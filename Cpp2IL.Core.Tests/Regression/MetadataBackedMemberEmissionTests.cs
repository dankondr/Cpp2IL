using System;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils.AsmResolver;
using NUnit.Framework;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// castle-recovery#83 - emitted IL may only name members the recovered typedefs
// actually carry. VectorN.Min/Max have no MethodDef rows in il2cpp metadata
// (il2cpp folds them: managed callers never reach them), so the lifter's
// VectorMin/VectorMax ops must lower to members that exist - Mathf.Min/Max per
// component when Mathf carries them, else the inline `a > b ? a : b` compare
// Unity's own implementation compiles to. memmove stays a Buffer.MemoryCopy
// call only while the recovered corlib declares it.
public class MetadataBackedMemberEmissionTests
{
    private ApplicationAnalysisContext _app = null!;
    private TypeAnalysisContext _single = null!;
    private TypeAnalysisContext _void = null!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        _app = TestGameLoader.LoadSimple2022Game();
        _single = _app.SystemTypes.SystemSingleType;
        _void = _app.SystemTypes.SystemVoidType;
    }

    // The caller's declaring type must see the vector typedef: emit it on a
    // Tests.Host class injected into the vector's own assembly so the
    // value-type locals do not collapse to the Int32 placeholder.
    private MethodAnalysisContext Runner(InjectedTypeAnalysisContext host, string name,
        TypeAnalysisContext returnType,
        (TypeAnalysisContext Type, string Name)[] parameters, out LocalVariable[] locals)
    {
        var caller = new InjectedMethodAnalysisContext(host, name, returnType,
            R.MethodAttributes.Public | R.MethodAttributes.Static,
            parameters.Select(p => p.Type).ToArray(), parameters.Select(p => p.Name).ToArray());
        locals = parameters.Select((p, i) => new LocalVariable(p.Name, new Register(i, $"X{i}", -1), p.Type)).ToArray();
        caller.ParameterLocals = [.. locals];
        caller.Locals = [.. locals];
        caller.AnalysisWarnings = [];
        return caller;
    }

    private ModuleDefinition NewModule()
    {
        var module = new ModuleDefinition("Emission.dll",
            new AssemblyReference("System.Private.CoreLib", typeof(object).Assembly.GetName().Version!));
        var holder = new TypeDefinition("Tests", "Primitives", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(holder);
        return module;
    }

    // Declares a runnable TypeDef in the module for an analysis context and
    // binds the extra-data slot ToTypeSignature/ToMethodDescriptor/
    // ToFieldDescriptor read, so references land on the module's own defs.
    private TypeDefinition BindType(ModuleDefinition module, TypeAnalysisContext context)
    {
        var definition = new TypeDefinition(context.Namespace, context.Name,
            TypeAttributes.Public | (context.IsValueType
                ? TypeAttributes.Sealed | TypeAttributes.SequentialLayout
                : TypeAttributes.Class),
            context.IsValueType
                ? module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType")
                : module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(definition);
        context.PutExtraData("AsmResolverType", definition);
        return definition;
    }

    private FieldDefinition BindField(ModuleDefinition module, TypeDefinition owner, FieldAnalysisContext context)
    {
        var definition = new FieldDefinition(context.Name, FieldAttributes.Public,
            new FieldSignature(Sig(module, context.FieldType)));
        owner.Fields.Add(definition);
        context.PutExtraData("AsmResolverField", definition);
        return definition;
    }

    private MethodDefinition BindMethod(ModuleDefinition module, TypeDefinition owner, MethodAnalysisContext context)
    {
        var signature = context.IsStatic
            ? MethodSignature.CreateStatic(Sig(module, context.ReturnType),
                context.Parameters.Select(p => Sig(module, p.ParameterType)).ToArray())
            : MethodSignature.CreateInstance(Sig(module, context.ReturnType),
                context.Parameters.Select(p => Sig(module, p.ParameterType)).ToArray());
        var attributes = MethodAttributes.Public
            | (context.IsStatic ? MethodAttributes.Static : 0)
            | (context.Name == ".ctor" ? MethodAttributes.SpecialName | MethodAttributes.RuntimeSpecialName : 0);
        var definition = new MethodDefinition(context.Name, attributes, signature);
        owner.Methods.Add(definition);
        context.PutExtraData("AsmResolverMethod", definition);
        return definition;
    }

    private static TypeSignature Sig(ModuleDefinition module, TypeAnalysisContext type) =>
        type.FullName switch
        {
            "System.Single" => module.CorLibTypeFactory.Single,
            "System.Int32" => module.CorLibTypeFactory.Int32,
            "System.Int64" => module.CorLibTypeFactory.Int64,
            "System.UInt64" => module.CorLibTypeFactory.UInt64,
            "System.Void" => module.CorLibTypeFactory.Void,
            _ => type.ToTypeSignature(),
        };

    private static MethodDefinition Definition(ModuleDefinition module, string name,
        TypeAnalysisContext returnType, (TypeAnalysisContext Type, string Name)[] parameters)
    {
        var owner = new TypeDefinition("Tests", name + "Runner", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var definition = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(Sig(module, returnType),
                parameters.Select(p => Sig(module, p.Type))));
        owner.Methods.Add(definition);
        for (var i = 0; i < parameters.Length; i++)
            definition.ParameterDefinitions.Add(new ParameterDefinition((ushort)(i + 1), parameters[i].Name, default));
        return definition;
    }

    private (R.Assembly Assembly, R.MethodInfo Method) Load(
        MethodAnalysisContext caller, MethodDefinition definition, ModuleDefinition module)
    {
        IlGenerator.GenerateIl(caller, definition);
        var assembly = new AssemblyDefinition("Emission", new Version(1, 0));
        assembly.Modules.Add(module);
        using var stream = new System.IO.MemoryStream();
        module.Write(stream);
        var loaded = R.Assembly.Load(stream.ToArray());
        return (loaded, loaded.GetType($"Tests.{caller.Name}Runner")!.GetMethod("Run")!);
    }

    // Every memberref an emitted body names must resolve to a definition that
    // exists - in this harness that means a MethodDefinition/FieldDefinition in
    // the module (references outside would be raw MemberReferences).
    private static void AssertAllMemberRefsResolve(MethodDefinition definition)
    {
        foreach (var instruction in definition.CilMethodBody!.Instructions)
        {
            switch (instruction.Operand)
            {
                case MemberReference reference:
                    Assert.Fail($"dangling memberref {reference.FullName}");
                    break;
                case MethodSpecification specification:
                    Assert.That(specification.Method, Is.TypeOf<MethodDefinition>(),
                        $"spec {specification.FullName} must land on a MethodDef");
                    break;
            }
        }
    }

    private (TypeAnalysisContext Vector4, TypeAnalysisContext Mathf) FixtureTypes(ModuleDefinition module)
    {
        var coreModule = _app.AssembliesByName["UnityEngine.CoreModule"];
        var vector4 = coreModule.GetTypeByFullName("UnityEngine.Vector4")!;
        var mathf = coreModule.GetTypeByFullName("UnityEngine.Mathf")!;
        var vector4Def = BindType(module, vector4);
        var mathfDef = BindType(module, mathf);

        var components = new[] { "x", "y", "z", "w" }
            .Select(name => vector4.Fields.First(f => f.Name == name))
            .Select(field => (field, BindField(module, vector4Def, field)))
            .ToArray();

        // Runnable bodies: the ctor assigns its parameters component-wise, and
        // Mathf.Min/Max forward to System.MathF which the real corlib carries.
        var constructor = vector4.Methods.First(m => m is { IsStatic: false } && m.Name == ".ctor"
            && m.Parameters.Count == 4
            && m.Parameters.All(p => p.ParameterType.DefaultFullName == "System.Single"));
        var ctorDef = BindMethod(module, vector4Def, constructor);
        ctorDef.CilMethodBody = new CilMethodBody();
        for (var i = 0; i < components.Length; i++)
        {
            ctorDef.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0);
            ctorDef.CilMethodBody.Instructions.Add(new CilInstruction(CilOpCodes.Ldarg, (ushort)(i + 1)));
            ctorDef.CilMethodBody.Instructions.Add(CilOpCodes.Stfld, components[i].Item2);
        }
        ctorDef.CilMethodBody.Instructions.Add(CilOpCodes.Ret);

        var mathfBody = new Func<string, MethodDefinition>(name =>
        {
            var method = mathf.Methods.First(m => m is { IsStatic: true } && m.Name == name
                && m.Parameters.Count == 2
                && m.Parameters.All(p => p.ParameterType.DefaultFullName == "System.Single"));
            var definition = BindMethod(module, mathfDef, method);
            definition.CilMethodBody = new CilMethodBody();
            var keepLhs = new CilInstruction(CilOpCodes.Ldarg_0);
            definition.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0);
            definition.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_1);
            definition.CilMethodBody.Instructions.Add(
                name == "Min" ? CilOpCodes.Blt : CilOpCodes.Bgt, new CilInstructionLabel(keepLhs));
            definition.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_1);
            definition.CilMethodBody.Instructions.Add(CilOpCodes.Ret);
            definition.CilMethodBody.Instructions.Add(keepLhs);
            definition.CilMethodBody.Instructions.Add(CilOpCodes.Ret);
            return definition;
        });
        mathfBody("Min");
        mathfBody("Max");
        return (vector4, mathf);
    }

    [Test]
    public void VectorMinMaxLowersToMathfWhenMetadataCarriesIt()
    {
        var module = NewModule();
        var (vector4, _) = FixtureTypes(module);
        var host = _app.AssembliesByName["UnityEngine.CoreModule"].InjectType("Tests", "Host",
            _app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var parameters = new[] { (vector4, "a"), (vector4, "b") };
        var caller = Runner(host, "Min", vector4, parameters, out var locals);
        var result = new LocalVariable("res", new Register(8, "X8", 1), vector4);
        caller.Locals = [.. locals, result];
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.VectorMin, result, locals[0], locals[1]),
            new Instruction(1, OpCode.Return, result),
        ]);

        var definition = Definition(module, "Min", vector4, parameters);
        var (_, method) = Load(caller, definition, module);

        AssertAllMemberRefsResolve(definition);
        Assert.That(definition.CilMethodBody!.Instructions.Count(i => i.OpCode == CilOpCodes.Call
            && i.Operand is MethodDefinition callee
            && callee.Name == "Min" && callee.DeclaringType!.Name == "Mathf"), Is.EqualTo(4),
            "one Mathf.Min call per component");
        Assert.That(definition.CilMethodBody.Instructions.Count(i => i.OpCode == CilOpCodes.Newobj),
            Is.EqualTo(1), "the vector is rebuilt through its metadata ctor");

        var vectorType = method.DeclaringType!.Assembly.GetType("UnityEngine.Vector4")!;
        var a = Activator.CreateInstance(vectorType, [4f, 1f, 9f, 2f]);
        var b = Activator.CreateInstance(vectorType, [3f, 5f, 7f, 8f]);
        var min = method.Invoke(null, [a, b])!;
        Assert.That(vectorType.GetField("x")!.GetValue(min), Is.EqualTo(3f));
        Assert.That(vectorType.GetField("w")!.GetValue(min), Is.EqualTo(2f));
    }

    [Test]
    public void VectorMinMaxLowersToInlineCompareWithoutMathf()
    {
        // A Vector2 typedef in an assembly with no Mathf still lowers honestly:
        // fields and the ctor come from the vector's own metadata, the compare
        // is emitted inline.
        var module = NewModule();
        var systemAssembly = _app.AssembliesByName["System"];
        var vector2 = systemAssembly.InjectType("UnityEngine", "Vector2",
            _app.SystemTypes.SystemValueTypeType, R.TypeAttributes.Public | R.TypeAttributes.Sealed);
        var vector2Def = BindType(module, vector2);
        var fieldDefs = new[] { "x", "y" }
            .Select(name => vector2.InjectFieldContext(name, _single, R.FieldAttributes.Public))
            .Select(field => BindField(module, vector2Def, field))
            .ToArray();
        var ctorContext = vector2.InjectMethodContext(".ctor", _void,
            R.MethodAttributes.Public, [_single, _single]);
        var ctorDef = BindMethod(module, vector2Def, ctorContext);
        ctorDef.CilMethodBody = new CilMethodBody();
        for (var i = 0; i < fieldDefs.Length; i++)
        {
            ctorDef.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0);
            ctorDef.CilMethodBody.Instructions.Add(new CilInstruction(CilOpCodes.Ldarg, (ushort)(i + 1)));
            ctorDef.CilMethodBody.Instructions.Add(CilOpCodes.Stfld, fieldDefs[i]);
        }
        ctorDef.CilMethodBody.Instructions.Add(CilOpCodes.Ret);

        var host = systemAssembly.InjectType("Tests", "Host",
            _app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var parameters = new (TypeAnalysisContext Type, string Name)[] { (vector2, "a"), (vector2, "b") };
        var caller = Runner(host, "Max", vector2, parameters, out var locals);
        var result = new LocalVariable("res", new Register(8, "X8", 1), vector2);
        caller.Locals = [.. locals, result];
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.VectorMax, result, locals[0], locals[1]),
            new Instruction(1, OpCode.Return, result),
        ]);

        var definition = Definition(module, "Max", vector2, parameters);
        var (_, method) = Load(caller, definition, module);

        AssertAllMemberRefsResolve(definition);
        Assert.That(definition.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Call),
            Is.False, "no Mathf in the declaring assembly means no call at all");
        Assert.That(definition.CilMethodBody.Instructions.Count(i => i.OpCode == CilOpCodes.Bgt),
            Is.EqualTo(2), "the component-wise compare is emitted inline");

        var vectorType = method.DeclaringType!.Assembly.GetType("UnityEngine.Vector2")!;
        var a = Activator.CreateInstance(vectorType, [4f, 1f]);
        var b = Activator.CreateInstance(vectorType, [3f, 5f]);
        var max = method.Invoke(null, [a, b])!;
        Assert.That(vectorType.GetField("x")!.GetValue(max), Is.EqualTo(4f));
        Assert.That(vectorType.GetField("y")!.GetValue(max), Is.EqualTo(5f));
    }
}
