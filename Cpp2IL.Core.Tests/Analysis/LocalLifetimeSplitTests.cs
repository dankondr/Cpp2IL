using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils.AsmResolver;
using ReflectionFieldAttributes = System.Reflection.FieldAttributes;
using ReflectionMethodAttributes = System.Reflection.MethodAttributes;
using ReflectionTypeAttributes = System.Reflection.TypeAttributes;

namespace Cpp2IL.Core.Tests.Analysis;

/// <summary>
/// Flow-sensitive local typing: the lifter tracks a native register as one whole, but a
/// scalar operand position only touches the register's low lane. When a resolved operand
/// position has an incompatible CLR stack kind (a scalar I4/I8/F/native-int view against
/// a local whose type is a value-type aggregate), the position is split off to the
/// register's lane-0 field - a different slot, not a different value - instead of
/// merging the kinds into one local or degrading to a default. Definitions that stay
/// inside one compatible live range still coalesce into a single local.
/// </summary>
public class LocalLifetimeSplitTests
{
    private static ApplicationAnalysisContext App => Cpp2IlApi.CurrentAppContext!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    // A public-field value type standing in for UnityEngine.Vector3: three floats
    // x/y/z at offsets 0/4/8, so the register's low lane is field `x`.
    private static TypeAnalysisContext Vector3(ApplicationAnalysisContext app)
    {
        var vector = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "UnityEngine", "Vector3",
            app.AssembliesByName["mscorlib"].GetTypeByFullName("System.ValueType")!,
            ReflectionTypeAttributes.Public | ReflectionTypeAttributes.Sealed | ReflectionTypeAttributes.SequentialLayout);
        var offset = 0;
        foreach (var name in new[] { "x", "y", "z" })
        {
            vector.Fields.Add(new InjectedFieldAnalysisContext(name, app.SystemTypes.SystemSingleType,
                ReflectionFieldAttributes.Public, vector, offset));
            offset += 4;
        }

        return vector;
    }

    // A public-field value type shaped like an enum: one Int32 field `value__` at
    // offset 0, so an I4 operand position on it resolves to the lane field.
    private static TypeAnalysisContext Enum32(ApplicationAnalysisContext app)
    {
        var kind = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Lane", "Enum32",
            app.AssembliesByName["mscorlib"].GetTypeByFullName("System.ValueType")!,
            ReflectionTypeAttributes.Public | ReflectionTypeAttributes.Sealed | ReflectionTypeAttributes.SequentialLayout);
        kind.Fields.Add(new InjectedFieldAnalysisContext("value__", app.SystemTypes.SystemInt32Type,
            ReflectionFieldAttributes.Public, kind, 0));
        return kind;
    }

    private static InjectedMethodAnalysisContext Method(ApplicationAnalysisContext app, string name,
        TypeAnalysisContext returnType, TypeAnalysisContext[] parameterTypes, params string[] parameterNames)
        => new(app.SystemTypes.SystemObjectType, name, returnType,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, parameterTypes, parameterNames);

    private static ISILControlFlowGraph Graph(IReadOnlyList<Instruction> instructions)
    {
        // Resolve numeric jump targets to instruction references, as the lifter does.
        foreach (var instruction in instructions)
            if (instruction.OpCode is OpCode.Jump or OpCode.ConditionalJump
                && instruction.Operands[0] is Immediate { Value: { } immediate })
                instruction.SetOperand(0, instructions[(int)immediate]);

        return new ISILControlFlowGraph(instructions.ToList());
    }

    private static TypeSignature CorLibSignature(ModuleDefinition module, TypeAnalysisContext type)
        => type is SzArrayTypeAnalysisContext szArray
            ? CorLibSignature(module, szArray.ElementType).MakeSzArrayType()
            : type.FullName switch
        {
            "System.Single" => module.CorLibTypeFactory.Single,
            "System.Double" => module.CorLibTypeFactory.Double,
            "System.Int32" => module.CorLibTypeFactory.Int32,
            "System.Int64" => module.CorLibTypeFactory.Int64,
            "System.Boolean" => module.CorLibTypeFactory.Boolean,
            "System.Object" => module.CorLibTypeFactory.Object,
            "System.Void" => module.CorLibTypeFactory.Void,
            _ => type.ToTypeSignature(),
        };

    // Emit placeholder TypeDefinitions for every context the body will reference and
    // wire injected fields to real FieldDefinitions (with the real corlib field type,
    // so ldfld pushes a genuine float, not a module-local duplicate).
    private static (ModuleDefinition module, IReadOnlyDictionary<TypeAnalysisContext, TypeSignature> signatures)
        EmitModule(ApplicationAnalysisContext app, params TypeAnalysisContext[] types)
    {
        var module = new ModuleDefinition("LifetimeSplit.dll",
            new AssemblyReference("System.Private.CoreLib", typeof(object).Assembly.GetName().Version!));
        var signatures = new Dictionary<TypeAnalysisContext, TypeSignature>();
        foreach (var context in types)
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
            signatures[context] = definition.ToTypeSignature(context.IsValueType);

            foreach (var field in context.Fields.OfType<InjectedFieldAnalysisContext>())
            {
                var fieldDefinition = new FieldDefinition(field.Name, FieldAttributes.Public,
                    new FieldSignature(CorLibSignature(module, field.FieldType)));
                definition.Fields.Add(fieldDefinition);
                field.PutExtraData("AsmResolverField", fieldDefinition);
            }
        }

        return (module, signatures);
    }

    private static MethodDefinition Runner(ModuleDefinition module,
        IReadOnlyDictionary<TypeAnalysisContext, TypeSignature> signatures,
        TypeAnalysisContext returnType, TypeAnalysisContext[] parameterTypes, string[] parameterNames)
    {
        var owner = new TypeDefinition("Tests", "Runner", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var definition = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(CorLibSignature(module, returnType),
                parameterTypes.Select(t => CorLibSignature(module, t))));
        owner.Methods.Add(definition);
        for (var i = 0; i < parameterNames.Length; i++)
            definition.ParameterDefinitions.Add(new ParameterDefinition((ushort)(i + 1), parameterNames[i], default));
        return definition;
    }

    // The emitted body declares locals typed by the module's placeholder corlib
    // definitions; rebind the ones standing in for primitives to the real corlib
    // signatures so the produced assembly actually JITs.
    private static void RebindPrimitiveLocals(MethodDefinition definition, ModuleDefinition module)
    {
        foreach (var local in definition.CilMethodBody!.LocalVariables)
            local.VariableType = local.VariableType.FullName switch
            {
                "System.Single" => module.CorLibTypeFactory.Single,
                "System.Double" => module.CorLibTypeFactory.Double,
                "System.Int32" => module.CorLibTypeFactory.Int32,
                "System.Int64" => module.CorLibTypeFactory.Int64,
                "System.Boolean" => module.CorLibTypeFactory.Boolean,
                "System.Object" => module.CorLibTypeFactory.Object,
                _ => local.VariableType,
            };
    }

    // Generate the body, write the module, load it and invoke - the call is what makes
    // the JIT prepare the body, which is where an incompatible stloc throws
    // InvalidProgramException.
    private static object?[] EmitAndInvoke(MethodAnalysisContext context, MethodDefinition definition,
        ModuleDefinition module, params object?[] arguments)
    {
        IlGenerator.GenerateIl(context, definition);
        RebindPrimitiveLocals(definition, module);

        var assembly = new AssemblyDefinition("LifetimeSplit", new Version(1, 0));
        assembly.Modules.Add(module);
        using var stream = new MemoryStream();
        module.Write(stream);
        var loaded = System.Reflection.Assembly.Load(stream.ToArray());
        var run = loaded.GetType("Tests.Runner")!.GetMethod(definition.Name!)!;
        run.Invoke(null, arguments);
        return arguments;
    }

    private static object VectorInstance(System.Reflection.Assembly assembly, float x)
    {
        var vector = Activator.CreateInstance(assembly.GetType("UnityEngine.Vector3")!)!;
        var vectorType = vector.GetType();
        vectorType.GetField("x")!.SetValue(vector, x);
        vectorType.GetField("y")!.SetValue(vector, 0f);
        vectorType.GetField("z")!.SetValue(vector, 0f);
        return vector;
    }

    private static System.Reflection.Assembly EmitAssembly(MethodAnalysisContext context,
        MethodDefinition definition, ModuleDefinition module)
    {
        IlGenerator.GenerateIl(context, definition);
        RebindPrimitiveLocals(definition, module);
        var assembly = new AssemblyDefinition("LifetimeSplit", new Version(1, 0));
        assembly.Modules.Add(module);
        using var stream = new MemoryStream();
        module.Write(stream);
        return System.Reflection.Assembly.Load(stream.ToArray());
    }

    [Test]
    public void ScalarOperationOnAggregateLocalReadsLaneZeroField()
    {
        // fneg s8, s0: the destination is a float, so the source reads v0's low lane
        // - Vector3.x - not the whole vector local.
        var app = App;
        var vector = Vector3(app);
        var parameter = new LocalVariable("arg0", new Register(0, "X0"), vector);
        var vec = new LocalVariable("vec", new Register(8, "V0", 2), vector);
        var scalar = new LocalVariable("scalar", new Register(8, "V8", 3), app.SystemTypes.SystemSingleType);
        var ret = new LocalVariable("ret", new Register(0, "X8", 1), app.SystemTypes.SystemSingleType);
        var context = Method(app, "Run", app.SystemTypes.SystemSingleType, [vector], ["arg0"]);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, vec, parameter),
            new Instruction(1, OpCode.Negate, scalar, vec),
            new Instruction(2, OpCode.Move, ret, scalar),
            new Instruction(3, OpCode.Return, ret)]);
        context.Locals = [parameter, vec, scalar, ret];
        context.ParameterLocals = [parameter];
        context.AnalysisWarnings = [];

        LocalVariables.ResolveTypesAndFields(context);

        var negate = context.ControlFlowGraph.Instructions.Single(i => i.OpCode == OpCode.Negate);
        Assert.Multiple(() =>
        {
            Assert.That(negate.Operands[1], Is.TypeOf<FieldReference>());
            var lane = (FieldReference)negate.Operands[1];
            Assert.That(lane.Field.Name, Is.EqualTo("x"));
            Assert.That(lane.Local, Is.SameAs(vec));
        });

        var (module, signatures) = EmitModule(app, vector, app.SystemTypes.SystemSingleType,
            app.SystemTypes.SystemVoidType);
        var definition = Runner(module, signatures, app.SystemTypes.SystemSingleType, [vector], ["arg0"]);
        var loaded = EmitAssembly(context, definition, module);

        Assert.Multiple(() =>
        {
            var il = definition.CilMethodBody!.Instructions;
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldfld), Is.True);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Neg), Is.True);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call), Is.False,
                "no fake vector op_UnaryNegation call");
        });

        var result = loaded.GetType("Tests.Runner")!.GetMethod("Run")!
            .Invoke(null, [VectorInstance(loaded, 2.5f)]);
        Assert.That(result, Is.EqualTo(-2.5f));
    }

    [Test]
    public void ScalarCopyFromAggregateLocalReadsLaneZeroField()
    {
        // fmov s8, s0 as a plain move: a scalar slot reads the lane field.
        var app = App;
        var vector = Vector3(app);
        var vec = new LocalVariable("vec", new Register(8, "V0", 1), vector);
        var scalar = new LocalVariable("scalar", new Register(8, "V8", 1), app.SystemTypes.SystemSingleType);
        var ret = new LocalVariable("ret", new Register(0, "X8", 1), app.SystemTypes.SystemSingleType);
        var context = Method(app, "Run", app.SystemTypes.SystemSingleType, [], []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, scalar, vec),
            new Instruction(1, OpCode.Move, ret, scalar),
            new Instruction(2, OpCode.Return, ret)]);
        context.Locals = [vec, scalar, ret];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];

        LocalVariables.ResolveTypesAndFields(context);

        var move = context.ControlFlowGraph.Instructions.First(i => i.OpCode == OpCode.Move);
        Assert.That(move.Operands[1], Is.TypeOf<FieldReference>());

        var (module, signatures) = EmitModule(app, vector, app.SystemTypes.SystemSingleType,
            app.SystemTypes.SystemVoidType);
        var definition = Runner(module, signatures, app.SystemTypes.SystemSingleType, [], []);
        var loaded = EmitAssembly(context, definition, module);

        Assert.That(definition.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Ldfld), Is.True);
        // zero-initialized vec: x is 0, so the read is 0.
        var result = loaded.GetType("Tests.Runner")!.GetMethod("Run")!.Invoke(null, []);
        Assert.That(result, Is.EqualTo(0f));
    }

    [Test]
    public void ScalarCopyIntoAggregateLocalWritesLaneZeroField()
    {
        // fmov s0, s8 as a plain move into a vector-typed local: only the low lane is
        // defined, so the store targets x, leaving y/z at the local's initial zeroes.
        var app = App;
        var vector = Vector3(app);
        var parameter = new LocalVariable("arg0", new Register(0, "X0"), app.SystemTypes.SystemSingleType);
        var vec = new LocalVariable("vec", new Register(0, "V0", 1), vector);
        var ret = new LocalVariable("ret", new Register(8, "V8", 1), vector);
        var context = Method(app, "Run", vector, [app.SystemTypes.SystemSingleType], ["arg0"]);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, vec, parameter),
            new Instruction(1, OpCode.Move, ret, vec),
            new Instruction(2, OpCode.Return, ret)]);
        context.Locals = [parameter, vec, ret];
        context.ParameterLocals = [parameter];
        context.AnalysisWarnings = [];

        LocalVariables.ResolveTypesAndFields(context);

        var move = context.ControlFlowGraph.Instructions.First(i => i.OpCode == OpCode.Move);
        Assert.Multiple(() =>
        {
            Assert.That(move.Operands[0], Is.TypeOf<FieldReference>());
            Assert.That(((FieldReference)move.Operands[0]).Field.Name, Is.EqualTo("x"));
        });

        var (module, signatures) = EmitModule(app, vector, app.SystemTypes.SystemSingleType,
            app.SystemTypes.SystemVoidType);
        var definition = Runner(module, signatures, vector, [app.SystemTypes.SystemSingleType], ["arg0"]);
        var loaded = EmitAssembly(context, definition, module);

        Assert.That(definition.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Stfld), Is.True);

        var vectorType = loaded.GetType("UnityEngine.Vector3")!;
        var result = loaded.GetType("Tests.Runner")!.GetMethod("Run")!.Invoke(null, [7.5f]);
        Assert.Multiple(() =>
        {
            Assert.That(vectorType.GetField("x")!.GetValue(result), Is.EqualTo(7.5f));
            Assert.That(vectorType.GetField("y")!.GetValue(result), Is.EqualTo(0f));
            Assert.That(vectorType.GetField("z")!.GetValue(result), Is.EqualTo(0f));
        });
    }

    [Test]
    public void RegisterReuseAcrossBranchesSplitsAtKindBoundary()
    {
        // One physical register carries a vector down one arm and a float down the
        // other - the X/S reuse of the parallax fixture. The join's phi has the
        // scalar kind, so the vector arm's edge copy writes... wait, reads the lane.
        var app = App;
        var vector = Vector3(app);
        var cond = new Register(0, "X0");
        var vecReg = new Register(1, "X1");
        var fReg = new Register(2, "X2");
        var slot = new Register(8, "V8");
        var instructions = new List<Instruction>
        {
            new(0, OpCode.ConditionalJump, new Immediate(3), cond),
            new(1, OpCode.Move, slot, vecReg),
            new(2, OpCode.Jump, new Immediate(4)),
            new(3, OpCode.Move, slot, fReg),
            new(4, OpCode.Return, slot),
        };
        var context = Method(app, "Run", app.SystemTypes.SystemSingleType,
            [app.SystemTypes.SystemBooleanType, vector, app.SystemTypes.SystemSingleType],
            ["pick", "vec", "f"]);
        context.ControlFlowGraph = Graph(instructions);
        context.ParameterOperands = [cond, vecReg, fReg];
        context.AnalysisWarnings = [];

        SsaForm.Build(context.ControlFlowGraph, new DominatorInfo(context.ControlFlowGraph));
        LocalVariables.CreateAll(context);
        LocalVariables.ResolveTypesAndFields(context);
        SsaForm.Remove(context);
        CopyCoalescer.Run(context);
        LocalVariables.ResolveLateGeneratedTypes(context);

        // The vector arm reaches a float-typed phi: its edge copy reads the lane-0
        // field instead of storing the whole vector into a float local.
        Assert.That(context.ControlFlowGraph.Instructions.Any(i =>
                i.OpCode == OpCode.Move && i.Operands[1] is FieldReference { Field.Name: "x" }),
            Is.True);

        var (module, signatures) = EmitModule(app, vector, app.SystemTypes.SystemSingleType,
            app.SystemTypes.SystemVoidType, app.SystemTypes.SystemBooleanType);
        var definition = Runner(module, signatures, app.SystemTypes.SystemSingleType,
            [app.SystemTypes.SystemBooleanType, vector, app.SystemTypes.SystemSingleType],
            ["pick", "vec", "f"]);
        var loaded = EmitAssembly(context, definition, module);

        var run = loaded.GetType("Tests.Runner")!.GetMethod("Run")!;
        var vec = VectorInstance(loaded, 2.5f);
        Assert.Multiple(() =>
        {
            Assert.That(run.Invoke(null, [true, vec, 7.5f]), Is.EqualTo(7.5f));
            Assert.That(run.Invoke(null, [false, vec, 7.5f]), Is.EqualTo(2.5f));
        });
    }

    [Test]
    public void IncompatibleLifetimesOfOneRegisterStayDistinctLocals()
    {
        // One register redefined as float, then reference, then int, then struct:
        // every definition is a separate lifetime and stays its own typed local.
        var app = App;
        var vector = Vector3(app);
        var locals = new[]
        {
            new LocalVariable("f", new Register(8, "X8", 1), app.SystemTypes.SystemSingleType),
            new LocalVariable("o", new Register(8, "X8", 2), app.SystemTypes.SystemObjectType),
            new LocalVariable("i", new Register(8, "X8", 3), app.SystemTypes.SystemInt32Type),
            new LocalVariable("s", new Register(8, "X8", 4), vector),
        };
        var parameters = new[]
        {
            new LocalVariable("arg0", new Register(0, "X0"), app.SystemTypes.SystemSingleType),
            new LocalVariable("arg1", new Register(1, "X1"), app.SystemTypes.SystemObjectType),
            new LocalVariable("arg2", new Register(2, "X2"), app.SystemTypes.SystemInt32Type),
            new LocalVariable("arg3", new Register(3, "X3"), vector),
        };
        var ret = new LocalVariable("ret", new Register(0, "X8", 5), app.SystemTypes.SystemInt32Type);
        var context = Method(app, "Run", app.SystemTypes.SystemInt32Type,
            [app.SystemTypes.SystemSingleType, app.SystemTypes.SystemObjectType,
             app.SystemTypes.SystemInt32Type, vector],
            ["arg0", "arg1", "arg2", "arg3"]);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, locals[0], parameters[0]),
            new Instruction(1, OpCode.Move, locals[1], parameters[1]),
            new Instruction(2, OpCode.Move, locals[2], parameters[2]),
            new Instruction(3, OpCode.Move, locals[3], parameters[3]),
            new Instruction(4, OpCode.Move, ret, locals[2]),
            new Instruction(5, OpCode.Return, ret)]);
        context.Locals = [.. parameters, .. locals, ret];
        context.ParameterLocals = [.. parameters];
        context.AnalysisWarnings = [];

        LocalVariables.ResolveTypesAndFields(context);
        CopyCoalescer.Run(context.ControlFlowGraph);

        var (module, signatures) = EmitModule(app, vector, app.SystemTypes.SystemSingleType,
            app.SystemTypes.SystemObjectType, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemVoidType);
        var definition = Runner(module, signatures, app.SystemTypes.SystemInt32Type,
            [app.SystemTypes.SystemSingleType, app.SystemTypes.SystemObjectType,
             app.SystemTypes.SystemInt32Type, vector],
            ["arg0", "arg1", "arg2", "arg3"]);
        var loaded = EmitAssembly(context, definition, module);

        Assert.Multiple(() =>
        {
            var declared = definition.CilMethodBody!.LocalVariables.Select(v => v.VariableType.FullName).ToList();
            Assert.That(declared, Does.Contain("System.Single"));
            Assert.That(declared, Does.Contain("System.Object"));
            Assert.That(declared, Does.Contain("System.Int32"));
            Assert.That(declared, Does.Contain("UnityEngine.Vector3"));
        });

        var result = loaded.GetType("Tests.Runner")!.GetMethod("Run")!
            .Invoke(null, [1.5f, new object(), 42, VectorInstance(loaded, 9f)]);
        Assert.That(result, Is.EqualTo(42));
    }

    [Test]
    public void PhiWithCompatibleIntegerWidthsEmitsValidStores()
    {
        // phi over an I4 version and an I8 version of one register: compatible integer
        // kinds stay one local; the wider arm's edge copy narrows to the phi's type.
        var app = App;
        var cond = new Register(0, "X0");
        var i32 = new Register(1, "X1");
        var i64 = new Register(2, "X2");
        var slot = new Register(8, "X8");
        var instructions = new List<Instruction>
        {
            new(0, OpCode.ConditionalJump, new Immediate(3), cond),
            new(1, OpCode.Move, slot, i32),
            new(2, OpCode.Jump, new Immediate(4)),
            new(3, OpCode.Move, slot, i64),
            new(4, OpCode.Return, slot),
        };
        var context = Method(app, "Run", app.SystemTypes.SystemInt32Type,
            [app.SystemTypes.SystemBooleanType, app.SystemTypes.SystemInt32Type,
             app.SystemTypes.SystemInt64Type],
            ["pick", "a", "b"]);
        context.ControlFlowGraph = Graph(instructions);
        context.ParameterOperands = [cond, i32, i64];
        context.AnalysisWarnings = [];

        SsaForm.Build(context.ControlFlowGraph, new DominatorInfo(context.ControlFlowGraph));
        LocalVariables.CreateAll(context);
        LocalVariables.ResolveTypesAndFields(context);
        SsaForm.Remove(context);
        CopyCoalescer.Run(context);
        LocalVariables.ResolveLateGeneratedTypes(context);

        var (module, signatures) = EmitModule(app, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemInt64Type, app.SystemTypes.SystemVoidType,
            app.SystemTypes.SystemBooleanType);
        var definition = Runner(module, signatures, app.SystemTypes.SystemInt32Type,
            [app.SystemTypes.SystemBooleanType, app.SystemTypes.SystemInt32Type,
             app.SystemTypes.SystemInt64Type],
            ["pick", "a", "b"]);
        var loaded = EmitAssembly(context, definition, module);

        var run = loaded.GetType("Tests.Runner")!.GetMethod("Run")!;
        Assert.Multiple(() =>
        {
            Assert.That(run.Invoke(null, [false, 5, 42L]), Is.EqualTo(5));
            Assert.That(run.Invoke(null, [true, 5, 42L]), Is.EqualTo(42));
        });
    }

    [Test]
    public void CompatibleAliasWithinOneLifetimeCoalesces()
    {
        // mov x8, x8 between two same-kind versions is an alias inside one lifetime:
        // coalescing still folds them into a single local.
        var app = App;
        var parameter = new LocalVariable("arg0", new Register(0, "X0"), app.SystemTypes.SystemInt32Type);
        var first = new LocalVariable("v1", new Register(8, "X8", 1), app.SystemTypes.SystemInt32Type);
        var alias = new LocalVariable("v2", new Register(8, "X8", 2), app.SystemTypes.SystemInt32Type);
        var ret = new LocalVariable("ret", new Register(0, "X8", 3), app.SystemTypes.SystemInt32Type);
        var increment = new LocalVariable("inc", new Register(8, "X8", 4), app.SystemTypes.SystemInt32Type);
        var add = new Instruction(2, OpCode.Add, increment, alias, new Immediate(1));
        var context = Method(app, "Run", app.SystemTypes.SystemInt32Type,
            [app.SystemTypes.SystemInt32Type], ["arg0"]);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, first, parameter),
            new Instruction(1, OpCode.Move, alias, first),
            add,
            new Instruction(3, OpCode.Move, ret, increment),
            new Instruction(4, OpCode.Return, ret)]);
        context.Locals = [parameter, first, alias, increment, ret];
        context.ParameterLocals = [parameter];
        context.AnalysisWarnings = [];

        CopyCoalescer.Run(context.ControlFlowGraph);

        // the alias collapsed: the add reads the copy's destination local (the
        // union's representative), i.e. both names resolve to one slot.
        Assert.That(add.Operands[1], Is.SameAs(alias));

        var (module, signatures) = EmitModule(app, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemVoidType);
        var definition = Runner(module, signatures, app.SystemTypes.SystemInt32Type,
            [app.SystemTypes.SystemInt32Type], ["arg0"]);
        var loaded = EmitAssembly(context, definition, module);

        var result = loaded.GetType("Tests.Runner")!.GetMethod("Run")!.Invoke(null, [41]);
        Assert.That(result, Is.EqualTo(42));
    }

    [Test]
    public void LoopCarriedCompatibleLocalStaysOneLocal()
    {
        // A loop phi over same-kind versions of one register is one lifetime: all its
        // versions coalesce into a single local and the emitted loop is valid.
        var app = App;
        var start = new Register(0, "X0");
        var counter = new Register(8, "X8");
        var flag = new Register(16, "TEMP");
        var instructions = new List<Instruction>
        {
            new(0, OpCode.Move, counter, start),
            new(1, OpCode.CheckLess, flag, counter, new Immediate(10)),
            new(2, OpCode.Not, flag, flag),
            new(3, OpCode.ConditionalJump, new Immediate(6), flag),
            new(4, OpCode.Add, counter, counter, new Immediate(1)),
            new(5, OpCode.Jump, new Immediate(1)),
            new(6, OpCode.Return, counter),
        };
        var context = Method(app, "Run", app.SystemTypes.SystemInt32Type,
            [app.SystemTypes.SystemInt32Type], ["arg0"]);
        context.ControlFlowGraph = Graph(instructions);
        context.ParameterOperands = [start];
        context.AnalysisWarnings = [];

        SsaForm.Build(context.ControlFlowGraph, new DominatorInfo(context.ControlFlowGraph));
        LocalVariables.CreateAll(context);
        LocalVariables.ResolveTypesAndFields(context);
        SsaForm.Remove(context);
        CopyCoalescer.Run(context);
        LocalVariables.ResolveLateGeneratedTypes(context);

        var counterLocals = context.ControlFlowGraph.Instructions
            .SelectMany(i => i.Operands)
            .OfType<LocalVariable>()
            .Where(l => l.Register.Name == "X8")
            .Distinct()
            .ToList();
        Assert.That(counterLocals, Has.Count.EqualTo(1),
            "every version of the loop variable is the same coalesced local");

        var (module, signatures) = EmitModule(app, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemVoidType, app.SystemTypes.SystemBooleanType);
        var definition = Runner(module, signatures, app.SystemTypes.SystemInt32Type,
            [app.SystemTypes.SystemInt32Type], ["arg0"]);
        var loaded = EmitAssembly(context, definition, module);

        var result = loaded.GetType("Tests.Runner")!.GetMethod("Run")!.Invoke(null, [3]);
        Assert.That(result, Is.EqualTo(10));
    }

    [Test]
    public void NestedFieldLaneInsideArrayIndexKeepsReceiverLocalRegistered()
    {
        // A lane FieldReference propagated into an ArrayAccess index can be the enum
        // local's only remaining use. A pruning pass that drops that receiver leaves
        // the emitted locals table without it, and the field load's ldloca hits
        // KeyNotFoundException - the corpus crash this test guards.
        var app = App;
        var kind = Enum32(app);
        var strings = new SzArrayTypeAnalysisContext(app.SystemTypes.SystemStringType);
        var arr = new LocalVariable("arg0", new Register(8, "X8"), strings);
        var kindLocal = new LocalVariable("kind", new Register(9, "X9", 6), kind);
        var dst = new LocalVariable("dst", new Register(0, "X0", 1), app.SystemTypes.SystemStringType);
        var context = Method(app, "Run", app.SystemTypes.SystemStringType, [strings], ["arg0"]);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, dst, new ArrayAccess(arr, new FieldReference(kind.Fields[0], kindLocal, 0))),
            new Instruction(1, OpCode.Return, dst)]);
        context.Locals = [arr, kindLocal, dst];
        context.ParameterLocals = [arr];
        context.AnalysisWarnings = [];

        LocalVariables.RemoveUnused(context);

        Assert.That(context.Locals, Does.Contain(kindLocal),
            "lane receiver pruned: the emitted locals table loses it and emission throws");

        var (module, signatures) = EmitModule(app, kind, app.SystemTypes.SystemStringType,
            app.SystemTypes.SystemVoidType);
        var definition = Runner(module, signatures, app.SystemTypes.SystemStringType, [strings], ["arg0"]);
        var loaded = EmitAssembly(context, definition, module);

        var result = loaded.GetType("Tests.Runner")!.GetMethod("Run")!
            .Invoke(null, [new[] { "hit", "other" }]);
        Assert.That(result, Is.EqualTo("hit"));
    }
}
