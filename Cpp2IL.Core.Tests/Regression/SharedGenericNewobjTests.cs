using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: IL emission — shared-generic newobj retargeting (#41, fcd1aaac).
// Shared generics erase the callee's instantiation to object: a fused
// Newobj + .ctor CallVoid must name the destination's concrete instantiation
// (List<string>), not the erased one the call site carried (List<object>).
public class SharedGenericNewobjTests
{
    [Test]
    public void FusedNewobjRetargetsConstructorToDestinationInstantiation()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var listDefinition = app.AssembliesByName["mscorlib"]
            .GetTypeByFullName("System.Collections.Generic.List`1")!;
        var parameterless = listDefinition.Methods.First(m => m.Name == ".ctor" && m.Parameters.Count == 0);
        var erasedType = new GenericInstanceTypeAnalysisContext(listDefinition,
            [app.SystemTypes.SystemObjectType]);
        var concreteType = new GenericInstanceTypeAnalysisContext(listDefinition,
            [app.SystemTypes.SystemStringType]);
        var erasedCtor = new ConcreteGenericMethodAnalysisContext(parameterless,
            [app.SystemTypes.SystemObjectType], []);
        var list = new LocalVariable("list", new Register(null, "list")) { Type = concreteType };

        var callerType = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "Maker", app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        var caller = callerType.InjectMethodContext("Run", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Newobj, list, erasedType),
            new(1, OpCode.CallVoid, erasedCtor, list),
            new(2, OpCode.Return)]);
        caller.Locals = [list];
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];

        var module = new ModuleDefinition("NewobjRetarget.dll");
        var listTypeDefinition = new TypeDefinition("System.Collections.Generic", "List`1",
            TypeAttributes.Public | TypeAttributes.Class);
        listTypeDefinition.GenericParameters.Add(new GenericParameter("T"));
        listDefinition.PutExtraData("AsmResolverType", listTypeDefinition);
        module.TopLevelTypes.Add(listTypeDefinition);
        var ctorDefinition = new MethodDefinition(".ctor", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        listTypeDefinition.Methods.Add(ctorDefinition);
        parameterless.PutExtraData("AsmResolverMethod", ctorDefinition);
        foreach (var t in new[] { app.SystemTypes.SystemVoidType, app.SystemTypes.SystemObjectType,
                     app.SystemTypes.SystemStringType })
            t.PutExtraData("AsmResolverType", new TypeDefinition(t.Namespace, t.Name,
                TypeAttributes.Public | (t.IsValueType ? TypeAttributes.Sealed : TypeAttributes.Class),
                t.IsValueType ? module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType") : null));
        var type = new TypeDefinition("Tests", "Maker", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        type.Methods.Add(method);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        var newobj = il.Where(i => i.OpCode == CilOpCodes.Newobj).ToList();
        Assert.Multiple(() =>
        {
            Assert.That(newobj, Has.Count.EqualTo(1),
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(newobj[0].Operand?.ToString(), Does.Contain("System.String"),
                () => newobj[0].Operand?.ToString() ?? "<null>");
            Assert.That(newobj[0].Operand?.ToString(), Does.Not.Contain("System.Object"),
                () => newobj[0].Operand?.ToString() ?? "<null>");
        });
    }
}
