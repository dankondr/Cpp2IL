using System.Collections.Generic;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// Shared synthetic fixtures for the regression tests: an injected caller method
// with a hand-built ISIL graph, plus AsmResolver stubs for the corlib types the
// emitted IL must name. Mirrors the helpers in IlGeneratorTests.cs — kept local
// so this folder stays self-contained.
internal static class SyntheticFixture
{
    public static void SeedCorLibTypes(ApplicationAnalysisContext app, ModuleDefinition module,
        params TypeAnalysisContext[] types)
    {
        foreach (var type in types)
        {
            var baseRef = type is { IsValueType: true }
                ? module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType")
                : null;
            type.PutExtraData("AsmResolverType",
                new TypeDefinition(type.Namespace, type.Name,
                    TypeAttributes.Public | (type.IsValueType ? TypeAttributes.Sealed | TypeAttributes.SequentialLayout : TypeAttributes.Class),
                    baseRef));
        }
    }

    public static (MethodAnalysisContext caller, MethodDefinition method) ForeignCaller(
        ApplicationAnalysisContext app, ModuleDefinition module, List<Instruction> instructions,
        List<LocalVariable> locals, TypeAnalysisContext? returnType = null)
    {
        var returnType_ = returnType ?? app.SystemTypes.SystemVoidType;
        var callerType = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "ForeignCaller", app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        var caller = callerType.InjectMethodContext("Run", returnType_,
            R.MethodAttributes.Public | R.MethodAttributes.Static);
        caller.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        caller.Locals = locals;
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];
        var type = new TypeDefinition("Tests", "ForeignCaller", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var ilReturnType = returnType_ == app.SystemTypes.SystemVoidType
            ? module.CorLibTypeFactory.Void
            : returnType_.GetExtraData<TypeDefinition>("AsmResolverType")!.ToTypeSignature();
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(ilReturnType));
        type.Methods.Add(method);
        return (caller, method);
    }
}
