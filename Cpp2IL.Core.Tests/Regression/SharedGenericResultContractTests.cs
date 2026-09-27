using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: IL emission — shared-generic result evidence (#57, 69b7bc0c).
// A shared-generic call's instantiation must be solved from the result local's
// declared type only. Its emitted (sanitized) type is a runtime-safe fallback —
// the internal *Enum marker lowers to int — and must not be taken as proof the
// callee ran as CreateInstance<System.Int32>: the honest body keeps the marker
// instantiation, which the caller cannot name, so it emits the diagnostic stub.
public class SharedGenericResultContractTests
{
    [Test]
    public void ErasedGenericCallResultDoesNotFabricateInt32Instantiation()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var activator = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Activator")!;
        var createInstance = activator.Methods.Single(method =>
            method.Name == "CreateInstance" && method.GenericParameters.Count == 1
            && method.Parameters.Count == 0);
        var markerType = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Int32Enum")!;
        Assert.That(markerType.Visibility, Is.EqualTo(R.TypeAttributes.NotPublic),
            "fixture corlib should expose the shared-generic enum markers as internal");
        var module = new ModuleDefinition("ErasedResult.dll");
        markerType.PutExtraData("AsmResolverType", new TypeDefinition(markerType.Namespace,
            markerType.Name,
            TypeAttributes.NotPublic | TypeAttributes.Sealed | TypeAttributes.SequentialLayout,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType")));
        // The native call site carries the erased shared instantiation: CreateInstance<Int32Enum>.
        var callee = new ConcreteGenericMethodAnalysisContext(createInstance, [], [markerType]);
        var result = new LocalVariable("result", new Register(null, "result"));
        var sink = new LocalVariable("sink", new Register(null, "sink"))
            { Type = app.SystemTypes.SystemInt32Type };
        SeedCorLibTypes(app, module, app.SystemTypes.SystemVoidType,
            app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemObjectType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Call, callee, result),
            new(1, OpCode.Move, sink, result),
            new(2, OpCode.Return)], [result, sink]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => (i.OpCode == CilOpCodes.Call || i.OpCode == CilOpCodes.Callvirt)
                    && i.Operand?.ToString()?.Contains("CreateInstance<System.Int32>") == true),
                Is.False, "the marker's int fallback must not become the callee's instantiation");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Throw), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
        Assert.That(il.All(i => i.OpCode == CilOpCodes.Ldstr
                || i.Operand?.ToString()?.Contains("Int32Enum") != true), Is.True,
            "no metadata token may name the invisible marker type (the ldstr diagnostic may)");
        Assert.That(method.CilMethodBody.LocalVariables.All(l =>
            l.VariableType?.FullName?.Contains("Int32Enum") != true), Is.True);
    }

}
