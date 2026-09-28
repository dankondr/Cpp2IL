using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: address of a managed-pointer local in a raw-pointer slot
// (castle-recovery#121). The pinned-buffer idiom passes &cell where cell is a
// T& local, so the operand emits as T&&. No IL converts a managed pointer to an
// unmanaged pointer, so the slot gets the diagnosed default - but the address
// load must not be emitted at all: a T&& on the stack is the `ref ref x` term
// C# cannot express.
public class ByRefAddressSlotTests
{
    [Test]
    public void AddressOfByRefLocalIntoPointerSlotKeepsDiagnosticOnly()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var byteType = app.SystemTypes.SystemByteType;
        var blob = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"],
            "Tests", "Blob", app.SystemTypes.SystemValueTypeType,
            R.TypeAttributes.Public | R.TypeAttributes.Sealed | R.TypeAttributes.SequentialLayout);
        var pointer = new PointerTypeAnalysisContext(blob);
        var calleeHolder = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"],
            "Tests", "Native", app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        var callee = calleeHolder.InjectMethodContext("Take", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, pointer);

        var cell = new LocalVariable("cell", new Register(null, "cell"),
            new ByRefTypeAnalysisContext(byteType));
        var module = new ModuleDefinition("ByRefAddr.dll");
        SeedCorLibTypes(app, module, byteType, app.SystemTypes.SystemVoidType, blob);
        var blobDefinition = new TypeDefinition("Tests", "Blob",
            TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        module.TopLevelTypes.Add(blobDefinition);
        blob.PutExtraData("AsmResolverType", blobDefinition);
        var nativeDefinition = new TypeDefinition("Tests", "Native",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(nativeDefinition);
        var calleeDefinition = new MethodDefinition("Take",
            MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void,
                [new PointerTypeSignature(blobDefinition.ToTypeSignature())]));
        nativeDefinition.Methods.Add(calleeDefinition);
        callee.PutExtraData("AsmResolverMethod", calleeDefinition);
        calleeHolder.PutExtraData("AsmResolverType", nativeDefinition);

        // ISIL for `Take(&cell)` where cell is byte&: the operand emits as byte&&.
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.CallVoid, callee, new AddressOf(cell)),
            new(1, OpCode.Return)], [cell]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => (i.OpCode == CilOpCodes.Ldloca || i.OpCode == CilOpCodes.Ldloca_S)
                    && i.Operand is CilLocalVariable), Is.False,
                "loading &cell would emit a byte&& the call site only drops - and " +
                "ilspy renders the dropped T&& load as the C#-illegal `ref ref`\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("System.Byte&&")), Is.True,
                "the unrepresentable conversion keeps its named diagnostic\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call
                    && i.Operand is IMethodDescriptor named && named.Name?.ToString() == "Take"),
                Is.True, () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }
}
