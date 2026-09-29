using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;
using BindingFlags = System.Reflection.BindingFlags;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: ISIL→IL emission — a slot whose operand was never produced
// is filled with a synthetic default (a note plus ldnull/ldc/default(T)). When
// the destination has no store spelling, that value is popped right back off
// and decompiles to `_ = <expr>` (CS8183). The diagnostics already name the
// site, so the emitted IL must keep only the notes: no synthetic value, no pop.
public class DiscardedDefaultEmissionTests
{
    [Test]
    public void UnspellableNewarrStoreCarriesOnlyTheDiagnoses()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        // An element type with no resolvable token makes the array value
        // unproducible; the destination is a raw indexed memory form no store
        // opcode can spell, so the synthetic default used to be pushed and
        // popped (`_ = null`).
        var element = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"],
            "Tests", "OpaqueElement", app.SystemTypes.SystemObjectType,
            System.Reflection.TypeAttributes.Public);
        var array = new SzArrayTypeAnalysisContext(element);
        var destination = new MemoryOperand(indexRegister: new Immediate(8), scale: 1);
        var module = new ModuleDefinition("DiscardedDefault.dll");
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.NewArr, destination, array, new Immediate(4)),
            new(1, OpCode.Return)], []);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.True,
                "the site must still carry a named decompiler-issue note\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Count(i => i.OpCode == CilOpCodes.Ldstr), Is.EqualTo(2),
                "both notes survive: the slot note and the store-drop note\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("the value was dropped")),
                Is.True,
                "the store-drop note intervening between the default and the pop survives\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldnull), Is.False,
                "no synthetic null may be emitted for a discarded operand slot\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Pop), Is.False,
                "the discarded value is removed with its pop, not pushed and dropped\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    // The removal pass itself, driven on a hand-built body: labels and handler
    // boundaries land on the first instruction an ISIL op emits, so a target
    // inside a removed range cannot be produced through GenerateIl.
    private static void RunRemoveDiscardedDefaults(MethodDefinition method, MethodDefinition writeLine)
        => typeof(IlGenerator)
            .GetMethod("RemoveDiscardedDefaults", BindingFlags.NonPublic | BindingFlags.Static)!
            .Invoke(null, [method, writeLine]);

    private static (MethodDefinition method, MethodDefinition writeLine) DiscardedDefaultBody(ModuleDefinition module)
    {
        var owner = new TypeDefinition("Tests", "Holder", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var writeLine = new MethodDefinition("WriteLine", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void, [module.CorLibTypeFactory.String]));
        owner.Methods.Add(writeLine);
        var method = new MethodDefinition("M", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(method);
        method.CilMethodBody = new CilMethodBody();
        var il = method.CilMethodBody.Instructions;
        // [0..1] slot note, [2..3] intervening store note, [4] synthetic push,
        // [5] pop, [6] the kept continuation.
        il.Add(CilOpCodes.Ldstr, "Operand slot of type Tests.Opaque filled with a synthetic default value");
        il.Add(CilOpCodes.Call, writeLine);
        il.Add(CilOpCodes.Ldstr, "Store into unknown operand: [r0+8]");
        il.Add(CilOpCodes.Call, writeLine);
        il.Add(CilOpCodes.Ldnull);
        il.Add(CilOpCodes.Pop);
        il.Add(CilOpCodes.Ret);
        return (method, writeLine);
    }

    [Test]
    public void BranchIntoRemovedRangeRetargetsPastIt()
    {
        var module = new ModuleDefinition("Retarget.dll");
        var (method, writeLine) = DiscardedDefaultBody(module);
        var il = method.CilMethodBody!.Instructions;
        // A branch landing on the synthetic push inside the removal range.
        var branch = new CilInstruction(CilOpCodes.Br, new CilInstructionLabel(il[4]));
        il.Insert(0, branch);

        RunRemoveDiscardedDefaults(method, writeLine);

        Assert.Multiple(() =>
        {
            Assert.That(il.Select(i => i.OpCode), Is.EqualTo(new[]
                { CilOpCodes.Br, CilOpCodes.Ldstr, CilOpCodes.Call, CilOpCodes.Ldstr, CilOpCodes.Call, CilOpCodes.Ret }));
            var target = ((CilInstructionLabel)il[0].Operand!).Instruction;
            Assert.That(ReferenceEquals(target, il[^1]), Is.True,
                "the branch is retargeted to the first kept instruction past the removal");
        });
    }

    [Test]
    public void ExceptionHandlerBoundaryIntoRemovedRangeRetargetsPastIt()
    {
        var module = new ModuleDefinition("RetargetEh.dll");
        var (method, writeLine) = DiscardedDefaultBody(module);
        var il = method.CilMethodBody!.Instructions;
        method.CilMethodBody!.ExceptionHandlers.Add(new CilExceptionHandler
        {
            HandlerType = CilExceptionHandlerType.Finally,
            TryStart = new CilInstructionLabel(il[0]),
            TryEnd = new CilInstructionLabel(il[4]), // ends inside the removal range
            HandlerStart = new CilInstructionLabel(il[6]),
            HandlerEnd = new CilInstructionLabel(il[6]),
        });

        RunRemoveDiscardedDefaults(method, writeLine);

        var handler = method.CilMethodBody.ExceptionHandlers[0];
        Assert.Multiple(() =>
        {
            Assert.That(il.Select(i => i.OpCode), Is.EqualTo(new[]
                { CilOpCodes.Ldstr, CilOpCodes.Call, CilOpCodes.Ldstr, CilOpCodes.Call, CilOpCodes.Ret }));
            Assert.That(ReferenceEquals(((CilInstructionLabel)handler.TryEnd!).Instruction, il[^1]),
                Is.True, "the try boundary is retargeted to the first kept instruction past the removal");
        });
    }
}
