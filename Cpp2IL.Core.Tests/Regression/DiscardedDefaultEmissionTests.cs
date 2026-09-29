using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

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
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldnull), Is.False,
                "no synthetic null may be emitted for a discarded operand slot\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Pop), Is.False,
                "the discarded value is removed with its pop, not pushed and dropped\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
        });
    }
}
