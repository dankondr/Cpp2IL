using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: all-zero literals into value slots (castle-recovery#136).
// A zero literal carries the all-zero bit pattern the binary proves the slot
// held, so default(contract) fills the slot honestly - the exact value a real
// conversion would produce - and no substitution diagnostic is needed.
public class ZeroLiteralSlotDefaultTests
{
    private static InjectedTypeAnalysisContext InjectStruct(ApplicationAnalysisContext app, string name) =>
        new(app.AssembliesByName["mscorlib"], "Tests", name,
            app.SystemTypes.SystemValueTypeType,
            R.TypeAttributes.Public | R.TypeAttributes.Sealed | R.TypeAttributes.SequentialLayout);

    [Test]
    public void ZeroLiteralIntoStructSlotEmitsDefaultWithoutDiagnostic()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var structType = InjectStruct(app, "Point");
        var slot = new LocalVariable("slot", new Register(null, "slot")) { Type = structType };
        var module = new ModuleDefinition("StructSlot.dll");
        SeedCorLibTypes(app, module, structType, app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, slot, new Immediate(0)),
            new(1, OpCode.Return)], [slot]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Initobj), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call), Is.False,
                "a proven-zero slot needs no conversion - the diagnostic call must be gone");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("substituting")), Is.False,
                "the binary proves the slot is zero - no value is being substituted");
        });
    }

    [Test]
    public void NonzeroLiteralIntoStructSlotKeepsSubstitutionDiagnostic()
    {
        // A nonzero literal is not the value the slot proves; the substitution
        // must stay diagnosed.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var structType = InjectStruct(app, "Point");
        var slot = new LocalVariable("slot", new Register(null, "slot")) { Type = structType };
        var module = new ModuleDefinition("StructSlot.dll");
        SeedCorLibTypes(app, module, structType, app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, slot, new Immediate(4)),
            new(1, OpCode.Return)], [slot]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("substituting")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call), Is.True,
                "the diagnostic must be an emitted call, not just a string");
        });
    }
}
