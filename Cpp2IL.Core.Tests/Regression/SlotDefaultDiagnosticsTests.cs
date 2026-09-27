using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: default-substitution diagnostics (castle-recovery#90).
// A slot load that can never satisfy its contract substitutes default(contract)
// or a fabricated local address. These substitutions used to be silent, so the
// method read as clean output; every such site must now emit the
// codeverify-visible decompiler-issue call (ldstr <Diagnostic> + call) that
// counts the method as incomplete.
public class SlotDefaultDiagnosticsTests
{
    private static InjectedTypeAnalysisContext InjectStruct(ApplicationAnalysisContext app, string name) =>
        new(app.AssembliesByName["mscorlib"], "Tests", name,
            app.SystemTypes.SystemValueTypeType,
            R.TypeAttributes.Public | R.TypeAttributes.Sealed | R.TypeAttributes.SequentialLayout);

    [Test]
    public void UnloadableOperandIntoStructSlotEmitsSubstitutionDiagnostic()
    {
        // A literal can never fill a non-primitive value-type slot, so
        // LoadOperandIntoSlot substitutes default(Struct) for it.
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
                    && i.Operand is string text && text.Contains("synthetic default")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call), Is.True,
                "the diagnostic must be an emitted call, not just a string");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Initobj), Is.True,
                "the substituted slot still carries the struct default");
        });
    }

    [Test]
    public void LiteralIntoRefSlotEmitsSubstitutionDiagnostic()
    {
        // A literal cannot produce a managed pointer; the ref/out slot gets the
        // address of a fresh zero-initialized local.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var structType = InjectStruct(app, "PointRef");
        var slot = new LocalVariable("slot", new Register(null, "slot"))
            { Type = new ByRefTypeAnalysisContext(structType) };
        var module = new ModuleDefinition("RefSlot.dll");
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
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldloca), Is.True,
                "the substituted ref slot still carries a local address");
        });
    }
}
