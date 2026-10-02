using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.ISIL;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: ISIL→IL emission — a value Cpp2IL cannot recover is
// replaced by a stub that notes the issue and throws. The instruction that
// consumed the value (here the stloc) used to be emitted after the throw:
// unreachable, but il2cpp converts dead code with an empty stack, fails with
// `Stack empty.` and aborts the whole assembly. Nothing unreachable may follow
// the throw, every note stays, and code another branch reaches stays.
public class StubDeadTailTests
{
    [Test]
    public void StubbedOperandLeavesNoConsumerAfterTheThrow()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var module = new ModuleDefinition("StubDeadTail.dll");
        SeedCorLibTypes(app, module, int32, app.SystemTypes.SystemVoidType, app.SystemTypes.SystemBooleanType);
        var pointer = new LocalVariable("pointer", new Register(null, "X8_v1"));
        var flag = new LocalVariable("flag", new Register(null, "flag"), app.SystemTypes.SystemBooleanType);
        var result = new LocalVariable("result", new Register(null, "result")) { Type = int32 };
        var exit = new Instruction(3, OpCode.Return);
        // if (flag) return; result = [pointer + 8]; <a note of its own>; return.
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.ConditionalJump, exit, flag),
            new(1, OpCode.Move, result, new MemoryOperand(pointer, addend: 8, accessSize: 4)),
            new(2, OpCode.IndirectCall, pointer),
            exit], [pointer, flag, result]);

        IlGenerator.GenerateIl(caller, method);

        var body = method.CilMethodBody!;
        var il = body.Instructions;
        var dump = string.Join("\n", il.Select(i => i.ToString()));
        HashSet<CilInstruction> targets = new(ReferenceEqualityComparer.Instance);
        foreach (var instruction in il)
            if (instruction.Operand is CilInstructionLabel { Instruction: { } target })
                targets.Add(target);
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Throw), Is.True, dump);
            for (var k = 0; k < il.Count - 1; k++)
                if (il[k].OpCode == CilOpCodes.Throw)
                    Assert.That(targets.Contains(il[k + 1]), Is.True,
                        $"{il[k + 1]} after the throw is unreachable\n{dump}");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stloc), Is.False,
                "the stub's consumer is dead and not emitted\n" + dump);
            // The never-stored flag's note, the stub's and the dead instruction's.
            Assert.That(il.Count(i => i.OpCode == CilOpCodes.Call), Is.EqualTo(3),
                "every note survives\n" + dump);
            Assert.That(il.Count(i => i.OpCode == CilOpCodes.Ret), Is.EqualTo(1),
                "the return the branch reaches stays\n" + dump);
            Assert.DoesNotThrow(() => body.ComputeMaxStack(), dump);
        });
    }
}
