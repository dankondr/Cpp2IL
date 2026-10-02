using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;

namespace Cpp2IL.Core.Tests.Regression;

// LLD's Cortex-A53 erratum-843419 fix (castle-recovery#214): a load/store after an adrp at page offset
// 0xff8/0xffc is moved into a veneer `<insn>; b <branch + 4>` and the method keeps `b veneer` in its place.
// That branch is lifted as the relocated instruction and lifting continues; any other target stays a tail call.
public class ErratumVeneerTests
{
    private const ulong Method = 0x10000;
    private const ulong Veneer = 0x90000;
    private const uint Ret = 0xd65f03c0;
    private const uint MovX0X19 = 0xaa1303e0;
    private const uint LdrX19X19_70 = 0xf9403a73; // ldr x19, [x19, #0x70]
    private const uint AdrpX20NextPage = 0xb0000014; // adrp x20, page + 0x1000
    private const uint LdrX20X20_D8 = 0xf9406e94; // ldr x20, [x20, #0xd8]
    private const uint LdrX0X20 = 0xf9400280; // ldr x0, [x20]

    private static uint B(ulong from, ulong to) => 0x14000000 | (uint)(((long)to - (long)from >> 2) & 0x03ffffff);

    private static List<Instruction> Lift(uint[] method, uint relocated, ulong backTo)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Test",
            app.SystemTypes.SystemObjectType, MethodAttributes.Public | MethodAttributes.Static, []);
        var veneer = new Dictionary<ulong, uint> { [Veneer] = relocated, [Veneer + 4] = B(Veneer + 4, backTo) };
        return new NewArmV8InstructionSet().ConvertInstructions(
            Disassembler.Disassemble(method.SelectMany(BitConverter.GetBytes).ToArray(), Method), context,
            readWord: a => veneer.TryGetValue(a, out var w) ? w : null);
    }

    // b veneer; mov x0, x19; ret
    private static List<Instruction> LiftLoad(uint relocated, ulong backTo)
        => Lift([B(Method, Veneer), MovX0X19, Ret], relocated, backTo);

    [Test]
    public void RelocatedLoadIsLiftedInPlaceOfTheBranch()
    {
        var il = LiftLoad(LdrX19X19_70, Method + 4);

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == OpCode.Call), Is.False, "the veneer branch is not a tail call");
            Assert.That((il[0].OpCode, il[0].NativeAddress), Is.EqualTo((OpCode.Move, Method)));
            Assert.That(il[0].Operands[1], Is.EqualTo(new MemoryOperand(new Register(null, "X19"), addend: 0x70, accessSize: 8)));
            Assert.That(il.Count(i => i.OpCode == OpCode.Return), Is.EqualTo(1));
            Assert.That(il.Any(i => i.NativeAddress == Method + 4), Is.True, "lifting continues after the branch");
        });
    }

    [Test]
    public void RelocatedAdrpRelativeLoadReadsThePage()
    {
        // adrp x20, page; b veneer; ldr x0, [x20]; ret  -- veneer: ldr x20, [x20, #0xd8]; b back
        var il = Lift([AdrpX20NextPage, B(Method + 4, Veneer), LdrX0X20, Ret], LdrX20X20_D8, Method + 8);

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == OpCode.Call), Is.False);
            var relocated = il.Single(i => i.NativeAddress == Method + 4);
            Assert.That(relocated.OpCode, Is.EqualTo(OpCode.Move));
            Assert.That(relocated.Operands[1], Is.EqualTo(new MemoryOperand(addend: 0x11000 + 0xd8, accessSize: 8)));
            Assert.That(il.Any(i => i.NativeAddress == Method + 8), Is.True);
        });
    }

    [Test]
    public void OtherBranchTargetsStayTailCalls()
    {
        uint[] method = [B(Method, Veneer), MovX0X19, Ret];
        var insns = Disassembler.Disassemble(method.SelectMany(BitConverter.GetBytes).ToArray(), Method).ToList();
        foreach (var (relocated, backTo, why) in new (uint, ulong, string)[]
        {
            (LdrX19X19_70, Method + 8, "returns elsewhere"),
            (0x58000080, Method + 4, "ldr literal is PC-relative"),
            (0x10000080, Method + 4, "adr is PC-relative"),
            (B(Veneer, Method + 4), Method + 4, "first instruction is a branch"),
        })
        {
            var veneer = new Dictionary<ulong, uint> { [Veneer] = relocated, [Veneer + 4] = B(Veneer + 4, backTo) };
            Assert.That(NewArmV8InstructionSet.FollowRelocationVeneers(insns, Method, Method + 12,
                a => veneer.TryGetValue(a, out var w) ? w : null), Is.SameAs(insns), why);
        }
    }
}
