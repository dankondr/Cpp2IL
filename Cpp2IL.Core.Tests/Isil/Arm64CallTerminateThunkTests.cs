using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Il2CppApiFunctions;
using Disarm;

namespace Cpp2IL.Core.Tests.Isil;

// Structural recognition of the __clang_call_terminate comdat thunk:
// [stp x29, x30, [sp, #-N]!]? [mov x29, sp]? bl __cxa_begin_catch;
// bl _ZSt9terminatev; [brk]? — the entire function extent, noreturn.
public class Arm64CallTerminateThunkTests
{
    private const ulong Base = 0x1000;
    private static ulong Addr(int index) => Base + (ulong)index * 4;

    private const uint StpFpLrPre = 0xa9bf7bfd; // stp x29, x30, [sp, #-16]!
    private const uint MovFpSp = 0x910003fd; // mov x29, sp
    private const uint Brk = 0xd4200020; // brk #0x1
    private const uint Ret = 0xd65f03c0;
    private const uint MovX0X1 = 0xaa0103e0;

    private static uint Bl(ulong pc, ulong target) =>
        0x94000000 | (uint)(((target - pc) >> 2) & 0x03ffffff);

    private static List<Arm64Instruction> Disasm(uint[] words) =>
        Disassembler.Disassemble(Blob(words), Base).ToList();

    private static byte[] Blob(uint[] words)
    {
        var bytes = new byte[words.Length * 4];
        for (var i = 0; i < words.Length; i++)
            BitConverter.GetBytes(words[i]).CopyTo(bytes, i * 4);
        return bytes;
    }

    private static Func<ulong, uint?> Reader(uint[] words) =>
        address => address >= Base && address < Base + (ulong)words.Length * 4
            ? words[(address - Base) / 4]
            : null;

    private const ulong BeginCatch = 0x2000;
    private const ulong Terminate = 0x3000;

    private static string? Resolve(ulong target) =>
        target == BeginCatch ? "__cxa_begin_catch"
            : target == Terminate ? "_ZSt9terminatev" : null;

    private static bool Match(uint[] words, int start = 0, int? end = null,
        IReadOnlySet<ulong>? callTargets = null)
    {
        var disassembly = Disasm(words);
        return NewArm64KeyFunctionAddresses.TryMatchCallTerminateThunk(
            disassembly, start, end ?? disassembly.Count,
            callTargets ?? new HashSet<ulong> { Base },
            Reader(words), Resolve);
    }

    [Test]
    public void ExactComdatThunkResolves() =>
        Assert.That(Match(
        [
            StpFpLrPre, MovFpSp,
            Bl(Addr(2), BeginCatch), Bl(Addr(3), Terminate),
        ]), Is.True);

    [Test]
    public void ThunkWithTrapWordResolves() =>
        Assert.That(Match(
        [
            StpFpLrPre, MovFpSp,
            Bl(Addr(2), BeginCatch), Bl(Addr(3), Terminate), Brk,
        ]), Is.True);

    [Test]
    public void ThunkWithoutPrologueResolves() =>
        Assert.That(Match([Bl(Addr(0), BeginCatch), Bl(Addr(1), Terminate)]), Is.True);

    [Test]
    public void FunctionThatContinuesAfterTheCallsDoesNotResolve()
        // A real function may open with the same calls but keep going: the
        // extent must be exactly the thunk shape.
        => Assert.That(Match(
        [
            StpFpLrPre, MovFpSp,
            Bl(Addr(2), BeginCatch), Bl(Addr(3), Terminate),
            MovX0X1, Ret,
        ]), Is.False);

    [Test]
    public void CallBetweenTheTwoBlInstructionsDoesNotResolve() =>
        Assert.That(Match(
        [
            Bl(Addr(0), BeginCatch), MovX0X1, Bl(Addr(2), Terminate),
        ]), Is.False);

    [Test]
    public void WrongCalleeDoesNotResolve() =>
        Assert.That(Match([Bl(Addr(0), BeginCatch), Bl(Addr(1), 0x4000)]), Is.False);

    [Test]
    public void ReorderedCallsDoNotResolve() =>
        Assert.That(Match([Bl(Addr(0), Terminate), Bl(Addr(1), BeginCatch)]), Is.False);

    [Test]
    public void NonFunctionStartDoesNotResolve()
    {
        // Leading fall-through instruction means index 1 is not a function start.
        var words = new[]
        {
            MovX0X1,
            Bl(Addr(1), BeginCatch), Bl(Addr(2), Terminate),
        };
        var disassembly = Disasm(words);

        Assert.That(NewArm64KeyFunctionAddresses.TryMatchCallTerminateThunk(
            disassembly, 1, disassembly.Count, new HashSet<ulong>(),
            Reader(words), Resolve), Is.False);
    }

    [Test]
    public void AllowedImportNamesCoverEhRuntime()
    {
        foreach (var name in new[]
                 {
                     "__cxa_allocate_exception", "__cxa_throw", "__cxa_end_catch",
                     "__cxa_begin_catch", "__cxa_get_exception_ptr",
                     "__cxa_rethrow", "_Unwind_Resume", "_ZSt9terminatev",
                 })
            Assert.That(NewArm64KeyFunctionAddresses.IsAllowedVeneerImportName(name), Is.True, name);
        Assert.That(NewArm64KeyFunctionAddresses.IsAllowedVeneerImportName("memcpy"), Is.False);
        Assert.That(NewArm64KeyFunctionAddresses.IsAllowedVeneerImportName("fopen"), Is.False);
    }
}
