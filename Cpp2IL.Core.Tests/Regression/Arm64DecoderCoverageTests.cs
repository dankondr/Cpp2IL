using System;
using System.Linq;
using Disarm;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: parser — the vendored ARM64 decoder pin (#16/#47).
// Every word below is an encoding the pre-fork Disarm release could not decode;
// each was verified against LLVM 20 disassembly with operand-level checks in
// vendor/Disarm/Disarm.Tests/DecoderRegressionTests.cs. Mnemonics are compared
// by name so this file also compiles against the unpatched decoder.
public class Arm64DecoderCoverageTests
{
    private static Arm64Instruction Decode(uint word)
        => Disassembler.Disassemble(BitConverter.GetBytes(word), 0).Single();

    [TestCase(0x0F080420u, "SSHR")]   // sshr v0.8b, v1.8b, #8 — SIMD shift by immediate
    [TestCase(0x0F08A420u, "SSHLL")]  // sshll v0.8h, v1.8b, #0 — widening SIMD shift
    [TestCase(0x0E31B820u, "ADDV")]   // addv b0, v1.8b — across-lanes reduce
    [TestCase(0x0E050020u, "TBL")]    // tbl v0.8b, {v0.16b}, v1.8b — table lookup
    [TestCase(0x0D000120u, "ST1")]    // st1 {v0.b}[0], [x1] — single-element lane store
    [TestCase(0x0D40C120u, "LD1R")]   // ld1r {v0.8b}, [x1] — lane replicate load
    [TestCase(0xC8A07C20u, "CAS")]    // cas x0, x0, [x1] — LSE compare-and-swap
    [TestCase(0x38200020u, "LDADDB")] // ldaddb w0, w0, [x1] — LSE atomic add
    public void DecoderResolvesPatchedEncodings(uint word, string expected)
        => Assert.That(Decode(word).Mnemonic.ToString(), Is.EqualTo(expected), $"0x{word:X8}");
}
