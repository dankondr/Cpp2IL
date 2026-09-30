using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: landing pads from the unwind tables (castle-recovery#206). The
// unwinder's entry points are the pads of .gcc_except_table; code reachable only from a
// pad is handler code and is split out of the instruction stream before the control-flow
// graph is built, so it is never lifted as a continuation of the normal path. Every pad
// leaves one diagnostic naming its address until its region shape is proven.
public class EhRegionPartitionTests
{
    private static ApplicationAnalysisContext App => Cpp2IlApi.CurrentAppContext!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    private static InjectedMethodAnalysisContext NewMethod(EhFunctionInfo? unwind)
    {
        var owner = new InjectedTypeAnalysisContext(App.AssembliesByName["mscorlib"], "Tests", "Owner",
            App.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Class);
        var method = owner.InjectMethodContext("M", App.SystemTypes.SystemVoidType,
            System.Reflection.MethodAttributes.Public, []);
        method.ConvertedIsil = [];
        method.AnalysisWarnings = [];
        method.UnwindInfo = unwind;
        return method;
    }

    private static EhFunctionInfo Unwind(ulong start, ulong size,
        params (ulong Start, ulong Length, ulong Pad, ulong Action)[] sites)
    {
        var info = new EhFunctionInfo { Start = start, Size = size };
        foreach (var site in sites)
            info.CallSites.Add(new EhCallSiteInfo(site.Start, site.Length, site.Pad, site.Action));
        return info;
    }

    private static Instruction At(ulong nativeAddress, int index, OpCode opCode, params IOperand[] operands)
        => new(index, opCode, new List<IOperand>(operands)) { NativeAddress = nativeAddress };

    // Normal path, then a landing pad the unwinder alone enters: the pad's instructions move
    // to a region, the stream keeps the normal path, one diagnostic names the pad's address.
    [Test]
    public void PadOnlyCodeMovesToARegionAndIsDiagnosed()
    {
        var method = NewMethod(Unwind(0x1000, 0x120, (0x1000, 0x0C, 0x2000, 1)));
        method.ConvertedIsil!.AddRange(new List<Instruction>
        {
            At(0x1000, 0, OpCode.Move, new Register(null, "X0"), new Register(null, "X1")),
            At(0x1004, 1, OpCode.CallVoid, new Immediate(0x9999)),
            At(0x1008, 2, OpCode.Return),
            // Landing pad at 0x2000: X0 is the exception object here.
            At(0x2000, 3, OpCode.Move, new Register(null, "X19"), new Register(null, "X0")),
            At(0x2004, 4, OpCode.CallVoid, new Immediate(0x8888)),
            At(0x2008, 5, OpCode.Return),
        });

        EhRegionPartition.Partition(method);

        Assert.That(method.ConvertedIsil, Has.Count.EqualTo(3));
        Assert.That(method.ConvertedIsil!.Select(i => i.NativeAddress),
            Is.EqualTo(new ulong[] { 0x1000, 0x1004, 0x1008 }));
        Assert.That(method.ConvertedIsil[2].Index, Is.EqualTo(2), "kept instructions are re-indexed");

        var region = method.LandingPadRegions.Single();
        Assert.That(region.PadAddress, Is.EqualTo(0x2000));
        Assert.That(region.Instructions.Select(i => i.NativeAddress),
            Is.EqualTo(new ulong[] { 0x2000, 0x2004, 0x2008 }));
        Assert.That(region.CallSites.Single().Start, Is.EqualTo(0x1000));

        Assert.That(method.AnalysisWarnings, Has.Count.EqualTo(1));
        Assert.That(method.AnalysisWarnings[0], Does.Contain("0x2000"));
    }

    // A handler whose tail jumps back into the normal path (a catch rejoining the method):
    // the merge point is normal code and stays; only the pad's own code is dropped.
    [Test]
    public void HandlerFallingBackIntoNormalCodeKeepsTheMergePoint()
    {
        var method = NewMethod(Unwind(0x1000, 0x100, (0x1000, 0x08, 0x2000, 1)));
        var merge = At(0x1010, 4, OpCode.Return);
        method.ConvertedIsil!.AddRange(new List<Instruction>
        {
            At(0x1000, 0, OpCode.Move, new Register(null, "X0"), new Register(null, "X1")),
            At(0x1004, 1, OpCode.ConditionalJump, merge, new Register(null, "XZR")),
            // Pad at 0x2000 runs its handler then merges back at 0x1010.
            At(0x2000, 2, OpCode.Move, new Register(null, "X19"), new Register(null, "X0")),
            At(0x2004, 3, OpCode.Jump, merge),
            merge,
        });

        EhRegionPartition.Partition(method);

        Assert.That(method.ConvertedIsil!.Select(i => i.NativeAddress),
            Is.EqualTo(new ulong[] { 0x1000, 0x1004, 0x1010 }), "the merge point stays on the normal path");
        var region = method.LandingPadRegions.Single();
        Assert.That(region.Instructions.Select(i => i.NativeAddress),
            Is.EqualTo(new ulong[] { 0x2000, 0x2004 }));
    }

    // A machine branch to the pad's address is normal control flow sharing the block: the
    // code stays in the stream. The pad is still diagnosed - no region shape is proven.
    [Test]
    public void NormalJumpOntoPadAddressKeepsTheCode()
    {
        var method = NewMethod(Unwind(0x1000, 0x100, (0x1000, 0x08, 0x2000, 1)));
        var shared = At(0x2000, 3, OpCode.Move, new Register(null, "X0"), new Register(null, "X1"));
        method.ConvertedIsil!.AddRange(new List<Instruction>
        {
            At(0x1000, 0, OpCode.ConditionalJump, shared, new Register(null, "XZR")),
            At(0x1004, 1, OpCode.Move, new Register(null, "X0"), new Register(null, "X2")),
            At(0x1008, 2, OpCode.Return),
            shared,
            At(0x2004, 4, OpCode.Return),
        });

        EhRegionPartition.Partition(method);

        Assert.That(method.ConvertedIsil, Has.Count.EqualTo(5), "nothing is dropped");
        Assert.That(method.LandingPadRegions.Single().Instructions, Is.Empty);
        Assert.That(method.AnalysisWarnings, Has.Count.EqualTo(1));
        Assert.That(method.AnalysisWarnings[0], Does.Contain("0x2000"));
    }

    // A pad whose instruction never made it into the stream still gets a region and its
    // diagnostic: the unproven pad must stay visible.
    [Test]
    public void PadWithoutLiftedCodeStillDiagnoses()
    {
        var method = NewMethod(Unwind(0x1000, 0x10, (0x1000, 0x08, 0x3000, 1)));
        method.ConvertedIsil!.AddRange(new List<Instruction>
        {
            At(0x1000, 0, OpCode.Move, new Register(null, "X0"), new Register(null, "X1")),
            At(0x1004, 1, OpCode.Return),
        });

        EhRegionPartition.Partition(method);

        Assert.That(method.ConvertedIsil, Has.Count.EqualTo(2));
        Assert.That(method.LandingPadRegions.Single().PadAddress, Is.EqualTo(0x3000));
        Assert.That(method.AnalysisWarnings.Single(), Does.Contain("0x3000"));
    }

    // Without unwind information the stream is untouched, exactly as a binary without the
    // sections lifts today.
    [Test]
    public void NoUnwindInfoLeavesTheStreamAlone()
    {
        var method = NewMethod(unwind: null);
        method.ConvertedIsil!.AddRange(new List<Instruction>
        {
            At(0x1000, 0, OpCode.Move, new Register(null, "X0"), new Register(null, "X1")),
            At(0x2000, 1, OpCode.CallVoid, new Immediate(0x8888)),
            At(0x2004, 2, OpCode.Return),
        });

        EhRegionPartition.Partition(method);

        Assert.That(method.ConvertedIsil, Has.Count.EqualTo(3));
        Assert.That(method.LandingPadRegions, Is.Empty);
        Assert.That(method.AnalysisWarnings, Is.Empty);
    }
}
