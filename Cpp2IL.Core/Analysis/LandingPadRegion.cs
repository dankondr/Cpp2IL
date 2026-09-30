using System.Collections.Generic;
using Cpp2IL.Core.ISIL;
using LibCpp2IL;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// One landing pad of a method's unwind table: the code only the unwinder enters.
/// The pad's handler instructions are moved out of the method's normal instruction stream
/// by <see cref="EhRegionPartition"/> and kept here, keyed to the call-site ranges that
/// unwind to them.
/// </summary>
public sealed class LandingPadRegion
{
    /// <summary>The landing pad's entry address (virtual address in the binary).</summary>
    public required ulong PadAddress { get; init; }

    /// <summary>The call-site ranges (native addresses) that unwind to this pad.</summary>
    public List<EhCallSiteInfo> CallSites { get; } = [];

    /// <summary>
    /// The pad's handler-only instructions, in stream order. Shared tails owned by an
    /// earlier pad are absent from a later pad's list.
    /// </summary>
    public List<Instruction> Instructions { get; } = [];
}
