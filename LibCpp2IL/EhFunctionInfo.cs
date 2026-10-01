using System.Collections.Generic;

namespace LibCpp2IL;

/// <summary>
/// One call-site range of a function's unwind info: code in [Start, Start + Length) unwinds
/// to the landing pad. All values are virtual addresses in the binary; Action is the LSDA
/// action-table index the unwinder dispatches on.
/// </summary>
public sealed record EhCallSiteInfo(ulong Start, ulong Length, ulong LandingPad, ulong Action)
{
    public ulong End => Start + Length;

    // Null means the action/type table could not be decoded; it is not proof of cleanup.
    public IReadOnlyList<EhActionInfo>? Actions { get; init; }
}

// Positive filters select a C++ RTTI entry, zero is cleanup, negative filters are
// exception specifications. TypeInfo is null when the entry could not be resolved.
public sealed record EhActionInfo(long Filter, ulong? TypeInfo);

/// <summary>
/// Unwind-table information for one function: its true extent in the binary and, when the
/// compiler emitted cleanup or handler code for it, the call-site ranges that unwind into
/// each of its landing pads.
/// </summary>
public sealed class EhFunctionInfo
{
    public required ulong Start { get; init; }

    /// <summary>
    /// The function's byte extent, from its frame description entry. A method body ends
    /// here, not at the next metadata entry's start.
    /// </summary>
    public required ulong Size { get; init; }

    public ulong End => Start + Size;

    /// <summary>
    /// Call-site ranges that unwind to a landing pad, in table order. Ranges whose unwind
    /// escapes the function entirely (no landing pad) are not listed.
    /// </summary>
    public List<EhCallSiteInfo> CallSites { get; } = [];

    public bool HasLandingPads => CallSites.Count != 0;
}
