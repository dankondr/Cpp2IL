namespace Cpp2IL.Core.ISIL;

/// <param name="ProvenBytes">
/// Bytes of <paramref name="Value"/> this operand provably describes - a 32-bit
/// quantity claims four, a whole-register literal eight. Null means the
/// producing instruction recorded no provenance. Provenance is metadata, not
/// identity: two immediates with the same value remain equal under
/// <see cref="Equals(Immediate)"/>.
/// </param>
public readonly record struct Immediate(long Value, int? ProvenBytes = null) : IOperand
{
    public ulong UnsignedValue => unchecked((ulong)Value);

    // Without a recorded count the value's own width is the only evidence: a
    // constant too wide for a W register needed an X-register write, anything
    // narrower may be a folded movk's residue and proves only four bytes.
    public int EffectiveProvenBytes => ProvenBytes ?? (UnsignedValue > uint.MaxValue ? 8 : 4);

    public bool Equals(Immediate other) => Value == other.Value;

    public override int GetHashCode() => Value.GetHashCode();

    public override string ToString() => Value.ToString();
}
