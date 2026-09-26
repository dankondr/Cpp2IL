using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.ISIL;

// An explicit managed cast backed by a recovered native type guard.
public sealed class ReferenceCast(LocalVariable value, TypeAnalysisContext type, bool nullOnFailure = false) : IOperand
{
    public LocalVariable Value { get; } = value;
    public TypeAnalysisContext Type { get; } = type;
    public bool NullOnFailure { get; } = nullOnFailure;

    public override string ToString() => $"{(NullOnFailure ? "isinst" : "cast")}<{Type.FullName}>({Value})";
}
