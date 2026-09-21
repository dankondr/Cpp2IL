using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.ISIL;

// An explicit managed cast backed by a recovered native type guard.
public sealed class ReferenceCast(LocalVariable value, TypeAnalysisContext type) : IOperand
{
    public LocalVariable Value { get; } = value;
    public TypeAnalysisContext Type { get; } = type;

    public override string ToString() => $"cast<{Type.FullName}>({Value})";
}
