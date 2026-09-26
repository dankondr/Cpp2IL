using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.ISIL;

public class FieldReference(FieldAnalysisContext field, LocalVariable local, int offset,
    IReadOnlyList<FieldAnalysisContext>? containers = null, int accessSize = 0) : IOperand
{
    public FieldAnalysisContext Field = field;
    public LocalVariable Local = local;
    public int Offset = offset;
    public IReadOnlyList<FieldAnalysisContext> Containers = containers ?? [];
    public int AccessSize = accessSize;

    public override string ToString() => $"{Local.Name}.{string.Join(".", Containers.Select(f => f.Name).Append(Field.Name))} ({Field.FieldType.FullName})";
}

public class SelectedFieldReference(LocalVariable selector,
    IReadOnlyList<(long Value, FieldReference Field)> choices) : IOperand
{
    public LocalVariable Selector = selector;
    public IReadOnlyList<(long Value, FieldReference Field)> Choices = choices;
    public TypeAnalysisContext FieldType => Choices[0].Field.Field.FieldType;

    public override string ToString() =>
        $"select({Selector.Name}: {string.Join(", ", Choices.Select(c => $"{c.Value} => {c.Field}"))})";
}

// A field within a value-type array element (`array[index].field`).
public class ArrayElementFieldReference(LocalVariable array, IOperand index, FieldAnalysisContext field) : IOperand
{
    public LocalVariable Array = array;
    public IOperand Index = index;
    public FieldAnalysisContext Field = field;

    public override string ToString() => $"{Array.Name}[{Index}].{Field.Name} ({Field.FieldType.FullName})";
}
