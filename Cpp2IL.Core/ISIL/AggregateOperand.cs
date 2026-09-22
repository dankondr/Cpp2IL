using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.ISIL;

/// <summary>Ordered, typed ABI lanes for an ARM64 homogeneous float aggregate.</summary>
public sealed class AggregateOperand : LocalVariable
{
    public AggregateOperand(TypeAnalysisContext aggregateType, IReadOnlyList<IOperand> lanes)
        : base($"aggregate_{aggregateType.Name}", new Register(null, $"aggregate_{aggregateType.FullName}"), aggregateType)
    {
        if (lanes.Count is < 2 or > 4)
            throw new ArgumentOutOfRangeException(nameof(lanes), lanes.Count, "HFA aggregates must contain 2..4 lanes.");

        AggregateType = aggregateType;
        ElementType = aggregateType.Fields.First(field => !field.IsStatic).FieldType;
        ElementWidth = ElementType == aggregateType.AppContext.SystemTypes.SystemSingleType ? 4 : 8;
        Lanes = lanes.ToList();
    }

    public TypeAnalysisContext AggregateType { get; }
    public TypeAnalysisContext ElementType { get; }
    public int ElementWidth { get; }
    public List<IOperand> Lanes { get; private set; }
    public bool IsAggregateParameter { get; set; }

    public void ReplaceLanes(IEnumerable<IOperand> lanes) => Lanes = lanes.ToList();

    public override string ToString() => $"{AggregateType.FullName}[{string.Join(", ", Lanes)}]";
}
