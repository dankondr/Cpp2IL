using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// A System.Object slot contract reserved for locals whose manufactured
// System.Boolean claim was vetoed by LocalVariables.TryClaimBoolean. It is the
// object's own context in every emission-relevant respect - same definition,
// same name, same value-type answer - but it is a distinct runtime type, so
// EmitStackCoerce/StackContractSatisfied can refuse a scalar->object coerce
// into exactly these slots: a flag or integer edge reaching one keeps the
// named decompiler-issue note the Boolean-typed slot emitted for the same
// site, while every other System.Object contract keeps the box conversion.
public sealed class BooleanClaimVetoedSlotTypeAnalysisContext(TypeAnalysisContext slot)
    : TypeAnalysisContext(slot.Definition, slot.DeclaringAssembly)
{
    public override string DefaultName => "Object";
    public override string DefaultNamespace => "System";
    public override bool IsValueType => false;
}
