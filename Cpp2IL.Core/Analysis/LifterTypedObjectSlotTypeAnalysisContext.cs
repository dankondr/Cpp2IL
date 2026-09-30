using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// A System.Object slot contract that comes only from Cpp2IL's own typing -
// a local whose recovered type fell back to object - and not from declared
// metadata (a signature parameter or return, a field, an array element). It
// is the object's own context in every emission-relevant respect - same
// definition, same name, same value-type answer - but it is a distinct
// runtime type, so EmitStackCoerce can tell a fabricated-by-us object slot
// apart from one the binary declared: an unproven scalar edge into a lifter
// slot keeps the prior emission and the named note (throwing would leave the
// register-reuse local unassigned), while an edge into declared metadata gets
// the note and the honest stop.
public sealed class LifterTypedObjectSlotTypeAnalysisContext(TypeAnalysisContext slot)
    : TypeAnalysisContext(slot.Definition, slot.DeclaringAssembly)
{
    public override string DefaultName => "Object";
    public override string DefaultNamespace => "System";
    public override bool IsValueType => false;
}
