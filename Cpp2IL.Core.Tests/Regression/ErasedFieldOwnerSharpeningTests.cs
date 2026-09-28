using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: compile bucket invalid-conversion (castle-recovery#115).
// A field reference materialized while its owner local still carried the erased
// shared instantiation keeps it even though the owner emits as the sharpened
// instantiation: `Enumerator<object,object>::current` types the destination
// `KeyValuePair<object,object>` while the emitted `get_Current` returns
// `KeyValuePair<string,int>` - a stloc the verifier rejects. The field must be
// re-resolved onto the instantiation the local actually emits as.
public class ErasedFieldOwnerSharpeningTests
{
    [Test]
    public void EnumeratorCurrentFieldResolvesOnSharpenedOwner()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var mscorlib = app.AssembliesByName["mscorlib"];
        var dictionary = mscorlib.GetTypeByFullName("System.Collections.Generic.Dictionary`2")!;
        var enumerator = mscorlib.GetTypeByFullName("System.Collections.Generic.Dictionary`2+Enumerator")!;
        var pair = mscorlib.GetTypeByFullName("System.Collections.Generic.KeyValuePair`2")!;
        var getEnumerator = dictionary.Methods.Single(method => method.Name == "GetEnumerator");

        var concreteDictionary = new GenericInstanceTypeAnalysisContext(dictionary,
            [app.SystemTypes.SystemStringType, app.SystemTypes.SystemInt32Type]);
        var erasedEnumerator = new GenericInstanceTypeAnalysisContext(enumerator,
            [app.SystemTypes.SystemObjectType, app.SystemTypes.SystemObjectType]);
        var erasedPair = new GenericInstanceTypeAnalysisContext(pair,
            [app.SystemTypes.SystemObjectType, app.SystemTypes.SystemObjectType]);

        // The open generic def's metadata field offsets are all 0; find the real
        // offset of the enumerator's `current` field through the same instance-layout
        // walk the resolver uses.
        var accessSize = (int)(2 * app.Binary.PointerSizeBytes);
        var currentOffset = -1;
        for (var candidate = 0; candidate < 128; candidate += 4)
            if (MetadataResolver.FindInstanceFieldPathAtOffset(erasedEnumerator, candidate, accessSize)
                    is { Field.Name: "current" })
                currentOffset = candidate;
        Assert.That(currentOffset, Is.GreaterThanOrEqualTo(0),
            () => "the current field must resolve on the erased instantiation; fields="
                + string.Join(",", enumerator.Fields.Select(f => $"{f.Name}@{f.Offset}:{f.FieldType.FullName}")));
        var staleField = new ConcreteGenericFieldAnalysisContext(
            enumerator.Fields.Single(field => field.Name == "current"), erasedEnumerator);

        var source = new LocalVariable("source", new Register(null, "source"), concreteDictionary);
        var owner = new LocalVariable("owner", new Register(null, "owner"), erasedEnumerator);
        var current = new LocalVariable("current", new Register(null, "current"), erasedPair);

        var method = new InjectedMethodAnalysisContext(
            mscorlib.GetTypeByFullName("System.Object")!, "Probe",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, []);
        method.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Call, getEnumerator, owner, source),
            new(1, OpCode.Move, current,
                new FieldReference(staleField, owner, currentOffset, [], accessSize)),
            new(2, OpCode.Return)]);
        method.Locals = [source, owner, current];

        LocalVariables.ResolveTypesAndFields(method);

        var produced = (GenericInstanceTypeAnalysisContext)current.Type!;
        Assert.Multiple(() =>
        {
            Assert.That(produced.GenericType.Name, Is.EqualTo("KeyValuePair`2"));
            Assert.That(produced.GenericArguments.Select(argument => argument.FullName),
                Is.EqualTo(new[] { "System.String", "System.Int32" }));
        });
    }
}
