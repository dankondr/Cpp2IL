using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: compile bucket invalid-conversion (castle-recovery#104).
// Shared-generic code copies a concretely-typed receiver into an argument
// register whose slot keeps the erased instantiation (Dictionary<object,object>).
// Hidden-return sharpening then has to see through that copy; the erased
// destination's own type must not count as use-contract evidence - it echoes
// the same erased instantiation back in a loop. The sharpened receiver type
// also has to fall back to the source's own declared type when sharpening
// finds nothing more concrete.
public class ErasedReceiverSharpeningTests
{
    [Test]
    public void HiddenEnumeratorReturnSharpensThroughErasedArgumentCopy()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var mscorlib = app.AssembliesByName["mscorlib"];
        var dictionary = mscorlib.GetTypeByFullName("System.Collections.Generic.Dictionary`2")!;
        var getEnumerator = dictionary.Methods.Single(method => method.Name == "GetEnumerator");
        var concrete = new GenericInstanceTypeAnalysisContext(dictionary,
            [app.SystemTypes.SystemStringType, app.SystemTypes.SystemObjectType]);
        var erased = new GenericInstanceTypeAnalysisContext(dictionary,
            [app.SystemTypes.SystemObjectType, app.SystemTypes.SystemObjectType]);

        var source = new LocalVariable("source", new Register(null, "source"), concrete);
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"), erased);
        var buffer = new LocalVariable("buffer", new Register(null, "stack_-30"));
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"));

        var method = new InjectedMethodAnalysisContext(
            mscorlib.GetTypeByFullName("System.Object")!, "Probe",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, []);
        var call = new Instruction(2, OpCode.Call, getEnumerator,
            new MemoryOperand(pointer), receiver);
        method.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, pointer, new AddressOf(buffer)),
            new(1, OpCode.Move, receiver, source),
            call,
            new(3, OpCode.Return)]);
        method.Locals = [source, receiver, buffer, pointer];

        LocalVariables.ResolveTypesAndFields(method);

        var result = (LocalVariable)call.Destination!;
        Assert.That(result.HiddenReturnBuffer, Is.SameAs(buffer));
        var produced = (GenericInstanceTypeAnalysisContext)result.Type!;
        Assert.Multiple(() =>
        {
            Assert.That(produced.GenericType.Name, Is.EqualTo("Enumerator"));
            Assert.That(produced.GenericArguments.Select(argument => argument.FullName),
                Is.EqualTo(new[] { "System.String", "System.Object" }));
        });
    }
}
