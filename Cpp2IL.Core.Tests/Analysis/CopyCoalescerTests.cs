using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class CopyCoalescerTests
{
    [Test]
    public void RewritesReceiverInsideAddressedField()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var valueType = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.ValueType")!;
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Value",
            valueType, TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout);
        var field = new InjectedFieldAnalysisContext("value", app.SystemTypes.SystemInt32Type,
            FieldAttributes.Public, ownerType, 0);
        ownerType.Fields.Add(field);

        var slot = new Register(7, "stack", 1);
        var loaded = new LocalVariable("loaded", slot, ownerType);
        var alias = new LocalVariable("alias", slot.Copy(2), ownerType);
        var load = new Instruction(0, OpCode.Move, loaded, new Immediate(0));
        var copy = new Instruction(1, OpCode.Move, alias, loaded);
        var call = new Instruction(2, OpCode.CallVoid, new StringLiteral("consume"),
            new AddressOf(new FieldReference(field, alias, 0)));
        var cfg = new ISILControlFlowGraph([load, copy, call, new Instruction(3, OpCode.Return)]);

        CopyCoalescer.Run(cfg);

        var addressedField = (FieldReference)((AddressOf)call.Operands[1]).Target;
        Assert.That(addressedField.Local, Is.SameAs(load.Destination));
    }
}
