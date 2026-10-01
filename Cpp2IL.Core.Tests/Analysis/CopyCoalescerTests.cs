using System.Linq;
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

    [Test]
    public void VersionsOfOneAddressedSlotShareALocalAcrossASharedGenericType()
    {
        // Two foreach loops reuse one frame slot for their enumerators; the shared finally's
        // Dispose(&slot) typed its version as the shared-generic List<Int32Enum>.Enumerator. It is
        // the same storage as the loops' List<string>.Enumerator, so all versions are one local.
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var list = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var enumerator = list.NestedTypes.Single(type => type.Name.StartsWith("Enumerator"));
        var shared = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Int32Enum")
                     ?? new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "System", "Int32Enum",
                         app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var concreteType = new GenericInstanceTypeAnalysisContext(enumerator, [app.SystemTypes.SystemStringType]);
        var sharedType = new GenericInstanceTypeAnalysisContext(enumerator, [shared]);

        var slot = new Register(7, "stack_-80", 1);
        var first = new LocalVariable("first", slot, concreteType);
        var second = new LocalVariable("second", slot.Copy(2), concreteType);
        var merged = new LocalVariable("merged", slot.Copy(3), sharedType);
        var cfg = new ISILControlFlowGraph([
            new(0, OpCode.CallVoid, new StringLiteral("MoveNext"), new AddressOf(first)),
            new(1, OpCode.CallVoid, new StringLiteral("MoveNext"), new AddressOf(second)),
            new(2, OpCode.CallVoid, new StringLiteral("Dispose"), new AddressOf(merged)),
            new(3, OpCode.Return)]);

        CopyCoalescer.Run(cfg);

        var receivers = cfg.Instructions.Where(i => i.OpCode == OpCode.CallVoid)
            .Select(i => ((AddressOf)i.Operands[1]).Target).Distinct().ToList();
        Assert.That(receivers, Has.Count.EqualTo(1));
        Assert.That(((LocalVariable)receivers[0]).Type!.FullName, Is.EqualTo(concreteType.FullName));
    }
}
