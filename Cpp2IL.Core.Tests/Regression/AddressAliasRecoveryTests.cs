using System.Collections.Generic;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: dataflow — object-address alias folding (#38, 95fb169d).
// ARM64 lifting leaves an alias local (alias = root + displacement) that later
// memory accesses index off. ResolveFieldOffsets folds the alias back into the
// base only when the folded [root + offset] resolves to a known access shape:
// an instance field at that offset, the array length slot, or an element edge.
public class AddressAliasRecoveryTests
{
    private static InjectedMethodAnalysisContext Method(TypeAnalysisContext ownerType,
        ApplicationAnalysisContext app, List<Instruction> instructions)
    {
        var method = new InjectedMethodAnalysisContext(ownerType, "Read",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, []);
        method.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        return method;
    }

    [Test]
    public void ArrayLengthLoadThroughAddressAlias()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var array = new LocalVariable("array", new Register(null, "array"),
            new SzArrayTypeAnalysisContext(app.SystemTypes.SystemInt32Type));
        var alias = new LocalVariable("alias", new Register(null, "alias"));
        var length = new LocalVariable("length", new Register(null, "length"));
        // alias = array - 8; [alias + 32] folds to [array + 24], the 64-bit length slot.
        var load = new Instruction(1, OpCode.Move, length,
            new MemoryOperand(alias, addend: 32, accessSize: 4));
        var method = Method(ownerType, app, [
            new(0, OpCode.Add, alias, array, new Immediate(-8)), load, new(2, OpCode.Return)]);

        MetadataResolver.ResolveFieldOffsets(method);
        ArrayRecovery.Run(method);

        Assert.Multiple(() =>
        {
            Assert.That(load.Operands[1], Is.TypeOf<ArrayLength>(),
                () => load.Operands[1]?.ToString() ?? "<null>");
            Assert.That(((ArrayLength)load.Operands[1]).Array, Is.SameAs(array));
        });
    }

    [Test]
    public void IndexedArrayLoadThroughAddressAlias()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var array = new LocalVariable("array", new Register(null, "array"),
            new SzArrayTypeAnalysisContext(app.SystemTypes.SystemInt32Type));
        var alias = new LocalVariable("alias", new Register(null, "alias"));
        var index = new LocalVariable("index", new Register(null, "index"),
            app.SystemTypes.SystemInt32Type);
        var element = new LocalVariable("element", new Register(null, "element"));
        // alias = array + 32; [alias + index*4] folds to array[index] (4-byte elements).
        var load = new Instruction(1, OpCode.Move, element,
            new MemoryOperand(alias, index, addend: 0, scale: 4, accessSize: 4));
        var method = Method(ownerType, app, [
            new(0, OpCode.Add, alias, array, new Immediate(32)), load, new(2, OpCode.Return)]);

        MetadataResolver.ResolveFieldOffsets(method);
        ArrayRecovery.Run(method);

        Assert.Multiple(() =>
        {
            Assert.That(load.Operands[1], Is.TypeOf<ArrayAccess>(),
                () => load.Operands[1]?.ToString() ?? "<null>");
            var access = (ArrayAccess)load.Operands[1];
            Assert.That(access.Array, Is.SameAs(array));
            Assert.That(access.Index, Is.SameAs(index));
        });
    }

    [Test]
    public void TypedAddressAliasStillFoldsToField()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var field = new InjectedFieldAnalysisContext("items", app.SystemTypes.SystemObjectType,
            FieldAttributes.Public, ownerType, 56);
        ownerType.Fields.Add(field);
        var owner = new LocalVariable("owner", new Register(null, "owner"), ownerType);
        // A lifted alias can carry a leftover managed type; the type is not the proof,
        // the resolvable [root + offset] shape is.
        var alias = new LocalVariable("alias", new Register(null, "alias"), ownerType);
        var result = new LocalVariable("result", new Register(null, "result"));
        var load = new Instruction(1, OpCode.Move, result,
            new MemoryOperand(alias, accessSize: 8));
        var method = Method(ownerType, app, [
            new(0, OpCode.Add, alias, owner, new Immediate(56)), load, new(2, OpCode.Return)]);

        MetadataResolver.ResolveFieldOffsets(method);

        Assert.Multiple(() =>
        {
            Assert.That(load.Operands[1], Is.TypeOf<FieldReference>(),
                () => load.Operands[1]?.ToString() ?? "<null>");
            Assert.That(((FieldReference)load.Operands[1]).Field, Is.SameAs(field));
        });
    }
}
