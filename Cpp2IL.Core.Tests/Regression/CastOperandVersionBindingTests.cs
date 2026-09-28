using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: compile bucket CS0039 (castle-recovery#137). A cast operand must
// carry the type the binary actually proves for the value it casts; when propagation
// invents a type for it upstream of SSA, the emitter produces statically impossible
// `as` conversions. Two binding bugs fed invented types into the operand:
//
//  - A reference-array element load `ld [base + ElementsOffset]` whose base is pointer
//    arithmetic (`Add(array, scaled index)`), not the array local itself, fell through
//    the element-typing rule. The loaded local stayed untyped, picked up an unrelated
//    type by register reuse, and the `as` bound to it failed statically.
//    ArrayRecovery proves the same `Add(array, scaled index)` shape later, after typing.
//
//  - PropagatePhi backward-typed every untyped phi input to the result's joined type,
//    including inputs produced by a copy or another merge. Those locals carry the value
//    their own producer proves; stamping them asserts a type the binary never proves
//    (a register reused upstream for an unrelated value joins against `this`, the input
//    is stamped `this`'s type, and `input as T` fails statically).
public class CastOperandVersionBindingTests
{
    [Test]
    public void PointerArithmeticElementLoadBindsArrayElementType()
    {
        // `Move loaded, [Add(array, scaledIndex) + ElementsOffset]` is the element load
        // ArrayRecovery later rewrites to an ArrayAccess - the loaded local is a T.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var elementType = app.SystemTypes.SystemStringType;
        var array = new LocalVariable("array", new Register(8, "x8"))
            { Type = new SzArrayTypeAnalysisContext(elementType) };
        var scaledIndex = new LocalVariable("scaledIndex", new Register(19, "x19"));
        var pointer = new LocalVariable("pointer", new Register(20, "x20"));
        var loaded = new LocalVariable("loaded", new Register(21, "x21"));
        var elementOffset = 4 * app.Binary.PointerSizeBytes;
        var module = new AsmResolver.DotNet.ModuleDefinition("ElementLoad.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemStringType,
            app.SystemTypes.SystemObjectType, app.SystemTypes.SystemVoidType);
        var (caller, _) = ForeignCaller(app, module, [
            new Instruction(0, OpCode.Add, pointer, array, scaledIndex),
            new Instruction(1, OpCode.Move, loaded,
                new MemoryOperand(pointer, addend: elementOffset, accessSize: app.Binary.PointerSizeBytes)),
            new Instruction(2, OpCode.Return)],
            [array, scaledIndex, pointer, loaded]);

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.That(loaded.Type, Is.SameAs(elementType),
            "the element load must carry the array's element type, not an unproven reuse type");
    }

    [Test]
    public void PointerArithmeticElementLoadFollowsMoveAndAddChain()
    {
        // The base may arrive through one or more copies of the pointer before the load.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var elementType = app.SystemTypes.SystemStringType;
        var array = new LocalVariable("array", new Register(8, "x8"))
            { Type = new SzArrayTypeAnalysisContext(elementType) };
        var scaledIndex = new LocalVariable("scaledIndex", new Register(19, "x19"));
        var pointer = new LocalVariable("pointer", new Register(20, "x20"));
        var pointerCopy = new LocalVariable("pointerCopy", new Register(22, "x22"));
        var loaded = new LocalVariable("loaded", new Register(21, "x21"));
        var elementOffset = 4 * app.Binary.PointerSizeBytes;
        var module = new AsmResolver.DotNet.ModuleDefinition("ElementLoadChain.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemStringType,
            app.SystemTypes.SystemObjectType, app.SystemTypes.SystemVoidType);
        var (caller, _) = ForeignCaller(app, module, [
            new Instruction(0, OpCode.Add, pointer, array, scaledIndex),
            new Instruction(1, OpCode.Move, pointerCopy, pointer),
            new Instruction(2, OpCode.Move, loaded,
                new MemoryOperand(pointerCopy, addend: elementOffset, accessSize: app.Binary.PointerSizeBytes)),
            new Instruction(3, OpCode.Return)],
            [array, scaledIndex, pointer, pointerCopy, loaded]);

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.That(loaded.Type, Is.SameAs(elementType),
            "the element load must resolve the array through the copy chain");
    }

    [Test]
    public void PhiBackwardTypingSkipsCopyProducedInput()
    {
        // `Phi(joined, [copyProduced, thisCopy])` where `copyProduced` is defined by a
        // `Move` from an object-typed value: the join takes thisCopy's type, but the
        // copy-produced input must keep the type its own producer proves. Stamping it
        // to the joined type asserts a conversion the binary never proves - the input
        // was carrying an unrelated value of a reused register.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var joinedType = app.SystemTypes.SystemExceptionType;
        var thisLocal = new LocalVariable("thisLocal", new Register(19, "x19"))
            { Type = joinedType };
        var thisCopy = new LocalVariable("thisCopy", new Register(19, "x19"));
        var valueLocal = new LocalVariable("valueLocal", new Register(0, "x0"))
            { Type = app.SystemTypes.SystemObjectType };
        var copyProduced = new LocalVariable("copyProduced", new Register(20, "x20"));
        var joined = new LocalVariable("joined", new Register(21, "x21"));
        var module = new AsmResolver.DotNet.ModuleDefinition("PhiGuard.dll");
        SeedCorLibTypes(app, module, joinedType, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemVoidType);
        var (caller, _) = ForeignCaller(app, module, [
            new Instruction(0, OpCode.Move, thisCopy, thisLocal),
            new Instruction(1, OpCode.Phi, joined, copyProduced, thisCopy),
            new Instruction(2, OpCode.Move, copyProduced, valueLocal),
            new Instruction(3, OpCode.Return)],
            [thisLocal, thisCopy, valueLocal, copyProduced, joined]);

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.Multiple(() =>
        {
            Assert.That(copyProduced.Type, Is.SameAs(app.SystemTypes.SystemObjectType),
                "the copy-produced phi input must keep its producer's proven type");
            Assert.That(joined.Type, Is.SameAs(joinedType),
                "the phi result still joins on the typed input");
        });
    }

    [Test]
    public void GenericReferenceCastResultReportsBoxedReference()
    {
        // isinst/castclass push `ref !0` - a boxed-T-or-null reference (ECMA III.4.15),
        // not the `value !0` the parameter's own stack kind declares. Reporting the
        // parameter makes downstream coercions emit `box !0` on a value that is already
        // a reference - invalid IL the verifier rejects.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var source = new LocalVariable("source", new Register(0, "x0"))
            { Type = app.SystemTypes.SystemObjectType };
        var module = new AsmResolver.DotNet.ModuleDefinition("GenericCast.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemVoidType);
        var (caller, _) = ForeignCaller(app, module, [new Instruction(0, OpCode.Return)], [source]);
        var genericParameter = new GenericParameterTypeAnalysisContext("T", 0,
            LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_MVAR, 0, caller);
        caller.GenericParameters.Add(genericParameter);

        var emitted = IlGenerator.EmittedOperandType(new ReferenceCast(source, genericParameter), caller);
        Assert.That(emitted, Is.TypeOf<BoxedTypeAnalysisContext>()
                .And.Property("ElementType").SameAs(genericParameter),
            "a reference cast to a generic parameter produces `ref !0`, not value !0");
    }

    [Test]
    public void CastOperandToGenericSlotEmitsUnboxAny()
    {
        // `unbox.any` is the canonical `ref !0` -> `value !0` conversion: it pops the
        // cast's boxed-T-or-null and pushes `value !0`. Dropping the value for a
        // synthetic default loses a cast the binary proves.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var source = new LocalVariable("source", new Register(0, "x0"))
            { Type = app.SystemTypes.SystemObjectType };
        var sink = new LocalVariable("sink", new Register(1, "x1"))
            { Type = app.SystemTypes.SystemObjectType };
        var module = new AsmResolver.DotNet.ModuleDefinition("GenericCoerce.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [], []);
        var genericParameter = new GenericParameterTypeAnalysisContext("T", 0,
            LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_MVAR, 0, caller);
        caller.GenericParameters.Add(genericParameter);
        var casted = new LocalVariable("casted", new Register(2, "x2")) { Type = genericParameter };
        caller.Locals = [source, sink, casted];
        caller.ControlFlowGraph = new Cpp2IL.Core.Graphs.ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, casted, new ReferenceCast(source, genericParameter)),
            // Read the converted value back so the store is not elided as dead.
            new Instruction(1, OpCode.Move, sink, casted),
            new Instruction(2, OpCode.Move, new MemoryOperand(sink, addend: 0, accessSize: 8), source),
            new Instruction(3, OpCode.Return)]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == AsmResolver.PE.DotNet.Cil.CilOpCodes.Unbox_Any), Is.True,
            () => string.Join("\n", il.Select(i => i.ToString())));
    }
}
