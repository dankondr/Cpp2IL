using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils.AsmResolver;
using R = System.Reflection;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: silent scalar -> object boxes (castle-recovery#189).
// A scalar value pushed where a slot requires System.Object is honest only when
// the binary proves the value already is a reference, or that it allocated a
// box for it (an il2cpp_value_box helper / ISIL Box in the operand's
// definitions). Every other scalar -> object edge used to emit a fabricated
// `box`; it must now carry a named decompiler-issue note and stop instead.
public class ScalarObjectEdgeTests
{
    private static LocalVariable Local(string name, TypeAnalysisContext type) =>
        new(name, new Register(null, name)) { Type = type };

    private static (InjectedTypeAnalysisContext owner, InjectedFieldAnalysisContext field)
        ObjectFieldHolder(ApplicationAnalysisContext app, string name)
    {
        var owner = new InjectedTypeAnalysisContext(
            app.AssembliesByName["UnityEngine.CoreModule"], "Tests", name,
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var field = new InjectedFieldAnalysisContext("slot", app.SystemTypes.SystemObjectType,
            R.FieldAttributes.Public | R.FieldAttributes.Static, owner, 16);
        owner.Fields.Add(field);
        return (owner, field);
    }

    private static void SeedField(FieldAnalysisContext field, ModuleDefinition module)
    {
        var definition = new FieldDefinition(field.Name,
            field.Attributes.HasFlag(R.FieldAttributes.Static)
                ? FieldAttributes.Public | FieldAttributes.Static : FieldAttributes.Public,
            new FieldSignature(field.FieldType.ToTypeSignature()));
        field.DeclaringType!.GetExtraData<TypeDefinition>("AsmResolverType")!.Fields.Add(definition);
        field.PutExtraData("AsmResolverField", definition);
    }

    private static TypeDefinition SeedOwner(InjectedTypeAnalysisContext owner,
        ModuleDefinition module, string name)
    {
        var ownerTypeDef = new TypeDefinition("Tests", name,
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(ownerTypeDef);
        owner.PutExtraData("AsmResolverType", ownerTypeDef);
        return ownerTypeDef;
    }

    [Test]
    public void UnprovenScalarMoveIntoObjectSlotEmitsNoteNotBox()
    {
        // An Int32 value moved into a System.Object field has no definition
        // proving a reference or a box; the store used to fabricate `box`. The
        // edge now emits the decompiler-issue note and an honest stop.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var (owner, field) = ObjectFieldHolder(app, "MoveSlot");
        var intLocal = Local("i", app.SystemTypes.SystemInt32Type);
        var module = new ModuleDefinition("UnprovenMove.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemObjectType);
        SeedOwner(owner, module, "MoveSlot");
        SeedField(field, module);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, intLocal, new Immediate(5)),
            new(1, OpCode.Move, new FieldReference(field, intLocal, 16), intLocal),
            new(2, OpCode.Return)], [intLocal]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Box), Is.False,
                () => "the unproven edge must not fabricate a box:\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("no binary proof")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Throw), Is.True,
                "the unproven edge stops the method rather than feeding the slot a made-up value");
        });
    }

    [Test]
    public void UnprovenArithmeticResultIntoObjectSlotEmitsNoteNotBox()
    {
        // The dominant class: an integer arithmetic result stored into an
        // Object-typed slot. The register provably carried an integer, so the
        // box into the object slot was a conversion the binary never made.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var (owner, field) = ObjectFieldHolder(app, "ArithSlot");
        var intLocal = Local("i", app.SystemTypes.SystemInt32Type);
        var module = new ModuleDefinition("UnprovenArith.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemObjectType);
        SeedOwner(owner, module, "ArithSlot");
        SeedField(field, module);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, intLocal, new Immediate(5)),
            new(1, OpCode.Add, new FieldReference(field, intLocal, 16), intLocal, new Immediate(5)),
            new(2, OpCode.Return)], [intLocal]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Add), Is.True,
                () => "the proven integer arithmetic still emits:\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Box), Is.False,
                () => "the unproven result edge must not fabricate a box:\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("no binary proof")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Throw), Is.True);
        });
    }

    [Test]
    public void BoxHelperProducedOperandKeepsBox()
    {
        // When the operand's definitions include a call to the il2cpp_value_box
        // allocation helper the binary proves the box: `box` stays.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var (owner, field) = ObjectFieldHolder(app, "BoxSlot");
        var helperType = new InjectedTypeAnalysisContext(
            app.AssembliesByName["UnityEngine.CoreModule"], "Tests", "BoxHelpers",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var valueBox = helperType.InjectMethodContext("il2cpp_value_box",
            app.SystemTypes.SystemInt32Type,
            R.MethodAttributes.Public | R.MethodAttributes.Static,
            app.SystemTypes.SystemInt32Type);
        var boxed = Local("v", app.SystemTypes.SystemInt32Type);
        var module = new ModuleDefinition("ProvenBox.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemObjectType);
        SeedOwner(owner, module, "BoxSlot");
        SeedField(field, module);
        var helperTypeDef = new TypeDefinition("Tests", "BoxHelpers",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(helperTypeDef);
        var valueBoxDef = new MethodDefinition("il2cpp_value_box",
            MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Int32,
                [module.CorLibTypeFactory.Int32]));
        helperTypeDef.Methods.Add(valueBoxDef);
        valueBox.PutExtraData("AsmResolverMethod", valueBoxDef);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Call, valueBox, boxed, new Immediate(1)),
            new(1, OpCode.Move, new FieldReference(field, boxed, 16), boxed),
            new(2, OpCode.Return)], [boxed]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Box), Is.True,
                () => "a proven box allocation keeps `box`:\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("no binary proof")), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void ReferenceProducedOperandEmitsTheReference()
    {
        // The operand's local is scalar-labeled, but its only definition loads a
        // reference-typed field - the binary proves the slot really holds an
        // object reference, so the producing load itself is the value emitted.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var (owner, field) = ObjectFieldHolder(app, "RefSlot");
        var holderType = new InjectedTypeAnalysisContext(
            app.AssembliesByName["UnityEngine.CoreModule"], "Tests", "RefHolder",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var heldField = new InjectedFieldAnalysisContext("held",
            app.SystemTypes.SystemStringType,
            R.FieldAttributes.Public | R.FieldAttributes.Static, holderType, 16);
        holderType.Fields.Add(heldField);
        var carrier = Local("v", app.SystemTypes.SystemInt32Type);
        var holder = Local("h", holderType);
        var module = new ModuleDefinition("ProvenRef.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemStringType, app.SystemTypes.SystemObjectType);
        SeedOwner(owner, module, "RefSlot");
        SeedField(field, module);
        SeedOwner(holderType, module, "RefHolder");
        SeedField(heldField, module);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, carrier, new FieldReference(heldField, holder, 16)),
            new(1, OpCode.Move, new FieldReference(field, carrier, 16), carrier),
            new(2, OpCode.Return)], [carrier, holder]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stsfld), Is.True,
                () => "the proven reference value reaches the object slot:\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Box), Is.False,
                () => "the proven reference needs no box:\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("no binary proof")), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void LifterTypedObjectSlotWithScalarDefinitionsRetypesToTheScalar()
    {
        // Object is the lifter's fallback tag on a register whose real type
        // analysis lost. When the register's own definitions all prove the
        // same scalar, the slot is declared as that scalar: the store needs
        // no edge, no `box` and no note at all.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var slot = Local("v", app.SystemTypes.SystemObjectType);
        var flagA = Local("a", app.SystemTypes.SystemInt32Type);
        var flagB = Local("b", app.SystemTypes.SystemInt32Type);
        var module = new ModuleDefinition("RetypedSlot.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemObjectType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, flagA, new Immediate(1)),
            new(1, OpCode.Move, flagB, new Immediate(2)),
            new(2, OpCode.CheckLess, slot, flagA, flagB),
            new(3, OpCode.Return)], [slot, flagA, flagB]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(method.CilMethodBody.LocalVariables.Any(local =>
                    local.VariableType?.ToString()?.Contains("Int32") == true), Is.True,
                () => "the slot is declared as the proven Int32:\n"
                    + string.Join("\n", method.CilMethodBody.LocalVariables.Select(l => l.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Box), Is.False,
                () => "no edge remains to fabricate a box for:\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.False,
                () => "no edge remains to note either:\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Throw), Is.False);
        });
    }

    [Test]
    public void MixedLifetimeObjectSlotKeepsNoteAndBoxWithoutThrow()
    {
        // One register carries both lifetimes: a definition from an unprovable
        // object local and a literal store. It cannot be retyped to one honest
        // slot, so it keeps System.Object - but throwing the scalar store
        // would leave the later lifetime reading an unassigned local. The
        // unproven edge keeps the named note plus the prior `box` emission,
        // and the path is not stopped.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var slot = Local("v", app.SystemTypes.SystemObjectType);
        var objLocal = Local("o", app.SystemTypes.SystemObjectType);
        var module = new ModuleDefinition("MixedSlot.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemObjectType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, slot, objLocal),
            new(1, OpCode.Move, slot, new Immediate(5)),
            new(2, OpCode.Return)], [slot, objLocal]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(method.CilMethodBody.LocalVariables.Any(local =>
                    local.VariableType?.ToString()?.Contains("Object") == true), Is.True,
                () => "the mixed-lifetime slot keeps System.Object:\n"
                    + string.Join("\n", method.CilMethodBody.LocalVariables.Select(l => l.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Box), Is.True,
                () => "the lifter-typed contract keeps the prior box emission:\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("no binary proof")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Throw), Is.False,
                () => "the store must not stop the path - the register is shared:\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void ReadBeforeAnyDefinitionKeepsObjectSlotNotUnassignedLoad()
    {
        // The lifter's register names are not SSA: this register's only
        // definition is the instruction that also reads it. Retyping the slot
        // would emit `ldloc` before any `stloc` - an unassigned-local read the
        // C# layer cannot spell. The slot keeps System.Object, so the
        // unemittable operation leaves its noted default store instead.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var slot = Local("v", app.SystemTypes.SystemObjectType);
        var module = new ModuleDefinition("SelfReadSlot.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemObjectType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Subtract, slot, slot, slot),
            new(1, OpCode.Return)], [slot]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        var firstStore = il.ToList().FindIndex(i => i.OpCode == CilOpCodes.Stloc);
        Assert.Multiple(() =>
        {
            Assert.That(method.CilMethodBody.LocalVariables.Any(local =>
                    local.VariableType?.ToString()?.Contains("Object") == true), Is.True,
                () => "the unreadable slot keeps System.Object:\n"
                    + string.Join("\n", method.CilMethodBody.LocalVariables.Select(l => l.ToString())));
            Assert.That(firstStore, Is.GreaterThanOrEqualTo(0),
                () => "the honest stop still assigns the slot:\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(firstStore < 0 || il.Take(firstStore).All(i => i.OpCode != CilOpCodes.Ldloc), Is.True,
                () => "no ldloc may precede the slot's first store:\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void BlockMemoryDestinationObjectSlotKeepsObjectNotInitblk()
    {
        // A block memory op lowers to initblk/cpblk - IL the verifier rejects
        // outright. Retyping the destination slot to the proven scalar would
        // let the op's operand proofs pass and emit that invalid IL where the
        // object slot keeps the op on its named unrecoverable diagnostic.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var slot = Local("v", app.SystemTypes.SystemObjectType);
        var module = new ModuleDefinition("BlockSlot.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemObjectType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, slot, new Immediate(5)),
            new(1, OpCode.MemorySet, new AddressOf(slot), new Immediate(0), new Immediate(208)),
            new(2, OpCode.Return)], [slot]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(method.CilMethodBody.LocalVariables.Any(local =>
                    local.VariableType?.ToString()?.Contains("Object") == true), Is.True,
                () => "a block-op operand keeps System.Object:\n"
                    + string.Join("\n", method.CilMethodBody.LocalVariables.Select(l => l.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Initblk), Is.False,
                () => "the block op must not emit unverifiable IL:\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("Unproven block memory operand")), Is.True,
                () => "the op keeps its named diagnostic:\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
        });
    }
}
