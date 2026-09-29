using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;
using R = System.Reflection;
using F = AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes;
using T = AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: compile bucket readonly-write (castle-recovery#148).
// A store into [this + K] on a generic type resolves to a member path whose
// leaf belongs to an interior value-typed container - `this.state.token`, not
// `this.token`. Binding that leaf onto the outer instantiation relabels its
// declaring type, which lets the ctor-initonly gate pass against the wrong
// owner and emits a stfld the type never declared (CS0191 + invalid IL). The
// leaf must bind to the innermost container's instantiation; when the member
// then refuses the write it keeps its named diagnostic instead.
public class NestedLeafOwnerBindingTests
{
    private static FieldAnalysisContext SeedField(ModuleDefinition module, TypeAnalysisContext owner,
        string name, TypeAnalysisContext fieldType, int offset,
        R.FieldAttributes attrs = R.FieldAttributes.Public,
        F asmAttrs = F.Public)
    {
        var field = new InjectedFieldAnalysisContext(name, fieldType, attrs, owner, offset);
        owner.Fields.Add(field);
        var definition = owner.GetExtraData<TypeDefinition>("AsmResolverType")!;
        var fieldDefinition = new FieldDefinition(name, asmAttrs,
            new FieldSignature(fieldType.GetExtraData<TypeSignature>("AsmResolverSignature")
                ?? module.CorLibTypeFactory.CorLibScope.CreateTypeReference(fieldType.Namespace, fieldType.Name)
                    .ToTypeSignature(fieldType.IsValueType)));
        definition.Fields.Add(fieldDefinition);
        field.PutExtraData("AsmResolverField", fieldDefinition);
        return field;
    }

    private static TypeAnalysisContext SeededOwner(ApplicationAnalysisContext app,
        ModuleDefinition module, string name, TypeAnalysisContext baseType)
    {
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", name,
            baseType, R.TypeAttributes.Public);
        var definition = new TypeDefinition("Tests", name,
            T.Public | (baseType.IsValueType ? T.Sealed | T.SequentialLayout : T.Class),
            baseType.IsValueType
                ? module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType")
                : module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(definition);
        owner.PutExtraData("AsmResolverType", definition);
        return owner;
    }

    // Every injected .ctor's implicit base call must resolve to a descriptor.
    private static void SeedObjectCtor(TypeAnalysisContext objectType, ModuleDefinition module)
    {
        var objectDefinition = objectType.GetExtraData<TypeDefinition>("AsmResolverType")!;
        module.TopLevelTypes.Add(objectDefinition);
        var ctorDefinition = new MethodDefinition(".ctor", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        objectDefinition.Methods.Add(ctorDefinition);
        objectType.Methods.Single(m => m.Name == ".ctor" && m.Parameters.Count == 0)
            .PutExtraData("AsmResolverMethod", ctorDefinition);
    }

    // A .ctor on a generic definition whose `this` is the instantiation -
    // `Box<T>::.ctor` bound to `this : Box<int>`.
    private static (TypeAnalysisContext state, InjectedTypeAnalysisContext box,
        GenericInstanceTypeAnalysisContext instance, FieldAnalysisContext stateField)
        GenericFixture(ApplicationAnalysisContext app, ModuleDefinition module)
    {
        var objectType = app.SystemTypes.SystemObjectType;
        var int64 = app.SystemTypes.SystemInt64Type;
        SeedCorLibTypes(app, module, objectType, int64, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemValueTypeType, app.SystemTypes.SystemVoidType);
        var state = SeededOwner(app, module, "State", app.SystemTypes.SystemValueTypeType);
        SeedField(module, state, "header", int64, 0);
        var box = (InjectedTypeAnalysisContext)SeededOwner(app, module, "Box`1", objectType);
        var t = new GenericParameterTypeAnalysisContext("T", 0, Il2CppTypeEnum.IL2CPP_TYPE_VAR,
            R.GenericParameterAttributes.None, box);
        box.GenericParameters.Add(t);
        SeedField(module, box, "head", objectType, 0x10);
        var stateField = SeedField(module, box, "state", state, 0x18);
        var instance = new GenericInstanceTypeAnalysisContext(box,
            [app.SystemTypes.SystemInt32Type]);
        SeedObjectCtor(objectType, module);
        return (state, box, instance, stateField);
    }

    private static (MethodAnalysisContext caller, MethodDefinition method) CtorCaller(
        InjectedTypeAnalysisContext declaringType, ModuleDefinition module,
        List<Instruction> instructions, List<LocalVariable> locals,
        List<LocalVariable> parameters)
    {
        var caller = declaringType.InjectMethodContext(".ctor",
            declaringType.AppContext.SystemTypes.SystemVoidType, R.MethodAttributes.Public);
        caller.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        caller.Locals = locals;
        caller.ParameterLocals = parameters;
        caller.AnalysisWarnings = [];
        var method = new MethodDefinition(".ctor", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        declaringType.GetExtraData<TypeDefinition>("AsmResolverType")!.Methods.Add(method);
        return (caller, method);
    }

    [Test]
    public void ReadonlyLeafInsideGenericStructFieldKeepsDiagnostic()
    {
        // `Box<int>::.ctor` writes [this + 0x20] = state.token. token is
        // initonly on the non-generic State, so the ctor-initonly exception
        // does not apply: the store cannot be spelled and keeps its named
        // diagnostic. Bound onto Box<int> instead, the leaf would read as an
        // initonly member of the constructor's own type - the exact misbind
        // that emitted CS0191 in the recovery corpora.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("NestedLeafBinding.dll");
        var (state, box, instance, _) = GenericFixture(app, module);
        var token = SeedField(module, state, "token", app.SystemTypes.SystemObjectType, 8,
            R.FieldAttributes.Public | R.FieldAttributes.InitOnly, F.Public | F.InitOnly);
        var self = new LocalVariable("this", new Register(null, "this"), instance) { IsThis = true };
        var value = new LocalVariable("value", new Register(null, "value"),
            app.SystemTypes.SystemObjectType);
        var (caller, method) = CtorCaller(box, module, [
            new(0, OpCode.Move, new MemoryOperand(self, addend: 0x20, accessSize: 8), value),
            new(1, OpCode.Return)], [self, value], [self]);

        LocalVariables.ResolveTypesAndFields(caller);
        IlGenerator.GenerateIl(caller, method);

        var reference = (FieldReference)caller.ControlFlowGraph!.Instructions[0].Operands[0];
        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(reference.Field.DeclaringType, Is.SameAs(state),
                "the leaf stays a State member - its real declaring type");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stfld), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("Inaccessible field store")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void WritableLeafInsideGenericStructFieldStillBinds()
    {
        // Same nested shape with a writable leaf: `this.state.tag = v` stays a
        // legal nested store and emits ldflda + stfld.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("NestedLeafBinding.dll");
        var (state, box, instance, _) = GenericFixture(app, module);
        SeedField(module, state, "tag", app.SystemTypes.SystemObjectType, 8);
        var self = new LocalVariable("this", new Register(null, "this"), instance) { IsThis = true };
        var value = new LocalVariable("value", new Register(null, "value"),
            app.SystemTypes.SystemObjectType);
        var (caller, method) = CtorCaller(box, module, [
            new(0, OpCode.Move, new MemoryOperand(self, addend: 0x20, accessSize: 8), value),
            new(1, OpCode.Return)], [self, value], [self, value]);

        LocalVariables.ResolveTypesAndFields(caller);
        IlGenerator.GenerateIl(caller, method);

        var reference = (FieldReference)caller.ControlFlowGraph!.Instructions[0].Operands[0];
        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(reference.Field.DeclaringType, Is.SameAs(state));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldflda
                    && i.Operand?.ToString().Contains("state") == true), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stfld
                    && i.Operand?.ToString().Contains("tag") == true), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void ConstFieldStoreKeepsDiagnostic()
    {
        // A store onto a literal (const) field has no managed spelling from any
        // caller - even the declaring .cctor cannot assign a const - so it
        // keeps the inaccessible-store diagnostic instead of emitting stsfld
        // the C# compiler rejects (CS0131).
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("LiteralStore.dll");
        var int32 = app.SystemTypes.SystemInt32Type;
        SeedCorLibTypes(app, module, int32, app.SystemTypes.SystemVoidType);
        var pool = (InjectedTypeAnalysisContext)SeededOwner(app, module, "Pool",
            app.SystemTypes.SystemObjectType);
        var maximum = SeedField(module, pool, "Maximum", int32, 0,
            R.FieldAttributes.Public | R.FieldAttributes.Static | R.FieldAttributes.Literal,
            F.Public | F.Static | F.Literal);
        var owner = new LocalVariable("owner", new Register(null, "owner"), pool);
        var value = new LocalVariable("value", new Register(null, "value"), int32);
        var caller = pool.InjectMethodContext(".cctor", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, new FieldReference(maximum, owner, 0), value),
            new(1, OpCode.Return)]);
        caller.Locals = [owner, value];
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];
        var method = new MethodDefinition(".cctor", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        pool.GetExtraData<TypeDefinition>("AsmResolverType")!.Methods.Add(method);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stsfld), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("Inaccessible field store")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }
}
