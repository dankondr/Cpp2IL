using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: dominating mid-body base-.ctor calls (castle-recovery#107).
// IL2CPP inlines constructor chains, so a lifted derived .ctor keeps a distant
// ancestor .ctor call on `this` with the real base .ctor's body stores left
// behind it. A `call` to a .ctor on `this` mid-body cannot verify and cannot be
// written as a C# `base(...)` initializer; the call must move to the head.
public class InlinedBaseConstructorCallTests
{
    private static (InjectedTypeAnalysisContext type, TypeDefinition definition) InjectType(
        ApplicationAnalysisContext app, ModuleDefinition module, string name,
        TypeAnalysisContext baseType, ITypeDefOrRef baseTypeReference)
    {
        var type = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", name, baseType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var definition = new TypeDefinition("Tests", name,
            TypeAttributes.Public | TypeAttributes.Class, baseTypeReference);
        module.TopLevelTypes.Add(definition);
        type.PutExtraData("AsmResolverType", definition);
        return (type, definition);
    }

    private static (MethodAnalysisContext context, MethodDefinition definition) InjectCtor(
        InjectedTypeAnalysisContext type, TypeDefinition definition, ModuleDefinition module,
        params (string Name, TypeAnalysisContext Context, TypeSignature Signature)[] parameters)
    {
        var context = type.InjectMethodContext(".ctor", type.AppContext.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public, parameters.Select(p => p.Context).ToArray());
        var method = new MethodDefinition(".ctor", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void,
                parameters.Select(p => p.Signature)));
        for (var i = 0; i < parameters.Length; i++)
            method.ParameterDefinitions.Add(new ParameterDefinition((ushort)(i + 1), parameters[i].Name, default));
        definition.Methods.Add(method);
        context.PutExtraData("AsmResolverMethod", method);
        return (context, method);
    }

    [Test]
    public void InlinedBaseConstructorStoreTrailHoistsCallWithRecoveredArguments()
    {
        // The derived .ctor kept the distant ancestor's .ctor call while the real
        // base .ctor was inlined: its `this.F = arg` stores trail the call. The
        // matching base .ctor is identified from its own parameter-fed stores and
        // the call is hoisted with the trail operands as its arguments.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("InlinedCtor.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemStringType, app.SystemTypes.SystemBooleanType);

        var (ancestor, ancestorDef) = InjectType(app, module, "Ancestor",
            app.SystemTypes.SystemObjectType, module.CorLibTypeFactory.Object.Type);
        var (baseType, baseDef) = InjectType(app, module, "Base", ancestor, ancestorDef.ToTypeReference());
        var (derived, derivedDef) = InjectType(app, module, "Derived", baseType, baseDef.ToTypeReference());

        var (ancestorCtor, _) = InjectCtor(ancestor, ancestorDef, module);
        var (baseCtor, baseCtorDef) = InjectCtor(baseType, baseDef, module,
            ("count", app.SystemTypes.SystemInt32Type, module.CorLibTypeFactory.Int32),
            ("name", app.SystemTypes.SystemStringType, module.CorLibTypeFactory.String));

        var countField = baseType.InjectFieldContext("count", app.SystemTypes.SystemInt32Type,
            R.FieldAttributes.Public);
        var nameField = baseType.InjectFieldContext("name", app.SystemTypes.SystemStringType,
            R.FieldAttributes.Public);
        var flagField = derived.InjectFieldContext("flag", app.SystemTypes.SystemBooleanType,
            R.FieldAttributes.Public);
        var countFieldDef = new FieldDefinition("count", FieldAttributes.Public, module.CorLibTypeFactory.Int32);
        baseDef.Fields.Add(countFieldDef);
        countField.PutExtraData("AsmResolverField", countFieldDef);
        var nameFieldDef = new FieldDefinition("name", FieldAttributes.Public, module.CorLibTypeFactory.String);
        baseDef.Fields.Add(nameFieldDef);
        nameField.PutExtraData("AsmResolverField", nameFieldDef);
        var flagFieldDef = new FieldDefinition("flag", FieldAttributes.Public, module.CorLibTypeFactory.Boolean);
        derivedDef.Fields.Add(flagFieldDef);
        flagField.PutExtraData("AsmResolverField", flagFieldDef);

        // The base .ctor's own body: ancestor init plus `this.F = param` stores.
        var baseThis = new LocalVariable("this", new Register(null, "this"), baseType) { IsThis = true };
        var baseCount = new LocalVariable("count", new Register(null, "p0"), app.SystemTypes.SystemInt32Type);
        var baseName = new LocalVariable("name", new Register(null, "p1"), app.SystemTypes.SystemStringType);
        baseCtor.ParameterLocals = [baseThis, baseCount, baseName];
        baseCtor.Locals = [baseThis, baseCount, baseName];
        baseCtor.AnalysisWarnings = [];
        baseCtor.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.CallVoid, ancestorCtor, baseThis),
            new(1, OpCode.Move, new FieldReference(countField, baseThis, 0), baseCount),
            new(2, OpCode.Move, new FieldReference(nameField, baseThis, 0), baseName),
            new(3, OpCode.Return)]);

        var (caller, method) = InjectCtor(derived, derivedDef, module,
            ("count", app.SystemTypes.SystemInt32Type, module.CorLibTypeFactory.Int32),
            ("name", app.SystemTypes.SystemStringType, module.CorLibTypeFactory.String));
        var thisLocal = new LocalVariable("this", new Register(null, "this"), derived) { IsThis = true };
        var count = new LocalVariable("count", new Register(null, "p0"), app.SystemTypes.SystemInt32Type);
        var name = new LocalVariable("name", new Register(null, "p1"), app.SystemTypes.SystemStringType);
        caller.ParameterLocals = [thisLocal, count, name];
        caller.Locals = [thisLocal, count, name];
        caller.AnalysisWarnings = [];
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.CallVoid, ancestorCtor, thisLocal),
            new(1, OpCode.Move, new FieldReference(countField, thisLocal, 0), count),
            new(2, OpCode.Move, new FieldReference(nameField, thisLocal, 0), name),
            // A store to a field the candidate's map does not cover is a derived
            // field initializer, not inlined-body evidence: it stays in the body.
            new(3, OpCode.Move, new FieldReference(flagField, thisLocal, 0), new Immediate(0)),
            new(4, OpCode.Return)]);
        caller.DominatorInfo = new DominatorInfo(caller.ControlFlowGraph);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        var callIndex = il.ToList().FindIndex(i => i.OpCode == CilOpCodes.Call);
        Assert.Multiple(() =>
        {
            Assert.That(il[0].OpCode, Is.EqualTo(CilOpCodes.Ldarg_0),
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il[1].OpCode, Is.EqualTo(CilOpCodes.Ldarg));
            Assert.That(il[2].OpCode, Is.EqualTo(CilOpCodes.Ldarg));
            Assert.That(callIndex, Is.EqualTo(3));
            Assert.That(il[callIndex].Operand, Is.SameAs(baseCtorDef),
                "the inlined-store trail identifies the real base .ctor");
            // The consumed `this.count`/`this.name` stores are gone - the base
            // call performs them; the uncovered `this.flag` initializer stays.
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stfld && ReferenceEquals(i.Operand, flagFieldDef)),
                Is.True, "the derived field initializer keeps its in-body store");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stfld && ReferenceEquals(i.Operand, countFieldDef)),
                Is.False, "the store the recovered base call performs is consumed");
            Assert.That(il[^1].OpCode, Is.EqualTo(CilOpCodes.Ret));
        });
    }

    [Test]
    public void ConstructorCallArgumentReadsThroughStoredFieldForwardsStoreSource()
    {
        // A legal immediate-base .ctor call sits mid-body because an argument is
        // a field read on a local that was populated just above it. The field's
        // single dominating store gives the entry-live operand, so the call can
        // move to the initializer position with the stored value.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("ForwardedCtorArg.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemStringType);

        var (baseType, baseDef) = InjectType(app, module, "Base",
            app.SystemTypes.SystemObjectType, module.CorLibTypeFactory.Object.Type);
        var (derived, derivedDef) = InjectType(app, module, "Derived", baseType, baseDef.ToTypeReference());
        var (closure, closureDef) = InjectType(app, module, "Closure",
            app.SystemTypes.SystemObjectType, module.CorLibTypeFactory.Object.Type);

        var (baseCtor, baseCtorDef) = InjectCtor(baseType, baseDef, module,
            ("property", app.SystemTypes.SystemStringType, module.CorLibTypeFactory.String),
            ("descriptor", app.SystemTypes.SystemStringType, module.CorLibTypeFactory.String));
        var descriptorField = closure.InjectFieldContext("descriptor",
            app.SystemTypes.SystemStringType, R.FieldAttributes.Public);
        var descriptorFieldDef = new FieldDefinition("descriptor", FieldAttributes.Public,
            module.CorLibTypeFactory.String);
        closureDef.Fields.Add(descriptorFieldDef);
        descriptorField.PutExtraData("AsmResolverField", descriptorFieldDef);

        var (caller, method) = InjectCtor(derived, derivedDef, module,
            ("property", app.SystemTypes.SystemStringType, module.CorLibTypeFactory.String),
            ("descriptor", app.SystemTypes.SystemStringType, module.CorLibTypeFactory.String));
        var thisLocal = new LocalVariable("this", new Register(null, "this"), derived) { IsThis = true };
        var property = new LocalVariable("property", new Register(null, "p0"), app.SystemTypes.SystemStringType);
        var descriptor = new LocalVariable("descriptor", new Register(null, "p1"), app.SystemTypes.SystemStringType);
        var closureLocal = new LocalVariable("closure", new Register(null, "v0"), closure);
        caller.ParameterLocals = [thisLocal, property, descriptor];
        caller.Locals = [thisLocal, property, descriptor, closureLocal];
        caller.AnalysisWarnings = [];
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, new FieldReference(descriptorField, closureLocal, 0), descriptor),
            new(1, OpCode.CallVoid, baseCtor, thisLocal, property,
                new FieldReference(descriptorField, closureLocal, 0)),
            new(2, OpCode.Return)]);
        caller.DominatorInfo = new DominatorInfo(caller.ControlFlowGraph);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        var callIndex = il.ToList().FindIndex(i => i.OpCode == CilOpCodes.Call && ReferenceEquals(i.Operand, baseCtorDef));
        Assert.Multiple(() =>
        {
            Assert.That(il[0].OpCode, Is.EqualTo(CilOpCodes.Ldarg_0),
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il[1].OpCode, Is.EqualTo(CilOpCodes.Ldarg));
            Assert.That(il[2].OpCode, Is.EqualTo(CilOpCodes.Ldarg),
                "the field-read operand forwards to the parameter its store placed there");
            Assert.That(callIndex, Is.EqualTo(3));
            Assert.That(il[^1].OpCode, Is.EqualTo(CilOpCodes.Ret));
        });
    }
}
