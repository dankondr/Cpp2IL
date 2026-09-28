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
// IL2CPP inlines constructor chains, so a lifted derived .ctor can keep a
// `call` to a .ctor on `this` mid-body - it cannot verify and cannot be written
// as a C# `base(...)` initializer; the call must move to the head. Hoisting is
// allowed only over code that provably cannot observe the moved call: a `this`
// write or read on any path reaching the call keeps it in place.
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

    [Test]
    public void ThisFieldWriteInOneBranchArmBlocksHoist()
    {
        // A legal immediate-base .ctor call whose argument is a field read on a
        // closure local - the operand resolves only through the store-forwarding
        // path, which `SafeToHoistBefore` guards. One arm of a conditional
        // writes `this.seen` before the paths rejoin at the call block; that arm
        // does not dominate the call, so only the full predecessor closure sees
        // the write - and the call must stay where it is.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("BranchedCtor.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemStringType,
            app.SystemTypes.SystemBooleanType);

        var (baseType, baseDef) = InjectType(app, module, "Base",
            app.SystemTypes.SystemObjectType, module.CorLibTypeFactory.Object.Type);
        var (derived, derivedDef) = InjectType(app, module, "Derived", baseType, baseDef.ToTypeReference());
        var (closure, closureDef) = InjectType(app, module, "Closure",
            app.SystemTypes.SystemObjectType, module.CorLibTypeFactory.Object.Type);

        var (baseCtor, _) = InjectCtor(baseType, baseDef, module,
            ("descriptor", app.SystemTypes.SystemStringType, module.CorLibTypeFactory.String));

        var descriptorField = closure.InjectFieldContext("descriptor",
            app.SystemTypes.SystemStringType, R.FieldAttributes.Public);
        var descriptorFieldDef = new FieldDefinition("descriptor", FieldAttributes.Public,
            module.CorLibTypeFactory.String);
        closureDef.Fields.Add(descriptorFieldDef);
        descriptorField.PutExtraData("AsmResolverField", descriptorFieldDef);
        var seenField = derived.InjectFieldContext("seen", app.SystemTypes.SystemBooleanType,
            R.FieldAttributes.Public);
        var seenFieldDef = new FieldDefinition("seen", FieldAttributes.Public, module.CorLibTypeFactory.Boolean);
        derivedDef.Fields.Add(seenFieldDef);
        seenField.PutExtraData("AsmResolverField", seenFieldDef);

        var (caller, method) = InjectCtor(derived, derivedDef, module,
            ("descriptor", app.SystemTypes.SystemStringType, module.CorLibTypeFactory.String),
            ("cond", app.SystemTypes.SystemBooleanType, module.CorLibTypeFactory.Boolean));
        var thisLocal = new LocalVariable("this", new Register(null, "this"), derived) { IsThis = true };
        var descriptor = new LocalVariable("descriptor", new Register(null, "p0"), app.SystemTypes.SystemStringType);
        var cond = new LocalVariable("cond", new Register(null, "p1"), app.SystemTypes.SystemBooleanType);
        var closureLocal = new LocalVariable("closure", new Register(null, "v0"), closure);
        caller.ParameterLocals = [thisLocal, descriptor, cond];
        caller.Locals = [thisLocal, descriptor, cond, closureLocal];
        caller.AnalysisWarnings = [];
        var store = new Instruction(4, OpCode.Move,
            new FieldReference(descriptorField, closureLocal, 0), descriptor);
        var call = new Instruction(5, OpCode.CallVoid, baseCtor, thisLocal,
            new FieldReference(descriptorField, closureLocal, 0));
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.ConditionalJump, store, cond),
            new(1, OpCode.Move, new FieldReference(seenField, thisLocal, 0), new Immediate(1)),
            new(2, OpCode.Jump, store),
            new(3, OpCode.Jump, store),
            store,
            call,
            new(6, OpCode.Return)]);
        caller.DominatorInfo = new DominatorInfo(caller.ControlFlowGraph);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        var callIndex = il.ToList().FindIndex(i => i.OpCode == CilOpCodes.Call
            && i.Operand is MethodDefinition m && m.Name == ".ctor");
        var storeIndex = il.ToList().FindIndex(i => i.OpCode == CilOpCodes.Stfld
            && ReferenceEquals(i.Operand, seenFieldDef));
        Assert.Multiple(() =>
        {
            Assert.That(storeIndex, Is.GreaterThanOrEqualTo(0),
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(callIndex, Is.GreaterThan(storeIndex),
                "the base call must stay after the conditional `this` write - it cannot be hoisted");
        });
    }
}
