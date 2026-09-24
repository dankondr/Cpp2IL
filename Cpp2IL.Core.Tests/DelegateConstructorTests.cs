using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests;

// Shared-generic code erases delegate instantiations to object arguments, so a
// recovered `newobj Func<object, bool>::.ctor` can be paired with an ldftn
// target whose concrete signature the erased Invoke can never accept. The
// generator re-derives the instantiation from the target's signature, and when
// nothing can satisfy the verifier's DelegateCtor check it emits a diagnostic
// plus a null delegate instead of an unverifiable newobj.
public class DelegateConstructorTests
{
    [SetUp] public void Setup() { Cpp2IlApi.ResetInternalState(); TestGameLoader.LoadSimple2019Game(); }

    private sealed class Fixture(ApplicationAnalysisContext app)
    {
        public readonly TypeAnalysisContext FuncDefinition =
            app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Func`2")!;
        public readonly MethodAnalysisContext FuncCtor =
            app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Func`2")!.Methods
                .First(m => m.Name == ".ctor");
        public readonly InjectedTypeAnalysisContext Closure =
            new(app.SystemTypes.SystemObjectType.DeclaringAssembly, "Tests", "Closure",
                app.SystemTypes.SystemObjectType, R.TypeAttributes.Public);
        public readonly InjectedTypeAnalysisContext Owner =
            new(app.SystemTypes.SystemObjectType.DeclaringAssembly, "Tests", "Owner",
                app.SystemTypes.SystemObjectType, R.TypeAttributes.Public);
        public readonly LocalVariable Result;
        public readonly LocalVariable ClosureLocal;
        public readonly GenericInstanceTypeAnalysisContext ErasedGit;
        public readonly ConcreteGenericMethodAnalysisContext ErasedCtor;

        public Fixture(ApplicationAnalysisContext app, TypeAnalysisContext arg, TypeAnalysisContext ret)
            : this(app)
        {
            ErasedGit = new GenericInstanceTypeAnalysisContext(FuncDefinition, [arg, ret]);
            ErasedCtor = new ConcreteGenericMethodAnalysisContext(FuncCtor, [arg, ret], []);
            Result = new LocalVariable("result", new Register(null, "result"), ErasedGit);
            ClosureLocal = new LocalVariable("closure", new Register(null, "closure"), Closure);
        }
    }

    private static InjectedMethodAnalysisContext Caller(Fixture fixture,
        ApplicationAnalysisContext app, IOperand functionPointer)
    {
        var caller = new InjectedMethodAnalysisContext(fixture.Owner, "Create",
            app.SystemTypes.SystemVoidType, R.MethodAttributes.Public | R.MethodAttributes.Static, []);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Newobj, fixture.Result, fixture.ErasedGit),
            new(1, OpCode.CallVoid, fixture.ErasedCtor, fixture.Result, fixture.ClosureLocal, functionPointer),
            new(2, OpCode.Return)]);
        caller.Locals = [fixture.ClosureLocal, fixture.Result];
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];
        return caller;
    }

    private static MethodDefinition Definitions(ModuleDefinition module, Fixture fixture,
        MethodAnalysisContext target, MethodSignature targetSignature,
        ApplicationAnalysisContext app, MethodDefinition callerDefinition)
    {
        var closureType = new TypeDefinition("Tests", "Closure", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        var ownerType = new TypeDefinition("Tests", "Owner", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        var funcType = new TypeDefinition("System", "Func`2", TypeAttributes.Public,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "MulticastDelegate"));
        module.TopLevelTypes.Add(closureType);
        module.TopLevelTypes.Add(ownerType);
        module.TopLevelTypes.Add(funcType);

        foreach (var (type, name) in new (TypeAnalysisContext Type, string Name)[]
        {
            (app.SystemTypes.SystemObjectType, "Object"),
            (app.SystemTypes.SystemBooleanType, "Boolean"),
            (app.SystemTypes.SystemStringType, "String"),
            (app.SystemTypes.SystemInt32Type, "Int32"),
            (app.SystemTypes.SystemIntPtrType, "IntPtr"),
            (app.SystemTypes.SystemVoidType, "Void"),
        })
            type.PutExtraData("AsmResolverType",
                new TypeDefinition("System", name, TypeAttributes.Public));

        fixture.Closure.PutExtraData("AsmResolverType", closureType);
        fixture.Owner.PutExtraData("AsmResolverType", ownerType);
        fixture.FuncDefinition.PutExtraData("AsmResolverType", funcType);

        var targetDefinition = new MethodDefinition("Match", MethodAttributes.Public, targetSignature);
        closureType.Methods.Add(targetDefinition);
        target.PutExtraData("AsmResolverMethod", targetDefinition);

        ownerType.Methods.Add(callerDefinition);
        return targetDefinition;
    }

    [Test]
    public void ErasedDelegateConstructorIsSharpenedToTheLdftnTargetSignature()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var fixture = new Fixture(app, app.SystemTypes.SystemObjectType, app.SystemTypes.SystemBooleanType);
        var target = new InjectedMethodAnalysisContext(fixture.Closure, "Match",
            app.SystemTypes.SystemBooleanType, R.MethodAttributes.Public,
            [app.SystemTypes.SystemStringType]);
        fixture.Closure.Methods.Add(target);
        var caller = Caller(fixture, app, new RuntimeMethodInfoAnalysisContext(target, fixture.Closure.DeclaringAssembly));

        var module = new ModuleDefinition("DelegateSharpen.dll");
        var callerDefinition = new MethodDefinition("Create", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        var targetDefinition = Definitions(module, fixture, target,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Boolean, [module.CorLibTypeFactory.String]),
            app, callerDefinition);

        IlGenerator.GenerateIl(caller, callerDefinition);

        var il = callerDefinition.CilMethodBody!.Instructions;
        var newobj = il.Single(i => i.OpCode == CilOpCodes.Newobj);
        var reference = (MemberReference)newobj.Operand!;
        var declaring = (GenericInstanceTypeSignature)((TypeSpecification)reference.DeclaringType!).Signature!;
        Assert.Multiple(() =>
        {
            Assert.That(declaring.TypeArguments[0].FullName, Is.EqualTo("System.String"));
            Assert.That(declaring.TypeArguments[1].FullName, Is.EqualTo("System.Boolean"));
            // ldftn still immediately precedes the newobj, as the delegate pattern requires.
            var newobjIndex = il.IndexOf(newobj);
            Assert.That(il[newobjIndex - 1].OpCode, Is.EqualTo(CilOpCodes.Ldftn));
            Assert.That(il[newobjIndex - 1].Operand, Is.SameAs(targetDefinition));
        });
    }

    [Test]
    public void AlreadyMatchingDelegateConstructionKeepsTheRecoveredInstantiation()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var fixture = new Fixture(app, app.SystemTypes.SystemObjectType, app.SystemTypes.SystemBooleanType);
        var target = new InjectedMethodAnalysisContext(fixture.Closure, "Match",
            app.SystemTypes.SystemBooleanType, R.MethodAttributes.Public,
            [app.SystemTypes.SystemObjectType]);
        fixture.Closure.Methods.Add(target);
        var caller = Caller(fixture, app, new RuntimeMethodInfoAnalysisContext(target, fixture.Closure.DeclaringAssembly));

        var module = new ModuleDefinition("DelegateKeep.dll");
        var callerDefinition = new MethodDefinition("Create", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        Definitions(module, fixture, target,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Boolean, [module.CorLibTypeFactory.Object]),
            app, callerDefinition);

        IlGenerator.GenerateIl(caller, callerDefinition);

        var newobj = callerDefinition.CilMethodBody!.Instructions.Single(i => i.OpCode == CilOpCodes.Newobj);
        var reference = (MemberReference)newobj.Operand!;
        var declaring = (GenericInstanceTypeSignature)((TypeSpecification)reference.DeclaringType!).Signature!;
        Assert.Multiple(() =>
        {
            Assert.That(declaring.TypeArguments[0].FullName, Is.EqualTo("System.Object"));
            Assert.That(declaring.TypeArguments[1].FullName, Is.EqualTo("System.Boolean"));
        });
    }

    [Test]
    public void DelegateConstructionWithArityMismatchFallsBackToDiagnosticAndNull()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var fixture = new Fixture(app, app.SystemTypes.SystemObjectType, app.SystemTypes.SystemBooleanType);
        var target = new InjectedMethodAnalysisContext(fixture.Closure, "Match",
            app.SystemTypes.SystemInt32Type, R.MethodAttributes.Public,
            [app.SystemTypes.SystemStringType, app.SystemTypes.SystemObjectType]);
        fixture.Closure.Methods.Add(target);
        var caller = Caller(fixture, app, new RuntimeMethodInfoAnalysisContext(target, fixture.Closure.DeclaringAssembly));

        var module = new ModuleDefinition("DelegateFallback.dll");
        var callerDefinition = new MethodDefinition("Create", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        Definitions(module, fixture, target,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Int32,
                [module.CorLibTypeFactory.String, module.CorLibTypeFactory.Object]),
            app, callerDefinition);

        IlGenerator.GenerateIl(caller, callerDefinition);

        var il = callerDefinition.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Newobj), Is.False);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldnull), Is.True);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call), Is.True);
        });
    }

    [Test]
    public void DelegateConstructionWithoutMethodPointerOperandFallsBackToNull()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var fixture = new Fixture(app, app.SystemTypes.SystemObjectType, app.SystemTypes.SystemBooleanType);
        var target = new InjectedMethodAnalysisContext(fixture.Closure, "Match",
            app.SystemTypes.SystemBooleanType, R.MethodAttributes.Public,
            [app.SystemTypes.SystemStringType]);
        fixture.Closure.Methods.Add(target);
        // A local holding the MethodInfo* emits a plain native int, not a method pointer.
        var pointerLocal = new LocalVariable("fn", new Register(null, "fn"),
            new RuntimeMethodInfoAnalysisContext(target, fixture.Closure.DeclaringAssembly));
        var caller = Caller(fixture, app, pointerLocal);
        caller.Locals.Add(pointerLocal);

        var module = new ModuleDefinition("DelegateNoTarget.dll");
        var callerDefinition = new MethodDefinition("Create", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        Definitions(module, fixture, target,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Boolean, [module.CorLibTypeFactory.String]),
            app, callerDefinition);
        app.SystemTypes.SystemIntPtrType.PutExtraData("AsmResolverType",
            new TypeDefinition("System", "IntPtr", TypeAttributes.Public));

        IlGenerator.GenerateIl(caller, callerDefinition);

        var il = callerDefinition.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Newobj), Is.False);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldnull), Is.True);
        });
    }
}
