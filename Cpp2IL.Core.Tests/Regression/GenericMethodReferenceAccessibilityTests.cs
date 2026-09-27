using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils.AsmResolver;
using LibCpp2IL.BinaryStructures;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: protected-member-ldftn (CS1540). A generic method
// reference - ldftn/call/callvirt/ldtoken of a ConcreteGenericMethodAnalysisContext
// - resolves to the base definition, so emitting it must widen that definition
// exactly like a plain reference would. The generic descriptor path never ran
// EnsureAccessible, so a protected generic method kept `family` while its
// decompiled reference (e.g. `Base.Find<T>` as a method group, or the same
// call through a base-typed receiver) needs at least the internal half of
// protected internal inside the same emitted assembly.
public class GenericMethodReferenceAccessibilityTests
{
    private static ApplicationAnalysisContext LoadApp()
    {
        Cpp2IlApi.ResetInternalState();
        return TestGameLoader.LoadSimple2022Game();
    }

    private static (InjectedTypeAnalysisContext context, TypeDefinition emitted) AddType(
        AssemblyAnalysisContext assembly, ModuleDefinition module,
        string name, TypeAnalysisContext? baseType)
    {
        var context = assembly.InjectType("Recovered", name, baseType,
            R.TypeAttributes.NotPublic | R.TypeAttributes.Class);
        var emitted = new TypeDefinition("Recovered", name,
            TypeAttributes.NotPublic | TypeAttributes.Class)
        {
            BaseType = module.CorLibTypeFactory.Object.Type
        };
        module.TopLevelTypes.Add(emitted);
        context.PutExtraData("AsmResolverType", emitted);
        return (context, emitted);
    }

    private static (InjectedMethodAnalysisContext context, MethodDefinition emitted) AddMethod(
        InjectedTypeAnalysisContext type, TypeDefinition emittedType,
        string name, R.MethodAttributes attributes, ModuleDefinition module)
    {
        var context = type.InjectMethodContext(name, type,
            attributes, []);
        var emitted = new MethodDefinition(name, (MethodAttributes)context.Attributes,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Object));
        emittedType.Methods.Add(emitted);
        context.PutExtraData("AsmResolverMethod", emitted);
        return (context, emitted);
    }

    private static MethodAttributes AccessOf(MethodDefinition method) =>
        method.Attributes & MethodAttributes.MemberAccessMask;

    // A same-assembly reference to a protected generic method - the ldftn site
    // `__ldftn(Base.Find<T>)` inside a derived or sibling type - needs the
    // internal half of protected internal; `family` alone leaves the emitted
    // C# unbuildable (CS1540) because the qualifier names the declaring type.
    [Test]
    public void SameAssemblyGenericMethodReferenceWidensToProtectedInternal()
    {
        var app = LoadApp();
        var module = new ModuleDefinition("Game.dll");
        var asm = app.InjectAssembly("Recovered.Game");
        var (owner, ownerEmitted) = AddType(asm, module, "Owner", app.SystemTypes.SystemObjectType);
        var (caller, _) = AddType(asm, module, "Caller", app.SystemTypes.SystemObjectType);
        var (member, memberEmitted) = AddMethod(owner, ownerEmitted, "Find",
            R.MethodAttributes.Family | R.MethodAttributes.HideBySig
                | R.MethodAttributes.Virtual | R.MethodAttributes.NewSlot, module);
        member.GenericParameters.Add(new GenericParameterTypeAnalysisContext("T", 0,
            Il2CppTypeEnum.IL2CPP_TYPE_MVAR, 0, member));
        // T's own signature leaf is a generic parameter - it widens nothing, so
        // only the member access itself is under test.
        member.ReturnType = member.GenericParameters[0];
        var concrete = member.MakeGenericInstanceMethod(owner);

        using (MemberAccessibility.EmittingFrom(caller))
            concrete.ToMethodDescriptor();

        Assert.Multiple(() =>
        {
            Assert.That(AccessOf(memberEmitted), Is.EqualTo(MethodAttributes.FamilyOrAssembly));
            Assert.That(memberEmitted.DeclaringType!.Attributes & TypeAttributes.VisibilityMask,
                Is.EqualTo(TypeAttributes.NotPublic),
                "the member widens, not its containing type");
        });
    }

    // The same reference without an emitting scope keeps the conservative
    // populate-time answer: the member promotes to public, matching what a
    // plain method reference has always done.
    [Test]
    public void UnscopedGenericMethodReferenceStillPromotesToPublic()
    {
        var app = LoadApp();
        var module = new ModuleDefinition("Game.dll");
        var asm = app.InjectAssembly("Recovered.Game");
        var (owner, ownerEmitted) = AddType(asm, module, "Owner", app.SystemTypes.SystemObjectType);
        var (member, memberEmitted) = AddMethod(owner, ownerEmitted, "Find",
            R.MethodAttributes.Family | R.MethodAttributes.HideBySig, module);
        member.GenericParameters.Add(new GenericParameterTypeAnalysisContext("T", 0,
            Il2CppTypeEnum.IL2CPP_TYPE_MVAR, 0, member));
        member.ReturnType = member.GenericParameters[0];
        var concrete = member.MakeGenericInstanceMethod(owner);

        concrete.ToMethodDescriptor();

        Assert.That(AccessOf(memberEmitted), Is.EqualTo(MethodAttributes.Public));
    }

    // Generic methods on external runtime types (e.g. `List<T>.Add` reached by
    // ldftn) resolve to definitions we do not emit: the reference must not
    // attempt widening.
    [Test]
    public void ExternalGenericMethodReferenceKeepsDeclaredAccess()
    {
        var app = LoadApp();
        var module = new ModuleDefinition("Game.dll");
        var asm = app.InjectAssembly("Recovered.Game");
        var (caller, _) = AddType(asm, module, "Caller", app.SystemTypes.SystemObjectType);
        var external = app.AssembliesByName["mscorlib"];
        var owner = new InjectedTypeAnalysisContext(external, "Recovered", "ExternalOwner",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var ownerEmitted = new TypeDefinition("Recovered", "ExternalOwner",
            TypeAttributes.Public | TypeAttributes.Class);
        owner.PutExtraData("AsmResolverType", ownerEmitted);
        var (member, memberEmitted) = AddMethod(owner, ownerEmitted, "Find",
            R.MethodAttributes.Family | R.MethodAttributes.HideBySig, module);
        member.GenericParameters.Add(new GenericParameterTypeAnalysisContext("T", 0,
            Il2CppTypeEnum.IL2CPP_TYPE_MVAR, 0, member));
        member.ReturnType = member.GenericParameters[0];
        var concrete = member.MakeGenericInstanceMethod(owner);

        using (MemberAccessibility.EmittingFrom(caller))
            concrete.ToMethodDescriptor();

        Assert.That(AccessOf(memberEmitted), Is.EqualTo(MethodAttributes.Family));
    }
}
