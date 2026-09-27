using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils.AsmResolver;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: inconsistent-accessibility (CS0050/CS0051/CS0052/CS0053).
// Widening a referenced member must stop at the least access the emitted
// reference needs: a reference inside the member's private enclosing scope
// needs none, one inside the emitted friend scope needs only internal, and a
// genuinely external one still promotes to public. A widened member also
// cannot outrank the types its signature names.
public class ReferenceScopeAccessibilityTests
{
    private static ApplicationAnalysisContext LoadApp()
    {
        Cpp2IlApi.ResetInternalState();
        return TestGameLoader.LoadSimple2022Game();
    }

    private static (InjectedTypeAnalysisContext context, TypeDefinition emitted) AddType(
        AssemblyAnalysisContext assembly, ModuleDefinition module,
        string name, TypeAnalysisContext? baseType, TypeDefinition? emittedBase = null)
    {
        var context = assembly.InjectType("Recovered", name, baseType,
            R.TypeAttributes.NotPublic | R.TypeAttributes.Class);
        var emitted = new TypeDefinition("Recovered", name,
            TypeAttributes.NotPublic | TypeAttributes.Class)
        {
            BaseType = emittedBase ?? module.CorLibTypeFactory.Object.Type
        };
        module.TopLevelTypes.Add(emitted);
        context.PutExtraData("AsmResolverType", emitted);
        return (context, emitted);
    }

    private static (InjectedTypeAnalysisContext context, TypeDefinition emitted) AddNestedType(
        InjectedTypeAnalysisContext parent, TypeDefinition emittedParent,
        string name, TypeAnalysisContext? baseType)
    {
        var context = parent.InjectNestedType(name, baseType,
            R.TypeAttributes.NestedPrivate | R.TypeAttributes.Class);
        var emitted = new TypeDefinition(null, name,
            TypeAttributes.NestedPrivate | TypeAttributes.Class)
        {
            BaseType = emittedParent.DeclaringModule!.CorLibTypeFactory.Object.Type
        };
        emittedParent.NestedTypes.Add(emitted);
        context.PutExtraData("AsmResolverType", emitted);
        return (context, emitted);
    }

    private static (InjectedMethodAnalysisContext context, MethodDefinition emitted) AddMethod(
        InjectedTypeAnalysisContext type, TypeDefinition emittedType,
        string name, R.MethodAttributes attributes, TypeAnalysisContext[]? args = null)
    {
        var context = type.InjectMethodContext(name, type.AppContext.SystemTypes.SystemVoidType,
            attributes, args ?? []);
        var factory = emittedType.DeclaringModule!.CorLibTypeFactory;
        var emitted = new MethodDefinition(name, (MethodAttributes)context.Attributes,
            MethodSignature.CreateInstance(factory.Void,
                args?.Select(a => a.GetExtraData<TypeDefinition>("AsmResolverType")!.ToTypeSignature())
                    .ToArray() ?? []));
        emittedType.Methods.Add(emitted);
        context.PutExtraData("AsmResolverMethod", emitted);
        return (context, emitted);
    }

    private static MethodAttributes AccessOf(MethodDefinition method) =>
        method.Attributes & MethodAttributes.MemberAccessMask;

    private static TypeAttributes VisibilityOf(TypeDefinition type) =>
        type.Attributes & TypeAttributes.VisibilityMask;

    // A reference emitted inside the member's own declaring type - a sibling
    // member's body - needs no widening at all: the member and its declaring
    // chain keep declared access.
    [Test]
    public void InScopeReferenceKeepsMemberAndTypeAtDeclaredAccess()
    {
        var app = LoadApp();
        var module = new ModuleDefinition("Game.dll");
        var asm = app.InjectAssembly("Recovered.Game");
        var (outer, outerEmitted) = AddType(asm, module, "Outer", app.SystemTypes.SystemObjectType);
        var (inner, innerEmitted) = AddNestedType(outer, outerEmitted, "Inner", app.SystemTypes.SystemObjectType);
        var (member, memberEmitted) = AddMethod(inner, innerEmitted, "Secret",
            R.MethodAttributes.Private | R.MethodAttributes.HideBySig);

        using (MemberAccessibility.EmittingFrom(inner))
            MemberAccessibility.EnsureAccessible(member);

        Assert.Multiple(() =>
        {
            Assert.That(AccessOf(memberEmitted), Is.EqualTo(MethodAttributes.Private));
            Assert.That(VisibilityOf(innerEmitted), Is.EqualTo(TypeAttributes.NestedPrivate));
            Assert.That(VisibilityOf(outerEmitted), Is.EqualTo(TypeAttributes.NotPublic));
        });
    }

    // The CLR lets an enclosing type reach a nested type's private member, but
    // C# does not (CS0122): a state-machine field its owning method assigns is
    // such a reference, so the member has to widen - to internal, not public.
    [Test]
    public void EnclosingTypeReferenceWidensOnlyToInternal()
    {
        var app = LoadApp();
        var module = new ModuleDefinition("Game.dll");
        var asm = app.InjectAssembly("Recovered.Game");
        var (outer, outerEmitted) = AddType(asm, module, "Outer", app.SystemTypes.SystemObjectType);
        var (inner, innerEmitted) = AddNestedType(outer, outerEmitted, "Inner", app.SystemTypes.SystemObjectType);
        var (member, memberEmitted) = AddMethod(inner, innerEmitted, "State",
            R.MethodAttributes.Private | R.MethodAttributes.HideBySig);

        using (MemberAccessibility.EmittingFrom(outer))
            MemberAccessibility.EnsureAccessible(member);

        Assert.Multiple(() =>
        {
            Assert.That(AccessOf(memberEmitted), Is.EqualTo(MethodAttributes.Assembly));
            Assert.That(VisibilityOf(innerEmitted), Is.EqualTo(TypeAttributes.NestedAssembly));
            Assert.That(VisibilityOf(outerEmitted), Is.EqualTo(TypeAttributes.NotPublic));
        });
    }

    // A sibling top-level type in the same emitted assembly shares the
    // assembly's internals, so a reference from it widens only to internal.
    [Test]
    public void SameAssemblyReferenceWidensOnlyToInternal()
    {
        var app = LoadApp();
        var module = new ModuleDefinition("Game.dll");
        var asm = app.InjectAssembly("Recovered.Game");
        var (owner, ownerEmitted) = AddType(asm, module, "Owner", app.SystemTypes.SystemObjectType);
        var (caller, _) = AddType(asm, module, "Caller", app.SystemTypes.SystemObjectType);
        var (member, memberEmitted) = AddMethod(owner, ownerEmitted, "Work",
            R.MethodAttributes.Private | R.MethodAttributes.HideBySig);

        using (MemberAccessibility.EmittingFrom(caller))
            MemberAccessibility.EnsureAccessible(member);

        Assert.Multiple(() =>
        {
            Assert.That(AccessOf(memberEmitted), Is.EqualTo(MethodAttributes.Assembly));
            Assert.That(VisibilityOf(ownerEmitted), Is.EqualTo(TypeAttributes.NotPublic));
        });
    }

    // When an internal-scope reference widens a member whose signature names a
    // private nested type, the signature type rises to match or the member ends
    // up more visible than a type in its own signature.
    [Test]
    public void WidenedMemberRaisesPrivateSignatureTypeToMatch()
    {
        var app = LoadApp();
        var module = new ModuleDefinition("Game.dll");
        var asm = app.InjectAssembly("Recovered.Game");
        var (owner, ownerEmitted) = AddType(asm, module, "Owner", app.SystemTypes.SystemObjectType);
        var (caller, _) = AddType(asm, module, "Caller", app.SystemTypes.SystemObjectType);
        var (signature, signatureEmitted) = AddNestedType(owner, ownerEmitted, "Signature",
            app.SystemTypes.SystemObjectType);
        var (member, memberEmitted) = AddMethod(owner, ownerEmitted, "Use",
            R.MethodAttributes.Private | R.MethodAttributes.HideBySig, [signature]);

        using (MemberAccessibility.EmittingFrom(caller))
            MemberAccessibility.EnsureAccessible(member);

        Assert.Multiple(() =>
        {
            Assert.That(AccessOf(memberEmitted), Is.EqualTo(MethodAttributes.Assembly));
            Assert.That(VisibilityOf(signatureEmitted), Is.EqualTo(TypeAttributes.NestedAssembly),
                "the signature type must cover the member's new access");
            Assert.That(VisibilityOf(ownerEmitted), Is.EqualTo(TypeAttributes.NotPublic));
        });
    }

    // A containing type can widen through a reference to a different member
    // (or any other reference site). The members it already holds then expose
    // their signature types at the enlarged effective domain even though their
    // own access never changed, and the widened type's own base must cover it.
    [Test]
    public void WidenedContainerReCoversMemberSignaturesAndBaseType()
    {
        var app = LoadApp();
        var module = new ModuleDefinition("Game.dll");
        var asm = app.InjectAssembly("Recovered.Game");
        var (outer, outerEmitted) = AddType(asm, module, "Outer", app.SystemTypes.SystemObjectType);
        var (inner, innerEmitted) = AddNestedType(outer, outerEmitted, "Inner", app.SystemTypes.SystemObjectType);
        var (signature, signatureEmitted) = AddType(asm, module, "Signature", app.SystemTypes.SystemObjectType);
        innerEmitted.BaseType = signatureEmitted;
        AddMethod(inner, innerEmitted, "Use",
            R.MethodAttributes.Public | R.MethodAttributes.HideBySig, [signature]);
        var (other, _) = AddMethod(inner, innerEmitted, "Other",
            R.MethodAttributes.Private | R.MethodAttributes.HideBySig);

        MemberAccessibility.EnsureAccessible(other); // an unscoped, external reference

        Assert.Multiple(() =>
        {
            Assert.That(VisibilityOf(innerEmitted), Is.EqualTo(TypeAttributes.NestedPublic));
            Assert.That(VisibilityOf(signatureEmitted), Is.EqualTo(TypeAttributes.Public),
                "a widened type's base type and its members' signature types must cover its new domain");
        });
    }

    // Without an emitting scope the old conservative answer stays: a populate-
    // time or otherwise unscoped reference promotes the member to public.
    [Test]
    public void UnscopedReferenceStillPromotesToPublic()
    {
        var app = LoadApp();
        var module = new ModuleDefinition("Game.dll");
        var asm = app.InjectAssembly("Recovered.Game");
        var (owner, ownerEmitted) = AddType(asm, module, "Owner", app.SystemTypes.SystemObjectType);
        var (member, memberEmitted) = AddMethod(owner, ownerEmitted, "Work",
            R.MethodAttributes.Private | R.MethodAttributes.HideBySig);

        MemberAccessibility.EnsureAccessible(member);

        Assert.Multiple(() =>
        {
            Assert.That(AccessOf(memberEmitted), Is.EqualTo(MethodAttributes.Public));
            Assert.That(VisibilityOf(ownerEmitted), Is.EqualTo(TypeAttributes.Public));
        });
    }
}
