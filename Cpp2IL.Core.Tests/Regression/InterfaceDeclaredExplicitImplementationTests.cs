using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: interface-return-type-mismatch (CS0738) and
// interface-member-not-implemented (CS0535) from default interface
// implementations. IL2CPP records no vtable and no interface offsets for
// interface typedefs, so the .override rows of explicit implementations
// declared on an interface must be recovered from the compiled member name
// ("Ns.IFace<T>.Member"). Without them the emitted assembly loses the
// MethodImpl bindings, and decompiled implementors bind the interface member
// to a same-named member with a different return type.
public class InterfaceDeclaredExplicitImplementationTests
{
    private const MethodAttributes InterfaceMember =
        MethodAttributes.Public | MethodAttributes.Abstract | MethodAttributes.Virtual | MethodAttributes.NewSlot | MethodAttributes.HideBySig;

    private const MethodAttributes ExplicitImplementation =
        MethodAttributes.Private | MethodAttributes.Final | MethodAttributes.Virtual | MethodAttributes.HideBySig;

    private const TypeAttributes Interface =
        TypeAttributes.Public | TypeAttributes.Interface | TypeAttributes.Abstract;

    private static ApplicationAnalysisContext LoadApp()
    {
        Cpp2IlApi.ResetInternalState();
        return TestGameLoader.LoadSimple2022Game();
    }

    private static GenericParameterTypeAnalysisContext GenericParameter(TypeAnalysisContext owner, string name, int index)
    {
        var parameter = new GenericParameterTypeAnalysisContext(name, index, Il2CppTypeEnum.IL2CPP_TYPE_VAR, 0, owner);
        owner.GenericParameters.Add(parameter);
        return parameter;
    }

    [Test]
    public void ExplicitImplementationDeclaredOnInterface()
    {
        var app = LoadApp();
        var assembly = app.AssembliesByName["mscorlib"];

        var iface = assembly.InjectType("Recovered", "ISource", null, Interface);
        var getResult = iface.InjectMethodContext("GetResult",
            app.SystemTypes.SystemInt32Type, InterfaceMember, [app.SystemTypes.SystemInt16Type]);

        var implementor = assembly.InjectType("Recovered", "IExtendedSource", null, Interface);
        implementor.InterfaceContexts.Add(iface);
        var explicitImpl = implementor.InjectMethodContext("Recovered.ISource.GetResult",
            app.SystemTypes.SystemInt32Type, ExplicitImplementation, [app.SystemTypes.SystemInt16Type]);

        Assert.That(explicitImpl.Overrides, Is.EqualTo(new[] { getResult }));
    }

    [Test]
    public void ExplicitImplementationOnGenericInterfaceUsesInstantiation()
    {
        var app = LoadApp();
        var assembly = app.AssembliesByName["mscorlib"];

        // IFaceBase carries a same-named overload; the generic instantiation
        // must pick the member whose signature actually matches.
        var ifaceBase = assembly.InjectType("Recovered", "ISourceBase", null, Interface);
        ifaceBase.InjectMethodContext("GetResult",
            app.SystemTypes.SystemVoidType, InterfaceMember, [app.SystemTypes.SystemInt16Type]);

        var iface = assembly.InjectType("Recovered", "ISource`1", null, Interface);
        var ifaceParam = GenericParameter(iface, "TSource", 0);
        var genericGetResult = iface.InjectMethodContext("GetResult",
            ifaceParam, InterfaceMember, [app.SystemTypes.SystemInt16Type]);
        iface.InterfaceContexts.Add(ifaceBase);

        var implementor = assembly.InjectType("Recovered", "IExtendedSource`1", null, Interface);
        var implementorParam = GenericParameter(implementor, "T", 0);
        implementor.InterfaceContexts.Add(new GenericInstanceTypeAnalysisContext(iface, [implementorParam]));
        var explicitImpl = implementor.InjectMethodContext("Recovered.ISource<T>.GetResult",
            implementorParam, ExplicitImplementation, [app.SystemTypes.SystemInt16Type]);

        var overrides = explicitImpl.Overrides;
        Assert.Multiple(() =>
        {
            Assert.That(overrides, Has.Count.EqualTo(1));
            var concrete = (ConcreteGenericMethodAnalysisContext)overrides[0];
            Assert.That(concrete.BaseMethodContext, Is.SameAs(genericGetResult));
            Assert.That(concrete.DeclaringType, Is.TypeOf<GenericInstanceTypeAnalysisContext>()
                .With.Property(nameof(GenericInstanceTypeAnalysisContext.GenericType)).SameAs(iface));
        });
    }

    [Test]
    public void DottedNameOnInterfaceWithoutMatchingMemberDoesNotBind()
    {
        var app = LoadApp();
        var assembly = app.AssembliesByName["mscorlib"];

        var iface = assembly.InjectType("Recovered", "ISource", null, Interface);
        iface.InjectMethodContext("GetResult",
            app.SystemTypes.SystemInt32Type, InterfaceMember, [app.SystemTypes.SystemInt16Type]);

        var implementor = assembly.InjectType("Recovered", "IExtendedSource", null, Interface);
        implementor.InterfaceContexts.Add(iface);
        // Same name, arity mismatch: the encoded interface is generic, the
        // implemented one is not, so no MethodImpl must be emitted.
        var explicitImpl = implementor.InjectMethodContext("Recovered.ISource<T>.GetResult",
            app.SystemTypes.SystemInt32Type, ExplicitImplementation, [app.SystemTypes.SystemInt16Type]);

        Assert.That(explicitImpl.Overrides, Is.Empty);
    }

    [Test]
    public void PlainInterfaceMembersDoNotSelfBind()
    {
        var app = LoadApp();
        var assembly = app.AssembliesByName["mscorlib"];

        var iface = assembly.InjectType("Recovered", "ISource", null, Interface);
        var getResult = iface.InjectMethodContext("GetResult",
            app.SystemTypes.SystemInt32Type, InterfaceMember, [app.SystemTypes.SystemInt16Type]);

        Assert.That(getResult.Overrides, Is.Empty);
    }
}
