using System.Reflection;
using System.Linq;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Tests;

public class Arm64CallingConventionResolverTests
{
    [Test]
    public void HomogeneousFloatAggregateDoesNotConsumeIntegerRegister()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var valueType = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.ValueType")!;
        var color = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "UnityEngine", "Color",
            valueType, TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout);
        foreach (var name in new[] { "r", "g", "b", "a" })
            color.Fields.Add(new InjectedFieldAnalysisContext(name, app.SystemTypes.SystemSingleType,
                FieldAttributes.Public, color));

        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Button",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var method = new InjectedMethodAnalysisContext(owner, "StartColorTween", app.SystemTypes.SystemVoidType,
            MethodAttributes.Public, [app.SystemTypes.SystemObjectType, color, app.SystemTypes.SystemBooleanType]);

        var operands = new Arm64CallingConventionResolver().ResolveForManaged(method);

        Assert.That(operands.Select(operand => operand.ToString()), Is.EqualTo(new[] { "X0", "X1", "V0", "X2", "X3" }));
    }

    // AAPCS64 B.4: a composite wider than 16 bytes travels as a pointer to a
    // caller-owned copy in one integer register, so later arguments - and the
    // MethodInfo - stay in the registers after it.
    [Test]
    public void WideCompositeTakesOnePointerRegister()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var valueType = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.ValueType")!;
        var loadout = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Loadout",
            valueType, TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout);
        foreach (var name in new[] { "a", "b", "c" })
            loadout.Fields.Add(new InjectedFieldAnalysisContext(name, app.SystemTypes.SystemInt64Type,
                FieldAttributes.Public, loadout));

        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Panel",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var method = new InjectedMethodAnalysisContext(owner, "SetData", app.SystemTypes.SystemVoidType,
            MethodAttributes.Public, [loadout, app.SystemTypes.SystemInt32Type]);
        var resolver = new Arm64CallingConventionResolver();

        var operands = resolver.ResolveForManaged(method);

        Assert.That(operands.Select(operand => operand.ToString()), Is.EqualTo(new[] { "X0", "X1", "X2", "X3" }));
        Assert.That(resolver.PassesByReference(loadout), Is.True);
        Assert.That(resolver.PassesByReference(app.SystemTypes.SystemInt64Type), Is.False);
    }
}
