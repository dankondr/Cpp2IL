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
}
