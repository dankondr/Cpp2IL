using System.Linq;
using System.Reflection;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Tests.Utils;

public class Arm64AggregateAbiTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    [Test]
    public void Vector3ReturnUsesOrderedFloatLanes()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var vector3 = app.AllTypes.Single(type => type.FullName == "UnityEngine.Vector3");
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "ReturnVector3", vector3,
            MethodAttributes.Static, []);
        var resolver = new Arm64CallingConventionResolver();

        var aggregate = (AggregateOperand)resolver.ReturnOperand(method);

        Assert.Multiple(() =>
        {
            Assert.That(aggregate.AggregateType, Is.SameAs(vector3));
            Assert.That(aggregate.ElementType, Is.SameAs(app.SystemTypes.SystemSingleType));
            Assert.That(aggregate.ElementWidth, Is.EqualTo(4));
            Assert.That(aggregate.Lanes.Select(lane => ((Register)lane).Name), Is.EqualTo(["V0", "V1", "V2"]));
        });
    }

    [Test]
    public void Vector3ArgumentUsesOrderedFloatLanes()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var vector3 = app.AllTypes.Single(type => type.FullName == "UnityEngine.Vector3");
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "TakeVector3",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, [vector3]);
        var resolver = new Arm64CallingConventionResolver();

        var aggregate = (AggregateOperand)resolver.ResolveForManaged(method)[0];

        Assert.That(aggregate.Lanes.Select(lane => ((Register)lane).Name), Is.EqualTo(["V0", "V1", "V2"]));
    }

    [Test]
    public void Vector3IntDoesNotUseFloatingPointAggregatePath()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var vector3Int = app.AllTypes.Single(type => type.FullName == "UnityEngine.Vector3Int");
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "TakeVector3Int",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, [vector3Int]);
        var resolver = new Arm64CallingConventionResolver();

        var operand = resolver.ResolveForManaged(method)[0];

        Assert.That(operand, Is.TypeOf<Register>());
        Assert.That(((Register)operand).Name, Is.EqualTo("X0"));
    }
}
