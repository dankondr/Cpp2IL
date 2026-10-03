using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// castle-recovery#327: type-test narrowing can resolve a virtual call's
// declaring type to a type the caller cannot name (an internal corlib
// subclass). The member reference keeps its declared accessibility, so the
// call must respell through the slot's visible base declaration - virtual
// dispatch reaches the same override.
public class NarrowedCalleeVisibilityTests
{
    [Test]
    public void CallvirtOnHiddenDeclaringTypeResolvesTheVisibleBase()
    {
        var appContext = TestGameLoader.LoadSimple2019Game();
        var ordinal = appContext.AssembliesByName["mscorlib"].GetTypeByFullName("System.OrdinalComparer")!;
        var narrowed = ordinal.Methods.First(m => m.Name == "Equals" && m.Parameters.Count == 2);
        var caller = new InjectedMethodAnalysisContext(
            new InjectedTypeAnalysisContext(appContext.AssembliesByName["UnityEngine.CoreModule"],
                "Game", "Caller", appContext.SystemTypes.SystemObjectType, R.TypeAttributes.Public),
            "M", appContext.SystemTypes.SystemVoidType, R.MethodAttributes.Public | R.MethodAttributes.Static,
            []);

        var substitute = InaccessibleCalleeRecovery.TrySubstitute(narrowed);
        using (Assert.EnterMultipleScope())
        {
            Assert.That(InaccessibleCalleeRecovery.IsVisibleFrom(narrowed, caller), Is.False,
                "a public member on an internal declaring type is not nameable");
            Assert.That(substitute?.DeclaringType?.FullName, Is.EqualTo("System.StringComparer"));
            Assert.That(substitute != null && InaccessibleCalleeRecovery.IsVisibleFrom(substitute, caller),
                Is.True, "the base-declared method is nameable");
        }
    }
}
