using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.OutputFormats;
using Cpp2IL.Core.Utils.AsmResolver;
using NUnit.Framework;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

public class AutoPropertyStubDeterminismTests
{
    // castle-recovery#167: FillAllMethodBodies fills method stubs in parallel
    // while MemberAccessibility.EnsureAccessible widens the emitted backing
    // field the moment another module's body references it. MethodStubber
    // keyed its auto-property check on the emitted FieldDefinition's access
    // flags, so the same accessor landed on a real get_/set_ body or a
    // return-default stub depending on scheduling. The decision must read the
    // declared access, which never mutates: stubbing after the widening must
    // still emit the auto-property body.
    [Test]
    public void StubbedAccessorsKeepAutoPropertyBodiesAfterFieldWidening()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var assembly = app.AssembliesByName["UnityEngine.CoreModule"];

        var holderType = assembly.InjectType("Tests", "StubbedAutoPropertyHolder",
            app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        var fieldContext = holderType.InjectFieldContext("<Value>k__BackingField",
            app.SystemTypes.SystemInt32Type, R.FieldAttributes.Private);
        var getterContext = holderType.InjectMethodContext("get_Value",
            app.SystemTypes.SystemInt32Type,
            R.MethodAttributes.Public | R.MethodAttributes.HideBySig | R.MethodAttributes.SpecialName);
        var setterContext = holderType.InjectMethodContext("set_Value",
            app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.HideBySig | R.MethodAttributes.SpecialName,
            app.SystemTypes.SystemInt32Type);
        holderType.InjectPropertyContext("Value",
            app.SystemTypes.SystemInt32Type, getterContext, setterContext, R.PropertyAttributes.None);

        var format = new StubbingFormat();
        var module = format.BuildAssemblies(app)
            .First(a => a.Name == assembly.Name.ToString()).ManifestModule!;
        var emittedType = module.GetAllTypes()
            .First(t => t.FullName == "Tests.StubbedAutoPropertyHolder");
        var emittedField = emittedType.Fields.Single(f => f.Name == "<Value>k__BackingField");

        // Reorder the parallel work the losing schedule produced: a cross-module
        // field reference widened the emitted backing field before this module's
        // stub fill ran.
        MemberAccessibility.EnsureAccessible(emittedField, fieldContext);
        Assert.That(emittedField.Attributes & FieldAttributes.FieldAccessMask,
            Is.EqualTo(FieldAttributes.Public),
            "the emitted field must have been widened for this test to exercise the losing order");

        var getter = emittedType.Methods.Single(m => m.Name == "get_Value");
        format.Fill(getter, getterContext);
        Assert.Multiple(() =>
        {
            Assert.That(getter.CilMethodBody!.Instructions.Select(i => i.OpCode.Code),
                Is.EqualTo(new[] { CilCode.Ldarg_0, CilCode.Ldfld, CilCode.Ret }),
                "get_Value must keep the auto-property body its declared evidence proves");
            Assert.That(getter.CilMethodBody.Instructions[1].Operand, Is.SameAs(emittedField));
        });

        var setter = emittedType.Methods.Single(m => m.Name == "set_Value");
        format.Fill(setter, setterContext);
        Assert.Multiple(() =>
        {
            Assert.That(setter.CilMethodBody!.Instructions.Select(i => i.OpCode.Code),
                Is.EqualTo(new[] { CilCode.Ldarg_0, CilCode.Ldarg_1, CilCode.Stfld, CilCode.Ret }),
                "set_Value must keep the auto-property body its declared evidence proves");
            Assert.That(setter.CilMethodBody.Instructions[2].Operand, Is.SameAs(emittedField));
        });
    }

    private sealed class StubbingFormat : AsmResolverDllOutputFormatEmpty
    {
        public void Fill(MethodDefinition method, MethodAnalysisContext context) =>
            FillMethodBodyWithStub(method, context);
    }
}
