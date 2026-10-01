using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.OutputFormats;
using R = System.Reflection;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: compile bucket invalid-conversion (castle-recovery#139). A
// `[ref + K]` load or store resolved onto an instance field of a value type T
// asks for a `&T` receiver: the field's declaring type is a value type, so
// ldfld/stfld/ldobj/stobj need a managed pointer, not the bare reference the
// local emits. `unbox` is the only verifier-legal ref -> &T bridge: it asserts
// the reference boxes T and throws InvalidCastException when the assertion is
// wrong instead of dereferencing a reference as a pointer (which ILSpy prints
// as `*(T*)(nint)ref` -> CS0030).
public class BoxedValueFieldAccessTests
{
    // An enum with its `value__` slot plus the AsmResolver stubs the emitted IL
    // has to name: the enum token for `unbox` and the field token for the raw
    // access.
    private static (InjectedTypeAnalysisContext choice, InjectedFieldAnalysisContext valueField)
        InjectEnum(ApplicationAnalysisContext app, ModuleDefinition module)
    {
        var mscorlib = app.AssembliesByName["mscorlib"];
        var enumBase = mscorlib.GetTypeByFullName("System.Enum")
            ?? new InjectedTypeAnalysisContext(mscorlib, "System", "Enum",
                app.SystemTypes.SystemValueTypeType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var choice = new InjectedTypeAnalysisContext(mscorlib, "Tests", "Choice",
            enumBase, R.TypeAttributes.Public | R.TypeAttributes.Sealed
                | R.TypeAttributes.SequentialLayout);
        var valueField = choice.InjectFieldContext("value__", app.SystemTypes.SystemInt32Type,
            R.FieldAttributes.Public);

        var corlib = module.CorLibTypeFactory;
        var enumDefinition = new TypeDefinition("Tests", "Choice",
            TypeAttributes.Public | TypeAttributes.Sealed,
            corlib.CorLibScope.CreateTypeReference("System", "Enum"));
        var valueDefinition = new FieldDefinition("value__",
            FieldAttributes.Public | FieldAttributes.SpecialName | FieldAttributes.RuntimeSpecialName,
            new FieldSignature(corlib.Int32));
        enumDefinition.Fields.Add(valueDefinition);
        module.TopLevelTypes.Add(enumDefinition);
        choice.PutExtraData("AsmResolverType", enumDefinition);
        valueField.PutExtraData("AsmResolverField", valueDefinition);
        return (choice, valueField);
    }

    [Test]
    public void EnumUnderlyingLoadOnReferenceReceiverUnboxes()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("Boxed.dll");
        var (choice, valueField) = InjectEnum(app, module);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemObjectType, app.SystemTypes.SystemVoidType);
        var holder = new LocalVariable("holder", new Register(null, "x0"))
            { Type = app.SystemTypes.SystemObjectType };
        var result = new LocalVariable("result", new Register(null, "x8"))
            { Type = app.SystemTypes.SystemInt32Type };
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, result, new FieldReference(valueField, holder, 0x10)),
            new(1, OpCode.Return)], [holder, result]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Unbox), Is.True,
            () => string.Join("\n", il.Select(i => i.ToString())));

        DecompilerMemberAccessRewrites.Apply(method);

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Unbox_Any), Is.True,
                () => "unbox + ldobj fuses to unbox.any\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Unbox), Is.False,
                "no bare unbox survives once its ldobj consumer fused");
        });
    }

    [Test]
    public void EnumUnderlyingStoreOnReferenceReceiverUnboxes()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("Boxed.dll");
        var (choice, valueField) = InjectEnum(app, module);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemObjectType, app.SystemTypes.SystemVoidType);
        var holder = new LocalVariable("holder", new Register(null, "x0"))
            { Type = app.SystemTypes.SystemObjectType };
        var source = new LocalVariable("source", new Register(null, "x1"))
            { Type = app.SystemTypes.SystemInt32Type };
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, new FieldReference(valueField, holder, 0x10), source),
            new(1, OpCode.Return)], [holder, source]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Unbox_Any), Is.True,
            () => string.Join("\n", il.Select(i => i.ToString())));

        DecompilerMemberAccessRewrites.Apply(method);

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Unbox_Any), Is.True,
                "a store needs a mutable managed pointer - unbox.any into a scratch local");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stobj), Is.True,
                "the value__ store survives on the managed pointer unbox.any produced");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stfld
                    && i.Operand == null), Is.False);
        });
    }
}
