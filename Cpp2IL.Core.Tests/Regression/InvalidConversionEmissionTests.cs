using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Model.CustomAttributes;
using R = System.Reflection;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: compile bucket invalid-conversion (castle-recovery#81).
// A runtime-class operand lowered into an object slot keeps the Type that
// LoadOperand emits (ldtoken + GetTypeFromHandle); reporting the operand as
// IntPtr made the store coercion emit box IntPtr over the Type, which ilspy
// decompiles to the invalid cast (IntPtr)typeof(T). A ref struct (IsByRefLike)
// can never be boxed, so an unbridgeable coercion defaults the slot instead of
// emitting box <ref struct> - and emits a decompiler-issue diagnostic so the
// dropped operand stays measured.
public class InvalidConversionEmissionTests
{
    [Test]
    public void RuntimeClassIntoObjectSlotEmitsTypeNotBoxedIntPtr()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var runtimeClass = new RuntimeClassTypeAnalysisContext(app.SystemTypes.SystemStringType,
            app.AssembliesByName["UnityEngine.CoreModule"]);
        var slot = new LocalVariable("slot", new Register(null, "slot"))
            { Type = app.SystemTypes.SystemObjectType };
        var module = new ModuleDefinition("KlassSlot.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemStringType,
            app.SystemTypes.SystemObjectType, app.SystemTypes.SystemIntPtrType,
            app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, slot, runtimeClass),
            new(1, OpCode.Return)], [slot]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldtoken), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call
                    && i.Operand?.ToString().Contains("GetTypeFromHandle") == true), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Box), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void ByRefLikePointerIntoObjectSlotDefaultsInsteadOfBoxing()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var mscorlib = app.AssembliesByName["mscorlib"];
        var attribute = new InjectedTypeAnalysisContext(mscorlib,
            "System.Runtime.CompilerServices", "IsByRefLikeAttribute",
            app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class | R.TypeAttributes.Sealed);
        var attributeCtor = attribute.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.HideBySig
                | R.MethodAttributes.SpecialName | R.MethodAttributes.RTSpecialName);
        var refStruct = new InjectedTypeAnalysisContext(mscorlib, "Tests", "ByRefBuffer",
            app.SystemTypes.SystemValueTypeType,
            R.TypeAttributes.Public | R.TypeAttributes.Sealed | R.TypeAttributes.SequentialLayout);
        refStruct.CustomAttributes = [new AnalyzedCustomAttribute(attributeCtor)];
        var slot = new LocalVariable("slot", new Register(null, "slot"))
            { Type = app.SystemTypes.SystemObjectType };
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"))
            { Type = new ByRefTypeAnalysisContext(refStruct) };
        var module = new ModuleDefinition("RefStruct.dll");
        SeedCorLibTypes(app, module, refStruct, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, slot, pointer),
            new(1, OpCode.Return)], [slot, pointer]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Box), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldobj), Is.False,
                "the managed pointer is dropped before any dereference is emitted");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldnull), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text
                    && text.Contains("Ref struct cannot cross")), Is.True,
                "the dropped ref struct must stay an explicit diagnostic");
        });
    }
}
