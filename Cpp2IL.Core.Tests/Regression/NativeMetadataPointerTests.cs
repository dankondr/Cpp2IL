using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: IL emission — native metadata pointers into pointer slots
// (castle-recovery#134). An Il2CppClass<T> operand feeding a System.IntPtr slot
// is the type's runtime-metadata pointer: the honest emission is ldtoken +
// RuntimeTypeHandle::get_Value (what TypeHandle.Value is under IL2CPP), not a
// diagnosed native-int zero. An Il2CppMethodInfo operand for a .ctor names a
// constructor handle: ldftn/GetMethod cannot spell it, but GetConstructor can.
public class NativeMetadataPointerTests
{
    [Test]
    public void RuntimeClassOperandIntoIntPtrSlotEmitsHandleValue()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var stringType = app.SystemTypes.SystemStringType;
        var runtimeClass = new RuntimeClassTypeAnalysisContext(stringType,
            app.AssembliesByName["UnityEngine.CoreModule"]);
        var slot = new LocalVariable("slot", new Register(null, "slot"))
            { Type = app.SystemTypes.SystemIntPtrType };
        var module = new ModuleDefinition("NativeMetadataPointer.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemIntPtrType,
            app.SystemTypes.SystemVoidType, app.SystemTypes.SystemObjectType, stringType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, slot, runtimeClass),
            new(1, OpCode.Return)], [slot]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldtoken
                    && i.Operand?.ToString()?.Contains("System.String") == true),
                Is.True, () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call
                    && i.Operand?.ToString()?.Contains("get_Value") == true),
                Is.True, "the pointer slot carries the type's handle value");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand?.ToString()?.Contains("native metadata pointer") == true),
                Is.False, "the slot is recovered, not diagnosed");
        });
    }

    [Test]
    public void ConstructorMethodInfoIntoIntPtrSlotEmitsGetConstructor()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("ConstructorHandle.dll");
        var declaringType = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "Widget", app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        declaringType.PutExtraData("AsmResolverType",
            new TypeDefinition("Tests", "Widget",
                TypeAttributes.Public | TypeAttributes.Class,
                module.CorLibTypeFactory.Object.Type));
        var ctor = declaringType.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.HideBySig
                | R.MethodAttributes.SpecialName | R.MethodAttributes.RTSpecialName);
        var methodInfo = new RuntimeMethodInfoAnalysisContext(ctor, declaringType.DeclaringAssembly);
        var slot = new LocalVariable("slot", new Register(null, "slot"))
            { Type = app.SystemTypes.SystemIntPtrType };
        SeedCorLibTypes(app, module, app.SystemTypes.SystemIntPtrType,
            app.SystemTypes.SystemVoidType, app.SystemTypes.SystemObjectType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, slot, methodInfo),
            new(1, OpCode.Return)], [slot]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Callvirt
                    && i.Operand?.ToString()?.Contains("GetConstructor") == true),
                Is.True, () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Callvirt
                    && i.Operand?.ToString()?.Contains("get_MethodHandle") == true),
                Is.True, "the constructor lookup carries the runtime method handle");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call
                    && i.Operand?.ToString()?.Contains("get_Value") == true),
                Is.True, "the slot carries the IntPtr the handle wraps");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand?.ToString()?.Contains("cannot be spelled") == true),
                Is.False, "the .ctor handle is spelled, not diagnosed");
        });
    }
}
