using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: compiler-generated-name — the decompiler prints pseudo-calls
// (__ldftn/__ldtoken/<PrivateImplementationDetails>) where the emitted IL does not
// match a shape it can lower. Two patterns were Cpp2IL's doing:
//
//  * RuntimeHelpers.InitializeArray(array, fieldHandle) calls carried a spurious
//    `castclass System.Array` on the array argument, because SZARRAY/ARRAY type
//    contexts reported no base type. That broke ILSpy's InitializeArray pattern
//    match, leaving a raw `__ldtoken(<PrivateImplementationDetails>.__field)` in
//    the output. Array contexts now report System.Array as their base.
//  * A standalone `ldftn` on an instance method — recovered for a spilled
//    method-pointer slot — is valid CIL but has no C# spelling, so it prints as
//    `__ldftn`. ldftn now survives only where C# can spell it: static methods and
//    the function-pointer argument of a delegate (object, native int) .ctor.
//    Everywhere else the slot keeps the native-int zero placeholder.
public class CompilerGeneratedNameTests
{
    private static TypeAnalysisContext SystemRuntimeFieldHandle(ApplicationAnalysisContext app) =>
        app.AssembliesByName["mscorlib"].GetTypeByFullName("System.RuntimeFieldHandle")!;

    private static TypeAnalysisContext SystemArray(ApplicationAnalysisContext app) =>
        app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Array")!;

    private static TypeAnalysisContext SystemMulticastDelegate(ApplicationAnalysisContext app) =>
        app.AssembliesByName["mscorlib"].GetTypeByFullName("System.MulticastDelegate")!;

    [Test]
    public void InitializeArrayArgumentEmitsNoCastClassToSystemArray()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var assembly = app.AssembliesByName["UnityEngine.CoreModule"];
        var bytes = new SzArrayTypeAnalysisContext(app.SystemTypes.SystemByteType);
        var holder = new InjectedTypeAnalysisContext(assembly, "Tests", "StaticData",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var blob = holder.InjectFieldContext("Blob", bytes,
            R.FieldAttributes.Public | R.FieldAttributes.Static);
        var runtimeHelpers = new InjectedTypeAnalysisContext(assembly,
            "System.Runtime.CompilerServices", "RuntimeHelpers",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var initializeArray = runtimeHelpers.InjectMethodContext("InitializeArray",
            app.SystemTypes.SystemVoidType, R.MethodAttributes.Public | R.MethodAttributes.Static,
            SystemArray(app), SystemRuntimeFieldHandle(app));
        var fieldInfo = new RuntimeFieldInfoAnalysisContext(blob, assembly);
        var bytesLocal = new LocalVariable("bytes", new Register(null, "bytes")) { Type = bytes };

        var module = new ModuleDefinition("ArrayInit.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemByteType, app.SystemTypes.SystemIntPtrType,
            app.SystemTypes.SystemVoidType, app.SystemTypes.SystemObjectType,
            SystemArray(app), SystemRuntimeFieldHandle(app));
        var holderDefinition = new TypeDefinition("Tests", "StaticData",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(holderDefinition);
        holder.PutExtraData("AsmResolverType", holderDefinition);
        var blobDefinition = new FieldDefinition("Blob", FieldAttributes.Public | FieldAttributes.Static,
            new FieldSignature(module.CorLibTypeFactory.Byte.MakeSzArrayType()));
        holderDefinition.Fields.Add(blobDefinition);
        blob.PutExtraData("AsmResolverField", blobDefinition);
        var helpersDefinition = new TypeDefinition("System.Runtime.CompilerServices", "RuntimeHelpers",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(helpersDefinition);
        runtimeHelpers.PutExtraData("AsmResolverType", helpersDefinition);
        var initializeArrayDefinition = new MethodDefinition("InitializeArray",
            MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void,
            [
                module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "Array")
                    .ToTypeSignature(true),
                module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "RuntimeFieldHandle")
                    .ToTypeSignature(true)
            ]));
        helpersDefinition.Methods.Add(initializeArrayDefinition);
        initializeArray.PutExtraData("AsmResolverMethod", initializeArrayDefinition);

        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.CallVoid, initializeArray, bytesLocal, fieldInfo),
            new(1, OpCode.Return)], [bytesLocal]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(bytes.BaseType?.FullName, Is.EqualTo("System.Array"));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Castclass), Is.False,
                () => "no castclass between the array local and InitializeArray:\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldtoken), Is.True,
                "the field operand keeps its ldtoken emission");
        });
    }

    [Test]
    public void StandaloneInstanceMethodHandleKeepsNullPointerPlaceholder()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var assembly = app.AssembliesByName["UnityEngine.CoreModule"];
        var target = new InjectedTypeAnalysisContext(assembly, "Tests", "Widget",
                app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class)
            .InjectMethodContext("OnEvent", app.SystemTypes.SystemVoidType, R.MethodAttributes.Public);
        var widget = target.DeclaringType!;
        var methodInfo = new RuntimeMethodInfoAnalysisContext(target, assembly);
        var slot = new LocalVariable("slot", new Register(null, "slot"))
            { Type = app.SystemTypes.SystemIntPtrType };
        var module = new ModuleDefinition("SpilledFn.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemIntPtrType,
            app.SystemTypes.SystemVoidType, app.SystemTypes.SystemObjectType);
        var widgetDefinition = new TypeDefinition("Tests", "Widget",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(widgetDefinition);
        widget.PutExtraData("AsmResolverType", widgetDefinition);
        var targetDefinition = new MethodDefinition("OnEvent", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        widgetDefinition.Methods.Add(targetDefinition);
        target.PutExtraData("AsmResolverMethod", targetDefinition);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, slot, methodInfo),
            new(1, OpCode.Return)], [slot]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldftn), Is.False,
                () => "an instance-method pointer outside a delegate .ctor cannot print as C#:\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Conv_I), Is.True,
                "the slot keeps the native-int zero placeholder");
        });
    }

    [Test]
    public void DelegateCtorFunctionPointerSlotStillEmitsLdftn()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var assembly = app.AssembliesByName["UnityEngine.CoreModule"];
        var delegateType = new InjectedTypeAnalysisContext(assembly, "Tests", "Handler",
            SystemMulticastDelegate(app),
            R.TypeAttributes.Public | R.TypeAttributes.Class | R.TypeAttributes.Sealed);
        var ctor = delegateType.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.HideBySig
                | R.MethodAttributes.SpecialName | R.MethodAttributes.RTSpecialName,
            app.SystemTypes.SystemObjectType, app.SystemTypes.SystemIntPtrType);
        delegateType.InjectMethodContext("Invoke", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public);
        var widget = new InjectedTypeAnalysisContext(assembly, "Tests", "Widget",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var target = widget.InjectMethodContext("OnEvent", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public);
        var methodInfo = new RuntimeMethodInfoAnalysisContext(target, assembly);
        var receiver = new LocalVariable("handler", new Register(null, "handler")) { Type = delegateType };
        var targetObject = new LocalVariable("target", new Register(null, "target")) { Type = widget };

        var module = new ModuleDefinition("DelegateCtor.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemIntPtrType,
            app.SystemTypes.SystemVoidType, app.SystemTypes.SystemObjectType);
        var handlerDefinition = new TypeDefinition("Tests", "Handler",
            TypeAttributes.Public | TypeAttributes.Class | TypeAttributes.Sealed,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "MulticastDelegate"));
        module.TopLevelTypes.Add(handlerDefinition);
        delegateType.PutExtraData("AsmResolverType", handlerDefinition);
        var ctorDefinition = new MethodDefinition(".ctor", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void,
            [module.CorLibTypeFactory.Object, module.CorLibTypeFactory.IntPtr]));
        ctorDefinition.ParameterDefinitions.Add(new ParameterDefinition(1, "o", 0));
        ctorDefinition.ParameterDefinitions.Add(new ParameterDefinition(2, "ptr", 0));
        handlerDefinition.Methods.Add(ctorDefinition);
        ctor.PutExtraData("AsmResolverMethod", ctorDefinition);
        var widgetDefinition = new TypeDefinition("Tests", "Widget",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(widgetDefinition);
        widget.PutExtraData("AsmResolverType", widgetDefinition);
        var targetDefinition = new MethodDefinition("OnEvent", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        widgetDefinition.Methods.Add(targetDefinition);
        target.PutExtraData("AsmResolverMethod", targetDefinition);

        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.CallVoid, ctor, receiver, targetObject, methodInfo),
            new(1, OpCode.Return)], [receiver, targetObject]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldftn), Is.True,
                () => "the (object, native int) slot of a delegate .ctor folds into newobj:\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Newobj), Is.True,
                "the delegate .ctor lowers to newobj");
        });
    }
}
