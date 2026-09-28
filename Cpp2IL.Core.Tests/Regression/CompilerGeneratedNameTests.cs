using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.DotNet.Signatures.Parsing;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Model.CustomAttributes;
using Cpp2IL.Core.Utils.AsmResolver;
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
//    `__ldftn`. When the pointer lands in a local that no instruction ever
//    loads, the store is dead and the whole Move drops out. Live destinations
//    (fields, call arguments, locals that are read) keep their ldftn; replacing
//    the pointer with a placeholder would silently discard a real value.
//  * A standalone `ldtoken <field>` — recovered for a RuntimeFieldHandle or
//    IntPtr slot — is likewise unspellable (`__ldtoken`). Non-initializer
//    loads now go through `typeof(D).GetField(name, flags).FieldHandle`;
//    only the field argument of RuntimeHelpers.InitializeArray keeps the
//    token, because ilspy folds that call shape into an array initializer.
//  * Nested types that kept their own namespace were emitted into
//    custom-attribute blobs as "Parent+Ns.Child", which nothing resolves;
//    the blob SerString must be the ECMA-335 canonical "Ns.Parent+Child".
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
    public void StandaloneInstanceMethodPointerStoreToUnreadLocalIsDropped()
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
                () => "the dead method-pointer store drops entirely:\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Conv_I), Is.False,
                "no zero placeholder is substituted for the dropped pointer");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stloc || i.OpCode == CilOpCodes.Stloc_S
                || i.OpCode == CilOpCodes.Stloc_0 || i.OpCode == CilOpCodes.Stloc_1
                || i.OpCode == CilOpCodes.Stloc_2 || i.OpCode == CilOpCodes.Stloc_3), Is.False,
                "the store itself is gone, not just the load");
        });
    }

    [Test]
    public void InstanceMethodPointerStoreToLiveLocalEmitsReflectionLookup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var assembly = app.AssembliesByName["UnityEngine.CoreModule"];
        var widget = new InjectedTypeAnalysisContext(assembly, "Tests", "Widget",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var target = widget.InjectMethodContext("OnEvent", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public);
        var methodInfo = new RuntimeMethodInfoAnalysisContext(target, assembly);
        var slot = new LocalVariable("slot", new Register(null, "slot"))
            { Type = app.SystemTypes.SystemIntPtrType };
        var readBack = new LocalVariable("readBack", new Register(null, "readBack"))
            { Type = app.SystemTypes.SystemIntPtrType };

        var module = new ModuleDefinition("LiveLocalFn.dll");
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
            new(1, OpCode.Move, readBack, slot),
            new(2, OpCode.Return)], [slot, readBack]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        var calledNames = il.Where(i => i.OpCode == CilOpCodes.Call || i.OpCode == CilOpCodes.Callvirt)
            .Select(i => (i.Operand as IMethodDescriptor)?.Name?.ToString())
            .ToList();
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldftn), Is.False,
                () => "an instance-method ldftn has no C# spelling (__ldftn):\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldtoken), Is.True,
                "the lookup starts from typeof(D)");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                && i.Operand?.ToString() == "OnEvent"), Is.True,
                "the method name reaches GetMethod as a string");
            Assert.That(calledNames, Has.Member("GetMethod"));
            Assert.That(calledNames, Has.Member("get_MethodHandle"));
            Assert.That(calledNames, Has.Member("get_Value"),
                "the IntPtr slot takes the wrapped pointer via RuntimeMethodHandle.Value");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                && i.Operand?.ToString()?.Contains("code entry pointer") == true), Is.False,
                "a MethodInfo* load is exactly RuntimeMethodHandle.Value - no decompiler-issue note");
        });
    }

    [Test]
    public void CodePointerMethodPointerStoreEmitsLookupWithDecompilerNote()
    {
        // An il2cpp_resolve_icall result is a code entry pointer, not the
        // MethodInfo* the handle wraps; the closest spellable value still
        // approximates, so the method carries a decompiler-issue note.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var assembly = app.AssembliesByName["UnityEngine.CoreModule"];
        var widget = new InjectedTypeAnalysisContext(assembly, "Tests", "Widget",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var target = widget.InjectMethodContext("OnEvent", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public);
        var methodInfo = new RuntimeMethodInfoAnalysisContext(target, assembly)
            { IsCodePointer = true };
        var slot = new LocalVariable("slot", new Register(null, "slot"))
            { Type = app.SystemTypes.SystemIntPtrType };
        var readBack = new LocalVariable("readBack", new Register(null, "readBack"))
            { Type = app.SystemTypes.SystemIntPtrType };

        var module = new ModuleDefinition("CodePtrFn.dll");
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
            new(1, OpCode.Move, readBack, slot),
            new(2, OpCode.Return)], [slot, readBack]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        var calledNames = il.Where(i => i.OpCode == CilOpCodes.Call || i.OpCode == CilOpCodes.Callvirt)
            .Select(i => (i.Operand as IMethodDescriptor)?.Name?.ToString())
            .ToList();
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldftn), Is.False,
                () => "an instance-method ldftn has no C# spelling (__ldftn):\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(calledNames, Has.Member("GetMethod"));
            Assert.That(calledNames, Has.Member("get_MethodHandle"));
            Assert.That(calledNames, Has.Member("get_Value"));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                && i.Operand?.ToString()?.Contains("code entry pointer") == true), Is.True,
                "a code-pointer load keeps the method marked incomplete via a decompiler-issue note");
        });
    }

    [Test]
    public void MethodPointerToRuntimeMethodHandleEmitsReflectionLookup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var assembly = app.AssembliesByName["UnityEngine.CoreModule"];
        var runtimeMethodHandle = app.AssembliesByName["mscorlib"]
            .GetTypeByFullName("System.RuntimeMethodHandle")!;
        var widget = new InjectedTypeAnalysisContext(assembly, "Tests", "Widget",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var target = widget.InjectMethodContext("OnEvent", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public);
        var methodInfo = new RuntimeMethodInfoAnalysisContext(target, assembly);
        var slot = new LocalVariable("slot", new Register(null, "slot")) { Type = runtimeMethodHandle };
        var readBack = new LocalVariable("readBack", new Register(null, "readBack"))
            { Type = runtimeMethodHandle };

        var module = new ModuleDefinition("HandleFn.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemIntPtrType,
            app.SystemTypes.SystemVoidType, app.SystemTypes.SystemObjectType, runtimeMethodHandle);
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
            new(1, OpCode.Move, readBack, slot),
            new(2, OpCode.Return)], [slot, readBack]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        var calledNames = il.Where(i => i.OpCode == CilOpCodes.Call || i.OpCode == CilOpCodes.Callvirt)
            .Select(i => (i.Operand as IMethodDescriptor)?.Name?.ToString())
            .ToList();
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldtoken
                && i.Operand is IMethodDescriptor), Is.False,
                () => "ldtoken on a method has no C# spelling (__ldtoken):\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(calledNames, Has.Member("GetMethod"));
            Assert.That(calledNames, Has.Member("get_MethodHandle"));
            Assert.That(calledNames, Has.No.Member("get_Value"),
                "a RuntimeMethodHandle slot stops at .MethodHandle");
        });
    }

    [Test]
    public void StandaloneStaticMethodPointerFieldStoreStillEmitsLdftn()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var assembly = app.AssembliesByName["UnityEngine.CoreModule"];
        var widget = new InjectedTypeAnalysisContext(assembly, "Tests", "Widget",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var target = widget.InjectMethodContext("OnEvent", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static);
        var ptrField = widget.InjectFieldContext("Ptr", app.SystemTypes.SystemIntPtrType,
            R.FieldAttributes.Public);
        var methodInfo = new RuntimeMethodInfoAnalysisContext(target, assembly);
        var holder = new LocalVariable("holder", new Register(null, "holder")) { Type = widget };
        var readBack = new LocalVariable("readBack", new Register(null, "readBack"))
            { Type = app.SystemTypes.SystemIntPtrType };
        var fieldRef = new FieldReference(ptrField, holder, 8);
        var module = new ModuleDefinition("LiveFn.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemIntPtrType,
            app.SystemTypes.SystemVoidType, app.SystemTypes.SystemObjectType);
        var widgetDefinition = new TypeDefinition("Tests", "Widget",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(widgetDefinition);
        widget.PutExtraData("AsmResolverType", widgetDefinition);
        var targetDefinition = new MethodDefinition("OnEvent",
            MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        widgetDefinition.Methods.Add(targetDefinition);
        target.PutExtraData("AsmResolverMethod", targetDefinition);
        var ptrDefinition = new FieldDefinition("Ptr", FieldAttributes.Public,
            new FieldSignature(module.CorLibTypeFactory.IntPtr));
        widgetDefinition.Fields.Add(ptrDefinition);
        ptrField.PutExtraData("AsmResolverField", ptrDefinition);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, fieldRef, methodInfo),
            new(1, OpCode.Move, readBack, fieldRef),
            new(2, OpCode.Return)], [holder, readBack]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldftn), Is.True,
                () => "a field destination is live memory, so the pointer is kept:\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stfld), Is.True,
                "the store into the field is emitted");
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

    [Test]
    public void FieldHandleStoreToRuntimeFieldHandleSlotEmitsReflectionLookup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var assembly = app.AssembliesByName["UnityEngine.CoreModule"];
        var holder = new InjectedTypeAnalysisContext(assembly, "Tests", "StaticData",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var blob = holder.InjectFieldContext("Blob", app.SystemTypes.SystemInt32Type,
            R.FieldAttributes.Public | R.FieldAttributes.Static);
        var fieldInfo = new RuntimeFieldInfoAnalysisContext(blob, assembly);
        var slot = new LocalVariable("slot", new Register(null, "slot"))
            { Type = SystemRuntimeFieldHandle(app) };
        var readBack = new LocalVariable("readBack", new Register(null, "readBack"))
            { Type = SystemRuntimeFieldHandle(app) };

        var module = new ModuleDefinition("FieldHandle.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemVoidType, app.SystemTypes.SystemObjectType,
            SystemRuntimeFieldHandle(app));
        var holderDefinition = new TypeDefinition("Tests", "StaticData",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(holderDefinition);
        holder.PutExtraData("AsmResolverType", holderDefinition);
        var blobDefinition = new FieldDefinition("Blob",
            FieldAttributes.Public | FieldAttributes.Static,
            new FieldSignature(module.CorLibTypeFactory.Int32));
        holderDefinition.Fields.Add(blobDefinition);
        blob.PutExtraData("AsmResolverField", blobDefinition);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, slot, fieldInfo),
            new(1, OpCode.Move, readBack, slot),
            new(2, OpCode.Return)], [slot, readBack]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        var calledNames = il.Where(i => i.OpCode == CilOpCodes.Call || i.OpCode == CilOpCodes.Callvirt)
            .Select(i => (i.Operand as IMethodDescriptor)?.Name?.ToString())
            .ToList();
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldtoken && i.Operand is IFieldDescriptor),
                Is.False,
                () => "a standalone ldtoken <field> has no C# spelling (__ldtoken):\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldtoken
                && i.Operand is not IFieldDescriptor), Is.True,
                "the lookup starts from typeof(D)");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                && i.Operand?.ToString() == "Blob"), Is.True,
                "the field name reaches GetField as a string");
            Assert.That(calledNames, Has.Member("GetField"));
            Assert.That(calledNames, Has.Member("get_FieldHandle"));
        });
    }

    [Test]
    public void FieldHandleStoreToIntPtrSlotTakesHandleValue()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var assembly = app.AssembliesByName["UnityEngine.CoreModule"];
        var holder = new InjectedTypeAnalysisContext(assembly, "Tests", "StaticData",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var blob = holder.InjectFieldContext("Blob", app.SystemTypes.SystemInt32Type,
            R.FieldAttributes.Public | R.FieldAttributes.Static);
        var fieldInfo = new RuntimeFieldInfoAnalysisContext(blob, assembly);
        var slot = new LocalVariable("slot", new Register(null, "slot"))
            { Type = app.SystemTypes.SystemIntPtrType };
        var readBack = new LocalVariable("readBack", new Register(null, "readBack"))
            { Type = app.SystemTypes.SystemIntPtrType };

        var module = new ModuleDefinition("FieldPointer.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemVoidType, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemIntPtrType);
        var holderDefinition = new TypeDefinition("Tests", "StaticData",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(holderDefinition);
        holder.PutExtraData("AsmResolverType", holderDefinition);
        var blobDefinition = new FieldDefinition("Blob",
            FieldAttributes.Public | FieldAttributes.Static,
            new FieldSignature(module.CorLibTypeFactory.Int32));
        holderDefinition.Fields.Add(blobDefinition);
        blob.PutExtraData("AsmResolverField", blobDefinition);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, slot, fieldInfo),
            new(1, OpCode.Move, readBack, slot),
            new(2, OpCode.Return)], [slot, readBack]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        var calledNames = il.Where(i => i.OpCode == CilOpCodes.Call || i.OpCode == CilOpCodes.Callvirt)
            .Select(i => (i.Operand as IMethodDescriptor)?.Name?.ToString())
            .ToList();
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldtoken && i.Operand is IFieldDescriptor),
                Is.False,
                () => "a standalone ldtoken <field> has no C# spelling (__ldtoken):\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(calledNames, Has.Member("GetField"));
            Assert.That(calledNames, Has.Member("get_FieldHandle"));
            Assert.That(calledNames, Has.Member("get_Value"),
                "the IntPtr slot takes the wrapped pointer via RuntimeFieldHandle.Value");
        });
    }

    [Test]
    public void NestedTypeAttributeArgumentEmitsCanonicalBlobName()
    {
        // Attribute blobs serialize typeof() arguments as SerStrings; a nested
        // type's canonical name keeps the namespace only on the outermost
        // element ("Tests.Outer+Inner"), not on the nested one
        // ("Tests.Outer+Tests.Inner" - what AsmResolver's TypeNameBuilder
        // otherwise writes when the nested typedef kept its namespace).
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var assembly = app.AssembliesByName["UnityEngine.CoreModule"];
        var outer = new InjectedTypeAnalysisContext(assembly, "Tests", "Outer",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var inner = outer.InjectNestedType("Inner", app.SystemTypes.SystemObjectType);
        var attribute = new InjectedTypeAnalysisContext(assembly, "Tests", "Marker",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var ctor = attribute.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public, app.SystemTypes.SystemTypeType);

        var module = new ModuleDefinition("AttrArg.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemVoidType, app.SystemTypes.SystemTypeType);
        var outerDefinition = new TypeDefinition("Tests", "Outer",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(outerDefinition);
        outer.PutExtraData("AsmResolverType", outerDefinition);
        var innerDefinition = new TypeDefinition("Tests", "Inner",
            TypeAttributes.NestedPublic | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        outerDefinition.NestedTypes.Add(innerDefinition);
        inner.PutExtraData("AsmResolverType", innerDefinition);

        var analyzed = new AnalyzedCustomAttribute(ctor);
        var parameter = new CustomAttributeTypeParameter(inner, analyzed,
            CustomAttributeParameterKind.ConstructorParam, 0);
        var argument = AsmResolverAssemblyPopulator.FromAnalyzedAttributeArgument(parameter, false);

        var emitted = argument.Elements.Single();
        Assert.That(emitted, Is.InstanceOf<TypeSignature>());
        Assert.That(TypeNameBuilder.GetAssemblyQualifiedName(
                (TypeSignature)emitted!, module),
            Is.EqualTo("Tests.Outer+Inner"));
    }
}
