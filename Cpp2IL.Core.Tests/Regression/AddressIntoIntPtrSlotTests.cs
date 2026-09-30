using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;
using R = System.Reflection;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: a managed address (`&T` from ldloca/ldflda/ref) reaching a
// System.IntPtr slot with no conversion (castle-recovery#176). conv.* reject a
// managed pointer outright, so the only verifiable spelling of the raw address
// is the corlib helper `Unsafe.AsPointer<T>`: it returns `void*`, which the
// verifier reads as native int - satisfying the IntPtr slot and carrying
// exactly the address value the binary moved. Sites whose element cannot be a
// generic argument (or whose corlib carries no helper) keep the diagnosed
// default.
public class AddressIntoIntPtrSlotTests
{
    // Injects a corlib `Unsafe` type carrying `static void* AsPointer<T>(ref T)`
    // the way the recovered mscorlib does, with emitted AsmResolver members.
    private static (InjectedTypeAnalysisContext unsafeType, InjectedMethodAnalysisContext asPointer)
        InjectUnsafeAsPointer(ApplicationAnalysisContext app, ModuleDefinition module)
    {
        var unsafeType = app.AssembliesByName["mscorlib"].InjectType(
            "System.Runtime.CompilerServices", "Unsafe", app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Abstract | R.TypeAttributes.Sealed);
        var asPointer = unsafeType.InjectMethodContext("AsPointer",
            new PointerTypeAnalysisContext(app.SystemTypes.SystemVoidType),
            R.MethodAttributes.Public | R.MethodAttributes.Static);
        var genericT = new GenericParameterTypeAnalysisContext("T", 0, Il2CppTypeEnum.IL2CPP_TYPE_MVAR,
            (R.GenericParameterAttributes)0, asPointer);
        asPointer.GenericParameters.Add(genericT);
        asPointer.Parameters.Add(new InjectedParameterAnalysisContext(null,
            new ByRefTypeAnalysisContext(genericT), R.ParameterAttributes.None, 0, asPointer));

        var unsafeDefinition = new TypeDefinition("System.Runtime.CompilerServices", "Unsafe",
            TypeAttributes.Public | TypeAttributes.Abstract | TypeAttributes.Sealed,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(unsafeDefinition);
        var asPointerDefinition = new MethodDefinition("AsPointer",
            MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void.MakePointerType(), 1,
                [new GenericParameterSignature(GenericParameterType.Method, 0).MakeByReferenceType()]));
        unsafeDefinition.Methods.Add(asPointerDefinition);
        unsafeType.PutExtraData("AsmResolverType", unsafeDefinition);
        asPointer.PutExtraData("AsmResolverMethod", asPointerDefinition);
        return (unsafeType, asPointer);
    }

    private static bool CallsAsPointer(CilInstructionCollection il, string name) =>
        il.Any(i => i.OpCode == CilOpCodes.Call
            && i.Operand is IMethodDescriptor called && called.Name?.ToString() == name);

    [Test]
    public void LocalAddressIntoIntPtrSlotEmitsAsPointer()
    {
        // `intptr = (IntPtr)&value` - a real address take into a native-int
        // slot. The emitted body must call Unsafe.AsPointer<int32> over the
        // ldloca rather than dropping the address for a synthetic default.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("AddrIntPtr.dll");
        InjectUnsafeAsPointer(app, module);

        var intLocal = new LocalVariable("value", new Register(null, "value"),
            app.SystemTypes.SystemInt32Type);
        var ptrLocal = new LocalVariable("intptr", new Register(null, "intptr"),
            app.SystemTypes.SystemIntPtrType);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemIntPtrType, app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, ptrLocal, new AddressOf(intLocal)),
            new(1, OpCode.Return)], [intLocal, ptrLocal]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldloca
                    || i.OpCode == CilOpCodes.Ldloca_S), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(CallsAsPointer(il, "AsPointer"), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stloc), Is.True,
                "the native-int result still stores into the IntPtr slot");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("No legal conversion")), Is.False,
                "a proven site takes no synthetic default\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void ArrayAddressIntoIntPtrSlotEmitsAsPointerOfArray()
    {
        // `intptr = (IntPtr)&values` where values is int[] - the stack holds
        // `&int[]`, so the helper must be instantiated as AsPointer<int[]>:
        // `!!0&` unifies with the operand only when `!!0` is the element type
        // verbatim. Unwrapping to AsPointer<int> would leave a `&int`
        // requirement under an `&int[]` value, which ILVerify rejects.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("AddrArrayIntPtr.dll");
        InjectUnsafeAsPointer(app, module);

        var arrayType = new SzArrayTypeAnalysisContext(app.SystemTypes.SystemInt32Type);
        var arrLocal = new LocalVariable("values", new Register(null, "values"), arrayType);
        var ptrLocal = new LocalVariable("intptr", new Register(null, "intptr"),
            app.SystemTypes.SystemIntPtrType);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemIntPtrType, app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, ptrLocal, new AddressOf(arrLocal)),
            new(1, OpCode.Return)], [arrLocal, ptrLocal]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call
                    && i.Operand is MethodSpecification { Signature: GenericInstanceMethodSignature generic }
                    && generic.TypeArguments[0] is SzArrayTypeSignature), Is.True,
                "AsPointer<T> must be instantiated with the array type itself\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("No legal conversion")), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    private static (MethodAnalysisContext caller, MethodDefinition method) StateMachineMoveNext(
        ApplicationAnalysisContext app, ModuleDefinition module, List<Instruction> instructions,
        List<LocalVariable> locals, string name)
    {
        var sm = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", name, app.SystemTypes.SystemValueTypeType,
            R.TypeAttributes.Public | R.TypeAttributes.Sealed);
        var caller = sm.InjectMethodContext("MoveNext", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Private);
        caller.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        caller.Locals = locals;
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];
        var type = new TypeDefinition("Tests", name, TypeAttributes.Public | TypeAttributes.Sealed
            | TypeAttributes.SequentialLayout,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("MoveNext", MethodAttributes.Private,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        type.Methods.Add(method);
        return (caller, method);
    }

    [Test]
    public void StateMachineMoveNextAddressIntoIntPtrSlotKeepsDiagnostic()
    {
        // `intptr = (IntPtr)&value` inside a compiler-generated state machine's
        // MoveNext - ilspy renders the generated body without an unsafe
        // context, so a `void*` call there cannot compile. The site keeps its
        // diagnosed default and the note names the withheld spelling.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("AddrIntPtrMoveNext.dll");
        InjectUnsafeAsPointer(app, module);

        var intLocal = new LocalVariable("value", new Register(null, "value"),
            app.SystemTypes.SystemInt32Type);
        var ptrLocal = new LocalVariable("intptr", new Register(null, "intptr"),
            app.SystemTypes.SystemIntPtrType);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemIntPtrType, app.SystemTypes.SystemVoidType);
        var (caller, method) = StateMachineMoveNext(app, module, [
            new(0, OpCode.Move, ptrLocal, new AddressOf(intLocal)),
            new(1, OpCode.Return)], [intLocal, ptrLocal], "<FetchAsync>d__3");

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(CallsAsPointer(il, "AsPointer"), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("No legal conversion")
                    && text.Contains("state-machine")), Is.True,
                "the note must name why the proven spelling is withheld\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void AmbiguousUnsafeAddressIntoIntPtrSlotKeepsDiagnostic()
    {
        // `intptr = (IntPtr)&value` where the caller can see a second
        // System.Runtime.CompilerServices.Unsafe (a vendored copy in the
        // caller's own assembly standing in for the NuGet facade). The
        // unqualified helper name is then ambiguous for the emitted source -
        // the site keeps its diagnosed default and the note names why.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("AddrIntPtrAmbig.dll");
        InjectUnsafeAsPointer(app, module);
        app.AssembliesByName["UnityEngine.CoreModule"].InjectType(
            "System.Runtime.CompilerServices", "Unsafe", app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Abstract | R.TypeAttributes.Sealed);

        var intLocal = new LocalVariable("value", new Register(null, "value"),
            app.SystemTypes.SystemInt32Type);
        var ptrLocal = new LocalVariable("intptr", new Register(null, "intptr"),
            app.SystemTypes.SystemIntPtrType);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemIntPtrType, app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, ptrLocal, new AddressOf(intLocal)),
            new(1, OpCode.Return)], [intLocal, ptrLocal]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(CallsAsPointer(il, "AsPointer"), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("No legal conversion")
                    && text.Contains("more than one System.Runtime.CompilerServices.Unsafe")), Is.True,
                "the note must name why the proven spelling is withheld\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void UnusedVendoredUnsafeAddressIntoIntPtrSlotEmitsAsPointer()
    {
        // A second `System.Runtime.CompilerServices.Unsafe` exists in the
        // corpus (a vendored facade in an assembly the caller's members never
        // bind), so the emitted module cannot see it - the corlib helper name
        // is unambiguous and the proven spelling must still be emitted.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("AddrIntPtrUnused.dll");
        InjectUnsafeAsPointer(app, module);
        app.AssembliesByName["System.Xml"].InjectType(
            "System.Runtime.CompilerServices", "Unsafe", app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Abstract | R.TypeAttributes.Sealed);

        var intLocal = new LocalVariable("value", new Register(null, "value"),
            app.SystemTypes.SystemInt32Type);
        var ptrLocal = new LocalVariable("intptr", new Register(null, "intptr"),
            app.SystemTypes.SystemIntPtrType);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemIntPtrType, app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, ptrLocal, new AddressOf(intLocal)),
            new(1, OpCode.Return)], [intLocal, ptrLocal]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.That(CallsAsPointer(il, "AsPointer"), Is.True,
            () => string.Join("\n", il.Select(i => i.ToString())));
    }

    [Test]
    public void ByRefElementAddressIntoIntPtrSlotKeepsDiagnostic()
    {
        // `intptr = (IntPtr)&cell` where cell is byte& - the operand is byte&&
        // and a managed pointer can never be a generic argument, so no honest
        // AsPointer spelling exists. The site keeps its named decompiler-issue
        // note rather than a fabricated value.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("AddrIntPtrDiag.dll");
        InjectUnsafeAsPointer(app, module);

        var cell = new LocalVariable("cell", new Register(null, "cell"),
            new ByRefTypeAnalysisContext(app.SystemTypes.SystemByteType));
        var ptrLocal = new LocalVariable("intptr", new Register(null, "intptr"),
            app.SystemTypes.SystemIntPtrType);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemByteType,
            app.SystemTypes.SystemIntPtrType, app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, ptrLocal, new AddressOf(cell)),
            new(1, OpCode.Return)], [cell, ptrLocal]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(CallsAsPointer(il, "AsPointer"), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("No legal conversion")
                    && text.Contains("System.IntPtr")), Is.True,
                "the unproven site keeps its named decompiler-issue note\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call), Is.True,
                "the diagnostic must be an emitted call, not just a string");
        });
    }
}
