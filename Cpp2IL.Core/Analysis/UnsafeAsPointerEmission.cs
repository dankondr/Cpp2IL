using System.Collections.Concurrent;
using System.Linq;
using AsmResolver;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils.AsmResolver;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Emission of <c>System.Runtime.CompilerServices.Unsafe.AsPointer&lt;T&gt;</c>
/// for a <c>&amp;T</c> operand landing in a native-int slot (the pinned-address
/// idiom). <c>conv.*</c> and every binary op reject a managed pointer outright
/// (ECMA III.1.5), so <c>Unsafe.AsPointer</c> is the only verifiable spelling
/// of the raw address: it returns <c>void*</c>, which the verifier reads as
/// native unsigned int and which therefore satisfies a
/// <c>System.IntPtr</c>/<c>System.UIntPtr</c> or <c>void*</c> slot with no
/// further conversion - exactly the value the binary moved.
/// </summary>
internal static class UnsafeAsPointerEmission
{
    // The helper lookup is per application and needed once per coercion site;
    // body emission runs parallel per assembly, so cache it under a lock-safe
    // map keyed on the context.
    private static readonly ConcurrentDictionary<ApplicationAnalysisContext, MethodAnalysisContext?> AsPointerCache = new();

    private const string UnsafeFullName = "System.Runtime.CompilerServices.Unsafe";

    /// <summary>
    /// Whether <c>call void* UnsafeInterop.AsPointer&lt;element&gt;(!!0&amp;)</c>
    /// can stand in for a <c>&amp;element</c> operand: the element must be a
    /// lawful generic argument that the emitting method can name, some emitted
    /// corlib assembly must actually carry the helper, and the calling method
    /// must render in an unsafe-capable context. Anything less is an unproven
    /// site and keeps its diagnosed default.
    /// </summary>
    internal static bool Satisfiable(TypeAnalysisContext? element, MethodAnalysisContext? context) =>
        UsableGenericArgument(element, context)
        && ResolveAsPointer(element!.AppContext) != null
        && !HostLacksUnsafeContext(context);

    /// <summary>
    /// Why an otherwise-proven site keeps its diagnosed default, or null when
    /// the ordinary "no legal conversion" text already names the shape. Only
    /// meaningful when <see cref="Satisfiable"/> is false; also null when the
    /// slot is not one <see cref="ServesSlot"/> would ever take, since the
    /// helper spelling was never on the table there.
    /// </summary>
    internal static string? BlockedReason(ByRefTypeAnalysisContext from, TypeAnalysisContext? to,
        MethodAnalysisContext? context)
    {
        if (!ServesSlot(to)
            || from.ElementType is not { } element
            || !UsableGenericArgument(element, context)
            || ResolveAsPointer(element.AppContext) == null)
            return null;
        if (HostLacksUnsafeContext(context))
            return "the Unsafe.AsPointer<T> spelling is withheld because the host is a compiler-generated state-machine MoveNext, which decompiles without an unsafe context";
        return null;
    }

    // A `MoveNext` on a compiler-generated state machine (`<X>d__N`, iterator
    // or async) renders through ilspy's generated-code path, which never emits
    // an `unsafe` modifier - a `void*` call inside it would not compile, so
    // the site is unproven there regardless of the slot's contract.
    private static bool HostLacksUnsafeContext(MethodAnalysisContext? context) =>
        context is { Name: "MoveNext", DeclaringType: { } stateMachine }
        && (stateMachine.IsCompilerGeneratedBasedOnCustomAttributes
            || stateMachine.Name is { } name
            && name.StartsWith('<')
            && (name.Contains(">d__") || name.Contains(">c__Iterator")));

    /// <summary>
    /// Emits <c>call void* UnsafeInterop.AsPointer&lt;element&gt;(!!0&amp;)</c>
    /// over the operand already on the stack, leaving <c>void*</c>. The call
    /// targets a uniquely-named public forwarder synthesized once in the
    /// helper's own corlib module, so the unqualified helper name can never
    /// collide with a second <c>System.Runtime.CompilerServices.Unsafe</c>
    /// the caller can see, and no caller ever needs the corlib helper's
    /// accessibility widened. Returns false when the site is unproven (see
    /// <see cref="Satisfiable"/>); the caller then drops the operand and
    /// emits the diagnosed default.
    /// </summary>
    internal static bool TryEmit(ByRefTypeAnalysisContext from, MethodAnalysisContext? context,
        CilInstructionCollection instructions)
    {
        // The generic argument is the address's element type verbatim: the
        // stack carries `&element`, and `!!0&` unifies with it only when
        // `!!0 == element` - unwrapping an `X[]` element to `X` would leave a
        // `&X` callee requirement under a `&X[]` value.
        var element = from.ElementType;
        if (!Satisfiable(element, context))
            return false;
        var helper = ResolveAsPointer(element!.AppContext)!;
        instructions.Add(CilOpCodes.Call,
            ResolveForwarder(helper).MakeGenericInstanceMethod([element.ToTypeSignature()]));
        return true;
    }

    // The helper sits in the recovered corlib, which is keyed, so an unsigned
    // caller cannot receive internals access to it - and widening the real
    // `System.Runtime.CompilerServices.Unsafe` to public makes that name
    // ambiguous for every caller that also references the vendored copy
    // (CS0433 leaks even into game code that writes `typeof(Unsafe)`). The
    // forwarder sidesteps both: a public, uniquely-named type synthesized in
    // the corlib module itself, whose body calls the helper in-assembly - so
    // the corlib keeps its declared accessibility and every caller names a
    // type nobody else declares. Cached per helper; the module mutation is
    // serialized because bodies emit in parallel.
    private const string ForwarderFullName = "Cpp2IL.Recovery.UnsafeInterop";

    private static readonly ConcurrentDictionary<MethodAnalysisContext, MethodDefinition> ForwarderCache = new();

    private static MethodDefinition ResolveForwarder(MethodAnalysisContext helper) =>
        ForwarderCache.GetOrAdd(helper, static resolved =>
        {
            var helperDef = resolved.GetExtraData<MethodDefinition>("AsmResolverMethod")!;
            var module = helperDef.DeclaringType!.DeclaringModule!;
            lock (module)
            {
                var type = module.TopLevelTypes.FirstOrDefault(t => t.FullName == ForwarderFullName);
                if (type == null)
                {
                    type = new TypeDefinition("Cpp2IL.Recovery", "UnsafeInterop",
                        TypeAttributes.Public | TypeAttributes.Abstract | TypeAttributes.Sealed
                            | TypeAttributes.BeforeFieldInit,
                        helperDef.DeclaringType.BaseType);
                    module.TopLevelTypes.Add(type);
                }
                return type.Methods.FirstOrDefault(m => m.Name == "AsPointer")
                       ?? CreateForwarderMethod(type, module, helperDef);
            }
        });

    private static MethodDefinition CreateForwarderMethod(TypeDefinition owner, ModuleDefinition module,
        MethodDefinition helperDef)
    {
        var signature = MethodSignature.CreateStatic(
            module.CorLibTypeFactory.Void.MakePointerType(), 1,
            [new GenericParameterSignature(GenericParameterType.Method, 0).MakeByReferenceType()]);
        var method = new MethodDefinition("AsPointer",
            MethodAttributes.Public | MethodAttributes.Static, signature);
        owner.Methods.Add(method);
        method.GenericParameters.Add(new GenericParameter("T"));
        var body = new CilMethodBody();
        body.Instructions.Add(CilOpCodes.Ldarg_0);
        body.Instructions.Add(CilOpCodes.Call,
            helperDef.MakeGenericInstanceMethod(
                [new GenericParameterSignature(GenericParameterType.Method, 0)]));
        body.Instructions.Add(CilOpCodes.Ret);
        method.CilMethodBody = body;
        return method;
    }

    // `void*` slots take the helper's own return type, so they are served too;
    // a typed unmanaged pointer slot is not (void* -> T* has no verifiable
    // conversion), and the native-int result is what IntPtr/UIntPtr want.
    internal static bool ServesSlot(TypeAnalysisContext? contract) =>
        contract is { FullName: "System.IntPtr" or "System.UIntPtr" }
            or PointerTypeAnalysisContext { ElementType.FullName: "System.Void" };

    // A generic argument must be a closed-ish, non-pointer, non-byref,
    // non-ref-struct type: pointers and byrefs are illegal arguments, ref
    // structs cannot be generic arguments at all, and the synthetic marker /
    // rgctx contexts name no real type (they only pretend a token exists).
    // Generic parameters are lawful arguments - the instantiation keeps them
    // verbatim - and so are wrapped forms like `X[]`: `!!0 == X[]` is what the
    // `&X[]` stack unifies with. The caller must be able to name the argument
    // (same visibility gate every token-bearing emission uses).
    private static bool UsableGenericArgument(TypeAnalysisContext? element, MethodAnalysisContext? context) =>
        element switch
        {
            null => false,
            ByRefTypeAnalysisContext or PointerTypeAnalysisContext => false,
            RuntimeClassTypeAnalysisContext or RuntimeMethodInfoAnalysisContext
                or RuntimeFieldInfoAnalysisContext or StaticFieldStorageTypeAnalysisContext
                or RgctxTableTypeAnalysisContext or MethodRgctxTableTypeAnalysisContext
                or SentinelTypeAnalysisContext or BoxedTypeAnalysisContext => false,
            GenericParameterTypeAnalysisContext => true,
            _ => !(element.IsValueType && IlGenerator.IsByRefLike(element))
                 && IlGenerator.TypeTokenUsableFrom(element, context),
        };

    // Finds the corlib copy of `static void* Unsafe::AsPointer<T>(ref T)` among
    // the emitted assemblies: a static single-parameter generic whose only
    // parameter is a byref and whose return is an unmanaged pointer, carrying
    // an emitted definition. Corlib-named assemblies are preferred so a facade
    // copy (e.g. the Unsafe reference assembly) never wins the bind.
    private static MethodAnalysisContext? ResolveAsPointer(ApplicationAnalysisContext appContext) =>
        AsPointerCache.GetOrAdd(appContext, ScanForAsPointer);

    private static MethodAnalysisContext? ScanForAsPointer(ApplicationAnalysisContext appContext)
    {
        foreach (var corlibFirst in appContext.AssembliesByName.Values.OrderBy(a =>
                     a.Name is "mscorlib" or "netstandard" or "System.Private.CoreLib" ? 0 : 1))
        {
            if (corlibFirst.GetTypeByFullName(UnsafeFullName) is not { } unsafeType)
                continue;
            var candidate = unsafeType.Methods.FirstOrDefault(method =>
                method is { IsStatic: true, Name: "AsPointer" }
                && method.GenericParameters.Count == 1
                && method.Parameters.Count == 1
                && method.Parameters[0].ParameterType is ByRefTypeAnalysisContext
                && method.ReturnType is PointerTypeAnalysisContext
                && method.GetExtraData<MethodDefinition>("AsmResolverMethod") != null);
            if (candidate != null)
                return candidate;
        }
        return null;
    }
}
