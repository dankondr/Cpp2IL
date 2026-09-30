using System.Collections.Concurrent;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.PE.DotNet.Cil;
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

    /// <summary>
    /// Whether <c>call void* Unsafe.AsPointer&lt;element&gt;(!!0&amp;)</c> can
    /// stand in for a <c>&amp;element</c> operand: the element must be a lawful
    /// generic argument that the emitting method can name, and some emitted
    /// corlib assembly must actually carry the helper. Anything less is an
    /// unproven site and keeps its diagnosed default.
    /// </summary>
    internal static bool Satisfiable(TypeAnalysisContext? element, MethodAnalysisContext? context) =>
        UsableGenericArgument(element, context)
        && ResolveAsPointer(element!.AppContext) != null;

    /// <summary>
    /// Emits <c>call void* Unsafe.AsPointer&lt;element&gt;(!!0&amp;)</c> over
    /// the operand already on the stack, leaving <c>void*</c>. Returns false
    /// when the site is unproven (see <see cref="Satisfiable"/>); the caller
    /// then drops the operand and emits the diagnosed default.
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
        // The recovered corlib declares Unsafe internal, and the descriptor
        // path freezes every external-runtime member against widening. A
        // scoped EnsureAccessible is still required here: a keyed corlib
        // cannot grant internals to an unsigned caller, so the least access
        // this specific reference needs is what the ambient scope demands -
        // internal where a grant exists, public elsewhere.
        MemberAccessibility.EnsureAccessible(
            helper.GetExtraData<MethodDefinition>("AsmResolverMethod")!, helper);
        instructions.Add(CilOpCodes.Call,
            helper.MakeGenericInstanceMethod(element).ToMethodDescriptor());
        return true;
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
            if (corlibFirst.GetTypeByFullName("System.Runtime.CompilerServices.Unsafe") is not { } unsafeType)
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
