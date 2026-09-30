using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Model.Contexts;

/// <summary>
/// Synthetic type for a value that holds an IL2CPP runtime method pointer - most sources produce a
/// <c>MethodInfo*</c> (the value a method-metadata global, invoke-data MethodInfo field, RGCTX
/// method slot or hidden MethodInfo parameter carries, and exactly what
/// <c>RuntimeMethodHandle.Value</c> is under IL2CPP); an <c>il2cpp_resolve_icall</c> result instead
/// loads the method's code entry pointer (<c>Il2CppMethodPointer</c>, the
/// <c>MethodInfo::methodPointer</c> field), marked via <see cref="IsCodePointer"/>.
/// </summary>
public class RuntimeMethodInfoAnalysisContext(MethodAnalysisContext representedMethod, AssemblyAnalysisContext referencedFrom)
    : ReferencedTypeAnalysisContext(referencedFrom)
{
    /// <summary>The method whose runtime MethodInfo this value points to.</summary>
    public MethodAnalysisContext RepresentedMethod { get; } = representedMethod;

    /// <summary>
    /// True when the original code loaded the method's code entry pointer
    /// (an <c>Il2CppMethodPointer</c>, e.g. an <c>il2cpp_resolve_icall</c> result or a cached
    /// icall) rather than its <c>MethodInfo*</c> handle. The closest spellable managed value is
    /// the handle, so emission of one into a pointer slot must carry a decompiler-issue note.
    /// </summary>
    public bool IsCodePointer { get; init; }

    // A pointer-sized runtime handle; there is no Il2CppType enum value for the Il2CppMethodInfo struct.
    public override Il2CppTypeEnum Type => Il2CppTypeEnum.IL2CPP_TYPE_I;

    public override string DefaultName => "Il2CppMethodInfo";

    public override string DefaultNamespace => "";

    public override bool IsValueType => false;
}
