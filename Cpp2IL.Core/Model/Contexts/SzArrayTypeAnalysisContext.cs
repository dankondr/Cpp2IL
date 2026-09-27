using System;
using Cpp2IL.Core.Utils;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Model.Contexts;

public class SzArrayTypeAnalysisContext(TypeAnalysisContext elementType)
    : WrappedTypeAnalysisContext(elementType)
{
    public SzArrayTypeAnalysisContext(Il2CppType rawType, ApplicationAnalysisContext context)
        : this(context.ResolveIl2CppType(rawType.GetEncapsulatedType()))
    {
    }

    public sealed override Il2CppTypeEnum Type => Il2CppTypeEnum.IL2CPP_TYPE_SZARRAY;

    public sealed override string DefaultName => $"{ElementType.DefaultName}[]";

    public sealed override string? OverrideName
    {
        get => $"{ElementType.Name}[]";
        set => throw new NotSupportedException();
    }

    public sealed override bool IsValueType => false;

    // Every array type derives from System.Array; wrapped types have no
    // definition to read that from, so name it from the corlib context.
    public sealed override TypeAnalysisContext? DefaultBaseType =>
        AppContext.SystemTypes?.SystemArrayType;
}
