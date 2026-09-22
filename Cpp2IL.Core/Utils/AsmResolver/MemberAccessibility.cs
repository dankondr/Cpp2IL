using AsmResolver.DotNet;
using AsmResolver.PE.DotNet.Metadata.Tables;

namespace Cpp2IL.Core.Utils.AsmResolver;

/// <summary>
/// Makes a copied member usable by recovered IL when native code proved a direct
/// access to metadata-private storage. This is deliberately called only while a
/// descriptor is emitted; it does not broaden untouched metadata.
/// </summary>
internal static class MemberAccessibility
{
    public static void EnsureAccessible(FieldDefinition field)
    {
        field.Attributes = (field.Attributes & ~FieldAttributes.FieldAccessMask) | FieldAttributes.Public;
        EnsureDeclaringTypeAccessible(field.DeclaringType);
    }

    public static void EnsureAccessible(MethodDefinition method)
    {
        method.Attributes = (method.Attributes & ~MethodAttributes.MemberAccessMask) | MethodAttributes.Public;
        EnsureDeclaringTypeAccessible(method.DeclaringType);
    }

    private static void EnsureDeclaringTypeAccessible(TypeDefinition? type)
    {
        while (type != null)
        {
            var visibility = type.DeclaringType == null
                ? TypeAttributes.Public
                : TypeAttributes.NestedPublic;
            type.Attributes = (type.Attributes & ~TypeAttributes.VisibilityMask) | visibility;
            type = type.DeclaringType;
        }
    }
}
