using System;
using System.Reflection;
using System.Reflection.Emit;

namespace Cpp2IL.JitOracle.Tests;

/// <summary>
/// Emits fixture assemblies whose method bodies cannot be expressed in C#:
/// deliberately runtime-invalid stloc sequences. Reflection.Emit does not
/// verify emitted IL, which is exactly what lets these bodies exist.
/// </summary>
public static class FixtureEmit
{
    /// <summary>
    /// Assembly whose methods mirror the runtime-invalid class Unity/Mono caught:
    /// stloc writes incompatible with the declared locals.
    /// </summary>
    public static string EmitInvalidAssembly(string directory)
    {
        var builder = new PersistedAssemblyBuilder(
            new AssemblyName("JitOracleFixtures.Invalid"), typeof(object).Assembly);
        var module = builder.DefineDynamicModule("JitOracleFixtures.Invalid");
        var type = module.DefineType(
            "JitOracleFixtures.Invalid.Holder", TypeAttributes.Public | TypeAttributes.Class);

        // Control: proves enumeration continues after a failed method.
        Emit(type, "Good", typeof(int), Type.EmptyTypes, il =>
        {
            il.Emit(OpCodes.Ldc_I4, 42);
            il.Emit(OpCodes.Ret);
        });

        // stloc to a local index outside the declared range — the same
        // "Invalid IL code ... IL_xxxx: stloc N" class Unity/Mono reported.
        Emit(type, "BadStlocOutOfRange", typeof(int), Type.EmptyTypes, il =>
        {
            il.DeclareLocal(typeof(int));
            il.Emit(OpCodes.Ldc_I4_1);
            il.Emit(OpCodes.Stloc, (short)7);
            il.Emit(OpCodes.Ldloc_0);
            il.Emit(OpCodes.Ret);
        });

        // Primitive type-mismatched stloc (float -> int32 local): whether a JIT
        // rejects it is runtime-specific; the runtime record captures which ran.
        Emit(type, "BadStlocPrimitiveMismatch", typeof(int), Type.EmptyTypes, il =>
        {
            il.DeclareLocal(typeof(int));
            il.Emit(OpCodes.Ldc_R4, 1.5f);
            il.Emit(OpCodes.Stloc_0);
            il.Emit(OpCodes.Ldloc_0);
            il.Emit(OpCodes.Ret);
        });

        // Primitive -> reference mismatched stloc (int32 -> string local).
        // Never safe to invoke; prepare-only must not call it either.
        Emit(type, "BadStlocRefMismatch", typeof(string), Type.EmptyTypes, il =>
        {
            il.DeclareLocal(typeof(string));
            il.Emit(OpCodes.Ldc_I4_1);
            il.Emit(OpCodes.Stloc_0);
            il.Emit(OpCodes.Ldloc_0);
            il.Emit(OpCodes.Ret);
        });

        type.CreateType();
        var path = Path.Combine(directory, "JitOracleFixtures.Invalid.dll");
        builder.Save(path);
        return path;
    }

    /// <summary>
    /// Assembly exercising --vectors: one correctly-implemented method plus one
    /// whose body hides a bad stloc, so vector invocation deterministically fails
    /// while the process continues to the remaining vectors.
    /// </summary>
    public static string EmitCorruptVectorsAssembly(string directory)
    {
        var builder = new PersistedAssemblyBuilder(
            new AssemblyName("JitOracleFixtures.Corrupt"), typeof(object).Assembly);
        var module = builder.DefineDynamicModule("JitOracleFixtures.Corrupt");
        var type = module.DefineType(
            "JitOracleFixtures.Corrupt.Holder", TypeAttributes.Public | TypeAttributes.Class);

        Emit(type, "Add", typeof(int), [typeof(int), typeof(int)], il =>
        {
            il.DeclareLocal(typeof(int));
            il.Emit(OpCodes.Ldarg_0);
            il.Emit(OpCodes.Ldarg_1);
            il.Emit(OpCodes.Add);
            il.Emit(OpCodes.Stloc, (short)7);
            il.Emit(OpCodes.Ldloc_0);
            il.Emit(OpCodes.Ret);
        });

        Emit(type, "Mul", typeof(int), [typeof(int), typeof(int)], il =>
        {
            il.Emit(OpCodes.Ldarg_0);
            il.Emit(OpCodes.Ldarg_1);
            il.Emit(OpCodes.Mul);
            il.Emit(OpCodes.Ret);
        });

        type.CreateType();
        var path = Path.Combine(directory, "JitOracleFixtures.Corrupt.dll");
        builder.Save(path);
        return path;
    }

    private static void Emit(
        TypeBuilder type, string name, Type? returnType, Type[] parameters, Action<ILGenerator> emit)
    {
        var method = type.DefineMethod(
            name, MethodAttributes.Public | MethodAttributes.Static, returnType, parameters);
        emit(method.GetILGenerator());
    }
}
