using System.Reflection;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Text;
using System.Text.Json;

namespace Cpp2IL.JitOracle;

public sealed class RunStats
{
    public int Types;
    public int Methods;
    public int Prepared;
    public int Skipped;
    public int Failed;
    public int TypeFailures;
    public int VectorTotal;
    public int VectorPassed;
    public int VectorFailed;
    public bool AnyFailures => Failed > 0 || TypeFailures > 0 || VectorFailed > 0;
}

public static class Oracle
{
    private const BindingFlags DeclaredMembers =
        BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Static | BindingFlags.Instance | BindingFlags.DeclaredOnly;

    public static int Run(OracleOptions options, TextWriter output)
    {
        var assemblyPath = Path.GetFullPath(options.AssemblyPath!);
        var dependenciesDir = Path.GetFullPath(
            options.DependenciesDir ?? Path.GetDirectoryName(assemblyPath)!);

        var sink = options.OutputPath is { } outFile
            ? new StreamWriter(File.Create(outFile), new UTF8Encoding(false)) { AutoFlush = true }
            : output;

        try
        {
            EmitRuntime(sink);

            var context = new OracleLoadContext(dependenciesDir);
            var stats = new RunStats();
            Assembly assembly;
            try
            {
                assembly = context.LoadFromAssemblyPath(assemblyPath);
            }
            catch (Exception exception) when (exception is not FileNotFoundException
                                                and not DirectoryNotFoundException)
            {
                sink.WriteLine(JsonSerializer.Serialize(new
                {
                    record = "assembly",
                    assembly = Path.GetFileNameWithoutExtension(assemblyPath),
                    outcome = "failed",
                    exception = exception.GetType().FullName,
                    message = Sanitize(exception.Message),
                }));
                stats.TypeFailures++;
                EmitSummary(null, sink, stats);
                return 1;
            }

            var assemblyName = assembly.GetName().Name!;
            foreach (var entry in EnumerateConcreteMethods(assembly, sink, stats))
                PrepareOne(entry, assemblyName, sink, stats);

            if (options.VectorsPath is { } vectorsPath)
                VectorRunner.Run(assembly, vectorsPath, sink, stats);

            EmitSummary(assembly, sink, stats);
            return stats.AnyFailures ? 1 : 0;
        }
        finally
        {
            if (options.OutputPath is not null)
                sink.Dispose();
        }
    }

    private static List<(MethodBase Method, int Token)> EnumerateConcreteMethods(
        Assembly assembly, TextWriter sink, RunStats stats)
    {
        Type[] types;
        try
        {
            types = assembly.GetTypes();
        }
        catch (ReflectionTypeLoadException exception)
        {
            types = exception.Types.Where(t => t is not null).Cast<Type>().ToArray();
            foreach (var loaderException in exception.LoaderExceptions.Where(e => e is not null))
            {
                sink.WriteLine(JsonSerializer.Serialize(new
                {
                    record = "type",
                    outcome = "failed",
                    exception = loaderException!.GetType().FullName,
                    message = Sanitize(loaderException.Message),
                }));
                stats.TypeFailures++;
            }
        }
        catch (Exception exception)
        {
            sink.WriteLine(JsonSerializer.Serialize(new
            {
                record = "type",
                outcome = "failed",
                exception = exception.GetType().FullName,
                message = Sanitize(exception.Message),
            }));
            stats.TypeFailures++;
            return [];
        }

        var orderedTypes = types
            .Select(t => (Type: t, Token: SafeToken(t)))
            .OrderBy(t => t.Token)
            .ToList();
        stats.Types = orderedTypes.Count;

        var methods = new List<(MethodBase Method, int Token)>();
        foreach (var (type, _) in orderedTypes)
        {
            try
            {
                foreach (var member in type.GetMethods(DeclaredMembers).Cast<MethodBase>()
                             .Concat(type.GetConstructors(DeclaredMembers)))
                    methods.Add((member, SafeToken(member)));
            }
            catch (Exception exception)
            {
                sink.WriteLine(JsonSerializer.Serialize(new
                {
                    record = "type",
                    type = type.FullName,
                    outcome = "failed",
                    exception = exception.GetType().FullName,
                    message = Sanitize(exception.Message),
                }));
                stats.TypeFailures++;
            }
        }

        var ordered = methods.OrderBy(m => m.Token).ToList();
        stats.Methods = ordered.Count;
        return ordered;
    }

    private static void PrepareOne(
        (MethodBase Method, int Token) entry, string assemblyName, TextWriter sink, RunStats stats)
    {
        var method = entry.Method;
        var token = $"0x{entry.Token:X8}";
        string signature;
        try
        {
            signature = FormatSignature(method);
        }
        catch
        {
            try
            {
                signature = $"{method.DeclaringType?.Name ?? "?"}::{method.Name}";
            }
            catch
            {
                signature = "?";
            }
        }

        try
        {
            PrepareOneCore(method, assemblyName, token, signature, sink, stats);
        }
        catch (Exception exception)
        {
            // Type resolution for lazy metadata can throw anywhere; a failed
            // record must never kill the run.
            EmitFailure(assemblyName, token, signature, exception, sink);
            stats.Failed++;
        }
    }

    private static void PrepareOneCore(
        MethodBase method, string assemblyName, string token, string signature,
        TextWriter sink, RunStats stats)
    {
        if (TryGetSkipReason(method, out var reason, out var classifyException))
        {
            sink.WriteLine(JsonSerializer.Serialize(new
            {
                record = "method",
                assembly = assemblyName,
                token,
                signature,
                outcome = "skipped",
                reason,
            }));
            stats.Skipped++;
            return;
        }

        if (classifyException is not null)
        {
            EmitFailure(assemblyName, token, signature, classifyException, sink);
            stats.Failed++;
            return;
        }

        try
        {
            RuntimeHelpers.PrepareMethod(method.MethodHandle);
            sink.WriteLine(JsonSerializer.Serialize(new
            {
                record = "method",
                assembly = assemblyName,
                token,
                signature,
                outcome = "prepared",
            }));
            stats.Prepared++;
        }
        catch (Exception exception)
        {
            EmitFailure(assemblyName, token, signature, exception, sink);
            stats.Failed++;
        }
    }

    /// <summary>
    /// Returns true when the method must be reported as skipped. When it returns
    /// false, <paramref name="classifyException"/> may still carry an anomaly
    /// observed while classifying (e.g. an unreadable method body).
    /// </summary>
    private static bool TryGetSkipReason(MethodBase method, out string reason, out Exception? classifyException)
    {
        reason = string.Empty;
        classifyException = null;

        if (method.IsAbstract)
        {
            reason = "abstract";
            return true;
        }

        if ((method.Attributes & MethodAttributes.PinvokeImpl) != 0)
        {
            reason = "pinvoke";
            return true;
        }

        MethodImplAttributes implFlags;
        try
        {
            implFlags = method.GetMethodImplementationFlags();
        }
        catch (Exception exception)
        {
            classifyException = exception;
            return false;
        }

        if ((implFlags & MethodImplAttributes.InternalCall) != 0)
        {
            reason = "internal-call";
            return true;
        }

        if (method.ContainsGenericParameters)
        {
            reason = "open-generic";
            return true;
        }

        try
        {
            if (method.GetMethodBody() is null)
            {
                reason = "no-il-body";
                return true;
            }
        }
        catch (Exception exception)
        {
            classifyException = exception;
            return false;
        }

        return false;
    }

    private static void EmitFailure(
        string assemblyName, string token, string signature, Exception exception, TextWriter sink)
    {
        sink.WriteLine(JsonSerializer.Serialize(new
        {
            record = "method",
            assembly = assemblyName,
            token,
            signature,
            outcome = "failed",
            exception = exception.GetType().FullName,
            message = Sanitize(exception.Message),
        }));
    }

    private static void EmitRuntime(TextWriter sink)
    {
        var mono = Type.GetType("Mono.Runtime") is not null;
        sink.WriteLine(JsonSerializer.Serialize(new
        {
            record = "runtime",
            runtime = mono ? "Mono" : "CoreCLR",
            framework = RuntimeInformation.FrameworkDescription,
            os = RuntimeInformation.OSDescription,
            arch = RuntimeInformation.ProcessArchitecture.ToString(),
            jit = mono ? "mono-jit" : "RyuJIT",
        }));
    }

    private static void EmitSummary(Assembly? assembly, TextWriter sink, RunStats stats)
    {
        sink.WriteLine(JsonSerializer.Serialize(new
        {
            record = "summary",
            assembly = assembly?.GetName().Name,
            types = stats.Types,
            methods = stats.Methods,
            prepared = stats.Prepared,
            skipped = stats.Skipped,
            failed = stats.Failed + stats.TypeFailures,
            vectors = stats.VectorTotal == 0
                ? null
                : new { total = stats.VectorTotal, passed = stats.VectorPassed, failed = stats.VectorFailed },
        }));
    }

    internal static string FormatSignature(MethodBase method)
    {
        var builder = new StringBuilder();
        if (method is MethodInfo info)
            builder.Append(TypeName(info.ReturnType)).Append(' ');
        builder.Append(method.DeclaringType?.FullName ?? "?");
        builder.Append("::");
        builder.Append(method.Name);
        builder.Append('(');
        builder.Append(string.Join(", ", method.GetParameters().Select(p => TypeName(p.ParameterType))));
        builder.Append(')');
        return builder.ToString();
    }

    internal static string TypeName(Type type) => type.FullName ?? type.Name;

    internal static string Sanitize(string? message) =>
        string.IsNullOrEmpty(message) ? string.Empty : message.Replace('\r', ' ').Replace('\n', ' ');

    private static int SafeToken(MemberInfo member)
    {
        try
        {
            return member.MetadataToken;
        }
        catch
        {
            return int.MaxValue;
        }
    }
}
