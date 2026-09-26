using System.Reflection;
using System.Text.Json;

namespace Cpp2IL.JitOracle;

/// <summary>
/// Explicitly enabled vector mode: invokes only the allowlisted public static
/// methods listed in a vectors JSON file, converts only primitive/string
/// arguments, and compares the exact result. No searching for "similar"
/// methods, no constructors, no arbitrary execution.
/// </summary>
public static class VectorRunner
{
    private static readonly HashSet<Type> SupportedTypes =
    [
        typeof(bool), typeof(sbyte), typeof(byte), typeof(short), typeof(ushort),
        typeof(int), typeof(uint), typeof(long), typeof(ulong),
        typeof(float), typeof(double), typeof(char), typeof(string),
    ];

    public static void Run(Assembly assembly, string vectorsPath, TextWriter sink, RunStats stats)
    {
        using var document = JsonDocument.Parse(File.ReadAllText(vectorsPath));
        var cases = document.RootElement.GetProperty("cases");

        foreach (var testCase in cases.EnumerateArray())
        {
            var descriptor = testCase.GetProperty("method").GetString()!;
            var args = testCase.GetProperty("args");
            var result = testCase.GetProperty("result");
            stats.VectorTotal++;
            try
            {
                RunCase(assembly, descriptor, args, result, sink, stats);
            }
            catch (Exception exception)
            {
                sink.WriteLine(JsonSerializer.Serialize(new
                {
                    record = "vector",
                    method = descriptor,
                    args,
                    outcome = "exception",
                    exception = exception.GetType().FullName,
                    message = Oracle.Sanitize(exception.Message),
                }));
                stats.VectorFailed++;
            }
        }
    }

    private static void RunCase(
        Assembly assembly, string descriptor, JsonElement args, JsonElement result,
        TextWriter sink, RunStats stats)
    {
        var separator = descriptor.LastIndexOf("::", StringComparison.Ordinal);
        if (separator <= 0)
        {
            EmitResolutionError(sink, stats, descriptor, args, "malformed-descriptor");
            return;
        }

        var typeName = descriptor[..separator];
        var methodName = descriptor[(separator + 2)..];

        var type = assembly.GetType(typeName, throwOnError: false);
        if (type is null)
        {
            EmitResolutionError(sink, stats, descriptor, args, "type-not-found");
            return;
        }

        var sameName = type
            .GetMethods(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Static
                        | BindingFlags.Instance | BindingFlags.DeclaredOnly)
            .Where(m => m.Name == methodName)
            .OrderBy(m => m.MetadataToken)
            .ToList();

        var candidates = sameName
            .Where(m => m.IsPublic && m.IsStatic && !m.ContainsGenericParameters
                        && m.GetParameters().Length == args.GetArrayLength())
            .OrderBy(m => m.MetadataToken)
            .ToList();

        if (candidates.Count == 0)
        {
            var reason = sameName.Count == 0 ? "method-not-found" : "no-public-static-overload";
            EmitResolutionError(sink, stats, descriptor, args, reason);
            return;
        }

        var method = candidates[0];
        var parameters = method.GetParameters();
        if (parameters.Any(p => !SupportedTypes.Contains(p.ParameterType))
            || !SupportedTypes.Contains(method.ReturnType))
        {
            EmitResolutionError(sink, stats, descriptor, args, "unsupported-signature");
            return;
        }

        object?[] invokeArgs;
        try
        {
            invokeArgs = parameters
                .Select((p, i) => ConvertArg(args[i], p.ParameterType))
                .ToArray();
        }
        catch (Exception)
        {
            EmitResolutionError(sink, stats, descriptor, args, "argument-conversion");
            return;
        }

        try
        {
            var actual = method.Invoke(null, invokeArgs);
            var expected = ConvertArg(result, method.ReturnType);
            var passed = Equals(actual, expected);
            sink.WriteLine(JsonSerializer.Serialize(new
            {
                record = "vector",
                method = descriptor,
                args,
                outcome = passed ? "pass" : "mismatch",
                expected,
                actual,
            }));
            if (passed)
                stats.VectorPassed++;
            else
                stats.VectorFailed++;
        }
        catch (Exception exception)
        {
            var cause = exception is TargetInvocationException { InnerException: not null } tie
                ? tie.InnerException
                : exception;
            sink.WriteLine(JsonSerializer.Serialize(new
            {
                record = "vector",
                method = descriptor,
                args,
                outcome = "exception",
                exception = cause!.GetType().FullName,
                message = Oracle.Sanitize(cause.Message),
            }));
            stats.VectorFailed++;
        }
    }

    private static void EmitResolutionError(
        TextWriter sink, RunStats stats, string descriptor, JsonElement args, string reason)
    {
        sink.WriteLine(JsonSerializer.Serialize(new
        {
            record = "vector",
            method = descriptor,
            args,
            outcome = "resolution-error",
            reason,
        }));
        stats.VectorFailed++;
    }

    private static object? ConvertArg(JsonElement value, Type type)
    {
        if (type == typeof(bool)) return value.GetBoolean();
        if (type == typeof(sbyte)) return value.GetSByte();
        if (type == typeof(byte)) return value.GetByte();
        if (type == typeof(short)) return value.GetInt16();
        if (type == typeof(ushort)) return value.GetUInt16();
        if (type == typeof(int)) return value.GetInt32();
        if (type == typeof(uint)) return value.GetUInt32();
        if (type == typeof(long)) return value.GetInt64();
        if (type == typeof(ulong)) return value.GetUInt64();
        if (type == typeof(float)) return value.GetSingle();
        if (type == typeof(double)) return value.GetDouble();
        if (type == typeof(char))
        {
            var s = value.GetString();
            if (s is { Length: 1 }) return s[0];
            throw new NotSupportedException("char vector value must be a single character");
        }
        if (type == typeof(string)) return value.ValueKind == JsonValueKind.Null ? null : value.GetString();
        throw new NotSupportedException("unsupported vector type: " + type.FullName);
    }
}
