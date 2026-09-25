using System.Reflection;
using System.Runtime.Loader;

namespace Cpp2IL.JitOracle;

/// <summary>
/// Resolves the target assembly's dependencies from a single directory.
/// Framework/facade references fall through to the default context so that
/// recovered <c>System.*</c> stubs never shadow the real BCL.
/// </summary>
public sealed class OracleLoadContext : AssemblyLoadContext
{
    private readonly string _dependenciesDir;

    public OracleLoadContext(string dependenciesDir)
        : base("jitoracle", isCollectible: true) => _dependenciesDir = dependenciesDir;

    protected override Assembly? Load(AssemblyName assemblyName)
    {
        var name = assemblyName.Name;
        if (name is null || IsFrameworkName(name))
            return null;

        var candidate = Path.Combine(_dependenciesDir, name + ".dll");
        return File.Exists(candidate) ? LoadFromAssemblyPath(candidate) : null;
    }

    private static bool IsFrameworkName(string name) =>
        name.Equals("mscorlib", StringComparison.Ordinal)
        || name.Equals("netstandard", StringComparison.Ordinal)
        || name.StartsWith("System", StringComparison.Ordinal)
        || name.StartsWith("Microsoft.", StringComparison.Ordinal);
}
