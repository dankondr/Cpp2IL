namespace Cpp2IL.JitOracle;

public sealed class OracleOptions
{
    public string? AssemblyPath { get; private init; }
    public string? DependenciesDir { get; private init; }
    public string? VectorsPath { get; private init; }
    public string? OutputPath { get; private init; }
    public bool ShowHelp { get; private init; }
    public string? Error { get; private init; }

    public static OracleOptions Parse(string[] args)
    {
        if (args.Length == 0)
            return new OracleOptions { ShowHelp = true };

        string? assemblyPath = null;
        string? depsDir = null;
        string? vectorsPath = null;
        string? outputPath = null;
        string? error = null;

        for (var i = 0; i < args.Length && error is null; i++)
        {
            var arg = args[i];
            switch (arg)
            {
                case "-h":
                case "--help":
                    return new OracleOptions { ShowHelp = true };
                case "--assembly":
                    assemblyPath = Next(args, ref i, arg, ref error);
                    break;
                case "--deps":
                    depsDir = Next(args, ref i, arg, ref error);
                    break;
                case "--vectors":
                    vectorsPath = Next(args, ref i, arg, ref error);
                    break;
                case "--out":
                    outputPath = Next(args, ref i, arg, ref error);
                    break;
                default:
                    error = $"unknown argument: {arg}";
                    break;
            }
        }

        if (error is null && assemblyPath is null)
            error = "missing required --assembly <path>";

        return new OracleOptions
        {
            AssemblyPath = assemblyPath,
            DependenciesDir = depsDir,
            VectorsPath = vectorsPath,
            OutputPath = outputPath,
            Error = error,
        };

        static string? Next(string[] argv, ref int index, string flag, ref string? error)
        {
            if (index + 1 >= argv.Length)
            {
                error = $"missing value for {flag}";
                return null;
            }
            index++;
            return argv[index];
        }
    }
}
