namespace Cpp2IL.JitOracle;

public static class Program
{
    public static int Main(string[] args) => Run(args, Console.Out, Console.Error);

    public static int Run(string[] args, TextWriter stdout, TextWriter stderr)
    {
        var options = OracleOptions.Parse(args);
        if (options.ShowHelp)
        {
            stdout.Write(Usage);
            return 0;
        }

        if (options.Error is { } error)
        {
            stderr.WriteLine("jitoracle: " + error);
            stderr.Write(Usage);
            return 2;
        }

        try
        {
            return Oracle.Run(options, stdout);
        }
        catch (Exception exception)
        {
            stderr.WriteLine($"jitoracle: {exception.GetType().FullName}: {exception.Message}");
            return 2;
        }
    }

    internal const string Usage = """
        jitoracle — minimal runtime JIT oracle for recovered .NET assemblies

        Usage:
          jitoracle --assembly <dll> [--deps <dir>] [--vectors <json>] [--out <file>]

        Options:
          --assembly <path>  Managed assembly to inspect (required).
          --deps <dir>       Directory containing dependency assemblies
                             (default: the target assembly's own directory).
          --vectors <file>   Enable vector mode: invoke ONLY the allowlisted public
                             static methods listed in the JSON file and compare their
                             exact results. Prepare-only remains the default without it.
          --out <file>       Write JSON records to this file instead of stdout.
          -h, --help         Show this help.

        Output is one JSON record per line (JSONL), ordered deterministically by
        metadata token. Prepare-only asks the runtime JIT to prepare every concrete
        method body (RuntimeHelpers.PrepareMethod) and never executes user code.
        Abstract, PInvoke, internal-call, open-generic and IL-less methods are
        reported as "skipped" with a reason.

        Exit codes:
          0  every concrete method prepared and every vector passed
          1  at least one preparation or vector failure
          2  usage / IO error
        """;
}
