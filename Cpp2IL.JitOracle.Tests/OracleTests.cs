using System.Text.Json;
using NUnit.Framework;

namespace Cpp2IL.JitOracle.Tests;

[TestFixture]
public sealed class OracleTests
{
    private static string ValidAssembly => Path.Combine(AppContext.BaseDirectory, "JitOracleFixtures.Valid.dll");
    private static string DepsDir => AppContext.BaseDirectory;

    private static (int Exit, string Stdout, string Stderr) Run(params string[] args)
    {
        var stdout = new StringWriter();
        var stderr = new StringWriter();
        var exit = Program.Run(args, stdout, stderr);
        return (exit, stdout.ToString(), stderr.ToString());
    }

    private static JsonDocument[] Records(string stdout) =>
        stdout.Split('\n', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries)
            .Select(line => JsonDocument.Parse(line))
            .ToArray();

    private static string FreshDir()
    {
        var dir = Path.Combine(TestContext.CurrentContext.WorkDirectory, Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(dir);
        return dir;
    }

    private static string WriteVectors(string dir, string json)
    {
        var path = Path.Combine(dir, "vectors.json");
        File.WriteAllText(path, json);
        return path;
    }

    [Test]
    public void Help_ShowsUsage()
    {
        var (exit, stdout, _) = Run("--help");
        Assert.That(exit, Is.EqualTo(0));
        Assert.That(stdout, Does.Contain("Usage:"));
    }

    [Test]
    public void MissingAssemblyArg_IsUsageError()
    {
        var (exit, _, stderr) = Run("--deps", DepsDir);
        Assert.That(exit, Is.EqualTo(2));
        Assert.That(stderr, Does.Contain("--assembly"));
    }

    [Test]
    public void MissingAssemblyFile_IsUsageError()
    {
        var (exit, _, _) = Run("--assembly", Path.Combine(DepsDir, "does-not-exist.dll"), "--deps", DepsDir);
        Assert.That(exit, Is.EqualTo(2));
    }

    [Test]
    public void PrepareOnly_ValidAssembly_PassesAndClassifies()
    {
        var (exit, stdout, _) = Run("--assembly", ValidAssembly, "--deps", DepsDir);
        Assert.That(exit, Is.EqualTo(0), stdout);

        var records = Records(stdout);
        Assert.That(records[0].RootElement.GetProperty("record").GetString(), Is.EqualTo("runtime"));
        Assert.That(records[0].RootElement.GetProperty("runtime").GetString(), Is.Not.Empty);
        Assert.That(records[0].RootElement.GetProperty("framework").GetString(), Is.Not.Empty);

        var methods = records.Where(r => r.RootElement.GetProperty("record").GetString() == "method").ToArray();
        Assert.That(methods.Select(m => m.RootElement.GetProperty("outcome").GetString()), Has.None.EqualTo("failed"));

        var prepared = methods.Where(m => m.RootElement.GetProperty("outcome").GetString() == "prepared")
            .Select(m => m.RootElement.GetProperty("signature").GetString()!).ToArray();
        Assert.That(prepared, Has.Some.Contains("Add("));
        Assert.That(prepared, Has.Some.Contains("Cat("));
        Assert.That(prepared, Has.Some.Contains("StaticOk("));
        Assert.That(prepared, Has.Some.Contains("Instance("));

        var skipReasons = methods.Where(m => m.RootElement.GetProperty("outcome").GetString() == "skipped")
            .Select(m => m.RootElement.GetProperty("reason").GetString()!).ToArray();
        Assert.That(skipReasons, Has.Member("abstract"));
        Assert.That(skipReasons, Has.Member("pinvoke"));
        Assert.That(skipReasons, Has.Member("internal-call"));
        Assert.That(skipReasons, Has.Member("open-generic"));
    }

    [Test]
    public void PrepareOnly_InvalidAssembly_DetectsAndContinues()
    {
        var dir = FreshDir();
        var invalid = FixtureEmit.EmitInvalidAssembly(dir);

        var (exit, stdout, _) = Run("--assembly", invalid, "--deps", dir);
        Assert.That(exit, Is.EqualTo(1), stdout);

        var records = Records(stdout);
        var methods = records.Where(r => r.RootElement.GetProperty("record").GetString() == "method").ToArray();

        var bad = methods.SingleOrDefault(m =>
            m.RootElement.GetProperty("signature").GetString()!.Contains("BadStlocOutOfRange"));
        Assert.That(bad, Is.Not.Null);
        Assert.That(bad!.RootElement.GetProperty("outcome").GetString(), Is.EqualTo("failed"));
        Assert.That(bad.RootElement.GetProperty("exception").GetString(),
            Is.EqualTo("System.InvalidProgramException"));

        var good = methods.Single(m => m.RootElement.GetProperty("signature").GetString()!.Contains("::Good("));
        Assert.That(good.RootElement.GetProperty("outcome").GetString(), Is.EqualTo("prepared"));

        // Every enumerated method was reached: the process did not die on the bad body.
        var summary = records.Last(r => r.RootElement.GetProperty("record").GetString() == "summary");
        Assert.That(summary.RootElement.GetProperty("methods").GetInt32(),
            Is.GreaterThanOrEqualTo(methods.Length));
        Assert.That(summary.RootElement.GetProperty("failed").GetInt32(), Is.GreaterThanOrEqualTo(1));
    }

    [Test]
    public void PrepareOnly_IsDeterministic()
    {
        var first = Run("--assembly", ValidAssembly, "--deps", DepsDir);
        var second = Run("--assembly", ValidAssembly, "--deps", DepsDir);
        Assert.That(first.Stdout, Is.EqualTo(second.Stdout));
    }

    [Test]
    public void Vectors_OnValidAssembly_AllPass()
    {
        var dir = FreshDir();
        var vectors = WriteVectors(dir, """
            {"schema":1,"cases":[
              {"method":"JitOracleFixtures.Valid.VectorMethods::Add","args":[1,2],"result":3},
              {"method":"JitOracleFixtures.Valid.VectorMethods::Cat","args":["x",2],"result":"x2"},
              {"method":"JitOracleFixtures.Valid.VectorMethods::BigXor","args":[8],"result":24},
              {"method":"JitOracleFixtures.Valid.VectorMethods::Half","args":[3.0],"result":1.5}
            ]}
            """);

        var (exit, stdout, _) = Run("--assembly", ValidAssembly, "--deps", DepsDir, "--vectors", vectors);
        Assert.That(exit, Is.EqualTo(0), stdout);

        var vectors_ = Records(stdout)
            .Where(r => r.RootElement.GetProperty("record").GetString() == "vector")
            .ToArray();
        Assert.That(vectors_.Length, Is.EqualTo(4));
        Assert.That(vectors_.Select(v => v.RootElement.GetProperty("outcome").GetString()),
            Has.All.EqualTo("pass"));
    }

    [Test]
    public void Vectors_OnCorruptAssembly_DeterministicallyFail()
    {
        var dir = FreshDir();
        var corrupt = FixtureEmit.EmitCorruptVectorsAssembly(dir);
        var vectors = WriteVectors(dir, """
            {"schema":1,"cases":[
              {"method":"JitOracleFixtures.Corrupt.Holder::Add","args":[1,2],"result":3},
              {"method":"JitOracleFixtures.Corrupt.Holder::Mul","args":[2,3],"result":6}
            ]}
            """);

        var (exit, stdout, _) = Run("--assembly", corrupt, "--deps", dir, "--vectors", vectors);
        Assert.That(exit, Is.EqualTo(1), stdout);

        var vectors_ = Records(stdout)
            .Where(r => r.RootElement.GetProperty("record").GetString() == "vector")
            .ToArray();
        Assert.That(vectors_.Length, Is.EqualTo(2));

        var add = vectors_.Single(v => v.RootElement.GetProperty("method").GetString()!.EndsWith("::Add"));
        Assert.That(add.RootElement.GetProperty("outcome").GetString(), Is.EqualTo("exception"));
        Assert.That(add.RootElement.GetProperty("exception").GetString(),
            Is.EqualTo("System.InvalidProgramException"));

        var mul = vectors_.Single(v => v.RootElement.GetProperty("method").GetString()!.EndsWith("::Mul"));
        Assert.That(mul.RootElement.GetProperty("outcome").GetString(), Is.EqualTo("pass"));
        Assert.That(mul.RootElement.GetProperty("actual").GetInt32(), Is.EqualTo(6));
    }

    [Test]
    public void Vectors_MissingType_IsResolutionError()
    {
        var dir = FreshDir();
        var vectors = WriteVectors(dir, """
            {"schema":1,"cases":[
              {"method":"No.Such.Type::Method","args":[],"result":0}
            ]}
            """);

        var (exit, stdout, _) = Run("--assembly", ValidAssembly, "--deps", DepsDir, "--vectors", vectors);
        Assert.That(exit, Is.EqualTo(1), stdout);

        var vector = Records(stdout).Single(r => r.RootElement.GetProperty("record").GetString() == "vector");
        Assert.That(vector.RootElement.GetProperty("outcome").GetString(), Is.EqualTo("resolution-error"));
        Assert.That(vector.RootElement.GetProperty("reason").GetString(), Is.EqualTo("type-not-found"));
    }
}
