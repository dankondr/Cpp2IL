using System;
using System.Linq;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Metadata.Tables;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.OutputFormats;
using NUnit.Framework;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// castle-recovery#83 — IL2CPP folds literal fields (System.Math::PI/E) and
// strips helper methods it never exposes to managed callers
// (Unsafe::InitBlock/CopyBlock, Buffer::MemoryCopy, VectorN::Min/Max), while
// the emitted method bodies still name them: initblk/cpblk decompile to
// Unsafe.* calls, vector min/max lift to VectorN.Min/Max memberrefs, and the
// decompiler renders PI/E multiples as Math.PI/Math.E. FrameworkSurfaceMembers
// restores those members when the materialized bodies or live ISIL graphs
// demand them.
public class FrameworkSurfaceMembersTests
{
    // The fixture corlib's System.Math has no PI/E fields and its
    // System.Runtime.CompilerServices.Unsafe carries no InitBlock.
    [Test]
    public void BodySurfaceMembersAreRestoredFromIsilDemand()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var pi = new LocalVariable("pi", new Register(null, "pi")) { Type = app.SystemTypes.SystemDoubleType };
        var buffer = new LocalVariable("buffer", new Register(null, "buffer"))
            { Type = app.SystemTypes.SystemObjectType };
        var callerType = app.Assemblies.Last(a => a.Name != "mscorlib")
            .InjectType("Tests", "FrameworkSurfaceCaller", app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        var caller = callerType.InjectMethodContext("Run", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static);
        caller.ControlFlowGraph = new ISILControlFlowGraph(
        [
            // initblk — decompiles to Unsafe.InitBlock(ref buffer, ...)
            new(0, OpCode.MemorySet, buffer, new Immediate(0), new Immediate(16)),
            // ldc.r8 3.1415926535897931 — decompiles to Math.PI
            new(1, OpCode.Move, pi, new DoubleLiteral(Math.PI)),
            new(2, OpCode.Return),
        ]);
        caller.Locals = [pi, buffer];
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];

        var assemblies = new AsmResolverDllOutputFormatEmpty().BuildAssemblies(app);
        var corlib = assemblies.First(a => a.Name == "mscorlib").ManifestModule!;

        var math = corlib.TopLevelTypes.First(t => t.FullName == "System.Math");
        var piField = math.Fields.FirstOrDefault(f => f.Name?.ToString() == "PI");
        Assert.That(piField, Is.Not.Null, "an emitted ldc.r8 of PI must name a Math.PI the corlib carries");
        Assert.That(piField!.Constant?.Value is { } blob && BitConverter.ToDouble(blob.Data) == Math.PI,
            Is.True, "the restored field holds the real constant, not a fabricated value");
        Assert.That(piField.Attributes.HasFlag(FieldAttributes.Literal), Is.True);

        var unsafeType = corlib.TopLevelTypes.First(t =>
            t.FullName == "System.Runtime.CompilerServices.Unsafe");
        var initBlock = unsafeType.Methods.FirstOrDefault(m => m.Name?.ToString() == "InitBlock"
            && m.Signature is { } sig
            && sig.ParameterTypes.Count == 3
            && sig.ParameterTypes[0] is ByReferenceTypeSignature);
        Assert.That(initBlock, Is.Not.Null,
            "an emitted initblk must name an Unsafe.InitBlock the corlib carries");
        Assert.That(initBlock!.GenericParameters.Count, Is.EqualTo(1),
            "the restored InitBlock binds ref-to-any-type call sites");
        Assert.That(initBlock.CilMethodBody?.Instructions.Any(i => i.OpCode == CilOpCodes.Initblk),
            Is.True, "the restored member's body is the raw initblk the lifted code carried");
    }
}
