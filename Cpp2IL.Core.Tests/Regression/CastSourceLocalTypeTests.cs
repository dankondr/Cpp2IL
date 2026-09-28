using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: compile bucket CS0039 (castle-recovery#116). A register reused
// for a differently-typed value strands a stale propagated type on the versioned
// local that reaches an isinst/castclass source slot once the producing Move is
// dead-code eliminated. The slot's contract is a managed object reference - the
// only proven type - so the local must be declared object, not the leftover type.
// A local with a non-cast use keeps its type: without proof the register carried
// the later type, the site stays diagnosed instead of silently retyped.
public class CastSourceLocalTypeTests
{
    [Test]
    public void StaleTypeOnOrphanCastSourceEmitsObject()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var target = app.SystemTypes.SystemExceptionType;
        var reused = new LocalVariable("reused", new Register(null, "reused"))
            { Type = app.SystemTypes.SystemStringType };
        var result = new LocalVariable("result", new Register(null, "result"))
            { Type = target };
        var module = new ModuleDefinition("CastSource.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemStringType, target,
            app.SystemTypes.SystemObjectType, app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, result, new ReferenceCast(reused, target, true)),
            new(1, OpCode.Return)], [reused, result]);

        IlGenerator.GenerateIl(caller, method);

        var body = method.CilMethodBody!;
        Assert.Multiple(() =>
        {
            Assert.That(body.LocalVariables[0].VariableType?.FullName, Is.EqualTo("System.Object"),
                () => string.Join("\n", body.LocalVariables.Select(v => v.VariableType?.FullName)));
            Assert.That(body.Instructions.Any(i => i.OpCode == CilOpCodes.Isinst), Is.True,
                () => string.Join("\n", body.Instructions.Select(i => i.ToString())));
        });
    }

    [Test]
    public void CastSourceWithOtherUseKeepsDeclaredType()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var target = app.SystemTypes.SystemExceptionType;
        var reused = new LocalVariable("reused", new Register(null, "reused"))
            { Type = app.SystemTypes.SystemStringType };
        var copy = new LocalVariable("copy", new Register(null, "copy"))
            { Type = app.SystemTypes.SystemStringType };
        var result = new LocalVariable("result", new Register(null, "result"))
            { Type = target };
        var module = new ModuleDefinition("CastSourceOtherUse.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemStringType, target,
            app.SystemTypes.SystemObjectType, app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, copy, reused),
            new(1, OpCode.Move, result, new ReferenceCast(reused, target, true)),
            new(2, OpCode.Return)], [reused, copy, result]);

        IlGenerator.GenerateIl(caller, method);

        var body = method.CilMethodBody!;
        Assert.Multiple(() =>
        {
            Assert.That(body.LocalVariables[0].VariableType?.FullName, Is.EqualTo("System.String"),
                () => string.Join("\n", body.LocalVariables.Select(v => v.VariableType?.FullName)));
            Assert.That(body.Instructions.Any(i => i.OpCode == CilOpCodes.Isinst), Is.True,
                () => string.Join("\n", body.Instructions.Select(i => i.ToString())));
        });
    }

    [Test]
    public void CastToObjectTargetKeepsDeclaredType()
    {
        // Demoting to object would equal the cast target, so the emitter drops
        // the redundant isinst and the null-check that consumed its result
        // decompiles into a raw local-vs-token compare. The stale declared type
        // keeps the isinst alive and the site compilable.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var target = app.SystemTypes.SystemObjectType;
        var reused = new LocalVariable("reused", new Register(null, "reused"))
            { Type = app.SystemTypes.SystemStringType };
        var result = new LocalVariable("result", new Register(null, "result"))
            { Type = target };
        var module = new ModuleDefinition("CastSourceObject.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemStringType, target,
            app.SystemTypes.SystemObjectType, app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, result, new ReferenceCast(reused, target, true)),
            new(1, OpCode.Return)], [reused, result]);

        IlGenerator.GenerateIl(caller, method);

        var body = method.CilMethodBody!;
        Assert.Multiple(() =>
        {
            Assert.That(body.LocalVariables[0].VariableType?.FullName, Is.EqualTo("System.String"),
                () => string.Join("\n", body.LocalVariables.Select(v => v.VariableType?.FullName)));
            Assert.That(body.Instructions.Any(i => i.OpCode == CilOpCodes.Isinst), Is.True,
                () => string.Join("\n", body.Instructions.Select(i => i.ToString())));
        });
    }
}
