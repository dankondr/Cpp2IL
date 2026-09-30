using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery tail of the scalar->object box cluster (castle-recovery#189): the
// retargeted `ref` locals a rescued method tail surfaces. A `T&` local whose
// binds repoint between an out parameter and locals cannot be spelled in C#
// (`ref` locals cannot rebind to a narrower scope, and binding an `out`
// parameter reads it unassigned) - so ByrefAliasForwarding resolves every use
// against the binding that reaches it and removes the alias.
public class RefAliasRebindTests
{
    private static (MethodAnalysisContext caller, MethodDefinition method) Setup(
        ApplicationAnalysisContext app, ModuleDefinition module,
        List<Instruction> instructions, List<LocalVariable> locals, List<LocalVariable> parameters)
    {
        var (caller, method) = ForeignCaller(app, module, instructions, locals);
        caller.ParameterLocals = parameters;
        method.Signature = MethodSignature.CreateStatic(module.CorLibTypeFactory.Void,
            parameters.Select(_ => (TypeSignature)new ByReferenceTypeSignature(
                module.CorLibTypeFactory.Byte)).ToArray());
        for (var i = 0; i < parameters.Count; i++)
            method.ParameterDefinitions.Add(
                new ParameterDefinition((ushort)(i + 1), parameters[i].Name, (ParameterAttributes)0));
        return (caller, method);
    }

    private static bool HasSelfCopy(IReadOnlyList<CilInstruction> il)
    {
        for (var i = 0; i + 1 < il.Count; i++)
        {
            if (il[i].OpCode is { } load && (load == CilOpCodes.Ldloc || load == CilOpCodes.Ldloc_S)
                && il[i + 1].OpCode is { } store
                && (store == CilOpCodes.Stloc || store == CilOpCodes.Stloc_S)
                && Equals(il[i].Operand, il[i + 1].Operand))
                return true;
        }
        return false;
    }

    [Test]
    public void ReboundRefAliasResolvesEachUseToReachingPointee()
    {
        // `r` binds &param on entry and &x inside a conditional arm; no use is
        // reached by both bindings, so each deref reads its reaching pointee
        // and the alias can go away entirely.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var byteType = app.SystemTypes.SystemByteType;
        var byteByRef = new ByRefTypeAnalysisContext(byteType);
        var module = new ModuleDefinition("RefRebind.dll");
        SeedCorLibTypes(app, module, byteType, app.SystemTypes.SystemVoidType,
            app.SystemTypes.SystemBooleanType, app.SystemTypes.SystemInt32Type);

        var p = new LocalVariable("p", new Register(0, "p"), byteByRef);
        var r = new LocalVariable("r", new Register(8, "r"), byteByRef);
        var x = new LocalVariable("x", new Register(1, "x"), byteType);
        var y = new LocalVariable("y", new Register(2, "y"), byteType);
        var flag = new LocalVariable("flag", new Register(3, "flag"),
            app.SystemTypes.SystemBooleanType);

        var rebind = new Instruction(4, OpCode.Move, r, new AddressOf(x));
        var ret = new Instruction(6, OpCode.Return);
        var instructions = new List<Instruction>
        {
            new(0, OpCode.Move, r, new AddressOf(p)),
            new(1, OpCode.CheckEqual, flag, x, y),
            new(2, OpCode.ConditionalJump, rebind, flag),
            new(3, OpCode.Move, new MemoryOperand(r, null, 0, accessSize: 1), new Immediate(7)),
            new(4, OpCode.Jump, ret),
            rebind,
            new(5, OpCode.Move, new MemoryOperand(r, null, 0, accessSize: 1), new Immediate(9)),
            ret,
        };

        var (caller, method) = Setup(app, module, instructions, [r, x, y, flag], [p]);
        ByrefAliasForwarding.Run(caller);
        IlGenerator.GenerateIl(caller, method);

        var body = method.CilMethodBody!;
        var il = body.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(caller.Locals.Contains(r), Is.False,
                "the rebound alias is eliminated entirely\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stind_I1 || i.OpCode == CilOpCodes.Stobj),
                Is.True,
                "the entry binding's use writes through the parameter\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => (i.OpCode == CilOpCodes.Stloc || i.OpCode == CilOpCodes.Stloc_S)),
                Is.True,
                "the arm binding's use writes the pointee directly\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void UniformAddressAliasResolvesPointeeAtCompoundUses()
    {
        // `r = &x` with a deref use [r+0] cannot forward &x (the root operand
        // is not a local), but the pointee x substitutes: [x+0] spells x's own
        // cell.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var byteType = app.SystemTypes.SystemByteType;
        var byteByRef = new ByRefTypeAnalysisContext(byteType);
        var module = new ModuleDefinition("RefPointee.dll");
        SeedCorLibTypes(app, module, byteType, app.SystemTypes.SystemVoidType);

        var r = new LocalVariable("r", new Register(8, "r"), byteByRef);
        var x = new LocalVariable("x", new Register(1, "x"), byteType);

        var instructions = new List<Instruction>
        {
            new(0, OpCode.Move, r, new AddressOf(x)),
            new(1, OpCode.Move, new MemoryOperand(r, null, 0, accessSize: 1), new Immediate(5)),
            new(2, OpCode.Return),
        };

        var (caller, method) = Setup(app, module, instructions, [r, x], []);
        ByrefAliasForwarding.Run(caller);
        IlGenerator.GenerateIl(caller, method);

        var body = method.CilMethodBody!;
        var il = body.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(caller.Locals.Contains(r), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(body.LocalVariables.Any(v => v.VariableType is ByReferenceTypeSignature),
                Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stloc || i.OpCode == CilOpCodes.Stloc_S),
                Is.True,
                "the store lands on the pointee's own cell\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void PathDependentAliasKeepsRefSlot()
    {
        // `r` binds &x on one edge and &y on the other; the join's deref really
        // is path-dependent, so the local stays a `ref` slot rather than
        // guessing one pointee.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var byteType = app.SystemTypes.SystemByteType;
        var byteByRef = new ByRefTypeAnalysisContext(byteType);
        var module = new ModuleDefinition("RefJoin.dll");
        SeedCorLibTypes(app, module, byteType, app.SystemTypes.SystemVoidType,
            app.SystemTypes.SystemBooleanType, app.SystemTypes.SystemInt32Type);

        var r = new LocalVariable("r", new Register(8, "r"), byteByRef);
        var x = new LocalVariable("x", new Register(1, "x"), byteType);
        var y = new LocalVariable("y", new Register(2, "y"), byteType);
        var flag = new LocalVariable("flag", new Register(3, "flag"),
            app.SystemTypes.SystemBooleanType);

        var bindX = new Instruction(3, OpCode.Move, r, new AddressOf(x));
        var join = new Instruction(5, OpCode.Move,
            new MemoryOperand(r, null, 0, accessSize: 1), new Immediate(1));
        var instructions = new List<Instruction>
        {
            new(0, OpCode.Move, r, new AddressOf(x)),
            new(1, OpCode.CheckEqual, flag, x, y),
            new(2, OpCode.ConditionalJump, join, flag),
            new(3, OpCode.Move, r, new AddressOf(y)),
            new(4, OpCode.Jump, join),
            join,
            new(6, OpCode.Return),
        };

        var (caller, method) = Setup(app, module, instructions, [r, x, y, flag], []);
        ByrefAliasForwarding.Run(caller);
        IlGenerator.GenerateIl(caller, method);

        Assert.That(caller.Locals.Contains(r), Is.True,
            "a use reached by different pointees keeps the ref local");
    }

    [Test]
    public void SelfCellCopyIsNotEmitted()
    {
        // `v = [v+0]` reads and writes the same cell - the emitter's `[v+0]`
        // shortcut spells it `v = v`, which a decompiler renders as an
        // unassigned self-read. The no-op copy is dropped instead.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("SelfCell.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemIntPtrType,
            app.SystemTypes.SystemVoidType);

        var v = new LocalVariable("v", new Register(8, "v"), app.SystemTypes.SystemIntPtrType);
        var instructions = new List<Instruction>
        {
            new(0, OpCode.Move, v, new Immediate(0)),
            new(1, OpCode.Move, v, new MemoryOperand(v, null, 0, accessSize: 8)),
            new(2, OpCode.Return),
        };

        var (caller, method) = ForeignCaller(app, module, instructions, [v]);
        ByrefAliasForwarding.Run(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.That(HasSelfCopy(il), Is.False,
            "a self-cell copy must not emit `ldloc x; stloc x`\n"
                + string.Join("\n", il.Select(i => i.ToString())));
    }
}
