using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// IL2CPP boxes a value that never escapes the call it is handed to on the stack
/// (<c>Il2CppFakeBox&lt;T&gt;</c> in il2cpp-codegen.h): a frame struct
/// <c>{ klass, monitor = IL2CPP_FAKE_BOX_SENTRY (-1), T m_Value }</c> whose address is
/// the boxed object - the receiver of e.g. <c>Enum.ToString</c> on an enum constant. The
/// lifter sees three frame stores and <c>&amp;klassCell</c> as the object, so the
/// receiver became the class pointer and the value was dropped as a dead store.
///
/// <see cref="Run"/> runs before the first dead-code pass (which would drop the sentry
/// and value stores nothing reads) and turns the address into a fresh local defined by
/// <c>Box local, klassCell, valueCell</c>. <see cref="ResolveTypes"/> runs once
/// metadata is resolved: the class operand becomes the value type it describes, or -
/// when it does not describe one - the rewrite is undone.
/// </summary>
public static class FakeBoxRecovery
{
    public static void Run(MethodAnalysisContext method)
    {
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        var cfg = method.ControlFlowGraph!;
        var reads = new Dictionary<LocalVariable, int>();
        var definitions = new Dictionary<LocalVariable, Instruction?>();
        foreach (var instruction in cfg.Instructions)
        {
            // A phi read is SSA bookkeeping at a join (the shared throw block of
            // inlined bounds checks merges every frame cell), not a use.
            if (instruction.OpCode != OpCode.Phi)
                foreach (var used in DeadCodeEliminator.UsedLocals(instruction))
                    reads[used] = reads.GetValueOrDefault(used) + 1;
            if (instruction.Destination is LocalVariable defined)
                definitions[defined] = definitions.ContainsKey(defined) ? null : instruction;
        }

        foreach (var block in cfg.Blocks)
        {
            // `p = &klassCell`, read once, by an instruction later in the block.
            for (var j = 0; j < block.Instructions.Count; j++)
            {
                if (block.Instructions[j] is not { OpCode: OpCode.Move,
                        Operands: [LocalVariable address, AddressOf { Target: LocalVariable addressed }] }
                    || FrameStructFieldReads.FrameOffset(addressed) is not { } offset
                    || reads.GetValueOrDefault(address) != 1)
                    continue;
                var u = block.Instructions.FindIndex(j + 1, i => i.Operands.Contains(address));
                if (u < 0
                    || LastFrameStore(block, u, offset) is not { Destination: LocalVariable klassCell }
                    || LastFrameStore(block, u, offset + pointerSize) is not
                        { Operands: [LocalVariable sentryCell, var sentry] }
                    || !IsSentry(sentry, definitions)
                    || reads.GetValueOrDefault(sentryCell) != 0
                    || LastFrameStore(block, u, offset + 2 * pointerSize) is not { Destination: LocalVariable valueCell })
                    continue;

                var user = block.Instructions[u];
                var boxed = new LocalVariable($"fakeBox_{user.Index}",
                    new Register(null, $"FAKEBOX_{method.Locals.Count}"));
                method.Locals.Add(boxed);
                block.Instructions.Insert(u, new Instruction(user.Index, OpCode.Box, boxed, klassCell, valueCell));
                for (var i = 0; i < user.Operands.Count; i++)
                    if (ReferenceEquals(user.Operands[i], address))
                        user.SetOperand(i, boxed);
            }
        }
    }

    // IL2CPP_FAKE_BOX_SENTRY is UINTPTR_MAX, often materialized once into a register.
    private static bool IsSentry(IOperand operand, Dictionary<LocalVariable, Instruction?> definitions)
    {
        for (var depth = 0; depth < 4; depth++)
        {
            if (operand is Immediate { Value: -1 })
                return true;
            if (operand is not LocalVariable local
                || definitions.GetValueOrDefault(local) is not { OpCode: OpCode.Move, Operands: [_, var source] })
                return false;
            operand = source;
        }
        return false;
    }

    public static void ResolveTypes(MethodAnalysisContext method)
    {
        var cfg = method.ControlFlowGraph!;
        foreach (var box in cfg.Instructions.ToList())
        {
            if (box is not { OpCode: OpCode.Box, Operands: [LocalVariable boxed, LocalVariable klassCell, _] }
                || !boxed.Name.StartsWith("fakeBox_"))
                continue;

            // The cell's resolved type, or what was moved into it (a class load or a copy of one).
            var source = cfg.Instructions.FirstOrDefault(i => ReferenceEquals(i.Destination, klassCell))
                is { OpCode: OpCode.Move, Operands: [_, var moved] } ? moved : null;
            var described = new[] { klassCell.Type, source, (source as LocalVariable)?.Type }
                .OfType<RuntimeClassTypeAnalysisContext>().FirstOrDefault()?.RepresentedType;
            // One frame cell holds the whole value only for a scalar; a wider struct
            // spans cells this rewrite does not gather.
            if (described is { IsValueType: true }
                && (IlGenerator.IntegralStackWidth(described) != 0
                    || described.FullName is "System.Single" or "System.Double"))
            {
                box.SetOperand(1, described);
                continue;
            }

            // Not a class pointer of a value type after all: hand the address back.
            foreach (var user in cfg.Instructions)
                for (var i = 0; i < user.Operands.Count; i++)
                    if (ReferenceEquals(user.Operands[i], boxed))
                        user.SetOperand(i, new AddressOf(klassCell));
            box.OpCode = OpCode.Nop;
            box.SetOperands();
        }
    }

    // The latest store into the frame cell at `offset` before position `end` of the block.
    private static Instruction? LastFrameStore(Graphs.Block block, int end, long offset)
    {
        for (var k = end - 1; k >= 0; k--)
            if (block.Instructions[k] is { OpCode: OpCode.Move, Destination: LocalVariable cell } store
                && FrameStructFieldReads.FrameOffset(cell) == offset)
                return store;
        return null;
    }
}
