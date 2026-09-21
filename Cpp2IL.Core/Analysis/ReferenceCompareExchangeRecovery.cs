using System;
using System.Collections.Concurrent;
using System.Linq;
using System.Runtime.CompilerServices;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

public static class ReferenceCompareExchangeRecovery
{
    private static readonly ConditionalWeakTable<ApplicationAnalysisContext, ConcurrentDictionary<ulong, bool>> Matches = new();

    public static void Run(MethodAnalysisContext method)
    {
        var app = method.AppContext;
        if (app.InstructionSet is not NewArmV8InstructionSet || app.Binary.PointerSizeBytes != 8)
            return;
        var cache = Matches.GetOrCreateValue(app);
        ResolveCalls(method, target => cache.GetOrAdd(target, address =>
        {
            var keys = app.GetOrCreateKeyFunctionAddresses();
            return MatchesHelper(address,
                a => BitConverter.ToUInt32(app.Binary.GetRawBinaryContent().Slice((int)app.Binary.MapVirtualAddressToRaw(a), 4).ToArray(), 0),
                a => a != 0 && (a == keys.il2cpp_codegen_write_barrier || keys.WriteBarrierAliases.Contains(a)));
        }));
    }

    // Run after copy coalescing: the address must still have exactly one definition.
    // Do not infer atomics from event names, generic method names or an ordinary store.
    internal static void ResolveCalls(MethodAnalysisContext method, Func<ulong, bool> matches)
    {
        var generic = method.AppContext.SystemTypes.SystemObjectType.DeclaringAssembly
            .GetTypeByFullName("System.Threading.Interlocked")?.Methods.SingleOrDefault(m =>
                m.Name == "CompareExchange" && m.IsStatic && m.GenericParameters.Count == 1
                && m.Parameters.Count == 3 && m.Parameters[0].ParameterType is ByRefTypeAnalysisContext);
        if (generic == null)
            return;
        var definitions = method.ControlFlowGraph!.Instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).Where(g => g.Count() == 1)
            .ToDictionary(g => g.Key, g => g.Single());
        foreach (var call in method.ControlFlowGraph.Instructions)
        {
            if (call is not { OpCode: OpCode.Call, Operands: [Immediate target, LocalVariable result, LocalVariable address, var value, var comparand, ..] }
                || !definitions.TryGetValue(address, out var producer)
                || producer is not { OpCode: OpCode.Add, Operands: [_, LocalVariable receiver, Immediate offset] }
                || receiver.Type is not { Definition: not null, IsValueType: false } owner
                || owner is PointerTypeAnalysisContext or ByRefTypeAnalysisContext or GenericParameterTypeAnalysisContext
                || !matches(target.UnsignedValue))
                continue;
            FieldAnalysisContext? field = null;
            for (var type = owner; type != null && field == null; type = type.BaseType)
                field = type.Fields.SingleOrDefault(f => !f.IsStatic && f.BackingData?.FieldOffset == offset.Value);
            if (field?.FieldType is not { IsValueType: false } referent
                || referent is PointerTypeAnalysisContext or ByRefTypeAnalysisContext or GenericParameterTypeAnalysisContext
                || referent.Definition == null)
                continue;
            call.SetOperands(generic.MakeGenericInstanceMethod(referent), result,
                new AddressOf(new FieldReference(field, receiver, (int)offset.Value)), value, comparand);
            result.Type = referent;

            var callBlock = method.ControlFlowGraph.Blocks.Single(block => block.Instructions.Contains(call));
            if (value is LocalVariable checkedValue
                && callBlock.Instructions.TakeWhile(i => i != call).All(i => i.OpCode == OpCode.Nop)
                && ReferenceCastRecovery.HasExactTypeGuard(callBlock, checkedValue, referent))
                call.SetOperand(3, new ReferenceCast(checkedValue, referent));

            if (comparand is LocalVariable previous)
            {
                var writes = method.ControlFlowGraph.Instructions
                    .Where(instruction => ReferenceEquals(instruction.Destination, previous)).ToArray();
                bool IsFieldLoad(Instruction instruction) => instruction is
                    { OpCode: OpCode.Move, Operands: [_, FieldReference source] }
                    && ReferenceEquals(source.Field, field)
                    && ReferenceEquals(source.Local, receiver);

                if (writes.Any(IsFieldLoad) && writes.All(instruction => IsFieldLoad(instruction)
                    || instruction is { OpCode: OpCode.Move, Operands: [_, var priorResult] }
                    && ReferenceEquals(priorResult, result)))
                    call.SetOperand(4, new ReferenceCast(previous, referent));
            }
        }
    }

    // This exact ABI wrapper calls a closed 64-bit acquire/release CAS kernel,
    // fences with DMB ISH, and invokes the independently resolved reference barrier.
    // Branch destinations and the CPU feature flag are relocatable, never game addresses.
    internal static bool MatchesHelper(ulong address, Func<ulong, uint> read, Func<ulong, bool> isBarrier)
    {
        try
        {
            uint[] wrapper = [0xf81e0ffe,0xa9014ff4,0xaa0003f4,0xaa0203f3,0xaa0203e0,0xaa1403e2,
                0,0xeb13001f,0xd5033bbf,0x9a800273,0xaa1403e0,0,0xaa1303e0,0xa9414ff4,0xf84207fe,0xd65f03c0];
            for (var i = 0; i < wrapper.Length; i++)
                if (wrapper[i] != 0 && read(address + (ulong)i * 4) != wrapper[i])
                    return false;
            var kernel = CallTarget(address + 24);
            var barrier = CallTarget(address + 44);
            if (kernel == 0 || !isBarrier(barrier))
                return false;
            uint[] body = [0xd503245f,0,0,0x34000070,0xc8e0fc41,0xd65f03c0,
                0xaa0003f0,0xc85ffc40,0xeb10001f,0x54000061,0xc811fc41,0x35ffff91,0xd65f03c0];
            for (var i = 0; i < body.Length; i++)
                if (body[i] != 0 && read(kernel + (ulong)i * 4) != body[i])
                    return false;
            // ADRP X16 + LDRB W16,[X16,#imm] reads only the CPU feature selector.
            return (read(kernel + 4) & 0x9f00001f) == 0x90000010
                && (read(kernel + 8) & 0xffc003ff) == 0x39400210;
        }
        catch (Exception)
        {
            return false; // unmapped/truncated/unknown native input is not proof
        }

        ulong CallTarget(ulong site)
        {
            var word = read(site);
            return (word & 0xfc000000) == 0x94000000
                ? unchecked((ulong)((long)site + ((int)(word << 6) >> 4))) : 0;
        }
    }
}
