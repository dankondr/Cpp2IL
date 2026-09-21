using System.Collections.Generic;
using System.Linq;
using Disarm;
using Cpp2IL.Core.Logging;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Il2CppApiFunctions;

public class NewArm64KeyFunctionAddresses : BaseKeyFunctionAddresses
{
    protected override ulong GetWriteBarrier()
    {
        var binary = _appContext.Binary;
        var export = binary.GetVirtualAddressOfExportedFunctionByName("il2cpp_gc_wbarrier_set_field");
        WriteBarrierAliases.Clear();
        if (export == 0)
            return 0;
        uint Read(ulong address) => System.BitConverter.ToUInt32(binary.GetRawBinaryContent().Slice((int)binary.MapVirtualAddressToRaw(address), 4).ToArray(), 0);
        var core = MatchWriteBarrierExport(export, Read);
        if (core == 0)
            return 0;
        WriteBarrierAliases.Add(core);
        // Only pure B veneers preserve the barrier-only ABI. In particular, never
        // include the exported setter or its STR wrapper: those perform the store.
        var branches = DisassembleTextSection().Where(i => i.Mnemonic == Arm64Mnemonic.B
            && i.MnemonicConditionCode is Arm64ConditionCode.NONE or Arm64ConditionCode.AL).ToArray();
        bool changed;
        do
        {
            changed = false;
            foreach (var branch in branches)
                if (WriteBarrierAliases.Contains(branch.BranchTarget))
                    changed |= WriteBarrierAliases.Add(branch.Address);
        } while (changed);
        return core;
    }

    // Export ABI: (object, slot, value). Match exact argument shuffle, then the
    // setter's exact STR followed by B; the B target is barrier-only (slot in X0).
    internal static ulong MatchWriteBarrierExport(ulong export, System.Func<ulong, uint> read)
    {
        if (read(export) != 0xaa0103e0 || read(export + 4) != 0xaa0203e1)
            return 0;
        var setter = Branch(export + 8);
        if (setter == 0 || read(setter) != 0xf9000001)
            return 0;
        return Branch(setter + 4);

        ulong Branch(ulong address)
        {
            var word = read(address);
            if ((word & 0xfc000000) != 0x14000000)
                return 0;
            var delta = (long)((int)(word << 6) >> 4);
            return unchecked((ulong)((long)address + delta));
        }
    }

    private List<Arm64Instruction>? _cachedDisassembledBytes;

    private List<Arm64Instruction> DisassembleTextSection()
    {
        if (_cachedDisassembledBytes == null)
        {
            var binary = _appContext.Binary;
            var toDisasm = binary.GetEntirePrimaryExecutableSection();
            _cachedDisassembledBytes = Disassembler.Disassemble(toDisasm, binary.GetVirtualAddressOfPrimaryExecutableSection(), new(true, true, false)).ToList();
        }

        return _cachedDisassembledBytes;
    }

    private HashSet<ulong> CallTargets => field ??=
    [
        .. DisassembleTextSection()
            .Where(i => i.Mnemonic == Arm64Mnemonic.BL)
            .Select(i => i.BranchTarget)
    ];

    private bool IsFunctionStart(List<Arm64Instruction> disassembly, int index)
    {
        if (CallTargets.Contains(disassembly[index].Address))
            return true;

        if (index == 0)
            return true;

        // it's a function start if the previous instruction can't fall through into it
        var previous = disassembly[index - 1];
        return previous.Mnemonic is Arm64Mnemonic.RET or Arm64Mnemonic.RETAA or Arm64Mnemonic.RETAB or Arm64Mnemonic.BR or Arm64Mnemonic.BRK or Arm64Mnemonic.INVALID
               || (previous.Mnemonic == Arm64Mnemonic.B && previous.MnemonicConditionCode is Arm64ConditionCode.NONE or Arm64ConditionCode.AL);
    }

    protected override IEnumerable<ulong> FindAllThunkFunctions(ulong addr, uint maxBytesBack = 0, params ulong[] addressesToIgnore)
    {
        //Disassemble .text
        var disassembly = DisassembleTextSection();

        for (var index = 0; index < disassembly.Count; index++)
        {
            var instruction = disassembly[index];

            // a thunk ends by tail-calling the real function
            if (instruction.Mnemonic != Arm64Mnemonic.B || instruction.MnemonicConditionCode is not (Arm64ConditionCode.NONE or Arm64ConditionCode.AL) || instruction.BranchTarget != addr)
                continue;

            if (addressesToIgnore.Contains(instruction.Address))
                continue;

            // walk back over any setup instructions to the start of the function containing the branch,
            // bailing if it's too far away to be a thunk
            var maxInstructionsBack = (int)(maxBytesBack / 4);
            for (var back = 0; back <= maxInstructionsBack && index - back >= 0; back++)
            {
                if (!IsFunctionStart(disassembly, index - back))
                    continue;

                var start = disassembly[index - back].Address;
                if (!addressesToIgnore.Contains(start))
                    yield return start;

                break;
            }
        }
    }

    protected override ulong FindFirstCallTargetInMethod(ulong methodVa)
    {
        var instructions = NewArm64Utils.GetArm64MethodBodyAtVirtualAddress(_appContext, methodVa, false);
        var call = instructions.FirstOrDefault(i => i.Mnemonic == Arm64Mnemonic.BL);
        return call.Mnemonic == Arm64Mnemonic.BL ? call.BranchTarget : 0;
    }

    protected override ulong GetObjectIsInstFromSystemType()
    {
        Logger.Verbose("\tTrying to use System.Type::IsInstanceOfType to find il2cpp::vm::Object::IsInst...");
        var typeIsInstanceOfType = ReflectionCache.GetType("Type", "System")?.Methods?.FirstOrDefault(m => m.Name == "IsInstanceOfType");
        if (typeIsInstanceOfType == null)
        {
            Logger.VerboseNewline("Type or method not found, aborting.");
            return 0;
        }

        //IsInstanceOfType is a very simple ICall, that looks like this:
        //  Il2CppClass* klass = vm::Class::FromIl2CppType(type->type.type);
        //  return il2cpp::vm::Object::IsInst(obj, klass) != NULL;
        //The last call is to Object::IsInst

        Logger.Verbose($"IsInstanceOfType found at 0x{typeIsInstanceOfType.MethodPointer:X}...");
        var instructions = NewArm64Utils.GetArm64MethodBodyAtVirtualAddress(_appContext, typeIsInstanceOfType.MethodPointer, false);

        var lastCall = instructions.LastOrDefault(i => i.Mnemonic == Arm64Mnemonic.BL);

        if (lastCall.Mnemonic == Arm64Mnemonic.INVALID)
        {
            Logger.VerboseNewline("Method does not match expected signature. Aborting.");
            return 0;
        }

        Logger.VerboseNewline($"Success. IsInst found at 0x{lastCall.BranchTarget:X}");
        return lastCall.BranchTarget;
    }

    protected override ulong FindFunctionThisIsAThunkOf(ulong thunkPtr, bool prioritiseCall = false)
    {
        var instructions = NewArm64Utils.GetArm64MethodBodyAtVirtualAddress(_appContext, thunkPtr, false);

        var target = prioritiseCall ? Arm64Mnemonic.BL : Arm64Mnemonic.B;
        var matchingCall = instructions.FirstOrDefault(i => i.Mnemonic == target);

        if (matchingCall.Mnemonic == Arm64Mnemonic.INVALID)
        {
            target = target == Arm64Mnemonic.BL ? Arm64Mnemonic.B : Arm64Mnemonic.BL;
            matchingCall = instructions.FirstOrDefault(i => i.Mnemonic == target);
        }

        return matchingCall.Mnemonic != Arm64Mnemonic.INVALID ? matchingCall.BranchTarget : 0;
    }

    protected override int GetCallerCount(ulong toWhere)
    {
        //Disassemble .text
        var disassembly = DisassembleTextSection();

        //Find all jumps to the target address
        return disassembly.Count(i => i.Mnemonic is Arm64Mnemonic.B or Arm64Mnemonic.BL && i.BranchTarget == toWhere);
    }
}
