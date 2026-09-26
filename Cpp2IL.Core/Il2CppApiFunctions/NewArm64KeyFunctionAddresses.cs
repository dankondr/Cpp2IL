using System.Collections.Generic;
using System.Linq;
using Disarm;
using Cpp2IL.Core.Logging;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Il2CppApiFunctions;

public class NewArm64KeyFunctionAddresses : BaseKeyFunctionAddresses
{
    protected override ulong FindCodegenIsInstAfterRuntimeClassInit(ulong classInitVeneer)
    {
        var binary = _appContext.Binary;
        uint Read(ulong address) => System.BitConverter.ToUInt32(binary.GetRawBinaryContent()
            .Slice((int)binary.MapVirtualAddressToRaw(address), 4).ToArray(), 0);
        return AdjacentIsInstVeneer(classInitVeneer, Read);
    }

    internal static ulong AdjacentIsInstVeneer(ulong classInitVeneer, System.Func<ulong, uint> read)
        => IsUnconditionalBranch(read(classInitVeneer))
            && IsUnconditionalBranch(read(classInitVeneer + 4))
                ? classInitVeneer + 4
                : 0;

    private static bool IsUnconditionalBranch(uint word) => (word & 0xfc000000) == 0x14000000;

    // A function entry that is just one unconditional B forwards its caller to the
    // branch destination: an identity (one-hop / tail-call) veneer. Returns the
    // branch destination, or 0 when the entry word is unreadable or not an
    // unconditional B. `read` must return null for words it cannot supply.
    internal static ulong MatchTailCallVeneerTarget(ulong address, System.Func<ulong, uint?> read)
    {
        if (read(address) is not { } word || !IsUnconditionalBranch(word))
            return 0;
        var delta = (long)((int)(word << 6) >> 4);
        return unchecked((ulong)((long)address + delta));
    }

    // Linker-style GOT trampoline: adrp xd, page; ldr xt, [xd, #off];
    // (optional) add xd, xd, #off; br xt — materializes the call target from a
    // pointer slot. `read` must return null for unmappable/truncated words; any
    // word that cannot be read fails the match. On success returns the VA of the
    // pointer slot read by the ldr.
    internal static bool TryDecodeGotVeneerSlot(ulong address, System.Func<ulong, uint?> read, out ulong slotVa)
    {
        slotVa = 0;

        if (read(address) is not { } adrp || (adrp & 0x9f000000) != 0x90000000)
            return false;
        var pageReg = (int)(adrp & 0x1f);
        var imm21 = (long)((adrp >> 5) & 0x7ffff) << 2 | (long)((adrp >> 29) & 0x3);
        if ((imm21 & 0x100000) != 0)
            imm21 -= 0x200000;
        var page = (long)(address & ~0xfffUL) + (imm21 << 12);

        if (read(address + 4) is not { } ldr
            || (ldr & 0xffc00000) != 0xf9400000
            || (int)((ldr >> 5) & 0x1f) != pageReg)
            return false;
        var targetReg = (int)(ldr & 0x1f);
        var slotOffset = (long)((ldr >> 10) & 0xfff) * 8;

        var brWord = read(address + 8);
        if (brWord is { } maybeAdd
            && (maybeAdd & 0xff000000) == 0x91000000
            && (int)(maybeAdd & 0x1f) == pageReg
            && (int)((maybeAdd >> 5) & 0x1f) == pageReg)
            brWord = read(address + 12);

        if (brWord is not { } br
            || (br & 0xfffffc1f) != 0xd61f0000
            || (int)((br >> 5) & 0x1f) != targetReg)
            return false;

        slotVa = (ulong)(page + slotOffset);
        return true;
    }

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
        => IsFunctionStart(disassembly, index, CallTargets);

    internal static bool IsFunctionStart(List<Arm64Instruction> disassembly, int index, IReadOnlySet<ulong> callTargets)
    {
        if (callTargets.Contains(disassembly[index].Address))
            return true;

        if (index == 0)
            return true;

        // it's a function start if the previous instruction can't fall through into it
        var previous = disassembly[index - 1];
        return previous.Mnemonic is Arm64Mnemonic.RET or Arm64Mnemonic.RETAA or Arm64Mnemonic.RETAB or Arm64Mnemonic.BR or Arm64Mnemonic.BRK or Arm64Mnemonic.INVALID
               || (previous.Mnemonic == Arm64Mnemonic.B && previous.MnemonicConditionCode is Arm64ConditionCode.NONE or Arm64ConditionCode.AL);
    }

    /// <summary>
    /// Finds function-start veneers consisting of a single unconditional B whose
    /// destination is a resolved address. Returns (alias address, resolved name)
    /// pairs; the same blob scanned at any image base yields the same set.
    /// </summary>
    internal static List<KeyValuePair<ulong, string>> FindTailCallVeneerAliases(
        List<Arm64Instruction> disassembly, IReadOnlyDictionary<ulong, string> addressToName, IReadOnlySet<ulong> callTargets)
    {
        var aliases = new List<KeyValuePair<ulong, string>>();
        for (var index = 0; index < disassembly.Count; index++)
        {
            var instruction = disassembly[index];
            if (instruction.Mnemonic != Arm64Mnemonic.B
                || instruction.MnemonicConditionCode is not (Arm64ConditionCode.NONE or Arm64ConditionCode.AL)
                || !IsFunctionStart(disassembly, index, callTargets))
                continue;

            if (addressToName.TryGetValue(instruction.BranchTarget, out var name))
                aliases.Add(new(instruction.Address, name));
        }
        return aliases;
    }

    private Dictionary<ulong, string>? _addressToName;

    private Dictionary<ulong, string> GetAddressToNameMap()
    {
        if (_addressToName != null)
            return _addressToName;

        var map = new Dictionary<ulong, string>();
        foreach (var (name, address) in ResolvedAddresses)
            if (address != 0)
                map.TryAdd(address, name);

        // The worker the metadata-init wrapper calls doubles as the *_inline
        // entry's leaf, so bare tail-call veneers of it resolve under that name.
        if (il2cpp_codegen_initialize_runtime_metadata != 0
            && FindFirstCallTargetInMethod(il2cpp_codegen_initialize_runtime_metadata) is var initLeaf
            && initLeaf != 0)
            map.TryAdd(initLeaf, nameof(il2cpp_codegen_initialize_runtime_metadata_inline));

        return _addressToName = map;
    }

    protected override void ResolveVeneerAliases()
    {
        var addressToName = GetAddressToNameMap();
        var disassembly = DisassembleTextSection();

        foreach (var (address, name) in FindTailCallVeneerAliases(disassembly, addressToName, CallTargets))
            AddResolvedAlias(name, address);

        uint? Read(ulong va) => TryReadWord(va);
        for (var index = 0; index < disassembly.Count; index++)
            if (disassembly[index].Mnemonic == Arm64Mnemonic.ADRP
                && IsFunctionStart(disassembly, index)
                && TryResolveGotVeneer(disassembly[index].Address, addressToName, Read, out var name))
                AddResolvedAlias(name, disassembly[index].Address);
    }

    // Bounds-checked 4-byte read: null when va is unmappable or fewer than 4
    // bytes of the loaded image remain at the mapped offset.
    private uint? TryReadWord(ulong va)
    {
        var binary = _appContext.Binary;
        if (!binary.TryMapVirtualAddressToRaw(va, out var raw) || raw < 0 || raw + 4 > binary.RawLength)
            return null;
        return System.BitConverter.ToUInt32(binary.GetRawBinaryContent().Slice((int)raw, 4).ToArray(), 0);
    }

    private bool TryResolveGotVeneer(ulong address, IReadOnlyDictionary<ulong, string> addressToName,
        System.Func<ulong, uint?> read, out string name)
    {
        name = string.Empty;
        var binary = _appContext.Binary;
        if (!TryDecodeGotVeneerSlot(address, read, out var slotVa)
            || !binary.TryMapVirtualAddressToRaw(slotVa, out var slotRaw)
            || slotRaw < 0 || slotRaw + 8 > binary.RawLength)
            return false;
        // Dynamic relocations have already been applied to the loaded image, so the
        // slot holds the in-image VA for defined symbols and 0 for imports.
        var target = binary.ReadPointerAtVirtualAddress(slotVa);
        if (addressToName.TryGetValue(target, out var resolved))
        {
            name = resolved;
            return true;
        }
        return false;
    }

    private readonly HashSet<ulong> _rejectedAliasTargets = [];

    protected override bool TryResolveVeneerAlias(ulong address)
    {
        // Runs under the base alias lock on analysis threads; memoize rejects.
        if (_rejectedAliasTargets.Contains(address) || _appContext?.Binary is not { } binary)
            return false;

        var resolved = false;
        if (binary.TryMapVirtualAddressToRaw(address, out var raw) && raw >= 0 && raw + 4 <= binary.RawLength)
        {
            var addressToName = GetAddressToNameMap();
            uint? Read(ulong va) => TryReadWord(va);

            var branchTarget = MatchTailCallVeneerTarget(address, Read);
            if (branchTarget != 0 && addressToName.TryGetValue(branchTarget, out var name))
            {
                AddResolvedAlias(name, address);
                resolved = true;
            }
            else if (TryResolveGotVeneer(address, addressToName, Read, out var gotName))
            {
                AddResolvedAlias(gotName, address);
                resolved = true;
            }
        }

        if (!resolved)
            _rejectedAliasTargets.Add(address);
        return resolved;
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
