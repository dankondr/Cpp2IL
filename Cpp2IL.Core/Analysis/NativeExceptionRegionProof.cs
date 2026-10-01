using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using Cpp2IL.Core.Il2CppApiFunctions;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using LibCpp2IL;

namespace Cpp2IL.Core.Analysis;

// Compares native cleanup effects before SSA changes register/stack identities. A match
// includes the call arguments, not just the shared native target. The normal copy is
// subsequently emitted with its already-resolved managed signature and locals.
internal sealed class NativeExceptionRegionProof(MethodAnalysisContext context,
    Func<ulong, List<Instruction>?>? closureBody = null)
{
    internal sealed record Result(List<List<ulong>> CleanupCalls, List<EhCallSiteInfo> Sites, HashSet<ulong> Pads);
    private const string Exception = "exception", Wrapper = "exception-wrapper";
    private readonly List<Instruction> code = context.ExceptionRegionInstructions ?? [];
    private readonly Dictionary<ulong, List<Instruction>> nativeBodies = [];
    private readonly Dictionary<ulong, string?> helperNames = [];
    private readonly Dictionary<string, List<ulong>> cleanups = [];
    private int handlerSteps;
    private readonly Dictionary<int, State> exceptionStates = [];

    private sealed class State
    {
        internal int Frame;
        internal int Sp;
        internal Dictionary<string, string> Registers = [];
        internal Dictionary<string, string> Memory = [];
        internal Dictionary<string, int> MemoryWidths = [];
        internal Dictionary<string, string> StorageOrigins = [];
        internal List<string> Effects = [];
        internal HashSet<ulong> Pads = [];
        internal List<List<string>> AuxiliaryEffects = [];
        internal bool Terminated;
        internal bool Returned;
        internal State Copy() => new()
        {
            Frame = Frame, Sp = Sp, Registers = new(Registers), Memory = new(Memory), MemoryWidths = new(MemoryWidths),
            StorageOrigins = new(StorageOrigins), Effects = new(Effects), Pads = new(Pads), AuxiliaryEffects = new(AuxiliaryEffects), Terminated = Terminated, Returned = Returned
        };
    }

    internal static List<Instruction> Snapshot(List<Instruction> source)
    {
        var copies = source.ToDictionary(i => i, i => new Instruction(i.Index, i.OpCode, i.Operands.ToList())
        { NativeAddress = i.NativeAddress, NativeStoreWidthBytes = i.NativeStoreWidthBytes,
            NativeMemoryAccessSize = i.NativeMemoryAccessSize });
        foreach (var copy in copies.Values)
            for (var n = 0; n < copy.Operands.Count; n++)
                if (copy.Operands[n] is Instruction target && copies.TryGetValue(target, out var clone))
                    copy.SetOperand(n, clone);
        return source.Select(i => copies[i]).ToList();
    }

    internal List<Result> Find()
    {
        if (code.Count == 0 || context.UnwindInfo == null)
            return [];
        var states = NormalStates();
        if (states == null)
            return [];
        foreach (var (index, state) in states)
        {
            var instruction = code[index];
            if (instruction.OpCode == OpCode.CallVoid && CallKey(instruction, state) is { } key
                && Helper(instruction.Operands[0]) == null)
            {
                if (!cleanups.TryGetValue(key, out var addresses))
                    cleanups[key] = addresses = [];
                addresses.Add(instruction.NativeAddress);
            }
        }
        var results = new Dictionary<string, Result>();
        foreach (var site in context.UnwindInfo.CallSites)
        {
            // IL2CPP catches its C++ exception wrapper, then implements managed finally/catch
            // inside that clause. A selector alone is not evidence of a managed exception.
            var action = site.Actions?.FirstOrDefault(a => a.Filter > 0 && a.TypeInfo is > 0
                && KeyFunctionRecovery.IsExceptionWrapperTypeInfo(context, new Immediate(unchecked((long)a.TypeInfo.Value))));
            if (site.Actions == null || site.Actions.Any(a => a.Filter < 0)
                || action == null && !site.Actions.All(a => a.Filter == 0))
                continue;
            var seeds = Seeds(site, states).ToList();
            var entry = code.FindIndex(i => i.NativeAddress == site.LandingPad);
            if (seeds.Count == 0 || entry < 0) continue;
            var paths = new List<State>();
            var walked = true;
            foreach (var seed in seeds)
            {
                var state = seed.Copy();
                Clobber(state);
                state.Registers["X0"] = Exception;
                state.Registers["X1"] = Number(action?.Filter ?? 0);
                state.Pads.Add(site.LandingPad);
                handlerSteps = 4096;
                if (!WalkHandler(code, entry, state, [], paths, 0)) { walked = false; break; }
            }
            if (!walked || paths.Count == 0
                || paths.Any(p => p.Terminated || p.Returned || p.Effects.Count == 0 || p.Effects.Distinct().Count() != p.Effects.Count
                    || !p.Effects.SequenceEqual(paths[0].Effects)
                    || p.AuxiliaryEffects.Any(e => !e.SequenceEqual(p.Effects))))
                continue;
            var signature = string.Join(";", paths[0].Effects);
            if (!results.TryGetValue(signature, out var result))
            {
                var calls = paths[0].Effects.Select(effect => cleanups[effect].Distinct().ToList()).ToList();
                results[signature] = result = new(calls, [], []);
            }
            result.Sites.Add(site);
            foreach (var path in paths)
                result.Pads.UnionWith(path.Pads);
        }
        return results.Values.ToList();
    }

    internal sealed record CatchResult(TypeAnalysisContext Type, LocalVariable ExceptionLocal,
        List<Instruction> Handler, List<EhCallSiteInfo> Sites, HashSet<ulong> Pads, ulong MergeAddress, Instruction? Return = null);

    internal List<CatchResult> FindCatches(Func<ulong, bool>? wrapperTypeProof = null)
    {
        if (code.Count == 0 || context.UnwindInfo == null) return [];
        if (!code.Any(i => i.IsCall && Helper(i.Operands[0]) is
                nameof(BaseKeyFunctionAddresses.il2cpp_vm_object_is_inst) or "il2cpp_class_is_assignable_from")) return [];
        var states = NormalStates();
        if (states == null) return [];
        wrapperTypeProof ??= address => KeyFunctionRecovery.IsExceptionWrapperTypeInfo(context, new Immediate(unchecked((long)address)));
        var result = new List<CatchResult>();
        foreach (var site in context.UnwindInfo.CallSites)
        {
            var action = site.Actions?.FirstOrDefault(a => a.Filter > 0 && a.TypeInfo is > 0 && wrapperTypeProof(a.TypeInfo.Value));
            if (action == null || site.Actions!.Any(a => a.Filter < 0)) continue;
            var seeds = Seeds(site, states).ToList();
            var index = code.FindIndex(i => i.NativeAddress == site.LandingPad);
            if (seeds.Count == 0 || index < 0 || seeds.Any(s => s.Sp != seeds[0].Sp)) continue;
            var state = seeds[0].Copy();
            foreach (var seed in seeds.Skip(1))
            {
                Intersect(state.Registers, seed.Registers);
                Intersect(state.Memory, seed.Memory);
                Intersect(state.MemoryWidths, seed.MemoryWidths);
                Intersect(state.StorageOrigins, seed.StorageOrigins);
            }
            Clobber(state);
            state.Registers["X0"] = Exception;
            state.Registers["X1"] = Number(action.Filter);
            state.Pads.Add(site.LandingPad);
            var visited = new HashSet<int>();
            TypeAnalysisContext? type = null;
            while (visited.Count < 128 && visited.Add(index))
            {
                var instruction = code[index];
                if (context.LandingPadRegions.Any(p => p.PadAddress == instruction.NativeAddress)) state.Pads.Add(instruction.NativeAddress);
                if (instruction.IsCall)
                {
                    var args = instruction.Operands.Skip(instruction.OpCode == OpCode.CallVoid ? 1 : 2).Select(o => Value(o, state)).ToArray();
                    var helper = Helper(instruction.Operands[0]);
                    var classTest = helper == "il2cpp_class_is_assignable_from";
                    var catchType = args.Length < 2 ? null
                        : classTest && args[1] == "m(" + Exception + ")" ? ResolveCatchType(args[0])
                        : helper == nameof(BaseKeyFunctionAddresses.il2cpp_vm_object_is_inst) && args[0] == Exception
                            ? ResolveCatchType(args[1]) : null;
                    if (catchType != null)
                    {
                        type = catchType;
                        var mismatch = state.Copy();
                        Clobber(mismatch);
                        Set(instruction.Destination, Number(0), mismatch);
                        handlerSteps = 4096;
                        var paths = new List<State>();
                        if (index + 1 >= code.Count || !WalkHandler(code, index + 1, mismatch, [], paths, 0)
                            || paths.Count == 0 || paths.Any(p => p.Terminated || p.Returned || p.Effects.Count != 0)) { type = null; break; }
                        foreach (var path in paths) state.Pads.UnionWith(path.Pads);
                        Clobber(state);
                        Set(instruction.Destination, classTest ? Number(1) : Exception, state);
                        index++;
                        break;
                    }
                    if (helper == nameof(BaseKeyFunctionAddresses.il2cpp_codegen_initialize_runtime_metadata_inline))
                    {
                        var value = Load(args.FirstOrDefault(), state);
                        Clobber(state);
                        Set(instruction.Destination, value, state);
                        index++;
                        continue;
                    }
                    if (helper != "__cxa_begin_catch" || args.FirstOrDefault() != Exception) break;
                    Clobber(state);
                    Set(instruction.Destination, Wrapper, state);
                }
                else if (!TransferScaffolding(instruction, state, false)) break;
                var next = Successors(code, index, state).ToList();
                if (next.Count != 1) break;
                index = next[0];
            }
            if (type == null) continue;
            var exceptionLocal = new LocalVariable("caughtException", new Register(null, "EH_EXCEPTION"), type);
            var handler = new List<Instruction>();
            var handlerValues = new Dictionary<string, LocalVariable>();
            var endedCatch = false;
            var merge = -1;
            visited.Clear();
            while (index < code.Count && visited.Count < 128 && visited.Add(index))
            {
                if (states.ContainsKey(index)) { merge = index; break; }
                var instruction = code[index];
                if (endedCatch && instruction.OpCode == OpCode.Return)
                {
                    // Void catches reuse a normal return; a value catch proves its
                    // own return operand and gets a separate continuation below.
                    merge = context.IsVoid
                        ? states.Keys.Where(i => code[i].OpCode == OpCode.Return && code[i].Operands.Count == 0).DefaultIfEmpty(-1).First()
                        : index;
                    break;
                }
                if (instruction.IsCall || instruction.OpCode == OpCode.IndirectCall)
                {
                    if (Helper(instruction.Operands[0]) == nameof(BaseKeyFunctionAddresses.il2cpp_codegen_initialize_runtime_metadata_inline))
                    {
                        var argument = instruction.Operands.Skip(instruction.OpCode == OpCode.CallVoid ? 1 : 2).FirstOrDefault();
                        var value = argument == null ? null : Load(Value(argument, state), state);
                        Clobber(state);
                        Set(instruction.Destination, value, state);
                    }
                    else if (Helper(instruction.Operands[0]) == "__cxa_end_catch")
                    { endedCatch = true; Clobber(state); }
                    else
                    {
                        var virtualCall = instruction.OpCode == OpCode.IndirectCall;
                        var callee = virtualCall ? CatchVirtualCallee(instruction, state, type)
                            : instruction.Operands[0] as MethodAnalysisContext;
                        if (callee == null && instruction.Operands[0] is Immediate address
                            && context.AppContext.MethodsByAddress.TryGetValue(address.UnsignedValue, out var methods) && methods.Count == 1)
                            callee = methods[0];
                        callee ??= CatchCallee(instruction, state);
                        if (callee == null || callee.Name == ".ctor") break;
                        // Raw indirect calls reserve operand 1 for the result, even for void.
                        // Reference results use one register; aggregate and scalar ABI lowering stays outside this proof.
                        if (!callee.IsVoid && (instruction.Destination is not Register || callee.ReturnType.IsValueType
                            || callee.Parameters.Any(p => p.ParameterType.IsValueType))) break;
                        var count = callee.Parameters.Count + (callee.IsStatic ? 0 : 1);
                        var arguments = instruction.Operands.Skip(instruction.OpCode == OpCode.CallVoid ? 1 : 2).Take(count)
                            .Select(o => CatchArgument(o, state, exceptionLocal, handlerValues)).ToArray();
                        if (arguments.Length != count || arguments.Any(a => a == null)) break;
                        var operands = new List<IOperand> { callee };
                        LocalVariable? resultLocal = null;
                        if (!callee.IsVoid)
                        {
                            resultLocal = new LocalVariable("catchResult" + handler.Count,
                                new Register(null, "EH_RESULT_" + handler.Count), callee.ReturnType);
                            operands.Add(resultLocal);
                        }
                        operands.AddRange(arguments!);
                        handler.Add(new Instruction(handler.Count, callee.IsVoid ? OpCode.CallVoid : OpCode.Call, operands)
                            { NativeAddress = instruction.NativeAddress, IsVirtualDispatch = virtualCall });
                        InvalidateCallStorage(instruction, state, callee);
                        Clobber(state);
                        if (resultLocal != null)
                        {
                            var value = "catch-result:" + handler.Count;
                            handlerValues[value] = resultLocal;
                            Set(instruction.Destination, value, state);
                        }
                    }
                }
                else if (instruction is { OpCode: OpCode.Move, Destination: MemoryOperand memory }
                    && (instruction.NativeStoreWidthBytes ?? memory.AccessSize) is > 0 and var width
                    && ThisField(Address(memory, state), width) is { } field)
                {
                    var value = CatchArgument(instruction.Operands[1], state, exceptionLocal, handlerValues);
                    if (value == null) break;
                    handler.Add(new Instruction(handler.Count, OpCode.Move, [field, value]) { NativeAddress = instruction.NativeAddress });
                    Transfer(instruction, state);
                }
                else if (TryClassInitGuard(index, state, out var initialized, out var afterInit, out var join))
                {
                    handler.Add(initialized!);
                    state = afterInit!;
                    index = join;
                    continue;
                }
                else if (!TransferScaffolding(instruction, state, false)) break;
                var next = Successors(code, index, state).ToList();
                if (next.Count != 1) break;
                index = next[0];
            }
            // A value return gets its own continuation outside the catch. It must
            // not read the normal path's SSA return local, which has no catch input.
            Instruction? returned = null;
            ulong mergeAddress;
            if (merge < 0 || !endedCatch) continue;
            if (context.IsVoid)
            {
                if (!VoidEpilogue(merge, out mergeAddress)) continue;
            }
            else
            {
                returned = CatchReturn(merge, state, exceptionLocal, handlerValues);
                if (returned == null) continue;
                mergeAddress = returned.NativeAddress;
            }
            var existing = result.FirstOrDefault(r => r.Type == type && r.MergeAddress == mergeAddress
                && (r.Return == null ? returned == null : returned != null
                    && r.Return.Operands.Select(HandlerOperandKey).SequenceEqual(returned.Operands.Select(HandlerOperandKey)))
                && r.Handler.Count == handler.Count && r.Handler.Zip(handler).All(p =>
                    p.First.OpCode == p.Second.OpCode && p.First.IsVirtualDispatch == p.Second.IsVirtualDispatch
                    && p.First.Operands.Select(HandlerOperandKey)
                        .SequenceEqual(p.Second.Operands.Select(HandlerOperandKey))));
            if (existing != null) { existing.Sites.Add(site); existing.Pads.UnionWith(state.Pads); }
            else result.Add(new(type, exceptionLocal, handler, [site], state.Pads, mergeAddress, returned));
        }
        return result;
    }

    private static string? HandlerOperandKey(IOperand operand) => operand switch
    {
        MethodAnalysisContext method => method.DeclaringType?.DeclaringAssembly.Name + ":" + method.FullNameWithSignature,
        FieldReference field => $"{field.Offset}:{field}",
        _ => operand.ToString()
    };

    private static bool TransferScaffolding(Instruction instruction, State state, bool allowWrapperStore)
    {
        if (instruction.OpCode is not (OpCode.Nop or OpCode.Move or OpCode.ShiftStack or OpCode.Jump
            or OpCode.ConditionalJump or OpCode.Add or OpCode.Subtract or OpCode.Not
            or OpCode.CheckEqual or OpCode.CheckNotEqual or OpCode.CheckLess or OpCode.CheckGreater
            or OpCode.CheckLessOrEqual or OpCode.CheckGreaterOrEqual or OpCode.And or OpCode.Or or OpCode.Xor
            or OpCode.ShiftLeft or OpCode.ShiftRight)) return false;
        if (instruction.IsAssignment && instruction.OpCode != OpCode.Move && instruction.Destination is not Register) return false;
        // Instruction.Destination omits absolute-address stores as constants.
        // They are still effects and must not disappear from the unwind proof.
        if (instruction.OpCode == OpCode.Move && instruction.Operands[0] is MemoryOperand memory
            && !(allowWrapperStore && Address(memory, state) == Wrapper)
            && Address(memory, state)?.StartsWith("f", StringComparison.Ordinal) != true) return false;
        Transfer(instruction, state);
        return true;
    }

    private bool VoidEpilogue(int index, out ulong returnAddress)
    {
        returnAddress = 0;
        var seen = new HashSet<int>();
        while (index < code.Count && seen.Add(index))
        {
            var instruction = code[index];
            if (instruction.OpCode == OpCode.Return)
            {
                returnAddress = instruction.NativeAddress;
                return instruction.Operands.Count == 0 && context.IsVoid;
            }
            if (instruction.OpCode is not (OpCode.Move or OpCode.ShiftStack or OpCode.Nop or OpCode.Jump)) return false;
            if (instruction.OpCode == OpCode.Move && instruction.Destination is not Register) return false;
            var successors = Successors(code, index, new State()).ToList();
            if (successors.Count != 1) return false;
            index = successors[0];
        }
        return false;
    }

    private Instruction? CatchReturn(int index, State state, LocalVariable exceptionLocal,
        Dictionary<string, LocalVariable> handlerValues)
    {
        if (context.ReturnType is PointerTypeAnalysisContext or ByRefTypeAnalysisContext or GenericParameterTypeAnalysisContext) return null;
        state = state.Copy();
        var seen = new HashSet<int>();
        while (index < code.Count && seen.Add(index))
        {
            var instruction = code[index];
            if (instruction.OpCode == OpCode.Return)
            {
                if (instruction.Operands.Count != 1) return null;
                var value = CatchArgument(instruction.Operands[0], state, exceptionLocal, handlerValues);
                var types = context.AppContext.SystemTypes;
                if (context.ReturnType.IsValueType)
                {
                    if (value is not Immediate { Value: >= int.MinValue and <= int.MaxValue }
                        || context.ReturnType != types.SystemInt32Type && context.ReturnType != types.SystemBooleanType
                        || context.ReturnType == types.SystemBooleanType && value is not Immediate { Value: 0 or 1 }) return null;
                }
                else if (value is not Immediate { Value: 0 })
                {
                    var type = value is StringLiteral ? types.SystemStringType : (value as LocalVariable)?.Type;
                    while (type != null && type != context.ReturnType) type = type.DefaultBaseType;
                    if (type == null) return null;
                }
                return new Instruction(0, OpCode.Return, [value!]) { NativeAddress = instruction.NativeAddress };
            }
            if (instruction.OpCode is not (OpCode.Move or OpCode.ShiftStack or OpCode.Nop or OpCode.Jump)
                || instruction.OpCode == OpCode.Move && instruction.Destination is not Register) return null;
            Transfer(instruction, state);
            var next = Successors(code, index, state).ToList();
            if (next.Count != 1) return null;
            index = next[0];
        }
        return null;
    }

    private IOperand? CatchArgument(IOperand operand, State state, LocalVariable exceptionLocal,
        Dictionary<string, LocalVariable> handlerValues)
    {
        var value = Value(operand, state);
        if (value == Exception) return exceptionLocal;
        if (value != null && handlerValues.TryGetValue(value, out var result)) return result;
        var parameterLocal = context.ParameterLocals.FirstOrDefault(l => !l.IsMethodInfo && l.Type is { IsValueType: false }
            and not (PointerTypeAnalysisContext or ByRefTypeAnalysisContext or GenericParameterTypeAnalysisContext)
            && value == "argument:" + l.Register.Name);
        if (parameterLocal != null) return parameterLocal;
        try
        {
            if (MetadataAddress(value) is { } literalAddress
                && context.AppContext.LibCpp2IlContext.GetLiteralByAddress(literalAddress) is { } literalValue)
                return new StringLiteral(literalValue);
        }
        catch (Exception) { return null; }
        if (TryNumber(value, out var number)) return new Immediate(number);
        if (operand is StringLiteral literal) return literal;
        if (context.ParameterOperands.FirstOrDefault() is Register parameter && !context.IsStatic)
        {
            if (value == "argument:" + parameter.Name) return context.ParameterLocals.FirstOrDefault(l => l.IsThis);
            if (ThisField(value, 0) is { } field && field.Field.FieldType.IsValueType) return new AddressOf(field);
        }
        return null;
    }

    private FieldReference? ThisField(string? address, int width)
    {
        if (context.IsStatic || context.DeclaringType == null || context.ParameterOperands.FirstOrDefault() is not Register parameter
            || context.ParameterLocals.FirstOrDefault(l => l.IsThis) is not { } self) return null;
        var root = "argument:" + parameter.Name;
        var offset = 0L;
        if (address != root && (address == null || !address.StartsWith("(" + root + "+", StringComparison.Ordinal)
                || !address.EndsWith(')') || !long.TryParse(address[(root.Length + 2)..^1], out offset))) return null;
        if (width == 0 && offset >= 0 && offset <= int.MaxValue
            && MetadataResolver.FindInstanceFieldAtOffset(context.DeclaringType, offset) is { } whole)
            return new FieldReference(whole, self, (int)offset);
        if (offset < 0 || offset > int.MaxValue || MetadataResolver.FindInstanceFieldPathAtOffset(context.DeclaringType, offset, width) is not { } path)
            return null;
        if (width != 0 && StorageSize(path.Field.FieldType) != width) return null;
        return new FieldReference(path.Field, self, (int)offset, path.Containers, width);
    }

    private bool TryClassInitGuard(int index, State state, out Instruction? initialized, out State? after, out int join)
    {
        initialized = null;
        after = null;
        join = -1;
        if (index == 0 || code[index] is not { OpCode: OpCode.ConditionalJump } branch
            || branch.Operands[0] is not Instruction target) return false;
        var test = index - 1;
        var flag = branch.Operands[1];
        var negated = code[test] is { OpCode: OpCode.Not, Operands: [var destination, var input] }
            && Equals(destination, flag) && Equals(input, flag);
        if (negated) test--;
        if (test < 0 || code[test] is not { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual,
                Operands: [var compared, var loaded, Immediate { Value: 0 }] } comparison
            || !Equals(compared, flag) || (comparison.OpCode == OpCode.CheckEqual) != negated)
            return false;
        var read = Value(loaded, state);
        if (read == null || !read.StartsWith("m((", StringComparison.Ordinal) || !read.EndsWith("))", StringComparison.Ordinal)) return false;
        var plus = read.LastIndexOf('+');
        if (plus < 3 || !uint.TryParse(read[(plus + 1)..^2], out var offset)
            || !Il2CppClassUsefulOffsets.TryGetField(offset, context.AppContext.MetadataVersion, context.AppContext.Binary.is32Bit,
                out var field, out _) || field != Il2CppClassUsefulOffsets.Il2CppClassField.CctorFinished)
            return false;
        var klass = read[3..plus];
        if (ResolveClassType(klass) is not { } type) return false;
        join = code.IndexOf(target);
        if (join <= index + 1 || join > index + 12) return false;
        var initializedState = state.Copy();
        var called = false;
        for (var n = index + 1; n < join; n++)
        {
            var instruction = code[n];
            if (instruction.IsCall)
            {
                if (called || Helper(instruction.Operands[0]) is not ("il2cpp_runtime_class_init_export"
                        or "il2cpp_runtime_class_init_actual" or "il2cpp_codegen_runtime_class_init")
                    || instruction.Operands.Count <= (instruction.OpCode == OpCode.CallVoid ? 1 : 2) || Value(instruction.Operands[instruction.OpCode == OpCode.CallVoid ? 1 : 2], initializedState) != klass)
                    return false;
                called = true;
                InvalidateCallStorage(instruction, initializedState, null);
                Clobber(initializedState);
            }
            else if (instruction.OpCode != OpCode.Nop
                && (instruction.OpCode is not (OpCode.Move or OpCode.Add) || instruction.Destination is not Register
                    || !TransferScaffolding(instruction, initializedState, false))) return false;
        }
        if (!called) return false;
        var runInitializer = context.AppContext.SystemTypes.SystemObjectType.DeclaringAssembly.Types
            .FirstOrDefault(t => t.FullName == "System.Runtime.CompilerServices.RuntimeHelpers")?.Methods
            .FirstOrDefault(m => m.Name == "RunClassConstructor" && m.IsStatic && m.IsVoid
                && m.Parameters.Count == 1 && m.Parameters[0].ParameterType.FullName == "System.RuntimeTypeHandle");
        if (runInitializer == null) return false;
        // Preserve initializer effects explicitly. A completed class initializer is
        // a no-op in the CLR; the native guard's slow path performs the same action.
        initialized = new Instruction(index, OpCode.CallVoid, [runInitializer, type]) { NativeAddress = code[index + 1].NativeAddress };
        after = state.Copy();
        Intersect(after.Registers, initializedState.Registers);
        Intersect(after.Memory, initializedState.Memory);
        return true;
    }

    private MethodAnalysisContext? CatchVirtualCallee(Instruction instruction, State state, TypeAnalysisContext type)
    {
        // The function pointer and hidden MethodInfo must be the two halves of the
        // same virtual entry on the caught object's class. Keep callvirt dispatch.
        var target = Value(instruction.Operands[0], state);
        const string prefix = "m((m(exception)+";
        if (context.AppContext.Binary.is32Bit || target == null || !target.StartsWith(prefix, StringComparison.Ordinal)
            || !target.EndsWith("))", StringComparison.Ordinal) || !long.TryParse(target[prefix.Length..^2], out var offset)
            || Il2CppClassUsefulOffsets.GetVTableSlot(offset, context.AppContext.MetadataVersion, false) is not { } slot)
            return null;
        for (var declarer = type; declarer != null; declarer = declarer.DefaultBaseType)
        {
            var callee = declarer.Methods.FirstOrDefault(m => m.Definition?.slot == slot);
            if (callee == null) continue;
            var args = instruction.Operands.Skip(2).Select(o => Value(o, state)).ToArray();
            if (callee.IsStatic || callee.Parameters.Count != 0 || args.Length <= 1 || args[0] != Exception
                || args[callee.Parameters.Count + 1] != prefix + (offset + context.AppContext.Binary.PointerSizeBytes) + "))")
                return null;
            return callee;
        }
        return null;
    }

    private MethodAnalysisContext? CatchCallee(Instruction instruction, State state)
    {
        // Shared generic bodies can lack an address-map entry. As in
        // ResolveCallsViaMethodInfo, require metadata in the exact hidden slot.
        var arguments = instruction.Operands.Skip(instruction.OpCode == OpCode.CallVoid ? 1 : 2).ToArray();
        for (var n = 0; n < arguments.Length; n++)
        {
            if (MetadataAddress(Value(arguments[n], state)) is not { } address) continue;
            try
            {
                var usage = context.AppContext.LibCpp2IlContext.GetMethodGlobalByAddress(address);
                if (usage?.Type is not (MetadataUsageType.MethodDef or MetadataUsageType.MethodRef)) continue;
                var method = context.AppContext.ResolveContextForMethod(usage);
                if (method == null || method == context || !method.IsVoid || method.IsStatic || n != method.Parameters.Count + 1
                    || ThisField(Value(arguments[0], state), 0) is not { } receiver
                    || receiver.Field.FieldType.FullName != method.DeclaringType?.FullName) continue;
                return method;
            }
            catch (Exception) { }
        }
        return null;
    }

    private ulong? MetadataAddress(string? value)
    {
        if (value == null) return null;
        var loads = 0;
        while (value.StartsWith("m(", StringComparison.Ordinal) && value.EndsWith(')'))
        { loads++; value = value[2..^1]; }
        if (loads is < 1 or > 2 || !TryNumber(value, out var address)) return null;
        try { return loads == 2 ? context.AppContext.Binary.ReadPointerAtVirtualAddress(unchecked((ulong)address)) : unchecked((ulong)address); }
        catch (Exception) { return null; }
    }

    private TypeAnalysisContext? DefaultsClassType(string? value)
    {
        // Use the same absolute-pointer load and published layout map as
        // SeedIl2CppDefaultsClassTypes. Register copies retain this expression;
        // joins retain it only when all incoming native states agree.
        if (!context.AppContext.UnityVersion.GreaterThanOrEquals(6000) || value == null
            || !value.StartsWith("m((m(#", StringComparison.Ordinal) || !value.EndsWith("))", StringComparison.Ordinal)) return null;
        var plus = value.LastIndexOf('+');
        if (plus < 0 || !long.TryParse(value[(plus + 1)..^2], out var offset)) return null;
        var root = value[3..plus];
        if (!root.EndsWith(')') || !TryNumber(root[2..^1], out _)) return null;
        return KeyFunctionRecovery.Unity6PrimitiveDefaultsClass(context.AppContext.SystemTypes, offset);
    }

    private TypeAnalysisContext? ResolveClassType(string? value)
    {
        var type = DefaultsClassType(value)
            ?? code.SelectMany(i => i.Operands).OfType<TypeAnalysisContext>().FirstOrDefault(t => value == "type:" + t.FullName);
        if (type == null && value != null)
        {
            var loads = 0;
            while (value.StartsWith("m(", StringComparison.Ordinal) && value.EndsWith(')'))
            { loads++; value = value[2..^1]; }
            if (loads is 1 or 2 && TryNumber(value, out var address))
            {
                try
                {
                    var pointer = unchecked((ulong)address);
                    if (loads == 2) pointer = context.AppContext.Binary.ReadPointerAtVirtualAddress(pointer);
                    if (context.AppContext.LibCpp2IlContext.GetTypeGlobalByAddress(pointer) is { } metadataType)
                        type = context.AppContext.ResolveIl2CppType(metadataType);
                }
                catch (Exception) { return null; }
            }
        }
        return type;
    }

    private TypeAnalysisContext? ResolveCatchType(string? value)
    {
        var type = ResolveClassType(value);
        if (type == context.AppContext.SystemTypes.SystemObjectType && DefaultsClassType(value) == type) return type;
        for (var parent = type; parent != null; parent = parent.DefaultBaseType)
            if (parent == context.AppContext.SystemTypes.SystemExceptionType) return type;
        return null;
    }

    private IEnumerable<State> Seeds(EhCallSiteInfo site, Dictionary<int, State> states) => states
        .Where(p => (code[p.Key].IsCall || code[p.Key].OpCode == OpCode.IndirectCall)
            && code[p.Key].NativeAddress >= site.Start && code[p.Key].NativeAddress < site.End)
        .Select(p => exceptionStates.GetValueOrDefault(p.Key) ?? p.Value);

    private Dictionary<int, State>? NormalStates()
    {
        exceptionStates.Clear();
        var initial = new State();
        foreach (var operand in context.ParameterOperands.OfType<Register>())
            initial.Registers[operand.Name] = "argument:" + operand.Name;
        var states = new Dictionary<int, State> { [0] = initial };
        var pending = new Queue<int>();
        pending.Enqueue(0);
        var pads = context.UnwindInfo!.CallSites.Select(s => s.LandingPad).ToHashSet();
        var throws = context.ControlFlowGraph?.Instructions.Where(i => i.OpCode == OpCode.Throw)
            .Select(i => i.NativeAddress).ToHashSet() ?? [];
        // ponytail: bounded analysis rejects very large/slow-converging CFGs; raise the
        // bound only with a measured missed shape, rather than guessing their state.
        var callees = context.ControlFlowGraph?.Instructions.Where(i => i.IsCall && i.Operands[0] is MethodAnalysisContext)
            .GroupBy(i => i.NativeAddress).Where(g => g.Select(i => i.Operands[0]).Distinct().Count() == 1)
            .ToDictionary(g => g.Key, g => (MethodAnalysisContext)g.First().Operands[0]) ?? [];
        var budget = code.Count * 32;
        while (pending.Count > 0)
        {
            if (--budget < 0)
                return null;
            var index = pending.Dequeue();
            var instruction = code[index];
            var after = states[index].Copy();
            Transfer(instruction, after);
            if (instruction.IsCall || instruction.OpCode == OpCode.IndirectCall)
            {
                // Addressed native storage can be written by a call (including a hidden
                // struct result). Initial zeroes are not facts about the returned object.
                var callee = callees.GetValueOrDefault(instruction.NativeAddress);
                InvalidateCallStorage(instruction, after, callee);
                // A callee may write its arguments before throwing. Use the same
                // invalidation on the exceptional edge, before assigning a return value.
                exceptionStates[index] = after.Copy();
                if (instruction.Destination is MemoryOperand resultStorage && Address(resultStorage, after) is { } resultAddress)
                    after.StorageOrigins[resultAddress] = instruction.NativeAddress.ToString("X");
                Clobber(after);
                if (instruction.Destination is Register destination)
                    after.Registers[destination.Name] = "result:" + instruction.NativeAddress;
            }
            // Raw conversion retains a fall-through after a call whose no-return
            // contract was only recognized by the normal analysis. It must not merge
            // one out-of-line throw site's frame into the next throw site's frame.
            if ((instruction.IsCall || instruction.OpCode == OpCode.IndirectCall) && throws.Contains(instruction.NativeAddress)) continue;
            foreach (var next in Successors(code, index, states[index]))
            {
                if (pads.Contains(code[next].NativeAddress))
                    continue;
                if (!states.TryGetValue(next, out var existing))
                {
                    states[next] = after.Copy();
                    pending.Enqueue(next);
                }
                else
                {
                    if (existing.Sp != after.Sp)
                        return null;
                    if (Intersect(existing.Registers, after.Registers) | Intersect(existing.Memory, after.Memory)
                        | Intersect(existing.MemoryWidths, after.MemoryWidths)
                        | Intersect(existing.StorageOrigins, after.StorageOrigins))
                        pending.Enqueue(next);
                }
            }
        }
        return states;
    }

    private void InvalidateCallStorage(Instruction instruction, State state, MethodAnalysisContext? callee)
    {
        // A call can mutate heap cells through aliases or static state, even
        // without a pointer argument. Retain only independently tracked frame cells.
        foreach (var cell in state.Memory.Keys.Where(k => !k.StartsWith("f", StringComparison.Ordinal)).ToArray())
            state.Memory.Remove(cell);
        var arguments = instruction.Operands.Skip(instruction.OpCode == OpCode.CallVoid ? 1 : 2);
        // Boxing reads the value bytes; the barrier-only helper performs GC
        // bookkeeping after a separate store. Neither writes the frame slot.
        // Unknown calls and the exported write-barrier setter still invalidate it.
        var readOnlyStorage = Helper(instruction.Operands[0]) is nameof(BaseKeyFunctionAddresses.il2cpp_value_box)
            or nameof(BaseKeyFunctionAddresses.il2cpp_vm_object_box) or nameof(BaseKeyFunctionAddresses.il2cpp_codegen_write_barrier);
        var writes = arguments.Where(_ => !readOnlyStorage)
            .Select(o => (Address: Value(o, state), Size: ArgumentStorageSize(callee, o))).ToList();
        if (instruction.Destination is MemoryOperand result)
            writes.Add((Address(result, state), StorageSize(callee?.ReturnType)));
        foreach (var (address, size) in writes)
        {
            if (address?.StartsWith("f", StringComparison.Ordinal) != true) continue;
            var separator = address.IndexOf(':');
            if (separator < 0 || !long.TryParse(address[(separator + 1)..], out var start)) continue;
            foreach (var cell in state.Memory.Keys.ToArray())
                if (cell.StartsWith(address[..(separator + 1)], StringComparison.Ordinal)
                    && long.TryParse(cell[(separator + 1)..], out var offset) && (offset >= start || state.MemoryWidths.GetValueOrDefault(cell) == 0
                        || offset + state.MemoryWidths[cell] > start)
                    && (size == 0 || offset < start + size))
                    state.Memory.Remove(cell);
        }
    }

    private long ArgumentStorageSize(MethodAnalysisContext? callee, IOperand argument)
    {
        if (callee == null || argument is not Register register) return 0;
        var locations = context.AppContext.InstructionSet.GetParameterOperandsFromMethod(callee);
        var index = locations.FindIndex(o => o is Register r && r.Name == register.Name);
        if (index < 0) return 0;
        var type = !callee.IsStatic && index == 0 ? callee.DeclaringType
            : callee.Parameters.ElementAtOrDefault(index - (callee.IsStatic ? 0 : 1))?.ParameterType;
        if (type is ByRefTypeAnalysisContext byRef)
            return byRef.ElementType.IsValueType ? StorageSize(byRef.ElementType) : context.AppContext.Binary.PointerSizeBytes;
        return type is { IsValueType: true } ? StorageSize(type) : 0;
    }

    private long StorageSize(TypeAnalysisContext? type)
    {
        if (type == null || !type.IsValueType || type is GenericParameterTypeAnalysisContext) return 0;
        var pointerSize = context.AppContext.Binary.PointerSizeBytes;
        if (type is not GenericInstanceTypeAnalysisContext) return TypeSizes.UnboxedSize(type, pointerSize);
        // Use the existing instantiated field layout, not the erased generic
        // definition's sizeof(T). Unknown layouts keep the conservative invalidation.
        var fields = GenericInstanceFieldLayout.EnumerateInstanceFields(type, pointerSize);
        if (fields is not { Count: > 0 }) return 0;
        var end = fields.Max(f => f.Offset + f.Size);
        return (end + pointerSize - 1) / pointerSize * pointerSize;
    }

    private static bool Intersect<T>(Dictionary<string, T> target, Dictionary<string, T> incoming)
    {
        var changed = false;
        foreach (var key in target.Keys.ToArray())
            if (!incoming.TryGetValue(key, out var value) || !EqualityComparer<T>.Default.Equals(value, target[key]))
            { target.Remove(key); changed = true; }
        return changed;
    }

    private bool WalkHandler(List<Instruction> body, int index, State state, HashSet<int> visited,
        List<State> completed, int depth)
    {
        // ponytail: bound the whole branch tree as well as each path; complex
        // shared dispatchers remain diagnosed instead of expanding exponentially.
        if (--handlerSteps < 0 || depth > 5 || visited.Count > 192 || completed.Count > 32 || !visited.Add(index))
            return false;
        var instruction = body[index];
        if (context.LandingPadRegions.Any(p => p.PadAddress == instruction.NativeAddress))
            state.Pads.Add(instruction.NativeAddress);
        if (instruction.IsCall)
        {
            var cleanupKey = CallKey(instruction, state);
            var matchedCleanup = cleanupKey != null && cleanups.ContainsKey(cleanupKey);
            if (matchedCleanup)
                InvalidateCallStorage(instruction, state, instruction.Operands[0] as MethodAnalysisContext);
            ProveAuxiliaryPads(instruction, state, depth);
            var args = instruction.Operands.Skip(instruction.OpCode == OpCode.CallVoid ? 1 : 2)
                .Select(o => Value(o, state)).ToArray();
            var helper = Helper(instruction.Operands[0]);
            if (matchedCleanup)
            {
                state.Effects.Add(cleanupKey!);
                Clobber(state);
            }
            else if (helper is "__cxa_begin_catch")
            {
                if (args.FirstOrDefault() != Exception) return false;
                Clobber(state);
                Set(instruction.Destination, Wrapper, state);
            }
            else if (helper is "_ZSt9terminatev" or "std::terminate")
            {
                state.Terminated = true;
                completed.Add(state);
                return true;
            }
            else if (helper is "__cxa_end_catch")
                Clobber(state);
            else if (helper is "__cxa_allocate_exception")
            {
                if (args.FirstOrDefault() != Number(context.AppContext.Binary.PointerSizeBytes)) return false;
                Clobber(state);
                Set(instruction.Destination, Wrapper, state);
            }
            else if (helper is "__cxa_throw")
            {
                if (args.Length < 3 || args[0] != Wrapper || args[2] != Number(0)
                    || !state.Memory.TryGetValue(Wrapper, out var wrapped) || wrapped != Exception
                    || !TryNumber(args[1], out var typeInfo)
                    || !KeyFunctionRecovery.IsExceptionWrapperTypeInfo(context, new Immediate(typeInfo)))
                    return false;
                completed.Add(state);
                return true;
            }
            else if (helper is "il2cpp_raise_exception" or "il2cpp_vm_exception_raise" or "il2cpp_codegen_raise_exception"
                or "__cxa_rethrow" or "_Unwind_Resume")
            {
                if (helper != "__cxa_rethrow" && args.FirstOrDefault() != Exception) return false;
                completed.Add(state);
                return true;
            }
            else if (helper is "il2cpp_codegen_initialize_runtime_metadata" or "il2cpp_codegen_initialize_method"
                or "il2cpp_codegen_runtime_class_init")
            {
                InvalidateCallStorage(instruction, state, null);
                Clobber(state);
            }
            else if (instruction.Operands[0] is Immediate target && NativeBody(target.UnsignedValue) is { } nested)
            {
                var child = state.Copy();
                child.Frame = depth + 1;
                child.Sp = 0;
                foreach (var cell in child.Memory.Keys.Where(k => k.StartsWith($"f{child.Frame}:", StringComparison.Ordinal)).ToArray())
                { child.Memory.Remove(cell); child.MemoryWidths.Remove(cell); child.StorageOrigins.Remove(cell); }
                var exits = new List<State>();
                if (!WalkHandler(nested, 0, child, [], exits, depth + 1)) return false;
                if (exits.Count == 0) return false;
                foreach (var exit in exits)
                {
                    if (!exit.Returned) { completed.Add(exit); continue; }
                    // Returning from a cleanup closure is not an unwind exit. Continue
                    // its caller with the proven writes/effects and the caller's frame.
                    exit.Returned = false;
                    exit.Frame = state.Frame;
                    exit.Sp = state.Sp;
                    Clobber(exit);
                    var next = Successors(body, index, exit).ToList();
                    if (next.Count == 0 || !next.All(n => WalkHandler(body, n, exit.Copy(), new(visited), completed, depth)))
                        return false;
                }
                return true;
            }
            else
            {
                return false;
            }
        }
        else if (instruction.OpCode == OpCode.Throw && Value(instruction.Operands[0], state) == Exception)
        {
            completed.Add(state);
            return true;
        }
        else if (instruction.OpCode == OpCode.Return)
        {
            if (depth == 0 || state.Sp != 0 || instruction.Operands.Count != 0) return false;
            state.Returned = true;
            completed.Add(state);
            return true;
        }
        else if (!TransferScaffolding(instruction, state, true)) return false;
        var successors = Successors(body, index, state).ToList();
        return successors.Count > 0 && successors.All(next =>
            WalkHandler(body, next, state.Copy(), new(visited), completed, depth));
    }

    private void ProveAuxiliaryPads(Instruction call, State state, int depth)
    {
        if (depth >= 5) return;
        foreach (var site in context.UnwindInfo!.CallSites.Where(s => call.NativeAddress >= s.Start
                     && call.NativeAddress < s.End && !state.Pads.Contains(s.LandingPad)))
        {
            if (site.Actions == null || site.Actions.Any(a => a.Filter < 0)) continue;
            var entry = code.FindIndex(i => i.NativeAddress == site.LandingPad);
            if (entry < 0) continue;
            var auxiliary = state.Copy();
            auxiliary.Effects.Clear();
            auxiliary.AuxiliaryEffects.Clear();
            auxiliary.Pads.Add(site.LandingPad);
            Clobber(auxiliary);
            auxiliary.Registers["X0"] = Exception;
            auxiliary.Registers["X1"] = Number(0);
            var paths = new List<State>();
            if (!WalkHandler(code, entry, auxiliary, [], paths, depth + 1) || paths.Count == 0) continue;
            var terminateGuard = site.Actions.All(a => a.Filter > 0 && a.TypeInfo == 0)
                && paths.All(p => p.Terminated && p.Effects.Count == 0);
            if (!terminateGuard && paths.Any(p => p.Terminated || p.Returned || p.Effects.Count == 0)) continue;
            foreach (var path in paths)
            {
                state.Pads.UnionWith(path.Pads);
                if (!terminateGuard) state.AuxiliaryEffects.Add(path.Effects);
                state.AuxiliaryEffects.AddRange(path.AuxiliaryEffects);
            }
        }
    }

    private List<Instruction>? NativeBody(ulong address)
    {
        if (closureBody != null) return closureBody(address);
        if (nativeBodies.TryGetValue(address, out var existing)) return existing;
        try
        {
            if (context.AppContext.Binary.EhFunctions?.TryGetValue(address, out var extent) != true
                || extent is not { Size: <= 768 })
                return null;
            var method = new NativeMethodAnalysisContext(context.AppContext.SystemTypes.SystemObjectType, address, true);
            method.EnsureRawBytes();
            var body = context.AppContext.InstructionSet.GetIsilFromMethod(method);
            nativeBodies[address] = body;
            return body;
        }
        catch (Exception) { return null; }
    }

    private string? Helper(IOperand operand)
    {
        if (operand is StringLiteral literal) return literal.Value;
        if (operand is not Immediate target) return null;
        var address = target.UnsignedValue;
        if (helperNames.TryGetValue(address, out var name)) return name;
        var binary = context.AppContext.Binary;
        var keys = context.AppContext.GetOrCreateKeyFunctionAddresses();
        name = keys.Pairs.FirstOrDefault(p => p.Value == address).Key;
        if (name == null && keys.WriteBarrierAliases.Contains(address))
            name = nameof(BaseKeyFunctionAddresses.il2cpp_codegen_write_barrier);
        if (name == null && !binary.TryGetExportedFunctionName(address, out name))
            NewArm64KeyFunctionAddresses.TryResolveGotVeneerImportName(binary, address, out name!);
        if (string.IsNullOrEmpty(name) && KeyFunctionRecovery.IsClassIsAssignableFrom(binary, address))
            name = "il2cpp_class_is_assignable_from";
        helperNames[address] = string.IsNullOrEmpty(name) ? null : name;
        return helperNames[address];
    }

    private string? CallKey(Instruction instruction, State state)
    {
        if (instruction.OpCode != OpCode.CallVoid) return null;
        var arguments = instruction.Operands.Skip(1).Select(o => Value(o, state)).Select(value =>
            value != null && state.StorageOrigins.TryGetValue(value, out var origin) ? value + "@" + origin : value).ToArray();
        var target = instruction.Operands[0] is MethodAnalysisContext method ? method.FullNameWithSignature : instruction.Operands[0].ToString();
        return arguments.Any(a => a == null || !StableArgument(a.Split('@')[0])) ? null : target + "(" + string.Join(",", arguments) + ")";
    }

    private bool StableArgument(string value)
    {
        if (!value.StartsWith("m(", StringComparison.Ordinal)) return true;
        // Equal expressions are not equal values across a potentially mutating call.
        // Only metadata handles may be reloaded symbolically; arbitrary heap/frame
        // loads need a tracked value from the reaching definition.
        var address = value;
        var loads = 0;
        while (address.StartsWith("m(", StringComparison.Ordinal) && address.EndsWith(')'))
        { loads++; address = address[2..^1]; }
        if (!TryNumber(address, out var raw) || loads is < 1 or > 2) return false;
        try
        {
            var pointer = unchecked((ulong)raw);
            if (loads == 2) pointer = context.AppContext.Binary.ReadPointerAtVirtualAddress(pointer);
            return context.AppContext.LibCpp2IlContext.GetMethodGlobalByAddress(pointer)?.Type
                is MetadataUsageType.MethodDef or MetadataUsageType.MethodRef;
        }
        catch (Exception) { return false; }
    }

    private static IEnumerable<int> Successors(List<Instruction> body, int index, State state)
    {
        var instruction = body[index];
        if (instruction.OpCode is OpCode.Return or OpCode.Throw) yield break;
        if (instruction.OpCode is OpCode.Jump or OpCode.ConditionalJump or OpCode.IndirectJump)
        {
            var condition = instruction.OpCode == OpCode.ConditionalJump && instruction.Operands.Count > 1
                ? Value(instruction.Operands[1], state) : null;
            if (instruction.Operands[0] is Instruction target && body.IndexOf(target) is var destination && destination >= 0
                && condition != Number(0))
                yield return destination;
            if (instruction.OpCode != OpCode.ConditionalJump || condition == Number(1)) yield break;
        }
        if (index + 1 < body.Count) yield return index + 1;
    }

    private static void Clobber(State state)
    {
        for (var i = 0; i <= 18; i++) state.Registers.Remove("X" + i);
        for (var i = 0; i < 32; i++)
            if (i < 8 || i > 15) state.Registers.Remove("V" + i);
    }

    private static string Number(long value) => "#" + value.ToString(CultureInfo.InvariantCulture);
    private static bool TryNumber(string? value, out long number)
    { number = 0; return value is { Length: > 1 } && value[0] == '#' && long.TryParse(value[1..], out number); }
    private static string Frame(State state, int offset) => $"f{state.Frame}:{state.Sp + offset}";

    private static string? Plus(string? value, long offset)
    {
        if (value == null) return null;
        if (TryNumber(value, out var number)) return Number(unchecked(number + offset));
        if (value.StartsWith("f", StringComparison.Ordinal) && value.IndexOf(':') is var colon && colon > 0
            && long.TryParse(value[(colon + 1)..], out var displacement))
            return value[..(colon + 1)] + (displacement + offset);
        return offset == 0 ? value : value.Length < 160 ? $"({value}+{offset})" : null;
    }

    private static string? Address(MemoryOperand memory, State state)
    {
        var offset = memory.Addend;
        if (memory.Index != null)
        {
            if (!TryNumber(Value(memory.Index, state), out var index)) return null;
            offset = unchecked(offset + index * (memory.Scale <= 1 ? 1 : memory.Scale));
        }
        return Plus(memory.Base == null ? Number(0) : Value(memory.Base, state), offset);
    }

    private static string? Load(string? address, State state)
    {
        if (address == null) return null;
        if (state.Memory.TryGetValue(address, out var stored)) return stored;
        if (address == Wrapper) return Exception;
        return address.Length < 160 ? "m(" + address + ")" : null;
    }

    private static string? Value(IOperand operand, State state) => operand switch
    {
        Immediate immediate => Number(immediate.Value),
        TypeAnalysisContext type => "type:" + type.FullName,
        Register register => state.Registers.GetValueOrDefault(register.Name),
        LocalVariable local => "local:" + local.Name,
        StackOffset stack => Load(Frame(state, stack.Offset), state),
        AddressOf { Target: StackOffset stack } => Frame(state, stack.Offset),
        AddressOf { Target: LocalVariable local } => "&local:" + local.Name,
        MemoryOperand memory => Load(Address(memory, state), state),
        _ => null,
    };

    private static void Set(IOperand? operand, string? value, State state, int width = 0)
    {
        Dictionary<string, string>? storage = null;
        string? key = null;
        if (operand is Register register) { storage = state.Registers; key = register.Name; }
        else if (operand is StackOffset stack) { storage = state.Memory; key = Frame(state, stack.Offset); }
        else if (operand is MemoryOperand memory) { storage = state.Memory; key = Address(memory, state); }
        if (storage == null || key == null) return;
        if (ReferenceEquals(storage, state.Memory))
        {
            if (key.StartsWith("f", StringComparison.Ordinal) && key.IndexOf(':') is var colon
                && long.TryParse(key[(colon + 1)..], out var start))
                foreach (var cell in state.Memory.Keys.ToArray())
                    if (cell.StartsWith(key[..(colon + 1)], StringComparison.Ordinal)
                        && long.TryParse(cell[(colon + 1)..], out var offset)
                        && (width == 0 || offset < start + width)
                        && (offset >= start || state.MemoryWidths.GetValueOrDefault(cell) == 0
                                    || offset + state.MemoryWidths[cell] > start))
                        state.Memory.Remove(cell);
            state.MemoryWidths[key] = width;
        }
        if (value == null) storage.Remove(key); else storage[key] = value;
    }

    private static void Transfer(Instruction instruction, State state)
    {
        var operands = instruction.Operands;
        if (instruction.OpCode == OpCode.ShiftStack && operands[0] is Immediate shift)
        { state.Sp += (int)shift.Value; return; }
        if (instruction.Destination == null || instruction.IsCall || instruction.OpCode == OpCode.IndirectCall) return;
        var left = operands.Count > 1 ? Value(operands[1], state) : null;
        var right = operands.Count > 2 ? Value(operands[2], state) : null;
        string? result = null;
        if (instruction.OpCode == OpCode.Move) result = left;
        else if (instruction.OpCode is OpCode.Add or OpCode.Subtract && TryNumber(right, out var delta))
            result = Plus(left, instruction.OpCode == OpCode.Add ? delta : -delta);
        else if (instruction.OpCode == OpCode.Not && TryNumber(left, out var flag)) result = Number(flag == 0 ? 1 : 0);
        else if (instruction.OpCode is OpCode.CheckEqual or OpCode.CheckNotEqual
            && (TryNumber(left, out _) && TryNumber(right, out _)
                || left == Exception && right == Number(0) || right == Exception && left == Number(0)))
            result = Number((left == right) == (instruction.OpCode == OpCode.CheckEqual) ? 1 : 0);
        else if (TryNumber(left, out var a) && TryNumber(right, out var b))
            result = instruction.OpCode switch
            {
                OpCode.CheckLess => Number(a < b ? 1 : 0),
                OpCode.CheckLessOrEqual => Number(a <= b ? 1 : 0),
                OpCode.CheckGreater => Number(a > b ? 1 : 0),
                OpCode.CheckGreaterOrEqual => Number(a >= b ? 1 : 0),
                OpCode.And => Number(a & b),
                OpCode.Or => Number(a | b),
                OpCode.Xor => Number(a ^ b),
                _ => null
            };
        Set(instruction.Destination, result, state, instruction.NativeStoreWidthBytes
            ?? instruction.NativeMemoryAccessSize ?? (instruction.Destination is MemoryOperand memory ? memory.AccessSize : 0));
    }
}
