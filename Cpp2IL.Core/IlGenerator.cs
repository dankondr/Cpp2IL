using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using System.Runtime.CompilerServices;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Extensions;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using Cpp2IL.Core.Utils.AsmResolver;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core;

public static class IlGenerator
{
    private const string HelpersNamespace = "Cpp2ILInjected";
    private const string HelpersTypeName = "Cpp2ILHelpers";
    private const string NoteIssueMethodName = "NoteDecompilerIssue";

    public static void InjectHelpersType(ApplicationAnalysisContext appContext)
    {
        var helpersType = appContext.InjectTypeIntoAllAssemblies(
            HelpersNamespace,
            HelpersTypeName,
            appContext.SystemTypes.SystemObjectType,
            TypeAttributes.Public | TypeAttributes.Class | TypeAttributes.Abstract | TypeAttributes.Sealed);

        helpersType.InjectMethodToAllAssemblies(
            NoteIssueMethodName,
            appContext.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static,
            [appContext.SystemTypes.SystemStringType]);
    }

    public static void GenerateIl(MethodAnalysisContext context, MethodDefinition definition)
    {
        var assembly = context.DeclaringType!.DeclaringAssembly;
        var module = definition.DeclaringModule!;
        var factory = module.CorLibTypeFactory;

        var noteIssueContext = assembly
            .GetTypeByFullName($"{HelpersNamespace}.{HelpersTypeName}")?.Methods.FirstOrDefault(m => m.Name == NoteIssueMethodName);

        var writeLine = noteIssueContext != null
            ? noteIssueContext.ToMethodDescriptor()
            : factory.CorLibScope
                .CreateTypeReference("System", "Console")
                .CreateMemberReference("WriteLine", MethodSignature.CreateStatic(factory.Void, [factory.String]));

        // Change branch targets to instructions
        foreach (var instruction in context.ControlFlowGraph!.Blocks.SelectMany(block => block.Instructions))
        {
            if (instruction.Operands.Count > 0 && instruction.Operands[0] is Block target)
            {
                if (target.Instructions.Count > 0)
                    instruction.SetOperand(0, target.Instructions[0]);
            }
        }

        var body = new CilMethodBody()
        {
            InitializeLocals = true, // Without this ILSpy does: CompilerServices.Unsafe.SkipInit(out object obj);
            // Compute per method below so one invalid reconstruction cannot abort the assembly.
            ComputeMaxStackOnBuild = false
        };

        definition.CilMethodBody = body;

        // Make sure context.Locals actually has all locals (idk why it doesn't sometimes)
        foreach (var operand in context.ControlFlowGraph.Instructions.SelectMany(i => i.Operands))
        {
            LocalVariable? local = null;

            if (operand is SelectedFieldReference selected)
            {
                if (!context.Locals.Contains(selected.Selector))
                    context.Locals.Add(selected.Selector);
                foreach (var receiver in selected.Choices.Select(c => c.Field.Local).Distinct())
                    if (!context.Locals.Contains(receiver))
                        context.Locals.Add(receiver);
            }

            if (operand is FieldReference field)
                local = field.Local;

            var elementField = operand switch
            {
                ArrayElementFieldReference direct => direct,
                AddressOf { Target: ArrayElementFieldReference addressedElementField } => addressedElementField,
                _ => null
            };
            if (elementField != null)
            {
                local = elementField.Array;
                if (elementField.Index is LocalVariable index && !context.Locals.Contains(index))
                    context.Locals.Add(index);
            }

            if (operand is LocalVariable local2)
                local = local2;

            if (operand is MemoryOperand memory && memory.Base is LocalVariable local3)
                local = local3;

            var elementOperand = operand is AddressOf { Target: ArrayAccess elementAddress } ? elementAddress : operand;

            if (elementOperand is ArrayAccess arrayAccess)
            {
                local = arrayAccess.Array;

                if (arrayAccess.Index is LocalVariable index && !context.Locals.Contains(index))
                    context.Locals.Add(index);
            }

            if (operand is ArrayLength arrayLength)
                local = arrayLength.Array;

            if (operand is AddressOf { Target: LocalVariable addressed })
                local = addressed;

            if (operand is AddressOf { Target: FieldReference addressedField })
                local = addressedField.Local;

            if (operand is ReferenceCast referenceCast)
                local = referenceCast.Value;

            if (local != null && !context.Locals.Contains(local))
                context.Locals.Add(local);
        }

        // Map ISIL locals to IL. The declared type joins the method body's locals
        // signature, so a local whose recovered type cannot be named here is
        // declared as the closest verifier-legal placeholder instead.
        Dictionary<LocalVariable, CilLocalVariable> locals = [];
        foreach (var local in context.Locals)
        {
            var emittedType = EmittableLocalType(EmittedLocalType(local, context), context);
            var ilType = emittedType == context.AppContext.SystemTypes.SystemObjectType
                ? module.CorLibTypeFactory.Object
                : emittedType == context.AppContext.SystemTypes.SystemBooleanType
                    ? module.CorLibTypeFactory.Boolean
                    : emittedType.ToTypeSignature();
            var ilLocal = new CilLocalVariable(ilType);
            body.LocalVariables.Add(ilLocal);
            locals.Add(local, ilLocal);
        }

        // Generate IL
        Dictionary<Instruction, List<CilInstruction>> instructionMap = [];
        var constructorPairs = FindConstructorPairs(context);
        var thisConstructorCalls = ThisConstructorCallPlan.Create(context);
        Dictionary<Block, CilInstruction> blockEntryMap = [];
        List<(CilInstruction BranchInstruction, Block TargetBlock)> pendingBlockBranchFixups = [];

        // An inlined-away constructor chain is re-anchored to the immediate base
        // constructor at the top of the body, where managed code runs it.
        foreach (var (constructor, arguments) in thisConstructorCalls?.PrologueCalls ?? [])
        {
            // A base .ctor the caller cannot name cannot be invoked; the stub keeps
            // the body honest - it throws, which the verifier permits in a .ctor.
            if (!CalleeUsableFrom(constructor, context))
            {
                EmitInaccessibleCalleeStub(constructor, definition, writeLine);
                continue;
            }
            body.Instructions.Add(CilOpCodes.Ldarg_0);
            for (var i = 0; i < constructor.Parameters.Count; i++)
            {
                if (i < arguments.Length && arguments[i] is { } argument)
                    LoadOperandIntoSlot(argument, constructor.Parameters[i].ParameterType, context, definition, locals, writeLine);
                else
                    PushDefaultOf(constructor.Parameters[i].ParameterType, definition, body.Instructions, context);
            }
            body.Instructions.Add(CilOpCodes.Call, constructor.ToMethodDescriptor());
        }

        foreach (var block in context.ControlFlowGraph!.Blocks)
        {
            if (block == context.ControlFlowGraph.EntryBlock || block == context.ControlFlowGraph.ExitBlock)
                continue;

            if (block.Instructions.Count == 0)
                continue;

            foreach (var instruction in block.Instructions)
            {
                var generated = GenerateInstructions(instruction, context, definition, locals, writeLine, constructorPairs, thisConstructorCalls);
                instructionMap.Add(instruction, generated);

                if (!blockEntryMap.ContainsKey(block) && generated.Count > 0)
                    blockEntryMap[block] = generated[0];
            }

            var lastInstruction = block.Instructions.Last();
            
            if (lastInstruction.OpCode == OpCode.ConditionalJump)
            {
                var trueTarget = TryResolveJumpTargetBlock(lastInstruction, context.ControlFlowGraph);
                var falseSuccessor = block.Successors.FirstOrDefault(s => s != trueTarget && s != context.ControlFlowGraph.ExitBlock);
                if (falseSuccessor == null) continue;
                var bridge = new CilInstruction(CilOpCodes.Br, new CilInstructionLabel());
                definition.CilMethodBody!.Instructions.Add(bridge);
                pendingBlockBranchFixups.Add((bridge, falseSuccessor));
            }

            else if (lastInstruction.OpCode != OpCode.Jump && lastInstruction.OpCode != OpCode.Return && lastInstruction.OpCode != OpCode.IndirectJump)
            {
                var successor = block.Successors.FirstOrDefault(s => s != context.ControlFlowGraph.ExitBlock);
                if (successor == null) continue;
                var bridge = new CilInstruction(CilOpCodes.Br, new CilInstructionLabel());
                definition.CilMethodBody!.Instructions.Add(bridge);
                pendingBlockBranchFixups.Add((bridge, successor));
            }
        }

        // Branches that land on a skipped this-constructor call resume at whatever
        // executes next, like fused constructor calls retargeting to their allocation.
        Dictionary<Instruction, CilInstruction> skippedThisConstructorRedirects = [];
        if (thisConstructorCalls != null)
        {
            foreach (var skipped in thisConstructorCalls.Skip)
            {
                var skippedBlock = context.ControlFlowGraph.FindBlockByInstruction(skipped);
                if (skippedBlock == null)
                    continue;

                CilInstruction? redirect = null;
                for (var i = skippedBlock.Instructions.IndexOf(skipped) + 1; i < skippedBlock.Instructions.Count && redirect == null; i++)
                    if (instructionMap.TryGetValue(skippedBlock.Instructions[i], out var mapped) && mapped.Count > 0)
                        redirect = mapped[0];

                if (redirect == null)
                    foreach (var successor in skippedBlock.Successors)
                        if ((redirect = ResolveBlockEntryInstruction(successor, blockEntryMap)) != null)
                            break;

                if (redirect != null)
                    skippedThisConstructorRedirects[skipped] = redirect;
            }
        }

        // Set IL branch targets
        foreach (var kvp in instructionMap)
        {
            var instruction = kvp.Key;
            var il = kvp.Value;

            if (instruction.OpCode == OpCode.Jump || instruction.OpCode == OpCode.ConditionalJump)
            {
                var ilBranch = il.First(i => i.OpCode == CilOpCodes.Br || i.OpCode == CilOpCodes.Brtrue);

                if (instruction.Operands[0] is Block targetBlock)
                {
                    context.AddWarning($"Branch target block not in cfg: {instruction} ({targetBlock})");
                    ilBranch.OpCode = CilOpCodes.Nop;
                    ilBranch.Operand = null;
                    continue;
                }

                var target = (Instruction)instruction.Operands[0];
                // A fused constructor call is not serialized as its own IL instruction. Retarget
                // branches that landed on it to the paired allocation that does survive emission.
                target = ConstructorAllocationForCall(target, constructorPairs) ?? target;

                var mappedTarget = instructionMap.TryGetValue(target, out var mapped) && mapped.Count > 0
                    ? mapped[0]
                    : skippedThisConstructorRedirects.TryGetValue(target, out var redirect) ? redirect : null;

                if (mappedTarget == null)
                {
                    context.AddWarning($"Branch target not in ISIL to IL map: {instruction} --- {target}");
                    ilBranch.OpCode = CilOpCodes.Nop;
                    ilBranch.Operand = null;
                    continue;
                }

                ilBranch.Operand = new CilInstructionLabel(mappedTarget);
            }
        }
        
        foreach (var (branchInstruction, targetBlock) in pendingBlockBranchFixups)
        {
            var target = ResolveBlockEntryInstruction(targetBlock, blockEntryMap);
            if (target == null)
            {
                context.AddWarning($"Unable to resolve branch target block: {targetBlock}");
                branchInstruction.OpCode = CilOpCodes.Nop;
                branchInstruction.Operand = null;
                continue;
            }

            branchInstruction.Operand = new CilInstructionLabel(target);
        }

        // Nothing may fall off the physical end of a body: a conditional branch
        // (or any other fall-through-capable opcode) as the last instruction
        // makes the verifier index a fall-through block past the code end. The
        // ISIL successor was the synthetic exit - an edge the CFG models without
        // a Return instruction - so the honest continuation is a plain return:
        // default(T) on the stack when the method returns a value.
        var lastEmitted = body.Instructions.LastOrDefault();
        if (lastEmitted != null && lastEmitted.OpCode.Code is not (CilCode.Br or CilCode.Br_S
                or CilCode.Ret or CilCode.Throw or CilCode.Leave or CilCode.Leave_S
                or CilCode.Jmp or CilCode.Endfinally or CilCode.Rethrow))
        {
            if (!context.IsVoid)
                PushDefaultOf(context.ReturnType, definition, body.Instructions, context);
            body.Instructions.Add(CilOpCodes.Ret);
        }

        // Add analysis warnings
        var instructions = body.Instructions;
        foreach (var warning in context.AnalysisWarnings)
        {
            instructions.Add(CilOpCodes.Ldstr, Diagnostic("Warning: " + warning));
            instructions.Add(CilOpCodes.Call, writeLine);
        }
        if (context.AnalysisWarnings.Count != 0)
        {
            // Even unreachable CIL must not fall off the physical end of a body:
            // the CLR rejects such a trailer before executing the valid entry path.
            // If malformed recovered control flow reaches diagnostics, fail closed.
            instructions.Add(CilOpCodes.Ldnull);
            instructions.Add(CilOpCodes.Throw);
        }

        try
        {
            body.MaxStack = body.ComputeMaxStack();
        }
        catch (StackImbalanceException exception)
        {
            // Preserve the invalid body as evidence, but never label failed stack analysis
            // as recovered or hide it behind a guessed stack bound.
            var warning = "Invalid reconstructed IL stack: " + exception.Message;
            context.AddWarning(warning);
            instructions.Add(CilOpCodes.Ldstr, Diagnostic(warning));
            instructions.Add(CilOpCodes.Call, writeLine);
            instructions.Add(CilOpCodes.Ldnull);
            instructions.Add(CilOpCodes.Throw);

            // The verifier rejects any push past the declared bound, and the
            // CilMethodBody default of 0 makes the first push of an otherwise
            // stack-consistent body report StackOverflow. The honest ceiling is
            // everything the body can push: an instruction never pushes more than
            // its opcode's push count, so no path exceeds their sum.
            body.MaxStack = (int)System.Math.Min(ushort.MaxValue,
                instructions.Sum(instruction => instruction.OpCode.StackBehaviourPush switch
                {
                    CilStackBehaviour.Push0 => 0L,
                    CilStackBehaviour.Push1_Push1 => 2L,
                    _ => 1L,
                }));
        }
    }


    // Limit so we don't run into the 16mb limit (see AsmResolver issue #775)
    private static string Diagnostic(string message) 
        => message.Length <= 250 ? message : message[..250] + "…";

    // Replaces a call the verifier could never resolve with the standard diagnostic stub:
    // note the unnameable callee, then throw. The ISIL operands are never loaded, so the
    // stack stays balanced and the destination (if any) keeps its default.
    private static void EmitInaccessibleCalleeStub(MethodAnalysisContext callee, MethodDefinition method,
        IMethodDescriptor writeLine)
    {
        var instructions = method.CilMethodBody!.Instructions;
        var module = method.DeclaringModule!;
        var diagnostic = Diagnostic($"Inaccessible callee: {callee.FullNameWithSignature}");
        instructions.Add(CilOpCodes.Ldstr, diagnostic);
        instructions.Add(CilOpCodes.Call, writeLine);
        instructions.Add(CilOpCodes.Ldstr, diagnostic);
        instructions.Add(CilOpCodes.Newobj, module.CorLibTypeFactory.CorLibScope
            .CreateTypeReference("System", "Exception")
            .CreateMemberReference(".ctor", MethodSignature.CreateInstance(module.CorLibTypeFactory.Void,
                [module.CorLibTypeFactory.String])));
        instructions.Add(CilOpCodes.Throw);
    }

    private static Block? TryResolveJumpTargetBlock(Instruction jumpInstruction, ISILControlFlowGraph cfg)
    {
        if (jumpInstruction.Operands.Count == 0)
            return null;

        if (jumpInstruction.Operands[0] is Block targetBlock)
            return targetBlock;

        if (jumpInstruction.Operands[0] is Instruction targetInstruction)
            return cfg.FindBlockByInstruction(targetInstruction);

        return null;
    }

    private static CilInstruction? ResolveBlockEntryInstruction(Block block,
        Dictionary<Block, CilInstruction> blockEntryMap, HashSet<Block>? visited = null)
    {
        if (blockEntryMap.TryGetValue(block, out var target))
            return target;

        visited ??= [];
        if (!visited.Add(block))
            return null;

        foreach (var successor in block.Successors)
        {
            var resolved = ResolveBlockEntryInstruction(successor, blockEntryMap, visited);
            if (resolved != null)
                return resolved;
        }
        return null;
    }

    private static List<CilInstruction> GenerateInstructions(Instruction instruction, MethodAnalysisContext context,
        MethodDefinition method, Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine,
        IReadOnlyDictionary<Instruction, Instruction> constructorPairs, ThisConstructorCallPlan? thisConstructorCalls)
    {
        var body = method.CilMethodBody!;
        var instructions = body.Instructions;
        var currentCount = instructions.Count;
        var startIndex = instructions.Count;

        if (constructorPairs.Values.Contains(instruction))
            return [];

        if (thisConstructorCalls?.Skip.Contains(instruction) == true)
            return [];

        var module = method.DeclaringModule!;

        switch (instruction.OpCode)
        {
            case OpCode.Invalid:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Invalid instruction: {instruction}"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;

            case OpCode.NotImplemented:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Not implemented instruction: {instruction.Operands[0]}"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;

            case OpCode.Interrupt:
            case OpCode.Nop:
                instructions.Add(CilOpCodes.Nop);
                break;

            case OpCode.Move:
                // Il2CppClass::static_fields is a native implementation pointer, not a
                // managed value. Field accesses rooted in this local are emitted as
                // ldsfld/stsfld, so materializing the pointer only creates a bogus
                // unmanaged load before otherwise valid static-field IL.
                if (instruction.Operands is
                    [LocalVariable { Type: StaticFieldStorageTypeAnalysisContext },
                     MemoryOperand { Index: null, Scale: 0,
                         Base: LocalVariable { Type: RuntimeClassTypeAnalysisContext } }])
                {
                    instructions.Add(CilOpCodes.Nop);
                    break;
                }

                if (instruction.Operands[0] is MemoryOperand
                    { Index: null, Addend: 0, Scale: 0, Base: LocalVariable
                        { Type: ByRefTypeAnalysisContext { ElementType: { IsValueType: false } referent } } address } store
                    && referent is not (PointerTypeAnalysisContext or ByRefTypeAnalysisContext or GenericParameterTypeAnalysisContext)
                    && store.AccessSize == context.AppContext.Binary.PointerSizeBytes)
                {
                    LoadLocal(address, method, locals, context);
                    LoadOperandIntoSlot(instruction.Operands[1], referent, context, method, locals, writeLine);
                    instructions.Add(CilOpCodes.Stind_Ref);
                    break;
                }

                if (instruction.Operands[0] is FieldReference field) // stfld takes instance before value so LoadOperand StoreToOperand doesn't work
                {
                    if (WholeValueContainerReference(field,
                            EmittedOperandType(instruction.Operands[1], context)) is { } wholeValue
                        && FieldReferenceUsableFrom(wholeValue, context, writeAccess: true))
                    {
                        if (!wholeValue.Field.IsStatic)
                            LoadFieldReceiver(wholeValue, context, method, locals, writeLine);
                        LoadOperandIntoSlot(instruction.Operands[1], wholeValue.Field.FieldType,
                            context, method, locals, writeLine);
                        instructions.Add(wholeValue.Field.IsStatic ? CilOpCodes.Stsfld : CilOpCodes.Stfld,
                            wholeValue.Field.IsStatic ? wholeValue.Field.ToFieldDescriptor()
                                : FieldDescriptorFor(wholeValue.Field, FieldReceiverType(wholeValue, context)));
                        break;
                    }
                    if (BackingFieldConversion(field, context) is { } conversion)
                    {
                        if (field.Containers.Count == 0)
                        {
                            LoadOperandIntoSlot(instruction.Operands[1], conversion.Parameters[0].ParameterType,
                                context, method, locals, writeLine);
                            instructions.Add(CilOpCodes.Call, conversion.ToMethodDescriptor());
                            StoreToOperand(field.Local, method, locals, writeLine, context);
                            break;
                        }

                        var outerField = field.Containers[^1];
                        var outer = new FieldReference(outerField, field.Local, outerField.Offset,
                            field.Containers.Take(field.Containers.Count - 1).ToArray());
                        if (FieldReferenceUsableFrom(outer, context, writeAccess: true))
                        {
                            if (!outerField.IsStatic)
                                LoadFieldReceiver(outer, context, method, locals, writeLine);
                            LoadOperandIntoSlot(instruction.Operands[1], conversion.Parameters[0].ParameterType,
                                context, method, locals, writeLine);
                            instructions.Add(CilOpCodes.Call, conversion.ToMethodDescriptor());
                            instructions.Add(outerField.IsStatic ? CilOpCodes.Stsfld : CilOpCodes.Stfld,
                                outerField.IsStatic ? outerField.ToFieldDescriptor()
                                    : FieldDescriptorFor(outerField, FieldReceiverType(outer, context)));
                            break;
                        }
                    }
                    if (!FieldReferenceUsableFrom(field, context, writeAccess: true))
                    {
                        EmitUnrecoverableOperation(method, writeLine,
                            $"Inaccessible field store: {field.Field.DeclaringType?.FullName}.{field.Field.Name}");
                        break;
                    }
                    if (!field.Field.IsStatic)
                    {
                        // Same rule as the recovery stfld path: inside the
                        // declaring .ctor `this` is the only legal initonly
                        // receiver regardless of whether the local provably
                        // aliases it.
                        if (field.Containers.Count == 0 && RequiresThisPointerReceiver(field.Field, context)
                            && (field.Local is null or LocalVariable
                                || ThisAliasLocals(context).Contains(field.Local)))
                            instructions.Add(CilOpCodes.Ldarg_0);
                        else
                            LoadFieldReceiver(field, context, method, locals, writeLine);
                    }

                    LoadOperandIntoSlot(instruction.Operands[1], field.Field.FieldType, context, method, locals, writeLine);
                    instructions.Add(field.Field.IsStatic ? CilOpCodes.Stsfld : CilOpCodes.Stfld,
                        field.Field.IsStatic ? field.Field.ToFieldDescriptor()
                            : FieldDescriptorFor(field.Field, FieldReceiverType(field, context)));
                    break;
                }

                // stelem needs array and index before the value, so like stfld it can't go through LoadOperand/StoreToOperand.
                // This also lets ILSpy handle it as a proper array initializer
                if (instruction.Operands[0] is ArrayAccess { Array.Type: SzArrayTypeAnalysisContext { ElementType: { } stored } } target)
                {
                    LoadArrayBase(target.Array, method, locals, context);
                    LoadOperandIntoSlot(target.Index, context.AppContext.SystemTypes.SystemInt32Type, context, method, locals, writeLine);
                    LoadOperand(instruction.Operands[1], method, locals, writeLine, stored, context);
                    CoerceOrDefault(EmittedOperandType(instruction.Operands[1], context, stored), stored, method, context);
                    if (StelemOpCode(stored) is { } stelemOp)
                        instructions.Add(stelemOp);
                    else if (TypeTokenUsableFrom(stored, context))
                        instructions.Add(CilOpCodes.Stelem, stored.ToTypeSignature().ToTypeDefOrRef());
                    else
                        EmitUnrecoverableOperation(method, writeLine,
                            $"Inaccessible array element type: {stored.FullName}");
                    break;
                }

                var moveDestinationType = StoreContract(instruction.Operands[0], context);
                LoadOperandIntoSlot(instruction.Operands[1], moveDestinationType, context, method, locals, writeLine);
                StoreToOperand(instruction.Operands[0], method, locals, writeLine, context);
                break;

            case OpCode.SignExtend32:
                LoadOperandIntoSlot(instruction.Operands[1], context.AppContext.SystemTypes.SystemInt32Type, context, method, locals, writeLine);
                instructions.Add(CilOpCodes.Conv_I4);
                instructions.Add(CilOpCodes.Conv_I8);
                EmitStackCoerceOrDefault(context.AppContext.SystemTypes.SystemInt64Type,
                    StoreContract(instruction.Operands[0], context), method, context);
                StoreToOperand(instruction.Operands[0], method, locals, writeLine, context);
                break;

            case OpCode.NewArr:
                var newArrayDestination = StoreContract(instruction.Operands[0], context);
                if (instruction.Operands is [_, SzArrayTypeAnalysisContext { ElementType: { } newArrayElement }, { } length])
                {
                    if (TypeTokenUsableFrom(newArrayElement, context))
                    {
                        LoadOperandIntoSlot(length, context.AppContext.SystemTypes.SystemInt32Type, context, method, locals, writeLine);
                        instructions.Add(CilOpCodes.Newarr, newArrayElement.ToTypeSignature().ToTypeDefOrRef());
                        CoerceOrDefault(new SzArrayTypeAnalysisContext(newArrayElement), newArrayDestination, method, context);
                    }
                    else
                    {
                        // The element type cannot be named here (e.g. a shared-generic
                        // instantiation over a corlib-internal marker); the honest array
                        // value is a default of the slot type.
                        instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Inaccessible array element type: {newArrayElement.FullName}"));
                        instructions.Add(CilOpCodes.Call, writeLine);
                        EmitNullOrDefault(newArrayDestination, method, instructions, context);
                    }
                }
                else if (newArrayDestination is { IsValueType: true } && CanEmitTypeToken(newArrayDestination))
                    EmitDefaultValueLocal(newArrayDestination, method, instructions, context);
                else
                    EmitNullOrDefault(StoreContract(instruction.Operands[0], context), method, instructions, context);

                StoreToOperand(instruction.Operands[0], method, locals, writeLine, context);
                break;

            case OpCode.Newobj:
                // Try and fuse our Newobj + the follow up constructor CallVoid into one IL newobj.
                // If we can't, just fall back to an Ldnull.
                var allocatedDestination = StoreContract(instruction.Operands[0], context);
                if (constructorPairs.TryGetValue(instruction, out var constructorCall)
                    && constructorCall.Operands is [MethodAnalysisContext constructor, _, ..])
                {
                    List<IOperand>? inlinedDefaultArgs = null;
                    var allocationType = AllocatedClassOperand(context, instruction) ?? allocatedDestination;
                    if (constructor.DeclaringType?.FullName == "System.Object"
                        && allocationType != null
                        && TryGetOptionalInlinedConstructor(allocationType, context,
                            out var optionalConstructor, out inlinedDefaultArgs))
                    {
                        constructor = optionalConstructor;
                        RemoveInlinedConstructorStores(context, instruction, constructorCall,
                            (LocalVariable)instruction.Operands[0]);
                    }
                    else
                        constructor = Analysis.AllocationConstructorRecovery.Resolve(instruction, constructor) ?? constructor;
                    constructor = ThisConstructorCallPlan.RetargetToDestinationInstantiation(constructor, allocatedDestination)
                        ?? constructor;
                    IMethodDescriptor? bareAllocationConstructor = null;
                    if (constructor.DeclaringType?.FullName == "System.Object"
                        && allocatedDestination is { IsAbstract: false, IsValueType: false } castDestination
                        && castDestination.FullName != "System.Object")
                    {
                        if (MatchingConcreteConstructor(castDestination, constructor, context) is { } concreteConstructor)
                            constructor = concreteConstructor;
                        else if (AllocatedClassOperand(context, instruction) is { } allocatedClass
                            && ThisConstructorCallPlan.SameTypeIdentity(allocatedClass, castDestination))
                            bareAllocationConstructor = EnsureBareAllocationConstructor(allocatedClass, constructor, method);
                    }
                    if (bareAllocationConstructor != null)
                    {
                        instructions.Add(CilOpCodes.Newobj, bareAllocationConstructor);
                        StoreToOperand(instruction.Operands[0], method, locals, writeLine, context);
                        constructorCall.OpCode = OpCode.Nop;
                        constructorCall.SetOperands();
                        break;
                    }
                    // The resolved .ctor can sit on an abstract declaring type when IL2CPP
                    // inlined the derived .ctor's forwarding body - the paired call then names
                    // the abstract base even though object_new was given the concrete class.
                    // newobj on an abstract type is illegal, so re-anchor to a matching .ctor
                    // on a concrete type: the class operand object_new was invoked with is the
                    // honest allocated type, then the store destination. When neither proves a
                    // concrete type the allocation cannot be reproduced honestly - emit a
                    // diagnostic and the destination's default rather than an unverifiable
                    // newobj.
                    if (constructor.DeclaringType is { IsAbstract: true })
                    {
                        var concreteCtor = (AllocatedClassOperand(context, instruction) is { IsAbstract: false } allocatedClass
                                ? MatchingConcreteConstructor(allocatedClass, constructor, context)
                                : null)
                            ?? (allocatedDestination is { IsAbstract: false } concreteDestination
                                ? MatchingConcreteConstructor(concreteDestination, constructor, context)
                                : null);
                        if (concreteCtor == null)
                        {
                            instructions.Add(CilOpCodes.Ldstr, Diagnostic(
                                $"Cannot construct abstract type {constructor.DeclaringType.FullName}: allocation's concrete type could not be recovered"));
                            instructions.Add(CilOpCodes.Call, writeLine);
                            EmitNullOrDefault(allocatedDestination, method, instructions, context);
                            StoreToOperand(instruction.Operands[0], method, locals, writeLine, context);

                            constructorCall.OpCode = OpCode.Nop;
                            constructorCall.SetOperands();
                            break;
                        }
                        constructor = concreteCtor;
                    }
                    // Operands run [ctor, newObject, arguments..., methodInfo], so take only as many as
                    // the constructor declares (i.e. drop methodInfo)
                    var constructorArgs = inlinedDefaultArgs
                        ?? constructorCall.Operands.Skip(ConstructorReceiverIndex(constructorCall) + 1)
                            .Take(constructor.Parameters.Count).ToList();

                    // A delegate .ctor verifies only against a function pointer whose
                    // signature matches the delegate's Invoke. Shared generics erase the
                    // instantiation to object arguments, so re-derive it from the ldftn
                    // target's real signature; when nothing satisfies the check, note the
                    // loss and leave a null delegate rather than an unverifiable newobj.
                    if (ResolveDelegateConstructor(constructor, constructorArgs, context,
                            out var delegateFailure) is { } delegateConstructor)
                        constructor = delegateConstructor;
                    else if (delegateFailure != null)
                    {
                        instructions.Add(CilOpCodes.Ldstr, Diagnostic(delegateFailure));
                        instructions.Add(CilOpCodes.Call, writeLine);
                        EmitNullOrDefault(allocatedDestination, method, instructions, context);
                        StoreToOperand(instruction.Operands[0], method, locals, writeLine, context);

                        constructorCall.OpCode = OpCode.Nop;
                        constructorCall.SetOperands();
                        break;
                    }

                    // A constructor on a shared-generic instantiation over a type the
                    // caller cannot see (List<System.Int32Enum>) emits a member
                    // reference the verifier rejects - same contract as a call target.
                    if (!CalleeUsableFrom(constructor, context))
                    {
                        EmitInaccessibleCalleeStub(constructor, method, writeLine);
                        constructorCall.OpCode = OpCode.Nop;
                        constructorCall.SetOperands();
                        break;
                    }

                    for (var i = 0; i < constructorArgs.Count; i++)
                        LoadOperandIntoSlot(constructorArgs[i], constructor.Parameters[i].ParameterType, context, method, locals, writeLine);

                    instructions.Add(CilOpCodes.Newobj, constructor.ToMethodDescriptor());
                    EmitStackCoerceOrDefault(constructor.DeclaringType,
                        StoreContract(instruction.Operands[0], context), method, context);
                    StoreToOperand(instruction.Operands[0], method, locals, writeLine, context);

                    constructorCall.OpCode = OpCode.Nop;
                    constructorCall.SetOperands();
                }
                else if (instruction.Operands is [_, TypeAnalysisContext allocatedType] && allocatedType.Methods.FirstOrDefault(m => m is { Name: ".ctor", Parameters.Count: 0 }) is { } parameterlessCtor)
                {
                    // Nothing to fuse with, so the allocation was self-contained. The type is still right, so construct it bare.
                    parameterlessCtor = ThisConstructorCallPlan.RetargetToDestinationInstantiation(parameterlessCtor, allocatedDestination)
                        ?? parameterlessCtor;
                    if (parameterlessCtor.DeclaringType?.FullName == "System.Object"
                        && allocatedDestination is { IsAbstract: false, IsValueType: false } concreteDestination
                        && concreteDestination.FullName != "System.Object"
                        && MatchingConcreteConstructor(concreteDestination, parameterlessCtor, context) is { } concreteConstructor)
                        parameterlessCtor = concreteConstructor;
                    // An abstract allocated type can never be constructed honestly; when a
                    // concrete destination offers the matching .ctor re-anchor to it, else
                    // emit the diagnostic and the destination's default.
                    if (parameterlessCtor.DeclaringType is { IsAbstract: true })
                    {
                        if (allocatedDestination is { IsAbstract: false } selfContainedDestination
                            && MatchingConcreteConstructor(selfContainedDestination, parameterlessCtor, context) is { } reanchored)
                            parameterlessCtor = reanchored;
                        else
                        {
                            instructions.Add(CilOpCodes.Ldstr, Diagnostic(
                                $"Cannot construct abstract type {parameterlessCtor.DeclaringType.FullName}: allocation's concrete type could not be recovered"));
                            instructions.Add(CilOpCodes.Call, writeLine);
                            EmitNullOrDefault(allocatedDestination, method, instructions, context);
                            StoreToOperand(instruction.Operands[0], method, locals, writeLine, context);
                            break;
                        }
                    }
                    if (!CalleeUsableFrom(parameterlessCtor, context))
                    {
                        EmitInaccessibleCalleeStub(parameterlessCtor, method, writeLine);
                        break;
                    }
                    instructions.Add(CilOpCodes.Newobj, parameterlessCtor.ToMethodDescriptor());
                    EmitStackCoerceOrDefault(parameterlessCtor.DeclaringType ?? allocatedType,
                        StoreContract(instruction.Operands[0], context), method, context);
                    StoreToOperand(instruction.Operands[0], method, locals, writeLine, context);
                }
                else
                {
                    EmitNullOrDefault(StoreContract(instruction.Operands[0], context), method, instructions, context);
                    StoreToOperand(instruction.Operands[0], method, locals, writeLine, context);
                }
                break;

            case OpCode.Box:
                if (instruction.Operands is [_, TypeAnalysisContext boxedType, var boxedValue])
                {
                    if (!TypeTokenUsableFrom(boxedType, context))
                    {
                        // The boxed type cannot be named here (e.g. a shared-generic
                        // instantiation over a corlib-internal marker); the honest
                        // value is a default of the slot type.
                        instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Inaccessible box type: {boxedType.FullName}"));
                        instructions.Add(CilOpCodes.Call, writeLine);
                        EmitNullOrDefault(StoreContract(instruction.Operands[0], context), method, instructions, context);
                    }
                    else
                    {
                        // il2cpp_value_box takes the value by address, but IL boxes it by value
                        LoadOperandIntoSlot(boxedValue is AddressOf { Target: LocalVariable byRef } ? byRef : boxedValue,
                            boxedType, context, method, locals, writeLine);
                        instructions.Add(CilOpCodes.Box, boxedType.ToTypeSignature().ToTypeDefOrRef());
                        var boxContract = StoreContract(instruction.Operands[0], context);
                        if (boxContract is { IsValueType: true } or ByRefTypeAnalysisContext
                            or PointerTypeAnalysisContext or GenericParameterTypeAnalysisContext)
                        {
                            instructions.Add(CilOpCodes.Pop);
                            PushDefaultOf(boxContract, method, instructions, context);
                        }
                        // `box` leaves a boxed-T reference; a slot that wants a narrower
                        // reference still needs the castclass the contract requires.
                        else if (boxContract is { IsValueType: false }
                            and not (ByRefTypeAnalysisContext or PointerTypeAnalysisContext
                                or GenericParameterTypeAnalysisContext)
                            && !IsAssignableToLoose(boxedType, boxContract) && CanEmitTypeToken(boxContract))
                        {
                            if (TypeTokenUsableFrom(boxContract, context))
                                instructions.Add(CilOpCodes.Castclass, boxContract.ToTypeSignature().ToTypeDefOrRef());
                            else
                            {
                                instructions.Add(CilOpCodes.Pop);
                                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Inaccessible cast target: {boxContract.FullName}"));
                                instructions.Add(CilOpCodes.Call, writeLine);
                                PushDefaultOf(boxContract, method, instructions, context);
                            }
                        }
                    }
                }
                else
                    EmitNullOrDefault(StoreContract(instruction.Operands[0], context), method, instructions, context);

                StoreToOperand(instruction.Operands[0], method, locals, writeLine, context);
                break;

            case OpCode.Throw:
                var exceptionCtor = instruction.Operands is [TypeAnalysisContext exceptionType]
                    ? exceptionType.Methods.FirstOrDefault(m => m.Name == ".ctor" && m.Parameters.Count == 0)
                    : null;
                if (exceptionCtor != null
                    && !CalleeUsableFrom(exceptionCtor, context))
                {
                    // Constructing the exception would name an inaccessible member; the
                    // raise is still honest - the diagnostic stub ends in throw too.
                    EmitUnrecoverableOperation(method, writeLine,
                        $"Inaccessible exception constructor: {exceptionCtor.DeclaringType?.FullName}.{exceptionCtor.Name}");
                    break;
                }
                if (exceptionCtor != null && exceptionCtor.DeclaringType is { IsAbstract: true })
                {
                    // An abstract exception type cannot be constructed honestly; fail with
                    // the diagnostic exception rather than an unverifiable newobj.
                    EmitUnrecoverableOperation(method, writeLine,
                        $"Cannot construct abstract exception type {exceptionCtor.DeclaringType?.FullName}");
                    break;
                }
                if (exceptionCtor != null)
                    instructions.Add(CilOpCodes.Newobj, exceptionCtor.ToMethodDescriptor());
                else if (instruction.Operands is [LocalVariable or FieldReference or SelectedFieldReference])
                {
                    LoadOperand(instruction.Operands[0], method, locals, writeLine, null, context); // an already-constructed exception
                    CoerceOrDefault(EmittedOperandType(instruction.Operands[0], context),
                        context.AppContext.SystemTypes.SystemExceptionType, method, context);
                }
                else
                    instructions.Add(CilOpCodes.Ldnull);

                instructions.Add(CilOpCodes.Throw);
                break;

            case OpCode.Phi:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Phi opcodes should not exist at this point in decompilation ({instruction})"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;

            case OpCode.Call:
            case OpCode.CallVoid:
                var retargetedBaseConstructor = thisConstructorCalls is not null
                    && thisConstructorCalls.Retarget.TryGetValue(instruction, out var retargeted)
                        ? retargeted
                        : null;

                if (instruction.Operands[0] is not MethodAnalysisContext targetMethod)
                {
                    // An unresolved call on `this` inside a .ctor can be the lost
                    // base-init call; ThisConstructorCallPlan re-anchors those to
                    // the recovered .ctor instead of the usual diagnostic stub.
                    if (retargetedBaseConstructor == null)
                    {
                        if (instruction.Operands[0] is Immediate targetAddress)
                            instructions.Add(CilOpCodes.Ldstr, $"Method not found @{targetAddress.UnsignedValue:X}");
                        else // Probably key function. Just the target, the full operand dump is huge and blows the 16MB #US heap limit
                            instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Unknown call target operand: {instruction.Operands[0]}"));

                        instructions.Add(CilOpCodes.Call, writeLine);
                        break;
                    }
                    targetMethod = retargetedBaseConstructor;
                }

                if (Analysis.StringConstructorRecovery.Resolve(instruction, targetMethod) is { } stringConstructor)
                {
                    if (!CalleeUsableFrom(stringConstructor, context))
                    {
                        EmitInaccessibleCalleeStub(stringConstructor, method, writeLine);
                        break;
                    }
                    var firstArgument = instruction.OpCode == OpCode.Call ? 3 : 2;
                    for (var i = 0; i < stringConstructor.Parameters.Count; i++)
                        LoadOperandIntoSlot(instruction.Operands[firstArgument + i], stringConstructor.Parameters[i].ParameterType, context, method, locals, writeLine);
                    instructions.Add(CilOpCodes.Newobj, stringConstructor.ToMethodDescriptor());
                    if (instruction.OpCode == OpCode.Call)
                    {
                        CoerceOrDefault(stringConstructor.DeclaringType,
                            StoreContract(instruction.Operands[1], context),
                            method, context);
                        StoreToOperand(instruction.Operands[1], method, locals, writeLine, context);
                    }
                    else
                        instructions.Add(CilOpCodes.Pop);
                    break;
                }

                if (retargetedBaseConstructor != null)
                    targetMethod = retargetedBaseConstructor;

                var thisParamIndex = instruction.OpCode == OpCode.Call ? 2 : 1;

                // Shared generics erase T to object at the call site, so the resolved callee
                // can sit on List<object> while the receiver operand emits as List<T>; when
                // both share the generic definition, the honest callee is the receiver's
                // instantiation (which is what the native code actually invoked).
                if (!targetMethod.IsStatic && instruction.Operands.Count - 1 >= thisParamIndex)
                    targetMethod = ThisConstructorCallPlan.RetargetToDestinationInstantiation(targetMethod,
                            SharedGenericEvidenceType(instruction.Operands[thisParamIndex], context))
                        ?? targetMethod;

                // The rest of the shared-generic erasure is recovered the same
                // way: the callee's open signature is matched against the types
                // the receiver, parameter and result operands actually emit, so
                // `PersistentMap<object,object>::op_Inequality` fed by a
                // PersistentMap<string,AssetObject> local and a `T Get()` stored
                // into a Dictionary both name the instantiation the native code
                // ran with.
                targetMethod = SolveSharedGenericArguments(targetMethod, instruction, context, thisParamIndex)
                    ?? targetMethod;

                if (TryEmitUnityQuaternionInternal(instruction, targetMethod, context, method, locals, writeLine))
                    break;

                // IL2CPP leaves direct calls to corlib members managed code could never name: the
                // internal slow paths of inlined BCL operations (List<T>.AddWithResize, private
                // Math.ThrowMinMaxException) or shared-generic instantiations over non-public
                // marker types. Swap in the honest public equivalent when one exists; otherwise
                // leave a diagnostic stub rather than a reference the verifier rejects. The check
                // runs after every retarget: the receiver's own instantiation is what the emitted
                // member reference actually names.
                if (!CalleeUsableFrom(targetMethod, context)
                    || !Analysis.InaccessibleCalleeRecovery.SatisfiesDeclaredConstraints(targetMethod))
                {
                    if (Analysis.InaccessibleCalleeRecovery.TrySubstitute(targetMethod) is { } accessibleCallee
                        && CalleeUsableFrom(accessibleCallee, context)
                        && Analysis.InaccessibleCalleeRecovery.SatisfiesDeclaredConstraints(accessibleCallee))
                        targetMethod = accessibleCallee;
                    else
                    {
                        EmitInaccessibleCalleeStub(targetMethod, method, writeLine);
                        break;
                    }
                }

                var importedMethod = targetMethod.ToMethodDescriptor();

                // A `call` to a reference-type .ctor on anything but `this` inside a .ctor
                // is IL2CPP's re-init of an allocated object; emit newobj and store the fresh
                // object back into the receiver slot instead.
                IOperand? ctorReinitReceiver = null;
                // A .ctor call lifted without any receiver operand cannot be a `call`
                // either; it degrades to a bare newobj whose result is dropped.
                var ctorNoReceiver = false;
                // A struct's instance `this` is a managed pointer to that struct -
                // `call StructType::.ctor` initializes through it in place too.
                var structCallee = !targetMethod.IsStatic && targetMethod.DeclaringType is { IsValueType: true } structDeclaring
                    ? structDeclaring
                    : null;
                var isOwnThis = false;
                if (!targetMethod.IsStatic) // Load 'this' param
                {
                    var referenceTypeConstructor = targetMethod.Name == ".ctor"
                        && retargetedBaseConstructor == null && structCallee == null;
                    if ((instruction.Operands.Count - 1) >= thisParamIndex)
                    {
                        var thisOperand = instruction.Operands[thisParamIndex];
                        var receiverType = EmittedOperandType(thisOperand, context, targetMethod.DeclaringType);
                        if (targetMethod.Name != ".ctor" && !context.IsStatic
                            && context.DeclaringType != null && targetMethod.DeclaringType != null
                            && LooseAssignable(context.DeclaringType, targetMethod.DeclaringType)
                            && (receiverType == null || !StackAssignableTo(receiverType, targetMethod.DeclaringType))
                            && context.ParameterLocals.FirstOrDefault(local => local.IsThis) is { } actualThis)
                            thisOperand = actualThis;
                        isOwnThis = !context.IsStatic && thisOperand is LocalVariable thisLocal
                            && (thisLocal.IsThis || ReferenceEquals(thisLocal, context.ParameterLocals.FirstOrDefault()));
                        // Outside a .ctor there is no `this`-initialization exemption,
                        // so a .ctor call even on the caller's own `this` is a re-init
                        // of an allocated object and takes the newobj+store path too.
                        if (referenceTypeConstructor
                            && !(isOwnThis && context is { IsStatic: false, Name: ".ctor" }))
                            ctorReinitReceiver = thisOperand;

                        // A struct's instance `this` is a managed pointer: when the receiver
                        // is a local of exactly that struct type (a foreach enumerator is the
                        // common case) its address is the honest receiver. Mismatched or
                        // non-addressable operands keep the old value+coerce path.
                        var receiverCilLocal = thisOperand is LocalVariable receiverLocal
                            && locals.TryGetValue(receiverLocal, out var foundReceiver)
                                ? foundReceiver
                                : null;
                        if (ctorReinitReceiver == null && !isOwnThis && structCallee != null && receiverCilLocal != null
                            && thisOperand is LocalVariable typedReceiverLocal
                            && ThisConstructorCallPlan.SameTypeIdentity(EmittedLocalType(typedReceiverLocal, context), structCallee))
                            instructions.Add(CilOpCodes.Ldloca, receiverCilLocal);
                        else if (ctorReinitReceiver == null && !isOwnThis && structCallee != null
                            && !ReceiverEmitsStructAddress(thisOperand, context, structCallee))
                        {
                            // Catch/finally register reuse can leave a lost or mistyped
                            // operand in the receiver slot (an exception object, the loop
                            // boolean, a dropped constant); none of them can form `&T`.
                            // The unique local of the struct type is the slot the native
                            // code used; a fresh default local is the honest fallback.
                            if (!EmitFallbackStructReceiver(structCallee, context, method, locals))
                                LoadOperand(thisOperand, method, locals, writeLine, targetMethod.DeclaringType, context);
                        }
                        else if (ctorReinitReceiver == null)
                        {
                            var thisTarget = structCallee != null
                                ? new ByRefTypeAnalysisContext(structCallee)
                                : targetMethod.DeclaringType;
                            // The receiver's stack type under its own contract: a zero
                            // literal emits ldnull (the contract type itself), a nonzero
                            // one keeps its natural width for the coerce below.
                            var thisEmitted = EmittedOperandType(thisOperand, context, thisTarget);
                            if (isOwnThis && thisEmitted != null && thisTarget != null
                                && !StackAssignableTo(thisEmitted, thisTarget)
                                && TryEmitThisFieldReceiver(context, thisTarget, method))
                            {
                                // `this` cannot be the callee's receiver, but the compiler's
                                // own escape applies: a state machine or display class reaches
                                // its enclosing instance through <>4__this (or another field
                                // typed for the contract), which is what the native code passed.
                            }
                            else
                            {
                                LoadOperand(thisOperand, method, locals, writeLine, targetMethod.DeclaringType, context);
                                // A struct's instance `this` is a managed pointer, not the value —
                                // coerce toward `&T` (which no stack op can forge) so a ldloca
                                // receiver is left alone instead of being unboxed. The method's own
                                // `this` must stay a bare ldarg.0 when it already satisfies the
                                // callee - only a provable contract mismatch earns a coercion.
                                if ((!isOwnThis && (targetMethod.Name is not ".ctor" || structCallee != null))
                                    || (isOwnThis && thisEmitted != null && thisTarget != null
                                        && !StackAssignableTo(thisEmitted, thisTarget)))
                                {
                                    // An unmanaged pointer is not a legal receiver: T* is
                                    // a native int to the verifier, never the &T or object
                                    // reference `this` needs, and no conversion forges a
                                    // managed pointer from a raw address. Drop it and offer
                                    // the honest fallback - the unique local of the struct
                                    // type, or a fresh default &T.
                                    if (thisEmitted is PointerTypeAnalysisContext)
                                    {
                                        instructions.Add(CilOpCodes.Pop);
                                        if (structCallee == null
                                            || !EmitFallbackStructReceiver(structCallee, context, method, locals))
                                            PushDefaultOf(thisTarget, method, instructions, context);
                                    }
                                    else
                                        CoerceOrDefault(thisEmitted, thisTarget, method, context);
                                }
                            }
                        }
                    }
                    else
                    {
                        instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Non static method called without 'this' param ({instruction})"));
                        instructions.Add(CilOpCodes.Call, writeLine);
                        if (referenceTypeConstructor)
                            ctorNoReceiver = true;
                        else if (structCallee == null || !EmitFallbackStructReceiver(structCallee, context, method, locals))
                            instructions.Add(CilOpCodes.Ldnull);
                    }
                }

                // A re-init `call` to a .ctor on an abstract declaring type is emitted as
                // `newobj` below, but IL2CPP leaves the inlined derived .ctor's base-init
                // naming the abstract base - that newobj cannot verify. Re-anchor to a
                // matching .ctor on the receiver's concrete type before any argument is
                // pushed; when none is provable emit the diagnostic and the defaults.
                if (ctorReinitReceiver != null && targetMethod.DeclaringType is { IsAbstract: true })
                {
                    if (EmittedOperandType(ctorReinitReceiver, context) is { IsAbstract: false } concreteReceiver
                        && MatchingConcreteConstructor(concreteReceiver, targetMethod, context) is { } reanchoredCtor)
                    {
                        targetMethod = reanchoredCtor;
                        importedMethod = targetMethod.ToMethodDescriptor();
                    }
                    else
                    {
                        instructions.Add(CilOpCodes.Ldstr, Diagnostic(
                            $"Cannot construct abstract type {targetMethod.DeclaringType.FullName}: receiver's concrete type could not be recovered"));
                        instructions.Add(CilOpCodes.Call, writeLine);
                        EmitNullOrDefault(StoreContract(ctorReinitReceiver, context), method, instructions, context);
                        StoreToOperand(ctorReinitReceiver, method, locals, writeLine, context);
                        if (instruction.OpCode == OpCode.Call)
                        {
                            EmitNullOrDefault(StoreContract(instruction.Operands[1], context), method, instructions, context);
                            StoreToOperand(instruction.Operands[1], method, locals, writeLine, context);
                        }
                        break;
                    }
                }

                // Load normal params
                var callParamIndex = instruction.OpCode == OpCode.Call ? (targetMethod.IsStatic ? 2 : 3) : (targetMethod.IsStatic ? 1 : 2);

                // A `call` to a delegate .ctor lowers to `newobj` below, so the
                // function-pointer requirement from the fused allocation path
                // applies here too; without a resolvable ldftn target the
                // honest result is a diagnostic and a null delegate.
                if (ctorReinitReceiver != null || ctorNoReceiver)
                {
                    var callCtorArgs = instruction.Operands.Skip(callParamIndex)
                        .Take(targetMethod.Parameters.Count).ToList();
                    if (ResolveDelegateConstructor(targetMethod, callCtorArgs, context,
                            out var callDelegateFailure) is { } callDelegateCtor)
                    {
                        targetMethod = callDelegateCtor;
                        importedMethod = targetMethod.ToMethodDescriptor();
                    }
                    else if (callDelegateFailure != null)
                    {
                        instructions.Add(CilOpCodes.Ldstr, Diagnostic(callDelegateFailure));
                        instructions.Add(CilOpCodes.Call, writeLine);
                        if (ctorReinitReceiver != null)
                        {
                            EmitNullOrDefault(StoreContract(ctorReinitReceiver, context), method, instructions, context);
                            StoreToOperand(ctorReinitReceiver, method, locals, writeLine, context);
                        }
                        if (instruction.OpCode == OpCode.Call)
                        {
                            EmitNullOrDefault(StoreContract(instruction.Operands[1], context), method, instructions, context);
                            StoreToOperand(instruction.Operands[1], method, locals, writeLine, context);
                        }
                        break;
                    }
                }

                // A call whose target was only identified after lifting still carries the operands the
                // unknown-callee convention gave it, which may be fewer than the method actually takes.
                // The stack still has to match the signature, so anything missing gets a placeholder.
                var availableArgs = instruction.Operands.Count - callParamIndex;
                for (var i = 0; i < targetMethod.Parameters.Count; i++)
                {
                    var parameterType = targetMethod.Parameters[i].ParameterType;

                    if (i < availableArgs)
                    {
                        var argumentOperand = instruction.Operands[callParamIndex + i];
                        var operandFeedsParameter = argumentOperand switch
                        {
                            RuntimeMethodInfoAnalysisContext => parameterType.FullName
                                is "System.RuntimeMethodHandle" or "System.IntPtr" or "System.UIntPtr",
                            RuntimeFieldInfoAnalysisContext => parameterType.FullName
                                is "System.RuntimeFieldHandle" or "System.IntPtr" or "System.UIntPtr",
                            RuntimeClassTypeAnalysisContext => parameterType.FullName
                                is "System.RuntimeTypeHandle" or "System.Type" or "System.Object"
                                    or "System.IntPtr" or "System.UIntPtr",
                            RgctxTableTypeAnalysisContext or MethodRgctxTableTypeAnalysisContext
                                or StaticFieldStorageTypeAnalysisContext => parameterType.FullName
                                is "System.IntPtr" or "System.UIntPtr",
                            _ => true,
                        };
                        if (!operandFeedsParameter)
                        {
                            // A hidden shared-generic argument (MethodInfo*/klass*/rgctx) landed in a
                            // real parameter slot; the actual argument was dropped upstream. Stub the
                            // slot rather than emit a wrongly-typed placeholder.
                            PushDefaultOf(parameterType, method, instructions, context);
                        }
                        else
                            LoadOperandIntoSlot(argumentOperand, parameterType, context, method, locals, writeLine);
                    }
                    else
                        PushDefaultOf(parameterType, method, instructions, context);
                }

                if (ctorReinitReceiver != null)
                {
                    instructions.Add(CilOpCodes.Newobj, importedMethod);
                    if (instruction.OpCode == OpCode.Call)
                        instructions.Add(CilOpCodes.Dup); // the constructed object is also the call result
                    EmitStackCoerceOrDefault(targetMethod.DeclaringType,
                        StoreContract(ctorReinitReceiver, context), method, context);
                    StoreToOperand(ctorReinitReceiver, method, locals, writeLine, context);
                    if (instruction.OpCode == OpCode.Call)
                    {
                        CoerceOrDefault(targetMethod.DeclaringType,
                            StoreContract(instruction.Operands[1], context), method, context);
                        StoreToOperand(instruction.Operands[1], method, locals, writeLine, context);
                    }
                    break;
                }

                if (ctorNoReceiver)
                {
                    instructions.Add(CilOpCodes.Newobj, importedMethod);
                    if (instruction.OpCode == OpCode.Call && instruction.Operands.Count > 1)
                    {
                        CoerceOrDefault(targetMethod.DeclaringType,
                            StoreContract(instruction.Operands[1], context), method, context);
                        StoreToOperand(instruction.Operands[1], method, locals, writeLine, context);
                    }
                    else
                        instructions.Add(CilOpCodes.Pop);
                    break;
                }
                // ECMA III.3.19: a `call` to a non-final virtual method on a non-sealed
                // reference type only verifies on the caller's own `this` pointer (or a
                // boxed value type). IL2CPP resolves virtual dispatches it can prove into
                // direct calls on ordinary locals/fields, and Enum::ToString-style callee
                // recovery lands on a virtual member of a reference type; the verifiable
                // spelling of those calls is `callvirt`, which also matches the slot
                // dispatch the native code actually performed. A receiver that is the
                // caller's own `this` keeps `call` so base calls stay non-virtual.
                var directCallToVirtual = !targetMethod.IsStatic && retargetedBaseConstructor == null
                    && structCallee == null
                    && targetMethod.IsVirtual && !targetMethod.IsFinal
                    && targetMethod.DeclaringType is { IsSealed: false }
                    && !isOwnThis;
                instructions.Add(!targetMethod.IsStatic && retargetedBaseConstructor == null
                        && structCallee == null
                        && (instruction.IsVirtualDispatch || targetMethod.DeclaringType?.IsInterface == true
                            || directCallToVirtual)
                    ? CilOpCodes.Callvirt
                    : CilOpCodes.Call, importedMethod);

                // the lifter's guess at whether the callee returns anything can disagree with the
                // signature we later resolved, so go by the signature and balance the stack
                if (!targetMethod.IsVoid)
                {
                    if (instruction.OpCode == OpCode.Call)
                    {
                        var resultContract = StoreContract(instruction.Operands[1], context);
                        // The member reference, not a possibly stale analysis override,
                        // determines the value the CIL call leaves on the stack.
                        // A value-type result stored in object must be boxed even when
                        // analysis mislabeled the call as returning object.
                        if (instruction.Operands[1] is LocalVariable resultLocal
                            && locals[resultLocal].VariableType.FullName == "System.Object"
                            && importedMethod.Signature?.ReturnType is { IsValueType: true } actualReturn)
                            instructions.Add(CilOpCodes.Box, actualReturn.ToTypeDefOrRef());
                        else
                            EmitStackCoerceOrDefault(EffectiveCallReturnType(targetMethod),
                                resultContract, method, context);
                        StoreToOperand(instruction.Operands[1], method, locals, writeLine, context);
                    }
                    else
                        instructions.Add(CilOpCodes.Pop);
                }

                break;

            case OpCode.IndirectCall:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Indirect call: {instruction.Operands[0]} (should have been resolved before IL gen)"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;

            case OpCode.Return:
                if (instruction.Operands is [var returnedException]
                    && IsExceptionValueReturnedFromIncompatibleMethod(context, returnedException))
                {
                    // IL2CPP exception helpers can leave a constructed exception in the native
                    // return register after the raise edge was lost. Never emit `ret exception`
                    // for a method whose managed result cannot hold it.
                    LoadOperand(returnedException, method, locals, writeLine, null, context);
                    instructions.Add(CilOpCodes.Throw);
                    break;
                }

                if (!context.IsVoid)
                {
                    if (instruction.Operands.Count == 1)
                        LoadOperandIntoSlot(instruction.Operands[0], context.ReturnType, context, method, locals, writeLine);
                    else
                        EmitNullOrDefault(context.ReturnType, method, instructions, context); // ret still pops a value even if we lost track of it
                }
                instructions.Add(CilOpCodes.Ret);
                break;

            case OpCode.Jump:
                instructions.Add(CilOpCodes.Br, new CilInstructionLabel());
                break;

            case OpCode.ConditionalJump:
                var conditionType = EmittedOperandType(instruction.Operands[1], context);
                LoadOperand(instruction.Operands[1], method, locals, writeLine, null, context);
                // brtrue won't pop an i64; the native branch tested the full register
                // for non-zero, which is exactly `x > 0` unsigned.
                if (IntegralStackWidth(conditionType) == 8)
                {
                    instructions.Add(CilOpCodes.Ldc_I8, 0L);
                    instructions.Add(CilOpCodes.Cgt_Un);
                }
                else if (conditionType is { IsValueType: true } && IntegralStackWidth(conditionType) == 0)
                {
                    // brtrue cannot test a non-integral value type (or a float); the
                    // condition is unrecoverable, so default it to false rather than
                    // leave a struct on the stack.
                    instructions.Add(CilOpCodes.Pop);
                    instructions.Add(CilOpCodes.Ldc_I4_0);
                }
                instructions.Add(CilOpCodes.Brtrue, new CilInstructionLabel());
                break;

            case OpCode.IndirectJump:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Indirect jump: {instruction.Operands[0]} (should have been resolved before IL gen)"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;

            case OpCode.ShiftStack:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Stack shift: {instruction} (stack analysis should have removed these)"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;

            case OpCode.VectorMin:
            case OpCode.VectorMax:
                if (!TryEmitUnityVectorMinMax(instruction, context, method, locals, writeLine))
                    EmitUnrecoverableOperation(method, writeLine, $"Unrecoverable vector min/max: {instruction}");
                break;

            case OpCode.MemoryCopy:
            case OpCode.MemorySet:
            case OpCode.MemoryMove:
                EmitBlockMemoryOperation(instruction, context, method, locals, writeLine);
                break;

            case OpCode.CheckEqual:
            case OpCode.CheckGreater:
            case OpCode.CheckLess:
            case OpCode.CheckNotEqual:
            case OpCode.CheckGreaterOrEqual:
            case OpCode.CheckLessOrEqual:

            case OpCode.Add:
            case OpCode.Subtract:
            case OpCode.Multiply:
            case OpCode.Divide:
            case OpCode.Modulo:

            case OpCode.ShiftLeft:
            case OpCode.ShiftRight:

            case OpCode.And:
            case OpCode.Or:
            case OpCode.Xor:
                // klass pointer read => GetType
                if (instruction.OpCode is OpCode.CheckEqual or OpCode.CheckNotEqual
                    && TryEmitExactTypeComparison(instruction, method, locals, writeLine, context))
                    break;

                if (TryEmitUnityVectorOperation(instruction, context, method, locals, writeLine))
                    break;

                // Integer ops on operands that cannot legally sit in an integer slot are
                // native idioms the lifter mistyped: `&slot | N`/`&slot + N` names a field
                // inside a struct local, `packed >> 32`/`packed & mask` selects a field out
                // of a value lifted as one unit, and `x ^ x`/`x - x` folds to zero for any
                // operand kind. Recover the managed equivalent when layout allows it.
                if (TryEmitRecoveredIntegerOperation(instruction, context, method, locals, writeLine))
                    break;

                var isComparison = instruction.OpCode is >= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual;

                // Float operations on a promoted integer operand need an explicit conversion, so both
                // operands are coerced to the (float) result type. A no-op when they already match.
                var floatConversion = FloatOperationConversion(instruction);

                // `&T`/`ref T` + N is field addressing, not arithmetic: the native
                // add computes the address of the field at byte offset N. Emit the
                // field access itself instead of invalid pointer math.
                if (instruction.OpCode is OpCode.Add or OpCode.Subtract
                    && TryResolveFieldAddressArithmetic(instruction, context) is { } fieldAddress
                    && FieldUsableFrom(fieldAddress.Field, context, writeAccess: true)
                    // The member reference names the owner instantiation, whose type
                    // arguments the field's own declaration does not carry.
                    && (context.DeclaringType == null
                        || Analysis.InaccessibleCalleeRecovery.IsVisibleType(fieldAddress.Owner, context.DeclaringType)))
                {
                    if (!fieldAddress.Field.IsStatic)
                        LoadOperand(fieldAddress.Base, method, locals, writeLine, null, context);
                    // Fields found on a generic instance's definition must be
                    // referenced on the instantiation, or the verifier sees an
                    // instance type mismatch against the base operand.
                    var fieldGit = GenericFieldOwnerInstance(fieldAddress.Owner, fieldAddress.Field);
                    var resolvedField = fieldAddress.Field is ConcreteGenericFieldAnalysisContext
                        ? fieldAddress.Field
                        : fieldGit != null
                        ? new ConcreteGenericFieldAnalysisContext(fieldAddress.Field, fieldGit)
                        : fieldAddress.Field;
                    var fieldContract = StoreContract(instruction.Operands[0], context);
                    TypeAnalysisContext? fieldResult;
                    if (fieldContract is ByRefTypeAnalysisContext fieldByRef
                        && fieldByRef.ElementType.FullName == resolvedField.FieldType.FullName)
                    {
                        instructions.Add(resolvedField.IsStatic ? CilOpCodes.Ldsflda : CilOpCodes.Ldflda,
                            resolvedField.ToFieldDescriptor());
                        fieldResult = fieldContract;
                    }
                    else if (fieldContract == null
                        || StackContractSatisfied(resolvedField.FieldType, fieldContract, context))
                    {
                        instructions.Add(resolvedField.IsStatic ? CilOpCodes.Ldsfld : CilOpCodes.Ldfld,
                            resolvedField.ToFieldDescriptor());
                        fieldResult = resolvedField.FieldType;
                    }
                    else
                    {
                        // `base+offset` computes the field's address; a contract that can
                        // hold neither &F nor F itself (an object slot for a pointer
                        // field) has no honest value. The base operand is already on
                        // the stack, so drop it before the default.
                        if (!resolvedField.IsStatic)
                            instructions.Add(CilOpCodes.Pop);
                        instructions.Add(CilOpCodes.Ldstr,
                            Diagnostic($"Unrepresentable field address: {resolvedField}"));
                        instructions.Add(CilOpCodes.Call, writeLine);
                        PushDefaultOf(fieldContract, method, instructions, context);
                        StoreToOperand(instruction.Operands[0], method, locals, writeLine, context);
                        break;
                    }
                    CoerceOrDefault(fieldResult, fieldContract, method, context);
                    StoreToOperand(instruction.Operands[0], method, locals, writeLine, context);
                    break;
                }

                // Integer operations share a single stack type: the widest non-literal operand,
                // or (for value-producing ops) the destination. Comparison destinations are the
                // bool result, not the compared type, so they never seed the operand type. A float
                // conversion supplies the shared contract itself.
                var operandType = floatConversion == null
                    ? BinaryOperandType(instruction, context, !isComparison)
                    : floatConversion == CilOpCodes.Conv_R4
                        ? context.AppContext.SystemTypes.SystemSingleType
                        : context.AppContext.SystemTypes.SystemDoubleType;

                // No operand claimed an integer width (e.g. two references or a struct
                // reaching a bitwise op): the slot still has to be an integer, so coerce
                // to i4 and let the slot loader produce unbox/placeholder as needed.
                if (operandType == null && floatConversion == null && !isComparison)
                    operandType = context.AppContext.SystemTypes.SystemInt32Type;

                // shl/shr take an i32/n-int shift amount, not the value type.
                var operand2Type = instruction.OpCode is OpCode.ShiftLeft or OpCode.ShiftRight
                    ? context.AppContext.SystemTypes.SystemInt32Type
                    : operandType;

                // Numeric inference can sharpen an object-typed analysis local to a
                // floating CIL local. The locals table is the verifier's authority;
                // if either compared slot is declared float, load both sides at that
                // width (notably `0 > recoveredDouble`).
                if (isComparison)
                {
                    var declaredFloat = instruction.Operands.Skip(1).Take(2)
                        .OfType<LocalVariable>()
                        .Select(local => locals.TryGetValue(local, out var emitted)
                            ? emitted.VariableType.FullName : null)
                        .FirstOrDefault(name => name is "System.Single" or "System.Double");
                    if (declaredFloat != null)
                    {
                        operandType = declaredFloat == "System.Double"
                            ? context.AppContext.SystemTypes.SystemDoubleType
                            : context.AppContext.SystemTypes.SystemSingleType;
                        operand2Type = operandType;
                    }
                }

                // Bitwise/shift ops are integer-only in IL. An operand that provably emits
                // a non-integer (float, struct or concrete reference — unlike an untyped
                // object local which may still hold a boxed int) makes the operation
                // unrecoverable; emit an honest diagnostic instead of invalid IL.
                var unrecoverableIntegerOperation = instruction.OpCode
                    is OpCode.ShiftLeft or OpCode.ShiftRight or OpCode.And or OpCode.Or or OpCode.Xor
                    && instruction.Operands.Skip(1).Any(operand =>
                        EmittedOperandType(operand, context, operandType) is { } operandEmitted
                        && IntegralStackWidth(operandEmitted) == 0
                        && (operandEmitted.IsValueType || operandEmitted.FullName != "System.Object"));

                // A managed pointer cannot participate in any binary op (ILVerify
                // rejects `&` in add/sub entirely): the contract stays the shared
                // numeric type and EmitStackCoerce dereferences `&` to it with the
                // matching ldind width. Pointer arithmetic that names a field is
                // recovered earlier by the address resolver.
                var contract1 = NullComparisonType(instruction, 1, context) ?? operandType;
                var contract2 = NullComparisonType(instruction, 2, context) ?? operand2Type;

                // The stack types after loading under the contract - a missing contract
                // leaves the operand's natural emission.
                var stack1 = contract1 ?? NaturalEmittedType(instruction.Operands[1], context);
                var stack2 = contract2 ?? NaturalEmittedType(instruction.Operands[2], context);
                var emitted1 = EmittedOperandType(instruction.Operands[1], context, contract1);
                var emitted2 = EmittedOperandType(instruction.Operands[2], context, contract2);
                var operandsUsable = isComparison
                    ? OperandsShareComparableKind(instruction.OpCode, stack1, stack2)
                    : NumericStackKind(instruction.OpCode, stack1) && NumericStackKind(instruction.OpCode, stack2)
                        && !(instruction.OpCode == OpCode.Add
                            && stack1 is ByRefTypeAnalysisContext && stack2 is ByRefTypeAnalysisContext);
                if (unrecoverableIntegerOperation
                    || !StackContractSatisfied(emitted1, contract1, context, isComparison)
                    || !StackContractSatisfied(emitted2, contract2, context, isComparison)
                    || !operandsUsable)
                {
                    if (unrecoverableIntegerOperation)
                        EmitUnrecoverableOperation(method, writeLine, $"Unrecoverable integer operation: {instruction}");
                    // No shared stack kind exists for this operation (e.g. a Vector3
                    // tested against an int, or a struct fed to add). Equality still
                    // has honest answers - a shared native-int lowering covers
                    // integral/pointer operands, and a zero literal on a managed or
                    // generic operand is the null test - while ordering and
                    // arithmetic have none, so they default to false/zero.
                    else if (instruction.OpCode is not (OpCode.CheckEqual or OpCode.CheckNotEqual)
                        || !(TryEmitNativeIntEquality(instruction, context, method, locals, writeLine)
                            || TryEmitReferenceEquality(instruction, context, method, locals, writeLine)))
                        EmitUnrecoverableOperation(method, writeLine, $"Unrecoverable operation: {instruction}");
                    EmitStackCoerceOrDefault(context.AppContext.SystemTypes.SystemInt32Type,
                        StoreContract(instruction.Operands[0], context), method, context);
                    StoreToOperand(instruction.Operands[0], method, locals, writeLine, context);
                    break;
                }

                LoadOperandIntoSlot(instruction.Operands[1], contract1, context, method, locals, writeLine, isComparison);
                LoadOperandIntoSlot(instruction.Operands[2], contract2, context, method, locals, writeLine, isComparison);

                switch (instruction.OpCode)
                {
                    case OpCode.CheckEqual: instructions.Add(CilOpCodes.Ceq); break;
                    case OpCode.CheckGreater: instructions.Add(CilOpCodes.Cgt); break;
                    case OpCode.CheckLess: instructions.Add(CilOpCodes.Clt); break;

                    // a != b  ==  (a == b) == 0
                    case OpCode.CheckNotEqual:
                        instructions.Add(CilOpCodes.Ceq);
                        instructions.Add(CilOpCodes.Ldc_I4_0);
                        instructions.Add(CilOpCodes.Ceq);
                        break;
                    // a >= b  ==  !(a < b)
                    case OpCode.CheckGreaterOrEqual:
                        instructions.Add(CilOpCodes.Clt);
                        instructions.Add(CilOpCodes.Ldc_I4_0);
                        instructions.Add(CilOpCodes.Ceq);
                        break;
                    // a <= b  ==  !(a > b)
                    case OpCode.CheckLessOrEqual:
                        instructions.Add(CilOpCodes.Cgt);
                        instructions.Add(CilOpCodes.Ldc_I4_0);
                        instructions.Add(CilOpCodes.Ceq);
                        break;

                    case OpCode.Add: instructions.Add(CilOpCodes.Add); break;
                    case OpCode.Subtract: instructions.Add(CilOpCodes.Sub); break;
                    case OpCode.Multiply: instructions.Add(CilOpCodes.Mul); break;
                    case OpCode.Divide: instructions.Add(CilOpCodes.Div); break;
                    case OpCode.Modulo: instructions.Add(CilOpCodes.Rem); break;

                    case OpCode.ShiftLeft: instructions.Add(CilOpCodes.Shl); break;
                    case OpCode.ShiftRight: instructions.Add(CilOpCodes.Shr); break;
                    case OpCode.And: instructions.Add(CilOpCodes.And); break;
                    case OpCode.Or: instructions.Add(CilOpCodes.Or); break;
                    case OpCode.Xor: instructions.Add(CilOpCodes.Xor); break;
                }

                var resultType = isComparison
                    ? context.AppContext.SystemTypes.SystemInt32Type
                    : stack1 is ByRefTypeAnalysisContext resultByRef
                            && instruction.OpCode is OpCode.Add or OpCode.Subtract
                        ? stack2 is ByRefTypeAnalysisContext
                            ? context.AppContext.SystemTypes.SystemIntPtrType // &-& is a native int
                            : resultByRef // & +/- i keeps the managed pointer
                        : operandType ?? EmittedOperandType(instruction.Operands[1], context);
                EmitStackCoerceOrDefault(resultType, StoreContract(instruction.Operands[0], context), method, context, true);
                StoreToOperand(instruction.Operands[0], method, locals, writeLine, context);
                break;

            case OpCode.Not:
            case OpCode.Negate:
            {
                if (TryEmitUnityVectorOperation(instruction, context, method, locals, writeLine))
                    break;
                // `mvn` on `fmov` bits is the same reinterpretation idiom as the
                // binary bitwise ops.
                if (instruction.OpCode == OpCode.Not
                    && TryEmitFloatCarrierIntegerOperation(instruction, context, method, locals, writeLine))
                    break;
                var unaryOperandType = EmittedOperandType(instruction.Operands[1], context);
                if (unaryOperandType is PointerTypeAnalysisContext)
                {
                    // `not`/`neg` on a raw pointer: the pointer is lost, keep the
                    // operation on a native-int placeholder instead of an invalid `*`.
                    instructions.Add(CilOpCodes.Ldc_I4_0);
                    instructions.Add(CilOpCodes.Conv_I);
                }
                else
                {
                    LoadOperand(instruction.Operands[1], method, locals, writeLine, null, context);
                    // `not`/`neg` on `&x` really means the pointed value; the coerce
                    // dereferences an integral element or drops a lost one for zero.
                    if (unaryOperandType is ByRefTypeAnalysisContext)
                        EmitStackCoerce(unaryOperandType, context.AppContext.SystemTypes.SystemIntPtrType, method, context);
                }

                var unaryResultType = unaryOperandType is ByRefTypeAnalysisContext or PointerTypeAnalysisContext
                    ? context.AppContext.SystemTypes.SystemIntPtrType
                    : unaryOperandType;
                // The operand kinds the operation can honestly consume: integral
                // kinds for either op, floats for neg, and managed pointers already
                // lowered to native int above. Structs, generic parameters and
                // reference operands have no decode - neg on them is unrecoverable.
                var unaryOperandUsable = unaryOperandType == null
                    || unaryOperandType is ByRefTypeAnalysisContext or PointerTypeAnalysisContext
                    || IntegralStackWidth(unaryOperandType) != 0
                    || instruction.OpCode == OpCode.Negate
                        && unaryOperandType.FullName is "System.Single" or "System.Double";

                if (instruction.OpCode == OpCode.Negate)
                {
                    if (unaryOperandUsable)
                        instructions.Add(CilOpCodes.Neg);
                    else
                        EmitUnrecoverableOperation(method, writeLine, $"Unrecoverable integer operation: {instruction}");
                }
                else if (unaryOperandType is { IsValueType: false }
                    and not (ByRefTypeAnalysisContext or PointerTypeAnalysisContext
                        or GenericParameterTypeAnalysisContext)
                    && !IsNativeHandleType(unaryOperandType))
                {
                    // `!x` on a reference is a null test; there is no bitwise-not of an object.
                    instructions.Add(CilOpCodes.Ldnull);
                    instructions.Add(CilOpCodes.Ceq);
                    unaryResultType = context.AppContext.SystemTypes.SystemInt32Type;
                }
                else if (IsBoolean(instruction.Operands[1], context))
                {
                    instructions.Add(CilOpCodes.Ldc_I4_0);
                    instructions.Add(CilOpCodes.Ceq);
                    unaryResultType = context.AppContext.SystemTypes.SystemInt32Type;
                }
                else if (!unaryOperandUsable)
                    // `not` on a struct/float has no honest decode; keep the diagnostic.
                    EmitUnrecoverableOperation(method, writeLine, $"Unrecoverable integer operation: {instruction}");
                else
                    instructions.Add(CilOpCodes.Not);

                EmitStackCoerceOrDefault(unaryResultType, StoreContract(instruction.Operands[0], context), method, context);
                StoreToOperand(instruction.Operands[0], method, locals, writeLine, context);
                break;
            }

            default:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Unknown instruction: {instruction}"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;
        }

        return instructions.ToList().GetRange(startIndex, instructions.Count - startIndex); // Return added IL
    }

    private static bool IsExceptionValueReturnedFromIncompatibleMethod(MethodAnalysisContext context, IOperand operand)
    {
        var valueType = operand switch
        {
            LocalVariable { Type: { } type } => type,
            FieldReference { Field.FieldType: { } type } => type,
            SelectedFieldReference { FieldType: { } type } => type,
            _ => null
        };

        if (valueType is null || valueType is GenericParameterTypeAnalysisContext
            || !valueType.IsAssignableTo(context.AppContext.SystemTypes.SystemExceptionType))
            return false;

        if (context.ReturnType is GenericParameterTypeAnalysisContext
            || valueType.IsAssignableTo(context.ReturnType))
            return false;

        return true;
    }
    
    private static int ConstructorReceiverIndex(Instruction constructorCall) => constructorCall.OpCode == OpCode.CallVoid ? 1 : 2;

    private static Dictionary<Instruction, Instruction> FindConstructorPairs(MethodAnalysisContext context)
    {
        var instructions = context.ControlFlowGraph!.Instructions;
        var pairs = new Dictionary<Instruction, Instruction>();

        foreach (var allocation in instructions.Where(i => i.OpCode == OpCode.Newobj))
        {
            if (FindConstructorCall(context, allocation) is { } constructorCall)
            {
                Analysis.AllocationConstructorRecovery.RewriteInlinedFieldInitializer(context, allocation,
                    constructorCall);
                pairs[allocation] = constructorCall;
            }
        }

        return pairs;
    }

    private static Instruction? ConstructorAllocationForCall(Instruction constructorCall,
        IReadOnlyDictionary<Instruction, Instruction> constructorPairs)
    {
        foreach (var pair in constructorPairs)
        {
            if (ReferenceEquals(pair.Value, constructorCall))
                return pair.Key;
        }

        return null;
    }

    // IL2CPP inlines constructor chains, so a derived .ctor can be left calling a
    // distant ancestor .ctor on `this` (e.g. MonoBehaviour or Object) instead of the
    // immediate base. The verifier only accepts own-type or direct-base .ctor calls
    // on `this`, so provable calls are re-anchored to the immediate base .ctor:
    // parameterless calls move to the prologue (managed order runs base init before
    // field stores), calls whose arguments are all parameters/constants may follow
    // them, and everything else is retargeted in place or left as evidence.
    private sealed class ThisConstructorCallPlan
    {
        public readonly HashSet<Instruction> Skip = [];
        public readonly Dictionary<Instruction, MethodAnalysisContext> Retarget = [];
        public readonly List<(MethodAnalysisContext Constructor, IOperand?[] Arguments)> PrologueCalls = [];

        public static ThisConstructorCallPlan? Create(MethodAnalysisContext context)
        {
            if (context is not { IsStatic: false, Name: ".ctor" }
                || context.DeclaringType is not { IsValueType: false } declaringType
                || declaringType.BaseType is not { } immediateBase)
                return null;

            var thisLocal = context.ParameterLocals.FirstOrDefault();
            List<(Instruction Instruction, MethodAnalysisContext Callee)> calls = [];
            List<Instruction> unresolvedThisCalls = [];
            foreach (var instruction in context.ControlFlowGraph!.Instructions)
            {
                if (!instruction.IsCall
                    || instruction.Operands.Count <= ConstructorReceiverIndex(instruction)
                    || instruction.Operands[ConstructorReceiverIndex(instruction)] is not LocalVariable receiver
                    // Same rule as the emitter's own-this check: the flag, or the local
                    // analysis pinned as the 'this' parameter.
                    || !(receiver.IsThis || ReferenceEquals(receiver, thisLocal)))
                    continue;

                if (instruction.Operands[0] is MethodAnalysisContext { IsStatic: false, Name: ".ctor" } callee)
                    calls.Add((instruction, callee));
                else if (instruction.Operands[0] is Immediate)
                    // A call on `this` whose target stayed a raw address: a .ctor's `call`
                    // on `this` is only ever legal to a .ctor, so this is the init call
                    // the lifter failed to name.
                    unresolvedThisCalls.Add(instruction);
            }

            List<(Instruction Instruction, MethodAnalysisContext Callee)> distant = [];
            var hasLegalInitialization = false;
            foreach (var call in calls)
            {
                if (SameTypeIdentity(call.Callee.DeclaringType, declaringType)
                    || SameTypeIdentity(call.Callee.DeclaringType, immediateBase))
                    hasLegalInitialization = true;
                else
                    // A `call` to a .ctor on `this` only verifies when the callee is an
                    // overload of this .ctor or the immediate base's; anything else is a
                    // leftover of the inlined base chain (or a broken base-type link) and
                    // must be re-anchored or dropped.
                    distant.Add(call);
            }

            // Re-anchor an unresolved `this` call to the .ctor its operand shape
            // selects - the recovered target keeps the real arguments, unlike a
            // synthesized prologue.
            ThisConstructorCallPlan? RetargetUnresolvedThisCall()
            {
                foreach (var call in unresolvedThisCalls)
                    if (ResolveThisConstructorCall(call, declaringType, immediateBase, context) is { } recovered)
                    {
                        var retargeted = new ThisConstructorCallPlan();
                        retargeted.Retarget[call] = recovered;
                        return retargeted;
                    }

                return null;
            }

            if (calls.Count == 0)
            {
                if (RetargetUnresolvedThisCall() is { } recoveredPlan)
                    return recoveredPlan;

                // No .ctor call on `this` survived lifting at all (IL2CPP elides the
                // trivial Object::.ctor chain); the verifier still requires `this`
                // initialized before ret, so synthesize the honest base-init call
                // when the immediate base offers a reachable .ctor.
                var baseCtor = FindParameterlessBaseConstructor(immediateBase);
                if (baseCtor == null
                    || !IsAccessibleBaseConstructor(baseCtor, context)
                    || !CalleeUsableFrom(baseCtor, context))
                    baseCtor = FindAccessibleBaseConstructor(immediateBase, -1, context)
                        ?? FindUniqueAccessibleBaseConstructor(immediateBase, context);
                if (baseCtor == null)
                    return null;
                var synthesized = new ThisConstructorCallPlan();
                synthesized.PrologueCalls.Add((baseCtor, new IOperand?[baseCtor.Parameters.Count]));
                return synthesized;
            }

            if (distant.Count == 0)
            {
                // Managed source runs the base .ctor before anything else touches
                // `this`, but the inlined chain can leave the surviving legal call
                // late in the body while earlier instructions read `this` as a
                // value. When the call is the only one and its arguments are live
                // from the first slot (immediates and parameters), hoist it to a
                // prologue - the position managed code always runs it in. The same
                // hoist applies when the call sits behind a guard some `ret` path
                // bypasses: arguments that are not live at entry emit their default,
                // the recovered operand shape the call carried anyway.
                if (calls.Count == 1 && hasLegalInitialization
                    && (PrologueArguments(calls[0].Instruction, calls[0].Callee, context) is { } initArguments
                        || (!InitCallDominatesAllReturns(calls[0].Instruction, context)
                            && (initArguments = PrologueArguments(calls[0].Instruction, calls[0].Callee, context,
                                allowDefaults: true)) != null)))
                {
                    var hoisted = new ThisConstructorCallPlan();
                    hoisted.Skip.Add(calls[0].Instruction);
                    hoisted.PrologueCalls.Add((calls[0].Callee, initArguments));
                    return hoisted;
                }
                return null;
            }

            var plan = new ThisConstructorCallPlan();
            if (hasLegalInitialization)
            {
                // The genuine initialization call survived; further ancestor calls are
                // remnants of the chain it was inlined from.
                foreach (var (instruction, _) in distant)
                    plan.Skip.Add(instruction);
                return plan;
            }

            // A distant-ancestor call has to be re-anchored to the immediate base to
            // verify. Same-signature matches reproduce the original `base(...)` call;
            // when the inlined chain leaves no matching signature, the closest
            // accessible base .ctor still initializes `this` honestly: same arity
            // keeps the surviving operands meaningful, a parameterless .ctor invents
            // nothing, and any wider signature is filled with defaults.
            List<(Instruction Instruction, MethodAnalysisContext Replacement)> resolved = [];
            List<Instruction> unresolved = [];
            foreach (var (instruction, callee) in distant)
            {
                var match = FindImmediateBaseConstructor(immediateBase, callee);
                if (match != null
                    && (!IsAccessibleBaseConstructor(match, context)
                        || !CalleeUsableFrom(match, context)))
                    match = null;
                match ??= FindAccessibleBaseConstructor(immediateBase, callee.Parameters.Count, context);
                if (match != null)
                    resolved.Add((instruction, match));
                else
                    unresolved.Add(instruction);
            }

            if (resolved.Count == 0)
            {
                if (RetargetUnresolvedThisCall() is { } retargetedPlan)
                    return retargetedPlan;

                // No distant call could be re-anchored and no unresolved `this`
                // call could be shape-matched; `this` still has to be initialized
                // before ret, so fall back to the closest reachable base .ctor and
                // drop the distant calls the verifier must reject.
                var fallbackCtor = FindParameterlessBaseConstructor(immediateBase);
                if (fallbackCtor == null
                    || !IsAccessibleBaseConstructor(fallbackCtor, context)
                    || !CalleeUsableFrom(fallbackCtor, context))
                    fallbackCtor = FindAccessibleBaseConstructor(immediateBase, -1, context)
                        ?? FindUniqueAccessibleBaseConstructor(immediateBase, context);
                if (fallbackCtor == null)
                    return null;
                foreach (var (instruction, _) in distant)
                    plan.Skip.Add(instruction);
                plan.PrologueCalls.Add((fallbackCtor, new IOperand?[fallbackCtor.Parameters.Count]));
                return plan;
            }

            // Distant calls with no reachable base .ctor are inlined-chain remnants;
            // once `this` is initialized by the retargeted calls they only re-run
            // work the inlining already emitted, so drop them rather than emit a
            // call the verifier must reject.
            foreach (var instruction in unresolved)
                plan.Skip.Add(instruction);

            var replacement = resolved[0].Replacement;
            if (resolved.Count == distant.Count
                && replacement.Parameters.Count == 0
                && resolved.All(r => SameMethodIdentity(r.Replacement, replacement)))
            {
                foreach (var (instruction, _) in resolved)
                    plan.Skip.Add(instruction);
                plan.PrologueCalls.Add((replacement, []));
                return plan;
            }

            if (resolved.Count == 1
                && PrologueArguments(resolved[0].Instruction, replacement, context) is { } prologueArguments)
            {
                plan.Skip.Add(resolved[0].Instruction);
                plan.PrologueCalls.Add((replacement, prologueArguments));
                return plan;
            }

            foreach (var (instruction, method) in resolved)
                plan.Retarget[instruction] = method;
            return plan;
        }

        private static IOperand?[]? PrologueArguments(Instruction call, MethodAnalysisContext replacement,
            MethodAnalysisContext context, bool allowDefaults = false)
        {
            var receiver = ConstructorReceiverIndex(call);
            if (call.Operands.Count < receiver + 1 + replacement.Parameters.Count)
                return null;

            var arguments = call.Operands.Skip(receiver + 1).Take(replacement.Parameters.Count)
                .Select(a => a switch
                {
                    Immediate or StringLiteral or FloatLiteral or DoubleLiteral or TypeAnalysisContext => a,
                    LocalVariable local when !local.IsThis && !local.IsMethodInfo
                        && context.ParameterLocals.Contains(local) => a,
                    _ => null,
                }).ToArray();
            return allowDefaults || arguments.All(a => a != null) ? arguments : null;
        }

        // A base-init call the verifier honours only covers the `ret`s its block
        // dominates; a guard can leave a path that reaches `ret` with `this` still
        // uninitialized.
        private static bool InitCallDominatesAllReturns(Instruction call, MethodAnalysisContext context)
        {
            var graph = context.ControlFlowGraph;
            var dominators = context.DominatorInfo;
            if (graph == null || dominators == null)
                return true; // no basis to judge - keep the call in place

            var callBlock = graph.Blocks.FirstOrDefault(block => block.Instructions.Contains(call));
            if (callBlock == null)
                return true;

            foreach (var block in graph.Blocks)
                if (block.Instructions.Any(instruction => instruction.OpCode == OpCode.Return)
                    && !dominators.Dominates(callBlock, block))
                    return false;
            return true;
        }

        private static MethodAnalysisContext? FindParameterlessBaseConstructor(TypeAnalysisContext immediateBase)
        {
            var genericInstance = immediateBase as GenericInstanceTypeAnalysisContext;
            var definition = genericInstance?.GenericType ?? immediateBase;

            MethodAnalysisContext? match = null;
            foreach (var candidate in definition.Methods)
            {
                if (candidate is not { IsStatic: false, Name: ".ctor" } || candidate.Parameters.Count != 0)
                    continue;

                var concrete = genericInstance != null
                    ? new ConcreteGenericMethodAnalysisContext(candidate, genericInstance.GenericArguments, [])
                    : candidate;
                if (match != null)
                    return null;
                match = concrete;
            }

            return match;
        }

        // The single .ctor the immediate base exposes that the derived .ctor may
        // name, or null when the choice is not pinned to exactly one.
        private static MethodAnalysisContext? FindUniqueAccessibleBaseConstructor(TypeAnalysisContext immediateBase,
            MethodAnalysisContext context)
        {
            var genericInstance = immediateBase as GenericInstanceTypeAnalysisContext;
            var definition = genericInstance?.GenericType ?? immediateBase;

            MethodAnalysisContext? match = null;
            foreach (var candidate in definition.Methods)
            {
                if (candidate is not { IsStatic: false, Name: ".ctor" })
                    continue;

                var concrete = genericInstance != null
                    ? new ConcreteGenericMethodAnalysisContext(candidate, genericInstance.GenericArguments, [])
                        : candidate;
                // A .ctor the derived type cannot name was never the init call.
                if (!IsAccessibleBaseConstructor(concrete, context))
                    continue;
                if (match != null)
                    return null;
                match = concrete;
            }

            return match;
        }

        // In a .ctor the only `call` `this` may receive is a constructor call, so an
        // unresolved call on `this` is the init call whose target the lifter lost.
        // Recover it by matching the operand shape against the .ctors of the
        // immediate base and the declaring type: a unique signature match is the
        // honest callee; ambiguity returns null and keeps the diagnostic stub.
        private static MethodAnalysisContext? ResolveThisConstructorCall(Instruction call,
            TypeAnalysisContext declaringType, TypeAnalysisContext immediateBase, MethodAnalysisContext context)
        {
            var receiver = ConstructorReceiverIndex(call);
            var argumentCount = call.Operands.Count - receiver - 1;
            // A trailing hidden MethodInfo or rgctx-table argument rides along on
            // unknown-callee calls (generic instantiations carry the rgctx slot
            // after the real arguments).
            if (argumentCount > 0
                && call.Operands[^1] is RuntimeMethodInfoAnalysisContext
                    or LocalVariable { IsMethodInfo: true }
                    or LocalVariable { Type: RuntimeMethodInfoAnalysisContext }
                    or MemoryOperand { Base: LocalVariable { Type: RgctxTableTypeAnalysisContext
                        or MethodRgctxTableTypeAnalysisContext } })
                argumentCount--;

            MethodAnalysisContext? match = null;
            foreach (var owner in new[] { immediateBase, declaringType })
            {
                var ownerInstance = owner as GenericInstanceTypeAnalysisContext;
                var ownerDefinition = ownerInstance?.GenericType ?? owner;
                var sibling = SameTypeIdentity(ownerDefinition,
                    (declaringType as GenericInstanceTypeAnalysisContext)?.GenericType ?? declaringType);

                foreach (var candidate in ownerDefinition.Methods)
                {
                    if (candidate is not { IsStatic: false, Name: ".ctor" }
                        || candidate.Parameters.Count != argumentCount
                        || ReferenceEquals(candidate, context)
                        || SameMethodIdentity(candidate, context))
                        continue;

                    var concrete = ownerInstance != null
                        ? new ConcreteGenericMethodAnalysisContext(candidate, ownerInstance.GenericArguments, [])
                        : candidate;

                    // A sibling .ctor is always nameable from its own type; a base
                    // .ctor must be reachable from the derived constructor.
                    if (!sibling && !IsAccessibleBaseConstructor(concrete, context))
                        continue;

                    if (!CallArgumentsSatisfy(call, receiver, concrete, context))
                        continue;

                    if (match != null)
                        return null; // two legal targets - resolving would be a guess

                    match = concrete;
                }
            }

            return match;
        }

        // Every operand the call still carries must be able to feed the candidate's
        // parameter in that slot; an untyped operand cannot disqualify, a mistyped
        // one can.
        private static bool CallArgumentsSatisfy(Instruction call, int receiver,
            MethodAnalysisContext constructor, MethodAnalysisContext context)
        {
            for (var i = 0; i < constructor.Parameters.Count; i++)
            {
                var parameterType = constructor.Parameters[i].ParameterType;
                var emitted = EmittedOperandType(call.Operands[receiver + 1 + i], context, parameterType);
                if (emitted != null && !LooseAssignable(emitted, parameterType))
                    return false;
            }

            return true;
        }

        // A derived .ctor may always name its direct base .ctor on `this`: family
        // access covers protected bases, and only truly private or cross-assembly
        // assembly-only constructors are out of reach. A private .ctor on a base
        // emitted into this same assembly stays reachable because member definitions
        // are relaxed to public when their descriptors are emitted.
        private static bool IsAccessibleBaseConstructor(MethodAnalysisContext constructor,
            MethodAnalysisContext caller)
        {
            var access = constructor.Attributes & MethodAttributes.MemberAccessMask;
            if (access is MethodAttributes.Public or MethodAttributes.Family)
                return true;

            var sameAssembly = constructor.DeclaringType?.DeclaringAssembly != null
                && ReferenceEquals(caller.DeclaringType?.DeclaringAssembly,
                    constructor.DeclaringType.DeclaringAssembly);
            // Emitted siblings share InternalsVisibleTo, so internal .ctors cross
            // the assembly boundary; private ones still do not.
            var assemblyScope = sameAssembly
                || Extensions.AccessibilityExtensions.SharesEmittedInternals(
                    caller.DeclaringType?.DeclaringAssembly, constructor.DeclaringType?.DeclaringAssembly);
            return access switch
            {
                MethodAttributes.FamORAssem => true,
                MethodAttributes.Assembly or MethodAttributes.FamANDAssem => assemblyScope,
                // Emission relaxes same-assembly member definitions to public; a
                // constructed (generic) base keeps its declared access, so the
                // IsVisibleFrom check stays the gate for those.
                MethodAttributes.Private => sameAssembly,
                _ => false,
            };
        }

        private static MethodAnalysisContext? FindImmediateBaseConstructor(TypeAnalysisContext immediateBase,
            MethodAnalysisContext distantCallee)
        {
            var genericInstance = immediateBase as GenericInstanceTypeAnalysisContext;
            var definition = genericInstance?.GenericType ?? immediateBase;

            MethodAnalysisContext? match = null;
            foreach (var candidate in definition.Methods)
            {
                if (candidate is not { IsStatic: false, Name: ".ctor" }
                    || candidate.Parameters.Count != distantCallee.Parameters.Count)
                    continue;

                var concrete = genericInstance != null
                    ? new ConcreteGenericMethodAnalysisContext(candidate, genericInstance.GenericArguments, [])
                    : candidate;
                if (!SameMethodSignature(concrete, distantCallee))
                    continue;

                if (match != null)
                    return null;
                match = concrete;
            }

            return match;
        }

        // The inlined-away chain can leave a distant .ctor call whose signature no
        // immediate-base .ctor repeats. `this` still has to be initialized by a legal
        // call, so fall back to the closest accessible base .ctor: matching arity
        // keeps the call's surviving operands aligned with real parameters, a
        // parameterless .ctor invents nothing, and otherwise the smallest signature
        // minimizes defaulted arguments. arity of -1 means no surviving call.
        private static MethodAnalysisContext? FindAccessibleBaseConstructor(TypeAnalysisContext immediateBase,
            int distantArity, MethodAnalysisContext caller)
        {
            var genericInstance = immediateBase as GenericInstanceTypeAnalysisContext;
            var definition = genericInstance?.GenericType ?? immediateBase;

            MethodAnalysisContext? best = null;
            var bestScore = int.MaxValue;
            foreach (var candidate in definition.Methods)
            {
                if (candidate is not { IsStatic: false, Name: ".ctor" })
                    continue;

                var concrete = genericInstance != null
                    ? new ConcreteGenericMethodAnalysisContext(candidate, genericInstance.GenericArguments, [])
                    : candidate;
                if (!IsAccessibleBaseConstructor(concrete, caller)
                    // A constructed base's .ctor reaches the verifier with declared
                    // accessibility intact, so it must also survive that check.
                    || !CalleeUsableFrom(concrete, caller))
                    continue;

                var score = candidate.Parameters.Count == distantArity ? 0
                    : candidate.Parameters.Count == 0 ? 1
                    : 2 + candidate.Parameters.Count;
                if (score < bestScore)
                {
                    best = concrete;
                    bestScore = score;
                }
            }

            return best;
        }

        // IL2CPP shares generic code across reference-type arguments, so the lifter may tag
        // a `newobj` with `List<object>` while every use site wants `List<string>`. When the
        // allocated type and the destination are instantiations of the same generic
        // definition, rebuild the constructor against the destination's instantiation.
        internal static MethodAnalysisContext? RetargetToDestinationInstantiation(MethodAnalysisContext constructor,
            TypeAnalysisContext? destinationType)
        {
            if (destinationType is ByRefTypeAnalysisContext byRefDestination)
                destinationType = byRefDestination.ElementType;
            if (destinationType is not GenericInstanceTypeAnalysisContext destination)
                return null;

            // The callee may sit on another instantiation of the same generic definition
            // (shared generics erase T to object) or on the definition itself; both can be
            // re-anchored to the destination's concrete arguments.
            var source = constructor.DeclaringType as GenericInstanceTypeAnalysisContext;
            var sourceDefinition = source?.GenericType ?? constructor.DeclaringType;
            if (sourceDefinition == null
                || !SameTypeIdentity(sourceDefinition, destination.GenericType)
                || (source != null
                    && (source.GenericArguments.Count != destination.GenericArguments.Count
                        || source.GenericArguments.Zip(destination.GenericArguments, SameTypeIdentity).All(match => match))))
                return null;

            var baseConstructor = constructor is ConcreteGenericMethodAnalysisContext concrete
                ? concrete.BaseMethodContext
                : constructor;
            var methodArguments = (constructor as ConcreteGenericMethodAnalysisContext)?.MethodGenericParameters
                ?? (IReadOnlyList<TypeAnalysisContext>)[];
            return new ConcreteGenericMethodAnalysisContext(baseConstructor, destination.GenericArguments, methodArguments);
        }

        private static bool SameMethodIdentity(MethodAnalysisContext a, MethodAnalysisContext b)
        {
            var aBase = a is ConcreteGenericMethodAnalysisContext concreteA ? concreteA.BaseMethodContext : a;
            var bBase = b is ConcreteGenericMethodAnalysisContext concreteB ? concreteB.BaseMethodContext : b;
            return ReferenceEquals(aBase, bBase) && SameMethodSignature(a, b);
        }

        // The matched base .ctor is declared on a different type than the distant
        // callee by definition, so identity is a name + signature comparison only.
        private static bool SameMethodSignature(MethodAnalysisContext a, MethodAnalysisContext b) =>
            a.Name == b.Name
            && a.Parameters.Count == b.Parameters.Count
            && a.Parameters.Zip(b.Parameters, (x, y) => SameTypeIdentity(x.ParameterType, y.ParameterType)).All(z => z);

        // Concrete generic method contexts build their declaring type fresh, and identical
        // metadata types can arrive as different context objects, so compare structurally.
        internal static bool SameTypeIdentity(TypeAnalysisContext? a, TypeAnalysisContext? b)
        {
            if (a == null || b == null)
                return false;
            if (ReferenceEquals(a, b) || a.FullName == b.FullName)
                return true;
            return a is GenericInstanceTypeAnalysisContext left
                && b is GenericInstanceTypeAnalysisContext right
                && SameTypeIdentity(left.GenericType, right.GenericType)
                && left.GenericArguments.Count == right.GenericArguments.Count
                && left.GenericArguments.Zip(right.GenericArguments, SameTypeIdentity).All(z => z);
        }
    }

    // Finds a .ctor on `concreteType` whose signature matches `constructor`'s and which
    // is visible from the emitting method, to re-anchor a `newobj` whose resolved .ctor
    // sits on an abstract base. For a generic instance the definition's .ctor is
    // re-instantiated with the instance's arguments; the definition-level signature
    // comparison additionally tolerates shared-generic erasure where the abstract
    // callee's parameters were recovered as their substitution (e.g. object).
    private static MethodAnalysisContext? MatchingConcreteConstructor(TypeAnalysisContext concreteType,
        MethodAnalysisContext constructor, MethodAnalysisContext context)
    {
        var instance = concreteType as GenericInstanceTypeAnalysisContext;
        var definition = instance?.GenericType ?? concreteType;
        var constructorBase = (constructor as ConcreteGenericMethodAnalysisContext)?.BaseMethodContext ?? constructor;

        foreach (var candidate in definition.Methods)
        {
            if (candidate is not { IsStatic: false, Name: ".ctor" }
                || candidate.Parameters.Count != constructor.Parameters.Count)
                continue;

            var instantiated = instance == null
                ? candidate
                : new ConcreteGenericMethodAnalysisContext(candidate, instance.GenericArguments, []);
            if ((instantiated.Parameters.Zip(constructor.Parameters,
                    (x, y) => ThisConstructorCallPlan.SameTypeIdentity(x.ParameterType, y.ParameterType)).All(z => z)
                || candidate.Parameters.Zip(constructorBase.Parameters,
                    (x, y) => ThisConstructorCallPlan.SameTypeIdentity(x.ParameterType, y.ParameterType)).All(z => z))
                && ConstructorVisibleFrom(instantiated, context))
                return instantiated;
        }

        return null;
    }

    private static bool TryGetOptionalInlinedConstructor(TypeAnalysisContext allocated,
        MethodAnalysisContext caller, out MethodAnalysisContext constructor, out List<IOperand> arguments)
    {
        constructor = null!;
        arguments = null!;
        var candidates = allocated.Methods.Where(method => method is { IsStatic: false, Name: ".ctor" }
            && method.Parameters.Count > 0
            && method.Parameters.All(parameter => parameter.Attributes.HasFlag(ParameterAttributes.HasDefault))
            && ConstructorVisibleFrom(method, caller)).ToArray();
        if (candidates is not [{ } candidate])
            return false;

        var defaults = candidate.Parameters.Select(parameter => DefaultValueOperand(parameter.DefaultValue)).ToList();
        if (defaults.Any(value => value == null))
            return false;
        constructor = candidate;
        arguments = defaults.Select(value => value!).ToList();
        return true;
    }

    private static IOperand? DefaultValueOperand(object? value) => value switch
    {
        null => new Immediate(0),
        bool boolean => new Immediate(boolean ? 1 : 0),
        char character => new Immediate(character),
        byte number => new Immediate(number),
        sbyte number => new Immediate(number),
        short number => new Immediate(number),
        ushort number => new Immediate(number),
        int number => new Immediate(number),
        uint number => new Immediate(number),
        long number => new Immediate(number),
        ulong number when number <= long.MaxValue => new Immediate((long)number),
        float number => new FloatLiteral(number),
        double number => new DoubleLiteral(number),
        string text => new StringLiteral(text),
        _ => null,
    };

    private static void RemoveInlinedConstructorStores(MethodAnalysisContext caller, Instruction allocation,
        Instruction constructorCall, LocalVariable instance)
    {
        var instructions = caller.ControlFlowGraph!.Instructions;
        var start = instructions.IndexOf(allocation);
        var constructorIndex = instructions.IndexOf(constructorCall);
        for (var i = start + 1; i < instructions.Count; i++)
        {
            var current = instructions[i];
            if (current is { OpCode: OpCode.Move,
                    Operands: [FieldReference { Local: var receiver, Containers.Count: 0 }, _] }
                && ReferenceEquals(receiver, instance))
            {
                current.OpCode = OpCode.Nop;
                current.SetOperands();
                continue;
            }
            if (i <= constructorIndex || current.OpCode == OpCode.Nop
                || current.Operands.Any(operand => ReferenceEquals(operand, instance)))
                continue;
            break;
        }
    }

    // IL2CPP can inline a concrete constructor into the caller, leaving object_new
    // followed by Object::.ctor and direct field stores. If the concrete class has
    // no managed parameterless constructor, add the minimal allocation shell that
    // represents those two native operations; the following recovered stores still
    // perform the real initialization.
    private static IMethodDescriptor? EnsureBareAllocationConstructor(TypeAnalysisContext concreteType,
        MethodAnalysisContext objectConstructor, MethodDefinition caller)
    {
        if (concreteType.BaseType?.FullName != "System.Object"
            || concreteType.GetExtraData<TypeDefinition>("AsmResolverType") is not { } typeDefinition
            || !ReferenceEquals(typeDefinition.DeclaringModule, caller.DeclaringModule))
            return null;

        var factory = caller.DeclaringModule!.CorLibTypeFactory;
        var signature = MethodSignature.CreateInstance(factory.Void, []);
        if (typeDefinition.Methods.FirstOrDefault(method =>
                method.Name == ".ctor" && method.Signature?.ParameterTypes.Count == 0) is { } existing)
            return existing;

        var constructor = new MethodDefinition(".ctor",
            AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
            | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.HideBySig
            | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.SpecialName
            | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.RuntimeSpecialName,
            signature);
        var body = new CilMethodBody();
        body.Instructions.Add(CilOpCodes.Ldarg_0);
        body.Instructions.Add(CilOpCodes.Call, objectConstructor.ToMethodDescriptor());
        body.Instructions.Add(CilOpCodes.Ret);
        constructor.CilMethodBody = body;
        typeDefinition.Methods.Add(constructor);
        return constructor;
    }

    // Shared generics erase the callee's instantiation arguments to System.Object at
    // the call site, but the operand types carry the instantiation the native code
    // actually ran: the callee's open signature is matched against the emitted
    // types of the parameter operands and the declared type of the result slot.
    // Only provably-erased arguments (System.Object or an open parameter) are
    // replaced - a concrete argument from metadata is already authoritative.
    private static MethodAnalysisContext? SolveSharedGenericArguments(
        MethodAnalysisContext targetMethod, Instruction instruction, MethodAnalysisContext context, int thisParamIndex,
        bool includeResultContract = true)
    {
        var open = (targetMethod as ConcreteGenericMethodAnalysisContext)?.BaseMethodContext ?? targetMethod;
        var declaringInstance = targetMethod.DeclaringType as GenericInstanceTypeAnalysisContext;
        var typeArguments = declaringInstance?.GenericArguments.ToArray();
        var methodArguments = (targetMethod as ConcreteGenericMethodAnalysisContext)?.MethodGenericParameters.ToArray();
        if ((methodArguments == null || methodArguments.Length == 0) && open.GenericParameters.Count > 0)
            methodArguments = open.GenericParameters.Cast<TypeAnalysisContext>().ToArray();
        if (typeArguments == null && methodArguments == null)
            return null;

        var changed = false;
        // The verifier checks `this` against the callee's constructed declaring
        // type, so for an instance call the type arguments are pinned by what the
        // receiver operand emits (RetargetToDestinationInstantiation already
        // re-anchors to it). Solving them further from the result contract would
        // retarget the callee past the receiver - List<object>::get_Item fed by
        // a List<object> local must stay List<object>::get_Item. A static callee
        // names no receiver, so its instantiation is free to be sharpened from
        // any operand evidence.
        var maySolveTypeArguments = targetMethod.IsStatic;
        void Solve(TypeAnalysisContext? pattern, TypeAnalysisContext? concrete)
        {
            if (pattern == null || concrete == null)
                return;
            switch (pattern)
            {
                case GenericParameterTypeAnalysisContext { Type: Il2CppTypeEnum.IL2CPP_TYPE_VAR } typeParameter
                    when maySolveTypeArguments && typeArguments != null && typeParameter.Index < typeArguments.Length:
                    if (IsErasedSharedArgument(typeArguments[typeParameter.Index])
                        && concrete is not (ByRefTypeAnalysisContext or PointerTypeAnalysisContext
                            or GenericParameterTypeAnalysisContext)
                        && !IsErasedSharedArgument(concrete)
                        && !ThisConstructorCallPlan.SameTypeIdentity(typeArguments[typeParameter.Index], concrete))
                    {
                        typeArguments[typeParameter.Index] = concrete;
                        changed = true;
                    }
                    break;
                case GenericParameterTypeAnalysisContext { Type: Il2CppTypeEnum.IL2CPP_TYPE_MVAR } methodParameter
                    when methodArguments != null && methodParameter.Index < methodArguments.Length:
                    if (IsErasedSharedArgument(methodArguments[methodParameter.Index])
                        && concrete is not (ByRefTypeAnalysisContext or PointerTypeAnalysisContext
                            or GenericParameterTypeAnalysisContext)
                        && !IsErasedSharedArgument(concrete)
                        && !ThisConstructorCallPlan.SameTypeIdentity(methodArguments[methodParameter.Index], concrete))
                    {
                        methodArguments[methodParameter.Index] = concrete;
                        changed = true;
                    }
                    break;
                case ByRefTypeAnalysisContext byRef:
                    Solve(byRef.ElementType,
                        concrete is ByRefTypeAnalysisContext concreteByRef ? concreteByRef.ElementType : concrete);
                    break;
                case PointerTypeAnalysisContext pointer when concrete is PointerTypeAnalysisContext concretePointer:
                    Solve(pointer.ElementType, concretePointer.ElementType);
                    break;
                case GenericInstanceTypeAnalysisContext patternInstance
                    when concrete is SzArrayTypeAnalysisContext array
                        && patternInstance.GenericArguments.Count == 1
                        && IsArrayGenericInterface(patternInstance.GenericType):
                    Solve(patternInstance.GenericArguments[0], array.ElementType);
                    break;
                case GenericInstanceTypeAnalysisContext patternInstance
                    when concrete is GenericInstanceTypeAnalysisContext concreteInstance
                        && (ThisConstructorCallPlan.SameTypeIdentity(patternInstance.GenericType, concreteInstance.GenericType)
                            || concreteInstance.IsAssignableTo(patternInstance.GenericType))
                        && patternInstance.GenericArguments.Count == concreteInstance.GenericArguments.Count:
                    for (var k = 0; k < patternInstance.GenericArguments.Count; k++)
                        Solve(patternInstance.GenericArguments[k], concreteInstance.GenericArguments[k]);
                    break;
            }
        }

        var parameterOperandStart = thisParamIndex + (targetMethod.IsStatic ? 0 : 1);
        for (var i = 0; i < open.Parameters.Count && parameterOperandStart + i < instruction.Operands.Count; i++)
        {
            var operand = instruction.Operands[parameterOperandStart + i];
            // Hidden shared-generic channels (MethodInfo*/klass*/rgctx) can sit in a
            // parameter slot; their emitted nint is not the argument's type.
            if (operand is RuntimeMethodInfoAnalysisContext or RuntimeFieldInfoAnalysisContext
                or RuntimeClassTypeAnalysisContext or RgctxTableTypeAnalysisContext
                or MethodRgctxTableTypeAnalysisContext or StaticFieldStorageTypeAnalysisContext)
                continue;
            Solve(open.Parameters[i].ParameterType, SharedGenericEvidenceType(operand, context));
        }

        if (includeResultContract && instruction.OpCode == OpCode.Call && instruction.Operands.Count > 1)
            Solve(open.ReturnType, DirectSharedGenericEvidenceType(instruction.Operands[1], context));

        if (!changed)
            return null;

        // Every parameter the call feeds must still match once the solved
        // arguments are substituted in: a second operand disagreeing with the
        // instantiation the first one selected would emit a call whose own
        // argument list the verifier rejects. Unresolved slots stay erased and
        // impose no constraint.
        for (var i = 0; i < open.Parameters.Count && parameterOperandStart + i < instruction.Operands.Count; i++)
        {
            var operand = instruction.Operands[parameterOperandStart + i];
            if (operand is RuntimeMethodInfoAnalysisContext or RuntimeFieldInfoAnalysisContext
                or RuntimeClassTypeAnalysisContext or RgctxTableTypeAnalysisContext
                or MethodRgctxTableTypeAnalysisContext or StaticFieldStorageTypeAnalysisContext)
                continue;
            if (!OperandMatchesSolvedPattern(open.Parameters[i].ParameterType,
                    SharedGenericEvidenceType(operand, context), typeArguments, methodArguments))
                return null;
        }

        var solvedTypeArguments = typeArguments
            ?? (targetMethod as ConcreteGenericMethodAnalysisContext)?.TypeGenericParameters
            ?? [];
        return new ConcreteGenericMethodAnalysisContext(open, solvedTypeArguments, methodArguments ?? []);
    }

    // Whether the emitted operand type still satisfies the open parameter pattern
    // after the shared-generic solve: every generic parameter the pattern spells
    // out must resolve to exactly the type the operand carries.
    private static bool OperandMatchesSolvedPattern(TypeAnalysisContext pattern,
        TypeAnalysisContext? concrete, TypeAnalysisContext[]? typeArguments,
        TypeAnalysisContext[]? methodArguments)
    {
        if (concrete == null)
            return true;
        switch (pattern)
        {
            case GenericParameterTypeAnalysisContext { Type: Il2CppTypeEnum.IL2CPP_TYPE_VAR } typeParameter
                when typeArguments != null && typeParameter.Index < typeArguments.Length:
                return SlotAccepts(typeArguments[typeParameter.Index]);
            case GenericParameterTypeAnalysisContext { Type: Il2CppTypeEnum.IL2CPP_TYPE_MVAR } methodParameter
                when methodArguments != null && methodParameter.Index < methodArguments.Length:
                return SlotAccepts(methodArguments[methodParameter.Index]);
            case GenericParameterTypeAnalysisContext:
                return true;
            case ByRefTypeAnalysisContext byRef:
                return concrete is ByRefTypeAnalysisContext concreteByRef
                    && OperandMatchesSolvedPattern(byRef.ElementType, concreteByRef.ElementType,
                        typeArguments, methodArguments);
            case PointerTypeAnalysisContext pointer:
                return concrete is PointerTypeAnalysisContext concretePointer
                    && OperandMatchesSolvedPattern(pointer.ElementType, concretePointer.ElementType,
                        typeArguments, methodArguments);
            case GenericInstanceTypeAnalysisContext patternInstance:
                if (concrete is SzArrayTypeAnalysisContext array
                    && patternInstance.GenericArguments.Count == 1
                    && IsArrayGenericInterface(patternInstance.GenericType))
                    return OperandMatchesSolvedPattern(patternInstance.GenericArguments[0], array.ElementType,
                        typeArguments, methodArguments);
                if (concrete is not GenericInstanceTypeAnalysisContext concreteInstance)
                    return false;
                if (ThisConstructorCallPlan.SameTypeIdentity(patternInstance.GenericType, concreteInstance.GenericType))
                    return patternInstance.GenericArguments.Count == concreteInstance.GenericArguments.Count
                        && patternInstance.GenericArguments.Zip(concreteInstance.GenericArguments,
                            (p, c) => OperandMatchesSolvedPattern(p, c, typeArguments, methodArguments)).All(match => match);
                try
                {
                    var instantiatedPattern = GenericInstantiation.Instantiate(patternInstance,
                        typeArguments ?? [], methodArguments ?? []);
                    return concreteInstance.IsAssignableTo(instantiatedPattern);
                }
                catch
                {
                    return false;
                }
            default:
                return ThisConstructorCallPlan.SameTypeIdentity(pattern, concrete)
                    || concrete.IsAssignableTo(pattern);
        }

        // An unsolved slot still emits its erased argument (object), which any
        // operand feeds legally; a solved one is the parameter type verbatim, so
        // the operand must be assignable to it.
        bool SlotAccepts(TypeAnalysisContext solved) =>
            IsErasedSharedArgument(solved)
            || ThisConstructorCallPlan.SameTypeIdentity(solved, concrete)
            || concrete.IsAssignableTo(solved);
    }

    private static bool IsArrayGenericInterface(TypeAnalysisContext type) => type.FullName is
        "System.Collections.Generic.IEnumerable`1"
        or "System.Collections.Generic.ICollection`1"
        or "System.Collections.Generic.IList`1"
        or "System.Collections.Generic.IReadOnlyCollection`1"
        or "System.Collections.Generic.IReadOnlyList`1";

    private static bool IsErasedSharedArgument(TypeAnalysisContext argument) =>
        argument is GenericParameterTypeAnalysisContext
        || argument.FullName is "System.Object" or "System.ValueType"
        || IsSharedEnumMarker(argument);

    private static bool IsSharedEnumMarker(TypeAnalysisContext argument) =>
        argument.FullName is "System.SByteEnum" or "System.ByteEnum"
            or "System.Int16Enum" or "System.UInt16Enum"
            or "System.Int32Enum" or "System.UInt32Enum"
            or "System.Int64Enum" or "System.UInt64Enum";

    private static bool ContainsSharedEnumMarker(TypeAnalysisContext argument) =>
        IsSharedEnumMarker(argument)
        || argument is WrappedTypeAnalysisContext wrapped
            && ContainsSharedEnumMarker(wrapped.ElementType)
        || argument is GenericInstanceTypeAnalysisContext instance
            && instance.GenericArguments.Any(ContainsSharedEnumMarker);

    private static bool ContainsErasedSharedArgument(TypeAnalysisContext argument) =>
        IsErasedSharedArgument(argument)
        || argument is GenericInstanceTypeAnalysisContext instance
        && instance.GenericArguments.Any(ContainsErasedSharedArgument);

    // The original call site had access to the .ctor, but the re-anchored candidate sits on a
    // different (concrete) type, so its own accessibility must hold from the emitting method -
    // both the member access and the declaring type's visibility to the caller.
    private static bool ConstructorVisibleFrom(MethodAnalysisContext candidate, MethodAnalysisContext context)
    {
        var declaring = candidate.DeclaringType is GenericInstanceTypeAnalysisContext instance
            ? instance.GenericType
            : candidate.DeclaringType;
        var caller = context.DeclaringType;
        if (declaring == null || caller == null)
            return true; // no metadata basis to judge the access

        var sameAssembly = ReferenceEquals(caller.DeclaringAssembly, declaring.DeclaringAssembly)
            || Extensions.AccessibilityExtensions.SharesEmittedInternals(caller.DeclaringAssembly, declaring.DeclaringAssembly);
        var memberVisible = (candidate.Attributes & MethodAttributes.MemberAccessMask) switch
        {
            MethodAttributes.Public => true,
            // Private members are visible to the declaring type itself, to anything nested
            // inside it, and to the enclosing type of a nested declaration.
            MethodAttributes.Private => IsWithinOrSame(caller, declaring) || IsWithinOrSame(declaring, caller),
            MethodAttributes.Assembly => sameAssembly,
            MethodAttributes.Family => IsWithinOrSame(caller, declaring) || caller.IsAssignableTo(declaring),
            MethodAttributes.FamANDAssem => sameAssembly && (IsWithinOrSame(caller, declaring) || caller.IsAssignableTo(declaring)),
            MethodAttributes.FamORAssem => sameAssembly || IsWithinOrSame(caller, declaring) || caller.IsAssignableTo(declaring),
            _ => false,
        };

        return memberVisible && declaring.IsAccessibleTo(caller);
    }

    private static bool IsWithinOrSame(TypeAnalysisContext candidate, TypeAnalysisContext declaring)
    {
        for (var current = candidate; current != null; current = current.DeclaringType)
            if (ReferenceEquals(current, declaring))
                return true;

        return false;
    }

    // The Il2CppClass* the native object_new was invoked with is the allocation's
    // honest type. It can reach the ISIL operand already resolved (a type or a
    // class-pointer local) or still as a raw metadata-usage global address, which
    // the same usage table ResolveMetadataUsages consults resolves here. Anything
    // else leaves the allocated type unknown.
    private static TypeAnalysisContext? AllocatedClassOperand(MethodAnalysisContext context, Instruction newobj) =>
        newobj.Operands.Count > 1 ? AllocatedClassOperand(context, newobj.Operands[1]) : null;

    private static TypeAnalysisContext? AllocatedClassOperand(MethodAnalysisContext context, IOperand classOperand) =>
        classOperand switch
        {
            RuntimeClassTypeAnalysisContext { RepresentedType: { } represented } => represented,
            TypeAnalysisContext type => type,
            LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType: { } represented } } => represented,
            MemoryOperand { Base: null, Index: null, Scale: 0 } memory => ResolveTypeGlobal(context, (ulong)memory.Addend),
            Immediate immediate => ResolveTypeGlobal(context, immediate.UnsignedValue),
            LocalVariable local => AllocatedClassFromLocal(context, local),
            _ => null,
        };

    // A class argument carried in a local still names the allocated type when every
    // definition of that local is a Move of the same type-metadata global. Any other
    // definition - or two different globals - makes the contents unknowable.
    private static TypeAnalysisContext? AllocatedClassFromLocal(MethodAnalysisContext context, LocalVariable local)
    {
        TypeAnalysisContext? resolved = null;
        foreach (var instruction in context.ControlFlowGraph!.Instructions)
        {
            if (!ReferenceEquals(instruction.Destination, local))
                continue;

            var candidate = instruction switch
            {
                { OpCode: OpCode.Move, Operands: [_, TypeAnalysisContext type] }
                    => type is RuntimeClassTypeAnalysisContext { RepresentedType: { } represented } ? represented : type,
                { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Base: null, Index: null, Scale: 0 } memory] }
                    => ResolveTypeGlobal(context, (ulong)memory.Addend),
                { OpCode: OpCode.Move, Operands: [_, Immediate immediate] }
                    => ResolveTypeGlobal(context, immediate.UnsignedValue),
                _ => null,
            };

            if (candidate == null || (resolved != null && !ReferenceEquals(resolved, candidate)))
                return null;
            resolved = candidate;
        }

        return resolved;
    }

    private static TypeAnalysisContext? ResolveTypeGlobal(MethodAnalysisContext context, ulong address) =>
        context.AppContext.LibCpp2IlContext.GetTypeGlobalByAddress(address) is { } typeGlobal
            ? context.AppContext.ResolveIl2CppType(typeGlobal)
            : null;

    // Try find the constructor call for an allocation. CFG traversal may place the
    // call before the allocation even though both operate on the same SSA local.
    private static Instruction? FindConstructorCall(MethodAnalysisContext context, Instruction newobj)
    {
        var newObject = newobj.Operands[0];

        // The allocation and the constructor call routinely end up in different blocks
        var instructions = context.ControlFlowGraph!.Instructions;
        var index = instructions.IndexOf(newobj);

        if (index < 0)
            return null;

        for (var i = index + 1; i < instructions.Count; i++)
        {
            var candidate = instructions[i];

            if (candidate is not { OpCode: OpCode.Call or OpCode.CallVoid, Operands: [MethodAnalysisContext { Name: ".ctor" }, ..] })
                continue;

            var receiver = ConstructorReceiverIndex(candidate);

            if (candidate.Operands.Count > receiver && ReferenceEquals(candidate.Operands[receiver], newObject))
                return candidate;
        }

        for (var i = 0; i < index; i++)
        {
            var candidate = instructions[i];

            if (candidate is not { OpCode: OpCode.Call or OpCode.CallVoid, Operands: [MethodAnalysisContext { Name: ".ctor" }, ..] })
                continue;

            var receiver = ConstructorReceiverIndex(candidate);

            if (candidate.Operands.Count > receiver && ReferenceEquals(candidate.Operands[receiver], newObject))
                return candidate;
        }

        return null;
    }

    // A `newobj SomeDelegate::.ctor(object, native int)` verifies only when the
    // function pointer on the stack names a method whose signature satisfies the
    // delegate's Invoke (ILVerify's DelegateCtor check). IL2CPP shares generic
    // code across reference arguments, so the recovered instantiation is often
    // erased to System.Object arguments while the ldftn target keeps its
    // concrete signature - `Func<object, bool>` paired with `bool M(UnitData)`.
    // When the erased pairing cannot verify, the target's real signature gives
    // the honest concrete instantiation; when nothing satisfies the check the
    // site degrades to a diagnostic and a null delegate instead.

    // Returns the .ctor to emit - possibly re-instantiated so Invoke matches the
    // ldftn target - or null when `constructor` should be emitted unchanged.
    // `failure` is set to the diagnostic message when no legal emission exists.
    private static MethodAnalysisContext? ResolveDelegateConstructor(
        MethodAnalysisContext constructor, IReadOnlyList<IOperand> constructorArgs,
        MethodAnalysisContext context, out string? failure)
    {
        failure = null;

        var delegateType = constructor.DeclaringType;
        if (constructor.Name != ".ctor" || delegateType == null)
            return null;

        var delegateDefinition = delegateType is GenericInstanceTypeAnalysisContext genericDelegate
            ? genericDelegate.GenericType
            : delegateType;

        // A delegate .ctor is only ever (object, native int); any other shape
        // is an ordinary constructor and keeps the plain emission path.
        if (constructor.Parameters.Count != 2
            || constructor.Parameters[0].ParameterType is { IsValueType: true }
            or ByRefTypeAnalysisContext or PointerTypeAnalysisContext
            || constructor.Parameters[1].ParameterType.FullName is not ("System.IntPtr" or "System.UIntPtr"))
        {
            if (DerivesFromMulticastDelegate(delegateDefinition))
                failure = $"Unverifiable delegate construction: {delegateType.FullName}.ctor is not (object, native int)";
            return null;
        }
        if (!DerivesFromMulticastDelegate(delegateDefinition)
            && HierarchyResolvesToNonDelegate(delegateDefinition))
            return null;

        // The function-pointer argument reaches the stack as a method (ldftn)
        // only for a RuntimeMethodInfo operand; anything else emits a plain
        // native int the verifier cannot accept - and on a delegate .ctor a
        // non-method stack value crashes the verifier outright, so this check
        // has to run even when Invoke itself cannot be resolved.
        if (constructorArgs.Count < 2
            || constructorArgs[1] is not RuntimeMethodInfoAnalysisContext { RepresentedMethod: { } represented })
        {
            failure = $"Unverifiable delegate construction: {delegateType.FullName} has no resolvable function-pointer target";
            return null;
        }

        var invoke = delegateDefinition.Methods.FirstOrDefault(m => m is { IsStatic: false, Name: "Invoke" });
        if (invoke == null)
        {
            // A delegate type we can see but cannot find an Invoke on can never
            // satisfy the check; one whose members were never resolved is left
            // alone because we cannot prove the pairing either way.
            if (delegateDefinition.Methods.Count > 0)
                failure = $"Unverifiable delegate construction: {delegateType.FullName} has no resolvable Invoke";
            return null;
        }

        // The method actually emitted is the visible substitute, exactly as
        // LoadOperand resolves it for the IntPtr contract.
        var target = represented;
        if (!CalleeUsableFrom(target, context))
        {
            if (Analysis.InaccessibleCalleeRecovery.TrySubstitute(target) is { } substitute
                && CalleeUsableFrom(substitute, context))
                target = substitute;
            else
            {
                failure = $"Unverifiable delegate construction: {delegateType.FullName} target {represented.FullNameWithSignature} is inaccessible";
                return null;
            }
        }
        if (target.Name is ".ctor")
        {
            // ldftn cannot name a constructor; the emission degenerates to a
            // null pointer, which is not a method either.
            failure = $"Unverifiable delegate construction: {delegateType.FullName} target is a constructor";
            return null;
        }

        var isNullTarget = constructorArgs[0] is Immediate { Value: 0 };
        var objectEmitted = isNullTarget ? null : EmittedOperandType(constructorArgs[0], context);

        // ldftn of a non-final virtual method is only legal on `this` or a boxed
        // receiver; any other target fails before the signature is even compared.
        if (!target.IsStatic
            && (target.Attributes & MethodAttributes.Virtual) != 0
            && (target.Attributes & MethodAttributes.Final) == 0
            && target.DeclaringType is not { IsSealed: true }
            && constructorArgs[0] is not LocalVariable { IsThis: true }
            && objectEmitted is not { IsValueType: true })
        {
            failure = $"Unverifiable delegate construction: {delegateType.FullName} target {target.FullNameWithSignature} is a non-final virtual method";
            return null;
        }

        var instantiationArgs = (delegateType as GenericInstanceTypeAnalysisContext)?.GenericArguments;

        // The recovered instantiation already satisfies the verifier: leave it alone.
        if (DelegateSignatureMatches(invoke, instantiationArgs, target, objectEmitted, isNullTarget))
            return null;

        if (delegateDefinition.GenericParameters.Count == 0
            || SolveDelegateInstantiation(delegateDefinition, invoke, target, context,
                    instantiationArgs) is not { } solved
            || !DelegateSignatureMatches(invoke, solved, target, objectEmitted, isNullTarget))
        {
            failure = $"Unverifiable delegate construction: {delegateType.FullName} cannot be instantiated for target {target.FullNameWithSignature}";
            return null;
        }

        var baseConstructor = constructor is ConcreteGenericMethodAnalysisContext concrete
            ? concrete.BaseMethodContext
            : null;
        if (baseConstructor?.DeclaringType == null
            || !ThisConstructorCallPlan.SameTypeIdentity(baseConstructor.DeclaringType, delegateDefinition))
            baseConstructor = delegateDefinition.Methods.FirstOrDefault(m =>
                m is { IsStatic: false, Name: ".ctor" } && m.Parameters.Count == 2);
        if (baseConstructor == null)
        {
            failure = $"Unverifiable delegate construction: {delegateType.FullName} has no resolvable .ctor";
            return null;
        }

        return new ConcreteGenericMethodAnalysisContext(baseConstructor, solved, []);
    }

    // Whether the base chain resolves to a concrete non-delegate root
    // (System.Object/ValueType/Enum). A chain that ends without reaching one -
    // the common case for a corlib delegate like Func`2 whose base was never
    // resolved - is indistinguishable from an actual delegate, so the
    // function-pointer requirement must still apply: the verifier resolves the
    // hierarchy from the reference assemblies and crashes on a plain native int.
    private static bool HierarchyResolvesToNonDelegate(TypeAnalysisContext type)
    {
        for (var current = type; current != null;
             current = current.BaseType ?? (current as GenericInstanceTypeAnalysisContext)?.GenericType.BaseType)
        {
            if (current.FullName is "System.MulticastDelegate" or "System.Delegate")
                return false;
            if (current.FullName is "System.Object" or "System.ValueType" or "System.Enum")
                return true;
            if (current.BaseType == null)
                return false;
        }
        return false;
    }

    private static bool DerivesFromMulticastDelegate(TypeAnalysisContext type)
    {
        for (var current = type; current != null;
             current = current.BaseType ?? (current as GenericInstanceTypeAnalysisContext)?.GenericType.BaseType)
            if (current.FullName == "System.MulticastDelegate")
                return true;
        return false;
    }

    // Mirrors the verifier's IsDelegateAssignable plus the stack-shape checks
    // around it: an open delegate takes an ldnull target and a closed one a real
    // object, Invoke's parameters must be assignable to the target's parameters
    // pairwise, and the target's return must be assignable to Invoke's return.
    private static bool DelegateSignatureMatches(
        MethodAnalysisContext invoke, IReadOnlyList<TypeAnalysisContext>? instantiationArgs,
        MethodAnalysisContext target, TypeAnalysisContext? objectEmitted, bool isNullTarget)
    {
        var invokeParameters = invoke.Parameters
            .Select(p => InstantiateDelegateType(p.ParameterType, instantiationArgs)).ToList();
        var invokeReturn = InstantiateDelegateType(invoke.ReturnType, instantiationArgs);

        var totalTargetArgs = target.Parameters.Count + (target.IsStatic ? 0 : 1);

        bool isOpen;
        if (totalTargetArgs == invokeParameters.Count)
            isOpen = true;
        else if (totalTargetArgs == invokeParameters.Count + 1)
            isOpen = false;
        else
            return false;

        // An open delegate takes a null target object, a closed one a real reference.
        if (isOpen != isNullTarget)
            return false;

        if (totalTargetArgs == 0)
            return true; // An open static delegate over a parameterless method.

        var consumedArgs = isOpen ? 1 : 0;
        if (isOpen)
        {
            // Invoke's first parameter stands in for the target's receiver, or
            // for its first fixed argument when the target is static.
            var firstTargetArgument = OpenDelegateFirstArgument(target);
            if (firstTargetArgument == null || !LooseAssignable(invokeParameters[0], firstTargetArgument))
                return false;
        }
        else
        {
            // The pushed object must be a reference assignable to the target's
            // receiver type, or to its first fixed argument for a static target.
            var firstTargetArgument = target.IsStatic
                ? target.Parameters[0].ParameterType
                : target.DeclaringType;
            if (firstTargetArgument == null || objectEmitted == null
                || objectEmitted is ByRefTypeAnalysisContext or PointerTypeAnalysisContext
                    or GenericParameterTypeAnalysisContext
                || !LooseAssignable(objectEmitted, firstTargetArgument))
                return false;
        }

        if (target.IsStatic)
            consumedArgs--;

        if (invokeParameters.Count - consumedArgs != target.Parameters.Count)
            return false;

        for (var i = isOpen ? 1 : 0; i < invokeParameters.Count; i++)
            if (!LooseAssignable(invokeParameters[i], target.Parameters[i - consumedArgs].ParameterType))
                return false;

        // void only ever matches void.
        if (invokeReturn.FullName == "System.Void" || target.ReturnType.FullName == "System.Void")
            return invokeReturn.FullName == target.ReturnType.FullName;

        return LooseAssignable(target.ReturnType, invokeReturn);
    }

    private static TypeAnalysisContext? OpenDelegateFirstArgument(MethodAnalysisContext target) =>
        target.IsStatic
            ? target.Parameters.Count > 0 ? target.Parameters[0].ParameterType : null
            : target.DeclaringType is { IsValueType: true } valueTypeOwner
                ? new ByRefTypeAnalysisContext(valueTypeOwner)
                : target.DeclaringType;

    private static TypeAnalysisContext InstantiateDelegateType(TypeAnalysisContext type,
        IReadOnlyList<TypeAnalysisContext>? instantiationArgs) =>
        instantiationArgs == null ? type : GenericInstantiation.Instantiate(type, instantiationArgs, []);

    private static bool LooseAssignable(TypeAnalysisContext from, TypeAnalysisContext to) =>
        ThisConstructorCallPlan.SameTypeIdentity(from, to) || IsAssignableToLoose(from, to);

    // Rebuilds the delegate's generic arguments from the ldftn target's signature
    // so Invoke accepts it: each Invoke parameter bounds the generic argument
    // *below* the matching target parameter (the Invoke argument must be
    // assignable to it) and the return bounds it *above* the target's return.
    // Returns null when the arity pairing fails or a parameter has no candidate
    // satisfying every bound.
    private static List<TypeAnalysisContext>? SolveDelegateInstantiation(
        TypeAnalysisContext delegateDefinition, MethodAnalysisContext invoke,
        MethodAnalysisContext target, MethodAnalysisContext context,
        IReadOnlyList<TypeAnalysisContext>? fallbackArgs)
    {
        var genericParameterCount = delegateDefinition.GenericParameters.Count;
        var upperBounds = new List<TypeAnalysisContext>?[genericParameterCount];
        var lowerBounds = new List<TypeAnalysisContext>?[genericParameterCount];

        bool Bind(TypeAnalysisContext bound, bool upper, int index)
        {
            // Byrefs, pointers and void are not legal generic arguments.
            if (bound is ByRefTypeAnalysisContext or PointerTypeAnalysisContext
                || bound.FullName == "System.Void")
                return false;
            var bounds = upper ? upperBounds : lowerBounds;
            (bounds[index] ??= []).Add(bound);
            return true;
        }

        // invokeToTarget: the instantiated Invoke type must be assignable to the
        // target type (parameter positions); the reverse for the return type.
        bool Unify(TypeAnalysisContext invokeType, TypeAnalysisContext targetType, bool invokeToTarget)
        {
            switch (invokeType)
            {
                case GenericParameterTypeAnalysisContext { Type: Il2CppTypeEnum.IL2CPP_TYPE_VAR } parameter
                    when parameter.Index < genericParameterCount:
                    return Bind(targetType, invokeToTarget, parameter.Index);
                case GenericInstanceTypeAnalysisContext invokeInstance
                    when targetType is GenericInstanceTypeAnalysisContext targetInstance
                        && ThisConstructorCallPlan.SameTypeIdentity(invokeInstance.GenericType, targetInstance.GenericType)
                        && invokeInstance.GenericArguments.Count == targetInstance.GenericArguments.Count:
                    return invokeInstance.GenericArguments
                        .Zip(targetInstance.GenericArguments, (a, b) => Unify(a, b, invokeToTarget))
                        .All(result => result);
                case SzArrayTypeAnalysisContext invokeArray
                    when targetType is SzArrayTypeAnalysisContext targetArray:
                    return Unify(invokeArray.ElementType, targetArray.ElementType, invokeToTarget);
                case ByRefTypeAnalysisContext invokeByRef
                    when targetType is ByRefTypeAnalysisContext targetByRef:
                    return Unify(invokeByRef.ElementType, targetByRef.ElementType, invokeToTarget);
                case PointerTypeAnalysisContext invokePointer
                    when targetType is PointerTypeAnalysisContext targetPointer:
                    return Unify(invokePointer.ElementType, targetPointer.ElementType, invokeToTarget);
                default:
                    // A concrete leaf moves with no instantiation; the verifier's
                    // directional assignability is the entire check.
                    return invokeToTarget
                        ? LooseAssignable(invokeType, targetType)
                        : LooseAssignable(targetType, invokeType);
            }
        }

        var totalTargetArgs = target.Parameters.Count + (target.IsStatic ? 0 : 1);
        bool isOpen;
        if (totalTargetArgs == invoke.Parameters.Count)
            isOpen = true;
        else if (totalTargetArgs == invoke.Parameters.Count + 1)
            isOpen = false;
        else
            return null;

        var consumedArgs = isOpen ? 1 : 0;
        if (isOpen && totalTargetArgs != 0)
        {
            var firstTargetArgument = OpenDelegateFirstArgument(target);
            if (firstTargetArgument == null
                || !Unify(invoke.Parameters[0].ParameterType, firstTargetArgument, true))
                return null;
        }
        if (target.IsStatic)
            consumedArgs--;

        for (var i = isOpen ? 1 : 0; i < invoke.Parameters.Count; i++)
            if (!Unify(invoke.Parameters[i].ParameterType, target.Parameters[i - consumedArgs].ParameterType, true))
                return null;

        if (invoke.ReturnType.FullName == "System.Void" || target.ReturnType.FullName == "System.Void")
        {
            if (invoke.ReturnType.FullName != target.ReturnType.FullName)
                return null;
        }
        else if (!Unify(invoke.ReturnType, target.ReturnType, false))
            return null;

        var solved = new List<TypeAnalysisContext>(genericParameterCount);
        var objectType = context.AppContext.SystemTypes.SystemObjectType;
        for (var i = 0; i < genericParameterCount; i++)
        {
            var upper = upperBounds[i];
            var lower = lowerBounds[i];
            if (upper == null && lower == null)
            {
                // The parameter never reaches Invoke's signature; keep the
                // recovered argument when there is one.
                solved.Add(fallbackArgs != null && i < fallbackArgs.Count
                    ? fallbackArgs[i] : objectType);
                continue;
            }

            TypeAnalysisContext? pick = null;
            foreach (var candidate in (lower ?? []).Concat(upper ?? []))
            {
                if (!UsableDelegateArgument(candidate, context))
                    continue;
                if ((upper ?? []).All(bound => LooseAssignable(candidate, bound))
                    && (lower ?? []).All(bound => LooseAssignable(bound, candidate)))
                {
                    pick = candidate;
                    break;
                }
            }
            if (pick == null)
                return null;
            solved.Add(pick);
        }
        return solved;
    }

    private static bool UsableDelegateArgument(TypeAnalysisContext type, MethodAnalysisContext context) =>
        CanEmitTypeToken(type) && DelegateArgumentsCallerOwned(type, context);

    // A generic argument may reference the calling method's own generic
    // parameters (a generic caller building Action<T>), but never a foreign
    // owner's - the emitted index would silently rebind to the caller's
    // parameter at that slot.
    private static bool DelegateArgumentsCallerOwned(TypeAnalysisContext type, MethodAnalysisContext context) =>
        type switch
        {
            GenericParameterTypeAnalysisContext parameter => parameter.Type switch
            {
                // Reference equality alone is not enough: the owner's generic
                // container must actually cover the index, otherwise the emitted
                // signature names a slot that does not exist.
                Il2CppTypeEnum.IL2CPP_TYPE_VAR =>
                    ReferenceEquals(parameter.Owner, context.DeclaringType)
                    && parameter.Index < context.DeclaringType.GenericParameters.Count,
                Il2CppTypeEnum.IL2CPP_TYPE_MVAR =>
                    ReferenceEquals(parameter.Owner, context)
                    && parameter.Index < context.GenericParameters.Count,
                _ => false,
            },
            SzArrayTypeAnalysisContext array => DelegateArgumentsCallerOwned(array.ElementType, context),
            ArrayTypeAnalysisContext array => DelegateArgumentsCallerOwned(array.ElementType, context),
            WrappedTypeAnalysisContext wrapped => DelegateArgumentsCallerOwned(wrapped.ElementType, context),
            GenericInstanceTypeAnalysisContext instance =>
                instance.GenericArguments.All(argument => DelegateArgumentsCallerOwned(argument, context)),
            _ => true,
        };

    private static CilOpCode? FloatOperationConversion(Instruction instruction)
    {
        if (instruction.OpCode is not (OpCode.CheckEqual or OpCode.CheckGreater or OpCode.CheckLess
            or OpCode.CheckNotEqual or OpCode.CheckGreaterOrEqual or OpCode.CheckLessOrEqual
            or OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.Divide or OpCode.Modulo))
            return null;

        var resultType = (instruction.Operands[0] as LocalVariable)?.Type?.FullName;
        if (resultType is "System.Single")
            return CilOpCodes.Conv_R4;
        if (resultType is "System.Double")
            return CilOpCodes.Conv_R8;

        var operandType = instruction.Operands.Skip(1).Take(2)
            .Select(FloatOperandType)
            .FirstOrDefault(type => type != null);
        return operandType switch
        {
            "System.Single" => CilOpCodes.Conv_R4,
            "System.Double" => CilOpCodes.Conv_R8,
            _ => null,
        };
    }

    private static string? FloatOperandType(IOperand operand) => operand switch
    {
        FloatLiteral => "System.Single",
        DoubleLiteral => "System.Double",
        LocalVariable { Type.FullName: var type } when type is "System.Single" or "System.Double" => type,
        FieldReference { Field.FieldType.FullName: var type } when type is "System.Single" or "System.Double" => type,
        SelectedFieldReference { FieldType.FullName: var type } when type is "System.Single" or "System.Double" => type,
        _ => null,
    };

    private static void LoadOperand(IOperand operand, MethodDefinition method,
        Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine,
        TypeAnalysisContext? expectedType, MethodAnalysisContext callingContext)
    {
        var instructions = method.CilMethodBody!.Instructions;

        var module = method.DeclaringModule!;

        // A null reference reaches us as an integer zero, which would otherwise be emitted as a literal 0
        // and read back as a cast from a number. Runtime handle types lower to native int, where the
        // zero is an address, not a reference.
        // Byrefs, unmanaged pointers and generic parameters are not managed
        // references either; their zeroes are handled inside the switch.
        if (expectedType is { IsValueType: false } && IsZeroConstant(operand) && !IsNativeHandleType(expectedType)
            && expectedType is not (ByRefTypeAnalysisContext or PointerTypeAnalysisContext
                or GenericParameterTypeAnalysisContext))
        {
            instructions.Add(CilOpCodes.Ldnull);
            return;
        }

        // Enums share the stack type of their underlying primitive, so literal
        // emission keys off the underlying contract rather than the enum name.
        var literalType = expectedType is { IsEnumType: true }
            ? expectedType.DefaultEnumUnderlyingType ?? expectedType
            : expectedType;

        switch (operand)
        {
            case Immediate immediate when literalType?.FullName is "System.IntPtr" or "System.UIntPtr":
                if (immediate.Value is >= int.MinValue and <= int.MaxValue)
                    instructions.Add(CilOpCodes.Ldc_I4, (int)immediate.Value);
                else
                    instructions.Add(CilOpCodes.Ldc_I8, immediate.Value);
                instructions.Add(literalType.FullName == "System.UIntPtr" ? CilOpCodes.Conv_U : CilOpCodes.Conv_I);
                break;
            case Immediate immediate when literalType?.FullName == "System.Single":
                instructions.Add(CilOpCodes.Ldc_R4, (float)immediate.Value);
                break;
            case Immediate immediate when literalType?.FullName == "System.Double":
                instructions.Add(CilOpCodes.Ldc_R8, (double)immediate.Value);
                break;
            case Immediate immediate when literalType?.FullName is "System.Int64" or "System.UInt64":
                if (immediate.Value is >= int.MinValue and <= int.MaxValue)
                {
                    instructions.Add(CilOpCodes.Ldc_I4, (int)immediate.Value);
                    instructions.Add(literalType.FullName == "System.UInt64" ? CilOpCodes.Conv_U8 : CilOpCodes.Conv_I8);
                }
                else
                    instructions.Add(CilOpCodes.Ldc_I8, immediate.Value);
                break;
            // A native W-register literal may be represented as unsigned 32-bit or
            // wider in ISIL. The known narrow contract supplies the width.
            case Immediate immediate when literalType?.FullName is "System.Int32" or "System.UInt32"
                    or "System.Boolean" or "System.Byte" or "System.SByte"
                    or "System.Int16" or "System.UInt16" or "System.Char":
                if (immediate.Value is >= int.MinValue and <= uint.MaxValue)
                    instructions.Add(CilOpCodes.Ldc_I4, unchecked((int)immediate.Value));
                else
                {
                    // Only the low word reaches the managed slot, so keep the literal
                    // intact and let the conversion truncate instead of the emitter.
                    instructions.Add(CilOpCodes.Ldc_I8, immediate.Value);
                    instructions.Add(CilOpCodes.Conv_I4);
                }
                break;
            // ref/out/in slots need a managed pointer; a fresh local is the only
            // honest default, same as in PushDefaultOf. The element is sanitized
            // because the temp's declared type is a signature token too.
            case Immediate when literalType is ByRefTypeAnalysisContext byRefLiteral
                    && CanEmitTypeToken(byRefLiteral.ElementType):
                var byRefLocal = new CilLocalVariable(
                    EmittableLocalType(byRefLiteral.ElementType, callingContext).ToTypeSignature());
                method.CilMethodBody!.LocalVariables.Add(byRefLocal);
                instructions.Add(CilOpCodes.Ldloca, byRefLocal);
                break;
            // An unmanaged pointer accepts a native int, so a literal survives as
            // an address value rather than a broken null.
            case Immediate immediate when literalType is PointerTypeAnalysisContext:
                if (immediate.Value is >= int.MinValue and <= int.MaxValue)
                    instructions.Add(CilOpCodes.Ldc_I4, (int)immediate.Value);
                else
                    instructions.Add(CilOpCodes.Ldc_I8, immediate.Value);
                instructions.Add(CilOpCodes.Conv_I);
                break;
            // A literal in a non-primitive value-type or generic-parameter slot is a
            // dropped operand, not a real value; default(T) is the only honest filler.
            case Immediate when literalType is { IsValueType: true } or GenericParameterTypeAnalysisContext
                    && CanEmitTypeToken(literalType):
                EmitDefaultValueLocal(literalType, method, instructions, callingContext);
                break;
            case Immediate { Value: >= int.MinValue and <= int.MaxValue } immediate:
                instructions.Add(CilOpCodes.Ldc_I4, (int)immediate.Value);
                break;
            case Immediate immediate:
                instructions.Add(CilOpCodes.Ldc_I8, immediate.Value);
                break;
            case FloatLiteral f:
                instructions.Add(CilOpCodes.Ldc_R4, f.Value);
                break;
            case DoubleLiteral d:
                instructions.Add(CilOpCodes.Ldc_R8, d.Value);
                break;
            case Vector128Literal vector when literalType?.FullName == "System.Single":
                instructions.Add(CilOpCodes.Ldc_R4, vector.X);
                break;
            case Vector128Literal vector when literalType?.FullName is "System.Int32" or "System.UInt32":
                instructions.Add(CilOpCodes.Ldc_I4, System.BitConverter.SingleToInt32Bits(vector.X));
                break;
            case Vector128Literal vector when literalType?.FullName == "System.Double":
                var lowDoubleBits = (long)(uint)System.BitConverter.SingleToInt32Bits(vector.X)
                    | (long)System.BitConverter.SingleToInt32Bits(vector.Y) << 32;
                instructions.Add(CilOpCodes.Ldc_R8, System.BitConverter.Int64BitsToDouble(lowDoubleBits));
                break;
            case Vector128Literal vector:
                var componentCount = literalType?.DefaultFullName switch
                {
                    "UnityEngine.Vector2" => 2,
                    "UnityEngine.Vector3" => 3,
                    _ => 4,
                };
                var vectorConstructor = literalType?.Methods.FirstOrDefault(candidate =>
                    candidate is { IsStatic: false, Name: ".ctor" }
                    && candidate.Parameters.Count == componentCount
                    && candidate.Parameters.All(parameter => parameter.ParameterType.FullName == "System.Single"));
                if (vectorConstructor == null)
                {
                    instructions.Add(CilOpCodes.Ldstr, Diagnostic(
                        $"Cannot construct 128-bit constant as {literalType?.FullName ?? "unknown type"}"));
                    instructions.Add(CilOpCodes.Call, writeLine);
                    PushDefaultOf(literalType ?? callingContext.AppContext.SystemTypes.SystemObjectType,
                        method, instructions, callingContext);
                    break;
                }
                instructions.Add(CilOpCodes.Ldc_R4, vector.X);
                instructions.Add(CilOpCodes.Ldc_R4, vector.Y);
                if (componentCount >= 3)
                    instructions.Add(CilOpCodes.Ldc_R4, vector.Z);
                if (componentCount >= 4)
                    instructions.Add(CilOpCodes.Ldc_R4, vector.W);
                instructions.Add(CilOpCodes.Newobj, vectorConstructor.ToMethodDescriptor());
                break;
            case StringLiteral s:
                instructions.Add(CilOpCodes.Ldstr, s.Value);
                break;
            case LocalVariable local:
                LoadLocal(local, method, locals, callingContext);
                break;
            case ReferenceCast referenceCast:
                var castTarget = referenceCast.Type;
                var castValueType = EmittedOperandType(referenceCast.Value, callingContext);
                // A cast to the canonical shared instantiation is the lifter
                // mistyping the object; the instance the native code held is the
                // value's own instantiation.
                if (castTarget is GenericInstanceTypeAnalysisContext erasedCast
                    && erasedCast.GenericArguments.Any(ContainsErasedSharedArgument)
                    && castValueType is GenericInstanceTypeAnalysisContext valueInstance
                    && ThisConstructorCallPlan.SameTypeIdentity(valueInstance.GenericType, erasedCast.GenericType))
                    castTarget = valueInstance;
                if (!TypeTokenUsableFrom(castTarget, callingContext))
                {
                    // The target type cannot be named here (e.g. a shared-generic
                    // instantiation over a corlib-internal marker); a cast token for it
                    // would fail access checks, so the honest value is a default of the
                    // target type.
                    instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Inaccessible cast target: {referenceCast.Type.FullName}"));
                    instructions.Add(CilOpCodes.Call, writeLine);
                    PushDefaultOf(castTarget, method, instructions, callingContext);
                    break;
                }
                LoadLocal(referenceCast.Value, method, locals, callingContext);
                // A cast to the value's own type verifies without the opcode.
                if (!ThisConstructorCallPlan.SameTypeIdentity(castValueType, castTarget))
                    instructions.Add(referenceCast.NullOnFailure ? CilOpCodes.Isinst : CilOpCodes.Castclass,
                        castTarget.ToTypeSignature().ToTypeDefOrRef());
                break;
            case ArrayLength arrayLength:
                LoadArrayBase(arrayLength.Array, method, locals, callingContext);
                instructions.Add(CilOpCodes.Ldlen);
                instructions.Add(CilOpCodes.Conv_I4);
                break;
            case AddressOf { Target: LocalVariable addressed }:
                instructions.Add(CilOpCodes.Ldloca, locals[addressed]);
                break;
            case AddressOf { Target: FieldReference addressedField }:
                if (!FieldReferenceUsableFrom(addressedField, callingContext, writeAccess: true))
                {
                    // The field cannot legally be addressed here; a fresh zeroed
                    // local is the honest managed-address placeholder.
                    PushDefaultOf(new ByRefTypeAnalysisContext(addressedField.Field.FieldType),
                        method, instructions, callingContext);
                    break;
                }
                if (!addressedField.Field.IsStatic)
                    LoadFieldReceiver(addressedField, callingContext, method, locals, writeLine);
                instructions.Add(addressedField.Field.IsStatic ? CilOpCodes.Ldsflda : CilOpCodes.Ldflda,
                    addressedField.Field.IsStatic ? addressedField.Field.ToFieldDescriptor()
                        : FieldDescriptorFor(addressedField.Field,
                            FieldReceiverType(addressedField, callingContext)));
                break;
            case AddressOf { Target: ArrayAccess elementAddress }:
                var elementAddressType = ((SzArrayTypeAnalysisContext)elementAddress.Array.Type!).ElementType;
                if (!TypeTokenUsableFrom(elementAddressType, callingContext))
                {
                    instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Inaccessible array element type: {elementAddressType.FullName}"));
                    instructions.Add(CilOpCodes.Call, writeLine);
                    PushDefaultOf(new ByRefTypeAnalysisContext(elementAddressType), method, instructions, callingContext);
                    break;
                }
                LoadArrayBase(elementAddress.Array, method, locals, callingContext);
                LoadOperandIntoSlot(elementAddress.Index, callingContext.AppContext.SystemTypes.SystemInt32Type,
                    callingContext, method, locals, writeLine);
                instructions.Add(CilOpCodes.Ldelema, elementAddressType.ToTypeSignature().ToTypeDefOrRef());
                break;
            case AddressOf { Target: ArrayElementFieldReference elementFieldAddress }:
                var addressedArrayElementType = ((SzArrayTypeAnalysisContext)elementFieldAddress.Array.Type!).ElementType;
                if (!TypeTokenUsableFrom(addressedArrayElementType, callingContext)
                    || !FieldUsableFrom(elementFieldAddress.Field, callingContext, writeAccess: true,
                        receiverType: addressedArrayElementType))
                {
                    PushDefaultOf(new ByRefTypeAnalysisContext(elementFieldAddress.Field.FieldType),
                        method, instructions, callingContext);
                    break;
                }
                LoadArrayBase(elementFieldAddress.Array, method, locals, callingContext);
                LoadOperandIntoSlot(elementFieldAddress.Index, callingContext.AppContext.SystemTypes.SystemInt32Type,
                    callingContext, method, locals, writeLine);
                instructions.Add(CilOpCodes.Ldelema, addressedArrayElementType.ToTypeSignature().ToTypeDefOrRef());
                instructions.Add(CilOpCodes.Ldflda,
                    FieldDescriptorFor(elementFieldAddress.Field, addressedArrayElementType));
                break;
            case ArrayAccess arrayAccess:
                var arrayElementType = ((SzArrayTypeAnalysisContext)arrayAccess.Array.Type!).ElementType;
                if (!TypeTokenUsableFrom(arrayElementType, callingContext))
                {
                    instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Inaccessible array element type: {arrayElementType.FullName}"));
                    instructions.Add(CilOpCodes.Call, writeLine);
                    PushDefaultOf(arrayElementType, method, instructions, callingContext);
                    break;
                }
                LoadArrayBase(arrayAccess.Array, method, locals, callingContext);
                LoadOperandIntoSlot(arrayAccess.Index, callingContext.AppContext.SystemTypes.SystemInt32Type,
                    callingContext, method, locals, writeLine);
                if (LdelemOpCode(arrayElementType) is { } ldelemOpCode)
                    instructions.Add(ldelemOpCode);
                else
                    instructions.Add(CilOpCodes.Ldelem, arrayElementType.ToTypeSignature().ToTypeDefOrRef());
                break;
            case ArrayElementFieldReference elementField:
                var containingElementType = ((SzArrayTypeAnalysisContext)elementField.Array.Type!).ElementType;
                if (!TypeTokenUsableFrom(containingElementType, callingContext)
                    || !FieldUsableFrom(elementField.Field, callingContext, receiverType: containingElementType))
                {
                    PushDefaultOf(elementField.Field.FieldType, method, instructions, callingContext);
                    break;
                }
                LoadArrayBase(elementField.Array, method, locals, callingContext);
                LoadOperandIntoSlot(elementField.Index, callingContext.AppContext.SystemTypes.SystemInt32Type,
                    callingContext, method, locals, writeLine);
                instructions.Add(CilOpCodes.Ldelema, containingElementType.ToTypeSignature().ToTypeDefOrRef());
                instructions.Add(CilOpCodes.Ldfld, FieldDescriptorFor(elementField.Field, containingElementType));
                break;
            case FieldReference field:
                if (TryEmitInlinedEnumeratorCurrent(field, callingContext, method, locals, writeLine))
                    break;
                if (TryEmitInlinedListCount(field, callingContext, method, locals))
                    break;
                if (WholeValueContainerReference(field, expectedType) is { } wholeValue
                    && FieldReferenceUsableFrom(wholeValue, callingContext))
                {
                    if (wholeValue.Field.IsStatic)
                        instructions.Add(CilOpCodes.Ldsfld, wholeValue.Field.ToFieldDescriptor());
                    else
                    {
                        LoadFieldReceiver(wholeValue, callingContext, method, locals, writeLine);
                        instructions.Add(CilOpCodes.Ldfld,
                            FieldDescriptorFor(wholeValue.Field,
                                FieldReceiverType(wholeValue, callingContext)));
                    }
                    break;
                }
                if (!FieldReferenceUsableFrom(field, callingContext))
                {
                    PushDefaultOf(field.Field.FieldType, method, instructions, callingContext);
                    break;
                }
                if (field.Field.IsStatic)
                {
                    instructions.Add(CilOpCodes.Ldsfld, field.Field.ToFieldDescriptor());
                    break;
                }

                LoadFieldReceiver(field, callingContext, method, locals, writeLine);
                instructions.Add(CilOpCodes.Ldfld,
                    FieldDescriptorFor(field.Field, FieldReceiverType(field, callingContext)));
                break;
            case SelectedFieldReference selected:
                EmitSelectedFieldLoad(selected, method, locals, writeLine, expectedType, callingContext);
                break;
            case MemoryOperand memory:
                if (TryRecoverLateFieldReference(memory, callingContext, out var lateField))
                {
                    if (TryEmitInlinedListCount(lateField, callingContext, method, locals))
                        break;
                    LoadOperand(lateField, method, locals, writeLine, expectedType, callingContext);
                    break;
                }
                if (TryGetDeterministicMemoryReferent(memory, expectedType, out var referent))
                {
                    // A zero-offset load through a typed pointer/byref is an actual managed
                    // dereference. Everything else stays unresolved below: ISIL has no proof
                    // that an arbitrary native address or offset names a managed field.
                    if (referent is { IsValueType: true } && !TypeTokenUsableFrom(referent, callingContext))
                    {
                        instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Inaccessible dereference type: {referent.FullName}"));
                        instructions.Add(CilOpCodes.Call, writeLine);
                        PushDefaultOf(referent, method, instructions, callingContext);
                        break;
                    }
                    LoadLocal((LocalVariable)memory.Base!, method, locals, callingContext);
                    instructions.Add(referent switch
                    {
                        PointerTypeAnalysisContext or ByRefTypeAnalysisContext => new CilInstruction(CilOpCodes.Ldind_I),
                        { IsValueType: true } => new CilInstruction(CilOpCodes.Ldobj, referent.ToTypeSignature().ToTypeDefOrRef()),
                        _ => new CilInstruction(CilOpCodes.Ldind_Ref)
                    });
                    break;
                }
                instructions.Add(CilOpCodes.Ldstr, Diagnostic("Unmanaged memory load: " + operand));
                instructions.Add(CilOpCodes.Call, writeLine);
                var exceptionCtor = module.CorLibTypeFactory.CorLibScope
                    .CreateTypeReference("System", "Exception")
                    .CreateMemberReference(".ctor", MethodSignature.CreateInstance(module.CorLibTypeFactory.Void, [module.CorLibTypeFactory.String]));
                instructions.Add(CilOpCodes.Ldstr, Diagnostic("Unmanaged memory load: " + operand));
                instructions.Add(CilOpCodes.Newobj, exceptionCtor);
                instructions.Add(CilOpCodes.Throw);
                break;
            case RuntimeMethodInfoAnalysisContext runtimeMethod:
                // A delegate constructor takes its target as a native pointer, which is exactly ldftn.
                // ldftn cannot name a .ctor though; the unresolved placeholder below stays
                // verifier-legal (a native-int zero) instead of fabricating a function pointer.
                var represented = runtimeMethod.RepresentedMethod;
                var representedVisible = !CalleeUsesSharedEnumMarker(represented)
                    && (callingContext == null
                        || Analysis.InaccessibleCalleeRecovery.IsVisibleFrom(represented, callingContext));
                if (!representedVisible)
                {
                    // The same invisible corlib helpers show up as function pointers; the honest
                    // substitutes are the ones a direct call would use.
                    represented = Analysis.InaccessibleCalleeRecovery.TrySubstitute(represented) ?? represented;
                    representedVisible = !CalleeUsesSharedEnumMarker(represented)
                        && (callingContext == null
                            || Analysis.InaccessibleCalleeRecovery.IsVisibleFrom(represented, callingContext));
                }
                if (expectedType?.FullName == "System.IntPtr" && represented.Name is not ".ctor" && representedVisible)
                {
                    instructions.Add(CilOpCodes.Ldftn, represented.ToMethodDescriptor());
                    break;
                }
                if (expectedType?.FullName == "System.RuntimeMethodHandle" && representedVisible)
                {
                    instructions.Add(CilOpCodes.Ldtoken, represented.ToMethodDescriptor());
                    break;
                }

                //Not fully implemented, these basically shouldn't actually ever exist in the final IL.
                // A struct handle slot takes its default; everything else keeps the
                // native-int zero the handle wrapper lowers to.
                if (expectedType is { IsValueType: true }
                    && expectedType.FullName is not "System.IntPtr" and not "System.UIntPtr")
                    PushDefaultOf(expectedType, method, instructions, callingContext);
                else
                {
                    instructions.Add(CilOpCodes.Ldc_I4_0);
                    instructions.Add(CilOpCodes.Conv_I);
                }
                break;
            case RuntimeFieldInfoAnalysisContext runtimeField:
                // fieldof(F), e.g. the handle InitializeArray takes.
                if (expectedType?.FullName == "System.RuntimeFieldHandle")
                {
                    if (RuntimeFieldTokenUsableFrom(runtimeField.RepresentedField, callingContext))
                        instructions.Add(CilOpCodes.Ldtoken, runtimeField.RepresentedField.ToFieldDescriptor());
                    else
                        PushDefaultOf(expectedType, method, instructions, callingContext);
                    break;
                }

                instructions.Add(CilOpCodes.Ldc_I4_0);
                instructions.Add(CilOpCodes.Conv_I);
                break;
            case RuntimeClassTypeAnalysisContext runtimeClass when expectedType?.FullName == "System.RuntimeTypeHandle":
                if (TypeTokenUsableFrom(runtimeClass.RepresentedType, callingContext))
                    instructions.Add(CilOpCodes.Ldtoken, runtimeClass.RepresentedType.ToTypeSignature().ToTypeDefOrRef());
                else
                    PushDefaultOf(expectedType, method, instructions, callingContext);
                break;
            case RuntimeClassTypeAnalysisContext runtimeClass
                when expectedType?.FullName is "System.Type" or "System.Object":
                if (!TypeTokenUsableFrom(runtimeClass.RepresentedType, callingContext))
                {
                    PushDefaultOf(expectedType, method, instructions, callingContext);
                    break;
                }
                // The native arg is a klass*; the managed contract wants the Type object for it.
                instructions.Add(CilOpCodes.Ldtoken, runtimeClass.RepresentedType.ToTypeSignature().ToTypeDefOrRef());
                instructions.Add(CilOpCodes.Call, module.CorLibTypeFactory.CorLibScope
                    .CreateTypeReference("System", "Type")
                    .CreateMemberReference("GetTypeFromHandle",
                        MethodSignature.CreateStatic(
                            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "Type").ToTypeSignature(true),
                            [module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "RuntimeTypeHandle").ToTypeSignature(true)])));
                break;
            case RuntimeClassTypeAnalysisContext or RgctxTableTypeAnalysisContext
                or MethodRgctxTableTypeAnalysisContext or StaticFieldStorageTypeAnalysisContext:
                instructions.Add(CilOpCodes.Ldc_I4_0);
                instructions.Add(CilOpCodes.Conv_I);
                break;
            case TypeAnalysisContext type:
                var corLibScope = module.CorLibTypeFactory.CorLibScope;
                var runtimeTypeHandle = corLibScope.CreateTypeReference("System", "RuntimeTypeHandle");

                if (expectedType?.FullName == "System.RuntimeTypeHandle")
                {
                    if (TypeTokenUsableFrom(type, callingContext))
                        instructions.Add(CilOpCodes.Ldtoken, type.ToTypeSignature().ToTypeDefOrRef());
                    else
                        PushDefaultOf(expectedType, method, instructions, callingContext);
                    break;
                }

                if (expectedType?.FullName is "System.IntPtr" or "System.UIntPtr"
                    || expectedType is RuntimeClassTypeAnalysisContext)
                {
                    if (!TypeTokenUsableFrom(type, callingContext))
                    {
                        // The honest value of an unnameable handle is the null address.
                        instructions.Add(CilOpCodes.Ldc_I4_0);
                        instructions.Add(CilOpCodes.Conv_I);
                        break;
                    }
                    var handleLocal = new CilLocalVariable(runtimeTypeHandle.ToTypeSignature(true));
                    method.CilMethodBody!.LocalVariables.Add(handleLocal);
                    var getValue = runtimeTypeHandle.CreateMemberReference("get_Value",
                        MethodSignature.CreateInstance(corLibScope.CreateTypeReference("System", "IntPtr").ToTypeSignature(true)));
                    instructions.Add(CilOpCodes.Ldtoken, type.ToTypeSignature().ToTypeDefOrRef());
                    instructions.Add(CilOpCodes.Stloc, handleLocal);
                    instructions.Add(CilOpCodes.Ldloca, handleLocal);
                    instructions.Add(CilOpCodes.Call, getValue);
                    break;
                }

                // typeof(T)
                var typeFromHandle = corLibScope
                    .CreateTypeReference("System", "Type")
                    .CreateMemberReference("GetTypeFromHandle", MethodSignature.CreateStatic(
                        corLibScope.CreateTypeReference("System", "Type").ToTypeSignature(false),
                        [runtimeTypeHandle.ToTypeSignature(true)]));

                if (TypeTokenUsableFrom(type, callingContext))
                {
                    instructions.Add(CilOpCodes.Ldtoken, type.ToTypeSignature().ToTypeDefOrRef());
                    instructions.Add(CilOpCodes.Call, typeFromHandle);
                }
                else
                    instructions.Add(CilOpCodes.Ldnull);
                break;
            default:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic("Unknown operand: " + operand));
                instructions.Add(CilOpCodes.Call, writeLine);
                instructions.Add(CilOpCodes.Ldnull);
                break;
        }
    }

    private static TypeAnalysisContext? FieldReceiverType(FieldReference field, MethodAnalysisContext context) =>
        field.Containers.Count == 0 ? EmittedOperandType(field.Local, context) : field.Containers[^1].FieldType;

    private static bool FieldReferenceUsableFrom(FieldReference field, MethodAnalysisContext context,
        bool writeAccess = false)
    {
        var receiverType = EmittedOperandType(field.Local, context);
        foreach (var container in field.Containers)
        {
            if (!FieldUsableFrom(container, context, receiverType: receiverType))
                return false;
            receiverType = container.FieldType;
        }
        return FieldUsableFrom(field.Field, context, writeAccess,
            receiverType: field.Field.IsStatic ? null : receiverType);
    }

    private static void EmitSelectedFieldLoad(SelectedFieldReference selected, MethodDefinition method,
        Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine,
        TypeAnalysisContext? expectedType, MethodAnalysisContext context)
    {
        var instructions = method.CilMethodBody!.Instructions;
        var end = new CilInstruction(CilOpCodes.Nop);
        var branches = new List<((long Value, FieldReference Field) Choice, CilInstruction Target)>();
        for (var i = 0; i < selected.Choices.Count - 1; i++)
            branches.Add((selected.Choices[i], new CilInstruction(CilOpCodes.Nop)));

        foreach (var (choice, target) in branches)
        {
            LoadOperandIntoSlot(selected.Selector, context.AppContext.SystemTypes.SystemInt64Type,
                context, method, locals, writeLine);
            instructions.Add(CilOpCodes.Ldc_I8, choice.Value);
            instructions.Add(CilOpCodes.Beq, new CilInstructionLabel(target));
        }

        LoadOperand(selected.Choices[^1].Field, method, locals, writeLine, expectedType, context);
        instructions.Add(CilOpCodes.Br, new CilInstructionLabel(end));
        foreach (var (choice, target) in branches)
        {
            instructions.Add(target);
            LoadOperand(choice.Field, method, locals, writeLine, expectedType, context);
            instructions.Add(CilOpCodes.Br, new CilInstructionLabel(end));
        }
        instructions.Add(end);
    }

    private static void LoadFieldReceiver(FieldReference field, MethodAnalysisContext context, MethodDefinition method,
        Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine)
    {
        void LoadBase(FieldAnalysisContext target)
        {
            var contract = FieldBaseContract(target);
            if (!context.IsStatic && target.DeclaringType != null && context.DeclaringType != null
                && ThisConstructorCallPlan.SameTypeIdentity(GenericDefinition(target.DeclaringType),
                    GenericDefinition(context.DeclaringType))
                && (!StackContractSatisfied(EmittedOperandType(field.Local, context), contract, context)
                    || IsUndefinedOwnTypeReceiver(field.Local, context)))
            {
                method.CilMethodBody!.Instructions.Add(CilOpCodes.Ldarg_0);
                return;
            }
            if (contract is ByRefTypeAnalysisContext)
            {
                if (!EmitManagedAddress(field.Local, method, context, locals, writeLine))
                    PushDefaultOf(contract, method, method.CilMethodBody!.Instructions, context);
            }
            else
                LoadOperandIntoSlot(field.Local, contract, context, method, locals, writeLine);
        }

        if (field.Containers.Count == 0)
        {
            LoadBase(field.Field);
            return;
        }

        var receiverType = EmittedOperandType(field.Local, context);
        var first = field.Containers[0];
        var start = 0;
        if (first.IsStatic)
        {
            method.CilMethodBody!.Instructions.Add(CilOpCodes.Ldsflda, first.ToFieldDescriptor());
            receiverType = first.FieldType;
            start = 1;
        }
        else
            LoadBase(first);
        foreach (var container in field.Containers.Skip(start))
        {
            method.CilMethodBody!.Instructions.Add(CilOpCodes.Ldflda,
                FieldDescriptorFor(container, receiverType));
            receiverType = container.FieldType;
        }
    }

    private static bool IsUndefinedOwnTypeReceiver(IOperand receiver, MethodAnalysisContext context) =>
        receiver is LocalVariable local
        && !local.IsThis
        && !context.ParameterLocals.Contains(local)
        && context.ControlFlowGraph?.Instructions.All(instruction =>
            !ReferenceEquals(instruction.Destination, local)) == true;
    
    private static bool TryEmitExactTypeComparison(Instruction instruction, MethodDefinition method,
        Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine,
        MethodAnalysisContext context)
    {
        var left = instruction.Operands[1];
        var right = instruction.Operands[2];

        IOperand typeOperand;
        LocalVariable objLocal;

        if (left is TypeAnalysisContext && IsKlassPointerLoad(right, out var rightLocal))
            (typeOperand, objLocal) = (left, rightLocal);
        else if (right is TypeAnalysisContext && IsKlassPointerLoad(left, out var leftLocal))
            (typeOperand, objLocal) = (right, leftLocal);
        else
            return false;

        var module = method.DeclaringModule!;
        if (typeOperand is TypeAnalysisContext comparedType && !TypeTokenUsableFrom(comparedType, context))
        {
            // The compared type cannot be named here; there is no honest constant for
            // `obj.GetType() == typeof(T)`, so the operation is unrecoverable.
            EmitUnrecoverableOperation(method, writeLine,
                $"Inaccessible compared type: {comparedType.FullName}");
            return true;
        }
        var instructions = method.CilMethodBody!.Instructions;

        var getType = module.CorLibTypeFactory.CorLibScope
            .CreateTypeReference("System", "Object")
            .CreateMemberReference("GetType", MethodSignature.CreateInstance(
                module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "Type").ToTypeSignature(false)));

        LoadLocal(objLocal, method, locals, context);
        // GetType is a reference-type member: a generic or value-typed operand
        // reaches it only through box.
        CoerceOrDefault(EmittedLocalType(objLocal, context), context?.AppContext.SystemTypes.SystemObjectType, method, context);
        instructions.Add(CilOpCodes.Callvirt, getType);
        LoadOperand(typeOperand, method, locals, writeLine,
            ResolveSystemType(context, "System.Type"), context); // emits typeof(T)
        instructions.Add(CilOpCodes.Ceq);

        if (instruction.OpCode == OpCode.CheckNotEqual)
        {
            instructions.Add(CilOpCodes.Ldc_I4_0);
            instructions.Add(CilOpCodes.Ceq);
        }

        EmitStackCoerceOrDefault(context.AppContext.SystemTypes.SystemInt32Type,
            StoreContract(instruction.Operands[0], context), method, context);
        StoreToOperand(instruction.Operands[0], method, locals, writeLine, context);
        return true;
    }
    
    private static bool IsKlassPointerLoad(IOperand operand, out LocalVariable local)
    {
        if (operand is MemoryOperand { Index: null, Addend: 0, Scale: 0, Base: LocalVariable { Type.IsValueType: false } baseLocal })
        {
            local = baseLocal;
            return true;
        }

        local = null!;
        return false;
    }

    private static bool TryGetDeterministicMemoryReferent(MemoryOperand memory, TypeAnalysisContext? expectedType,
        out TypeAnalysisContext referent)
    {
        referent = null!;
        if (memory.Index != null || memory.Addend != 0 || memory.Scale != 0
            || memory.Base is not LocalVariable { Type: ByRefTypeAnalysisContext or PointerTypeAnalysisContext } local
            || local.Type is not WrappedTypeAnalysisContext pointer)
            return false;

        referent = pointer.ElementType;
        if (referent is GenericParameterTypeAnalysisContext || expectedType is GenericParameterTypeAnalysisContext)
            return false;

        if (expectedType is null)
            return true;

        if (referent is PointerTypeAnalysisContext or ByRefTypeAnalysisContext
            || expectedType is PointerTypeAnalysisContext or ByRefTypeAnalysisContext)
            return referent.FullName == expectedType.FullName;

        return referent.IsValueType == expectedType.IsValueType
            && (referent.IsValueType
                ? referent.FullName == expectedType.FullName
                : referent.IsAssignableTo(expectedType));
    }

    private static bool TryRecoverLateFieldReference(MemoryOperand memory, MethodAnalysisContext context,
        out FieldReference fieldReference)
    {
        fieldReference = null!;
        if (memory.Index != null || memory.Scale != 0 || memory.Base is not LocalVariable local)
            return false;

        if (local.Type != context.AppContext.SystemTypes.SystemObjectType
            || (CallDefinedLocalType(local, context) ?? ObjectDefinitionType(local, context)) is not { } owner
            || owner == context.AppContext.SystemTypes.SystemObjectType)
            return false;
        var field = Analysis.MetadataResolver.FindInstanceFieldAtOffset(owner, memory.Addend);
        if (field == null)
            return false;
        if (owner is GenericInstanceTypeAnalysisContext genericOwner)
            field = new ConcreteGenericFieldAnalysisContext(field, genericOwner);
        fieldReference = new FieldReference(field, local, (int)memory.Addend);
        return true;
    }

    private static bool TryEmitInlinedListCount(FieldReference field, MethodAnalysisContext context,
        MethodDefinition method, Dictionary<LocalVariable, CilLocalVariable> locals)
    {
        if (field is not { Field.Name: "_size", Local: LocalVariable receiver }
            || EmittedLocalType(receiver, context) is not GenericInstanceTypeAnalysisContext list
            || list.GenericType.FullName != "System.Collections.Generic.List`1"
            || list.GenericType.Methods.FirstOrDefault(candidate => candidate.Name == "get_Count"
                && !candidate.IsStatic && candidate.Parameters.Count == 0) is not { } getter)
            return false;

        LoadLocal(receiver, method, locals, context);
        method.CilMethodBody!.Instructions.Add(CilOpCodes.Call,
            new ConcreteGenericMethodAnalysisContext(getter, list.GenericArguments, []).ToMethodDescriptor());
        return true;
    }

    private static bool TryEmitInlinedEnumeratorCurrent(FieldReference field, MethodAnalysisContext context,
        MethodDefinition method, Dictionary<LocalVariable, CilLocalVariable> locals,
        IMethodDescriptor writeLine)
    {
        var current = field.Field.Name == "_current" && field.Containers.Count == 0
            ? field.Field
            : field.Containers.FirstOrDefault();
        if (current?.Name != "_current"
            || EmittedLocalType(field.Local, context) is not GenericInstanceTypeAnalysisContext enumerator
            || enumerator.GenericType.Methods.FirstOrDefault(candidate => candidate.Name == "get_Current"
                && !candidate.IsStatic && candidate.Parameters.Count == 0) is not { } getter)
            return false;

        var currentType = current.FieldType;
        var nestedReceiverType = field.Containers.Count == 1
            ? currentType
            : field.Containers.LastOrDefault()?.FieldType;
        var nestedGetter = field.Containers.Count > 0 && nestedReceiverType != null
            ? PublicFieldGetter(nestedReceiverType, field.Field)
            : null;
        if (field.Containers.Count > 0
            && (!TypeTokenUsableFrom(currentType, context)
                || field.Containers.Skip(1).Any(container => !FieldUsableFrom(container, context))
                || !FieldUsableFrom(field.Field, context, receiverType: nestedReceiverType)
                && nestedGetter == null))
            return false;
        if (!EmitManagedAddress(field.Local, method, context, locals, writeLine))
            return false;

        var concreteGetter = new ConcreteGenericMethodAnalysisContext(getter, enumerator.GenericArguments, []);
        var instructions = method.CilMethodBody!.Instructions;
        instructions.Add(CilOpCodes.Call, concreteGetter.ToMethodDescriptor());
        if (field.Containers.Count == 0)
            return true;

        var temp = new CilLocalVariable(currentType.ToTypeSignature());
        method.CilMethodBody.LocalVariables.Add(temp);
        instructions.Add(CilOpCodes.Stloc, temp);
        instructions.Add(CilOpCodes.Ldloca, temp);
        var receiverType = currentType;
        foreach (var container in field.Containers.Skip(1))
        {
            instructions.Add(CilOpCodes.Ldflda, FieldDescriptorFor(container, receiverType));
            receiverType = container.FieldType;
        }
        if (nestedGetter != null)
            instructions.Add(CilOpCodes.Call, nestedGetter.ToMethodDescriptor());
        else
            instructions.Add(CilOpCodes.Ldfld, FieldDescriptorFor(field.Field, receiverType));
        return true;
    }

    private static MethodAnalysisContext? PublicFieldGetter(TypeAnalysisContext receiver,
        FieldAnalysisContext field)
    {
        var name = field.Name;
        if (name.StartsWith("<", System.StringComparison.Ordinal)
            && name.IndexOf('>') is var end && end > 1)
            name = name[1..end];
        else if (name.Length > 0)
            name = char.ToUpperInvariant(name[0]) + name[1..];
        var definition = receiver is GenericInstanceTypeAnalysisContext generic
            ? generic.GenericType
            : receiver;
        var getter = definition.Methods.FirstOrDefault(candidate => candidate.Name == $"get_{name}"
            && !candidate.IsStatic && candidate.Parameters.Count == 0
            && (candidate.Attributes & MethodAttributes.MemberAccessMask) == MethodAttributes.Public);
        return getter == null ? null
            : receiver is GenericInstanceTypeAnalysisContext instance
                ? new ConcreteGenericMethodAnalysisContext(getter, instance.GenericArguments, [])
                : getter;
    }

    private static void PushDefaultOf(TypeAnalysisContext type, MethodDefinition method, CilInstructionCollection instructions,
        MethodAnalysisContext? context)
    {
        //TODO Remove this, we should be handling arguments correctly in ISIL resolution, this is a hack to emit balanced stacks.
        //TODO At the *very* least we should emit a console.writeline saying that we did this.
        if (type is ByRefTypeAnalysisContext byRefParameter)
        {
            // ref/out/in slots need a managed pointer; a fresh local is the only
            // honest default - the callee may write through it and the result is
            // dropped, same as any other placeholder. The element is sanitized for
            // the same reason locals are: the temp's declared type is a signature
            // token too.
            var elementType = EmittableLocalType(byRefParameter.ElementType, context);
            if (TypeTokenUsableFrom(elementType, context))
            {
                var tempLocal = new CilLocalVariable(elementType.ToTypeSignature());
                method.CilMethodBody!.LocalVariables.Add(tempLocal);
                instructions.Add(CilOpCodes.Ldloca, tempLocal);
            }
            else
                instructions.Add(CilOpCodes.Ldc_I4_0, 0);
            return;
        }

        // An unmanaged pointer slot takes a native-int zero (the honest null address);
        // ldnull below would be a reference, not a pointer.
        if (type is PointerTypeAnalysisContext)
        {
            instructions.Add(CilOpCodes.Ldc_I4_0);
            instructions.Add(CilOpCodes.Conv_I);
            return;
        }

        // default(T) on a generic parameter is initobj on a T local - the same
        // emission the compiler uses - because ldnull is only legal for reference Ts.
        if (type is GenericParameterTypeAnalysisContext && CanEmitTypeToken(type))
        {
            EmitDefaultValueLocal(type, method, instructions, context);
            return;
        }

        if (!type.IsValueType)
        {
            instructions.Add(CilOpCodes.Ldnull);
            return;
        }

        switch (type.FullName)
        {
            case "System.Single": instructions.Add(CilOpCodes.Ldc_R4, 0f); break;
            case "System.Double": instructions.Add(CilOpCodes.Ldc_R8, 0d); break;
            case "System.Int64" or "System.UInt64": instructions.Add(CilOpCodes.Ldc_I8, 0L); break;
            case "System.IntPtr": instructions.Add(CilOpCodes.Ldc_I4_0); instructions.Add(CilOpCodes.Conv_I); break;
            case "System.UIntPtr": instructions.Add(CilOpCodes.Ldc_I4_0); instructions.Add(CilOpCodes.Conv_U); break;
            // The small integral types share the i4 stack kind; a literal zero is the
            // cheapest default and verifies the same as an initobj temp.
            case "System.Int32" or "System.UInt32" or "System.Boolean" or "System.Byte"
                or "System.SByte" or "System.Int16" or "System.UInt16" or "System.Char":
                instructions.Add(CilOpCodes.Ldc_I4_0);
                break;
            default:
                if (CanEmitTypeToken(type) || HasEmittedLocalOfType(type, method))
                    EmitDefaultValueLocal(type, method, instructions, context);
                else
                    instructions.Add(CilOpCodes.Ldc_I4_0);
                break;
        }
    }

    // `newobj .ctor()` fails to resolve on types that do not declare one explicitly
    // (the verifier will not invent the implicit struct ctor), so default(T) goes
    // through a zero-initialized temp local instead.
    private static void EmitDefaultValueLocal(TypeAnalysisContext type, MethodDefinition method,
        CilInstructionCollection instructions, MethodAnalysisContext? context)
    {
        if (!TypeTokenUsableFrom(type, context) && !HasEmittedLocalOfType(type, method))
        {
            // initobj would name a type the caller cannot see, and the temp local
            // would carry the same invalid signature; the sanitized placeholder
            // keeps the same shape (int32 for marker structs, ldnull for references).
            PushDefaultOf(EmittableLocalType(type, context), method, instructions, context);
            return;
        }
        var signature = type.ToTypeSignature();
        var tempLocal = new CilLocalVariable(signature);
        method.CilMethodBody!.LocalVariables.Add(tempLocal);
        instructions.Add(CilOpCodes.Ldloca, tempLocal);
        instructions.Add(CilOpCodes.Initobj, signature.ToTypeDefOrRef());
        instructions.Add(CilOpCodes.Ldloc, tempLocal);
    }

    private static bool HasEmittedLocalOfType(TypeAnalysisContext type, MethodDefinition method)
    {
        if (method.CilMethodBody == null)
            return false;
        TypeSignature signature;
        try
        {
            signature = type.ToTypeSignature();
        }
        catch
        {
            return false;
        }
        return method.CilMethodBody.LocalVariables.Any(local =>
            local.VariableType.FullName == signature.FullName);
    }

    // A local's declared type is part of the method body's locals signature, so it
    // is subject to the same accessibility rules as an instruction token. When the
    // recovered type cannot be named here, declare the closest verifier-legal
    // shape instead: the same wrapper over a sanitized element for arrays and
    // byrefs (so element and pointer ops still resolve), the enum's underlying
    // primitive for marker structs, a native int for unmanaged pointers, and
    // object for anything else.
    private static TypeAnalysisContext EmittableLocalType(TypeAnalysisContext type, MethodAnalysisContext? context)
    {
        // IL2CPP's shared-generic enum markers are absent from Unity's managed
        // runtime. Concrete evidence is sharpened before this point; unresolved
        // occurrences keep their wrapper shape over the underlying primitive.
        if (IsSharedEnumMarker(type))
            return type.DefaultEnumUnderlyingType ?? type.AppContext.SystemTypes.SystemInt32Type;
        if (type is SzArrayTypeAnalysisContext markerArray
            && ContainsSharedEnumMarker(markerArray.ElementType))
            return new SzArrayTypeAnalysisContext(EmittableLocalType(markerArray.ElementType, context));
        if (type is ByRefTypeAnalysisContext markerByRef
            && ContainsSharedEnumMarker(markerByRef.ElementType))
            return new ByRefTypeAnalysisContext(EmittableLocalType(markerByRef.ElementType, context));
        if (type is PointerTypeAnalysisContext markerPointer
            && ContainsSharedEnumMarker(markerPointer.ElementType))
            return new PointerTypeAnalysisContext(EmittableLocalType(markerPointer.ElementType, context));
        if (type is GenericInstanceTypeAnalysisContext markerInstance
            && markerInstance.GenericArguments.Any(ContainsSharedEnumMarker))
            return new GenericInstanceTypeAnalysisContext(markerInstance.GenericType,
                markerInstance.GenericArguments.Select(argument => EmittableLocalType(argument, context)).ToArray());
        // Only a type that produces a token but names something the caller cannot
        // see needs the placeholder; anything unemittable keeps the existing
        // behavior (the corlib-signature special cases and the literal defaults).
        // A generic parameter is the method's own type variable: ldarg/stloc
        // signatures name it directly, and no placeholder could stand in for it.
        if (type is GenericParameterTypeAnalysisContext)
            return context == null || DelegateArgumentsCallerOwned(type, context)
                ? type
                : context.AppContext.SystemTypes.SystemObjectType;
        if (context?.DeclaringType == null
            || !CanEmitTypeToken(type)
            || (Analysis.InaccessibleCalleeRecovery.IsVisibleType(type, context.DeclaringType)
                && DelegateArgumentsCallerOwned(type, context)))
            return type;
        return type switch
        {
            SzArrayTypeAnalysisContext array =>
                new SzArrayTypeAnalysisContext(EmittableLocalType(array.ElementType, context)),
            ByRefTypeAnalysisContext byRef =>
                new ByRefTypeAnalysisContext(EmittableLocalType(byRef.ElementType, context)),
            PointerTypeAnalysisContext => context.AppContext.SystemTypes.SystemIntPtrType,
            { IsValueType: true } => type is { IsEnumType: true }
                && type.DefaultEnumUnderlyingType is { } underlying
                    ? EmittableLocalType(underlying, context)
                    : context.AppContext.SystemTypes.SystemInt32Type,
            _ => context.AppContext.SystemTypes.SystemObjectType,
        };
    }

    private static bool IsBoolean(IOperand operand, MethodAnalysisContext context) =>
        DestinationType(operand) == context.AppContext.SystemTypes.SystemBooleanType;

    // The stack type `ldloc`/`stloc` actually produces: the analysis type mapped
    // through the same placeholder rules the locals signature used. A local whose
    // recovered type the caller cannot name (e.g. a generic instantiation over a
    // corlib-internal marker) is declared object/int instead, and every contract
    // check has to see that emitted type rather than the unnameable analysis one.
    // A local tagged with the canonical shared instantiation
    // (PersistentMap<object,object>) is recovered from the instantiation its
    // definitions actually produce - a call's instantiated return, or the value
    // a mistyped cast was applied to.
    private static TypeAnalysisContext? SharpenedLocalInstanceType(
        LocalVariable local, GenericInstanceTypeAnalysisContext erasedInstance,
        MethodAnalysisContext context, HashSet<LocalVariable> visited)
    {
        if (!visited.Add(local) || context.ControlFlowGraph == null)
            return null;
        foreach (var instruction in context.ControlFlowGraph.Instructions)
        {
            if (!ReferenceEquals(instruction.Destination, local))
                continue;
            foreach (var produced in ProducedInstanceTypes(instruction, context, visited))
            {
                if (produced is SzArrayTypeAnalysisContext array
                    && erasedInstance.GenericType.FullName == "System.Collections.Generic.IEnumerable`1"
                    && !ContainsUnusableSharpenedArgument(array.ElementType, context))
                    return new GenericInstanceTypeAnalysisContext(erasedInstance.GenericType, [array.ElementType]);
                if (produced is GenericInstanceTypeAnalysisContext producedInstance
                    && ThisConstructorCallPlan.SameTypeIdentity(producedInstance.GenericType, erasedInstance.GenericType)
                    && !ThisConstructorCallPlan.SameTypeIdentity(producedInstance, erasedInstance)
                    && !producedInstance.GenericArguments.Any(argument =>
                        ContainsUnusableSharpenedArgument(argument, context)))
                    return producedInstance;
            }
        }

        // An allocation can be lifted through an erased temporary (`List<object>`)
        // even though its next managed store proves the concrete instantiation.
        // Use that slot contract only when every concrete use agrees.
        GenericInstanceTypeAnalysisContext? useContract = null;
        bool AcceptUseContract(GenericInstanceTypeAnalysisContext candidate)
        {
            if (!ThisConstructorCallPlan.SameTypeIdentity(candidate.GenericType, erasedInstance.GenericType)
                || candidate.GenericArguments.Any(argument =>
                    ContainsUnusableSharpenedArgument(argument, context)))
                return true;
            if (useContract != null && !ThisConstructorCallPlan.SameTypeIdentity(useContract, candidate))
                return false;
            useContract = candidate;
            return true;
        }

        foreach (var instruction in context.ControlFlowGraph.Instructions)
        {
            if (instruction is not { OpCode: OpCode.Move, Operands: [var destination, var source, ..] }
                || !ReferenceEquals(source, local)
                || DestinationType(destination) is not GenericInstanceTypeAnalysisContext candidate)
                continue;
            if (!AcceptUseContract(candidate))
                return null;
        }
        foreach (var cast in context.ControlFlowGraph.Instructions.SelectMany(instruction => instruction.Operands)
                     .OfType<ReferenceCast>().Where(cast => ReferenceEquals(cast.Value, local)))
            if (cast.Type is GenericInstanceTypeAnalysisContext candidate && !AcceptUseContract(candidate))
                return null;
        if (useContract != null)
            return useContract;
        return null;
    }

    private static bool ContainsUnusableSharpenedArgument(TypeAnalysisContext argument,
        MethodAnalysisContext context) =>
        IsSharedEnumMarker(argument)
        || argument is GenericParameterTypeAnalysisContext
            && !DelegateArgumentsCallerOwned(argument, context)
        || argument is WrappedTypeAnalysisContext wrapped
            && ContainsUnusableSharpenedArgument(wrapped.ElementType, context)
        || argument is GenericInstanceTypeAnalysisContext instance
            && instance.GenericArguments.Any(nested => ContainsUnusableSharpenedArgument(nested, context));

    private static IEnumerable<TypeAnalysisContext> ProducedInstanceTypes(
        Instruction instruction, MethodAnalysisContext context, HashSet<LocalVariable> visited)
    {
        if (instruction.Operands is [MethodAnalysisContext callee, ..] && !callee.IsVoid)
            yield return callee.ReturnType;
        foreach (var operand in instruction.Operands.Skip(1))
        {
            switch (operand)
            {
                case TypeAnalysisContext producedType when instruction.OpCode == OpCode.Newobj:
                    yield return producedType;
                    break;
                case ReferenceCast referenceCast:
                    yield return EmittedOperandType(referenceCast.Value, context);
                    break;
                case LocalVariable source:
                    // EmittedOperandType would recurse through the same sharpening
                    // with a fresh visited-set; keep the cycle guard instead.
                    yield return DirectCallDefinedLocalType(source, context)
                        ?? (source.Type is GenericInstanceTypeAnalysisContext sourceInstance
                        && sourceInstance.GenericArguments.Any(ContainsErasedSharedArgument)
                        ? SharpenedLocalInstanceType(source, sourceInstance, context, visited)
                        : source.Type);
                    break;
                default:
                    yield return EmittedOperandType(operand, context);
                    break;
            }
        }
    }

    internal static TypeAnalysisContext EmittedLocalType(LocalVariable local, MethodAnalysisContext context) =>
        EmittableLocalType(EmittedLocalTypeCore(local, context, []), context);

    private static TypeAnalysisContext? SharpenedFieldAddressType(LocalVariable local,
        MethodAnalysisContext context)
    {
        TypeAnalysisContext? fieldType = null;
        var found = false;
        foreach (var instruction in context.ControlFlowGraph!.Instructions)
        {
            if (!ReferenceEquals(instruction.Destination, local))
                continue;
            var address = instruction.OpCode is OpCode.Add or OpCode.Subtract
                ? TryResolveFieldAddressArithmetic(instruction, context)
                : null;
            if (address == null || fieldType != null
                && !ThisConstructorCallPlan.SameTypeIdentity(fieldType, address.Field.FieldType))
                return null;
            fieldType = address.Field.FieldType;
            found = true;
        }
        return found && fieldType != null ? new ByRefTypeAnalysisContext(fieldType) : null;
    }

    private static TypeAnalysisContext EmittedLocalTypeCore(LocalVariable local, MethodAnalysisContext context, HashSet<LocalVariable> visited)
    {
        // `ldarg` always pushes the declared parameter type: when the lifter tagged the
        // parameter local with a different type (register reuse packs a Vector3 arg onto a
        // later parameter register) the declared signature is what the verifier sees.
        // The match is by the parameter's own register local - a scratch local that
        // merely shares a parameter's name (`v2 @ X8` vs parameter `v2 @ V3`) is not
        // the argument and keeps its own type.
        if (!local.IsThis && !local.IsMethodInfo
            && context.ParameterLocals.Contains(local)
            && context.Parameters.FirstOrDefault(p => p.ParameterName == local.Name) is { } parameter)
            return IsNativeHandleType(parameter.ParameterType)
                ? context.AppContext.SystemTypes.SystemIntPtrType
                : parameter.ParameterType;
        // `this` loads use ldarg.0, whose stack type is the declaring type (a managed
        // pointer to it for value-type methods) - even when the lifter tagged the
        // local with the bare struct type, the address is what lands on the stack.
        // On a generic type `this` verifies as the self-instantiation def<!0..!n>,
        // which is what the local analysis stored - prefer it over the bare def.
        // A static method has no `this`: an X0 local the lifter tagged IsThis there
        // is an ordinary parameter and keeps its declared parameter type.
        if (local.IsThis && !context.IsStatic && context.DeclaringType is { } thisDeclaring)
        {
            var thisType = local.Type as GenericInstanceTypeAnalysisContext ?? thisDeclaring;
            return thisType.IsValueType ? new ByRefTypeAnalysisContext(thisType) : thisType;
        }
        // System.Object is also the lifter's fallback for a register whose real
        // numeric type was lost. Do not guess from arithmetic alone; a concrete
        // numeric mate (array length, typed field/parameter, etc.) must prove it.
        if (local.Type == context.AppContext.SystemTypes.SystemObjectType
            && NumericLocalTypes(context).TryGetValue(local, out var recoveredNumericType))
            return recoveredNumericType;
        if (local.Type != null && local.Type != context.AppContext.SystemTypes.SystemVoidType)
        {
            if (CallDefinedLocalType(local, context) is { } callType)
                return callType;
            // IL2CPP represents `ref enumField` through a native pointer local whose
            // shared-generic metadata type is an internal *Enum marker. The defining
            // base+offset operation still proves the exact managed field address.
            if ((IsErasedSharedArgument(local.Type)
                    || local.Type is ByRefTypeAnalysisContext byRef
                    && IsErasedSharedArgument(byRef.ElementType))
                && SharpenedFieldAddressType(local, context) is { } fieldAddress)
                return fieldAddress;
            // Shared-generic erasure can tag a local with the canonical
            // PersistentMap<object,object> instantiation while the values that
            // actually reach it carry the concrete one; recover the local's type
            // from its definitions so downstream consumers stay consistent.
            if (local.Type is GenericInstanceTypeAnalysisContext erasedInstance
                && erasedInstance.GenericArguments.Any(ContainsErasedSharedArgument)
                && SharpenedLocalInstanceType(local, erasedInstance, context, visited) is { } sharpened)
                return sharpened;
            if (local.Type == context.AppContext.SystemTypes.SystemObjectType
                && ObjectDefinitionType(local, context) is { } sourceType)
                return sourceType;
            if (local.Type == context.AppContext.SystemTypes.SystemObjectType
                && SharpenedObjectAllocationType(local, context) is { } allocatedType)
                return allocatedType;
            return IsNativeHandleType(local.Type) ? context.AppContext.SystemTypes.SystemIntPtrType : local.Type;
        }
        if (context.DeclaringType is { } declaringType
            && !context.IsStatic && ReferenceEquals(local, context.ParameterLocals.FirstOrDefault()))
            return declaringType.IsValueType ? new ByRefTypeAnalysisContext(declaringType) : declaringType;
        if (IsBooleanEmissionLocal(local, context))
            return context.AppContext.SystemTypes.SystemBooleanType;
        if (IsNativePointerEmissionLocal(local, context))
            return context.AppContext.SystemTypes.SystemIntPtrType;
        if (NumericLocalTypes(context).TryGetValue(local, out var numericType) && CanEmitTypeToken(numericType))
            return numericType;
        return context.AppContext.SystemTypes.SystemObjectType;
    }

    private static TypeAnalysisContext? CallDefinedLocalType(LocalVariable local,
        MethodAnalysisContext context)
    {
        TypeAnalysisContext? produced = null;
        var found = false;
        var inferredFromArguments = false;
        foreach (var definition in context.ControlFlowGraph!.Instructions
                     .Where(instruction => ReferenceEquals(instruction.Destination, local)))
        {
            if (definition is not { OpCode: OpCode.Call,
                    Operands: [MethodAnalysisContext { IsVoid: false } callee, ..] })
                return null;
            var resolved = !callee.IsStatic && definition.Operands.Count > 2
                ? ThisConstructorCallPlan.RetargetToDestinationInstantiation(callee,
                      DirectSharedGenericEvidenceType(definition.Operands[2], context)) ?? callee
                : callee;
            var solved = SolveSharedGenericArguments(resolved, definition, context, 2, false);
            var returnType = EffectiveCallReturnType(solved ?? resolved);
            if (!CanEmitTypeToken(returnType)
                || produced != null && !ThisConstructorCallPlan.SameTypeIdentity(produced, returnType))
                return null;
            inferredFromArguments |= !ReferenceEquals(resolved, callee) || solved != null;
            produced = returnType;
            found = true;
        }
        if (!found || produced == null)
            return null;

        var matchingStore = false;
        foreach (var use in context.ControlFlowGraph.Instructions)
        {
            if (use is not { OpCode: OpCode.Move, Operands: [var destination, var source, ..] }
                || !ReferenceEquals(source, local)
                || DestinationType(destination) is not { } contract
                || contract.FullName == "System.Object")
                continue;
            if (!produced.IsValueType && contract.FullName == "System.Boolean")
                continue;
            if (!ThisConstructorCallPlan.SameTypeIdentity(produced, contract))
            {
                // Hidden struct returns from shared generic code are initially typed
                // from the erased callee (Enumerator<object>).  The receiver can later
                // prove the concrete result (Enumerator<EmoteData>); do not let the
                // stale move destination erase that stronger call-site evidence.
                if (!inferredFromArguments
                    || produced is not GenericInstanceTypeAnalysisContext producedInstance
                    || contract is not GenericInstanceTypeAnalysisContext contractInstance
                    || !contractInstance.GenericArguments.Any(ContainsErasedSharedArgument)
                    || !ThisConstructorCallPlan.SameTypeIdentity(
                        producedInstance.GenericType, contractInstance.GenericType))
                    return null;
            }
            matchingStore = true;
        }
        return matchingStore || inferredFromArguments || produced.FullName != "System.Object"
            ? produced
            : null;
    }

    private static TypeAnalysisContext? DirectCallDefinedLocalType(LocalVariable local,
        MethodAnalysisContext context)
    {
        TypeAnalysisContext? produced = null;
        foreach (var definition in context.ControlFlowGraph!.Instructions
                     .Where(instruction => ReferenceEquals(instruction.Destination, local)))
        {
            if (definition is not { OpCode: OpCode.Call,
                    Operands: [MethodAnalysisContext { IsVoid: false } callee, ..] })
                return null;
            var resolved = !callee.IsStatic && definition.Operands.Count > 2
                ? ThisConstructorCallPlan.RetargetToDestinationInstantiation(callee,
                      DirectSharedGenericEvidenceType(definition.Operands[2], context)) ?? callee
                : callee;
            var returnType = EffectiveCallReturnType(resolved);
            if (!CanEmitTypeToken(returnType)
                || produced != null && !ThisConstructorCallPlan.SameTypeIdentity(produced, returnType))
                return null;
            produced = returnType;
        }
        return produced;
    }

    private static TypeAnalysisContext? ObjectDefinitionType(LocalVariable local,
        MethodAnalysisContext context)
    {
        TypeAnalysisContext? inferred = null;
        foreach (var definition in context.ControlFlowGraph!.Instructions
                     .Where(instruction => ReferenceEquals(instruction.Destination, local)))
        {
            if (definition is not { OpCode: OpCode.Move, Operands.Count: > 1 })
                return null;
            var sourceType = definition.Operands[1] switch
            {
                ArrayAccess { Array.Type: SzArrayTypeAnalysisContext array } => array.ElementType,
                FieldReference field => field.Field.FieldType,
                SelectedFieldReference selected => selected.FieldType,
                ReferenceCast cast => cast.Type,
                _ => null
            };
            if (sourceType == null || sourceType.IsValueType
                || sourceType == context.AppContext.SystemTypes.SystemObjectType
                || inferred != null && !ThisConstructorCallPlan.SameTypeIdentity(inferred, sourceType))
                return null;
            inferred = sourceType;
        }
        return inferred;
    }

    internal static TypeAnalysisContext EffectiveCallReturnType(MethodAnalysisContext method)
    {
        var result = method.ReturnType;
        if (method is not ConcreteGenericMethodAnalysisContext concrete
            || result is not GenericInstanceTypeAnalysisContext instance
            || instance.GenericArguments.Count != concrete.TypeGenericParameters.Count
            || !instance.GenericArguments.All(IsErasedSharedArgument))
            return result;

        return new GenericInstanceTypeAnalysisContext(instance.GenericType,
            concrete.TypeGenericParameters);
    }

    internal static MethodAnalysisContext RetargetToReceiverInstantiation(MethodAnalysisContext method,
        TypeAnalysisContext? receiverType) =>
        ThisConstructorCallPlan.RetargetToDestinationInstantiation(method, receiverType) ?? method;

    // object_new can lose its class operand and collapse to System.Object while the
    // immediately following managed cast still proves the allocated reference type.
    private static TypeAnalysisContext? SharpenedObjectAllocationType(LocalVariable local,
        MethodAnalysisContext context)
    {
        var definitions = context.ControlFlowGraph!.Instructions
            .Where(instruction => ReferenceEquals(instruction.Destination, local))
            .ToList();
        if (definitions.Count == 0 || definitions.Any(instruction => instruction.OpCode != OpCode.Newobj))
            return null;

        TypeAnalysisContext? contract = null;
        foreach (var definition in definitions)
        {
            var allocated = AllocatedClassOperand(context, definition);
            if (allocated == null || allocated.IsValueType)
                return null;
            // System.Object is the lifter's unknown-class fallback, not contrary
            // evidence against the concrete managed cast/return contract below.
            if (allocated.FullName == "System.Object")
                continue;
            if (contract != null && !ThisConstructorCallPlan.SameTypeIdentity(contract, allocated))
                return null;
            contract = allocated;
        }

        var aliases = new HashSet<LocalVariable> { local };
        var changed = true;
        while (changed)
        {
            changed = false;
            foreach (var instruction in context.ControlFlowGraph.Instructions
                         .Where(instruction => instruction.OpCode is OpCode.Move or OpCode.Phi))
            {
                var linked = instruction.Operands.OfType<LocalVariable>().ToList();
                if (!linked.Any(aliases.Contains))
                    continue;
                foreach (var alias in linked)
                    changed |= aliases.Add(alias);
            }
        }

        foreach (var cast in context.ControlFlowGraph.Instructions
                     .SelectMany(instruction => instruction.Operands)
                     .OfType<ReferenceCast>()
                     .Where(cast => aliases.Contains(cast.Value)))
        {
            if (cast.Type is { IsValueType: true } || cast.Type.FullName == "System.Object"
                || (contract != null && !ThisConstructorCallPlan.SameTypeIdentity(contract, cast.Type)))
                return null;
            contract = cast.Type;
        }

        // A native object_new result is often copied through an object-typed SSA
        // temporary and only constrained by the managed method's return slot.
        // That return signature is the same hard contract as an explicit cast.
        if (context.ReturnType is { IsValueType: false } returnType
            && returnType.FullName != "System.Object"
            && context.ControlFlowGraph.Instructions.Any(instruction =>
                instruction.OpCode == OpCode.Return
                && instruction.Operands.OfType<LocalVariable>().Any(aliases.Contains)))
        {
            if (contract != null && !ThisConstructorCallPlan.SameTypeIdentity(contract, returnType))
                return null;
            contract = returnType;
        }
        return contract;
    }

    private static bool IsNativePointerEmissionLocal(LocalVariable local, MethodAnalysisContext context)
    {
        var definitions = context.ControlFlowGraph!.Instructions
            .Where(instruction => ReferenceEquals(instruction.Destination, local))
            .ToList();
        return definitions.Count > 0 && definitions.All(instruction =>
            instruction.NativeIntegerWidthBits == context.AppContext.Binary.PointerSizeBytes * 8
            && instruction.OpCode == OpCode.Move
            && instruction.Operands[1] is Immediate);
    }

    private static bool IsBooleanEmissionLocal(LocalVariable local, MethodAnalysisContext context) =>
        IsBooleanEmissionLocal(local, context, []);

    private static bool IsBooleanEmissionLocal(LocalVariable local, MethodAnalysisContext context,
        HashSet<LocalVariable> active)
    {
        if (!active.Add(local))
            return false;
        var definitions = context.ControlFlowGraph!.Instructions
            .Where(instruction => ReferenceEquals(instruction.Destination, local))
            .ToList();
        var result = definitions.Count > 0 && definitions.All(instruction =>
            instruction.OpCode is >= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual
            || instruction.OpCode == OpCode.Not && IsBooleanEmissionOperand(instruction.Operands[1], context, active)
            || instruction.OpCode is OpCode.And or OpCode.Or or OpCode.Xor
                && instruction.Operands.Skip(1).All(operand => IsBooleanEmissionOperand(operand, context, active)));
        active.Remove(local);
        return result;
    }

    private static bool IsBooleanEmissionOperand(IOperand operand, MethodAnalysisContext context,
        HashSet<LocalVariable> active) => operand switch
    {
        Immediate { Value: 0 or 1 } => true,
        LocalVariable { Type.FullName: "System.Boolean" } => true,
        LocalVariable local when local.Type == null => IsBooleanEmissionLocal(local, context, active),
        _ => false,
    };

    // Untyped locals that only ever flow through numeric operations get a numeric
    // CIL type instead of System.Object: union-find merges locals across Move/Phi/
    // arithmetic edges, concrete numeric contracts (typed mates, fields, params,
    // returns) seed each class, and any use that needs a non-numeric stack kind
    // disqualifies the whole class so those locals stay honestly untyped.
    private static Dictionary<LocalVariable, TypeAnalysisContext> NumericLocalTypes(MethodAnalysisContext context)
    {
        if (context.GetExtraData<Dictionary<LocalVariable, TypeAnalysisContext>>("NumericLocalTypes") is { } cached)
            return cached;
        var computed = ComputeNumericLocalTypes(context);
        context.PutExtraData("NumericLocalTypes", computed);
        return computed;
    }

    private static Dictionary<LocalVariable, TypeAnalysisContext> ComputeNumericLocalTypes(MethodAnalysisContext context)
    {
        var instructions = context.ControlFlowGraph!.Instructions.ToList();
        var parent = new Dictionary<LocalVariable, LocalVariable>();
        var constraints = new Dictionary<LocalVariable, List<TypeAnalysisContext>>();
        var disqualified = new HashSet<LocalVariable>();
        // Locals that must be numeric because they feed an op with no non-numeric
        // stack form (add/sub/mul/bitwise/shift — unlike ceq, which refs also take).
        var numericOpUse = new HashSet<LocalVariable>();

        LocalVariable Find(LocalVariable local)
        {
            if (!parent.TryGetValue(local, out var p))
                parent[local] = p = local;
            return parent[local] == local ? local : parent[local] = Find(parent[local]);
        }

        void Union(LocalVariable a, LocalVariable b) => parent[Find(a)] = Find(b);

        bool IsNumeric(TypeAnalysisContext? type) =>
            type != null && type.FullName is "System.Single" or "System.Double" || IntegralStackWidth(type) > 0;

        // Contracts a boxed numeric still satisfies — a value stored into one of
        // these slots can legitimately be an int/float, so they neither seed a
        // numeric type nor disqualify the class.
        bool IsBoxingCompatible(TypeAnalysisContext type) =>
            type.FullName is "System.Object" or "System.ValueType"
                or "System.IComparable" or "System.IFormattable" or "System.IConvertible";

        void AddOperandConstraint(IOperand operand, TypeAnalysisContext? type)
        {
            if (operand is not LocalVariable local)
                return;
            var root = Find(local);
            // Reference slots are boxing-compatible: any numeric value reaches them
            // through box/castclass, and any reference reaches numerics through
            // unbox.any — neither forbids a numeric inference. Managed pointers,
            // raw pointers and concrete structs do.
            if (type == null || IsBoxingCompatible(type)
                || type is { IsValueType: false }
                    and not (ByRefTypeAnalysisContext or PointerTypeAnalysisContext))
                return;
            if (IsNumeric(type))
                (constraints.TryGetValue(root, out var list) ? list : constraints[root] = []).Add(type);
            else
                disqualified.Add(root);
        }

        void Disqualify(IOperand operand)
        {
            if (operand is LocalVariable local)
                disqualified.Add(Find(local));
        }

        void UnionLocalOperands(IEnumerable<IOperand> operands)
        {
            LocalVariable? first = null;
            foreach (var operand in operands)
                if (operand is LocalVariable local)
                {
                    if (first == null) first = local;
                    else Union(first, local);
                }
        }

        // What an operand pushes, using only declared types (no inference) so it
        // can seed constraints while the inference itself is still running. A
        // managed address, struct value or concrete reference anchors the whole
        // union class: a slot that has to receive one can never be an Int32.
        TypeAnalysisContext? DeclaredStackType(IOperand operand)
        {
            var type = operand switch
            {
                LocalVariable local => local.Type,
                FieldReference field => field.Field.FieldType,
                SelectedFieldReference selected => selected.FieldType,
                ArrayAccess { Array.Type: SzArrayTypeAnalysisContext array } => array.ElementType,
                ArrayElementFieldReference elementField => elementField.Field.FieldType,
                ArrayLength => context.AppContext.SystemTypes.SystemInt32Type,
                AddressOf { Target: LocalVariable addressed }
                    => new ByRefTypeAnalysisContext(addressed.Type ?? context.AppContext.SystemTypes.SystemObjectType),
                AddressOf { Target: FieldReference addressedField }
                    => new ByRefTypeAnalysisContext(addressedField.Field.FieldType),
                AddressOf { Target: ArrayAccess { Array.Type: SzArrayTypeAnalysisContext addressedArray } }
                    => new ByRefTypeAnalysisContext(addressedArray.ElementType),
                AddressOf { Target: ArrayElementFieldReference addressedElementField }
                    => new ByRefTypeAnalysisContext(addressedElementField.Field.FieldType),
                AddressOf => context.AppContext.SystemTypes.SystemIntPtrType,
                ReferenceCast cast => cast.Type,
                StringLiteral => context.AppContext.SystemTypes.SystemStringType,
                FloatLiteral => context.AppContext.SystemTypes.SystemSingleType,
                DoubleLiteral => context.AppContext.SystemTypes.SystemDoubleType,
                _ => null
            };
            return type != null && IsNativeHandleType(type) ? type.AppContext.SystemTypes.SystemIntPtrType : type;
        }

        // Every local in the instruction is constrained by the declared shapes of
        // its operand mates: Move(&x -> v) disqualifies v, Move(v -> intField)
        // seeds int, and arith results inherit the operand family.
        void SeedMateConstraints(IEnumerable<IOperand> instructionOperands)
        {
            var operands = instructionOperands.ToList();
            foreach (var local in operands.OfType<LocalVariable>())
                foreach (var mate in operands)
                    if (!ReferenceEquals(mate, local))
                        AddOperandConstraint(local, DeclaredStackType(mate));
        }

        foreach (var instruction in instructions)
        {
            // Nested locals inside compound operands still carry stack contracts:
            // field hosts, array bases, address targets and cast sources can never
            // be numeric.
            foreach (var operand in instruction.Operands)
                switch (operand)
                {
                    case FieldReference { Local: LocalVariable host }: Disqualify(host); break;
                    case SelectedFieldReference selected:
                        foreach (var receiver in selected.Choices.Select(c => c.Field.Local).Distinct())
                            Disqualify(receiver);
                        AddOperandConstraint(selected.Selector, context.AppContext.SystemTypes.SystemInt64Type);
                        break;
                    case ArrayAccess { Array: LocalVariable array }:
                        Disqualify(array);
                        AddOperandConstraint(((ArrayAccess)operand).Index, context.AppContext.SystemTypes.SystemInt32Type);
                        break;
                    case AddressOf { Target: LocalVariable target }: Disqualify(target); break;
                    case MemoryOperand { Base: LocalVariable memoryBase }: Disqualify(memoryBase); break;
                    case ReferenceCast { Value: LocalVariable castSource }: Disqualify(castSource); break;
                    case ArrayLength { Array: LocalVariable lengthArray }: Disqualify(lengthArray); break;
                }

            var op = instruction.OpCode;
            if (op is >= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual)
            {
                // The bool result is not the compared type; only operand locals union.
                UnionLocalOperands(instruction.Operands.Skip(1));
                foreach (var operand in instruction.Operands.Skip(1))
                    AddOperandConstraint(operand, DestinationType(operand));
                SeedMateConstraints(instruction.Operands.Skip(1));
            }
            else if (op is OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.Divide or OpCode.Modulo
                or OpCode.And or OpCode.Or or OpCode.Xor or OpCode.Not or OpCode.Negate or OpCode.SignExtend32)
            {
                // Result shares the operand family, so the destination unions too.
                UnionLocalOperands(instruction.Operands);
                foreach (var operand in instruction.Operands)
                {
                    if (operand is LocalVariable numericLocal)
                        numericOpUse.Add(Find(numericLocal));
                    AddOperandConstraint(operand, DestinationType(operand));
                }
                foreach (var source in instruction.Operands.Skip(1))
                    AddOperandConstraint(instruction.Operands[0], DeclaredStackType(source));
            }
            else if (op is OpCode.ShiftLeft or OpCode.ShiftRight)
            {
                UnionLocalOperands([instruction.Operands[0], instruction.Operands[1]]);
                foreach (var operand in instruction.Operands.Take(2))
                    if (operand is LocalVariable shiftLocal)
                        numericOpUse.Add(Find(shiftLocal));
                AddOperandConstraint(instruction.Operands[0], DestinationType(instruction.Operands[0]));
                AddOperandConstraint(instruction.Operands[1], DestinationType(instruction.Operands[1]));
                AddOperandConstraint(instruction.Operands[0], DeclaredStackType(instruction.Operands[1]));
                AddOperandConstraint(instruction.Operands[2], context.AppContext.SystemTypes.SystemInt32Type);
            }
            else if (op is OpCode.Move or OpCode.Phi)
            {
                UnionLocalOperands(instruction.Operands);
                foreach (var operand in instruction.Operands)
                    AddOperandConstraint(operand, DestinationType(operand));
                SeedMateConstraints(instruction.Operands);
            }
            else if (op is OpCode.Call or OpCode.CallVoid or OpCode.IndirectCall)
            {
                var target = instruction.Operands[0] as MethodAnalysisContext;
                var paramIndex = op == OpCode.Call ? (target?.IsStatic == true ? 2 : 3) : (target?.IsStatic == true ? 1 : 2);
                for (var i = paramIndex; i < instruction.Operands.Count; i++)
                {
                    var paramType = target != null && i - paramIndex < target.Parameters.Count
                        ? target.Parameters[i - paramIndex].ParameterType
                        : null;
                    AddOperandConstraint(instruction.Operands[i], paramType);
                }
                if (target is { IsStatic: false })
                    Disqualify(instruction.Operands[op == OpCode.Call ? 2 : 1]);
                if (op == OpCode.Call && instruction.Operands.Count > 1)
                    AddOperandConstraint(instruction.Operands[1], target?.ReturnType);
                if (op == OpCode.IndirectCall)
                    Disqualify(instruction.Operands[0]);
            }
            else if (op == OpCode.Return && instruction.Operands.Count > 0)
                AddOperandConstraint(instruction.Operands[0], context.ReturnType);
            else if (op == OpCode.ConditionalJump && instruction.Operands.Count > 1)
                // brtrue accepts refs and ints alike; too ambiguous to seed a type.
                Disqualify(instruction.Operands[1]);
            else if (op == OpCode.NewArr)
            {
                Disqualify(instruction.Operands[0]);
                if (instruction.Operands.Count > 2)
                    AddOperandConstraint(instruction.Operands[2], context.AppContext.SystemTypes.SystemInt32Type);
            }
            else if (op == OpCode.Newobj)
                Disqualify(instruction.Operands[0]);
            else if (op is OpCode.Throw or OpCode.IndirectJump)
                foreach (var operand in instruction.Operands)
                    Disqualify(operand);
        }

        // Re-key constraints and disqualifications by their final roots.
        var rootConstraints = new Dictionary<LocalVariable, List<TypeAnalysisContext>>();
        foreach (var pair in constraints)
        {
            var final = Find(pair.Key);
            (rootConstraints.TryGetValue(final, out var list) ? list : rootConstraints[final] = []).AddRange(pair.Value);
        }
        var rootDisqualified = new HashSet<LocalVariable>(disqualified.Select(Find));

        var rootNumericOpUse = new HashSet<LocalVariable>(numericOpUse.Select(Find));
        var systemTypes = context.AppContext.SystemTypes;

        var result = new Dictionary<LocalVariable, TypeAnalysisContext>();
        var members = parent.Keys.GroupBy(Find);
        foreach (var group in members)
        {
            var root = group.Key;
            if (rootDisqualified.Contains(root))
                continue;
            var hasTypes = rootConstraints.TryGetValue(root, out var types) && types.Count > 0;
            if (!hasTypes && !rootNumericOpUse.Contains(root))
                continue;
            var picked = hasTypes
                ? types!.FirstOrDefault(t => t.FullName == "System.Double")
                    ?? types.FirstOrDefault(t => t.FullName == "System.Single")
                    ?? types.FirstOrDefault(t => IntegralStackWidth(t) == 8)
                    ?? types[0]
                : systemTypes.SystemInt32Type;
            foreach (var member in group)
                if (member.Type == null
                    || member.Type == systemTypes.SystemObjectType && hasTypes)
                    result[member] = picked;
        }
        return result;
    }

    private static bool IsZeroConstant(IOperand operand) => operand is Immediate { Value: 0 };

    private static TypeAnalysisContext? NullComparisonType(Instruction instruction, int operandIndex, MethodAnalysisContext context)
    {
        if (instruction.OpCode is not (OpCode.CheckEqual or OpCode.CheckNotEqual)
            || !IsZeroConstant(instruction.Operands[operandIndex])) return null;
        var otherOperand = instruction.Operands[3 - operandIndex];
        // Untyped locals may be inferred as numeric by NumericLocalTypes; the emitted
        // stack type, not the raw analysis type, is the real stack contract. Memory
        // dereferences report their referent here the same way locals report theirs.
        var otherType = EmittedOperandType(otherOperand, context);
        // Untyped locals are emitted as System.Object. Match the actual CIL local contract so a
        // zero equality test is a reference-null comparison rather than invalid object-vs-I4 IL.
        if (otherType == null && otherOperand is LocalVariable)
            return context.AppContext.SystemTypes.SystemObjectType;
        // Runtime handles, unmanaged/byref pointers and unconstrained generic parameters
        // are not managed references, even when their IsValueType property is false.
        return otherType is not null
            and not (RuntimeClassTypeAnalysisContext or RuntimeMethodInfoAnalysisContext
                or RuntimeFieldInfoAnalysisContext or PointerTypeAnalysisContext
                or ByRefTypeAnalysisContext or GenericParameterTypeAnalysisContext)
            && (!otherType.IsValueType || otherType.FullName is "System.Object" or "System.String")
            ? otherType
            : null;
    }
    
    private static TypeAnalysisContext? DestinationType(IOperand destination)
    {
        var type = destination switch
        {
            LocalVariable local => local.Type,
            FieldReference field => field.Field.FieldType,
            SelectedFieldReference selected => selected.FieldType,
            ArrayAccess { Array.Type: SzArrayTypeAnalysisContext array } => array.ElementType,
            ArrayElementFieldReference elementField => elementField.Field.FieldType,
            _ => null
        };
        // Handle contexts are emitted as System.IntPtr, so that is the real contract
        // the stack value has to satisfy.
        return type != null && IsNativeHandleType(type) ? type.AppContext.SystemTypes.SystemIntPtrType : type;
    }

    // The contract StoreToOperand actually enforces: a bare [baseLocal] memory store
    // degrades to `stloc` of that local, so its slot contract is the base local's
    // emitted type even though the memory operand itself declares none.
    private static TypeAnalysisContext? StoreContract(IOperand destination, MethodAnalysisContext context)
    {
        // `this` is the one local whose declared type is not what `stloc` sees:
        // ldarg.0/stloc on a struct method's this moves a managed pointer, so the
        // store contract is the emitted type, not the bare struct.
        var declared = destination is LocalVariable { IsThis: true }
            ? null
            : DestinationType(destination);
        // A shared-generic erased instantiation (List<object>) is not the local
        // the emitted body declares when sharpening recovered the concrete one;
        // the contract must agree with the declaration or the store coerces the
        // operand into a type the slot does not accept.
        if (declared is GenericInstanceTypeAnalysisContext declaredInstance
            && declaredInstance.GenericArguments.Any(ContainsErasedSharedArgument)
            && destination is LocalVariable destinationLocal
            && EmittedLocalTypeCore(destinationLocal, context, []) is GenericInstanceTypeAnalysisContext
                {
                    GenericType: { } sharpenedDefinition,
                    GenericArguments: { } sharpenedArguments
                } sharpenedContract
            && ThisConstructorCallPlan.SameTypeIdentity(sharpenedDefinition, declaredInstance.GenericType)
            && !sharpenedArguments.Any(argument =>
                ContainsUnusableSharpenedArgument(argument, context)))
            return sharpenedContract;
        if (declared is ByRefTypeAnalysisContext declaredByRef
            && IsErasedSharedArgument(declaredByRef.ElementType)
            && destination is LocalVariable byRefLocal
            && EmittedLocalType(byRefLocal, context) is ByRefTypeAnalysisContext sharpenedByRef
            && !IsErasedSharedArgument(sharpenedByRef.ElementType))
            return sharpenedByRef;
        if (declared == context.AppContext.SystemTypes.SystemObjectType
            && destination is LocalVariable objectLocal
            && EmittedLocalType(objectLocal, context) is { } concreteContract
            && concreteContract != context.AppContext.SystemTypes.SystemObjectType)
            return concreteContract;
        if (destination is LocalVariable callLocal
            && CallDefinedLocalType(callLocal, context) is { } callContract)
            return callContract;
        if (declared != null)
            return declared;
        return destination switch
        {
            LocalVariable local => EmittedLocalType(local, context),
            MemoryOperand { Index: null, Addend: 0, Scale: 0, Base: LocalVariable { Type: not ByRefTypeAnalysisContext } baseLocal }
                => EmittedLocalType(baseLocal, context),
            _ => null
        };
    }

    // Type evidence used to solve shared generics. Unlike the final emitted stack
    // type, this must not mistake a runtime-safe marker fallback (Int32Enum -> int)
    // for a proven concrete instantiation.
    private static TypeAnalysisContext? DirectSharedGenericEvidenceType(IOperand operand,
        MethodAnalysisContext context) => operand switch
    {
        FieldReference field => field.Field.FieldType,
        SelectedFieldReference selected => selected.FieldType,
        ArrayAccess { Array.Type: SzArrayTypeAnalysisContext array } => array.ElementType,
        ReferenceCast cast when !ContainsErasedSharedArgument(cast.Type) => cast.Type,
        LocalVariable { Type: { } type } when type != context.AppContext.SystemTypes.SystemObjectType
            && type != context.AppContext.SystemTypes.SystemVoidType
            && !ContainsErasedSharedArgument(type) => type,
        _ => null
    };

    internal static TypeAnalysisContext? SharedGenericEvidenceType(IOperand operand,
        MethodAnalysisContext context) => operand switch
    {
        LocalVariable local => EmittedLocalTypeCore(local, context, []),
        AddressOf { Target: LocalVariable addressedLocal }
            => new ByRefTypeAnalysisContext(EmittedLocalTypeCore(addressedLocal, context, [])),
        ReferenceCast { Value: var value, Type: GenericInstanceTypeAnalysisContext target }
            when target.GenericArguments.Any(ContainsErasedSharedArgument)
            => SharedGenericEvidenceType(value, context),
        _ => EmittedOperandType(operand, context)
    };

    // The stack type an operand produces once emitted, before any coercion. `expectedType`
    // is the consumer's contract where the emission site knows it: literal immediates adapt
    // to it, and runtime-handle operands lower differently for handle/typeof contracts.
    internal static TypeAnalysisContext? EmittedOperandType(IOperand operand, MethodAnalysisContext context,
        TypeAnalysisContext? expectedType = null) =>
        operand switch
        {
            // A literal with no contract adapts to whatever type the consumer picks
            // for it; only a known contract pins down its emitted width. A zero into
            // a reference contract emits ldnull, which is the contract type itself.
            Immediate immediate => expectedType is null ? null
                : immediate.Value == 0 && expectedType is { IsValueType: false } && !IsNativeHandleType(expectedType)
                    && expectedType is not (ByRefTypeAnalysisContext or PointerTypeAnalysisContext
                        or GenericParameterTypeAnalysisContext)
                    ? expectedType
                    : EmittedImmediateType(immediate, expectedType, context),
            LocalVariable local => EmittedLocalType(local, context),
            FieldReference field => field.Field.FieldType,
            SelectedFieldReference selected => selected.FieldType,
            ArrayElementFieldReference elementField => elementField.Field.FieldType,
            ArrayAccess { Array.Type: SzArrayTypeAnalysisContext array } => array.ElementType,
            ArrayLength => context.AppContext.SystemTypes.SystemInt32Type,
            // ldloca/ldflda/ldelema push a managed pointer, not a native int.
            AddressOf { Target: LocalVariable addressedLocal }
                => new ByRefTypeAnalysisContext(EmittedLocalType(addressedLocal, context)),
            AddressOf { Target: FieldReference addressedField }
                => new ByRefTypeAnalysisContext(addressedField.Field.FieldType),
            AddressOf { Target: ArrayAccess { Array.Type: SzArrayTypeAnalysisContext addressedArray } }
                => new ByRefTypeAnalysisContext(addressedArray.ElementType),
            AddressOf { Target: ArrayElementFieldReference addressedElementField }
                => new ByRefTypeAnalysisContext(addressedElementField.Field.FieldType),
            AddressOf => context.AppContext.SystemTypes.SystemIntPtrType,
            ReferenceCast cast => EmittableLocalType(cast.Type, context),
            StringLiteral => context.AppContext.SystemTypes.SystemStringType,
            FloatLiteral => context.AppContext.SystemTypes.SystemSingleType,
            DoubleLiteral => context.AppContext.SystemTypes.SystemDoubleType,
            Vector128Literal => expectedType,
            RuntimeMethodInfoAnalysisContext or RuntimeFieldInfoAnalysisContext
                => expectedType?.FullName is "System.RuntimeMethodHandle" or "System.RuntimeFieldHandle"
                    ? ResolveSystemType(context, expectedType.FullName)
                    : context.AppContext.SystemTypes.SystemIntPtrType,
            RuntimeClassTypeAnalysisContext
                => expectedType?.FullName is "System.RuntimeTypeHandle" or "System.Type"
                    ? ResolveSystemType(context, expectedType.FullName == "System.Type" ? "System.Type" : "System.RuntimeTypeHandle")
                    : context.AppContext.SystemTypes.SystemIntPtrType,
            StaticFieldStorageTypeAnalysisContext or RgctxTableTypeAnalysisContext
                or MethodRgctxTableTypeAnalysisContext
                => context.AppContext.SystemTypes.SystemIntPtrType,
            // A deterministic memory dereference pushes whatever LoadOperand emits:
            // ldind.i for pointer referents, ldobj/ldind.ref for managed ones.
            MemoryOperand memory => TryRecoverLateFieldReference(memory, context, out var lateField)
                ? lateField.Field.FieldType
                : TryGetDeterministicMemoryReferent(memory, expectedType, out var referent)
                    ? referent is PointerTypeAnalysisContext or ByRefTypeAnalysisContext
                        ? context.AppContext.SystemTypes.SystemIntPtrType
                        : referent
                    : null,
            // A bare type operand (ldtoken): LoadOperand emits ldtoken + GetTypeFromHandle
            // for ordinary contracts, the bare handle for RuntimeTypeHandle, or a native
            // pointer for handle contracts — report what is actually pushed.
            TypeAnalysisContext => expectedType?.FullName switch
            {
                "System.RuntimeTypeHandle" => ResolveSystemType(context, "System.RuntimeTypeHandle"),
                "System.IntPtr" or "System.UIntPtr" => context.AppContext.SystemTypes.SystemIntPtrType,
                _ when expectedType is RuntimeClassTypeAnalysisContext
                    => context.AppContext.SystemTypes.SystemIntPtrType,
                _ => ResolveSystemType(context, "System.Type"),
            },
            _ => null
        };

    private static TypeAnalysisContext? ResolveSystemType(MethodAnalysisContext context, string fullName) =>
        context.AppContext.GetAssemblyByName("mscorlib")?.GetTypeByFullName(fullName);

    // Mirrors the Immediate branch of LoadOperand: the reported stack type is whatever
    // the literal actually emits under the consumer's contract.
    // ldelem.any pushes the element type verbatim, so narrow primitives and
    // enums land on the stack as Byte/Short/Char - no arithmetic or store slot
    // accepts them. The typed opcodes normalize to the evaluation-stack types.
    private static CilOpCode? LdelemOpCode(TypeAnalysisContext elementType)
    {
        var type = elementType is { IsEnumType: true, DefaultEnumUnderlyingType: { } underlying }
            ? underlying
            : elementType;
        return type.FullName switch
        {
            "System.Boolean" or "System.Byte" => CilOpCodes.Ldelem_U1,
            "System.SByte" => CilOpCodes.Ldelem_I1,
            "System.Int16" => CilOpCodes.Ldelem_I2,
            "System.Char" or "System.UInt16" => CilOpCodes.Ldelem_U2,
            "System.Int32" => CilOpCodes.Ldelem_I4,
            "System.UInt32" => CilOpCodes.Ldelem_U4,
            "System.Int64" or "System.UInt64" => CilOpCodes.Ldelem_I8,
            "System.Single" => CilOpCodes.Ldelem_R4,
            "System.Double" => CilOpCodes.Ldelem_R8,
            "System.IntPtr" or "System.UIntPtr" => CilOpCodes.Ldelem_I,
            _ when !type.IsValueType => CilOpCodes.Ldelem_Ref,
            _ => null,
        };
    }

    private static TypeAnalysisContext EmittedImmediateType(Immediate immediate, TypeAnalysisContext? expectedType,
        MethodAnalysisContext context)
    {
        var systemTypes = context.AppContext.SystemTypes;
        var literalType = expectedType is { IsEnumType: true }
            ? expectedType.DefaultEnumUnderlyingType ?? expectedType
            : expectedType;
        return literalType switch
        {
            // ldloca of a fresh local produces the managed pointer itself.
            ByRefTypeAnalysisContext => literalType,
            // Unmanaged pointers take the literal as a native-int address.
            PointerTypeAnalysisContext => systemTypes.SystemIntPtrType,
            _ => literalType?.FullName switch
            {
                "System.IntPtr" or "System.UIntPtr" => literalType,
                "System.Single" => systemTypes.SystemSingleType,
                "System.Double" => systemTypes.SystemDoubleType,
                "System.Int64" or "System.UInt64" => literalType,
                "System.Int32" or "System.UInt32" or "System.Boolean" or "System.Byte" or "System.SByte"
                    or "System.Int16" or "System.UInt16" or "System.Char" => systemTypes.SystemInt32Type,
                _ => immediate.Value is >= int.MinValue and <= int.MaxValue
                    ? systemTypes.SystemInt32Type
                    : systemTypes.SystemInt64Type,
            }
        };
    }

    // Runtime handle wrappers (klass/method/field/rgctx handles) lower to a raw
    // pointer-sized value at emission even though their contexts are not value types.
    private static bool IsNativeHandleType(TypeAnalysisContext type) =>
        type is RuntimeClassTypeAnalysisContext or RuntimeMethodInfoAnalysisContext
            or RuntimeFieldInfoAnalysisContext or StaticFieldStorageTypeAnalysisContext
            or RgctxTableTypeAnalysisContext or MethodRgctxTableTypeAnalysisContext;

    // Native width of the type's evaluation-stack representation: 4 for anything
    // narrowing to i32, 8 for 64-bit primitives, -1 for native-int/pointer/byref
    // values and 0 for non-integral stack kinds.
    internal static int IntegralStackWidth(TypeAnalysisContext? type)
    {
        if (type == null)
            return 0;
        if (type is PointerTypeAnalysisContext or ByRefTypeAnalysisContext || IsNativeHandleType(type))
            return -1;

        if (type is GenericInstanceTypeAnalysisContext { GenericType.IsEnumType: true } enumInstance)
            return IntegralStackWidth(enumInstance.GenericType.DefaultEnumUnderlyingType
                ?? type.AppContext.SystemTypes.SystemInt32Type);

        return type.FullName switch
        {
            "System.Boolean" or "System.Byte" or "System.SByte" or "System.Char"
                or "System.Int16" or "System.UInt16" or "System.Int32" or "System.UInt32" => 4,
            "System.Int64" or "System.UInt64" => 8,
            "System.IntPtr" or "System.UIntPtr" => -1,
            _ when type is { IsEnumType: true } => IntegralStackWidth(type.DefaultEnumUnderlyingType),
            _ => 0
        };
    }

    private static bool IsUnsignedType(TypeAnalysisContext type) =>
        type.FullName is "System.Boolean" or "System.Byte" or "System.Char"
            or "System.UInt16" or "System.UInt32" or "System.UInt64" or "System.UIntPtr"
        || type is { IsEnumType: true, DefaultEnumUnderlyingType: { } underlying } && IsUnsignedType(underlying);

    // Emits the conversion needed to make a value of `from` acceptable where `to` is
    // required: primitive width change, box, unbox or reference cast. Returns false
    // when no legal conversion exists and the value still does not satisfy `to`;
    // callers then drop the unrepresentable value and fill the slot honestly.
    private static bool EmitStackCoerce(TypeAnalysisContext? from, TypeAnalysisContext? to, MethodDefinition method,
        MethodAnalysisContext? context, bool convertByRef = false)
    {
        // Handle contexts have no managed stack type of their own; everything below
        // reasons about the native int they emit as.
        if (from != null && IsNativeHandleType(from))
            from = from.AppContext.SystemTypes.SystemIntPtrType;
        if (to != null && IsNativeHandleType(to))
            to = to.AppContext.SystemTypes.SystemIntPtrType;

        if (from == null || to == null || from.FullName == to.FullName)
            return true;

        // No stack op synthesizes a generic-parameter or byref value from another kind.
        if (to is GenericParameterTypeAnalysisContext or ByRefTypeAnalysisContext)
            return false;

        var instructions = method.CilMethodBody!.Instructions;

        // A generic-parameter value into a reference slot boxes like any value
        // type; box !T is the standard generic-store sequence. A value-type slot
        // cannot take !T by any stack op, so that pairing stays unbridgeable.
        if (from is GenericParameterTypeAnalysisContext)
        {
            if (!to.IsValueType && to is not PointerTypeAnalysisContext && CanEmitTypeToken(from))
            {
                instructions.Add(CilOpCodes.Box, from.ToTypeSignature().ToTypeDefOrRef());
                if (!IsAssignableToLoose(from, to))
                {
                    // A cast the caller cannot name is not a legal coercion; the caller
                    // drops the box result and defaults the slot instead.
                    if (!TypeTokenUsableFrom(to, context))
                        return false;
                    if (CanEmitTypeToken(to))
                        instructions.Add(CilOpCodes.Castclass, to.ToTypeSignature().ToTypeDefOrRef());
                }
            }
            return !to.IsValueType;
        }
        var fromWidth = IntegralStackWidth(from);
        var toWidth = IntegralStackWidth(to);

        // An unmanaged pointer already is a native int to the verifier; conv.i
        // lands the requested width. Managed pointers take no conversion at all:
        // conv.*/binary ops reject `&`, so a `&` reaching a numeric slot must be
        // dereferenced instead (handled by the block below).
        if (from is PointerTypeAnalysisContext && convertByRef && toWidth != 0)
        {
            instructions.Add(CilOpCodes.Conv_I);
            fromWidth = -1;
        }

        // `&T` into a native-int or unmanaged-pointer slot is the pinned-address
        // idiom, but no verifiable IL converts `&` to `*`/nint - conv.* reject
        // managed pointers outright (ECMA III.1.5 keeps the conversion
        // unverifiable). The honest emission drops the address and defaults
        // the slot - the same placeholder an unresolvable operand gets -
        // instead of fabricating a value-as-pointer or leaving a raw `&`.
        if (from is ByRefTypeAnalysisContext
            && to is PointerTypeAnalysisContext or { FullName: "System.IntPtr" or "System.UIntPtr" })
        {
            instructions.Add(CilOpCodes.Pop);
            PushDefaultOf(to, method, instructions, context);
            return true;
        }

        // A managed pointer read back as a value is an honest dereference: ldobj
        // for value elements, ldind.ref for references. Neither deref finishes
        // the job by itself - the value on the stack is still the element type,
        // so the element still has to satisfy the slot's contract.
        if (from is ByRefTypeAnalysisContext byRef && to is not ByRefTypeAnalysisContext
            && fromWidth == -1)
        {
            var element = byRef.ElementType;
            if (element is ByRefTypeAnalysisContext or PointerTypeAnalysisContext
                || element.IsValueType && !TypeTokenUsableFrom(element, context)
                || !StackContractSatisfied(element, to, context, convertByRef))
                return false;
            if (element.IsValueType)
                instructions.Add(CilOpCodes.Ldobj, element.ToTypeSignature().ToTypeDefOrRef());
            else
                instructions.Add(CilOpCodes.Ldind_Ref);
            return EmitStackCoerce(element, to, method, context, convertByRef);
        }

        if (fromWidth != 0 && toWidth != 0)
        {
            if (fromWidth == toWidth)
                return true;
            if (toWidth < 0)
                instructions.Add(IsUnsignedType(from) ? CilOpCodes.Conv_U : CilOpCodes.Conv_I);
            else if (toWidth == 8)
                instructions.Add(IsUnsignedType(from) ? CilOpCodes.Conv_U8 : CilOpCodes.Conv_I8);
            else
                instructions.Add(IsUnsignedType(from) ? CilOpCodes.Conv_U4 : CilOpCodes.Conv_I4);
            return true;
        }

        var fromIsFloat = from.FullName is "System.Single" or "System.Double";
        var toIsFloat = to.FullName is "System.Single" or "System.Double";

        if (fromIsFloat && toWidth != 0)
        {
            instructions.Add(toWidth == 8 ? CilOpCodes.Conv_I8
                : toWidth < 0 ? CilOpCodes.Conv_I : CilOpCodes.Conv_I4);
            return true;
        }

        if (toIsFloat)
        {
            if (fromIsFloat || fromWidth != 0)
            {
                instructions.Add(to.FullName == "System.Single" ? CilOpCodes.Conv_R4 : CilOpCodes.Conv_R8);
                return true;
            }
            return false;
        }

        // Some recovered corlib contexts lose their value-type flag even though
        // their stack kind and name remain exact. A primitive entering any managed
        // reference slot still must be boxed; key this off the canonical name, not
        // the unreliable flag.
        var factory = method.DeclaringModule!.CorLibTypeFactory;
        TypeSignature? primitive = from.FullName switch
        {
            "System.Boolean" => factory.Boolean,
            "System.Byte" => factory.Byte,
            "System.SByte" => factory.SByte,
            "System.Char" => factory.Char,
            "System.Int16" => factory.Int16,
            "System.UInt16" => factory.UInt16,
            "System.Int32" => factory.Int32,
            "System.UInt32" => factory.UInt32,
            "System.Int64" => factory.Int64,
            "System.UInt64" => factory.UInt64,
            "System.Single" => factory.Single,
            "System.Double" => factory.Double,
            _ => null
        };
        if (primitive != null && !to.IsValueType
            && to is not (PointerTypeAnalysisContext or ByRefTypeAnalysisContext))
        {
            instructions.Add(CilOpCodes.Box, primitive.ToTypeDefOrRef());
            if (to.FullName == "System.Object" || !CanEmitTypeToken(to))
                return true;
            if (!TypeTokenUsableFrom(to, context))
                return false;
            instructions.Add(CilOpCodes.Castclass, to.ToTypeSignature().ToTypeDefOrRef());
            return true;
        }

        if (from.IsValueType && !to.IsValueType)
        {
            // Primitive corlib values always have a usable signature token even when
            // a reduced analysis fixture has no AsmResolver type mapping for them.
            // Leaving their I4/I8/R value unboxed in an object slot is invalid IL.
            if (!CanEmitTypeToken(from))
                return true;
            if (!TypeTokenUsableFrom(from, context))
                return false;
            instructions.Add(CilOpCodes.Box, from.ToTypeSignature().ToTypeDefOrRef());
            // box yields a `from` reference; an interface/other-ref destination still
            // needs the narrowing cast the verifier requires.
            if (IsAssignableToLoose(from, to) || !CanEmitTypeToken(to))
                return true;
            if (!TypeTokenUsableFrom(to, context))
                return false;
            instructions.Add(CilOpCodes.Castclass, to.ToTypeSignature().ToTypeDefOrRef());
            return true;
        }

        if (!from.IsValueType && to.IsValueType)
        {
            if (!CanEmitTypeToken(to))
                return true;
            if (!TypeTokenUsableFrom(to, context))
                return false;
            instructions.Add(CilOpCodes.Unbox_Any, to.ToTypeSignature().ToTypeDefOrRef());
            return true;
        }

        if (!from.IsValueType && !to.IsValueType)
        {
            // When the cast token cannot be emitted the value is left as-is: it may
            // still be runtime-compatible, and the verifier's complaint is no worse
            // than dropping real data for a guessed default. A token that exists but
            // is not visible here fails instead, so the caller defaults the slot.
            if (IsAssignableToLoose(from, to) || !CanEmitTypeToken(to))
                return true;
            if (!TypeTokenUsableFrom(to, context))
                return false;
            instructions.Add(CilOpCodes.Castclass, to.ToTypeSignature().ToTypeDefOrRef());
            return true;
        }

        // Different value types (or a pointer kind with no legal conversion): no
        // stack operation turns the emitted value into what the slot requires.
        return false;
    }

    // Coerces the emitted value into the slot's contract, or - when no stack
    // operation can bridge the types - drops it and fills the slot with the same
    // honest default PushDefaultOf uses for operands that were lost upstream.
    private static void CoerceOrDefault(TypeAnalysisContext? from, TypeAnalysisContext? to, MethodDefinition method,
        MethodAnalysisContext? context, bool convertByRef = false)
    {
        if (to == null || EmitStackCoerce(from, to, method, context, convertByRef))
            return;
        var instructions = method.CilMethodBody!.Instructions;
        instructions.Add(CilOpCodes.Pop);
        PushDefaultOf(to, method, instructions, context);
    }

    // True when the operand's emitted stack type is already a pointer to the struct a
    // callee needs as `this`: `&T`/`T*` from an address-taken or pointer-typed operand.
    private static bool ReceiverEmitsStructAddress(IOperand operand, MethodAnalysisContext context,
        TypeAnalysisContext structType) => EmittedOperandType(operand, context, structType) switch
        {
            ByRefTypeAnalysisContext byRef => ThisConstructorCallPlan.SameTypeIdentity(byRef.ElementType, structType),
            PointerTypeAnalysisContext pointer => ThisConstructorCallPlan.SameTypeIdentity(pointer.ElementType, structType),
            _ => false,
        };

    // A `this` slot for a struct method needs `&T`, which no stack operation can forge
    // from a lost or mistyped operand. When exactly one local of that struct type
    // exists its address is the honest receiver (the foreach enumerator); otherwise a
    // fresh default local is the only honest managed pointer to offer, same as
    // PushDefaultOf for ref/out parameters.
    private static bool EmitFallbackStructReceiver(TypeAnalysisContext structType, MethodAnalysisContext context,
        MethodDefinition method, Dictionary<LocalVariable, CilLocalVariable> locals)
    {
        var matched = UniqueLocalOfType(locals, context, structType);
        if (matched != null)
        {
            method.CilMethodBody!.Instructions.Add(CilOpCodes.Ldloca, matched);
            return true;
        }

        if (!CanEmitTypeToken(structType))
            return false;

        var defaultReceiver = new CilLocalVariable(structType.ToTypeSignature());
        method.CilMethodBody!.LocalVariables.Add(defaultReceiver);
        method.CilMethodBody.Instructions.Add(CilOpCodes.Ldloca, defaultReceiver);
        return true;
    }

    // The callee's receiver is provably not `this`, but the compiler keeps the
    // instance the native code actually passed inside the declaring type itself:
    // state machines and display classes reach their enclosing instance through
    // `<>4__this`, and any other contract-typed field is the same kind of slot.
    // Emits `ldarg.0; ldfld` (plus any residual coercion) and returns true;
    // false when no usable field fits the contract.
    private static bool TryEmitThisFieldReceiver(MethodAnalysisContext context, TypeAnalysisContext? contract,
        MethodDefinition method)
    {
        if (context.IsStatic || context.DeclaringType is not { } declaringType || contract == null)
            return false;

        var usableFields = InstanceFields(declaringType)
            .Where(field => !field.IsStatic && FieldUsableFrom(field, context))
            .ToList();
        var match = usableFields.FirstOrDefault(field =>
                ThisConstructorCallPlan.SameTypeIdentity(field.FieldType, contract))
            ?? usableFields.FirstOrDefault(field => StackAssignableTo(field.FieldType, contract));
        if (match == null)
            return false;

        var thisReceiver = context.ParameterLocals.FirstOrDefault() is { } thisLocal
            ? EmittedLocalType(thisLocal, context)
            : context.DeclaringType;
        method.CilMethodBody!.Instructions.Add(CilOpCodes.Ldarg_0);
        method.CilMethodBody.Instructions.Add(CilOpCodes.Ldfld, FieldDescriptorFor(match, thisReceiver));
        CoerceOrDefault(match.FieldType, contract, method, context);
        return true;
    }

    private static CilLocalVariable? UniqueLocalOfType(Dictionary<LocalVariable, CilLocalVariable> locals,
        MethodAnalysisContext context, TypeAnalysisContext type)
    {
        CilLocalVariable? match = null;
        foreach (var pair in locals)
        {
            if (!ThisConstructorCallPlan.SameTypeIdentity(EmittedLocalType(pair.Key, context), type))
                continue;
            if (match != null)
                return null;
            match = pair.Value;
        }
        return match;
    }

    // True when a raw stack value of type `from` already satisfies a `to` slot with
    // no conversion: identical types, the same reduced integral kind (the i4 family
    // includes enums/bool/char), the shared native-int kind, or a reference
    // assignable to the slot type.
    private static bool StackAssignableTo(TypeAnalysisContext from, TypeAnalysisContext to)
    {
        if (from.FullName == to.FullName)
            return true;
        if (from is ByRefTypeAnalysisContext || to is ByRefTypeAnalysisContext
            || from is GenericParameterTypeAnalysisContext || to is GenericParameterTypeAnalysisContext)
            return false; // only the identical type above satisfies these slots
        if (from is PointerTypeAnalysisContext || to is PointerTypeAnalysisContext)
            return IntegralStackWidth(from) < 0 && IntegralStackWidth(to) < 0;
        var fromWidth = IntegralStackWidth(from);
        var toWidth = IntegralStackWidth(to);
        if (fromWidth > 0 && fromWidth == toWidth)
            return true;
        if (fromWidth < 0 && toWidth < 0)
            return true;
        return !from.IsValueType && !to.IsValueType && IsAssignableToLoose(from, to);
    }

    // Mirrors EmitStackCoerce: true when a `from` value can occupy a `to` slot -
    // either it already does or a legal conversion exists. This is a stack-kind
    // question only: EmitStackCoerce already skips conversions whose type token is
    // missing, so a metadata gap degrades to the old pass-through instead of
    // discarding a recoverable value. When it returns false the operand can never
    // satisfy the slot (e.g. an int into a Vector3 argument) and the site should
    // emit default(to) rather than leave an uncoercible value on the stack.
    private static bool StackContractSatisfied(TypeAnalysisContext? from, TypeAnalysisContext? to,
        MethodAnalysisContext? context, bool convertByRef = false)
    {
        if (from != null && IsNativeHandleType(from))
            from = from.AppContext.SystemTypes.SystemIntPtrType;
        if (to != null && IsNativeHandleType(to))
            to = to.AppContext.SystemTypes.SystemIntPtrType;

        if (from == null || to == null || from.FullName == to.FullName)
            return true;

        // No stack op synthesizes a generic-parameter or byref destination value;
        // only the identical type already satisfies those slots.
        if (to is GenericParameterTypeAnalysisContext or ByRefTypeAnalysisContext)
            return StackAssignableTo(from, to);

        // A T source fits a managed reference through box T; nothing else is legal.
        // Mirrors EmitStackCoerce: a reference target that needs a narrowing cast
        // fails when the cast token is not visible to the caller.
        if (from is GenericParameterTypeAnalysisContext)
            return !to.IsValueType && to is not PointerTypeAnalysisContext
                && (IsAssignableToLoose(from, to) || !CanEmitTypeToken(to) || TypeTokenUsableFrom(to, context));

        var fromWidth = IntegralStackWidth(from);
        var toWidth = IntegralStackWidth(to);

        // A raw pointer slot takes a native-int value: an integral/native source
        // reaches it through conv.i, a managed pointer needs the opt-in convertByRef.
        if (to is PointerTypeAnalysisContext)
            return fromWidth != 0 || from is ByRefTypeAnalysisContext && convertByRef;

        if (from is ByRefTypeAnalysisContext or PointerTypeAnalysisContext)
        {
            // An unmanaged pointer already is a native int; the opt-in convertByRef
            // conv.i or the target's own width rules apply. A managed pointer can
            // only reach a non-& slot through dereference, so the mirror is the
            // element's own satisfiability.
            if (from is PointerTypeAnalysisContext)
                return toWidth != 0;
            var element = ((ByRefTypeAnalysisContext)from).ElementType;
            return element is not (ByRefTypeAnalysisContext or PointerTypeAnalysisContext)
                && (!element.IsValueType || TypeTokenUsableFrom(element, context))
                && StackContractSatisfied(element, to, context, convertByRef);
        }

        if (fromWidth != 0 && toWidth != 0)
            return true; // conv.i/u/u4/u8 lands the target's stack kind
        if (from.FullName is "System.Single" or "System.Double" && toWidth != 0)
            return true;
        if (to.FullName is "System.Single" or "System.Double")
            return from.FullName is "System.Single" or "System.Double" || fromWidth != 0;
        if (from.IsValueType && !to.IsValueType)
            // box, plus castclass when the reference target narrows - both need
            // tokens the caller can legally name
            return !CanEmitTypeToken(from)
                || TypeTokenUsableFrom(from, context)
                    && (IsAssignableToLoose(from, to) || !CanEmitTypeToken(to) || TypeTokenUsableFrom(to, context));
        if (!from.IsValueType && to.FullName == "System.Boolean")
            return false;
        if (!from.IsValueType && to.IsValueType)
            return !CanEmitTypeToken(to) || TypeTokenUsableFrom(to, context); // unbox.any accepts any managed reference
        if (!from.IsValueType && !to.IsValueType)
            // castclass narrows any reference pair - unless the caller cannot name it
            return IsAssignableToLoose(from, to) || !CanEmitTypeToken(to) || TypeTokenUsableFrom(to, context);
        return StackAssignableTo(from, to);
    }

    // Loads an operand for a consumer slot with a known type contract. When the
    // operand's emitted type can never satisfy the contract (e.g. an int local in
    // a Vector3 argument slot) the operand is dropped and default(contract) is
    // emitted instead - the only honest filler for a value that was not recovered.
    private static void LoadOperandIntoSlot(IOperand operand, TypeAnalysisContext? contract,
        MethodAnalysisContext context, MethodDefinition method,
        Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine,
        bool convertByRef = false)
    {
        operand = RuntimeFieldHandleSource(operand, contract, context);
        if (operand is FieldReference container
            && NestedValueFieldForContract(container, contract) is { } nested)
            operand = nested;
        if (operand is FieldReference nestedField
            && WholeValueContainerReference(nestedField, contract) is { } wholeValue)
            operand = wholeValue;
        // A bare type operand into a value-type slot has no honest emission except
        // runtime handles and native-int class handles, which have real token values.
        if (operand is TypeAnalysisContext and not RuntimeMethodInfoAnalysisContext
            && contract is { IsValueType: true }
            && contract.FullName is not ("System.RuntimeTypeHandle" or "System.RuntimeMethodHandle" or "System.RuntimeFieldHandle"
                or "System.IntPtr" or "System.UIntPtr"))
        {
            PushDefaultOf(contract, method, method.CilMethodBody!.Instructions, context);
            return;
        }
        var emitted = operand is MemoryOperand memory
            && TryRecoverLateFieldReference(memory, context, out var lateField)
                ? lateField.Field.FieldType
                : EmittedOperandType(operand, context, contract);
        if (operand is LocalVariable { IsThis: true }
            && contract is { IsValueType: true }
            && emitted is { IsValueType: false } and not PointerTypeAnalysisContext and not ByRefTypeAnalysisContext)
        {
            // `this` in a value slot is native pointer math on the receiver - a class
            // `this` is never a boxed value, so even after initialization the load
            // has no honest managed form; before the base .ctor runs it is also an
            // uninitialized read.
            PushDefaultOf(contract, method, method.CilMethodBody!.Instructions, context);
            return;
        }
        if (contract == null || StackContractSatisfied(emitted, contract, context, convertByRef))
        {
            LoadOperand(operand, method, locals, writeLine, contract, context);
            EmitStackCoerce(emitted, contract, method, context, convertByRef);
            return;
        }
        PushDefaultOf(contract, method, method.CilMethodBody!.Instructions, context);
    }

    private static FieldReference? NestedValueFieldForContract(FieldReference field,
        TypeAnalysisContext? contract)
    {
        if (contract == null || !field.Field.FieldType.IsValueType)
            return null;
        var matches = InstanceFields(field.Field.FieldType)
            .Where(candidate => !candidate.IsStatic
                && ThisConstructorCallPlan.SameTypeIdentity(candidate.FieldType, contract))
            .ToList();
        if (matches.Count != 1)
            return null;
        var nested = matches[0];
        return new FieldReference(nested, field.Local, field.Offset + nested.Offset,
            field.Containers.Append(field.Field).ToArray(), field.AccessSize);
    }

    internal static IOperand RuntimeFieldHandleSource(IOperand operand, TypeAnalysisContext? contract,
        MethodAnalysisContext context)
    {
        if (contract?.FullName != "System.RuntimeFieldHandle" || operand is not LocalVariable local)
            return operand;

        var visited = new HashSet<LocalVariable>();
        while (visited.Add(local))
        {
            var definitions = context.ControlFlowGraph!.Instructions
                .Where(instruction => ReferenceEquals(instruction.Destination, local)).ToList();
            if (definitions is not [{ OpCode: OpCode.Move, Operands: [_, var source, ..] }])
                break;
            if (source is RuntimeFieldInfoAnalysisContext)
                return source;
            if (source is not LocalVariable alias)
                break;
            local = alias;
        }
        return operand;
    }

    // Coerces an already-emitted stack value into a slot contract. When no legal
    // coercion exists the value is replaced by default(contract) - same as a
    // dropped operand - so the consuming store still sees a compatible type.
    private static void EmitStackCoerceOrDefault(TypeAnalysisContext? from, TypeAnalysisContext? contract,
        MethodDefinition method, MethodAnalysisContext? context, bool convertByRef = false)
    {
        var instructions = method.CilMethodBody!.Instructions;
        if (contract == null || StackContractSatisfied(from, contract, context, convertByRef))
        {
            EmitStackCoerce(from, contract, method, context, convertByRef);
            return;
        }
        instructions.Add(CilOpCodes.Pop);
        PushDefaultOf(contract, method, instructions, context);
    }

    // A missing value for a value-type or generic-parameter slot is default(T);
    // everything else gets the usual null.
    private static void EmitNullOrDefault(TypeAnalysisContext? contract, MethodDefinition method,
        CilInstructionCollection instructions, MethodAnalysisContext? context)
    {
        if (contract is { IsValueType: true } or GenericParameterTypeAnalysisContext)
            PushDefaultOf(contract, method, instructions, context);
        else
            instructions.Add(CilOpCodes.Ldnull);
    }

    // The type an operand actually emits with no consumer contract - immediates
    // take their natural width instead of adapting to a consumer.
    private static TypeAnalysisContext? NaturalEmittedType(IOperand operand, MethodAnalysisContext context) =>
        operand is Immediate immediate
            ? EmittedImmediateType(immediate, null, context)
            : EmittedOperandType(operand, context);

    // Whether two emitted stack values can legally meet a comparison opcode: ceq
    // pairs equal primitive widths, any two managed references or two native ints;
    // relational ops pair equal numeric widths (or an i4 with a native int).
    // Anything else - including every value-type pairing - cannot be compared.
    private static bool OperandsShareComparableKind(OpCode opCode, TypeAnalysisContext? a, TypeAnalysisContext? b)
    {
        if (a == null || b == null)
            return true; // Unknown emission (e.g. a throwing stub) - leave it alone.
        if (a is GenericParameterTypeAnalysisContext || b is GenericParameterTypeAnalysisContext)
            return false;

        var aWidth = IntegralStackWidth(a);
        var bWidth = IntegralStackWidth(b);
        var aIsFloat = a.FullName is "System.Single" or "System.Double";
        var bIsFloat = b.FullName is "System.Single" or "System.Double";
        var aNumeric = aWidth != 0 || aIsFloat;
        var bNumeric = bWidth != 0 || bIsFloat;

        if (aNumeric && bNumeric)
        {
            if (opCode is OpCode.CheckEqual or OpCode.CheckNotEqual)
                return aWidth == bWidth && aIsFloat == bIsFloat;
            if (aIsFloat != bIsFloat)
                return false; // float and integer kinds never pair
            if (aWidth < 0 || bWidth < 0)
                return aWidth == bWidth || aWidth == 4 || bWidth == 4; // rel ops allow i4 with native int
            return aWidth == bWidth;
        }

        if (opCode is OpCode.CheckEqual or OpCode.CheckNotEqual)
        {
            var aIsRef = !a.IsValueType && a is not (PointerTypeAnalysisContext or ByRefTypeAnalysisContext);
            var bIsRef = !b.IsValueType && b is not (PointerTypeAnalysisContext or ByRefTypeAnalysisContext);
            if (aIsRef && bIsRef)
                return true; // ceq compares any two managed references
            return aWidth < 0 && bWidth < 0; // ceq also pairs two native ints
        }
        return false;
    }

    // The stack kinds a binary numeric op can combine: arithmetic accepts
    // integral and float operands (managed pointers in add/sub for pointer
    // arithmetic), bitwise and shift ops accept integral kinds only. A null
    // type is an unknown emission and is left alone.
    private static bool NumericStackKind(OpCode opCode, TypeAnalysisContext? type) => type switch
    {
        null => true,
        ByRefTypeAnalysisContext => opCode is OpCode.Add or OpCode.Subtract,
        _ => IntegralStackWidth(type) != 0
            || type.FullName is "System.Single" or "System.Double"
                && opCode is OpCode.Add or OpCode.Subtract or OpCode.Multiply
                    or OpCode.Divide or OpCode.Modulo
    };

    // Equality between integral or pointer operands lowers to ceq on two native
    // ints - every side converts through conv.i (a zero literal is then the
    // native null-address test). Returns false when an operand cannot become a
    // native int, leaving callers to try the reference form or default.
    private static bool TryEmitNativeIntEquality(Instruction instruction, MethodAnalysisContext context,
        MethodDefinition method, Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine)
    {
        var instructions = method.CilMethodBody!.Instructions;
        var nativeInt = context.AppContext.SystemTypes.SystemIntPtrType;
        var operands = instruction.Operands.Skip(1).Take(2).ToList();
        foreach (var operand in operands)
        {
            var emitted = NaturalEmittedType(operand, context);
            if (emitted == null || emitted is not (PointerTypeAnalysisContext or ByRefTypeAnalysisContext)
                && !IsNativeHandleType(emitted) && IntegralStackWidth(emitted) == 0)
                return false; // a struct, float or reference side cannot lower to a native int
            // conv.* rejects managed pointers, so a `&` side only reaches native
            // int when its pointee can: `&x` lowers to the dereferenced value.
            if (!StackContractSatisfied(emitted, nativeInt, context, convertByRef: true))
                return false;
        }
        foreach (var operand in operands)
        {
            LoadOperand(operand, method, locals, writeLine, null, context);
            EmitStackCoerce(NaturalEmittedType(operand, context), nativeInt, method, context, true);
        }
        instructions.Add(CilOpCodes.Ceq);
        if (instruction.OpCode == OpCode.CheckNotEqual)
        {
            instructions.Add(CilOpCodes.Ldc_I4_0);
            instructions.Add(CilOpCodes.Ceq);
        }
        return true;
    }

    // An equality test between incompatible stack kinds still has an honest answer
    // in IL: boxed values compare by reference, and a zero literal is the native
    // code's null test. Emits both operands as references followed by ceq (with the
    // != inversion for CheckNotEqual). Returns false when a side cannot become a
    // reference, leaving callers to emit the default false.
    private static bool TryEmitReferenceEquality(Instruction instruction, MethodAnalysisContext context,
        MethodDefinition method, Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine)
    {
        var instructions = method.CilMethodBody!.Instructions;
        var operands = instruction.Operands.Skip(1).Take(2).ToList();
        // Verify every side first: a partial emission would leave a stray value on
        // the stack when the fallback default is emitted instead.
        var emitted = new List<TypeAnalysisContext?>(operands.Count);
        foreach (var operand in operands)
        {
            if (operand is Immediate { Value: 0 })
            {
                emitted.Add(null); // the zero literal becomes ldnull below
                continue;
            }

            var emittedType = NaturalEmittedType(operand, context);
            if (emittedType is null or PointerTypeAnalysisContext or ByRefTypeAnalysisContext
                || IsNativeHandleType(emittedType))
                return false; // pointer and unknown emissions cannot become references
            if ((emittedType.IsValueType || emittedType is GenericParameterTypeAnalysisContext)
                && !TypeTokenUsableFrom(emittedType, context))
                return false; // a value side that cannot box cannot become a reference either
            emitted.Add(emittedType);
        }

        for (var i = 0; i < operands.Count; i++)
        {
            if (emitted[i] == null)
            {
                // The native test compared against zero - on a managed operand
                // that is exactly a null comparison.
                instructions.Add(CilOpCodes.Ldnull);
                continue;
            }

            LoadOperand(operands[i], method, locals, writeLine, null, context);
            if (emitted[i] is { IsValueType: true } or GenericParameterTypeAnalysisContext)
                instructions.Add(CilOpCodes.Box, emitted[i]!.ToTypeSignature().ToTypeDefOrRef());
            // Reference-kind values pass through as they are.
        }

        instructions.Add(CilOpCodes.Ceq);
        if (instruction.OpCode == OpCode.CheckNotEqual)
        {
            instructions.Add(CilOpCodes.Ldc_I4_0);
            instructions.Add(CilOpCodes.Ceq);
        }
        return true;
    }

    // IsAssignableTo compares context objects by reference, but the emitter sees distinct
    // context instances for the same instantiated type (e.g. a base generic declaring type
    // vs. the method's declaring type). Falling back to a name-based hierarchy walk keeps
    // the cast honest while avoiding no-op castclass instructions ILVerify rejects
    // (base `this` calls and delegate constructor targets).
    private static bool IsAssignableToLoose(TypeAnalysisContext derivedType, TypeAnalysisContext baseType)
    {
        if (derivedType.IsAssignableTo(baseType))
            return true;

        // Every reference type is assignable to System.Object, even when the base-type
        // chain stops at an unresolved referenced type.
        if (baseType.FullName == "System.Object" && !derivedType.IsValueType)
            return true;

        var current = derivedType;
        while (current != null)
        {
            if (current.FullName == baseType.FullName)
                return true;
            // Generic instances resolved from Il2CppType leave DefaultBaseType unset; the
            // definition's base is the correct continuation for a name-based walk.
            current = current.BaseType
                ?? (current as GenericInstanceTypeAnalysisContext)?.GenericType.BaseType;
        }

        return derivedType.InterfaceContexts.Any(@interface => IsAssignableToLoose(@interface, baseType));
    }

    // True when ToTypeSignature can produce a usable operand for box/unbox/castclass.
    // Reduced test fixtures may not carry the AsmResolver metadata the real pipeline
    // always has, in which case the coercion is skipped rather than fatal.
    private static bool CanEmitTypeToken(TypeAnalysisContext? type) => type switch
    {
        null => false,
        GenericInstanceTypeAnalysisContext generic => CanEmitTypeToken(generic.GenericType)
            && generic.GenericArguments.All(CanEmitTypeToken),
        WrappedTypeAnalysisContext wrapped => CanEmitTypeToken(wrapped.ElementType),
        GenericParameterTypeAnalysisContext or SentinelTypeAnalysisContext
            or RuntimeClassTypeAnalysisContext or RuntimeMethodInfoAnalysisContext
            or RuntimeFieldInfoAnalysisContext or StaticFieldStorageTypeAnalysisContext
            or RgctxTableTypeAnalysisContext or MethodRgctxTableTypeAnalysisContext => true,
        _ => type.GetExtraData<TypeDefinition>("AsmResolverType") != null
    };

    // CanEmitTypeToken answers whether a token can be produced for the type; this answers
    // whether the caller may legally name it. Shared-generic recovery composes instances
    // over corlib-internal marker types (List<System.Int32Enum>) that produce a token the
    // verifier rejects, so every token-bearing op routes through here instead of
    // CanEmitTypeToken alone.
    private static bool TypeTokenUsableFrom(TypeAnalysisContext? type, MethodAnalysisContext? context) =>
        type != null
            && !ContainsSharedEnumMarker(type)
            && CanEmitTypeToken(type)
            && (context?.DeclaringType == null
                || (Analysis.InaccessibleCalleeRecovery.IsVisibleType(type, context.DeclaringType)
                    && DelegateArgumentsCallerOwned(type, context)));

    private static bool CalleeUsesSharedEnumMarker(MethodAnalysisContext method) =>
        method.DeclaringType != null && ContainsSharedEnumMarker(method.DeclaringType)
        || ContainsSharedEnumMarker(method.ReturnType)
        || method.Parameters.Any(parameter => ContainsSharedEnumMarker(parameter.ParameterType))
        || method is ConcreteGenericMethodAnalysisContext generic
            && (generic.TypeGenericParameters.Any(ContainsSharedEnumMarker)
                || generic.MethodGenericParameters.Any(ContainsSharedEnumMarker));

    private static bool CalleeUsableFrom(MethodAnalysisContext method, MethodAnalysisContext context) =>
        !CalleeUsesSharedEnumMarker(method)
        && Analysis.InaccessibleCalleeRecovery.IsVisibleFrom(method, context);

    private sealed record FieldAddressArithmetic(IOperand Base, TypeAnalysisContext Owner, FieldAnalysisContext Field);
    private sealed record NativeAddressRoot(IOperand Base, TypeAnalysisContext Owner, long Offset, bool IsStatic = false);

    // `&T`/`ref T` +|- a byte-offset literal is the address of the instance field at
    // that offset, not integer math. The base is whichever operand emits as a managed
    // pointer or reference; the other must be a non-negative literal.
    private static FieldAddressArithmetic? TryResolveFieldAddressArithmetic(Instruction instruction,
        MethodAnalysisContext context)
    {
        for (var i = 1; i <= 2; i++)
        {
            var baseOperand = instruction.Operands[i];
            var offsetOperand = instruction.Operands[3 - i];
            if (offsetOperand is not Immediate { Value: >= 0 } offset)
                continue;
            // `literal - pointer` has no meaning; only the pointer-on-the-left form.
            if (instruction.OpCode == OpCode.Subtract && i == 2)
                continue;
            var root = TryResolveNativeAddressRoot(baseOperand, context, []);
            if (root == null)
                continue;
            var totalOffset = root.Offset + (instruction.OpCode == OpCode.Subtract ? -offset.Value : offset.Value);
            if (totalOffset < 0)
                continue;
            var field = root.IsStatic
                ? Analysis.MetadataResolver.FindStaticFieldAtOffset(root.Owner, totalOffset)
                : Analysis.MetadataResolver.FindInstanceFieldAtOffset(root.Owner, totalOffset);
            if (field is not null
                && CanEmitTypeToken(field.FieldType))
                return new FieldAddressArithmetic(root.Base, root.Owner, field);
        }
        return null;
    }

    // Native code commonly keeps `this + A` in a register, then adds B before
    // storing. The first add may already look like a managed field value, but the
    // second still operates on its address. Flatten that unique add chain back to
    // the managed root so A+B resolves to the actual field instead of `field + B`.
    private static NativeAddressRoot? TryResolveNativeAddressRoot(IOperand operand,
        MethodAnalysisContext context, HashSet<LocalVariable> visited)
    {
        var staticFieldsOffset = context.AppContext.Binary.is32Bit ? 0x5C : 0xB8;
        if (operand is AddressOf { Target: FieldReference addressed }
            && !addressed.Field.IsStatic
            && EmittedOperandType(addressed.Local, context) is { IsValueType: false } rootOwner
            // FieldReference.Offset is the original absolute native offset from
            // the object, including any value-type container path.
            && addressed.Offset >= 0)
            return new NativeAddressRoot(addressed.Local, rootOwner, addressed.Offset);

        if (operand is MemoryOperand
            {
                Base: LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType: var staticOwner } },
                Index: null, Scale: 0, Addend: var staticOffset
            } && staticOffset == staticFieldsOffset)
            return new NativeAddressRoot(operand, staticOwner, 0, true);

        if (operand is LocalVariable local && visited.Add(local))
        {
            Instruction? definition = null;
            foreach (var candidate in context.ControlFlowGraph!.Instructions)
            {
                if (!ReferenceEquals(candidate.Destination, local))
                    continue;
                if (definition != null)
                    return null;
                definition = candidate;
            }

            if (definition is { OpCode: OpCode.Add or OpCode.Subtract, Operands.Count: >= 3 })
            {
                for (var i = 1; i <= 2; i++)
                {
                    if (definition.Operands[3 - i] is not Immediate { Value: >= 0 } displacement
                        || definition.OpCode == OpCode.Subtract && i == 2)
                        continue;
                    var root = TryResolveNativeAddressRoot(definition.Operands[i], context, visited);
                    if (root == null)
                        continue;
                    var offset = root.Offset
                        + (definition.OpCode == OpCode.Subtract ? -displacement.Value : displacement.Value);
                    return offset >= 0 ? root with { Offset = offset } : null;
                }
                return null;
            }
        }

        var owner = EmittedOperandType(operand, context) switch
        {
            ByRefTypeAnalysisContext byRef => byRef.ElementType,
            PointerTypeAnalysisContext => null,
            { IsValueType: false } reference => reference,
            // ldarg.0 of a struct method's own `this` pushes &T even though the
            // local is declared T, so the addend still reaches a field.
            { IsValueType: true } valueType when operand is LocalVariable { IsThis: true }
                => valueType,
            _ => null
        };
        return owner == null ? null : new NativeAddressRoot(operand, owner, 0);
    }

    // The shared operand type for a binary instruction: the widest non-literal
    // operand, or (for value-producing ops) the destination. Comparison destinations
    // are the bool result, never the compared type, so they must not seed it.
    private static TypeAnalysisContext? BinaryOperandType(Instruction instruction, MethodAnalysisContext context,
        bool allowDestination)
    {
        TypeAnalysisContext? picked = null;
        TypeAnalysisContext? pickedFloat = null;
        var pickedWidth = 0;
        foreach (var operand in instruction.Operands.Skip(1))
        {
            var emitted = EmittedOperandType(operand, context);
            // A managed pointer operand participates through its dereferenced
            // element (conv/binary ops reject `&`), so the element's width - not
            // the pointer kind - decides the shared numeric contract.
            var stackType = emitted is ByRefTypeAnalysisContext byRefOperand
                ? byRefOperand.ElementType
                : emitted;
            stackType = EnumStackType(stackType);
            if (stackType?.FullName is "System.Single" or "System.Double")
            {
                if (pickedFloat == null || stackType.FullName == "System.Double")
                    pickedFloat = stackType;
                continue;
            }
            var width = IntegralStackWidth(stackType);
            if (width == 0)
                continue;
            if (width < 0)
                // Pointer/byref/native-int operands make the operation native-int;
                // returning IntPtr (not the operand's own type) keeps zero literals
                // as `conv.i` instead of an invalid null/pointer confusion.
                return context.AppContext.SystemTypes.SystemIntPtrType;
            if (width > pickedWidth)
            {
                picked = stackType;
                pickedWidth = width;
            }
        }

        if (pickedFloat != null)
            return pickedFloat;
        if (picked != null || !allowDestination)
            return picked;

        var destination = EnumStackType(EmittedOperandType(instruction.Operands[0], context));
        if (IntegralStackWidth(destination) != 0)
            return destination;

        // All-literal arithmetic (e.g. native pointer math kept as ldc+add) still
        // produces a concrete width on the stack: the widest literal's natural
        // emission. Naming it keeps mixed-width adds valid and result coercion honest.
        foreach (var operand in instruction.Operands.Skip(1))
            if (operand is Immediate literal)
            {
                var literalType = EmittedImmediateType(literal, null, context);
                if (IntegralStackWidth(literalType) > pickedWidth)
                {
                    picked = literalType;
                    pickedWidth = IntegralStackWidth(literalType);
                }
            }
        return picked;
    }

    private static TypeAnalysisContext? EnumStackType(TypeAnalysisContext? type)
    {
        var genericDefinition = (type as GenericInstanceTypeAnalysisContext)?.GenericType;
        if (type is not { IsEnumType: true } && genericDefinition is not { IsEnumType: true })
            return type;
        return type!.DefaultEnumUnderlyingType
            ?? genericDefinition?.DefaultEnumUnderlyingType
            ?? type.AppContext.SystemTypes.SystemInt32Type;
    }

    // The operation cannot be represented as legal IL (e.g. a bitwise op on a
    // float or reference operand). Emit the diagnostic and an exception, the same
    // honest contract as unmanaged memory loads.
    private static void EmitUnrecoverableOperation(MethodDefinition method, IMethodDescriptor writeLine, string detail)
    {
        var instructions = method.CilMethodBody!.Instructions;
        var module = method.DeclaringModule!;
        instructions.Add(CilOpCodes.Ldstr, Diagnostic(detail));
        instructions.Add(CilOpCodes.Call, writeLine);
        var exceptionCtor = module.CorLibTypeFactory.CorLibScope
            .CreateTypeReference("System", "Exception")
            .CreateMemberReference(".ctor", MethodSignature.CreateInstance(module.CorLibTypeFactory.Void, [module.CorLibTypeFactory.String]));
        instructions.Add(CilOpCodes.Ldstr, Diagnostic(detail));
        instructions.Add(CilOpCodes.Newobj, exceptionCtor);
        instructions.Add(CilOpCodes.Throw);
    }

    // A recovered block-memory import. memcpy lowers to cpblk and memset to initblk;
    // memmove cannot share cpblk because CIL gives cpblk no overlap semantics, so it
    // calls System.Buffer.MemoryCopy - the runtime's own overlap-safe byte move and no
    // external dependency. The proofs the recovery pass made are repeated before
    // anything is pushed: propagation can swap operand locals after the rewrite, and
    // an operand that can no longer be proven must fail honestly rather than let a
    // byte copy stand in for a write-barriered store.
    private static void EmitBlockMemoryOperation(Instruction instruction, MethodAnalysisContext context,
        MethodDefinition method, Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine)
    {
        var instructions = method.CilMethodBody!.Instructions;
        var module = method.DeclaringModule!;

        if (instruction.Operands.Count is < 3 or > 4)
        {
            EmitUnrecoverableOperation(method, writeLine, $"Malformed block memory operation: {instruction}");
            return;
        }

        var destination = instruction.Operands[0];
        var content = instruction.Operands[1];
        var count = instruction.Operands[2];

        var contentProvable = instruction.OpCode == OpCode.MemorySet
            ? Analysis.BlockMemoryImportRecovery.IsScalarOperand(content, context)
            : Analysis.BlockMemoryImportRecovery.IsPointerOperandRepresentable(content, context);
        if (!Analysis.BlockMemoryImportRecovery.IsProvablyReferenceFreeRegion(destination, context)
            || !contentProvable
            || !Analysis.BlockMemoryImportRecovery.IsScalarOperand(count, context))
        {
            EmitUnrecoverableOperation(method, writeLine, $"Unproven block memory operand: {instruction}");
            return;
        }

        switch (instruction.OpCode)
        {
            case OpCode.MemoryCopy:
                // cpblk accepts a managed pointer or native int for both addresses.
                EmitBlockPointerOperand(destination, false, context, method, locals, writeLine);
                EmitBlockPointerOperand(content, false, context, method, locals, writeLine);
                EmitBlockSizeOperand(count, context, method, locals, writeLine);
                instructions.Add(CilOpCodes.Cpblk);
                break;
            case OpCode.MemorySet:
                EmitBlockPointerOperand(destination, false, context, method, locals, writeLine);
                // initblk's fill is a 32-bit value; libc memsets with its low byte.
                LoadOperand(content, method, locals, writeLine, null, context);
                instructions.Add(CilOpCodes.Conv_U4);
                EmitBlockSizeOperand(count, context, method, locals, writeLine);
                instructions.Add(CilOpCodes.Initblk);
                break;
            case OpCode.MemoryMove:
                // Buffer.MemoryCopy(void* source, void* destination, ulong destinationSizeInBytes,
                // ulong sourceBytesToCopy): sourceBytesToCopy <= destinationSizeInBytes always
                // holds when both are the same byte count.
                EmitBlockPointerOperand(content, true, context, method, locals, writeLine);
                EmitBlockPointerOperand(destination, true, context, method, locals, writeLine);
                EmitBlockLengthOperand(count, context, method, locals, writeLine);
                EmitBlockLengthOperand(count, context, method, locals, writeLine);
                instructions.Add(CilOpCodes.Call, module.CorLibTypeFactory.CorLibScope
                    .CreateTypeReference("System", "Buffer")
                    .CreateMemberReference("MemoryCopy", MethodSignature.CreateStatic(
                        module.CorLibTypeFactory.Void,
                        [module.CorLibTypeFactory.Void.MakePointerType(),
                            module.CorLibTypeFactory.Void.MakePointerType(),
                            module.CorLibTypeFactory.UInt64,
                            module.CorLibTypeFactory.UInt64])));
                break;
        }

        // libc memcpy/memset/memmove return the destination pointer; a still-read
        // result local receives it as a native int.
        if (instruction.Operands.Count == 4 && instruction.Operands[3] is { } result)
        {
            EmitBlockPointerOperand(destination, true, context, method, locals, writeLine);
            StoreToOperand(result, method, locals, writeLine, context);
        }
    }

    // Loads a block-op pointer operand in a shape cpblk/initblk accept: managed
    // pointers and native ints pass through, integral values and literals are
    // extended. forceNativeInt converts managed pointers too, for the void*
    // parameters of Buffer.MemoryCopy.
    private static void EmitBlockPointerOperand(IOperand operand, bool forceNativeInt, MethodAnalysisContext context,
        MethodDefinition method, Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine)
    {
        var width = operand is Immediate ? 8 : IntegralStackWidth(EmittedOperandType(operand, context));
        LoadOperand(operand, method, locals, writeLine, null, context);
        if (forceNativeInt || width != -1)
            method.CilMethodBody!.Instructions.Add(CilOpCodes.Conv_U);
    }

    // A block size is size_t: native unsigned int on the stack.
    private static void EmitBlockSizeOperand(IOperand operand, MethodAnalysisContext context,
        MethodDefinition method, Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine)
    {
        LoadOperand(operand, method, locals, writeLine, null, context);
        if (operand is Immediate || IntegralStackWidth(EmittedOperandType(operand, context)) != -1)
            method.CilMethodBody!.Instructions.Add(CilOpCodes.Conv_U);
    }

    // Buffer.MemoryCopy's sizes are ulong.
    private static void EmitBlockLengthOperand(IOperand operand, MethodAnalysisContext context,
        MethodDefinition method, Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine)
    {
        LoadOperand(operand, method, locals, writeLine, null, context);
        method.CilMethodBody!.Instructions.Add(CilOpCodes.Conv_U8);
    }

    // Integer ops on operands that cannot legally sit in an integer slot are
    // native idioms the lifter mistyped: `&slot | N`/`&slot + N` names a field
    // inside a struct local, `packed >> 32`/`packed & mask` selects a field out
    // of a value lifted as one unit, and `x ^ x`/`x - x` folds to zero for any
    // operand kind. Recovers the managed equivalent when layout allows it.
    private static bool TryEmitRecoveredIntegerOperation(Instruction instruction, MethodAnalysisContext context,
        MethodDefinition method, Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine)
    {
        if (instruction.OpCode is >= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual)
            return false;

        var instructions = method.CilMethodBody!.Instructions;
        var destinationType = DestinationType(instruction.Operands[0])
            ?? (instruction.Operands[0] is LocalVariable resultLocal ? EmittedLocalType(resultLocal, context) : null);

        // `x ^ x`/`x - x` is provably zero even when the operand's own type is lost.
        if (instruction.OpCode is OpCode.Xor or OpCode.Subtract
            && IsSameStorage(instruction.Operands[1], instruction.Operands[2])
            && IntegralStackWidth(EmittedOperandType(instruction.Operands[1], context)) <= 0)
        {
            instructions.Add(CilOpCodes.Ldc_I4_0);
            CoerceOrDefault(context.AppContext.SystemTypes.SystemInt32Type, destinationType, method, context);
            StoreToOperand(instruction.Operands[0], method, locals, writeLine, context);
            return true;
        }

        if (TryEmitFloatCarrierIntegerOperation(instruction, context, method, locals, writeLine))
            return true;

        // `&local OP const` computes the address of a field inside the local's
        // value type; when a field sits at exactly that offset and can feed the
        // destination, the whole operation is the field access itself.
        if (instruction.OpCode is OpCode.Or or OpCode.Add
            && FindAddressOffsetField(instruction, context, out var address, out var addressField)
            && FieldUsableFrom(addressField, context,
                receiverType: addressField.IsStatic ? null : EmittedOperandType(address, context))
            && (ThisConstructorCallPlan.SameTypeIdentity(addressField.FieldType, destinationType)
                || IntegralStackWidth(addressField.FieldType) != 0
                    && destinationType is not ByRefTypeAnalysisContext and not PointerTypeAnalysisContext
                    && IntegralStackWidth(destinationType) != 0)
            && EmitManagedAddress(address, method, context, locals, writeLine))
        {
            instructions.Add(CilOpCodes.Ldfld,
                FieldDescriptorFor(addressField, EmittedOperandType(address, context)));
            CoerceOrDefault(addressField.FieldType, destinationType, method, context);
            StoreToOperand(instruction.Operands[0], method, locals, writeLine, context);
            return true;
        }

        // `packed >> N`/`packed OP mask`: the surviving bytes are a field.
        if (TryGetPackedFieldAccess(instruction, context, out var packed, out var packedField, out var otherOperand)
            && FieldUsableFrom(packedField, context,
                receiverType: packedField.IsStatic ? null : EmittedOperandType(packed, context))
            && EmitManagedAddress(packed, method, context, locals, writeLine))
        {
            var fieldType = packedField.FieldType;
            instructions.Add(CilOpCodes.Ldfld,
                FieldDescriptorFor(packedField, EmittedOperandType(packed, context)));
            if (otherOperand != null)
            {
                // The op applies to the low-word field only; that is exact for the
                // masked range (and for wraps/shifts the field itself is the answer).
                LoadOperand(otherOperand, method, locals, writeLine, fieldType, context);
                CoerceOrDefault(EmittedOperandType(otherOperand, context, fieldType), fieldType, method, context);
                instructions.Add(instruction.OpCode switch
                {
                    OpCode.And => new CilInstruction(CilOpCodes.And),
                    OpCode.Or => new CilInstruction(CilOpCodes.Or),
                    OpCode.Xor => new CilInstruction(CilOpCodes.Xor),
                    OpCode.Add => new CilInstruction(CilOpCodes.Add),
                    OpCode.Subtract => new CilInstruction(CilOpCodes.Sub),
                    OpCode.Multiply => new CilInstruction(CilOpCodes.Mul),
                    OpCode.Divide => new CilInstruction(CilOpCodes.Div),
                    OpCode.Modulo => new CilInstruction(CilOpCodes.Rem),
                    _ => new CilInstruction(CilOpCodes.Nop),
                });
            }
            CoerceOrDefault(fieldType, destinationType, method, context);
            StoreToOperand(instruction.Operands[0], method, locals, writeLine, context);
            return true;
        }

        return false;
    }

    // ARM64 `fmov` transfers identical bits between the FP and integer register
    // banks — `BitConverter.*To*Bits` in managed terms, never a `conv.*` numeric
    // conversion. A float-typed operand inside an integer-domain bitwise op is
    // therefore a proven bit reinterpretation: the operation is legal on the
    // same-width integer carrier. Reinterpret each float operand through
    // BitConverter, run the op on the carrier, and produce a float back only at
    // a proven FP consumer — a destination of the carrier's float type. Any
    // width disagreement, or a non-integral operand, has no honest carrier and
    // leaves the operation unrecoverable.
    private static bool TryEmitFloatCarrierIntegerOperation(Instruction instruction, MethodAnalysisContext context,
        MethodDefinition method, Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine)
    {
        if (instruction.OpCode is not (OpCode.And or OpCode.Or or OpCode.Xor
                or OpCode.Not or OpCode.ShiftLeft or OpCode.ShiftRight))
            return false;

        var systemTypes = context.AppContext.SystemTypes;
        var isShift = instruction.OpCode is OpCode.ShiftLeft or OpCode.ShiftRight;
        var operands = instruction.Operands.Skip(1).ToArray();

        // The carrier width is the single width the op's value operands provably
        // share: a float operand contributes the width of its bit pattern, an
        // integral operand its stack width, a native int or pointer its register
        // width. Literals adapt to the carrier but one that does not fit it is a
        // width disagreement of its own. A shift's amount joins no consensus —
        // the CIL ops take an i32/n-int count regardless.
        var carrierWidth = 0;
        var sawFloat = false;
        for (var i = 0; i < operands.Length; i++)
        {
            var joinsCarrier = !(isShift && i == 1);
            if (operands[i] is Immediate immediate)
            {
                if (joinsCarrier && carrierWidth == 4
                    && unchecked((long)(int)immediate.Value) != immediate.Value
                    && unchecked((long)(uint)immediate.Value) != immediate.Value)
                    return false;
                continue;
            }
            var emitted = EmittedOperandType(operands[i], context);
            int width;
            if (emitted?.FullName is "System.Single" or "System.Double")
            {
                sawFloat = true;
                width = emitted.FullName == "System.Single" ? 4 : 8;
            }
            else if (emitted is ByRefTypeAnalysisContext)
                return false; // `&x` is a managed pointer, not bits a carrier can hold
            else
            {
                var integral = IntegralStackWidth(emitted);
                if (integral == 0)
                    return false;
                width = integral < 0 ? 8 : integral;
            }
            if (joinsCarrier && carrierWidth != 0 && carrierWidth != width)
                return false;
            if (joinsCarrier)
                carrierWidth = width;
        }
        if (!sawFloat || carrierWidth == 0)
            return false;

        // A float result comes back only at a proven FP consumer — a destination
        // of the carrier's own float type (`fmov` into a V register after the
        // integer op). An integral destination of any width is an honest
        // consumer: a narrower slot truncates exactly like a W-register read of
        // the X result, a wider one sees the zero-extension every ARM64 W-write
        // performs. Everything else — a `&` slot the carrier cannot enter, a
        // struct/reference destination no stack coercion can satisfy, or a float
        // of the wrong width — has no honest store and stays unrecoverable.
        // These checks run before any instruction is emitted.
        var storeContract = StoreContract(instruction.Operands[0], context);
        TypeAnalysisContext? fpConsumer = null;
        if (storeContract != null)
        {
            if (storeContract is ByRefTypeAnalysisContext)
                return false;
            var destinationWidth = storeContract.FullName == "System.Single" ? 4
                : storeContract.FullName == "System.Double" ? 8
                : IntegralStackWidth(storeContract);
            if (destinationWidth == 0)
                return false;
            if (storeContract.FullName is "System.Single" or "System.Double")
            {
                if (destinationWidth != carrierWidth)
                    return false;
                fpConsumer = storeContract;
            }
        }

        var instructions = method.CilMethodBody!.Instructions;
        var module = method.DeclaringModule!;
        var factory = module.CorLibTypeFactory;
        var bitConverter = factory.CorLibScope.CreateTypeReference("System", "BitConverter");
        var carrierType = carrierWidth == 4 ? systemTypes.SystemInt32Type : systemTypes.SystemInt64Type;

        for (var i = 0; i < operands.Length; i++)
        {
            var operand = operands[i];
            var emitted = operand is Immediate ? null : EmittedOperandType(operand, context);
            if (emitted?.FullName is "System.Single" or "System.Double")
            {
                // `fmov` between the banks: the float's own bits at its own
                // width, reinterpreted through BitConverter — the only legal
                // float → integer sequence.
                LoadOperand(operand, method, locals, writeLine, emitted, context);
                var single = emitted.FullName == "System.Single";
                instructions.Add(CilOpCodes.Call, bitConverter.CreateMemberReference(
                    single ? "SingleToInt32Bits" : "DoubleToInt64Bits",
                    MethodSignature.CreateStatic(single ? factory.Int32 : factory.Int64,
                        [single ? factory.Single : factory.Double])));
                if (isShift && i == 1 && !single)
                    // the count is i32-shaped: keep the carrier's low bits
                    EmitStackCoerceOrDefault(systemTypes.SystemInt64Type, systemTypes.SystemInt32Type, method, context);
            }
            else if (isShift && i == 1)
                LoadOperandIntoSlot(operand, systemTypes.SystemInt32Type, context, method, locals, writeLine);
            else
                LoadOperandIntoSlot(operand, carrierType, context, method, locals, writeLine);
        }

        instructions.Add(instruction.OpCode switch
        {
            OpCode.And => new CilInstruction(CilOpCodes.And),
            OpCode.Or => new CilInstruction(CilOpCodes.Or),
            OpCode.Xor => new CilInstruction(CilOpCodes.Xor),
            OpCode.Not => new CilInstruction(CilOpCodes.Not),
            OpCode.ShiftLeft => new CilInstruction(CilOpCodes.Shl),
            OpCode.ShiftRight => new CilInstruction(CilOpCodes.Shr),
            _ => new CilInstruction(CilOpCodes.Nop),
        });

        // The carrier's unsigned twin as the result type: a wider integral
        // destination then coerces with conv.u*, reproducing the zero-extension
        // an ARM64 W-register write always performs on the X register.
        TypeAnalysisContext resultType = carrierWidth == 4
            ? systemTypes.SystemUInt32Type
            : systemTypes.SystemUInt64Type;
        if (fpConsumer != null)
        {
            // The store is a V-register float again: reinterpret the carrier
            // result back through the matching `fmov`.
            var single = fpConsumer.FullName == "System.Single";
            instructions.Add(CilOpCodes.Call, bitConverter.CreateMemberReference(
                single ? "Int32BitsToSingle" : "Int64BitsToDouble",
                MethodSignature.CreateStatic(single ? factory.Single : factory.Double,
                    [single ? factory.Int32 : factory.Int64])));
            resultType = fpConsumer;
        }

        CoerceOrDefault(resultType, storeContract, method, context);
        StoreToOperand(instruction.Operands[0], method, locals, writeLine, context);
        return true;
    }

    private static bool TryEmitUnityVectorOperation(Instruction instruction, MethodAnalysisContext context,
        MethodDefinition method, Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine)
    {
        if (instruction.OpCode is not (OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.Divide or OpCode.Negate))
            return false;

        var resultType = StoreContract(instruction.Operands[0], context);
        if (!IsUnityVector(resultType) && instruction.Operands[0] is LocalVariable result)
        {
            var useTypes = context.ControlFlowGraph!.Instructions
                .Where(use => use is { OpCode: OpCode.Move, Operands.Count: >= 2 }
                    && ReferenceEquals(use.Operands[1], result))
                .Select(use => DestinationType(use.Operands[0]))
                .Where(IsUnityVector)
                .DistinctBy(type => type!.FullName)
                .ToList();
            if (useTypes.Count == 1)
                resultType = useTypes[0];
        }
        if (!IsUnityVector(resultType))
            resultType = instruction.Operands.Skip(1)
                .Select(operand => EmittedOperandType(operand, context))
                .FirstOrDefault(IsUnityVector);
        if (!IsUnityVector(resultType))
            return false;

        var operatorName = instruction.OpCode switch
        {
            OpCode.Add => "op_Addition",
            OpCode.Subtract => "op_Subtraction",
            OpCode.Multiply => "op_Multiply",
            OpCode.Divide => "op_Division",
            OpCode.Negate => "op_UnaryNegation",
            _ => null,
        };
        var @operator = resultType!.Methods.FirstOrDefault(candidate => candidate is
            { IsStatic: true }
            && candidate.Name == operatorName
            && ThisConstructorCallPlan.SameTypeIdentity(candidate.ReturnType, resultType)
            && candidate.Parameters.Count == (instruction.OpCode == OpCode.Negate ? 1 : 2)
            && CanLoadVectorOperand(instruction.Operands[1], candidate.Parameters[0].ParameterType, context)
            && (instruction.OpCode == OpCode.Negate
                || CanLoadVectorOperand(instruction.Operands[2], candidate.Parameters[1].ParameterType, context)));
        if (@operator == null)
            return false;

        LoadVectorOperand(instruction.Operands[1], @operator.Parameters[0].ParameterType,
            context, method, locals, writeLine);
        if (instruction.OpCode != OpCode.Negate)
            LoadVectorOperand(instruction.Operands[2], @operator.Parameters[1].ParameterType,
                context, method, locals, writeLine);
        method.CilMethodBody!.Instructions.Add(CilOpCodes.Call, @operator.ToMethodDescriptor());
        StoreToOperand(instruction.Operands[0], method, locals, writeLine, context);
        return true;
    }

    private static bool TryEmitUnityVectorMinMax(Instruction instruction, MethodAnalysisContext context,
        MethodDefinition method, Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine)
    {
        var vector = StoreContract(instruction.Operands[0], context);
        if (!IsUnityVector(vector))
            vector = instruction.Operands.Skip(1)
                .Select(operand => EmittedOperandType(operand, context))
                .FirstOrDefault(IsUnityVector);
        if (!IsUnityVector(vector))
            return false;

        LoadVectorOperand(instruction.Operands[1], vector!, context, method, locals, writeLine);
        LoadVectorOperand(instruction.Operands[2], vector!, context, method, locals, writeLine);
        var signature = vector!.ToTypeSignature();
        var target = new MemberReference(signature.ToTypeDefOrRef(),
            instruction.OpCode == OpCode.VectorMin ? "Min" : "Max",
            MethodSignature.CreateStatic(signature, [signature, signature]));
        method.CilMethodBody!.Instructions.Add(CilOpCodes.Call, target);
        StoreToOperand(instruction.Operands[0], method, locals, writeLine, context);
        return true;
    }

    private static bool TryEmitUnityQuaternionInternal(Instruction instruction, MethodAnalysisContext target,
        MethodAnalysisContext context, MethodDefinition method,
        Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine)
    {
        if (instruction.OpCode != OpCode.Call || instruction.Operands.Count < 3 || !target.IsStatic
            || target.Parameters.Count != 1 || target.DeclaringType?.DefaultFullName != "UnityEngine.Quaternion"
            || target.Name is not ("Internal_FromEulerRad" or "Internal_ToEulerRad"))
            return false;

        var quaternion = target.DeclaringType;
        var vector = target.Name == "Internal_FromEulerRad" ? target.Parameters[0].ParameterType : target.ReturnType;
        var multiply = vector.Methods.FirstOrDefault(candidate => candidate is
            { Name: "op_Multiply", IsStatic: true, Parameters.Count: 2 }
            && ThisConstructorCallPlan.SameTypeIdentity(candidate.ReturnType, vector)
            && ThisConstructorCallPlan.SameTypeIdentity(candidate.Parameters[0].ParameterType, vector)
            && candidate.Parameters[1].ParameterType.DefaultFullName == "System.Single");
        if (multiply == null)
            return false;

        var publicMethod = target.Name == "Internal_FromEulerRad"
            ? quaternion.Methods.FirstOrDefault(candidate => candidate is
                { Name: "Euler", IsStatic: true, Parameters.Count: 1 }
                && ThisConstructorCallPlan.SameTypeIdentity(candidate.Parameters[0].ParameterType, vector))
            : quaternion.Methods.FirstOrDefault(candidate => candidate is
                { Name: "get_eulerAngles", IsStatic: false, Parameters.Count: 0 });
        if (publicMethod == null)
            return false;

        LoadOperandIntoSlot(instruction.Operands[2], target.Parameters[0].ParameterType,
            context, method, locals, writeLine);
        if (target.Name == "Internal_FromEulerRad")
        {
            method.CilMethodBody!.Instructions.Add(CilOpCodes.Ldc_R4, 57.29578f);
            method.CilMethodBody.Instructions.Add(CilOpCodes.Call, multiply.ToMethodDescriptor());
            method.CilMethodBody.Instructions.Add(CilOpCodes.Call, publicMethod.ToMethodDescriptor());
        }
        else
        {
            method.CilMethodBody!.Instructions.Add(CilOpCodes.Call, publicMethod.ToMethodDescriptor());
            method.CilMethodBody.Instructions.Add(CilOpCodes.Ldc_R4, 0.017453292f);
            method.CilMethodBody.Instructions.Add(CilOpCodes.Call, multiply.ToMethodDescriptor());
        }

        EmitStackCoerceOrDefault(target.ReturnType, StoreContract(instruction.Operands[1], context), method, context);
        StoreToOperand(instruction.Operands[1], method, locals, writeLine, context);
        return true;
    }

    private static bool IsUnityVector(TypeAnalysisContext? type) =>
        type?.DefaultFullName is "UnityEngine.Vector2" or "UnityEngine.Vector3" or "UnityEngine.Vector4";

    private static bool CanLoadVectorOperand(IOperand operand, TypeAnalysisContext parameter,
        MethodAnalysisContext context)
    {
        if (operand is Vector128Literal)
            return IsUnityVector(parameter);
        var source = EmittedOperandType(operand, context, parameter);
        return StackContractSatisfied(source, parameter, context)
            || FindUnityVectorConversion(source, parameter) != null;
    }

    private static void LoadVectorOperand(IOperand operand, TypeAnalysisContext parameter,
        MethodAnalysisContext context, MethodDefinition method,
        Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine)
    {
        var source = EmittedOperandType(operand, context, parameter);
        if (FindUnityVectorConversion(source, parameter) is { } conversion)
        {
            LoadOperandIntoSlot(operand, source, context, method, locals, writeLine);
            method.CilMethodBody!.Instructions.Add(CilOpCodes.Call, conversion.ToMethodDescriptor());
            return;
        }
        LoadOperandIntoSlot(operand, parameter, context, method, locals, writeLine);
    }

    private static MethodAnalysisContext? FindUnityVectorConversion(TypeAnalysisContext? source,
        TypeAnalysisContext target)
    {
        if (!IsUnityVector(source) || !IsUnityVector(target)
            || ThisConstructorCallPlan.SameTypeIdentity(source, target))
            return null;
        return source!.Methods.Concat(target.Methods).FirstOrDefault(candidate => candidate is
            { Name: "op_Implicit", IsStatic: true, Parameters.Count: 1 }
            && ThisConstructorCallPlan.SameTypeIdentity(candidate.Parameters[0].ParameterType, source)
            && ThisConstructorCallPlan.SameTypeIdentity(candidate.ReturnType, target));
    }

    private static bool IsSameStorage(IOperand left, IOperand right) => (left, right) switch
    {
        (LocalVariable x, LocalVariable y) => ReferenceEquals(x, y),
        (FieldReference x, FieldReference y)
            => ReferenceEquals(x.Field, y.Field) && ReferenceEquals(x.Local, y.Local),
        (Immediate x, Immediate y) => x.Value == y.Value,
        _ => false,
    };

    // `&local OP const`: the constant names a byte offset inside the local's
    // value type. Returns the field sitting at exactly that offset.
    private static bool FindAddressOffsetField(Instruction instruction, MethodAnalysisContext context,
        out LocalVariable address, out FieldAnalysisContext field)
    {
        address = null!;
        field = null!;
        for (var i = 1; i <= 2; i++)
        {
            if (instruction.Operands[i] is not AddressOf { Target: LocalVariable target }
                || instruction.Operands[3 - i] is not Immediate { Value: >= 0 and <= int.MaxValue } offset)
                continue;
            var slotType = EmittedLocalType(target, context);
            if (slotType is not { IsValueType: true })
                continue;
            var candidate = FindInstanceField(slotType, (int)offset.Value, requireIntegral: false, context);
            if (candidate == null)
                continue;
            address = target;
            field = candidate;
            return true;
        }
        return false;
    }

    // `packed >> N` selects the field covering the surviving high bytes;
    // `packed OP mask` applies the op to the low-word field. Only fires when the
    // packed operand emits as a non-integral value type.
    private static bool TryGetPackedFieldAccess(Instruction instruction, MethodAnalysisContext context,
        out IOperand packed, out FieldAnalysisContext field, out IOperand? other)
    {
        packed = null!;
        field = null!;
        other = null;
        for (var i = 1; i <= 2; i++)
        {
            var operand = instruction.Operands[i];
            // A struct method's `this` is an address (`&T`), never a packed value;
            // `this + N` is field addressing and belongs to the field resolver.
            if (operand is LocalVariable { IsThis: true })
                continue;
            var operandType = EmittedOperandType(operand, context);
            if (operandType is not { IsValueType: true } || IntegralStackWidth(operandType) != 0)
                continue;
            var mate = instruction.Operands[3 - i];

            if (instruction.OpCode is OpCode.ShiftRight && i == 1
                && mate is Immediate { Value: >= 8 and < 64 } shift
                && shift.Value % 8 == 0
                && FindInstanceField(operandType, (int)(shift.Value / 8), requireIntegral: true, context) is { } shiftedField
                && PrimitiveByteSize(shiftedField.FieldType) * 8 >= 64 - shift.Value)
            {
                packed = operand;
                field = shiftedField;
                return true;
            }

            // The low word of an add/sub/mul/bitwise op is exact, so applying it
            // to the low-word field is honest. Division, modulo and shifts mix
            // across the whole value, so they never qualify here. Subtraction is
            // only honest when the packed value is the left operand.
            var lowWordOp = instruction.OpCode is OpCode.And or OpCode.Or or OpCode.Xor
                or OpCode.Add or OpCode.Multiply || instruction.OpCode is OpCode.Subtract && i == 1;
            if (lowWordOp
                && mate is Immediate { Value: var mask }
                && FindInstanceField(operandType, 0, requireIntegral: true, context) is { } lowField
                && unchecked((ulong)mask) <= LowMask(PrimitiveByteSize(lowField.FieldType)))
            {
                packed = operand;
                field = lowField;
                other = mate;
                return true;
            }
        }
        return false;
    }

    private static ulong LowMask(int byteSize) =>
        byteSize >= 8 ? ulong.MaxValue : byteSize <= 0 ? 0UL : (1UL << (byteSize * 8)) - 1;

    // Instance fields of a possibly generic-instance type, concretized against
    // the instance so field types come back instantiated.
    private static IEnumerable<FieldAnalysisContext> InstanceFields(TypeAnalysisContext type) =>
        type is GenericInstanceTypeAnalysisContext generic
            ? generic.GenericType.Fields.Select(field => field.MakeConcreteGenericField(generic.GenericArguments))
            : type.Fields;

    private static FieldAnalysisContext? FindInstanceField(TypeAnalysisContext? type, int offset, bool requireIntegral,
        MethodAnalysisContext context) =>
        type == null ? null
            : InstanceFields(type).FirstOrDefault(field => !field.IsStatic && field.Offset == offset
                && (!requireIntegral || IntegralStackWidth(field.FieldType) != 0)
                && FieldUsableFrom(field, context));

    private static bool CanEmitFieldToken(FieldAnalysisContext field) =>
        (field is ConcreteGenericFieldAnalysisContext concrete ? concrete.BaseFieldContext : field)
            .GetExtraData<FieldDefinition>("AsmResolverField") != null;

    internal static MethodAnalysisContext? BackingFieldConversion(FieldReference field,
        MethodAnalysisContext context)
    {
        if (field.Field.IsStatic || field.Field.DeclaringType is not { IsValueType: true } owner)
            return null;
        var receiverType = field.Containers.Count == 0
            ? EmittedLocalType(field.Local, context)
            : field.Containers[^1].FieldType;
        if (receiverType.FullName != owner.FullName)
            return null;
        return owner.Methods.FirstOrDefault(method => method.Name == "op_Implicit" && method.IsStatic
            && method.Parameters.Count == 1
            && method.Parameters[0].ParameterType.FullName == field.Field.FieldType.FullName
            && method.ReturnType.FullName == owner.FullName
            && (method.Attributes & MethodAttributes.MemberAccessMask) == MethodAttributes.Public);
    }

    internal static FieldReference? WholeValueContainerReference(FieldReference field,
        TypeAnalysisContext? valueType)
    {
        if (valueType == null || field.Containers.Count == 0 || field.Field.Offset != 0)
            return null;
        for (var i = field.Containers.Count - 1; i >= 0; i--)
        {
            var container = field.Containers[i];
            if (container.FieldType.FullName != valueType.FullName
                || field.Containers.Skip(i + 1).Any(inner => inner.Offset != 0))
                continue;
            return new FieldReference(container, field.Local, container.Offset,
                field.Containers.Take(i).ToArray());
        }
        return null;
    }

    internal static bool RuntimeFieldTokenUsableFrom(FieldAnalysisContext field,
        MethodAnalysisContext context)
    {
        if (!CanEmitFieldToken(field))
            return false;
        if (FieldUsableFrom(field, context))
            return true;
        if ((field.Attributes & FieldAttributes.FieldAccessMask) != FieldAttributes.Assembly
            || field.DeclaringType?.DeclaringAssembly is not { } declaringAssembly
            || context.DeclaringType?.DeclaringAssembly is not { } callerAssembly)
            return false;
        return ReferenceEquals(declaringAssembly, callerAssembly)
            || declaringAssembly.Name != null && declaringAssembly.Name == callerAssembly.Name;
    }

    // ldfld/ldflda need the field visible from the emitting method; writing or
    // taking the address additionally requires that initonly fields only be
    // touched from the declaring type's own constructor.
    // Instance field ops on a value type take a managed pointer receiver (`&T`),
    // not the value itself - ldfld/stfld on a bare T would read or mutate a temp
    // copy, and stfld initonly is only legal through `this`.
    private static TypeAnalysisContext? FieldBaseContract(FieldAnalysisContext field)
        => field.DeclaringType is { IsValueType: true } valueOwner
            ? new ByRefTypeAnalysisContext(valueOwner)
            : field.DeclaringType;

    private static TypeAnalysisContext? GenericDefinition(TypeAnalysisContext? type)
        => type is GenericInstanceTypeAnalysisContext instance ? instance.GenericType : type;

    internal static GenericInstanceTypeAnalysisContext? GenericFieldOwnerInstance(
        TypeAnalysisContext owner, FieldAnalysisContext field)
    {
        var declaring = GenericDefinition(field.DeclaringType);
        for (TypeAnalysisContext? current = owner; current != null;
             current = current.BaseType ?? (current as GenericInstanceTypeAnalysisContext)?.GenericType.BaseType)
            if (current is GenericInstanceTypeAnalysisContext instance
                && declaring != null
                && ThisConstructorCallPlan.SameTypeIdentity(declaring, instance.GenericType))
                return instance;
        return null;
    }

    // A field reference declared on a generic definition must be emitted on the
    // receiver's own instantiation: `ldfld !0 C`1::f` expects a `ref C`1` (the
    // unbound definition), which no stack value can be, while `C`1<!0>::f` is the
    // member the verifier actually accepts.
    private static IFieldDescriptor FieldDescriptorFor(FieldAnalysisContext field,
        TypeAnalysisContext? receiverType)
    {
        if (field is ConcreteGenericFieldAnalysisContext concrete)
        {
            // Metadata recovery can accidentally carry an outer generic owner's
            // instantiation onto an inner value-type field (for example
            // ValueTuple<Vector3,...>::Item1.y). The field still belongs to Vector3;
            // emitting it on ValueTuple produces a non-existent member reference.
            if (GenericDefinition(concrete.BaseFieldContext.DeclaringType) is { } baseDeclaring
                && GenericDefinition(concrete.DeclaringType) is { } concreteDeclaring
                && !ThisConstructorCallPlan.SameTypeIdentity(baseDeclaring, concreteDeclaring))
                return FieldDescriptorFor(concrete.BaseFieldContext, receiverType);
            return field.ToFieldDescriptor();
        }
        var receiverInstance = receiverType switch
        {
            GenericInstanceTypeAnalysisContext instance => instance,
            ByRefTypeAnalysisContext { ElementType: GenericInstanceTypeAnalysisContext instance } => instance,
            _ => null,
        };
        if (receiverInstance == null || GenericDefinition(field.DeclaringType) is not { } declaringDefinition
            || !ThisConstructorCallPlan.SameTypeIdentity(declaringDefinition, receiverInstance.GenericType))
            return field.ToFieldDescriptor();
        if (field.GetExtraData<FieldDefinition>("AsmResolverField") is not { } definition)
            return field.ToFieldDescriptor();
        MemberAccessibility.EnsureAccessible(definition);
        return new MemberReference(receiverInstance.ToTypeSignature().ToTypeDefOrRef(),
            field.Name, new FieldSignature(field.ToTypeSignature()));
    }

    // stfld on an initonly instance field only verifies when the receiver is the
    // literal `this` pointer (ILVerify requires actualThis.IsThisPtr) - a copy of
    // `this` parked in an ordinary local does not qualify even though it holds the
    // same object.
    private static bool RequiresThisPointerReceiver(FieldAnalysisContext field, MethodAnalysisContext context) =>
        (field.Attributes & FieldAttributes.InitOnly) != 0
        && context.Name == ".ctor"
        && field.DeclaringType != null && context.DeclaringType != null
        && ThisConstructorCallPlan.SameTypeIdentity(GenericDefinition(field.DeclaringType),
            GenericDefinition(context.DeclaringType));

    // Locals that provably only ever hold `this`: every one of their definitions is
    // a move or phi whose sources are themselves this-aliases. Loading such a local
    // as ldarg.0 is semantics-preserving and satisfies the IsThisPtr rule. Cached per
    // method because GenerateIl runs per method body, potentially in parallel.
    private static readonly ConditionalWeakTable<MethodAnalysisContext, HashSet<LocalVariable>> ThisAliasCache = new();

    private static HashSet<LocalVariable> ThisAliasLocals(MethodAnalysisContext context) =>
        ThisAliasCache.GetValue(context, ComputeThisAliasLocals);

    private static HashSet<LocalVariable> ComputeThisAliasLocals(MethodAnalysisContext context)
    {
        var aliases = new HashSet<LocalVariable>();
        var instructions = context.ControlFlowGraph?.Instructions;
        if (instructions == null)
            return aliases;

        var definitions = new Dictionary<LocalVariable, List<Instruction>>();
        foreach (var instruction in instructions)
            if (instruction.Destination is LocalVariable destination)
            {
                if (!definitions.TryGetValue(destination, out var list))
                    definitions[destination] = list = [];
                list.Add(instruction);
            }

        // `this` itself is the root alias - but only while it is never written:
        // if a this-local is ever the destination of another value, copies made
        // earlier hold a different object than a fresh ldarg.0 would read.
        foreach (var local in context.Locals)
            if (local.IsThis && !definitions.ContainsKey(local))
                aliases.Add(local);

        var changed = true;
        while (changed)
        {
            changed = false;
            foreach (var pair in definitions)
            {
                if (aliases.Contains(pair.Key))
                    continue;
                if (pair.Value.All(definition => CopiesOnlyAliases(definition, aliases)))
                {
                    aliases.Add(pair.Key);
                    changed = true;
                }
            }
        }

        return aliases;
    }

    private static bool CopiesOnlyAliases(Instruction definition, HashSet<LocalVariable> aliases) =>
        definition.OpCode switch
        {
            OpCode.Move => definition.Operands[1] is LocalVariable source && aliases.Contains(source),
            OpCode.Phi => definition.Operands.Skip(1)
                .All(source => source is LocalVariable phi && aliases.Contains(phi)),
            // alias +/- a constant displacement is still rooted in `this`: a
            // FieldReference operand asserts its base is the object itself, so
            // wherever such a local feeds an initonly store the only legal
            // receiver managed code could have used is ldarg.0.
            OpCode.Add or OpCode.Subtract => definition.Operands[1] is LocalVariable source
                && aliases.Contains(source)
                && definition.Operands.Skip(2).All(operand => operand is Immediate),
            _ => false,
        };

    private static bool FieldUsableFrom(FieldAnalysisContext field, MethodAnalysisContext context,
        bool writeAccess = false, TypeAnalysisContext? receiverType = null)
    {
        if (!CanEmitFieldToken(field))
            return false;
        var attrs = field.Attributes;
        // The verifier splits initonly writes by storage class: stsfld belongs to
        // the field's .cctor, stfld to the field's own .ctor (and through `this`
        // itself - see RequiresThisPointerReceiver).
        if (writeAccess && (attrs & FieldAttributes.InitOnly) != 0
            && !((field.IsStatic ? context.Name is ".cctor" : context.Name is ".ctor")
                && field.DeclaringType != null && context.DeclaringType != null
                && ThisConstructorCallPlan.SameTypeIdentity(GenericDefinition(field.DeclaringType),
                    GenericDefinition(context.DeclaringType))))
            return false;
        var callerType = context.DeclaringType;
        var declaring = field.DeclaringType;
        if (declaring == null || callerType == null)
            return true;
        // Member references keep declared accessibility everywhere: the field's own
        // signature type, the declaring type it names, and - when the reference is
        // emitted on the receiver's instantiation - the receiver's type arguments.
        if (!Analysis.InaccessibleCalleeRecovery.IsVisibleType(field.FieldType, callerType)
            || !Analysis.InaccessibleCalleeRecovery.IsVisibleType(declaring, callerType)
            || receiverType != null
                && !Analysis.InaccessibleCalleeRecovery.IsVisibleType(receiverType, callerType))
            return false;
        // A direct native access proves that an inlined managed member reached a
        // same-assembly field. ToFieldDescriptor widens exactly that copied
        // definition, so private storage remains faithfully usable. Dependency
        // assemblies (UnityEngine/mscorlib) are not replaced in the recovered
        // project and therefore keep their real accessibility.
        var callerAssembly = callerType.DeclaringAssembly;
        var declaringAssembly = declaring.DeclaringAssembly;
        if (callerAssembly != null && declaringAssembly != null
            && (ReferenceEquals(callerAssembly, declaringAssembly)
                || callerAssembly.Name != null && callerAssembly.Name == declaringAssembly.Name))
            return true;

        if (declaring is GenericInstanceTypeAnalysisContext declaringInstance)
            declaring = declaringInstance.GenericType;
        if (callerType is GenericInstanceTypeAnalysisContext callerInstance)
            callerType = callerInstance.GenericType;
        var sameAssembly = Extensions.AccessibilityExtensions.SharesEmittedInternals(
            callerType.DeclaringAssembly, declaring.DeclaringAssembly);
        var sameType = ThisConstructorCallPlan.SameTypeIdentity(declaring, callerType);
        return (attrs & FieldAttributes.FieldAccessMask) switch
        {
            FieldAttributes.Public => true,
            FieldAttributes.Private => sameType,
            FieldAttributes.Assembly => sameAssembly,
            FieldAttributes.Family => sameType || callerType.IsAssignableTo(declaring),
            FieldAttributes.FamANDAssem => sameAssembly && (sameType || callerType.IsAssignableTo(declaring)),
            FieldAttributes.FamORAssem => sameAssembly || sameType || callerType.IsAssignableTo(declaring),
            _ => false,
        };
    }

    // Typed `stelem` requires the stack value to be exactly the element type, which
    // narrow integrals can never produce (everything loads as i4); the dedicated
    // element opcodes accept the i4 family directly.
    private static CilOpCode? StelemOpCode(TypeAnalysisContext elementType)
    {
        var effective = elementType is { IsEnumType: true }
            ? elementType.DefaultEnumUnderlyingType : elementType;
        return effective?.FullName switch
        {
            "System.Boolean" or "System.Byte" or "System.SByte" => CilOpCodes.Stelem_I1,
            "System.Char" or "System.Int16" or "System.UInt16" => CilOpCodes.Stelem_I2,
            "System.Int32" or "System.UInt32" => CilOpCodes.Stelem_I4,
            "System.Int64" or "System.UInt64" => CilOpCodes.Stelem_I8,
            "System.IntPtr" or "System.UIntPtr" => CilOpCodes.Stelem_I,
            "System.Single" => CilOpCodes.Stelem_R4,
            "System.Double" => CilOpCodes.Stelem_R8,
            _ when effective is { IsValueType: false } => CilOpCodes.Stelem_Ref,
            _ => null,
        };
    }

    // Byte size of a primitive or enum field; 0 when the layout is not known.
    private static int PrimitiveByteSize(TypeAnalysisContext? type) => type?.FullName switch
    {
        "System.Boolean" or "System.Byte" or "System.SByte" => 1,
        "System.Int16" or "System.UInt16" or "System.Char" => 2,
        "System.Int32" or "System.UInt32" or "System.Single" => 4,
        "System.Int64" or "System.UInt64" or "System.Double" => 8,
        "System.IntPtr" or "System.UIntPtr" => 8,
        _ when type is { IsEnumType: true } => PrimitiveByteSize(type.DefaultEnumUnderlyingType),
        _ => 0,
    };

    // Pushes a managed address (`&`) or object reference that ldfld/ldflda can
    // consume for the given storage operand. Returns false for anything that has
    // no managed address.
    private static bool EmitManagedAddress(IOperand operand, MethodDefinition method,
        MethodAnalysisContext context, Dictionary<LocalVariable, CilLocalVariable> locals,
        IMethodDescriptor writeLine)
    {
        var instructions = method.CilMethodBody!.Instructions;
        switch (operand)
        {
            case LocalVariable { IsThis: true }:
                instructions.Add(CilOpCodes.Ldarg_0);
                return true;
            case LocalVariable local:
                var parameter = ParameterForLocal(local, method, context);
                if (EmittedLocalType(local, context) is { IsValueType: false })
                {
                    if (parameter != null)
                        instructions.Add(CilOpCodes.Ldarg, parameter);
                    else
                        instructions.Add(CilOpCodes.Ldloc, locals[local]);
                }
                else if (parameter != null)
                    instructions.Add(CilOpCodes.Ldarga, parameter);
                else
                    instructions.Add(CilOpCodes.Ldloca, locals[local]);
                return true;
            case FieldReference { Field.IsStatic: true } staticField:
                if (!FieldUsableFrom(staticField.Field, context, writeAccess: true))
                    return false;
                instructions.Add(CilOpCodes.Ldsflda, staticField.Field.ToFieldDescriptor());
                return true;
            case FieldReference field:
                if (!FieldReferenceUsableFrom(field, context, writeAccess: true))
                    return false;
                if (field.Containers.Count == 0)
                {
                    if (!EmitManagedAddress(field.Local, method, context, locals, writeLine))
                        return false;
                }
                else
                    LoadFieldReceiver(field, context, method, locals, writeLine);
                instructions.Add(CilOpCodes.Ldflda,
                    FieldDescriptorFor(field.Field, FieldReceiverType(field, context)));
                return true;
            case ArrayAccess { Array.Type: SzArrayTypeAnalysisContext array } access:
                if (!TypeTokenUsableFrom(array.ElementType, context))
                    return false; // ldelema would name a type the caller cannot see
                LoadArrayBase(access.Array, method, locals, context);
                LoadOperandIntoSlot(access.Index, context.AppContext.SystemTypes.SystemInt32Type,
                    context, method, locals, writeLine);
                instructions.Add(CilOpCodes.Ldelema, array.ElementType.ToTypeSignature().ToTypeDefOrRef());
                return true;
            default:
                return false;
        }
    }

    // The array an element access was lifted through always declares SzArray, but the
    // local it was coalesced into can carry a narrower or wrong type (register reuse
    // packs scalars into array slots). ldelem/ldelema/ldlen/stelem all need the real
    // array type on the stack, so coerce the base to the operand's own array type.
    private static void LoadArrayBase(LocalVariable array, MethodDefinition method,
        Dictionary<LocalVariable, CilLocalVariable> locals, MethodAnalysisContext context)
    {
        LoadLocal(array, method, locals, context);
        CoerceOrDefault(EmittedLocalType(array, context), array.Type, method, context);
    }

    // A scratch local can share a parameter's name (register reuse: `v2 @ X8` the
    // float[] local vs `v2 @ V3` the Single parameter). Only a local that actually
    // is the parameter's register local loads through ldarg; anything else is ldloc.
    private static AsmResolver.DotNet.Collections.Parameter? ParameterForLocal(LocalVariable local, MethodDefinition method, MethodAnalysisContext context)
    {
        if (context.ParameterLocals.Contains(local))
            return context.Parameters.FirstOrDefault(p => p.ParameterName == local.Name) is { } analysisParameter
                ? method.Parameters.FirstOrDefault(p => p.Name == analysisParameter.ParameterName)
                : method.Parameters.FirstOrDefault(p => p.Name == local.Name);

        // Copy propagation can erase `MOV XcalleeSaved, Xarg` and leave only a
        // later argument-register SSA local. If that local has no definition and
        // exactly one declared parameter has its type, the parameter is its only
        // possible managed value.
        if (local is { IsThis: false, IsReturn: false, IsMethodInfo: false, Type: { } localType }
            && context.ControlFlowGraph?.Instructions.All(instruction =>
                !ReferenceEquals(instruction.Destination, local)) == true)
        {
            var matches = context.Parameters.Where(parameter =>
                ThisConstructorCallPlan.SameTypeIdentity(parameter.ParameterType, localType)
                || (ContainsErasedSharedArgument(parameter.ParameterType)
                    || ContainsErasedSharedArgument(localType))
                && ThisConstructorCallPlan.SameTypeIdentity(GenericDefinition(parameter.ParameterType),
                    GenericDefinition(localType))).ToList();
            if (matches.Count == 1)
                return method.Parameters.FirstOrDefault(p => p.Name == matches[0].ParameterName);
        }

        return null;
    }

    private static void LoadLocal(LocalVariable local, MethodDefinition method, Dictionary<LocalVariable, CilLocalVariable> locals,
        MethodAnalysisContext context)
    {
        var instructions = method.CilMethodBody!.Instructions;

        if (local.IsThis)
        {
            instructions.Add(CilOpCodes.Ldarg_0);
            return;
        }

        var parameter = ParameterForLocal(local, method, context);

        if (parameter != null)
            instructions.Add(CilOpCodes.Ldarg, parameter);
        else
            instructions.Add(CilOpCodes.Ldloc, locals[local]);
    }

    private static void StoreToOperand(IOperand operand, MethodDefinition method,
        Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine,
        MethodAnalysisContext context)
    {
        var instructions = method.CilMethodBody!.Instructions;

        switch (operand)
        {
            case LocalVariable local:
                instructions.Add(CilOpCodes.Stloc, locals[local]);
                break;

            case FieldReference field:
                if (!FieldReferenceUsableFrom(field, context, writeAccess: true))
                {
                    // The value is already on the stack; the field cannot legally
                    // be referenced here, so fail honestly.
                    EmitUnrecoverableOperation(method, writeLine,
                        $"Inaccessible field store: {field.Field.DeclaringType?.FullName}.{field.Field.Name}");
                    break;
                }
                var fieldDescriptor = field.Field.IsStatic
                    ? field.Field.ToFieldDescriptor()
                    : FieldDescriptorFor(field.Field, FieldReceiverType(field, context));

                if (field.Field.IsStatic)
                {
                    instructions.Add(CilOpCodes.Stsfld, fieldDescriptor);
                    break;
                }

                // stfld wants the object underneath the value, but the value is already on the stack, so
                // park it in a temporary while we load the object. The scratch takes the
                // instantiated field type: the descriptor's raw signature keeps the generic
                // definition's !T, which has no meaning in this method's locals signature.
                var scratch = new CilLocalVariable(
                    EmittableLocalType(field.Field.FieldType, context).ToTypeSignature());
                method.CilMethodBody!.LocalVariables.Add(scratch);

                instructions.Add(CilOpCodes.Stloc, scratch);
                // Same rule as the MoveAssign stfld path: an initonly store inside the
                // field's own .ctor only verifies through `this`, which is the receiver
                // valid managed source could only have used.
                if (field.Containers.Count == 0 && RequiresThisPointerReceiver(field.Field, context)
                    && (field.Local is null or LocalVariable
                        || ThisAliasLocals(context).Contains(field.Local)))
                    instructions.Add(CilOpCodes.Ldarg_0);
                else
                    LoadFieldReceiver(field, context, method, locals, writeLine);
                instructions.Add(CilOpCodes.Ldloc, scratch);
                instructions.Add(CilOpCodes.Stfld, fieldDescriptor);
                break;

            case ArrayAccess arrayAccess:
                // stelem needs array and index before the value, so the same trick as stfld
                var elementType = ((SzArrayTypeAnalysisContext)arrayAccess.Array.Type!).ElementType;
                if (!TypeTokenUsableFrom(elementType, context))
                {
                    // The element type cannot be named here - not even the scratch
                    // local's signature - so drop the stored value and fail honestly.
                    instructions.Add(CilOpCodes.Pop);
                    EmitUnrecoverableOperation(method, writeLine,
                        $"Inaccessible array element type: {elementType.FullName}");
                    break;
                }
                var elementScratch = new CilLocalVariable(elementType.ToTypeSignature());
                method.CilMethodBody!.LocalVariables.Add(elementScratch);

                instructions.Add(CilOpCodes.Stloc, elementScratch);
                LoadArrayBase(arrayAccess.Array, method, locals, context);
                LoadOperandIntoSlot(arrayAccess.Index, context.AppContext.SystemTypes.SystemInt32Type,
                    context, method, locals, writeLine);
                instructions.Add(CilOpCodes.Ldloc, elementScratch);
                if (StelemOpCode(elementType) is { } storeElementOp)
                    instructions.Add(storeElementOp);
                else
                    instructions.Add(CilOpCodes.Stelem, elementType.ToTypeSignature().ToTypeDefOrRef());
                break;

            case MemoryOperand memory:
                if (memory.Base is LocalVariable { Type: ByRefTypeAnalysisContext })
                {
                    instructions.Add(CilOpCodes.Pop);
                    instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Unsupported managed-pointer store ({memory.AccessSize} bytes): {memory}"));
                    instructions.Add(CilOpCodes.Call, writeLine);
                    break;
                }
                if (memory.Index == null && memory.Addend == 0 && memory.Scale == 0
                    && memory.Base is LocalVariable local2)
                {
                    // Can pointer assignments just be ignored because it's C#? (Move [local], 123)
                    instructions.Add(CilOpCodes.Stloc, locals[local2]);
                    break;
                }
                instructions.Add(CilOpCodes.Pop);
                break;

            default:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Store into unknown operand: {operand}"));
                instructions.Add(CilOpCodes.Call, writeLine);
                instructions.Add(CilOpCodes.Pop);
                break;
        }
    }
}
