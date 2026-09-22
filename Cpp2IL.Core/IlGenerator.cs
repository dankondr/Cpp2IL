using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Extensions;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
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
            null,
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

            if (operand is FieldReference field)
                local = field.Local;

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

        // Map ISIL locals to IL
        Dictionary<LocalVariable, CilLocalVariable> locals = [];
        foreach (var local in context.Locals)
        {
            var emittedType = EmittedLocalType(local, context);
            var ilType = emittedType == context.AppContext.SystemTypes.SystemObjectType
                ? module.CorLibTypeFactory.Object
                : emittedType == context.AppContext.SystemTypes.SystemBooleanType
                    ? module.CorLibTypeFactory.Boolean
                    : emittedType.ToTypeSignature();
            var ilLocal = new CilLocalVariable(ilType);
            body.LocalVariables.Add(ilLocal);
            locals.Add(local, ilLocal);
        }

        /* foreach (var instruction in context.ControlFlowGraph!.Instructions)
        {
            body.Instructions.Add(CilOpCodes.Ldstr, instruction.ToString());
            body.Instructions.Add(CilOpCodes.Call, _importer!.ImportMethod(_writeLine!));
        }
        body.Instructions.Add(CilOpCodes.Ldstr, "-------------------------------------------------------------------------");
        body.Instructions.Add(CilOpCodes.Call, _importer!.ImportMethod(_writeLine!)); */

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
            body.Instructions.Add(CilOpCodes.Ldarg_0);
            for (var i = 0; i < arguments.Length; i++)
                LoadOperand(arguments[i], definition, locals, writeLine, constructor.Parameters[i].ParameterType);
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
                    : skippedThisConstructorRedirects.GetValueOrDefault(target);

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
        }
    }

    // Limit so we don't run into the 16mb limit (see AsmResolver issue #775)
    private static string Diagnostic(string message) 
        => message.Length <= 250 ? message : message[..250] + "…";
    
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
                if (instruction.Operands[0] is MemoryOperand
                    { Index: null, Addend: 0, Scale: 0, Base: LocalVariable
                        { Type: ByRefTypeAnalysisContext { ElementType: { IsValueType: false } referent } } address } store
                    && referent is not (PointerTypeAnalysisContext or ByRefTypeAnalysisContext or GenericParameterTypeAnalysisContext)
                    && store.AccessSize == context.AppContext.Binary.PointerSizeBytes)
                {
                    LoadLocal(address, method, locals);
                    LoadOperand(instruction.Operands[1], method, locals, writeLine, referent);
                    instructions.Add(CilOpCodes.Stind_Ref);
                    break;
                }

                if (instruction.Operands[0] is FieldReference field) // stfld takes instance before value so LoadOperand StoreToOperand doesn't work
                {
                    if (!field.Field.IsStatic)
                        LoadLocal(field.Local, method, locals);

                    LoadOperand(instruction.Operands[1], method, locals, writeLine, field.Field.FieldType);
                    EmitStackCoerce(EmittedOperandType(instruction.Operands[1], context, field.Field.FieldType), field.Field.FieldType, method);
                    instructions.Add(field.Field.IsStatic ? CilOpCodes.Stsfld : CilOpCodes.Stfld, field.Field.ToFieldDescriptor());
                    break;
                }

                // stelem needs array and index before the value, so like stfld it can't go through LoadOperand/StoreToOperand.
                // This also lets ILSpy handle it as a proper array initializer
                if (instruction.Operands[0] is ArrayAccess { Array.Type: SzArrayTypeAnalysisContext { ElementType: { } stored } } target)
                {
                    LoadLocal(target.Array, method, locals);
                    LoadOperand(target.Index, method, locals, writeLine);
                    LoadOperand(instruction.Operands[1], method, locals, writeLine, stored);
                    EmitStackCoerce(EmittedOperandType(instruction.Operands[1], context, stored), stored, method);
                    instructions.Add(CilOpCodes.Stelem, stored.ToTypeSignature().ToTypeDefOrRef());
                    break;
                }

                var moveDestinationType = DestinationType(instruction.Operands[0])
                    ?? (instruction.Operands[0] is LocalVariable local ? EmittedLocalType(local, context) : null);
                LoadOperand(instruction.Operands[1], method, locals, writeLine, moveDestinationType);
                EmitStackCoerce(EmittedOperandType(instruction.Operands[1], context, moveDestinationType), moveDestinationType, method);
                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

            case OpCode.SignExtend32:
                LoadOperand(instruction.Operands[1], method, locals, writeLine);
                instructions.Add(CilOpCodes.Conv_I4);
                instructions.Add(CilOpCodes.Conv_I8);
                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

            case OpCode.NewArr:
                if (instruction.Operands is [_, SzArrayTypeAnalysisContext { ElementType: { } newArrayElement }, { } length])
                {
                    LoadOperand(length, method, locals, writeLine);
                    instructions.Add(CilOpCodes.Newarr, newArrayElement.ToTypeSignature().ToTypeDefOrRef());
                }
                else
                    instructions.Add(CilOpCodes.Ldnull);

                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

            case OpCode.Newobj:
                // Try and fuse our Newobj + the follow up constructor CallVoid into one IL newobj.
                // If we can't, just fall back to an Ldnull.
                if (constructorPairs.TryGetValue(instruction, out var constructorCall)
                    && constructorCall.Operands is [MethodAnalysisContext constructor, _, ..])
                {
                    constructor = Analysis.AllocationConstructorRecovery.Resolve(instruction, constructor) ?? constructor;
                    constructor = ThisConstructorCallPlan.RetargetToDestinationInstantiation(constructor,
                            DestinationType(instruction.Operands[0])
                            ?? (instruction.Operands[0] is LocalVariable allocatedLocal ? EmittedLocalType(allocatedLocal, context) : null))
                        ?? constructor;
                    // Operands run [ctor, newObject, arguments..., methodInfo], so take only as many as
                    // the constructor declares (i.e. drop methodInfo)
                    var constructorArgs = constructorCall.Operands.Skip(ConstructorReceiverIndex(constructorCall) + 1).Take(constructor.Parameters.Count).ToList();
                    for (var i = 0; i < constructorArgs.Count; i++)
                    {
                        LoadOperand(constructorArgs[i], method, locals, writeLine, constructor.Parameters[i].ParameterType);
                        EmitStackCoerce(EmittedOperandType(constructorArgs[i], context, constructor.Parameters[i].ParameterType), constructor.Parameters[i].ParameterType, method);
                    }

                    instructions.Add(CilOpCodes.Newobj, constructor.ToMethodDescriptor());
                    StoreToOperand(instruction.Operands[0], method, locals, writeLine);

                    constructorCall.OpCode = OpCode.Nop;
                    constructorCall.SetOperands();
                }
                else if (instruction.Operands is [_, TypeAnalysisContext allocatedType] && allocatedType.Methods.FirstOrDefault(m => m is { Name: ".ctor", Parameters.Count: 0 }) is { } parameterlessCtor)
                {
                    // Nothing to fuse with, so the allocation was self-contained. The type is still right, so construct it bare.
                    parameterlessCtor = ThisConstructorCallPlan.RetargetToDestinationInstantiation(parameterlessCtor,
                            DestinationType(instruction.Operands[0])
                            ?? (instruction.Operands[0] is LocalVariable allocatedLocal ? EmittedLocalType(allocatedLocal, context) : null))
                        ?? parameterlessCtor;
                    instructions.Add(CilOpCodes.Newobj, parameterlessCtor.ToMethodDescriptor());
                    StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                }
                else
                {
                    instructions.Add(CilOpCodes.Ldnull);
                    StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                }
                break;

            case OpCode.Box:
                if (instruction.Operands is [_, TypeAnalysisContext boxedType, var boxedValue])
                {
                    // il2cpp_value_box takes the value by address, but IL boxes it by value
                    LoadOperand(boxedValue is AddressOf { Target: LocalVariable byRef } ? byRef : boxedValue, method, locals, writeLine, boxedType);
                    instructions.Add(CilOpCodes.Box, boxedType.ToTypeSignature().ToTypeDefOrRef());
                }
                else
                    instructions.Add(CilOpCodes.Ldnull);

                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

            case OpCode.Throw:
                if (instruction.Operands is [TypeAnalysisContext exceptionType]
                    && exceptionType.Methods.FirstOrDefault(m => m.Name == ".ctor" && m.Parameters.Count == 0) is { } exceptionCtor)
                    instructions.Add(CilOpCodes.Newobj, exceptionCtor.ToMethodDescriptor());
                else if (instruction.Operands is [LocalVariable or FieldReference])
                    LoadOperand(instruction.Operands[0], method, locals, writeLine); // an already-constructed exception
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
                if (instruction.Operands[0] is not MethodAnalysisContext targetMethod)
                {
                    if (instruction.Operands[0] is Immediate targetAddress)
                        instructions.Add(CilOpCodes.Ldstr, $"Method not found @{targetAddress.UnsignedValue:X}");
                    else // Probably key function. Just the target, the full operand dump is huge and blows the 16MB #US heap limit
                        instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Unknown call target operand: {instruction.Operands[0]}"));

                    instructions.Add(CilOpCodes.Call, writeLine);
                    break;
                }

                if (Analysis.StringConstructorRecovery.Resolve(instruction, targetMethod) is { } stringConstructor)
                {
                    var firstArgument = instruction.OpCode == OpCode.Call ? 3 : 2;
                    for (var i = 0; i < stringConstructor.Parameters.Count; i++)
                    {
                        LoadOperand(instruction.Operands[firstArgument + i], method, locals, writeLine, stringConstructor.Parameters[i].ParameterType);
                        EmitStackCoerce(EmittedOperandType(instruction.Operands[firstArgument + i], context, stringConstructor.Parameters[i].ParameterType), stringConstructor.Parameters[i].ParameterType, method);
                    }
                    instructions.Add(CilOpCodes.Newobj, stringConstructor.ToMethodDescriptor());
                    if (instruction.OpCode == OpCode.Call)
                        StoreToOperand(instruction.Operands[1], method, locals, writeLine);
                    else
                        instructions.Add(CilOpCodes.Pop);
                    break;
                }

                var retargetedBaseConstructor = thisConstructorCalls?.Retarget.GetValueOrDefault(instruction);
                if (retargetedBaseConstructor != null)
                    targetMethod = retargetedBaseConstructor;

                var importedMethod = targetMethod.ToMethodDescriptor();

                var thisParamIndex = instruction.OpCode == OpCode.Call ? 2 : 1;

                if (!targetMethod.IsStatic) // Load 'this' param
                {
                    if ((instruction.Operands.Count - 1) >= thisParamIndex)
                    {
                        LoadOperand(instruction.Operands[thisParamIndex], method, locals, writeLine, targetMethod.DeclaringType);
                        // A struct's instance `this` is a managed pointer, not the value —
                        // coerce toward `&T` (which no stack op can forge) so a ldloca
                        // receiver is left alone instead of being unboxed. The method's own
                        // `this` and constructor receivers must stay a bare ldarg.0 for the
                        // verifier, so they skip coercion entirely.
                        var thisOperand = instruction.Operands[thisParamIndex];
                        var isOwnThis = thisOperand is LocalVariable thisLocal
                            && (thisLocal.IsThis || ReferenceEquals(thisLocal, context.ParameterLocals.FirstOrDefault()));
                        if (targetMethod.Name is not ".ctor" && !isOwnThis)
                        {
                            var thisEmitted = EmittedOperandType(thisOperand, context);
                            var thisTarget = targetMethod.DeclaringType is { IsValueType: true } declaringStruct
                                ? new ByRefTypeAnalysisContext(declaringStruct)
                                : targetMethod.DeclaringType;
                            EmitStackCoerce(thisEmitted, thisTarget, method);
                        }
                    }
                    else
                    {
                        instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Non static method called without 'this' param ({instruction})"));
                        instructions.Add(CilOpCodes.Call, writeLine);
                        instructions.Add(CilOpCodes.Ldnull);
                    }
                }

                // Load normal params
                var callParamIndex = instruction.OpCode == OpCode.Call ? (targetMethod.IsStatic ? 2 : 3) : (targetMethod.IsStatic ? 1 : 2);
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
                            PushDefaultOf(parameterType, method, instructions);
                        }
                        else
                        {
                            LoadOperand(argumentOperand, method, locals, writeLine, parameterType);
                            EmitStackCoerce(EmittedOperandType(argumentOperand, context, parameterType), parameterType, method);
                        }
                    }
                    else
                        PushDefaultOf(parameterType, method, instructions);
                }

                instructions.Add(!targetMethod.IsStatic && retargetedBaseConstructor == null
                        && (instruction.IsVirtualDispatch || targetMethod.DeclaringType?.IsInterface == true)
                    ? CilOpCodes.Callvirt
                    : CilOpCodes.Call, importedMethod);

                // the lifter's guess at whether the callee returns anything can disagree with the
                // signature we later resolved, so go by the signature and balance the stack
                if (!targetMethod.IsVoid)
                {
                    if (instruction.OpCode == OpCode.Call)
                    {
                        EmitStackCoerce(targetMethod.ReturnType,
                            DestinationType(instruction.Operands[1])
                            ?? (instruction.Operands[1] is LocalVariable callResult ? EmittedLocalType(callResult, context) : null),
                            method);
                        StoreToOperand(instruction.Operands[1], method, locals, writeLine);
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
                    LoadOperand(returnedException, method, locals, writeLine);
                    instructions.Add(CilOpCodes.Throw);
                    break;
                }

                if (!context.IsVoid)
                {
                    if (instruction.Operands.Count == 1)
                    {
                        LoadOperand(instruction.Operands[0], method, locals, writeLine, context.ReturnType);
                        EmitStackCoerce(EmittedOperandType(instruction.Operands[0], context, context.ReturnType), context.ReturnType, method);
                    }
                    else
                        instructions.Add(CilOpCodes.Ldnull); // ret still pops a value even if we lost track of it
                }
                instructions.Add(CilOpCodes.Ret);
                break;

            case OpCode.Jump:
                instructions.Add(CilOpCodes.Br, new CilInstructionLabel());
                break;

            case OpCode.ConditionalJump:
                LoadOperand(instruction.Operands[1], method, locals, writeLine);
                // brtrue won't pop an i64; the native branch tested the full register
                // for non-zero, which is exactly `x > 0` unsigned.
                if (IntegralStackWidth(EmittedOperandType(instruction.Operands[1], context)) == 8)
                {
                    instructions.Add(CilOpCodes.Ldc_I8, 0L);
                    instructions.Add(CilOpCodes.Cgt_Un);
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
                    && TryEmitExactTypeComparison(instruction, method, locals, writeLine))
                    break;

                // Float operations on a promoted integer operand need an explicit conversion, so both
                // operands are coerced to the (float) result type. A no-op when they already match.
                var floatConversion = FloatOperationConversion(instruction);

                // Integer operations share a single stack type: the widest non-literal operand,
                // or (for value-producing ops) the destination. Comparison destinations are the
                // bool result, not the compared type, so they never seed the operand type.
                var operandType = floatConversion == null
                    ? BinaryOperandType(instruction, context,
                        instruction.OpCode is < OpCode.CheckEqual or > OpCode.CheckLessOrEqual)
                    : null;

                LoadOperand(instruction.Operands[1], method, locals, writeLine,
                    NullComparisonType(instruction, 1, context) ?? operandType);
                if (floatConversion is { } conv1)
                    instructions.Add(conv1);
                else
                    EmitStackCoerce(EmittedOperandType(instruction.Operands[1], context, operandType), operandType, method,
                        instruction.OpCode is >= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual);
                // shl/shr take an i32/n-int shift amount, not the value type.
                var operand2Type = instruction.OpCode is OpCode.ShiftLeft or OpCode.ShiftRight
                    ? context.AppContext.SystemTypes.SystemInt32Type
                    : operandType;
                LoadOperand(instruction.Operands[2], method, locals, writeLine,
                    NullComparisonType(instruction, 2, context) ?? operand2Type);
                if (floatConversion is { } conv2)
                    instructions.Add(conv2);
                else
                    EmitStackCoerce(EmittedOperandType(instruction.Operands[2], context, operand2Type), operand2Type, method,
                        instruction.OpCode is >= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual);

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

                var resultType = instruction.OpCode is >= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual
                    ? context.AppContext.SystemTypes.SystemInt32Type
                    : operandType ?? EmittedOperandType(instruction.Operands[1], context);
                EmitStackCoerce(resultType,
                    DestinationType(instruction.Operands[0])
                    ?? (instruction.Operands[0] is LocalVariable resultLocal ? EmittedLocalType(resultLocal, context) : null),
                    method);
                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

            case OpCode.Not:
            case OpCode.Negate:
                LoadOperand(instruction.Operands[1], method, locals, writeLine);

                if (instruction.OpCode == OpCode.Negate)
                    instructions.Add(CilOpCodes.Neg);
                else if (IsBoolean(instruction.Operands[1], context))
                {
                    instructions.Add(CilOpCodes.Ldc_I4_0);
                    instructions.Add(CilOpCodes.Ceq);
                }
                else
                    instructions.Add(CilOpCodes.Not);

                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

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
                pairs[allocation] = constructorCall;
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
        public readonly List<(MethodAnalysisContext Constructor, IOperand[] Arguments)> PrologueCalls = [];

        public static ThisConstructorCallPlan? Create(MethodAnalysisContext context)
        {
            if (context is not { IsStatic: false, Name: ".ctor" }
                || context.DeclaringType is not { IsValueType: false } declaringType
                || declaringType.BaseType is not { } immediateBase)
                return null;

            List<(Instruction Instruction, MethodAnalysisContext Callee)> calls = [];
            foreach (var instruction in context.ControlFlowGraph!.Instructions)
            {
                if (!instruction.IsCall
                    || instruction.Operands[0] is not MethodAnalysisContext { IsStatic: false, Name: ".ctor" } callee
                    || instruction.Operands.Count <= ConstructorReceiverIndex(instruction)
                    || instruction.Operands[ConstructorReceiverIndex(instruction)] is not LocalVariable { IsThis: true })
                    continue;

                calls.Add((instruction, callee));
            }

            List<(Instruction Instruction, MethodAnalysisContext Callee)> distant = [];
            var hasLegalInitialization = false;
            foreach (var call in calls)
            {
                if (SameTypeIdentity(call.Callee.DeclaringType, declaringType)
                    || SameTypeIdentity(call.Callee.DeclaringType, immediateBase))
                    hasLegalInitialization = true;
                else if (IsDistantAncestorOf(declaringType, call.Callee.DeclaringType)
                         || SameGenericDefinition(call.Callee.DeclaringType, immediateBase))
                    distant.Add(call);
            }

            if (distant.Count == 0)
                return null;

            var plan = new ThisConstructorCallPlan();
            if (hasLegalInitialization)
            {
                // The genuine initialization call survived; further ancestor calls are
                // remnants of the chain it was inlined from.
                foreach (var (instruction, _) in distant)
                    plan.Skip.Add(instruction);
                return plan;
            }

            List<(Instruction Instruction, MethodAnalysisContext Replacement)> resolved = [];
            foreach (var (instruction, callee) in distant)
                if (FindImmediateBaseConstructor(immediateBase, callee) is { } match)
                    resolved.Add((instruction, match));

            if (resolved.Count == 0
                || resolved.Any(r => !SameMethodIdentity(r.Replacement, resolved[0].Replacement)))
                return null;

            var replacement = resolved[0].Replacement;
            if (replacement.Parameters.Count == 0)
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

        private static IOperand[]? PrologueArguments(Instruction call, MethodAnalysisContext replacement,
            MethodAnalysisContext context)
        {
            var receiver = ConstructorReceiverIndex(call);
            if (call.Operands.Count < receiver + 1 + replacement.Parameters.Count)
                return null;

            var arguments = call.Operands.Skip(receiver + 1).Take(replacement.Parameters.Count).ToArray();
            return arguments.All(a => a switch
            {
                Immediate or StringLiteral or FloatLiteral or DoubleLiteral or TypeAnalysisContext => true,
                LocalVariable local => !local.IsThis && !local.IsMethodInfo && context.ParameterLocals.Contains(local),
                _ => false,
            }) ? arguments : null;
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

        private static bool IsDistantAncestorOf(TypeAnalysisContext declaringType, TypeAnalysisContext? target)
        {
            if (target == null)
                return false;
            for (var ancestor = declaringType.BaseType?.BaseType; ancestor != null; ancestor = ancestor.BaseType)
                if (SameTypeIdentity(ancestor, target) || SameGenericDefinition(ancestor, target))
                    return true;
            return false;
        }

        private static bool SameGenericDefinition(TypeAnalysisContext? a, TypeAnalysisContext? b) =>
            a is GenericInstanceTypeAnalysisContext left
            && b is GenericInstanceTypeAnalysisContext right
            && left.GenericType.FullName == right.GenericType.FullName;

        // IL2CPP shares generic code across reference-type arguments, so the lifter may tag
        // a `newobj` with `List<object>` while every use site wants `List<string>`. When the
        // allocated type and the destination are instantiations of the same generic
        // definition, rebuild the constructor against the destination's instantiation.
        internal static MethodAnalysisContext? RetargetToDestinationInstantiation(MethodAnalysisContext constructor,
            TypeAnalysisContext? destinationType)
        {
            if (destinationType is not GenericInstanceTypeAnalysisContext destination
                || constructor.DeclaringType is not GenericInstanceTypeAnalysisContext source
                || !SameTypeIdentity(source.GenericType, destination.GenericType)
                || source.GenericArguments.Count != destination.GenericArguments.Count
                || source.GenericArguments.Zip(destination.GenericArguments, SameTypeIdentity).All(match => match))
                return null;

            var baseConstructor = constructor is ConcreteGenericMethodAnalysisContext concrete
                ? concrete.BaseMethodContext
                : constructor;
            return new ConcreteGenericMethodAnalysisContext(baseConstructor, destination.GenericArguments, []);
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
        private static bool SameTypeIdentity(TypeAnalysisContext? a, TypeAnalysisContext? b)
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
        _ => null,
    };

    private static void LoadOperand(IOperand operand, MethodDefinition method,
        Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine,
        TypeAnalysisContext? expectedType = null)
    {
        var instructions = method.CilMethodBody!.Instructions;

        var module = method.DeclaringModule!;

        // A null reference reaches us as an integer zero, which would otherwise be emitted as a literal 0
        // and read back as a cast from a number. Runtime handle types lower to native int, where the
        // zero is an address, not a reference.
        if (expectedType is { IsValueType: false } && IsZeroConstant(operand) && !IsNativeHandleType(expectedType))
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
            case StringLiteral s:
                instructions.Add(CilOpCodes.Ldstr, s.Value);
                break;
            case LocalVariable local:
                LoadLocal(local, method, locals);
                break;
            case ReferenceCast referenceCast:
                LoadLocal(referenceCast.Value, method, locals);
                instructions.Add(CilOpCodes.Castclass, referenceCast.Type.ToTypeSignature().ToTypeDefOrRef());
                break;
            case ArrayLength arrayLength:
                LoadLocal(arrayLength.Array, method, locals);
                instructions.Add(CilOpCodes.Ldlen);
                instructions.Add(CilOpCodes.Conv_I4);
                break;
            case AddressOf { Target: LocalVariable addressed }:
                instructions.Add(CilOpCodes.Ldloca, locals[addressed]);
                break;
            case AddressOf { Target: FieldReference addressedField }:
                if (!addressedField.Field.IsStatic)
                    LoadLocal(addressedField.Local, method, locals);
                instructions.Add(addressedField.Field.IsStatic ? CilOpCodes.Ldsflda : CilOpCodes.Ldflda,
                    addressedField.Field.ToFieldDescriptor());
                break;
            case AddressOf { Target: ArrayAccess elementAddress }:
                LoadLocal(elementAddress.Array, method, locals);
                LoadOperand(elementAddress.Index, method, locals, writeLine);
                instructions.Add(CilOpCodes.Ldelema,
                    ((SzArrayTypeAnalysisContext)elementAddress.Array.Type!).ElementType.ToTypeSignature().ToTypeDefOrRef());
                break;
            case ArrayAccess arrayAccess:
                LoadLocal(arrayAccess.Array, method, locals);
                LoadOperand(arrayAccess.Index, method, locals, writeLine);
                instructions.Add(CilOpCodes.Ldelem,
                    ((SzArrayTypeAnalysisContext)arrayAccess.Array.Type!).ElementType.ToTypeSignature().ToTypeDefOrRef());
                break;
            case FieldReference field:
                if (field.Field.IsStatic)
                {
                    instructions.Add(CilOpCodes.Ldsfld, field.Field.ToFieldDescriptor());
                    break;
                }

                LoadLocal(field.Local, method, locals);
                instructions.Add(CilOpCodes.Ldfld, field.Field.ToFieldDescriptor());
                break;
            case MemoryOperand memory:
                if (TryGetDeterministicMemoryReferent(memory, expectedType, out var referent))
                {
                    LoadLocal((LocalVariable)memory.Base!, method, locals);

                    // A zero-offset load through a typed pointer/byref is an actual managed
                    // dereference. Everything else stays unresolved below: ISIL has no proof
                    // that an arbitrary native address or offset names a managed field.
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
                if (expectedType?.FullName == "System.IntPtr" && runtimeMethod.RepresentedMethod.Name is not ".ctor")
                {
                    instructions.Add(CilOpCodes.Ldftn, runtimeMethod.RepresentedMethod.ToMethodDescriptor());
                    break;
                }
                if (expectedType?.FullName == "System.RuntimeMethodHandle")
                {
                    instructions.Add(CilOpCodes.Ldtoken, runtimeMethod.RepresentedMethod.ToMethodDescriptor());
                    break;
                }

                //Not fully implemented, these basically shouldn't actually ever exist in the final IL.
                instructions.Add(CilOpCodes.Ldc_I4_0);
                instructions.Add(CilOpCodes.Conv_I);
                break;
            case RuntimeFieldInfoAnalysisContext runtimeField:
                // fieldof(F), e.g. the handle InitializeArray takes.
                if (expectedType?.FullName == "System.RuntimeFieldHandle")
                {
                    instructions.Add(CilOpCodes.Ldtoken, runtimeField.RepresentedField.ToFieldDescriptor());
                    break;
                }

                instructions.Add(CilOpCodes.Ldc_I4_0);
                instructions.Add(CilOpCodes.Conv_I);
                break;
            case RuntimeClassTypeAnalysisContext runtimeClass when expectedType?.FullName == "System.RuntimeTypeHandle":
                instructions.Add(CilOpCodes.Ldtoken, runtimeClass.RepresentedType.ToTypeSignature().ToTypeDefOrRef());
                break;
            case RuntimeClassTypeAnalysisContext runtimeClass
                when expectedType?.FullName is "System.Type" or "System.Object":
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
                    instructions.Add(CilOpCodes.Ldtoken, type.ToTypeSignature().ToTypeDefOrRef());
                    break;
                }

                if (expectedType?.FullName is "System.IntPtr" or "System.UIntPtr"
                    || expectedType is RuntimeClassTypeAnalysisContext)
                {
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

                instructions.Add(CilOpCodes.Ldtoken, type.ToTypeSignature().ToTypeDefOrRef());
                instructions.Add(CilOpCodes.Call, typeFromHandle);
                break;
            default:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic("Unknown operand: " + operand));
                instructions.Add(CilOpCodes.Call, writeLine);
                instructions.Add(CilOpCodes.Ldnull);
                break;
        }
    }
    
    private static bool TryEmitExactTypeComparison(Instruction instruction, MethodDefinition method,
        Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine)
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
        var instructions = method.CilMethodBody!.Instructions;

        var getType = module.CorLibTypeFactory.CorLibScope
            .CreateTypeReference("System", "Object")
            .CreateMemberReference("GetType", MethodSignature.CreateInstance(
                module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "Type").ToTypeSignature(false)));

        LoadLocal(objLocal, method, locals);
        instructions.Add(CilOpCodes.Callvirt, getType);
        LoadOperand(typeOperand, method, locals, writeLine); // emits typeof(T)
        instructions.Add(CilOpCodes.Ceq);

        if (instruction.OpCode == OpCode.CheckNotEqual)
        {
            instructions.Add(CilOpCodes.Ldc_I4_0);
            instructions.Add(CilOpCodes.Ceq);
        }

        StoreToOperand(instruction.Operands[0], method, locals, writeLine);
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

    private static void PushDefaultOf(TypeAnalysisContext type, MethodDefinition method, CilInstructionCollection instructions)
    {
        //TODO Remove this, we should be handling arguments correctly in ISIL resolution, this is a hack to emit balanced stacks.
        //TODO At the *very* least we should emit a console.writeline saying that we did this.
        if (type is ByRefTypeAnalysisContext byRefParameter)
        {
            // ref/out/in slots need a managed pointer; a fresh local is the only
            // honest default - the callee may write through it and the result is
            // dropped, same as any other placeholder.
            var elementType = byRefParameter.ElementType;
            if (CanEmitTypeToken(elementType))
            {
                var tempLocal = new CilLocalVariable(elementType.ToTypeSignature());
                method.CilMethodBody!.LocalVariables.Add(tempLocal);
                instructions.Add(CilOpCodes.Ldloca, tempLocal);
            }
            else
                instructions.Add(CilOpCodes.Ldc_I4_0, 0);
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
            default:
                // `newobj .ctor()` fails to resolve on types that do not declare one
                // explicitly (the verifier will not invent the implicit struct ctor),
                // so default(T) goes through a zero-initialized temp local instead.
                if (CanEmitTypeToken(type))
                {
                    var signature = type.ToTypeSignature();
                    var tempLocal = new CilLocalVariable(signature);
                    method.CilMethodBody!.LocalVariables.Add(tempLocal);
                    instructions.Add(CilOpCodes.Ldloca, tempLocal);
                    instructions.Add(CilOpCodes.Initobj, signature.ToTypeDefOrRef());
                    instructions.Add(CilOpCodes.Ldloc, tempLocal);
                }
                else
                    instructions.Add(CilOpCodes.Ldc_I4_0);
                break;
        }
    }

    private static bool IsBoolean(IOperand operand, MethodAnalysisContext context) =>
        DestinationType(operand) == context.AppContext.SystemTypes.SystemBooleanType;

    private static TypeAnalysisContext EmittedLocalType(LocalVariable local, MethodAnalysisContext context)
    {
        if (local.Type != null && local.Type != context.AppContext.SystemTypes.SystemVoidType)
            return IsNativeHandleType(local.Type) ? context.AppContext.SystemTypes.SystemIntPtrType : local.Type;
        // `this` loads use ldarg.0, whose stack type is the declaring type (a managed
        // pointer to it for value-type methods), even when ISIL leaves the local untyped.
        if (context.DeclaringType is { } declaringType
            && (local.IsThis || !context.IsStatic && ReferenceEquals(local, context.ParameterLocals.FirstOrDefault())))
            return declaringType.IsValueType ? new ByRefTypeAnalysisContext(declaringType) : declaringType;
        if (IsBooleanEmissionLocal(local, context))
            return context.AppContext.SystemTypes.SystemBooleanType;
        if (IsNativePointerEmissionLocal(local, context))
            return context.AppContext.SystemTypes.SystemIntPtrType;
        return context.AppContext.SystemTypes.SystemObjectType;
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

    private static bool IsZeroConstant(IOperand operand) => operand is Immediate { Value: 0 };

    private static TypeAnalysisContext? NullComparisonType(Instruction instruction, int operandIndex, MethodAnalysisContext context)
    {
        if (instruction.OpCode is not (OpCode.CheckEqual or OpCode.CheckNotEqual)
            || !IsZeroConstant(instruction.Operands[operandIndex])) return null;
        var otherOperand = instruction.Operands[3 - operandIndex];
        var otherType = DestinationType(otherOperand);
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
            ArrayAccess { Array.Type: SzArrayTypeAnalysisContext array } => array.ElementType,
            _ => null
        };
        // Handle contexts are emitted as System.IntPtr, so that is the real contract
        // the stack value has to satisfy.
        return type != null && IsNativeHandleType(type) ? type.AppContext.SystemTypes.SystemIntPtrType : type;
    }

    // The stack type an operand produces once emitted, before any coercion. `expectedType`
    // is the consumer's contract where the emission site knows it: literal immediates adapt
    // to it, and runtime-handle operands lower differently for handle/typeof contracts.
    private static TypeAnalysisContext? EmittedOperandType(IOperand operand, MethodAnalysisContext context,
        TypeAnalysisContext? expectedType = null) =>
        operand switch
        {
            // A literal with no contract adapts to whatever type the consumer picks
            // for it; only a known contract pins down its emitted width. A zero into
            // a reference contract emits ldnull, which is the contract type itself.
            Immediate immediate => expectedType is null ? null
                : immediate.Value == 0 && expectedType is { IsValueType: false } && !IsNativeHandleType(expectedType)
                    ? expectedType
                    : EmittedImmediateType(immediate, expectedType, context),
            LocalVariable local => EmittedLocalType(local, context),
            FieldReference field => field.Field.FieldType,
            ArrayAccess { Array.Type: SzArrayTypeAnalysisContext array } => array.ElementType,
            ArrayLength => context.AppContext.SystemTypes.SystemInt32Type,
            // ldloca/ldflda/ldelema push a managed pointer, not a native int.
            AddressOf { Target: LocalVariable addressedLocal }
                => new ByRefTypeAnalysisContext(EmittedLocalType(addressedLocal, context)),
            AddressOf { Target: FieldReference addressedField }
                => new ByRefTypeAnalysisContext(addressedField.Field.FieldType),
            AddressOf { Target: ArrayAccess { Array.Type: SzArrayTypeAnalysisContext addressedArray } }
                => new ByRefTypeAnalysisContext(addressedArray.ElementType),
            AddressOf => context.AppContext.SystemTypes.SystemIntPtrType,
            ReferenceCast cast => cast.Type,
            StringLiteral => context.AppContext.SystemTypes.SystemStringType,
            FloatLiteral => context.AppContext.SystemTypes.SystemSingleType,
            DoubleLiteral => context.AppContext.SystemTypes.SystemDoubleType,
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
            _ => null
        };

    private static TypeAnalysisContext? ResolveSystemType(MethodAnalysisContext context, string fullName) =>
        context.AppContext.GetAssemblyByName("mscorlib")?.GetTypeByFullName(fullName);

    // Mirrors the Immediate branch of LoadOperand: the reported stack type is whatever
    // the literal actually emits under the consumer's contract.
    private static TypeAnalysisContext EmittedImmediateType(Immediate immediate, TypeAnalysisContext? expectedType,
        MethodAnalysisContext context)
    {
        var systemTypes = context.AppContext.SystemTypes;
        var literalType = expectedType is { IsEnumType: true }
            ? expectedType.DefaultEnumUnderlyingType ?? expectedType
            : expectedType;
        return literalType?.FullName switch
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
    private static int IntegralStackWidth(TypeAnalysisContext? type)
    {
        if (type == null)
            return 0;
        if (type is PointerTypeAnalysisContext or ByRefTypeAnalysisContext || IsNativeHandleType(type))
            return -1;

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
    // required: primitive width change, box, unbox or reference cast. No-ops whenever
    // the stack contract already matches or no legal conversion exists.
    private static void EmitStackCoerce(TypeAnalysisContext? from, TypeAnalysisContext? to, MethodDefinition method,
        bool convertByRef = false)
    {
        // Handle contexts have no managed stack type of their own; everything below
        // reasons about the native int they emit as.
        if (from != null && IsNativeHandleType(from))
            from = from.AppContext.SystemTypes.SystemIntPtrType;
        if (to != null && IsNativeHandleType(to))
            to = to.AppContext.SystemTypes.SystemIntPtrType;

        if (from == null || to == null || from.FullName == to.FullName)
            return;

        // No stack op synthesizes a generic-parameter or byref value from another kind.
        if (to is GenericParameterTypeAnalysisContext or ByRefTypeAnalysisContext
            || from is GenericParameterTypeAnalysisContext)
            return;

        var instructions = method.CilMethodBody!.Instructions;
        var fromWidth = IntegralStackWidth(from);
        var toWidth = IntegralStackWidth(to);

        // ceq/cgt/clt cannot merge a managed pointer with anything else, while add/sub
        // on `&` want the pointer kept as-is, so the conversion is opt-in per site.
        if (from is ByRefTypeAnalysisContext or PointerTypeAnalysisContext
            && convertByRef && toWidth != 0)
        {
            instructions.Add(CilOpCodes.Conv_I);
            fromWidth = -1;
        }

        // A managed pointer read back as a value is an honest dereference: ldobj on
        // an exact element match, ldind.ref for reference targets.
        if (from is ByRefTypeAnalysisContext byRef && to is not ByRefTypeAnalysisContext
            && fromWidth == -1 && !convertByRef)
        {
            if (to.IsValueType)
            {
                if (byRef.ElementType.FullName == to.FullName && CanEmitTypeToken(to))
                    instructions.Add(CilOpCodes.Ldobj, to.ToTypeSignature().ToTypeDefOrRef());
            }
            else if (!byRef.ElementType.IsValueType)
                instructions.Add(CilOpCodes.Ldind_Ref);
            return;
        }

        if (fromWidth != 0 && toWidth != 0)
        {
            if (fromWidth == toWidth)
                return;
            if (toWidth < 0)
                instructions.Add(IsUnsignedType(from) ? CilOpCodes.Conv_U : CilOpCodes.Conv_I);
            else if (toWidth == 8)
                instructions.Add(IsUnsignedType(from) ? CilOpCodes.Conv_U8 : CilOpCodes.Conv_I8);
            else
                instructions.Add(IsUnsignedType(from) ? CilOpCodes.Conv_U4 : CilOpCodes.Conv_I4);
            return;
        }

        var fromIsFloat = from.FullName is "System.Single" or "System.Double";
        var toIsFloat = to.FullName is "System.Single" or "System.Double";

        if (fromIsFloat && toWidth != 0)
        {
            instructions.Add(toWidth == 8 ? CilOpCodes.Conv_I8 : CilOpCodes.Conv_I4);
            return;
        }

        if (toIsFloat)
        {
            if (fromIsFloat || fromWidth != 0)
                instructions.Add(to.FullName == "System.Single" ? CilOpCodes.Conv_R4 : CilOpCodes.Conv_R8);
            return;
        }

        if (from.IsValueType && !to.IsValueType)
        {
            if (CanEmitTypeToken(from))
                instructions.Add(CilOpCodes.Box, from.ToTypeSignature().ToTypeDefOrRef());
            // box yields a `from` reference; an interface/other-ref destination still
            // needs the narrowing cast the verifier requires.
            if (!IsAssignableToLoose(from, to) && CanEmitTypeToken(to))
                instructions.Add(CilOpCodes.Castclass, to.ToTypeSignature().ToTypeDefOrRef());
            return;
        }

        if (!from.IsValueType && to.IsValueType)
        {
            if (CanEmitTypeToken(to))
                instructions.Add(CilOpCodes.Unbox_Any, to.ToTypeSignature().ToTypeDefOrRef());
            return;
        }

        if (!from.IsValueType && !to.IsValueType && !IsAssignableToLoose(from, to) && CanEmitTypeToken(to))
            instructions.Add(CilOpCodes.Castclass, to.ToTypeSignature().ToTypeDefOrRef());
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

    // The shared operand type for a binary instruction: the widest non-literal
    // operand, or (for value-producing ops) the destination. Comparison destinations
    // are the bool result, never the compared type, so they must not seed it.
    private static TypeAnalysisContext? BinaryOperandType(Instruction instruction, MethodAnalysisContext context,
        bool allowDestination)
    {
        TypeAnalysisContext? picked = null;
        var pickedWidth = 0;
        foreach (var operand in instruction.Operands.Skip(1))
        {
            var width = IntegralStackWidth(EmittedOperandType(operand, context));
            if (width == 0)
                continue;
            if (width < 0)
                // Pointer/byref/native-int operands make the operation native-int;
                // returning IntPtr (not the operand's own type) keeps zero literals
                // as `conv.i` instead of an invalid null/pointer confusion.
                return context.AppContext.SystemTypes.SystemIntPtrType;
            if (width > pickedWidth)
            {
                picked = EmittedOperandType(operand, context);
                pickedWidth = width;
            }
        }

        if (picked != null || !allowDestination)
            return picked;

        var destination = EmittedOperandType(instruction.Operands[0], context);
        return IntegralStackWidth(destination) != 0 ? destination : null;
    }

    private static void LoadLocal(LocalVariable local, MethodDefinition method, Dictionary<LocalVariable, CilLocalVariable> locals)
    {
        var instructions = method.CilMethodBody!.Instructions;

        if (local.IsThis)
        {
            instructions.Add(CilOpCodes.Ldarg_0);
            return;
        }

        var parameter = method.Parameters.FirstOrDefault(p => p.Name == local.Name);

        if (parameter != null)
            instructions.Add(CilOpCodes.Ldarg, parameter);
        else
            instructions.Add(CilOpCodes.Ldloc, locals[local]);
    }

    private static void StoreToOperand(IOperand operand, MethodDefinition method,
        Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine)
    {
        var instructions = method.CilMethodBody!.Instructions;

        switch (operand)
        {
            case LocalVariable local:
                instructions.Add(CilOpCodes.Stloc, locals[local]);
                break;

            case FieldReference field:
                var fieldDescriptor = field.Field.ToFieldDescriptor();

                if (field.Field.IsStatic)
                {
                    instructions.Add(CilOpCodes.Stsfld, fieldDescriptor);
                    break;
                }

                // stfld wants the object underneath the value, but the value is already on the stack, so
                // park it in a temporary while we load the object.
                var scratch = new CilLocalVariable(fieldDescriptor.Signature!.FieldType);
                method.CilMethodBody!.LocalVariables.Add(scratch);

                instructions.Add(CilOpCodes.Stloc, scratch);
                LoadLocal(field.Local, method, locals);
                instructions.Add(CilOpCodes.Ldloc, scratch);
                instructions.Add(CilOpCodes.Stfld, fieldDescriptor);
                break;

            case ArrayAccess arrayAccess:
                // stelem needs array and index before the value, so the same trick as stfld
                var elementType = ((SzArrayTypeAnalysisContext)arrayAccess.Array.Type!).ElementType;
                var elementScratch = new CilLocalVariable(elementType.ToTypeSignature());
                method.CilMethodBody!.LocalVariables.Add(elementScratch);

                instructions.Add(CilOpCodes.Stloc, elementScratch);
                LoadLocal(arrayAccess.Array, method, locals);
                LoadOperand(arrayAccess.Index, method, locals, writeLine);
                instructions.Add(CilOpCodes.Ldloc, elementScratch);
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
