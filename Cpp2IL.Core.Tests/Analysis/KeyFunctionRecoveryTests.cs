using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class KeyFunctionRecoveryTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    [Test]
    public void BoxTypeFallsBackToAddressedValue()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var value = new LocalVariable("value", new Register(null, "value"))
            { Type = app.SystemTypes.SystemInt32Type };
        var result = new LocalVariable("result", new Register(null, "result"));
        var instruction = new Instruction(0, OpCode.Call,
            new StringLiteral("il2cpp_vm_object_box"), result,
            new MemoryOperand(addend: 0x81AAA10), new AddressOf(value));

        KeyFunctionRecovery.RewriteBox(instruction);

        Assert.That(instruction.OpCode, Is.EqualTo(OpCode.Box));
        Assert.That(instruction.Operands[0], Is.SameAs(result));
        Assert.That(instruction.Operands[1], Is.SameAs(app.SystemTypes.SystemInt32Type));
        Assert.That(((AddressOf)instruction.Operands[2]).Target, Is.SameAs(value));
    }

    [Test]
    public void NativeEndCatchBookkeepingIsRemoved()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var end = new Instruction(0, OpCode.CallVoid, new StringLiteral("__cxa_end_catch"));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Fixture",
            app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([end, new(1, OpCode.Return)])
        };

        KeyFunctionRecovery.Run(method);

        Assert.Multiple(() =>
        {
            Assert.That(end.OpCode, Is.EqualTo(OpCode.Nop));
            Assert.That(end.Operands, Is.Empty);
        });
    }

    [Test]
    public void NativeBeginCatchBecomesWrapperCellPointer()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var header = new LocalVariable("header", new Register(null, "x0"));
        var wrapper = new LocalVariable("wrapper", new Register(null, "x1"));
        var exception = new LocalVariable("exception", new Register(null, "x2"));
        var beginCatch = new Instruction(0, OpCode.Call,
            new StringLiteral("__cxa_begin_catch"), wrapper, header);
        var load = new Instruction(1, OpCode.Move, exception, new MemoryOperand(wrapper));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Fixture",
            app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([beginCatch, load, new(2, OpCode.Return)])
        };

        KeyFunctionRecovery.Run(method);

        Assert.Multiple(() =>
        {
            Assert.That(beginCatch.OpCode, Is.EqualTo(OpCode.Add));
            Assert.That(beginCatch.Operands[0], Is.SameAs(wrapper));
            Assert.That(beginCatch.Operands[1], Is.SameAs(header));
            Assert.That(((Immediate)beginCatch.Operands[2]).Value,
                Is.EqualTo(KeyFunctionRecovery.UnwindHeaderToObjectOffset));
            Assert.That(wrapper.Type, Is.TypeOf<PointerTypeAnalysisContext>());
            Assert.That(((PointerTypeAnalysisContext)wrapper.Type!).ElementType,
                Is.SameAs(app.SystemTypes.SystemExceptionType));
            Assert.That(exception.Type, Is.SameAs(app.SystemTypes.SystemExceptionType));
        });
    }

    [Test]
    public void NativeBeginCatchDiscardedResultIsRemoved()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var header = new LocalVariable("header", new Register(null, "x0"));
        var beginCatch = new Instruction(0, OpCode.CallVoid,
            new StringLiteral("__cxa_begin_catch"), header);
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Fixture",
            app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([beginCatch, new(1, OpCode.Return)])
        };

        KeyFunctionRecovery.Run(method);

        Assert.That(beginCatch.OpCode, Is.EqualTo(OpCode.Nop));
    }

    [Test]
    public void NativeBeginCatchWithForeignUseKeepsUntypedPointer()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var header = new LocalVariable("header", new Register(null, "x0"));
        var wrapper = new LocalVariable("wrapper", new Register(null, "x1"));
        var other = new LocalVariable("other", new Register(null, "x2"));
        var beginCatch = new Instruction(0, OpCode.Call,
            new StringLiteral("__cxa_begin_catch"), wrapper, header);
        // A read past the exception field: not the il2cpp wrapper extraction.
        var foreignLoad = new Instruction(1, OpCode.Move, other, new MemoryOperand(wrapper, addend: 8));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Fixture",
            app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([beginCatch, foreignLoad, new(2, OpCode.Return)])
        };

        KeyFunctionRecovery.Run(method);

        Assert.Multiple(() =>
        {
            // The pointer arithmetic is still provable; the exception typing is not.
            Assert.That(beginCatch.OpCode, Is.EqualTo(OpCode.Add));
            Assert.That(wrapper.Type, Is.Null);
            Assert.That(other.Type, Is.Null);
        });
    }

    [Test]
    public void NativeRethrowThrowsTheCaughtException()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var header = new LocalVariable("header", new Register(null, "x0"));
        var wrapper = new LocalVariable("wrapper", new Register(null, "x1"));
        var exception = new LocalVariable("exception", new Register(null, "x2"));
        var beginCatch = new Instruction(0, OpCode.Call,
            new StringLiteral("__cxa_begin_catch"), wrapper, header);
        var load = new Instruction(1, OpCode.Move, exception, new MemoryOperand(wrapper));
        var rethrow = new Instruction(2, OpCode.CallVoid, new StringLiteral("__cxa_rethrow"));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Fixture",
            app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([beginCatch, load, rethrow])
        };
        method.DominatorInfo = new DominatorInfo(method.ControlFlowGraph);

        KeyFunctionRecovery.Run(method);

        Assert.Multiple(() =>
        {
            Assert.That(rethrow.OpCode, Is.EqualTo(OpCode.Throw));
            Assert.That(rethrow.Operands[0], Is.SameAs(exception));
        });
    }

    [Test]
    public void NativeRethrowWithoutExceptionLoadSynthesizesIt()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var header = new LocalVariable("header", new Register(null, "x0"));
        var wrapper = new LocalVariable("wrapper", new Register(null, "x1"));
        var beginCatch = new Instruction(0, OpCode.Call,
            new StringLiteral("__cxa_begin_catch"), wrapper, header);
        var rethrow = new Instruction(1, OpCode.CallVoid, new StringLiteral("__cxa_rethrow"));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Fixture",
            app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([beginCatch, rethrow])
        };
        method.DominatorInfo = new DominatorInfo(method.ControlFlowGraph);

        KeyFunctionRecovery.Run(method);

        Assert.Multiple(() =>
        {
            Assert.That(rethrow.OpCode, Is.EqualTo(OpCode.Throw));
            var exception = rethrow.Operands[0] as LocalVariable;
            Assert.That(exception, Is.Not.Null);
            Assert.That(exception!.Type, Is.SameAs(app.SystemTypes.SystemExceptionType));
            var load = method.ControlFlowGraph!.Instructions
                .Single(i => i.OpCode == OpCode.Move && i.Operands[0] == (IOperand)exception);
            Assert.That(((MemoryOperand)load.Operands[1]).Base, Is.SameAs(wrapper));
        });
    }

    [Test]
    public void NativeRethrowOutsideCatchStaysUnresolved()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var rethrow = new Instruction(0, OpCode.CallVoid, new StringLiteral("__cxa_rethrow"));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Fixture",
            app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([rethrow, new(1, OpCode.Return)])
        };

        KeyFunctionRecovery.Run(method);

        Assert.That(rethrow.OpCode, Is.EqualTo(OpCode.CallVoid));
        Assert.That(rethrow.Operands[0], Is.TypeOf<StringLiteral>());
    }

    [Test]
    public void NativeUnwindResumeRethrowsTheResumedException()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var header = new LocalVariable("header", new Register(null, "x0"));
        var resume = new Instruction(0, OpCode.CallVoid,
            new StringLiteral("_Unwind_Resume"), header);
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Fixture",
            app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([resume])
        };

        KeyFunctionRecovery.Run(method);

        Assert.Multiple(() =>
        {
            Assert.That(resume.OpCode, Is.EqualTo(OpCode.Throw));
            var exception = resume.Operands[0] as LocalVariable;
            Assert.That(exception, Is.Not.Null);
            Assert.That(exception!.Type, Is.SameAs(app.SystemTypes.SystemExceptionType));

            var instructions = method.ControlFlowGraph!.Instructions;
            var add = instructions.FirstOrDefault(i => i.OpCode == OpCode.Add);
            var load = instructions.FirstOrDefault(i => i.OpCode == OpCode.Move);
            Assert.That(add, Is.Not.Null);
            Assert.That(load, Is.Not.Null);
            Assert.That(load!.Operands[0], Is.SameAs(exception));
            Assert.That(((MemoryOperand)load.Operands[1]).Base, Is.SameAs(add!.Operands[0]));
            Assert.That(((Immediate)add.Operands[2]).Value,
                Is.EqualTo(KeyFunctionRecovery.UnwindHeaderToObjectOffset));
        });
    }

    [Test]
    public void NativeUnwindResumeOnWrapperCellLoadsDirectly()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var header = new LocalVariable("header", new Register(null, "x0"));
        var wrapper = new LocalVariable("wrapper", new Register(null, "x1"));
        var beginCatch = new Instruction(0, OpCode.Call,
            new StringLiteral("__cxa_begin_catch"), wrapper, header);
        var resume = new Instruction(1, OpCode.CallVoid,
            new StringLiteral("_Unwind_Resume"), wrapper);
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Fixture",
            app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([beginCatch, resume])
        };

        method.DominatorInfo = new DominatorInfo(method.ControlFlowGraph);

        KeyFunctionRecovery.Run(method);

        Assert.Multiple(() =>
        {
            Assert.That(resume.OpCode, Is.EqualTo(OpCode.Throw));
            var exception = resume.Operands[0] as LocalVariable;
            Assert.That(exception, Is.Not.Null);
            // The argument already is the wrapper cell: no extra header add.
            Assert.That(method.ControlFlowGraph!.Instructions
                .Any(i => i.OpCode == OpCode.Add && i.Operands[1] == (IOperand)wrapper), Is.False);
        });
    }

    [Test]
    public void NativeUnwindResumeWithImmediateArgumentStaysUnresolved()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var resume = new Instruction(0, OpCode.CallVoid,
            new StringLiteral("_Unwind_Resume"), new Immediate(0));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Fixture",
            app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([resume])
        };

        KeyFunctionRecovery.Run(method);

        Assert.That(resume.OpCode, Is.EqualTo(OpCode.CallVoid));
    }

    [Test]
    public void CallTerminateThunkBecomesTerminalThrow()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var call = new Instruction(0, OpCode.CallVoid,
            new StringLiteral("__clang_call_terminate"));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Fixture",
            app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([call])
        };

        KeyFunctionRecovery.Run(method);

        Assert.Multiple(() =>
        {
            Assert.That(call.OpCode, Is.EqualTo(OpCode.Throw));
            Assert.That(call.Operands[0], Is.SameAs(app.SystemTypes.SystemExceptionType));
        });
    }

    [Test]
    public void CaughtExceptionLoadEmitsManagedReferenceLoadAndRethrow()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var exceptionType = app.SystemTypes.SystemExceptionType;
        var header = new LocalVariable("header", new Register(null, "x0"));
        var wrapper = new LocalVariable("wrapper", new Register(null, "x1"));
        var exception = new LocalVariable("exception", new Register(null, "x2"));
        var beginCatch = new Instruction(0, OpCode.Call,
            new StringLiteral("__cxa_begin_catch"), wrapper, header);
        var load = new Instruction(1, OpCode.Move, exception, new MemoryOperand(wrapper));
        var rethrow = new Instruction(2, OpCode.CallVoid, new StringLiteral("__cxa_rethrow"));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Fixture",
            app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([beginCatch, load, rethrow])
        };
        method.DominatorInfo = new DominatorInfo(method.ControlFlowGraph);
        method.Locals = [header, wrapper, exception];
        method.ParameterLocals = [];
        method.AnalysisWarnings = [];

        KeyFunctionRecovery.Run(method);

        var module = new AsmResolver.DotNet.ModuleDefinition("CatchPad.dll");
        var callerType = new AsmResolver.DotNet.TypeDefinition("Tests", "CatchPad",
            AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(callerType);
        if (exceptionType.GetExtraData<AsmResolver.DotNet.TypeDefinition>("AsmResolverType") == null)
            exceptionType.PutExtraData("AsmResolverType",
                new AsmResolver.DotNet.TypeDefinition(exceptionType.Namespace, exceptionType.Name,
                    AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public));
        var emit = new AsmResolver.DotNet.MethodDefinition("Run",
            AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
                | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            AsmResolver.DotNet.Signatures.MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        callerType.Methods.Add(emit);

        IlGenerator.GenerateIl(method, emit);
        var il = emit.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == AsmResolver.PE.DotNet.Cil.CilOpCodes.Ldind_Ref),
                Is.True, () => string.Join("\n", il));
            Assert.That(il.Any(i => i.OpCode == AsmResolver.PE.DotNet.Cil.CilOpCodes.Throw),
                Is.True, () => string.Join("\n", il));
        });
    }

    [Test]
    public void NativeExceptionWrapperThrowBecomesManagedThrow()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var allocation = new LocalVariable("allocation", new Register(null, "x0"));
        var exception = new LocalVariable("exception", new Register(null, "x1"))
            { Type = app.SystemTypes.SystemExceptionType };
        var allocate = new Instruction(0, OpCode.Call,
            new StringLiteral("__cxa_allocate_exception"), allocation,
            new Immediate(app.Binary.is32Bit ? 4 : 8));
        var store = new Instruction(1, OpCode.Move, new MemoryOperand(allocation), exception);
        var nativeThrow = new Instruction(2, OpCode.Call,
            new StringLiteral("__cxa_throw"), new LocalVariable("unused", new Register(null, "x0")),
            allocation, new Immediate(0x1234), new Immediate(0));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Fixture",
            app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([allocate, store, nativeThrow])
        };

        var rewritten = KeyFunctionRecovery.RewriteNativeExceptionThrow(method, nativeThrow, _ => true);

        Assert.Multiple(() =>
        {
            Assert.That(rewritten, Is.True);
            Assert.That(allocate.OpCode, Is.EqualTo(OpCode.Nop));
            Assert.That(store.OpCode, Is.EqualTo(OpCode.Nop));
            Assert.That(nativeThrow.OpCode, Is.EqualTo(OpCode.Throw));
            Assert.That(nativeThrow.Operands[0], Is.SameAs(exception));
        });
    }

    [Test]
    public void NativeExceptionWrapperWithEscapingAllocationIsPreserved()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var allocation = new LocalVariable("allocation", new Register(null, "x0"));
        var exception = new LocalVariable("exception", new Register(null, "x1"));
        var allocate = new Instruction(0, OpCode.Call,
            new StringLiteral("__cxa_allocate_exception"), allocation,
            new Immediate(app.Binary.is32Bit ? 4 : 8));
        var store = new Instruction(1, OpCode.Move, new MemoryOperand(allocation), exception);
        var escape = new Instruction(2, OpCode.Move,
            new LocalVariable("copy", new Register(null, "x2")), allocation);
        var nativeThrow = new Instruction(3, OpCode.CallVoid, new StringLiteral("__cxa_throw"),
            allocation, new Immediate(0x1234), new Immediate(0));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Fixture",
            app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([allocate, store, escape, nativeThrow])
        };

        Assert.That(KeyFunctionRecovery.RewriteNativeExceptionThrow(method, nativeThrow, _ => true), Is.False);
        Assert.That(nativeThrow.OpCode, Is.EqualTo(OpCode.CallVoid));
    }

    [Test]
    public void MistypedExceptionWrapperCellStillBecomesManagedThrow()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var allocation = new LocalVariable("allocation", new Register(null, "x0"));
        var exception = new LocalVariable("exception", new Register(null, "x1"));
        var fakeOwner = app.SystemTypes.SystemExceptionType;
        var fakeField = fakeOwner.Fields[0];
        var priorUse = new Instruction(-1, OpCode.Move,
            new LocalVariable("prior", new Register(null, "x2")), allocation);
        var allocate = new Instruction(0, OpCode.Call,
            new StringLiteral("__cxa_allocate_exception"), allocation,
            new Immediate(app.Binary.is32Bit ? 4 : 8));
        var store = new Instruction(1, OpCode.Move,
            new FieldReference(fakeField, allocation, 0), exception);
        var nativeThrow = new Instruction(4, OpCode.CallVoid, new StringLiteral("__cxa_throw"),
            allocation, new Immediate(0x1234), new Immediate(0));
        var guard = new Instruction(2, OpCode.ConditionalJump, nativeThrow, new Immediate(1));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Fixture",
            app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([priorUse, allocate, store, guard, new(3, OpCode.Nop), nativeThrow])
        };

        Assert.That(KeyFunctionRecovery.RewriteNativeExceptionThrow(method, nativeThrow, _ => true), Is.True);
        Assert.That(nativeThrow.Operands[0], Is.SameAs(exception));
    }

    [Test]
    public void IsInstHelperBecomesManagedReferenceCast()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var value = new LocalVariable("value", new Register(null, "value"))
            { Type = app.SystemTypes.SystemObjectType };
        var result = new LocalVariable("result", new Register(null, "result"))
            { Type = app.SystemTypes.SystemStringType };
        var instruction = new Instruction(0, OpCode.Call,
            new StringLiteral("il2cpp_vm_object_is_inst"), result, value,
            app.SystemTypes.SystemStringType, new Immediate(0));

        KeyFunctionRecovery.RewriteIsInst(instruction,
            new ISILControlFlowGraph([instruction, new(1, OpCode.Return)]), app.Binary.is32Bit);

        Assert.That(instruction.OpCode, Is.EqualTo(OpCode.Move));
        Assert.That(instruction.Operands[0], Is.SameAs(result));
        Assert.That(instruction.Operands[1], Is.TypeOf<ReferenceCast>());
        Assert.That(((ReferenceCast)instruction.Operands[1]).Type,
            Is.SameAs(app.SystemTypes.SystemStringType));
        Assert.That(((ReferenceCast)instruction.Operands[1]).NullOnFailure, Is.True);
    }

    [Test]
    public void IsInstRuntimeClassBecomesCastToRepresentedType()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var value = new LocalVariable("value", new Register(null, "value"))
            { Type = app.SystemTypes.SystemObjectType };
        var result = new LocalVariable("result", new Register(null, "result"));
        var runtimeClass = new RuntimeClassTypeAnalysisContext(app.SystemTypes.SystemStringType,
            app.SystemTypes.SystemStringType.DeclaringAssembly);
        var instruction = new Instruction(0, OpCode.Call,
            new StringLiteral("il2cpp_vm_object_is_inst"), result, value,
            runtimeClass, new Immediate(0));

        KeyFunctionRecovery.RewriteIsInst(instruction,
            new ISILControlFlowGraph([instruction, new(1, OpCode.Return)]), app.Binary.is32Bit);

        Assert.That(instruction.OpCode, Is.EqualTo(OpCode.Move));
        Assert.That(((ReferenceCast)instruction.Operands[1]).Type,
            Is.SameAs(app.SystemTypes.SystemStringType));
    }

    [Test]
    public void InlinedClassHierarchyCheckBecomesNullableIsInst()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var value = new LocalVariable("value", new Register(null, "value"))
            { Type = app.SystemTypes.SystemObjectType };
        var runtimeClass = new LocalVariable("runtimeClass", new Register(null, "runtimeClass"))
            { Type = new RuntimeClassTypeAnalysisContext(app.SystemTypes.SystemObjectType,
                app.SystemTypes.SystemObjectType.DeclaringAssembly) };
        var targetClass = new LocalVariable("targetClass", new Register(null, "targetClass"))
            { Type = new RuntimeClassTypeAnalysisContext(app.SystemTypes.SystemStringType,
                app.SystemTypes.SystemStringType.DeclaringAssembly) };
        var shiftedDepth = new LocalVariable("shiftedDepth", new Register(null, "shiftedDepth"));
        var hierarchyAddress = new LocalVariable("hierarchyAddress", new Register(null, "hierarchyAddress"));
        var result = new LocalVariable("result", new Register(null, "result"))
            { Type = app.SystemTypes.SystemBooleanType };
        var depthResult = new LocalVariable("depthResult", new Register(null, "depthResult"))
            { Type = app.SystemTypes.SystemBooleanType };
        var failure = new Instruction(8, OpCode.Return);
        var depthCheck = new Instruction(2, OpCode.CheckLess, depthResult,
            new MemoryOperand(runtimeClass, addend: 0x130),
            new MemoryOperand(targetClass, addend: 0x130));
        var check = new Instruction(6, OpCode.CheckEqual, result,
            new MemoryOperand(hierarchyAddress, addend: -8), app.SystemTypes.SystemStringType);
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Fixture",
            app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([
                new(0, OpCode.Move, runtimeClass, new MemoryOperand(value)),
                new(1, OpCode.Move, targetClass, app.SystemTypes.SystemStringType),
                depthCheck,
                new(3, OpCode.ConditionalJump, failure, depthResult),
                new(4, OpCode.ShiftLeft, shiftedDepth,
                    new MemoryOperand(targetClass, addend: 0x130), new Immediate(3)),
                new(5, OpCode.Add, hierarchyAddress,
                    new MemoryOperand(runtimeClass, addend: 0xC8), shiftedDepth),
                check,
                new(7, OpCode.Return),
                failure]),
        };

        KeyFunctionRecovery.Run(method);

        Assert.That(check.OpCode, Is.EqualTo(OpCode.CheckNotEqual));
        Assert.That(check.Operands[1], Is.TypeOf<ReferenceCast>());
        var cast = (ReferenceCast)check.Operands[1];
        Assert.Multiple(() =>
        {
            Assert.That(depthCheck.OpCode, Is.EqualTo(OpCode.Move));
            Assert.That(((Immediate)depthCheck.Operands[1]).Value, Is.Zero);
            Assert.That(cast.Value, Is.SameAs(value));
            Assert.That(cast.Type, Is.SameAs(app.SystemTypes.SystemStringType));
            Assert.That(cast.NullOnFailure, Is.True);
            Assert.That(check.Operands[2], Is.TypeOf<Immediate>());
            Assert.That(((Immediate)check.Operands[2]).Value, Is.Zero);
        });
    }

    [Test]
    public void IsInstArrayElementClassBecomesManagedReferenceCast()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var value = new LocalVariable("value", new Register(null, "value"))
            { Type = app.SystemTypes.SystemObjectType };
        var result = new LocalVariable("result", new Register(null, "result"));
        var arrayClass = new LocalVariable("arrayClass", new Register(null, "klass"))
        {
            Type = new RuntimeClassTypeAnalysisContext(
                new SzArrayTypeAnalysisContext(app.SystemTypes.SystemStringType),
                app.SystemTypes.SystemStringType.DeclaringAssembly),
        };
        var elementClassOffset = app.Binary.is32Bit ? 0u : 0x40u;
        var classPointer = new LocalVariable("classPointer", new Register(null, "target"));
        var classLoad = new Instruction(0, OpCode.Move, classPointer,
            new MemoryOperand(arrayClass, addend: elementClassOffset));
        var instruction = new Instruction(1, OpCode.Call,
            new StringLiteral("il2cpp_vm_object_is_inst"), result, value,
            classPointer, new Immediate(0));
        var graph = new ISILControlFlowGraph([classLoad, instruction, new(2, OpCode.Return)]);

        KeyFunctionRecovery.RewriteIsInst(instruction, graph, app.Binary.is32Bit);

        Assert.That(instruction.OpCode, Is.EqualTo(OpCode.Move));
        Assert.That(((ReferenceCast)instruction.Operands[1]).Type,
            Is.SameAs(app.SystemTypes.SystemStringType));
    }

    [Test]
    public void IsInstArrayObjectClassBecomesManagedReferenceCast()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var value = new LocalVariable("value", new Register(null, "value"))
            { Type = app.SystemTypes.SystemObjectType };
        var result = new LocalVariable("result", new Register(null, "result"));
        var array = new LocalVariable("array", new Register(null, "array"))
            { Type = new SzArrayTypeAnalysisContext(app.SystemTypes.SystemStringType) };
        var arrayClass = new LocalVariable("arrayClass", new Register(null, "klass"));
        var elementClass = new LocalVariable("elementClass", new Register(null, "element"));
        var elementClassOffset = app.Binary.is32Bit ? 0u : 0x40u;
        var instruction = new Instruction(2, OpCode.Call,
            new StringLiteral("il2cpp_vm_object_is_inst"), result, value,
            elementClass, new Immediate(0));
        var graph = new ISILControlFlowGraph([
            new(0, OpCode.Move, arrayClass, new MemoryOperand(array)),
            new(1, OpCode.Move, elementClass, new MemoryOperand(arrayClass, addend: elementClassOffset)),
            instruction,
            new(3, OpCode.Return),
        ]);

        KeyFunctionRecovery.RewriteIsInst(instruction, graph, app.Binary.is32Bit);

        Assert.That(instruction.OpCode, Is.EqualTo(OpCode.Move));
        Assert.That(((ReferenceCast)instruction.Operands[1]).Type,
            Is.SameAs(app.SystemTypes.SystemStringType));
    }

    [Test]
    public void ArrayElementClassLoadBecomesRuntimeClassOperand()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var arrayClass = new LocalVariable("arrayClass", new Register(null, "klass"))
        {
            Type = new RuntimeClassTypeAnalysisContext(
                new SzArrayTypeAnalysisContext(app.SystemTypes.SystemStringType),
                app.SystemTypes.SystemStringType.DeclaringAssembly),
        };
        var elementClass = new LocalVariable("elementClass", new Register(null, "element"));
        var load = new Instruction(0, OpCode.Move, elementClass,
            new MemoryOperand(arrayClass, addend: app.Binary.is32Bit ? 0 : 0x40));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Fixture",
            app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([load, new(1, OpCode.Return)]),
        };

        KeyFunctionRecovery.Run(method);

        Assert.That(load.Operands[1], Is.TypeOf<RuntimeClassTypeAnalysisContext>());
        Assert.That(((RuntimeClassTypeAnalysisContext)load.Operands[1]).RepresentedType,
            Is.SameAs(app.SystemTypes.SystemStringType));
        Assert.That(elementClass.Type, Is.SameAs(load.Operands[1]));
    }

    [Test]
    public void OrdinaryClassElementLoadPreservesRepresentedType()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var klass = new LocalVariable("klass", new Register(null, "klass"))
        {
            Type = new RuntimeClassTypeAnalysisContext(app.SystemTypes.SystemStringType,
                app.SystemTypes.SystemStringType.DeclaringAssembly),
        };
        var elementClass = new LocalVariable("elementClass", new Register(null, "element"));
        var load = new Instruction(0, OpCode.Move, elementClass,
            new MemoryOperand(klass, addend: app.Binary.is32Bit ? 0 : 0x40));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Fixture",
            app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([load, new(1, OpCode.Return)]),
        };

        KeyFunctionRecovery.Run(method);

        Assert.That(((RuntimeClassTypeAnalysisContext)load.Operands[1]).RepresentedType,
            Is.SameAs(app.SystemTypes.SystemStringType));
    }

    [Test]
    public void Unity6DefaultsInt32ClassOffsetIsRecognized()
    {
        var types = Cpp2IlApi.CurrentAppContext!.SystemTypes;

        Assert.That(KeyFunctionRecovery.Unity6PrimitiveDefaultsClass(types, 0x48),
            Is.SameAs(types.SystemInt32Type));
        Assert.That(KeyFunctionRecovery.Unity6PrimitiveDefaultsClass(types, 0x78),
            Is.SameAs(types.SystemSingleType));
        Assert.That(KeyFunctionRecovery.Unity6PrimitiveDefaultsClass(types, 0x90),
            Is.SameAs(types.SystemStringType));
    }

    [Test]
    public void Unity6DefaultsClassLoadSeedsRuntimeClassType()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimpleV106Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var defaults = new LocalVariable("defaults", new Register(null, "X8"));
        var klass = new LocalVariable("klass", new Register(null, "X9"));
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Read",
            app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, defaults, new MemoryOperand(addend: 0x81AAA10)),
            new(1, OpCode.Move, klass, new MemoryOperand(defaults, addend: 0x90)),
            new(2, OpCode.Return)]);

        LocalVariables.SeedIl2CppDefaultsClassTypes(context);

        Assert.That(klass.Type, Is.TypeOf<RuntimeClassTypeAnalysisContext>());
        Assert.That(((RuntimeClassTypeAnalysisContext)klass.Type!).RepresentedType,
            Is.SameAs(app.SystemTypes.SystemStringType));
    }

    [Test]
    public void DefaultsDefinitionMatchesClonedSsaLocalByRegister()
    {
        var register = new Register(null, "x23", 4);
        var definition = new LocalVariable("definition", register);
        var use = new LocalVariable("use", register);
        var graph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, definition, new MemoryOperand(addend: 0x81AAA10)),
            new Instruction(1, OpCode.Return),
        ]);

        Assert.That(KeyFunctionRecovery.HasAbsoluteDefinition(graph, use), Is.True);
    }

    [Test]
    public void BoxClassPointerMoveIsUnwrappedToDefaultsField()
    {
        var defaults = new LocalVariable("defaults", new Register(null, "x23", 4));
        var classPointer = new LocalVariable("classPointer", new Register(null, "x0", 126));
        var source = new MemoryOperand(defaults, addend: 0x48);
        var graph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, classPointer, source),
            new Instruction(1, OpCode.Return),
        ]);

        Assert.That(KeyFunctionRecovery.ResolveMoveSource(graph, classPointer), Is.EqualTo(source));
    }
}
