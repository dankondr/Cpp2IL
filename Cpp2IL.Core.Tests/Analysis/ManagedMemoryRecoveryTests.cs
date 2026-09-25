using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using AsmResolver;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Analysis;

public class ManagedMemoryRecoveryTests
{
    private ApplicationAnalysisContext _app = null!;
    private TypeAnalysisContext _int32 = null!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        _app = TestGameLoader.LoadSimple2019Game();
        _int32 = _app.SystemTypes.SystemInt32Type;
    }

    private static LocalVariable Local(string name, int register) =>
        new(name, new Register(register, $"X{register}"));

    private MethodAnalysisContext NewCaller(string name, SzArrayTypeAnalysisContext arrayType,
        out LocalVariable array)
    {
        var holder = new InjectedTypeAnalysisContext(_app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", $"{name}Holder", _app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        var caller = new InjectedMethodAnalysisContext(holder, name, _int32,
            R.MethodAttributes.Public | R.MethodAttributes.Static,
            (ReadOnlySpan<TypeAnalysisContext>)[arrayType], (ReadOnlySpan<string>)["input"]);
        holder.Methods.Add(caller);
        array = new LocalVariable("input", new Register(0, "X0"), arrayType);
        caller.ParameterLocals = [array];
        caller.Locals = [array];
        caller.AnalysisWarnings = [];
        return caller;
    }

    private static void AssertNoMemoryOperands(MethodAnalysisContext caller) =>
        Assert.That(caller.ControlFlowGraph!.Instructions.SelectMany(i => i.Operands).OfType<MemoryOperand>(),
            Is.Empty);

    private static IEnumerable<Instruction> DefinitionsOf(MethodAnalysisContext caller, LocalVariable local) =>
        caller.ControlFlowGraph!.Instructions.Where(i => i.Destination is { } d && ReferenceEquals(d, local));

    [Test]
    public void DownCounterCharElementWalkerProjectsManagedAccess()
    {
        var arrayType = _app.SystemTypes.SystemCharType.MakeSzArrayType();
        var caller = NewCaller("DownCounter", arrayType, out var array);
        var p = Local("p", 8);
        var c = Local("c", 9);
        var h = Local("h", 0);
        var t1 = Local("t1", 11);
        var t2 = Local("t2", 18);
        var cond = Local("cond", 27);
        var ret = Local("ret", 0);
        var pBack = Local("pBack", 8); // loop-carried copies have no definition
        var cBack = Local("cBack", 9);

        var instructions = new List<Instruction>
        {
            new(0, OpCode.And, cBack, new ArrayLength(array), new Immediate(0xFFFFFFFFL)),
            new(1, OpCode.Add, pBack, array, new Immediate(32)),
            new(2, OpCode.Move, h, new Immediate(0x7E3779B9)),
            new(-1, OpCode.Move, c, cBack),
            new(-1, OpCode.Move, p, pBack),
            // loop
            new(3, OpCode.Add, pBack, p, new Immediate(2)),
            new(4, OpCode.ShiftLeft, t1, h, new Immediate(5)),
            new(5, OpCode.Add, t2, h, t1),
            new(6, OpCode.Subtract, cBack, c, new Immediate(1)),
            new(7, OpCode.Xor, h, t2, new MemoryOperand(p, null, 0, 0, 2)),
            new(8, OpCode.CheckNotEqual, cond, c, new Immediate(1)),
            new(9, OpCode.ConditionalJump, new Immediate(0), cond),
            new(10, OpCode.Or, ret, h, new Immediate(1)),
            new(11, OpCode.Return, ret),
        };
        instructions[11].SetOperand(0, instructions[3]); // loop back to the phi copies
        caller.Locals.AddRange([p, c, h, t1, t2, cond, ret]);
        caller.ControlFlowGraph = new ISILControlFlowGraph(instructions);

        ArrayRecovery.Run(caller);

        var xor = caller.ControlFlowGraph.Instructions.Single(i => i.OpCode == OpCode.Xor);
        var access = (ArrayAccess)xor.Operands[2];
        Assert.That(ReferenceEquals(access.Array, array), Is.True);

        // index = length - counter, synthesized at the access
        var indexDef = caller.ControlFlowGraph.Instructions
            .Single(i => i.Destination is { } d && ReferenceEquals(d, access.Index));
        Assert.That(indexDef.OpCode, Is.EqualTo(OpCode.Subtract));
        Assert.That(indexDef.Operands[1], Is.TypeOf<ArrayLength>());
        Assert.That(ReferenceEquals(indexDef.Operands[2], c) || ReferenceEquals(indexDef.Operands[2], cBack),
            Is.True, "index must subtract the loop counter");

        AssertNoMemoryOperands(caller);
        Assert.That(DefinitionsOf(caller, p).Select(i => i.OpCode), Is.All.EqualTo(OpCode.Nop));
    }

    [Test]
    public void UpCounterIntElementWalkerProjectsManagedAccess()
    {
        var arrayType = _app.SystemTypes.SystemInt32Type.MakeSzArrayType();
        var caller = NewCaller("UpCounter", arrayType, out var array);
        var p = Local("p", 8);
        var i = Local("i", 9);
        var v = Local("v", 10);
        var cond = Local("cond", 27);
        var ret = Local("ret", 0);

        var instructions = new List<Instruction>
        {
            new(0, OpCode.Move, i, new Immediate(0)),
            new(1, OpCode.Add, p, array, new Immediate(32)),
            // loop
            new(2, OpCode.Move, v, new MemoryOperand(p, null, 0, 0, 4)),
            new(3, OpCode.Add, p, p, new Immediate(4)),
            new(4, OpCode.Add, i, i, new Immediate(1)),
            new(5, OpCode.CheckLess, cond, i, new MemoryOperand(array, null, 24)),
            new(6, OpCode.ConditionalJump, new Immediate(0), cond),
            new(7, OpCode.Return, ret),
        };
        instructions[6].SetOperand(0, instructions[2]); // loop back
        caller.Locals.AddRange([p, i, v, cond, ret]);
        caller.ControlFlowGraph = new ISILControlFlowGraph(instructions);

        ArrayRecovery.Run(caller);

        var load = caller.ControlFlowGraph.Instructions.Single(i => i.OpCode == OpCode.Move && ReferenceEquals(i.Destination, v));
        var access = (ArrayAccess)load.Operands[1];
        Assert.That(ReferenceEquals(access.Array, array), Is.True);
        Assert.That(ReferenceEquals(access.Index, i), Is.True);
        AssertNoMemoryOperands(caller);
    }

    [Test]
    public void ByteElementWalkerProjectsManagedAccess()
    {
        var arrayType = _app.SystemTypes.SystemByteType.MakeSzArrayType();
        var caller = NewCaller("ByteWalker", arrayType, out var array);
        var p = Local("p", 8);
        var c = Local("c", 9);
        var v = Local("v", 10);
        var cond = Local("cond", 27);

        var instructions = new List<Instruction>
        {
            new(0, OpCode.And, c, new ArrayLength(array), new Immediate(0xFFFFFFFFL)),
            new(1, OpCode.Add, p, array, new Immediate(32)),
            // loop
            new(2, OpCode.Move, v, new MemoryOperand(p, null, 0, 0, 1)),
            new(3, OpCode.Add, p, p, new Immediate(1)),
            new(4, OpCode.Subtract, c, c, new Immediate(1)),
            new(5, OpCode.CheckNotEqual, cond, c, new Immediate(0)),
            new(6, OpCode.ConditionalJump, v, cond),
            new(7, OpCode.Return, v),
        };
        instructions[6].SetOperand(0, instructions[2]);
        caller.Locals.AddRange([p, c, v, cond]);
        caller.ControlFlowGraph = new ISILControlFlowGraph(instructions);

        ArrayRecovery.Run(caller);

        var load = caller.ControlFlowGraph.Instructions.Single(i => i.OpCode == OpCode.Move && ReferenceEquals(i.Destination, v));
        Assert.That(load.Operands[1], Is.TypeOf<ArrayAccess>());
        AssertNoMemoryOperands(caller);
    }

    [Test]
    public void ReferenceElementWalkerProjectsManagedAccess()
    {
        var arrayType = _app.SystemTypes.SystemStringType.MakeSzArrayType();
        var caller = NewCaller("ReferenceWalker", arrayType, out var array);
        var p = Local("p", 8);
        var c = Local("c", 9);
        var v = Local("v", 10);
        var cond = Local("cond", 27);

        var instructions = new List<Instruction>
        {
            new(0, OpCode.And, c, new ArrayLength(array), new Immediate(0xFFFFFFFFL)),
            new(1, OpCode.Add, p, array, new Immediate(32)),
            // loop
            new(2, OpCode.Move, v, new MemoryOperand(p, null, 0, 0, 8)),
            new(3, OpCode.Add, p, p, new Immediate(8)),
            new(4, OpCode.Subtract, c, c, new Immediate(1)),
            new(5, OpCode.CheckNotEqual, cond, c, new Immediate(0)),
            new(6, OpCode.ConditionalJump, v, cond),
            new(7, OpCode.Return, v),
        };
        instructions[6].SetOperand(0, instructions[2]);
        caller.Locals.AddRange([p, c, v, cond]);
        caller.ControlFlowGraph = new ISILControlFlowGraph(instructions);

        ArrayRecovery.Run(caller);

        var load = caller.ControlFlowGraph.Instructions.Single(i => i.OpCode == OpCode.Move && ReferenceEquals(i.Destination, v));
        Assert.That(load.Operands[1], Is.TypeOf<ArrayAccess>());
        AssertNoMemoryOperands(caller);
    }

    [Test]
    public void FixedElementPointerProjectsConstantIndex()
    {
        var arrayType = _app.SystemTypes.SystemInt32Type.MakeSzArrayType();
        var caller = NewCaller("FixedPointer", arrayType, out var array);
        var p = Local("p", 8);
        var v0 = Local("v0", 10);
        var v2 = Local("v2", 11);

        caller.Locals.AddRange([p, v0, v2]);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Add, p, array, new Immediate(32)),
            new(1, OpCode.Move, v0, new MemoryOperand(p)),
            new(2, OpCode.Move, v2, new MemoryOperand(p, null, 8)),
            new(3, OpCode.Return, v0),
        ]);

        ArrayRecovery.Run(caller);

        var load0 = caller.ControlFlowGraph.Instructions[1];
        var access0 = (ArrayAccess)load0.Operands[1];
        Assert.That(ReferenceEquals(access0.Array, array), Is.True);
        Assert.That(access0.Index, Is.EqualTo(new Immediate(0)));

        var load2 = caller.ControlFlowGraph.Instructions[2];
        var access2 = (ArrayAccess)load2.Operands[1];
        Assert.That(access2.Index, Is.EqualTo(new Immediate(2)));

        AssertNoMemoryOperands(caller);
    }

    [Test]
    public void ScaledIndexOnElementPointerProjectsManagedAccess()
    {
        var arrayType = _app.SystemTypes.SystemInt32Type.MakeSzArrayType();
        var caller = NewCaller("ScaledIndex", arrayType, out var array);
        var p = Local("p", 8);
        var i = Local("i", 9);
        var v = Local("v", 10);

        caller.Locals.AddRange([p, i, v]);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Add, p, array, new Immediate(32)),
            new(1, OpCode.Move, v, new MemoryOperand(p, i, 0, 4, 4)),
            new(2, OpCode.Return, v),
        ]);

        ArrayRecovery.Run(caller);

        var load = caller.ControlFlowGraph.Instructions[1];
        var access = (ArrayAccess)load.Operands[1];
        Assert.That(ReferenceEquals(access.Array, array), Is.True);
        Assert.That(ReferenceEquals(access.Index, i), Is.True);
        AssertNoMemoryOperands(caller);
    }

    [Test]
    public void ElementPointerStoreProjectsManagedAccess()
    {
        var arrayType = _app.SystemTypes.SystemInt32Type.MakeSzArrayType();
        var caller = NewCaller("ElementStore", arrayType, out var array);
        var p = Local("p", 8);
        var c = Local("c", 9);
        var v = Local("v", 10);
        var cond = Local("cond", 27);

        var instructions = new List<Instruction>
        {
            new(0, OpCode.And, c, new ArrayLength(array), new Immediate(0xFFFFFFFFL)),
            new(1, OpCode.Add, p, array, new Immediate(32)),
            // loop
            new(2, OpCode.Move, new MemoryOperand(p, null, 0, 0, 4), v),
            new(3, OpCode.Add, p, p, new Immediate(4)),
            new(4, OpCode.Subtract, c, c, new Immediate(1)),
            new(5, OpCode.CheckNotEqual, cond, c, new Immediate(0)),
            new(6, OpCode.ConditionalJump, v, cond),
            new(7, OpCode.Return, v),
        };
        instructions[6].SetOperand(0, instructions[2]);
        caller.Locals.AddRange([p, c, v, cond]);
        caller.ControlFlowGraph = new ISILControlFlowGraph(instructions);

        ArrayRecovery.Run(caller);

        var store = caller.ControlFlowGraph.Instructions
            .Single(i => i.OpCode == OpCode.Move && i.Operands[0] is not LocalVariable);
        Assert.That(store.Operands[0], Is.TypeOf<ArrayAccess>());
        AssertNoMemoryOperands(caller);
    }

    [Test]
    public void HeaderOffsetPointerStaysUnresolved()
    {
        var arrayType = _app.SystemTypes.SystemInt32Type.MakeSzArrayType();
        var caller = NewCaller("HeaderOffset", arrayType, out var array);
        var p = Local("p", 8);
        var v = Local("v", 10);

        // pointer seeded into the array header, not at the elements
        caller.Locals.AddRange([p, v]);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Add, p, array, new Immediate(24)),
            new(1, OpCode.Move, v, new MemoryOperand(p)),
            new(2, OpCode.Return, v),
        ]);

        ArrayRecovery.Run(caller);

        var load = caller.ControlFlowGraph.Instructions[1];
        Assert.That(load.Operands[1], Is.TypeOf<MemoryOperand>());
    }

    [Test]
    public void WrongStrideWalkerStaysUnresolved()
    {
        var arrayType = _app.SystemTypes.SystemCharType.MakeSzArrayType();
        var caller = NewCaller("WrongStride", arrayType, out var array);
        var p = Local("p", 8);
        var c = Local("c", 9);
        var v = Local("v", 10);
        var cond = Local("cond", 27);

        var instructions = new List<Instruction>
        {
            new(0, OpCode.And, c, new ArrayLength(array), new Immediate(0xFFFFFFFFL)),
            new(1, OpCode.Add, p, array, new Immediate(32)),
            // loop walks 4 bytes per char - not the element stride
            new(2, OpCode.Move, v, new MemoryOperand(p, null, 0, 0, 2)),
            new(3, OpCode.Add, p, p, new Immediate(4)),
            new(4, OpCode.Subtract, c, c, new Immediate(1)),
            new(5, OpCode.CheckNotEqual, cond, c, new Immediate(0)),
            new(6, OpCode.ConditionalJump, v, cond),
            new(7, OpCode.Return, v),
        };
        instructions[6].SetOperand(0, instructions[2]);
        caller.Locals.AddRange([p, c, v, cond]);
        caller.ControlFlowGraph = new ISILControlFlowGraph(instructions);

        ArrayRecovery.Run(caller);

        var load = caller.ControlFlowGraph.Instructions.Single(i => i.OpCode == OpCode.Move && ReferenceEquals(i.Destination, v));
        Assert.That(load.Operands[1], Is.TypeOf<MemoryOperand>());
    }

    [Test]
    public void AmbiguousRootWalkerStaysUnresolved()
    {
        var arrayType = _app.SystemTypes.SystemInt32Type.MakeSzArrayType();
        var caller = NewCaller("Ambiguous", arrayType, out var array);
        var other = new LocalVariable("other", new Register(1, "X1"), arrayType);
        var p = Local("p", 8);
        var v = Local("v", 10);
        var cond = Local("cond", 27);

        var instructions = new List<Instruction>
        {
            new(0, OpCode.Add, p, array, new Immediate(32)),
            new(1, OpCode.Add, p, other, new Immediate(32)),
            // loop
            new(2, OpCode.Move, v, new MemoryOperand(p, null, 0, 0, 4)),
            new(3, OpCode.Add, p, p, new Immediate(4)),
            new(4, OpCode.CheckNotEqual, cond, v, new Immediate(0)),
            new(5, OpCode.ConditionalJump, v, cond),
            new(6, OpCode.Return, v),
        };
        instructions[5].SetOperand(0, instructions[2]);
        caller.Locals.AddRange([other, p, v, cond]);
        caller.ControlFlowGraph = new ISILControlFlowGraph(instructions);

        ArrayRecovery.Run(caller);

        var load = caller.ControlFlowGraph.Instructions.Single(i => i.OpCode == OpCode.Move && ReferenceEquals(i.Destination, v));
        Assert.That(load.Operands[1], Is.TypeOf<MemoryOperand>());
    }

    [Test]
    public void NonArrayRootWalkerStaysUnresolved()
    {
        var arrayType = _app.SystemTypes.SystemInt32Type.MakeSzArrayType();
        var caller = NewCaller("NonArray", arrayType, out var array);
        var obj = new LocalVariable("obj", new Register(1, "X1"), _app.SystemTypes.SystemObjectType);
        var p = Local("p", 8);
        var v = Local("v", 10);

        caller.Locals.AddRange([obj, p, v]);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Add, p, obj, new Immediate(32)),
            new(1, OpCode.Move, v, new MemoryOperand(p)),
            new(2, OpCode.Return, v),
        ]);

        ArrayRecovery.Run(caller);

        var load = caller.ControlFlowGraph.Instructions[1];
        Assert.That(load.Operands[1], Is.TypeOf<MemoryOperand>());
    }

    [Test]
    public void GenericInstanceFieldThroughBaseChainResolves()
    {
        // An Action<T>-style generic definition inherits non-generic bases that carry
        // the real instance fields - the fields live on the chain, not the definition.
        var assembly = _app.AssembliesByName["UnityEngine.CoreModule"];
        var intPtr = _app.SystemTypes.SystemIntPtrType;
        var int32 = _app.SystemTypes.SystemInt32Type;
        var baseType = new InjectedTypeAnalysisContext(assembly, "System", "DelegateBase",
            _app.SystemTypes.SystemObjectType, R.TypeAttributes.Public);
        var methodPtr = new InjectedFieldAnalysisContext("method_ptr", intPtr,
            R.FieldAttributes.Family, baseType, offset: 0x18);
        baseType.Fields.Add(methodPtr);
        var genericDef = new InjectedTypeAnalysisContext(assembly, "System", "Action`1",
            baseType, R.TypeAttributes.Public);
        var genericInstance = genericDef.MakeGenericInstanceType(int32);

        var field = MetadataResolver.FindInstanceFieldAtOffset(genericInstance, 0x18);

        Assert.That(field, Is.Not.Null);
        Assert.That(field!.Name, Is.EqualTo("method_ptr"));
    }

    [Test]
    public void CharArrayHashFixtureComputesFold()
    {
        var charType = _app.SystemTypes.SystemCharType;
        var arrayType = charType.MakeSzArrayType();
        var caller = NewCaller("HashFixture", arrayType, out var input);
        var p = Local("p", 8);
        var c = Local("c", 9);
        var h = Local("h", 0);
        var t1 = Local("t1", 11);
        var t2 = Local("t2", 18);
        var cond1 = Local("cond1", 27);
        var cond2 = Local("cond2", 28);
        var cond3 = Local("cond3", 29);
        var ret = Local("ret", 0);
        var pBack = Local("pBack", 8);
        var cBack = Local("cBack", 9);
        const long seed = 0x7E3779B9;

        var placeholder = new Immediate(0);
        var instructions = new List<Instruction>
        {
            // if (input == null || input.Length < 1) goto earlyExit
            new(0, OpCode.CheckEqual, cond1, input, new Immediate(0)),
            new(1, OpCode.ConditionalJump, placeholder, cond1),
            new(2, OpCode.CheckLess, cond2, new MemoryOperand(input, null, 24), new Immediate(1)),
            new(3, OpCode.ConditionalJump, placeholder, cond2),
            // h = seed; cBack = len; pBack = &elements (back-edge locals hold seeds)
            new(4, OpCode.And, cBack, new MemoryOperand(input, null, 24), new Immediate(0xFFFFFFFFL)),
            new(5, OpCode.Add, pBack, input, new Immediate(32)),
            new(6, OpCode.Move, h, new Immediate(seed)),
            new(-1, OpCode.Move, c, cBack),
            new(-1, OpCode.Move, p, pBack),
            // loop: h = h*33 ^ *p; p += 2; while (--c != 0)
            new(7, OpCode.ShiftLeft, t1, h, new Immediate(5)),
            new(8, OpCode.Add, t2, h, t1),
            new(9, OpCode.Xor, h, t2, new MemoryOperand(p, null, 0, 0, 2)),
            new(10, OpCode.Add, pBack, p, new Immediate(2)),
            new(11, OpCode.Subtract, cBack, c, new Immediate(1)),
            new(12, OpCode.CheckNotEqual, cond3, cBack, new Immediate(0)),
            new(13, OpCode.ConditionalJump, placeholder, cond3),
            new(14, OpCode.Jump, placeholder), // skip early-exit block
            // earlyExit
            new(15, OpCode.Move, h, new Immediate(seed)),
            // merge
            new(16, OpCode.Or, ret, h, new Immediate(1)),
            new(17, OpCode.Return, ret),
        };
        instructions[1].SetOperand(0, instructions[17]);   // null -> earlyExit
        instructions[3].SetOperand(0, instructions[17]);   // len < 1 -> earlyExit
        instructions[15].SetOperand(0, instructions[7]);   // loop back to the phi copies
        instructions[16].SetOperand(0, instructions[18]);  // skip early-exit to merge
        caller.Locals.AddRange([p, c, h, t1, t2, cond1, cond2, cond3, ret]);
        caller.ControlFlowGraph = new ISILControlFlowGraph(instructions);

        ArrayRecovery.Run(caller);

        AssertNoMemoryOperands(caller);

        var module = new ModuleDefinition("ManagedMemoryRecoveryTests.dll");
        var assembly = new AssemblyDefinition("ManagedMemoryRecoveryTests", new Version(1, 0, 0, 0));
        foreach (var primitive in new[]
        {
            _app.SystemTypes.SystemObjectType, _app.SystemTypes.SystemCharType,
            _app.SystemTypes.SystemInt32Type, _app.SystemTypes.SystemBooleanType,
            _app.SystemTypes.SystemVoidType
        })
            primitive.PutExtraData("AsmResolverType",
                new TypeDefinition("System", primitive.Name, TypeAttributes.Public));
        var type = new TypeDefinition("ManagedMemoryRecoveryTests", "HashUtil",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        assembly.Modules.Add(module);
        var methodDefinition = new MethodDefinition("Hash",
            MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Int32,
                [module.CorLibTypeFactory.Char.MakeSzArrayType()]));
        type.Methods.Add(methodDefinition);
        methodDefinition.ParameterDefinitions.Add(new ParameterDefinition(1, "input", 0));
        caller.PutExtraData("AsmResolverMethod", methodDefinition);

        IlGenerator.GenerateIl(caller, methodDefinition);

        // Rebind primitive locals to real corlib signatures so the emitted assembly
        // references the runtime's own Char/Int32 rather than placeholder defs.
        var ilLocals = methodDefinition.CilMethodBody!.LocalVariables;
        foreach (var ilLocal in ilLocals)
        {
            ilLocal.VariableType = ilLocal.VariableType?.FullName switch
            {
                "System.Char[]" => module.CorLibTypeFactory.Char.MakeSzArrayType(),
                "System.Char" => module.CorLibTypeFactory.Char,
                "System.Int32" => module.CorLibTypeFactory.Int32,
                "System.Boolean" => module.CorLibTypeFactory.Boolean,
                _ => ilLocal.VariableType,
            };
        }

        Assert.That(methodDefinition.CilMethodBody!.Instructions
                .Any(i => i.OpCode == CilOpCodes.Ldelem_U2), Is.True, "expected a char element load");

        using var stream = new MemoryStream();
        module.Write(stream);
        var loaded = R.Assembly.Load(stream.ToArray());
        var hash = loaded.GetType("ManagedMemoryRecoveryTests.HashUtil")!.GetMethod("Hash")!;

        foreach (var value in new[] { "", "abc", "héllo π€\U0001F600" })
        {
            var expected = (int)seed;
            foreach (var ch in value)
                expected = (expected + (expected << 5)) ^ ch;
            expected |= 1;
            Assert.That(hash.Invoke(null, [value.ToCharArray()]), Is.EqualTo(expected),
                $"hash mismatch for \"{value}\"");
        }
    }
}
