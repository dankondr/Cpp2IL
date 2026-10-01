using System;
using System.Linq;
using System.Reflection;
using System.Threading;
using System.Threading.Tasks;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class InlinedMemberRecoveryTests
{
    private static ApplicationAnalysisContext App => Cpp2IlApi.CurrentAppContext!;
    private static AssemblyAnalysisContext Mscorlib => App.AssembliesByName["mscorlib"];
    private static AssemblyAnalysisContext OtherAssembly => App.AssembliesByName["System.Core"];

    private static LocalVariable Local(string name, TypeAnalysisContext? type = null) =>
        new(name, new Register(null, name), type);

    private static InjectedMethodAnalysisContext CallerIn(AssemblyAnalysisContext assembly) =>
        new(new InjectedTypeAnalysisContext(assembly, "Tests", "Caller",
                App.SystemTypes.SystemObjectType, TypeAttributes.Public),
            "Call", App.SystemTypes.SystemVoidType, MethodAttributes.Static, []);

    private static InjectedTypeAnalysisContext InjectedStruct(string name) =>
        new(Mscorlib, "Tests", name, App.SystemTypes.SystemValueTypeType, TypeAttributes.Public);

    private static InjectedFieldAnalysisContext Field(InjectedTypeAnalysisContext owner,
        string name, TypeAnalysisContext type, FieldAttributes attributes) =>
        new(name, type, attributes, owner, 0);

    private static InjectedMethodAnalysisContext Member(InjectedTypeAnalysisContext owner,
        string name, TypeAnalysisContext returnType, MethodAttributes attributes,
        params TypeAnalysisContext[] parameters) =>
        new(owner, name, returnType, attributes, parameters);

    private static void GiveBody(InjectedMethodAnalysisContext method, LocalVariable thisLocal,
        LocalVariable[] parameters, params Instruction[] instructions)
    {
        thisLocal.IsThis = true;
        method.ParameterLocals = [thisLocal, ..parameters];
        method.ControlFlowGraph = new ISILControlFlowGraph(instructions.ToList());
    }

    private static void GiveBody(InjectedMethodAnalysisContext method,
        params Instruction[] instructions) =>
        method.ControlFlowGraph = new ISILControlFlowGraph(instructions.ToList());

    // A read-only struct filled field by field through a return buffer maps to the
    // constructor whose body assigns those fields from its parameters.
    [Test]
    public void ReturnBufferStructFillCallsConstructor()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();

        var record = InjectedStruct("Record");
        var f1 = Field(record, "a", App.SystemTypes.SystemInt32Type, FieldAttributes.Private);
        var f2 = Field(record, "b", App.SystemTypes.SystemInt32Type, FieldAttributes.Private);
        record.Fields.Add(f1);
        record.Fields.Add(f2);

        var ctor = Member(record, ".ctor", App.SystemTypes.SystemVoidType,
            MethodAttributes.Public, App.SystemTypes.SystemInt32Type,
            App.SystemTypes.SystemInt32Type);
        record.Methods.Add(ctor);
        var ctorThis = Local("this", record);
        var ctorP0 = Local("p0", App.SystemTypes.SystemInt32Type);
        var ctorP1 = Local("p1", App.SystemTypes.SystemInt32Type);
        GiveBody(ctor, ctorThis, [ctorP0, ctorP1],
            new Instruction(0, OpCode.Move, new FieldReference(f1, ctorThis, 0), ctorP0),
            new Instruction(1, OpCode.Move, new FieldReference(f2, ctorThis, 0), ctorP1),
            new Instruction(2, OpCode.Return));

        var caller = CallerIn(OtherAssembly);
        var buffer = Local("returnBuffer", record);
        var v0 = Local("v0", App.SystemTypes.SystemInt32Type);
        var v1 = Local("v1", App.SystemTypes.SystemInt32Type);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, new FieldReference(f1, buffer, 0), v0),
            new Instruction(1, OpCode.Move, new FieldReference(f2, buffer, 0), v1),
            new Instruction(2, OpCode.Return),
        ]);

        InlinedMemberRecovery.Run(caller);

        var block = caller.ControlFlowGraph.Blocks.First(b => b.Instructions.Count > 0);
        var call = block.Instructions.FirstOrDefault(i => i.OpCode == OpCode.CallVoid);
        Assert.Multiple(() =>
        {
            Assert.That(call, Is.Not.Null);
            Assert.That(call!.Operands[0], Is.SameAs((IOperand)ctor));
            Assert.That(call.Operands[1], Is.SameAs((IOperand)buffer));
            Assert.That(call.Operands[2], Is.SameAs((IOperand)v0));
            Assert.That(call.Operands[3], Is.SameAs((IOperand)v1));
            Assert.That(block.Instructions.Count(i => i.OpCode == OpCode.Move), Is.Zero);
        });
    }

    // An awaiter built from a task through a private field maps to the producer
    // whose body fills exactly that field from `this` - `task.GetAwaiter()`.
    [Test]
    public void AwaiterFieldStoreCallsProducer()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();

        var task = InjectedStruct("Task");
        var awaiter = InjectedStruct("Awaiter");
        var taskField = Field(awaiter, "task", task, FieldAttributes.Private);
        awaiter.Fields.Add(taskField);

        var getAwaiter = Member(task, "GetAwaiter", awaiter,
            MethodAttributes.Public);
        task.Methods.Add(getAwaiter);
        var producerThis = Local("this", task);
        var produced = Local("produced", awaiter);
        GiveBody(getAwaiter, producerThis, [],
            new Instruction(0, OpCode.Move, new FieldReference(taskField, produced, 0),
                producerThis),
            new Instruction(1, OpCode.Return, produced));

        var caller = CallerIn(OtherAssembly);
        var taskLocal = Local("task", task);
        var awaiterLocal = Local("awaiter", awaiter);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, new FieldReference(taskField, awaiterLocal, 0),
                taskLocal),
            new Instruction(1, OpCode.Return),
        ]);

        InlinedMemberRecovery.Run(caller);

        var block = caller.ControlFlowGraph.Blocks.First(b => b.Instructions.Count > 0);
        var call = block.Instructions.FirstOrDefault(i => i.OpCode == OpCode.Call);
        Assert.Multiple(() =>
        {
            Assert.That(call, Is.Not.Null);
            Assert.That(call!.Operands[0], Is.SameAs((IOperand)getAwaiter));
            Assert.That(call.Operands[1], Is.TypeOf<LocalVariable>());
            // The task is the receiver - a struct, so passed by address.
            Assert.That(call.Operands[2], Is.TypeOf<AddressOf>());
            Assert.That(((AddressOf)call.Operands[2]).Target, Is.SameAs((IOperand)taskLocal));
            var move = block.Instructions.FirstOrDefault(i => i.OpCode == OpCode.Move);
            Assert.That(move, Is.Not.Null);
            Assert.That(move!.Operands[0], Is.SameAs((IOperand)awaiterLocal));
            Assert.That(move.Operands[1], Is.SameAs(call.Operands[1]));
        });
    }

    // A store into a private field maps to the accessible setter whose body is
    // exactly that store.
    [Test]
    public void PrivateFieldStoreCallsSetter()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();

        var owner = new InjectedTypeAnalysisContext(Mscorlib, "Tests", "Box",
            App.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var hidden = Field(owner, "hidden", App.SystemTypes.SystemInt32Type,
            FieldAttributes.Private);
        owner.Fields.Add(hidden);

        var setter = Member(owner, "set_Value", App.SystemTypes.SystemVoidType,
            MethodAttributes.Public, App.SystemTypes.SystemInt32Type);
        owner.Methods.Add(setter);
        var setterThis = Local("this", owner);
        var setterParam = Local("value", App.SystemTypes.SystemInt32Type);
        GiveBody(setter, setterThis, [setterParam],
            new Instruction(0, OpCode.Move, new FieldReference(hidden, setterThis, 0),
                setterParam),
            new Instruction(1, OpCode.Return));

        var caller = CallerIn(OtherAssembly);
        var obj = Local("obj", owner);
        var value = Local("value", App.SystemTypes.SystemInt32Type);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, new FieldReference(hidden, obj, 0), value),
            new Instruction(1, OpCode.Return),
        ]);

        InlinedMemberRecovery.Run(caller);

        var block = caller.ControlFlowGraph.Blocks.First(b => b.Instructions.Count > 0);
        var call = block.Instructions.FirstOrDefault(i => i.OpCode == OpCode.CallVoid);
        Assert.Multiple(() =>
        {
            Assert.That(call, Is.Not.Null);
            Assert.That(call!.Operands[0], Is.SameAs((IOperand)setter));
            Assert.That(call.Operands[1], Is.SameAs((IOperand)obj));
            Assert.That(call.Operands[2], Is.SameAs((IOperand)value));
            Assert.That(block.Instructions.Count(i => i.OpCode == OpCode.Move), Is.Zero);
        });
    }

    // A read of a private static readonly field maps to the accessible static
    // getter whose body returns it - the Vector2.zero shape.
    [Test]
    public void PrivateStaticFieldReadCallsGetter()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();

        var vector = InjectedStruct("Vec");
        var hidden = Field(vector, "hidden", App.SystemTypes.SystemInt32Type,
            FieldAttributes.Private | FieldAttributes.Static);
        vector.Fields.Add(hidden);

        var getter = Member(vector, "get_P", App.SystemTypes.SystemInt32Type,
            MethodAttributes.Public | MethodAttributes.Static);
        vector.Methods.Add(getter);
        var getterStatics = Local("statics",
            new StaticFieldStorageTypeAnalysisContext(vector, Mscorlib));
        var getterResult = Local("result", App.SystemTypes.SystemInt32Type);
        GiveBody(getter,
            new Instruction(0, OpCode.Move, getterResult,
                new FieldReference(hidden, getterStatics, 0)),
            new Instruction(1, OpCode.Return, getterResult));

        var caller = CallerIn(OtherAssembly);
        var statics = Local("statics",
            new StaticFieldStorageTypeAnalysisContext(vector, Mscorlib));
        var destination = Local("d", App.SystemTypes.SystemInt32Type);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, destination,
                new FieldReference(hidden, statics, 0)),
            new Instruction(1, OpCode.Return),
        ]);

        InlinedMemberRecovery.Run(caller);

        var block = caller.ControlFlowGraph.Blocks.First(b => b.Instructions.Count > 0);
        var call = block.Instructions.FirstOrDefault(i => i.OpCode == OpCode.Call);
        Assert.Multiple(() =>
        {
            Assert.That(call, Is.Not.Null);
            Assert.That(call!.Operands[0], Is.SameAs((IOperand)getter));
            var move = block.Instructions.First(i => i.OpCode == OpCode.Move);
            Assert.That(move.Operands[0], Is.SameAs((IOperand)destination));
            Assert.That(move.Operands[1], Is.SameAs(call.Operands[1]));
        });
    }

    // A struct getter assembles its result lane-wise into the return
    // aggregate (`ret.x <- tmp.x`, `ret.y <- statics.sf.y`) - the real
    // `Vector2.zero` codegen shape. Reads of the whole field and of single
    // lanes both map to the accessible getter.
    [Test]
    public void PerLaneStructReturnCallsGetter()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();

        var vector = InjectedStruct("Vec");
        var fx = Field(vector, "x", App.SystemTypes.SystemInt32Type, FieldAttributes.Public);
        var fy = Field(vector, "y", App.SystemTypes.SystemInt32Type, FieldAttributes.Public);
        var hidden = Field(vector, "hidden", vector,
            FieldAttributes.Private | FieldAttributes.Static);
        vector.Fields.Add(fx);
        vector.Fields.Add(fy);
        vector.Fields.Add(hidden);

        var getter = Member(vector, "get_P", vector,
            MethodAttributes.Public | MethodAttributes.Static);
        vector.Methods.Add(getter);
        var getterStatics = Local("statics",
            new StaticFieldStorageTypeAnalysisContext(vector, Mscorlib));
        var tmp = Local("tmp", vector);
        var result = Local("result", vector);
        GiveBody(getter,
            new Instruction(0, OpCode.Move, tmp,
                new FieldReference(hidden, getterStatics, 0)),
            new Instruction(1, OpCode.Move, new FieldReference(fx, result, 0),
                new FieldReference(fx, tmp, 0)),
            new Instruction(2, OpCode.Move, new FieldReference(fy, result, 0),
                new FieldReference(fy, getterStatics, 0, [hidden])),
            new Instruction(3, OpCode.Return, result));

        var caller = CallerIn(OtherAssembly);
        var statics = Local("statics",
            new StaticFieldStorageTypeAnalysisContext(vector, Mscorlib));
        var whole = Local("d", vector);
        var lane = Local("e", vector);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, whole,
                new FieldReference(hidden, statics, 0)),
            new Instruction(1, OpCode.Move, new FieldReference(fy, lane, 0),
                new FieldReference(fy, statics, 0, [hidden])),
            new Instruction(2, OpCode.Return),
        ]);

        InlinedMemberRecovery.Run(caller);

        var block = caller.ControlFlowGraph.Blocks.First(b => b.Instructions.Count > 0);
        var calls = block.Instructions.Where(i => i.OpCode == OpCode.Call).ToList();
        Assert.Multiple(() =>
        {
            Assert.That(calls, Has.Count.EqualTo(1));
            Assert.That(calls[0].Operands[0], Is.SameAs((IOperand)getter));
            var produced = calls[0].Operands[1];
            var wholeMove = block.Instructions.First(i => i.OpCode == OpCode.Move
                && i.Operands[0] == whole);
            Assert.That(wholeMove.Operands[1], Is.SameAs(produced));
            var laneSource = block.Instructions
                .SelectMany(i => i.Operands).OfType<FieldReference>()
                .FirstOrDefault(f => f.Containers.Count == 0
                    && ReferenceEquals(f.Local, produced));
            Assert.That(laneSource, Is.Not.Null);
            Assert.That(laneSource!.Field, Is.SameAs((FieldAnalysisContext)fy));
            Assert.That(block.Instructions.SelectMany(i => i.Operands)
                .OfType<FieldReference>().Count(f => ReferenceEquals(f.Local, statics)),
                Is.Zero);
        });
    }

    // Consecutive stores into different fields of the same object are
    // separate accesses: each maps to its own accessible setter.
    [Test]
    public void PerLeafStoresCallSeparateSetters()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();

        var owner = new InjectedTypeAnalysisContext(Mscorlib, "Tests", "Pair",
            App.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var fx = Field(owner, "x", App.SystemTypes.SystemInt32Type, FieldAttributes.Private);
        var fy = Field(owner, "y", App.SystemTypes.SystemInt32Type, FieldAttributes.Private);
        owner.Fields.Add(fx);
        owner.Fields.Add(fy);

        var setX = Member(owner, "set_X", App.SystemTypes.SystemVoidType,
            MethodAttributes.Public, App.SystemTypes.SystemInt32Type);
        var setY = Member(owner, "set_Y", App.SystemTypes.SystemVoidType,
            MethodAttributes.Public, App.SystemTypes.SystemInt32Type);
        owner.Methods.Add(setX);
        owner.Methods.Add(setY);
        foreach (var (setter, field) in new[] { (setX, fx), (setY, fy) })
        {
            var thisL = Local("this", owner);
            var param = Local("value", App.SystemTypes.SystemInt32Type);
            GiveBody(setter, thisL, [param],
                new Instruction(0, OpCode.Move, new FieldReference(field, thisL, 0), param),
                new Instruction(1, OpCode.Return));
        }

        var caller = CallerIn(OtherAssembly);
        var obj = Local("obj", owner);
        var a = Local("a", App.SystemTypes.SystemInt32Type);
        var b = Local("b", App.SystemTypes.SystemInt32Type);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, new FieldReference(fx, obj, 0), a),
            new Instruction(1, OpCode.Move, new FieldReference(fy, obj, 0), b),
            new Instruction(2, OpCode.Return),
        ]);

        InlinedMemberRecovery.Run(caller);

        var block = caller.ControlFlowGraph.Blocks.First(b => b.Instructions.Count > 0);
        var calls = block.Instructions.Where(i => i.OpCode == OpCode.CallVoid).ToList();
        Assert.Multiple(() =>
        {
            Assert.That(calls, Has.Count.EqualTo(2));
            Assert.That(calls[0].Operands[0], Is.SameAs((IOperand)setX));
            Assert.That(calls[0].Operands[1], Is.SameAs((IOperand)obj));
            Assert.That(calls[0].Operands[2], Is.SameAs((IOperand)a));
            Assert.That(calls[1].Operands[0], Is.SameAs((IOperand)setY));
            Assert.That(calls[1].Operands[2], Is.SameAs((IOperand)b));
            Assert.That(block.Instructions.Count(i => i.OpCode == OpCode.Move), Is.Zero);
        });
    }

    // Stores through a byref return buffer name the element type's members.
    [Test]
    public void ByRefBufferStoreStaysDiagnosed()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();

        var record = InjectedStruct("Record");
        var f1 = Field(record, "a", App.SystemTypes.SystemInt32Type, FieldAttributes.Private);
        record.Fields.Add(f1);

        var setter = Member(record, "set_A", App.SystemTypes.SystemVoidType,
            MethodAttributes.Public, App.SystemTypes.SystemInt32Type);
        record.Methods.Add(setter);
        var setterThis = Local("this", record);
        var setterParam = Local("value", App.SystemTypes.SystemInt32Type);
        GiveBody(setter, setterThis, [setterParam],
            new Instruction(0, OpCode.Move, new FieldReference(f1, setterThis, 0), setterParam),
            new Instruction(1, OpCode.Return));

        var caller = CallerIn(OtherAssembly);
        var buffer = Local("returnBuffer", record.MakeByReferenceType());
        var v0 = Local("v0", App.SystemTypes.SystemInt32Type);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, new FieldReference(f1, buffer, 0), v0),
            new Instruction(1, OpCode.Return),
        ]);

        InlinedMemberRecovery.Run(caller);

        var block = caller.ControlFlowGraph.Blocks.First(b => b.Instructions.Count > 0);
        // A member call on the buffer would need `ldloc` on the `T&` slot as
        // the `&T` receiver - emission cannot spell it, so the store stays.
        Assert.Multiple(() =>
        {
            Assert.That(block.Instructions.FirstOrDefault(i => i.OpCode == OpCode.CallVoid),
                Is.Null);
            Assert.That(block.Instructions.Count(i => i.OpCode == OpCode.Move
                && i.Operands[0] is FieldReference), Is.EqualTo(1));
        });
    }

    // Two accessible members with the same produced shape cannot be told apart -
    // the access stays a field store.
    [Test]
    public void AmbiguousMembersKeepTheDiagnosedAccess()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();

        var owner = new InjectedTypeAnalysisContext(Mscorlib, "Tests", "Pair",
            App.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var hidden = Field(owner, "hidden", App.SystemTypes.SystemInt32Type,
            FieldAttributes.Private);
        owner.Fields.Add(hidden);

        foreach (var name in new[] { "set_A", "set_B" })
        {
            var setter = Member(owner, name, App.SystemTypes.SystemVoidType,
                MethodAttributes.Public, App.SystemTypes.SystemInt32Type);
            owner.Methods.Add(setter);
            var thisL = Local("this", owner);
            var param = Local("p", App.SystemTypes.SystemInt32Type);
            GiveBody(setter, thisL, [param],
                new Instruction(0, OpCode.Move, new FieldReference(hidden, thisL, 0), param),
                new Instruction(1, OpCode.Return));
        }

        var caller = CallerIn(OtherAssembly);
        var obj = Local("obj", owner);
        var value = Local("value", App.SystemTypes.SystemInt32Type);
        var store = new Instruction(0, OpCode.Move, new FieldReference(hidden, obj, 0), value);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            store,
            new Instruction(1, OpCode.Return),
        ]);

        InlinedMemberRecovery.Run(caller);

        var block = caller.ControlFlowGraph.Blocks.First(b => b.Instructions.Count > 0);
        Assert.Multiple(() =>
        {
            Assert.That(store.OpCode, Is.EqualTo(OpCode.Move));
            Assert.That(block.Instructions.Any(i => i.OpCode is OpCode.Call or OpCode.CallVoid),
                Is.False);
        });
    }

    // A member force-lifted for a summary runs the pipeline with this pass
    // suppressed, so a forced body can never itself force another - two
    // workers then never wait on each other. The body's own Analyze() runs
    // the pass once.
    [Test]
    public void ForcedBodyRunsMemberRecoveryOnItsOwnAnalyze()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();

        var owner = new InjectedTypeAnalysisContext(Mscorlib, "Tests", "Box",
            App.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var hidden = Field(owner, "hidden", App.SystemTypes.SystemInt32Type,
            FieldAttributes.Private);
        owner.Fields.Add(hidden);

        var setter = Member(owner, "set_Value", App.SystemTypes.SystemVoidType,
            MethodAttributes.Public, App.SystemTypes.SystemInt32Type);
        owner.Methods.Add(setter);
        var setterThis = Local("this", owner);
        var setterParam = Local("value", App.SystemTypes.SystemInt32Type);
        GiveBody(setter, setterThis, [setterParam],
            new Instruction(0, OpCode.Move, new FieldReference(hidden, setterThis, 0),
                setterParam),
            new Instruction(1, OpCode.Return));

        var carrier = new InjectedTypeAnalysisContext(OtherAssembly, "Tests", "Carrier",
            App.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var forced = Member(carrier, "Write", App.SystemTypes.SystemVoidType,
            MethodAttributes.Public, App.SystemTypes.SystemInt32Type);
        carrier.Methods.Add(forced);
        var forcedThis = Local("this", carrier);
        var obj = Local("obj", owner);
        var value = Local("value", App.SystemTypes.SystemInt32Type);
        GiveBody(forced, forcedThis, [value],
            new Instruction(0, OpCode.Move, new FieldReference(hidden, obj, 0), value),
            new Instruction(1, OpCode.Return));

        // The summary-forced lift does not run this pass on the body's own
        // diagnosed store.
        forced.AnalyzeForMemberSummary();
        var block = forced.ControlFlowGraph.Blocks.First(b => b.Instructions.Count > 0);
        Assert.That(block.Instructions.FirstOrDefault(i => i.OpCode == OpCode.CallVoid),
            Is.Null);

        forced.Analyze();
        var call = block.Instructions.FirstOrDefault(i => i.OpCode == OpCode.CallVoid);
        Assert.Multiple(() =>
        {
            Assert.That(call, Is.Not.Null);
            Assert.That(call!.Operands[0], Is.SameAs((IOperand)setter));
            Assert.That(call.Operands[1], Is.SameAs((IOperand)obj));
            Assert.That(call.Operands[2], Is.SameAs((IOperand)value));
        });
        forced.Analyze(); // pending consumed: a second Analyze does not re-run
        Assert.That(block.Instructions.Count(i => i.OpCode == OpCode.CallVoid),
            Is.EqualTo(1));
    }

    // A body another worker holds the method monitor on cannot be read yet:
    // the ask waits that lift out - a body still inside AnalyzeCore never runs
    // this pass, so the wait cannot cycle - then recovers once the body lands.
    [Test]
    public void InFlightMemberWaitsForBodyThenRecovers()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();

        var owner = new InjectedTypeAnalysisContext(Mscorlib, "Tests", "Box",
            App.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var hidden = Field(owner, "hidden", App.SystemTypes.SystemInt32Type,
            FieldAttributes.Private);
        owner.Fields.Add(hidden);

        var setter = Member(owner, "set_Value", App.SystemTypes.SystemVoidType,
            MethodAttributes.Public, App.SystemTypes.SystemInt32Type);
        owner.Methods.Add(setter);
        var setterThis = Local("this", owner);
        var setterParam = Local("value", App.SystemTypes.SystemInt32Type);
        GiveBody(setter, setterThis, [setterParam],
            new Instruction(0, OpCode.Move, new FieldReference(hidden, setterThis, 0),
                setterParam),
            new Instruction(1, OpCode.Return));

        var caller = CallerIn(OtherAssembly);
        var obj = Local("obj", owner);
        var value = Local("value", App.SystemTypes.SystemInt32Type);
        var store = new Instruction(0, OpCode.Move,
            new FieldReference(hidden, obj, 0), value);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            store,
            new Instruction(1, OpCode.Return),
        ]);

        // The member's monitor stands in for a parallel worker mid-analysis:
        // the ask waits for it instead of settling for a diagnosis.
        Monitor.Enter(setter);
        Task<int> task;
        try
        {
            task = Task.Run(() => InlinedMemberRecovery.Run(caller));
            Assert.That(task.Wait(TimeSpan.FromMilliseconds(500)), Is.False,
                "the pass finished while the member body was still in flight");
        }
        finally
        {
            Monitor.Exit(setter);
        }
        Assert.That(task.Wait(TimeSpan.FromSeconds(30)), Is.True);

        var block = caller.ControlFlowGraph.Blocks.First(b => b.Instructions.Count > 0);
        var call = block.Instructions.FirstOrDefault(i => i.OpCode == OpCode.CallVoid);
        Assert.Multiple(() =>
        {
            Assert.That(call, Is.Not.Null);
            Assert.That(call!.Operands[0], Is.SameAs((IOperand)setter));
        });
    }

    // `result = <statics>.field; return result` - a static getter's body.
    private static ISILControlFlowGraph ReturnsStatic(TypeAnalysisContext holder,
        FieldAnalysisContext field, AssemblyAnalysisContext assembly)
    {
        var statics = Local("statics", new StaticFieldStorageTypeAnalysisContext(holder, assembly));
        var result = Local("result", field.FieldType);
        return new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, result, new FieldReference(field, statics, 0)),
            new Instruction(1, OpCode.Return, result),
        ]);
    }

    private static Block Body(MethodAnalysisContext method) =>
        method.ControlFlowGraph!.Blocks.First(b => b.Instructions.Count > 0);

    // A getter's own read of its static is not an inlined copy of itself:
    // rewriting it would make the getter call itself forever.
    [Test]
    public void StaticGetterKeepsItsOwnRead()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();

        var holder = InjectedStruct("Counter");
        var count = Field(holder, "count", App.SystemTypes.SystemInt32Type,
            FieldAttributes.Private | FieldAttributes.Static);
        var getter = Member(holder, "Read", App.SystemTypes.SystemInt32Type,
            MethodAttributes.Public | MethodAttributes.Static);
        holder.Methods.Add(getter);
        getter.ControlFlowGraph = ReturnsStatic(holder, count, Mscorlib);

        InlinedMemberRecovery.Run(getter);

        var read = Body(getter).Instructions.First(i => i.OpCode == OpCode.Move).Operands[1];
        Assert.Multiple(() =>
        {
            Assert.That(Body(getter).Instructions.Any(i => i.OpCode == OpCode.Call), Is.False);
            Assert.That(read, Is.TypeOf<FieldReference>());
            Assert.That(((FieldReference)read).Field, Is.SameAs((FieldAnalysisContext)count));
        });
    }

    // A static the caller can name - here a private one of its own assembly,
    // the `count++` beside `Read() => count` shape - is read directly, not
    // through the holder's getter.
    [Test]
    public void AccessibleStaticReadStaysDirect()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();

        var holder = InjectedStruct("Counter");
        var count = Field(holder, "count", App.SystemTypes.SystemInt32Type,
            FieldAttributes.Private | FieldAttributes.Static);
        var getter = Member(holder, "Read", App.SystemTypes.SystemInt32Type,
            MethodAttributes.Public | MethodAttributes.Static);
        holder.Methods.Add(getter);
        getter.ControlFlowGraph = ReturnsStatic(holder, count, Mscorlib);

        var caller = CallerIn(Mscorlib);
        var statics = Local("statics", new StaticFieldStorageTypeAnalysisContext(holder, Mscorlib));
        var destination = Local("d", App.SystemTypes.SystemInt32Type);
        var read = new FieldReference(count, statics, 0);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, destination, read),
            new Instruction(1, OpCode.Return),
        ]);

        InlinedMemberRecovery.Run(caller);

        Assert.Multiple(() =>
        {
            Assert.That(Body(caller).Instructions.Any(i => i.OpCode == OpCode.Call), Is.False);
            Assert.That(Body(caller).Instructions.First(i => i.OpCode == OpCode.Move).Operands[1],
                Is.SameAs((IOperand)read));
        });
    }

    // Two instantiations of one generic holder keep separate statics: each
    // read calls its own instantiation's getter and never reuses the other's
    // result.
    [Test]
    public void GenericHolderInstantiationsCallTheirOwnGetter()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();

        // A concrete instantiation's getter only has a body through the
        // binary's variants, so the holder is a real generic type whose
        // variants get the synthetic `return hidden` body.
        var holder = Mscorlib.GetTypeByFullName("System.Collections.Generic.EqualityComparer`1")!;
        var hidden = new InjectedFieldAnalysisContext("hidden", App.SystemTypes.SystemInt32Type,
            FieldAttributes.Private | FieldAttributes.Static, holder);
        var getter = holder.Methods.Single(m => m.Name == "get_Default");
        var variants = App.ConcreteGenericMethodsByRef.Values
            .Where(v => v.BaseMethodContext == getter && v.UnderlyingPointer != 0).ToList();
        Assert.That(variants, Is.Not.Empty);
        foreach (var variant in variants)
            variant.ControlFlowGraph = ReturnsStatic(holder, hidden, Mscorlib);

        var ofInt = holder.MakeGenericInstanceType(App.SystemTypes.SystemInt32Type);
        var ofString = holder.MakeGenericInstanceType(App.SystemTypes.SystemStringType);
        var caller = CallerIn(OtherAssembly);
        var a = Local("a", App.SystemTypes.SystemInt32Type);
        var b = Local("b", App.SystemTypes.SystemInt32Type);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, a, new FieldReference(hidden,
                Local("s1", new StaticFieldStorageTypeAnalysisContext(ofInt, Mscorlib)), 0)),
            new Instruction(1, OpCode.Move, b, new FieldReference(hidden,
                Local("s2", new StaticFieldStorageTypeAnalysisContext(ofString, Mscorlib)), 0)),
            new Instruction(2, OpCode.Return),
        ]);

        InlinedMemberRecovery.Run(caller);

        var instructions = Body(caller).Instructions;
        var calls = instructions.Where(i => i.OpCode == OpCode.Call).ToList();
        IOperand SourceOf(LocalVariable destination) => instructions
            .First(i => i.OpCode == OpCode.Move && i.Operands[0] == destination).Operands[1];
        Assert.That(calls, Has.Count.EqualTo(2));
        Assert.Multiple(() =>
        {
            Assert.That(calls.Select(c => ((MethodAnalysisContext)c.Operands[0]).DeclaringType!.FullName),
                Is.EqualTo(new[] { ofInt.FullName, ofString.FullName }));
            Assert.That(SourceOf(a), Is.SameAs(calls[0].Operands[1]));
            Assert.That(SourceOf(b), Is.SameAs(calls[1].Operands[1]));
        });
    }
}
