using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.Utils.AsmResolver;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: ISIL→IL emission — the "erased object → shared T" coercion
// shape. IL2CPP shared generics marshal `!T` arguments through locals the
// lifter typed as object (or the fully-shared placeholder). When a callee's
// generic-parameter contract proves the marshaled content and every producer
// is marshaled-`!T` content (an undisturbed move chain, a frame cell, or a
// call whose return declares the same `!T`), the erased local is retyped to
// `!T` and the argument emits cleanly. When the producer cannot prove `!T`
// (e.g. a call returning object), the site keeps its named diagnostic.
public class ErasedObjectSharedGenericTests
{
    private static (MethodAnalysisContext caller, MethodDefinition method,
        GenericParameterTypeAnalysisContext typeArgument, InjectedTypeAnalysisContext callerType)
        GenericHost(ApplicationAnalysisContext app, ModuleDefinition module,
            List<LocalVariable> locals)
    {
        var (caller, method) = ForeignCaller(app, module, [], locals);
        var callerType = (InjectedTypeAnalysisContext)caller.DeclaringType!;
        var typeArgument = new GenericParameterTypeAnalysisContext("T", 0,
            Il2CppTypeEnum.IL2CPP_TYPE_VAR, 0, callerType);
        callerType.GenericParameters.Add(typeArgument);
        return (caller, method, typeArgument, callerType);
    }

    private static MethodAnalysisContext InjectTake(InjectedTypeAnalysisContext callerType,
        ModuleDefinition module, MethodDefinition hostMethod,
        GenericParameterTypeAnalysisContext argumentType)
    {
        var take = callerType.InjectMethodContext("Take", argumentType.AppContext.SystemTypes.SystemVoidType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static,
            argumentType);
        var takeDefinition = new MethodDefinition("Take",
            MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void,
                [argumentType.ToTypeSignature()]));
        hostMethod.DeclaringType!.Methods.Add(takeDefinition);
        take.PutExtraData("AsmResolverMethod", takeDefinition);
        return take;
    }

    [Test]
    public void ProvenMarshaledContentAdoptsSharedGenericContract()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("ErasedObject.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemVoidType);
        // spill carries the erased marshaling rep; proven already spells `!T`.
        var spill = new LocalVariable("spill", new Register(null, "spill"))
            { Type = app.SystemTypes.SystemObjectType };
        var proven = new LocalVariable("proven", new Register(null, "proven"));
        var (caller, method, typeArgument, callerType) =
            GenericHost(app, module, [spill, proven]);
        proven.Type = typeArgument;
        var take = InjectTake(callerType, module, method, typeArgument);
        // spill := a `!T`-typed local, then feeds Take's `!T` parameter. Before
        // the erased-object recovery, the object-typed local hits a
        // conversion diagnostic at the argument; afterwards it adopts `!T`
        // and the call emits without any note.
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(-1, OpCode.Move, proven, new Immediate(0)),
            new(0, OpCode.Move, spill, proven),
            new(1, OpCode.CallVoid, take, spill),
            new(2, OpCode.Return)]);

        IlGenerator.GenerateIl(caller, method);

        var body = method.CilMethodBody!;
        Assert.Multiple(() =>
        {
            Assert.That(body.Instructions.Any(i => i.OpCode == CilOpCodes.Call
                    && i.Operand?.ToString().Contains("Take") == true), Is.True,
                () => string.Join("\n", body.Instructions.Select(i => i.ToString())));
            Assert.That(body.Instructions.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.False,
                () => string.Join("\n", body.Instructions.Select(i => i.ToString())));
        });
    }

    [Test]
    public void ErasedSpillOfSharedGenericCellAdoptsContract()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("ErasedCell.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemVoidType);
        var stack = new LocalVariable("stack", new Register(null, "stack_-180"));
        // The dominant r241 producer: an object-typed local defined by a
        // frame-cell read, where both the cell and the copy feed `!T` slots.
        var spill = new LocalVariable("spill", new Register(null, "spill"))
            { Type = app.SystemTypes.SystemObjectType };
        var (caller, method, typeArgument, callerType) =
            GenericHost(app, module, [stack, spill]);
        var take = InjectTake(callerType, module, method, typeArgument);
        var cell = new MemoryOperand(stack, addend: 0, accessSize: 8);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, spill, cell),
            new(1, OpCode.CallVoid, take, cell),
            new(2, OpCode.CallVoid, take, spill),
            new(3, OpCode.Return)]);

        IlGenerator.GenerateIl(caller, method);

        var body = method.CilMethodBody!;
        Assert.That(body.Instructions.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.False,
            () => string.Join("\n", body.Instructions.Select(i => i.ToString())));
    }

    [Test]
    public void FsgMarshaledUseKeepsErasedLocalAndNote()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("ErasedFsg.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemVoidType);
        // The erased rep itself: a local already carrying the fully-shared
        // placeholder type.
        var fsgType = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Unity.IL2CPP.Metadata", "__Il2CppFullySharedGenericType",
            app.SystemTypes.SystemObjectType,
            System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Class);
        SeedCorLibTypes(app, module, fsgType);
        var spill = new LocalVariable("spill", new Register(null, "spill")) { Type = fsgType };
        var proven = new LocalVariable("proven", new Register(null, "proven"));
        var (caller, method, typeArgument, callerType) =
            GenericHost(app, module, [spill, proven]);
        proven.Type = typeArgument;
        var take = InjectTake(callerType, module, method, typeArgument);
        // A marshaled cell wants only the erased rep: passing the adopted `!T`
        // value would emit a `castclass` to the FSG placeholder - a type check
        // the binary never performs. The local keeps its erased type, the `!T`
        // use keeps its note and the FSG use emits no fabricated cast.
        var takeFsg = callerType.InjectMethodContext("TakeFsg",
            app.SystemTypes.SystemVoidType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static,
            fsgType);
        var takeFsgDefinition = new MethodDefinition("TakeFsg",
            MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void,
                [fsgType.ToTypeSignature()]));
        method.DeclaringType!.Methods.Add(takeFsgDefinition);
        takeFsg.PutExtraData("AsmResolverMethod", takeFsgDefinition);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(-1, OpCode.Move, proven, new Immediate(0)),
            new(0, OpCode.Move, spill, proven),
            new(1, OpCode.CallVoid, take, spill),
            new(2, OpCode.CallVoid, takeFsg, spill),
            new(3, OpCode.Return)]);

        IlGenerator.GenerateIl(caller, method);

        var body = method.CilMethodBody!;
        var instructions = body.Instructions;
        // The FSG-cell use: the argument window feeding TakeFsg must contain no
        // fabricated `castclass` to the placeholder. (The FSG-typed local's own
        // definition site is a separate, pre-existing marshal and is not what
        // this assertion measures.)
        var takeFsgCallIndex = instructions
            .Select((ins, i) => (ins, i))
            .Where(x => x.ins.OpCode == CilOpCodes.Call
                && x.ins.Operand?.ToString().Contains("TakeFsg") == true)
            .Select(x => x.i).FirstOrDefault(-1);
        Assert.That(takeFsgCallIndex, Is.GreaterThanOrEqualTo(0),
            () => string.Join("\n", instructions.Select(i => i.ToString())));
        var window = instructions.Skip(System.Math.Max(0, takeFsgCallIndex - 4)).Take(4).ToList();
        Assert.Multiple(() =>
        {
            Assert.That(window.Any(i => i.OpCode == CilOpCodes.Castclass
                    && i.Operand?.ToString().Contains("__Il2CppFullySharedGenericType") == true),
                Is.False,
                () => string.Join("\n", instructions.Select(i => i.ToString())));
            Assert.That(instructions.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("operand to T")), Is.True,
                () => string.Join("\n", instructions.Select(i => i.ToString())));
        });
    }

    [Test]
    public void ErasedReceiverRetargetMarshalsFsgContract()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("ErasedRetarget.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemVoidType);
        var fsgType = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Unity.IL2CPP.Metadata", "__Il2CppFullySharedGenericType",
            app.SystemTypes.SystemObjectType,
            System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Class);
        SeedCorLibTypes(app, module, fsgType);
        // Box<T>::TakeBox(T) - the metadata callee declares `!T`, but the
        // receiver spells `Box<FSG>` so the emitted slot is the fully-shared
        // placeholder: the same retarget the call emitter performs.
        var boxType = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Erased", "Box`1",
            app.SystemTypes.SystemObjectType,
            System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Class);
        var boxT = new GenericParameterTypeAnalysisContext("T", 0,
            Il2CppTypeEnum.IL2CPP_TYPE_VAR, 0, boxType);
        boxType.GenericParameters.Add(boxT);
        var takeBox = boxType.InjectMethodContext("TakeBox",
            app.SystemTypes.SystemVoidType,
            System.Reflection.MethodAttributes.Public,
            boxT);
        var boxDefinition = new TypeDefinition("Erased", "Box`1",
            TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        boxDefinition.GenericParameters.Add(new GenericParameter("T"));
        module.TopLevelTypes.Add(boxDefinition);
        var takeBoxDefinition = new MethodDefinition("TakeBox",
            MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void,
                [new GenericParameterSignature(AsmResolver.DotNet.Signatures.GenericParameterType.Type, 0)]));
        boxDefinition.Methods.Add(takeBoxDefinition);
        takeBox.PutExtraData("AsmResolverMethod", takeBoxDefinition);
        boxType.PutExtraData("AsmResolverType", boxDefinition);
        var recv = new LocalVariable("recv", new Register(null, "recv"))
            { Type = new GenericInstanceTypeAnalysisContext(boxType, [fsgType]) };
        // spill is the erased rep: its `!T` use would adopt, but the
        // FSG-marshaled argument slot on the retargeted callee vetoes - the
        // value stays erased, the `!T` use keeps its note and no `castclass`
        // to the placeholder is fabricated.
        var spill = new LocalVariable("spill", new Register(null, "spill")) { Type = fsgType };
        var (caller, method, typeArgument, callerType) =
            GenericHost(app, module, [recv, spill]);
        var take = InjectTake(callerType, module, method, typeArgument);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.CallVoid, take, spill),
            new(1, OpCode.CallVoid, takeBox, recv, spill),
            new(2, OpCode.Return)]);

        IlGenerator.GenerateIl(caller, method);

        var body = method.CilMethodBody!;
        var instructions = body.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(instructions.Any(i => i.OpCode == CilOpCodes.Call
                    && i.Operand?.ToString().Contains("TakeBox") == true), Is.True,
                () => string.Join("\n", instructions.Select(i => i.ToString())));
            Assert.That(instructions.Any(i => i.OpCode == CilOpCodes.Castclass
                    && i.Operand?.ToString().Contains("__Il2CppFullySharedGenericType") == true),
                Is.False,
                () => string.Join("\n", instructions.Select(i => i.ToString())));
            Assert.That(instructions.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("operand to T")), Is.True,
                () => string.Join("\n", instructions.Select(i => i.ToString())));
        });
    }

    [Test]
    public void UnprovenProducerKeepsConversionDiagnostic()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("ErasedUnproven.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemVoidType);
        // produced holds a call's object return - it cannot prove `!T`, so the
        // erased local must stay erased and the argument keeps its note.
        var spill = new LocalVariable("spill", new Register(null, "spill"))
            { Type = app.SystemTypes.SystemObjectType };
        var produced = new LocalVariable("produced", new Register(null, "produced"))
            { Type = app.SystemTypes.SystemObjectType };
        var (caller, method, typeArgument, callerType) =
            GenericHost(app, module, [spill, produced]);
        var take = InjectTake(callerType, module, method, typeArgument);
        var provide = callerType.InjectMethodContext("Provide",
            app.SystemTypes.SystemObjectType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static);
        var provideDefinition = new MethodDefinition("Provide",
            MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Object));
        method.DeclaringType!.Methods.Add(provideDefinition);
        provide.PutExtraData("AsmResolverMethod", provideDefinition);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Call, provide, produced),
            new(1, OpCode.Move, spill, produced),
            new(2, OpCode.CallVoid, take, spill),
            new(3, OpCode.Return)]);

        IlGenerator.GenerateIl(caller, method);

        var body = method.CilMethodBody!;
        Assert.That(body.Instructions.Any(i => i.OpCode == CilOpCodes.Ldstr
                && i.Operand is string text && text.Contains("operand to T")), Is.True,
            () => string.Join("\n", body.Instructions.Select(i => i.ToString())));
    }
}
