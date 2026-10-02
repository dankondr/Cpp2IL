using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using static Cpp2IL.Core.Tests.Regression.NestedFieldPathLoadTests;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery mechanism (castle-recovery#211): a get-only auto-property is assigned in its
// own type's constructor. `static Event X { get; } = new Event();` is
// `stsfld <X>k__BackingField` in the .cctor, `Name { get; } = v` is `stfld` in the .ctor.
// Elsewhere such a store has no spelling and stays diagnosed - never a silent drop.
public class OwnInitializerBackingFieldStoreTests
{
    // Holder { static string <Shared>k__BackingField @0 (statics); string <Name>k__BackingField @0x10 },
    // getters get_Shared/get_Name, no setters. The caller stores `value` into one of them.
    private static (MethodAnalysisContext Caller, Instruction Store) Store(bool isStatic, string callerName)
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var str = app.SystemTypes.SystemStringType;
        var holder = InjectClass(app, "Holder");
        var property = isStatic ? "Shared" : "Name";
        holder.Fields.Add(new InjectedFieldAnalysisContext($"<{property}>k__BackingField", str,
            R.FieldAttributes.Private | (isStatic ? R.FieldAttributes.Static : 0), holder, isStatic ? 0 : 0x10));
        var kind = isStatic ? R.MethodAttributes.Static : 0;
        holder.InjectMethodContext($"get_{property}", str, R.MethodAttributes.Public | kind);
        var caller = holder.InjectMethodContext(callerName, app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | kind | (callerName.StartsWith('.') ? R.MethodAttributes.SpecialName | R.MethodAttributes.RTSpecialName : 0));

        var value = Local("value", str);
        Instruction store;
        List<Instruction> body;
        List<LocalVariable> locals;
        if (isStatic)
        {
            var klass = Local("klass", new RuntimeClassTypeAnalysisContext(holder, holder.DeclaringAssembly));
            var statics = Local("statics", new StaticFieldStorageTypeAnalysisContext(holder, holder.DeclaringAssembly));
            store = new Instruction(2, OpCode.Move, new MemoryOperand(statics, null, 0, 0, 8), value);
            body = [new(0, OpCode.Move, klass, holder),
                new(1, OpCode.Move, statics, new MemoryOperand(klass, null, app.Binary.is32Bit ? 0x5C : 0xB8, 0, 8)),
                store, new(3, OpCode.Return)];
            locals = [klass, statics, value];
        }
        else
        {
            var self = Local("this", holder);
            self.IsThis = true;
            store = new Instruction(0, OpCode.Move, new MemoryOperand(self, null, 0x10, 0, 8), value);
            body = [store, new(1, OpCode.Return)];
            locals = [self, value];
        }
        caller.ControlFlowGraph = new ISILControlFlowGraph(body);
        caller.Locals = locals;
        caller.ParameterLocals = isStatic ? [value] : [locals[0], value];
        caller.AnalysisWarnings = [];

        MetadataResolver.ResolveFieldOffsets(caller);
        return (caller, store);
    }

    [Test]
    public void StaticGetOnlyPropertyIsAssignedInItsOwnCctor()
    {
        var (_, store) = Store(isStatic: true, ".cctor");

        Assert.That((store.Operands[0] as FieldReference)?.Field.Name, Is.EqualTo("<Shared>k__BackingField"));
    }

    [Test]
    public void InstanceGetOnlyPropertyIsAssignedInItsOwnCtor()
    {
        var (_, store) = Store(isStatic: false, ".ctor");

        Assert.That((store.Operands[0] as FieldReference)?.Field.Name, Is.EqualTo("<Name>k__BackingField"));
    }

    [Test]
    public void GetOnlyPropertyStoreElsewhereStaysUnresolved()
    {
        // C# cannot assign a get-only property outside its constructor.
        var (_, store) = Store(isStatic: true, "Reset");

        Assert.That(store.Operands[0], Is.InstanceOf<MemoryOperand>());
    }

    [Test]
    public void UnresolvedStoreAtOffsetZeroIsDiagnosedNotStoredIntoThePointer()
    {
        // `[p] = v` writes what p points at. Storing v into p would drop the write silently.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("Drop.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemIntPtrType, app.SystemTypes.SystemStringType);
        var pointer = Local("pointer", app.SystemTypes.SystemIntPtrType);
        var value = Local("value", app.SystemTypes.SystemInt32Type);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, value, new Immediate(7)),
            new(1, OpCode.Move, new MemoryOperand(pointer, null, 0, 0, 4), value),
            new(2, OpCode.Return)], [pointer, value]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr && i.Operand is string text
                && text.Contains("could not be emitted")), Is.True, () => Dump(method));
            Assert.That(il.Count(i => i.OpCode.Code is CilCode.Stloc or CilCode.Stloc_S or CilCode.Stloc_0
                or CilCode.Stloc_1 or CilCode.Stloc_2 or CilCode.Stloc_3), Is.EqualTo(1), () => Dump(method));
        });
    }
}
