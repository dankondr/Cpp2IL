using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;
using F = AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes;
using T = AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: indexed array dereferences whose element-region offset is
// folded into the index local - `[array + biased * stride + off]` where
// `biased = i + elementsOffset / stride`, as the binary keeps it (#159).
// IL2CPP emits an unsigned bounds check (`CheckLess` onto the carry flag)
// before such accesses; when the in-bounds edge of the branch it feeds
// dominates the access, the index is proven and the dereference is a real
// ldelem/stelem/ldelema+member access. Without a dominating check the site
// keeps its diagnostic.
public class GuardedArrayIndexTests
{
    private static TypeAnalysisContext SeedElement(ApplicationAnalysisContext app,
        ModuleDefinition module, string name, params (string Name, int Offset)[] fields)
    {
        var single = app.SystemTypes.SystemSingleType;
        var element = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", name,
            app.SystemTypes.SystemValueTypeType,
            System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Sealed
                | System.Reflection.TypeAttributes.SequentialLayout);
        var definition = new TypeDefinition("Tests", name,
            T.Public | T.Sealed | T.SequentialLayout,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        module.TopLevelTypes.Add(definition);
        element.PutExtraData("AsmResolverType", definition);
        foreach (var (fieldName, offset) in fields)
        {
            var field = new InjectedFieldAnalysisContext(fieldName, single,
                System.Reflection.FieldAttributes.Public, element, offset);
            element.Fields.Add(field);
            var fieldDefinition = new FieldDefinition(fieldName, F.Public,
                new FieldSignature(module.CorLibTypeFactory.Single));
            definition.Fields.Add(fieldDefinition);
            field.PutExtraData("AsmResolverField", fieldDefinition);
        }
        return element;
    }

    private static string Emit(IEnumerable<CilInstruction> il) => string.Join("\n", il.Select(i => i.ToString()));

    // The IL2CPP guard preamble: `length = array->max_length`,
    // `flag = index <u length` onto the named flag register, `flagNot = !flag`,
    // branch on `index >=u length` to `oob`. The access on the fall-through
    // (in-bounds) edge is `[array + (index + bias) * scale + addend]`.
    private static MethodDefinition GuardedCaller(ApplicationAnalysisContext app,
        ModuleDefinition module, TypeAnalysisContext elementType, int bias,
        string flagRegister, LocalVariable value, bool store = false,
        int addend = 0, int scale = 0, int accessSize = 0)
    {
        var array = new LocalVariable("array", new Register(null, "array"))
            { Type = new SzArrayTypeAnalysisContext(elementType) };
        var index = new LocalVariable("index", new Register(null, "index"))
            { Type = app.SystemTypes.SystemInt32Type };
        var biased = new LocalVariable("biased", new Register(null, "biased"))
            { Type = app.SystemTypes.SystemInt32Type };
        var memory = new MemoryOperand(array, biased, addend, scale, accessSize);
        var access = store
            ? new Instruction(5, OpCode.Move, memory, value)
            : new Instruction(5, OpCode.Move, value, memory);
        var length = new LocalVariable("length", new Register(null, "length"))
            { Type = app.SystemTypes.SystemInt32Type };
        var flag = new LocalVariable("flag", new Register(null, flagRegister));
        var flagNot = new LocalVariable("flagNot", new Register(null, flagRegister));
        var oob = new Instruction(9, OpCode.Move,
            new LocalVariable("dummy", new Register(null, "dummy")), new Immediate(1));
        var instructions = new List<Instruction>
        {
            new(0, OpCode.Add, biased, index, new Immediate(bias)),
            new(1, OpCode.Move, length, new MemoryOperand(array, addend: 24)),
            new(2, OpCode.CheckLess, flag, index, length),
            new(3, OpCode.Not, flagNot, flag),
            new(4, OpCode.ConditionalJump, oob, flagNot),
            access,
            new(6, OpCode.Return),
            oob,
            new(10, OpCode.Return)
        };
        var locals = new List<LocalVariable> { array, index, biased, length, flag, flagNot, value };
        var (caller, method) = ForeignCaller(app, module, instructions, locals);
        caller.ParameterLocals = locals;
        caller.DominatorInfo = new DominatorInfo(caller.ControlFlowGraph!);
        ArrayRecovery.Run(caller);
        IlGenerator.GenerateIl(caller, method);
        return method;
    }

    [Test]
    public void GuardedIndexLoadEmitsLdelem()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var module = new ModuleDefinition("GuardedIndexLoad.dll");
        SeedCorLibTypes(app, module, int32, app.SystemTypes.SystemVoidType);
        var result = new LocalVariable("result", new Register(null, "result")) { Type = int32 };

        // [array + (index + 8) * 4] = array[index] in an int32[] - the header
        // offset (0x20) is folded into the index as +8 elements.
        var method = GuardedCaller(app, module, int32, bias: 8, "C", result, scale: 4);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode.ToString()!.Contains("ldelem")), Is.True,
                () => Emit(il));
            Assert.That(il.Where(i => i.OpCode == CilOpCodes.Ldstr).All(i =>
                    i.Operand?.ToString()?.Contains("operand to System.Object slot") == true), Is.True,
                () => Emit(il));
        });
    }

    [Test]
    public void GuardedIndexStoreEmitsStelem()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var module = new ModuleDefinition("GuardedIndexStore.dll");
        SeedCorLibTypes(app, module, int32, app.SystemTypes.SystemVoidType);
        var value = new LocalVariable("value", new Register(null, "value")) { Type = int32 };

        var method = GuardedCaller(app, module, int32, bias: 8, "C", value, store: true, scale: 4);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode.ToString()!.Contains("stelem")), Is.True,
                () => Emit(il));
            Assert.That(il.Where(i => i.OpCode == CilOpCodes.Ldstr).All(i =>
                    i.Operand?.ToString()?.Contains("operand to System.Object slot") == true), Is.True,
                () => Emit(il));
        });
    }

    [Test]
    public void GuardedIndexMemberLoadEmitsLdelemaLdfld()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var single = app.SystemTypes.SystemSingleType;
        var module = new ModuleDefinition("GuardedIndexMember.dll");
        SeedCorLibTypes(app, module, single, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemValueTypeType, app.SystemTypes.SystemVoidType);
        var element = SeedElement(app, module, "Pair", ("x", 0), ("y", 4));
        var result = new LocalVariable("result", new Register(null, "result")) { Type = single };

        // [array + (index + 4) * 8 + 4] = array[index].y
        var method = GuardedCaller(app, module, element, bias: 4, "C", result,
            addend: 4, scale: 8);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldelema), Is.True,
                () => Emit(il));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldfld
                    && i.Operand?.ToString().Contains("y") == true), Is.True,
                () => Emit(il));
            Assert.That(il.Where(i => i.OpCode == CilOpCodes.Ldstr).All(i =>
                    i.Operand?.ToString()?.Contains("operand to System.Object slot") == true), Is.True,
                () => Emit(il));
        });
    }

    [Test]
    public void UnguardedIndexKeepsDiagnostic()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var module = new ModuleDefinition("UnguardedIndex.dll");
        SeedCorLibTypes(app, module, int32, app.SystemTypes.SystemVoidType);
        var array = new LocalVariable("array", new Register(null, "array"))
            { Type = new SzArrayTypeAnalysisContext(int32) };
        var index = new LocalVariable("index", new Register(null, "index")) { Type = int32 };
        var biased = new LocalVariable("biased", new Register(null, "biased")) { Type = int32 };
        var result = new LocalVariable("result", new Register(null, "result")) { Type = int32 };
        // Identical dereference shape, no bounds check anywhere.
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Add, biased, index, new Immediate(8)),
            new(1, OpCode.Move, result, new MemoryOperand(array, biased, scale: 4)),
            new(2, OpCode.Return)], [array, index, biased, result]);
        caller.ParameterLocals = [array, index, biased, result];
        caller.DominatorInfo = new DominatorInfo(caller.ControlFlowGraph!);

        ArrayRecovery.Run(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.True,
                () => Emit(il));
            Assert.That(il.Any(i => i.OpCode.ToString()!.Contains("ldelem")), Is.False,
                () => Emit(il));
        });
    }

    [Test]
    public void SignedCompareDoesNotProveIndex()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var module = new ModuleDefinition("SignedCompare.dll");
        SeedCorLibTypes(app, module, int32, app.SystemTypes.SystemVoidType);
        var result = new LocalVariable("result", new Register(null, "result")) { Type = int32 };

        // A signed-compare flag (N register, produced by flag folding) is not
        // the unsigned bounds check IL2CPP emits, so the index stays unproven.
        var method = GuardedCaller(app, module, int32, bias: 8, "N", result, scale: 4);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.True,
                () => Emit(il));
            Assert.That(il.Any(i => i.OpCode.ToString()!.Contains("ldelem")), Is.False,
                () => Emit(il));
        });
    }
}
