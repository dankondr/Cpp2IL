using System.Collections.Generic;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery mechanism (castle-recovery#211): `x = c ? a.config : null; x.limit`. A use
// as op_Equality's argument types the merge with the parameter's base type, but every
// value it holds is a config or null, so the access resolves against the config.
public class MergedBaseTypeTests
{
    private static (Instruction Load, FieldAnalysisContext Limit, LocalVariable Merged) Build(bool otherInputUnrelated)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var mscorlib = app.AssembliesByName["mscorlib"];
        var baseType = new InjectedTypeAnalysisContext(mscorlib, "Tests", "Base",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var config = new InjectedTypeAnalysisContext(mscorlib, "Tests", "Config", baseType, TypeAttributes.Public);
        var other = new InjectedTypeAnalysisContext(mscorlib, "Tests", "Other", baseType, TypeAttributes.Public);
        var limit = new InjectedFieldAnalysisContext("limit", app.SystemTypes.SystemInt32Type,
            FieldAttributes.Public, config, 0x18);
        config.Fields.Add(limit);

        var value = new LocalVariable("value", new Register(null, "value"), config);
        var second = new LocalVariable("second", new Register(null, "second"), otherInputUnrelated ? other : null);
        var merged = new LocalVariable("merged", new Register(null, "merged"), baseType);
        var result = new LocalVariable("result", new Register(null, "result"));
        var load = new Instruction(3, OpCode.Move, result, new MemoryOperand(merged, addend: 0x18, accessSize: 4));
        var method = new InjectedMethodAnalysisContext(config, "Read", app.SystemTypes.SystemVoidType,
            MethodAttributes.Static, []);
        method.ControlFlowGraph = new ISILControlFlowGraph([
            otherInputUnrelated ? new(0, OpCode.Nop) : new(0, OpCode.Move, second, new Immediate(0)),
            new(1, OpCode.Nop),
            new(2, OpCode.Phi, merged, value, second),
            load, new(4, OpCode.Return)]);

        MetadataResolver.ResolveFieldOffsets(method);
        return (load, limit, merged);
    }

    [Test]
    public void AccessThroughMergeOfValueAndNullUsesTheValueType()
    {
        var (load, limit, merged) = Build(otherInputUnrelated: false);

        Assert.That(load.Operands[1], Is.TypeOf<FieldReference>(), () => load.Operands[1]?.ToString() ?? "<null>");
        Assert.That(((FieldReference)load.Operands[1]).Field, Is.SameAs(limit));
        // Declared with the type it holds, so the access needs no cast.
        Assert.That(merged.Type, Is.SameAs(limit.DeclaringType));
    }

    [Test]
    public void MergeOfTwoObjectTypesStaysUnresolved()
    {
        var (load, _, _) = Build(otherInputUnrelated: true);

        Assert.That(load.Operands[1], Is.TypeOf<MemoryOperand>());
    }
}
