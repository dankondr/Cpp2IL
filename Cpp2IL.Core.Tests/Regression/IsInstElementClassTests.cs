using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: invalid-conversion isinst/`as` behind an Il2CppClass<T> slot
// (castle-recovery#114). A reference-array store emits a runtime element-class
// check: `LDR klass,[array]` then `LDR target,[klass + element_class]` feed
// object_is_inst. The klass local is typed Il2CppClass<array.Type>, but
// array.Type can be polluted by register merging (a phi merging the array
// register with an unrelated typed copy). The element class is provable from
// the allocation that produced the array - recover it from that definition
// rather than the polluted local tag.
public class IsInstElementClassTests
{
    [Test]
    public void ElementClassOfPollutedArrayResolvesFromAllocationProducer()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var objectArray = new SzArrayTypeAnalysisContext(app.SystemTypes.SystemObjectType);
        // Register merging left the array's copy carrying an unrelated type.
        var pollutant = app.SystemTypes.SystemExceptionType;
        var array = new LocalVariable("array", new Register(null, "x0"))
            { Type = pollutant };
        var arrayClass = new LocalVariable("arrayClass", new Register(null, "x1"))
        {
            Type = new RuntimeClassTypeAnalysisContext(objectArray, objectArray.DeclaringAssembly),
        };
        var copy = new LocalVariable("copy", new Register(null, "x21"))
            { Type = pollutant };
        var klass = new LocalVariable("klass", new Register(null, "x8"))
        {
            Type = new RuntimeClassTypeAnalysisContext(pollutant, pollutant.DeclaringAssembly),
        };
        var element = new LocalVariable("element", new Register(null, "x1_v2"));
        var value = new LocalVariable("value", new Register(null, "x0_v9"))
            { Type = app.SystemTypes.SystemStringType };
        var result = new LocalVariable("result", new Register(null, "x0_v10"))
            { Type = pollutant };
        var elementOffset = app.Binary.is32Bit ? 0x20u : 0x40u;
        var isinst = new Instruction(4, OpCode.Call,
            new StringLiteral("il2cpp_vm_object_is_inst"), result, value,
            element, new Immediate(0));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Fixture",
            app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([
                new Instruction(0, OpCode.Call, new StringLiteral("SzArrayNew"),
                    array, arrayClass, new Immediate(3)),
                new Instruction(1, OpCode.Move, copy, array),
                new Instruction(2, OpCode.Move, klass, new MemoryOperand(copy)),
                new Instruction(3, OpCode.Move, element, new MemoryOperand(klass, addend: elementOffset)),
                isinst,
                new Instruction(5, OpCode.Return),
            ]),
        };

        KeyFunctionRecovery.Run(method);

        Assert.Multiple(() =>
        {
            Assert.That(isinst.OpCode, Is.EqualTo(OpCode.Move));
            var cast = (ReferenceCast)isinst.Operands[1];
            Assert.That(cast.Type, Is.SameAs(app.SystemTypes.SystemObjectType),
                "the store-check class is the array's element type");
            Assert.That(cast.Value, Is.SameAs(value));
            Assert.That(cast.NullOnFailure, Is.True);
            Assert.That(result.Type, Is.SameAs(app.SystemTypes.SystemObjectType),
                "the isinst result local is typed from the cast target");
            Assert.That(element.Type, Is.TypeOf<RuntimeClassTypeAnalysisContext>());
            Assert.That(((RuntimeClassTypeAnalysisContext)element.Type!).RepresentedType,
                Is.SameAs(app.SystemTypes.SystemObjectType));
        });
    }

    [Test]
    public void ElementClassOfUnprovableInstanceKeepsRepresentedTag()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var pollutant = app.SystemTypes.SystemExceptionType;
        var instance = new LocalVariable("instance", new Register(null, "x21"))
            { Type = pollutant };
        var klass = new LocalVariable("klass", new Register(null, "x8"))
        {
            Type = new RuntimeClassTypeAnalysisContext(pollutant, pollutant.DeclaringAssembly),
        };
        var element = new LocalVariable("element", new Register(null, "x1_v2"));
        var elementLoad = new Instruction(1, OpCode.Move, element,
            new MemoryOperand(klass, addend: app.Binary.is32Bit ? 0x20u : 0x40u));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Fixture",
            app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([
                new Instruction(0, OpCode.Move, klass, new MemoryOperand(instance)),
                elementLoad,
                new Instruction(2, OpCode.Return),
            ]),
        };

        KeyFunctionRecovery.Run(method);

        // The instance producer is opaque (a parameter), so the load keeps the
        // klass tag's represented type - unchanged from before.
        Assert.That(elementLoad.Operands[1], Is.TypeOf<RuntimeClassTypeAnalysisContext>());
        Assert.That(((RuntimeClassTypeAnalysisContext)elementLoad.Operands[1]).RepresentedType,
            Is.SameAs(pollutant));
    }
}
