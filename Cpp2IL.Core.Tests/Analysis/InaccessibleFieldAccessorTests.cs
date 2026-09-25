using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class InaccessibleFieldAccessorTests
{
    private static ApplicationAnalysisContext App => Cpp2IlApi.CurrentAppContext!;
    private static AssemblyAnalysisContext Mscorlib => App.AssembliesByName["mscorlib"];

    // A caller in a different assembly than the declaring type - cross-assembly private reads
    // are the case the accessor substitution exists for.
    private static InjectedMethodAnalysisContext CallerIn(AssemblyAnalysisContext assembly)
    {
        var owner = new InjectedTypeAnalysisContext(assembly, "Tests", "Caller",
            App.SystemTypes.SystemObjectType, TypeAttributes.Public);
        return new InjectedMethodAnalysisContext(owner, "Read",
            App.SystemTypes.SystemVoidType, MethodAttributes.Static, []);
    }

    private static (InjectedMethodAnalysisContext Method, Instruction Instruction)
        FieldRead(InjectedMethodAnalysisContext caller, TypeAnalysisContext receiverType, long addend, int accessSize = 4)
    {
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"), receiverType);
        var result = new LocalVariable("result", new Register(null, "result"));
        var load = new Instruction(0, OpCode.Move, result,
            new MemoryOperand(receiver, addend: addend, accessSize: accessSize));
        caller.ControlFlowGraph = new ISILControlFlowGraph([load, new(1, OpCode.Return)]);
        return (caller, load);
    }

    [Test]
    public void PrivateCorlibFieldReadSubstitutesPublicGetter()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        // String._stringLength @0x10 is private to mscorlib; the inlined managed source is
        // String.get_Length - the only public parameterless int getter String exposes.
        var caller = CallerIn(App.AssembliesByName["System.Core"]);
        var (method, load) = FieldRead(caller, App.SystemTypes.SystemStringType, 16);

        MetadataResolver.ResolveFieldOffsets(method);

        Assert.Multiple(() =>
        {
            Assert.That(load.OpCode, Is.EqualTo(OpCode.Call));
            Assert.That(load.Operands[0], Is.TypeOf<MethodAnalysisContext>());
            Assert.That(((MethodAnalysisContext)load.Operands[0]).Name, Is.EqualTo("get_Length"));
            Assert.That(((MethodAnalysisContext)load.Operands[0]).DeclaringType!.FullName,
                Is.EqualTo("System.String"));
        });
    }

    [Test]
    public void PrivateSameTypeFieldReadStaysDirectRead()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var owner = new InjectedTypeAnalysisContext(Mscorlib, "Tests", "Secret",
            App.SystemTypes.SystemObjectType, TypeAttributes.Public);
        owner.Fields.Add(new InjectedFieldAnalysisContext("hidden",
            App.SystemTypes.SystemInt32Type, FieldAttributes.Private, owner, 16));
        var caller = new InjectedMethodAnalysisContext(owner, "Read",
            App.SystemTypes.SystemVoidType, MethodAttributes.Static, []);
        var (method, load) = FieldRead(caller, owner, 16);

        MetadataResolver.ResolveFieldOffsets(method);

        Assert.Multiple(() =>
        {
            Assert.That(load.OpCode, Is.EqualTo(OpCode.Move));
            Assert.That(load.Operands[1], Is.TypeOf<FieldReference>());
            Assert.That(((FieldReference)load.Operands[1]).Field.Name, Is.EqualTo("hidden"));
        });
    }

    [Test]
    public void PublicFieldReadStaysDirectRead()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var owner = new InjectedTypeAnalysisContext(Mscorlib, "Tests", "Open",
            App.SystemTypes.SystemObjectType, TypeAttributes.Public);
        owner.Fields.Add(new InjectedFieldAnalysisContext("value",
            App.SystemTypes.SystemInt32Type, FieldAttributes.Public, owner, 16));
        var caller = CallerIn(App.AssembliesByName["System.Core"]);
        var (method, load) = FieldRead(caller, owner, 16);

        MetadataResolver.ResolveFieldOffsets(method);

        Assert.Multiple(() =>
        {
            Assert.That(load.OpCode, Is.EqualTo(OpCode.Move));
            Assert.That(load.Operands[1], Is.TypeOf<FieldReference>());
            Assert.That(((FieldReference)load.Operands[1]).Field.Name, Is.EqualTo("value"));
        });
    }

    [Test]
    public void PrivateFieldWithNoAccessorStaysUnresolvedDirectRead()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        // cross-assembly private with no public getter: nothing honest to substitute
        var owner = new InjectedTypeAnalysisContext(Mscorlib, "Tests", "Opaque",
            App.SystemTypes.SystemObjectType, TypeAttributes.Public);
        owner.Fields.Add(new InjectedFieldAnalysisContext("hidden",
            App.SystemTypes.SystemInt64Type, FieldAttributes.Private, owner, 16));
        var caller = CallerIn(App.AssembliesByName["System.Core"]);
        var (method, load) = FieldRead(caller, owner, 16, accessSize: 8);

        MetadataResolver.ResolveFieldOffsets(method);

        Assert.Multiple(() =>
        {
            Assert.That(load.OpCode, Is.EqualTo(OpCode.Move));
            Assert.That(load.Operands[1], Is.TypeOf<FieldReference>());
            Assert.That(((FieldReference)load.Operands[1]).Field.Name, Is.EqualTo("hidden"));
        });
    }

    [Test]
    public void AmbiguousAccessorCandidatesStayDirectRead()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        // two public int getters: which accessor inlined the read is not knowable - leave the
        // resolved field reference rather than picking one
        var owner = new InjectedTypeAnalysisContext(Mscorlib, "Tests", "Forked",
            App.SystemTypes.SystemObjectType, TypeAttributes.Public);
        owner.Fields.Add(new InjectedFieldAnalysisContext("hidden",
            App.SystemTypes.SystemInt32Type, FieldAttributes.Private, owner, 16));
        owner.Methods.Add(new InjectedMethodAnalysisContext(owner, "get_Left",
            App.SystemTypes.SystemInt32Type, MethodAttributes.Public, []));
        owner.Methods.Add(new InjectedMethodAnalysisContext(owner, "get_Right",
            App.SystemTypes.SystemInt32Type, MethodAttributes.Public, []));
        var caller = CallerIn(App.AssembliesByName["System.Core"]);
        var (method, load) = FieldRead(caller, owner, 16);

        MetadataResolver.ResolveFieldOffsets(method);

        Assert.Multiple(() =>
        {
            Assert.That(load.OpCode, Is.EqualTo(OpCode.Move));
            Assert.That(load.Operands[1], Is.TypeOf<FieldReference>());
        });
    }
}
