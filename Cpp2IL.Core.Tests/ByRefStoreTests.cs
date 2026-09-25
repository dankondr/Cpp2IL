using System;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.InstructionSets;
using Disarm;

namespace Cpp2IL.Core.Tests;

public class ByRefStoreTests
{
    [TestCase(0xbd400000u, 4)] // ldr s0, [x0]
    [TestCase(0xf9400020u, 8)] // ldr x0, [x1]
    [TestCase(0x39400020u, 1)] // ldrb w0, [x1]
    public void NativeLoadRetainsWidth(uint encoding, int width)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Load",
            app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Static, []);
        var lifted = new NewArmV8InstructionSet().ConvertInstructions(Disassembler.Disassemble(BitConverter.GetBytes(encoding), 0), caller);
        Assert.That(((MemoryOperand)lifted[0].Operands[1]).AccessSize, Is.EqualTo(width));
    }

    [TestCase(0xf900003fu, 8)] // str xzr, [x1]
    [TestCase(0xb900003fu, 4)] // str wzr, [x1]
    [TestCase(0x7900003fu, 2)] // strh wzr, [x1]
    [TestCase(0x3900003fu, 1)] // strb wzr, [x1]
    public void NativeStoreRetainsWidth(uint encoding, int width)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Store",
            app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Static, []);
        var lifted = new NewArmV8InstructionSet().ConvertInstructions(Disassembler.Disassemble(BitConverter.GetBytes(encoding), 0), caller);
        Assert.That(((MemoryOperand)lifted[0].Operands[0]).AccessSize, Is.EqualTo(width));
    }

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    [TestCase("reference", 8, 0, true)]
    [TestCase("reference", 4, 0, false)]
    [TestCase("reference", 1, 0, false)]
    [TestCase("reference", 16, 0, false)]
    [TestCase("reference", 0, 0, false)]
    [TestCase("reference", 8, 8, false)]
    [TestCase("int", 4, 0, false)]
    [TestCase("struct", 8, 0, false)]
    [TestCase("pointer", 8, 0, false)]
    [TestCase("generic", 8, 0, false)]
    [TestCase("unmanaged", 8, 0, false)]
    [TestCase("ordinary", 8, 0, false)]
    public void OnlyExactReferenceByrefStoreDereferencesDestination(string kind, int width, int offset, bool supported)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var element = kind switch
        {
            "int" => app.SystemTypes.SystemInt32Type,
            "struct" => app.AssembliesByName["mscorlib"].GetTypeByFullName("System.DateTime")!,
            "pointer" => new PointerTypeAnalysisContext(app.SystemTypes.SystemInt32Type),
            "generic" => new GenericParameterTypeAnalysisContext("T", 0,
                LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_VAR, 0, app.SystemTypes.SystemObjectType),
            _ => app.SystemTypes.SystemObjectType
        };
        TypeAnalysisContext parameterType = kind switch
        {
            "unmanaged" => new PointerTypeAnalysisContext(element),
            "ordinary" => element,
            _ => new ByRefTypeAnalysisContext(element)
        };
        var parameter = new LocalVariable("destination", new Register(null, "X1"), parameterType);
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Write",
            app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, [parameterType]);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, new MemoryOperand(parameter, addend: offset) { AccessSize = width }, new Immediate(0)),
            new(1, OpCode.Return)]);
        caller.Locals = [parameter];
        caller.ParameterLocals = [parameter];
        caller.AnalysisWarnings = [];
        var module = new ModuleDefinition("ByrefFixture.dll", new AssemblyReference("System.Private.CoreLib", typeof(object).Assembly.GetName().Version!));
        foreach (var context in new[] { app.SystemTypes.SystemObjectType, app.SystemTypes.SystemInt32Type,
                     app.AssembliesByName["mscorlib"].GetTypeByFullName("System.DateTime")! })
        {
            var placeholder = new TypeDefinition("Fixture", context.Name, TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
            module.TopLevelTypes.Add(placeholder);
            context.PutExtraData("AsmResolverType", placeholder);
        }
        var type = new TypeDefinition("Tests", "Writer", TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var definition = new MethodDefinition("Write", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void, [module.CorLibTypeFactory.Object.MakeByReferenceType()]));
        type.Methods.Add(definition);
        definition.ParameterDefinitions.Add(new ParameterDefinition(1, "destination", 0));
        IlGenerator.GenerateIl(caller, definition);
        var instructions = definition.CilMethodBody!.Instructions;
        Assert.That(instructions.Any(i => i.OpCode == CilOpCodes.Stind_Ref), Is.EqualTo(supported));
        if (!supported)
        {
            if (kind is not ("ordinary" or "unmanaged"))
                Assert.That(instructions.Any(i => i.Operand is string text && text.StartsWith("Unsupported managed-pointer store")), Is.True);
            else
                Assert.That(instructions.Any(i => i.OpCode == CilOpCodes.Stloc), Is.True, "Existing non-byref path unchanged");
            return;
        }
        Assert.That(instructions.Any(i => i.OpCode == CilOpCodes.Stloc), Is.False, "Do not overwrite the address local");
        // Execute emitted instructions with a non-null caller slot: the write must reach that slot.
        foreach (var local in definition.CilMethodBody.LocalVariables)
            local.VariableType = module.CorLibTypeFactory.Object.MakeByReferenceType();
        var assembly = new AssemblyDefinition("ByrefFixture", new Version(1, 0));
        assembly.Modules.Add(module);
        using var stream = new System.IO.MemoryStream();
        module.Write(stream);
        var loaded = System.Reflection.Assembly.Load(stream.ToArray());
        object?[] arguments = [new object()];
        loaded.GetType("Tests.Writer")!.GetMethod("Write")!.Invoke(null, arguments);
        Assert.That(arguments[0], Is.Null);
    }
}
