using System;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests;

public class IlGeneratorHfaTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    [Test]
    public void ValueTypeAggregateStoreUsesManagedPointerAndProducesVerifiableBody()
    {
        var result = GenerateAggregateMove(3);
        var instructions = result.Method.CilMethodBody!.Instructions;

        var fieldLoads = instructions
            .Select((instruction, index) => (instruction, index))
            .Where(pair => pair.instruction.OpCode == CilOpCodes.Ldfld)
            .ToArray();

        Assert.That(fieldLoads, Has.Length.EqualTo(3));
        Assert.That(fieldLoads.All(pair => instructions[pair.index - 1].OpCode == CilOpCodes.Ldloca), Is.True,
            "value-type ldfld must consume a managed pointer from ldloca");

        var assemblyDefinition = new AssemblyDefinition("HfaVerifier", new Version(1, 0));
        assemblyDefinition.Modules.Add(result.Module);
        using var stream = new System.IO.MemoryStream();
        Assert.DoesNotThrow(() => result.Module.Write(stream));
        var assembly = R.Assembly.Load(stream.ToArray());
        Assert.DoesNotThrow(() => assembly.GetType("Tests.HfaVerifier")!.GetMethod("Move")!.Invoke(null, null));
    }

    [Test]
    public void AggregateLoadAndStoreBoundToAvailableLanes()
    {
        Assert.DoesNotThrow(() => GenerateAggregateMove(2));
    }

    private static (ModuleDefinition Module, MethodDefinition Method) GenerateAggregateMove(int laneCount)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("HfaVerifier.dll",
            new AssemblyReference("System.Private.CoreLib", typeof(object).Assembly.GetName().Version!));
        var valueType = module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType");
        var scalarDefinition = new TypeDefinition("Tests", "Single", TypeAttributes.Public | TypeAttributes.Sealed,
            valueType);
        var vectorDefinition = new TypeDefinition("Tests", "Vector3", TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout,
            valueType);
        module.TopLevelTypes.Add(scalarDefinition);
        module.TopLevelTypes.Add(vectorDefinition);
        app.SystemTypes.SystemSingleType.PutExtraData("AsmResolverType", scalarDefinition);

        var vector = new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly, "Tests", "Vector3",
            app.SystemTypes.SystemValueTypeType, R.TypeAttributes.Public | R.TypeAttributes.Sealed);
        vector.PutExtraData("AsmResolverType", vectorDefinition);

        foreach (var name in new[] { "x", "y", "z" })
        {
            var field = vector.InjectFieldContext(name, app.SystemTypes.SystemSingleType, R.FieldAttributes.Public);
            var fieldDefinition = new FieldDefinition(name, FieldAttributes.Public,
                new FieldSignature(scalarDefinition.ToTypeSignature()));
            vectorDefinition.Fields.Add(fieldDefinition);
            field.PutExtraData("AsmResolverField", fieldDefinition);
        }

        var sourceLanes = Enumerable.Range(0, laneCount)
            .Select(i => new LocalVariable($"source{i}", new Register(null, $"source{i}"), app.SystemTypes.SystemSingleType))
            .ToArray();
        var destinationLanes = Enumerable.Range(0, laneCount)
            .Select(i => new LocalVariable($"destination{i}", new Register(null, $"destination{i}"), app.SystemTypes.SystemSingleType))
            .ToArray();
        var source = new AggregateOperand(vector, sourceLanes);
        var destination = new AggregateOperand(vector, destinationLanes);
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Move",
            app.SystemTypes.SystemVoidType, R.MethodAttributes.Public | R.MethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, destination, source),
            new Instruction(1, OpCode.Return)]);
        context.Locals = [.. sourceLanes, .. destinationLanes, source, destination];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];

        var holder = new TypeDefinition("Tests", "HfaVerifier", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(holder);
        var method = new MethodDefinition("Move", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        holder.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);
        return (module, method);
    }
}
