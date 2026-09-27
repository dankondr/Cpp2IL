using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: throw-helper epilogue (gaps of Cpp2IL#100). A call to a helper
// proven non-returning must lower to Throw even when the call's destination local
// has readers — keeping the impossible fall-through edge live via Newobj lets joins
// below it read locals that no incoming path assigns (CS0165). A helper that merely
// produces an exception value for the caller keeps Newobj.
public class ThrowHelperEpilogueTests
{
    [Test]
    public void ProvenNonReturningHelperLowersToThrow()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var (exceptionType, ctorDefinition) = ExceptionFixture(app);
        var produced = new LocalVariable("produced", new Register(null, "produced")) { Type = exceptionType };
        var used = new LocalVariable("used", new Register(null, "used")) { Type = app.SystemTypes.SystemObjectType };
        var module = new ModuleDefinition("ThrowHelper.dll");
        SeedCorLibTypes(app, module, exceptionType, app.SystemTypes.SystemObjectType, app.SystemTypes.SystemVoidType);
        var call = new Instruction(0, OpCode.Call, new Immediate(0x1000), produced);
        var (caller, method) = ForeignCaller(app, module, [
            call,
            new(1, OpCode.Move, used, produced),
            new(2, OpCode.Return)], [produced, used]);
        var helperBlock = caller.ControlFlowGraph!.Blocks.Single(b => b.Instructions.Contains(call));

        MetadataResolver.LowerThrowHelperCall(caller, helperBlock, call, exceptionType,
            isProvenNonReturning: true, []);

        Assert.Multiple(() =>
        {
            Assert.That(call.OpCode, Is.EqualTo(OpCode.Throw));
            Assert.That(call.ThrowFromNonReturningCall, Is.True,
                "a raise replacing a consumed call result is not an injected-check epilogue");
        });

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        var producedLocal = method.CilMethodBody.LocalVariables[caller.Locals.IndexOf(produced)];
        var newobjIndex = il.IndexOf(il.Single(i => i.OpCode == CilOpCodes.Newobj));
        Assert.Multiple(() =>
        {
            Assert.That(il[newobjIndex].Operand, Is.EqualTo(ctorDefinition),
                "the proven helper's epilogue constructs the thrown exception");
            Assert.That(il[newobjIndex + 1].OpCode, Is.EqualTo(CilOpCodes.Throw),
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stloc && i.Operand == producedLocal), Is.False,
                "a non-returning call never produces a value to store\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void UnprovenHelperWithReadResultKeepsNewobj()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var (exceptionType, ctorDefinition) = ExceptionFixture(app);
        var produced = new LocalVariable("produced", new Register(null, "produced")) { Type = exceptionType };
        var used = new LocalVariable("used", new Register(null, "used")) { Type = app.SystemTypes.SystemObjectType };
        var module = new ModuleDefinition("ThrowHelperUnproven.dll");
        SeedCorLibTypes(app, module, exceptionType, app.SystemTypes.SystemObjectType, app.SystemTypes.SystemVoidType);
        var call = new Instruction(0, OpCode.Call, new Immediate(0x1000), produced);
        var (caller, method) = ForeignCaller(app, module, [
            call,
            new(1, OpCode.Move, used, produced),
            new(2, OpCode.Return)], [produced, used]);
        var helperBlock = caller.ControlFlowGraph!.Blocks.Single(b => b.Instructions.Contains(call));

        MetadataResolver.LowerThrowHelperCall(caller, helperBlock, call, exceptionType,
            isProvenNonReturning: false, []);

        Assert.That(call.OpCode, Is.EqualTo(OpCode.Newobj));

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        var producedLocal = method.CilMethodBody.LocalVariables[caller.Locals.IndexOf(produced)];
        Assert.Multiple(() =>
        {
            Assert.That(il.Single(i => i.OpCode == CilOpCodes.Newobj).Operand, Is.EqualTo(ctorDefinition));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stloc && i.Operand == producedLocal), Is.True,
                "an unproven helper still hands the constructed exception back to the caller\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    private static (TypeAnalysisContext type, MethodDefinition ctor) ExceptionFixture(ApplicationAnalysisContext app)
    {
        var type = new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly!,
            "System", "SyntheticException", app.SystemTypes.SystemObjectType, R.TypeAttributes.Public);
        var constructor = type.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType, R.MethodAttributes.Public);
        var module = new ModuleDefinition("ThrowHelperTypes.dll");
        var definition = new TypeDefinition("System", "SyntheticException", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        var ctorDefinition = new MethodDefinition(".ctor", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        definition.Methods.Add(ctorDefinition);
        type.PutExtraData("AsmResolverType", definition);
        constructor.PutExtraData("AsmResolverMethod", ctorDefinition);
        return (type, ctorDefinition);
    }
}
