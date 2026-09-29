using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: ref-alias copies merging at a join (castle-recovery#153).
// Phi lowering leaves a Move per incoming edge; when every copy spells the same
// ref parameter, the joined local is the same alias re-spelled - but no single
// definition exists to forward, so the local survives into emission and each
// store becomes `alias = ref param`: a rebind of a ref local to a ref parameter
// C# cannot express (CS9079). ByrefAliasForwarding reads the shared root at the
// uses instead and removes the local, restoring `Take(ref clip)`.
public class ByRefAliasForwardingTests
{
    private static (MethodAnalysisContext caller, MethodDefinition method) Setup(
        ApplicationAnalysisContext app, ModuleDefinition module,
        List<Instruction> instructions, List<LocalVariable> locals, List<LocalVariable> parameters,
        TypeAnalysisContext byteType)
    {
        var (caller, method) = ForeignCaller(app, module, instructions, locals);
        caller.ParameterLocals = parameters;
        method.Signature = MethodSignature.CreateStatic(module.CorLibTypeFactory.Void,
            parameters.Select(_ => (TypeSignature)new ByReferenceTypeSignature(
                module.CorLibTypeFactory.Byte)).ToArray());
        for (var i = 0; i < parameters.Count; i++)
            method.ParameterDefinitions.Add(
                new ParameterDefinition((ushort)(i + 1), parameters[i].Name, (ParameterAttributes)0));
        return (caller, method);
    }

    private static (InjectedTypeAnalysisContext holder, MethodAnalysisContext callee, TypeDefinition holderDefinition)
        NativeCallee(ApplicationAnalysisContext app, ModuleDefinition module, string name,
            params TypeSignature[] parameters)
    {
        var holder = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"],
            "Tests", "Native", app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        var holderDefinition = new TypeDefinition("Tests", "Native",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(holderDefinition);
        holder.PutExtraData("AsmResolverType", holderDefinition);
        var callee = holder.InjectMethodContext(name, app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, app.SystemTypes.SystemByteType.MakeByReferenceType());
        var calleeDefinition = new MethodDefinition(name,
            MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void, parameters));
        holderDefinition.Methods.Add(calleeDefinition);
        callee.PutExtraData("AsmResolverMethod", calleeDefinition);
        return (holder, callee, holderDefinition);
    }

    [Test]
    public void JoinMergedRefAliasReadsTheSharedParameter()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var byteType = app.SystemTypes.SystemByteType;
        var clipType = new ByRefTypeAnalysisContext(byteType);
        var module = new ModuleDefinition("ByRefAlias.dll");
        SeedCorLibTypes(app, module, byteType, app.SystemTypes.SystemVoidType,
            app.SystemTypes.SystemBooleanType);
        var (_, take, _) = NativeCallee(app, module, "Take",
            new ByReferenceTypeSignature(module.CorLibTypeFactory.Byte));

        var clip = new LocalVariable("clip", new Register(1, "clip"), clipType);
        var alias = new LocalVariable("alias", new Register(20, "alias"), clipType);
        var flag = new LocalVariable("flag", new Register(2, "flag"),
            app.SystemTypes.SystemBooleanType);
        var left = new LocalVariable("left", new Register(3, "left"), byteType);
        var right = new LocalVariable("right", new Register(4, "right"), byteType);

        var secondCopy = new Instruction(4, OpCode.Move, alias, clip);
        var join = new Instruction(5, OpCode.CallVoid, take, alias);
        var instructions = new List<Instruction>
        {
            new(0, OpCode.CheckEqual, flag, left, right),
            new(1, OpCode.ConditionalJump, secondCopy, flag),
            new(2, OpCode.Move, alias, clip),
            new(3, OpCode.Jump, join),
            secondCopy,
            join,
            new(6, OpCode.Return),
        };

        var (caller, method) = Setup(app, module, instructions,
            [clip, alias, flag, left, right], [clip], byteType);

        ByrefAliasForwarding.Run(caller);
        IlGenerator.GenerateIl(caller, method);

        var body = method.CilMethodBody!;
        var il = body.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(caller.Locals.Contains(alias), Is.False,
                "the alias local only ever re-spelled `clip`: it is eliminated\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call
                    && i.Operand is IMethodDescriptor named && named.Name?.ToString() == "Take"),
                Is.True, () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldarg || i.OpCode == CilOpCodes.Ldarg_S),
                Is.True,
                "the call reads the ref parameter directly - `Take(ref clip)`\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void CallBoundRefSlotKeepsItsLocalWhenWrittenThrough()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var byteType = app.SystemTypes.SystemByteType;
        var byteByRef = new ByRefTypeAnalysisContext(byteType);
        var module = new ModuleDefinition("ByRefWrite.dll");
        SeedCorLibTypes(app, module, byteType, app.SystemTypes.SystemVoidType);

        // `byte& Read()` - a ref-returning producer (the readonly-ref shape the
        // stripped signatures cannot distinguish). Its destination local is a real
        // ref binding, not an alias copy, so it must keep its ref slot.
        var readerHolder = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"],
            "Tests", "Native", app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        var holderDefinition = new TypeDefinition("Tests", "Native",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(holderDefinition);
        readerHolder.PutExtraData("AsmResolverType", holderDefinition);
        var reader = readerHolder.InjectMethodContext("Read", byteByRef,
            R.MethodAttributes.Public | R.MethodAttributes.Static);
        var readerDefinition = new MethodDefinition("Read",
            MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(new ByReferenceTypeSignature(module.CorLibTypeFactory.Byte)));
        holderDefinition.Methods.Add(readerDefinition);
        reader.PutExtraData("AsmResolverMethod", readerDefinition);

        var pinned = new LocalVariable("pinned", new Register(0, "pinned"), byteByRef);
        var alias = new LocalVariable("alias", new Register(20, "alias"), byteByRef);

        var instructions = new List<Instruction>
        {
            new(0, OpCode.Call, reader, pinned),
            new(1, OpCode.Move, alias, pinned),
            // The binary writes through the alias: [alias] = 0
            new(2, OpCode.Move, new MemoryOperand(alias, null, 0, accessSize: 1), new Immediate(0)),
            new(3, OpCode.Return),
        };

        var (caller, method) = Setup(app, module, instructions, [pinned, alias], [], byteType);

        ByrefAliasForwarding.Run(caller);
        IlGenerator.GenerateIl(caller, method);

        var body = method.CilMethodBody!;
        var il = body.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(caller.Locals.Contains(alias), Is.False,
                "the copy alias forwards to the call-bound slot\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(caller.Locals.Contains(pinned), Is.True,
                "the call-bound ref slot stays a `ref` local - its binding diagnostic stands\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(body.LocalVariables.Any(v => v.VariableType is ByReferenceTypeSignature),
                Is.True,
                "the `byte&` slot is not laundered to a pointer or a value\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stind_I1 || i.OpCode == CilOpCodes.Stind_I
                    || i.OpCode == CilOpCodes.Stobj),
                Is.True,
                "the write through the alias is preserved, not dropped\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
        });
    }
}
