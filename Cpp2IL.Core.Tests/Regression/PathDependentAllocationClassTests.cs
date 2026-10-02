using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// `x = flag ? new A() : new B();` compiled to one object_new whose class pointer is a
// phi of A's and B's class: the join typed the local with the first input's class, so
// pairing the shared base .ctor with it built an A on both paths. No single newobj can
// say what the native code does; the site has to stay diagnosed.
public class PathDependentAllocationClassTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    [Test]
    public void PhiOfTwoClassPointersBuildsNoSingleNewobj()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var assembly = app.SystemTypes.SystemObjectType.DeclaringAssembly;
        var baseType = new InjectedTypeAnalysisContext(assembly, "Tests", "Base", app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public);
        var a = new InjectedTypeAnalysisContext(assembly, "Tests", "A", baseType, R.TypeAttributes.Public);
        var b = new InjectedTypeAnalysisContext(assembly, "Tests", "B", baseType, R.TypeAttributes.Public);
        var baseConstructor = baseType.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType, R.MethodAttributes.Public);
        var aConstructor = a.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType, R.MethodAttributes.Public);
        var bConstructor = b.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType, R.MethodAttributes.Public);

        var flag = new LocalVariable("flag", new Register(null, "flag"), app.SystemTypes.SystemBooleanType);
        var klass = new LocalVariable("klass", new Register(null, "klass"),
            new RuntimeClassTypeAnalysisContext(a, assembly));
        var result = new LocalVariable("result", new Register(null, "result"), baseType);
        var caller = new InjectedMethodAnalysisContext(baseType, "Create", baseType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, [app.SystemTypes.SystemBooleanType]);
        var ofB = new Instruction(3, OpCode.Move, klass, b);
        var join = new Instruction(4, OpCode.Newobj, result, klass);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.ConditionalJump, ofB, flag),
            new(1, OpCode.Move, klass, a),
            new(2, OpCode.Jump, join),
            ofB,
            join,
            new(5, OpCode.CallVoid, baseConstructor, result),
            new(6, OpCode.Return, result)]);
        caller.Locals = [flag, klass, result];
        caller.ParameterLocals = [flag];
        caller.AnalysisWarnings = [];

        var module = new ModuleDefinition("PathDependentAllocation.dll");
        TypeDefinition Define(string name, ITypeDefOrRef? baseDefinition)
        {
            var definition = new TypeDefinition("Tests", name, TypeAttributes.Public, baseDefinition);
            module.TopLevelTypes.Add(definition);
            return definition;
        }
        MethodDefinition Constructor(TypeDefinition owner)
        {
            var constructor = new MethodDefinition(".ctor", MethodAttributes.Public,
                MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
            owner.Methods.Add(constructor);
            return constructor;
        }
        foreach (var (system, name) in new[] { (app.SystemTypes.SystemObjectType, "Object"),
                     (app.SystemTypes.SystemBooleanType, "Boolean"), (app.SystemTypes.SystemIntPtrType, "IntPtr") })
        {
            var systemDefinition = new TypeDefinition("System", name, TypeAttributes.Public);
            module.TopLevelTypes.Add(systemDefinition);
            system.PutExtraData("AsmResolverType", systemDefinition);
        }
        var baseDefinition = Define("Base", module.CorLibTypeFactory.Object.Type);
        var aDefinition = Define("A", baseDefinition);
        var bDefinition = Define("B", baseDefinition);
        baseType.PutExtraData("AsmResolverType", baseDefinition);
        a.PutExtraData("AsmResolverType", aDefinition);
        b.PutExtraData("AsmResolverType", bDefinition);
        baseConstructor.PutExtraData("AsmResolverMethod", Constructor(baseDefinition));
        aConstructor.PutExtraData("AsmResolverMethod", Constructor(aDefinition));
        bConstructor.PutExtraData("AsmResolverMethod", Constructor(bDefinition));
        var definition = new MethodDefinition("Create", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(baseDefinition.ToTypeSignature(), [module.CorLibTypeFactory.Boolean]));
        baseDefinition.Methods.Add(definition);

        IlGenerator.GenerateIl(caller, definition);

        var il = definition.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Where(instruction => instruction.OpCode == CilOpCodes.Newobj), Is.Empty);
            Assert.That(caller.AnalysisWarnings.Concat(il.Where(instruction => instruction.OpCode == CilOpCodes.Ldstr)
                    .Select(instruction => (string)instruction.Operand!)),
                Has.Some.Contains("Allocated class differs by path"));
        });
    }
}
