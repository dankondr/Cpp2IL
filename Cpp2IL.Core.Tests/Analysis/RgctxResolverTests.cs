using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class RgctxResolverTests
{
    private static ApplicationAnalysisContext App => Cpp2IlApi.CurrentAppContext!;
    private static AssemblyAnalysisContext Mscorlib => App.AssembliesByName["mscorlib"];

    private static TypeAnalysisContext MscorlibType(string fullName) => Mscorlib.GetTypeByFullName(fullName)!;

    private static TypeAnalysisContext Generic(string fullName, params TypeAnalysisContext[] arguments)
        => new GenericInstanceTypeAnalysisContext(MscorlibType(fullName), arguments);

    private static MethodAnalysisContext GenericMethod(MethodAnalysisContext definition,
        TypeAnalysisContext[] typeArguments, TypeAnalysisContext[] methodArguments)
        => new ConcreteGenericMethodAnalysisContext(definition, typeArguments, methodArguments);

    private static (InjectedMethodAnalysisContext Method, Instruction Instruction, LocalVariable Destination)
        TableLoad(LocalVariable source, long addend)
    {
        var method = new InjectedMethodAnalysisContext(App.SystemTypes.SystemObjectType, "Load",
            App.SystemTypes.SystemVoidType, MethodAttributes.Static, []);
        var destination = new LocalVariable("destination", new Register(null, "destination"));
        var instruction = new Instruction(0, OpCode.Move, destination,
            new MemoryOperand(source, addend: addend));
        method.ControlFlowGraph = new ISILControlFlowGraph([instruction, new(1, OpCode.Return)]);
        return (method, instruction, destination);
    }

    private static LocalVariable Typed(string name, TypeAnalysisContext type)
        => new(name, new Register(null, name), type);

    private static TypeAnalysisContext? Resolved(LocalVariable tableLocal, long addend,
        out IOperand operand, out LocalVariable destination)
    {
        var (method, instruction, dest) = TableLoad(tableLocal, addend);
        RgctxResolver.Run(method);
        operand = instruction.Operands[1];
        destination = dest;
        return dest.Type;
    }

    private static TypeAnalysisContext? Resolved(LocalVariable tableLocal, long addend)
        => Resolved(tableLocal, addend, out _, out _);

    [Test]
    public void TypeRgctxClassAndTypeEntriesProduceConcreteClasses()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var instance = Generic("System.Nullable`1", App.SystemTypes.SystemInt32Type);
        var table = Typed("table", new RgctxTableTypeAnalysisContext(instance, instance.DeclaringAssembly));

        // [0] CLASS T, [1] CLASS Nullable`1<T>, [6] TYPE T
        Assert.Multiple(() =>
        {
            Assert.That(((RuntimeClassTypeAnalysisContext)Resolved(table, 0)!).RepresentedType,
                Is.SameAs(App.SystemTypes.SystemInt32Type));

            var self = ((RuntimeClassTypeAnalysisContext)Resolved(table, 8)!).RepresentedType;
            Assert.That(self, Is.TypeOf<GenericInstanceTypeAnalysisContext>());
            Assert.That(((GenericInstanceTypeAnalysisContext)self).GenericType.FullName,
                Is.EqualTo("System.Nullable`1"));
            Assert.That(((GenericInstanceTypeAnalysisContext)self).GenericArguments.Single(),
                Is.SameAs(App.SystemTypes.SystemInt32Type));

            Assert.That(((RuntimeClassTypeAnalysisContext)Resolved(table, 48)!).RepresentedType,
                Is.SameAs(App.SystemTypes.SystemInt32Type));
        });
    }

    [Test]
    public void TypeRgctxNestedConstructedGenericInstantiatesFully()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var inner = Generic("System.Collections.Generic.List`1", App.SystemTypes.SystemInt32Type);
        var instance = Generic("System.Nullable`1", inner);
        var table = Typed("table", new RgctxTableTypeAnalysisContext(instance, instance.DeclaringAssembly));

        // [1] CLASS Nullable`1<T> - a constructed generic whose argument is itself constructed
        var resolved = ((RuntimeClassTypeAnalysisContext)Resolved(table, 8)!).RepresentedType;
        Assert.Multiple(() =>
        {
            var outer = (GenericInstanceTypeAnalysisContext)resolved;
            Assert.That(outer.GenericType.FullName, Is.EqualTo("System.Nullable`1"));
            var argument = (GenericInstanceTypeAnalysisContext)outer.GenericArguments.Single();
            Assert.That(argument.GenericType.FullName,
                Is.EqualTo("System.Collections.Generic.List`1"));
            Assert.That(argument.GenericArguments.Single(), Is.SameAs(App.SystemTypes.SystemInt32Type));
        });
    }

    [Test]
    public void TypeRgctxConstrainedEntriesResolveToOpaqueHelperPointer()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var instance = Generic("System.Nullable`1", App.SystemTypes.SystemInt32Type);
        var table = Typed("table", new RgctxTableTypeAnalysisContext(instance, instance.DeclaringAssembly));

        // [2..4] CONSTRAINED - the runtime slot is a ConstrainedCall* helper handle, not a
        // managed descriptor, so the only honest type is an opaque pointer.
        var resolved = Resolved(table, 16);
        Assert.Multiple(() =>
        {
            Assert.That(resolved, Is.TypeOf<PointerTypeAnalysisContext>());
            Assert.That(((PointerTypeAnalysisContext)resolved!).ElementType.FullName,
                Is.EqualTo("System.Void"));
        });
    }

    [Test]
    public void TypeRgctxMethodEntryResolvesRuntimeMethodInfo()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var instance = Generic("System.Nullable`1", App.SystemTypes.SystemInt32Type);
        var table = Typed("table", new RgctxTableTypeAnalysisContext(instance, instance.DeclaringAssembly));

        // [5] METHOD
        var resolved = Resolved(table, 40);
        Assert.That(resolved, Is.TypeOf<RuntimeMethodInfoAnalysisContext>());
    }

    [Test]
    public void MethodRgctxEntriesResolveAllKinds()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var array = MscorlibType("System.Array");
        var asReadOnly = array.Methods.First(m => m.Name == "AsReadOnly"
            && m.GenericParameters.Count == 1 && m.Definition?.RgctXs.Length == 4);
        var method = GenericMethod(asReadOnly, [], [App.SystemTypes.SystemInt32Type]);
        var table = Typed("table",
            new MethodRgctxTableTypeAnalysisContext(method, method.CustomAttributeAssembly));

        Assert.Multiple(() =>
        {
            // [0] CLASS T[] - array wrapper
            var arrayClass = ((RuntimeClassTypeAnalysisContext)Resolved(table, 0)!).RepresentedType;
            Assert.That(arrayClass, Is.TypeOf<SzArrayTypeAnalysisContext>());
            Assert.That(((SzArrayTypeAnalysisContext)arrayClass).ElementType,
                Is.SameAs(App.SystemTypes.SystemInt32Type));

            // [1] CLASS ReadOnlyCollection`1<T>
            var roc = ((RuntimeClassTypeAnalysisContext)Resolved(table, 8)!).RepresentedType;
            Assert.That(roc, Is.TypeOf<GenericInstanceTypeAnalysisContext>());
            Assert.That(((GenericInstanceTypeAnalysisContext)roc).GenericType.FullName,
                Is.EqualTo("System.Collections.ObjectModel.ReadOnlyCollection`1"));

            // [2] METHOD ReadOnlySpan`1<T>.ctor - RuntimeMethodInfo over a concrete generic method
            var info = (RuntimeMethodInfoAnalysisContext)Resolved(table, 16)!;
            Assert.That(info.RepresentedMethod, Is.TypeOf<ConcreteGenericMethodAnalysisContext>());

            // [3] CLASS IList`1<T>
            var ilist = ((RuntimeClassTypeAnalysisContext)Resolved(table, 24)!).RepresentedType;
            Assert.That(ilist, Is.TypeOf<GenericInstanceTypeAnalysisContext>());
            Assert.That(((GenericInstanceTypeAnalysisContext)ilist).GenericType.FullName,
                Is.EqualTo("System.Collections.Generic.IList`1"));
        });
    }

    [Test]
    public void MethodRgctxSharedReferenceGenericInstantiatesConcreteTypes()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var array = MscorlibType("System.Array");
        var asReadOnly = array.Methods.First(m => m.Name == "AsReadOnly"
            && m.GenericParameters.Count == 1 && m.Definition?.RgctXs.Length == 4);
        var method = GenericMethod(asReadOnly, [], [App.SystemTypes.SystemStringType]);
        var table = Typed("table",
            new MethodRgctxTableTypeAnalysisContext(method, method.CustomAttributeAssembly));

        // shared reference generic: T = string, a reference type - [0] T[] must not be erased
        var resolved = ((RuntimeClassTypeAnalysisContext)Resolved(table, 0)!).RepresentedType;
        Assert.Multiple(() =>
        {
            Assert.That(resolved, Is.TypeOf<SzArrayTypeAnalysisContext>());
            Assert.That(((SzArrayTypeAnalysisContext)resolved).ElementType,
                Is.SameAs(App.SystemTypes.SystemStringType));
        });
    }

    [Test]
    public void MethodRgctxByrefWrapperInstantiates()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var array = MscorlibType("System.Array");
        var resize = array.Methods.First(m => m.Name == "Resize"
            && m.GenericParameters.Count == 1);
        var method = GenericMethod(resize, [], [App.SystemTypes.SystemInt32Type]);
        var table = Typed("table",
            new MethodRgctxTableTypeAnalysisContext(method, method.CustomAttributeAssembly));

        // [0] CLASS T[]& - byref wrapper around the instantiated szarray
        var resolved = ((RuntimeClassTypeAnalysisContext)Resolved(table, 0)!).RepresentedType;
        Assert.Multiple(() =>
        {
            Assert.That(resolved, Is.TypeOf<ByRefTypeAnalysisContext>());
            Assert.That(((ByRefTypeAnalysisContext)resolved).ElementType,
                Is.TypeOf<SzArrayTypeAnalysisContext>());
            Assert.That(((SzArrayTypeAnalysisContext)((ByRefTypeAnalysisContext)resolved).ElementType).ElementType,
                Is.SameAs(App.SystemTypes.SystemInt32Type));
        });
    }

    [Test]
    public void MethodRgctxMultipleMethodArgumentsInstantiateEach()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var array = MscorlibType("System.Array");
        var convertAll = array.Methods.First(m => m.Name == "ConvertAll"
            && m.GenericParameters.Count == 2);
        var method = GenericMethod(convertAll, [],
            [App.SystemTypes.SystemInt32Type, App.SystemTypes.SystemStringType]);
        var table = Typed("table",
            new MethodRgctxTableTypeAnalysisContext(method, method.CustomAttributeAssembly));

        // [1] CLASS Converter`2<TInput,TOutput>
        var resolved = ((RuntimeClassTypeAnalysisContext)Resolved(table, 8)!).RepresentedType;
        Assert.Multiple(() =>
        {
            var converter = (GenericInstanceTypeAnalysisContext)resolved;
            Assert.That(converter.GenericType.FullName, Is.EqualTo("System.Converter`2"));
            Assert.That(converter.GenericArguments[0], Is.SameAs(App.SystemTypes.SystemInt32Type));
            Assert.That(converter.GenericArguments[1], Is.SameAs(App.SystemTypes.SystemStringType));
        });
    }

    [Test]
    public void MethodInfoKlassChainResolvesDeclaringTypeAndMethodTable()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var array = MscorlibType("System.Array");
        var asReadOnly = array.Methods.First(m => m.Name == "AsReadOnly"
            && m.GenericParameters.Count == 1 && m.Definition?.RgctXs.Length == 4);
        var method = GenericMethod(asReadOnly, [], [App.SystemTypes.SystemInt32Type]);
        var info = Typed("info",
            new RuntimeMethodInfoAnalysisContext(method, array.DeclaringAssembly));

        // MethodInfo::klass (@0x20) -> RuntimeClass of the declaring type
        var klass = Resolved(info, 0x20);
        Assert.Multiple(() =>
        {
            Assert.That(klass, Is.TypeOf<RuntimeClassTypeAnalysisContext>());
            Assert.That(((RuntimeClassTypeAnalysisContext)klass!).RepresentedType, Is.SameAs(array));

            // MethodInfo::rgctx_data (@0x38) -> the method's own table
            var table = Resolved(info, 0x38);
            Assert.That(table, Is.TypeOf<MethodRgctxTableTypeAnalysisContext>());
            Assert.That(((MethodRgctxTableTypeAnalysisContext)table!).OwnerMethod, Is.SameAs(method));
        });
    }

    [Test]
    public void ClassRgctxDataChainResolvesTypeTable()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var instance = Generic("System.Nullable`1", App.SystemTypes.SystemInt32Type);
        var klass = Typed("klass", new RuntimeClassTypeAnalysisContext(instance, instance.DeclaringAssembly));

        // Il2CppClass::rgctx_data (@0xC0) -> the type's table, which then resolves entries
        var table = Resolved(klass, 0xC0);
        Assert.That(table, Is.TypeOf<RgctxTableTypeAnalysisContext>());
        Assert.That(((RgctxTableTypeAnalysisContext)table!).OwnerType, Is.SameAs(instance));
    }

    [Test]
    public void OutOfRangeEntryLeavesOperandUnresolved()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var instance = Generic("System.Nullable`1", App.SystemTypes.SystemInt32Type);
        var table = Typed("table", new RgctxTableTypeAnalysisContext(instance, instance.DeclaringAssembly));

        // Nullable`1 has 7 entries - slot 7 is out of range
        var resolved = Resolved(table, 7 * 8, out var operand, out var destination);
        Assert.Multiple(() =>
        {
            Assert.That(resolved, Is.Null);
            Assert.That(operand, Is.TypeOf<MemoryOperand>());
            Assert.That(destination.Type, Is.Null);
        });
    }

    [Test]
    public void UnalignedTableAccessLeavesOperandUnresolved()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var instance = Generic("System.Nullable`1", App.SystemTypes.SystemInt32Type);
        var table = Typed("table", new RgctxTableTypeAnalysisContext(instance, instance.DeclaringAssembly));

        var resolved = Resolved(table, 4, out var operand, out var destination);
        Assert.Multiple(() =>
        {
            Assert.That(resolved, Is.Null);
            Assert.That(operand, Is.TypeOf<MemoryOperand>());
            Assert.That(destination.Type, Is.Null);
        });
    }

    [Test]
    public void PartiallyInstantiatedMethodLeavesOperandUnresolved()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var array = MscorlibType("System.Array");
        var asReadOnly = array.Methods.First(m => m.Name == "AsReadOnly"
            && m.GenericParameters.Count == 1 && m.Definition?.RgctXs.Length == 4);
        // a concrete generic method with no method arguments - the generic context is genuinely
        // open, so the table must stay an explicit unresolved load rather than guessing T
        var partial = GenericMethod(asReadOnly, [], []);
        Assert.That(((ConcreteGenericMethodAnalysisContext)partial).IsPartialInstantiation, Is.True);
        var table = Typed("table",
            new MethodRgctxTableTypeAnalysisContext(partial, partial.CustomAttributeAssembly));

        var resolved = Resolved(table, 0, out var operand, out var destination);
        Assert.Multiple(() =>
        {
            Assert.That(resolved, Is.Null);
            Assert.That(operand, Is.TypeOf<MemoryOperand>());
            Assert.That(destination.Type, Is.Null);
        });
    }

    [Test]
    public void OpenMethodRgctxResolvesToOwnParameters()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var array = MscorlibType("System.Array");
        var asReadOnly = array.Methods.First(m => m.Name == "AsReadOnly"
            && m.GenericParameters.Count == 1 && m.Definition?.RgctXs.Length == 4);
        // the uninflated definition is shared generic code: its own T is the table's argument
        var table = Typed("table",
            new MethodRgctxTableTypeAnalysisContext(asReadOnly, asReadOnly.CustomAttributeAssembly));

        var resolved = ((RuntimeClassTypeAnalysisContext)Resolved(table, 0)!).RepresentedType;
        Assert.Multiple(() =>
        {
            Assert.That(resolved, Is.TypeOf<SzArrayTypeAnalysisContext>());
            Assert.That(((SzArrayTypeAnalysisContext)resolved).ElementType,
                Is.TypeOf<GenericParameterTypeAnalysisContext>());
        });
    }
}
