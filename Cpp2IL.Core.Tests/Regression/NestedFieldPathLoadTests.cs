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

// Recovery cluster: typed-base unmanaged loads (castle-recovery#141).
// A load through a typed base whose offset still misses must resolve to the
// member it provably is: a value-type member reached through a byref, or a
// member nested more than one value-type field deep. Wider reads that overlap
// but do not equal a member's storage must keep the diagnostic - resolving
// them to the first overlapped member would substitute a different value.
public class NestedFieldPathLoadTests
{
    private static InjectedTypeAnalysisContext InjectStruct(ApplicationAnalysisContext app, string name)
        => new(app.AssembliesByName["mscorlib"], "Tests", name,
            app.SystemTypes.SystemValueTypeType,
            R.TypeAttributes.Public | R.TypeAttributes.Sealed | R.TypeAttributes.SequentialLayout);

    private static InjectedTypeAnalysisContext InjectClass(ApplicationAnalysisContext app, string name)
        => new(app.AssembliesByName["mscorlib"], "Tests", name,
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);

    private static InjectedFieldAnalysisContext InjectField(string name, TypeAnalysisContext type,
        TypeAnalysisContext declaring, int offset)
    {
        var field = new InjectedFieldAnalysisContext(name, type, R.FieldAttributes.Public,
            declaring, offset);
        declaring.Fields.Add(field);
        return field;
    }

    // Point2 { float x @0; float y @4 }
    private static (InjectedTypeAnalysisContext type, FieldAnalysisContext x, FieldAnalysisContext y)
        Point2(ApplicationAnalysisContext app)
    {
        var type = InjectStruct(app, "Point2");
        var x = InjectField("x", app.SystemTypes.SystemSingleType, type, 0);
        var y = InjectField("y", app.SystemTypes.SystemSingleType, type, 4);
        return (type, x, y);
    }

    // Frame { Point2 origin @0; Point2 size @8 }
    private static (InjectedTypeAnalysisContext type, FieldAnalysisContext origin)
        Frame(ApplicationAnalysisContext app, TypeAnalysisContext point)
    {
        var type = InjectStruct(app, "Frame");
        var origin = InjectField("origin", point, type, 0);
        InjectField("size", point, type, 8);
        return (type, origin);
    }

    // Panel { Frame frame @0x10 } - a class so the object header keeps fields off 0.
    private static (InjectedTypeAnalysisContext type, FieldAnalysisContext frame)
        Panel(ApplicationAnalysisContext app, TypeAnalysisContext frameType)
    {
        var type = InjectClass(app, "Panel");
        var frame = InjectField("frame", frameType, type, 0x10);
        return (type, frame);
    }

    // Pair { int first @0; int second @4 }
    private static (InjectedTypeAnalysisContext type, FieldAnalysisContext first,
            FieldAnalysisContext second) Pair(ApplicationAnalysisContext app)
    {
        var type = InjectStruct(app, "Pair");
        var first = InjectField("first", app.SystemTypes.SystemInt32Type, type, 0);
        var second = InjectField("second", app.SystemTypes.SystemInt32Type, type, 4);
        return (type, first, second);
    }

    private static void Seed(ModuleDefinition module, ApplicationAnalysisContext app,
        params TypeAnalysisContext[] types)
    {
        var definitions = new Dictionary<TypeAnalysisContext, TypeDefinition>();
        foreach (var type in types)
        {
            var baseRef = type.IsValueType
                ? module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType")
                : module.CorLibTypeFactory.Object.Type;
            var attributes = type.IsValueType
                ? TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout
                : TypeAttributes.Public | TypeAttributes.Class;
            var definition = new TypeDefinition(type.Namespace, type.Name, attributes, baseRef);
            module.TopLevelTypes.Add(definition);
            type.PutExtraData("AsmResolverType", definition);
            definitions[type] = definition;
        }
        TypeSignature SignatureFor(TypeAnalysisContext fieldType)
        {
            if (definitions.TryGetValue(fieldType, out var definition))
                return definition.ToTypeSignature();
            if (fieldType == app.SystemTypes.SystemInt32Type)
                return module.CorLibTypeFactory.Int32;
            if (fieldType == app.SystemTypes.SystemSingleType)
                return module.CorLibTypeFactory.Single;
            return module.CorLibTypeFactory.Object;
        }

        foreach (var type in types)
        foreach (var field in type.Fields)
        {
            var fieldDefinition = new FieldDefinition(field.Name,
                AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes.Public,
                new FieldSignature(SignatureFor(field.FieldType)));
            definitions[type].Fields.Add(fieldDefinition);
            field.PutExtraData("AsmResolverField", fieldDefinition);
        }
    }

    private static LocalVariable Local(string name, TypeAnalysisContext? type = null)
        => new(name, new Register(null, name), type);

    private static bool EmitsUnmanagedLoadDiagnostic(MethodDefinition method)
        => method.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Ldstr
            && i.Operand is string text && text.Contains("Unmanaged memory load"));

    private static string Dump(MethodDefinition method)
        => string.Join("\n", method.CilMethodBody!.Instructions.Select(i => i.ToString()));

    [Test]
    public void ByRefToStructMemberReadResolvesToField()
    {
        // [min + 4] through a Pair& is min.second - the element type's member at
        // that offset - emitted as ldfld through the managed-pointer receiver.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var (pair, _, second) = Pair(app);
        var module = new ModuleDefinition("Reads.dll");
        Seed(module, app, pair);
        SeedCorLibTypes(app, module, pair, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemInt64Type, app.SystemTypes.SystemObjectType);

        var min = Local("min", new ByRefTypeAnalysisContext(pair));
        var dst = Local("dst", app.SystemTypes.SystemInt32Type);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, dst, new MemoryOperand(min, null, 4, 0, 4)),
            new(1, OpCode.Return)], [min, dst]);

        MetadataResolver.ResolveFieldOffsets(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldfld
                    && i.Operand is IFieldDescriptor f && f.Name == "second"), Is.True,
                () => Dump(method));
            Assert.That(EmitsUnmanagedLoadDiagnostic(method), Is.False, () => Dump(method));
        });
        Assert.That(second, Is.Not.Null);
    }

    [Test]
    public void TwoLevelNestedStructMemberReadResolvesPath()
    {
        // [panel + 0x14] = panel.frame.origin.y: frame @0x10 is a Frame, its
        // origin @0 is a Point2, whose y sits at relative offset 4. One level of
        // nesting cannot name it - the offset lands mid-member - so only a
        // multi-level path resolves it.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var (point, _, _) = Point2(app);
        var (frame, origin) = Frame(app, point);
        var (panel, frameField) = Panel(app, frame);
        var module = new ModuleDefinition("Reads.dll");
        Seed(module, app, point, frame, panel);
        SeedCorLibTypes(app, module, point, frame, panel, app.SystemTypes.SystemSingleType,
            app.SystemTypes.SystemObjectType);

        var receiver = Local("panel", panel);
        var dst = Local("dst", app.SystemTypes.SystemSingleType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, dst, new MemoryOperand(receiver, null, 0x14, 0, 4)),
            new(1, OpCode.Return)], [receiver, dst]);

        MetadataResolver.ResolveFieldOffsets(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Count(i => i.OpCode == CilOpCodes.Ldflda), Is.EqualTo(2),
                () => $"expected ldflda frame + ldflda origin, got:\n{Dump(method)}");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldfld
                    && i.Operand is IFieldDescriptor f && f.Name == "y"), Is.True,
                () => Dump(method));
            Assert.That(EmitsUnmanagedLoadDiagnostic(method), Is.False, () => Dump(method));
        });
        Assert.That(origin, Is.Not.Null);
        Assert.That(frameField, Is.Not.Null);
    }

    [Test]
    public void WideByRefReadOverlappingFirstMemberKeepsDiagnostic()
    {
        // [min + 0] as an eight-byte read covers BOTH Pair members; narrowing it
        // to `first` would substitute a different four-byte value, so the load
        // must keep its diagnostic instead of resolving.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var (pair, _, _) = Pair(app);
        var module = new ModuleDefinition("Reads.dll");
        Seed(module, app, pair);
        SeedCorLibTypes(app, module, pair, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemInt64Type, app.SystemTypes.SystemObjectType);

        var min = Local("min", new ByRefTypeAnalysisContext(pair));
        var dst = Local("dst", app.SystemTypes.SystemInt64Type);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, dst, new MemoryOperand(min, null, 0, 0, 8)),
            new(1, OpCode.Return)], [min, dst]);

        MetadataResolver.ResolveFieldOffsets(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldfld
                    && i.Operand is IFieldDescriptor f && f.Name == "first"), Is.False,
                () => $"eight-byte load must not narrow to first:\n{Dump(method)}");
            Assert.That(EmitsUnmanagedLoadDiagnostic(method), Is.True, () => Dump(method));
        });
    }

    // Cfg { <Level>k__BackingField int @0 } - an auto-property backing field is
    // only spellable through its accessor.
    private static (InjectedTypeAnalysisContext type, FieldAnalysisContext backing)
        Cfg(ApplicationAnalysisContext app)
    {
        var type = InjectStruct(app, "Cfg");
        var backing = new InjectedFieldAnalysisContext("<Level>k__BackingField",
            app.SystemTypes.SystemInt32Type, R.FieldAttributes.Private, type, 0);
        type.Fields.Add(backing);
        return (type, backing);
    }

    [Test]
    public void ByRefBackingFieldLoadWithVisibleGetterResolvesToField()
    {
        // [cfg& +0] reads Config's <Level>k__BackingField; the public getter is
        // callable from the caller, so the load resolves - the emission pass
        // then decides whether the accessor call or an honest default spells it.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var (cfg, backing) = Cfg(app);
        cfg.InjectMethodContext("get_Level", app.SystemTypes.SystemInt32Type,
            R.MethodAttributes.Public);
        var module = new ModuleDefinition("Reads.dll");
        Seed(module, app, cfg);
        SeedCorLibTypes(app, module, cfg, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemObjectType);

        var local = Local("cfg", new ByRefTypeAnalysisContext(cfg));
        var dst = Local("dst", app.SystemTypes.SystemInt32Type);
        var load = new Instruction(0, OpCode.Move, dst,
            new MemoryOperand(local, null, 0, 0, 4));
        var (caller, method) = ForeignCaller(app, module, [load, new(1, OpCode.Return)], [local, dst]);

        MetadataResolver.ResolveFieldOffsets(caller);
        IlGenerator.GenerateIl(caller, method);

        Assert.Multiple(() =>
        {
            Assert.That(load.Operands[1], Is.TypeOf<FieldReference>(),
                "a backing-field load with a callable getter must resolve");
            Assert.That(((FieldReference)load.Operands[1]).Field, Is.SameAs(backing));
            Assert.That(EmitsUnmanagedLoadDiagnostic(method), Is.False, () => Dump(method));
        });
    }

    [Test]
    public void ByRefBackingFieldStoreWithoutVisibleSetterKeepsDiagnostic()
    {
        // A store into Config's <Level>k__BackingField can only spell
        // cfg.Level = v; the setter is private, so the store keeps its
        // diagnostic instead of emitting an unspellable stfld.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var (cfg, backing) = Cfg(app);
        cfg.InjectMethodContext("set_Level", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Private, app.SystemTypes.SystemInt32Type);
        var module = new ModuleDefinition("Reads.dll");
        Seed(module, app, cfg);
        SeedCorLibTypes(app, module, cfg, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemObjectType);

        var local = Local("cfg", new ByRefTypeAnalysisContext(cfg));
        var src = Local("src", app.SystemTypes.SystemInt32Type);
        var store = new Instruction(0, OpCode.Move,
            new MemoryOperand(local, null, 0, 0, 4), src);
        var (caller, _) = ForeignCaller(app, module, [store, new(1, OpCode.Return)], [local, src]);

        MetadataResolver.ResolveFieldOffsets(caller);

        Assert.That(store.Operands[0], Is.TypeOf<MemoryOperand>(),
            "store into an unspellable backing field must keep its diagnostic operand");
        Assert.That(backing, Is.Not.Null);
    }

    [Test]
    public void NestedPathThroughLastBackingFieldContainerResolvesThroughGetter()
    {
        // [box +0x14] is box.<Inner>k__BackingField.y: the backing field is the
        // last container before a value-read leaf, so callvirt get_Inner +
        // ldfld y spells the same stack shape and the path resolves.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var (point, _, y) = Point2(app);
        var box = InjectClass(app, "Box");
        var backing = new InjectedFieldAnalysisContext("<Inner>k__BackingField",
            point, R.FieldAttributes.Private, box, 0x10);
        box.Fields.Add(backing);
        box.InjectMethodContext("get_Inner", point, R.MethodAttributes.Public);
        var module = new ModuleDefinition("Reads.dll");
        Seed(module, app, point, box);
        // Only the system types go to the corlib seeder - SeedCorLibTypes
        // rewrites AsmResolverType with a bare definition, which would shadow
        // the populated typedef the emitted member references bind to.
        SeedCorLibTypes(app, module, app.SystemTypes.SystemSingleType,
            app.SystemTypes.SystemObjectType);
        // The emitted surface must carry the accessor for the decompiler-facing
        // rewrite to name it - mirroring the real pipeline's emitted method.
        var boxDefinition = box.GetExtraData<TypeDefinition>("AsmResolverType")!;
        var pointDefinition = point.GetExtraData<TypeDefinition>("AsmResolverType")!;
        var innerDefinition = new PropertyDefinition("Inner", default,
            PropertySignature.CreateInstance(pointDefinition.ToTypeSignature()));
        boxDefinition.Properties.Add(innerDefinition);
        var getInner = new MethodDefinition("get_Inner",
            MethodAttributes.Public | MethodAttributes.HideBySig | MethodAttributes.SpecialName,
            MethodSignature.CreateInstance(pointDefinition.ToTypeSignature()));
        boxDefinition.Methods.Add(getInner);
        innerDefinition.SetSemanticMethods(getInner, null);

        var receiver = Local("box", box);
        var dst = Local("dst", app.SystemTypes.SystemSingleType);
        var load = new Instruction(0, OpCode.Move, dst,
            new MemoryOperand(receiver, null, 0x14, 0, 4));
        var (caller, method) = ForeignCaller(app, module, [load, new(1, OpCode.Return)], [receiver, dst]);

        MetadataResolver.ResolveFieldOffsets(caller);
        IlGenerator.GenerateIl(caller, method);
        Cpp2IL.Core.OutputFormats.DecompilerMemberAccessRewrites.Apply(method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(load.Operands[1], Is.TypeOf<FieldReference>(),
                "a last-hop backing-field container with a visible getter must resolve");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Callvirt
                    && i.Operand is IMethodDescriptor m && m.Name == "get_Inner"), Is.True,
                () => Dump(method));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldfld
                    && i.Operand is IFieldDescriptor f && f.Name == "y"), Is.True,
                () => Dump(method));
            Assert.That(EmitsUnmanagedLoadDiagnostic(method), Is.False, () => Dump(method));
        });
        Assert.That(backing, Is.Not.Null);
        Assert.That(y, Is.Not.Null);
    }

    [Test]
    public void NestedPathThroughNonLastBackingFieldContainerKeepsDiagnostic()
    {
        // [box +0x14] into box.<Inner>k__BackingField where Inner's member is
        // itself a struct field: the backing-field hop would feed a further
        // ldflda, which no accessor call can replace, so it keeps its
        // diagnostic even though get_Inner is public.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var (point, _, _) = Point2(app);
        var (frame, _) = Frame(app, point);
        var box = InjectClass(app, "Box");
        var backing = new InjectedFieldAnalysisContext("<Inner>k__BackingField",
            frame, R.FieldAttributes.Private, box, 0x10);
        box.Fields.Add(backing);
        box.InjectMethodContext("get_Inner", frame, R.MethodAttributes.Public);
        var module = new ModuleDefinition("Reads.dll");
        Seed(module, app, point, frame, box);
        SeedCorLibTypes(app, module, point, frame, box, app.SystemTypes.SystemSingleType,
            app.SystemTypes.SystemObjectType);

        var receiver = Local("box", box);
        var dst = Local("dst", app.SystemTypes.SystemSingleType);
        // box.<Inner>k__BackingField.origin.y: backing field is NOT the last
        // container (origin follows it), so the hop is unspellable.
        var load = new Instruction(0, OpCode.Move, dst,
            new MemoryOperand(receiver, null, 0x14, 0, 4));
        var (caller, _) = ForeignCaller(app, module, [load, new(1, OpCode.Return)], [receiver, dst]);

        MetadataResolver.ResolveFieldOffsets(caller);

        Assert.That(load.Operands[1], Is.TypeOf<MemoryOperand>(),
            "a non-last backing-field container hop must keep its diagnostic operand");
        Assert.That(backing, Is.Not.Null);
    }

    [Test]
    public void BackingFieldAddressReadSpellsGetterCall()
    {
        // ldflda T::<P>k__BackingField + ldobj T' moves exactly the backing
        // field's storage; with a public getter the pair collapses to the
        // callvirt get_P that produced the stack shape originally.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("Reads.dll");
        var holder = new TypeDefinition("Tests", "Holder",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(holder);
        var backing = new FieldDefinition("<Group>k__BackingField",
            FieldAttributes.Private, new FieldSignature(module.CorLibTypeFactory.Int32));
        holder.Fields.Add(backing);
        var property = new PropertyDefinition("Group", default,
            PropertySignature.CreateInstance(module.CorLibTypeFactory.Int32));
        holder.Properties.Add(property);
        var getter = new MethodDefinition("get_Group",
            MethodAttributes.Public | MethodAttributes.HideBySig | MethodAttributes.SpecialName,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Int32));
        holder.Methods.Add(getter);
        property.SetSemanticMethods(getter, null);
        var method = new MethodDefinition("M",
            MethodAttributes.Public, MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        holder.Methods.Add(method);
        method.CilMethodBody = new CilMethodBody();
        var instructions = method.CilMethodBody.Instructions;
        instructions.Add(CilOpCodes.Ldarg_0);
        instructions.Add(CilOpCodes.Ldflda, backing);
        instructions.Add(CilOpCodes.Ldobj, module.CorLibTypeFactory.Int32.Type);
        instructions.Add(CilOpCodes.Pop);
        instructions.Add(CilOpCodes.Ret);

        Cpp2IL.Core.OutputFormats.DecompilerMemberAccessRewrites.Apply(method);

        Assert.Multiple(() =>
        {
            Assert.That(instructions[1].OpCode, Is.EqualTo(CilOpCodes.Callvirt),
                "ldflda <P>k__BF + ldobj must collapse to the getter call");
            Assert.That(instructions[1].Operand, Is.SameAs(getter));
            Assert.That(instructions[2].OpCode, Is.EqualTo(CilOpCodes.Nop));
        });
        Assert.That(app, Is.Not.Null);
    }

    [Test]
    public void EnumUnderlyingAddressReadSpellsLdobjEnum()
    {
        // ldflda E::value__ + ldobj int32 pushes the same bytes as ldobj E on
        // &e - the address is identical and only the element type differed, so
        // the decompiler-facing rewrite retargets the consumer to the enum.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("Reads.dll");
        var enumDefinition = new TypeDefinition("Tests", "E",
            TypeAttributes.Public | TypeAttributes.Sealed,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "Enum"));
        var valueField = new FieldDefinition("value__",
            FieldAttributes.Public | FieldAttributes.SpecialName | FieldAttributes.RuntimeSpecialName,
            new FieldSignature(module.CorLibTypeFactory.Int32));
        enumDefinition.Fields.Add(valueField);
        module.TopLevelTypes.Add(enumDefinition);
        var method = new MethodDefinition("M",
            MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        enumDefinition.Methods.Add(method);
        method.CilMethodBody = new CilMethodBody();
        var instructions = method.CilMethodBody.Instructions;
        instructions.Add(CilOpCodes.Ldflda, valueField);
        instructions.Add(CilOpCodes.Ldobj, module.CorLibTypeFactory.Int32.Type);
        instructions.Add(CilOpCodes.Ret);

        Cpp2IL.Core.OutputFormats.DecompilerMemberAccessRewrites.Apply(method);

        Assert.Multiple(() =>
        {
            Assert.That(instructions[0].OpCode, Is.EqualTo(CilOpCodes.Nop),
                "the retagging ldflda should be dropped");
            Assert.That(instructions[1].OpCode, Is.EqualTo(CilOpCodes.Ldobj));
            Assert.That(instructions[1].Operand, Is.SameAs(enumDefinition));
        });
        Assert.That(app, Is.Not.Null);
    }

    [Test]
    public void ErasedBaseNestedMemberReadResolvesViaSharpenedOwner()
    {
        // An object-typed local defined by a field read sharpens to that field's
        // type at emission; [obj + 0x14] is then the same two-level nested read,
        // and the late field arm must carry the container path.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var (point, _, _) = Point2(app);
        var (frame, _) = Frame(app, point);
        var (panel, _) = Panel(app, frame);
        var holder = InjectClass(app, "Holder");
        var row = InjectField("row", panel, holder, 0x10);
        var module = new ModuleDefinition("Reads.dll");
        Seed(module, app, point, frame, panel, holder);
        SeedCorLibTypes(app, module, point, frame, panel, holder, app.SystemTypes.SystemSingleType,
            app.SystemTypes.SystemObjectType);

        var h = Local("h", holder);
        var obj = Local("obj", app.SystemTypes.SystemObjectType);
        var dst = Local("dst", app.SystemTypes.SystemSingleType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, obj, new FieldReference(row, h, 0x10)),
            new(1, OpCode.Move, dst, new MemoryOperand(obj, null, 0x14, 0, 4)),
            new(2, OpCode.Return)], [h, obj, dst]);

        MetadataResolver.ResolveFieldOffsets(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldfld
                    && i.Operand is IFieldDescriptor f && f.Name == "y"), Is.True,
                () => Dump(method));
            Assert.That(EmitsUnmanagedLoadDiagnostic(method), Is.False, () => Dump(method));
        });
    }
}
