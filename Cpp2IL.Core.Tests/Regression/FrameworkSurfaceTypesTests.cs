using System;
using System.Linq;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Model.CustomAttributes;
using Cpp2IL.Core.OutputFormats;
using Cpp2IL.Core.Utils;
using NUnit.Framework;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

public class FrameworkSurfaceTypesTests
{
    // The fixture's corlib defines none of MethodImplAttribute,
    // MethodImplOptions, MethodCodeType, StructLayoutAttribute, LayoutKind,
    // IndexerNameAttribute or AssemblyVersionAttribute, while il2cpp metadata
    // keeps surfaces (implflags, layout, indexers, assembly version) that
    // decompile back to those attributes.
    [Test]
    public void FlagSurfacesMaterializeMissingCorlibTypeDefs()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();

        var assemblies = new AsmResolverDllOutputFormatEmpty().BuildAssemblies(app);
        var corlib = assemblies.First(a => a.Name == "mscorlib").ManifestModule!;

        // implflags -> [MethodImpl]
        var methodImpl = corlib.TopLevelTypes.FirstOrDefault(t =>
            t.FullName == "System.Runtime.CompilerServices.MethodImplAttribute");
        Assert.That(methodImpl, Is.Not.Null);
        Assert.That(methodImpl!.BaseType?.FullName, Is.EqualTo("System.Attribute"));
        Assert.That(methodImpl.Methods.Any(m => m.IsConstructor
                && m.Signature?.ParameterTypes.Count == 1), Is.True,
            "MethodImplAttribute must have the ctor the attribute surface uses");
        Assert.That(methodImpl.Fields.Any(f => f.Name == "MethodCodeType"), Is.True);
        Assert.That(methodImpl.Properties.Any(p => p.Name == "Value"), Is.True);

        var options = corlib.TopLevelTypes.FirstOrDefault(t =>
            t.FullName == "System.Runtime.CompilerServices.MethodImplOptions");
        Assert.That(options, Is.Not.Null);
        Assert.That(options!.IsEnum, Is.True);
        Assert.That(options.Fields.Any(f => f.Name == "value__"
            && (f.Attributes & FieldAttributes.SpecialName) != 0
            && (f.Attributes & FieldAttributes.RuntimeSpecialName) != 0), Is.True);
        Assert.That(options.Fields.Any(f => f.Name == "AggressiveInlining"
            && (f.Attributes & FieldAttributes.Literal) != 0
            && f.Constant?.Value is { Data: { Length: 4 } d } && BitConverter.ToInt32(d) == 256), Is.True);

        var codeType = corlib.TopLevelTypes.FirstOrDefault(t =>
            t.FullName == "System.Runtime.CompilerServices.MethodCodeType");
        Assert.That(codeType?.IsEnum, Is.True);

        // value types / layout -> [StructLayout]
        var structLayout = corlib.TopLevelTypes.FirstOrDefault(t =>
            t.FullName == "System.Runtime.InteropServices.StructLayoutAttribute");
        Assert.That(structLayout, Is.Not.Null);
        Assert.That(structLayout!.BaseType?.FullName, Is.EqualTo("System.Attribute"));
        Assert.That(structLayout.Fields.Any(f => f.Name == "Size"), Is.True);
        Assert.That(structLayout.Fields.Any(f => f.Name == "Pack"), Is.True);
        Assert.That(structLayout.Fields.Any(f => f.Name == "CharSet"), Is.True);
        Assert.That(structLayout.Properties.Any(p => p.Name == "Value"), Is.True);

        var layoutKind = corlib.TopLevelTypes.FirstOrDefault(t =>
            t.FullName == "System.Runtime.InteropServices.LayoutKind");
        Assert.That(layoutKind?.IsEnum, Is.True);
        Assert.That(layoutKind!.Fields.Any(f => f.Name == "Sequential"
            && (f.Attributes & FieldAttributes.Literal) != 0
            && f.Constant?.Value is { Data: { Length: 4 } s } && BitConverter.ToInt32(s) == 0), Is.True);

        // parameterized non-"Item" properties -> [IndexerName]
        var indexerName = corlib.TopLevelTypes.FirstOrDefault(t =>
            t.FullName == "System.Runtime.CompilerServices.IndexerNameAttribute");
        Assert.That(indexerName, Is.Not.Null);
        Assert.That(indexerName!.BaseType?.FullName, Is.EqualTo("System.Attribute"));
        Assert.That(indexerName.Methods.Any(m => m.IsConstructor
            && m.Signature?.ParameterTypes is [CorLibTypeSignature]), Is.True);

        // assembly version -> [assembly: AssemblyVersion]
        var asmVersion = corlib.TopLevelTypes.FirstOrDefault(t =>
            t.FullName == "System.Reflection.AssemblyVersionAttribute");
        Assert.That(asmVersion, Is.Not.Null);
        Assert.That(asmVersion!.BaseType?.FullName, Is.EqualTo("System.Attribute"));
        Assert.That(asmVersion.Properties.Any(p => p.Name == "Version"), Is.True);
    }

    // An implflag surface injected onto an otherwise-fixture member must drive
    // the same materialization regardless of fixture content.
    [Test]
    public void InjectedImplFlagsMaterializeMethodImplSurface()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();

        var holder = new InjectedTypeAnalysisContext(
            app.AssembliesByName["UnityEngine.CoreModule"], "Tests", "ImplFlagHolder",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        holder.Methods.Add(new InjectedMethodAnalysisContext(holder, "Frozen",
            app.SystemTypes.SystemVoidType, R.MethodAttributes.Public | R.MethodAttributes.Static, [],
            defaultImplAttributes: R.MethodImplAttributes.AggressiveInlining));

        var assemblies = new AsmResolverDllOutputFormatEmpty().BuildAssemblies(app);
        var corlib = assemblies.First(a => a.Name == "mscorlib").ManifestModule!;

        Assert.That(corlib.TopLevelTypes.Any(t =>
            t.FullName == "System.Runtime.CompilerServices.MethodImplAttribute"), Is.True);
        Assert.That(corlib.TopLevelTypes.Any(t =>
            t.FullName == "System.Runtime.CompilerServices.MethodImplOptions"), Is.True);
    }

    // A System.Type attribute argument naming a nested type of a
    // global-namespace typedef must reuse that typedef, not materialize an
    // empty shell on top of it: the typedef carries Namespace=null while the
    // reference's empty namespace reads "", and an unnormalized typedef-side
    // compare misses the match.
    [Test]
    public void GlobalNamespaceNestedTypeAttributeArgumentReusesRealTypedef()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var assembly = app.AssembliesByName["UnityEngine.CoreModule"];

        var global = assembly.InjectType("", "GlobalData",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var inner = global.InjectNestedType("Inner", app.SystemTypes.SystemObjectType);
        global.InjectFieldContext("Marker", app.SystemTypes.SystemInt32Type,
            R.FieldAttributes.Public | R.FieldAttributes.Static);
        var attributeType = assembly.InjectType("Tests", "GlobalMarkerAttribute",
            app.SystemTypes.SystemAttributeType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        var constructor = attributeType.InjectMethodContext(".ctor",
            app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.SpecialName
                | R.MethodAttributes.RTSpecialName | R.MethodAttributes.HideBySig,
            app.SystemTypes.SystemTypeType);

        var holder = assembly.InjectType("Tests", "GlobalMarkerHolder",
            app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        holder.AnalyzeCustomAttributeData();
        holder.CustomAttributes ??= [];
        var attribute = new AnalyzedCustomAttribute(constructor);
        attribute.ConstructorParameters.Add(
            new CustomAttributeTypeParameter(inner, attribute,
                CustomAttributeParameterKind.ConstructorParam, 0));
        holder.CustomAttributes.Add(attribute);

        var assemblies = new AsmResolverDllOutputFormatEmpty().BuildAssemblies(app);
        var module = assemblies.First(a => a.Name == assembly.Name.ToString()).ManifestModule!;

        var typedefs = module.TopLevelTypes.Where(t => t.Name == "GlobalData").ToList();
        Assert.Multiple(() =>
        {
            Assert.That(typedefs, Has.Count.EqualTo(1),
                "the argument's declaring type must reuse the real typedef, not materialize a shell");
            Assert.That(typedefs.Single().Fields.Any(f => f.Name == "Marker"), Is.True,
                "the surviving typedef is the populated one, not an empty shell");
            Assert.That(typedefs.Single().NestedTypes.Count(t => t.Name == "Inner"), Is.EqualTo(1));
        });
    }
}
