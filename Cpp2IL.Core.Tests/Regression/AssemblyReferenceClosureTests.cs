using System;
using System.IO;
using System.Linq;
using AsmResolver.PE;
using AsmResolver.PE.DotNet.Metadata;
using AsmResolver.PE.DotNet.Metadata.Tables;
using AsmResolver.DotNet;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Model.CustomAttributes;
using Cpp2IL.Core.OutputFormats;
using NUnit.Framework;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// castle-recovery#70 — a typeof() argument serializes into a custom-attribute
// blob as an assembly-qualified name string without ever materializing a
// TypeRef row, so the assembly it names would be missing from the emitted
// module's AssemblyRef table entirely.
public class AssemblyReferenceClosureTests
{
    [Test]
    public void BlobOnlyForeignTypeArgumentsDeclareTheirAssembly()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var hostAssembly = app.AssembliesByName["UnityEngine.CoreModule"];

        // Any assembly the host module never references works as the blob-only
        // foreign target; pick deterministically so the test stays stable.
        var foreignName = app.AssembliesByName.Keys
            .Where(n => n != hostAssembly.Name.ToString() && n != "mscorlib")
            .OrderBy(n => n, StringComparer.Ordinal)
            .First();
        var foreignType = app.AssembliesByName[foreignName].TopLevelTypes
            .First(t => t.Name != "<Module>");

        var attributeType = hostAssembly.InjectType("Tests", "ForeignTypeReferenceAttribute",
            app.SystemTypes.SystemAttributeType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        var constructor = attributeType.InjectMethodContext(".ctor",
            app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.SpecialName
                | R.MethodAttributes.RTSpecialName | R.MethodAttributes.HideBySig,
            app.SystemTypes.SystemTypeType);

        var holder = hostAssembly.InjectType("Tests", "ForeignTypeReferenceHolder",
            app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        holder.AnalyzeCustomAttributeData();
        holder.CustomAttributes ??= [];
        var attribute = new AnalyzedCustomAttribute(constructor);
        attribute.ConstructorParameters.Add(
            new CustomAttributeTypeParameter(foreignType, attribute, CustomAttributeParameterKind.ConstructorParam, 0));
        holder.CustomAttributes.Add(attribute);

        var outputDir = Path.Combine(Path.GetTempPath(), "Cpp2IL.Tests", Guid.NewGuid().ToString());
        try
        {
            new AsmResolverDllOutputFormatEmpty().DoOutput(app, outputDir);

            var hostModuleName = hostAssembly.Name.ToString() + ".dll";
            var hostSeenForeign = false;

            foreach (var dllPath in Directory.EnumerateFiles(outputDir, "*.dll"))
            {
                var image = PEImage.FromFile(dllPath);
                var tables = image.DotNetDirectory!.Metadata!.GetStream<TablesStream>();
                var assemblyRefCount = tables.GetTable<AssemblyReferenceRow>(TableIndex.AssemblyRef).Count;

                foreach (var typeRefRow in tables.GetTable<TypeReferenceRow>(TableIndex.TypeRef))
                {
                    // ResolutionScope is a coded index; tag 2 encodes an
                    // AssemblyRef-table RID that must exist in this module.
                    if ((typeRefRow.ResolutionScope & 0b11) == 2)
                    {
                        Assert.That(typeRefRow.ResolutionScope >> 2,
                            Is.InRange(1u, (uint)assemblyRefCount),
                            $"{Path.GetFileName(dllPath)}: TypeRef scope RID {typeRefRow.ResolutionScope >> 2} exceeds AssemblyRef table ({assemblyRefCount})");
                    }
                }

                var module = ModuleDefinition.FromImage(image);
                var referenceNames = module.AssemblyReferences
                    .Select(r => r.Name?.ToString())
                    .Where(n => n is not null)
                    .ToList();
                Assert.That(referenceNames, Is.Unique,
                    $"{Path.GetFileName(dllPath)}: duplicate AssemblyRef names");

                if (Path.GetFileName(dllPath) == hostModuleName)
                    hostSeenForeign = referenceNames.Contains(foreignName);
            }

            Assert.That(hostSeenForeign, Is.True,
                $"{hostModuleName} must declare an AssemblyRef for the assembly its attribute blob names");
        }
        finally
        {
            Directory.Delete(outputDir, true);
        }
    }
}

