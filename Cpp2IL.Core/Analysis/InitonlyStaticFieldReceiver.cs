using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Utils.AsmResolver;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Read-side receivers through an initonly static. `ldsflda` on a readonly
/// static only verifies inside the declaring `.cctor`, so a read receiver
/// pushes the value instead (`ldsfld` + `ldfld` hops); the caller's leaf
/// `ldfld` then reads through the value on the stack. Store and address
/// consumers need `&amp;`, which has no legal spelling here - they keep the
/// `ldsflda` chain.
/// </summary>
internal static class InitonlyStaticFieldReceiver
{
    public static void PushValueChain(FieldReference field, MethodDefinition method)
    {
        var instructions = method.CilMethodBody!.Instructions;
        var receiverType = field.Containers[0].FieldType;
        instructions.Add(CilOpCodes.Ldsfld, field.Containers[0].ToFieldDescriptor());
        foreach (var container in field.Containers.Skip(1))
        {
            instructions.Add(CilOpCodes.Ldfld, IlGenerator.FieldDescriptorFor(container, receiverType));
            receiverType = IlGenerator.EmittedContainerFieldType(container, receiverType);
        }
    }
}
