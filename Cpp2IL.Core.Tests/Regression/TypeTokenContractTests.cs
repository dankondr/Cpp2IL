using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: IL emission — type tokens into native handle slots (#58, 4bc19667).
// A bare typeof(T) operand feeding a System.IntPtr slot is a native class handle:
// the honest emission is ldtoken + RuntimeTypeHandle::get_Value, not default(IntPtr).
public class TypeTokenContractTests
{
    [Test]
    public void BareTypeOperandIntoIntPtrSlotEmitsRealToken()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var stringType = app.SystemTypes.SystemStringType;
        var slot = new LocalVariable("slot", new Register(null, "slot"))
            { Type = app.SystemTypes.SystemIntPtrType };
        var module = new ModuleDefinition("TypeTokenContract.dll");
        foreach (var t in new[] { app.SystemTypes.SystemIntPtrType, app.SystemTypes.SystemVoidType,
                     app.SystemTypes.SystemObjectType, stringType })
            t.PutExtraData("AsmResolverType", new TypeDefinition(t.Namespace, t.Name,
                TypeAttributes.Public | (t.IsValueType ? TypeAttributes.Sealed | TypeAttributes.SequentialLayout : TypeAttributes.Class),
                t.IsValueType ? module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType") : null));
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, slot, stringType),
            new(1, OpCode.Return)], [slot]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldtoken
                    && i.Operand?.ToString()?.Contains("System.String") == true),
                Is.True, () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call
                    && i.Operand?.ToString()?.Contains("get_Value") == true),
                Is.True, "the handle slot carries the real token value, not a zero default");
        });
    }

}
