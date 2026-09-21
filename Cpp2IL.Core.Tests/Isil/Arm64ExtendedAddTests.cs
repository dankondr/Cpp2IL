using System.Linq;
using System.Reflection;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;

namespace Cpp2IL.Core.Tests.Isil;

public class Arm64ExtendedAddTests
{
    [Test]
    public void ExtendedAddRetainsSignedWordExtensionAndScale()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Test",
            app.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, []);
        // add x8, x8, w9, sxtw #4 ; ret
        var native = Disassembler.Disassemble(new byte[] { 0x08, 0xd1, 0x29, 0x8b, 0xc0, 0x03, 0x5f, 0xd6 }, 0).ToList();
        var il = new NewArmV8InstructionSet().ConvertInstructions(native, context);

        Assert.That(il.Select(i => i.OpCode.ToString()), Is.EqualTo(new[] { "SignExtend32", "ShiftLeft", "Add", "Return" }));
        Assert.That(il[1].Operands[2], Is.EqualTo(new Immediate(4)));
        Assert.That(il[0].Operands[1], Is.EqualTo(new Register(null, "X9")));
        Assert.That(il[2].Operands[2], Is.EqualTo(il[1].Operands[0]));
    }
}
