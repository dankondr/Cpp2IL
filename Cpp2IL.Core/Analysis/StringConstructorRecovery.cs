using System.Buffers.Binary;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

internal static class StringConstructorRecovery
{
    internal static MethodAnalysisContext? Resolve(Instruction call, MethodAnalysisContext factory)
    {
        var app=factory.AppContext;
        var str=app.SystemTypes.SystemStringType;
        // IL2CPP's instance CreateString allocation shim ignores a null pseudo-this.
        // Only recover the proven char/count constructor pattern, not arbitrary factories.
        var receiver=call.OpCode==OpCode.Call?2:1;
        if(app.InstructionSet is not NewArmV8InstructionSet || call.IsVirtualDispatch
            || call.OpCode is not (OpCode.Call or OpCode.CallVoid)
            || call.Operands.Count!=receiver+3 || call.Operands[receiver] is not Immediate{Value:0}
            || !ReferenceEquals(factory.DeclaringType,str) || factory.IsStatic || factory.Name!="CreateString"
            || (factory.Attributes&MethodAttributes.MemberAccessMask)!=MethodAttributes.Private || !ReferenceEquals(factory.ReturnType,str)
            || !MatchesParameters(factory) || factory.RawBytes.Length!=12 || factory.UnderlyingPointer==0)
            return null;
        var bytes=factory.RawBytes.AsSpan();
        if(BinaryPrimitives.ReadUInt32LittleEndian(bytes)!=0x2a0103e0
            || BinaryPrimitives.ReadUInt32LittleEndian(bytes[4..])!=0x2a0203e1) return null;
        var branch=BinaryPrimitives.ReadUInt32LittleEndian(bytes[8..]);
        if((branch&0xfc000000)!=0x14000000)return null;
        var target=unchecked((ulong)((long)factory.UnderlyingPointer+8+((int)(branch<<6)>>4)));
        if(!str.Methods.Any(m=>m.Name=="Ctor"&&m.IsStatic&&ReferenceEquals(m.ReturnType,str)
            &&MatchesParameters(m)&&m.UnderlyingPointer==target&&target!=0))return null;
        var constructors=str.Methods.Where(m=>m.Name==".ctor"&&!m.IsStatic&&m.IsVoid
            &&(m.Attributes&MethodAttributes.MemberAccessMask)==MethodAttributes.Public&&MatchesParameters(m)).ToArray();
        return constructors is [{ } constructor]?constructor:null;
    }

    private static bool MatchesParameters(MethodAnalysisContext method)=>method.Parameters.Count==2
        &&ReferenceEquals(method.Parameters[0].ParameterType,method.AppContext.SystemTypes.SystemCharType)
        &&ReferenceEquals(method.Parameters[1].ParameterType,method.AppContext.SystemTypes.SystemInt32Type);
}
