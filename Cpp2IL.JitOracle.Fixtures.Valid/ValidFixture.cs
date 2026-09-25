using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

namespace JitOracleFixtures.Valid
{
    public static class VectorMethods
    {
        public static int Add(int a, int b) => a + b;

        public static string Cat(string s, int n) => s + n;

        public static long BigXor(long x) => x ^ 0x10;

        public static float Half(float f) => f * 0.5f;

        // Open generic: skipped by prepare-only enumeration.
        public static T Echo<T>(T value) => value;

        // P/Invoke: skipped.
        [DllImport("user32.dll", EntryPoint = "GetDC")]
        public static extern int GetDc(int hwnd);

        // Internal call: skipped.
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern int ICall();
    }

    public abstract class AbstractBase
    {
        public abstract int Missing();
    }

    public sealed class Concrete : AbstractBase
    {
        public override int Missing() => 3;

        public int Instance() => 7;

        public static int StaticOk() => 5;
    }
}
