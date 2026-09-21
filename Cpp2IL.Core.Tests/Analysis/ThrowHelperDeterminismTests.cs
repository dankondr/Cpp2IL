using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Threading;
using System.Threading.Tasks;
using Cpp2IL.Core.Analysis;

namespace Cpp2IL.Core.Tests.Analysis;

public class ThrowHelperDeterminismTests
{
    [Test]
    public void WarmingDeepNodeMustNotBypassRootSearchBudget()
    {
        (string?, IReadOnlyList<ulong>) Inspect(ulong address) => address == 6
            ? ("NullReferenceException", []) : (null, [address + 1]);
        var cold = ThrowHelperRecovery.ResolveName(1, new(), Inspect);
        var warm = new ConcurrentDictionary<ulong, string?>();
        Assert.That(ThrowHelperRecovery.ResolveName(6, warm, Inspect), Is.EqualTo("NullReferenceException"));
        Assert.That(ThrowHelperRecovery.ResolveName(1, warm, Inspect), Is.EqualTo(cold));
        Assert.That(cold, Is.Null);
    }

    [Test]
    public void InProgressSearchMustNotPublishNullToAnotherRoot()
    {
        var cache = new ConcurrentDictionary<ulong, string?>();
        using var started = new ManualResetEventSlim();
        using var release = new ManualResetEventSlim();
        using var secondObserved = new ManualResetEventSlim();
        var visits = 0;
        (string?, IReadOnlyList<ulong>) Inspect(ulong address)
        {
            if (address == 2)
            {
                if (Interlocked.Increment(ref visits) == 2) secondObserved.Set();
                started.Set();
                if (!release.Wait(TimeSpan.FromSeconds(5))) throw new TimeoutException();
                return ("NullReferenceException", []);
            }
            if (address == 3) secondObserved.Set();
            return address == 1 ? (null, [2, 3]) : ("IndexOutOfRangeException", []);
        }
        var first = Task.Run(() => ThrowHelperRecovery.ResolveName(2, cache, Inspect));
        Assert.That(started.Wait(TimeSpan.FromSeconds(5)), Is.True);
        var second = Task.Run(() => ThrowHelperRecovery.ResolveName(1, cache, Inspect));
        // The old resolver reaches the fallback; the fixed resolver independently
        // reaches the still-blocked primary. Neither result depends on a timed race.
        try { Assert.That(secondObserved.Wait(TimeSpan.FromSeconds(5)), Is.True); }
        finally { release.Set(); }
        Assert.That(first.GetAwaiter().GetResult(), Is.EqualTo("NullReferenceException"));
        Assert.That(second.GetAwaiter().GetResult(), Is.EqualTo("NullReferenceException"));
    }

    [Test]
    public void CyclesStillAllowOtherBranchesToResolve()
    {
        (string?, IReadOnlyList<ulong>) Inspect(ulong address) => address switch
        {
            1 => (null, [2, 3]),
            2 => (null, [1]),
            _ => ("InvalidCastException", [])
        };
        Assert.That(ThrowHelperRecovery.ResolveName(1, new(), Inspect), Is.EqualTo("InvalidCastException"));
    }
}
