using System;
using System.Collections.Generic;
using System.Diagnostics.CodeAnalysis;
using System.Linq;
using System.Reflection;
using System.Text;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Logging;
using Cpp2IL.Core.Utils;
using LibCpp2IL;
using LibCpp2IL.Metadata;
using StableNameDotNet.Providers;

namespace Cpp2IL.Core.Model.Contexts;

/// <summary>
/// Represents one method within the application. Can be analyzed to attempt to reconstruct the function body.
/// </summary>
public class MethodAnalysisContext : HasGenericParameters, IMethodInfoProvider, ISIL.IOperand
{
    /// <summary>
    /// The underlying metadata for the method.
    ///
    /// Nullable iff this is a subclass.
    /// </summary>
    public readonly Il2CppMethodDefinition? Definition;

    /// <summary>
    /// The analysis context for the declaring type of this method.
    /// </summary>
    public readonly TypeAnalysisContext? DeclaringType;

    /// <summary>
    /// The address of this method as defined in the underlying metadata.
    /// </summary>
    public virtual ulong UnderlyingPointer => Definition?.MethodPointer ?? throw new("Subclasses of MethodAnalysisContext should override UnderlyingPointer");

    public ulong Rva => UnderlyingPointer == 0 ? 0 : AppContext.Binary.GetRva(UnderlyingPointer);

    /// <summary>
    /// The raw method body as machine code in the active instruction set.
    /// </summary>
    public BinarySlice RawBytes = BinarySlice.Empty;

    /// <summary>
    /// The first-stage-analyzed Instruction-Set-Independent Language Instructions.
    /// </summary>
    public List<Instruction>? ConvertedIsil;

    /// <summary>
    /// All ISIL local variables.
    /// </summary>
    public List<LocalVariable> Locals = [];

    /// <summary>
    /// Operands used as parameters.
    /// </summary>
    public List<ISIL.IOperand> ParameterOperands = [];

    /// <summary>
    /// The control flow graph for this method, if one is built.
    /// </summary>
    public ISILControlFlowGraph? ControlFlowGraph;

    /// <summary>
    /// Dominance info for the control flow graph.
    /// </summary>
    public DominatorInfo? DominatorInfo;

    /// <summary>
    /// The method's unwind-table entry when the binary provides one (ELF .eh_frame):
    /// its true extent and the call-site ranges that unwind to landing pads.
    /// </summary>
    public EhFunctionInfo? UnwindInfo;

    /// <summary>
    /// Landing-pad handler regions split out of <see cref="ConvertedIsil"/> by
    /// <see cref="Analysis.EhRegionPartition"/> - code only the unwinder enters.
    /// </summary>
    public List<LandingPadRegion> LandingPadRegions = [];

    internal List<Instruction>? ExceptionRegionInstructions;

    public List<string> AnalysisWarnings = [];

    public static int MaxMethodSizeBytes = 30000; // 30KB

    public List<ParameterAnalysisContext> Parameters = [];

    public List<LocalVariable> ParameterLocals = [];

    /// <summary>
    /// Does this method return void?
    /// </summary>
    public bool IsVoid => ReturnType == AppContext.SystemTypes.SystemVoidType;

    public bool IsStatic => (Attributes & MethodAttributes.Static) != 0;

    public bool IsVirtual => (Attributes & MethodAttributes.Virtual) != 0;

    public bool IsAbstract => (Attributes & MethodAttributes.Abstract) != 0;

    public bool IsNewSlot => (Attributes & MethodAttributes.NewSlot) != 0;

    public bool IsFinal => (Attributes & MethodAttributes.Final) != 0;

    protected override int CustomAttributeIndex => Definition?.customAttributeIndex ?? throw new("Subclasses of MethodAnalysisContext should override CustomAttributeIndex if they have custom attributes");

    public override AssemblyAnalysisContext CustomAttributeAssembly => DeclaringType?.DeclaringAssembly ?? throw new("Subclasses of MethodAnalysisContext should override CustomAttributeAssembly if they have custom attributes");

    public override string DefaultName => Definition?.Name ?? throw new("Subclasses of MethodAnalysisContext should override DefaultName");

    public string FullName => DeclaringType == null ? Name : $"{DeclaringType.FullName}::{Name}";

    public string FullNameWithSignature => $"{ReturnType.FullName} {FullName}({string.Join(", ", Parameters.Select(p => p.HumanReadableSignature))})";

    public virtual MethodAttributes DefaultAttributes => Definition?.Attributes ?? throw new($"Subclasses of MethodAnalysisContext should override {nameof(DefaultAttributes)}");

    public virtual MethodAttributes? OverrideAttributes { get; set; }

    public MethodAttributes Attributes
    {
        get => OverrideAttributes ?? DefaultAttributes;
        set => OverrideAttributes = value;
    }

    public virtual MethodImplAttributes DefaultImplAttributes => Definition?.MethodImplAttributes ?? throw new($"Subclasses of MethodAnalysisContext should override {nameof(DefaultImplAttributes)}");

    public virtual MethodImplAttributes? OverrideImplAttributes { get; set; }

    public MethodImplAttributes ImplAttributes
    {
        get => OverrideImplAttributes ?? DefaultImplAttributes;
        set => OverrideImplAttributes = value;
    }

    public MethodAttributes Visibility
    {
        get
        {
            return Attributes & MethodAttributes.MemberAccessMask;
        }
        set
        {
            Attributes = (Attributes & ~MethodAttributes.MemberAccessMask) | (value & MethodAttributes.MemberAccessMask);
        }
    }

    private List<GenericParameterTypeAnalysisContext>? _genericParameters;
    public override List<GenericParameterTypeAnalysisContext> GenericParameters
    {
        get
        {
            // Lazy load the generic parameters
            _genericParameters ??= Definition?.GenericContainer?.GenericParameters.Select(p => new GenericParameterTypeAnalysisContext(p, this)).ToList() ?? [];
            return _genericParameters;
        }
    }

    private ushort Slot => Definition?.slot ?? ushort.MaxValue;

    public virtual TypeAnalysisContext DefaultReturnType => AppContext.ResolveIl2CppType(Definition?.RawReturnType) ?? throw new($"Subclasses of MethodAnalysisContext should override {nameof(DefaultReturnType)}");

    public TypeAnalysisContext? OverrideReturnType { get; set; }

    //TODO Support custom attributes on return types (v31 feature)
    public TypeAnalysisContext ReturnType
    {
        get => OverrideReturnType ?? DefaultReturnType;
        set => OverrideReturnType = value;
    }

    public MethodAnalysisContext? BaseMethod
    {
        get
        {
            if (Definition == null)
                return null;

            var vtable = DeclaringType?.Definition?.VTable;
            if (vtable == null)
                return null;

            for (var i = 0; i < vtable.Length; ++i)
            {
                var vtableEntry = vtable[i];
                if (vtableEntry is null or { Type: not MetadataUsageType.MethodDef } || vtableEntry.AsMethod() != Definition)
                    continue;

                if (IsInterfaceSlot(this, i))
                {
                    continue;
                }

                var baseType = DeclaringType?.DefaultBaseType;
                while (baseType is not null)
                {
                    if (TryGetMethodForSlot(baseType, i, out var method))
                    {
                        return method;
                    }
                    baseType = baseType.DefaultBaseType;
                }
            }
            return null;
        }
    }

    private List<MethodAnalysisContext>? _overrides;

    /// <summary>
    /// The set of interface methods which this method explicitly overrides.
    /// </summary>
    public List<MethodAnalysisContext> Overrides
    {
        get
        {
            // Lazy load the overrides
            return _overrides ??= GetOverrides().ToList();
        }
    }

    private IEnumerable<MethodAnalysisContext> GetOverrides()
    {
        foreach (var method in GetVTableOverrides())
            yield return method;

        // Interface typedefs carry no vtable or interface-offset metadata, so
        // the walk above cannot recover the .override rows of explicit
        // implementations declared on the interface itself (default interface
        // implementations). Their member names encode the implemented member in
        // source form, e.g. "Namespace.IInterface<T>.Member".
        if (DeclaringType?.IsInterface == true)
            foreach (var method in GetExplicitInterfaceImplementations())
                yield return method;
    }

    private IEnumerable<MethodAnalysisContext> GetVTableOverrides()
    {
        if (Definition == null)
            yield break;

        var declaringTypeDefinition = DeclaringType?.Definition;
        if (declaringTypeDefinition == null)
            yield break;

        var vtable = declaringTypeDefinition.VTable;
        if (vtable == null)
            yield break;

        for (var i = 0; i < vtable.Length; ++i)
        {
            var vtableEntry = vtable[i];
            if (vtableEntry is null or { Type: not MetadataUsageType.MethodDef })
                continue;

            if (vtableEntry.AsMethod() != Definition)
                continue;

            // Interface inheritance
            foreach (var interfaceOffset in declaringTypeDefinition.InterfaceOffsets)
            {
                if (i >= interfaceOffset.offset)
                {
                    var interfaceTypeContext = AppContext.ResolveIl2CppType(interfaceOffset.Type);
                    var slot = i - interfaceOffset.offset;
                    if (TryGetMethodForSlot(interfaceTypeContext, slot, out var method) && !IsInterfaceSlot(method, slot))
                    {
                        yield return method;
                    }
                }
            }
        }
    }

    private IEnumerable<MethodAnalysisContext> GetExplicitInterfaceImplementations()
    {
        var lastDot = Name.LastIndexOf('.');
        if (lastDot <= 0 || lastDot == Name.Length - 1)
            yield break;

        var encodedInterfaceName = Name.Substring(0, lastDot);
        var memberName = Name.Substring(lastDot + 1);

        foreach (var interfaceContext in EnumerateImplementedInterfaces(DeclaringType))
        {
            if (!InterfaceNameMatches(interfaceContext, encodedInterfaceName))
                continue;

            var candidates = new List<MethodAnalysisContext>();
            var seenDefinitions = new HashSet<Il2CppMethodDefinition>();
            foreach (var member in EnumerateInterfaceMembers(interfaceContext))
            {
                if (member.Name != memberName || member.Parameters.Count != Parameters.Count)
                    continue;
                if (member.Definition != null && !seenDefinitions.Add(member.Definition))
                    continue;
                candidates.Add(member);
            }

            // Overload clones reachable through multiple base interfaces (a
            // generic interface inheriting its non-generic twin, for example)
            // are disambiguated by signature.
            if (candidates.Count > 1)
                candidates.RemoveAll(candidate => !SignatureEquivalent(candidate));
            if (candidates.Count != 1)
                continue;

            var match = candidates[0];
            if (interfaceContext is GenericInstanceTypeAnalysisContext genericInstance
                && match.DeclaringType?.GenericParameters.Count == genericInstance.GenericArguments.Count)
                yield return new ConcreteGenericMethodAnalysisContext(match, genericInstance.GenericArguments, []);
            else
                yield return match;
        }
    }

    private bool SignatureEquivalent(MethodAnalysisContext candidate)
    {
        for (var i = 0; i < Parameters.Count; i++)
        {
            if (!TypesEquivalent(Parameters[i].ParameterType, candidate.Parameters[i].ParameterType))
                return false;
        }

        return TypesEquivalent(ReturnType, candidate.ReturnType);
    }

    private static bool TypesEquivalent(TypeAnalysisContext a, TypeAnalysisContext b)
    {
        // Generic parameters spell differently on either side of the encoded
        // name ("IInterface<T>" declared on "IOther<T>" vs "TResult" on
        // "IInterface<TResult>"), so compare them by position, not name.
        if (a is GenericParameterTypeAnalysisContext || b is GenericParameterTypeAnalysisContext)
        {
            var aParameter = a as GenericParameterTypeAnalysisContext;
            var bParameter = b as GenericParameterTypeAnalysisContext;
            return aParameter?.Index == bParameter?.Index && aParameter?.Type == bParameter?.Type;
        }

        if (a is GenericInstanceTypeAnalysisContext || b is GenericInstanceTypeAnalysisContext)
        {
            var aInstance = a as GenericInstanceTypeAnalysisContext;
            var bInstance = b as GenericInstanceTypeAnalysisContext;
            return aInstance?.GenericType.FullName == bInstance?.GenericType.FullName
                && aInstance!.GenericArguments.Count == bInstance!.GenericArguments.Count
                && aInstance.GenericArguments.Zip(bInstance.GenericArguments).All(pair => TypesEquivalent(pair.First, pair.Second));
        }

        if (a is WrappedTypeAnalysisContext || b is WrappedTypeAnalysisContext)
        {
            var aWrapped = a as WrappedTypeAnalysisContext;
            var bWrapped = b as WrappedTypeAnalysisContext;
            return aWrapped?.GetType() == bWrapped?.GetType() && TypesEquivalent(aWrapped!.ElementType, bWrapped!.ElementType);
        }

        return a.FullName == b.FullName;
    }

    private static bool InterfaceNameMatches(TypeAnalysisContext interfaceContext, string encodedName)
    {
        if (StripGenericArgumentLists(encodedName) != SourceStyleName(interfaceContext))
            return false;

        var arity = interfaceContext is GenericInstanceTypeAnalysisContext genericInstance
            ? genericInstance.GenericArguments.Count
            : interfaceContext.GenericParameters.Count;
        return CountEncodedGenericArguments(encodedName) == arity;
    }

    /// <summary>
    /// The interface's name as it appears in a source-style explicit
    /// implementation member name: dotted namespace and declaring-type chain,
    /// each name stripped of any `` `N `` arity suffix or "&lt;...&gt;" argument list.
    /// </summary>
    private static string SourceStyleName(TypeAnalysisContext context)
    {
        var definitionContext = Unwrap(context);

        var names = new Stack<string>();
        for (var current = definitionContext; current != null; current = Unwrap(current.DeclaringType))
        {
            var name = current.Name;
            var terminator = name.IndexOfAny(['`', '<']);
            names.Push(terminator < 0 ? name : name[..terminator]);
        }

        var ns = definitionContext?.Namespace;
        return (string.IsNullOrEmpty(ns) ? "" : ns + ".") + string.Join('.', names);

        static TypeAnalysisContext? Unwrap(TypeAnalysisContext? context)
            => context is GenericInstanceTypeAnalysisContext genericInstance ? genericInstance.GenericType : context;
    }

    private static string StripGenericArgumentLists(string name)
    {
        var builder = new StringBuilder(name.Length);
        var depth = 0;
        foreach (var c in name)
        {
            if (c == '<')
                depth++;
            else if (c == '>')
                depth--;
            else if (depth == 0)
                builder.Append(c);
        }

        return builder.ToString();
    }

    private static int CountEncodedGenericArguments(string name)
    {
        // Encoded instantiations use source-style generics ("IFoo<A, B<C>>").
        // Only top-level commas delimit arguments; commas inside a nested
        // argument list or a function-pointer parameter list do not.
        var total = 0;
        var depth = 0;
        var parenDepth = 0;
        var commas = 0;
        var inGroup = false;
        foreach (var c in name)
        {
            switch (c)
            {
                case '<':
                    if (depth++ == 0)
                    {
                        inGroup = true;
                        commas = 0;
                    }
                    break;
                case '>':
                    if (--depth == 0 && inGroup)
                    {
                        total += commas + 1;
                        inGroup = false;
                    }
                    break;
                case '(':
                    if (depth > 0)
                        parenDepth++;
                    break;
                case ')':
                    if (parenDepth > 0)
                        parenDepth--;
                    break;
                case ',':
                    if (depth == 1 && parenDepth == 0)
                        commas++;
                    break;
            }
        }

        return total;
    }

    private static IEnumerable<TypeAnalysisContext> EnumerateImplementedInterfaces(TypeAnalysisContext? type)
    {
        var seen = new HashSet<TypeAnalysisContext>();
        var pending = new Stack<TypeAnalysisContext>(InterfacesOf(type));
        while (pending.Count > 0)
        {
            var current = pending.Pop();
            if (!seen.Add(current))
                continue;

            yield return current;

            foreach (var parent in InterfacesOf(current))
                pending.Push(parent);
        }

        static IEnumerable<TypeAnalysisContext> InterfacesOf(TypeAnalysisContext? context)
            => context switch
            {
                null => [],
                GenericInstanceTypeAnalysisContext genericInstance => genericInstance.GenericType.InterfaceContexts,
                _ => context.InterfaceContexts,
            };
    }

    private static IEnumerable<MethodAnalysisContext> EnumerateInterfaceMembers(TypeAnalysisContext interfaceContext)
    {
        var ownMethods = interfaceContext is GenericInstanceTypeAnalysisContext genericInstance
            ? genericInstance.GenericType.Methods
            : interfaceContext.Methods;
        foreach (var method in ownMethods)
            yield return method;

        foreach (var baseInterface in EnumerateImplementedInterfaces(interfaceContext))
        {
            var baseMethods = baseInterface is GenericInstanceTypeAnalysisContext genericBase
                ? genericBase.GenericType.Methods
                : baseInterface.Methods;
            foreach (var method in baseMethods)
                yield return method;
        }
    }

    private static bool IsInterfaceSlot(MethodAnalysisContext method, int slot)
    {
        var declaringTypeDefinition = method.DeclaringType?.Definition;
        if (declaringTypeDefinition == null)
            return false;

        foreach (var interfaceOffset in declaringTypeDefinition.InterfaceOffsets)
        {
            if (slot >= interfaceOffset.offset)
            {
                var interfaceTypeContext = method.AppContext.ResolveIl2CppType(interfaceOffset.Type);
                if (HasMethodForSlot(interfaceTypeContext, slot - interfaceOffset.offset))
                {
                    return true;
                }
            }
        }
        return false;
    }

    private static bool HasMethodForSlot(TypeAnalysisContext declaringType, int slot)
    {
        if (declaringType is GenericInstanceTypeAnalysisContext genericInstanceType)
        {
            return genericInstanceType.GenericType.Methods.Any(m => m.Slot == slot);
        }
        else
        {
            return declaringType.Methods.Any(m => m.Slot == slot);
        }
    }

    private static bool TryGetMethodForSlot(TypeAnalysisContext declaringType, int slot, [NotNullWhen(true)] out MethodAnalysisContext? method)
    {
        if (declaringType is GenericInstanceTypeAnalysisContext genericInstanceType)
        {
            var genericMethod = genericInstanceType.GenericType.Methods.FirstOrDefault(m => m.Slot == slot);
            if (genericMethod is not null)
            {
                method = new ConcreteGenericMethodAnalysisContext(genericMethod, genericInstanceType.GenericArguments, []);
                return true;
            }
        }
        else
        {
            var baseMethod = declaringType.Methods.FirstOrDefault(m => m.Slot == slot);
            if (baseMethod is not null)
            {
                method = baseMethod;
                return true;
            }
        }

        method = null;
        return false;
    }

    public MethodAnalysisContext(Il2CppMethodDefinition? definition, TypeAnalysisContext parent) : base(definition?.token ?? 0, parent.AppContext)
    {
        DeclaringType = parent;
        Definition = definition;

        if (Definition != null)
        {
            InitCustomAttributeData();

            for (var i = 0; i < Definition.InternalParameterData!.Length; i++)
            {
                var parameterDefinition = Definition.InternalParameterData![i];
                Parameters.Add(new(parameterDefinition, i, this));
            }
        }
    }

    public void EnsureRawBytes()
    {
        //Some abstract methods (on interfaces, no less) apparently have a body? Unity doesn't support default interface methods so idk what's going on here.
        //E.g. UnityEngine.Purchasing.AppleCore.dll: UnityEngine.Purchasing.INativeAppleStore::SetUnityPurchasingCallback on among us (itch.io build)
        if (UnderlyingPointer != 0 && !DefaultAttributes.HasFlag(MethodAttributes.Abstract))
        {
            RawBytes = AppContext.InstructionSet.GetRawBytesForMethod(this, this is AttributeGeneratorMethodAnalysisContext);

            if (RawBytes.Length == 0)
            {
                Logger.VerboseNewline("\t\t\tUnexpectedly got 0-byte method body for " + this + $". Pointer was 0x{UnderlyingPointer:X}", "MAC");
            }
        }
    }

    protected MethodAnalysisContext(ApplicationAnalysisContext context) : base(0, context)
    { }

    // ConvertedIsil is assigned early inside AnalyzeCore, so it cannot mark
    // completion: only this does. Recovery passes may ask for a member's lifted
    // body mid-pipeline (see InlinedMemberRecovery) - the lock serializes a
    // nested Analyze() against the parallel decompile's own call, and waiting
    // callers resume on the flag, not on the first writes.
    private volatile bool _analysisDone;

    // A body lifted by a summary ask (AnalyzeForMemberSummary) skips the
    // member-recovery pass, so a forced body can never itself force another -
    // two workers can then never wait on each other. The pass stays pending
    // and whichever Analyze() lands first runs it once.
    private bool _suppressMemberRecovery;
    private volatile bool _memberRecoveryPending;

    // The member-body facts InlinedMemberRecovery summarizes from, captured at
    // a fixed point in AnalyzeCore so a forced read and the body's own
    // pipeline see the same instructions.
    internal InlinedMemberRecovery.BodyFacts? MemberBodyFacts;

    [MemberNotNull(nameof(ConvertedIsil))]
    public void Analyze()
    {
        if (_analysisDone)
        {
            if (_memberRecoveryPending)
                RunDeferredMemberRecovery();
            ConvertedIsil ??= [];
            return;
        }

        lock (this)
        {
            if (!_analysisDone)
            {
                AnalyzeCore();
                _analysisDone = true;
            }
            RunDeferredMemberRecoveryCore();
            ConvertedIsil ??= [];
        }
    }

    // Lift the member for a member-body summary only. Called with this
    // monitor already held by the asking thread (Monitor.TryEnter), so the
    // lock is a same-thread re-entry: the suppression is what keeps the
    // nested pipeline from reaching back into the recovery pass.
    internal void AnalyzeForMemberSummary()
    {
        lock (this)
        {
            if (_analysisDone)
                return;
            _suppressMemberRecovery = true;
            AnalyzeCore();
            _analysisDone = true;
            _memberRecoveryPending = true;
            ConvertedIsil ??= [];
        }
    }

    private void RunDeferredMemberRecovery()
    {
        lock (this)
        {
            RunDeferredMemberRecoveryCore();
        }
    }

    private void RunDeferredMemberRecoveryCore()
    {
        if (!_memberRecoveryPending)
            return;
        _memberRecoveryPending = false;
        InlinedMemberRecovery.Run(this);
    }

    [MemberNotNull(nameof(ConvertedIsil))]
    private void AnalyzeCore()
    {
        if (MaxMethodSizeBytes != -1 && RawBytes.Length > MaxMethodSizeBytes)
        {
            Logger.WarnNewline($"Method {FullName} is too big ({RawBytes.Length} bytes), skipping analysis.");
            ConvertedIsil = [];
            return;
        }

        if (ConvertedIsil != null)
            return;

        if (UnderlyingPointer == 0)
        {
            ConvertedIsil = [];
            return;
        }

        ConvertedIsil = AppContext.InstructionSet.GetIsilFromMethod(this);
        ParameterOperands = AppContext.InstructionSet.GetParameterOperandsFromMethod(this);

        if (ConvertedIsil.Count == 0)
            return; //Nothing to do, empty function

        // Landing-pad handler code is not a continuation of the normal path; the unwind
        // tables name it, so move it out before the graph is built.
        EhRegionPartition.Partition(this);

        ControlFlowGraph = new ISILControlFlowGraph(ConvertedIsil);

        // Indirect jumps/calls should probably be resolved here before stack analysis

        StackAnalyzer.Analyze(this);

        // Dominator info must be computed after stack analysis, which removes unreachable/empty
        // blocks and would otherwise leave the dominator tree out of sync with the graph SSA sees.
        DominatorInfo = new DominatorInfo(ControlFlowGraph);

        // Create locals
        SsaForm.Build(this);
        LocalVariables.CreateAll(this);

        // Fold the explicit per-comparison flag arithmetic back into single relational comparisons,
        // then eliminate the now-dead flag computations. Both run in SSA form, where each
        // flag/temporary has a single, version-stable definition.
        FlagConditionRecovery.Run(this);
        // Stack-built boxes (Il2CppFakeBox) before the dead-code pass drops their value store.
        FakeBoxRecovery.Run(this);
        DeadCodeEliminator.Run(this);

        // PLT imports are named before call resolution can mistake one for a managed method.
        BlockMemoryImportRecovery.NameImports(this);

        // Resolve call targets, strings and getters, then run the combined type-propagation and
        // field-resolution fixpoint - all while still in SSA form, so every local is
        // single-assignment and a type, once known, is stable for that value.
        MetadataResolver.ResolveAll(this);

        // Resolve KeyFunctionAddress calls, then collect what removing the write barriers left dead.
        KeyFunctionRecovery.Run(this);
        DeadCodeEliminator.Run(this);

        // Delete any il2cpp_codegen_initialize_runtime_metadata/il2cpp_codegen_initialize_method
        MetadataInitGuardRemover.Run(this);

        // Delete inlined GC write barriers
        WriteBarrierRecovery.Run(this);

        InjectedCheckRemover.Run(this);

        var finishInterfaceDispatchRecovery = InterfaceDispatchRecovery.Run(this);

        LocalVariables.ResolveTypesAndFields(this);

        // Runtime class targets become available only after type resolution.
        KeyFunctionRecovery.Run(this);
        FakeBoxRecovery.ResolveTypes(this);
        ArrayRecovery.RecoverObjectFieldAddresses(this);

        // Needs the MethodInfo* receivers typed, so runs after resolution unlike the class-init guards
        MetadataInitGuardRemover.RunRgctx(this);

        MetadataInitGuardRemover.RewriteUnguardedInits(this);

        // Needs type resolved for delegate locals
        DelegateInvokeRecovery.Run(this);
        // Needs klass/method-info locals typed, so runs after the same resolution
        TailCallRecovery.Run(this);
        BooleanFlagSimplifier.Run(this);
        DeadCodeEliminator.Run(this);
        finishInterfaceDispatchRecovery?.Invoke();

        // A frame cell holding a copy of an address-taken struct's field is that field's storage;
        // read it as the field before copies are forwarded.
        FrameStructFieldReads.Run(this);

        // Copy/constant propagation belongs in SSA, where one definition dominates all uses and phis
        // make joins explicit, so forwarding a value is an unconditional global substitution.
        SsaSimplifier.Run(this);

        // Folding a constant exposes more to propagate
        for (var i = 0; i < 8 && ConstantFolder.Run(this); i++)
            SsaSimplifier.Run(this);

        // SSA propagation can expose a trailing concrete MethodInfo* only after
        // the initial type-resolution fixpoint. Give the normal resolver one more
        // chance before SSA is removed (shared generic thunks depend on this).
        MetadataResolver.ResolveCallsViaMethodInfo(this);
        MetadataInitGuardRemover.Run(this);
        MetadataInitGuardRemover.RewriteUnguardedInits(this);

        InternalCallGuardRemover.Run(this);
        ArrayRecovery.RecoverAccesses(this);
        KeyFunctionRecovery.Run(this);

        SsaForm.Remove(this);

        // Phi removal leaves a copy per merged version, most of which can share one local
        CopyCoalescer.Run(this);

        // Now out of SSA: clean up the per-edge copies that phi removal introduced (a local can have
        // several definitions merging at a join here, so this pass propagates conservatively), then
        // drop dead locals.
        Simplifier.Simplify(this);

        // Fix float literals
        FloatLiteralRecovery.Run(this);

        // Runs late so array and runtime-class operands reach their helpers after copy propagation has inlined them.
        ArrayRecovery.Run(this);
        // Needs the array accesses recovered, and a T[,] index is only recovered while its bounds check proves it.
        Il2CppCheckRecovery.Run(this);
        LocalVariables.ResolveLateGeneratedTypes(this);
        KeyFunctionRecovery.Run(this);

        LocalVariables.TypeAddressedLocals(this);

        ConstantBranchFolder.Run(this);

        // Canonicalize `x ?? (x = v)` cache-store merges to a single post-join
        // read so the guarded block stays a bare store, the shape ILSpy's
        // cached-`??` transforms fold.
        CoalesceStoreRecovery.Run(this);

        // Near-last, as it depends on the final block layout
        EqualityBranchInverter.Run(this);

        // Every call that was going to resolve now has. Any argument registers it ended up
        // not using are just keeping their definitions alive, so drop them.
        ReferenceCastRecovery.Run(this);
        ReferenceCompareExchangeRecovery.Run(this);
        CallArgumentTrimmer.Run(this);
        // Struct arguments the ABI passes as an address are spelled as the value they name.
        ByReferenceArgumentRecovery.Run(this);
        InlinedListClearRecovery.Run(this);
        InlinedListAddRecovery.Run(this);

        // Member accesses an inlined member left behind - a store into a field the
        // caller cannot name, or a read behind a private container - map back to
        // the accessible member (ctor, setter, factory, getter) whose own lifted
        // body is exactly that access. The body facts are captured first, at
        // this fixed point, so a member summarized mid-pipeline and one read
        // after its own analysis describe the same body.
        InlinedMemberRecovery.CaptureBodyFacts(this);
        if (!_suppressMemberRecovery)
            InlinedMemberRecovery.Run(this);

        // ARM64 ELF block-memory imports (`bl` into a GOT veneer whose relocated symbol
        // is memcpy/memset/memmove) become dedicated block ops, scalar imports get a
        // managed equivalent or their symbol name. This runs last so it sees the
        // final operand forms - after copy forwarding, SSA removal and local
        // coalescing - which is what emission will see too, and destination/provenance
        // checks cannot drift between the two.
        BlockMemoryImportRecovery.Run(this);

        // The stack protector's canary compare + __stack_chk_fail call survives as
        // dead machinery once imports are named; excise it while dead-code
        // elimination still runs below to sweep the freed operands.
        StackProtectorRecovery.Run(this);

        // Some helpers only acquire their canonical key-function name in late recovery. This final
        // cleanup prevents runtime-only metadata/class-init helpers from reaching managed IL.
        MetadataInitGuardRemover.Run(this);
        MetadataInitGuardRemover.RewriteUnguardedInits(this);
        DeadCodeEliminator.Run(this);
        DeadCodeEliminator.RemoveReturnsAfterThrow(ControlFlowGraph);

        // Ref-alias copies that survive every earlier pass spell `ref` binds against ref
        // parameters, which C# cannot express - so their uses read the shared root instead.
        ByrefAliasForwarding.Run(this);

        // Late passes still write the reads a packed struct's register carries:
        // EqualityBranchInverter rewrites comparison conditions, and addressed
        // stack locals only gained their stored type at TypeAddressedLocals. One
        // more pass out of SSA rewrites what surfaced here. Container hops - the
        // `ldflda` step on the root - land here, where emitted local types are
        // final and no later pass can restamp them.
        PackedRegisterFields.Run(this, finalPass: true);

        // A packed read projected only here, on a local whose emitted type could
        // not be proven inside the fixpoint, can still carry a leaf the caller
        // cannot spell: the accessor rewrite above has already run, so one more
        // pass maps such reads onto their returned-field accessors.
        if (!_suppressMemberRecovery)
            InlinedMemberRecovery.Run(this);

        // A bounds-checked indexed read of a constant table is LLVM's
        // switch-to-lookup-table lowering; recover it to a real switch once
        // local types and operand forms are final.
        SwitchLookupTableRecovery.Run(this);

        LocalVariables.RemoveUnused(this);

    }

    public void AddWarning(string warning) => AnalysisWarnings.Add(warning);

    public void ReleaseAnalysisData()
    {
        ConvertedIsil = null;
        ExceptionRegionInstructions = null;
        ControlFlowGraph = null;
        // MemberBodyFacts stays: it is the whole point of the facts - a way to
        // read a member body without holding its pipeline data. Clearing it
        // would make a member ask's answer depend on whether it lands before
        // or after this method's emit.
        DominatorInfo = null;
    }

    public ConcreteGenericMethodAnalysisContext MakeGenericInstanceMethod(params IEnumerable<TypeAnalysisContext> methodGenericParameters)
    {
        if (this is ConcreteGenericMethodAnalysisContext methodOnGenericInstanceType)
        {
            return new ConcreteGenericMethodAnalysisContext(methodOnGenericInstanceType.BaseMethodContext, methodOnGenericInstanceType.TypeGenericParameters, methodGenericParameters);
        }
        else
        {
            return new ConcreteGenericMethodAnalysisContext(this, [], methodGenericParameters);
        }
    }

    public ConcreteGenericMethodAnalysisContext MakeConcreteGenericMethod(IEnumerable<TypeAnalysisContext> typeGenericParameters, IEnumerable<TypeAnalysisContext> methodGenericParameters)
    {
        if (this is ConcreteGenericMethodAnalysisContext)
        {
            throw new InvalidOperationException($"Attempted to make a {nameof(ConcreteGenericMethodAnalysisContext)} concrete: {this}");
        }
        else
        {
            return new ConcreteGenericMethodAnalysisContext(this, typeGenericParameters, methodGenericParameters);
        }
    }

    public override string ToString() => $"Method: {FullName}";

    #region StableNameDot implementation

    ITypeInfoProvider IMethodInfoProvider.ReturnType =>
        Definition!.RawReturnType!.ThisOrElementIsGenericParam()
            ? new GenericParameterTypeInfoProviderWrapper(Definition.RawReturnType!.GetGenericParamName())
            : TypeAnalysisContext.GetSndnProviderForType(AppContext, Definition!.RawReturnType);

    IEnumerable<IParameterInfoProvider> IMethodInfoProvider.ParameterInfoProviders => Parameters;

    string IMethodInfoProvider.MethodName => Name;

    MethodAttributes IMethodInfoProvider.MethodAttributes => Attributes;

    MethodSemantics IMethodInfoProvider.MethodSemantics
    {
        get
        {
            if (DeclaringType != null)
            {
                //This one is a bit trickier, as il2cpp doesn't use semantics.
                foreach (var prop in DeclaringType.Properties)
                {
                    if (prop.Getter == this)
                        return MethodSemantics.Getter;
                    if (prop.Setter == this)
                        return MethodSemantics.Setter;
                }

                foreach (var evt in DeclaringType.Events)
                {
                    if (evt.Adder == this)
                        return MethodSemantics.AddOn;
                    if (evt.Remover == this)
                        return MethodSemantics.RemoveOn;
                    if (evt.Invoker == this)
                        return MethodSemantics.Fire;
                }
            }

            return 0;
        }
    }

    #endregion
}
