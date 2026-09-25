using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using Cpp2IL.Core.Extensions;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Utils.AsmResolver;

public static class ContextToMethodDescriptor
{
    private static MethodDefinition GetMethodDefinition(this MethodAnalysisContext context)
    {
        var method = context.GetExtraData<MethodDefinition>("AsmResolverMethod") ?? throw new($"AsmResolver method not found in method analysis context for {context}");
        if (!AccessibilityExtensions.IsExternalRuntimeAssembly(context.DeclaringType?.DeclaringAssembly?.Name))
            MemberAccessibility.EnsureAccessible(method);
        return method;
    }

    private static MethodSignature ToMethodSignature(this MethodAnalysisContext context)
    {
        var returnType = context.ReturnType.ToTypeSignature();
        var parameters = context.Parameters.Select(p => p.ToTypeSignature());

        return context.IsStatic
            ? MethodSignature.CreateStatic(returnType, context.GenericParameters.Count, parameters)
            : MethodSignature.CreateInstance(returnType, context.GenericParameters.Count, parameters);
    }

    public static IMethodDescriptor ToMethodDescriptor(this MethodAnalysisContext context)
    {
        return context is ConcreteGenericMethodAnalysisContext concreteMethod
            ? concreteMethod.ToMethodDescriptor()
            : context.GetMethodDefinition();
    }

    public static IMethodDescriptor ToMethodDescriptor(this ConcreteGenericMethodAnalysisContext context)
    {
        var memberReference = new MemberReference(
            SatisfyingDeclaringType(context)?.ToTypeSignature().ToTypeDefOrRef(),
            context.Name,
            context.BaseMethodContext.ToMethodSignature());

        var methodGenericParameters = context.MethodGenericParameters;
        if (methodGenericParameters.Count == 0)
            return memberReference;

        var genericParameters = context.BaseMethodContext.GenericParameters;
        var typeSignatures = methodGenericParameters
            .Select((p, i) => i < genericParameters.Count
                ? SatisfyingGenericArgument(p, genericParameters[i], context.TypeGenericParameters, methodGenericParameters)
                : p)
            .Select(p => p.ToTypeSignature());
        return memberReference.MakeGenericInstanceMethod(typeSignatures);
    }

    // il2cpp shares one instantiation across reference-type arguments and erases
    // the spec's generic arguments to System.Object; the real argument arrives
    // through an rgctx slot the emitted code cannot name. The verifier checks
    // instantiation arguments against the generic parameter's constraints, so an
    // erased argument is swapped for the nearest closed type the parameter itself
    // permits - the constraint type for `where T : I`, a concrete primitive for
    // struct/unmanaged - keeping the instantiation honest and verifiable.
    private static TypeAnalysisContext? SatisfyingDeclaringType(ConcreteGenericMethodAnalysisContext context)
    {
        var declaringType = context.DeclaringType;
        if (declaringType is not GenericInstanceTypeAnalysisContext
            || context.BaseMethodContext.DeclaringType is not { } baseDeclaring
            || baseDeclaring.GenericParameters.Count != context.TypeGenericParameters.Count)
            return declaringType;

        var arguments = context.TypeGenericParameters
            .Select((a, i) => SatisfyingGenericArgument(a, baseDeclaring.GenericParameters[i], context.TypeGenericParameters, []))
            .ToArray();
        return arguments.SequenceEqual(context.TypeGenericParameters)
            ? declaringType
            : baseDeclaring.MakeGenericInstanceType(arguments);
    }

    private static TypeAnalysisContext SatisfyingGenericArgument(
        TypeAnalysisContext argument, GenericParameterTypeAnalysisContext parameter,
        IReadOnlyList<TypeAnalysisContext> typeArguments, IReadOnlyList<TypeAnalysisContext> methodArguments)
    {
        if (SatisfiesConstraints(argument, parameter, typeArguments, methodArguments))
            return argument;
        foreach (var constraint in parameter.ConstraintTypes)
        {
            // An F-bounded constraint (`where T : IMessage<T>`) still references a
            // generic parameter and can never serve as its own argument; one that
            // only names already-bound parameters (`where U : ModProcessorBase<T>`)
            // instantiates to a closed candidate that may honestly satisfy U.
            if (SubstitutedConstraint(constraint, typeArguments, methodArguments) is not { } substituted
                || ContainsGenericParameters(substituted))
                continue;
            if (SatisfiesConstraints(substituted, parameter, typeArguments, methodArguments))
                return substituted;
        }
        var systemTypes = parameter.AppContext.SystemTypes;
        return parameter.Attributes.HasFlag(GenericParameterAttributes.NotNullableValueTypeConstraint)
            ? systemTypes.SystemInt32Type
            : systemTypes.SystemObjectType;
    }

    internal static bool SatisfiesConstraints(
        TypeAnalysisContext argument, GenericParameterTypeAnalysisContext parameter,
        IReadOnlyList<TypeAnalysisContext> typeArguments, IReadOnlyList<TypeAnalysisContext> methodArguments)
    {
        var attributes = parameter.Attributes;
        if (argument is GenericParameterTypeAnalysisContext argumentParameter)
        {
            // A generic argument satisfies the callee's constraints through its
            // own declaration: `where U : struct` accepts T when T is itself
            // declared `where T : struct`, not by probing its runtime shape.
            var argumentAttributes = argumentParameter.Attributes;
            if (attributes.HasFlag(GenericParameterAttributes.ReferenceTypeConstraint)
                    && !argumentAttributes.HasFlag(GenericParameterAttributes.ReferenceTypeConstraint)
                || attributes.HasFlag(GenericParameterAttributes.NotNullableValueTypeConstraint)
                    && !argumentAttributes.HasFlag(GenericParameterAttributes.NotNullableValueTypeConstraint)
                || attributes.HasFlag(GenericParameterAttributes.DefaultConstructorConstraint)
                    && !argumentAttributes.HasFlag(GenericParameterAttributes.DefaultConstructorConstraint)
                    && !argumentAttributes.HasFlag(GenericParameterAttributes.NotNullableValueTypeConstraint))
                return false;
            foreach (var constraint in parameter.ConstraintTypes)
            {
                var substituted = SubstitutedConstraint(constraint, typeArguments, methodArguments);
                if (substituted == null)
                    continue;
                if (argumentParameter.FullName != substituted.FullName
                    && !argumentParameter.ConstraintTypes.Any(own =>
                        own.FullName == substituted.FullName || own.IsAssignableTo(substituted)))
                    return false;
            }
            return true;
        }
        if (attributes.HasFlag(GenericParameterAttributes.ReferenceTypeConstraint) && argument.IsValueType)
            return false;
        if (attributes.HasFlag(GenericParameterAttributes.NotNullableValueTypeConstraint) && !argument.IsValueType)
            return false;
        // `where T : new()` accepts a constructible type only - interfaces and
        // abstract classes can satisfy the type constraints yet must not be
        // substituted here.
        if (attributes.HasFlag(GenericParameterAttributes.DefaultConstructorConstraint)
            && !SatisfiesDefaultConstructor(argument))
            return false;
        foreach (var constraint in parameter.ConstraintTypes)
        {
            // The constraint is checked the way the verifier sees it: parameters
            // inside the constraint bind to the arguments actually supplied, so
            // `where T : IMessage<T>` on argument Foo tests Foo against
            // IMessage<Foo>.
            if (SubstitutedConstraint(constraint, typeArguments, methodArguments) is { } substituted
                && !argument.IsAssignableTo(substituted))
                return false;
        }
        return true;
    }

    private static bool SatisfiesDefaultConstructor(TypeAnalysisContext argument)
    {
        if (argument.IsValueType)
            return true;
        var definition = (argument as GenericInstanceTypeAnalysisContext)?.GenericType ?? argument;
        if (definition is not { IsAbstract: false, IsInterface: false })
            return false;
        // A class with no declared instance .ctor records still has the implicit
        // public default il2cpp may not list; declared ctors all being
        // parameterized is what removes it.
        var constructors = definition.Methods.Where(m => m is { IsStatic: false, Name: ".ctor" }).ToList();
        return constructors.Count == 0 || constructors.Any(m => m.Parameters.Count == 0);
    }

    private static TypeAnalysisContext? SubstitutedConstraint(
        TypeAnalysisContext constraint,
        IReadOnlyList<TypeAnalysisContext> typeArguments, IReadOnlyList<TypeAnalysisContext> methodArguments)
    {
        if (!ContainsGenericParameters(constraint))
            return constraint;
        try
        {
            var substituted = GenericInstantiation.Instantiate(constraint, typeArguments, methodArguments);
            return ContainsGenericParameters(substituted) ? null : substituted;
        }
        catch
        {
            // malformed or out-of-range parameter references can't be
            // instantiated - the constraint stays open and is skipped.
            return null;
        }
    }

    private static bool ContainsGenericParameters(TypeAnalysisContext type) => type switch
    {
        GenericParameterTypeAnalysisContext => true,
        GenericInstanceTypeAnalysisContext instance => instance.GenericArguments.Any(ContainsGenericParameters),
        SzArrayTypeAnalysisContext szArray => ContainsGenericParameters(szArray.ElementType),
        ArrayTypeAnalysisContext array => ContainsGenericParameters(array.ElementType),
        ByRefTypeAnalysisContext byRef => ContainsGenericParameters(byRef.ElementType),
        PointerTypeAnalysisContext pointer => ContainsGenericParameters(pointer.ElementType),
        _ => false,
    };
}
