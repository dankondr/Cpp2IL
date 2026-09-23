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
                ? SatisfyingGenericArgument(p, genericParameters[i])
                : p)
            .Select(p => p.ToTypeSignature());
        return memberReference.MakeGenericInstanceMethod(typeSignatures);
    }

    // il2cpp shares one instantiation across reference-type arguments and erases
    // the spec's generic arguments to System.Object; the real argument arrives
    // through an rgctx slot the emitted code cannot name. The verifier checks
    // instantiation arguments against the generic parameter's constraints, so an
    // erased argument is swapped for the nearest type the parameter itself
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
            .Select((a, i) => SatisfyingGenericArgument(a, baseDeclaring.GenericParameters[i]))
            .ToArray();
        return arguments.SequenceEqual(context.TypeGenericParameters)
            ? declaringType
            : baseDeclaring.MakeGenericInstanceType(arguments);
    }

    private static TypeAnalysisContext SatisfyingGenericArgument(TypeAnalysisContext argument, GenericParameterTypeAnalysisContext parameter)
    {
        if (SatisfiesConstraints(argument, parameter))
            return argument;
        foreach (var constraint in parameter.ConstraintTypes)
            if (SatisfiesConstraints(constraint, parameter))
                return constraint;
        var systemTypes = parameter.AppContext.SystemTypes;
        return parameter.Attributes.HasFlag(GenericParameterAttributes.NotNullableValueTypeConstraint)
            ? systemTypes.SystemInt32Type
            : systemTypes.SystemObjectType;
    }

    private static bool SatisfiesConstraints(TypeAnalysisContext argument, GenericParameterTypeAnalysisContext parameter)
    {
        var attributes = parameter.Attributes;
        if (attributes.HasFlag(GenericParameterAttributes.ReferenceTypeConstraint) && argument.IsValueType)
            return false;
        if (attributes.HasFlag(GenericParameterAttributes.NotNullableValueTypeConstraint) && !argument.IsValueType)
            return false;
        if (argument is GenericParameterTypeAnalysisContext argumentParameter)
            return parameter.ConstraintTypes.All(constraint =>
                argumentParameter.FullName == constraint.FullName
                || argumentParameter.ConstraintTypes.Any(own =>
                    own.FullName == constraint.FullName || own.IsAssignableTo(constraint)));
        return parameter.ConstraintTypes.All(argument.IsAssignableTo);
    }
}
