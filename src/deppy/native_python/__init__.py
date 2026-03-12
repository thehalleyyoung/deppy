"""Native Python analysis for the sheaf-descent semantic typing system.

This package provides Python-specific analyses that extract semantic
information from Python's runtime constructs -- classes, protocols,
exceptions, comprehensions, generators, and decorators.

Modules
-------
class_analyzer
    Constructor analysis, field initialization, protocol conformance.
protocol_inference
    Infer structural protocols from usage patterns.
exception_analyzer
    Exception flow analysis: raised, caught, propagation paths.
comprehension_analyzer
    List/dict/set comprehension and generator expression semantics.
generator_analyzer
    Generator and iterator protocol analysis.
decorator_analyzer
    Decorator chain effect analysis.
"""

from deppy.native_python.class_analyzer import (
    ClassAnalysisResult,
    ClassAnalyzer,
    FieldInfo,
    MethodInfo,
    ProtocolConformance,
)

from deppy.native_python.protocol_inference import (
    AttributeUsage,
    BuiltinUsage,
    InferredProtocol,
    MethodUsage,
    OperatorUsage,
    ProtocolInferrer,
)

from deppy.native_python.exception_analyzer import (
    ExceptionAnalyzer,
    ExceptionFlowResult,
    HandlerInfo,
    RaiseInfo,
)

from deppy.native_python.comprehension_analyzer import (
    ComprehensionAnalyzer,
    ComprehensionInfo,
    ComprehensionKind,
    FilterInfo,
    GeneratorClauseInfo,
)

from deppy.native_python.generator_analyzer import (
    GeneratorAnalyzer,
    GeneratorInfo,
    SendInfo,
    YieldInfo,
)

from deppy.native_python.decorator_analyzer import (
    DecoratorAnalyzer,
    DecoratorEffect,
    DecoratorStackResult,
)

__all__ = [
    # class_analyzer
    "ClassAnalysisResult",
    "ClassAnalyzer",
    "FieldInfo",
    "MethodInfo",
    "ProtocolConformance",
    # protocol_inference
    "AttributeUsage",
    "BuiltinUsage",
    "InferredProtocol",
    "MethodUsage",
    "OperatorUsage",
    "ProtocolInferrer",
    # exception_analyzer
    "ExceptionAnalyzer",
    "ExceptionFlowResult",
    "HandlerInfo",
    "RaiseInfo",
    # comprehension_analyzer
    "ComprehensionAnalyzer",
    "ComprehensionInfo",
    "ComprehensionKind",
    "FilterInfo",
    "GeneratorClauseInfo",
    # generator_analyzer
    "GeneratorAnalyzer",
    "GeneratorInfo",
    "SendInfo",
    "YieldInfo",
    # decorator_analyzer
    "DecoratorAnalyzer",
    "DecoratorEffect",
    "DecoratorStackResult",
]
