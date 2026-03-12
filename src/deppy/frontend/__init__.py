"""deppy.frontend -- Sheaf-theoretic frontend for Python source analysis.

This package implements the frontend pipeline that transforms Python source
code into the sheaf-theoretic IR consumed by Algorithm 1 (Cover Synthesis).

The pipeline stages are:

1. **Module loading** (``module_loader``): Read Python files, resolve imports,
   build the module dependency graph.

2. **AST lowering** (``ast_visitor``): Walk the Python AST and produce
   ``IRModule`` containing ``IRFunction``, ``IRClass``, and ``IRStatement``
   nodes, each annotated with ``SourceSpan`` data.

3. **Type annotation parsing** (``type_annotation_parser``): Convert Python
   type annotations to ``deppy.types.base.TypeBase`` objects that seed
   carrier types at boundary observation sites.

4. **Decorator parsing** (``decorator_parser``): Recognize ``@deppy.*``
   decorators and produce ``ContractSeed`` / ``ProofSeed`` / ``InvariantSeed``
   dataclasses that contribute to boundary sections.

5. **IR representation** (``ir/``): Frozen dataclasses for all IR nodes,
   with a pretty-printer for debugging.

Usage::

    from deppy.frontend import lower_source, pretty_print

    ir = lower_source('''
        def f(x: int) -> int:
            return x + 1
    ''')
    print(pretty_print(ir))
"""

# IR types and pretty-printing
from deppy.frontend.ir import (
    IRModule,
    IRFunction,
    IRClass,
    IRParam,
    IRDecorator,
    IRStatement,
    IRExpr,
    IRAssign,
    IRAugAssign,
    IRReturn,
    IRIf,
    IRFor,
    IRWhile,
    IRRaise,
    IRTry,
    IRWith,
    IRAssert,
    IRExprStmt,
    IRDelete,
    IRName,
    IRConstant,
    IRCall,
    IRBinOp,
    IRSubscript,
    IRAttribute,
    IRTuple,
    IRList,
    IRDict,
    IRLambda,
    IRComprehension,
    IRIfExpr,
    pretty_print,
    pretty_print_stmt,
    pretty_print_expr,
    UNKNOWN_SPAN,
)

# AST lowering
from deppy.frontend.ast_visitor import (
    IRLowering,
    lower_source,
    lower_file,
)

# Type annotation parsing
from deppy.frontend.type_annotation_parser import (
    AnnotationParser,
    ForwardRef,
    TypeVarRef,
    parse_annotation,
    parse_annotation_string,
    parse_function_annotations,
)

# Decorator parsing
from deppy.frontend.decorator_parser import (
    ContractSeed,
    ProofSeed,
    DecreaseSeed,
    InvariantSeed,
    TransportSeed,
    GhostSeed,
    WitnessSeed,
    DecoratorSeed,
    DecoratorParser,
    SeedKind,
    parse_decorators,
    extract_contracts,
    extract_proof_seeds,
    extract_invariant_seeds,
    extract_transport_seeds,
)

# Module loading
from deppy.frontend.module_loader import (
    ModuleInfo,
    ImportInfo,
    ModuleLoader,
    load_module,
    load_package,
    load_source,
)

__all__ = [
    # IR
    "IRModule",
    "IRFunction",
    "IRClass",
    "IRParam",
    "IRDecorator",
    "IRStatement",
    "IRExpr",
    "IRAssign",
    "IRAugAssign",
    "IRReturn",
    "IRIf",
    "IRFor",
    "IRWhile",
    "IRRaise",
    "IRTry",
    "IRWith",
    "IRAssert",
    "IRExprStmt",
    "IRDelete",
    "IRName",
    "IRConstant",
    "IRCall",
    "IRBinOp",
    "IRSubscript",
    "IRAttribute",
    "IRTuple",
    "IRList",
    "IRDict",
    "IRLambda",
    "IRComprehension",
    "IRIfExpr",
    "pretty_print",
    "pretty_print_stmt",
    "pretty_print_expr",
    "UNKNOWN_SPAN",
    # AST lowering
    "IRLowering",
    "lower_source",
    "lower_file",
    # Type annotation parsing
    "AnnotationParser",
    "ForwardRef",
    "TypeVarRef",
    "parse_annotation",
    "parse_annotation_string",
    "parse_function_annotations",
    # Decorator parsing
    "ContractSeed",
    "ProofSeed",
    "DecreaseSeed",
    "InvariantSeed",
    "TransportSeed",
    "GhostSeed",
    "WitnessSeed",
    "DecoratorSeed",
    "DecoratorParser",
    "SeedKind",
    "parse_decorators",
    "extract_contracts",
    "extract_proof_seeds",
    "extract_invariant_seeds",
    "extract_transport_seeds",
    # Module loading
    "ModuleInfo",
    "ImportInfo",
    "ModuleLoader",
    "load_module",
    "load_package",
    "load_source",
]
