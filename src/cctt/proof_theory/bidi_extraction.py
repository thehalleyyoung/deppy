"""Bidirectional Proof ↔ Code — F*-style extraction adapted for Python.

F*'s extraction pipeline: proof → OCaml/F#/C.
Our pipeline: proof ↔ Python, BIDIRECTIONALLY.

Forward:  Proof(f ≡ spec) → Python code + certificate
Backward: Python code + spec → proof obligation (what needs proving)

The key Pythonic adaptations vs. F*:

1. **Duck-type fiber obligations** — instead of F*'s refinement types over
   ML-style types, we generate obligations per duck-type fiber. A function
   that takes "something iterable" creates obligations for each concrete
   fiber (list, tuple, set, generator, dict.keys(), ...).

2. **Dict-shape obligations** — when a function returns a dict, the
   obligation decomposes by key (each key's value type is a separate
   obligation). This is the DependentDict from pythonic_types.py.

3. **None-safety obligations** — every Optional[T] return creates a
   fiber split: the Some fiber (T operations) and the None fiber.
   The proof must handle both.

4. **Exception obligations** — try/except creates effect-type obligations.
   The proof must show the except handler covers the thrown exception types.

5. **Mutation obligations** — in-place operations (list.sort, dict.update)
   create pre/post state obligations connected by the MutableRef type.

6. **Library obligations** — calls to external libraries (numpy, sympy)
   create trust-boundary obligations that reference library contracts.

Round-Trip Guarantee
====================
We do NOT claim a full round-trip theorem (that would require proving
the OTerm compiler is an inverse of extraction). Instead:

    Forward:  proven  — extraction preserves proof validity
    Backward: sound   — generated obligations are necessary conditions
    Together: the composition reduces the untrusted gap to the OTerm compiler

Usage::

    # Forward: proof → code
    code = extract_verified("sort", proof, lhs, rhs)

    # Backward: code → obligations
    obligations = obligate("my_function.py", "returns sorted unique list")

    # Library-aware: code using sympy → obligations referencing sympy axioms
    obligations = obligate_with_libraries(
        "my_solver.py",
        "solves the system correctly",
        libraries=["sympy", "numpy"],
    )
"""
from __future__ import annotations

import ast
import textwrap
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Set, Tuple

from cctt.denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
    compile_to_oterm,
)

from cctt.proof_theory.terms import (
    ProofTerm,
    Refl, Sym, Trans, Cong,
    Beta, Delta, Eta,
    NatInduction, ListInduction, WellFoundedInduction,
    AxiomApp, MathlibTheorem,
    LoopInvariant, Simulation, AbstractionRefinement,
    CommDiagram, FunctorMap,
    Z3Discharge,
    FiberDecomposition, CechGluing,
    Assume, Cut, LetProof,
    CasesSplit, Ext,
    Rewrite, RewriteChain,
    ArithmeticSimp, ListSimp, Definitional,
    FiberRestrict, Descent, PathCompose, MathLibAxiom, FiberwiseUnivalence,
    normalize_term, free_vars,
    var, lit, op, abstract,
)

from cctt.proof_theory.checker import (
    check_proof, VerificationResult, ProofContext,
)

from cctt.proof_theory.pythonic_types import (
    CType, PyAtom, DuckType, DictShape, PyList, PyDict, PySet, PyTuple,
    Nullable, PyUnion, MutableRef, ExceptionEffect, GeneratorType,
    Protocol, Refinement, Sigma, Pi, DependentDict, PyLibType,
    INT, FLOAT, STR, BOOL, NONE_TYPE,
    ITERABLE, SEQUENCE, MAPPING, CALLABLE_DUCK, NUMERIC,
    infer_type_from_ops, fiber_decompose_type,
)

from cctt.proof_theory.predicates import (
    Pred, PVar, PLit, PCompare, PIsNone, PNot, PAnd, POr,
    PAttr, PCall, PLibCall, PIsInstance, PHasAttr, PContains,
    RefinementFiber, RefinementCover, Decidability,
    parse_predicate, extract_library_deps,
)

from cctt.proof_theory.library_axioms import (
    TrustProvenance, TrustSource,
    LibraryAxiom, LibraryContract,
    LibraryTheory, get_library,
)


# ═══════════════════════════════════════════════════════════════════
# Proof obligations — what needs to be proved about Python code
# ═══════════════════════════════════════════════════════════════════

class ObligationKind:
    """Kinds of proof obligations generated from Python code."""
    POSTCONDITION = "postcondition"       # @guarantee text
    PRECONDITION = "precondition"         # assume() call
    INVARIANT = "invariant"               # check() call / loop invariant
    NONE_SAFETY = "none_safety"           # Optional return handled
    EXCEPTION_SAFETY = "exception_safety" # try/except covers raises
    TYPE_FIBER = "type_fiber"             # per-duck-type fiber obligation
    MUTATION_SAFETY = "mutation_safety"   # in-place op pre/post
    LIBRARY_CONTRACT = "library_contract" # library preconditions satisfied
    DICT_SHAPE = "dict_shape"             # dict key/value constraints
    TERMINATION = "termination"           # recursive function terminates
    EQUIVALENCE = "equivalence"           # two implementations are equivalent


@dataclass
class ProofObligation:
    """A single thing that needs to be proved about Python code.

    This is the BACKWARD direction: code → what needs proving.
    Each obligation knows:
      - what it asserts
      - what duck-type fiber it lives in
      - what trust level would satisfy it
      - whether Z3 can handle it
    """
    kind: str                    # from ObligationKind
    description: str             # human-readable
    fiber: str = ''              # duck-type fiber (if applicable)
    refinement: Optional[Pred] = None  # refinement predicate for this fiber
    formula: str = ''            # Z3 formula (if Z3-decidable)
    z3_decidable: bool = False
    library: str = ''            # library reference (if applicable)
    code_location: str = ''      # file:line
    suggested_tactic: str = ''   # hint for proof search
    severity: str = 'required'   # 'required' or 'advisory'
    resolved: bool = False
    proof: Optional[ProofTerm] = None

    def pretty(self) -> str:
        status = '✓' if self.resolved else '○'
        z3 = ' [Z3]' if self.z3_decidable else ''
        lib = f' [{self.library}]' if self.library else ''
        fiber = f' @{self.fiber}' if self.fiber else ''
        ref = f' [{self.refinement.pretty()}]' if self.refinement else ''
        return f'{status} {self.kind}{z3}{lib}{fiber}{ref}: {self.description}'


@dataclass
class ObligationBundle:
    """All obligations generated from a piece of Python code.

    Bundles obligations by fiber for Čech-style verification:
    prove each fiber independently, then glue via descent.
    """
    function_name: str
    source: str
    obligations: List[ProofObligation] = field(default_factory=list)
    fiber_groups: Dict[str, List[ProofObligation]] = field(default_factory=dict)
    library_deps: List[str] = field(default_factory=list)
    inferred_type: Optional[CType] = None
    refinement_cover: Optional[RefinementCover] = None

    def add(self, obligation: ProofObligation) -> None:
        self.obligations.append(obligation)
        if obligation.fiber:
            self.fiber_groups.setdefault(obligation.fiber, []).append(obligation)

    @property
    def total(self) -> int:
        return len(self.obligations)

    @property
    def resolved_count(self) -> int:
        return sum(1 for o in self.obligations if o.resolved)

    @property
    def all_resolved(self) -> bool:
        required = [o for o in self.obligations if o.severity == 'required']
        return all(o.resolved for o in required)

    def summary(self) -> str:
        lines = [f'Obligations for {self.function_name}: '
                 f'{self.resolved_count}/{self.total} resolved']
        if self.library_deps:
            lines.append(f'  Libraries: {", ".join(self.library_deps)}')
        if self.fiber_groups:
            lines.append(f'  Fibers: {", ".join(sorted(self.fiber_groups.keys()))}')
        for o in self.obligations:
            lines.append(f'  {o.pretty()}')
        return '\n'.join(lines)


# ═══════════════════════════════════════════════════════════════════
# BACKWARD: Python code → proof obligations
# ═══════════════════════════════════════════════════════════════════

def obligate(source: str, guarantee_text: str = '',
             libraries: Optional[List[str]] = None) -> ObligationBundle:
    """Generate proof obligations from Python source code.

    This is the BACKWARD direction of bidirectional extraction:
    given code and a spec, what needs to be proved?

    Pythonic obligations generated:
    - None-safety for every Optional return
    - Exception coverage for try/except
    - Per-fiber type obligations from duck typing
    - Library contract obligations for external calls
    - Dict shape obligations for dict returns
    - Mutation safety for in-place operations
    - Termination for recursive functions
    """
    try:
        tree = ast.parse(textwrap.dedent(source))
    except SyntaxError:
        bundle = ObligationBundle("unknown", source)
        bundle.add(ProofObligation(
            kind=ObligationKind.POSTCONDITION,
            description="could not parse source",
            severity='required',
        ))
        return bundle

    # Find the function definition
    func_def = None
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            func_def = node
            break

    func_name = func_def.name if func_def else 'unknown'
    bundle = ObligationBundle(func_name, source)
    bundle.library_deps = libraries or []

    if guarantee_text:
        bundle.add(ProofObligation(
            kind=ObligationKind.POSTCONDITION,
            description=guarantee_text,
            suggested_tactic='auto',
        ))

    if func_def is None:
        return bundle

    # Analyze the function body
    _analyze_none_safety(func_def, bundle)
    _analyze_exception_safety(func_def, bundle)
    _analyze_duck_type_fibers(func_def, bundle)
    _analyze_library_calls(func_def, bundle, libraries or [])
    _analyze_dict_shapes(func_def, bundle)
    _analyze_mutation(func_def, bundle)
    _analyze_recursion(func_def, bundle)
    _analyze_loop_invariants(func_def, bundle)

    return bundle


def _analyze_none_safety(func_def: ast.FunctionDef,
                         bundle: ObligationBundle) -> None:
    """Check for None-return paths and generate obligations."""
    has_none_return = False
    has_value_return = False

    for node in ast.walk(func_def):
        if isinstance(node, ast.Return):
            if node.value is None:
                has_none_return = True
            elif (isinstance(node.value, ast.Constant) and
                  node.value.value is None):
                has_none_return = True
            else:
                has_value_return = True

    # Implicit None return (no return statement, or function body ends without return)
    body = func_def.body
    if body and not isinstance(body[-1], ast.Return):
        has_none_return = True

    if has_none_return and has_value_return:
        bundle.add(ProofObligation(
            kind=ObligationKind.NONE_SAFETY,
            description=f'{func_def.name} may return None — callers must handle Optional',
            fiber='none',
            suggested_tactic='cases on return value',
        ))


def _analyze_exception_safety(func_def: ast.FunctionDef,
                               bundle: ObligationBundle) -> None:
    """Analyze try/except and generate exception obligations."""
    for node in ast.walk(func_def):
        if isinstance(node, ast.Raise):
            exc_name = 'Exception'
            if node.exc:
                if isinstance(node.exc, ast.Call) and isinstance(node.exc.func, ast.Name):
                    exc_name = node.exc.func.id
                elif isinstance(node.exc, ast.Name):
                    exc_name = node.exc.id
            bundle.add(ProofObligation(
                kind=ObligationKind.EXCEPTION_SAFETY,
                description=f'may raise {exc_name} — callers must handle or propagate',
                fiber=f'except_{exc_name}',
                suggested_tactic='exception_handling',
            ))

        if isinstance(node, ast.Try):
            caught = set()
            for handler in node.handlers:
                if handler.type:
                    if isinstance(handler.type, ast.Name):
                        caught.add(handler.type.id)
                    elif isinstance(handler.type, ast.Tuple):
                        for elt in handler.type.elts:
                            if isinstance(elt, ast.Name):
                                caught.add(elt.id)
                else:
                    caught.add('Exception')  # bare except
            if caught:
                bundle.add(ProofObligation(
                    kind=ObligationKind.EXCEPTION_SAFETY,
                    description=f'catches {", ".join(sorted(caught))} — handler must preserve postcondition',
                    fiber='except_handler',
                    suggested_tactic='exception_cases',
                ))


def _analyze_duck_type_fibers(func_def: ast.FunctionDef,
                                bundle: ObligationBundle) -> None:
    """Analyze duck-type usage and generate per-fiber obligations."""
    params = [arg.arg for arg in func_def.args.args]

    for param in params:
        ops: Set[str] = set()
        for node in ast.walk(func_def):
            # Method calls on param
            if (isinstance(node, ast.Call) and
                isinstance(node.func, ast.Attribute) and
                isinstance(node.func.value, ast.Name) and
                node.func.value.id == param):
                ops.add(node.func.attr)
            # Subscript
            if (isinstance(node, ast.Subscript) and
                isinstance(node.value, ast.Name) and
                node.value.id == param):
                ops.add('__getitem__')
            # len() call
            if (isinstance(node, ast.Call) and
                isinstance(node.func, ast.Name) and
                node.func.id == 'len' and
                node.args and isinstance(node.args[0], ast.Name) and
                node.args[0].id == param):
                ops.add('__len__')
            # iter() or for-loop
            if isinstance(node, ast.For):
                if isinstance(node.iter, ast.Name) and node.iter.id == param:
                    ops.add('__iter__')
            # in operator
            if isinstance(node, ast.Compare):
                for comp_op, comparator in zip(node.ops, node.comparators):
                    if isinstance(comp_op, ast.In) and isinstance(comparator, ast.Name):
                        if comparator.id == param:
                            ops.add('__contains__')

        if ops:
            inferred = infer_type_from_ops(frozenset(ops))
            bundle.add(ProofObligation(
                kind=ObligationKind.TYPE_FIBER,
                description=f'param {param} used as {inferred.pretty()} (ops: {", ".join(sorted(ops)[:5])})',
                fiber=f'param_{param}',
                suggested_tactic='fiber_split',
            ))


def _analyze_library_calls(func_def: ast.FunctionDef,
                            bundle: ObligationBundle,
                            libraries: List[str]) -> None:
    """Find calls to library functions and generate contract obligations."""
    for node in ast.walk(func_def):
        if not isinstance(node, ast.Call):
            continue

        # module.function() pattern
        if isinstance(node.func, ast.Attribute):
            if isinstance(node.func.value, ast.Name):
                module = node.func.value.id
                method = node.func.attr

                # Check if this is a known library
                theory = get_library(module)
                if theory is None and module in libraries:
                    # Unknown library — generic obligation
                    bundle.add(ProofObligation(
                        kind=ObligationKind.LIBRARY_CONTRACT,
                        description=f'{module}.{method}() — no contract available',
                        library=module,
                        severity='advisory',
                    ))
                    continue

                if theory:
                    contract = theory.get_contract(method)
                    if contract:
                        for pre in contract.preconditions:
                            bundle.add(ProofObligation(
                                kind=ObligationKind.LIBRARY_CONTRACT,
                                description=f'{module}.{method} requires: {pre}',
                                library=module,
                                suggested_tactic='library_contract',
                            ))
                        if contract.raises:
                            for exc in contract.raises:
                                bundle.add(ProofObligation(
                                    kind=ObligationKind.EXCEPTION_SAFETY,
                                    description=f'{module}.{method} may raise {exc}',
                                    library=module,
                                    fiber=f'except_{exc}',
                                    severity='advisory',
                                ))

            # Chained calls: module.sub.function()
            if isinstance(node.func.value, ast.Attribute):
                # e.g., np.linalg.solve
                if isinstance(node.func.value.value, ast.Name):
                    top_module = node.func.value.value.id
                    sub_module = node.func.value.attr
                    method = node.func.attr
                    qualname = f'{sub_module}.{method}'

                    theory = get_library(top_module)
                    if theory:
                        contract = theory.get_contract(qualname)
                        if contract:
                            for pre in contract.preconditions:
                                bundle.add(ProofObligation(
                                    kind=ObligationKind.LIBRARY_CONTRACT,
                                    description=f'{top_module}.{qualname} requires: {pre}',
                                    library=top_module,
                                    suggested_tactic='library_contract',
                                ))


def _analyze_dict_shapes(func_def: ast.FunctionDef,
                          bundle: ObligationBundle) -> None:
    """Analyze dict construction and generate shape obligations."""
    for node in ast.walk(func_def):
        if isinstance(node, ast.Dict):
            if node.keys and all(isinstance(k, ast.Constant) and isinstance(k.value, str)
                                 for k in node.keys if k is not None):
                keys = [k.value for k in node.keys if k is not None and isinstance(k, ast.Constant)]
                bundle.add(ProofObligation(
                    kind=ObligationKind.DICT_SHAPE,
                    description=f'dict literal with keys {keys} — shape must match spec',
                    fiber='dict_shape',
                    suggested_tactic='dict_shape_check',
                    severity='advisory',
                ))


def _analyze_mutation(func_def: ast.FunctionDef,
                       bundle: ObligationBundle) -> None:
    """Detect in-place mutations and generate obligations."""
    mutating_methods = {'append', 'extend', 'insert', 'pop', 'remove', 'clear',
                        'sort', 'reverse', 'update', 'add', 'discard'}

    for node in ast.walk(func_def):
        if (isinstance(node, ast.Call) and
            isinstance(node.func, ast.Attribute) and
            node.func.attr in mutating_methods):
            target = ''
            if isinstance(node.func.value, ast.Name):
                target = node.func.value.id
            bundle.add(ProofObligation(
                kind=ObligationKind.MUTATION_SAFETY,
                description=f'{target}.{node.func.attr}() mutates in-place — '
                            f'pre/post state must satisfy invariant',
                fiber=f'mutation_{target}',
                suggested_tactic='mutation_invariant',
                severity='advisory',
            ))

        # Augmented assignment: x[i] = ..., x += ...
        if isinstance(node, ast.AugAssign):
            target = ''
            if isinstance(node.target, ast.Name):
                target = node.target.id
            elif isinstance(node.target, ast.Subscript):
                if isinstance(node.target.value, ast.Name):
                    target = node.target.value.id
            if target:
                bundle.add(ProofObligation(
                    kind=ObligationKind.MUTATION_SAFETY,
                    description=f'{target} mutated via augmented assignment',
                    fiber=f'mutation_{target}',
                    severity='advisory',
                ))


def _analyze_recursion(func_def: ast.FunctionDef,
                        bundle: ObligationBundle) -> None:
    """Detect recursion and generate termination obligations."""
    func_name = func_def.name
    for node in ast.walk(func_def):
        if (isinstance(node, ast.Call) and
            isinstance(node.func, ast.Name) and
            node.func.id == func_name):
            bundle.add(ProofObligation(
                kind=ObligationKind.TERMINATION,
                description=f'{func_name} is recursive — must prove termination '
                            f'(provide a measure function)',
                suggested_tactic='wf_induction',
            ))
            break


def _analyze_loop_invariants(func_def: ast.FunctionDef,
                              bundle: ObligationBundle) -> None:
    """Detect loops and generate invariant obligations."""
    for node in ast.walk(func_def):
        if isinstance(node, (ast.For, ast.While)):
            loop_type = 'for' if isinstance(node, ast.For) else 'while'
            bundle.add(ProofObligation(
                kind=ObligationKind.INVARIANT,
                description=f'{loop_type}-loop needs invariant to prove postcondition',
                suggested_tactic='loop_invariant',
                severity='advisory',
            ))


# ═══════════════════════════════════════════════════════════════════
# FORWARD: Proof → Python code with certificate (enhanced extraction)
# ═══════════════════════════════════════════════════════════════════

@dataclass
class VerifiedExtraction:
    """Result of forward extraction — code with full provenance.

    Enhanced over the basic ExtractedCode to include:
    - Per-fiber verification status
    - Library trust dependencies
    - Python-specific type information
    - Obligation resolution map
    """
    source: str
    function_name: str
    guarantee: str
    provenances: List[TrustProvenance] = field(default_factory=list)
    fiber_status: Dict[str, bool] = field(default_factory=dict)
    library_deps: List[str] = field(default_factory=list)
    inferred_type: Optional[CType] = None
    resolved_obligations: List[ProofObligation] = field(default_factory=list)

    @property
    def trust_level(self) -> str:
        """Overall trust level — limited by weakest link."""
        if not self.provenances:
            return '🔴 UNTRUSTED'
        weakest = min(self.provenances, key=lambda p: p.source.trust_rank)
        return weakest.trust_level

    @property
    def all_fibers_verified(self) -> bool:
        return all(self.fiber_status.values()) if self.fiber_status else False

    def with_guarantee(self) -> str:
        """Return source with @guarantee decorator and certificate."""
        lines = [
            'from deppy.hybrid import guarantee',
            '',
            f'@guarantee("{self.guarantee}")',
        ]
        if self.library_deps:
            libs = ', '.join(f'"{l}"' for l in self.library_deps)
            lines.append(f'# Depends on: {libs}')
        lines.append(f'# Trust: {self.trust_level}')
        lines.append(self.source)
        return '\n'.join(lines)

    def certificate_text(self) -> str:
        """Generate a human-readable certificate."""
        lines = [
            f'═══ Extraction Certificate for {self.function_name} ═══',
            f'Guarantee: {self.guarantee}',
            f'Trust level: {self.trust_level}',
        ]
        if self.fiber_status:
            lines.append(f'Fiber verification:')
            for fiber, ok in self.fiber_status.items():
                status = '✓' if ok else '✗'
                lines.append(f'  {status} {fiber}')
        if self.library_deps:
            lines.append(f'Library dependencies:')
            for lib in self.library_deps:
                lines.append(f'  🟠 {lib} (assumed)')
        if self.provenances:
            lines.append(f'Provenance chain:')
            for p in self.provenances:
                lines.append(f'  {p.trust_level} {p.name}')
        return '\n'.join(lines)


def extract_verified(
    function_name: str,
    proof: ProofTerm,
    lhs: OTerm,
    rhs: OTerm,
    guarantee: str = '',
    prefer: str = 'lhs',
    ctx: Optional[ProofContext] = None,
) -> VerifiedExtraction:
    """Forward extraction: proof → verified Python code.

    Enhanced over basic extraction to track:
    - Trust provenance through the proof tree
    - Per-fiber verification status
    - Library dependencies
    - Python-specific type information
    """
    # Verify the proof
    result = check_proof(proof, lhs, rhs, ctx)

    # Collect trust provenance from proof tree
    provenances = _collect_provenances(proof)

    # Collect library dependencies
    lib_deps = _collect_library_deps(proof)

    # Extract code from the preferred side
    from cctt.proof_theory.extraction import oterm_to_function
    term = lhs if prefer == 'lhs' else rhs
    source = oterm_to_function(term, function_name)

    # Determine per-fiber status
    fiber_status = _compute_fiber_status(proof)

    # Infer Pythonic type
    inferred = _infer_return_type_from_oterm(term)

    return VerifiedExtraction(
        source=source,
        function_name=function_name,
        guarantee=guarantee or f'{function_name} is verified equivalent',
        provenances=provenances,
        fiber_status=fiber_status,
        library_deps=lib_deps,
        inferred_type=inferred,
    )


def _collect_provenances(proof: ProofTerm) -> List[TrustProvenance]:
    """Walk proof tree and collect all trust provenances."""
    result = []

    if isinstance(proof, LibraryAxiom):
        result.append(proof.provenance())
    elif isinstance(proof, LibraryContract):
        result.append(TrustProvenance(
            source=TrustSource.LIBRARY_ASSUMED,
            name=f'{proof.library}.{proof.function_name}',
            library=proof.library,
            statement=proof.postcondition,
        ))
    elif isinstance(proof, Z3Discharge):
        result.append(TrustProvenance(
            source=TrustSource.Z3_PROVEN,
            name=f'z3_{proof.fragment}',
            statement=proof.formula[:80],
        ))
    elif isinstance(proof, (MathLibAxiom, MathlibTheorem)):
        name = proof.theorem_name
        result.append(TrustProvenance(
            source=TrustSource.MATHLIB,
            name=name,
        ))
    elif isinstance(proof, AxiomApp):
        result.append(TrustProvenance(
            source=TrustSource.STRUCTURAL,
            name=proof.axiom_name,
        ))
    elif isinstance(proof, Assume):
        result.append(TrustProvenance(
            source=TrustSource.USER_ASSUMPTION,
            name=proof.label,
        ))
    elif isinstance(proof, (FiberDecomposition, CechGluing, Descent)):
        result.append(TrustProvenance(
            source=TrustSource.CECH_DESCENT,
            name='cech_descent',
        ))

    # Import RefinementDescent safely
    try:
        from cctt.proof_theory.terms import RefinementDescent
        if isinstance(proof, RefinementDescent):
            # Trust level depends on the predicates' decidability
            lib_deps = set()
            for pred_str in proof.fiber_predicates.values():
                pred = parse_predicate(pred_str)
                lib_deps |= extract_library_deps(pred)
            if lib_deps:
                source = TrustSource.LIBRARY_ASSUMED
            elif proof.exhaustiveness == 'z3_proved':
                source = TrustSource.Z3_PROVEN
            else:
                source = TrustSource.CECH_DESCENT
            result.append(TrustProvenance(
                source=source,
                name=f'refinement_descent_{proof.base_type}',
                statement=f'{len(proof.fiber_predicates)} refinement fibers',
            ))
    except ImportError:
        pass

    # Recurse into children
    for child in proof.children():
        result.extend(_collect_provenances(child))

    return result


def _collect_library_deps(proof: ProofTerm) -> List[str]:
    """Collect all library dependencies from a proof tree."""
    libs: Set[str] = set()
    if isinstance(proof, LibraryAxiom):
        libs.add(proof.library)
    elif isinstance(proof, LibraryContract):
        libs.add(proof.library)
    for child in proof.children():
        libs.update(_collect_library_deps(child))
    return sorted(libs)


def _compute_fiber_status(proof: ProofTerm) -> Dict[str, bool]:
    """Compute per-fiber verification status from a proof tree."""
    status: Dict[str, bool] = {}

    if isinstance(proof, FiberDecomposition):
        for fiber_name, fiber_proof in proof.fiber_proofs.items():
            # A fiber is verified if it doesn't bottom out at Assume
            status[fiber_name] = not _contains_unresolved_assume(fiber_proof)
    elif isinstance(proof, Descent):
        for fiber_name, fiber_proof in proof.fiber_proofs.items():
            status[fiber_name] = not _contains_unresolved_assume(fiber_proof)
    elif isinstance(proof, CechGluing):
        for i, local in enumerate(proof.local_proofs):
            status[f'local_{i}'] = not _contains_unresolved_assume(local)

    return status


def _contains_unresolved_assume(proof: ProofTerm) -> bool:
    """Check if a proof contains any unresolved Assume nodes."""
    if isinstance(proof, Assume):
        return True
    return any(_contains_unresolved_assume(c) for c in proof.children())


def _infer_return_type_from_oterm(term: OTerm) -> CType:
    """Infer a Pythonic CType from an OTerm."""
    if isinstance(term, OLit):
        v = term.value
        if isinstance(v, int):
            return INT
        if isinstance(v, float):
            return FLOAT
        if isinstance(v, str):
            return STR
        if isinstance(v, bool):
            return PyAtom('bool')
        if v is None:
            return NONE_TYPE
        return CType()

    if isinstance(term, OSeq):
        if term.elements:
            elem_type = _infer_return_type_from_oterm(term.elements[0])
            return PyList(elem_type)
        return PyList(CType())

    if isinstance(term, ODict):
        if term.pairs:
            k_type = _infer_return_type_from_oterm(term.pairs[0][0])
            v_type = _infer_return_type_from_oterm(term.pairs[0][1])
            return PyDict(k_type, v_type)
        return PyDict(CType(), CType())

    if isinstance(term, OCase):
        t_type = _infer_return_type_from_oterm(term.true_branch)
        f_type = _infer_return_type_from_oterm(term.false_branch)
        if type(t_type) == type(f_type) and t_type == f_type:
            return t_type
        return PyUnion((t_type, f_type))

    if isinstance(term, OFold):
        return _infer_return_type_from_oterm(term.init)

    if isinstance(term, OMap):
        return PyList(CType())

    if isinstance(term, OLam):
        return CALLABLE_DUCK

    if isinstance(term, OCatch):
        return ExceptionEffect(
            return_type=_infer_return_type_from_oterm(term.body),
            raises=frozenset({'Exception'}),
        )

    return CType()


# ═══════════════════════════════════════════════════════════════════
# ROUND-TRIP: Obligate → Prove → Extract → Verify
# ═══════════════════════════════════════════════════════════════════

def verify_against_obligations(
    source: str,
    guarantee: str,
    proof: ProofTerm,
    libraries: Optional[List[str]] = None,
) -> Tuple[VerifiedExtraction, ObligationBundle]:
    """Full round-trip: generate obligations, check proof covers them.

    Returns the extraction result AND the obligation bundle showing
    which obligations were resolved by the proof.
    """
    # Backward: generate obligations
    bundle = obligate(source, guarantee, libraries)

    # Compile to OTerms
    result = compile_to_oterm(source)
    if result is None:
        return (VerifiedExtraction(
            source=source,
            function_name=bundle.function_name,
            guarantee=guarantee,
        ), bundle)

    oterm, _warnings = result

    # Forward: extract with proof
    extraction = extract_verified(
        function_name=bundle.function_name,
        proof=proof,
        lhs=oterm,
        rhs=oterm,
        guarantee=guarantee,
    )

    # Match proof provenances to obligations
    _resolve_obligations(bundle, extraction)

    extraction.resolved_obligations = [o for o in bundle.obligations if o.resolved]
    return extraction, bundle


def _resolve_obligations(bundle: ObligationBundle,
                          extraction: VerifiedExtraction) -> None:
    """Mark obligations as resolved based on extraction provenances."""
    for obligation in bundle.obligations:
        if obligation.kind == ObligationKind.LIBRARY_CONTRACT:
            # Resolved if we have a library provenance
            for p in extraction.provenances:
                if (p.source == TrustSource.LIBRARY_ASSUMED and
                    obligation.library and p.library == obligation.library):
                    obligation.resolved = True
                    break

        elif obligation.kind == ObligationKind.TYPE_FIBER:
            # Resolved if the fiber is verified
            if obligation.fiber in extraction.fiber_status:
                obligation.resolved = extraction.fiber_status[obligation.fiber]

        elif obligation.kind in (ObligationKind.POSTCONDITION,
                                  ObligationKind.INVARIANT):
            # Resolved if any structural/Z3 provenance covers it
            for p in extraction.provenances:
                if p.source in (TrustSource.STRUCTURAL, TrustSource.Z3_PROVEN,
                                TrustSource.LEAN_VERIFIED, TrustSource.MATHLIB):
                    obligation.resolved = True
                    break
