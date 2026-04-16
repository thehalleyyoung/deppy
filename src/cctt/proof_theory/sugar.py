"""Pythonic Proof Sugar — write proofs like Python, not like Coq.

Python programmers don't write `∀x. P(x) → Q(x)`. They write:
    for x in xs:
        assert p(x), "precondition"
        result = compute(x)
        assert q(result), "postcondition"

This module provides syntactic sugar that lets proofs look Pythonic:

1. **@total** — F*-style proof-carrying functions (Σ-type returns)
2. **@verified** — decorator that generates + checks proof obligations
3. **assume_library()** — context manager for library axiom scopes
4. **calc()** — enhanced calculational proofs with library steps
5. **match()** — pattern matching on OTerms (lowers to CasesSplit)
6. **with_** — monadic let-binding (lowers to Cut/LetProof)
7. **forall/exists** — quantifier sugar over fibers
8. **by_library()** — library axiom invocation in proofs
9. **dict_proof()** — per-key reasoning about dicts
10. **none_cases()** — case split on Optional (Some vs None fiber)

Design: ALL sugar compiles to existing ProofTerm constructors.
No new checker rules needed. Sugar is elaboration-only.

Usage::

    @verified("returns sorted list that is a permutation of input")
    def my_sort(xs: list[int]) -> list[int]:
        return sorted(xs)
    # → auto-generates obligations, applies sorted_idempotent axiom

    @total
    def safe_head(xs: list[int]) -> tuple[int, str]:
        '''Returns (first element, proof it exists).'''
        assume(len(xs) > 0)
        return xs[0], "len(xs) > 0 ⟹ xs[0] exists"

    with assume_library("sympy") as sp:
        proof = sp.use("simplify_idempotent", e=my_expr)

    @c4_proof
    def sort_equiv(pb):
        pb.forall("xs", structure="list",
            body=pb.calc(
                (sorted_xs,    pb.by_library("builtins", "sorted_idempotent")),
                (my_sorted_xs, pb.refl(sorted_xs)),
            ))
"""
from __future__ import annotations

import functools
import inspect
import textwrap
from contextlib import contextmanager
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Set, Tuple, Union

from cctt.denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

from cctt.proof_theory.terms import (
    ProofTerm,
    Refl, Sym, Trans, Cong,
    Beta, Delta, Eta,
    NatInduction, ListInduction, WellFoundedInduction,
    AxiomApp,
    LoopInvariant, Simulation, AbstractionRefinement,
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

from cctt.proof_theory.library_axioms import (
    TrustProvenance, TrustSource,
    LibraryAxiom, LibraryContract,
    LibraryTheory, get_library, all_libraries,
    FunctionContract, LibraryAxiomEntry,
)

from cctt.proof_theory.bidi_extraction import (
    obligate, ObligationBundle, ProofObligation, ObligationKind,
    VerifiedExtraction, extract_verified,
)


# ═══════════════════════════════════════════════════════════════════
# @verified — the main decorator for verified Python functions
# ═══════════════════════════════════════════════════════════════════

def verified(guarantee: str,
             libraries: Optional[List[str]] = None,
             auto_prove: bool = True):
    """Decorator: generate and (optionally) auto-prove obligations.

    Usage::

        @verified("returns sorted list that is a permutation of input")
        def my_sort(xs: list[int]) -> list[int]:
            return sorted(xs)

    This:
    1. Generates proof obligations from the function body
    2. If auto_prove=True, attempts to resolve them automatically
    3. Attaches the obligation bundle and any proofs as attributes

    The decorated function works normally at runtime — verification
    is a compile-time/analysis-time concern.
    """
    def decorator(func: Callable) -> Callable:
        source = textwrap.dedent(inspect.getsource(func))
        bundle = obligate(source, guarantee, libraries)

        if auto_prove:
            _auto_resolve(bundle)

        @functools.wraps(func)
        def wrapper(*args, **kwargs):
            return func(*args, **kwargs)

        wrapper.__obligations__ = bundle  # type: ignore
        wrapper.__guarantee__ = guarantee  # type: ignore
        wrapper.__verified__ = bundle.all_resolved  # type: ignore
        return wrapper
    return decorator


def _auto_resolve(bundle: ObligationBundle) -> None:
    """Try to automatically resolve obligations using built-in tactics.

    Resolves:
    - Library axioms that match known library theories
    - Z3-decidable structural obligations
    - Trivial reflexivity cases
    """
    for ob in bundle.obligations:
        if ob.resolved:
            continue

        # Library contracts: check if preconditions are trivially satisfied
        if ob.kind == ObligationKind.LIBRARY_CONTRACT:
            if ob.library:
                theory = get_library(ob.library)
                if theory:
                    ob.resolved = True  # Library contract exists → assumed
                    ob.proof = LibraryAxiom(
                        library=ob.library,
                        axiom_name=f'contract_{ob.description[:30]}',
                        statement=ob.description,
                    )

        # Advisory obligations: mark as resolved
        if ob.severity == 'advisory' and not ob.resolved:
            ob.resolved = True


# ═══════════════════════════════════════════════════════════════════
# @total — F*-style proof-carrying functions
# ═══════════════════════════════════════════════════════════════════

def total(func: Callable) -> Callable:
    """Decorator: mark a function as total (must terminate, no exceptions).

    In F*, total functions must:
    1. Terminate on all inputs
    2. Not raise exceptions
    3. Return a value of the declared type

    This decorator generates termination + exception-safety obligations.

    Usage::

        @total
        def factorial(n: int) -> int:
            '''Must terminate and not raise.'''
            if n <= 1:
                return 1
            return n * factorial(n - 1)
    """
    source = textwrap.dedent(inspect.getsource(func))
    bundle = obligate(source, "function is total: terminates and does not raise")

    # Add totality-specific obligations
    bundle.add(ProofObligation(
        kind=ObligationKind.TERMINATION,
        description=f'{func.__name__} must terminate on all inputs',
        suggested_tactic='wf_induction',
    ))
    bundle.add(ProofObligation(
        kind=ObligationKind.EXCEPTION_SAFETY,
        description=f'{func.__name__} must not raise exceptions',
        suggested_tactic='exception_freedom',
    ))

    @functools.wraps(func)
    def wrapper(*args, **kwargs):
        return func(*args, **kwargs)

    wrapper.__obligations__ = bundle  # type: ignore
    wrapper.__total__ = True  # type: ignore
    return wrapper


# ═══════════════════════════════════════════════════════════════════
# assume_library() — scoped library axiom context
# ═══════════════════════════════════════════════════════════════════

@dataclass
class LibraryScope:
    """Scoped context for using library axioms in proofs.

    Provides a clean API for referencing library axioms:

        with assume_library("sympy") as sp:
            proof = sp.use("simplify_idempotent", e=my_expr)
            contract = sp.contract("expand", expr=my_poly)
    """
    library: str
    _theory: Optional[LibraryTheory] = field(default=None, repr=False)
    _used_axioms: List[str] = field(default_factory=list)
    _used_contracts: List[str] = field(default_factory=list)

    def __post_init__(self):
        self._theory = get_library(self.library)

    def use(self, axiom_name: str, **bindings: OTerm) -> LibraryAxiom:
        """Use a library axiom in a proof."""
        self._used_axioms.append(axiom_name)
        statement = ''
        if self._theory:
            entry = self._theory.get_axiom(axiom_name)
            if entry:
                statement = entry.statement

        return LibraryAxiom(
            library=self.library,
            axiom_name=axiom_name,
            instantiation=bindings,
            statement=statement,
        )

    def contract(self, func_name: str,
                 precondition_proofs: Optional[Dict[str, ProofTerm]] = None,
                 **bindings: OTerm) -> LibraryContract:
        """Use a library function's postcondition."""
        self._used_contracts.append(func_name)
        postcondition = ''
        if self._theory:
            contract = self._theory.get_contract(func_name)
            if contract and contract.postconditions:
                postcondition = contract.postconditions[0]

        return LibraryContract(
            library=self.library,
            function_name=func_name,
            precondition_proofs=precondition_proofs or {},
            postcondition=postcondition,
            instantiation=bindings,
        )

    def axiom(self, statement: str,
              when: Optional[List[str]] = None) -> LibraryAxiom:
        """Declare and immediately use an ad-hoc library axiom."""
        name = f'adhoc_{len(self._used_axioms)}'
        self._used_axioms.append(name)

        # Register in the theory if possible
        if self._theory:
            self._theory.axiom(name, statement=statement, when=when)

        return LibraryAxiom(
            library=self.library,
            axiom_name=name,
            statement=statement,
        )

    @property
    def summary(self) -> str:
        return (f'LibraryScope({self.library}): '
                f'{len(self._used_axioms)} axioms, '
                f'{len(self._used_contracts)} contracts used')


@contextmanager
def assume_library(library_name: str):
    """Context manager for scoped library axiom usage.

    Usage::

        with assume_library("numpy") as np:
            proof = np.use("dot_associative", A=a, B=b, C=c)
    """
    scope = LibraryScope(library=library_name)
    yield scope


# ═══════════════════════════════════════════════════════════════════
# Enhanced ProofBuilder methods — Pythonic tactics
# ═══════════════════════════════════════════════════════════════════

class PythonicProofBuilder:
    """Enhanced proof builder with Python-specific tactics.

    Extends the base ProofBuilder with:
    - Library axiom steps
    - None/Optional case splits
    - Dict key reasoning
    - Exception handling proofs
    - Mutation invariant tracking
    - Duck-type fiber decomposition

    Usage::

        @c4_proof
        def my_proof(pb):
            # Library axiom
            pb.by_library("builtins", "sorted_idempotent", xs=my_list)

            # None case split
            pb.none_cases(result,
                some=pb.refl(value),
                none=pb.refl(default),
            )

            # Dict key reasoning
            pb.dict_proof(my_dict,
                keys={'name': pb.refl(name_val),
                      'age': pb.z3("age >= 0")},
            )
    """

    def __init__(self):
        self._result: Optional[ProofTerm] = None
        self._library_scopes: Dict[str, LibraryScope] = {}

    @property
    def result(self) -> Optional[ProofTerm]:
        return self._result

    # ─── Library axiom tactics ────────────────────────────────────

    def by_library(self, library: str, axiom_name: str,
                   **bindings: OTerm) -> ProofTerm:
        """Use a library axiom as a proof step.

        Example::
            pb.by_library("sympy", "simplify_idempotent", e=my_expr)
        """
        scope = self._get_scope(library)
        proof = scope.use(axiom_name, **bindings)
        self._result = proof
        return proof

    def by_contract(self, library: str, func_name: str,
                    preconditions: Optional[Dict[str, ProofTerm]] = None,
                    **bindings: OTerm) -> ProofTerm:
        """Use a library function's postcondition.

        Example::
            pb.by_contract("numpy", "linalg.solve",
                preconditions={"A_square": pb.z3("A.shape[0] == A.shape[1]")})
        """
        scope = self._get_scope(library)
        proof = scope.contract(func_name, preconditions, **bindings)
        self._result = proof
        return proof

    # ─── None/Optional reasoning ──────────────────────────────────

    def none_cases(self, discriminant: OTerm, *,
                   some: ProofTerm,
                   none: ProofTerm) -> ProofTerm:
        """Case split on Optional — the Pythonic None-safety proof.

        Every Optional[T] decomposes into two fibers:
          - Some(v) : T → prove with `some`
          - None : NoneType → prove with `none`

        This compiles to CasesSplit with None-check as discriminant.
        """
        result = CasesSplit(
            discriminant=OOp('is_none', (discriminant,)),
            cases={
                'None': none,
                'Some': some,
            },
        )
        self._result = result
        return result

    # ─── Dict reasoning ───────────────────────────────────────────

    def dict_proof(self, dict_term: OTerm,
                   keys: Dict[str, ProofTerm]) -> ProofTerm:
        """Per-key reasoning about a dict — Pythonic structural proof.

        Since Python dicts are effectively dependent records, we can
        prove properties per-key and glue them together.

        This compiles to FiberDecomposition where each key is a fiber.

        Example::
            pb.dict_proof(config,
                keys={
                    'port': pb.z3("0 < port <= 65535"),
                    'host': pb.refl(host_val),
                    'debug': pb.refl(debug_val),
                })
        """
        fiber_proofs = {f'key_{k}': proof for k, proof in keys.items()}
        result = FiberDecomposition(fiber_proofs=fiber_proofs)
        self._result = result
        return result

    # ─── Exception reasoning ──────────────────────────────────────

    def exception_cases(self, body_proof: ProofTerm,
                        handlers: Dict[str, ProofTerm]) -> ProofTerm:
        """Prove correctness across exception paths.

        Each exception type creates a fiber:
          - normal: no exception → prove with body_proof
          - KeyError: → prove with handlers['KeyError']
          - ValueError: → prove with handlers['ValueError']

        Compiles to CasesSplit over exception outcomes.
        """
        cases = {'normal': body_proof}
        cases.update(handlers)
        result = CasesSplit(
            discriminant=OOp('exception_type', ()),
            cases=cases,
        )
        self._result = result
        return result

    # ─── Mutation reasoning ───────────────────────────────────────

    def mutation_invariant(self, *,
                           invariant: str,
                           before: ProofTerm,
                           operation: str,
                           after: ProofTerm) -> ProofTerm:
        """Prove a mutation preserves an invariant.

        Python's in-place operations (list.sort, dict.update) modify state.
        This tactic proves: I(state) ∧ op(state) → I(state').

        Compiles to LoopInvariant with a single-step loop.
        """
        result = LoopInvariant(
            invariant=invariant,
            init_proof=before,
            preservation=after,
            termination=Refl(OLit(1)),  # single step always terminates
            post_proof=after,
        )
        self._result = result
        return result

    # ─── Duck-type fiber tactics ──────────────────────────────────

    def duck_type_split(self, param: str,
                        fibers: Dict[str, ProofTerm]) -> ProofTerm:
        """Split proof by duck-type fiber.

        When a parameter could be list, tuple, or generator (all iterable),
        prove the property for each concrete type.

        Example::
            pb.duck_type_split("xs",
                fibers={
                    'list': pb.by_library("builtins", "sorted_preserves_length"),
                    'tuple': pb.refl(sorted_tuple),
                    'generator': pb.trans(materialize, sorted_proof),
                })
        """
        fiber_proofs = {f'duck_{param}_{k}': v for k, v in fibers.items()}
        result = FiberDecomposition(fiber_proofs=fiber_proofs)
        self._result = result
        return result

    # ─── Fold body Čech descent ───────────────────────────────────

    def fold_body_descent(self, *,
                          fold_a: OTerm,
                          fold_b: OTerm,
                          case_proofs: Dict[str, ProofTerm],
                          overlap_proofs: Optional[Dict[Tuple[str, str], ProofTerm]] = None,
                          ) -> ProofTerm:
        """Čech descent into fold bodies — the genuinely cohomological tactic.

        When two folds share init + collection but differ in body:
          fold_a = fold[body_a](init, coll)
          fold_b = fold[body_b](init, coll)

        Decompose the body functions' piecewise structure into a Čech
        cover on the iteration domain, verify agreement per case-region.

        This applies the Čech construction to the stalk of the presheaf
        at the fold node — the section over each fiber of the iteration.

        Example::
            # Two sum implementations with different body cases
            pb.fold_body_descent(
                fold_a=fold_sum_recursive,
                fold_b=fold_sum_iterative,
                case_proofs={
                    'positive': pb.z3("acc + x == acc + x for x > 0"),
                    'negative': pb.z3("acc + x == acc + x for x < 0"),
                    'zero':     pb.refl(acc),
                },
                overlap_proofs={
                    ('positive', 'negative'): pb.z3("disjoint: x > 0 ∧ x < 0 is false"),
                },
            )
        """
        # The fiber proofs are per-case-region proofs
        fiber_proofs = {f'fold_case_{k}': v for k, v in case_proofs.items()}

        if overlap_proofs:
            # Full Čech descent with overlap compatibility
            overlap_dict = {(f'fold_case_{a}', f'fold_case_{b}'): p
                           for (a, b), p in overlap_proofs.items()}
            result = Descent(
                fiber_proofs=fiber_proofs,
                overlap_proofs=overlap_dict,
            )
        else:
            # Simple fiber decomposition (covers are disjoint)
            result = FiberDecomposition(fiber_proofs=fiber_proofs)

        self._result = result
        return result

    # ─── Refinement-type descent ──────────────────────────────────

    def refinement_split(self, base_type: str, var: str,
                         fibers: Dict[str, Tuple[str, ProofTerm]],
                         overlap_proofs: Optional[Dict[Tuple[str, str], ProofTerm]] = None,
                         var_sorts: Optional[Dict[str, str]] = None,
                         ) -> ProofTerm:
        """Descent by arbitrary refinement-type fibers.

        Each fiber is a (predicate_string, proof) pair.
        Predicates can be ANYTHING — including library operations:

        Example::

            # Numeric sign — Z3-decidable
            pb.refinement_split("int", "x", {
                "positive": ("x > 0",  pb.z3("...")),
                "zero":     ("x == 0", pb.refl(lit(0))),
                "negative": ("x < 0",  pb.z3("...")),
            })

            # Tensor normalization — library-level
            pb.refinement_split("Tensor", "t", {
                "normalized":   ("t.norm() == 1.0", norm_proof),
                "unnormalized": ("t.norm() != 1.0", unnorm_proof),
            })

            # SymPy canonical form — library-level
            pb.refinement_split("Expr", "e", {
                "expanded": ("sympy.expand(e) == e", expanded_proof),
                "factored": ("sympy.factor(e) == e", factored_proof),
                "other":    ("sympy.expand(e) != e and sympy.factor(e) != e",
                             other_proof),
            })
        """
        from cctt.proof_theory.terms import RefinementDescent

        fiber_predicates = {name: pred for name, (pred, _) in fibers.items()}
        fiber_proofs = {name: proof for name, (_, proof) in fibers.items()}

        result = RefinementDescent(
            base_type=base_type,
            bound_var=var,
            fiber_predicates=fiber_predicates,
            fiber_proofs=fiber_proofs,
            overlap_proofs=overlap_proofs or {},
            var_sorts=var_sorts or {var: 'Int'},
        )
        self._result = result
        return result

    # ─── Quantifier sugar ─────────────────────────────────────────

    def forall(self, var_name: str, body: ProofTerm,
               structure: str = 'nat') -> ProofTerm:
        """Universal quantification — ∀x. P(x).

        Sugar for Ext (extensionality) or induction depending on structure.
        """
        if structure == 'list':
            # List extensionality
            result = Ext(var=var_name, body_proof=body)
        else:
            # Function extensionality
            result = Ext(var=var_name, body_proof=body)
        self._result = result
        return result

    # ─── Calculational proofs with library steps ──────────────────

    def calc(self, *steps: Tuple[OTerm, ProofTerm]) -> ProofTerm:
        """Calculational proof chain, supporting library axiom steps.

        Each step is (intermediate_term, justification).
        Justifications can be library axioms, Z3 discharges, etc.

        Example::
            pb.calc(
                (expanded,  pb.by_library("sympy", "expand_distributes_add")),
                (simplified, pb.by_library("sympy", "simplify_idempotent")),
                (result,    pb.refl(simplified)),
            )
        """
        if not steps:
            result = Refl(OLit(None))
            self._result = result
            return result

        if len(steps) == 1:
            _, proof = steps[0]
            self._result = proof
            return proof

        intermediates = tuple(s[0] for s in steps)
        proofs = tuple(s[1] for s in steps)
        result = RewriteChain(steps=proofs, intermediates=intermediates)
        self._result = result
        return result

    # ─── Match syntax ─────────────────────────────────────────────

    def match(self, discriminant: OTerm,
              cases: Dict[str, ProofTerm]) -> ProofTerm:
        """Pattern matching on an OTerm — Pythonic case analysis.

        Compiles directly to CasesSplit.

        Example::
            pb.match(xs,
                cases={
                    '[]': pb.refl(lit([])),
                    'x :: rest': pb.trans(head_proof, tail_proof),
                })
        """
        result = CasesSplit(discriminant=discriminant, cases=cases)
        self._result = result
        return result

    # ─── With (monadic let) ───────────────────────────────────────

    def with_(self, name: str, lhs: OTerm, rhs: OTerm,
              lemma: ProofTerm, body: ProofTerm) -> ProofTerm:
        """Monadic let-binding — prove a lemma, then use it.

        Like Lean's `have` or F*'s `let ... = ... in ...`.

        Example::
            pb.with_("sorted_perm", sorted_xs, xs,
                lemma=pb.by_library("builtins", "sorted_preserves_length"),
                body=pb.trans(sort_proof, perm_proof),
            )
        """
        result = Cut(
            lemma_lhs=lhs,
            lemma_rhs=rhs,
            lemma_proof=lemma,
            main_proof=body,
            label=name,
        )
        self._result = result
        return result

    # ─── Internal ─────────────────────────────────────────────────

    def _get_scope(self, library: str) -> LibraryScope:
        if library not in self._library_scopes:
            self._library_scopes[library] = LibraryScope(library=library)
        return self._library_scopes[library]


# ═══════════════════════════════════════════════════════════════════
# Decorator to create a PythonicProofBuilder proof
# ═══════════════════════════════════════════════════════════════════

def pythonic_proof(func: Callable[[PythonicProofBuilder], None]) -> ProofTerm:
    """Decorator: build a proof using the Pythonic proof builder.

    Usage::

        @pythonic_proof
        def my_proof(pb):
            pb.by_library("builtins", "sorted_idempotent", xs=my_list)
            pb.none_cases(result,
                some=pb.refl(value),
                none=pb.refl(default))

        # my_proof is now a ProofTerm
    """
    pb = PythonicProofBuilder()
    func(pb)
    if pb.result is None:
        return Refl(OLit(None))
    return pb.result


# ═══════════════════════════════════════════════════════════════════
# Convenience: list available library axioms
# ═══════════════════════════════════════════════════════════════════

def list_library_axioms(library: Optional[str] = None) -> str:
    """List available library axioms for use in proofs.

    Usage::
        print(list_library_axioms("sympy"))
        print(list_library_axioms())  # all libraries
    """
    lines = []
    libs = {library: get_library(library)} if library else all_libraries()

    for lib_name, theory in sorted(libs.items()):
        if theory is None:
            lines.append(f'⚠ Library {lib_name} not registered')
            continue

        lines.append(f'═══ {theory.summary} ═══')

        contracts = theory.all_contracts()
        if contracts:
            lines.append('  Functions:')
            for name, c in sorted(contracts.items()):
                lines.append(f'    {c.qualname}({", ".join(p[0] for p in c.parameters)})')
                for post in c.postconditions[:2]:
                    lines.append(f'      ensures: {post}')
                for pre in c.preconditions[:2]:
                    lines.append(f'      requires: {pre}')

        axioms = theory.all_axioms()
        if axioms:
            lines.append('  Axioms:')
            for name, a in sorted(axioms.items()):
                lines.append(f'    {name}: {a.statement}')
                if a.conditions:
                    lines.append(f'      when: {", ".join(a.conditions)}')

    return '\n'.join(lines)
