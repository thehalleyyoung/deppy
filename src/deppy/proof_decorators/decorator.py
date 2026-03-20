from __future__ import annotations

import functools
import hashlib
import inspect
import time
from typing import Callable, Dict, List, Mapping, Sequence, Tuple

from deppy.core._protocols import SiteId, SiteKind, TrustLevel
from deppy.predicates import (
    And,
    BinOp,
    BoolLit,
    Call,
    Comparison,
    Contains,
    Disjoint,
    FloatLit,
    IntLit,
    IsNone,
    IsNotNone,
    NonEmpty,
    Not,
    NoneLit,
    Or,
    Permutation,
    Sorted,
    StrLit,
    Subset,
    Unique,
    Var,
)
from deppy.proof_decorators.certificate_bridge import artifact_from_solver_result, build_decorator_artifact
from deppy.proof_decorators.invariant_compiler import CompiledInvariant, compile_invariant
from deppy.proof_decorators.models import (
    DecoratedProofArtifact,
    DecoratorProofConfig,
    InvariantCheckResult,
    ProofDecoratorConfigurationError,
    ProofEmbeddingMode,
    VerificationError,
)
from deppy.solver import SolverObligation, SolverStatus, generate_certificate, quick_check


_DECORATOR_CACHE: Dict[str, Tuple[CompiledInvariant, ...]] = {}


def prove(
    *invariants: object,
    requires: Sequence[object] = (),
    ensures: Sequence[object] = (),
    timeout_ms: float = 200.0,
    strict: bool = False,
    eager: bool = True,
    cache_by_source_hash: bool = True,
) -> Callable[[Callable[..., object]], Callable[..., object]]:
    config = DecoratorProofConfig(
        timeout_ms=timeout_ms,
        strict=strict,
        eager=eager,
        cache_by_source_hash=cache_by_source_hash,
        embedding_mode=ProofEmbeddingMode.ANNOTATIONS,
    )

    def decorator(fn: Callable[..., object]) -> Callable[..., object]:
        source_hash = _source_hash(fn)
        compiled, from_cache = _compiled_invariants(
            source_hash,
            invariants,
            requires,
            ensures,
            config,
        )
        base_artifact = DecoratedProofArtifact(
            function_name=fn.__name__,
            source_hash=source_hash,
            status="pending",
            config=config,
            invariants=tuple(item.source for item in compiled),
            checks=(),
            warnings=(),
            from_cache=from_cache,
        )
        if config.eager:
            base_artifact = _run_preflight(compiled, base_artifact)
        _write_artifact(fn, base_artifact)

        @functools.wraps(fn)
        def wrapper(*args: object, **kwargs: object) -> object:
            bound = inspect.signature(fn).bind_partial(*args, **kwargs)
            bound.apply_defaults()
            env = dict(bound.arguments)
            runtime_checks: List[InvariantCheckResult] = []

            pre_compiled = [item for item in compiled if item.phase == "pre"]
            pre_results = [
                _check_runtime_invariant(fn.__name__, item, env, config.timeout_ms)
                for item in pre_compiled
            ]
            runtime_checks.extend(pre_results)

            if pre_results and config.strict and any(
                check.status != "verified"
                for check in pre_results
            ):
                artifact = build_decorator_artifact(
                    base_artifact,
                    checks=tuple(runtime_checks),
                    status=_aggregate_status(runtime_checks),
                )
                _write_artifact(wrapper, artifact)
                raise VerificationError(f"Precondition proof failed for {fn.__name__}")

            result = fn(*args, **kwargs)
            env_with_result = dict(env)
            env_with_result["result"] = result
            post_compiled = [item for item in compiled if item.phase == "post"]
            post_results = [
                _check_runtime_invariant(fn.__name__, item, env_with_result, config.timeout_ms)
                for item in post_compiled
            ]
            runtime_checks.extend(post_results)

            final_status = _aggregate_status(runtime_checks)
            artifact = build_decorator_artifact(
                base_artifact,
                checks=tuple(runtime_checks),
                status=final_status,
            )
            _write_artifact(wrapper, artifact)
            if config.strict and final_status != "verified":
                raise VerificationError(
                    f"Proof obligations failed for {fn.__name__} ({final_status})"
                )
            return result

        _write_artifact(wrapper, base_artifact)
        return wrapper

    return decorator


def _compiled_invariants(
    source_hash: str,
    invariants: Sequence[object],
    requires: Sequence[object],
    ensures: Sequence[object],
    config: DecoratorProofConfig,
) -> Tuple[Tuple[CompiledInvariant, ...], bool]:
    if config.cache_by_source_hash and source_hash in _DECORATOR_CACHE:
        return _DECORATOR_CACHE[source_hash], True

    compiled: List[CompiledInvariant] = []
    for invariant in invariants:
        compiled.append(compile_invariant(invariant, phase="auto"))
    for invariant in requires:
        compiled.append(compile_invariant(invariant, phase="pre"))
    for invariant in ensures:
        compiled.append(compile_invariant(invariant, phase="post"))
    compiled_tuple = tuple(compiled)
    if config.cache_by_source_hash:
        _DECORATOR_CACHE[source_hash] = compiled_tuple
    return compiled_tuple, False


def _run_preflight(
    compiled: Sequence[CompiledInvariant],
    artifact: DecoratedProofArtifact,
) -> DecoratedProofArtifact:
    warnings = list(artifact.warnings)
    for item in compiled:
        try:
            result = quick_check(item.predicate, timeout_ms=artifact.config.timeout_ms)
        except Exception as exc:  # pragma: no cover - defensive wrapper
            warnings.append(f"Preflight solver failure for '{item.source}': {exc}")
            continue
        if result.status == SolverStatus.UNSAT:
            warnings.append(f"Preflight contradiction detected for '{item.source}'")
        elif result.status in {SolverStatus.UNKNOWN, SolverStatus.TIMEOUT, SolverStatus.ERROR}:
            warnings.append(
                f"Preflight could not verify '{item.source}' ({result.status.value})"
            )
    status = "refuted" if any("contradiction" in warning for warning in warnings) else artifact.status
    return build_decorator_artifact(artifact, warnings=tuple(warnings), status=status)


def _check_runtime_invariant(
    function_name: str,
    invariant: CompiledInvariant,
    env: Mapping[str, object],
    timeout_ms: float,
) -> InvariantCheckResult:
    start = time.perf_counter()
    grounded = _ground_predicate(invariant.predicate, env)
    if grounded is None:
        return InvariantCheckResult(
            phase=invariant.phase,
            source=invariant.source,
            status="abstained",
            predicate_text=getattr(invariant.predicate, "pretty", lambda: repr(invariant.predicate))(),
            detail="Unsupported runtime values for invariant grounding",
            elapsed_ms=(time.perf_counter() - start) * 1000,
        )

    negated = Not(grounded)
    result = quick_check(negated, timeout_ms=timeout_ms)
    elapsed_ms = (time.perf_counter() - start) * 1000
    predicate_text = grounded.pretty()
    if result.status == SolverStatus.UNSAT:
        obligation = SolverObligation(
            site_id=SiteId(kind=SiteKind.PROOF, name=f"{function_name}:{invariant.phase}"),
            formula=negated,
            trust_level=TrustLevel.PROOF_BACKED,
        )
        certificate = generate_certificate(result, obligation)
        return InvariantCheckResult(
            phase=invariant.phase,
            source=invariant.source,
            status="verified",
            predicate_text=predicate_text,
            elapsed_ms=elapsed_ms,
            proof_certificate=artifact_from_solver_result(certificate),
        )
    if result.status == SolverStatus.SAT:
        return InvariantCheckResult(
            phase=invariant.phase,
            source=invariant.source,
            status="refuted",
            predicate_text=predicate_text,
            detail=result.explanation or "Negated runtime invariant is satisfiable",
            elapsed_ms=elapsed_ms,
        )
    if result.status == SolverStatus.TIMEOUT:
        return InvariantCheckResult(
            phase=invariant.phase,
            source=invariant.source,
            status="timeout",
            predicate_text=predicate_text,
            detail=result.explanation,
            elapsed_ms=elapsed_ms,
        )
    return InvariantCheckResult(
        phase=invariant.phase,
        source=invariant.source,
        status="abstained",
        predicate_text=predicate_text,
        detail=result.explanation or result.status.value,
        elapsed_ms=elapsed_ms,
    )


def _aggregate_status(checks: Sequence[InvariantCheckResult]) -> str:
    if not checks:
        return "pending"
    statuses = {check.status for check in checks}
    if "refuted" in statuses:
        return "refuted"
    if "timeout" in statuses:
        return "timeout"
    if statuses == {"verified"}:
        return "verified"
    return "abstained"


def _write_artifact(fn: Callable[..., object], artifact: DecoratedProofArtifact) -> None:
    annotations = dict(getattr(fn, "__annotations__", {}) or {})
    annotations["__proof__"] = artifact.to_dict()
    fn.__annotations__ = annotations
    fn.__proof_artifact__ = artifact


def _source_hash(fn: Callable[..., object]) -> str:
    try:
        source = inspect.getsource(fn)
    except (OSError, IOError):
        source = f"{fn.__module__}:{fn.__qualname__}"
    return hashlib.sha256(source.encode("utf-8")).hexdigest()[:32]


def _bool_pred(value: bool) -> object:
    return And([]) if value else Or([])


def _ground_predicate(predicate: object, env: Mapping[str, object]) -> object | None:
    if isinstance(predicate, Comparison):
        left = _eval_term(predicate.left, env)
        right = _eval_term(predicate.right, env)
        if left is None or right is None:
            return None
        try:
            value = _compare(predicate.op, left, right)
        except Exception:
            return None
        return _bool_pred(value)
    if isinstance(predicate, And):
        grounded = [_ground_predicate(item, env) for item in predicate.conjuncts]
        if any(item is None for item in grounded):
            return None
        return And(list(grounded)).simplify()
    if isinstance(predicate, Or):
        grounded = [_ground_predicate(item, env) for item in predicate.disjuncts]
        if any(item is None for item in grounded):
            return None
        return Or(list(grounded)).simplify()
    if isinstance(predicate, Not):
        inner = _ground_predicate(predicate.operand, env)
        return None if inner is None else Not(inner).simplify()
    if isinstance(predicate, NonEmpty):
        value = _eval_term(predicate.collection, env)
        return None if value is None else _bool_pred(len(value) > 0)
    if isinstance(predicate, Sorted):
        value = _eval_term(predicate.collection, env)
        return None if value is None else _bool_pred(list(value) == sorted(value, reverse=predicate.reverse))
    if isinstance(predicate, Unique):
        value = _eval_term(predicate.collection, env)
        return None if value is None else _bool_pred(len(list(value)) == len(set(value)))
    if isinstance(predicate, Contains):
        collection = _eval_term(predicate.collection, env)
        element = _eval_term(predicate.element, env)
        return None if collection is None or element is None else _bool_pred(element in collection)
    if isinstance(predicate, Subset):
        left = _eval_term(predicate.left, env)
        right = _eval_term(predicate.right, env)
        return None if left is None or right is None else _bool_pred(set(left).issubset(set(right)))
    if isinstance(predicate, Disjoint):
        left = _eval_term(predicate.left, env)
        right = _eval_term(predicate.right, env)
        return None if left is None or right is None else _bool_pred(set(left).isdisjoint(set(right)))
    if isinstance(predicate, Permutation):
        left = _eval_term(predicate.left, env)
        right = _eval_term(predicate.right, env)
        return None if left is None or right is None else _bool_pred(sorted(left) == sorted(right))
    if isinstance(predicate, IsNone):
        value = _eval_term(predicate.term, env)
        return None if value is None and not isinstance(predicate.term, NoneLit) and not _term_bound(predicate.term, env) else _bool_pred(value is None)
    if isinstance(predicate, IsNotNone):
        value = _eval_term(predicate.term, env)
        return None if value is None and not isinstance(predicate.term, NoneLit) and not _term_bound(predicate.term, env) else _bool_pred(value is not None)
    return None


def _term_bound(term: object, env: Mapping[str, object]) -> bool:
    return not isinstance(term, Var) or term.name in env


def _eval_term(term: object, env: Mapping[str, object]) -> object | None:
    if isinstance(term, Var):
        return env.get(term.name)
    if isinstance(term, IntLit):
        return term.value
    if isinstance(term, FloatLit):
        return term.value
    if isinstance(term, BoolLit):
        return term.value
    if isinstance(term, StrLit):
        return term.value
    if isinstance(term, NoneLit):
        return None
    if isinstance(term, Call) and term.func == "len" and len(term.args) == 1:
        arg = _eval_term(term.args[0], env)
        return None if arg is None else len(arg)
    if isinstance(term, BinOp):
        left = _eval_term(term.left, env)
        right = _eval_term(term.right, env)
        if left is None or right is None:
            return None
        if term.op == "+":
            return left + right
        if term.op == "-":
            return left - right
        if term.op == "*":
            return left * right
        if term.op == "//":
            return left // right
        if term.op == "%":
            return left % right
    return None


def _compare(op: str, left: object, right: object) -> bool:
    if op == ">":
        return left > right
    if op == ">=":
        return left >= right
    if op == "<":
        return left < right
    if op == "<=":
        return left <= right
    if op == "==":
        return left == right
    if op == "!=":
        return left != right
    raise ProofDecoratorConfigurationError(f"Unsupported comparison operator: {op}")
