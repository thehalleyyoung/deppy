"""
Deppy Pipeline — Module-level Safety Coverage Model (Gap 7)

Connects the ``ExceptionSourceFinder`` (which extracts every potential
exception site from a Python module) to the sidecar annotation system
(which records what an LLM has annotated about each function).

Produces a ``CoverageReport`` highlighting:
    * fully-annotated functions (all uncaught sources have matching
      ``raises_declarations`` or are covered by ``exception_free_when``),
    * partially-annotated functions (some sources unaddressed),
    * unannotated functions (sources exist but no sidecar spec present).

Also generates a ``.deppy`` template the LLM can fill in for any
unannotated function — driving incremental annotation.

Public API::

    from deppy.pipeline.safety_coverage import build_coverage
    report = build_coverage(source_code, sidecar_module)
    print(report.summary())
    template = report.deppy_template_for("mymod.foo")
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional

from deppy.core.kernel import ProofKernel
from deppy.pipeline.exception_sources import (
    ExceptionSource,
    FunctionSourceSummary,
    ModuleSourceSummary,
    find_exception_sources,
)
from deppy.pipeline.safety_predicates import (
    is_synthetic_predicate,
    safety_predicate_for,
)


@dataclass
class FunctionCoverage:
    """Coverage analysis for one function."""

    name: str
    total_sources: int
    uncaught_sources: list[ExceptionSource] = field(default_factory=list)
    addressed_sources: list[ExceptionSource] = field(default_factory=list)
    unaddressed_sources: list[ExceptionSource] = field(default_factory=list)
    has_sidecar: bool = False
    sidecar_declares_total: bool = False

    @property
    def is_fully_covered(self) -> bool:
        return not self.unaddressed_sources

    @property
    def coverage_ratio(self) -> float:
        n = len(self.uncaught_sources)
        if n == 0:
            return 1.0
        return len(self.addressed_sources) / n


@dataclass
class CoverageReport:
    """Module-wide coverage report."""

    module_path: str
    functions: dict[str, FunctionCoverage] = field(default_factory=dict)
    module_level_sources: list[ExceptionSource] = field(default_factory=list)

    # ── aggregate metrics ─────────────────────────────────────────

    @property
    def total_functions(self) -> int:
        return len(self.functions)

    @property
    def fully_covered(self) -> list[str]:
        return sorted(n for n, c in self.functions.items() if c.is_fully_covered)

    @property
    def partially_covered(self) -> list[str]:
        return sorted(
            n for n, c in self.functions.items()
            if c.has_sidecar and not c.is_fully_covered
        )

    @property
    def unannotated(self) -> list[str]:
        return sorted(
            n for n, c in self.functions.items()
            if not c.has_sidecar and c.uncaught_sources
        )

    @property
    def overall_coverage(self) -> float:
        funcs = [c for c in self.functions.values() if c.uncaught_sources]
        if not funcs:
            return 1.0
        return sum(c.coverage_ratio for c in funcs) / len(funcs)

    # ── output ────────────────────────────────────────────────────

    def summary(self) -> str:
        lines = [
            f"Coverage report for {self.module_path}",
            f"  total functions:   {self.total_functions}",
            f"  fully covered:     {len(self.fully_covered)}",
            f"  partially covered: {len(self.partially_covered)}",
            f"  unannotated:       {len(self.unannotated)}",
            f"  overall ratio:     {self.overall_coverage:.0%}",
        ]
        if self.unannotated:
            lines.append("  unannotated functions:")
            for n in self.unannotated[:10]:
                lines.append(f"    - {n} ({len(self.functions[n].uncaught_sources)} sources)")
        return "\n".join(lines)

    def deppy_template_for(self, func_name: str) -> str:
        """Generate a draft ``.deppy`` spec block for ``func_name``."""
        cov = self.functions.get(func_name)
        if cov is None:
            return f"# no source data for {func_name}\n"
        lines = [f"spec {func_name}:"]
        if cov.uncaught_sources:
            seen: set[tuple[str, str]] = set()
            for src in cov.uncaught_sources:
                cls = _exception_class_for(src)
                cond = safety_predicate_for(src)
                if not cond or cond in {"True", "False"}:
                    cond = src.trigger_condition or "TODO: describe trigger"
                key = (cls, cond)
                if key in seen:
                    continue
                seen.add(key)
                lines.append(f'    raises {cls}: when "{cond}"  # L{src.location.lineno}')
            if not seen:
                lines.append("    exception_free: true")
        else:
            lines.append("    exception_free: true")
        return "\n".join(lines) + "\n"

    def all_templates(self) -> str:
        return "\n".join(self.deppy_template_for(n) for n in self.unannotated)


# ───────────────────────── Helpers ─────────────────────────────────


def _exception_class_for(src: ExceptionSource) -> str:
    """Best-effort exception class name for a source."""
    name = src.kind.name
    table = {
        "ZERO_DIVISION": "ZeroDivisionError",
        "INDEX_ERROR": "IndexError",
        "KEY_ERROR": "KeyError",
        "ATTRIBUTE_ERROR": "AttributeError",
        "TYPE_ERROR": "TypeError",
        "VALUE_ERROR": "ValueError",
        "NAME_ERROR": "NameError",
        "OVERFLOW_ERROR": "OverflowError",
        "STOP_ITERATION": "StopIteration",
        "ASSERTION_ERROR": "AssertionError",
        "EXPLICIT_RAISE": "Exception",
        "CALL_PROPAGATION": "Exception",
    }
    return table.get(name, "Exception")


def _source_addressed_by_sidecar(src: ExceptionSource, spec) -> bool:
    """Per-source coverage check.

    A source is considered addressed by a sidecar spec when *any* of:

      * The spec declares ``is_total = True`` (escape hatch — caller asserts
        no exceptions ever escape, including this one).
      * The spec lists the matching exception class in ``raises_declarations``
        (the caller has documented that this exception can be raised, with a
        condition).
      * The spec gives an ``exception_free_when`` predicate AND that predicate
        plausibly addresses *this* exception kind.  We approximate plausibility
        by checking that the predicate string mentions the variable(s) used by
        the trigger condition (or, if no trigger, mentions any identifier from
        the source location's AST).

    The third clause is now **semantic**, not textual: the conjunction of
    ``exception_free_when`` predicates must imply the canonical safety
    predicate for *this* source (e.g. ``b > 0`` implies ``b != 0`` for
    division, but ``x > 0`` does not).
    """
    if spec is None:
        return False
    if getattr(spec, "is_total", False):
        return True
    target_cls = _exception_class_for(src)
    raises = getattr(spec, "raises_declarations", None) or []
    for cls, _cond in raises:
        if cls == target_cls or cls.endswith("." + target_cls):
            return True
    efw = list(getattr(spec, "exception_free_when", None) or [])
    if not efw:
        return False
    combined = " and ".join(f"({p})" for p in efw if p and p.strip()).strip()
    if not combined:
        return False
    safety_pred = _normalize_formula(safety_predicate_for(src))
    if not safety_pred or safety_pred == "False":
        return False
    if safety_pred == "True":
        return True
    combined = _normalize_formula(combined)
    if combined == safety_pred:
        return True
    if is_synthetic_predicate(safety_pred) or is_synthetic_predicate(combined):
        return False
    # CG7 cheat sweep (Issue 5): the safety predicate's free variables
    # must overlap the precondition's free variables.  Otherwise Z3
    # treats them as fresh (existentially-interpreted) names and may
    # spuriously prove ``(x>0) => (y!=0)`` when x,y are unrelated.
    if not _variables_overlap(combined, safety_pred):
        return False
    kernel = ProofKernel()
    return bool(kernel._z3_check(f"({combined}) => ({safety_pred})"))


def _free_names(expr: str) -> set[str]:
    """Best-effort free-name extraction; returns empty on parse failure."""
    import ast as _ast
    try:
        tree = _ast.parse(expr, mode="eval")
    except SyntaxError:
        return set()
    return {n.id for n in _ast.walk(tree) if isinstance(n, _ast.Name)}


def _variables_overlap(pre: str, pred: str) -> bool:
    pre_names = _free_names(pre) - {"True", "False", "None", "and", "or", "not"}
    pred_names = _free_names(pred) - {"True", "False", "None", "and", "or", "not"}
    if not pred_names:
        return True  # predicate is constant; precondition cannot constrain it but vacuity OK
    return bool(pre_names & pred_names)


def _normalize_formula(text: str) -> str:
    text = (text or "").strip()
    if "#" in text:
        text = text.split("#", 1)[0].rstrip()
    return text


# ───────────────────────── Public API ──────────────────────────────


def build_coverage(
    source: str,
    sidecar_specs: Optional[dict] = None,
    module_path: str = "<module>",
) -> CoverageReport:
    """Build a module-level safety coverage report.

    Args:
        source: Python source code as a string.
        sidecar_specs: Optional mapping ``{func_name: ExternalSpec}``.
        module_path: Display name for the module.

    Returns:
        A ``CoverageReport`` summarising annotation coverage.
    """
    sidecar_specs = sidecar_specs or {}
    summary: ModuleSourceSummary = find_exception_sources(source)
    report = CoverageReport(
        module_path=module_path,
        module_level_sources=list(summary.module_level_sources),
    )

    for fn_summary in summary.functions:
        spec = sidecar_specs.get(fn_summary.name)
        addressed: list[ExceptionSource] = []
        unaddressed: list[ExceptionSource] = []
        for src in fn_summary.uncaught_sources:
            if _source_addressed_by_sidecar(src, spec):
                addressed.append(src)
            else:
                unaddressed.append(src)
        report.functions[fn_summary.name] = FunctionCoverage(
            name=fn_summary.name,
            total_sources=fn_summary.total_sources,
            uncaught_sources=list(fn_summary.uncaught_sources),
            addressed_sources=addressed,
            unaddressed_sources=unaddressed,
            has_sidecar=spec is not None,
            sidecar_declares_total=bool(getattr(spec, "is_total", False)),
        )
    return report


__all__ = [
    "FunctionCoverage",
    "CoverageReport",
    "build_coverage",
]
