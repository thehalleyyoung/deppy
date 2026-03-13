"""Cohomology-guided test generation.

Uses H¹ obstruction classes from the spec verifier to identify
*untested behavioral boundaries* and generate targeted tests
that exercise exactly those boundaries.

Each H¹ class corresponds to a Čech cycle in the spec cover —
a loop of overlapping conjuncts where the proof transfer failed.
This cycle represents a behavioral boundary that existing proofs
don't cover, making it the highest-priority target for testing.

Usage:
    from deppy.render.cohomology_test_gen import generate_targeted_tests
    tests = generate_targeted_tests(verification_result)
    for t in tests:
        print(t.code)
"""

from __future__ import annotations

import ast
import random
import textwrap
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Set, Tuple


@dataclass
class TargetedTest:
    """A test generated to exercise a specific H¹ boundary."""
    test_name: str
    code: str
    target_conjunct: str       # Which spec conjunct this targets
    target_site: int           # Cover site index
    boundary_description: str  # What behavioral boundary this tests
    h1_class: int              # Which H¹ class this addresses
    priority: float = 1.0      # Higher = more important to test

    def format(self) -> str:
        return (
            f"# Target: {self.boundary_description}\n"
            f"# H¹ class {self.h1_class}, site {self.target_site}\n"
            f"# Priority: {self.priority:.2f}\n"
            f"{self.code}")


@dataclass
class TestGenerationResult:
    """Result of cohomology-guided test generation."""
    function_name: str
    tests: List[TargetedTest] = field(default_factory=list)
    h1_classes_targeted: int = 0
    total_h1_classes: int = 0
    inconclusive_sites: int = 0
    coverage_before: float = 0.0  # Proof coverage before tests
    coverage_after: float = 0.0   # Expected coverage after tests

    def summary(self) -> str:
        lines = [
            f"Cohomology-guided test generation: {self.function_name}",
            f"  H¹ classes targeted: "
            f"{self.h1_classes_targeted}/{self.total_h1_classes}",
            f"  Inconclusive VCs covered: {self.inconclusive_sites}",
            f"  Proof coverage: {self.coverage_before:.0%} → "
            f"{self.coverage_after:.0%} (expected)",
            f"  Tests generated: {len(self.tests)}",
        ]
        for t in self.tests:
            lines.append(f"    {t.test_name}: {t.boundary_description}")
        return "\n".join(lines)


def generate_targeted_tests(
    verification_result,  # SpecVerificationResult
    *,
    max_tests: int = 20,
    seed: int = 42,
) -> TestGenerationResult:
    """Generate tests targeting H¹ obstruction classes.

    For each inconclusive or failed VC, generate a test that exercises
    the corresponding behavioral boundary.
    """
    rng = random.Random(seed)

    vr = verification_result
    func_name = vr.function_name
    spec_name = vr.spec_name

    # Count proof status
    n_proved = vr.n_vcs_proved
    n_total = vr.n_vcs_total
    coverage_before = n_proved / n_total if n_total > 0 else 1.0

    # Find inconclusive and failed VCs — these are the H¹ boundaries
    target_sites: List[Tuple[int, Any]] = []
    for i, vcr in enumerate(vr.vc_results):
        if vcr is None:
            continue
        if not vcr.proved and "refuted" not in vcr.method:
            target_sites.append((i, vcr))

    # Group by conjunct (H¹ classes correspond to conjunct cycles)
    conjunct_groups: Dict[int, List[Tuple[int, Any]]] = {}
    if vr.cover:
        for i, vcr in target_sites:
            site = vr.cover.sites[i] if i < len(vr.cover.sites) else None
            conj_idx = site.conjunct_idx if site else i
            conjunct_groups.setdefault(conj_idx, []).append((i, vcr))
    else:
        for i, vcr in target_sites:
            conjunct_groups.setdefault(i, []).append((i, vcr))

    tests: List[TargetedTest] = []
    h1_classes = len(conjunct_groups)

    for class_idx, (conj_idx, sites) in enumerate(conjunct_groups.items()):
        if len(tests) >= max_tests:
            break

        # Get the conjunct text
        conj_text = ""
        if vr.spec_decomposition and conj_idx < len(vr.spec_decomposition.conjuncts):
            conj = vr.spec_decomposition.conjuncts[conj_idx]
            conj_text = conj.source

        # Generate a test for the most important site in this class
        site_idx, vcr = sites[0]
        boundary_desc = _describe_boundary(conj_text, vcr)

        # Generate test inputs based on conjunct analysis
        test_inputs = _generate_boundary_inputs(
            conj_text, vr.impl_analysis, rng)

        # Build test code
        test_code = _build_test_code(
            func_name, spec_name, test_inputs, conj_text, class_idx)

        tests.append(TargetedTest(
            test_name=f"test_{func_name}_h1_class_{class_idx}",
            code=test_code,
            target_conjunct=conj_text,
            target_site=site_idx,
            boundary_description=boundary_desc,
            h1_class=class_idx,
            priority=1.0 / (1 + len(sites)),  # More sites = harder
        ))

    # Sort by priority
    tests.sort(key=lambda t: -t.priority)

    expected_coverage = coverage_before + (1 - coverage_before) * 0.5 * (
        len(tests) / max(len(conjunct_groups), 1))

    return TestGenerationResult(
        function_name=func_name,
        tests=tests,
        h1_classes_targeted=min(len(tests), h1_classes),
        total_h1_classes=h1_classes,
        inconclusive_sites=len(target_sites),
        coverage_before=coverage_before,
        coverage_after=min(expected_coverage, 1.0),
    )


def _describe_boundary(conj_text: str, vcr) -> str:
    """Describe the behavioral boundary a conjunct represents."""
    if not conj_text:
        return f"Inconclusive VC ({vcr.method})"

    # Extract key predicates from the conjunct
    if "sorted" in conj_text.lower():
        return "Sorting invariant boundary"
    if "len(" in conj_text:
        return "Length preservation boundary"
    if ">=" in conj_text or "<=" in conj_text:
        return "Inequality bound boundary"
    if "==" in conj_text:
        return "Equality constraint boundary"
    if "in " in conj_text:
        return "Membership/containment boundary"
    if "is_" in conj_text or "has_" in conj_text:
        return "Structural property boundary"

    # Truncate long text
    if len(conj_text) > 60:
        return f"Spec conjunct: {conj_text[:57]}..."
    return f"Spec conjunct: {conj_text}"


def _generate_boundary_inputs(
    conj_text: str,
    impl_analysis,  # Optional[ImplAnalysis]
    rng: random.Random,
) -> List[str]:
    """Generate test inputs that exercise a behavioral boundary.

    Uses the conjunct text to infer what kind of inputs will
    hit the boundary: empty lists, zero values, negative indices, etc.
    """
    inputs = []

    # Detect boundary-relevant patterns
    if "empty" in conj_text.lower() or "len(" in conj_text:
        inputs.append("[]")
        inputs.append("[1]")
        inputs.append("[1, 2, 3]")

    if "sorted" in conj_text.lower():
        inputs.append("[3, 1, 2]")
        inputs.append("[1, 2, 3]")
        inputs.append("[]")

    if "0" in conj_text or "zero" in conj_text.lower():
        inputs.append("0")
        inputs.append("1")
        inputs.append("-1")

    if "negative" in conj_text.lower() or "< 0" in conj_text:
        inputs.append("-1")
        inputs.append("0")
        inputs.append("1")

    if not inputs:
        # Generic boundary inputs
        inputs.extend(["[]", "[1]", "[1, 2, 3]", "0", "1", "-1"])

    return inputs[:6]


def _build_test_code(
    func_name: str,
    spec_name: str,
    inputs: List[str],
    conj_text: str,
    class_idx: int,
) -> str:
    """Build a Python test function."""
    lines = [f"def test_{func_name}_h1_class_{class_idx}():"]
    lines.append(f'    """Target H¹ class {class_idx}: {conj_text[:60]}"""')

    if inputs:
        for i, inp in enumerate(inputs):
            lines.append(f"    # Boundary input {i}")
            lines.append(f"    result_{i} = {func_name}({inp})")
            if spec_name:
                lines.append(
                    f"    assert {spec_name}({inp}, result_{i}), "
                    f'"Failed on input {inp}"')
    else:
        lines.append(f"    result = {func_name}()")
        if spec_name:
            lines.append(f"    assert {spec_name}(result)")

    return "\n".join(lines)
