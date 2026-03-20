"""Pillar 9 — Benchmark suite of 50 LLM-generated artifacts with ground-truth
hallucination labels.

Each example carries a human-assigned label (artifact_kind, category,
hallucinations) so any checker function can be scored against ground truth.
"""
from __future__ import annotations

import hashlib
import math
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, FrozenSet, List, Optional, Tuple


# ---------------------------------------------------------------------------
# Data containers
# ---------------------------------------------------------------------------


# --- Integration with existing deppy codebase ---
try:
    from deppy.pipeline import analyze_source
    from deppy.refinement_engine import refine, verify
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False

@dataclass(frozen=True)
class HallucinationExample:
    """A single benchmark artifact with ground-truth hallucination labels."""

    id: str
    artifact_kind: str  # "code", "text", or "data"
    category: str       # e.g. "clean_code", "hallucinated_api", …
    artifact: str       # the LLM-generated content
    spec: str           # what it was supposed to be
    hallucinations: Tuple[Dict[str, str], ...]  # ground truth findings
    expected_structural_findings: int
    expected_semantic_findings: int

    @property
    def content_hash(self) -> str:
        return hashlib.sha256(self.artifact.encode()).hexdigest()[:16]

    @property
    def total_expected(self) -> int:
        return self.expected_structural_findings + self.expected_semantic_findings

    @property
    def is_clean(self) -> bool:
        return len(self.hallucinations) == 0


@dataclass
class BenchmarkResult:
    """Aggregated result of running a checker against the suite."""

    precision: float
    recall: float
    f1: float
    per_kind: Dict[str, Dict[str, float]]   # kind → {precision, recall, f1}
    confusion_matrix: Dict[str, Dict[str, int]]  # predicted × actual counts
    total_examples: int = 0
    total_findings: int = 0
    total_ground_truth: int = 0
    false_positives: int = 0
    false_negatives: int = 0

    def summary(self) -> str:
        lines = [
            "=== Hallucination Benchmark Results ===",
            f"  Examples evaluated : {self.total_examples}",
            f"  Ground-truth items : {self.total_ground_truth}",
            f"  Findings reported  : {self.total_findings}",
            f"  Precision          : {self.precision:.3f}",
            f"  Recall             : {self.recall:.3f}",
            f"  F1                 : {self.f1:.3f}",
            f"  False positives    : {self.false_positives}",
            f"  False negatives    : {self.false_negatives}",
            "",
            "--- Per-kind breakdown ---",
        ]
        for kind, scores in sorted(self.per_kind.items()):
            lines.append(
                f"  {kind:25s}  P={scores['precision']:.3f}  "
                f"R={scores['recall']:.3f}  F1={scores['f1']:.3f}"
            )
        return "\n".join(lines)


# ---------------------------------------------------------------------------
# Helper to build examples compactly
# ---------------------------------------------------------------------------

def _ex(
    id: str,
    kind: str,
    category: str,
    artifact: str,
    spec: str,
    hallucinations: List[Dict[str, str]],
    structural: int,
    semantic: int,
) -> HallucinationExample:
    return HallucinationExample(
        id=id,
        artifact_kind=kind,
        category=category,
        artifact=artifact,
        spec=spec,
        hallucinations=tuple(hallucinations),
        expected_structural_findings=structural,
        expected_semantic_findings=semantic,
    )


# ---------------------------------------------------------------------------
# The suite itself — 50 examples across 10 categories
# ---------------------------------------------------------------------------

class HallucinationSuite:
    """50 curated hallucination benchmark examples across 10 categories."""

    def __init__(self) -> None:
        self.examples: List[HallucinationExample] = []
        self._populate()

    # -- public API ---------------------------------------------------------

    def get_by_kind(self, kind: str) -> List[HallucinationExample]:
        """Filter examples by artifact_kind (code / text / data)."""
        return [e for e in self.examples if e.artifact_kind == kind]

    def get_by_category(self, category: str) -> List[HallucinationExample]:
        """Filter examples by hallucination category."""
        return [e for e in self.examples if e.category == category]

    def categories(self) -> List[str]:
        return sorted({e.category for e in self.examples})

    def evaluate(self, checker_fn: Callable[[str, str], List[Dict[str, str]]]) -> BenchmarkResult:
        """Run *checker_fn(artifact, spec)* on every example and score.

        *checker_fn* must return a list of dicts, each with at least a
        ``kind`` key (matching hallucination kind strings) so we can compute
        per-kind precision / recall / F1.
        """
        kind_tp: Dict[str, int] = {}
        kind_fp: Dict[str, int] = {}
        kind_fn: Dict[str, int] = {}
        confusion: Dict[str, Dict[str, int]] = {}
        total_findings = 0
        total_gt = 0

        for ex in self.examples:
            findings = checker_fn(ex.artifact, ex.spec)
            total_findings += len(findings)
            total_gt += len(ex.hallucinations)

            gt_kinds = [h["kind"] for h in ex.hallucinations]
            found_kinds = [f.get("kind", "unknown") for f in findings]

            gt_bag = _count(gt_kinds)
            found_bag = _count(found_kinds)

            all_kinds = set(gt_bag) | set(found_bag)
            for k in all_kinds:
                kind_tp.setdefault(k, 0)
                kind_fp.setdefault(k, 0)
                kind_fn.setdefault(k, 0)
                tp = min(gt_bag.get(k, 0), found_bag.get(k, 0))
                kind_tp[k] += tp
                kind_fp[k] += found_bag.get(k, 0) - tp
                kind_fn[k] += gt_bag.get(k, 0) - tp

            for fk in found_kinds:
                for gk in gt_kinds:
                    confusion.setdefault(fk, {})
                    confusion[fk].setdefault(gk, 0)
                    confusion[fk][gk] += 1

        per_kind: Dict[str, Dict[str, float]] = {}
        global_tp = global_fp = global_fn = 0
        for k in sorted(set(kind_tp) | set(kind_fp) | set(kind_fn)):
            tp = kind_tp.get(k, 0)
            fp = kind_fp.get(k, 0)
            fn = kind_fn.get(k, 0)
            global_tp += tp
            global_fp += fp
            global_fn += fn
            p = tp / (tp + fp) if (tp + fp) else 0.0
            r = tp / (tp + fn) if (tp + fn) else 0.0
            f = 2 * p * r / (p + r) if (p + r) else 0.0
            per_kind[k] = {"precision": p, "recall": r, "f1": f}

        precision = global_tp / (global_tp + global_fp) if (global_tp + global_fp) else 0.0
        recall = global_tp / (global_tp + global_fn) if (global_tp + global_fn) else 0.0
        f1 = 2 * precision * recall / (precision + recall) if (precision + recall) else 0.0

        return BenchmarkResult(
            precision=precision,
            recall=recall,
            f1=f1,
            per_kind=per_kind,
            confusion_matrix=confusion,
            total_examples=len(self.examples),
            total_findings=total_findings,
            total_ground_truth=total_gt,
            false_positives=global_fp,
            false_negatives=global_fn,
        )

    # -- private: populate the 50 examples ----------------------------------

    def _populate(self) -> None:
        self._add_clean_code()
        self._add_hallucinated_apis()
        self._add_wrong_field_names()
        self._add_logic_errors()
        self._add_fabricated_citations()
        self._add_fabricated_numbers()
        self._add_type_errors()
        self._add_schema_violations()
        self._add_inconsistencies()
        self._add_drift()
        assert len(self.examples) == 50, (
            f"Expected 50 examples, got {len(self.examples)}"
        )

    # ---- Category 1: Clean code (5 examples) -----------------------------

    def _add_clean_code(self) -> None:
        self.examples.append(_ex(
            id="clean-001",
            kind="code",
            category="clean_code",
            artifact=(
                "def binary_search(arr: list[int], target: int) -> int:\n"
                "    lo, hi = 0, len(arr) - 1\n"
                "    while lo <= hi:\n"
                "        mid = (lo + hi) // 2\n"
                "        if arr[mid] == target:\n"
                "            return mid\n"
                "        elif arr[mid] < target:\n"
                "            lo = mid + 1\n"
                "        else:\n"
                "            hi = mid - 1\n"
                "    return -1\n"
            ),
            spec="Correct binary search returning index or -1.",
            hallucinations=[],
            structural=0,
            semantic=0,
        ))

        self.examples.append(_ex(
            id="clean-002",
            kind="code",
            category="clean_code",
            artifact=(
                "def merge_sort(xs: list[int]) -> list[int]:\n"
                "    if len(xs) <= 1:\n"
                "        return xs\n"
                "    mid = len(xs) // 2\n"
                "    left = merge_sort(xs[:mid])\n"
                "    right = merge_sort(xs[mid:])\n"
                "    return _merge(left, right)\n"
                "\n"
                "def _merge(a: list[int], b: list[int]) -> list[int]:\n"
                "    result: list[int] = []\n"
                "    i = j = 0\n"
                "    while i < len(a) and j < len(b):\n"
                "        if a[i] <= b[j]:\n"
                "            result.append(a[i])\n"
                "            i += 1\n"
                "        else:\n"
                "            result.append(b[j])\n"
                "            j += 1\n"
                "    result.extend(a[i:])\n"
                "    result.extend(b[j:])\n"
                "    return result\n"
            ),
            spec="Merge sort — correct, stable, O(n log n).",
            hallucinations=[],
            structural=0,
            semantic=0,
        ))

        self.examples.append(_ex(
            id="clean-003",
            kind="code",
            category="clean_code",
            artifact=(
                "import json\n"
                "\n"
                "def load_config(path: str) -> dict:\n"
                "    with open(path, 'r') as f:\n"
                "        return json.load(f)\n"
            ),
            spec="Load a JSON config file and return as dict.",
            hallucinations=[],
            structural=0,
            semantic=0,
        ))

        self.examples.append(_ex(
            id="clean-004",
            kind="text",
            category="clean_code",
            artifact=(
                "Binary search runs in O(log n) time because each comparison "
                "halves the remaining search space.  It requires the input "
                "array to be sorted."
            ),
            spec="Accurate description of binary search complexity.",
            hallucinations=[],
            structural=0,
            semantic=0,
        ))

        self.examples.append(_ex(
            id="clean-005",
            kind="data",
            category="clean_code",
            artifact=(
                '{"name": "Alice", "age": 30, "email": "alice@example.com"}'
            ),
            spec="Valid user JSON with name, age, email.",
            hallucinations=[],
            structural=0,
            semantic=0,
        ))

    # ---- Category 2: Hallucinated APIs (5 examples) ----------------------

    def _add_hallucinated_apis(self) -> None:
        self.examples.append(_ex(
            id="api-001",
            kind="code",
            category="hallucinated_api",
            artifact=(
                "import torch\n"
                "encoder = torch.nn.TransfomerEncoder(\n"
                "    torch.nn.TransfomerEncoderLayer(d_model=512, nhead=8),\n"
                "    num_layers=6\n"
                ")\n"
            ),
            spec="Use torch.nn.TransformerEncoder (correct spelling).",
            hallucinations=[
                {"kind": "hallucinated_api", "location": "line 2",
                 "description": "TransfomerEncoder is misspelled — correct name is TransformerEncoder."},
                {"kind": "hallucinated_api", "location": "line 3",
                 "description": "TransfomerEncoderLayer is misspelled — correct name is TransformerEncoderLayer."},
            ],
            structural=2,
            semantic=0,
        ))

        self.examples.append(_ex(
            id="api-002",
            kind="code",
            category="hallucinated_api",
            artifact=(
                "import numpy as np\n"
                "arr = np.array([3, 1, 2])\n"
                "arr.sort_inplace()\n"
            ),
            spec="Sort a numpy array in-place. Correct API is arr.sort().",
            hallucinations=[
                {"kind": "hallucinated_api", "location": "line 3",
                 "description": "sort_inplace does not exist; use arr.sort()."},
            ],
            structural=1,
            semantic=0,
        ))

        self.examples.append(_ex(
            id="api-003",
            kind="code",
            category="hallucinated_api",
            artifact=(
                "import os\n"
                "full = os.path.joinpath('/home', 'user', 'data')\n"
            ),
            spec="Join path components. Correct API is os.path.join.",
            hallucinations=[
                {"kind": "hallucinated_api", "location": "line 2",
                 "description": "os.path.joinpath does not exist; use os.path.join."},
            ],
            structural=1,
            semantic=0,
        ))

        self.examples.append(_ex(
            id="api-004",
            kind="code",
            category="hallucinated_api",
            artifact=(
                "import collections\n"
                "counter = collections.FrequencyCounter(['a', 'b', 'a'])\n"
            ),
            spec="Use collections.Counter to count elements.",
            hallucinations=[
                {"kind": "hallucinated_api", "location": "line 2",
                 "description": "FrequencyCounter does not exist; use collections.Counter."},
            ],
            structural=1,
            semantic=0,
        ))

        self.examples.append(_ex(
            id="api-005",
            kind="code",
            category="hallucinated_api",
            artifact=(
                "import itertools\n"
                "pairs = itertools.pairwise_combinations(range(5), 2)\n"
            ),
            spec="Generate pairwise combinations. Correct API is itertools.combinations.",
            hallucinations=[
                {"kind": "hallucinated_api", "location": "line 2",
                 "description": "pairwise_combinations does not exist; use itertools.combinations."},
            ],
            structural=1,
            semantic=0,
        ))

    # ---- Category 3: Wrong field names (5 examples) ----------------------

    def _add_wrong_field_names(self) -> None:
        self.examples.append(_ex(
            id="field-001",
            kind="code",
            category="wrong_field_name",
            artifact=(
                "user = get_user(id=42)\n"
                "print(user.name)\n"
            ),
            spec="Access user.display_name (the actual field on the User model).",
            hallucinations=[
                {"kind": "wrong_field", "location": "line 2",
                 "description": "Field is display_name, not name."},
            ],
            structural=1,
            semantic=0,
        ))

        self.examples.append(_ex(
            id="field-002",
            kind="code",
            category="wrong_field_name",
            artifact=(
                "response = api.get('/items')\n"
                "for item in response.items:\n"
                "    process(item)\n"
            ),
            spec="API returns response.results, not response.items.",
            hallucinations=[
                {"kind": "wrong_field", "location": "line 2",
                 "description": "response.items does not exist; use response.results."},
            ],
            structural=1,
            semantic=0,
        ))

        self.examples.append(_ex(
            id="field-003",
            kind="code",
            category="wrong_field_name",
            artifact=(
                "config = load_config()\n"
                "db_url = config.database_url\n"
            ),
            spec="Config uses config.db_connection_string.",
            hallucinations=[
                {"kind": "wrong_field", "location": "line 2",
                 "description": "database_url does not exist; use db_connection_string."},
            ],
            structural=1,
            semantic=0,
        ))

        self.examples.append(_ex(
            id="field-004",
            kind="code",
            category="wrong_field_name",
            artifact=(
                "event = get_event()\n"
                "start = event.start_time\n"
                "end = event.end_time\n"
            ),
            spec="Event model uses starts_at / ends_at.",
            hallucinations=[
                {"kind": "wrong_field", "location": "line 2",
                 "description": "start_time should be starts_at."},
                {"kind": "wrong_field", "location": "line 3",
                 "description": "end_time should be ends_at."},
            ],
            structural=2,
            semantic=0,
        ))

        self.examples.append(_ex(
            id="field-005",
            kind="code",
            category="wrong_field_name",
            artifact=(
                "order = get_order(order_id)\n"
                "total = order.total_price\n"
            ),
            spec="Order model uses order.amount_due.",
            hallucinations=[
                {"kind": "wrong_field", "location": "line 2",
                 "description": "total_price does not exist; use amount_due."},
            ],
            structural=1,
            semantic=0,
        ))

    # ---- Category 4: Logic errors (5 examples) ---------------------------

    def _add_logic_errors(self) -> None:
        self.examples.append(_ex(
            id="logic-001",
            kind="code",
            category="logic_error",
            artifact=(
                "def find_max(arr: list[int]) -> int:\n"
                "    best = 0\n"
                "    for x in arr:\n"
                "        if x > best:\n"
                "            best = x\n"
                "    return best\n"
            ),
            spec="Find maximum value — should handle negatives (init with arr[0] or -inf).",
            hallucinations=[
                {"kind": "logic_error", "location": "line 2",
                 "description": "Initializing best=0 fails for all-negative arrays."},
            ],
            structural=0,
            semantic=1,
        ))

        self.examples.append(_ex(
            id="logic-002",
            kind="code",
            category="logic_error",
            artifact=(
                "def is_palindrome(s: str) -> bool:\n"
                "    for i in range(len(s)):\n"
                "        if s[i] != s[len(s) - i]:\n"
                "            return False\n"
                "    return True\n"
            ),
            spec="Check palindrome — off-by-one: should be s[len(s)-1-i].",
            hallucinations=[
                {"kind": "logic_error", "location": "line 3",
                 "description": "Off-by-one: s[len(s)-i] → IndexError; use s[len(s)-1-i]."},
            ],
            structural=1,
            semantic=0,
        ))

        self.examples.append(_ex(
            id="logic-003",
            kind="code",
            category="logic_error",
            artifact=(
                "def gcd(a: int, b: int) -> int:\n"
                "    while b != 0:\n"
                "        a, b = b, a % a\n"
                "    return a\n"
            ),
            spec="Euclidean GCD — should be a % b, not a % a.",
            hallucinations=[
                {"kind": "logic_error", "location": "line 3",
                 "description": "a % a is always 0 — should be a % b. Causes infinite loop or wrong result."},
            ],
            structural=0,
            semantic=1,
        ))

        self.examples.append(_ex(
            id="logic-004",
            kind="code",
            category="logic_error",
            artifact=(
                "def unique_elements(lst: list) -> list:\n"
                "    seen = set()\n"
                "    result = []\n"
                "    for x in lst:\n"
                "        if x not in seen:\n"
                "            result.append(x)\n"
                "            # forgot seen.add(x)\n"
                "    return result\n"
            ),
            spec="Return unique elements. Missing seen.add(x) means duplicates are kept.",
            hallucinations=[
                {"kind": "logic_error", "location": "line 6-7",
                 "description": "Missing seen.add(x) after appending — duplicates not removed."},
            ],
            structural=0,
            semantic=1,
        ))

        self.examples.append(_ex(
            id="logic-005",
            kind="code",
            category="logic_error",
            artifact=(
                "def clamp(value: float, lo: float, hi: float) -> float:\n"
                "    if value < lo:\n"
                "        return hi\n"
                "    if value > hi:\n"
                "        return lo\n"
                "    return value\n"
            ),
            spec="Clamp value to [lo, hi]. Returns are swapped — should return lo/hi respectively.",
            hallucinations=[
                {"kind": "logic_error", "location": "line 3",
                 "description": "Returns hi when value < lo; should return lo."},
                {"kind": "logic_error", "location": "line 5",
                 "description": "Returns lo when value > hi; should return hi."},
            ],
            structural=0,
            semantic=2,
        ))

    # ---- Category 5: Fabricated citations (5 examples) --------------------

    def _add_fabricated_citations(self) -> None:
        self.examples.append(_ex(
            id="cite-001",
            kind="text",
            category="fabricated_citation",
            artifact=(
                "As shown by Henderson et al. (2021), 'On the Convergence of "
                "Adam-Style Optimizers in Non-Convex Settings', arXiv:2103.99847, "
                "Adam converges under mild assumptions."
            ),
            spec="Cite a real paper. arXiv:2103.99847 does not exist.",
            hallucinations=[
                {"kind": "fabricated_citation", "location": "arXiv ID",
                 "description": "arXiv:2103.99847 is fabricated."},
            ],
            structural=1,
            semantic=0,
        ))

        self.examples.append(_ex(
            id="cite-002",
            kind="text",
            category="fabricated_citation",
            artifact=(
                "The Transformer architecture was introduced in 'Attention Is All "
                "You Need' (Vaswani et al., 2017).  A follow-up by Vaswani et al. "
                "(2019), 'Transformers Without Self-Attention', arXiv:1901.55432, "
                "removed self-attention entirely."
            ),
            spec="Only cite real papers. The 2019 paper is fabricated.",
            hallucinations=[
                {"kind": "fabricated_citation", "location": "second citation",
                 "description": "'Transformers Without Self-Attention' arXiv:1901.55432 is fabricated."},
            ],
            structural=1,
            semantic=0,
        ))

        self.examples.append(_ex(
            id="cite-003",
            kind="text",
            category="fabricated_citation",
            artifact=(
                "According to the landmark survey by Goodfellow et al. (2020), "
                "'A Comprehensive Survey of Generative Adversarial Networks', "
                "published in Nature Machine Intelligence vol. 7, pp. 112-140, "
                "GANs have been applied to over 500 domains."
            ),
            spec="Cite real publications. This journal volume/page is fabricated.",
            hallucinations=[
                {"kind": "fabricated_citation", "location": "journal reference",
                 "description": "Nature Machine Intelligence vol. 7 pp. 112-140 is fabricated."},
            ],
            structural=1,
            semantic=0,
        ))

        self.examples.append(_ex(
            id="cite-004",
            kind="text",
            category="fabricated_citation",
            artifact=(
                "Theorem 4.3 of Rudin's 'Principles of Mathematical Analysis' "
                "(3rd ed., 1976) proves that every Cauchy sequence in a complete "
                "metric space converges.  Theorem 11.42 extends this to "
                "non-Archimedean fields."
            ),
            spec="Rudin's book has no Theorem 11.42 on non-Archimedean fields.",
            hallucinations=[
                {"kind": "fabricated_citation", "location": "Theorem 11.42",
                 "description": "Theorem 11.42 on non-Archimedean fields is fabricated."},
            ],
            structural=0,
            semantic=1,
        ))

        self.examples.append(_ex(
            id="cite-005",
            kind="text",
            category="fabricated_citation",
            artifact=(
                "Smith and Jones (2022), 'Dependent Types for Large Language "
                "Models', Proceedings of POPL 2022, showed that refinement types "
                "can encode hallucination freedom."
            ),
            spec="No such paper appeared at POPL 2022.",
            hallucinations=[
                {"kind": "fabricated_citation", "location": "full citation",
                 "description": "Paper 'Dependent Types for LLMs' at POPL 2022 is entirely fabricated."},
            ],
            structural=1,
            semantic=0,
        ))

    # ---- Category 6: Fabricated numbers (5 examples) ---------------------

    def _add_fabricated_numbers(self) -> None:
        self.examples.append(_ex(
            id="num-001",
            kind="text",
            category="fabricated_number",
            artifact=(
                "Our model achieves 99.97% top-1 accuracy on ImageNet, "
                "surpassing all previous methods by a wide margin."
            ),
            spec="ImageNet SOTA top-1 is ~91%. 99.97% is impossible.",
            hallucinations=[
                {"kind": "fabricated_number", "location": "accuracy claim",
                 "description": "99.97% top-1 on ImageNet is fabricated; SOTA is ~91%."},
            ],
            structural=0,
            semantic=1,
        ))

        self.examples.append(_ex(
            id="num-002",
            kind="text",
            category="fabricated_number",
            artifact=(
                "GPT-4 has 1.8 trillion parameters according to the "
                "official OpenAI technical report."
            ),
            spec="OpenAI has not disclosed GPT-4's parameter count.",
            hallucinations=[
                {"kind": "fabricated_number", "location": "parameter count",
                 "description": "1.8 trillion parameters is unverified; OpenAI did not disclose this."},
            ],
            structural=0,
            semantic=1,
        ))

        self.examples.append(_ex(
            id="num-003",
            kind="text",
            category="fabricated_number",
            artifact=(
                "The Python standard library contains 4,218 modules as of "
                "Python 3.12."
            ),
            spec="The exact number of stdlib modules is much smaller (~300).",
            hallucinations=[
                {"kind": "fabricated_number", "location": "module count",
                 "description": "4,218 modules is fabricated; Python stdlib has ~300 top-level modules."},
            ],
            structural=0,
            semantic=1,
        ))

        self.examples.append(_ex(
            id="num-004",
            kind="text",
            category="fabricated_number",
            artifact=(
                "Rust compilation speeds improved by 340% between versions "
                "1.60 and 1.70, averaging 0.3 seconds per crate."
            ),
            spec="340% improvement and 0.3s average are fabricated metrics.",
            hallucinations=[
                {"kind": "fabricated_number", "location": "improvement claim",
                 "description": "340% compilation speed improvement is fabricated."},
                {"kind": "fabricated_number", "location": "average time",
                 "description": "0.3 seconds per crate average is fabricated."},
            ],
            structural=0,
            semantic=2,
        ))

        self.examples.append(_ex(
            id="num-005",
            kind="data",
            category="fabricated_number",
            artifact=(
                '{"benchmark": "MMLU", "score": 98.6, "model": "ExampleLLM-7B"}'
            ),
            spec="MMLU SOTA is ~90%. A 7B model at 98.6% is impossible.",
            hallucinations=[
                {"kind": "fabricated_number", "location": "score field",
                 "description": "98.6 MMLU for a 7B model is fabricated."},
            ],
            structural=0,
            semantic=1,
        ))

    # ---- Category 7: Type errors (5 examples) ----------------------------

    def _add_type_errors(self) -> None:
        self.examples.append(_ex(
            id="type-001",
            kind="code",
            category="type_error",
            artifact=(
                "def get_user_age(user_id: int) -> int:\n"
                "    user = lookup(user_id)\n"
                "    if user is None:\n"
                "        return 'unknown'\n"
                "    return user.age\n"
            ),
            spec="Return type is int, but returns str 'unknown' for missing user.",
            hallucinations=[
                {"kind": "type_error", "location": "line 4",
                 "description": "Returns str 'unknown' but declared return type is int."},
            ],
            structural=1,
            semantic=0,
        ))

        self.examples.append(_ex(
            id="type-002",
            kind="code",
            category="type_error",
            artifact=(
                "def average(nums: list[float]) -> float:\n"
                "    if not nums:\n"
                "        return None\n"
                "    return sum(nums) / len(nums)\n"
            ),
            spec="Return type is float but returns None for empty list.",
            hallucinations=[
                {"kind": "type_error", "location": "line 3",
                 "description": "Returns None but declared return type is float, not Optional[float]."},
            ],
            structural=1,
            semantic=0,
        ))

        self.examples.append(_ex(
            id="type-003",
            kind="code",
            category="type_error",
            artifact=(
                "def concat_ids(ids: list[int]) -> str:\n"
                "    return ','.join(ids)\n"
            ),
            spec="str.join expects Iterable[str] but ids is list[int].",
            hallucinations=[
                {"kind": "type_error", "location": "line 2",
                 "description": "join requires strings but ids contains ints; needs map(str, ids)."},
            ],
            structural=1,
            semantic=0,
        ))

        self.examples.append(_ex(
            id="type-004",
            kind="code",
            category="type_error",
            artifact=(
                "def parse_count(raw: str) -> int:\n"
                "    parts = raw.split(',')\n"
                "    return parts\n"
            ),
            spec="Should return int but returns list[str].",
            hallucinations=[
                {"kind": "type_error", "location": "line 3",
                 "description": "Returns list[str] from split() but declared return type is int."},
            ],
            structural=1,
            semantic=0,
        ))

        self.examples.append(_ex(
            id="type-005",
            kind="code",
            category="type_error",
            artifact=(
                "def safe_divide(a: float, b: float) -> float:\n"
                "    if b == 0:\n"
                "        return 'division by zero'\n"
                "    return a / b\n"
            ),
            spec="Return type is float but error case returns str.",
            hallucinations=[
                {"kind": "type_error", "location": "line 3",
                 "description": "Returns str 'division by zero' but declared return is float."},
            ],
            structural=1,
            semantic=0,
        ))

    # ---- Category 8: Schema violations (5 examples) ----------------------

    def _add_schema_violations(self) -> None:
        self.examples.append(_ex(
            id="schema-001",
            kind="data",
            category="schema_violation",
            artifact=(
                '{"name": "Alice", "email": "alice@example.com"}'
            ),
            spec='Required fields: name, age, email.  Missing "age".',
            hallucinations=[
                {"kind": "schema_violation", "location": "root",
                 "description": "Missing required field 'age'."},
            ],
            structural=1,
            semantic=0,
        ))

        self.examples.append(_ex(
            id="schema-002",
            kind="data",
            category="schema_violation",
            artifact=(
                '{"name": "Bob", "age": "thirty", "email": "bob@example.com"}'
            ),
            spec='Field "age" must be an integer, not a string.',
            hallucinations=[
                {"kind": "schema_violation", "location": "age",
                 "description": "age is string 'thirty' but schema requires integer."},
            ],
            structural=1,
            semantic=0,
        ))

        self.examples.append(_ex(
            id="schema-003",
            kind="data",
            category="schema_violation",
            artifact=(
                '{"users": [{"id": 1, "name": "A"}, {"id": "two", "name": "B"}]}'
            ),
            spec='Each user.id must be an integer.',
            hallucinations=[
                {"kind": "schema_violation", "location": "users[1].id",
                 "description": "id is string 'two' but schema requires integer."},
            ],
            structural=1,
            semantic=0,
        ))

        self.examples.append(_ex(
            id="schema-004",
            kind="data",
            category="schema_violation",
            artifact=(
                '{"status": "active", "items": [], "metadata": null}'
            ),
            spec='metadata must be an object (dict), not null.',
            hallucinations=[
                {"kind": "schema_violation", "location": "metadata",
                 "description": "metadata is null but schema requires object."},
            ],
            structural=1,
            semantic=0,
        ))

        self.examples.append(_ex(
            id="schema-005",
            kind="data",
            category="schema_violation",
            artifact=(
                '{"temperature": 25, "unit": "kelvin", "timestamp": "not-a-date"}'
            ),
            spec='timestamp must be ISO-8601 date string.',
            hallucinations=[
                {"kind": "schema_violation", "location": "timestamp",
                 "description": "timestamp 'not-a-date' is not valid ISO-8601."},
            ],
            structural=1,
            semantic=0,
        ))

    # ---- Category 9: Inconsistencies (5 examples) ------------------------

    def _add_inconsistencies(self) -> None:
        self.examples.append(_ex(
            id="incon-001",
            kind="code",
            category="inconsistency",
            artifact=(
                "def sort_list(xs: list[int]) -> list[int]:\n"
                '    """Sort the list in O(n log n) time using merge sort."""\n'
                "    for i in range(len(xs)):\n"
                "        for j in range(i + 1, len(xs)):\n"
                "            if xs[j] < xs[i]:\n"
                "                xs[i], xs[j] = xs[j], xs[i]\n"
                "    return xs\n"
            ),
            spec="Docstring says O(n log n) merge sort but code is O(n²) selection sort.",
            hallucinations=[
                {"kind": "inconsistency", "location": "docstring vs code",
                 "description": "Docstring claims O(n log n) merge sort; code is O(n²) selection sort."},
            ],
            structural=0,
            semantic=1,
        ))

        self.examples.append(_ex(
            id="incon-002",
            kind="code",
            category="inconsistency",
            artifact=(
                "def fibonacci(n: int) -> int:\n"
                '    """Return the n-th Fibonacci number.  Uses memoization for O(n) time."""\n'
                "    if n <= 1:\n"
                "        return n\n"
                "    return fibonacci(n - 1) + fibonacci(n - 2)\n"
            ),
            spec="Docstring claims memoization but code has none — O(2^n) not O(n).",
            hallucinations=[
                {"kind": "inconsistency", "location": "docstring vs code",
                 "description": "Claims memoization but uses naive recursion (exponential)."},
            ],
            structural=0,
            semantic=1,
        ))

        self.examples.append(_ex(
            id="incon-003",
            kind="code",
            category="inconsistency",
            artifact=(
                "def reverse_string(s: str) -> str:\n"
                '    """Reverse the string in-place without extra memory."""\n'
                "    return s[::-1]\n"
            ),
            spec="Docstring says 'in-place without extra memory' but slicing creates a new string.",
            hallucinations=[
                {"kind": "inconsistency", "location": "docstring vs code",
                 "description": "Claims in-place reversal but s[::-1] creates a new string object."},
            ],
            structural=0,
            semantic=1,
        ))

        self.examples.append(_ex(
            id="incon-004",
            kind="code",
            category="inconsistency",
            artifact=(
                "# Thread-safe counter implementation\n"
                "class Counter:\n"
                "    def __init__(self) -> None:\n"
                "        self.value = 0\n"
                "    def increment(self) -> None:\n"
                "        self.value += 1\n"
            ),
            spec="Comment says thread-safe but no lock is used.",
            hallucinations=[
                {"kind": "inconsistency", "location": "comment vs code",
                 "description": "Comment claims thread-safe but increment is not atomic and has no lock."},
            ],
            structural=0,
            semantic=1,
        ))

        self.examples.append(_ex(
            id="incon-005",
            kind="code",
            category="inconsistency",
            artifact=(
                "def search(data: list, key: str) -> bool:\n"
                '    """Perform binary search on the data list."""\n'
                "    for item in data:\n"
                "        if item == key:\n"
                "            return True\n"
                "    return False\n"
            ),
            spec="Docstring says binary search but code is linear scan.",
            hallucinations=[
                {"kind": "inconsistency", "location": "docstring vs code",
                 "description": "Claims binary search but implements linear scan."},
            ],
            structural=0,
            semantic=1,
        ))

    # ---- Category 10: Drift / deprecated API (5 examples) ----------------

    def _add_drift(self) -> None:
        self.examples.append(_ex(
            id="drift-001",
            kind="code",
            category="drift",
            artifact=(
                "import asyncio\n"
                "loop = asyncio.get_event_loop()\n"
                "loop.run_until_complete(main())\n"
            ),
            spec="get_event_loop() is deprecated since Python 3.10; use asyncio.run().",
            hallucinations=[
                {"kind": "drift", "location": "line 2",
                 "description": "asyncio.get_event_loop() deprecated; use asyncio.run()."},
            ],
            structural=1,
            semantic=0,
        ))

        self.examples.append(_ex(
            id="drift-002",
            kind="code",
            category="drift",
            artifact=(
                "from collections import MutableMapping\n"
                "class Config(MutableMapping):\n"
                "    pass\n"
            ),
            spec="MutableMapping moved to collections.abc in Python 3.3+; removed in 3.10.",
            hallucinations=[
                {"kind": "drift", "location": "line 1",
                 "description": "collections.MutableMapping removed in 3.10; use collections.abc.MutableMapping."},
            ],
            structural=1,
            semantic=0,
        ))

        self.examples.append(_ex(
            id="drift-003",
            kind="code",
            category="drift",
            artifact=(
                "import unittest\n"
                "class Tests(unittest.TestCase):\n"
                "    def test_equal(self):\n"
                "        self.assertEquals(1 + 1, 2)\n"
            ),
            spec="assertEquals is deprecated; use assertEqual (no trailing s).",
            hallucinations=[
                {"kind": "drift", "location": "line 4",
                 "description": "assertEquals deprecated; use assertEqual."},
            ],
            structural=1,
            semantic=0,
        ))

        self.examples.append(_ex(
            id="drift-004",
            kind="code",
            category="drift",
            artifact=(
                "import typing\n"
                "def greet(name: typing.Optional[str] = None) -> str:\n"
                "    return f'Hello, {name or \"World\"}'\n"
            ),
            spec="Since Python 3.10, use str | None instead of typing.Optional[str].",
            hallucinations=[
                {"kind": "drift", "location": "line 2",
                 "description": "typing.Optional deprecated in favour of X | None (PEP 604)."},
            ],
            structural=1,
            semantic=0,
        ))

        self.examples.append(_ex(
            id="drift-005",
            kind="code",
            category="drift",
            artifact=(
                "import os\n"
                "encoding = os.popen('locale charmap').read().strip()\n"
            ),
            spec="os.popen is legacy; use subprocess.run.",
            hallucinations=[
                {"kind": "drift", "location": "line 2",
                 "description": "os.popen is deprecated; use subprocess.run or subprocess.check_output."},
            ],
            structural=1,
            semantic=0,
        ))


# ---------------------------------------------------------------------------
# Utilities
# ---------------------------------------------------------------------------

def _count(items: List[str]) -> Dict[str, int]:
    """Frequency counter without importing collections."""
    bag: Dict[str, int] = {}
    for item in items:
        bag[item] = bag.get(item, 0) + 1
    return bag


# ---------------------------------------------------------------------------
# Self-test
# ---------------------------------------------------------------------------

def _self_test() -> None:
    suite = HallucinationSuite()
    assert len(suite.examples) == 50

    # Category counts
    cats = suite.categories()
    assert len(cats) == 10, f"Expected 10 categories, got {len(cats)}"
    for cat in cats:
        group = suite.get_by_category(cat)
        assert len(group) == 5, f"Category {cat!r} has {len(group)} examples, expected 5"

    # Artifact kinds
    code_examples = suite.get_by_kind("code")
    text_examples = suite.get_by_kind("text")
    data_examples = suite.get_by_kind("data")
    assert len(code_examples) + len(text_examples) + len(data_examples) == 50

    # Clean examples have zero expected findings
    for ex in suite.get_by_category("clean_code"):
        assert ex.is_clean
        assert ex.total_expected == 0

    # Non-clean examples have at least one hallucination
    for ex in suite.examples:
        if ex.category != "clean_code":
            assert len(ex.hallucinations) > 0, f"{ex.id} should have hallucinations"

    # Evaluate with a dummy checker that always returns nothing
    def null_checker(artifact: str, spec: str) -> List[Dict[str, str]]:
        return []

    result = suite.evaluate(null_checker)
    assert result.precision == 0.0 or result.total_findings == 0
    assert result.recall == 0.0
    assert result.total_examples == 50

    # Evaluate with a perfect checker (returns ground truth)
    def perfect_checker(artifact: str, spec: str) -> List[Dict[str, str]]:
        for ex in suite.examples:
            if ex.artifact == artifact and ex.spec == spec:
                return [dict(h) for h in ex.hallucinations]
        return []

    perfect_result = suite.evaluate(perfect_checker)
    assert abs(perfect_result.precision - 1.0) < 1e-9
    assert abs(perfect_result.recall - 1.0) < 1e-9
    assert abs(perfect_result.f1 - 1.0) < 1e-9

    print("hallucination_suite: all self-tests passed ✓")


if __name__ == "__main__":
    _self_test()
