from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import List


@dataclass(frozen=True)
class ExampleSpec:
    name: str
    filename: str
    expected_mismatch_codes: List[str] = field(default_factory=list)
    expected_heap_targets: List[str] = field(default_factory=list)
    expected_proof_goals: List[str] = field(default_factory=list)
    expected_core_proved: bool = False
    note: str = ""


EXAMPLES = [
    ExampleSpec(
        name='return_type_mismatch',
        filename='return_type_mismatch.py',
        expected_mismatch_codes=['return-type-mismatch'],
        note='Simple return mismatch that should always be caught.',
    ),
    ExampleSpec(
        name='protocol_mismatch',
        filename='protocol_mismatch.py',
        expected_mismatch_codes=['call-argument-mismatch'],
        note='Native Python protocol mismatch through a regular class.',
    ),
    ExampleSpec(
        name='heap_field_mismatch',
        filename='heap_field_mismatch.py',
        expected_mismatch_codes=['attribute-assignment-mismatch'],
        expected_heap_targets=['self.value'],
        note='Heap write violates a declared field type.',
    ),
    ExampleSpec(
        name='safe_guarded_head',
        filename='safe_guarded_head.py',
        note='Low-annotation example that should pass static mismatch checking.',
    ),
    ExampleSpec(
        name='constructor_usage_bug',
        filename='constructor_usage_bug.py',
        expected_mismatch_codes=['call-argument-mismatch'],
        note='Direct constructor-typed call mismatch.',
    ),
    ExampleSpec(
        name='native_box_ok',
        filename='native_box_ok.py',
        expected_heap_targets=['self.value'],
        note='Nominal class/heap example with no mismatch diagnostics.',
    ),
    ExampleSpec(
        name='pytorch_sort_proof_goal',
        filename='pytorch_sort_proof_goal.py',
        expected_proof_goals=['sorted(result)', 'perm(result, xs)'],
        note='TensorGuard-style sorting module whose semantic correctness is expressible as dependent proof goals.',
    ),
    ExampleSpec(
        name='pytorch_sort_bad_return',
        filename='pytorch_sort_bad_return.py',
        expected_mismatch_codes=['return-type-mismatch'],
        expected_proof_goals=['sorted(result)', 'perm(result, xs)'],
        note='TensorGuard-style sorting module with an obvious return bug that static analysis should catch.',
    ),

    ExampleSpec(
        name='dependent_sigma_witness',
        filename='dependent_sigma_witness.py',
        expected_core_proved=True,
        note='Non-refinement dependent example using a Sigma return type.',
    ),
    ExampleSpec(
        name='pytorch_shape_bug_from_tensorguard',
        filename='pytorch_shape_bug_from_tensorguard.py',
        note='A direct TensorGuard-style shape bug example illustrating a limitation of the current native-Python mismatch layer.',
    ),
    ExampleSpec(
        name='pytorch_unannotated_sort_inference_bug',
        filename='pytorch_unannotated_sort_inference_bug.py',
        expected_mismatch_codes=['assignment-mismatch'],
        expected_proof_goals=['sorted(result)', 'perm(result, xs)'],
        note='Unannotated PyTorch example where DepPy infers sorted-value semantics and catches mixing values with sort indices.',
    ),
    ExampleSpec(
        name='heap_protocol_branch_bug',
        filename='heap_protocol_branch_bug.py',
        expected_mismatch_codes=[
            'attribute-assignment-mismatch',
            'return-type-mismatch',
            'call-argument-mismatch',
        ],
        expected_heap_targets=['self.cached', 'self.shadow'],
        note='Heap-sensitive branch update plus protocol misuse to exercise CFG/heap SSA and static mismatch checking together.',
    ),
    ExampleSpec(
        name='pytorch_multi_pack_unannotated',
        filename='pytorch_multi_pack_unannotated.py',
        note='Unannotated PyTorch showcase covering the split sort, shape, and indexing theory packs in one corpus file.',
    ),
    ExampleSpec(
        name='mixed_mode_sort_equivalence',
        filename='mixed_mode_sort_equivalence.py',
        expected_proof_goals=['sorted(result)', 'perm(result, xs)'],
        note='Places proof-explicit and unannotated PyTorch sort implementations side-by-side to benchmark mixed-mode semantic alignment.',
    ),
    ExampleSpec(
        name='pytorch_long_capability_audit',
        filename='pytorch_long_capability_audit.py',
        expected_mismatch_codes=['call-argument-mismatch', 'assignment-mismatch'],
        note='Long-form capability audit showing automatic semantic inference, synthesized annotations, alias-forwarding propagation, nested trigger detection, and composed downstream theory activation.',
    ),
]


def examples_root() -> Path:
    return Path(__file__).resolve().parent
