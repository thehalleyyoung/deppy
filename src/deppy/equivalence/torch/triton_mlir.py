"""
MLIR dialect equivalence checker — lowering functor presheaf.

Models MLIR lowering as a chain of functors between dialect categories:
  - Objects: MLIR operations in each dialect
  - Morphisms: dialect lowering steps (e.g., Triton → TritonGPU → LLVM)
  - Sections: operation semantics at each dialect level
  - Equivalence: semantic preservation across the lowering chain

The lowering chain forms a category of categories (a 2-category):
  Triton → TritonGPU → TritonNVIDIA → LLVM
Each step is a functor; equivalence requires the composite functor
to preserve semantics (i.e., the diagram commutes).

Since MLIR is not directly available, this module works via text-based
parsing of MLIR assembly format (.mlir files).
"""

from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple

from ._protocols import (
    AnalysisJudgment,
    AnalysisMode,
    AnalysisVerdict,
    Bug,
    BugKind,
    EquivalenceVerdict,
    MLIRDialect,
    MLIRLoweringStep,
    MLIRModuleSpec,
    MLIROpSpec,
    ProgramId,
    SheafConditionResult,
    SiteId,
    SiteKind,
    TensorEquivalenceConfig,
    TensorLocalJudgment,
    TensorObstruction,
    TensorObstructionKind,
    TensorSiteKind,
    TensorStratum,
)


# ---------------------------------------------------------------------------
# MLIR text parser
# ---------------------------------------------------------------------------

# Standard MLIR op pattern: "dialect.op_name"(%arg0, ...) : (types) -> types
_OP_PATTERN = re.compile(
    r'"?(\w+)\.(\w+)"?\s*'      # dialect.op_name
    r'(?:\(([^)]*)\)|'           # operands in parens  OR
    r'([^:{]*))'                 # operands without parens (up to : or {)
    r'\s*(?::\s*(.+?))?'         # optional type annotation
    r'\s*$'
)

_FUNC_PATTERN = re.compile(r'func\.func\s+@(\w+)')
_MODULE_PATTERN = re.compile(r'module\s*(?:@(\w+))?')
_BLOCK_PATTERN = re.compile(r'\^(\w+)(?:\(([^)]*)\))?:')
_RESULT_PATTERN = re.compile(r'%(\w+)(?::(\d+))?\s*=\s*')


@dataclass
class MLIROperation:
    """A parsed MLIR operation."""
    dialect: str
    op_name: str
    operands: List[str]
    result_names: List[str]
    operand_types: List[str]
    result_types: List[str]
    attributes: Dict[str, str]
    regions: int = 0
    line_number: int = 0


@dataclass
class MLIRFunction:
    """A parsed MLIR function."""
    name: str
    args: List[Tuple[str, str]]  # (name, type)
    return_types: List[str]
    operations: List[MLIROperation]
    blocks: List[str]


@dataclass
class MLIRModule:
    """A parsed MLIR module."""
    name: str
    functions: List[MLIRFunction]
    dialect_ops: Dict[str, int]  # dialect.op -> count
    total_ops: int = 0


class MLIRTextParser:
    """
    Parses MLIR assembly text into structured form.

    This is the *observation functor* from MLIR text to the dialect site.
    Each parsed operation becomes a site; the dialect hierarchy generates
    morphisms (lowering steps between dialects).
    """

    def parse(self, text: str, name: str = "") -> MLIRModule:
        """Parse an MLIR module from text."""
        lines = text.strip().split("\n")

        functions: List[MLIRFunction] = []
        dialect_ops: Dict[str, int] = {}
        total_ops = 0
        module_name = name

        # Check for module declaration
        for line in lines:
            m = _MODULE_PATTERN.match(line.strip())
            if m and m.group(1):
                module_name = m.group(1)
                break

        # Parse functions
        current_func: Optional[MLIRFunction] = None
        current_ops: List[MLIROperation] = []
        current_blocks: List[str] = []

        for line_no, line in enumerate(lines, 1):
            stripped = line.strip()
            if not stripped or stripped.startswith("//"):
                continue

            # Function start
            func_match = _FUNC_PATTERN.search(stripped)
            if func_match:
                if current_func is not None:
                    current_func.operations = current_ops
                    current_func.blocks = current_blocks
                    functions.append(current_func)
                current_func = MLIRFunction(
                    name=func_match.group(1),
                    args=[], return_types=[],
                    operations=[], blocks=[],
                )
                current_ops = []
                current_blocks = []
                continue

            # Block label
            block_match = _BLOCK_PATTERN.search(stripped)
            if block_match:
                current_blocks.append(block_match.group(1))
                continue

            # Operation
            op = self._parse_operation(stripped, line_no)
            if op is not None:
                current_ops.append(op)
                total_ops += 1
                key = f"{op.dialect}.{op.op_name}"
                dialect_ops[key] = dialect_ops.get(key, 0) + 1

        # Finalize last function
        if current_func is not None:
            current_func.operations = current_ops
            current_func.blocks = current_blocks
            functions.append(current_func)

        return MLIRModule(
            name=module_name,
            functions=functions,
            dialect_ops=dialect_ops,
            total_ops=total_ops,
        )

    def _parse_operation(self, line: str, line_no: int) -> Optional[MLIROperation]:
        """Parse a single MLIR operation from a line."""
        # Check for result assignment
        result_names = []
        result_match = _RESULT_PATTERN.match(line)
        if result_match:
            result_names.append(f"%{result_match.group(1)}")
            line = line[result_match.end():]

        # Match the operation
        op_match = _OP_PATTERN.search(line)
        if op_match:
            dialect = op_match.group(1)
            op_name = op_match.group(2)
            # Group 3 = parens operands, Group 4 = bare operands
            operands_str = op_match.group(3) or op_match.group(4) or ""
            type_str = op_match.group(5) or ""

            operands = [o.strip() for o in operands_str.split(",") if o.strip()]
            # For MLIR, the type annotation after : describes both operand and result types
            result_types = [t.strip() for t in type_str.split("->")[-1].split(",")
                           if t.strip()] if "->" in type_str else []
            operand_types = [t.strip() for t in type_str.split("->")[0].split(",")
                            if t.strip()] if type_str else []

            attrs = self._parse_attributes(line)

            return MLIROperation(
                dialect=dialect,
                op_name=op_name,
                operands=operands,
                result_names=result_names,
                operand_types=operand_types,
                result_types=result_types,
                attributes=attrs,
                line_number=line_no,
            )
        return None

    def _parse_attributes(self, line: str) -> Dict[str, str]:
        """Parse attributes from an MLIR operation line."""
        attrs = {}
        # Look for {key = value, ...} blocks
        brace_match = re.search(r'\{([^}]+)\}', line)
        if brace_match:
            for part in brace_match.group(1).split(","):
                if "=" in part:
                    k, v = part.split("=", 1)
                    attrs[k.strip()] = v.strip()
        return attrs


# ---------------------------------------------------------------------------
# MLIR module spec builder
# ---------------------------------------------------------------------------

def build_mlir_module_spec(text: str, name: str = "") -> MLIRModuleSpec:
    """Build an MLIRModuleSpec from MLIR assembly text."""
    parser = MLIRTextParser()
    module = parser.parse(text, name)

    dialect_ops_dict: Dict[MLIRDialect, List[MLIROpSpec]] = {}
    for func in module.functions:
        for op in func.operations:
            mlir_dialect = _map_dialect(op.dialect)
            spec = MLIROpSpec(
                dialect=mlir_dialect,
                op_name=op.op_name,
                operand_types=tuple(op.operand_types),
                result_types=tuple(op.result_types),
                attributes=op.attributes,
                regions=op.regions,
            )
            dialect_ops_dict.setdefault(mlir_dialect, []).append(spec)

    # Infer lowering chain from present dialects
    present_dialects = set(dialect_ops_dict.keys())
    lowering_chain = _infer_lowering_chain(present_dialects)

    return MLIRModuleSpec(
        name=module.name or name,
        dialect_ops=dialect_ops_dict,
        lowering_chain=lowering_chain,
        source_text=text,
    )


def _map_dialect(name: str) -> MLIRDialect:
    """Map a dialect name string to MLIRDialect enum."""
    _MAP = {
        "triton": MLIRDialect.TRITON,
        "tt": MLIRDialect.TRITON,
        "triton_gpu": MLIRDialect.TRITON_GPU,
        "ttg": MLIRDialect.TRITON_GPU,
        "triton_nvidia": MLIRDialect.TRITON_NVIDIA,
        "ttn": MLIRDialect.TRITON_NVIDIA,
        "linalg": MLIRDialect.LINALG,
        "scf": MLIRDialect.SCFG,
        "arith": MLIRDialect.ARITH,
        "memref": MLIRDialect.MEMREF,
        "llvm": MLIRDialect.LLVM,
        "builtin": MLIRDialect.BUILTIN,
        "func": MLIRDialect.BUILTIN,
    }
    return _MAP.get(name.lower(), MLIRDialect.BUILTIN)


def _infer_lowering_chain(dialects: Set[MLIRDialect]) -> List[MLIRLoweringStep]:
    """Infer the lowering chain from present dialects."""
    # Standard Triton lowering: Triton → TritonGPU → LLVM
    chain = []
    ordered = [
        MLIRDialect.TRITON,
        MLIRDialect.TRITON_GPU,
        MLIRDialect.TRITON_NVIDIA,
        MLIRDialect.LLVM,
    ]
    present_ordered = [d for d in ordered if d in dialects]

    for i in range(len(present_ordered) - 1):
        chain.append(MLIRLoweringStep(
            source_dialect=present_ordered[i],
            target_dialect=present_ordered[i + 1],
            pass_name=f"lower-{present_ordered[i].name}-to-{present_ordered[i+1].name}",
            preserves_semantics=True,
        ))
    return chain


# ---------------------------------------------------------------------------
# MLIR operation fingerprint
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class MLIROpFingerprint:
    """Structural fingerprint of MLIR operations in a module."""
    op_histogram: Tuple[Tuple[str, int], ...]
    n_ops: int
    n_functions: int
    n_blocks: int
    dialects_present: Tuple[str, ...]
    lowering_depth: int


def compute_mlir_fingerprint(module: Any) -> MLIROpFingerprint:
    """Compute structural fingerprint of an MLIR module.

    Accepts both ``MLIRModule`` (parser output) and ``MLIRModuleSpec``
    (spec output).
    """
    # Handle both MLIRModule (parser) and MLIRModuleSpec (spec) types.
    if hasattr(module, "functions"):
        # Parser output: MLIRModule
        n_blocks = sum(len(f.blocks) for f in module.functions)
        dialects = sorted(set(
            op.dialect for f in module.functions for op in f.operations
        ))
        n_functions = len(module.functions)
        op_histogram = tuple(sorted(module.dialect_ops.items()))
        total_ops = module.total_ops
    else:
        # Spec output: MLIRModuleSpec
        n_blocks = 0
        dialects = sorted(str(d) for d in module.dialects_used)
        n_functions = 0
        op_histogram = tuple(
            sorted(
                (str(dialect) + "." + op.op_name, 1)
                for dialect, ops in module.dialect_ops.items()
                for op in ops
            )
        )
        total_ops = module.op_count

    return MLIROpFingerprint(
        op_histogram=op_histogram,
        n_ops=total_ops,
        n_functions=n_functions,
        n_blocks=n_blocks,
        dialects_present=tuple(dialects),
        lowering_depth=len(set(dialects)),
    )


# ---------------------------------------------------------------------------
# MLIR equivalence checker
# ---------------------------------------------------------------------------

class MLIREquivalenceChecker:
    """
    Checks equivalence of two MLIR modules.

    This implements the presheaf comparison on the dialect site category:
    1. Parse both modules into structured form
    2. Compare operation histograms (dialect-level section comparison)
    3. Compare lowering chains (functor composition)
    4. Check semantic preservation across lowering steps

    Sheaf-theoretically, MLIR lowering is a chain of functors:
      F₁: Cat(Triton) → Cat(TritonGPU)
      F₂: Cat(TritonGPU) → Cat(LLVM)
    Two modules are equivalent iff their images under the composite
    functor F₂ ∘ F₁ are naturally isomorphic.
    """

    def __init__(self, config: TensorEquivalenceConfig):
        self._config = config
        self._parser = MLIRTextParser()

    def check_site(
        self,
        spec_f: MLIRModuleSpec,
        spec_g: MLIRModuleSpec,
        site_id: SiteId,
    ) -> TensorLocalJudgment:
        """Check MLIR module equivalence at a site."""
        obstructions: List[TensorObstruction] = []

        # Parse both modules
        module_f = self._parser.parse(spec_f.source_text or "", spec_f.name)
        module_g = self._parser.parse(spec_g.source_text or "", spec_g.name)

        # 1. Operation histogram comparison
        fp_f = compute_mlir_fingerprint(module_f)
        fp_g = compute_mlir_fingerprint(module_g)

        if fp_f.op_histogram != fp_g.op_histogram:
            obstructions.append(TensorObstruction(
                kind=TensorObstructionKind.MLIR_OP_MISMATCH,
                stratum=TensorStratum.STRUCTURAL,
                sites=(site_id,),
                description=(f"Op histogram differs: "
                             f"f has {fp_f.n_ops} ops, g has {fp_g.n_ops} ops"),
            ))

        if fp_f.dialects_present != fp_g.dialects_present:
            obstructions.append(TensorObstruction(
                kind=TensorObstructionKind.MLIR_OP_MISMATCH,
                stratum=TensorStratum.STRUCTURAL,
                sites=(site_id,),
                description=(f"Dialects differ: "
                             f"f uses {fp_f.dialects_present}, "
                             f"g uses {fp_g.dialects_present}"),
            ))

        # 2. Lowering chain comparison
        if spec_f.lowering_chain != spec_g.lowering_chain:
            # Check if the chains are equivalent up to pass names
            f_chain = [(s.source_dialect, s.target_dialect) for s in spec_f.lowering_chain]
            g_chain = [(s.source_dialect, s.target_dialect) for s in spec_g.lowering_chain]
            if f_chain != g_chain:
                obstructions.append(TensorObstruction(
                    kind=TensorObstructionKind.MLIR_LOWERING_MISMATCH,
                    stratum=TensorStratum.STRUCTURAL,
                    sites=(site_id,),
                    description="Lowering chains differ",
                ))

        # 3. Function structure comparison
        if len(module_f.functions) != len(module_g.functions):
            obstructions.append(TensorObstruction(
                kind=TensorObstructionKind.MLIR_OP_MISMATCH,
                stratum=TensorStratum.STRUCTURAL,
                sites=(site_id,),
                description=(f"Function count: "
                             f"{len(module_f.functions)} vs "
                             f"{len(module_g.functions)}"),
            ))
        else:
            for f_func, g_func in zip(module_f.functions, module_g.functions):
                func_obs = self._compare_functions(f_func, g_func, site_id)
                obstructions.extend(func_obs)

        if obstructions:
            return TensorLocalJudgment(
                site_id=site_id,
                stratum=TensorStratum.STRUCTURAL,
                tensor_site_kind=TensorSiteKind.MLIR_OP,
                verdict=EquivalenceVerdict.INEQUIVALENT,
                explanation=f"MLIR module differs ({len(obstructions)} issues)",
                obstructions=tuple(obstructions),
            )

        return TensorLocalJudgment(
            site_id=site_id,
            stratum=TensorStratum.STRUCTURAL,
            tensor_site_kind=TensorSiteKind.MLIR_OP,
            verdict=EquivalenceVerdict.EQUIVALENT,
            explanation="MLIR modules structurally equivalent",
        )

    def check_lowering_site(
        self,
        spec_f: MLIRModuleSpec,
        spec_g: MLIRModuleSpec,
        site_id: SiteId,
    ) -> TensorLocalJudgment:
        """
        Check that the lowering functor preserves semantic equivalence.

        For each step in the lowering chain, verify that the
        source-level equivalence is preserved at the target level.
        This is the *functor preservation* condition.
        """
        obstructions: List[TensorObstruction] = []

        # Compare lowering steps
        f_steps = list(spec_f.lowering_chain)
        g_steps = list(spec_g.lowering_chain)

        if len(f_steps) != len(g_steps):
            obstructions.append(TensorObstruction(
                kind=TensorObstructionKind.MLIR_LOWERING_MISMATCH,
                stratum=TensorStratum.STRUCTURAL,
                sites=(site_id,),
                description=(f"Lowering depth: {len(f_steps)} vs {len(g_steps)}"),
            ))
        else:
            for i, (sf, sg) in enumerate(zip(f_steps, g_steps)):
                if sf.source_dialect != sg.source_dialect:
                    obstructions.append(TensorObstruction(
                        kind=TensorObstructionKind.MLIR_LOWERING_MISMATCH,
                        stratum=TensorStratum.STRUCTURAL,
                        sites=(site_id,),
                        description=(f"Step {i}: source dialect "
                                     f"{sf.source_dialect} vs {sg.source_dialect}"),
                    ))
                if sf.target_dialect != sg.target_dialect:
                    obstructions.append(TensorObstruction(
                        kind=TensorObstructionKind.MLIR_LOWERING_MISMATCH,
                        stratum=TensorStratum.STRUCTURAL,
                        sites=(site_id,),
                        description=(f"Step {i}: target dialect "
                                     f"{sf.target_dialect} vs {sg.target_dialect}"),
                    ))
                if sf.preserves_semantics != sg.preserves_semantics:
                    obstructions.append(TensorObstruction(
                        kind=TensorObstructionKind.MLIR_LOWERING_MISMATCH,
                        stratum=TensorStratum.STRUCTURAL,
                        sites=(site_id,),
                        description=(f"Step {i}: semantic preservation "
                                     f"f={sf.preserves_semantics}, "
                                     f"g={sg.preserves_semantics}"),
                    ))

        if obstructions:
            return TensorLocalJudgment(
                site_id=site_id,
                stratum=TensorStratum.STRUCTURAL,
                tensor_site_kind=TensorSiteKind.MLIR_OP,
                verdict=EquivalenceVerdict.INEQUIVALENT,
                explanation="MLIR lowering chain differs",
                obstructions=tuple(obstructions),
            )

        return TensorLocalJudgment(
            site_id=site_id,
            stratum=TensorStratum.STRUCTURAL,
            tensor_site_kind=TensorSiteKind.MLIR_OP,
            verdict=EquivalenceVerdict.EQUIVALENT,
            explanation="MLIR lowering chains equivalent",
        )

    def _compare_functions(self, f_func: MLIRFunction,
                           g_func: MLIRFunction,
                           site_id: SiteId) -> List[TensorObstruction]:
        """Compare two MLIR functions."""
        obs: List[TensorObstruction] = []

        if len(f_func.operations) != len(g_func.operations):
            obs.append(TensorObstruction(
                kind=TensorObstructionKind.MLIR_OP_MISMATCH,
                stratum=TensorStratum.STRUCTURAL,
                sites=(site_id,),
                description=(f"Function {f_func.name}: op count "
                             f"{len(f_func.operations)} vs "
                             f"{len(g_func.operations)}"),
            ))
            return obs

        for i, (f_op, g_op) in enumerate(zip(f_func.operations, g_func.operations)):
            if f_op.dialect != g_op.dialect or f_op.op_name != g_op.op_name:
                obs.append(TensorObstruction(
                    kind=TensorObstructionKind.MLIR_OP_MISMATCH,
                    stratum=TensorStratum.STRUCTURAL,
                    sites=(site_id,),
                    description=(f"Op {i}: {f_op.dialect}.{f_op.op_name} vs "
                                 f"{g_op.dialect}.{g_op.op_name}"),
                ))

        return obs

    # ------------------------------------------------------------------
    # Single-program analysis
    # ------------------------------------------------------------------

    # Canonical lowering order from high-level to low-level dialects
    _DIALECT_LEVEL: Dict[MLIRDialect, int] = {
        MLIRDialect.TRITON: 0,
        MLIRDialect.TRITON_GPU: 1,
        MLIRDialect.TRITON_NVIDIA: 2,
        MLIRDialect.LINALG: 1,
        MLIRDialect.SCFG: 2,
        MLIRDialect.ARITH: 3,
        MLIRDialect.MEMREF: 3,
        MLIRDialect.LLVM: 4,
        MLIRDialect.BUILTIN: 5,
    }

    def analyze(
        self,
        spec: MLIRModuleSpec,
        site_id: Optional[SiteId] = None,
    ) -> AnalysisJudgment:
        """Analyze a single MLIR module for validity issues.

        Checks for valid lowering chain (each step goes to a lower
        dialect), well-formed operations, and dialect consistency.
        A bug means the lowering functor presheaf is ill-formed —
        the chain of dialect functors does not compose correctly.
        """
        if site_id is None:
            site_id = SiteId(kind=SiteKind.TENSOR_SHAPE, name=f"mlir_analysis:{spec.name}")
        program = ProgramId(name=spec.name or "module", function_name=spec.name or "module")
        bugs: List[Bug] = []

        # Parse the module
        module = self._parser.parse(spec.source_text or "", spec.name)

        # --- Lowering chain validity ---------------------------------
        for i, step in enumerate(spec.lowering_chain):
            src_level = self._DIALECT_LEVEL.get(step.source_dialect, -1)
            tgt_level = self._DIALECT_LEVEL.get(step.target_dialect, -1)
            if src_level >= 0 and tgt_level >= 0 and tgt_level <= src_level:
                bugs.append(Bug(
                    kind=BugKind.INVALID_LOWERING,
                    stratum=TensorStratum.STRUCTURAL,
                    site_id=site_id,
                    description=(
                        f"Lowering step {i}: {step.source_dialect.name} "
                        f"(level {src_level}) → {step.target_dialect.name} "
                        f"(level {tgt_level}) is not a descent in the "
                        f"dialect hierarchy"
                    ),
                    repair_hint="Lowering must go from higher to lower dialect",
                ))
            if not step.preserves_semantics:
                bugs.append(Bug(
                    kind=BugKind.INVALID_LOWERING,
                    stratum=TensorStratum.STRUCTURAL,
                    site_id=site_id,
                    description=(
                        f"Lowering step {i} ({step.source_dialect.name} → "
                        f"{step.target_dialect.name}) is marked as "
                        f"non-semantics-preserving"
                    ),
                    severity=0.7,
                ))

        # --- Operation well-formedness --------------------------------
        for func in module.functions:
            seen_results: set = set()
            for op in func.operations:
                # Check for duplicate result names (SSA violation)
                for rname in op.result_names:
                    if rname in seen_results:
                        bugs.append(Bug(
                            kind=BugKind.INVALID_LOWERING,
                            stratum=TensorStratum.STRUCTURAL,
                            site_id=site_id,
                            description=(
                                f"SSA violation in {func.name}: result '{rname}' "
                                f"defined multiple times (line {op.line_number})"
                            ),
                        ))
                    seen_results.add(rname)

                # Check operand references exist (basic use-def check)
                for operand in op.operands:
                    if operand.startswith("%") and operand not in seen_results:
                        bugs.append(Bug(
                            kind=BugKind.INVALID_LOWERING,
                            stratum=TensorStratum.STRUCTURAL,
                            site_id=site_id,
                            description=(
                                f"Use-before-def in {func.name}: operand "
                                f"'{operand}' used at line {op.line_number} "
                                f"but not previously defined"
                            ),
                        ))

        # --- Dialect consistency: no upward references ----------------
        present_dialects = set(
            op.dialect
            for f in module.functions
            for op in f.operations
        )
        if spec.lowering_chain:
            final_target = spec.lowering_chain[-1].target_dialect
            final_level = self._DIALECT_LEVEL.get(final_target, -1)
            for d_name in present_dialects:
                mapped = _map_dialect(d_name)
                d_level = self._DIALECT_LEVEL.get(mapped, -1)
                if d_level >= 0 and final_level >= 0 and d_level < final_level:
                    bugs.append(Bug(
                        kind=BugKind.INVALID_LOWERING,
                        stratum=TensorStratum.STRUCTURAL,
                        site_id=site_id,
                        description=(
                            f"Module still contains high-level dialect "
                            f"'{d_name}' (level {d_level}) after lowering "
                            f"to {final_target.name} (level {final_level})"
                        ),
                        repair_hint="All ops should be lowered to the target dialect",
                    ))

        verdict = AnalysisVerdict.INVALID if bugs else AnalysisVerdict.VALID
        return AnalysisJudgment(
            verdict=verdict,
            program=program,
            mode=AnalysisMode.BUG_FINDING,
            bugs=bugs,
            stratum_results={TensorStratum.STRUCTURAL: verdict},
            explanation=(
                f"Found {len(bugs)} validity issues in MLIR module '{spec.name}'"
                if bugs else
                f"MLIR module '{spec.name}' lowering functor presheaf is well-formed"
            ),
        )
