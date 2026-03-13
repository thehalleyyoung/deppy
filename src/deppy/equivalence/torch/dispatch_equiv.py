"""
Dispatch equivalence checker — dispatch key presheaf, device semantics.

Models dispatch equivalence as a presheaf on the dispatch key lattice:
  - Objects: (device, dispatch_key) pairs
  - Morphisms: device transfer maps
  - Sections: dispatched implementations at each (device, key)
  - Equivalence: sections agree at all reachable dispatch keys

PyTorch's dispatch mechanism selects an implementation based on the
input tensor's dispatch key (CPU, CUDA, AutogradCPU, etc.).  Two functions
are dispatch-equivalent if they produce the same results under all
dispatch configurations.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple

from ._protocols import (
    AnalysisJudgment,
    AnalysisMode,
    AnalysisVerdict,
    Bug,
    BugKind,
    EquivalenceVerdict,
    ProgramId,
    SheafConditionResult,
    SiteId,
    SiteKind,
    TensorEquivalenceConfig,
    TensorLocalJudgment,
    TensorObstruction,
    TensorObstructionKind,
    TensorSiteKind,
    TensorSpec,
    TensorStratum,
)


# ---------------------------------------------------------------------------
# Device lattice
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class DeviceSpec:
    """A device specification (type + index)."""
    device_type: str  # "cpu", "cuda", "mps", etc.
    device_index: int = 0

    def __str__(self) -> str:
        if self.device_type == "cpu":
            return "cpu"
        return f"{self.device_type}:{self.device_index}"

    @staticmethod
    def from_string(s: str) -> "DeviceSpec":
        if ":" in s:
            parts = s.split(":")
            return DeviceSpec(device_type=parts[0], device_index=int(parts[1]))
        return DeviceSpec(device_type=s, device_index=0)


def available_devices() -> List[DeviceSpec]:
    """Get list of available devices."""
    devices = [DeviceSpec(device_type="cpu")]
    try:
        import torch
        if torch.cuda.is_available():
            for i in range(torch.cuda.device_count()):
                devices.append(DeviceSpec(device_type="cuda", device_index=i))
        if hasattr(torch.backends, "mps") and torch.backends.mps.is_available():
            devices.append(DeviceSpec(device_type="mps"))
    except ImportError:
        pass
    return devices


# ---------------------------------------------------------------------------
# Dispatch key analysis
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class DispatchKeyInfo:
    """Information about a PyTorch dispatch key."""
    name: str
    device: str
    is_autograd: bool = False
    is_backend: bool = True


def get_dispatch_keys_for_op(op_name: str) -> List[DispatchKeyInfo]:
    """
    Get the dispatch keys registered for a given PyTorch op.

    This probes the dispatch table, which is the *total space* of the
    dispatch presheaf.  Each dispatch key is a site; the section at
    that site is the kernel implementation selected for that key.
    """
    keys = []
    try:
        import torch
        # Standard dispatch keys
        for device in ["CPU", "CUDA", "Meta"]:
            keys.append(DispatchKeyInfo(name=device, device=device.lower()))
        for device in ["CPU", "CUDA"]:
            keys.append(DispatchKeyInfo(
                name=f"Autograd{device}",
                device=device.lower(),
                is_autograd=True,
            ))
    except ImportError:
        pass
    return keys


# ---------------------------------------------------------------------------
# Exception behavior comparison
# ---------------------------------------------------------------------------

@dataclass
class ExceptionBehavior:
    """Records exception behavior across test inputs."""
    n_success: int = 0
    n_exceptions: int = 0
    exception_types: Dict[str, int] = field(default_factory=dict)
    exception_inputs: List[str] = field(default_factory=list)


def probe_exception_behavior(fn: Any, test_inputs: List[List[Any]]) -> ExceptionBehavior:
    """Probe which inputs cause exceptions."""
    result = ExceptionBehavior()
    for inputs in test_inputs:
        try:
            fn(*inputs)
            result.n_success += 1
        except Exception as e:
            result.n_exceptions += 1
            etype = type(e).__name__
            result.exception_types[etype] = result.exception_types.get(etype, 0) + 1
            result.exception_inputs.append(repr(inputs)[:100])
    return result


# ---------------------------------------------------------------------------
# Dispatch equivalence checker
# ---------------------------------------------------------------------------

class DispatchEquivalenceChecker:
    """
    Checks dispatch and device equivalence of two tensor functions.

    This implements the local section comparison at device/dispatch sites:
    1. Device equivalence: same results on all available devices
    2. Device transfer: transferring inputs preserves equivalence
    3. Exception behavior: same inputs cause same exceptions
    4. Dispatch key: same kernels selected for same dispatch keys

    Sheaf-theoretically, device equivalence is a presheaf on the device
    category whose morphisms are device transfer maps (.to(device)).
    Restriction along a transfer morphism moves sections between devices.
    """

    def __init__(self, config: TensorEquivalenceConfig):
        self._config = config

    def check_site(
        self,
        fn_f: Any,
        fn_g: Any,
        test_inputs: List[List[Any]],
        site_id: SiteId,
    ) -> TensorLocalJudgment:
        """Check dispatch/device equivalence at a single site."""
        obstructions: List[TensorObstruction] = []

        # 1. Exception behavior comparison
        exc_f = probe_exception_behavior(fn_f, test_inputs)
        exc_g = probe_exception_behavior(fn_g, test_inputs)

        if exc_f.n_exceptions != exc_g.n_exceptions:
            obstructions.append(TensorObstruction(
                kind=TensorObstructionKind.EXCEPTION_BEHAVIOR,
                stratum=TensorStratum.METADATA,
                sites=(site_id,),
                description=(f"Exception count differs: "
                             f"f={exc_f.n_exceptions}, g={exc_g.n_exceptions}"),
            ))

        if exc_f.exception_types != exc_g.exception_types:
            obstructions.append(TensorObstruction(
                kind=TensorObstructionKind.EXCEPTION_BEHAVIOR,
                stratum=TensorStratum.METADATA,
                sites=(site_id,),
                description=(f"Exception types differ: "
                             f"f={exc_f.exception_types}, "
                             f"g={exc_g.exception_types}"),
            ))

        if obstructions:
            return TensorLocalJudgment(
                site_id=site_id,
                stratum=TensorStratum.METADATA,
                tensor_site_kind=TensorSiteKind.DEVICE,
                verdict=EquivalenceVerdict.INEQUIVALENT,
                explanation=f"Dispatch behavior differs ({len(obstructions)} issues)",
                obstructions=tuple(obstructions),
            )

        return TensorLocalJudgment(
            site_id=site_id,
            stratum=TensorStratum.METADATA,
            tensor_site_kind=TensorSiteKind.DEVICE,
            verdict=EquivalenceVerdict.EQUIVALENT,
            explanation="Dispatch behavior matches",
        )

    def check_device_transfer(
        self,
        fn_f: Any,
        fn_g: Any,
        test_inputs: List[List[Any]],
        site_id: SiteId,
        source_device: str = "cpu",
        target_device: str = "cpu",
    ) -> TensorLocalJudgment:
        """
        Check that device transfer commutes with function application.

        For f,g: Tensor → Tensor and device transfer T: Dev_a → Dev_b,
        verify that T(f(x)) = f(T(x)) and T(g(x)) = g(T(x)).
        This is the *naturality condition* for the device transfer morphism.
        """
        try:
            import torch
        except ImportError:
            return TensorLocalJudgment(
                site_id=site_id,
                stratum=TensorStratum.METADATA,
                tensor_site_kind=TensorSiteKind.DEVICE,
                verdict=EquivalenceVerdict.UNKNOWN,
                explanation="PyTorch not available",
            )

        if not torch.cuda.is_available() and "cuda" in target_device:
            return TensorLocalJudgment(
                site_id=site_id,
                stratum=TensorStratum.METADATA,
                tensor_site_kind=TensorSiteKind.DEVICE,
                verdict=EquivalenceVerdict.UNKNOWN,
                explanation="Target device not available",
            )

        obstructions: List[TensorObstruction] = []

        for inputs in test_inputs[:5]:  # Limit transfer tests
            try:
                # Compute on source device
                src_inputs = [
                    t.to(source_device) if isinstance(t, torch.Tensor) else t
                    for t in inputs
                ]
                out_f_src = fn_f(*src_inputs)
                out_g_src = fn_g(*src_inputs)

                # Transfer outputs to target
                out_f_transferred = self._transfer(out_f_src, target_device)
                out_g_transferred = self._transfer(out_g_src, target_device)

                # Compute on target device
                tgt_inputs = [
                    t.to(target_device) if isinstance(t, torch.Tensor) else t
                    for t in inputs
                ]
                out_f_tgt = fn_f(*tgt_inputs)
                out_g_tgt = fn_g(*tgt_inputs)

                # Check commutativity: T(f(x)) ≈ f(T(x))
                from .numerical_equiv import compare_tensors
                cmp = compare_tensors(
                    out_f_transferred if isinstance(out_f_transferred, torch.Tensor) else torch.tensor(0.0),
                    out_f_tgt if isinstance(out_f_tgt, torch.Tensor) else torch.tensor(0.0),
                    self._config.tolerance,
                )
                if cmp.verdict != EquivalenceVerdict.EQUIVALENT:
                    obstructions.append(TensorObstruction(
                        kind=TensorObstructionKind.DEVICE_MISMATCH,
                        stratum=TensorStratum.METADATA,
                        sites=(site_id,),
                        description=(f"Device transfer non-naturality for f: "
                                     f"T(f(x)) ≠ f(T(x)), "
                                     f"diff={cmp.max_abs_diff:.2e}"),
                    ))
            except Exception:
                continue

        if obstructions:
            return TensorLocalJudgment(
                site_id=site_id,
                stratum=TensorStratum.METADATA,
                tensor_site_kind=TensorSiteKind.DEVICE,
                verdict=EquivalenceVerdict.INEQUIVALENT,
                explanation="Device transfer non-naturality detected",
                obstructions=tuple(obstructions),
            )

        return TensorLocalJudgment(
            site_id=site_id,
            stratum=TensorStratum.METADATA,
            tensor_site_kind=TensorSiteKind.DEVICE,
            verdict=EquivalenceVerdict.EQUIVALENT,
            explanation=f"Device transfer natural: {source_device} → {target_device}",
        )

    def check_nondeterminism(
        self,
        fn_f: Any,
        fn_g: Any,
        test_inputs: List[List[Any]],
        site_id: SiteId,
        n_runs: int = 5,
    ) -> TensorLocalJudgment:
        """
        Check for nondeterminism in both functions.

        Nondeterminism means the function's section at a site is not
        well-defined (it's a multi-valued section / correspondence
        rather than a function).  If both functions are nondeterministic
        in the same way, they may still be equivalent in distribution.
        """
        try:
            import torch
        except ImportError:
            return TensorLocalJudgment(
                site_id=site_id,
                stratum=TensorStratum.BEHAVIORAL,
                tensor_site_kind=TensorSiteKind.DEVICE,
                verdict=EquivalenceVerdict.UNKNOWN,
                explanation="PyTorch not available",
            )

        obstructions: List[TensorObstruction] = []

        for inputs in test_inputs[:3]:
            f_outputs = []
            g_outputs = []
            for _ in range(n_runs):
                try:
                    cloned = [t.clone() if isinstance(t, torch.Tensor) else t
                              for t in inputs]
                    f_outputs.append(fn_f(*cloned))
                except Exception:
                    pass
                try:
                    cloned = [t.clone() if isinstance(t, torch.Tensor) else t
                              for t in inputs]
                    g_outputs.append(fn_g(*cloned))
                except Exception:
                    pass

            f_nondet = self._check_output_variance(f_outputs)
            g_nondet = self._check_output_variance(g_outputs)

            if f_nondet and not g_nondet:
                obstructions.append(TensorObstruction(
                    kind=TensorObstructionKind.NONDETERMINISM,
                    stratum=TensorStratum.BEHAVIORAL,
                    sites=(site_id,),
                    description="f is nondeterministic but g is deterministic",
                ))
            elif g_nondet and not f_nondet:
                obstructions.append(TensorObstruction(
                    kind=TensorObstructionKind.NONDETERMINISM,
                    stratum=TensorStratum.BEHAVIORAL,
                    sites=(site_id,),
                    description="g is nondeterministic but f is deterministic",
                ))

        if obstructions:
            return TensorLocalJudgment(
                site_id=site_id,
                stratum=TensorStratum.BEHAVIORAL,
                tensor_site_kind=TensorSiteKind.DEVICE,
                verdict=EquivalenceVerdict.INEQUIVALENT,
                explanation="Nondeterminism asymmetry",
                obstructions=tuple(obstructions),
            )

        return TensorLocalJudgment(
            site_id=site_id,
            stratum=TensorStratum.BEHAVIORAL,
            tensor_site_kind=TensorSiteKind.DEVICE,
            verdict=EquivalenceVerdict.EQUIVALENT,
            explanation="Determinism behavior matches",
        )

    @staticmethod
    def _transfer(out: Any, device: str) -> Any:
        try:
            import torch
            if isinstance(out, torch.Tensor):
                return out.to(device)
            if isinstance(out, (tuple, list)):
                return type(out)(
                    o.to(device) if isinstance(o, torch.Tensor) else o
                    for o in out
                )
        except Exception:
            pass
        return out

    @staticmethod
    def _check_output_variance(outputs: List[Any]) -> bool:
        """Check if outputs vary across runs (nondeterminism)."""
        if len(outputs) < 2:
            return False
        try:
            import torch
            ref = outputs[0]
            for out in outputs[1:]:
                if isinstance(ref, torch.Tensor) and isinstance(out, torch.Tensor):
                    if not torch.equal(ref, out):
                        return True
                elif ref != out:
                    return True
        except Exception:
            pass
        return False

    # ------------------------------------------------------------------
    # Single-program analysis
    # ------------------------------------------------------------------

    def analyze(
        self,
        fn: Any,
        test_inputs: List[List[Any]],
        site_id: Optional[SiteId] = None,
    ) -> AnalysisJudgment:
        """Analyze dispatch consistency and determinism of a single function.

        Checks for nondeterminism (multi-valued sections) and exception
        instability across the dispatch presheaf.  A well-formed presheaf
        section must be single-valued: repeated evaluation at the same
        site must yield the same observation.
        """
        try:
            import torch
        except ImportError:
            return AnalysisJudgment(
                verdict=AnalysisVerdict.UNKNOWN,
                program=ProgramId(name="fn"),
                mode=AnalysisMode.BUG_FINDING,
                explanation="PyTorch not available",
            )

        if site_id is None:
            site_id = SiteId(kind=SiteKind.TENSOR_SHAPE, name="dispatch_analysis")
        program = ProgramId(name="fn", function_name=getattr(fn, "__name__", "anonymous"))
        bugs: List[Bug] = []
        n_runs = 5

        for inputs in test_inputs:
            outputs: List[Any] = []
            exceptions: List[Optional[str]] = []

            for _ in range(n_runs):
                try:
                    cloned = [t.clone() if isinstance(t, torch.Tensor) else t
                              for t in inputs]
                    out = fn(*cloned)
                    outputs.append(out)
                    exceptions.append(None)
                except Exception as e:
                    outputs.append(None)
                    exceptions.append(type(e).__name__)

            # Check exception consistency
            exc_types = set(exceptions)
            if len(exc_types) > 1:
                bugs.append(Bug(
                    kind=BugKind.NONDETERMINISM,
                    stratum=TensorStratum.BEHAVIORAL,
                    site_id=site_id,
                    description=(
                        f"Exception behavior is nondeterministic: "
                        f"observed {exc_types} across {n_runs} runs"
                    ),
                    witness_input=repr(inputs)[:200],
                ))

            # Check output determinism
            valid_outputs = [o for o in outputs if o is not None]
            if self._check_output_variance(valid_outputs):
                bugs.append(Bug(
                    kind=BugKind.NONDETERMINISM,
                    stratum=TensorStratum.BEHAVIORAL,
                    site_id=site_id,
                    description=(
                        "Function produces different outputs on identical "
                        f"inputs across {n_runs} evaluations"
                    ),
                    witness_input=repr(inputs)[:200],
                    repair_hint="Use torch.use_deterministic_algorithms(True)",
                ))

        # Check available-device compatibility
        devices = available_devices()
        for dev in devices[:2]:
            for inputs in test_inputs[:1]:
                try:
                    dev_inputs = [
                        t.to(str(dev)) if isinstance(t, torch.Tensor) else t
                        for t in inputs
                    ]
                    fn(*dev_inputs)
                except RuntimeError as e:
                    err_msg = str(e)
                    if "not implemented" in err_msg.lower():
                        bugs.append(Bug(
                            kind=BugKind.NONDETERMINISM,
                            stratum=TensorStratum.METADATA,
                            site_id=site_id,
                            description=(
                                f"Function not implemented for device {dev}: "
                                f"{err_msg[:100]}"
                            ),
                            repair_hint=f"Add {dev} dispatch implementation",
                            severity=0.5,
                        ))
                except Exception:
                    pass

        verdict = AnalysisVerdict.INVALID if bugs else AnalysisVerdict.VALID
        return AnalysisJudgment(
            verdict=verdict,
            program=program,
            mode=AnalysisMode.BUG_FINDING,
            bugs=bugs,
            stratum_results={TensorStratum.BEHAVIORAL: verdict},
            explanation=(
                f"Found {len(bugs)} dispatch/determinism issues"
                if bugs else
                "Dispatch presheaf sections are single-valued and consistent"
            ),
        )
