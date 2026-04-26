"""
Progressive Feedback System
==========================

Provides streaming progress updates during verification instead of waiting
for full completion. Useful for large modules and interactive environments.

Features:
- Real-time progress reporting
- Incremental results streaming  
- Estimated time remaining
- Cancellation support
- Multiple output formats (text, JSON, structured)
"""
from __future__ import annotations

import json
import threading
import time
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Callable, Dict, List, Optional


class ProgressEventType(Enum):
    """Types of progress events."""
    STARTED = auto()
    PHASE_BEGIN = auto()
    PHASE_COMPLETE = auto()
    FUNCTION_BEGIN = auto()
    FUNCTION_COMPLETE = auto()
    ERROR = auto()
    WARNING = auto()
    COMPLETED = auto()


@dataclass
class ProgressEvent:
    """Single progress event."""
    type: ProgressEventType
    timestamp: float = field(default_factory=time.time)
    message: str = ""
    details: Dict[str, Any] = field(default_factory=dict)
    progress_pct: Optional[float] = None  # 0.0 to 100.0


class ProgressReporter(ABC):
    """Abstract base for progress reporting."""
    
    @abstractmethod
    def report(self, event: ProgressEvent) -> None:
        """Handle a progress event."""
        pass
    
    @abstractmethod
    def finalize(self) -> None:
        """Called when verification is complete."""
        pass


class TextProgressReporter(ProgressReporter):
    """Simple text-based progress reporter."""
    
    def __init__(self, show_functions: bool = True, show_details: bool = False):
        self.show_functions = show_functions
        self.show_details = show_details
        self._start_time: Optional[float] = None
    
    def report(self, event: ProgressEvent) -> None:
        if event.type == ProgressEventType.STARTED:
            self._start_time = event.timestamp
            print(f"🚀 Starting verification: {event.message}")
            
        elif event.type == ProgressEventType.PHASE_BEGIN:
            elapsed = event.timestamp - (self._start_time or event.timestamp)
            print(f"⚡ {event.message} (t+{elapsed:.1f}s)")
            
        elif event.type == ProgressEventType.PHASE_COMPLETE:
            elapsed = event.timestamp - (self._start_time or event.timestamp)
            if event.progress_pct is not None:
                print(f"✅ {event.message} [{event.progress_pct:.0f}%] (t+{elapsed:.1f}s)")
            else:
                print(f"✅ {event.message} (t+{elapsed:.1f}s)")
                
        elif event.type == ProgressEventType.FUNCTION_BEGIN and self.show_functions:
            print(f"   🔍 Verifying {event.message}...")
            
        elif event.type == ProgressEventType.FUNCTION_COMPLETE and self.show_functions:
            status = "✅" if event.details.get('success', False) else "❌"
            trust = event.details.get('trust', 'UNKNOWN')
            print(f"   {status} {event.message} (trust: {trust})")
            
        elif event.type == ProgressEventType.ERROR:
            print(f"❌ ERROR: {event.message}")
            if self.show_details and event.details:
                print(f"    Details: {event.details}")
                
        elif event.type == ProgressEventType.WARNING:
            print(f"⚠️  WARNING: {event.message}")
            
        elif event.type == ProgressEventType.COMPLETED:
            elapsed = event.timestamp - (self._start_time or event.timestamp)
            total_funcs = event.details.get('total_functions', 0)
            safe_funcs = event.details.get('safe_functions', 0)
            print(f"🏁 Verification complete in {elapsed:.1f}s: {safe_funcs}/{total_funcs} functions safe")
    
    def finalize(self) -> None:
        pass


class JSONProgressReporter(ProgressReporter):
    """JSON-based progress reporter for machine consumption."""
    
    def __init__(self, output_callback: Callable[[str], None]):
        self.output_callback = output_callback
    
    def report(self, event: ProgressEvent) -> None:
        event_data = {
            'type': event.type.name,
            'timestamp': event.timestamp,
            'message': event.message,
            'details': event.details,
            'progress_pct': event.progress_pct,
        }
        self.output_callback(json.dumps(event_data))
    
    def finalize(self) -> None:
        pass


class ProgressTracker:
    """Coordinates progress reporting across verification phases."""

    def __init__(self, reporters: List[ProgressReporter]):
        self.reporters = reporters
        self._lock = threading.Lock()
        self._start_time: Optional[float] = None
        self._total_functions = 0
        # Count successes and failures separately so a run where every
        # function failed does NOT show up as "100% complete" in the
        # JSON stream.  ``_completed_functions`` remains the sum (for
        # back-compat with existing consumers).
        self._completed_functions = 0
        self._succeeded_functions = 0
        self._failed_functions = 0
        self._current_phase = ""

    def start_verification(self, module_path: str, total_functions: int) -> None:
        """Signal start of verification."""
        self._start_time = time.time()
        self._total_functions = total_functions
        self._completed_functions = 0
        self._succeeded_functions = 0
        self._failed_functions = 0
        
        event = ProgressEvent(
            type=ProgressEventType.STARTED,
            message=f"Module {module_path} ({total_functions} functions)",
            details={'module_path': module_path, 'total_functions': total_functions}
        )
        self._broadcast(event)
    
    def begin_phase(self, phase_name: str) -> None:
        """Signal start of a verification phase."""
        with self._lock:
            self._current_phase = phase_name
        
        event = ProgressEvent(
            type=ProgressEventType.PHASE_BEGIN,
            message=phase_name,
            progress_pct=self._calculate_progress()
        )
        self._broadcast(event)
    
    def complete_phase(self, phase_name: str, success: bool = True) -> None:
        """Signal completion of a verification phase."""
        event = ProgressEvent(
            type=ProgressEventType.PHASE_COMPLETE,
            message=phase_name,
            details={'success': success},
            progress_pct=self._calculate_progress()
        )
        self._broadcast(event)
    
    def begin_function(self, function_name: str) -> None:
        """Signal start of function verification."""
        event = ProgressEvent(
            type=ProgressEventType.FUNCTION_BEGIN,
            message=function_name,
            progress_pct=self._calculate_progress()
        )
        self._broadcast(event)
    
    def complete_function(self, function_name: str, success: bool, trust_level: str = "UNKNOWN") -> None:
        """Signal completion of function verification.

        Splits success vs failure into separate counters so consumers
        can tell "100% processed, 80% passed" from "100% processed,
        100% passed" — the OLD implementation counted every outcome
        the same, making a fully-failed run report as "complete".
        """
        with self._lock:
            self._completed_functions += 1
            if success:
                self._succeeded_functions += 1
            else:
                self._failed_functions += 1

        event = ProgressEvent(
            type=ProgressEventType.FUNCTION_COMPLETE,
            message=function_name,
            details={
                'success': success, 'trust': trust_level,
                'succeeded_so_far': self._succeeded_functions,
                'failed_so_far': self._failed_functions,
            },
            progress_pct=self._calculate_progress(),
        )
        self._broadcast(event)
    
    def report_error(self, message: str, details: Optional[Dict[str, Any]] = None) -> None:
        """Report an error."""
        event = ProgressEvent(
            type=ProgressEventType.ERROR,
            message=message,
            details=details or {}
        )
        self._broadcast(event)
    
    def report_warning(self, message: str, details: Optional[Dict[str, Any]] = None) -> None:
        """Report a warning."""
        event = ProgressEvent(
            type=ProgressEventType.WARNING,
            message=message,
            details=details or {}
        )
        self._broadcast(event)
    
    def complete_verification(self, safe_functions: int) -> None:
        """Signal completion of entire verification."""
        event = ProgressEvent(
            type=ProgressEventType.COMPLETED,
            message="Verification complete",
            details={
                'total_functions': self._total_functions,
                'safe_functions': safe_functions,
                'duration': time.time() - (self._start_time or time.time())
            },
            progress_pct=100.0
        )
        self._broadcast(event)
        
        # Finalize all reporters
        for reporter in self.reporters:
            try:
                reporter.finalize()
            except Exception:
                pass  # Ignore reporter errors
    
    def _calculate_progress(self) -> float:
        """Calculate current progress percentage."""
        if self._total_functions == 0:
            return 0.0
        return (self._completed_functions / self._total_functions) * 100.0
    
    def _broadcast(self, event: ProgressEvent) -> None:
        """Send event to all reporters."""
        for reporter in self.reporters:
            try:
                reporter.report(event)
            except Exception:
                pass  # Don't let reporter errors break verification


def create_progress_tracker(
    verbose: bool = False,
    json_output: Optional[Callable[[str], None]] = None
) -> Optional[ProgressTracker]:
    """Create appropriate progress tracker based on options."""
    reporters: List[ProgressReporter] = []
    
    if verbose:
        reporters.append(TextProgressReporter(show_functions=True, show_details=True))
    
    if json_output:
        reporters.append(JSONProgressReporter(json_output))
    
    return ProgressTracker(reporters) if reporters else None