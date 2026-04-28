"""
Simple Parallel Function Verification
=====================================

Light-weight parallel execution for independent function verification
in the safety pipeline. Focuses on practical speedups without complex
dependency analysis.
"""
from __future__ import annotations

import concurrent.futures
import threading
from typing import Any, Callable, Dict, List, Optional


class SimpleParallelVerifier:
    """Simple parallel function verifier for the safety pipeline."""
    
    def __init__(self, max_workers: Optional[int] = None):
        self.max_workers = max_workers or 4  # Conservative default
        self._progress_lock = threading.Lock()
        self._completed = 0
        
    def verify_functions_parallel(
        self,
        function_names: List[str],
        verify_func: Callable[[str], Any],
        progress_callback: Optional[Callable[[str], None]] = None
    ) -> Dict[str, Any]:
        """Verify functions in parallel when beneficial."""
        
        # Use sequential for small numbers of functions
        if len(function_names) < 3:
            return self._verify_sequential(function_names, verify_func, progress_callback)
        
        # Use parallel for larger sets
        return self._verify_parallel(function_names, verify_func, progress_callback)
    
    def _verify_sequential(
        self,
        function_names: List[str],
        verify_func: Callable[[str], Any],
        progress_callback: Optional[Callable[[str], None]] = None
    ) -> Dict[str, Any]:
        """Sequential verification fallback.

        Returns the same shape as ``_verify_parallel``: a dict
        mapping function name → unwrapped data.  Earlier this method
        stored ``verify_func``'s raw return value (which is a
        ``(name, data)`` tuple in the production caller), causing
        downstream code in ``safety_pipeline.py`` to crash with
        ``TypeError: tuple indices must be integers or slices, not str``.
        """
        results = {}
        for i, fname in enumerate(function_names):
            try:
                result = verify_func(fname)
                # Match _verify_parallel's tuple-unwrapping convention.
                if isinstance(result, tuple) and len(result) == 2:
                    _, actual_result = result
                else:
                    actual_result = result
                results[fname] = actual_result
                if progress_callback:
                    progress_callback(f"Verified {fname} ({i+1}/{len(function_names)})")
            except Exception as e:
                results[fname] = None
                if progress_callback:
                    progress_callback(f"Failed {fname}: {e}")
        return results
    
    def _verify_parallel(
        self,
        function_names: List[str],
        verify_func: Callable[[str], Any],
        progress_callback: Optional[Callable[[str], None]] = None
    ) -> Dict[str, Any]:
        """Parallel verification using thread pool."""
        results = {}
        self._completed = 0
        
        def verify_with_progress(fname: str) -> tuple[str, Any]:
            try:
                result = verify_func(fname)
                # If verify_func returns a tuple (fname, data), extract the data
                if isinstance(result, tuple) and len(result) == 2:
                    _, actual_result = result
                else:
                    actual_result = result
                    
                with self._progress_lock:
                    self._completed += 1
                    if progress_callback:
                        progress_callback(f"Verified {fname} ({self._completed}/{len(function_names)})")
                return fname, actual_result
            except Exception as e:
                with self._progress_lock:
                    self._completed += 1
                    if progress_callback:
                        progress_callback(f"Failed {fname}: {e}")
                return fname, None
        
        with concurrent.futures.ThreadPoolExecutor(max_workers=self.max_workers) as executor:
            # Submit all functions
            future_to_fname = {
                executor.submit(verify_with_progress, fname): fname 
                for fname in function_names
            }
            
            # Collect results as they complete
            for future in concurrent.futures.as_completed(future_to_fname):
                fname, result = future.result()
                results[fname] = result
        
        return results