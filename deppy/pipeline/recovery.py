"""
Smart Error Recovery System
==========================

Provides graceful degradation and partial verification when components fail.
Instead of complete failure, attempts to continue with reduced functionality.

Features:
- Component-level isolation (AST parsing, Z3, Lean, etc.)
- Fallback strategies for each component
- Partial verification results when possible
- Error categorization and reporting
- Recovery suggestions
"""
from __future__ import annotations

import traceback
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Callable, Dict, List, Optional, Tuple, TypeVar, Union

T = TypeVar('T')


class RecoveryLevel(Enum):
    """Levels of error recovery."""
    NONE = auto()           # Complete failure
    MINIMAL = auto()        # Basic functionality only
    DEGRADED = auto()       # Most features work with warnings
    FULL = auto()           # All features working


class ComponentType(Enum):
    """Types of verifier components that can fail."""
    AST_PARSING = auto()
    SOURCE_ANALYSIS = auto()
    Z3_SOLVER = auto()
    LEAN_COMPILER = auto()
    KERNEL_VERIFICATION = auto()
    EFFECT_PROPAGATION = auto()
    COVERAGE_ANALYSIS = auto()
    CUBICAL_ATLAS = auto()


@dataclass
class RecoveryAction:
    """A single recovery action to take when a component fails."""
    component: ComponentType
    fallback_func: Callable[..., Any]
    description: str
    recovery_level: RecoveryLevel = RecoveryLevel.DEGRADED


@dataclass
class ErrorContext:
    """Context information about an error."""
    component: ComponentType
    exception: Exception
    input_data: Any = None
    traceback_str: str = ""
    recovery_attempted: bool = False
    recovery_successful: bool = False
    fallback_result: Any = None


class SmartRecoveryEngine:
    """Manages error recovery across verification components."""
    
    def __init__(self):
        self.recovery_actions: Dict[ComponentType, List[RecoveryAction]] = {}
        self.error_history: List[ErrorContext] = []
        self._setup_default_recovery_actions()
    
    def _setup_default_recovery_actions(self):
        """Setup default recovery strategies for each component."""
        
        # AST Parsing recovery
        def ast_recovery_fallback(source: str, *args, **kwargs):
            """Try to parse with relaxed error handling."""
            import ast
            try:
                # Try to parse with error handling mode
                return ast.parse(source, mode='exec')
            except SyntaxError as e:
                # Create minimal module with error info
                error_node = ast.Expr(value=ast.Constant(value=f"Syntax error: {e}"))
                return ast.Module(body=[error_node], type_ignores=[])
        
        self.add_recovery_action(ComponentType.AST_PARSING, ast_recovery_fallback,
                               "Fallback AST parsing with error tolerance", RecoveryLevel.MINIMAL)
        
        # Source Analysis recovery
        def source_analysis_fallback(*args, **kwargs):
            """Return empty analysis when source analysis fails."""
            from deppy.pipeline.exception_sources import ModuleSourceSummary
            return ModuleSourceSummary(module_path="<error>", functions=[], module_level_sources=[])
        
        self.add_recovery_action(ComponentType.SOURCE_ANALYSIS, source_analysis_fallback,
                               "Empty source analysis on failure", RecoveryLevel.MINIMAL)
        
        # Z3 Solver recovery
        def z3_recovery_fallback(*args, **kwargs):
            """Return 'unknown' result when Z3 fails."""
            return {'result': 'unknown', 'reason': 'Z3 solver unavailable'}
        
        self.add_recovery_action(ComponentType.Z3_SOLVER, z3_recovery_fallback,
                               "Z3 fallback to unknown results", RecoveryLevel.DEGRADED)
        
        # Lean Compiler recovery
        def lean_recovery_fallback(*args, **kwargs):
            """Skip Lean compilation when it fails."""
            return {'lean_checked': False, 'lean_source': None, 'error': 'Lean compiler unavailable'}
        
        self.add_recovery_action(ComponentType.LEAN_COMPILER, lean_recovery_fallback,
                               "Skip Lean compilation on failure", RecoveryLevel.DEGRADED)
        
        # Kernel verification recovery
        def kernel_recovery_fallback(*args, **kwargs):
            """Return untrusted result when kernel fails."""
            from deppy.core.kernel import VerificationResult, TrustLevel
            return VerificationResult(
                success=False,
                trust_level=TrustLevel.UNTRUSTED,
                message="Kernel verification failed - using fallback",
            )
        
        self.add_recovery_action(ComponentType.KERNEL_VERIFICATION, kernel_recovery_fallback,
                               "Fallback to untrusted results", RecoveryLevel.MINIMAL)
    
    def add_recovery_action(
        self,
        component: ComponentType,
        fallback_func: Callable[..., Any],
        description: str,
        recovery_level: RecoveryLevel = RecoveryLevel.DEGRADED
    ):
        """Add a recovery action for a component."""
        if component not in self.recovery_actions:
            self.recovery_actions[component] = []
        
        action = RecoveryAction(
            component=component,
            fallback_func=fallback_func,
            description=description,
            recovery_level=recovery_level
        )
        self.recovery_actions[component].append(action)
    
    def execute_with_recovery(
        self,
        component: ComponentType,
        func: Callable[..., T],
        *args,
        **kwargs
    ) -> Tuple[T, Optional[ErrorContext]]:
        """Execute a function with automatic recovery on failure."""
        try:
            result = func(*args, **kwargs)
            return result, None
        
        except Exception as e:
            # Create error context
            error_ctx = ErrorContext(
                component=component,
                exception=e,
                input_data=(args, kwargs),
                traceback_str=traceback.format_exc()
            )
            self.error_history.append(error_ctx)
            
            # Try recovery actions
            if component in self.recovery_actions:
                for action in self.recovery_actions[component]:
                    try:
                        error_ctx.recovery_attempted = True
                        fallback_result = action.fallback_func(*args, **kwargs)
                        error_ctx.recovery_successful = True
                        error_ctx.fallback_result = fallback_result
                        return fallback_result, error_ctx
                    
                    except Exception as recovery_error:
                        # Recovery failed, try next action
                        continue
            
            # No recovery possible - re-raise original exception
            error_ctx.recovery_successful = False
            raise e
    
    def get_recovery_summary(self) -> str:
        """Get summary of recovery actions taken."""
        if not self.error_history:
            return "No errors encountered."
        
        lines = [f"Error Recovery Summary ({len(self.error_history)} errors):"]
        
        by_component = {}
        for error in self.error_history:
            comp_name = error.component.name
            if comp_name not in by_component:
                by_component[comp_name] = {'total': 0, 'recovered': 0}
            by_component[comp_name]['total'] += 1
            if error.recovery_successful:
                by_component[comp_name]['recovered'] += 1
        
        for comp_name, stats in by_component.items():
            recovery_rate = stats['recovered'] / stats['total'] * 100
            lines.append(f"  {comp_name}: {stats['recovered']}/{stats['total']} recovered ({recovery_rate:.0f}%)")
        
        return "\n".join(lines)
    
    def get_error_diagnostics(self) -> List[str]:
        """Get diagnostic information for unrecovered errors."""
        diagnostics = []
        
        for error in self.error_history:
            if not error.recovery_successful:
                diagnostics.append(
                    f"{error.component.name} failed: {error.exception}"
                )
        
        return diagnostics
    
    def suggest_fixes(self) -> List[str]:
        """Suggest fixes for common error patterns."""
        suggestions = []
        
        # Analyze error patterns
        z3_errors = [e for e in self.error_history if e.component == ComponentType.Z3_SOLVER]
        lean_errors = [e for e in self.error_history if e.component == ComponentType.LEAN_COMPILER]
        ast_errors = [e for e in self.error_history if e.component == ComponentType.AST_PARSING]
        
        if z3_errors:
            suggestions.append("Z3 solver issues detected. Consider: pip install z3-solver")
        
        if lean_errors:
            suggestions.append("Lean compiler issues detected. Consider: installing Lean 4 toolchain")
        
        if ast_errors:
            suggestions.append("Python syntax errors detected. Check source code syntax")
        
        # Check for import errors
        import_errors = [e for e in self.error_history 
                        if isinstance(e.exception, ImportError)]
        if import_errors:
            missing_modules = set()
            for error in import_errors:
                if hasattr(error.exception, 'name') and error.exception.name:
                    missing_modules.add(error.exception.name)
            if missing_modules:
                suggestions.append(f"Missing Python modules: {', '.join(missing_modules)}. Consider: pip install {' '.join(missing_modules)}")
        
        return suggestions


# Global recovery engine instance
_global_recovery_engine: Optional[SmartRecoveryEngine] = None


def get_recovery_engine() -> SmartRecoveryEngine:
    """Get or create the global recovery engine."""
    global _global_recovery_engine
    if _global_recovery_engine is None:
        _global_recovery_engine = SmartRecoveryEngine()
    return _global_recovery_engine


def with_recovery(component: ComponentType):
    """Decorator to add recovery to a function."""
    def decorator(func: Callable[..., T]) -> Callable[..., T]:
        def wrapper(*args, **kwargs):
            engine = get_recovery_engine()
            result, error_ctx = engine.execute_with_recovery(component, func, *args, **kwargs)
            # Optionally log error context
            return result
        return wrapper
    return decorator


# Convenience functions for common recovery patterns
def safe_ast_parse(source: str, filename: str = "<string>"):
    """Parse AST with automatic recovery on syntax errors."""
    import ast
    engine = get_recovery_engine()
    result, error_ctx = engine.execute_with_recovery(
        ComponentType.AST_PARSING,
        ast.parse,
        source, filename
    )
    return result


def safe_z3_check(formula: str, context: str = ""):
    """Check Z3 formula with automatic recovery on solver errors."""
    def z3_check():
        # Placeholder - would integrate with actual Z3 checking
        return {'result': 'sat', 'model': {}}
    
    engine = get_recovery_engine()
    result, error_ctx = engine.execute_with_recovery(
        ComponentType.Z3_SOLVER,
        z3_check
    )
    return result