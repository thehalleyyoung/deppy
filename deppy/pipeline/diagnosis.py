"""Enhanced diagnosis engine for runtime safety verification failures.

Provides detailed error analysis, root cause identification, and actionable fix suggestions.
"""

from __future__ import annotations
import ast
import re
from typing import Dict, List, Optional, Any, NamedTuple
from dataclasses import dataclass
from enum import Enum

from deppy.core.kernel import TrustLevel
from deppy.pipeline.exception_sources import ExceptionKind


class DiagnosisCategory(Enum):
    """Categories of verification failures."""
    INCOMPLETE_SPEC = "incomplete_spec"        # Missing preconditions/postconditions
    AXIOM_TRUST = "axiom_trust"               # Untrusted axiom usage
    Z3_TIMEOUT = "z3_timeout"                 # Z3 solver timeouts
    COVERAGE_GAP = "coverage_gap"             # Exception sources not covered
    TERMINATION = "termination"               # Termination obligations not met
    TYPE_MISMATCH = "type_mismatch"           # Type annotation problems
    CALLEE_UNKNOWN = "callee_unknown"         # Unknown callee dependencies
    LEAN_EXPORT = "lean_export"               # Lean compilation failures
    SYNTAX_ERROR = "syntax_error"             # Python syntax/parsing errors
    ENVIRONMENT = "environment"               # Missing dependencies/tools


@dataclass
class DiagnosticFinding:
    """A single diagnostic finding with analysis and suggestions."""
    category: DiagnosisCategory
    severity: str  # "error", "warning", "info"
    location: str  # Function/module location
    message: str
    root_cause: str
    suggestions: List[str]
    code_snippet: Optional[str] = None
    references: List[str] = None  # Documentation/example links


class EnhancedDiagnosisEngine:
    """Advanced diagnosis engine for runtime safety verification failures."""
    
    def __init__(self):
        self.findings: List[DiagnosticFinding] = []
        self.patterns = self._initialize_error_patterns()
    
    def _initialize_error_patterns(self) -> Dict[str, DiagnosisCategory]:
        """Initialize common error patterns and their categories."""
        return {
            # Z3 patterns
            r"z3.*timeout": DiagnosisCategory.Z3_TIMEOUT,
            r"z3.*unknown": DiagnosisCategory.Z3_TIMEOUT,
            r"SMT solver failed": DiagnosisCategory.Z3_TIMEOUT,
            
            # Coverage patterns
            r"ARITHMETIC_ERROR.*not.*covered": DiagnosisCategory.COVERAGE_GAP,
            r"ATTRIBUTE_ERROR.*not.*covered": DiagnosisCategory.COVERAGE_GAP,
            r"INDEX_ERROR.*not.*covered": DiagnosisCategory.COVERAGE_GAP,
            r"KeyError.*not.*covered": DiagnosisCategory.COVERAGE_GAP,
            
            # Spec patterns
            r"no.*precondition": DiagnosisCategory.INCOMPLETE_SPEC,
            r"missing.*guarantee": DiagnosisCategory.INCOMPLETE_SPEC,
            r"vacuous.*spec": DiagnosisCategory.INCOMPLETE_SPEC,
            
            # Axiom patterns
            r"untrusted.*axiom": DiagnosisCategory.AXIOM_TRUST,
            r"legacy.*axiom": DiagnosisCategory.AXIOM_TRUST,
            
            # Termination patterns
            r"termination.*not.*proved": DiagnosisCategory.TERMINATION,
            r"recursion.*unbounded": DiagnosisCategory.TERMINATION,
            
            # Lean patterns
            r"lean.*compilation.*failed": DiagnosisCategory.LEAN_EXPORT,
            r"lean.*type.*error": DiagnosisCategory.LEAN_EXPORT,
            
            # Environment patterns  
            r"lean.*not.*found": DiagnosisCategory.ENVIRONMENT,
            r"z3.*not.*available": DiagnosisCategory.ENVIRONMENT,
        }
    
    def analyze_verdict(self, verdict) -> List[DiagnosticFinding]:
        """Analyze a ModuleSafetyVerdict and generate diagnostic findings."""
        self.findings = []
        
        # Analyze overall module safety
        if not verdict.module_safe:
            self._analyze_module_failure(verdict)
        
        # Analyze per-function failures  
        for func_name, func_verdict in verdict.functions.items():
            if not func_verdict.is_safe:
                self._analyze_function_failure(func_name, func_verdict, verdict)
        
        # Analyze trust level degradation
        if verdict.aggregate_trust != TrustLevel.KERNEL:
            self._analyze_trust_degradation(verdict)
        
        # Analyze notes for common error patterns
        self._analyze_error_notes(verdict.notes)
        
        return self.findings
    
    def _analyze_module_failure(self, verdict):
        """Analyze why the overall module failed verification."""
        if not verdict.internal_calls_closed:
            self.findings.append(DiagnosticFinding(
                category=DiagnosisCategory.CALLEE_UNKNOWN,
                severity="error",
                location="module",
                message="Module has unverified internal function calls",
                root_cause="The cubical atlas construction failed to prove all internal function calls are safe",
                suggestions=[
                    "Add @guarantee annotations to all functions that are called internally",
                    "Check that all @requires preconditions are satisfied at call sites",
                    "Verify that recursive functions have proper @decreases specifications",
                    "Consider adding axioms for trusted library functions"
                ]
            ))
        
        unsafe_functions = [name for name, fv in verdict.functions.items() if not fv.is_safe]
        if unsafe_functions:
            self.findings.append(DiagnosticFinding(
                category=DiagnosisCategory.COVERAGE_GAP,
                severity="error", 
                location=f"functions: {', '.join(unsafe_functions[:3])}{'...' if len(unsafe_functions) > 3 else ''}",
                message=f"{len(unsafe_functions)} function(s) failed verification",
                root_cause="Individual functions have unproven safety obligations",
                suggestions=[
                    "Review the per-function diagnostics below",
                    "Add missing @guarantee/@requires specifications",
                    "Use @axiom for trusted computations that are hard to prove"
                ]
            ))
    
    def _analyze_function_failure(self, func_name: str, func_verdict, module_verdict):
        """Analyze why a specific function failed verification."""
        
        # Check for coverage gaps
        uncovered_kinds = []
        if hasattr(func_verdict, 'coverage_result'):
            for source in func_verdict.coverage_result.get('uncovered_sources', []):
                if hasattr(source, 'exception_kind'):
                    uncovered_kinds.append(source.exception_kind)
        
        if uncovered_kinds:
            kind_names = [k.name if hasattr(k, 'name') else str(k) for k in uncovered_kinds]
            self.findings.append(DiagnosticFinding(
                category=DiagnosisCategory.COVERAGE_GAP,
                severity="error",
                location=func_name,
                message=f"Uncovered exception sources: {', '.join(kind_names)}",
                root_cause="Function has potential exception sources without corresponding safety specifications",
                suggestions=self._suggest_coverage_fixes(uncovered_kinds, func_name)
            ))
        
        # Check for missing specs
        if not hasattr(func_verdict, 'guarantee') or not func_verdict.guarantee:
            self.findings.append(DiagnosticFinding(
                category=DiagnosisCategory.INCOMPLETE_SPEC,
                severity="warning",
                location=func_name,
                message="No @guarantee postcondition specified",
                root_cause="Function lacks formal safety specification",
                suggestions=[
                    f"Add @guarantee annotation to {func_name}",
                    "Specify what conditions guarantee the function won't raise exceptions",
                    "Example: @guarantee('x > 0') if function requires positive inputs"
                ]
            ))
    
    def _suggest_coverage_fixes(self, uncovered_kinds, func_name: str) -> List[str]:
        """Generate specific fix suggestions based on uncovered exception kinds."""
        suggestions = []
        
        for kind in uncovered_kinds:
            kind_name = kind.name if hasattr(kind, 'name') else str(kind)
            
            if kind_name == "ARITHMETIC_ERROR":
                suggestions.extend([
                    "Add @requires preconditions to prevent division by zero",
                    "Use @guarantee to specify when arithmetic operations are safe", 
                    "Consider using Decimal instead of float for exact arithmetic"
                ])
            elif kind_name == "INDEX_ERROR":
                suggestions.extend([
                    "Add @requires('0 <= i < len(lst)') for list access",
                    "Use @guarantee to specify bounds checking is performed",
                    "Consider using .get() instead of [] for dict access"
                ])
            elif kind_name == "ATTRIBUTE_ERROR":
                suggestions.extend([
                    "Add @requires('obj is not None') if accessing attributes", 
                    "Use hasattr() checks before attribute access",
                    "Add type annotations to clarify expected object types"
                ])
            elif kind_name == "KEY_ERROR":
                suggestions.extend([
                    "Use dict.get(key, default) instead of dict[key]",
                    "Add @requires to specify which keys must exist",
                    "Use 'key in dict' checks before access"
                ])
            elif kind_name == "TERMINATION_UNADDRESSED":
                suggestions.extend([
                    f"Add @decreases specification to {func_name}",
                    "Specify a well-founded measure that decreases on each recursive call",
                    "Use @axiom('terminates') if termination is obvious but hard to prove"
                ])
        
        return list(set(suggestions))  # Remove duplicates
    
    def _analyze_trust_degradation(self, verdict):
        """Analyze why trust level is below LEAN_VERIFIED."""
        trust_level = verdict.aggregate_trust
        
        if trust_level == TrustLevel.UNTRUSTED:
            self.findings.append(DiagnosticFinding(
                category=DiagnosisCategory.AXIOM_TRUST,
                severity="error",
                location="module",
                message="Module trust is UNTRUSTED",
                root_cause="Critical verification failures or use of untrusted axioms",
                suggestions=[
                    "Review all error messages for verification failures",
                    "Replace untrusted axioms with proper proofs",
                    "Check that all @axiom uses are justified"
                ]
            ))
        elif trust_level in [TrustLevel.EFFECT_ASSUMED, TrustLevel.AXIOM_TRUSTED]:
            self.findings.append(DiagnosticFinding(
                category=DiagnosisCategory.AXIOM_TRUST,
                severity="warning",
                location="module", 
                message=f"Module trust degraded to {trust_level.name}",
                root_cause="Verification relies on axioms rather than complete proofs",
                suggestions=[
                    "Review axiom usage - can any be replaced with proofs?",
                    "Use more specific preconditions to enable automatic proving",
                    "Consider adding Lean proofs for higher trust level"
                ]
            ))
        elif trust_level != TrustLevel.KERNEL and not verdict.lean_checked:
            self.findings.append(DiagnosticFinding(
                category=DiagnosisCategory.LEAN_EXPORT,
                severity="info",
                location="module",
                message="Lean export not attempted or failed",
                root_cause="Could not achieve highest trust level due to Lean compilation",
                suggestions=[
                    "Install Lean 4 to enable machine-checked proofs",
                    "Fix any Lean compilation errors reported",
                    "Simplify complex specifications that may be hard to export to Lean"
                ]
            ))
    
    def _analyze_error_notes(self, notes: List[str]):
        """Analyze error notes for common patterns."""
        for note in notes:
            for pattern, category in self.patterns.items():
                if re.search(pattern, note, re.IGNORECASE):
                    self._create_pattern_finding(category, note)
                    break
    
    def _create_pattern_finding(self, category: DiagnosisCategory, note: str):
        """Create a diagnostic finding based on error pattern matching."""
        
        if category == DiagnosisCategory.Z3_TIMEOUT:
            self.findings.append(DiagnosticFinding(
                category=category,
                severity="warning",
                location="Z3 solver",
                message="Z3 solver timeout or failure",
                root_cause="Complex logical constraints exceeded solver time limits",
                suggestions=[
                    "Simplify preconditions and postconditions",
                    "Break complex functions into smaller, easier-to-verify pieces",
                    "Use @axiom for computationally complex but obviously correct properties",
                    "Increase Z3 timeout if verification is making progress"
                ],
                code_snippet=note
            ))
        
        elif category == DiagnosisCategory.ENVIRONMENT:
            tool = "lean" if "lean" in note.lower() else "z3" if "z3" in note.lower() else "tool"
            self.findings.append(DiagnosticFinding(
                category=category,
                severity="error",
                location="environment", 
                message=f"Required tool '{tool}' not available",
                root_cause="Missing system dependencies for verification",
                suggestions=[
                    f"Install {tool}: pip install {tool}" if tool == "z3" else f"Install Lean 4 from https://leanprover.github.io/",
                    "Check that tools are in system PATH",
                    "Verify tool versions are compatible with deppy"
                ],
                code_snippet=note
            ))
    
    def generate_diagnosis_report(self, findings: List[DiagnosticFinding]) -> str:
        """Generate a human-readable diagnosis report."""
        if not findings:
            return "✅ No issues detected - verification completed successfully!"
        
        report = ["🔍 VERIFICATION DIAGNOSIS REPORT", "=" * 50, ""]
        
        # Group findings by severity
        errors = [f for f in findings if f.severity == "error"]
        warnings = [f for f in findings if f.severity == "warning"] 
        infos = [f for f in findings if f.severity == "info"]
        
        for severity, findings_group in [("ERRORS", errors), ("WARNINGS", warnings), ("INFO", infos)]:
            if not findings_group:
                continue
                
            report.extend([f"\n{severity} ({len(findings_group)}):", "-" * 20])
            
            for i, finding in enumerate(findings_group, 1):
                report.extend([
                    f"\n{i}. {finding.message}",
                    f"   Location: {finding.location}",
                    f"   Category: {finding.category.value}",
                    f"   Root cause: {finding.root_cause}",
                    ""
                ])
                
                if finding.suggestions:
                    report.append("   💡 Suggestions:")
                    for suggestion in finding.suggestions:
                        report.append(f"      • {suggestion}")
                    report.append("")
                
                if finding.code_snippet:
                    report.extend([
                        "   📄 Context:",
                        f"      {finding.code_snippet}",
                        ""
                    ])
        
        # Summary
        total = len(findings)
        error_count = len(errors)
        report.extend([
            "\n" + "=" * 50,
            f"SUMMARY: {total} issue(s) found ({error_count} critical)",
            ""
        ])
        
        if error_count == 0:
            report.append("🟡 Verification completed with warnings - consider addressing for higher confidence")
        else:
            report.append("🔴 Verification failed - address critical errors above")
            
        return "\n".join(report)
    
    def suggest_next_steps(self, findings: List[DiagnosticFinding]) -> List[str]:
        """Suggest prioritized next steps based on findings."""
        if not findings:
            return ["✅ All verification checks passed!"]
        
        # Prioritize by severity and category
        critical_categories = [DiagnosisCategory.SYNTAX_ERROR, DiagnosisCategory.ENVIRONMENT]
        high_priority = [DiagnosisCategory.COVERAGE_GAP, DiagnosisCategory.INCOMPLETE_SPEC]
        
        steps = []
        
        # Critical issues first
        critical_findings = [f for f in findings if f.category in critical_categories and f.severity == "error"]
        if critical_findings:
            steps.append("🚨 CRITICAL: Fix environment/syntax issues first")
            for finding in critical_findings[:2]:  # Show top 2
                steps.extend(finding.suggestions[:1])  # Top suggestion only
        
        # High priority functional issues
        high_priority_findings = [f for f in findings if f.category in high_priority and f.severity == "error"]  
        if high_priority_findings:
            steps.append("🔧 HIGH PRIORITY: Address verification gaps")
            for finding in high_priority_findings[:3]:  # Show top 3
                steps.extend(finding.suggestions[:1])
        
        # Improvement opportunities  
        improvement_findings = [f for f in findings if f.severity in ["warning", "info"]]
        if improvement_findings:
            steps.append("📈 IMPROVEMENTS: Enhance trust and robustness")
            for finding in improvement_findings[:2]:  # Show top 2
                steps.extend(finding.suggestions[:1])
        
        return steps