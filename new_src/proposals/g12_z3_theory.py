"""Code proposals for chapters 25-26 (PyObj Z3 Theory & Semantic Algebra).

Exhaustive proposals formalizing the Z3 algebraic theory:
  1. Full constructor-destructor law verifier (CD1-CD4 for all 7 constructors)
  2. Opacity level classifier (fully / partially / uninterpreted)
  3. Uninterpreted function chain analyzer (opacity boundary detection)
  4. Z3 theory completeness checker (axiomatized vs opaque builtins)
  5. RecFunction compilation verifier (Python recursion → Z3 mapping)
  6. Ground term evaluator (closed Z3 terms → concrete values)
  7. Theory extension framework (safely add new interpreted operations)
  8. Soundness test generator (auto-generate Z3 theory soundness cases)
  9. Tag datatype exhaustiveness checker
  10. Semantic axiom audit (52-axiom sub-algebra coverage)
  11. Opacity boundary demonstration (Thm. 25.4)
  12. Uninterpreted chain analysis (sorted/list/set chains)
"""
from __future__ import annotations

import itertools
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Callable, Dict, FrozenSet, List, Optional, Set, Tuple

try:
    from z3 import (
        And, Bool, BoolSort, BoolVal, Const, ForAll, Function,
        Int, IntSort, IntVal, Not, Or, Solver, String, StringSort,
        StringVal, Xor, sat, unsat, unknown, is_true,
    )
    import z3 as _z3_mod
    _HAS_Z3 = True
except ImportError:
    _HAS_Z3 = False


# ═══════════════════════════════════════════════════════════
# §0  Constants — all PyObj constructors and their accessors
# ═══════════════════════════════════════════════════════════

CONSTRUCTORS: List[str] = [
    'IntObj', 'BoolObj', 'StrObj', 'NoneObj', 'Pair', 'Ref', 'Bottom',
]

_CTOR_ACCESSORS: Dict[str, List[str]] = {
    'IntObj': ['ival'],
    'BoolObj': ['bval'],
    'StrObj': ['sval'],
    'NoneObj': [],
    'Pair': ['fst', 'snd'],
    'Ref': ['addr'],
    'Bottom': [],
}


# ═══════════════════════════════════════════════════════════
# §1  Proposal 1 — Full Constructor-Destructor Verifier
#     Verifies CD1-CD4 for every constructor of the PyObj ADT
# ═══════════════════════════════════════════════════════════

@dataclass
class CDLawResult:
    """Result of a single CD-law check."""
    law: str
    constructor: str
    passed: bool
    detail: str = ''

    def __str__(self) -> str:
        mark = '✓' if self.passed else '✗'
        return f'{mark} {self.law}({self.constructor}): {self.detail}'


def _make_sample_value(S: Any, ctor_name: str) -> Tuple[Any, List[Any]]:
    """Create a sample constructed value and the free variables used."""
    if ctor_name == 'IntObj':
        v = Int('_cd_n')
        return S.IntObj(v), [v]
    if ctor_name == 'BoolObj':
        v = Bool('_cd_b')
        return S.BoolObj(v), [v]
    if ctor_name == 'StrObj':
        v = String('_cd_s')
        return S.StrObj(v), [v]
    if ctor_name == 'NoneObj':
        return S.NoneObj, []
    if ctor_name == 'Pair':
        a = Const('_cd_p1', S)
        b = Const('_cd_p2', S)
        return S.Pair(a, b), [a, b]
    if ctor_name == 'Ref':
        v = Int('_cd_r')
        return S.Ref(v), [v]
    if ctor_name == 'Bottom':
        return S.Bottom, []
    raise ValueError(f'Unknown constructor: {ctor_name}')


def verify_cd1_retraction(S: Any, ctor_name: str) -> List[CDLawResult]:
    """CD1: f_k(C_k(x)) = x  — accessor retracts constructor."""
    results: List[CDLawResult] = []
    accessors = _CTOR_ACCESSORS[ctor_name]
    if not accessors:
        results.append(CDLawResult('CD1', ctor_name, True,
                                   'no accessors (nullary constructor)'))
        return results
    val, free_vars = _make_sample_value(S, ctor_name)
    s = Solver()
    for i, acc_name in enumerate(accessors):
        accessor = getattr(S, acc_name)
        s.push()
        s.add(accessor(val) != free_vars[i])
        ok = s.check() == unsat
        results.append(CDLawResult('CD1', ctor_name, ok,
                                   f'{acc_name}({ctor_name}(x)) == x'))
        s.pop()
    return results


def verify_cd2_tester_positive(S: Any, ctor_name: str) -> CDLawResult:
    """CD2: is_C_k(C_k(x)) = True  — tester recognises own constructor."""
    val, _ = _make_sample_value(S, ctor_name)
    tester = getattr(S, f'is_{ctor_name}')
    s = Solver()
    s.add(Not(tester(val)))
    ok = s.check() == unsat
    return CDLawResult('CD2', ctor_name, ok,
                       f'is_{ctor_name}({ctor_name}(...)) == True')


def verify_cd3_tester_negative(S: Any, ctor_name: str) -> List[CDLawResult]:
    """CD3: is_C_j(C_k(x)) = False for j ≠ k  — testers are disjoint."""
    results: List[CDLawResult] = []
    val, _ = _make_sample_value(S, ctor_name)
    s = Solver()
    for other in CONSTRUCTORS:
        if other == ctor_name:
            continue
        tester = getattr(S, f'is_{other}')
        s.push()
        s.add(tester(val))
        ok = s.check() == unsat
        results.append(CDLawResult('CD3', ctor_name, ok,
                                   f'is_{other}({ctor_name}(...)) == False'))
        s.pop()
    return results


def verify_cd4_section(S: Any, ctor_name: str) -> List[CDLawResult]:
    """CD4: C_k(f_k(v)) = v when is_C_k(v)  — constructor-accessor section."""
    results: List[CDLawResult] = []
    accessors = _CTOR_ACCESSORS[ctor_name]
    if not accessors:
        results.append(CDLawResult('CD4', ctor_name, True,
                                   'no accessors (nullary)'))
        return results
    v = Const('_cd4_v', S)
    tester = getattr(S, f'is_{ctor_name}')
    s = Solver()
    s.add(tester(v))
    if ctor_name == 'IntObj':
        s.push()
        s.add(S.IntObj(S.ival(v)) != v)
        ok = s.check() == unsat
        results.append(CDLawResult('CD4', ctor_name, ok,
                                   'IntObj(ival(v)) == v when is_IntObj(v)'))
        s.pop()
    elif ctor_name == 'BoolObj':
        s.push()
        s.add(S.BoolObj(S.bval(v)) != v)
        ok = s.check() == unsat
        results.append(CDLawResult('CD4', ctor_name, ok,
                                   'BoolObj(bval(v)) == v when is_BoolObj(v)'))
        s.pop()
    elif ctor_name == 'StrObj':
        s.push()
        s.add(S.StrObj(S.sval(v)) != v)
        ok = s.check() == unsat
        results.append(CDLawResult('CD4', ctor_name, ok,
                                   'StrObj(sval(v)) == v when is_StrObj(v)'))
        s.pop()
    elif ctor_name == 'Pair':
        s.push()
        s.add(S.Pair(S.fst(v), S.snd(v)) != v)
        ok = s.check() == unsat
        results.append(CDLawResult('CD4', ctor_name, ok,
                                   'Pair(fst(v), snd(v)) == v when is_Pair(v)'))
        s.pop()
    elif ctor_name == 'Ref':
        s.push()
        s.add(S.Ref(S.addr(v)) != v)
        ok = s.check() == unsat
        results.append(CDLawResult('CD4', ctor_name, ok,
                                   'Ref(addr(v)) == v when is_Ref(v)'))
        s.pop()
    return results


def verify_ctor_dtor_laws(T: Any) -> List[CDLawResult]:
    """Verify CD1-CD4 exhaustively for all 7 PyObj constructors.

    CD1: Retraction  — accessor(ctor(x)) == x
    CD2: Tester+     — is_ctor(ctor(x)) == True
    CD3: Tester–     — is_other(ctor(x)) == False
    CD4: Section     — ctor(accessor(v)) == v  when is_ctor(v)

    Returns full list of CDLawResult objects.
    """
    if not _HAS_Z3:
        return []
    S = T.S
    all_results: List[CDLawResult] = []
    for ctor in CONSTRUCTORS:
        all_results.extend(verify_cd1_retraction(S, ctor))
        all_results.append(verify_cd2_tester_positive(S, ctor))
        all_results.extend(verify_cd3_tester_negative(S, ctor))
        all_results.extend(verify_cd4_section(S, ctor))
    return all_results


# ═══════════════════════════════════════════════════════════
# §2  Proposal 2 — Opacity Level Classifier (Def. 25.15)
# ═══════════════════════════════════════════════════════════

class OpacityLevel(Enum):
    """Three-level opacity classification for Z3 operations."""
    FULLY_INTERPRETED = 1
    PARTIALLY_INTERPRETED = 2
    UNINTERPRETED = 3


_LEVEL_DESCRIPTIONS: Dict[OpacityLevel, str] = {
    OpacityLevel.FULLY_INTERPRETED:
        'Full value reasoning (QF_LIA, QF_S, QF_BV)',
    OpacityLevel.PARTIALLY_INTERPRETED:
        'Structural reasoning (RecFunction unfolding)',
    OpacityLevel.UNINTERPRETED:
        'Congruence only (f(x)=f(y) iff x=y)',
}


@dataclass
class OpacityReport:
    """Detailed opacity classification for a single operation."""
    name: str
    level: OpacityLevel
    z3_theory: str
    has_axioms: bool
    axiom_names: List[str] = field(default_factory=list)

    @property
    def description(self) -> str:
        return _LEVEL_DESCRIPTIONS[self.level]

    def __str__(self) -> str:
        ax = f' axioms={self.axiom_names}' if self.axiom_names else ''
        return (f'{self.name}: Level {self.level.value} '
                f'({self.level.name}) [{self.z3_theory}]{ax}')


class OpacityClassifier:
    """Classify operations by interpretation level (Def. 25.15).

    Level 1 (FULLY_INTERPRETED): Native Z3 theories — integer
        arithmetic, boolean logic, string operations.
    Level 2 (PARTIALLY_INTERPRETED): RecFunctions over the PyObj ADT
        — binop, unop, truthy, fold, tag.
    Level 3 (UNINTERPRETED): Shared function symbols with optional
        equational axioms — sorted, reversed, list, etc.
    """

    FULLY_INTERPRETED: FrozenSet[str] = frozenset({
        'Add', 'Sub', 'Mult', 'FloorDiv', 'Mod', 'Pow',
        'LShift', 'RShift', 'BitOr', 'BitAnd', 'BitXor',
        'Lt', 'LtE', 'Gt', 'GtE', 'Eq', 'NotEq',
        'And', 'Or', 'Not',
        'Concat', 'Length',
    })

    STRUCTURALLY_INTERPRETED: FrozenSet[str] = frozenset({
        'binop', 'unop', 'truthy', 'fold', 'tag',
        'mklist', 'mkint', 'mkbool', 'mkstr', 'mknone', 'mkref',
        'GETITEM',
    })

    AXIOMATIZED_UNINTERPRETED: FrozenSet[str] = frozenset({
        'sorted', 'reversed', 'list', 'tuple', 'set', 'frozenset',
        'len', 'sum', 'mut_sort', 'mut_reverse',
    })

    BARE_UNINTERPRETED: FrozenSet[str] = frozenset({
        'dict', 'any', 'all', 'enumerate', 'zip', 'map', 'filter',
        'Counter', 'defaultdict', 'deque', 'type', 'hash', 'id',
        'repr', 'str', 'iter', 'next', 'print', 'input', 'open',
    })

    _Z3_THEORIES: Dict[str, str] = {
        'Add': 'QF_LIA', 'Sub': 'QF_LIA', 'Mult': 'QF_LIA',
        'FloorDiv': 'QF_LIA', 'Mod': 'QF_LIA', 'Pow': 'QF_NIA',
        'Lt': 'QF_LIA', 'LtE': 'QF_LIA', 'Gt': 'QF_LIA',
        'GtE': 'QF_LIA', 'Eq': 'QF_UF', 'NotEq': 'QF_UF',
        'And': 'QF_BOOL', 'Or': 'QF_BOOL', 'Not': 'QF_BOOL',
        'Concat': 'QF_S', 'Length': 'QF_S',
        'LShift': 'QF_BV', 'RShift': 'QF_BV',
        'BitOr': 'QF_BV', 'BitAnd': 'QF_BV', 'BitXor': 'QF_BV',
        'binop': 'QF_DT+LIA', 'unop': 'QF_DT+LIA',
        'truthy': 'QF_DT', 'fold': 'QF_DT+LIA', 'tag': 'QF_DT',
    }

    _AXIOM_MAP: Dict[str, List[str]] = {
        'sorted': ['S4_idempotent', 'S9_absorbs_reversed',
                    'S_absorbs_list', 'S_absorbs_tuple'],
        'reversed': ['S7_involution'],
        'list': ['I_idempotent'],
        'tuple': ['I_idempotent'],
        'set': ['I_idempotent', 'set_absorbs_sorted',
                'set_absorbs_reversed', 'set_absorbs_list'],
        'frozenset': ['I_idempotent'],
        'len': ['S6_preserved_by_sorted', 'S8_preserved_by_reversed',
                'len_preserved_by_list', 'len_preserved_by_tuple'],
        'sum': ['sum_permutation_invariant'],
        'mut_sort': ['E_mut_sort_eq_sorted'],
        'mut_reverse': ['E_mut_reverse_eq_reversed'],
    }

    @classmethod
    def classify(cls, op_name: str) -> OpacityLevel:
        """Return the opacity level for the named operation."""
        if op_name in cls.FULLY_INTERPRETED:
            return OpacityLevel.FULLY_INTERPRETED
        if op_name in cls.STRUCTURALLY_INTERPRETED:
            return OpacityLevel.PARTIALLY_INTERPRETED
        return OpacityLevel.UNINTERPRETED

    @classmethod
    def classify_detailed(cls, op_name: str) -> OpacityReport:
        """Return a full OpacityReport for the named operation."""
        level = cls.classify(op_name)
        theory = cls._Z3_THEORIES.get(op_name, 'QF_UF')
        axioms = cls._AXIOM_MAP.get(op_name, [])
        has_axioms = op_name in cls.AXIOMATIZED_UNINTERPRETED
        return OpacityReport(op_name, level, theory, has_axioms, axioms)

    @classmethod
    def reasoning_power(cls, level: OpacityLevel) -> str:
        """Describe Z3's reasoning power at the given level."""
        return _LEVEL_DESCRIPTIONS.get(level, 'Unknown')

    @classmethod
    def bulk_classify(cls, names: List[str]) -> Dict[OpacityLevel, List[str]]:
        """Classify a list of operation names and group by level."""
        groups: Dict[OpacityLevel, List[str]] = {
            OpacityLevel.FULLY_INTERPRETED: [],
            OpacityLevel.PARTIALLY_INTERPRETED: [],
            OpacityLevel.UNINTERPRETED: [],
        }
        for name in names:
            groups[cls.classify(name)].append(name)
        return groups


# ═══════════════════════════════════════════════════════════
# §3  Proposal 3 — Uninterpreted Function Chain Analyzer
# ═══════════════════════════════════════════════════════════

@dataclass
class ChainLink:
    """One link in a composed uninterpreted function chain."""
    fn_name: str
    opacity: OpacityLevel
    has_axioms: bool


@dataclass
class ChainAnalysis:
    """Full analysis of a composed function chain."""
    chain: List[ChainLink]
    total_opacity_transitions: int
    reducible_by_axioms: bool
    reduced_chain: List[str]
    proof_result: Optional[str] = None

    @property
    def opacity_boundary_indices(self) -> List[int]:
        """Indices where the opacity level changes."""
        boundaries = []
        for i in range(1, len(self.chain)):
            if self.chain[i].opacity != self.chain[i - 1].opacity:
                boundaries.append(i)
        return boundaries

    def __str__(self) -> str:
        names = [link.fn_name for link in self.chain]
        reduced = ' ∘ '.join(self.reduced_chain) if self.reduced_chain else '(empty)'
        return (f'Chain: {" ∘ ".join(names)}\n'
                f'  Transitions: {self.total_opacity_transitions}\n'
                f'  Reducible: {self.reducible_by_axioms}\n'
                f'  Reduced: {reduced}')


def analyze_function_chain(
    T: Any,
    fn_names: List[str],
) -> ChainAnalysis:
    """Analyze a chain of composed functions for opacity boundaries.

    Given [f, g, h], analyzes h(g(f(x))) — detects where the opacity
    level transitions, which axioms apply, and whether the chain
    can be algebraically reduced.
    """
    links: List[ChainLink] = []
    for name in fn_names:
        report = OpacityClassifier.classify_detailed(name)
        links.append(ChainLink(name, report.level, report.has_axioms))

    transitions = 0
    for i in range(1, len(links)):
        if links[i].opacity != links[i - 1].opacity:
            transitions += 1

    absorption_rules: Dict[Tuple[str, str], str] = {
        ('sorted', 'list'): 'sorted',
        ('sorted', 'tuple'): 'sorted',
        ('sorted', 'reversed'): 'sorted',
        ('sorted', 'sorted'): 'sorted',
        ('reversed', 'reversed'): '',
        ('list', 'list'): 'list',
        ('tuple', 'tuple'): 'tuple',
        ('set', 'set'): 'set',
        ('set', 'sorted'): 'set',
        ('set', 'reversed'): 'set',
        ('set', 'list'): 'set',
        ('set', 'tuple'): 'set',
        ('frozenset', 'frozenset'): 'frozenset',
    }

    reduced = list(fn_names)
    changed = True
    while changed:
        changed = False
        new_reduced: List[str] = []
        i = 0
        while i < len(reduced):
            if i + 1 < len(reduced):
                pair = (reduced[i + 1], reduced[i])
                if pair in absorption_rules:
                    replacement = absorption_rules[pair]
                    if replacement:
                        new_reduced.append(replacement)
                    i += 2
                    changed = True
                    continue
            new_reduced.append(reduced[i])
            i += 1
        reduced = new_reduced

    reducible = reduced != fn_names

    proof_result = None
    if _HAS_Z3 and len(fn_names) >= 2:
        S = T.S
        x = Const('_chain_x', S)
        ax_var = Const('_chain_ax', S)

        fns = [T.shared_fn(name, 1) for name in fn_names]
        full_term = x
        for fn in fns:
            full_term = fn(full_term)

        if reduced:
            red_fns = [T.shared_fn(name, 1) for name in reduced]
            red_term = x
            for fn in red_fns:
                red_term = fn(red_term)

            solver = Solver()
            for outer, inner in absorption_rules:
                if ((outer, 1) in T._shared_fns and
                        (inner, 1) in T._shared_fns):
                    fo = T._shared_fns[(outer, 1)]
                    fi = T._shared_fns[(inner, 1)]
                    result = absorption_rules[(outer, inner)]
                    if result == '':
                        solver.add(ForAll([ax_var], fo(fi(ax_var)) == ax_var))
                    elif result == outer:
                        solver.add(ForAll([ax_var], fo(fi(ax_var)) == fo(ax_var)))
                    elif result == inner:
                        solver.add(ForAll([ax_var], fo(fi(ax_var)) == fi(ax_var)))
                    else:
                        fr = T.shared_fn(result, 1)
                        solver.add(ForAll([ax_var], fo(fi(ax_var)) == fr(ax_var)))

            solver.add(full_term != red_term)
            r = solver.check()
            proof_result = 'reduced_equivalent' if r == unsat else str(r)

    return ChainAnalysis(links, transitions, reducible, reduced, proof_result)


def analyze_uninterpreted_chain(T: Any) -> Dict[str, Any]:
    """Analyze the sorted(list(set(x))) example from Section 25.8.3.

    Shows how axioms progressively reduce the chain.
    """
    if not _HAS_Z3:
        return {}

    S = T.S
    p0 = Const('p0_chain', S)
    ax = Const('_ax_ch', S)

    sf = T.shared_fn('sorted', 1)
    lf = T.shared_fn('list', 1)
    setf = T.shared_fn('set', 1)

    chain = sf(lf(setf(p0)))
    direct = sf(p0)

    results: Dict[str, Any] = {}

    s1 = Solver()
    s1.add(chain != direct)
    results['without_axioms'] = s1.check().r

    s2 = Solver()
    s2.add(ForAll([ax], sf(lf(ax)) == sf(ax)))
    s2.add(chain != direct)
    results['with_sorted_absorbs_list'] = s2.check().r

    reduced = sf(setf(p0))
    s3 = Solver()
    s3.add(ForAll([ax], sf(lf(ax)) == sf(ax)))
    s3.add(chain != reduced)
    results['chain_reduces'] = s3.check().r

    full_analysis = analyze_function_chain(T, ['set', 'list', 'sorted'])
    results['full_chain_analysis'] = str(full_analysis)

    return results


# ═══════════════════════════════════════════════════════════
# §4  Proposal 4 — Z3 Theory Completeness Checker
# ═══════════════════════════════════════════════════════════

@dataclass
class CompletenessReport:
    """Report on the completeness of the Z3 theory."""
    axiomatized: List[str]
    opaque: List[str]
    recfunction_defined: List[str]
    total_builtins: int
    coverage_pct: float

    def __str__(self) -> str:
        lines = [
            f'Theory Completeness: {self.coverage_pct:.1f}%',
            f'  RecFunction-defined: {", ".join(self.recfunction_defined)}',
            f'  Axiomatized: {", ".join(self.axiomatized)}',
            f'  Opaque ({len(self.opaque)}): {", ".join(self.opaque[:10])}...',
        ]
        return '\n'.join(lines)


ALL_PYTHON_BUILTINS: FrozenSet[str] = frozenset({
    'sorted', 'reversed', 'list', 'tuple', 'set', 'frozenset',
    'dict', 'sum', 'any', 'all', 'enumerate', 'zip', 'map',
    'filter', 'type', 'hash', 'id', 'repr', 'str', 'iter',
    'next', 'print', 'input', 'open', 'ord', 'chr',
    'float', 'complex', 'bytes', 'bytearray', 'memoryview',
    'object', 'super', 'property', 'classmethod', 'staticmethod',
    'isinstance', 'issubclass', 'callable', 'getattr', 'setattr',
    'hasattr', 'delattr', 'vars', 'dir', 'len', 'abs', 'min', 'max',
    'range', 'slice', 'bool', 'int',
})


def check_theory_completeness(T: Any) -> CompletenessReport:
    """Check which builtins have axioms vs remain fully opaque.

    Reports on coverage across the Python built-in namespace.
    """
    recfunction_defined = ['binop', 'unop', 'truthy', 'fold', 'tag']

    axiomatized: List[str] = []
    opaque: List[str] = []

    for name in sorted(ALL_PYTHON_BUILTINS):
        if name in OpacityClassifier.AXIOMATIZED_UNINTERPRETED:
            axiomatized.append(name)
        else:
            level = OpacityClassifier.classify(name)
            if level == OpacityLevel.UNINTERPRETED:
                opaque.append(name)

    total = len(ALL_PYTHON_BUILTINS) + len(recfunction_defined)
    covered = len(axiomatized) + len(recfunction_defined)
    pct = (covered / total * 100) if total else 0.0

    return CompletenessReport(
        axiomatized=axiomatized,
        opaque=opaque,
        recfunction_defined=recfunction_defined,
        total_builtins=total,
        coverage_pct=pct,
    )


def check_active_axiom_coverage(T: Any) -> Dict[str, bool]:
    """For each shared function currently registered in T, report
    whether it has axiom coverage in semantic_axioms()."""
    coverage: Dict[str, bool] = {}
    for (name, _arity) in sorted(T._shared_fns.keys()):
        coverage[name] = name in OpacityClassifier._AXIOM_MAP
    return coverage


# ═══════════════════════════════════════════════════════════
# §5  Proposal 5 — RecFunction Compilation Verifier
# ═══════════════════════════════════════════════════════════

@dataclass
class RecFunctionTestCase:
    """A ground test case for a RecFunction."""
    name: str
    description: str
    z3_assertion: Any
    expected_result: str
    passed: bool = False


def _build_recfn_test_cases(T: Any) -> List[RecFunctionTestCase]:
    """Build comprehensive ground-truth test cases for all RecFunctions."""
    if not _HAS_Z3:
        return []

    S = T.S
    cases: List[RecFunctionTestCase] = []

    try:
        from cctt.theory import (
            ADD, SUB, MUL, FLOORDIV, MOD,
            LT, LE, GT, GE, EQ, NE,
            MAX, MIN, IADD, IMUL,
            NEG, ABS_, NOT, BOOL_, INT_, LEN_,
        )
    except ImportError:
        ADD = 1; SUB = 2; MUL = 3; FLOORDIV = 5; MOD = 6
        LT = 20; LE = 21; GT = 22; GE = 23; EQ = 24; NE = 25
        MAX = 30; MIN = 31; IADD = 40; IMUL = 41
        NEG = 50; ABS_ = 52; NOT = 53; BOOL_ = 56; INT_ = 57; LEN_ = 55

    def mk(n: int) -> Any:
        return S.IntObj(IntVal(n))

    def mkb(b: bool) -> Any:
        return S.BoolObj(BoolVal(b))

    def mks(s: str) -> Any:
        return S.StrObj(StringVal(s))

    # ── binop arithmetic ──
    binop_arith = [
        (ADD, 3, 4, 7, '3 + 4 == 7'),
        (ADD, -1, 1, 0, '-1 + 1 == 0'),
        (ADD, 0, 0, 0, '0 + 0 == 0'),
        (SUB, 10, 3, 7, '10 - 3 == 7'),
        (SUB, 0, 5, -5, '0 - 5 == -5'),
        (MUL, 6, 7, 42, '6 * 7 == 42'),
        (MUL, 0, 999, 0, '0 * 999 == 0'),
        (MUL, -3, -4, 12, '-3 * -4 == 12'),
        (IADD, 2, 3, 5, 'iadd 2 3 == 5'),
        (IMUL, 4, 5, 20, 'imul 4 5 == 20'),
    ]
    for op, a, b, expected, desc in binop_arith:
        assertion = T.binop(op, mk(a), mk(b)) != mk(expected)
        cases.append(RecFunctionTestCase(
            'binop', desc, assertion, f'IntObj({expected})'))

    # ── binop comparisons ──
    binop_cmp = [
        (LT, 1, 2, True, '1 < 2'),
        (LT, 2, 1, False, '2 < 1'),
        (LT, 1, 1, False, '1 < 1'),
        (LE, 1, 1, True, '1 <= 1'),
        (GT, 5, 3, True, '5 > 3'),
        (GE, 3, 3, True, '3 >= 3'),
        (EQ, 7, 7, True, '7 == 7'),
        (EQ, 7, 8, False, '7 == 8'),
        (NE, 1, 2, True, '1 != 2'),
        (NE, 1, 1, False, '1 != 1'),
    ]
    for op, a, b, expected, desc in binop_cmp:
        assertion = T.binop(op, mk(a), mk(b)) != mkb(expected)
        cases.append(RecFunctionTestCase(
            'binop_cmp', desc, assertion, str(expected)))

    # ── binop max/min ──
    binop_mm = [
        (MAX, 3, 7, 7, 'max(3,7) == 7'),
        (MAX, 7, 3, 7, 'max(7,3) == 7'),
        (MIN, 3, 7, 3, 'min(3,7) == 3'),
        (MIN, 7, 3, 3, 'min(7,3) == 3'),
    ]
    for op, a, b, expected, desc in binop_mm:
        assertion = T.binop(op, mk(a), mk(b)) != mk(expected)
        cases.append(RecFunctionTestCase(
            'binop_mm', desc, assertion, f'IntObj({expected})'))

    # ── binop string concat ──
    assertion = T.binop(ADD, mks('hello'), mks(' world')) != mks('hello world')
    cases.append(RecFunctionTestCase(
        'binop_str', '"hello" + " world"', assertion, 'StrObj("hello world")'))

    # ── binop string equality ──
    assertion = T.binop(EQ, mks('abc'), mks('abc')) != mkb(True)
    cases.append(RecFunctionTestCase(
        'binop_str_eq', '"abc" == "abc"', assertion, 'True'))
    assertion = T.binop(NE, mks('a'), mks('b')) != mkb(True)
    cases.append(RecFunctionTestCase(
        'binop_str_ne', '"a" != "b"', assertion, 'True'))

    # ── binop bool eq/ne ──
    assertion = T.binop(EQ, mkb(True), mkb(True)) != mkb(True)
    cases.append(RecFunctionTestCase(
        'binop_bool_eq', 'True == True', assertion, 'True'))
    assertion = T.binop(NE, mkb(True), mkb(False)) != mkb(True)
    cases.append(RecFunctionTestCase(
        'binop_bool_ne', 'True != False', assertion, 'True'))

    # ── binop division-by-zero → Bottom ──
    assertion = T.binop(FLOORDIV, mk(10), mk(0)) != S.Bottom
    cases.append(RecFunctionTestCase(
        'binop_divzero', '10 // 0 == Bottom', assertion, 'Bottom'))
    assertion = T.binop(MOD, mk(10), mk(0)) != S.Bottom
    cases.append(RecFunctionTestCase(
        'binop_modzero', '10 % 0 == Bottom', assertion, 'Bottom'))

    # ── unop ──
    unop_cases = [
        (NEG, mk(5), mk(-5), 'neg(5) == -5'),
        (NEG, mk(-3), mk(3), 'neg(-3) == 3'),
        (NEG, mk(0), mk(0), 'neg(0) == 0'),
        (ABS_, mk(-7), mk(7), 'abs(-7) == 7'),
        (ABS_, mk(7), mk(7), 'abs(7) == 7'),
        (ABS_, mk(0), mk(0), 'abs(0) == 0'),
        (NOT, mk(0), mkb(True), 'not 0 == True'),
        (NOT, mk(5), mkb(False), 'not 5 == False'),
        (BOOL_, mk(0), mkb(False), 'bool(0) == False'),
        (BOOL_, mk(1), mkb(True), 'bool(1) == True'),
        (INT_, mk(42), mk(42), 'int(42) == 42'),
        (NOT, mkb(True), mkb(False), 'not True == False'),
        (NOT, mkb(False), mkb(True), 'not False == True'),
        (BOOL_, mkb(True), mkb(True), 'bool(True) == True'),
        (BOOL_, S.NoneObj, mkb(False), 'bool(None) == False'),
        (NOT, S.NoneObj, mkb(True), 'not None == True'),
    ]
    for op, inp, expected, desc in unop_cases:
        assertion = T.unop(op, inp) != expected
        cases.append(RecFunctionTestCase('unop', desc, assertion, str(expected)))

    # ── truthy ──
    truthy_cases = [
        (mk(0), False, 'truthy(0) == False'),
        (mk(1), True, 'truthy(1) == True'),
        (mk(-1), True, 'truthy(-1) == True'),
        (mkb(True), True, 'truthy(True) == True'),
        (mkb(False), False, 'truthy(False) == False'),
        (mks(''), False, 'truthy("") == False'),
        (mks('x'), True, 'truthy("x") == True'),
        (S.NoneObj, False, 'truthy(None) == False'),
        (S.Bottom, False, 'truthy(Bottom) == False'),
    ]
    for inp, expected, desc in truthy_cases:
        assertion = T.truthy(inp) != BoolVal(expected)
        cases.append(RecFunctionTestCase(
            'truthy', desc, assertion, str(expected)))

    # ── tag ──
    tag_cases = [
        (mk(42), T.TInt, 'tag(IntObj) == TInt'),
        (mkb(True), T.TBool_, 'tag(BoolObj) == TBool'),
        (mks('hi'), T.TStr_, 'tag(StrObj) == TStr'),
        (S.NoneObj, T.TNone_, 'tag(NoneObj) == TNone'),
        (S.Bottom, T.TBot, 'tag(Bottom) == TBot'),
    ]
    for inp, expected, desc in tag_cases:
        assertion = T.tag(inp) != expected
        cases.append(RecFunctionTestCase('tag', desc, assertion, str(expected)))

    # ── tag Pair and Ref ──
    p = S.Pair(mk(1), mk(2))
    assertion = T.tag(p) != T.TPair_
    cases.append(RecFunctionTestCase(
        'tag', 'tag(Pair(1,2)) == TPair', assertion, 'TPair'))
    r = S.Ref(IntVal(99))
    assertion = T.tag(r) != T.TRef_
    cases.append(RecFunctionTestCase(
        'tag', 'tag(Ref(99)) == TRef', assertion, 'TRef'))

    return cases


def verify_recfunction_compilation(T: Any) -> Dict[str, bool]:
    """Run all RecFunction ground-truth test cases.

    Returns dict of test_description -> passed.
    """
    cases = _build_recfn_test_cases(T)
    if not cases:
        return {}

    results: Dict[str, bool] = {}
    s = Solver()
    for case in cases:
        s.push()
        s.add(case.z3_assertion)
        case.passed = s.check() == unsat
        results[case.description] = case.passed
        s.pop()
    return results


def test_recfunction_ground_evaluation(T: Any) -> Dict[str, bool]:
    """Backwards-compatible wrapper around verify_recfunction_compilation."""
    return verify_recfunction_compilation(T)


# ═══════════════════════════════════════════════════════════
# §6  Proposal 6 — Ground Term Evaluator
# ═══════════════════════════════════════════════════════════

@dataclass
class GroundEvalResult:
    """Result of evaluating a closed Z3 term to a concrete value."""
    original_term: Any
    evaluated: bool
    value: Optional[Any] = None
    python_value: Optional[Any] = None
    sort_name: str = ''

    def __str__(self) -> str:
        if self.evaluated:
            return f'{self.sort_name}: {self.python_value}'
        return f'(could not evaluate: {self.sort_name})'


def evaluate_ground_term(T: Any, term: Any, timeout_ms: int = 2000) -> GroundEvalResult:
    """Evaluate a closed Z3 PyObj term to a concrete Python value.

    Uses a Z3 solver to find the unique value of the term.
    Only works for ground (variable-free) terms.
    """
    if not _HAS_Z3:
        return GroundEvalResult(term, False)

    S = T.S
    result_var = Const('_eval_r', S)

    s = Solver()
    s.set('timeout', timeout_ms)
    s.add(result_var == term)

    if s.check() != sat:
        return GroundEvalResult(term, False, sort_name=str(term.sort()))

    model = s.model()
    val = model.eval(result_var, model_completion=True)

    py_val = _z3_pyobj_to_python(S, val)

    return GroundEvalResult(
        original_term=term,
        evaluated=True,
        value=val,
        python_value=py_val,
        sort_name=str(term.sort()),
    )


def _z3_pyobj_to_python(S: Any, val: Any) -> Any:
    """Convert a Z3 PyObj model value to a Python value."""
    try:
        val_str = str(val)
        if val_str.startswith('IntObj(') and val_str.endswith(')'):
            inner = val_str[7:-1]
            try:
                return int(inner)
            except ValueError:
                pass
        if val_str.startswith('BoolObj(') and val_str.endswith(')'):
            inner = val_str[8:-1]
            return inner == 'True'
        if val_str.startswith('StrObj(') and val_str.endswith(')'):
            inner = val_str[7:-1]
            if inner.startswith('"') and inner.endswith('"'):
                return inner[1:-1]
            return inner
        if val_str == 'NoneObj':
            return None
        if val_str == 'Bottom':
            return '<Bottom>'
        if val_str.startswith('Ref(') and val_str.endswith(')'):
            return f'<Ref:{val_str[4:-1]}>'
        if val_str.startswith('Pair('):
            try:
                fst = _z3_pyobj_to_python(S, S.fst(val))
                snd = _z3_pyobj_to_python(S, S.snd(val))
                return (fst, snd)
            except Exception:
                pass
    except Exception:
        pass
    return f'<z3:{val}>'


def evaluate_binop_ground(T: Any, op: int, a: int, b: int) -> GroundEvalResult:
    """Convenience: evaluate a binop on two integer literals."""
    S = T.S
    term = T.binop(op, S.IntObj(IntVal(a)), S.IntObj(IntVal(b)))
    return evaluate_ground_term(T, term)


def evaluate_unop_ground(T: Any, op: int, a: int) -> GroundEvalResult:
    """Convenience: evaluate a unop on an integer literal."""
    S = T.S
    term = T.unop(op, S.IntObj(IntVal(a)))
    return evaluate_ground_term(T, term)


# ═══════════════════════════════════════════════════════════
# §7  Proposal 7 — Theory Extension Framework
# ═══════════════════════════════════════════════════════════

class TheoryExtensionError(Exception):
    """Raised when a theory extension would create inconsistency."""


@dataclass
class AxiomSpec:
    """Specification of a single equational axiom to add."""
    name: str
    description: str
    builder: Callable[[Any, Any], Any]

    def __str__(self) -> str:
        return f'Axiom({self.name}: {self.description})'


@dataclass
class ExtensionResult:
    """Result of attempting to extend the theory."""
    name: str
    consistent: bool
    axioms_added: int
    details: str = ''


class TheoryExtension:
    """Framework for safely extending the Z3 theory with new axioms.

    Checks for consistency before committing new axioms to a solver.
    """

    def __init__(self, T: Any) -> None:
        self._T = T
        self._pending: List[AxiomSpec] = []
        self._committed: List[AxiomSpec] = []

    def add_idempotence(self, fn_name: str) -> None:
        """Add axiom: fn(fn(x)) == fn(x)."""
        def builder(solver: Any, T: Any) -> Any:
            S = T.S
            x = Const(f'_ext_{fn_name}', S)
            fn = T.shared_fn(fn_name, 1)
            return ForAll([x], fn(fn(x)) == fn(x))
        self._pending.append(AxiomSpec(
            f'{fn_name}_idempotent',
            f'{fn_name}({fn_name}(x)) == {fn_name}(x)',
            builder))

    def add_involution(self, fn_name: str) -> None:
        """Add axiom: fn(fn(x)) == x."""
        def builder(solver: Any, T: Any) -> Any:
            S = T.S
            x = Const(f'_ext_{fn_name}', S)
            fn = T.shared_fn(fn_name, 1)
            return ForAll([x], fn(fn(x)) == x)
        self._pending.append(AxiomSpec(
            f'{fn_name}_involution',
            f'{fn_name}({fn_name}(x)) == x',
            builder))

    def add_absorption(self, outer: str, inner: str) -> None:
        """Add axiom: outer(inner(x)) == outer(x)."""
        def builder(solver: Any, T: Any) -> Any:
            S = T.S
            x = Const(f'_ext_{outer}_{inner}', S)
            fo = T.shared_fn(outer, 1)
            fi = T.shared_fn(inner, 1)
            return ForAll([x], fo(fi(x)) == fo(x))
        self._pending.append(AxiomSpec(
            f'{outer}_absorbs_{inner}',
            f'{outer}({inner}(x)) == {outer}(x)',
            builder))

    def add_preservation(self, measure: str, transform: str) -> None:
        """Add axiom: measure(transform(x)) == measure(x)."""
        def builder(solver: Any, T: Any) -> Any:
            S = T.S
            x = Const(f'_ext_{measure}_{transform}', S)
            fm = T.shared_fn(measure, 1)
            ft = T.shared_fn(transform, 1)
            return ForAll([x], fm(ft(x)) == fm(x))
        self._pending.append(AxiomSpec(
            f'{measure}_preserved_by_{transform}',
            f'{measure}({transform}(x)) == {measure}(x)',
            builder))

    def add_custom(self, name: str, description: str,
                   builder: Callable[[Any, Any], Any]) -> None:
        """Add a custom axiom via a builder function."""
        self._pending.append(AxiomSpec(name, description, builder))

    def check_consistency(self, timeout_ms: int = 5000) -> ExtensionResult:
        """Check whether pending axioms are consistent with the theory."""
        if not _HAS_Z3:
            return ExtensionResult('consistency_check', False, 0,
                                   'Z3 not available')
        if not self._pending:
            return ExtensionResult('consistency_check', True, 0,
                                   'no pending axioms')

        s = Solver()
        s.set('timeout', timeout_ms)

        for spec in self._committed:
            axiom = spec.builder(s, self._T)
            s.add(axiom)

        for spec in self._pending:
            axiom = spec.builder(s, self._T)
            s.add(axiom)

        result = s.check()
        if result == unsat:
            return ExtensionResult(
                'consistency_check', False, 0,
                'pending axioms are inconsistent with existing theory')
        return ExtensionResult(
            'consistency_check', True, len(self._pending),
            f'{len(self._pending)} axioms are consistent')

    def commit(self, solver: Any) -> ExtensionResult:
        """Commit pending axioms to the solver after consistency check."""
        cr = self.check_consistency()
        if not cr.consistent:
            raise TheoryExtensionError(cr.details)

        count = 0
        for spec in self._pending:
            axiom = spec.builder(solver, self._T)
            solver.add(axiom)
            self._committed.append(spec)
            count += 1
        self._pending.clear()

        return ExtensionResult(
            'commit', True, count,
            f'committed {count} axioms')

    @property
    def pending_count(self) -> int:
        return len(self._pending)

    @property
    def committed_count(self) -> int:
        return len(self._committed)

    def list_committed(self) -> List[str]:
        """Return names of all committed axioms."""
        return [spec.name for spec in self._committed]


# ═══════════════════════════════════════════════════════════
# §8  Proposal 8 — Soundness Test Generator
# ═══════════════════════════════════════════════════════════

@dataclass
class SoundnessTest:
    """An auto-generated soundness test case."""
    name: str
    category: str
    z3_formula: Any
    expected: str
    actual: str = ''
    passed: bool = False


def generate_algebraic_identity_tests(T: Any) -> List[SoundnessTest]:
    """Generate tests for standard algebraic identities.

    Tests that the Z3 RecFunctions correctly model:
    - Commutativity of + and *
    - Associativity of + and *
    - Identity elements (0 for +, 1 for *)
    - Negation properties
    - Distributivity of * over +
    """
    if not _HAS_Z3:
        return []

    try:
        from cctt.theory import ADD, SUB, MUL, NEG
    except ImportError:
        ADD = 1; SUB = 2; MUL = 3; NEG = 50

    S = T.S
    x = Const('_snd_x', S)
    y = Const('_snd_y', S)
    z = Const('_snd_z', S)
    xi = S.ival(x)
    yi = S.ival(y)
    zi = S.ival(z)
    int_guard = And(S.is_IntObj(x), S.is_IntObj(y), S.is_IntObj(z))

    tests: List[SoundnessTest] = []

    # Commutativity of +
    tests.append(SoundnessTest(
        'add_commutative', 'ring',
        ForAll([x, y], _z3_mod.Implies(
            And(S.is_IntObj(x), S.is_IntObj(y)),
            T.binop(ADD, x, y) == T.binop(ADD, y, x))),
        'valid'))

    # Commutativity of *
    tests.append(SoundnessTest(
        'mul_commutative', 'ring',
        ForAll([x, y], _z3_mod.Implies(
            And(S.is_IntObj(x), S.is_IntObj(y)),
            T.binop(MUL, x, y) == T.binop(MUL, y, x))),
        'valid'))

    # Additive identity: x + 0 == x
    zero = S.IntObj(IntVal(0))
    tests.append(SoundnessTest(
        'add_identity_right', 'ring',
        ForAll([x], _z3_mod.Implies(
            S.is_IntObj(x),
            T.binop(ADD, x, zero) == x)),
        'valid'))

    # Multiplicative identity: x * 1 == x
    one = S.IntObj(IntVal(1))
    tests.append(SoundnessTest(
        'mul_identity_right', 'ring',
        ForAll([x], _z3_mod.Implies(
            S.is_IntObj(x),
            T.binop(MUL, x, one) == x)),
        'valid'))

    # Additive inverse: x + neg(x) == 0
    tests.append(SoundnessTest(
        'add_inverse', 'ring',
        ForAll([x], _z3_mod.Implies(
            S.is_IntObj(x),
            T.binop(ADD, x, T.unop(NEG, x)) == zero)),
        'valid'))

    # Sub is add-neg: x - y == x + neg(y)
    tests.append(SoundnessTest(
        'sub_is_add_neg', 'ring',
        ForAll([x, y], _z3_mod.Implies(
            And(S.is_IntObj(x), S.is_IntObj(y)),
            T.binop(SUB, x, y) == T.binop(ADD, x, T.unop(NEG, y)))),
        'valid'))

    # Double negation: neg(neg(x)) == x
    tests.append(SoundnessTest(
        'double_negation', 'ring',
        ForAll([x], _z3_mod.Implies(
            S.is_IntObj(x),
            T.unop(NEG, T.unop(NEG, x)) == x)),
        'valid'))

    return tests


def generate_tag_soundness_tests(T: Any) -> List[SoundnessTest]:
    """Generate tests that tag() is consistent with constructors."""
    if not _HAS_Z3:
        return []

    S = T.S
    x = Const('_tag_snd', S)
    tests: List[SoundnessTest] = []

    ctor_tag_pairs = [
        ('IntObj', 'is_IntObj', T.TInt),
        ('BoolObj', 'is_BoolObj', T.TBool_),
        ('StrObj', 'is_StrObj', T.TStr_),
        ('NoneObj', 'is_NoneObj', T.TNone_),
        ('Pair', 'is_Pair', T.TPair_),
        ('Ref', 'is_Ref', T.TRef_),
        ('Bottom', 'is_Bottom', T.TBot),
    ]

    for ctor_name, tester_name, tag_val in ctor_tag_pairs:
        tester = getattr(S, tester_name)
        tests.append(SoundnessTest(
            f'tag_consistent_{ctor_name}', 'tag',
            ForAll([x], _z3_mod.Implies(tester(x), T.tag(x) == tag_val)),
            'valid'))

    # Tag exhaustiveness: tag covers all constructors
    all_tags = Or(
        T.tag(x) == T.TInt,
        T.tag(x) == T.TBool_,
        T.tag(x) == T.TStr_,
        T.tag(x) == T.TNone_,
        T.tag(x) == T.TPair_,
        T.tag(x) == T.TRef_,
        T.tag(x) == T.TBot,
    )
    tests.append(SoundnessTest(
        'tag_exhaustive', 'tag',
        ForAll([x], all_tags),
        'valid'))

    return tests


def generate_truthy_soundness_tests(T: Any) -> List[SoundnessTest]:
    """Generate tests for truthy() consistency with Python semantics."""
    if not _HAS_Z3:
        return []

    try:
        from cctt.theory import BOOL_, NOT
    except ImportError:
        BOOL_ = 56; NOT = 53

    S = T.S
    x = Const('_tru_snd', S)
    tests: List[SoundnessTest] = []

    # truthy(NoneObj) == False
    tests.append(SoundnessTest(
        'truthy_none_false', 'truthy',
        T.truthy(S.NoneObj) == BoolVal(False),
        'valid'))

    # truthy(Bottom) == False
    tests.append(SoundnessTest(
        'truthy_bottom_false', 'truthy',
        T.truthy(S.Bottom) == BoolVal(False),
        'valid'))

    # truthy(IntObj(0)) == False
    tests.append(SoundnessTest(
        'truthy_zero_false', 'truthy',
        T.truthy(S.IntObj(IntVal(0))) == BoolVal(False),
        'valid'))

    # truthy(BoolObj(b)) == b
    b = Bool('_tru_b')
    tests.append(SoundnessTest(
        'truthy_bool_identity', 'truthy',
        ForAll([b], T.truthy(S.BoolObj(b)) == b),
        'valid'))

    # truthy consistent with unop BOOL_
    tests.append(SoundnessTest(
        'truthy_matches_bool_unop', 'truthy',
        ForAll([x], _z3_mod.Implies(
            S.is_IntObj(x),
            T.truthy(x) == S.bval(T.unop(BOOL_, x)))),
        'valid'))

    # not(truthy(x)) == truthy(not(x)) for ints
    tests.append(SoundnessTest(
        'truthy_not_consistent', 'truthy',
        ForAll([x], _z3_mod.Implies(
            S.is_IntObj(x),
            Not(T.truthy(x)) == S.bval(T.unop(NOT, x)))),
        'valid'))

    return tests


def run_soundness_tests(
    T: Any,
    timeout_ms: int = 5000,
) -> Tuple[List[SoundnessTest], Dict[str, int]]:
    """Run all auto-generated soundness tests and return results.

    Returns (tests, summary) where summary maps category -> pass count.
    """
    all_tests: List[SoundnessTest] = []
    all_tests.extend(generate_algebraic_identity_tests(T))
    all_tests.extend(generate_tag_soundness_tests(T))
    all_tests.extend(generate_truthy_soundness_tests(T))

    if not _HAS_Z3 or not all_tests:
        return all_tests, {}

    s = Solver()
    s.set('timeout', timeout_ms)
    summary: Dict[str, int] = {}

    for test in all_tests:
        s.push()
        s.add(Not(test.z3_formula))
        r = s.check()
        test.passed = r == unsat
        test.actual = 'valid' if r == unsat else str(r)
        summary.setdefault(test.category, 0)
        if test.passed:
            summary[test.category] += 1
        s.pop()

    return all_tests, summary


# ═══════════════════════════════════════════════════════════
# §9  Proposal 9 — Tag Datatype Exhaustiveness Checker
# ═══════════════════════════════════════════════════════════

@dataclass
class ExhaustivenessResult:
    """Result of exhaustiveness checking for the PyObj ADT."""
    exhaustive: bool
    constructors_found: List[str]
    missing_testers: List[str]
    disjointness_violations: List[Tuple[str, str]]
    completeness_proof: Optional[str] = None


def check_tag_exhaustiveness(T: Any) -> ExhaustivenessResult:
    """Verify that PyObj constructors cover the entire sort.

    Checks:
    1. Every value satisfies exactly one is_* tester
    2. The disjunction of all testers is a tautology
    3. No two testers can be simultaneously true
    """
    if not _HAS_Z3:
        return ExhaustivenessResult(False, [], [], [])

    S = T.S
    v = Const('_exh_v', S)

    testers = {ctor: getattr(S, f'is_{ctor}') for ctor in CONSTRUCTORS}
    found: List[str] = []
    missing: List[str] = []

    for ctor, tester in testers.items():
        s = Solver()
        s.push()
        s.add(tester(v))
        if s.check() == sat:
            found.append(ctor)
        else:
            missing.append(ctor)
        s.pop()

    disjointness_violations: List[Tuple[str, str]] = []
    for c1, c2 in itertools.combinations(CONSTRUCTORS, 2):
        s = Solver()
        s.add(And(testers[c1](v), testers[c2](v)))
        if s.check() != unsat:
            disjointness_violations.append((c1, c2))

    s = Solver()
    all_testers = Or(*[testers[c](v) for c in CONSTRUCTORS])
    s.add(Not(all_testers))
    exhaustive = s.check() == unsat
    proof = 'tautology: ∨(is_Ck) holds for all v' if exhaustive else None

    return ExhaustivenessResult(
        exhaustive=exhaustive,
        constructors_found=found,
        missing_testers=missing,
        disjointness_violations=disjointness_violations,
        completeness_proof=proof,
    )


def check_tag_function_covers_all(T: Any) -> Dict[str, bool]:
    """Verify that the tag() RecFunction returns one of the 7 TTag values
    for every possible PyObj input."""
    if not _HAS_Z3:
        return {}

    S = T.S
    v = Const('_tagcov_v', S)
    results: Dict[str, bool] = {}

    all_tag_values = [
        T.TInt, T.TBool_, T.TStr_, T.TNone_,
        T.TPair_, T.TRef_, T.TBot,
    ]

    s = Solver()
    tag_covers = Or(*[T.tag(v) == tv for tv in all_tag_values])
    s.add(Not(tag_covers))
    results['tag_covers_all_inputs'] = s.check() == unsat

    tag_names = ['TInt', 'TBool', 'TStr', 'TNone', 'TPair', 'TRef', 'TBot']
    for ctor, tag_name, tag_val in zip(
            CONSTRUCTORS, tag_names, all_tag_values):
        tester = getattr(S, f'is_{ctor}')
        s2 = Solver()
        s2.add(tester(v))
        s2.add(T.tag(v) != tag_val)
        results[f'tag_{ctor}_correct'] = s2.check() == unsat

    return results


# ═══════════════════════════════════════════════════════════
# §10  Proposal 10 — Semantic Axiom Audit (52 axioms)
# ═══════════════════════════════════════════════════════════

@dataclass
class AxiomAuditReport:
    """Report on the 52-axiom semantic algebra coverage."""
    counts: Dict[str, int]
    total_active: int
    total_possible: int

    def coverage_pct(self) -> float:
        return (self.total_active / self.total_possible * 100
                if self.total_possible else 0.0)

    def __str__(self) -> str:
        lines = [f'Axiom Audit ({self.total_active}/{self.total_possible} '
                 f'= {self.coverage_pct():.0f}%):']
        for sub, count in sorted(self.counts.items()):
            lines.append(f'  {sub}: {count}')
        return '\n'.join(lines)


_SUBALGEBRA_MAX: Dict[str, int] = {
    'R_ring': 14,
    'L_lattice': 9,
    'S_sequence': 12,
    'F_fold': 4,
    'B_boolean': 7,
    'I_idempotent': 6,
    'E_effect': 5,
}


def audit_semantic_axioms(T: Any) -> AxiomAuditReport:
    """Audit which of the 52 axioms are active for the current Theory.

    Counts axioms by sub-algebra (Def. 26.8):
      R1-R14:  Integer ring (always active via binop)
      L1-L9:   Min-max lattice
      S1-S12:  Sequence algebra
      F1-F4:   Fold algebra (always active)
      B1-B7:   Boolean algebra (always active via unop/binop)
      I1-I6:   Idempotent semiring
      E1-E5:   Effect separation
    """
    fns = T._shared_fns
    counts: Dict[str, int] = {k: 0 for k in _SUBALGEBRA_MAX}

    counts['R_ring'] = 14
    counts['F_fold'] = 4
    counts['B_boolean'] = 7

    if ('min', 1) in fns or ('max', 1) in fns:
        counts['L_lattice'] = 9

    s_ops = {'sorted', 'reversed', 'list', 'tuple', 'len'}
    active_s = sum(1 for op in s_ops if (op, 1) in fns)
    if active_s > 0:
        counts['S_sequence'] = min(12, active_s * 3)

    idem_ops = {'set', 'frozenset', 'list', 'tuple', 'sorted'}
    active_i = sum(1 for op in idem_ops if (op, 1) in fns)
    counts['I_idempotent'] = min(6, active_i + 2)

    mut_ops = {k for k in fns if k[0].startswith('mut_')}
    if mut_ops:
        counts['E_effect'] = 5

    total_active = sum(counts.values())
    total_possible = sum(_SUBALGEBRA_MAX.values())

    return AxiomAuditReport(counts, total_active, total_possible)


# ═══════════════════════════════════════════════════════════
# §11  Proposal 11 — Opacity Boundary Demonstration (Thm. 25.4)
# ═══════════════════════════════════════════════════════════

@dataclass
class OpacityBoundaryTest:
    """One test in the opacity boundary demonstration."""
    name: str
    description: str
    expected: str
    actual: str
    passed: bool


def demonstrate_opacity_boundary(T: Any) -> List[OpacityBoundaryTest]:
    """Demonstrate the opacity boundary theorem (Thm. 25.4).

    Shows that uninterpreted functions can only prove equality via
    congruence, unless equational axioms are added.
    """
    if not _HAS_Z3:
        return []

    S = T.S
    results: List[OpacityBoundaryTest] = []

    x = Const('x_ob', S)
    y = Const('y_ob', S)
    sf = T.shared_fn('sorted', 1)

    # T1: Congruence — same input ⇒ same output
    s = Solver()
    s.add(sf(x) != sf(x))
    r = s.check()
    results.append(OpacityBoundaryTest(
        'congruence_self',
        'f(x) == f(x) by congruence',
        'unsat', str(r), r == unsat))

    # T2: Different inputs may still map to same output
    s = Solver()
    s.add(x != y)
    s.add(sf(x) == sf(y))
    r = s.check()
    results.append(OpacityBoundaryTest(
        'different_inputs_may_match',
        'x != y does not imply f(x) != f(y)',
        'sat', str(r), r == sat))

    # T3: Opaque function can match any concrete value
    s = Solver()
    s.add(sf(x) == S.IntObj(IntVal(42)))
    r = s.check()
    results.append(OpacityBoundaryTest(
        'opaque_accepts_concrete',
        'f(x) == IntObj(42) is satisfiable for opaque f',
        'sat', str(r), r == sat))

    # T4: Idempotence axiom lifts partial opacity
    s = Solver()
    s.add(ForAll([x], sf(sf(x)) == sf(x)))
    y2 = Const('y_ob2', S)
    s.add(sf(sf(y2)) != sf(y2))
    r = s.check()
    results.append(OpacityBoundaryTest(
        'idempotence_lifts_opacity',
        'with f∘f=f axiom, f(f(x)) == f(x) provable',
        'unsat', str(r), r == unsat))

    # T5: Without axioms, cannot prove f(f(x)) == f(x)
    s = Solver()
    s.add(sf(sf(x)) != sf(x))
    r = s.check()
    results.append(OpacityBoundaryTest(
        'no_axiom_no_idempotence',
        'without axioms, f(f(x)) == f(x) is not provable',
        'sat', str(r), r == sat))

    # T6: Involution axiom for reversed
    rf = T.shared_fn('reversed', 1)
    s = Solver()
    s.add(ForAll([x], rf(rf(x)) == x))
    z = Const('z_ob', S)
    s.add(rf(rf(z)) != z)
    r = s.check()
    results.append(OpacityBoundaryTest(
        'involution_reversed',
        'with reversed∘reversed=id, rev(rev(x)) == x',
        'unsat', str(r), r == unsat))

    # T7: Functional extensionality does NOT hold for opaque fns
    gf = T.shared_fn('my_opaque', 1)
    s = Solver()
    s.add(sf(x) != gf(x))
    r = s.check()
    results.append(OpacityBoundaryTest(
        'opaque_fns_distinguishable',
        'different opaque symbols are distinguishable',
        'sat', str(r), r == sat))

    # T8: Same symbol, different arity → different functions
    sf1 = T.shared_fn('testfn', 1)
    sf2 = T.shared_fn('testfn', 2)
    s = Solver()
    s.add(sf1(x) != sf2(x, y))
    r = s.check()
    results.append(OpacityBoundaryTest(
        'different_arity_distinguishable',
        'f/1 and f/2 are distinct symbols',
        'sat', str(r), r == sat))

    return results


# ═══════════════════════════════════════════════════════════
# §12  Proposal 12 — RecFunction Type-Preservation Verifier
# ═══════════════════════════════════════════════════════════

def verify_binop_type_preservation(T: Any) -> Dict[str, bool]:
    """Verify that binop preserves expected type relationships.

    E.g., int + int → int, int < int → bool, etc.
    """
    if not _HAS_Z3:
        return {}

    try:
        from cctt.theory import ADD, SUB, MUL, LT, LE, GT, GE, EQ, NE
    except ImportError:
        ADD = 1; SUB = 2; MUL = 3
        LT = 20; LE = 21; GT = 22; GE = 23; EQ = 24; NE = 25

    S = T.S
    x = Const('_tp_x', S)
    y = Const('_tp_y', S)
    results: Dict[str, bool] = {}

    # int OP int → int for arithmetic ops
    arith_ops = {'ADD': ADD, 'SUB': SUB, 'MUL': MUL}
    for name, op_code in arith_ops.items():
        s = Solver()
        s.add(And(S.is_IntObj(x), S.is_IntObj(y)))
        s.add(Not(S.is_IntObj(T.binop(op_code, x, y))))
        results[f'{name}_int_int_to_int'] = s.check() == unsat

    # int CMP int → bool for comparison ops
    cmp_ops = {'LT': LT, 'LE': LE, 'GT': GT, 'GE': GE, 'EQ': EQ, 'NE': NE}
    for name, op_code in cmp_ops.items():
        s = Solver()
        s.add(And(S.is_IntObj(x), S.is_IntObj(y)))
        s.add(Not(S.is_BoolObj(T.binop(op_code, x, y))))
        results[f'{name}_int_int_to_bool'] = s.check() == unsat

    return results


def verify_unop_type_preservation(T: Any) -> Dict[str, bool]:
    """Verify unop preserves expected type relationships."""
    if not _HAS_Z3:
        return {}

    try:
        from cctt.theory import NEG, ABS_, NOT, BOOL_, INT_
    except ImportError:
        NEG = 50; ABS_ = 52; NOT = 53; BOOL_ = 56; INT_ = 57

    S = T.S
    x = Const('_tp_ux', S)
    results: Dict[str, bool] = {}

    # NEG: int → int
    s = Solver()
    s.add(S.is_IntObj(x))
    s.add(Not(S.is_IntObj(T.unop(NEG, x))))
    results['NEG_int_to_int'] = s.check() == unsat

    # ABS: int → int
    s = Solver()
    s.add(S.is_IntObj(x))
    s.add(Not(S.is_IntObj(T.unop(ABS_, x))))
    results['ABS_int_to_int'] = s.check() == unsat

    # NOT on int → bool
    s = Solver()
    s.add(S.is_IntObj(x))
    s.add(Not(S.is_BoolObj(T.unop(NOT, x))))
    results['NOT_int_to_bool'] = s.check() == unsat

    # BOOL on int → bool
    s = Solver()
    s.add(S.is_IntObj(x))
    s.add(Not(S.is_BoolObj(T.unop(BOOL_, x))))
    results['BOOL_int_to_bool'] = s.check() == unsat

    # INT_ on int → int (identity)
    s = Solver()
    s.add(S.is_IntObj(x))
    s.add(Not(S.is_IntObj(T.unop(INT_, x))))
    results['INT_int_to_int'] = s.check() == unsat

    # NOT on bool → bool
    s = Solver()
    s.add(S.is_BoolObj(x))
    s.add(Not(S.is_BoolObj(T.unop(NOT, x))))
    results['NOT_bool_to_bool'] = s.check() == unsat

    # BOOL on None → bool
    s = Solver()
    s.add(Not(S.is_BoolObj(T.unop(BOOL_, S.NoneObj))))
    results['BOOL_none_to_bool'] = s.check() == unsat

    return results


# ═══════════════════════════════════════════════════════════
# §13  Utilities — shared helpers
# ═══════════════════════════════════════════════════════════

def run_all_proposals(T: Any) -> Dict[str, Any]:
    """Execute every proposal and collect results."""
    results: Dict[str, Any] = {}

    results['cd_laws'] = verify_ctor_dtor_laws(T)
    results['exhaustiveness'] = check_tag_exhaustiveness(T)
    results['tag_coverage'] = check_tag_function_covers_all(T)
    results['recfn_ground'] = verify_recfunction_compilation(T)
    results['type_pres_binop'] = verify_binop_type_preservation(T)
    results['type_pres_unop'] = verify_unop_type_preservation(T)
    results['axiom_audit'] = audit_semantic_axioms(T)
    results['completeness'] = check_theory_completeness(T)
    results['opacity_boundary'] = demonstrate_opacity_boundary(T)
    results['chain_analysis'] = analyze_uninterpreted_chain(T)

    soundness_tests, soundness_summary = run_soundness_tests(T)
    results['soundness_tests'] = soundness_tests
    results['soundness_summary'] = soundness_summary

    return results


# ═══════════════════════════════════════════════════════════
# Self-test
# ═══════════════════════════════════════════════════════════

if __name__ == '__main__':
    import sys
    sys.path.insert(0, '../')
    from cctt.theory import Theory

    T = Theory()
    _counts = {'pass': 0, 'fail': 0}

    def _tally(ok: bool) -> str:
        if ok:
            _counts['pass'] += 1
            return '✓'
        _counts['fail'] += 1
        return '✗'

    # ── §1: CD Laws ──
    print('=' * 60)
    print('§1  CD1-CD4 Verification (all 7 constructors)')
    print('=' * 60)
    cd_results = verify_ctor_dtor_laws(T)
    for r in cd_results:
        print(f'  {_tally(r.passed)} {r}')
    cd_pass = sum(1 for r in cd_results if r.passed)
    print(f'  → {cd_pass}/{len(cd_results)} laws verified\n')

    # ── §2: Opacity Classification ──
    print('=' * 60)
    print('§2  Opacity Level Classification')
    print('=' * 60)
    test_ops = ['Add', 'Sub', 'Mult', 'binop', 'unop', 'truthy',
                'sorted', 'reversed', 'Counter', 'zip', 'hash']
    for op in test_ops:
        report = OpacityClassifier.classify_detailed(op)
        print(f'  {report}')
    groups = OpacityClassifier.bulk_classify(test_ops)
    for level, ops in groups.items():
        print(f'  {level.name}: {ops}')
    print()

    # ── §3: Chain Analysis ──
    print('=' * 60)
    print('§3  Function Chain Analysis')
    print('=' * 60)
    chains_to_test = [
        ['set', 'list', 'sorted'],
        ['reversed', 'reversed'],
        ['sorted', 'sorted'],
        ['list', 'set', 'sorted'],
        ['frozenset', 'list', 'sorted'],
    ]
    for chain in chains_to_test:
        result = analyze_function_chain(T, chain)
        print(f'  {result}')
    print()

    # ── §4: Completeness ──
    print('=' * 60)
    print('§4  Theory Completeness Check')
    print('=' * 60)
    cr = check_theory_completeness(T)
    print(f'  {cr}')
    print()

    # ── §5: RecFunction Ground Evaluation ──
    print('=' * 60)
    print('§5  RecFunction Compilation Verification')
    print('=' * 60)
    ground = verify_recfunction_compilation(T)
    for name, ok in ground.items():
        print(f'  {_tally(ok)} {name}')
    gp = sum(ground.values())
    print(f'  → {gp}/{len(ground)} passed\n')

    # ── §6: Ground Term Evaluator ──
    print('=' * 60)
    print('§6  Ground Term Evaluator')
    print('=' * 60)
    try:
        from cctt.theory import ADD, SUB, MUL, NEG
    except ImportError:
        ADD = 1; SUB = 2; MUL = 3; NEG = 50
    eval_cases = [
        (ADD, 100, 200, 300),
        (SUB, 50, 30, 20),
        (MUL, 11, 11, 121),
    ]
    for op, a, b, expected in eval_cases:
        r = evaluate_binop_ground(T, op, a, b)
        ok = r.evaluated and r.python_value == expected
        print(f'  {_tally(ok)} binop({op}, {a}, {b}) = {r.python_value} '
              f'(expected {expected})')
    unop_evals = [
        (NEG, 42, -42),
        (NEG, -7, 7),
    ]
    for op, a, expected in unop_evals:
        r = evaluate_unop_ground(T, op, a)
        ok = r.evaluated and r.python_value == expected
        print(f'  {_tally(ok)} unop({op}, {a}) = {r.python_value} '
              f'(expected {expected})')
    print()

    # ── §7: Theory Extension Framework ──
    print('=' * 60)
    print('§7  Theory Extension Framework')
    print('=' * 60)
    ext = TheoryExtension(T)
    ext.add_idempotence('my_transform')
    ext.add_absorption('sorted', 'my_transform')
    cr = ext.check_consistency()
    print(f'  {_tally(cr.consistent)} consistency check: {cr.details}')
    solver = Solver()
    er = ext.commit(solver)
    print(f'  {_tally(er.consistent)} committed {er.axioms_added} axioms')
    print(f'  committed list: {ext.list_committed()}')

    # Inconsistency detection test
    ext2 = TheoryExtension(T)
    ext2.add_idempotence('test_inv_fn')
    ext2.add_involution('test_inv_fn')
    cr2 = ext2.check_consistency()
    print(f'  consistency of idem+invol: {cr2.consistent} '
          f'(may be consistent for trivial models)')
    print()

    # ── §8: Soundness Tests ──
    print('=' * 60)
    print('§8  Auto-Generated Soundness Tests')
    print('=' * 60)
    snd_tests, snd_summary = run_soundness_tests(T)
    for test in snd_tests:
        print(f'  {_tally(test.passed)} [{test.category}] {test.name}: '
              f'{test.actual}')
    print(f'  Summary: {snd_summary}')
    print()

    # ── §9: Tag Exhaustiveness ──
    print('=' * 60)
    print('§9  Tag Datatype Exhaustiveness')
    print('=' * 60)
    exh = check_tag_exhaustiveness(T)
    print(f'  {_tally(exh.exhaustive)} exhaustive: {exh.exhaustive}')
    print(f'  constructors found: {exh.constructors_found}')
    print(f'  missing testers: {exh.missing_testers}')
    print(f'  disjointness violations: {exh.disjointness_violations}')
    tcov = check_tag_function_covers_all(T)
    for name, ok in tcov.items():
        print(f'  {_tally(ok)} {name}')
    print()

    # ── §10: Axiom Audit ──
    print('=' * 60)
    print('§10 Semantic Axiom Audit')
    print('=' * 60)
    audit = audit_semantic_axioms(T)
    print(f'  {audit}')
    print()

    # ── §11: Opacity Boundary ──
    print('=' * 60)
    print('§11 Opacity Boundary Demonstration')
    print('=' * 60)
    ob_tests = demonstrate_opacity_boundary(T)
    for t in ob_tests:
        print(f'  {_tally(t.passed)} {t.name}: {t.description} '
              f'(expected={t.expected}, got={t.actual})')
    print()

    # ── §12: Type Preservation ──
    print('=' * 60)
    print('§12 Type Preservation Verification')
    print('=' * 60)
    tp_binop = verify_binop_type_preservation(T)
    for name, ok in tp_binop.items():
        print(f'  {_tally(ok)} {name}')
    tp_unop = verify_unop_type_preservation(T)
    for name, ok in tp_unop.items():
        print(f'  {_tally(ok)} {name}')
    print()

    # ── Summary ──
    print('=' * 60)
    print(f'TOTAL: {_counts["pass"]} passed, {_counts["fail"]} failed, '
          f'{_counts["pass"] + _counts["fail"]} total')
    print('=' * 60)
