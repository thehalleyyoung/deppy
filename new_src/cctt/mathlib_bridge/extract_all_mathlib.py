"""
Extract ALL theorems and lemmas from the full Mathlib4 repository.

Walks every .lean file under the Mathlib directory, extracts theorem/lemma
declarations using robust regex-based parsing with namespace tracking, and
produces a JSON catalog for downstream CCTT axiom generation.

Usage:
    PYTHONPATH=new_src python3 -m cctt.mathlib_bridge.extract_all_mathlib \
        --mathlib-dir /path/to/mathlib4_full/Mathlib \
        --output new_src/cctt/mathlib_bridge/mathlib_full_catalog.json
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys
import time
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Dict, List, Optional, Tuple


# ═══════════════════════════════════════════════════════════════════════════════
#  Data model
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class MathlibTheorem:
    name: str                     # fully qualified
    file_path: str                # source file (relative to Mathlib root)
    params: str                   # parameter text
    proposition: str              # the type/statement
    proof_text: str               # proof body (may be truncated)
    attributes: List[str]         # @[simp], @[ext], etc.
    namespace: str
    is_simp: bool                 # has @[simp]
    category: str                 # "list", "nat", "logic", "algebra", etc.
    subcategory: str              # "map", "filter", "comm", etc.
    kind: str = "theorem"         # "theorem" or "lemma"

    def to_dict(self) -> dict:
        return asdict(self)


# ═══════════════════════════════════════════════════════════════════════════════
#  Category classification
# ═══════════════════════════════════════════════════════════════════════════════

# Maps namespace/name prefixes to categories
_CATEGORY_RULES: List[Tuple[str, str]] = [
    # Specific data structures
    ("List", "list"),
    ("Array", "array"),
    ("String", "string"),
    ("Char", "string"),
    ("Option", "option"),
    ("Prod", "product"),
    ("Sigma", "product"),
    ("PProd", "product"),
    ("Sum", "product"),
    ("Fin", "arithmetic"),
    ("Finset", "finset"),
    ("Finsupp", "multiset"),
    ("Multiset", "multiset"),
    ("Set", "set"),
    ("Bool", "boolean"),
    ("Nat", "arithmetic"),
    ("Int", "arithmetic"),
    ("Rat", "arithmetic"),
    ("Real", "arithmetic"),
    ("Complex", "arithmetic"),
    ("Float", "arithmetic"),
    ("UInt", "arithmetic"),
    # Logic
    ("And", "logic"),
    ("Or", "logic"),
    ("Not", "logic"),
    ("Iff", "logic"),
    ("Exists", "logic"),
    ("Classical", "logic"),
    ("Decidable", "logic"),
    ("True", "logic"),
    ("False", "logic"),
    ("Eq", "logic"),
    ("HEq", "logic"),
    ("PLift", "logic"),
    ("ULift", "logic"),
    # Functions
    ("Function", "function"),
    ("Embedding", "function"),
    ("Injective", "function"),
    ("Surjective", "function"),
    ("Bijective", "function"),
    # Order
    ("LE", "order"),
    ("LT", "order"),
    ("GE", "order"),
    ("GT", "order"),
    ("Max", "order"),
    ("Min", "order"),
    ("Sup", "order"),
    ("Inf", "order"),
    ("Lattice", "order"),
    ("CompleteLattice", "order"),
    ("BooleanAlgebra", "order"),
    ("LinearOrder", "order"),
    ("PartialOrder", "order"),
    ("Preorder", "order"),
    ("OrderDual", "order"),
    ("OrderIso", "order"),
    ("OrderEmbedding", "order"),
    ("GaloisConnection", "order"),
    ("Filter", "order"),
    # Algebra
    ("Add", "algebra"),
    ("Mul", "algebra"),
    ("Neg", "algebra"),
    ("Inv", "algebra"),
    ("Sub", "algebra"),
    ("Div", "algebra"),
    ("Zero", "algebra"),
    ("One", "algebra"),
    ("Monoid", "algebra"),
    ("Group", "algebra"),
    ("Ring", "algebra"),
    ("Field", "algebra"),
    ("CommMonoid", "algebra"),
    ("CommGroup", "algebra"),
    ("CommRing", "algebra"),
    ("Semiring", "algebra"),
    ("CommSemiring", "algebra"),
    ("Module", "algebra"),
    ("Algebra", "algebra"),
    ("Subgroup", "algebra"),
    ("Subring", "algebra"),
    ("Ideal", "algebra"),
    ("Polynomial", "algebra"),
    ("MvPolynomial", "algebra"),
    ("PowerSeries", "algebra"),
    ("FreeGroup", "algebra"),
    ("FreeAlgebra", "algebra"),
    ("QuotientGroup", "algebra"),
    ("Matrix", "algebra"),
    ("LinearMap", "algebra"),
    ("BilinForm", "algebra"),
    ("TensorProduct", "algebra"),
    # Equivalences
    ("Equiv", "equivalence"),
    ("Iso", "equivalence"),
    ("MulEquiv", "equivalence"),
    ("AddEquiv", "equivalence"),
    ("RingEquiv", "equivalence"),
    ("OrderIso", "equivalence"),
    # Categorical
    ("Functor", "categorical"),
    ("Monad", "categorical"),
    ("Applicative", "categorical"),
    ("NatTrans", "categorical"),
    ("CategoryTheory", "categorical"),
    ("Adjunction", "categorical"),
    # Topology
    ("TopologicalSpace", "topology"),
    ("Continuous", "topology"),
    ("Homeomorph", "topology"),
    ("IsOpen", "topology"),
    ("IsClosed", "topology"),
    ("Compact", "topology"),
    ("Connected", "topology"),
    ("Metric", "topology"),
    # Combinatorics
    ("Combinatorics", "combinatorics"),
    ("SimpleGraph", "combinatorics"),
    ("Walk", "combinatorics"),
    # Number theory
    ("NumberTheory", "number_theory"),
    ("ZMod", "number_theory"),
    ("Zsqrtd", "number_theory"),
    ("GaussInt", "number_theory"),
    ("Padic", "number_theory"),
    ("Prime", "number_theory"),
    # Set theory
    ("Cardinal", "set_theory"),
    ("Ordinal", "set_theory"),
    ("SetTheory", "set_theory"),
    # Analysis
    ("Analysis", "analysis"),
    ("NNReal", "analysis"),
    ("ENNReal", "analysis"),
    ("Norm", "analysis"),
    ("Deriv", "analysis"),
    ("HasDerivAt", "analysis"),
    ("Integrable", "analysis"),
    ("MeasureTheory", "analysis"),
]

# Subcategory keywords
_SUBCAT_KEYWORDS: Dict[str, List[str]] = {
    "map": ["map", "Map"],
    "filter": ["filter", "Filter"],
    "fold": ["fold", "Fold", "foldl", "foldr"],
    "sort": ["sort", "Sort", "merge", "Merge", "perm", "Perm", "Sorted"],
    "zip": ["zip", "Zip", "zipWith"],
    "append": ["append", "Append", "concat", "Concat"],
    "reverse": ["reverse", "Reverse"],
    "length": ["length", "Length", "count", "Count", "card", "Card"],
    "take_drop": ["take", "Take", "drop", "Drop", "slice"],
    "get": ["get", "Get", "nth", "Nth", "index", "head", "tail", "last"],
    "nil_cons": ["nil", "Nil", "cons", "Cons", "empty", "Empty", "singleton"],
    "comm": ["comm", "Comm"],
    "assoc": ["assoc", "Assoc"],
    "distrib": ["distrib", "Distrib"],
    "zero_one": ["zero", "Zero", "one", "One"],
    "neg_inv": ["neg", "Neg", "inv", "Inv", "sub", "Sub"],
    "succ_pred": ["succ", "Succ", "pred", "Pred"],
    "div_mod": ["div", "Div", "mod", "Mod"],
    "comp": ["comp", "Comp", "compose"],
    "id": ["id", "Id", "identity"],
    "inj_surj": ["inj", "Inj", "surj", "Surj", "bij", "Bij"],
    "mem": ["mem", "Mem", "elem", "contains"],
    "union_inter": ["union", "Union", "inter", "Inter", "sdiff"],
    "subset": ["subset", "Subset", "superset", "Superset"],
    "not_and_or": ["not", "Not", "and", "And", "or", "Or"],
    "iff": ["iff", "Iff"],
    "exists_forall": ["exists", "Exists", "forall", "Forall"],
    "le_lt": ["le", "Le", "lt", "Lt", "ge", "Ge", "gt", "Gt"],
    "max_min": ["max", "Max", "min", "Min", "sup", "Sup", "inf", "Inf"],
    "order": ["monotone", "Monotone", "antitone", "Antitone", "strictMono"],
    "cast": ["cast", "Cast", "coe", "Coe", "lift", "Lift"],
    "equiv": ["equiv", "Equiv", "iso", "Iso"],
    "pow": ["pow", "Pow", "npow", "zpow"],
    "abs": ["abs", "Abs", "nonneg", "Nonneg"],
    "sum_prod": ["sum", "Sum", "prod", "Prod"],
    "range": ["range", "Range", "Icc", "Ico", "Ioc", "Ioo"],
}


def _classify_category(name: str, namespace: str, file_path: str) -> str:
    """Determine category from fully-qualified name, namespace, or file path."""
    # Check namespace first
    for prefix, cat in _CATEGORY_RULES:
        if namespace.startswith(prefix) or namespace.startswith(f"_{prefix}"):
            return cat
    # Check name
    parts = name.split(".")
    for part in parts:
        for prefix, cat in _CATEGORY_RULES:
            if part.startswith(prefix):
                return cat
    # Check file path
    fp = file_path.replace("\\", "/")
    if "/Data/List/" in fp:
        return "list"
    if "/Data/Array/" in fp:
        return "array"
    if "/Data/String/" in fp:
        return "string"
    if "/Data/Nat/" in fp or "/Data/Int/" in fp:
        return "arithmetic"
    if "/Data/Bool/" in fp:
        return "boolean"
    if "/Data/Option/" in fp:
        return "option"
    if "/Data/Prod/" in fp or "/Data/Sigma/" in fp:
        return "product"
    if "/Data/Fin/" in fp or "/Data/Finset/" in fp:
        return "finset"
    if "/Data/Multiset/" in fp:
        return "multiset"
    if "/Data/Set/" in fp:
        return "set"
    if "/Logic/" in fp:
        return "logic"
    if "/Order/" in fp:
        return "order"
    if "/Algebra/" in fp or "/GroupTheory/" in fp or "/RingTheory/" in fp:
        return "algebra"
    if "/CategoryTheory/" in fp:
        return "categorical"
    if "/Topology/" in fp:
        return "topology"
    if "/Analysis/" in fp or "/MeasureTheory/" in fp:
        return "analysis"
    if "/Combinatorics/" in fp:
        return "combinatorics"
    if "/NumberTheory/" in fp:
        return "number_theory"
    if "/SetTheory/" in fp:
        return "set_theory"
    if "/LinearAlgebra/" in fp:
        return "algebra"
    if "/Data/Equiv/" in fp:
        return "equivalence"
    if "/Tactic/" in fp:
        return "tactic"
    if "/Control/" in fp:
        return "categorical"
    return "other"


def _classify_subcategory(name: str, proposition: str) -> str:
    """Determine subcategory from the theorem name and proposition."""
    combined = name + " " + proposition
    best_score = 0
    best_subcat = "general"
    for subcat, keywords in _SUBCAT_KEYWORDS.items():
        score = sum(1 for kw in keywords if kw in combined)
        if score > best_score:
            best_score = score
            best_subcat = subcat
    return best_subcat


# ═══════════════════════════════════════════════════════════════════════════════
#  Lean theorem extraction (regex-based)
# ═══════════════════════════════════════════════════════════════════════════════

# Pattern to match theorem/lemma declarations
# This handles:
#   - optional attributes (@[simp], @[ext], etc.)
#   - optional modifiers (protected, private, noncomputable)
#   - theorem or lemma keyword
#   - name (possibly dotted)
#   - parameters (in {}, (), [])
#   - colon and proposition
#   - := or where or by
_ATTR_PATTERN = re.compile(r'@\[([^\]]*)\]')

# More robust line-by-line extraction approach
_DECL_START = re.compile(
    r'^(?:@\[.*?\]\s*\n?)*'
    r'(?:(?:protected|private)\s+)?'
    r'(?:noncomputable\s+)?'
    r'(theorem|lemma)\s+'
    r'([\w._]+)',
    re.MULTILINE
)


def _strip_comments(source: str) -> str:
    """Remove block comments /- ... -/ and line comments -- ... from source."""
    # First strip nested block comments
    result = []
    i = 0
    depth = 0
    while i < len(source):
        if i + 1 < len(source) and source[i:i+2] == '/-':
            depth += 1
            i += 2
            continue
        if depth > 0:
            if i + 1 < len(source) and source[i:i+2] == '-/':
                depth -= 1
                i += 2
                continue
            i += 1
            continue
        result.append(source[i])
        i += 1
    source = ''.join(result)

    # Strip line comments
    lines = source.split('\n')
    stripped = []
    for line in lines:
        # Find -- that isn't inside a string
        idx = line.find('--')
        if idx >= 0:
            # Simple heuristic: count quotes before --
            pre = line[:idx]
            if pre.count('"') % 2 == 0:
                line = pre
        stripped.append(line)
    return '\n'.join(stripped)


def _extract_attributes(text: str) -> List[str]:
    """Extract @[...] attributes from text preceding a declaration."""
    attrs = []
    for m in _ATTR_PATTERN.finditer(text):
        attr_text = m.group(1)
        # Split on commas for multiple attributes
        for a in attr_text.split(','):
            a = a.strip()
            if a:
                attrs.append(a)
    return attrs


def _find_matching_close(source: str, start: int, open_ch: str, close_ch: str) -> int:
    """Find matching close bracket, handling nesting."""
    depth = 1
    i = start
    while i < len(source) and depth > 0:
        if source[i] == open_ch:
            depth += 1
        elif source[i] == close_ch:
            depth -= 1
        i += 1
    return i


def _extract_params_and_type(source: str, pos: int) -> Tuple[str, str, int]:
    """Extract parameter block and proposition type starting from pos.

    Returns (params_text, proposition_text, end_pos).
    """
    params_parts = []
    i = pos

    # Skip whitespace
    while i < len(source) and source[i] in ' \t\n\r':
        i += 1

    # Consume parameter blocks: {}, (), []
    while i < len(source) and source[i] in '{([':
        open_ch = source[i]
        close_ch = {'{': '}', '(': ')', '[': ']'}[open_ch]
        start = i
        i = _find_matching_close(source, i + 1, open_ch, close_ch)
        params_parts.append(source[start:i])
        # Skip whitespace
        while i < len(source) and source[i] in ' \t\n\r':
            i += 1

    params_text = ' '.join(params_parts)

    # Expect ':'
    while i < len(source) and source[i] in ' \t\n\r':
        i += 1
    if i < len(source) and source[i] == ':':
        i += 1
    else:
        return params_text, "", i

    # Collect proposition until := or where
    prop_parts = []
    while i < len(source):
        # Check for := (end of proposition)
        if source[i:i+2] == ':=' and (i + 2 >= len(source) or source[i+2] != '='):
            break
        # Check for ' where' at start of line or preceded by whitespace
        if (source[i:i+5] == 'where' and
            (i == 0 or source[i-1] in ' \t\n') and
            (i + 5 >= len(source) or source[i+5] in ' \t\n')):
            break
        # Check for ' by ' or ' by\n' at end
        if (source[i:i+3] == ' by' and
            (i + 3 >= len(source) or source[i+3] in ' \t\n')):
            break
        if source[i:i+3] == '\nby' and (i + 3 >= len(source) or source[i+3] in ' \t\n'):
            break
        # Handle nested brackets in the proposition
        if source[i] in '({[':
            open_ch = source[i]
            close_ch = {'{': '}', '(': ')', '[': ']'}[open_ch]
            start = i
            i = _find_matching_close(source, i + 1, open_ch, close_ch)
            prop_parts.append(source[start:i])
            continue
        prop_parts.append(source[i])
        i += 1

    proposition = ''.join(prop_parts).strip()
    return params_text, proposition, i


def _extract_proof(source: str, pos: int, max_len: int = 500) -> Tuple[str, int]:
    """Extract proof text starting from pos. Truncate at max_len chars."""
    i = pos
    # Skip whitespace
    while i < len(source) and source[i] in ' \t\n\r':
        i += 1

    # After := or by
    if i < len(source) and source[i:i+2] == ':=':
        i += 2
    elif i < len(source) and source[i:i+2] == 'by':
        i += 2
    elif i < len(source) and source[i:i+5] == 'where':
        i += 5

    start = i
    # Heuristic: read until we hit another top-level declaration or end of file
    # Track bracket depth
    depth = 0
    while i < len(source):
        if source[i] in '({[':
            depth += 1
        elif source[i] in ')}]':
            depth -= 1
        # If depth is 0 and we see a new declaration keyword at start of line
        if depth <= 0 and i > start and source[i] == '\n':
            rest = source[i+1:i+50]
            rest_stripped = rest.lstrip()
            if any(rest_stripped.startswith(kw + ' ') or rest_stripped.startswith(kw + '\n')
                   for kw in ['theorem', 'lemma', 'def', 'instance', 'class',
                              'structure', 'inductive', 'abbrev', 'axiom',
                              'end', 'namespace', 'section', 'variable',
                              '#check', '#eval', '@[', 'open', 'noncomputable',
                              'protected theorem', 'protected lemma',
                              'protected def', 'private']):
                break
        if i - start > max_len:
            break
        i += 1

    proof = source[start:i].strip()
    if len(proof) > max_len:
        proof = proof[:max_len] + "..."
    return proof, i


def extract_theorems_from_file(
    file_path: str,
    mathlib_root: str,
) -> List[MathlibTheorem]:
    """Extract all theorem/lemma declarations from a single .lean file."""
    try:
        with open(file_path, 'r', encoding='utf-8', errors='replace') as f:
            raw_source = f.read()
    except (OSError, IOError):
        return []

    # Track relative path
    rel_path = os.path.relpath(file_path, mathlib_root)

    # Strip comments for parsing
    source = _strip_comments(raw_source)

    # Track namespaces
    current_namespaces: List[str] = []
    # Simple namespace tracking via scanning
    ns_open = re.compile(r'^namespace\s+([\w.]+)', re.MULTILINE)
    ns_close = re.compile(r'^end\s+([\w.]+)', re.MULTILINE)

    # Build a namespace map: position -> namespace stack
    # (simplified: just track which namespace we're in at each theorem position)
    ns_events: List[Tuple[int, str, bool]] = []  # (pos, name, is_open)
    for m in ns_open.finditer(source):
        ns_events.append((m.start(), m.group(1), True))
    for m in ns_close.finditer(source):
        ns_events.append((m.start(), m.group(1), False))
    ns_events.sort(key=lambda x: x[0])

    # Track variable declarations
    # (simplified: just note they exist)

    theorems: List[MathlibTheorem] = []

    # Find all theorem/lemma declarations
    for m in _DECL_START.finditer(source):
        kind = m.group(1)  # "theorem" or "lemma"
        name = m.group(2)
        decl_pos = m.start()
        after_name_pos = m.end()

        # Determine namespace at this position
        ns_stack: List[str] = []
        for ev_pos, ev_name, ev_open in ns_events:
            if ev_pos >= decl_pos:
                break
            if ev_open:
                ns_stack.append(ev_name)
            else:
                # Try to pop matching namespace
                if ns_stack and ns_stack[-1] == ev_name:
                    ns_stack.pop()
                elif ns_stack:
                    ns_stack.pop()

        namespace = '.'.join(ns_stack) if ns_stack else ""

        # Extract attributes from text before the declaration
        attr_region = source[max(0, decl_pos - 200):decl_pos]
        # Only look at the last few lines before the declaration
        attr_lines = attr_region.split('\n')[-5:]
        attr_text = '\n'.join(attr_lines)
        attributes = _extract_attributes(attr_text)

        is_simp = any('simp' in a for a in attributes)

        # Extract params and proposition
        params_text, proposition, end_pos = _extract_params_and_type(source, after_name_pos)

        # Extract proof (truncated)
        proof_text, _ = _extract_proof(source, end_pos)

        # Fully-qualify name
        full_name = f"{namespace}.{name}" if namespace else name
        # Handle _root_
        if name.startswith("_root_."):
            full_name = name[7:]  # strip _root_.

        # Classify
        category = _classify_category(full_name, namespace, rel_path)
        subcategory = _classify_subcategory(full_name, proposition)

        theorems.append(MathlibTheorem(
            name=full_name,
            file_path=rel_path,
            params=params_text,
            proposition=proposition,
            proof_text=proof_text,
            attributes=attributes,
            namespace=namespace,
            is_simp=is_simp,
            category=category,
            subcategory=subcategory,
            kind=kind,
        ))

    return theorems


# ═══════════════════════════════════════════════════════════════════════════════
#  Main: walk all .lean files and extract
# ═══════════════════════════════════════════════════════════════════════════════

def extract_all(
    mathlib_dir: str,
    output_path: Optional[str] = None,
    verbose: bool = True,
) -> Dict:
    """Walk ALL .lean files and extract every theorem/lemma.

    Returns a dict with keys: theorems (list of dicts), statistics.
    """
    mathlib_root = os.path.abspath(mathlib_dir)
    if not os.path.isdir(mathlib_root):
        print(f"ERROR: {mathlib_root} is not a directory", file=sys.stderr)
        sys.exit(1)

    # Collect all .lean files
    lean_files: List[str] = []
    for dirpath, _dirnames, filenames in os.walk(mathlib_root):
        for fn in filenames:
            if fn.endswith('.lean'):
                lean_files.append(os.path.join(dirpath, fn))

    lean_files.sort()
    total_files = len(lean_files)
    if verbose:
        print(f"Found {total_files} .lean files under {mathlib_root}")

    all_theorems: List[MathlibTheorem] = []
    files_processed = 0
    files_with_theorems = 0
    t0 = time.time()

    for i, fp in enumerate(lean_files):
        thms = extract_theorems_from_file(fp, mathlib_root)
        files_processed += 1
        if thms:
            files_with_theorems += 1
            all_theorems.extend(thms)
        if verbose and (i + 1) % 500 == 0:
            elapsed = time.time() - t0
            rate = (i + 1) / elapsed if elapsed > 0 else 0
            print(f"  [{i+1}/{total_files}] {len(all_theorems)} theorems, "
                  f"{rate:.0f} files/s")

    elapsed = time.time() - t0

    # Compute statistics
    cat_counts: Dict[str, int] = {}
    subcat_counts: Dict[str, int] = {}
    simp_count = 0
    kind_counts: Dict[str, int] = {"theorem": 0, "lemma": 0}
    for t in all_theorems:
        cat_counts[t.category] = cat_counts.get(t.category, 0) + 1
        subcat_counts[t.subcategory] = subcat_counts.get(t.subcategory, 0) + 1
        if t.is_simp:
            simp_count += 1
        kind_counts[t.kind] = kind_counts.get(t.kind, 0) + 1

    statistics = {
        "total_theorems": len(all_theorems),
        "total_files": total_files,
        "files_processed": files_processed,
        "files_with_theorems": files_with_theorems,
        "simp_lemmas": simp_count,
        "kind_counts": kind_counts,
        "category_counts": dict(sorted(cat_counts.items(), key=lambda x: -x[1])),
        "subcategory_counts": dict(sorted(
            subcat_counts.items(), key=lambda x: -x[1]
        )[:30]),  # top 30
        "extraction_time_seconds": round(elapsed, 1),
    }

    result = {
        "theorems": [t.to_dict() for t in all_theorems],
        "statistics": statistics,
    }

    if verbose:
        print(f"\n{'='*60}")
        print(f"Extraction complete in {elapsed:.1f}s")
        print(f"  Total .lean files:       {total_files}")
        print(f"  Files with theorems:     {files_with_theorems}")
        print(f"  Total theorems/lemmas:   {len(all_theorems)}")
        print(f"  @[simp] lemmas:          {simp_count}")
        print(f"\nCategory breakdown:")
        for cat, cnt in sorted(cat_counts.items(), key=lambda x: -x[1]):
            print(f"  {cat:25s} {cnt:>6d}")

    if output_path:
        os.makedirs(os.path.dirname(os.path.abspath(output_path)), exist_ok=True)
        with open(output_path, 'w') as f:
            json.dump(result, f, indent=1, ensure_ascii=False)
        if verbose:
            size_mb = os.path.getsize(output_path) / 1024 / 1024
            print(f"\nCatalog written to {output_path} ({size_mb:.1f} MB)")

    return result


# ═══════════════════════════════════════════════════════════════════════════════
#  CLI
# ═══════════════════════════════════════════════════════════════════════════════

def main():
    parser = argparse.ArgumentParser(
        description="Extract ALL theorems from Mathlib4"
    )
    parser.add_argument(
        "--mathlib-dir",
        default="/Users/halleyyoung/Documents/div/mathdivergence/mathlib4_full/Mathlib",
        help="Path to Mathlib source directory",
    )
    parser.add_argument(
        "--output",
        default=None,
        help="Output JSON file path",
    )
    args = parser.parse_args()

    if args.output is None:
        # Default output next to this script
        args.output = os.path.join(
            os.path.dirname(os.path.abspath(__file__)),
            "mathlib_full_catalog.json",
        )

    extract_all(args.mathlib_dir, args.output)


if __name__ == "__main__":
    main()
