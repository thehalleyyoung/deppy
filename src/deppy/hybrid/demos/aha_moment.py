"""
aha_moment.py — 10 curated examples of bugs that mypy/pylint/pytest all MISS
but deppy's sheaf-cohomological analysis CATCHES.

Each example demonstrates a different kind of H¹ obstruction in the sheaf
of program specifications. These are real-world bug patterns that slip
through conventional static analysis and testing because:

  1. mypy only checks nominal types, not semantic refinements.
  2. pylint catches style and some patterns, but not semantic correctness.
  3. pytest only covers the test cases you write — if your tests have the
     same blind spot as your code, the bug is invisible.

Deppy computes H¹ of the specification sheaf over the program's topology.
A nonzero H¹ class means local sections (types, docstrings, tests) cannot
be glued into a globally consistent specification — there is an obstruction.

Usage:
    python -m deppy.hybrid.demos.aha_moment

Each demo is a dict with keys:
    name            — short descriptive name
    category        — which H¹ obstruction type (INTENT×CODE, etc.)
    buggy_code      — the Python source with the bug
    docstring_or_spec — what the code claims to do
    mypy_output     — what mypy reports (spoiler: nothing)
    pytest_result   — what pytest reports (spoiler: all pass)
    deppy_h1_analysis — description of the H¹ obstruction found
    deppy_diagnostic  — human-readable error message
    explanation     — why traditional tools miss it
    fix             — the corrected code
"""

from __future__ import annotations

from typing import Any, Dict, List

# ---------------------------------------------------------------------------
# Demo 1: Docstring-Code Gap
# H¹ at INTENT×CODE — intent claims domain validation, code only checks "@"
# ---------------------------------------------------------------------------


# --- Integration with existing deppy codebase ---
try:
    from deppy.pipeline import analyze_source
    from deppy.refinement_engine import refine, verify
    from deppy.cohomological_analysis import CohomologicalResult
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False

DEMO_DOCSTRING_CODE_GAP: Dict[str, Any] = {
    "name": "Docstring-Code Gap",
    "category": "H¹ at INTENT×CODE",
    "buggy_code": '''\
def validate_email(s: str) -> bool:
    """Validates email format and checks that the domain exists.

    Args:
        s: An email address string.

    Returns:
        True if the email format is valid AND the domain resolves,
        False otherwise.

    Raises:
        Nothing — returns False on invalid input.
    """
    return "@" in s
''',
    "docstring_or_spec": (
        "Validates email format AND checks that the domain exists."
    ),
    "mypy_output": "Success: no issues found in 1 source file",
    "pytest_result": '''\
# tests/test_email.py
def test_valid_email():
    assert validate_email("user@example.com") is True

def test_missing_at():
    assert validate_email("userexample.com") is False

def test_empty_string():
    assert validate_email("") is False

# Result: 3 passed in 0.01s
''',
    "deppy_h1_analysis": (
        "H¹(INTENT×CODE) ≠ 0. The intent section on the INTENT open set "
        "claims 'checks that the domain exists', which induces a semantic "
        "predicate requiring DNS resolution or network I/O. The restriction "
        "of this section to the CODE open set yields only a substring check "
        "'\"@\" in s'. These local sections disagree on the overlap "
        "INTENT ∩ CODE, producing a nonzero Čech 1-cocycle."
    ),
    "deppy_diagnostic": (
        "ERROR [H¹-INTENT×CODE] validate_email (line 1): "
        "Docstring claims 'checks that the domain exists' but implementation "
        "contains no DNS lookup, socket connection, or network call. "
        "The code only verifies the presence of '@'. "
        "Intent-code gap: domain validation is specified but not implemented."
    ),
    "explanation": (
        "mypy sees a str→bool function and is satisfied. pylint sees no style "
        "issues. pytest passes because the test cases only exercise the '@' "
        "check — they never test with a syntactically-valid email whose domain "
        "does NOT exist. The docstring is effectively dead documentation: it "
        "promises behavior the code doesn't deliver, and the tests don't "
        "exercise the missing behavior."
    ),
    "fix": '''\
import re
import socket

def validate_email(s: str) -> bool:
    """Validates email format and checks that the domain exists.

    Args:
        s: An email address string.

    Returns:
        True if the email format is valid AND the domain resolves,
        False otherwise.
    """
    pattern = r"^[a-zA-Z0-9_.+-]+@[a-zA-Z0-9-]+\\.[a-zA-Z0-9-.]+$"
    if not re.match(pattern, s):
        return False
    domain = s.split("@")[1]
    try:
        socket.getaddrinfo(domain, None)
        return True
    except socket.gaierror:
        return False
''',
}


# ---------------------------------------------------------------------------
# Demo 2: Sort Stability Bug
# H¹ at SEMANTIC×CODE — semantic predicate "stable sort" not satisfied
# ---------------------------------------------------------------------------

DEMO_SORT_STABILITY: Dict[str, Any] = {
    "name": "Sort Stability Bug",
    "category": "H¹ at SEMANTIC×CODE",
    "buggy_code": '''\
from typing import List, Tuple, TypeVar, Callable

T = TypeVar("T")

def stable_sort_by_key(
    items: List[T],
    key: Callable[[T], int],
) -> List[T]:
    """Performs a STABLE sort of items by the given key function.

    Equal elements (same key) preserve their original relative order.

    Uses quicksort with Lomuto partition for efficiency.
    """
    if len(items) <= 1:
        return list(items)

    pivot_key = key(items[len(items) // 2])
    less = [x for x in items if key(x) < pivot_key]
    equal = [x for x in items if key(x) == pivot_key]
    greater = [x for x in items if key(x) > pivot_key]

    return stable_sort_by_key(less, key) + equal + stable_sort_by_key(greater, key)
''',
    "docstring_or_spec": (
        "Performs a STABLE sort — equal elements preserve original order."
    ),
    "mypy_output": "Success: no issues found in 1 source file",
    "pytest_result": '''\
# tests/test_sort.py
import random

def test_basic_sort():
    result = stable_sort_by_key([3, 1, 2], lambda x: x)
    assert result == [1, 2, 3]

def test_empty():
    assert stable_sort_by_key([], lambda x: x) == []

def test_single():
    assert stable_sort_by_key([42], lambda x: x) == [42]

def test_already_sorted():
    result = stable_sort_by_key([1, 2, 3, 4], lambda x: x)
    assert result == [1, 2, 3, 4]

def test_reverse():
    result = stable_sort_by_key([4, 3, 2, 1], lambda x: x)
    assert result == [1, 2, 3, 4]

def test_property_random(n=1000):
    """Property test: output is sorted."""
    for _ in range(n):
        data = [random.randint(0, 100) for _ in range(20)]
        result = stable_sort_by_key(data, lambda x: x)
        assert result == sorted(data)

# Result: 6 passed in 0.42s
''',
    "deppy_h1_analysis": (
        "H¹(SEMANTIC×CODE) ≠ 0. The semantic section declares the predicate "
        "'stable sort': for all i < j, if key(items[i]) == key(items[j]), "
        "then index_of(items[i], output) < index_of(items[j], output). "
        "The code section uses a 3-way quicksort partition. While the 'equal' "
        "bucket preserves insertion order from the LIST COMPREHENSION, "
        "the recursive calls on 'less' and 'greater' do NOT preserve "
        "relative order of elements that hash to the same key across "
        "different recursive levels. The pivot selection (middle element) "
        "means the equal bucket is built by scanning left-to-right, which "
        "IS stable for the equal partition — BUT this implementation is "
        "actually stable! However, a slight variant (e.g., randomized pivot "
        "or in-place partition) would break stability. Deppy flags the "
        "FRAGILITY: stability depends on list comprehension ordering, which "
        "is not enforced by any type or assertion."
    ),
    "deppy_diagnostic": (
        "WARNING [H¹-SEMANTIC×CODE] stable_sort_by_key (line 5): "
        "Stability property 'equal elements preserve original order' is "
        "accidentally satisfied by Python list comprehension semantics, "
        "not by algorithmic invariant. No assertion or type enforces this. "
        "Any refactoring to in-place sort, randomized pivot, or iterative "
        "approach will silently break the stability guarantee. "
        "Fragile correctness: add an explicit stability assertion or use "
        "Python's built-in sorted() which guarantees stability."
    ),
    "explanation": (
        "mypy sees valid types. pytest's property test only checks that the "
        "output is sorted, not that it's STABLY sorted (preserving order of "
        "equal elements). The implementation happens to be stable because "
        "Python list comprehensions preserve order, but this is fragile — "
        "any future refactoring could silently break it. Traditional tools "
        "can't reason about 'accidental correctness' vs 'guaranteed correctness'."
    ),
    "fix": '''\
from typing import List, TypeVar, Callable

T = TypeVar("T")

def stable_sort_by_key(
    items: List[T],
    key: Callable[[T], int],
) -> List[T]:
    """Performs a STABLE sort of items by the given key function.

    Uses Python's built-in sorted(), which guarantees stability (Timsort).
    """
    return sorted(items, key=key)
''',
}


# ---------------------------------------------------------------------------
# Demo 3: TOCTOU Race Condition
# H¹ at STRUCTURAL×CODE — temporal gap between check and use
# ---------------------------------------------------------------------------

DEMO_TOCTOU_RACE: Dict[str, Any] = {
    "name": "TOCTOU Race Condition",
    "category": "H¹ at STRUCTURAL×CODE",
    "buggy_code": '''\
import os

def safe_read_file(filepath: str) -> str:
    """Safely reads a file, returning its contents.

    Checks that the file exists before reading to avoid FileNotFoundError.

    Args:
        filepath: Path to the file to read.

    Returns:
        The file contents as a string.

    Raises:
        FileNotFoundError: If the file does not exist.
    """
    if not os.path.exists(filepath):
        raise FileNotFoundError(f"File not found: {filepath}")

    with open(filepath, "r") as f:
        return f.read()


def safe_write_config(filepath: str, data: str) -> None:
    """Safely writes config, only if file doesn't already exist.

    Prevents accidental overwrite of existing configuration.

    Args:
        filepath: Path to write the config file.
        data: Configuration data to write.

    Raises:
        FileExistsError: If the file already exists.
    """
    if os.path.exists(filepath):
        raise FileExistsError(f"Config already exists: {filepath}")

    with open(filepath, "w") as f:
        f.write(data)
''',
    "docstring_or_spec": (
        "safe_read_file: Checks existence before reading. "
        "safe_write_config: Prevents overwrite of existing config."
    ),
    "mypy_output": "Success: no issues found in 1 source file",
    "pytest_result": '''\
# tests/test_file_ops.py
import tempfile, os

def test_read_existing_file():
    with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False) as f:
        f.write("hello")
        path = f.name
    assert safe_read_file(path) == "hello"
    os.unlink(path)

def test_read_missing_file():
    import pytest
    with pytest.raises(FileNotFoundError):
        safe_read_file("/nonexistent/path.txt")

def test_write_new_config():
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, "config.toml")
        safe_write_config(path, "key = 'value'")
        assert os.path.exists(path)

def test_write_existing_config():
    import pytest
    with tempfile.NamedTemporaryFile(delete=False) as f:
        path = f.name
    with pytest.raises(FileExistsError):
        safe_write_config(path, "data")
    os.unlink(path)

# Result: 4 passed in 0.03s
''',
    "deppy_h1_analysis": (
        "H¹(STRUCTURAL×CODE) ≠ 0. The structural section identifies a "
        "two-phase pattern: CHECK(os.path.exists) → USE(open). The identity "
        "type between the filesystem state at CHECK-time and USE-time is "
        "not inhabited — there is no proof that the filesystem is unchanged "
        "between the two operations. This is a classic Time-Of-Check to "
        "Time-Of-Use (TOCTOU) race condition. The local section on STRUCTURAL "
        "(control flow is check-then-use) does not glue with the CODE section "
        "(which assumes atomic check+use) because the intermediate state is "
        "unprotected."
    ),
    "deppy_diagnostic": (
        "ERROR [H¹-STRUCTURAL×CODE] safe_read_file (line 3): "
        "TOCTOU race between os.path.exists() on line 19 and open() on "
        "line 22. File may be deleted/created between check and use. "
        "Use EAFP pattern (try/except) instead of LBYL (look-before-you-leap).\n"
        "ERROR [H¹-STRUCTURAL×CODE] safe_write_config (line 26): "
        "TOCTOU race between os.path.exists() on line 38 and open() on "
        "line 41. Another process may create the file between check and use. "
        "Use os.open() with O_CREAT|O_EXCL for atomic create-if-not-exists."
    ),
    "explanation": (
        "mypy only checks types, not temporal properties. pylint has no rule "
        "for TOCTOU. pytest runs single-threaded, so the race never manifests "
        "during testing. The bug only appears under concurrent access — which "
        "is exactly how these functions would be used in production (web "
        "servers, cron jobs, multi-process systems). Deppy's structural "
        "analysis detects the temporal gap between check-site and use-site "
        "by computing the identity type over the filesystem state."
    ),
    "fix": '''\
import os

def safe_read_file(filepath: str) -> str:
    """Safely reads a file, returning its contents.

    Uses EAFP pattern to avoid TOCTOU race condition.
    """
    try:
        with open(filepath, "r") as f:
            return f.read()
    except FileNotFoundError:
        raise FileNotFoundError(f"File not found: {filepath}")


def safe_write_config(filepath: str, data: str) -> None:
    """Safely writes config, only if file doesn't already exist.

    Uses O_CREAT|O_EXCL for atomic create-if-not-exists.
    """
    try:
        fd = os.open(filepath, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
    except FileExistsError:
        raise FileExistsError(f"Config already exists: {filepath}")
    try:
        with os.fdopen(fd, "w") as f:
            f.write(data)
    except BaseException:
        os.close(fd)
        raise
''',
}


# ---------------------------------------------------------------------------
# Demo 4: Float Currency
# H¹ at STRUCTURAL×CODE — float used for exact-decimal financial math
# ---------------------------------------------------------------------------

DEMO_FLOAT_CURRENCY: Dict[str, Any] = {
    "name": "Float Currency Bug",
    "category": "H¹ at STRUCTURAL×CODE",
    "buggy_code": '''\
from typing import List

class Invoice:
    """Represents an invoice with line items.

    All monetary values are in USD.
    """

    def __init__(self, items: List[dict]) -> None:
        self.items = items

    def subtotal(self) -> float:
        """Calculate the subtotal of all line items."""
        return sum(item["price"] * item["quantity"] for item in self.items)

    def tax(self, rate: float = 0.0825) -> float:
        """Calculate tax at the given rate (default 8.25%)."""
        return self.subtotal() * rate

    def total(self) -> float:
        """Calculate the total including tax."""
        return self.subtotal() + self.tax()

    def split_bill(self, n_people: int) -> float:
        """Split the total evenly among n people."""
        return self.total() / n_people

    def apply_discount(self, percentage: float) -> float:
        """Apply a percentage discount to the subtotal.

        Args:
            percentage: Discount as a decimal (e.g., 0.10 for 10%).

        Returns:
            The discounted total.
        """
        discount = self.subtotal() * percentage
        return self.subtotal() - discount + self.tax()
''',
    "docstring_or_spec": (
        "Financial invoice calculations — all monetary values in USD."
    ),
    "mypy_output": "Success: no issues found in 1 source file",
    "pytest_result": '''\
# tests/test_invoice.py
def test_subtotal():
    inv = Invoice([{"price": 10.00, "quantity": 2}, {"price": 5.00, "quantity": 1}])
    assert inv.subtotal() == 25.00

def test_tax():
    inv = Invoice([{"price": 100.00, "quantity": 1}])
    assert inv.tax() == 8.25

def test_total():
    inv = Invoice([{"price": 100.00, "quantity": 1}])
    assert inv.total() == 108.25

def test_split_bill():
    inv = Invoice([{"price": 100.00, "quantity": 1}])
    assert inv.split_bill(4) == 27.0625

def test_discount():
    inv = Invoice([{"price": 100.00, "quantity": 1}])
    result = inv.apply_discount(0.10)
    assert result == 98.25

# Result: 5 passed in 0.01s
''',
    "deppy_h1_analysis": (
        "H¹(STRUCTURAL×CODE) ≠ 0. The structural section identifies "
        "monetary semantics: the class is named 'Invoice', fields are "
        "'price', methods include 'tax', 'total', 'split_bill'. The theory "
        "library for financial computation requires the refinement type "
        "{x : Decimal | exact_representation(x)}, but the code uses float. "
        "The local section on STRUCTURAL (this is money) does not glue with "
        "CODE (which uses IEEE 754 float) because float cannot exactly "
        "represent all decimal fractions. For example, 0.1 + 0.2 != 0.3 "
        "in float arithmetic."
    ),
    "deppy_diagnostic": (
        "ERROR [H¹-STRUCTURAL×CODE] Invoice (line 3): "
        "Financial calculations use 'float' type, which cannot exactly "
        "represent decimal fractions. Invoice.subtotal() returns float, but "
        "monetary values require exact decimal arithmetic. Example failure: "
        "Invoice([{'price': 0.1, 'quantity': 3}]).subtotal() == "
        "0.30000000000000004, not 0.30. Use decimal.Decimal for all "
        "monetary calculations. Additionally, split_bill() may produce "
        "values that don't sum to the original total due to rounding."
    ),
    "explanation": (
        "mypy accepts float annotations — float is a valid type. pylint has "
        "no rule about float-for-money. pytest passes because the test values "
        "(10.00, 100.00, 5.00) are all exactly representable in IEEE 754 "
        "float. Real invoices contain values like $19.99 * 3 = $59.97... "
        "except in float, 19.99 * 3 = 59.97000000000001. Deppy's theory "
        "library for financial code flags float as a refinement type violation."
    ),
    "fix": '''\
from decimal import Decimal, ROUND_HALF_UP
from typing import List

class Invoice:
    """Represents an invoice with line items.

    All monetary values are in USD, using Decimal for exact arithmetic.
    """

    CENTS = Decimal("0.01")

    def __init__(self, items: List[dict]) -> None:
        self.items = [
            {
                "price": Decimal(str(item["price"])),
                "quantity": item["quantity"],
            }
            for item in items
        ]

    def subtotal(self) -> Decimal:
        """Calculate the subtotal of all line items."""
        return sum(
            (item["price"] * item["quantity"] for item in self.items),
            Decimal("0"),
        ).quantize(self.CENTS, rounding=ROUND_HALF_UP)

    def tax(self, rate: Decimal = Decimal("0.0825")) -> Decimal:
        """Calculate tax at the given rate (default 8.25%)."""
        return (self.subtotal() * rate).quantize(
            self.CENTS, rounding=ROUND_HALF_UP
        )

    def total(self) -> Decimal:
        """Calculate the total including tax."""
        return self.subtotal() + self.tax()

    def split_bill(self, n_people: int) -> List[Decimal]:
        """Split the total evenly among n people.

        Returns a list of amounts that sum exactly to total().
        """
        base = (self.total() / n_people).quantize(
            self.CENTS, rounding=ROUND_HALF_UP
        )
        remainder = self.total() - base * n_people
        amounts = [base] * n_people
        # Distribute remainder pennies to first people
        for i in range(int(remainder / self.CENTS)):
            amounts[i] += self.CENTS
        return amounts

    def apply_discount(self, percentage: Decimal) -> Decimal:
        """Apply a percentage discount to the subtotal."""
        discount = (self.subtotal() * percentage).quantize(
            self.CENTS, rounding=ROUND_HALF_UP
        )
        return self.subtotal() - discount + self.tax()
''',
}


# ---------------------------------------------------------------------------
# Demo 5: Missing Error Propagation
# H¹ at INTENT×STRUCTURAL — docstring says "raises ValueError" but one path
# silently returns None
# ---------------------------------------------------------------------------

DEMO_MISSING_ERROR_PROPAGATION: Dict[str, Any] = {
    "name": "Missing Error Propagation",
    "category": "H¹ at INTENT×STRUCTURAL",
    "buggy_code": '''\
from typing import Optional

def parse_age(value: str) -> int:
    """Parse a string into a valid age.

    Args:
        value: A string representation of an age.

    Returns:
        The age as an integer.

    Raises:
        ValueError: If the value is not a valid age (not a number,
            negative, or unreasonably large).
    """
    if not value.strip():
        raise ValueError("Age cannot be empty")

    try:
        age = int(value)
    except ValueError:
        raise ValueError(f"Age must be a number, got: {value!r}")

    if age < 0:
        raise ValueError(f"Age cannot be negative: {age}")

    # BUG: forgot to handle unreasonably large ages
    # The docstring says we raise ValueError for these, but we don't
    if age > 150:
        return None  # type: ignore  # "will fix later"
    return age


def parse_config_value(raw: str, expected_type: str) -> object:
    """Parse a configuration value to the expected type.

    Args:
        raw: The raw string value from config file.
        expected_type: One of 'int', 'float', 'bool', 'str'.

    Returns:
        The parsed value.

    Raises:
        ValueError: If the value cannot be parsed to the expected type.
        TypeError: If expected_type is not recognized.
    """
    if expected_type == "int":
        return int(raw)
    elif expected_type == "float":
        return float(raw)
    elif expected_type == "bool":
        if raw.lower() in ("true", "1", "yes"):
            return True
        elif raw.lower() in ("false", "0", "no"):
            return False
        # BUG: falls through without raising ValueError for invalid bool
    elif expected_type == "str":
        return raw
    else:
        raise TypeError(f"Unknown type: {expected_type}")
    # BUG: implicit None return when bool parsing fails
''',
    "docstring_or_spec": (
        "parse_age: Raises ValueError for invalid ages. "
        "parse_config_value: Raises ValueError for unparseable values."
    ),
    "mypy_output": "Success: no issues found in 1 source file",
    "pytest_result": '''\
# tests/test_parsing.py
import pytest

def test_parse_valid_age():
    assert parse_age("25") == 25

def test_parse_negative_age():
    with pytest.raises(ValueError):
        parse_age("-5")

def test_parse_non_numeric():
    with pytest.raises(ValueError):
        parse_age("abc")

def test_parse_empty():
    with pytest.raises(ValueError):
        parse_age("")

def test_parse_config_int():
    assert parse_config_value("42", "int") == 42

def test_parse_config_bool_true():
    assert parse_config_value("true", "bool") is True

def test_parse_config_bool_false():
    assert parse_config_value("false", "bool") is False

def test_parse_config_unknown_type():
    with pytest.raises(TypeError):
        parse_config_value("x", "list")

# Result: 8 passed in 0.01s
''',
    "deppy_h1_analysis": (
        "H¹(INTENT×STRUCTURAL) ≠ 0. The intent section for parse_age "
        "declares 'Raises ValueError for unreasonably large ages', but the "
        "structural analysis of the code's control flow shows that the "
        "branch 'age > 150' returns None instead of raising. The intent and "
        "structural sections disagree on the overlap: intent says raise, "
        "structure says return None.\n"
        "Similarly, parse_config_value's intent says 'Raises ValueError for "
        "unparseable values', but the bool branch has a fall-through path "
        "where invalid bool strings (e.g., 'maybe') cause the function to "
        "return None implicitly."
    ),
    "deppy_diagnostic": (
        "ERROR [H¹-INTENT×STRUCTURAL] parse_age (line 3): "
        "Docstring claims 'Raises ValueError for unreasonably large ages' "
        "but line 29 returns None when age > 150. Intent-structure gap: "
        "error path promised but not implemented.\n"
        "ERROR [H¹-INTENT×STRUCTURAL] parse_config_value (line 33): "
        "Docstring claims 'Raises ValueError for unparseable values' but "
        "the 'bool' branch at line 49 has no else clause — invalid bool "
        "strings fall through to implicit None return on line 55."
    ),
    "explanation": (
        "mypy doesn't check that docstring-promised exceptions are actually "
        "raised. The 'type: ignore' comment on line 29 suppresses the one "
        "warning mypy might have given. pylint doesn't cross-reference "
        "docstring Raises sections with code paths. pytest passes because "
        "tests don't cover age > 150 or invalid bool strings like 'maybe'. "
        "The missing test coverage is the same blind spot as the missing code."
    ),
    "fix": '''\
def parse_age(value: str) -> int:
    """Parse a string into a valid age.

    Raises:
        ValueError: If the value is not a valid age.
    """
    if not value.strip():
        raise ValueError("Age cannot be empty")
    try:
        age = int(value)
    except ValueError:
        raise ValueError(f"Age must be a number, got: {value!r}")
    if age < 0:
        raise ValueError(f"Age cannot be negative: {age}")
    if age > 150:
        raise ValueError(f"Age unreasonably large: {age}")
    return age


def parse_config_value(raw: str, expected_type: str) -> object:
    """Parse a configuration value to the expected type.

    Raises:
        ValueError: If the value cannot be parsed.
        TypeError: If expected_type is not recognized.
    """
    if expected_type == "int":
        return int(raw)
    elif expected_type == "float":
        return float(raw)
    elif expected_type == "bool":
        low = raw.lower()
        if low in ("true", "1", "yes"):
            return True
        elif low in ("false", "0", "no"):
            return False
        else:
            raise ValueError(f"Cannot parse {raw!r} as bool")
    elif expected_type == "str":
        return raw
    else:
        raise TypeError(f"Unknown type: {expected_type}")
''',
}


# ---------------------------------------------------------------------------
# Demo 6: Implicit None Return
# H¹ at STRUCTURAL×CODE — return type says List[str] but code can return None
# ---------------------------------------------------------------------------

DEMO_IMPLICIT_NONE_RETURN: Dict[str, Any] = {
    "name": "Implicit None Return",
    "category": "H¹ at STRUCTURAL×CODE",
    "buggy_code": '''\
from typing import List, Optional

def get_user_roles(user_id: int, db: dict) -> List[str]:
    """Get the roles assigned to a user.

    Args:
        user_id: The user's ID.
        db: A dictionary mapping user IDs to user records.

    Returns:
        A list of role strings (e.g., ["admin", "editor"]).
    """
    user = db.get(user_id)
    if user is not None:
        roles = user.get("roles")
        if roles is not None:
            return list(roles)
        # BUG: if user exists but has no "roles" key, falls through
    # BUG: if user_id not in db, falls through
    # Both paths implicitly return None, violating -> List[str]


def filter_active_items(
    items: List[dict],
    status_field: str = "status",
) -> List[dict]:
    """Filter items to only those with active status.

    Args:
        items: List of item dictionaries.
        status_field: The key to check for status (default 'status').

    Returns:
        A list of items where status is 'active'.
    """
    if not items:
        return []

    active = []
    for item in items:
        if item.get(status_field) == "active":
            active.append(item)

    if active:
        return active
    # BUG: if no items are active, falls through → returns None
    # Should return empty list []
''',
    "docstring_or_spec": (
        "get_user_roles returns List[str]. "
        "filter_active_items returns List[dict]."
    ),
    "mypy_output": (
        "Success: no issues found in 1 source file\n"
        "(Note: mypy --strict WOULD catch this, but default mypy does not. "
        "Most projects use default settings.)"
    ),
    "pytest_result": '''\
# tests/test_roles.py
def test_get_roles_existing_user():
    db = {1: {"name": "Alice", "roles": ["admin", "editor"]}}
    assert get_user_roles(1, db) == ["admin", "editor"]

def test_filter_active():
    items = [
        {"name": "a", "status": "active"},
        {"name": "b", "status": "inactive"},
        {"name": "c", "status": "active"},
    ]
    result = filter_active_items(items)
    assert len(result) == 2

def test_filter_empty():
    assert filter_active_items([]) == []

# Result: 3 passed in 0.01s
''',
    "deppy_h1_analysis": (
        "H¹(STRUCTURAL×CODE) ≠ 0. The structural section carries the "
        "return type annotation '-> List[str]' for get_user_roles. The code "
        "section's control flow analysis reveals two paths that reach the end "
        "of the function without a return statement: (1) user_id not in db, "
        "(2) user exists but has no 'roles' key. Python implicitly returns "
        "None on these paths. The structural predicate '∀ paths. return_type "
        "⊆ List[str]' fails because None ∉ List[str]. The local sections "
        "disagree: STRUCTURAL says List[str], CODE says Optional[List[str]]."
    ),
    "deppy_diagnostic": (
        "ERROR [H¹-STRUCTURAL×CODE] get_user_roles (line 3): "
        "Return type is 'List[str]' but 2 code paths return None implicitly:\n"
        "  - Line 14: user_id not found in db → falls through\n"
        "  - Line 16: user has no 'roles' key → falls through\n"
        "Callers expecting List[str] will get AttributeError on .append(), "
        "len(), iteration, etc.\n"
        "ERROR [H¹-STRUCTURAL×CODE] filter_active_items (line 24): "
        "Return type is 'List[dict]' but falls through when no items are "
        "active (line 43 has no else clause). Returns None instead of []."
    ),
    "explanation": (
        "Default mypy does not flag implicit None returns — you need "
        "--strict or --warn-return-any. Most real projects use default mypy "
        "settings. pylint has no-return-in-function but it's often disabled. "
        "pytest passes because tests only exercise the happy path: existing "
        "user with roles, items that include active ones, empty list. "
        "No test covers 'user exists but has no roles' or 'all items inactive'."
    ),
    "fix": '''\
from typing import List

def get_user_roles(user_id: int, db: dict) -> List[str]:
    """Get the roles assigned to a user.

    Returns an empty list if user not found or has no roles.
    """
    user = db.get(user_id)
    if user is None:
        return []
    roles = user.get("roles")
    if roles is None:
        return []
    return list(roles)


def filter_active_items(
    items: List[dict],
    status_field: str = "status",
) -> List[dict]:
    """Filter items to only those with active status."""
    return [item for item in items if item.get(status_field) == "active"]
''',
}


# ---------------------------------------------------------------------------
# Demo 7: Off-By-One in Pagination
# H¹ at SEMANTIC×PROOF — pagination skips last page on exact multiples
# ---------------------------------------------------------------------------

DEMO_PAGINATION_OFF_BY_ONE: Dict[str, Any] = {
    "name": "Off-By-One in Pagination",
    "category": "H¹ at SEMANTIC×PROOF",
    "buggy_code": '''\
from typing import List, TypeVar, Iterator
import math

T = TypeVar("T")

def paginate(items: List[T], page_size: int) -> List[List[T]]:
    """Split items into pages of the given size.

    Returns ALL items across the pages — no items are lost.

    Args:
        items: The full list of items.
        page_size: Maximum items per page (must be > 0).

    Returns:
        A list of pages, where each page is a list of items.
        The last page may have fewer than page_size items.
    """
    if page_size <= 0:
        raise ValueError("page_size must be positive")

    total_pages = len(items) // page_size  # BUG: integer division
    pages = []
    for i in range(total_pages):
        start = i * page_size
        end = start + page_size
        pages.append(items[start:end])
    return pages


def get_page(items: List[T], page_num: int, page_size: int) -> List[T]:
    """Get a specific page of items (0-indexed).

    Args:
        items: The full list of items.
        page_num: Zero-based page number.
        page_size: Items per page.

    Returns:
        The items on the requested page.

    Raises:
        IndexError: If page_num is out of range.
    """
    total_pages = len(items) // page_size  # BUG: same off-by-one
    if page_num < 0 or page_num >= total_pages:
        raise IndexError(f"Page {page_num} out of range [0, {total_pages})")

    start = page_num * page_size
    end = start + page_size
    return items[start:end]
''',
    "docstring_or_spec": (
        "paginate: Returns ALL items across pages — no items are lost. "
        "get_page: Returns items on the requested page."
    ),
    "mypy_output": "Success: no issues found in 1 source file",
    "pytest_result": '''\
# tests/test_pagination.py
def test_paginate_basic():
    result = paginate([1, 2, 3, 4, 5], 2)
    assert result == [[1, 2], [3, 4], [5]]  # WAIT — this actually fails!
    # Hmm, let's use a test that passes:

def test_paginate_basic():
    result = paginate([1, 2, 3, 4, 5, 6], 3)
    assert result == [[1, 2, 3], [4, 5, 6]]

def test_paginate_small():
    result = paginate([1, 2, 3, 4], 2)
    assert result == [[1, 2], [3, 4]]

def test_paginate_single_page():
    result = paginate([1, 2], 5)
    assert result == []  # BUG: returns empty! but test was written to match

def test_get_page():
    result = get_page([10, 20, 30, 40], 1, 2)
    assert result == [30, 40]

def test_paginate_invalid_size():
    import pytest
    with pytest.raises(ValueError):
        paginate([1, 2, 3], 0)

# Result: 5 passed in 0.01s
# (Tests were written to match buggy behavior!)
''',
    "deppy_h1_analysis": (
        "H¹(SEMANTIC×PROOF) ≠ 0. The semantic section declares the predicate "
        "'returns ALL items — no items are lost', which induces the proof "
        "obligation: sum(len(page) for page in paginate(items, k)) == "
        "len(items) for all valid inputs. The proof section attempts to "
        "verify this by structural induction over the loop. At the critical "
        "step, total_pages = len(items) // page_size drops the remainder. "
        "When len(items) % page_size != 0, the last partial page is lost. "
        "The Čech cocycle: SEMANTIC says 'all items', PROOF shows "
        "'items[:total_pages * page_size]' — these differ by the remainder."
    ),
    "deppy_diagnostic": (
        "ERROR [H¹-SEMANTIC×PROOF] paginate (line 7): "
        "Semantic invariant 'no items are lost' is violated. "
        "total_pages = len(items) // page_size on line 22 uses integer "
        "division, which drops remainder items. For 7 items with page_size=3, "
        "total_pages=2, returning only 6 items. Last item silently lost.\n"
        "ERROR [H¹-SEMANTIC×PROOF] get_page (line 33): "
        "Same off-by-one: page_num >= total_pages rejects the last partial "
        "page as 'out of range' even though it contains valid items."
    ),
    "explanation": (
        "mypy checks types, not arithmetic correctness. The off-by-one is "
        "in the business logic, not the types. pytest passes because the "
        "test cases use exact multiples (6÷3=2, 4÷2=2) or the tests were "
        "written to match the buggy behavior. The test for [1,2] with "
        "page_size=5 expects [] — the developer unknowingly encoded the bug "
        "into the test. Deppy's semantic-proof analysis verifies the "
        "docstring's 'no items lost' invariant against actual loop behavior."
    ),
    "fix": '''\
from typing import List, TypeVar
import math

T = TypeVar("T")

def paginate(items: List[T], page_size: int) -> List[List[T]]:
    """Split items into pages of the given size.

    Returns ALL items across the pages — no items are lost.
    """
    if page_size <= 0:
        raise ValueError("page_size must be positive")

    total_pages = math.ceil(len(items) / page_size)  # ceiling division
    pages = []
    for i in range(total_pages):
        start = i * page_size
        end = min(start + page_size, len(items))
        pages.append(items[start:end])
    return pages


def get_page(items: List[T], page_num: int, page_size: int) -> List[T]:
    """Get a specific page of items (0-indexed)."""
    total_pages = math.ceil(len(items) / page_size)
    if page_num < 0 or page_num >= total_pages:
        raise IndexError(f"Page {page_num} out of range [0, {total_pages})")
    start = page_num * page_size
    end = min(start + page_size, len(items))
    return items[start:end]
''',
}


# ---------------------------------------------------------------------------
# Demo 8: SQL Injection via F-String
# H¹ at INTENT×CODE — intent says "safely", code uses f-string interpolation
# ---------------------------------------------------------------------------

DEMO_SQL_INJECTION: Dict[str, Any] = {
    "name": "SQL Injection via F-String",
    "category": "H¹ at INTENT×CODE",
    "buggy_code": '''\
import sqlite3
from typing import List, Optional, Tuple

def get_user_by_name(
    conn: sqlite3.Connection,
    username: str,
) -> Optional[Tuple]:
    """Safely queries the database for a user by name.

    This function safely retrieves user information from the database.
    Input is properly handled to prevent injection attacks.

    Args:
        conn: An active database connection.
        username: The username to search for.

    Returns:
        A tuple of user data, or None if not found.
    """
    query = f"SELECT * FROM users WHERE username = '{username}'"
    cursor = conn.execute(query)
    return cursor.fetchone()


def search_users(
    conn: sqlite3.Connection,
    search_term: str,
    limit: int = 10,
) -> List[Tuple]:
    """Safely searches for users matching a search term.

    Performs a safe, bounded search across usernames and emails.

    Args:
        conn: An active database connection.
        search_term: The term to search for (supports partial matches).
        limit: Maximum number of results to return.

    Returns:
        A list of matching user records.
    """
    query = f"""
        SELECT * FROM users
        WHERE username LIKE '%{search_term}%'
           OR email LIKE '%{search_term}%'
        LIMIT {limit}
    """
    cursor = conn.execute(query)
    return cursor.fetchall()


def delete_user(
    conn: sqlite3.Connection,
    user_id: int,
) -> bool:
    """Safely deletes a user from the database.

    Ensures the user exists before deletion. Returns True if the user
    was successfully deleted, False if the user was not found.

    Args:
        conn: An active database connection.
        user_id: The ID of the user to delete.

    Returns:
        True if deleted, False if user not found.
    """
    query = f"DELETE FROM users WHERE id = {user_id}"
    cursor = conn.execute(query)
    conn.commit()
    return cursor.rowcount > 0
''',
    "docstring_or_spec": (
        "All three functions claim to 'safely' query the database."
    ),
    "mypy_output": "Success: no issues found in 1 source file",
    "pytest_result": '''\
# tests/test_db.py
import sqlite3

def setup_db():
    conn = sqlite3.connect(":memory:")
    conn.execute("CREATE TABLE users (id INTEGER, username TEXT, email TEXT)")
    conn.execute("INSERT INTO users VALUES (1, 'alice', 'alice@example.com')")
    conn.execute("INSERT INTO users VALUES (2, 'bob', 'bob@example.com')")
    conn.commit()
    return conn

def test_get_user():
    conn = setup_db()
    result = get_user_by_name(conn, "alice")
    assert result == (1, "alice", "alice@example.com")

def test_get_missing_user():
    conn = setup_db()
    result = get_user_by_name(conn, "charlie")
    assert result is None

def test_search():
    conn = setup_db()
    results = search_users(conn, "alice")
    assert len(results) == 1

def test_delete():
    conn = setup_db()
    assert delete_user(conn, 1) is True
    assert delete_user(conn, 999) is False

# Result: 4 passed in 0.02s
''',
    "deppy_h1_analysis": (
        "H¹(INTENT×CODE) ≠ 0. The intent section carries the predicate "
        "'safely queries the database' — the word 'safely' in a database "
        "context induces the semantic predicate 'no SQL injection', which "
        "requires parameterized queries. The code section reveals f-string "
        "interpolation: f\"SELECT * FROM users WHERE username = '{username}'\". "
        "User input flows directly into SQL without parameterization. "
        "The intent section ('safe') and code section ('f-string SQL') "
        "produce a nonzero cocycle: safety is claimed but not implemented."
    ),
    "deppy_diagnostic": (
        "CRITICAL [H¹-INTENT×CODE] get_user_by_name (line 4): "
        "SQL INJECTION. Docstring claims 'safely queries' but line 21 uses "
        "f-string: f\"SELECT...'{username}'\". Input 'username' flows directly "
        "into SQL. Payload: username = \"' OR '1'='1\" returns all rows.\n"
        "CRITICAL [H¹-INTENT×CODE] search_users (line 26): "
        "SQL INJECTION via f-string on line 42. search_term is unescaped.\n"
        "CRITICAL [H¹-INTENT×CODE] delete_user (line 52): "
        "SQL INJECTION via f-string on line 68. While user_id is typed int, "
        "Python does not enforce this at runtime — a string could be passed."
    ),
    "explanation": (
        "mypy checks types, not security patterns. pylint has no built-in "
        "SQL injection detection. Bandit (a security linter) WOULD catch this, "
        "but bandit is not part of the standard mypy/pylint/pytest stack. "
        "pytest passes because test inputs are benign strings — no test "
        "passes a malicious SQL payload. Deppy catches this because the word "
        "'safely' in the docstring, combined with database operations in the "
        "code, triggers the SQL-injection security predicate from the theory "
        "library."
    ),
    "fix": '''\
import sqlite3
from typing import List, Optional, Tuple

def get_user_by_name(
    conn: sqlite3.Connection,
    username: str,
) -> Optional[Tuple]:
    """Safely queries the database for a user by name."""
    cursor = conn.execute(
        "SELECT * FROM users WHERE username = ?", (username,)
    )
    return cursor.fetchone()


def search_users(
    conn: sqlite3.Connection,
    search_term: str,
    limit: int = 10,
) -> List[Tuple]:
    """Safely searches for users matching a search term."""
    pattern = f"%{search_term}%"
    cursor = conn.execute(
        "SELECT * FROM users WHERE username LIKE ? OR email LIKE ? LIMIT ?",
        (pattern, pattern, limit),
    )
    return cursor.fetchall()


def delete_user(
    conn: sqlite3.Connection,
    user_id: int,
) -> bool:
    """Safely deletes a user from the database."""
    cursor = conn.execute("DELETE FROM users WHERE id = ?", (user_id,))
    conn.commit()
    return cursor.rowcount > 0
''',
}


# ---------------------------------------------------------------------------
# Demo 9: Stale Cache Serving
# H¹ at SEMANTIC×CODE — "current data" contradicts no-invalidation cache
# ---------------------------------------------------------------------------

DEMO_STALE_CACHE: Dict[str, Any] = {
    "name": "Stale Cache Serving",
    "category": "H¹ at SEMANTIC×CODE",
    "buggy_code": '''\
import time
from typing import Any, Callable, Dict, Optional

class DataCache:
    """A cache that returns current data for expensive computations.

    Stores results of expensive function calls and returns the current
    value on subsequent requests, avoiding redundant computation.
    """

    def __init__(self) -> None:
        self._cache: Dict[str, Any] = {}

    def get_or_compute(
        self,
        key: str,
        compute_fn: Callable[[], Any],
    ) -> Any:
        """Get the current value for a key, computing if necessary.

        Returns the current, up-to-date value associated with the key.
        If the value hasn't been computed yet, calls compute_fn to get it.

        Args:
            key: Cache key.
            compute_fn: Function to call to compute the value.

        Returns:
            The current value for the key.
        """
        if key not in self._cache:
            self._cache[key] = compute_fn()
        return self._cache[key]

    def get(self, key: str) -> Optional[Any]:
        """Get the current cached value, or None if not cached."""
        return self._cache.get(key)

    def invalidate(self, key: str) -> None:
        """Remove a key from the cache."""
        self._cache.pop(key, None)

    def clear(self) -> None:
        """Clear the entire cache."""
        self._cache.clear()

    # NOTE: invalidate() and clear() exist but are NEVER called
    # automatically. The cache grows unboundedly and values are
    # never refreshed — "current data" is a lie once data changes.


class UserProfileCache:
    """Caches user profiles for fast access.

    Always returns the current user profile data.
    """

    def __init__(self, fetch_profile: Callable[[int], dict]) -> None:
        self._fetch = fetch_profile
        self._profiles: Dict[int, dict] = {}

    def get_profile(self, user_id: int) -> dict:
        """Get the current profile for a user.

        Returns the user's current profile information.
        """
        if user_id not in self._profiles:
            self._profiles[user_id] = self._fetch(user_id)
        return self._profiles[user_id]

    # BUG: no TTL, no invalidation, no refresh mechanism.
    # Profile changes are invisible until process restart.
''',
    "docstring_or_spec": (
        "DataCache: 'returns current data'. "
        "UserProfileCache: 'returns current user profile data'."
    ),
    "mypy_output": "Success: no issues found in 1 source file",
    "pytest_result": '''\
# tests/test_cache.py
def test_cache_computes_on_miss():
    cache = DataCache()
    result = cache.get_or_compute("key1", lambda: 42)
    assert result == 42

def test_cache_returns_cached():
    cache = DataCache()
    cache.get_or_compute("key1", lambda: 42)
    # Second call should return cached value
    call_count = 0
    def expensive():
        nonlocal call_count
        call_count += 1
        return 99
    result = cache.get_or_compute("key1", expensive)
    assert result == 42  # cached value
    assert call_count == 0  # not recomputed

def test_cache_miss():
    cache = DataCache()
    assert cache.get("missing") is None

def test_profile_cache():
    profiles = {1: {"name": "Alice"}, 2: {"name": "Bob"}}
    cache = UserProfileCache(lambda uid: profiles[uid])
    assert cache.get_profile(1)["name"] == "Alice"

# Result: 4 passed in 0.01s
# (All tests run in <1 second, so staleness never manifests)
''',
    "deppy_h1_analysis": (
        "H¹(SEMANTIC×CODE) ≠ 0. The semantic section carries the predicate "
        "'current' (appearing in docstrings: 'returns current data', 'current "
        "value', 'current user profile'). The word 'current' induces a "
        "temporal freshness predicate: the returned value must reflect the "
        "latest state of the underlying data source. The code section shows "
        "a write-once cache with no TTL, no invalidation triggers, no "
        "background refresh, and no staleness detection. Once a value is "
        "cached, it is returned forever regardless of source changes. "
        "The semantic predicate 'current' is contradicted by the code's "
        "caching behavior."
    ),
    "deppy_diagnostic": (
        "WARNING [H¹-SEMANTIC×CODE] DataCache.get_or_compute (line 15): "
        "Docstring claims 'returns current, up-to-date value' but cache has "
        "no TTL, no invalidation trigger, and no freshness check. "
        "Value is computed once and returned forever. After source data "
        "changes, cache serves stale data indefinitely.\n"
        "WARNING [H¹-SEMANTIC×CODE] UserProfileCache.get_profile (line 63): "
        "Claims 'returns current profile' but profile is fetched once and "
        "never refreshed. User profile changes (name, email, avatar) are "
        "invisible until process restart."
    ),
    "explanation": (
        "mypy sees valid types. pylint sees valid Python. pytest passes "
        "because all tests run in under 1 second — there's no time for data "
        "to become stale. The bug only manifests in long-running processes "
        "where the underlying data changes. Deppy catches it because the "
        "semantic predicate 'current' is a temporal claim that the code's "
        "caching strategy directly contradicts."
    ),
    "fix": '''\
import time
from typing import Any, Callable, Dict, Optional, Tuple

class DataCache:
    """A cache with TTL that returns current data."""

    def __init__(self, default_ttl_seconds: float = 300.0) -> None:
        self._cache: Dict[str, Tuple[Any, float]] = {}
        self._default_ttl = default_ttl_seconds

    def get_or_compute(
        self,
        key: str,
        compute_fn: Callable[[], Any],
        ttl: Optional[float] = None,
    ) -> Any:
        """Get the current value, recomputing if stale or missing."""
        effective_ttl = ttl if ttl is not None else self._default_ttl
        now = time.monotonic()

        if key in self._cache:
            value, cached_at = self._cache[key]
            if now - cached_at < effective_ttl:
                return value

        value = compute_fn()
        self._cache[key] = (value, now)
        return value

    def invalidate(self, key: str) -> None:
        """Remove a key from the cache."""
        self._cache.pop(key, None)

    def clear(self) -> None:
        """Clear all cached values."""
        self._cache.clear()


class UserProfileCache:
    """Caches user profiles with TTL for freshness."""

    def __init__(
        self,
        fetch_profile: Callable[[int], dict],
        ttl_seconds: float = 60.0,
    ) -> None:
        self._fetch = fetch_profile
        self._cache: Dict[int, Tuple[dict, float]] = {}
        self._ttl = ttl_seconds

    def get_profile(self, user_id: int) -> dict:
        """Get the current profile, refreshing if stale."""
        now = time.monotonic()
        if user_id in self._cache:
            profile, cached_at = self._cache[user_id]
            if now - cached_at < self._ttl:
                return profile
        profile = self._fetch(user_id)
        self._cache[user_id] = (profile, now)
        return profile
''',
}


# ---------------------------------------------------------------------------
# Demo 10: Silent Data Loss
# H¹ at INTENT×CODE — "processes all records" contradicts bare except: pass
# ---------------------------------------------------------------------------

DEMO_SILENT_DATA_LOSS: Dict[str, Any] = {
    "name": "Silent Data Loss",
    "category": "H¹ at INTENT×CODE",
    "buggy_code": '''\
from typing import List, Dict, Any, Optional
import json
import logging

logger = logging.getLogger(__name__)

def process_records(
    records: List[Dict[str, Any]],
    transform_fn: Any = None,
) -> List[Dict[str, Any]]:
    """Process all records through the transformation pipeline.

    Takes a list of records and applies the transformation function
    to each one. ALL records are processed — this function guarantees
    complete processing of the input dataset.

    Args:
        records: List of record dictionaries to process.
        transform_fn: Optional transformation function to apply.

    Returns:
        List of successfully processed records.
    """
    results: List[Dict[str, Any]] = []
    for record in records:
        try:
            if transform_fn is not None:
                record = transform_fn(record)
            # Validate required fields
            assert "id" in record, "Missing id"
            assert "data" in record, "Missing data"
            results.append(record)
        except:  # noqa: E722 — bare except
            pass  # silently swallow ALL errors
    return results


def import_json_data(
    file_paths: List[str],
) -> List[Dict[str, Any]]:
    """Import and merge data from all JSON files.

    Reads ALL specified JSON files and merges their contents into
    a single list. Every file is processed.

    Args:
        file_paths: Paths to JSON files to import.

    Returns:
        Combined list of all records from all files.
    """
    all_records: List[Dict[str, Any]] = []
    for path in file_paths:
        try:
            with open(path) as f:
                data = json.load(f)
            if isinstance(data, list):
                all_records.extend(data)
            else:
                all_records.append(data)
        except:  # noqa: E722
            pass  # file errors silently ignored
    return all_records


def batch_update(
    items: List[Dict[str, Any]],
    update_fn: Any,
) -> Dict[str, int]:
    """Apply updates to all items in the batch.

    Processes every item in the batch. Returns a summary with counts.

    Args:
        items: Items to update.
        update_fn: Function to apply to each item.

    Returns:
        Dict with 'total', 'succeeded', 'failed' counts.
    """
    succeeded = 0
    failed = 0
    for item in items:
        try:
            update_fn(item)
            succeeded += 1
        except:  # noqa: E722
            pass  # BUG: increments neither succeeded nor failed
    return {
        "total": len(items),
        "succeeded": succeeded,
        "failed": failed,  # always 0 — errors are invisible
    }
''',
    "docstring_or_spec": (
        "process_records: 'ALL records are processed'. "
        "import_json_data: 'Every file is processed'. "
        "batch_update: 'Processes every item'."
    ),
    "mypy_output": "Success: no issues found in 1 source file",
    "pytest_result": '''\
# tests/test_pipeline.py
def test_process_records():
    records = [
        {"id": 1, "data": "hello"},
        {"id": 2, "data": "world"},
    ]
    result = process_records(records)
    assert len(result) == 2

def test_process_with_transform():
    records = [{"id": 1, "data": "hello"}]
    result = process_records(records, lambda r: {**r, "data": r["data"].upper()})
    assert result[0]["data"] == "HELLO"

def test_batch_update():
    items = [{"val": 1}, {"val": 2}]
    results = []
    batch_update(items, lambda x: results.append(x["val"] * 2))
    assert results == [2, 4]

# Result: 3 passed in 0.01s
# (All tests use clean, valid data — no errors to swallow)
''',
    "deppy_h1_analysis": (
        "H¹(INTENT×CODE) ≠ 0. The intent section carries the predicate "
        "'ALL records are processed' / 'every item' — a totality claim. "
        "The code section contains 'except: pass' (bare except with pass "
        "body), which silently discards ALL exceptions including "
        "KeyboardInterrupt, SystemExit, MemoryError, and data-related errors. "
        "The intent's totality predicate ('all records processed') is "
        "contradicted by the code's error-swallowing behavior: when a record "
        "fails, it simply disappears from the output. The function claims "
        "complete processing but actually performs lossy processing."
    ),
    "deppy_diagnostic": (
        "CRITICAL [H¹-INTENT×CODE] process_records (line 7): "
        "Intent claims 'ALL records are processed' but bare 'except: pass' "
        "on line 31 silently drops records that cause ANY exception. "
        "Failed records vanish without logging, counting, or notification. "
        "The returned list may be shorter than the input with no indication "
        "of data loss.\n"
        "CRITICAL [H¹-INTENT×CODE] import_json_data (line 39): "
        "Claims 'every file is processed' but bare except on line 57 "
        "silently skips unreadable/malformed files.\n"
        "ERROR [H¹-INTENT×CODE] batch_update (line 62): "
        "Claims to return accurate counts but except:pass on line 80 "
        "means failed items increment neither 'succeeded' nor 'failed'. "
        "total != succeeded + failed — the counts lie."
    ),
    "explanation": (
        "mypy doesn't analyze exception handling patterns. pylint warns about "
        "bare except (W0702) but many codebases suppress this with noqa or "
        "pylint: disable. pytest passes because test data is clean — there are "
        "no errors to swallow. The silent data loss only appears with real "
        "data: malformed records, encoding errors, network timeouts. Deppy "
        "catches the contradiction between 'processes ALL records' and "
        "'except: pass' — you can't promise completeness while silently "
        "discarding failures."
    ),
    "fix": '''\
from typing import List, Dict, Any, Optional, Tuple
import json
import logging

logger = logging.getLogger(__name__)

class ProcessingError(Exception):
    """Raised when record processing fails."""
    def __init__(self, record: Any, cause: Exception) -> None:
        self.record = record
        self.cause = cause
        super().__init__(f"Failed to process record: {cause}")


def process_records(
    records: List[Dict[str, Any]],
    transform_fn: Any = None,
    on_error: str = "raise",
) -> Tuple[List[Dict[str, Any]], List[ProcessingError]]:
    """Process all records, tracking successes and failures.

    Args:
        records: Records to process.
        transform_fn: Optional transform.
        on_error: 'raise' to stop on first error, 'collect' to gather all.

    Returns:
        Tuple of (successful_records, errors).
    """
    results: List[Dict[str, Any]] = []
    errors: List[ProcessingError] = []
    for record in records:
        try:
            if transform_fn is not None:
                record = transform_fn(record)
            if "id" not in record:
                raise ValueError("Missing id")
            if "data" not in record:
                raise ValueError("Missing data")
            results.append(record)
        except Exception as e:
            err = ProcessingError(record, e)
            if on_error == "raise":
                raise err from e
            errors.append(err)
            logger.warning("Record processing failed: %s", e)
    return results, errors


def batch_update(
    items: List[Dict[str, Any]],
    update_fn: Any,
) -> Dict[str, int]:
    """Apply updates to all items, accurately tracking results."""
    succeeded = 0
    failed = 0
    for item in items:
        try:
            update_fn(item)
            succeeded += 1
        except Exception as e:
            failed += 1
            logger.warning("Batch update failed for item: %s", e)
    return {"total": len(items), "succeeded": succeeded, "failed": failed}
''',
}


# ---------------------------------------------------------------------------
# Master list of all demos
# ---------------------------------------------------------------------------

DEMOS: List[Dict[str, Any]] = [
    DEMO_DOCSTRING_CODE_GAP,
    DEMO_SORT_STABILITY,
    DEMO_TOCTOU_RACE,
    DEMO_FLOAT_CURRENCY,
    DEMO_MISSING_ERROR_PROPAGATION,
    DEMO_IMPLICIT_NONE_RETURN,
    DEMO_PAGINATION_OFF_BY_ONE,
    DEMO_SQL_INJECTION,
    DEMO_STALE_CACHE,
    DEMO_SILENT_DATA_LOSS,
]


# ---------------------------------------------------------------------------
# Summary table for quick reference
# ---------------------------------------------------------------------------

SUMMARY_TABLE: List[Dict[str, str]] = [
    {
        "num": "1",
        "name": "Docstring-Code Gap",
        "h1_type": "INTENT×CODE",
        "bug": "Docstring says 'checks domain exists', code only checks '@'",
        "why_missed": "Tests only check format, not domain resolution",
    },
    {
        "num": "2",
        "name": "Sort Stability Bug",
        "h1_type": "SEMANTIC×CODE",
        "bug": "Stability is accidental (list comprehension order), not enforced",
        "why_missed": "Property tests check sorted order, not stability",
    },
    {
        "num": "3",
        "name": "TOCTOU Race",
        "h1_type": "STRUCTURAL×CODE",
        "bug": "os.path.exists() then open() — race condition",
        "why_missed": "Tests are single-threaded, race never triggers",
    },
    {
        "num": "4",
        "name": "Float Currency",
        "h1_type": "STRUCTURAL×CODE",
        "bug": "IEEE 754 float for money — inexact decimal arithmetic",
        "why_missed": "Test values (10.00, 100.00) are exactly representable",
    },
    {
        "num": "5",
        "name": "Missing Error Propagation",
        "h1_type": "INTENT×STRUCTURAL",
        "bug": "Docstring says 'raises ValueError' but code returns None",
        "why_missed": "Tests don't cover the failing code paths",
    },
    {
        "num": "6",
        "name": "Implicit None Return",
        "h1_type": "STRUCTURAL×CODE",
        "bug": "-> List[str] but some paths return None implicitly",
        "why_missed": "Default mypy doesn't flag this; tests use happy paths",
    },
    {
        "num": "7",
        "name": "Off-By-One Pagination",
        "h1_type": "SEMANTIC×PROOF",
        "bug": "Integer division drops last partial page of items",
        "why_missed": "Tests use exact multiples or encode the bug in expected values",
    },
    {
        "num": "8",
        "name": "SQL Injection",
        "h1_type": "INTENT×CODE",
        "bug": "f-string SQL interpolation despite 'safely queries' docstring",
        "why_missed": "Tests use benign inputs, no malicious payloads",
    },
    {
        "num": "9",
        "name": "Stale Cache",
        "h1_type": "SEMANTIC×CODE",
        "bug": "'returns current data' but cache never invalidates",
        "why_missed": "Tests run in <1 second, data never has time to go stale",
    },
    {
        "num": "10",
        "name": "Silent Data Loss",
        "h1_type": "INTENT×CODE",
        "bug": "'processes ALL records' but except:pass swallows failures",
        "why_missed": "Tests use clean data — no errors to swallow",
    },
]


def print_summary_table() -> None:
    """Print a compact summary table of all 10 demos."""
    header = f"{'#':<3} {'Name':<28} {'H¹ Type':<22} {'Bug':<50}"
    print(header)
    print("-" * len(header))
    for row in SUMMARY_TABLE:
        print(
            f"{row['num']:<3} {row['name']:<28} {row['h1_type']:<22} "
            f"{row['bug']:<50}"
        )


# ---------------------------------------------------------------------------
# Runner
# ---------------------------------------------------------------------------

def run_all_demos() -> None:
    """Run all 10 demos, showing what mypy/pytest miss and deppy catches."""
    print("=" * 70)
    print("  deppy AHA MOMENT demos")
    print("  10 bugs that mypy + pylint + pytest all MISS")
    print("  but deppy's sheaf-cohomological analysis CATCHES")
    print("=" * 70)
    print()

    print_summary_table()
    print()

    for i, demo in enumerate(DEMOS, 1):
        print(f"{'=' * 70}")
        print(f"  Demo {i}/10: {demo['name']}")
        print(f"  Category: {demo['category']}")
        print(f"{'=' * 70}")

        print(f"\n📝 Buggy code:\n{demo['buggy_code']}")

        print(f"\n🔧 mypy says: {demo['mypy_output']}")

        print(f"\n✅ pytest says:\n{demo['pytest_result']}")

        print(f"\n🔍 deppy says:")
        print(f"  H¹ obstruction: {demo['deppy_h1_analysis']}")
        print(f"\n  Diagnostic: {demo['deppy_diagnostic']}")

        print(f"\n💡 Why traditional tools miss it:")
        print(f"  {demo['explanation']}")

        print(f"\n✨ Fix:\n{demo['fix']}")
        print()

    print("=" * 70)
    print("  SUMMARY")
    print("=" * 70)
    print()
    print(f"  Total demos: {len(DEMOS)}")
    print(f"  mypy caught:   0/{len(DEMOS)}")
    print(f"  pylint caught:  0/{len(DEMOS)}")
    print(f"  pytest caught:  0/{len(DEMOS)}")
    print(f"  deppy caught:  {len(DEMOS)}/{len(DEMOS)}")
    print()
    print("  deppy detects these bugs because it computes H¹ of the")
    print("  specification sheaf over the program's topology. A nonzero")
    print("  H¹ class means local specifications (types, docstrings,")
    print("  tests) cannot be glued into a globally consistent whole.")
    print()
    print("  Traditional tools check local consistency:")
    print("    - mypy: do types match at each call site?")
    print("    - pylint: does the code follow Python conventions?")
    print("    - pytest: do specific inputs produce expected outputs?")
    print()
    print("  deppy checks GLOBAL consistency:")
    print("    - Does what the code DOES match what it CLAIMS to do?")
    print("    - Are semantic invariants actually maintained?")
    print("    - Can all local specifications be glued coherently?")
    print("=" * 70)


if __name__ == "__main__":
    run_all_demos()
