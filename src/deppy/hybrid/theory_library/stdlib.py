"""Python Standard Library Theory Pack.

Stdlib Knowledge Base
─────────────────────
This module encodes the type-level and semantic knowledge about the Python
standard library that the hybrid verification pipeline needs.  It covers:

  • **Builtins** — ``len``, ``sorted``, ``range``, ``zip``, ``map``, etc.
  • **os / os.path** — filesystem operations with preconditions.
  • **json** — serialisation round-trip axioms.
  • **re** — pattern matching API surface.
  • **math** — numeric functions with domain preconditions.
  • **itertools / functools** — higher-order combinators.
  • **collections** — ``Counter``, ``defaultdict``, ``deque``, etc.
  • **typing** — the type-annotation API.
  • **pathlib** — object-oriented filesystem paths.
  • **datetime** — temporal types and arithmetic.
  • **dataclasses** — class generation helpers.
  • **enum** — enumeration base classes.
  • **hashlib** — cryptographic hash functions.
  • **logging** — the standard logging framework.

Anti-Hallucination
──────────────────
Each entry documents the *canonical* spelling and module location so that
misspelled or misplaced API references emitted by an LLM can be caught and
corrected before verification begins.
"""

from __future__ import annotations


# --- Integration with existing deppy codebase ---
try:
    from deppy.library_theories.arithmetic_theory import ArithmeticTheoryPack
    from deppy.library_theories.sequence_collection_theory import SequenceCollectionTheoryPack
    from deppy.library_theories.nullability_theory import NullabilityTheoryPack
    from deppy.theory_packs import register_pack_spec
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False

from typing import Dict, List

from deppy.hybrid.theory_library.base import (

    APIEntry,
    Axiom,
    HybridTheoryPack,
    TheoryPackMeta,
    TypeRule,
)

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _api(
    module: str,
    name: str,
    signature: str,
    description: str = "",
    *,
    lean_type: str | None = None,
    structural: list[str] | None = None,
    semantic: list[str] | None = None,
    added_in: str | None = None,
    deprecated_in: str | None = None,
) -> APIEntry:
    return APIEntry(
        module=module,
        name=name,
        signature=signature,
        lean_type=lean_type,
        description=description,
        structural_properties=structural or [],
        semantic_properties=semantic or [],
        added_in=added_in,
        deprecated_in=deprecated_in,
    )

# ---------------------------------------------------------------------------
# StdlibTheoryPack
# ---------------------------------------------------------------------------

class StdlibTheoryPack(HybridTheoryPack):
    """Theory pack for the Python ≥ 3.10 standard library."""

    def __init__(self) -> None:
        meta = TheoryPackMeta(
            name="Python Stdlib Theory Pack",
            version="1.0.0",
            library_name="stdlib",
            library_version="3.10",
            description=(
                "Type rules, API surface, and semantic axioms for the "
                "Python standard library (builtins, os, json, re, math, "
                "itertools, functools, collections, typing, pathlib, "
                "datetime, dataclasses, enum, hashlib, logging)."
            ),
            author="deppy contributors",
        )

        entries = self._build_api_entries()
        api_dict: Dict[str, APIEntry] = {}
        for e in entries:
            api_dict[e.qualified_name] = e

        super().__init__(
            meta=meta,
            api_entries=api_dict,
            type_rules=self._build_type_rules(),
            axioms=self._build_axioms(),
        )

    # ── API entries ────────────────────────────────────────────────────────

    @staticmethod
    def _build_api_entries() -> List[APIEntry]:  # noqa: C901 — intentionally long
        entries: List[APIEntry] = []
        _a = entries.append

        # -- builtins -------------------------------------------------------
        _a(_api("builtins", "len", "(obj: Sized) -> int",
               "Return the number of items in a container.",
               structural=["result >= 0"]))
        _a(_api("builtins", "range", "(stop: int) -> range",
               "Return an immutable sequence of numbers.",
               structural=["len(result) == max(0, stop)"]))
        _a(_api("builtins", "sorted", "(iterable: Iterable[T], /, *, key=None, reverse=False) -> list[T]",
               "Return a new sorted list.",
               structural=["len(result) == len(list(iterable))"],
               semantic=["result is sorted", "set(result) == set(iterable)"]))
        _a(_api("builtins", "reversed", "(seq: Reversible[T]) -> Iterator[T]",
               "Return a reverse iterator."))
        _a(_api("builtins", "enumerate", "(iterable: Iterable[T], start: int = 0) -> Iterator[tuple[int, T]]",
               "Return an enumerate object.",
               structural=["len(list(result)) == len(list(iterable))"]))
        _a(_api("builtins", "zip", "(*iterables: Iterable) -> Iterator[tuple]",
               "Iterate over several iterables in parallel.",
               structural=["len(list(result)) == min(len(x) for x in iterables)"]))
        _a(_api("builtins", "map", "(func: Callable, *iterables: Iterable) -> Iterator",
               "Apply function to every item of iterable.",
               structural=["len(list(result)) == min(len(x) for x in iterables)"]))
        _a(_api("builtins", "filter", "(func: Callable | None, iterable: Iterable[T]) -> Iterator[T]",
               "Construct an iterator from elements for which func returns true.",
               structural=["len(list(result)) <= len(list(iterable))"]))
        _a(_api("builtins", "sum", "(iterable: Iterable[T], /, start: T = 0) -> T",
               "Return the sum of a start value plus an iterable of numbers."))
        _a(_api("builtins", "min", "(*args, key=None, default=...) -> T",
               "Return the smallest item.",
               semantic=["result <= all elements"]))
        _a(_api("builtins", "max", "(*args, key=None, default=...) -> T",
               "Return the largest item.",
               semantic=["result >= all elements"]))
        _a(_api("builtins", "abs", "(x: SupportsAbs[T]) -> T",
               "Return the absolute value.",
               structural=["result >= 0"]))
        _a(_api("builtins", "round", "(number: float, ndigits: int | None = None) -> float | int",
               "Round a number to a given precision."))
        _a(_api("builtins", "isinstance", "(obj: object, classinfo) -> bool",
               "Return whether an object is an instance of a class."))
        _a(_api("builtins", "type", "(object) -> type",
               "Return the type of an object."))
        _a(_api("builtins", "print", "(*objects, sep=' ', end='\\n', file=None, flush=False) -> None",
               "Print objects to the text stream file."))
        _a(_api("builtins", "input", "(prompt: str = '') -> str",
               "Read a string from standard input."))
        _a(_api("builtins", "open", "(file, mode='r', buffering=-1, encoding=None, ...) -> IO",
               "Open a file and return a file object."))
        _a(_api("builtins", "int", "(x=0, /, base=10) -> int",
               "Convert a number or string to an integer."))
        _a(_api("builtins", "float", "(x=0) -> float",
               "Convert a string or number to a floating point number."))
        _a(_api("builtins", "str", "(object='') -> str",
               "Return a string version of object."))
        _a(_api("builtins", "bool", "(x=False) -> bool",
               "Return a Boolean value."))
        _a(_api("builtins", "list", "(iterable=()) -> list",
               "Create a new list."))
        _a(_api("builtins", "dict", "(**kwargs) -> dict",
               "Create a new dictionary."))
        _a(_api("builtins", "set", "(iterable=()) -> set",
               "Create a new set.",
               structural=["len(result) <= len(list(iterable))"]))
        _a(_api("builtins", "tuple", "(iterable=()) -> tuple",
               "Create a new tuple."))
        _a(_api("builtins", "frozenset", "(iterable=()) -> frozenset",
               "Create a new frozenset.",
               structural=["len(result) <= len(list(iterable))"]))
        _a(_api("builtins", "bytes", "(source=b'', encoding=None, errors=None) -> bytes",
               "Create a new bytes object."))
        _a(_api("builtins", "bytearray", "(source=b'', encoding=None, errors=None) -> bytearray",
               "Create a new bytearray object."))
        _a(_api("builtins", "memoryview", "(obj: bytes | bytearray) -> memoryview",
               "Create a memoryview from a bytes-like object."))
        _a(_api("builtins", "object", "() -> object",
               "The base class of the class hierarchy."))
        _a(_api("builtins", "super", "(type=None, object_or_type=None) -> super",
               "Return a proxy object that delegates method calls."))
        _a(_api("builtins", "property", "(fget=None, fset=None, fdel=None, doc=None) -> property",
               "Return a property attribute."))
        _a(_api("builtins", "staticmethod", "(function) -> staticmethod",
               "Transform a method into a static method."))
        _a(_api("builtins", "classmethod", "(function) -> classmethod",
               "Transform a method into a class method."))
        _a(_api("builtins", "hasattr", "(obj: object, name: str) -> bool",
               "Return whether the object has the named attribute."))
        _a(_api("builtins", "getattr", "(obj: object, name: str, default=...) -> Any",
               "Return the named attribute of object."))
        _a(_api("builtins", "setattr", "(obj: object, name: str, value: Any) -> None",
               "Set a named attribute on an object."))
        _a(_api("builtins", "delattr", "(obj: object, name: str) -> None",
               "Delete a named attribute on an object."))
        _a(_api("builtins", "repr", "(obj: object) -> str",
               "Return a string containing a printable representation."))
        _a(_api("builtins", "hash", "(obj: Hashable) -> int",
               "Return the hash value of the object."))
        _a(_api("builtins", "id", "(obj: object) -> int",
               "Return the identity of an object."))
        _a(_api("builtins", "callable", "(obj: object) -> bool",
               "Return whether the object appears callable."))
        _a(_api("builtins", "iter", "(object, sentinel=...) -> Iterator",
               "Return an iterator object."))
        _a(_api("builtins", "next", "(iterator, default=...) -> T",
               "Retrieve the next item from the iterator."))
        _a(_api("builtins", "all", "(iterable: Iterable) -> bool",
               "Return True if all elements are true."))
        _a(_api("builtins", "any", "(iterable: Iterable) -> bool",
               "Return True if any element is true."))
        _a(_api("builtins", "chr", "(i: int) -> str",
               "Return the string of one character whose Unicode code point is the integer i.",
               structural=["len(result) == 1"]))
        _a(_api("builtins", "ord", "(c: str) -> int",
               "Given a string of length one, return its Unicode code point.",
               structural=["0 <= result <= 1114111"]))
        _a(_api("builtins", "hex", "(x: int) -> str",
               "Convert an integer number to a lowercase hexadecimal string."))
        _a(_api("builtins", "oct", "(x: int) -> str",
               "Convert an integer number to an octal string."))
        _a(_api("builtins", "bin", "(x: int) -> str",
               "Convert an integer number to a binary string."))
        _a(_api("builtins", "pow", "(base, exp, mod=None) -> number",
               "Return base to the power exp."))
        _a(_api("builtins", "divmod", "(a, b) -> tuple[int, int]",
               "Return the pair (a // b, a % b)."))
        _a(_api("builtins", "dir", "(object=...) -> list[str]",
               "Return list of names in the current scope or object attributes."))
        _a(_api("builtins", "vars", "(object=...) -> dict",
               "Return the __dict__ attribute of the object."))
        _a(_api("builtins", "globals", "() -> dict[str, Any]",
               "Return the current global symbol table."))
        _a(_api("builtins", "locals", "() -> dict[str, Any]",
               "Return a mapping of the current local symbol table."))
        _a(_api("builtins", "exec", "(object, globals=None, locals=None) -> None",
               "Execute the given source in the context of globals and locals."))
        _a(_api("builtins", "eval", "(expression: str, globals=None, locals=None) -> Any",
               "Evaluate the given expression."))
        _a(_api("builtins", "compile", "(source, filename, mode, ...) -> code",
               "Compile source into a code object."))
        _a(_api("builtins", "format", "(value, format_spec='') -> str",
               "Convert a value to a formatted representation."))
        _a(_api("builtins", "ascii", "(obj: object) -> str",
               "Return an ASCII-only representation of an object."))
        _a(_api("builtins", "breakpoint", "(*args, **kws) -> None",
               "Call sys.breakpointhook()."))
        _a(_api("builtins", "issubclass", "(cls, classinfo) -> bool",
               "Return whether class is a subclass of classinfo."))

        # -- os --------------------------------------------------------------
        _a(_api("os", "makedirs", "(name: str, mode: int = 0o777, exist_ok: bool = False) -> None",
               "Recursive directory creation."))
        _a(_api("os", "listdir", "(path: str = '.') -> list[str]",
               "Return a list of entries in the directory."))
        _a(_api("os", "getcwd", "() -> str",
               "Return the current working directory."))
        _a(_api("os", "environ", "Mapping[str, str]",
               "Mapping of environment variables."))
        _a(_api("os", "remove", "(path: str) -> None",
               "Remove a file."))
        _a(_api("os", "rename", "(src: str, dst: str) -> None",
               "Rename a file or directory."))
        _a(_api("os", "walk", "(top: str, ...) -> Iterator[tuple[str, list[str], list[str]]]",
               "Directory tree generator."))
        _a(_api("os", "getenv", "(key: str, default: str | None = None) -> str | None",
               "Get an environment variable."))
        _a(_api("os", "cpu_count", "() -> int | None",
               "Return the number of CPUs."))
        _a(_api("os", "getpid", "() -> int",
               "Return the current process id."))

        # -- os.path ---------------------------------------------------------
        _a(_api("os.path", "join", "(path: str, *paths: str) -> str",
               "Join one or more path components."))
        _a(_api("os.path", "exists", "(path: str) -> bool",
               "Return True if path refers to an existing path."))
        _a(_api("os.path", "isfile", "(path: str) -> bool",
               "Return True if path is an existing regular file."))
        _a(_api("os.path", "isdir", "(path: str) -> bool",
               "Return True if path is an existing directory."))
        _a(_api("os.path", "basename", "(path: str) -> str",
               "Return the base name of pathname path."))
        _a(_api("os.path", "dirname", "(path: str) -> str",
               "Return the directory name of pathname path."))
        _a(_api("os.path", "splitext", "(path: str) -> tuple[str, str]",
               "Split the extension from a pathname."))
        _a(_api("os.path", "abspath", "(path: str) -> str",
               "Return a normalised absolutised version of path."))
        _a(_api("os.path", "expanduser", "(path: str) -> str",
               "Expand ~ and ~user constructions."))
        _a(_api("os.path", "getsize", "(path: str) -> int",
               "Return the size of path in bytes.",
               structural=["result >= 0"]))
        _a(_api("os.path", "relpath", "(path: str, start: str = os.curdir) -> str",
               "Return a relative filepath."))

        # -- json ------------------------------------------------------------
        _a(_api("json", "dumps", "(obj: Any, *, indent=None, sort_keys=False, ...) -> str",
               "Serialise obj to a JSON formatted string.",
               semantic=["json.loads(result) == obj for simple types"]))
        _a(_api("json", "loads", "(s: str | bytes, ...) -> Any",
               "Deserialise a JSON document.",
               semantic=["json.dumps(result) == s for canonical JSON"]))
        _a(_api("json", "dump", "(obj: Any, fp: IO, ...) -> None",
               "Serialise obj as a JSON stream to fp."))
        _a(_api("json", "load", "(fp: IO, ...) -> Any",
               "Deserialise a JSON stream."))

        # -- re --------------------------------------------------------------
        _a(_api("re", "match", "(pattern: str, string: str, flags: int = 0) -> re.Match | None",
               "Try to match pattern at the start of string."))
        _a(_api("re", "search", "(pattern: str, string: str, flags: int = 0) -> re.Match | None",
               "Search string for the first location where the pattern matches."))
        _a(_api("re", "findall", "(pattern: str, string: str, flags: int = 0) -> list[str]",
               "Return all non-overlapping matches of pattern in string."))
        _a(_api("re", "sub", "(pattern: str, repl, string: str, count: int = 0, flags: int = 0) -> str",
               "Return the string obtained by replacing occurrences of pattern."))
        _a(_api("re", "compile", "(pattern: str, flags: int = 0) -> re.Pattern",
               "Compile a regular expression pattern."))
        _a(_api("re", "split", "(pattern: str, string: str, maxsplit: int = 0, flags: int = 0) -> list[str]",
               "Split string by the occurrences of pattern."))
        _a(_api("re", "fullmatch", "(pattern: str, string: str, flags: int = 0) -> re.Match | None",
               "Try to match the whole string with the pattern."))
        _a(_api("re", "Pattern", "re.Pattern[str]", "Compiled regular expression object."))
        _a(_api("re", "Match", "re.Match[str]", "Match object returned by match/search."))

        # -- math ------------------------------------------------------------
        _a(_api("math", "sqrt", "(x: float) -> float",
               "Return the square root of x.",
               structural=["result >= 0"],
               semantic=["result * result == x"]))
        _a(_api("math", "sin", "(x: float) -> float",
               "Return the sine of x (measured in radians).",
               structural=["-1 <= result <= 1"]))
        _a(_api("math", "cos", "(x: float) -> float",
               "Return the cosine of x (measured in radians).",
               structural=["-1 <= result <= 1"]))
        _a(_api("math", "tan", "(x: float) -> float",
               "Return the tangent of x (measured in radians)."))
        _a(_api("math", "log", "(x: float, base: float = e) -> float",
               "Return the logarithm of x.",
               semantic=["base ** result == x"]))
        _a(_api("math", "exp", "(x: float) -> float",
               "Return e raised to the power of x.",
               structural=["result > 0"]))
        _a(_api("math", "ceil", "(x: float) -> int",
               "Return the ceiling of x.",
               structural=["result >= x"]))
        _a(_api("math", "floor", "(x: float) -> int",
               "Return the floor of x.",
               structural=["result <= x"]))
        _a(_api("math", "pi", "float", "The mathematical constant π = 3.14159…"))
        _a(_api("math", "e", "float", "The mathematical constant e = 2.71828…"))
        _a(_api("math", "inf", "float", "Positive infinity."))
        _a(_api("math", "nan", "float", "Not a number (NaN)."))
        _a(_api("math", "isnan", "(x: float) -> bool",
               "Return True if x is a NaN."))
        _a(_api("math", "isinf", "(x: float) -> bool",
               "Return True if x is positive or negative infinity."))
        _a(_api("math", "isfinite", "(x: float) -> bool",
               "Return True if x is neither NaN nor infinity."))
        _a(_api("math", "fabs", "(x: float) -> float",
               "Return the absolute value of x.",
               structural=["result >= 0"]))
        _a(_api("math", "factorial", "(n: int) -> int",
               "Return n factorial.",
               structural=["result >= 1"]))
        _a(_api("math", "gcd", "(*integers: int) -> int",
               "Return greatest common divisor.",
               structural=["result >= 0"]))
        _a(_api("math", "lcm", "(*integers: int) -> int",
               "Return least common multiple.",
               structural=["result >= 0"], added_in="3.9"))
        _a(_api("math", "comb", "(n: int, k: int) -> int",
               "Number of ways to choose k items from n.",
               structural=["result >= 0"], added_in="3.8"))
        _a(_api("math", "perm", "(n: int, k: int | None = None) -> int",
               "Number of permutations of k items from n.",
               structural=["result >= 0"], added_in="3.8"))
        _a(_api("math", "copysign", "(x: float, y: float) -> float",
               "Return x with the sign of y."))
        _a(_api("math", "degrees", "(x: float) -> float",
               "Convert angle x from radians to degrees."))
        _a(_api("math", "radians", "(x: float) -> float",
               "Convert angle x from degrees to radians."))
        _a(_api("math", "hypot", "(*coordinates: float) -> float",
               "Return the Euclidean distance.",
               structural=["result >= 0"]))
        _a(_api("math", "log2", "(x: float) -> float",
               "Return the base-2 logarithm of x."))
        _a(_api("math", "log10", "(x: float) -> float",
               "Return the base-10 logarithm of x."))
        _a(_api("math", "pow", "(x: float, y: float) -> float",
               "Return x raised to the power y."))
        _a(_api("math", "trunc", "(x: float) -> int",
               "Return the truncated integer value of x."))
        _a(_api("math", "prod", "(iterable, /, *, start=1) -> number",
               "Return the product of all elements.",
               added_in="3.8"))

        # -- itertools -------------------------------------------------------
        _a(_api("itertools", "chain", "(*iterables: Iterable[T]) -> Iterator[T]",
               "Chain iterables together.",
               structural=["len(list(result)) == sum(len(list(x)) for x in iterables)"]))
        _a(_api("itertools", "product", "(*iterables: Iterable, repeat: int = 1) -> Iterator[tuple]",
               "Cartesian product of input iterables."))
        _a(_api("itertools", "permutations", "(iterable: Iterable[T], r: int | None = None) -> Iterator[tuple[T, ...]]",
               "Successive r-length permutations of elements."))
        _a(_api("itertools", "combinations", "(iterable: Iterable[T], r: int) -> Iterator[tuple[T, ...]]",
               "r-length subsequences of elements from the iterable."))
        _a(_api("itertools", "combinations_with_replacement",
               "(iterable: Iterable[T], r: int) -> Iterator[tuple[T, ...]]",
               "r-length subsequences allowing repeated elements."))
        _a(_api("itertools", "groupby", "(iterable: Iterable[T], key=None) -> Iterator[tuple[K, Iterator[T]]]",
               "Group consecutive elements by key."))
        _a(_api("itertools", "islice", "(iterable: Iterable[T], stop: int) -> Iterator[T]",
               "Slice an iterator."))
        _a(_api("itertools", "cycle", "(iterable: Iterable[T]) -> Iterator[T]",
               "Cycle through an iterable infinitely."))
        _a(_api("itertools", "repeat", "(object: T, times: int = ...) -> Iterator[T]",
               "Repeat an object."))
        _a(_api("itertools", "accumulate", "(iterable: Iterable[T], func=operator.add, *, initial=None) -> Iterator[T]",
               "Running totals (or other binary function results)."))
        _a(_api("itertools", "starmap", "(function: Callable, iterable: Iterable) -> Iterator",
               "Apply function using argument tuples from iterable."))
        _a(_api("itertools", "count", "(start: int = 0, step: int = 1) -> Iterator[int]",
               "Count from start by step."))
        _a(_api("itertools", "compress", "(data: Iterable[T], selectors: Iterable) -> Iterator[T]",
               "Filter data by selectors."))
        _a(_api("itertools", "filterfalse", "(predicate, iterable: Iterable[T]) -> Iterator[T]",
               "Filter elements where predicate is false."))
        _a(_api("itertools", "dropwhile", "(predicate, iterable: Iterable[T]) -> Iterator[T]",
               "Drop while predicate is true, then yield remaining."))
        _a(_api("itertools", "takewhile", "(predicate, iterable: Iterable[T]) -> Iterator[T]",
               "Yield while predicate is true."))
        _a(_api("itertools", "zip_longest", "(*iterables, fillvalue=None) -> Iterator[tuple]",
               "Zip iterables padding shorter ones."))
        _a(_api("itertools", "tee", "(iterable: Iterable[T], n: int = 2) -> tuple[Iterator[T], ...]",
               "Return n independent iterators from a single iterable."))
        _a(_api("itertools", "pairwise", "(iterable: Iterable[T]) -> Iterator[tuple[T, T]]",
               "Successive overlapping pairs.", added_in="3.10"))

        # -- functools -------------------------------------------------------
        _a(_api("functools", "reduce", "(function: Callable, iterable: Iterable, initial=...) -> T",
               "Apply function of two arguments cumulatively."))
        _a(_api("functools", "partial", "(func: Callable, /, *args, **kwargs) -> functools.partial",
               "Return a new partial object."))
        _a(_api("functools", "lru_cache", "(maxsize: int = 128, typed: bool = False) -> Callable",
               "Least-recently-used cache decorator."))
        _a(_api("functools", "wraps", "(wrapped: Callable, ...) -> Callable",
               "Decorator factory to apply update_wrapper."))
        _a(_api("functools", "cached_property", "(func: Callable) -> cached_property",
               "Transform a method into a cached property.", added_in="3.8"))
        _a(_api("functools", "singledispatch", "(func: Callable) -> Callable",
               "Single-dispatch generic function decorator."))
        _a(_api("functools", "total_ordering", "(cls: type) -> type",
               "Class decorator that fills in missing ordering methods."))
        _a(_api("functools", "cmp_to_key", "(mycmp: Callable) -> Callable",
               "Convert a cmp function into a key function."))

        # -- collections -----------------------------------------------------
        _a(_api("collections", "Counter", "(iterable=...) -> Counter[T]",
               "Dict subclass for counting hashable objects."))
        _a(_api("collections", "defaultdict", "(default_factory=None, ...) -> defaultdict",
               "Dict subclass with a default factory."))
        _a(_api("collections", "OrderedDict", "(**kwargs) -> OrderedDict",
               "Dict subclass that remembers insertion order."))
        _a(_api("collections", "deque", "(iterable=(), maxlen=None) -> deque[T]",
               "Double-ended queue."))
        _a(_api("collections", "namedtuple", "(typename: str, field_names, ...) -> type",
               "Returns a new subclass of tuple with named fields."))
        _a(_api("collections", "ChainMap", "(*maps: Mapping) -> ChainMap",
               "Groups multiple dicts into a single mapping."))
        _a(_api("collections.abc", "Iterable", "abstract base class",
               "ABC for iterable objects."))
        _a(_api("collections.abc", "Iterator", "abstract base class",
               "ABC for iterator objects."))
        _a(_api("collections.abc", "Mapping", "abstract base class",
               "ABC for read-only mappings."))
        _a(_api("collections.abc", "MutableMapping", "abstract base class",
               "ABC for mutable mappings."))
        _a(_api("collections.abc", "Sequence", "abstract base class",
               "ABC for read-only sequences."))
        _a(_api("collections.abc", "MutableSequence", "abstract base class",
               "ABC for mutable sequences."))
        _a(_api("collections.abc", "Set", "abstract base class",
               "ABC for read-only sets."))
        _a(_api("collections.abc", "Callable", "abstract base class",
               "ABC for callable objects."))

        # -- typing ----------------------------------------------------------
        _a(_api("typing", "List", "alias for list", "Generic alias for list."))
        _a(_api("typing", "Dict", "alias for dict", "Generic alias for dict."))
        _a(_api("typing", "Set", "alias for set", "Generic alias for set."))
        _a(_api("typing", "Tuple", "alias for tuple", "Generic alias for tuple."))
        _a(_api("typing", "Optional", "Optional[X] = Union[X, None]",
               "Optional type alias."))
        _a(_api("typing", "Union", "Union[X, Y, ...]",
               "Union type."))
        _a(_api("typing", "Any", "special form", "The unconstrained type."))
        _a(_api("typing", "Callable", "Callable[[ArgTypes], ReturnType]",
               "Callable type."))
        _a(_api("typing", "Iterator", "Iterator[T]", "Iterator type."))
        _a(_api("typing", "Generator", "Generator[YieldType, SendType, ReturnType]",
               "Generator type."))
        _a(_api("typing", "TypeVar", "(name: str, *constraints, bound=None) -> TypeVar",
               "Type variable."))
        _a(_api("typing", "Generic", "base class", "Abstract base class for generic types."))
        _a(_api("typing", "Protocol", "base class",
               "Base class for protocol classes.", added_in="3.8"))
        _a(_api("typing", "Literal", "Literal[value, ...]",
               "Literal type.", added_in="3.8"))
        _a(_api("typing", "Final", "Final[type]",
               "Mark a variable or attribute as final.", added_in="3.8"))
        _a(_api("typing", "TypeAlias", "special form",
               "Explicit type alias declaration.", added_in="3.10"))
        _a(_api("typing", "TypeGuard", "TypeGuard[T]",
               "Narrowing type guard.", added_in="3.10"))
        _a(_api("typing", "ParamSpec", "(name: str) -> ParamSpec",
               "Parameter specification variable.", added_in="3.10"))
        _a(_api("typing", "Concatenate", "special form",
               "Used with ParamSpec.", added_in="3.10"))
        _a(_api("typing", "Annotated", "Annotated[T, metadata]",
               "Add context-specific metadata.", added_in="3.9"))
        _a(_api("typing", "ClassVar", "ClassVar[type]",
               "Mark class variables."))
        _a(_api("typing", "overload", "(func: Callable) -> Callable",
               "Decorator for overloaded functions."))
        _a(_api("typing", "cast", "(typ: type[T], val: Any) -> T",
               "Cast a value to a type."))
        _a(_api("typing", "TYPE_CHECKING", "bool",
               "False at runtime, True during type checking."))

        # -- pathlib ---------------------------------------------------------
        _a(_api("pathlib", "Path", "(*pathsegments: str) -> Path",
               "Object-oriented filesystem paths."))
        _a(_api("pathlib", "PurePath", "(*pathsegments: str) -> PurePath",
               "Pure path without I/O operations."))
        _a(_api("pathlib", "PurePosixPath", "(*pathsegments: str) -> PurePosixPath",
               "Pure path with POSIX semantics."))
        _a(_api("pathlib", "PureWindowsPath", "(*pathsegments: str) -> PureWindowsPath",
               "Pure path with Windows semantics."))
        _a(_api("pathlib", "PosixPath", "(*pathsegments: str) -> PosixPath",
               "Concrete path for POSIX systems."))
        _a(_api("pathlib", "WindowsPath", "(*pathsegments: str) -> WindowsPath",
               "Concrete path for Windows systems."))

        # -- datetime --------------------------------------------------------
        _a(_api("datetime", "datetime", "(...) -> datetime",
               "Combination of a date and a time."))
        _a(_api("datetime", "date", "(year: int, month: int, day: int) -> date",
               "Represents a date (year, month, day)."))
        _a(_api("datetime", "time", "(hour=0, minute=0, second=0, microsecond=0, tzinfo=None) -> time",
               "Represents a time of day."))
        _a(_api("datetime", "timedelta", "(days=0, seconds=0, microseconds=0, ...) -> timedelta",
               "Represents a duration."))
        _a(_api("datetime", "timezone", "(offset: timedelta, name: str = ...) -> timezone",
               "A fixed-offset timezone."))
        _a(_api("datetime", "datetime.now", "(tz=None) -> datetime",
               "Return the current local date and time."))
        _a(_api("datetime", "datetime.utcnow", "() -> datetime",
               "Return the current UTC date and time.",
               deprecated_in="3.12"))
        _a(_api("datetime", "datetime.fromisoformat", "(date_string: str) -> datetime",
               "Parse an ISO 8601 date string."))
        _a(_api("datetime", "date.today", "() -> date",
               "Return the current local date."))

        # -- dataclasses -----------------------------------------------------
        _a(_api("dataclasses", "dataclass", "(cls=None, /, *, init=True, repr=True, eq=True, order=False, ...) -> type",
               "Decorator to create data classes."))
        _a(_api("dataclasses", "field", "(*, default=MISSING, default_factory=MISSING, repr=True, ...) -> Field",
               "Customise individual dataclass fields."))
        _a(_api("dataclasses", "fields", "(class_or_instance) -> tuple[Field, ...]",
               "Return a tuple of Field objects."))
        _a(_api("dataclasses", "asdict", "(obj, *, dict_factory=dict) -> dict",
               "Convert a dataclass instance to a dict."))
        _a(_api("dataclasses", "astuple", "(obj, *, tuple_factory=tuple) -> tuple",
               "Convert a dataclass instance to a tuple."))
        _a(_api("dataclasses", "make_dataclass", "(cls_name: str, fields, ...) -> type",
               "Dynamically create a data class."))
        _a(_api("dataclasses", "replace", "(obj, /, **changes) -> dataclass_instance",
               "Create a new object replacing specified fields.", added_in="3.7"))
        _a(_api("dataclasses", "is_dataclass", "(obj) -> bool",
               "Return True if the parameter is a dataclass or an instance of one."))

        # -- enum ------------------------------------------------------------
        _a(_api("enum", "Enum", "base class", "Base class for creating enumerations."))
        _a(_api("enum", "IntEnum", "base class", "Enum where members are also ints."))
        _a(_api("enum", "Flag", "base class", "Support for bit flags.", added_in="3.6"))
        _a(_api("enum", "IntFlag", "base class", "Support for integer bit flags.", added_in="3.6"))
        _a(_api("enum", "auto", "() -> int", "Automatically assign enum values."))
        _a(_api("enum", "unique", "(enumeration: type) -> type",
               "Decorator ensuring unique member values."))
        _a(_api("enum", "StrEnum", "base class",
               "Enum where members are also strings.", added_in="3.11"))

        # -- hashlib ---------------------------------------------------------
        _a(_api("hashlib", "md5", "(data: bytes = b'') -> hash",
               "Return an MD5 hash object."))
        _a(_api("hashlib", "sha1", "(data: bytes = b'') -> hash",
               "Return a SHA-1 hash object."))
        _a(_api("hashlib", "sha256", "(data: bytes = b'') -> hash",
               "Return a SHA-256 hash object."))
        _a(_api("hashlib", "sha512", "(data: bytes = b'') -> hash",
               "Return a SHA-512 hash object."))
        _a(_api("hashlib", "sha384", "(data: bytes = b'') -> hash",
               "Return a SHA-384 hash object."))
        _a(_api("hashlib", "sha224", "(data: bytes = b'') -> hash",
               "Return a SHA-224 hash object."))
        _a(_api("hashlib", "blake2b", "(data: bytes = b'', ...) -> hash",
               "Return a BLAKE2b hash object.", added_in="3.6"))
        _a(_api("hashlib", "blake2s", "(data: bytes = b'', ...) -> hash",
               "Return a BLAKE2s hash object.", added_in="3.6"))
        _a(_api("hashlib", "new", "(name: str, data: bytes = b'') -> hash",
               "Generic constructor for hash objects."))

        # -- logging ---------------------------------------------------------
        _a(_api("logging", "getLogger", "(name: str | None = None) -> Logger",
               "Return a logger with the specified name."))
        _a(_api("logging", "debug", "(msg: str, *args, **kwargs) -> None",
               "Log a message with severity DEBUG."))
        _a(_api("logging", "info", "(msg: str, *args, **kwargs) -> None",
               "Log a message with severity INFO."))
        _a(_api("logging", "warning", "(msg: str, *args, **kwargs) -> None",
               "Log a message with severity WARNING."))
        _a(_api("logging", "error", "(msg: str, *args, **kwargs) -> None",
               "Log a message with severity ERROR."))
        _a(_api("logging", "critical", "(msg: str, *args, **kwargs) -> None",
               "Log a message with severity CRITICAL."))
        _a(_api("logging", "basicConfig", "(**kwargs) -> None",
               "Configure the default handler of the root logger."))
        _a(_api("logging", "StreamHandler", "(stream=None) -> StreamHandler",
               "Handler that writes to a stream."))
        _a(_api("logging", "FileHandler", "(filename: str, mode: str = 'a', ...) -> FileHandler",
               "Handler that writes to a file."))
        _a(_api("logging", "Formatter", "(fmt: str | None = None, ...) -> Formatter",
               "Formatter for log records."))
        _a(_api("logging", "Handler", "() -> Handler",
               "Base class for handlers."))
        _a(_api("logging", "Logger", "(name: str, level: int = 0) -> Logger",
               "Logger class."))
        _a(_api("logging", "NullHandler", "() -> NullHandler",
               "Handler that does nothing."))

        # -- string ----------------------------------------------------------
        _a(_api("str", "join", "(iterable: Iterable[str]) -> str",
               "Concatenate strings with separator."))
        _a(_api("str", "split", "(sep=None, maxsplit=-1) -> list[str]",
               "Split string by separator."))
        _a(_api("str", "strip", "(chars=None) -> str",
               "Return a copy with leading and trailing whitespace removed."))
        _a(_api("str", "replace", "(old: str, new: str, count: int = -1) -> str",
               "Return a copy with all occurrences of old replaced by new."))
        _a(_api("str", "startswith", "(prefix: str | tuple, start: int = 0, end: int = ...) -> bool",
               "Test if string starts with prefix."))
        _a(_api("str", "endswith", "(suffix: str | tuple, start: int = 0, end: int = ...) -> bool",
               "Test if string ends with suffix."))
        _a(_api("str", "upper", "() -> str",
               "Return a copy converted to uppercase.",
               structural=["len(result) == len(self)"]))
        _a(_api("str", "lower", "() -> str",
               "Return a copy converted to lowercase.",
               structural=["len(result) == len(self)"]))
        _a(_api("str", "format", "(*args, **kwargs) -> str",
               "Perform a string formatting operation."))
        _a(_api("str", "encode", "(encoding: str = 'utf-8', errors: str = 'strict') -> bytes",
               "Encode the string using the specified encoding."))
        _a(_api("str", "find", "(sub: str, start: int = 0, end: int = ...) -> int",
               "Return the lowest index where substring is found.",
               structural=["result >= -1"]))
        _a(_api("str", "count", "(sub: str, start: int = 0, end: int = ...) -> int",
               "Return the number of non-overlapping occurrences.",
               structural=["result >= 0"]))
        _a(_api("str", "isdigit", "() -> bool", "Return True if all characters are digits."))
        _a(_api("str", "isalpha", "() -> bool", "Return True if all characters are alphabetic."))
        _a(_api("str", "isalnum", "() -> bool", "Return True if all characters are alphanumeric."))
        _a(_api("str", "zfill", "(width: int) -> str",
               "Pad a numeric string with zeros on the left.",
               structural=["len(result) >= width"]))

        # -- sys -------------------------------------------------------------
        _a(_api("sys", "argv", "list[str]", "Command line arguments."))
        _a(_api("sys", "exit", "(status: int | str = 0) -> NoReturn",
               "Exit from Python."))
        _a(_api("sys", "path", "list[str]", "Module search path."))
        _a(_api("sys", "stdin", "TextIO", "Standard input stream."))
        _a(_api("sys", "stdout", "TextIO", "Standard output stream."))
        _a(_api("sys", "stderr", "TextIO", "Standard error stream."))
        _a(_api("sys", "version", "str", "Python version string."))
        _a(_api("sys", "platform", "str", "Platform identifier."))
        _a(_api("sys", "getsizeof", "(object, default=...) -> int",
               "Return the size of an object in bytes.",
               structural=["result >= 0"]))
        _a(_api("sys", "maxsize", "int", "Largest positive integer supported."))

        # -- copy ------------------------------------------------------------
        _a(_api("copy", "copy", "(x: T) -> T", "Create a shallow copy of x."))
        _a(_api("copy", "deepcopy", "(x: T, memo=None) -> T",
               "Create a deep copy of x."))

        # -- contextlib ------------------------------------------------------
        _a(_api("contextlib", "contextmanager", "(func: Callable) -> Callable",
               "Decorator to create a context manager from a generator function."))
        _a(_api("contextlib", "suppress", "(*exceptions: type[BaseException]) -> AbstractContextManager",
               "Suppress specified exceptions."))
        _a(_api("contextlib", "nullcontext", "(enter_result=None) -> AbstractContextManager",
               "No-op context manager.", added_in="3.7"))

        # -- abc -------------------------------------------------------------
        _a(_api("abc", "ABC", "base class", "Helper class that provides a standard base for ABCs."))
        _a(_api("abc", "abstractmethod", "(funcobj: Callable) -> Callable",
               "Decorator for abstract methods."))

        return entries

    # ── Type rules ─────────────────────────────────────────────────────────

    @staticmethod
    def _build_type_rules() -> List[TypeRule]:
        rules: List[TypeRule] = []
        _r = rules.append

        _r(TypeRule(
            name="len_nonneg",
            pattern="len(Sized) -> int",
            postcondition="result >= 0",
            lean_statement="theorem len_nonneg (xs : List α) : xs.length ≥ 0 := Nat.zero_le _",
        ))
        _r(TypeRule(
            name="sorted_preserves_length",
            pattern="sorted(list[T]) -> list[T]",
            postcondition="len(result) == len(input)",
            lean_statement="theorem sorted_preserves_length (xs : List α) [Ord α] : (xs.mergeSort).length = xs.length := sorry",
        ))
        _r(TypeRule(
            name="sorted_preserves_elements",
            pattern="sorted(list[T]) -> list[T]",
            postcondition="set(result) == set(input)",
            lean_statement="theorem sorted_preserves_elements (xs : List α) [Ord α] : (xs.mergeSort).toFinset = xs.toFinset := sorry",
        ))
        _r(TypeRule(
            name="range_length",
            pattern="range(n) -> range",
            precondition="n >= 0",
            postcondition="len(result) == n",
            lean_statement="theorem range_length (n : Nat) : (List.range n).length = n := List.length_range n",
        ))
        _r(TypeRule(
            name="reversed_preserves_length",
            pattern="reversed(list[T]) -> Iterator[T]",
            postcondition="len(list(result)) == len(input)",
            lean_statement="theorem reversed_preserves_length (xs : List α) : xs.reverse.length = xs.length := List.length_reverse xs",
        ))
        _r(TypeRule(
            name="enumerate_preserves_length",
            pattern="enumerate(Iterable[T]) -> Iterator[tuple[int, T]]",
            postcondition="len(list(result)) == len(list(input))",
        ))
        _r(TypeRule(
            name="zip_min_length",
            pattern="zip(Iterable[A], Iterable[B]) -> Iterator[tuple[A, B]]",
            postcondition="len(list(result)) == min(len(list(a)), len(list(b)))",
        ))
        _r(TypeRule(
            name="map_preserves_length",
            pattern="map(Callable, list[T]) -> Iterator",
            postcondition="len(list(result)) == len(input)",
        ))
        _r(TypeRule(
            name="filter_shrinks",
            pattern="filter(Callable, list[T]) -> Iterator[T]",
            postcondition="len(list(result)) <= len(input)",
        ))
        _r(TypeRule(
            name="set_dedup",
            pattern="set(list[T]) -> set[T]",
            postcondition="len(result) <= len(input)",
        ))
        _r(TypeRule(
            name="abs_nonneg",
            pattern="abs(number) -> number",
            postcondition="result >= 0",
            lean_statement="theorem abs_nonneg (x : Int) : Int.natAbs x ≥ 0 := Nat.zero_le _",
        ))
        _r(TypeRule(
            name="sqrt_nonneg",
            pattern="math.sqrt(float) -> float",
            precondition="x >= 0",
            postcondition="result >= 0",
        ))
        _r(TypeRule(
            name="exp_positive",
            pattern="math.exp(float) -> float",
            postcondition="result > 0",
        ))
        _r(TypeRule(
            name="ceil_ge_input",
            pattern="math.ceil(float) -> int",
            postcondition="result >= x",
        ))
        _r(TypeRule(
            name="floor_le_input",
            pattern="math.floor(float) -> int",
            postcondition="result <= x",
        ))
        _r(TypeRule(
            name="sin_bounded",
            pattern="math.sin(float) -> float",
            postcondition="-1 <= result <= 1",
        ))
        _r(TypeRule(
            name="cos_bounded",
            pattern="math.cos(float) -> float",
            postcondition="-1 <= result <= 1",
        ))
        _r(TypeRule(
            name="factorial_positive",
            pattern="math.factorial(int) -> int",
            precondition="n >= 0",
            postcondition="result >= 1",
        ))
        _r(TypeRule(
            name="list_constructor_from_iterable",
            pattern="list(Iterable[T]) -> list[T]",
            postcondition="len(result) == len(list(input))",
        ))
        _r(TypeRule(
            name="dict_keys_unique",
            pattern="dict(**kwargs) -> dict",
            postcondition="len(result) == len(set(result.keys()))",
        ))
        _r(TypeRule(
            name="str_upper_preserves_length",
            pattern="str.upper() -> str",
            postcondition="len(result) == len(self)",
        ))
        _r(TypeRule(
            name="str_lower_preserves_length",
            pattern="str.lower() -> str",
            postcondition="len(result) == len(self)",
        ))
        _r(TypeRule(
            name="str_split_nonempty",
            pattern="str.split(sep) -> list[str]",
            postcondition="len(result) >= 1",
        ))
        _r(TypeRule(
            name="chain_total_length",
            pattern="itertools.chain(*iterables) -> Iterator",
            postcondition="len(list(result)) == sum(len(list(x)) for x in iterables)",
        ))
        _r(TypeRule(
            name="json_roundtrip",
            pattern="json.loads(json.dumps(obj)) -> obj",
            postcondition="result == obj  # for JSON-serialisable obj",
            lean_statement="-- json_roundtrip: loads(dumps(obj)) = obj for JSON-serialisable obj\naxiom json_roundtrip : sorry",
        ))
        _r(TypeRule(
            name="chr_single_char",
            pattern="chr(int) -> str",
            precondition="0 <= i <= 1114111",
            postcondition="len(result) == 1",
        ))
        _r(TypeRule(
            name="ord_valid_range",
            pattern="ord(str) -> int",
            precondition="len(c) == 1",
            postcondition="0 <= result <= 1114111",
        ))
        _r(TypeRule(
            name="min_in_collection",
            pattern="min(Iterable[T]) -> T",
            precondition="len(list(iterable)) > 0",
            postcondition="result <= all elements",
        ))
        _r(TypeRule(
            name="max_in_collection",
            pattern="max(Iterable[T]) -> T",
            precondition="len(list(iterable)) > 0",
            postcondition="result >= all elements",
        ))
        _r(TypeRule(
            name="sum_of_empty",
            pattern="sum([], start) -> start",
            postcondition="result == start",
        ))
        _r(TypeRule(
            name="divmod_decomposition",
            pattern="divmod(a, b) -> tuple[int, int]",
            precondition="b != 0",
            postcondition="result[0] * b + result[1] == a",
        ))
        _r(TypeRule(
            name="gcd_nonneg",
            pattern="math.gcd(*integers) -> int",
            postcondition="result >= 0",
        ))
        _r(TypeRule(
            name="str_zfill_min_width",
            pattern="str.zfill(width) -> str",
            postcondition="len(result) >= width",
        ))
        _r(TypeRule(
            name="deque_maxlen",
            pattern="collections.deque(iterable, maxlen) -> deque",
            postcondition="len(result) <= maxlen if maxlen is not None",
        ))
        _r(TypeRule(
            name="copy_identity",
            pattern="copy.copy(x) -> T",
            postcondition="result == x",
        ))
        _r(TypeRule(
            name="deepcopy_identity",
            pattern="copy.deepcopy(x) -> T",
            postcondition="result == x",
        ))

        return rules

    # ── Axioms ─────────────────────────────────────────────────────────────

    @staticmethod
    def _build_axioms() -> List[Axiom]:
        axioms: List[Axiom] = []
        _x = axioms.append

        _x(Axiom(
            name="sorted_idempotent",
            statement="sorted(sorted(lst)) == sorted(lst)",
            lean_statement=(
                "theorem sorted_idempotent (xs : List α) [Ord α] :\n"
                "  mergeSort (mergeSort xs) = mergeSort xs := sorry"
            ),
            trust_level="tested",
            source="CPython property test",
        ))
        _x(Axiom(
            name="set_dedup_shrinks",
            statement="len(list(set(lst))) <= len(lst)",
            lean_statement=(
                "theorem set_dedup_shrinks (xs : List α) [DecidableEq α] :\n"
                "  xs.eraseDups.length ≤ xs.length := sorry"
            ),
            trust_level="tested",
            source="CPython property test",
        ))
        _x(Axiom(
            name="sorted_preserves_set",
            statement="set(sorted(lst)) == set(lst)",
            lean_statement=(
                "theorem sorted_preserves_set (xs : List α) [Ord α] :\n"
                "  (mergeSort xs).toFinset = xs.toFinset := sorry"
            ),
            trust_level="tested",
            source="CPython property test",
        ))
        _x(Axiom(
            name="reversed_reversed_identity",
            statement="list(reversed(list(reversed(lst)))) == lst",
            lean_statement=(
                "theorem reversed_reversed_identity (xs : List α) :\n"
                "  xs.reverse.reverse = xs := List.reverse_reverse xs"
            ),
            trust_level="verified",
            source="Lean proof",
        ))
        _x(Axiom(
            name="len_append",
            statement="len(a + b) == len(a) + len(b)  # for lists",
            lean_statement=(
                "theorem len_append (xs ys : List α) :\n"
                "  (xs ++ ys).length = xs.length + ys.length := List.length_append xs ys"
            ),
            trust_level="verified",
            source="Lean proof",
        ))
        _x(Axiom(
            name="json_roundtrip",
            statement="json.loads(json.dumps(x)) == x  # for JSON-serialisable x",
            lean_statement="axiom json_roundtrip : sorry",
            trust_level="assumed",
            source="JSON specification",
        ))
        _x(Axiom(
            name="map_len_preserves",
            statement="len(list(map(f, lst))) == len(lst)",
            lean_statement=(
                "theorem map_len_preserves (f : α → β) (xs : List α) :\n"
                "  (xs.map f).length = xs.length := List.length_map f xs"
            ),
            trust_level="verified",
            source="Lean proof",
        ))
        _x(Axiom(
            name="filter_subset",
            statement="set(filter(pred, lst)) ⊆ set(lst)",
            lean_statement=(
                "theorem filter_subset (p : α → Bool) (xs : List α) :\n"
                "  (xs.filter p).toFinset ⊆ xs.toFinset := sorry"
            ),
            trust_level="tested",
            source="CPython property test",
        ))
        _x(Axiom(
            name="sum_associative",
            statement="sum(a + b) == sum(a) + sum(b)  # for numeric lists",
            lean_statement="axiom sum_associative : sorry",
            trust_level="assumed",
            source="arithmetic",
        ))
        _x(Axiom(
            name="range_sorted",
            statement="list(range(n)) == sorted(range(n))  # for n >= 0",
            lean_statement=(
                "theorem range_sorted (n : Nat) :\n"
                "  List.range n = (List.range n).mergeSort := sorry"
            ),
            trust_level="tested",
            source="CPython property test",
        ))
        _x(Axiom(
            name="enumerate_index_correctness",
            statement="all(i == idx for idx, (i, _) in enumerate(enumerate(lst)))",
            trust_level="tested",
            source="CPython property test",
        ))
        _x(Axiom(
            name="zip_unzip",
            statement="list(zip(*zip(a, b))) == [(x, y) for x, y in zip(a, b)]  # when len(a)==len(b)",
            trust_level="tested",
            source="CPython property test",
        ))
        _x(Axiom(
            name="chain_concat",
            statement="list(itertools.chain(a, b)) == list(a) + list(b)",
            lean_statement=(
                "theorem chain_concat (xs ys : List α) :\n"
                "  xs ++ ys = xs ++ ys := rfl"
            ),
            trust_level="verified",
            source="Lean proof",
        ))
        _x(Axiom(
            name="counter_sum_equals_length",
            statement="sum(Counter(lst).values()) == len(lst)",
            trust_level="tested",
            source="CPython property test",
        ))
        _x(Axiom(
            name="str_split_join_roundtrip",
            statement="sep.join(s.split(sep)) == s  # for non-None sep",
            trust_level="tested",
            source="CPython property test",
        ))
        _x(Axiom(
            name="abs_idempotent",
            statement="abs(abs(x)) == abs(x)",
            lean_statement=(
                "theorem abs_idempotent (x : Int) :\n"
                "  Int.natAbs (Int.natAbs x) = Int.natAbs x := sorry"
            ),
            trust_level="tested",
            source="CPython property test",
        ))
        _x(Axiom(
            name="max_ge_min",
            statement="max(lst) >= min(lst)  # for non-empty lst",
            trust_level="tested",
            source="CPython property test",
        ))
        _x(Axiom(
            name="set_union_superset",
            statement="a | b ⊇ a and a | b ⊇ b  # for sets",
            trust_level="tested",
            source="set theory",
        ))
        _x(Axiom(
            name="set_intersection_subset",
            statement="a & b ⊆ a and a & b ⊆ b  # for sets",
            trust_level="tested",
            source="set theory",
        ))
        _x(Axiom(
            name="deepcopy_equality",
            statement="copy.deepcopy(x) == x  # for objects with __eq__",
            trust_level="assumed",
            source="copy module docs",
        ))

        return axioms
