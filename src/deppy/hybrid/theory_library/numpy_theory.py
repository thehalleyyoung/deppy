"""NumPy Theory Pack — Shape algebra as dependent types.

Shape Tracking
──────────────
NumPy's core abstraction is the *ndarray* whose **shape** is a tuple of
non-negative integers.  Operations like ``reshape``, ``matmul``, and
``concatenate`` impose algebraic constraints on shapes that can be expressed
as dependent-type preconditions and verified at the Z3 level:

  • ``reshape(arr, new_shape)`` requires ``prod(arr.shape) == prod(new_shape)``
  • ``matmul(a, b)`` requires ``a.shape[-1] == b.shape[-2]``
  • ``concatenate([a, b], axis)`` requires shapes to match on all axes
    except ``axis``

Broadcasting
────────────
NumPy's broadcasting rules are encoded as axioms so that the hybrid checker
can validate element-wise operations between arrays of different (but
compatible) shapes.

Anti-Hallucination
──────────────────
The pack catalogues the canonical NumPy API surface, catching misspellings
like ``np.reshpe`` or ``np.linespace`` before they reach execution.
"""

from __future__ import annotations


# --- Integration with existing deppy codebase ---
try:
    from deppy.library_theories.arithmetic_theory import ArithmeticTheoryPack
    from deppy.theory_packs import register_pack_spec, TheoryPackSpec
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
# NumPyTheoryPack
# ---------------------------------------------------------------------------

class NumPyTheoryPack(HybridTheoryPack):
    """Theory pack for NumPy ≥ 1.21 with shape-level dependent types."""

    def __init__(self) -> None:
        meta = TheoryPackMeta(
            name="NumPy Theory Pack",
            version="1.0.0",
            library_name="numpy",
            library_version="1.21",
            description=(
                "Shape algebra, type rules, API surface, and semantic axioms "
                "for NumPy.  Encodes array shapes as dependent types so that "
                "reshape/matmul/broadcast mismatches are caught statically."
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
    def _build_api_entries() -> List[APIEntry]:  # noqa: C901
        entries: List[APIEntry] = []
        _a = entries.append

        # -- array creation --------------------------------------------------
        _a(_api("numpy", "array",
               "(object, dtype=None, *, copy=True, order='K', subok=False, ndmin=0) -> ndarray",
               "Create an array.",
               structural=["result.ndim >= ndmin"]))
        _a(_api("numpy", "zeros",
               "(shape, dtype=float, order='C') -> ndarray",
               "Return a new array of given shape filled with zeros.",
               structural=["result.shape == shape", "all(result == 0)"]))
        _a(_api("numpy", "ones",
               "(shape, dtype=float, order='C') -> ndarray",
               "Return a new array of given shape filled with ones.",
               structural=["result.shape == shape", "all(result == 1)"]))
        _a(_api("numpy", "empty",
               "(shape, dtype=float, order='C') -> ndarray",
               "Return a new uninitialized array of given shape.",
               structural=["result.shape == shape"]))
        _a(_api("numpy", "full",
               "(shape, fill_value, dtype=None, order='C') -> ndarray",
               "Return a new array of given shape filled with fill_value.",
               structural=["result.shape == shape", "all(result == fill_value)"]))
        _a(_api("numpy", "zeros_like",
               "(a: ndarray, dtype=None, order='K', subok=True, shape=None) -> ndarray",
               "Return an array of zeros with the same shape and type as a.",
               structural=["result.shape == a.shape if shape is None"]))
        _a(_api("numpy", "ones_like",
               "(a: ndarray, dtype=None, order='K', subok=True, shape=None) -> ndarray",
               "Return an array of ones with the same shape and type as a.",
               structural=["result.shape == a.shape if shape is None"]))
        _a(_api("numpy", "empty_like",
               "(prototype: ndarray, dtype=None, order='K', subok=True, shape=None) -> ndarray",
               "Return a new uninitialized array with same shape as prototype.",
               structural=["result.shape == prototype.shape if shape is None"]))
        _a(_api("numpy", "full_like",
               "(a: ndarray, fill_value, dtype=None, order='K', subok=True, shape=None) -> ndarray",
               "Return a full array with the same shape and type as a.",
               structural=["result.shape == a.shape if shape is None"]))
        _a(_api("numpy", "arange",
               "(start=0, stop=None, step=1, dtype=None) -> ndarray",
               "Return evenly spaced values within a given interval.",
               structural=["result.ndim == 1"]))
        _a(_api("numpy", "linspace",
               "(start, stop, num=50, endpoint=True, retstep=False, dtype=None, axis=0) -> ndarray",
               "Return evenly spaced numbers over a specified interval.",
               structural=["result.shape[axis] == num"]))
        _a(_api("numpy", "logspace",
               "(start, stop, num=50, endpoint=True, base=10.0, dtype=None, axis=0) -> ndarray",
               "Return numbers spaced evenly on a log scale.",
               structural=["result.shape[axis] == num"]))
        _a(_api("numpy", "eye",
               "(N: int, M=None, k=0, dtype=float, order='C') -> ndarray",
               "Return a 2-D array with ones on the diagonal.",
               structural=["result.shape == (N, M if M else N)"]))
        _a(_api("numpy", "identity",
               "(n: int, dtype=float) -> ndarray",
               "Return the identity array.",
               structural=["result.shape == (n, n)"]))
        _a(_api("numpy", "diag",
               "(v: ndarray, k=0) -> ndarray",
               "Extract a diagonal or construct a diagonal array."))
        _a(_api("numpy", "fromfunction",
               "(function, shape, *, dtype=float, like=None) -> ndarray",
               "Construct an array by executing a function over each coordinate.",
               structural=["result.shape == shape"]))

        # -- shape manipulation ----------------------------------------------
        _a(_api("numpy", "reshape",
               "(a: ndarray, newshape) -> ndarray",
               "Give a new shape to an array without changing its data.",
               structural=["prod(result.shape) == prod(a.shape)", "result.shape == newshape"]))
        _a(_api("numpy", "transpose",
               "(a: ndarray, axes=None) -> ndarray",
               "Reverse or permute the axes of an array.",
               structural=["result.shape == tuple(a.shape[i] for i in reversed_axes)"]))
        _a(_api("numpy", "swapaxes",
               "(a: ndarray, axis1: int, axis2: int) -> ndarray",
               "Interchange two axes of an array."))
        _a(_api("numpy", "ravel",
               "(a: ndarray, order='C') -> ndarray",
               "Return a contiguous flattened array.",
               structural=["result.ndim == 1", "result.size == a.size"]))
        _a(_api("numpy", "flatten",
               "(a: ndarray, order='C') -> ndarray",
               "Return a copy of the array collapsed into one dimension.",
               structural=["result.ndim == 1", "result.size == a.size"]))
        _a(_api("numpy", "squeeze",
               "(a: ndarray, axis=None) -> ndarray",
               "Remove axes of length one from a."))
        _a(_api("numpy", "expand_dims",
               "(a: ndarray, axis) -> ndarray",
               "Expand the shape of an array by inserting a new axis.",
               structural=["result.ndim == a.ndim + 1"]))
        _a(_api("numpy", "moveaxis",
               "(a: ndarray, source, destination) -> ndarray",
               "Move axes of an array to new positions.",
               structural=["result.ndim == a.ndim"]))
        _a(_api("numpy", "rollaxis",
               "(a: ndarray, axis: int, start=0) -> ndarray",
               "Roll the specified axis backwards.",
               structural=["result.ndim == a.ndim"]))
        _a(_api("numpy", "atleast_1d",
               "(*arys) -> ndarray | list[ndarray]",
               "Convert inputs to arrays with at least one dimension.",
               structural=["result.ndim >= 1"]))
        _a(_api("numpy", "atleast_2d",
               "(*arys) -> ndarray | list[ndarray]",
               "Convert inputs to arrays with at least two dimensions.",
               structural=["result.ndim >= 2"]))
        _a(_api("numpy", "atleast_3d",
               "(*arys) -> ndarray | list[ndarray]",
               "Convert inputs to arrays with at least three dimensions.",
               structural=["result.ndim >= 3"]))

        # -- joining / splitting ---------------------------------------------
        _a(_api("numpy", "concatenate",
               "(arrays, axis=0, out=None, dtype=None, casting='same_kind') -> ndarray",
               "Join a sequence of arrays along an existing axis.",
               structural=["result.shape[axis] == sum(a.shape[axis] for a in arrays)"]))
        _a(_api("numpy", "stack",
               "(arrays, axis=0, out=None, dtype=None, casting='same_kind') -> ndarray",
               "Join a sequence of arrays along a new axis.",
               structural=["result.ndim == arrays[0].ndim + 1"]))
        _a(_api("numpy", "vstack",
               "(tup) -> ndarray",
               "Stack arrays in sequence vertically (row wise)."))
        _a(_api("numpy", "hstack",
               "(tup) -> ndarray",
               "Stack arrays in sequence horizontally (column wise)."))
        _a(_api("numpy", "dstack",
               "(tup) -> ndarray",
               "Stack arrays in sequence depth wise (along third axis)."))
        _a(_api("numpy", "column_stack",
               "(tup) -> ndarray",
               "Stack 1-D arrays as columns into a 2-D array."))
        _a(_api("numpy", "split",
               "(ary: ndarray, indices_or_sections, axis=0) -> list[ndarray]",
               "Split an array into multiple sub-arrays."))
        _a(_api("numpy", "hsplit",
               "(ary: ndarray, indices_or_sections) -> list[ndarray]",
               "Split an array into multiple sub-arrays horizontally."))
        _a(_api("numpy", "vsplit",
               "(ary: ndarray, indices_or_sections) -> list[ndarray]",
               "Split an array into multiple sub-arrays vertically."))
        _a(_api("numpy", "tile",
               "(A: ndarray, reps) -> ndarray",
               "Construct an array by repeating A the given number of times."))
        _a(_api("numpy", "repeat",
               "(a: ndarray, repeats, axis=None) -> ndarray",
               "Repeat elements of an array."))

        # -- linear algebra --------------------------------------------------
        _a(_api("numpy", "dot",
               "(a, b, out=None) -> ndarray | scalar",
               "Dot product of two arrays.",
               structural=["a.shape[-1] == b.shape[-2] for 2-D arrays"]))
        _a(_api("numpy", "matmul",
               "(x1: ndarray, x2: ndarray, ...) -> ndarray",
               "Matrix product of two arrays.",
               structural=[
                   "x1.shape[-1] == x2.shape[-2]",
                   "result.shape == (*broadcast(x1.shape[:-2], x2.shape[:-2]), x1.shape[-2], x2.shape[-1])",
               ]))
        _a(_api("numpy", "inner",
               "(a, b) -> ndarray | scalar",
               "Inner product of two arrays."))
        _a(_api("numpy", "outer",
               "(a, b, out=None) -> ndarray",
               "Compute the outer product of two vectors.",
               structural=["result.shape == (a.size, b.size)"]))
        _a(_api("numpy", "tensordot",
               "(a, b, axes=2) -> ndarray",
               "Compute tensor dot product along specified axes."))
        _a(_api("numpy", "cross",
               "(a, b, axisa=-1, axisb=-1, axisc=-1, axis=None) -> ndarray",
               "Return the cross product of two vectors."))
        _a(_api("numpy.linalg", "inv",
               "(a: ndarray) -> ndarray",
               "Compute the inverse of a matrix.",
               structural=["a.shape[-2] == a.shape[-1]", "result.shape == a.shape"]))
        _a(_api("numpy.linalg", "det",
               "(a: ndarray) -> ndarray | scalar",
               "Compute the determinant of an array.",
               structural=["a.shape[-2] == a.shape[-1]"]))
        _a(_api("numpy.linalg", "eig",
               "(a: ndarray) -> tuple[ndarray, ndarray]",
               "Compute the eigenvalues and right eigenvectors.",
               structural=["a.shape[-2] == a.shape[-1]"]))
        _a(_api("numpy.linalg", "eigvals",
               "(a: ndarray) -> ndarray",
               "Compute the eigenvalues of a general matrix."))
        _a(_api("numpy.linalg", "svd",
               "(a: ndarray, full_matrices=True, compute_uv=True, hermitian=False) -> tuple",
               "Singular Value Decomposition."))
        _a(_api("numpy.linalg", "solve",
               "(a: ndarray, b: ndarray) -> ndarray",
               "Solve a linear matrix equation.",
               structural=["a.shape[-2] == a.shape[-1]"]))
        _a(_api("numpy.linalg", "norm",
               "(x: ndarray, ord=None, axis=None, keepdims=False) -> ndarray | float",
               "Compute a matrix or vector norm.",
               structural=["result >= 0"]))
        _a(_api("numpy.linalg", "qr",
               "(a: ndarray, mode='reduced') -> tuple[ndarray, ndarray]",
               "Compute the QR factorisation of a matrix."))
        _a(_api("numpy.linalg", "cholesky",
               "(a: ndarray) -> ndarray",
               "Compute the Cholesky decomposition.",
               structural=["a.shape[-2] == a.shape[-1]", "result.shape == a.shape"]))
        _a(_api("numpy.linalg", "matrix_rank",
               "(M: ndarray, tol=None, hermitian=False) -> int",
               "Return matrix rank using SVD method."))
        _a(_api("numpy.linalg", "pinv",
               "(a: ndarray, rcond=1e-15, hermitian=False) -> ndarray",
               "Compute the pseudo-inverse of a matrix."))

        # -- reductions ------------------------------------------------------
        _a(_api("numpy", "sum",
               "(a: ndarray, axis=None, dtype=None, out=None, keepdims=False, initial=0, where=True) -> ndarray | scalar",
               "Sum of array elements over a given axis."))
        _a(_api("numpy", "mean",
               "(a: ndarray, axis=None, dtype=None, out=None, keepdims=False, where=True) -> ndarray | scalar",
               "Compute the arithmetic mean along the specified axis."))
        _a(_api("numpy", "std",
               "(a: ndarray, axis=None, dtype=None, out=None, ddof=0, keepdims=False, where=True) -> ndarray | scalar",
               "Compute the standard deviation along the specified axis.",
               structural=["result >= 0"]))
        _a(_api("numpy", "var",
               "(a: ndarray, axis=None, dtype=None, out=None, ddof=0, keepdims=False, where=True) -> ndarray | scalar",
               "Compute the variance along the specified axis.",
               structural=["result >= 0"]))
        _a(_api("numpy", "min",
               "(a: ndarray, axis=None, out=None, keepdims=False, initial=..., where=True) -> ndarray | scalar",
               "Return the minimum of an array or along an axis.",
               semantic=["result <= all elements along axis"]))
        _a(_api("numpy", "max",
               "(a: ndarray, axis=None, out=None, keepdims=False, initial=..., where=True) -> ndarray | scalar",
               "Return the maximum of an array or along an axis.",
               semantic=["result >= all elements along axis"]))
        _a(_api("numpy", "prod",
               "(a: ndarray, axis=None, dtype=None, out=None, keepdims=False, initial=1, where=True) -> ndarray | scalar",
               "Return the product of array elements over a given axis."))
        _a(_api("numpy", "cumsum",
               "(a: ndarray, axis=None, dtype=None, out=None) -> ndarray",
               "Return the cumulative sum of elements along a given axis.",
               structural=["result.shape == a.shape if axis is not None"]))
        _a(_api("numpy", "cumprod",
               "(a: ndarray, axis=None, dtype=None, out=None) -> ndarray",
               "Return the cumulative product of elements along a given axis."))
        _a(_api("numpy", "median",
               "(a: ndarray, axis=None, out=None, overwrite_input=False, keepdims=False) -> ndarray | scalar",
               "Compute the median along the specified axis."))
        _a(_api("numpy", "percentile",
               "(a: ndarray, q, axis=None, ...) -> ndarray | scalar",
               "Compute the q-th percentile of the data along the specified axis."))
        _a(_api("numpy", "any",
               "(a: ndarray, axis=None, out=None, keepdims=False, where=True) -> ndarray | bool",
               "Test whether any array element evaluates to True."))
        _a(_api("numpy", "all",
               "(a: ndarray, axis=None, out=None, keepdims=False, where=True) -> ndarray | bool",
               "Test whether all array elements evaluate to True."))

        # -- sorting / searching ---------------------------------------------
        _a(_api("numpy", "sort",
               "(a: ndarray, axis=-1, kind=None, order=None) -> ndarray",
               "Return a sorted copy of an array.",
               structural=["result.shape == a.shape"]))
        _a(_api("numpy", "argsort",
               "(a: ndarray, axis=-1, kind=None, order=None) -> ndarray",
               "Return the indices that would sort an array.",
               structural=["result.shape == a.shape"]))
        _a(_api("numpy", "argmin",
               "(a: ndarray, axis=None, out=None, keepdims=False) -> ndarray | int",
               "Return indices of the minimum values along an axis."))
        _a(_api("numpy", "argmax",
               "(a: ndarray, axis=None, out=None, keepdims=False) -> ndarray | int",
               "Return indices of the maximum values along an axis."))
        _a(_api("numpy", "argpartition",
               "(a: ndarray, kth, axis=-1, kind='introselect', order=None) -> ndarray",
               "Perform an indirect partition along the given axis.",
               structural=["result.shape == a.shape"]))
        _a(_api("numpy", "where",
               "(condition, x=None, y=None) -> ndarray | tuple[ndarray, ...]",
               "Return elements chosen from x or y depending on condition."))
        _a(_api("numpy", "unique",
               "(ar: ndarray, return_index=False, return_inverse=False, return_counts=False, axis=None) -> ndarray | tuple",
               "Find the unique elements of an array.",
               structural=["result.size <= ar.size"]))
        _a(_api("numpy", "nonzero",
               "(a: ndarray) -> tuple[ndarray, ...]",
               "Return the indices of the elements that are non-zero."))
        _a(_api("numpy", "searchsorted",
               "(a: ndarray, v, side='left', sorter=None) -> ndarray | int",
               "Find indices where elements should be inserted to maintain order."))

        # -- element-wise math -----------------------------------------------
        _a(_api("numpy", "abs",
               "(x: ndarray) -> ndarray",
               "Calculate the absolute value element-wise.",
               structural=["result.shape == x.shape", "all(result >= 0)"]))
        _a(_api("numpy", "sqrt",
               "(x: ndarray) -> ndarray",
               "Return the non-negative square-root element-wise.",
               structural=["result.shape == x.shape", "all(result >= 0)"]))
        _a(_api("numpy", "exp",
               "(x: ndarray) -> ndarray",
               "Calculate the exponential element-wise.",
               structural=["result.shape == x.shape", "all(result > 0)"]))
        _a(_api("numpy", "log",
               "(x: ndarray) -> ndarray",
               "Natural logarithm element-wise.",
               structural=["result.shape == x.shape"]))
        _a(_api("numpy", "log2",
               "(x: ndarray) -> ndarray",
               "Base-2 logarithm element-wise.",
               structural=["result.shape == x.shape"]))
        _a(_api("numpy", "log10",
               "(x: ndarray) -> ndarray",
               "Base-10 logarithm element-wise.",
               structural=["result.shape == x.shape"]))
        _a(_api("numpy", "sin",
               "(x: ndarray) -> ndarray",
               "Trigonometric sine element-wise.",
               structural=["result.shape == x.shape"]))
        _a(_api("numpy", "cos",
               "(x: ndarray) -> ndarray",
               "Trigonometric cosine element-wise.",
               structural=["result.shape == x.shape"]))
        _a(_api("numpy", "tan",
               "(x: ndarray) -> ndarray",
               "Compute tangent element-wise.",
               structural=["result.shape == x.shape"]))
        _a(_api("numpy", "power",
               "(x1: ndarray, x2: ndarray) -> ndarray",
               "First array elements raised to powers from second array.",
               structural=["result.shape == broadcast(x1.shape, x2.shape)"]))
        _a(_api("numpy", "clip",
               "(a: ndarray, a_min, a_max, out=None) -> ndarray",
               "Clip (limit) the values in an array.",
               structural=["result.shape == a.shape"]))
        _a(_api("numpy", "maximum",
               "(x1: ndarray, x2: ndarray, ...) -> ndarray",
               "Element-wise maximum of array elements.",
               structural=["result.shape == broadcast(x1.shape, x2.shape)"]))
        _a(_api("numpy", "minimum",
               "(x1: ndarray, x2: ndarray, ...) -> ndarray",
               "Element-wise minimum of array elements.",
               structural=["result.shape == broadcast(x1.shape, x2.shape)"]))
        _a(_api("numpy", "floor",
               "(x: ndarray) -> ndarray",
               "Return the floor of the input element-wise.",
               structural=["result.shape == x.shape"]))
        _a(_api("numpy", "ceil",
               "(x: ndarray) -> ndarray",
               "Return the ceiling of the input element-wise.",
               structural=["result.shape == x.shape"]))
        _a(_api("numpy", "round",
               "(a: ndarray, decimals=0, out=None) -> ndarray",
               "Evenly round to the given number of decimals.",
               structural=["result.shape == a.shape"]))
        _a(_api("numpy", "sign",
               "(x: ndarray) -> ndarray",
               "Returns an element-wise indication of the sign.",
               structural=["result.shape == x.shape"]))

        # -- boolean / comparison --------------------------------------------
        _a(_api("numpy", "isnan",
               "(x: ndarray) -> ndarray",
               "Test element-wise for NaN.",
               structural=["result.shape == x.shape", "result.dtype == bool"]))
        _a(_api("numpy", "isinf",
               "(x: ndarray) -> ndarray",
               "Test element-wise for positive or negative infinity.",
               structural=["result.shape == x.shape", "result.dtype == bool"]))
        _a(_api("numpy", "isfinite",
               "(x: ndarray) -> ndarray",
               "Test element-wise for finiteness.",
               structural=["result.shape == x.shape", "result.dtype == bool"]))
        _a(_api("numpy", "allclose",
               "(a, b, rtol=1e-05, atol=1e-08, equal_nan=False) -> bool",
               "Returns True if two arrays are element-wise equal within a tolerance."))
        _a(_api("numpy", "array_equal",
               "(a1: ndarray, a2: ndarray, equal_nan=False) -> bool",
               "True if two arrays have the same shape and elements."))
        _a(_api("numpy", "equal",
               "(x1: ndarray, x2: ndarray) -> ndarray",
               "Return element-wise equality comparison.",
               structural=["result.shape == broadcast(x1.shape, x2.shape)"]))

        # -- random ----------------------------------------------------------
        _a(_api("numpy.random", "rand",
               "(*dn: int) -> ndarray",
               "Random values in a given shape from uniform [0, 1).",
               structural=["result.shape == dn"]))
        _a(_api("numpy.random", "randn",
               "(*dn: int) -> ndarray",
               "Return samples from the standard normal distribution.",
               structural=["result.shape == dn"]))
        _a(_api("numpy.random", "randint",
               "(low, high=None, size=None, dtype=int) -> ndarray | int",
               "Return random integers from low (inclusive) to high (exclusive)."))
        _a(_api("numpy.random", "choice",
               "(a, size=None, replace=True, p=None) -> ndarray | scalar",
               "Generates a random sample from a given 1-D array."))
        _a(_api("numpy.random", "shuffle",
               "(x: ndarray) -> None",
               "Modify a sequence in-place by shuffling its contents."))
        _a(_api("numpy.random", "permutation",
               "(x) -> ndarray",
               "Randomly permute a sequence, or return a permuted range."))
        _a(_api("numpy.random", "seed",
               "(seed=None) -> None",
               "Seed the random number generator."))
        _a(_api("numpy.random", "normal",
               "(loc=0.0, scale=1.0, size=None) -> ndarray | float",
               "Draw random samples from a normal distribution."))
        _a(_api("numpy.random", "uniform",
               "(low=0.0, high=1.0, size=None) -> ndarray | float",
               "Draw samples from a uniform distribution."))
        _a(_api("numpy.random", "default_rng",
               "(seed=None) -> Generator",
               "Construct a new Generator with the default BitGenerator.",
               added_in="1.17"))

        # -- dtype / type utilities ------------------------------------------
        _a(_api("numpy", "dtype",
               "(obj, align=False, copy=False) -> dtype",
               "Create a data type object."))
        _a(_api("numpy", "asarray",
               "(a, dtype=None, order=None, like=None) -> ndarray",
               "Convert the input to an array."))
        _a(_api("numpy", "ascontiguousarray",
               "(a, dtype=None, like=None) -> ndarray",
               "Return a contiguous array (ndim >= 1) in memory (C order)."))
        _a(_api("numpy", "copy",
               "(a: ndarray, order='K', subok=False) -> ndarray",
               "Return an array copy of the given object.",
               structural=["result.shape == a.shape"]))
        _a(_api("numpy", "frombuffer",
               "(buffer, dtype=float, count=-1, offset=0, like=None) -> ndarray",
               "Interpret a buffer as a 1-D array."))
        _a(_api("numpy", "fromiter",
               "(iter, dtype, count=-1, like=None) -> ndarray",
               "Create a new 1-D array from an iterable object."))

        # -- FFT -------------------------------------------------------------
        _a(_api("numpy.fft", "fft",
               "(a: ndarray, n=None, axis=-1, norm=None) -> ndarray",
               "Compute the one-dimensional discrete Fourier Transform.",
               structural=["result.shape == a.shape if n is None"]))
        _a(_api("numpy.fft", "ifft",
               "(a: ndarray, n=None, axis=-1, norm=None) -> ndarray",
               "Compute the one-dimensional inverse discrete Fourier Transform."))
        _a(_api("numpy.fft", "fft2",
               "(a: ndarray, s=None, axes=(-2, -1), norm=None) -> ndarray",
               "Compute the 2-dimensional discrete Fourier Transform."))
        _a(_api("numpy.fft", "rfft",
               "(a: ndarray, n=None, axis=-1, norm=None) -> ndarray",
               "Compute the one-dimensional DFT for real input."))

        # -- miscellaneous ---------------------------------------------------
        _a(_api("numpy", "save",
               "(file, arr: ndarray, allow_pickle=True, fix_imports=True) -> None",
               "Save an array to a binary file in .npy format."))
        _a(_api("numpy", "load",
               "(file, mmap_mode=None, allow_pickle=False, fix_imports=True, encoding='ASCII') -> ndarray | NpzFile",
               "Load arrays or pickled objects from .npy/.npz files."))
        _a(_api("numpy", "savez",
               "(file, *args, **kwds) -> None",
               "Save several arrays into a single .npz file."))
        _a(_api("numpy", "meshgrid",
               "(*xi, copy=True, sparse=False, indexing='xy') -> list[ndarray]",
               "Return coordinate matrices from coordinate vectors."))
        _a(_api("numpy", "mgrid",
               "property -> nd_grid",
               "Return a dense multi-dimensional meshgrid."))
        _a(_api("numpy", "ogrid",
               "property -> nd_grid",
               "Return an open multi-dimensional meshgrid."))
        _a(_api("numpy", "indices",
               "(dimensions, dtype=int, sparse=False) -> ndarray | tuple[ndarray, ...]",
               "Return an array representing the indices of a grid."))
        _a(_api("numpy", "einsum",
               "(subscripts: str, *operands, out=None, ...) -> ndarray",
               "Evaluate the Einstein summation convention on the operands."))
        _a(_api("numpy", "trace",
               "(a: ndarray, offset=0, axis1=0, axis2=1, dtype=None, out=None) -> ndarray | scalar",
               "Return the sum along diagonals of the array."))

        return entries

    # ── Type rules ─────────────────────────────────────────────────────────

    @staticmethod
    def _build_type_rules() -> List[TypeRule]:
        rules: List[TypeRule] = []
        _r = rules.append

        _r(TypeRule(
            name="zeros_shape",
            pattern="numpy.zeros(shape) -> ndarray",
            postcondition="result.shape == shape",
            lean_statement="axiom zeros_shape (s : Shape) : (zeros s).shape = s",
        ))
        _r(TypeRule(
            name="ones_shape",
            pattern="numpy.ones(shape) -> ndarray",
            postcondition="result.shape == shape",
            lean_statement="axiom ones_shape (s : Shape) : (ones s).shape = s",
        ))
        _r(TypeRule(
            name="empty_shape",
            pattern="numpy.empty(shape) -> ndarray",
            postcondition="result.shape == shape",
        ))
        _r(TypeRule(
            name="full_shape",
            pattern="numpy.full(shape, fill_value) -> ndarray",
            postcondition="result.shape == shape",
        ))
        _r(TypeRule(
            name="reshape_prod_invariant",
            pattern="numpy.reshape(arr, new_shape) -> ndarray",
            precondition="prod(arr.shape) == prod(new_shape)",
            postcondition="result.shape == new_shape",
            lean_statement=(
                "axiom reshape_prod_invariant (a : NDArray s) (s' : Shape)\n"
                "  (h : prod s = prod s') : (reshape a s').shape = s'"
            ),
        ))
        _r(TypeRule(
            name="transpose_reverses_shape",
            pattern="numpy.transpose(arr) -> ndarray",
            postcondition="result.shape == tuple(reversed(arr.shape))",
            lean_statement=(
                "axiom transpose_reverses_shape (a : NDArray s) :\n"
                "  (transpose a).shape = s.reverse"
            ),
        ))
        _r(TypeRule(
            name="matmul_shape",
            pattern="numpy.matmul(a, b) -> ndarray",
            precondition="a.shape[-1] == b.shape[-2]",
            postcondition="result.shape[-2] == a.shape[-2] and result.shape[-1] == b.shape[-1]",
            lean_statement=(
                "axiom matmul_shape (a : NDArray [m, k]) (b : NDArray [k, n]) :\n"
                "  (matmul a b).shape = [m, n]"
            ),
        ))
        _r(TypeRule(
            name="dot_inner_dim",
            pattern="numpy.dot(a, b) -> ndarray",
            precondition="a.shape[-1] == b.shape[-2] for a.ndim >= 2 and b.ndim >= 2",
        ))
        _r(TypeRule(
            name="concatenate_axis_sum",
            pattern="numpy.concatenate(arrays, axis) -> ndarray",
            precondition="all shapes match except along axis",
            postcondition="result.shape[axis] == sum(a.shape[axis] for a in arrays)",
            lean_statement=(
                "axiom concatenate_axis_sum (xs : List (NDArray s)) (ax : Nat) :\n"
                "  (concat xs ax).shape[ax] = sum (fun x => x.shape[ax]) xs"
            ),
        ))
        _r(TypeRule(
            name="stack_new_axis",
            pattern="numpy.stack(arrays, axis) -> ndarray",
            precondition="all arrays have the same shape",
            postcondition="result.ndim == arrays[0].ndim + 1",
        ))
        _r(TypeRule(
            name="squeeze_removes_ones",
            pattern="numpy.squeeze(arr) -> ndarray",
            postcondition="all(d > 1 for d in result.shape) or result.ndim == 0",
        ))
        _r(TypeRule(
            name="expand_dims_adds_one",
            pattern="numpy.expand_dims(arr, axis) -> ndarray",
            postcondition="result.ndim == arr.ndim + 1",
        ))
        _r(TypeRule(
            name="ravel_1d",
            pattern="numpy.ravel(arr) -> ndarray",
            postcondition="result.ndim == 1 and result.size == arr.size",
        ))
        _r(TypeRule(
            name="outer_shape",
            pattern="numpy.outer(a, b) -> ndarray",
            postcondition="result.shape == (a.size, b.size)",
        ))
        _r(TypeRule(
            name="eye_shape",
            pattern="numpy.eye(N, M) -> ndarray",
            postcondition="result.shape == (N, M if M else N)",
        ))
        _r(TypeRule(
            name="identity_shape",
            pattern="numpy.identity(n) -> ndarray",
            postcondition="result.shape == (n, n)",
        ))
        _r(TypeRule(
            name="sort_preserves_shape",
            pattern="numpy.sort(arr) -> ndarray",
            postcondition="result.shape == arr.shape",
        ))
        _r(TypeRule(
            name="argsort_preserves_shape",
            pattern="numpy.argsort(arr) -> ndarray",
            postcondition="result.shape == arr.shape",
        ))
        _r(TypeRule(
            name="broadcast_elementwise",
            pattern="numpy.add(a, b) -> ndarray",
            postcondition="result.shape == broadcast(a.shape, b.shape)",
            lean_statement=(
                "axiom broadcast_elementwise (a : NDArray sa) (b : NDArray sb) :\n"
                "  (add a b).shape = broadcast sa sb"
            ),
        ))
        _r(TypeRule(
            name="abs_preserves_shape",
            pattern="numpy.abs(x) -> ndarray",
            postcondition="result.shape == x.shape",
        ))
        _r(TypeRule(
            name="sqrt_preserves_shape",
            pattern="numpy.sqrt(x) -> ndarray",
            postcondition="result.shape == x.shape",
        ))
        _r(TypeRule(
            name="exp_preserves_shape",
            pattern="numpy.exp(x) -> ndarray",
            postcondition="result.shape == x.shape",
        ))
        _r(TypeRule(
            name="log_preserves_shape",
            pattern="numpy.log(x) -> ndarray",
            postcondition="result.shape == x.shape",
        ))
        _r(TypeRule(
            name="clip_preserves_shape",
            pattern="numpy.clip(a, a_min, a_max) -> ndarray",
            postcondition="result.shape == a.shape",
        ))
        _r(TypeRule(
            name="copy_preserves_shape",
            pattern="numpy.copy(a) -> ndarray",
            postcondition="result.shape == a.shape",
        ))
        _r(TypeRule(
            name="inv_square_matrix",
            pattern="numpy.linalg.inv(a) -> ndarray",
            precondition="a.shape[-2] == a.shape[-1]",
            postcondition="result.shape == a.shape",
        ))
        _r(TypeRule(
            name="det_square_matrix",
            pattern="numpy.linalg.det(a) -> scalar",
            precondition="a.shape[-2] == a.shape[-1]",
        ))
        _r(TypeRule(
            name="solve_square_matrix",
            pattern="numpy.linalg.solve(a, b) -> ndarray",
            precondition="a.shape[-2] == a.shape[-1] and a.shape[-1] == b.shape[-2]",
        ))
        _r(TypeRule(
            name="norm_nonneg",
            pattern="numpy.linalg.norm(x) -> float",
            postcondition="result >= 0",
        ))
        _r(TypeRule(
            name="unique_shrinks",
            pattern="numpy.unique(arr) -> ndarray",
            postcondition="result.size <= arr.size",
        ))
        _r(TypeRule(
            name="linspace_num",
            pattern="numpy.linspace(start, stop, num) -> ndarray",
            postcondition="result.shape[0] == num",
        ))
        _r(TypeRule(
            name="arange_1d",
            pattern="numpy.arange(start, stop, step) -> ndarray",
            postcondition="result.ndim == 1",
        ))
        _r(TypeRule(
            name="diag_1d_to_2d",
            pattern="numpy.diag(v) -> ndarray",
            postcondition="result.ndim == 2 if v.ndim == 1",
        ))

        return rules

    # ── Axioms ─────────────────────────────────────────────────────────────

    @staticmethod
    def _build_axioms() -> List[Axiom]:
        axioms: List[Axiom] = []
        _x = axioms.append

        _x(Axiom(
            name="reshape_reshape",
            statement="reshape(reshape(a, s1), s2) == reshape(a, s2) when prod(a.shape) == prod(s1) == prod(s2)",
            lean_statement=(
                "axiom reshape_reshape (a : NDArray s) (s1 s2 : Shape)\n"
                "  (h1 : prod s = prod s1) (h2 : prod s1 = prod s2) :\n"
                "  reshape (reshape a s1) s2 = reshape a s2"
            ),
            trust_level="tested",
            source="NumPy property test",
        ))
        _x(Axiom(
            name="transpose_involution",
            statement="transpose(transpose(a)) == a",
            lean_statement=(
                "axiom transpose_involution (a : NDArray s) :\n"
                "  transpose (transpose a) = a"
            ),
            trust_level="tested",
            source="NumPy property test",
        ))
        _x(Axiom(
            name="matmul_associative",
            statement="matmul(matmul(a, b), c) == matmul(a, matmul(b, c))  # for compatible shapes",
            lean_statement=(
                "axiom matmul_associative (a : NDArray [m, k]) (b : NDArray [k, l]) (c : NDArray [l, n]) :\n"
                "  matmul (matmul a b) c = matmul a (matmul b c)"
            ),
            trust_level="assumed",
            source="Linear algebra",
        ))
        _x(Axiom(
            name="identity_matmul",
            statement="matmul(eye(n), a) == a  # for a.shape[0] == n",
            lean_statement=(
                "axiom identity_matmul (a : NDArray [n, m]) :\n"
                "  matmul (eye n) a = a"
            ),
            trust_level="tested",
            source="NumPy property test",
        ))
        _x(Axiom(
            name="zeros_add_identity",
            statement="a + zeros_like(a) == a",
            lean_statement="axiom zeros_add_identity (a : NDArray s) : add a (zeros s) = a",
            trust_level="tested",
            source="NumPy property test",
        ))
        _x(Axiom(
            name="ones_mul_identity",
            statement="a * ones_like(a) == a",
            lean_statement="axiom ones_mul_identity (a : NDArray s) : mul a (ones s) = a",
            trust_level="tested",
            source="NumPy property test",
        ))
        _x(Axiom(
            name="sort_idempotent",
            statement="sort(sort(a)) == sort(a)",
            trust_level="tested",
            source="NumPy property test",
        ))
        _x(Axiom(
            name="concatenate_split_roundtrip",
            statement="concatenate(split(a, n, axis), axis) == a  # for evenly divisible shapes",
            trust_level="tested",
            source="NumPy property test",
        ))
        _x(Axiom(
            name="flatten_reshape_equivalence",
            statement="flatten(a) == reshape(a, (a.size,))",
            trust_level="tested",
            source="NumPy property test",
        ))
        _x(Axiom(
            name="norm_nonneg",
            statement="linalg.norm(a) >= 0",
            lean_statement="axiom norm_nonneg (a : NDArray s) : norm a ≥ 0",
            trust_level="verified",
            source="Linear algebra",
        ))
        _x(Axiom(
            name="inv_inv_identity",
            statement="linalg.inv(linalg.inv(a)) == a  # for non-singular square matrices",
            lean_statement=(
                "axiom inv_inv_identity (a : NDArray [n, n]) (h : det a ≠ 0) :\n"
                "  inv (inv a) = a"
            ),
            trust_level="assumed",
            source="Linear algebra",
        ))
        _x(Axiom(
            name="det_product",
            statement="linalg.det(matmul(a, b)) == linalg.det(a) * linalg.det(b)",
            lean_statement=(
                "axiom det_product (a b : NDArray [n, n]) :\n"
                "  det (matmul a b) = det a * det b"
            ),
            trust_level="assumed",
            source="Linear algebra",
        ))
        _x(Axiom(
            name="broadcast_commutative",
            statement="a + b == b + a  # element-wise under broadcasting",
            trust_level="tested",
            source="NumPy property test",
        ))
        _x(Axiom(
            name="sum_of_zeros",
            statement="sum(zeros(shape)) == 0",
            lean_statement="axiom sum_of_zeros (s : Shape) : np_sum (zeros s) = 0",
            trust_level="tested",
            source="NumPy property test",
        ))
        _x(Axiom(
            name="mean_between_min_max",
            statement="min(a) <= mean(a) <= max(a)  # for real-valued arrays",
            trust_level="tested",
            source="NumPy property test",
        ))
        _x(Axiom(
            name="std_nonneg",
            statement="std(a) >= 0",
            trust_level="tested",
            source="NumPy property test",
        ))
        _x(Axiom(
            name="copy_equality",
            statement="array_equal(copy(a), a)",
            trust_level="tested",
            source="NumPy property test",
        ))
        _x(Axiom(
            name="squeeze_expand_roundtrip",
            statement="squeeze(expand_dims(a, axis), axis) == a",
            trust_level="tested",
            source="NumPy property test",
        ))

        return axioms
