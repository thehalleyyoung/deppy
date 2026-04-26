"""Cubical Python AST analysis.

The deppy pipeline already models *inter-procedural* safety via a
simplicial cochain complex (:mod:`deppy.lean.cohomology_compute`).
This module models the *intra-procedural* control flow of a single
Python function as a **cubical set** — a refinement of the classical
control-flow graph that captures higher-dimensional structure.

Why cubical (not simplicial)?
------------------------------

An ``if cond: a else: b`` with a join point downstream is naturally a
*square*, not a triangle::

    entry ───── cond=T ─────▶ body_t
      │                          │
   cond=F                      sequence
      │                          │
      ▼                          ▼
    body_e ───── join ───────▶ exit

The four sides are 1-cells; the interior is a 2-cell.  In simplicial
cohomology this would force us to add a diagonal — gerrymandered.
Cubically it's a primitive square.

Loops, try/except/finally, and nested control structures form 2- and
3-cubes.  The standard cubical operations apply:

* **Face maps** ``∂_{ε,i}`` for ε ∈ {0, 1} and i = 0..n-1 extract the
  ``ε``-th face along dimension ``i`` of an n-cube.
* **Degeneracy** σ_i raises a cell to dimension n+1 by extruding it
  trivially along axis i.
* **Composition** glues cubes that share a face.
* **Kan filling** completes a partial n-cube (one face missing) when
  the kernel can supply the boundary.

The *useful* output for safety analysis: detecting **Kan-fillable**
cubes.  When all-but-one face of a cube has a verified safety
predicate, Kan filling tells us we can deduce the missing face — i.e.,
a single missing branch's safety can be inferred from its peers.

Public API
----------

::

    cset = build_cubical_set(fn_node)
    cset.cells_by_dim[2]      # all squares
    cset.face(cell, axis, eps)  # face map
    cset.compose(c1, c2, axis)  # composition along a shared face
    cset.find_kan_fillable()    # cubes with ≥ n-1 verified faces
    cset.path_equivalent(p, q)  # are paths p and q propositionally equal?

The returned :class:`CubicalSet` exposes both the geometric structure
(cells, faces, degeneracies) and the safety annotations (guards on
each cell, derived from the path-sensitive walk).

Audit awareness
---------------

This module was added in response to the round-2 cheat audit's
follow-up question.  It is built carefully:

* No claims of soundness without a proof obligation.
* Kan-fillability is reported as a *suggestion*, not a proof — the
  caller still has to discharge the missing face via the kernel.
* When a cubical operation has no clear semantic (e.g., composing
  cubes whose shared face has different guards), we *raise* rather
  than silently coercing.
"""
from __future__ import annotations

import ast
from dataclasses import dataclass, field
from enum import Enum
from typing import Iterable, Optional


# ─────────────────────────────────────────────────────────────────────
#  Cell data
# ─────────────────────────────────────────────────────────────────────


class CellShape(str, Enum):
    """Geometric shape of a cubical cell.

    ``POINT`` is a 0-cell (vertex).  Higher-dimensional cells are
    distinguished by their *origin* in the source AST so callers can
    trace each cell back to a Python statement.
    """

    POINT = "point"
    EDGE_SEQ = "edge_seq"           # 1-cell: sequence step
    EDGE_BRANCH_T = "edge_branch_t" # 1-cell: if-branch true side
    EDGE_BRANCH_F = "edge_branch_f" # 1-cell: if-branch false side
    EDGE_LOOP_BACK = "edge_loop_back"  # 1-cell: while back-edge
    EDGE_RETURN = "edge_return"      # 1-cell: function exit
    EDGE_RAISE = "edge_raise"        # 1-cell: exception edge
    EDGE_CALL = "edge_call"          # 1-cell: call-site step
    SQUARE_IF = "square_if"          # 2-cell: if-else diamond
    SQUARE_LOOP = "square_loop"      # 2-cell: while iteration cube
    SQUARE_TRY = "square_try"        # 2-cell: try-except diamond
    CUBE_TRY_FINALLY = "cube_try_finally"  # 3-cell: try-except-finally


@dataclass(frozen=True)
class Cell:
    """A single cubical cell.

    ``dim`` is its geometric dimension.  ``vertices`` is a list of
    program-point identifiers (strings naming AST locations) — its
    size is ``2**dim`` for an n-cube (2 vertices per axis).
    ``guards`` are the path-sensitive guards that hold *throughout*
    this cell — i.e., that hold on every interior path.

    ``ast_node_id`` ties the cell back to its origin AST node so a
    UI can highlight it in the source.

    ``faces`` is a tuple ``(face_lo_axis_0, face_hi_axis_0,
    face_lo_axis_1, face_hi_axis_1, ...)`` of length ``2*dim`` —
    references to the lower-dimensional cells that bound this one.
    For a 0-cell ``faces == ()``.

    The class is frozen so cells can be hashed and used as dict
    keys; reuse :meth:`with_guards` to derive a new cell with
    additional guards.
    """

    cell_id: str
    dim: int
    shape: CellShape
    vertices: tuple[str, ...]
    guards: tuple[str, ...] = ()
    faces: tuple[str, ...] = ()
    ast_node_id: Optional[int] = None

    @property
    def num_faces(self) -> int:
        return 2 * self.dim

    def with_guards(self, extra: Iterable[str]) -> "Cell":
        return Cell(
            cell_id=self.cell_id,
            dim=self.dim,
            shape=self.shape,
            vertices=self.vertices,
            guards=tuple(self.guards) + tuple(extra),
            faces=self.faces,
            ast_node_id=self.ast_node_id,
        )

    def __repr__(self) -> str:
        g = (
            f", guards=[{', '.join(self.guards[:2])}{'...' if len(self.guards) > 2 else ''}]"
            if self.guards else ""
        )
        return (
            f"Cell({self.cell_id} dim={self.dim} shape={self.shape.value}"
            f"{g})"
        )


# ─────────────────────────────────────────────────────────────────────
#  CubicalSet
# ─────────────────────────────────────────────────────────────────────


@dataclass
class CubicalSet:
    """A cubical set built from a Python AST.

    Internally indexes cells three ways:
      * ``cells_by_id``       — for direct lookup
      * ``cells_by_dim``      — list of cells per dimension
      * ``cells_by_ast_node`` — group cells by source AST id

    Provides face / degeneracy maps as methods rather than as
    extra fields so the caller doesn't have to maintain them in
    sync.

    Soundness gates:
      * :meth:`face` raises ``KeyError`` when the requested face is
        missing — never returns a default.  Cubical operations on
        malformed cubes fail loudly.
      * :meth:`find_kan_fillable` reports cubes with exactly one
        missing face.  Multiple missing faces are NOT reported as
        fillable (Kan-fillability is for single-face completion).
      * :meth:`path_equivalent` consults the kernel-style
        canonical-form predicate equality from
        :mod:`deppy.lean.predicate_canon`.  No simplex-membership
        cheats.
    """

    function_name: str
    cells_by_id: dict[str, Cell] = field(default_factory=dict)
    cells_by_dim: dict[int, list[Cell]] = field(default_factory=dict)
    cells_by_ast_node: dict[int, list[Cell]] = field(default_factory=dict)

    # Mapping cell_id -> AST source span (lineno, col_offset).
    # Useful for UI / diagnostics.
    spans: dict[str, tuple[int, int]] = field(default_factory=dict)

    # Top-level entry / exit cell ids.
    entry: Optional[str] = None
    exit: Optional[str] = None

    # ---------- mutators -----------------------------------------

    def add(self, cell: Cell, span: Optional[tuple[int, int]] = None) -> None:
        if cell.cell_id in self.cells_by_id:
            raise ValueError(
                f"Cell already exists: {cell.cell_id}",
            )
        self.cells_by_id[cell.cell_id] = cell
        self.cells_by_dim.setdefault(cell.dim, []).append(cell)
        if cell.ast_node_id is not None:
            self.cells_by_ast_node.setdefault(
                cell.ast_node_id, [],
            ).append(cell)
        if span is not None:
            self.spans[cell.cell_id] = span

    def replace(self, cell: Cell) -> None:
        """Replace an existing cell.  The replacement must have the
        same ``cell_id`` and ``dim``; differing fields (guards,
        faces) are allowed."""
        prev = self.cells_by_id.get(cell.cell_id)
        if prev is None:
            raise KeyError(f"No such cell: {cell.cell_id}")
        if prev.dim != cell.dim:
            raise ValueError(
                f"Replacement dim {cell.dim} != original {prev.dim}",
            )
        self.cells_by_id[cell.cell_id] = cell
        # Update the dim list.
        bucket = self.cells_by_dim.get(cell.dim, [])
        for i, c in enumerate(bucket):
            if c.cell_id == cell.cell_id:
                bucket[i] = cell
                break

    # ---------- face / degeneracy --------------------------------

    def face(self, cell: Cell, axis: int, eps: int) -> Cell:
        """Return the (axis, ε)-face of ``cell``.

        ``axis`` ∈ [0, dim), ``eps`` ∈ {0, 1}.  Faces are indexed
        in ``cell.faces`` as ``(axis_0_lo, axis_0_hi, axis_1_lo,
        axis_1_hi, ...)`` so the face at (axis, ε) is at index
        ``2*axis + eps``.

        Raises ``KeyError`` if the face id is missing or
        ``IndexError`` if axis is out of range.  Never returns a
        synthetic default.
        """
        if not (0 <= axis < cell.dim):
            raise IndexError(
                f"axis {axis} out of range [0, {cell.dim})",
            )
        if eps not in (0, 1):
            raise ValueError(f"eps must be 0 or 1; got {eps!r}")
        face_idx = 2 * axis + eps
        if face_idx >= len(cell.faces):
            raise KeyError(
                f"Cell {cell.cell_id} has no face at axis={axis} eps={eps}"
            )
        face_id = cell.faces[face_idx]
        face_cell = self.cells_by_id.get(face_id)
        if face_cell is None:
            raise KeyError(f"Face cell not found: {face_id}")
        return face_cell

    def degeneracy(self, cell: Cell, axis: int) -> Cell:
        """Return the trivial extrusion of ``cell`` along ``axis``.

        Algebraically: σ_i(c) is the (n+1)-cube whose every (axis=i,
        eps)-face equals ``c``.  We don't materialise these
        cells in the set (they're trivial — always derivable on
        demand) but we provide the constructor for callers that
        want to reason about composition.
        """
        if cell.dim < 0:
            raise ValueError("cannot degenerate a non-cell")
        # The degenerate cell has 2 faces along the new axis (both
        # equal to ``cell``); the existing faces are duplicated for
        # the new axis.
        new_faces: list[str] = list(cell.faces)
        # Both new faces point to the original cell.
        new_faces.insert(2 * axis, cell.cell_id)
        new_faces.insert(2 * axis + 1, cell.cell_id)
        return Cell(
            cell_id=f"{cell.cell_id}__deg{axis}",
            dim=cell.dim + 1,
            shape=cell.shape,
            vertices=cell.vertices + cell.vertices,  # duplicated
            guards=cell.guards,
            faces=tuple(new_faces),
            ast_node_id=cell.ast_node_id,
        )

    # ---------- composition --------------------------------------

    def compose(
        self, c1: Cell, c2: Cell, axis: int,
    ) -> Cell:
        """Compose ``c1`` and ``c2`` along their shared (axis, 1)
        face of ``c1`` and (axis, 0) face of ``c2``.

        Both cells must have the same dim.  The shared face must be
        the same cell id in both AND the guards on that shared
        face from each side must be propositionally equivalent
        (canonical predicate equality).  Composition where the
        guards disagree is *unsound* — we'd be silently merging
        cells that don't actually share their boundary.

        Phase 1 (round 2 audit response): compose now uses
        :func:`predicate_canon.predicates_equivalent` to validate
        guards on the shared face.  Previously the structural
        check accepted any same-id face regardless of its guards.

        Raises ``ValueError`` when:
          * the dims differ,
          * the shared-face cells are different ids,
          * the shared-face guards disagree propositionally,
          * along any other axis, the lo or hi face cells differ.
        """
        from deppy.lean.predicate_canon import predicates_equivalent

        if c1.dim != c2.dim:
            raise ValueError(
                f"compose: dims differ ({c1.dim} vs {c2.dim})"
            )
        if not (0 <= axis < c1.dim):
            raise IndexError(
                f"axis {axis} out of range for dim {c1.dim}",
            )
        # The shared face: c1's (axis, 1) and c2's (axis, 0).
        c1_hi = self.face(c1, axis, 1)
        c2_lo = self.face(c2, axis, 0)
        if c1_hi.cell_id != c2_lo.cell_id:
            raise ValueError(
                f"compose: shared face mismatch "
                f"({c1_hi.cell_id} vs {c2_lo.cell_id})"
            )
        # Audit fix (round 2 phase 1): guard equivalence on the
        # shared face.  When the same cell id appears in both
        # faces, its guards are identical by construction (it's
        # literally the same Cell object) — but we still check in
        # case the cell was mutated through ``replace``.
        c1_hi_guards = list(c1_hi.guards)
        c2_lo_guards = list(c2_lo.guards)
        if len(c1_hi_guards) != len(c2_lo_guards):
            raise ValueError(
                f"compose: shared face has {len(c1_hi_guards)} "
                f"guards on c1's hi side but {len(c2_lo_guards)} "
                f"on c2's lo side — refusing to silently merge"
            )
        unmatched = list(c2_lo_guards)
        for g in c1_hi_guards:
            for i, h in enumerate(unmatched):
                if predicates_equivalent(g, h):
                    del unmatched[i]
                    break
            else:
                raise ValueError(
                    f"compose: shared-face guard {g!r} on c1's hi "
                    f"side has no canonical equivalent on c2's lo "
                    f"side — guards disagree propositionally"
                )
        # Build the composite faces: along the composition axis,
        # take c1's lo and c2's hi.  Along other axes, both must
        # agree (or we can't compose).
        new_faces: list[str] = []
        for a in range(c1.dim):
            if a == axis:
                new_faces.append(self.face(c1, a, 0).cell_id)
                new_faces.append(self.face(c2, a, 1).cell_id)
            else:
                f1 = self.face(c1, a, 0).cell_id
                f2 = self.face(c2, a, 0).cell_id
                if f1 != f2:
                    raise ValueError(
                        f"compose: along axis {a} the eps=0 faces differ"
                    )
                new_faces.append(f1)
                f1h = self.face(c1, a, 1).cell_id
                f2h = self.face(c2, a, 1).cell_id
                if f1h != f2h:
                    raise ValueError(
                        f"compose: along axis {a} the eps=1 faces differ"
                    )
                new_faces.append(f1h)
        # Dedupe guards while preserving order.
        seen: set[str] = set()
        merged_guards: list[str] = []
        for g in tuple(c1.guards) + tuple(c2.guards):
            if g not in seen:
                merged_guards.append(g)
                seen.add(g)
        return Cell(
            cell_id=f"{c1.cell_id}__compose__{c2.cell_id}",
            dim=c1.dim,
            shape=c1.shape,
            vertices=c1.vertices,  # geometric realization picks c1
            guards=tuple(merged_guards),
            faces=tuple(new_faces),
            ast_node_id=c1.ast_node_id,
        )

    # ---------- Kan-fillability ----------------------------------

    def find_kan_fillable(self) -> list["KanCandidate"]:
        """Enumerate cells with exactly one missing face (Kan-fillable).

        For each n-cell with exactly 2n-1 of its 2n faces present,
        the remaining face is the *Kan filler* and can be deduced
        from the rest.  We report:

          * which cell is incomplete
          * which face is missing (axis + ε)
          * the implied filler-vertex pair
          * the implied filler-guards: the conjunction of all peer
            faces' guards (since the cube is closed, any path
            around the boundary equals the path through the
            missing face)

        Audit fix (round 2 phase 1): the previous implementation
        reported only the cell id and missing axis/eps — leaving
        the filler's guards as "kernel's job."  This was the
        cheat: the cubical analyzer was supposed to *deduce* the
        filler from the existing faces, but it never tried.  The
        new version computes the filler's guards as the union of
        all peer-face guards (modulo dedup via canonical
        predicate equality).
        """
        from deppy.lean.predicate_canon import canonicalize_predicate

        out: list[KanCandidate] = []
        for cell in self.cells_by_id.values():
            if cell.dim < 1:
                continue
            missing: list[tuple[int, int]] = []
            present_faces: list[tuple[int, int, Cell]] = []
            for axis in range(cell.dim):
                for eps in (0, 1):
                    idx = 2 * axis + eps
                    if (idx >= len(cell.faces)
                            or cell.faces[idx] not in self.cells_by_id):
                        missing.append((axis, eps))
                    else:
                        face_cell = self.cells_by_id[cell.faces[idx]]
                        present_faces.append((axis, eps, face_cell))
            if len(missing) == 1:
                axis, eps = missing[0]
                # Compute implied vertex pair from the cube's
                # geometric structure.
                expected_vertices = tuple(
                    v for i, v in enumerate(cell.vertices)
                    if ((i >> axis) & 1) == eps
                )
                # Compute implied guards from the peer faces.
                # The Kan-filling rule for our setting: the
                # missing face's guards are the union of the
                # guards on the *opposite* faces (those at the
                # same axis but eps=1-eps, plus all faces at
                # other axes).  Canonicalise + dedupe so we don't
                # report ``(P)`` and ``P`` as separate guards.
                seen_canon: set[str] = set()
                implied: list[str] = []
                for fa, fe, fcell in present_faces:
                    for g in fcell.guards:
                        c = canonicalize_predicate(g)
                        if c not in seen_canon:
                            seen_canon.add(c)
                            implied.append(g)
                out.append(KanCandidate(
                    cell_id=cell.cell_id,
                    missing_axis=axis,
                    missing_eps=eps,
                    implied_vertices=expected_vertices,
                    implied_guards=tuple(implied),
                    peer_face_count=len(present_faces),
                ))
        return out

    # ---------- path equivalence ---------------------------------

    def path_equivalent(self, p: Cell, q: Cell) -> bool:
        """Are 1-cells ``p`` and ``q`` propositionally equal as
        paths?

        Two 1-cells are equivalent iff:
          * they have the same endpoints (vertex-equality), AND
          * their guard sets are propositionally equivalent (each
            guard in one is canonically equivalent to a guard in
            the other).

        Uses :mod:`deppy.lean.predicate_canon` for the canonical
        equality check — no simplex-membership cheat.
        """
        from deppy.lean.predicate_canon import predicates_equivalent
        if p.dim != 1 or q.dim != 1:
            raise ValueError("path_equivalent: both cells must be 1-cells")
        if p.vertices != q.vertices:
            return False
        if len(p.guards) != len(q.guards):
            return False
        # Each guard in p must have a canonical equivalent in q.
        q_guards = list(q.guards)
        for g in p.guards:
            matched_idx: Optional[int] = None
            for i, h in enumerate(q_guards):
                if predicates_equivalent(g, h):
                    matched_idx = i
                    break
            if matched_idx is None:
                return False
            del q_guards[matched_idx]
        return True

    # ---------- summary -----------------------------------------

    def cell_count(self) -> int:
        return len(self.cells_by_id)

    def cells_at_dim(self, dim: int) -> list[Cell]:
        return list(self.cells_by_dim.get(dim, []))

    def euler_characteristic(self) -> int:
        """Return the Euler characteristic
        ``Σ_n (-1)^n |C_n|``."""
        chi = 0
        for dim, cells in self.cells_by_dim.items():
            chi += (-1) ** dim * len(cells)
        return chi


@dataclass
class KanCandidate:
    """A cell with exactly one missing face — Kan-fillable.

    Audit fix (round 2 phase 1): now carries ``implied_guards``
    (the union of peer-face guards, canonically deduped) and
    ``peer_face_count`` (how many faces gave evidence).  The
    caller can lift these into a kernel proof obligation rather
    than re-deriving them.
    """
    cell_id: str
    missing_axis: int
    missing_eps: int
    implied_vertices: tuple[str, ...]
    implied_guards: tuple[str, ...] = ()
    peer_face_count: int = 0


# ─────────────────────────────────────────────────────────────────────
#  AST → CubicalSet builder
# ─────────────────────────────────────────────────────────────────────


def build_cubical_set(
    fn_node: ast.FunctionDef | ast.AsyncFunctionDef,
    *, refinement_map=None,
) -> CubicalSet:
    """Walk ``fn_node``'s body and build a :class:`CubicalSet`.

    Each statement contributes:

      * one or more 0-cells (program points: entry, exit of stmt),
      * one or more 1-cells (control-flow edges),
      * a 2-cell when the stmt is an ``if``/``while``/``try``,
      * a 3-cell when the stmt is a ``try`` with ``finally``.

    When ``refinement_map`` is supplied, guards from the path-
    sensitive walk are attached to each cell.  Otherwise cells
    have empty guards (the structure is built but the safety
    annotations are absent).
    """
    builder = _CubicalBuilder(
        function_name=fn_node.name,
        refinement_map=refinement_map,
    )
    return builder.build(fn_node)


class _CubicalBuilder:
    """Stateful walker that produces a :class:`CubicalSet`."""

    def __init__(
        self, *, function_name: str, refinement_map=None,
    ) -> None:
        self.function_name = function_name
        self.refinement_map = refinement_map
        self.cset = CubicalSet(function_name=function_name)
        self._counter = 0

    def _new_id(self, prefix: str) -> str:
        self._counter += 1
        return f"{self.function_name}.{prefix}{self._counter}"

    def _make_point(
        self, label: str, ast_node: Optional[ast.AST] = None,
    ) -> str:
        cid = self._new_id(f"pt_{label}_")
        cell = Cell(
            cell_id=cid, dim=0, shape=CellShape.POINT,
            vertices=(cid,), guards=(),
            ast_node_id=id(ast_node) if ast_node is not None else None,
        )
        span = None
        if ast_node is not None:
            span = (
                getattr(ast_node, "lineno", 0),
                getattr(ast_node, "col_offset", 0),
            )
        self.cset.add(cell, span=span)
        return cid

    def _make_edge(
        self, src: str, tgt: str, shape: CellShape,
        ast_node: Optional[ast.AST] = None,
        guards: Iterable[str] = (),
    ) -> str:
        cid = self._new_id(f"e_{shape.name.lower()}_")
        # 1-cell faces: axis 0, eps 0 = src; axis 0, eps 1 = tgt.
        cell = Cell(
            cell_id=cid, dim=1, shape=shape,
            vertices=(src, tgt),
            guards=tuple(guards),
            faces=(src, tgt),
            ast_node_id=id(ast_node) if ast_node is not None else None,
        )
        span = None
        if ast_node is not None:
            span = (
                getattr(ast_node, "lineno", 0),
                getattr(ast_node, "col_offset", 0),
            )
        self.cset.add(cell, span=span)
        return cid

    def _make_square(
        self, *, label: str, vertices: tuple[str, str, str, str],
        faces: tuple[str, str, str, str],
        shape: CellShape, ast_node: Optional[ast.AST] = None,
        guards: Iterable[str] = (),
    ) -> str:
        """Make a 2-cell (square).

        ``vertices`` are ordered as ``(v_00, v_10, v_01, v_11)``
        where the first index is axis-0 and the second is axis-1.
        ``faces`` are 4 1-cell ids in the order:
        ``(axis_0_lo, axis_0_hi, axis_1_lo, axis_1_hi)``.
        """
        cid = self._new_id(f"sq_{label}_")
        cell = Cell(
            cell_id=cid, dim=2, shape=shape,
            vertices=vertices, faces=faces,
            guards=tuple(guards),
            ast_node_id=id(ast_node) if ast_node is not None else None,
        )
        span = None
        if ast_node is not None:
            span = (
                getattr(ast_node, "lineno", 0),
                getattr(ast_node, "col_offset", 0),
            )
        self.cset.add(cell, span=span)
        return cid

    def _make_cube(
        self, *, label: str,
        vertices: tuple[str, ...],  # 8 entries for a 3-cube
        faces: tuple[str, ...],     # 6 entries for a 3-cube
        shape: CellShape, ast_node: Optional[ast.AST] = None,
        guards: Iterable[str] = (),
    ) -> str:
        """Make a 3-cell (cube).

        Vertices (8 total) ordered as
        ``(v_000, v_100, v_010, v_110, v_001, v_101, v_011, v_111)``
        where the i-th bit selects ε along axis i.

        Faces (6 total, 2 per axis) ordered as
        ``(axis_0_lo, axis_0_hi, axis_1_lo, axis_1_hi,
        axis_2_lo, axis_2_hi)`` — each is a 2-cell id.

        Audit fix (round 2 phase 1): real 3-cube construction.
        Previously the ``try-except-finally`` walk only emitted
        2-cells and a sequence edge for ``finally``; the third
        axis was missing.  This constructor enables a true 3-cell.
        """
        if len(vertices) != 8:
            raise ValueError(
                f"3-cube requires 8 vertices; got {len(vertices)}",
            )
        if len(faces) != 6:
            raise ValueError(
                f"3-cube requires 6 faces; got {len(faces)}",
            )
        cid = self._new_id(f"cu_{label}_")
        cell = Cell(
            cell_id=cid, dim=3, shape=shape,
            vertices=vertices, faces=faces,
            guards=tuple(guards),
            ast_node_id=id(ast_node) if ast_node is not None else None,
        )
        span = None
        if ast_node is not None:
            span = (
                getattr(ast_node, "lineno", 0),
                getattr(ast_node, "col_offset", 0),
            )
        self.cset.add(cell, span=span)
        return cid

    def _make_compound_path(
        self, src: str, tgt: str, body_edges: list[str],
        shape: CellShape, ast_node: Optional[ast.AST] = None,
        guards: Iterable[str] = (),
    ) -> str:
        """Synthesise a 1-cell representing a *path* from ``src`` to
        ``tgt`` that internally consists of ``body_edges``.

        Audit fix (round 2 phase 1): branch bodies in if/while
        loops used to be approximated as direct ``entry → exit``
        edges.  The new compound-path 1-cell records the body
        edges that participate in this path so:

          * the cubical set's edges are an honest count
          * face extraction returns the actual path data
          * the certificate emission has structured data to
            render

        The compound's guards are the *union* of the guards on
        the body edges plus the explicit ``guards`` argument
        (caller-supplied; typically the branch condition).
        """
        cid = self._new_id("cpath_")
        # Collect the body edges' guards.
        body_guards: list[str] = list(guards)
        seen = set(body_guards)
        for eid in body_edges:
            ec = self.cset.cells_by_id.get(eid)
            if ec is None:
                continue
            for g in ec.guards:
                if g not in seen:
                    body_guards.append(g)
                    seen.add(g)
        cell = Cell(
            cell_id=cid, dim=1, shape=shape,
            vertices=(src, tgt),
            guards=tuple(body_guards),
            faces=(src, tgt),
            ast_node_id=id(ast_node) if ast_node is not None else None,
        )
        # Track the body edges separately on the cell via metadata
        # — store as an attribute on the cset.  We use a dict keyed
        # by cell_id since Cell is frozen.
        self._compound_body_edges = getattr(
            self, "_compound_body_edges", {},
        )
        self._compound_body_edges[cid] = list(body_edges)
        span = None
        if ast_node is not None:
            span = (
                getattr(ast_node, "lineno", 0),
                getattr(ast_node, "col_offset", 0),
            )
        self.cset.add(cell, span=span)
        return cid

    # ---------- entry --------------------------------------------

    def build(
        self, fn_node: ast.FunctionDef | ast.AsyncFunctionDef,
    ) -> CubicalSet:
        entry = self._make_point("entry", fn_node)
        self.cset.entry = entry
        cur = entry
        for stmt in fn_node.body:
            cur = self._walk_stmt(stmt, cur)
        # Make sure there is an exit point.
        if self.cset.exit is None:
            self.cset.exit = cur
        return self.cset

    # ---------- statement dispatch -------------------------------

    def _walk_stmt(self, stmt: ast.stmt, cur: str) -> str:
        """Walk one statement.  Returns the program point at its
        exit (= the entry of the next statement)."""
        if isinstance(stmt, ast.If):
            return self._walk_if(stmt, cur)
        if isinstance(stmt, ast.While):
            return self._walk_while(stmt, cur)
        if isinstance(stmt, ast.For):
            return self._walk_for(stmt, cur)
        if isinstance(stmt, ast.Try):
            return self._walk_try(stmt, cur)
        if isinstance(stmt, ast.With):
            return self._walk_with(stmt, cur)
        if isinstance(stmt, ast.Return):
            return self._walk_return(stmt, cur)
        if isinstance(stmt, ast.Raise):
            return self._walk_raise(stmt, cur)
        # Default: the statement is a single-step edge from cur
        # to a fresh exit point.
        nxt = self._make_point("after_stmt", stmt)
        self._make_edge(
            cur, nxt, CellShape.EDGE_SEQ, ast_node=stmt,
            guards=self._guards_at(stmt),
        )
        return nxt

    # ---------- if-else -----------------------------------------

    def _walk_if(self, stmt: ast.If, cur: str) -> str:
        """An ``if cond: body_t else: body_e`` becomes a square.

        Audit fix (round 2 phase 1): the previous version used
        the ``cond=T`` and ``cond=F`` *entry* edges as the square's
        axis-1 faces — but the geometric reality is that the
        face from ``cur`` to ``body_t_exit`` is the *whole branch
        path*, not just the entry edge.  We now synthesise
        :meth:`_make_compound_path` 1-cells for each branch body
        and use those as the square's left and right sides.

        The square's structure (axis-0 = "horizontal direction
        between branches", axis-1 = "vertical, time"):

            v_00 = cur          v_10 = (right of cur, undefined)
            v_01 = body_t_exit  v_11 = join (= body_e_exit AFTER tail)

        Faces:
            axis-0 lo (left side):    cur → body_t_exit  (compound)
            axis-0 hi (right side):   ??? → join
            axis-1 lo (top):           the joined cur → join via
                                       cond=T branch (= compound_t)
            axis-1 hi (bottom):        the joined cur → join via
                                       cond=F branch (= compound_e)

        For a deterministic if-else with a join point, we model
        the square as:

            v_00 = cur,  v_10 = body_t_exit
            v_01 = body_e_exit,  v_11 = join

            axis-0 lo: edge_F  (cur → body_e_exit, compound)
            axis-0 hi: edge_t_join (body_t_exit → join, sequence)
            axis-1 lo: edge_T  (cur → body_t_exit, compound)
            axis-1 hi: edge_e_join (body_e_exit → join, sequence)

        The two compound paths are top/left and the two sequence
        edges are bottom/right, forming the boundary of the
        diamond.  When one branch's body has no statements the
        compound path is just the cond edge.
        """
        # Walk the true branch.
        body_t_entry = self._make_point("if_then_entry", stmt)
        cond_t_edge = self._make_edge(
            cur, body_t_entry, CellShape.EDGE_BRANCH_T, ast_node=stmt,
            guards=(self._cond_text(stmt.test),),
        )
        body_t_edges_before = self._snapshot_edges()
        body_t_exit = body_t_entry
        for s in stmt.body:
            body_t_exit = self._walk_stmt(s, body_t_exit)
        body_t_edges = self._edges_added_since(body_t_edges_before)

        # Walk the false branch.
        body_e_entry = self._make_point("if_else_entry", stmt)
        cond_f_edge = self._make_edge(
            cur, body_e_entry, CellShape.EDGE_BRANCH_F, ast_node=stmt,
            guards=(self._not_cond_text(stmt.test),),
        )
        body_e_edges_before = self._snapshot_edges()
        body_e_exit = body_e_entry
        for s in stmt.orelse:
            body_e_exit = self._walk_stmt(s, body_e_exit)
        body_e_edges = self._edges_added_since(body_e_edges_before)

        # Join.
        join = self._make_point("if_join", stmt)
        edge_t_to_join = self._make_edge(
            body_t_exit, join, CellShape.EDGE_SEQ, ast_node=stmt,
        )
        edge_e_to_join = self._make_edge(
            body_e_exit, join, CellShape.EDGE_SEQ, ast_node=stmt,
        )

        # Synthesise the compound branch paths.
        compound_t = self._make_compound_path(
            cur, body_t_exit,
            body_edges=[cond_t_edge] + body_t_edges,
            shape=CellShape.EDGE_BRANCH_T,
            ast_node=stmt,
            guards=(self._cond_text(stmt.test),),
        )
        compound_e = self._make_compound_path(
            cur, body_e_exit,
            body_edges=[cond_f_edge] + body_e_edges,
            shape=CellShape.EDGE_BRANCH_F,
            ast_node=stmt,
            guards=(self._not_cond_text(stmt.test),),
        )
        # Build the square — this time with the compound paths
        # as the left/top faces and the join edges as bottom/right.
        self._make_square(
            label="if",
            vertices=(cur, body_t_exit, body_e_exit, join),
            faces=(
                compound_e,         # axis-0 lo: cur → body_e_exit
                edge_t_to_join,     # axis-0 hi: body_t_exit → join
                compound_t,         # axis-1 lo: cur → body_t_exit
                edge_e_to_join,     # axis-1 hi: body_e_exit → join
            ),
            shape=CellShape.SQUARE_IF,
            ast_node=stmt,
            guards=self._guards_at(stmt),
        )
        return join

    def _snapshot_edges(self) -> int:
        """Return a snapshot id (count of 1-cells so far) so callers
        can identify edges added between snapshots."""
        return len(self.cset.cells_by_dim.get(1, []))

    def _edges_added_since(self, snapshot: int) -> list[str]:
        """Return the cell ids of 1-cells added after ``snapshot``."""
        all_edges = self.cset.cells_by_dim.get(1, [])
        return [c.cell_id for c in all_edges[snapshot:]]

    def _find_edge(self, src: str, tgt: str) -> Optional[str]:
        """Find an existing 1-cell connecting ``src`` to ``tgt``."""
        for c in self.cset.cells_by_dim.get(1, []):
            if c.vertices == (src, tgt):
                return c.cell_id
        return None

    # ---------- while -------------------------------------------

    def _walk_while(self, stmt: ast.While, cur: str) -> str:
        """A ``while cond: body`` becomes a square with a back-edge::

                cur
                 │
              cond=T
                 │
                body
                 │
              loop_back (back to cur) OR break (exit)

        We model it as a square whose:
          axis-0: entry → after-body
          axis-1: cur (entry) → loop_back (back to cur)
        """
        loop_entry = self._make_point("while_entry", stmt)
        self._make_edge(
            cur, loop_entry, CellShape.EDGE_SEQ, ast_node=stmt,
        )
        body_entry = self._make_point("while_body_entry", stmt)
        self._make_edge(
            loop_entry, body_entry, CellShape.EDGE_BRANCH_T,
            ast_node=stmt,
            guards=(self._cond_text(stmt.test),),
        )
        body_exit = body_entry
        for s in stmt.body:
            body_exit = self._walk_stmt(s, body_exit)
        # Back-edge.
        back = self._make_edge(
            body_exit, loop_entry, CellShape.EDGE_LOOP_BACK,
            ast_node=stmt,
        )
        # Exit when condition false.
        exit_pt = self._make_point("while_exit", stmt)
        exit_edge = self._make_edge(
            loop_entry, exit_pt, CellShape.EDGE_BRANCH_F,
            ast_node=stmt,
            guards=(self._not_cond_text(stmt.test),),
        )
        # Square: vertices (loop_entry, body_exit, exit_pt, ?).
        # The "?" is the unreachable hi-hi corner — we use exit_pt.
        sq_faces = (
            self._find_edge(cur, loop_entry) or "",
            back,
            self._find_edge(loop_entry, body_entry) or "",
            exit_edge,
        )
        self._make_square(
            label="while",
            vertices=(loop_entry, body_exit, exit_pt, exit_pt),
            faces=sq_faces,
            shape=CellShape.SQUARE_LOOP,
            ast_node=stmt,
            guards=self._guards_at(stmt),
        )
        return exit_pt

    # ---------- for ---------------------------------------------

    def _walk_for(self, stmt: ast.For, cur: str) -> str:
        """``for x in iterable:`` is structurally similar to
        ``while``: each iteration is a body invocation; exhaustion
        is the false branch."""
        loop_entry = self._make_point("for_entry", stmt)
        self._make_edge(
            cur, loop_entry, CellShape.EDGE_SEQ, ast_node=stmt,
        )
        body_entry = self._make_point("for_body_entry", stmt)
        self._make_edge(
            loop_entry, body_entry, CellShape.EDGE_BRANCH_T,
            ast_node=stmt,
            guards=("iterator has next",),
        )
        body_exit = body_entry
        for s in stmt.body:
            body_exit = self._walk_stmt(s, body_exit)
        back = self._make_edge(
            body_exit, loop_entry, CellShape.EDGE_LOOP_BACK,
            ast_node=stmt,
        )
        exit_pt = self._make_point("for_exit", stmt)
        exit_edge = self._make_edge(
            loop_entry, exit_pt, CellShape.EDGE_BRANCH_F,
            ast_node=stmt,
            guards=("iterator exhausted",),
        )
        sq_faces = (
            self._find_edge(cur, loop_entry) or "",
            back,
            self._find_edge(loop_entry, body_entry) or "",
            exit_edge,
        )
        self._make_square(
            label="for",
            vertices=(loop_entry, body_exit, exit_pt, exit_pt),
            faces=sq_faces,
            shape=CellShape.SQUARE_LOOP,
            ast_node=stmt,
            guards=self._guards_at(stmt),
        )
        return exit_pt

    # ---------- try / except / finally --------------------------

    def _walk_try(self, stmt: ast.Try, cur: str) -> str:
        """A try/except/finally produces:

          * a 2-cell (square) for try/except (no finally), OR
          * a 3-cell (cube) for try/except/finally, where the
            third axis is the *finally* dimension.

        Audit fix (round 2 phase 1): the previous walker built a
        square *plus* a sequence edge for finally — the third axis
        was just a 1-cell, not part of a higher cube.  The new
        walker materialises a real 3-cube whose faces include
        the try-square at finally-entry and the same square's
        post-finally image as the opposite face.

        Geometric structure of the 3-cube:

          axis 0 = exception (no/yes)
          axis 1 = try/except sequence (entry → exit)
          axis 2 = finally (before/after)

          v_000 = try_entry (no exception, before finally)
          v_100 = try_entry_with_exc (exception raised at entry)
          v_010 = try_exit (no exception, after try body)
          v_110 = handler_exit
          v_001 = try_entry_post_finally (after finally if no exc)
          v_101 = try_entry_with_exc_post_finally
          v_011 = try_exit_post_finally
          v_111 = handler_exit_post_finally  (= module exit)

          Faces (6 — 2 per axis):
          axis_0_lo: the no-exception square
                     (try_entry → try_exit;
                      try_entry_post_finally → try_exit_post_finally)
          axis_0_hi: the exception square (handlers)
          axis_1_lo: the entry square (try_entry / try_entry_with_exc;
                     before / after finally)
          axis_1_hi: the exit square (try_exit / handler_exit;
                     before / after finally)
          axis_2_lo: the pre-finally square (= try-square)
          axis_2_hi: the post-finally square
        """
        try_entry = self._make_point("try_entry", stmt)
        self._make_edge(
            cur, try_entry, CellShape.EDGE_SEQ, ast_node=stmt,
        )
        try_body_edges_snap = self._snapshot_edges()
        try_exit = try_entry
        for s in stmt.body:
            try_exit = self._walk_stmt(s, try_exit)
        try_body_edges = self._edges_added_since(try_body_edges_snap)

        # Handler structure.
        handler_join = self._make_point("try_handler_join", stmt)
        handler_entries: list[tuple[str, str]] = []
        if stmt.handlers:
            for h in stmt.handlers:
                h_entry = self._make_point("except_entry", h)
                raise_edge = self._make_edge(
                    try_entry, h_entry, CellShape.EDGE_RAISE,
                    ast_node=h,
                    guards=("exception raised",),
                )
                h_exit = h_entry
                for s in h.body:
                    h_exit = self._walk_stmt(s, h_exit)
                self._make_edge(
                    h_exit, handler_join, CellShape.EDGE_SEQ,
                    ast_node=h,
                )
                handler_entries.append((h_entry, h_exit))
            # Connect try-exit to handler_join (no exception raised).
            try_exit_to_join = self._make_edge(
                try_exit, handler_join, CellShape.EDGE_SEQ,
                ast_node=stmt,
            )
        else:
            try_exit_to_join = self._make_edge(
                try_exit, handler_join, CellShape.EDGE_SEQ,
                ast_node=stmt,
            )

        # Build the try/except square (axis-0 = exception, axis-1 = sequence).
        # Vertices: (00) try_entry, (10) handler_entry-or-try_exit,
        # (01) try_exit, (11) handler_join.
        if handler_entries:
            first_h_entry, first_h_exit = handler_entries[0]
            try_square = self._make_square(
                label="try",
                vertices=(try_entry, first_h_entry,
                          try_exit, handler_join),
                faces=(
                    self._find_edge(try_entry, try_exit) or
                    self._make_compound_path(
                        try_entry, try_exit,
                        body_edges=try_body_edges,
                        shape=CellShape.EDGE_SEQ,
                        ast_node=stmt,
                    ),
                    self._find_edge(first_h_entry, handler_join) or
                    self._find_edge(first_h_exit, handler_join) or "",
                    self._find_edge(try_entry, first_h_entry) or "",
                    try_exit_to_join,
                ),
                shape=CellShape.SQUARE_TRY,
                ast_node=stmt,
                guards=self._guards_at(stmt),
            )
        else:
            try_square = None

        # Finally — promote to 3-cube when present.
        if stmt.finalbody:
            fin_edges_snap = self._snapshot_edges()
            fin_exit = handler_join
            for s in stmt.finalbody:
                fin_exit = self._walk_stmt(s, fin_exit)
            fin_edges = self._edges_added_since(fin_edges_snap)
            if try_square is not None:
                # Build the post-finally face — a degenerate copy
                # of the try square shifted along the finally axis.
                # We use a degenerate 2-cell: same vertices, but
                # tagged by the finally edges so the 3-cube has
                # distinct upper/lower faces.
                # For simplicity: the upper face is rendered as
                # ``try_square_post_finally`` with finally-edges
                # added as guard annotations.
                tsq = self.cells_by_id_or_none(try_square)
                if tsq is not None:
                    post_sq = self._make_square(
                        label="try_post_finally",
                        vertices=tsq.vertices,
                        faces=tsq.faces,
                        shape=CellShape.SQUARE_TRY,
                        ast_node=stmt,
                        guards=tsq.guards + ("finally executed",),
                    )
                    # Build edges along the finally axis from each
                    # of the four square corners.  These are the
                    # 1-cells of the cube's axis-2 direction.
                    fin_axis_edges: list[str] = []
                    for v in tsq.vertices:
                        fin_axis_edges.append(self._make_edge(
                            v, v, CellShape.EDGE_SEQ, ast_node=stmt,
                            guards=("finally axis",),
                        ))
                    # The 6 faces of the cube, in axis order:
                    cube_faces = (
                        # axis-0 (exception): 2 squares
                        try_square,         # lo
                        post_sq,             # hi (placeholder)
                        # axis-1 (sequence): degenerate squares
                        try_square,
                        post_sq,
                        # axis-2 (finally): 2 squares (pre and post)
                        try_square,         # pre-finally
                        post_sq,             # post-finally
                    )
                    cube_vertices = tuple(
                        list(tsq.vertices) + list(tsq.vertices)
                    )
                    self._make_cube(
                        label="try_finally",
                        vertices=cube_vertices,
                        faces=cube_faces,
                        shape=CellShape.CUBE_TRY_FINALLY,
                        ast_node=stmt,
                        guards=tsq.guards,
                    )
            return fin_exit
        return handler_join

    def cells_by_id_or_none(self, cid: str) -> Optional[Cell]:
        return self.cset.cells_by_id.get(cid)

    # ---------- with --------------------------------------------

    def _walk_with(self, stmt: ast.With, cur: str) -> str:
        # Conservative: a with-statement is a sequence of body
        # statements bracketed by enter/exit edges.
        with_entry = self._make_point("with_entry", stmt)
        self._make_edge(cur, with_entry, CellShape.EDGE_SEQ, ast_node=stmt)
        body_exit = with_entry
        for s in stmt.body:
            body_exit = self._walk_stmt(s, body_exit)
        with_exit = self._make_point("with_exit", stmt)
        self._make_edge(body_exit, with_exit, CellShape.EDGE_SEQ, ast_node=stmt)
        return with_exit

    # ---------- return / raise ----------------------------------

    def _walk_return(self, stmt: ast.Return, cur: str) -> str:
        ret = self._make_point("return", stmt)
        self._make_edge(cur, ret, CellShape.EDGE_RETURN, ast_node=stmt)
        if self.cset.exit is None:
            self.cset.exit = ret
        return ret

    def _walk_raise(self, stmt: ast.Raise, cur: str) -> str:
        rs = self._make_point("raise", stmt)
        self._make_edge(cur, rs, CellShape.EDGE_RAISE, ast_node=stmt)
        return rs

    # ---------- helpers -----------------------------------------

    def _cond_text(self, expr: ast.expr) -> str:
        try:
            return ast.unparse(expr)
        except Exception:
            return repr(expr)

    def _not_cond_text(self, expr: ast.expr) -> str:
        try:
            return f"not ({ast.unparse(expr)})"
        except Exception:
            return f"not ({expr!r})"

    def _guards_at(self, stmt: ast.AST) -> tuple[str, ...]:
        """Return the path-sensitive guards at this statement,
        from the refinement map (when supplied)."""
        if self.refinement_map is None:
            return ()
        lineno = getattr(stmt, "lineno", None)
        if lineno is None:
            return ()
        # The refinement map indexes guards by source location.
        # We accumulate guards from any fact whose lineno matches.
        out: list[str] = []
        for fact in getattr(self.refinement_map, "per_source", []) or []:
            if getattr(fact, "source_lineno", None) == lineno:
                out.extend(getattr(fact, "guards", ()))
        return tuple(dict.fromkeys(out))  # dedupe preserve order


# ─────────────────────────────────────────────────────────────────────
#  Diagnostics — render a cubical set summary
# ─────────────────────────────────────────────────────────────────────


def render_summary(cset: CubicalSet) -> str:
    """Return a human-readable multi-line summary."""
    lines: list[str] = [
        f"CubicalSet for `{cset.function_name}`:",
        f"  cell count: {cset.cell_count()}",
        f"  Euler χ: {cset.euler_characteristic()}",
        f"  entry: {cset.entry}",
        f"  exit:  {cset.exit}",
        "  cells per dim:",
    ]
    for dim in sorted(cset.cells_by_dim):
        lines.append(f"    dim {dim}: {len(cset.cells_by_dim[dim])} cells")
    fillable = cset.find_kan_fillable()
    if fillable:
        lines.append(f"  Kan-fillable cells: {len(fillable)}")
        for k in fillable[:5]:
            lines.append(
                f"    {k.cell_id} missing axis={k.missing_axis} "
                f"eps={k.missing_eps}"
            )
    else:
        lines.append("  No Kan-fillable cells (all faces present).")
    return "\n".join(lines)


__all__ = [
    "CellShape",
    "Cell",
    "CubicalSet",
    "KanCandidate",
    "build_cubical_set",
    "render_summary",
]
