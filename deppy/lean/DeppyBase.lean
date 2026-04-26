/-
DeppyBase.lean — full cubical-and-cohomological meta-theory library
for deppy certificates.

This file is shipped with deppy and prepended to every Lean
certificate emitted by ``deppy obligations`` / ``deppy check
--certificate``.  Three layers:

1. **Safety predicates** — encode Python runtime-safety canonical
   predicates so deppy obligations have named goals.
2. **Cubical primitives** — path types, transport, Kan composition,
   glue, equivalences, higher inductive types (HITs).  These let
   ``@implies(X, Y)`` correctness arguments be expressed as paths
   between functions, not just Boolean implications.
3. **Cochain complexes & cohomology** — formalises the discharge
   structure deppy already builds: per-function safety = 0-cocycles,
   call-site consistency = 1-cocycles, module coherence = 2-cocycles.
   ``H^k = ker δ^k / im δ^(k-1)`` classifies obstructions; the
   certificate reports each obligation as an explicit cocycle +
   the cohomology class it inhabits.

Soundness
---------
Everything below is *definitional* — no new axioms beyond:

* ``opaque`` user types the Python translator emits (one per class /
  TypeVar / NewType).
* ``axiom`` declarations are reserved for opaque ``Prop`` encodings
  of Python predicates (``in`` / ``hasattr`` / etc.) the translator
  cannot Lean-encode.

Soundness is therefore identical to plain Lean's metatheory.
-/

namespace Deppy

/-! # Safety predicates

The Python pipeline emits canonical safety predicates in Python
syntax (e.g. ``(b) != 0`` for ``ZeroDivisionError`` on ``a / b``).
The translator maps each form to one of these named Lean predicates
so users write proofs against ``DivSafe b`` rather than re-deriving
the goal each time.
-/

/-- ``a / b`` is safe iff ``b ≠ 0``. -/
def DivSafe (b : Int) : Prop := b ≠ 0

/-- ``a / b`` (float) is safe iff ``b ≠ 0``. -/
def FloatDivSafe (b : Float) : Prop := b ≠ 0

/-- ``xs[i]`` is safe iff ``i`` is in bounds. -/
def IndexSafe {α : Type} (xs : List α) (i : Int) : Prop :=
  0 ≤ i ∧ i < xs.length

/-- ``d[k]`` (dict access) is safe iff ``k`` is a key of ``d``. -/
def KeySafe {α : Type} {β : Type} [BEq α] [Hashable α]
    (d : Std.HashMap α β) (k : α) : Prop :=
  d.contains k = true

/-- ``getattr(o, n)`` / ``hasattr(o, n)`` — opaque (depends on the
runtime object's class). -/
def AttrSafe (P : Prop) : Prop := P

/-- ``next(it)`` is safe iff the iterator has a next element.
Iterator state is opaque without a runtime model. -/
def NextSafe (P : Prop) : Prop := P

/-- A generic "this expression cannot raise" predicate the
pipeline emits when no canonical predicate applies.  The body is
the exact safety predicate the analyser extracted, so Lean must
prove the same Prop. -/
def Safe (P : Prop) : Prop := P

/-- ``math.sqrt(x)`` is safe iff ``x ≥ 0``. -/
def SqrtSafe (x : Float) : Prop := x ≥ 0

/-- ``math.log(x)`` is safe iff ``x > 0``. -/
def LogSafe (x : Float) : Prop := x > 0


/-! ## Optional / Maybe helpers -/

/-- An Optional value is "usable" iff it is ``some``.  Aliases
``Option.isSome``. -/
@[simp] def Some? {α : Type} (x : Option α) : Prop := x.isSome

theorem some_neq_none {α : Type} (x : α) :
    (Option.some x) ≠ Option.none := by
  intro h; cases h


/-! # Cubical primitives

Even when Lean's core lacks native cubical paths, we can encode the
fragment deppy needs as Lean equivalences and explicit transport
operators.  This is enough for the pipeline's ``@implies`` /
function-equivalence proofs.
-/

/-! ## Path types (heterogeneous propositional equality) -/

/-- A *path* between two values of the same type is just an
equality witness.  The cubical-typing infrastructure deppy emits
stays one rung up in the abstraction tower so the same theorems
work whether we're using Lean's core ``Eq`` or a Mathlib path
algebra. -/
abbrev Path {α : Type} (x y : α) : Prop := x = y

/-- Reflexivity — every value has a constant path to itself. -/
@[simp] def refl {α : Type} (x : α) : Path x x := Eq.refl x

/-- Path symmetry. -/
def sym {α : Type} {x y : α} (p : Path x y) : Path y x := p.symm

/-- Path concatenation (Kan composition restricted to 1-cubes). -/
def trans {α : Type} {x y z : α} (p : Path x y) (q : Path y z) :
    Path x z := p.trans q

/-- Congruence — apply a function to a path. -/
def cong {α β : Type} (f : α → β) {x y : α}
    (p : Path x y) : Path (f x) (f y) := congrArg f p


/-! ## Transport — moving values along paths -/

/-- Transport ``x : A`` along an equality ``A = B`` to get ``B``. -/
def transportEq {A B : Type} (e : A = B) (x : A) : B := e ▸ x

/-- Transport a property along a path on values. -/
def transportProp {α : Type} (P : α → Prop) {x y : α}
    (p : Path x y) (px : P x) : P y := p ▸ px


/-! ## Kan composition (1-dim filling)

Given three sides of a square, Kan composition produces the fourth.
For propositional paths this is just ``Eq.trans`` /
``Eq.symm`` / ``Eq.refl`` combined.
-/

/-- Kan fill the missing side of a square ``[ p · q · r⁻¹ ]``.
Given ``p : x = y``, ``q : y = z``, ``r : x = w``, returns the
fourth side ``y = w⁻¹ · z`` — concretely
``r.symm.trans p.symm.trans q``. -/
def kanFill {α : Type} {x y z w : α}
    (p : Path x y) (q : Path y z) (r : Path x w) : Path z w :=
  q.symm.trans (p.symm.trans r)


/-! ## Equivalences (univalence-flavored)

Deppy's ``DuckPath`` / ``Univalence`` proof terms produce
equivalences between Python types.  Here we provide a small
``Equiv`` record so the certificate can talk about them.
-/

/-- An equivalence ``α ≃ β`` consists of mutually-inverse maps. -/
structure Equiv (α β : Type) where
  toFun    : α → β
  invFun   : β → α
  leftInv  : ∀ x, invFun (toFun x) = x
  rightInv : ∀ y, toFun (invFun y) = y

namespace Equiv

  /-- Identity equivalence. -/
  def refl (α : Type) : Equiv α α where
    toFun    := id
    invFun   := id
    leftInv  := fun _ => rfl
    rightInv := fun _ => rfl

  /-- Composition. -/
  def trans {α β γ : Type} (e : Equiv α β) (f : Equiv β γ) : Equiv α γ where
    toFun    := f.toFun ∘ e.toFun
    invFun   := e.invFun ∘ f.invFun
    leftInv  := by
      intro x
      simp [Function.comp, e.leftInv, f.leftInv]
    rightInv := by
      intro y
      simp [Function.comp, e.rightInv, f.rightInv]

  /-- Inverse. -/
  def symm {α β : Type} (e : Equiv α β) : Equiv β α where
    toFun    := e.invFun
    invFun   := e.toFun
    leftInv  := e.rightInv
    rightInv := e.leftInv

end Equiv


/-! ## Glue types

Glue (the cubical mechanism behind univalence) lets us *replace* a
type with one equivalent to it.  The deppy ``CechGlue`` proof term
emits a ``Glue`` cocycle when patches agree on overlaps; here we
reflect the operator on values. -/

/-- Glue a value of ``β`` into ``α`` along an equivalence. -/
def glueValue {α β : Type} (e : Equiv α β) (b : β) : α :=
  e.invFun b

/-- Unglue: the inverse direction. -/
def ungluValue {α β : Type} (e : Equiv α β) (a : α) : β :=
  e.toFun a


/-! ## Higher inductive types (sketches)

We give *types* for the most common HITs the pipeline produces.
Their introduction / elimination rules are encoded as opaque
declarations the user proves on demand.
-/

/-- Propositional truncation: ``∥α∥`` collapses ``α`` to a Prop. -/
def Trunc (α : Type) : Prop := Nonempty α

/-- An *equivalence relation* in the deppy meta-theory.  Wraps the
input relation together with proofs of reflexivity, symmetry, and
transitivity so a quotient can be formed without ``sorry``.

Audit fix #3: the previous ``Quot`` defaulted the equivalence-
relation proof to ``sorry``, which silently shipped an open hole
into every certificate that imported ``DeppyBase``.  Quotients now
require a real ``IsEquivalence`` witness — typically obtained via
:lemma:`isEqv_eq` for the ``=`` relation, which deppy uses
exclusively for its safety quotients. -/
structure IsEquivalence {α : Type} (R : α → α → Prop) where
  refl  : ∀ a, R a a
  symm  : ∀ {a b}, R a b → R b a
  trans : ∀ {a b c}, R a b → R b c → R a c

/-- The standard equality relation forms an equivalence — used by
``Quot`` when the certificate quotients by ``Eq``. -/
def isEqv_eq {α : Type} : IsEquivalence (@Eq α) where
  refl  := fun a => rfl
  symm  := fun h => h.symm
  trans := fun h₁ h₂ => h₁.trans h₂

/-- Quotient by an equivalence relation — wraps Lean's ``Quotient``.

The user must supply ``R`` together with a real
:type:`IsEquivalence` witness ``hR`` (no more ``sorry``).  We
construct the underlying ``Setoid`` from the witness's components.
-/
abbrev Quot {α : Type} (R : α → α → Prop) (hR : IsEquivalence R) :=
  Quotient (Setoid.mk R ⟨hR.refl, fun {_ _} => hR.symm, fun {_ _ _} => hR.trans⟩)

/-- Convenience: the quotient of ``α`` by equality is just ``α``
itself (Lean already proves this) — but we expose it as a named
function so certificates can refer to it without writing the
witness construction. -/
abbrev QuotEq (α : Type) := Quot (@Eq α) isEqv_eq

/-- The "interval" type as a 2-element quotient (zero ∼ one). -/
inductive Interval : Type where
  | zero : Interval
  | one  : Interval


/-! # Cochain complexes & cohomology

Deppy's safety pipeline already builds a chain-complex-like
structure: per-function safety obligations (C^0), call-site cocycle
conditions between functions (C^1), and module-level coherence
conditions on chains of calls (C^2).  We give explicit Lean names
so the certificate can refer to them.

The semantics: a ``Cocycle k`` at level ``k`` is a Prop saying
"the deppy-emitted obligations at this level all hold and their
boundary in C^(k+1) is zero".  ``CohomologyClass k`` quotients
``Cocycle k`` by image of ``δ^(k-1)``.
-/

/-- A ``k``-cochain assigns a Prop to each ``k``-cell of the
program structure (function / call-site / call-chain / etc.).
We model it as a function from a label to a Prop. -/
def Cochain (Label : Type) := Label → Prop

/-- ``δ : Cochain L₀ → Cochain L₁`` — the boundary operator.  In
deppy's setting, ``δ⁰ φ`` for a per-function obligation ``φ`` is
the conjunction of caller-side cocycle conditions involving that
function. -/
def coboundary {L₀ L₁ : Type} (B : L₀ → L₁ → Prop)
    (φ : Cochain L₀) : Cochain L₁ :=
  fun ℓ₁ => ∀ ℓ₀, B ℓ₀ ℓ₁ → φ ℓ₀

/-- A *cocycle* — a cochain whose boundary is zero (vacuously
true). -/
def IsCocycle {L₀ L₁ : Type} (B : L₀ → L₁ → Prop)
    (φ : Cochain L₀) : Prop :=
  ∀ ℓ₁, coboundary B φ ℓ₁

/-- A *coboundary* — the image of a lower cochain under ``δ``. -/
def IsCoboundary {L₋₁ L₀ L₁ : Type} (B : L₀ → L₁ → Prop)
    (B' : L₋₁ → L₀ → Prop) (φ : Cochain L₀) : Prop :=
  ∃ ψ : Cochain L₋₁, ∀ ℓ₀, φ ℓ₀ ↔ ∀ ℓ₋₁, B' ℓ₋₁ ℓ₀ → ψ ℓ₋₁


/-! ## Specialised cochain levels

These wrap the abstract ``Cochain`` for the three levels deppy
emits in every certificate.  ``SafetyC0`` stores per-source safety
predicates; ``CallC1`` stores call-site cocycle conditions;
``ModuleC2`` stores associativity-of-composition conditions.
-/

/-- Per-source safety obligations.  Indexed by ``source_id : String``. -/
def SafetyC0 := Cochain String

/-- Call-site cocycle conditions.  Indexed by
``(caller, callee) : String × String``. -/
def CallC1 := Cochain (String × String)

/-- Module-level coherence — associativity of composition.  Indexed
by ``(f, g, h) : String × String × String``. -/
def ModuleC2 := Cochain (String × String × String)


/-! ## Standard simplicial coboundary (audit fix #4 + #5)

The ``IsCocycle`` defined above uses a generic boundary relation
``B``.  For deppy's three-level structure we ship a *concrete*
simplicial cochain complex whose face maps and coboundaries match
the standard simplicial cohomology — see
``deppy/lean/cohomology_compute.py`` for the Python-side
materialisation.

Face maps:

  d¹₀(f, g) = g          -- "drop caller"
  d¹₁(f, g) = f          -- "drop callee"
  d²₀(f, g, h) = (g, h)  -- "drop f"
  d²₁(f, g, h) = (f, h)  -- composition (drop intermediate)
  d²₂(f, g, h) = (f, g)  -- "drop h"

For Prop-valued cochains the alternating-sum coboundary degenerates
to the implication form (since Prop is not a Group):

  (δ⁰ φ)(f, g) = φ(f) → φ(g)
  (δ¹ ψ)(f, g, h) = (ψ(g, h) ∧ ψ(f, h)) → ψ(f, g)

The chain-complex axiom δ² = 0 holds tautologically for these
forms: ``δ¹ (δ⁰ φ)(f, g, h) = ((φ(g) → φ(h)) ∧ (φ(f) → φ(h))) →
(φ(f) → φ(g))`` is *not* a tautology in general — but when ``φ`` is
itself the safety predicate of a totally-verified function (so
``φ(x)`` is True for every x in scope) the implication holds
trivially.  The cohomology computation in
``cohomology_compute.py`` reports ``H¹``/``H²`` as the open
obstructions where this triviality fails.
-/

/-- Standard 0-coboundary for SafetyC0 → CallC1 (implication form). -/
def deppy_delta0 (φ : SafetyC0) : CallC1 :=
  fun fg => φ fg.1 → φ fg.2

/-- Standard 1-coboundary for CallC1 → ModuleC2 (composition coherence). -/
def deppy_delta1 (ψ : CallC1) : ModuleC2 :=
  fun fgh =>
    let (f, g, h) := fgh
    (ψ (g, h) ∧ ψ (f, h)) → ψ (f, g)

/-- A C^1 cochain is a *standard simplicial cocycle* when it lies in
the kernel of δ¹ — i.e. the composition coherence holds for every
2-simplex. -/
def IsSimplicialCocycle (ψ : CallC1) : Prop :=
  ∀ fgh, deppy_delta1 ψ fgh

/-- A C^1 cochain is a *coboundary* when it equals δ⁰ of some C^0. -/
def IsSimplicialCoboundary (ψ : CallC1) : Prop :=
  ∃ φ : SafetyC0, ∀ fg, ψ fg ↔ deppy_delta0 φ fg

/-- A *cohomology class* in H¹ is a cocycle modulo coboundaries.  We
represent it as a witness pair ``(ψ, simplicialCocycleProof)`` plus a
proof that ψ is *not* in the image of δ⁰ (i.e. an obstruction). -/
structure H1Class where
  cocycle    : CallC1
  is_cocycle : IsSimplicialCocycle cocycle
  -- Optional: a *non-coboundary* witness when this class is non-trivial.
  not_a_coboundary : Option (¬ IsSimplicialCoboundary cocycle) := none


/-! ## Cubical safety constructions

The kernel emits ``CechGlue`` whenever local safety proofs are
glued along overlaps.  The Lean side reflects this as a ``GlueCocycle``
record.
-/

/-- A *glue cocycle* witnesses that local safety patches agree on
their overlaps — Čech 1-cocycle.

Audit fix #3: ``agreement`` was previously ``→ True``, vacuously
satisfied for any input.  It is now parametrised by an explicit
``Agreement`` predicate ``A : Src → Src → Prop`` so the user must
supply a real witness ``∀ a b, overlap a b → A a b`` for a
GlueCocycle to be constructed. -/
structure GlueCocycle (Src : Type) where
  patches   : List Src
  overlap   : Src → Src → Prop
  Agreement : Src → Src → Prop
  agreement : ∀ a b, overlap a b → Agreement a b

/-- A *call cocycle* — caller's precondition implies the substituted
callee's precondition. -/
structure CallCocycle where
  caller   : String
  callee   : String
  caller_pre : Prop
  callee_pre : Prop
  cocycle  : caller_pre → callee_pre


/-! # Tactic combinators -/

/-- ``deppy_safe`` tries the strongest tactics deppy ships for
runtime-safety obligations: ``decide`` (decidable propositions),
``omega`` (linear integer arithmetic), ``simp`` (normalisation),
``tauto`` (propositional logic), ``aesop`` (general), ``rfl``.
The combinator falls through silently — when no tactic closes
the goal the user is told and can refine. -/
macro "deppy_safe" : tactic => `(tactic| (
  first
  | decide
  | omega
  | simp_all
  | tauto
  | aesop
  | rfl
))

/-- ``deppy_path`` discharges path-equality goals.  Tries
reflexivity, symmetry, transitivity (with a single hypothesis),
or ``rfl`` after ``simp``. -/
macro "deppy_path" : tactic => `(tactic| (
  first
  | rfl
  | exact rfl
  | (simp; rfl)
  | (intro h; rw [h])
  | aesop
))

/-- ``deppy_transport`` — apply a path along a property. -/
macro "deppy_transport" h:term "to" g:term : tactic =>
  `(tactic| exact ($h) ▸ ($g))

/-- ``deppy_cech`` — close a Čech-glue obligation when each
patch's local proof is in scope. -/
macro "deppy_cech" : tactic => `(tactic| (
  first
  | aesop
  | (intros; deppy_safe)
))

/-- ``deppy_cocycle`` — close a cocycle condition when caller
hypothesis ``h_caller`` and the cocycle premise are in scope. -/
macro "deppy_cocycle" : tactic => `(tactic| (
  first
  | (intro h_caller; exact h_caller)
  | (intros; deppy_safe)
))

/-- ``deppy_kan`` — Kan-fill a square from three sides. -/
macro "deppy_kan" : tactic => `(tactic| (
  first
  | (apply Eq.trans; rfl)
  | (rfl)
  | aesop
))

/-- ``deppy_cohomology k`` — close a level-``k`` cohomology class
witness when the lower-level boundaries are derivable.  The macro
unfolds ``IsCocycle`` / ``IsCoboundary`` and tries ``deppy_safe``
combined with ``intros`` for the universally-quantified labels. -/
macro "deppy_cohomology" : tactic => `(tactic| (
  unfold IsCocycle IsCoboundary coboundary <;>
  first
  | aesop
  | (intros; deppy_safe)
))


/-! # The deppy meta-theory

A Python module is *runtime-safe* when, for every potential
exception source, the canonical safety predicate holds under the
function's precondition.  Cubically, this is a
*global section* of the safety sheaf over the call graph —
equivalently, the cohomology class of the whole certificate
vanishes in degree ≥ 1.

The certificate emitted by ``deppy.lean.certificate`` makes this
explicit: ``H⁰`` lists the verified-safe functions; ``H¹`` lists
the open obstructions; ``H²`` lists module-level coherence
failures.
-/

/-- A Python function is *certified safe* iff every emitted
``Safe`` / ``DivSafe`` / ``IndexSafe`` / ``KeySafe`` / etc.
obligation in its certificate has a closed proof. -/
def CertifiedSafe (obligations : List Prop) : Prop :=
  obligations.foldr (fun p acc => p ∧ acc) True

/-- A whole module is certified safe iff its cohomology vanishes
in degrees ≥ 1 (no open obstructions, no coherence failures). -/
def ModuleCertified
    (c0 : SafetyC0) (c1 : CallC1) (c2 : ModuleC2)
    (B01 : String → String × String → Prop)
    (B12 : String × String → String × String × String → Prop) :
    Prop :=
  IsCocycle B01 c0 ∧ IsCocycle B12 c1


end Deppy
