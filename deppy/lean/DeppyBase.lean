/-
DeppyBase.lean — meta-theory and tactic library for deppy certificates.

This file is shipped with deppy and prepended to every Lean
certificate emitted by ``deppy obligations`` / ``deppy check
--certificate``.  It encodes the *Python runtime safety*
meta-theory in Lean and provides automation tactics so most
obligations close themselves without user intervention.

Everything here is conservative — it only adds *definitions* and
*lemmas*; we never declare new axioms beyond the obvious ones the
type translator produces (one per opaque user class).  Soundness is
therefore identical to plain Lean's metatheory.
-/

namespace Deppy

/-! ## Core safety predicates

The Python pipeline emits canonical safety predicates in Python
syntax (e.g. ``(b) != 0`` for ``ZeroDivisionError`` on ``a / b``).
The translator maps each form to one of these Lean predicates so
the user can write proofs against named Props rather than
hand-translating each obligation.
-/

/-- ``a / b`` is safe iff ``b ≠ 0``. -/
def DivSafe (b : Int) : Prop := b ≠ 0

/-- ``xs[i]`` is safe iff ``i`` is in bounds. -/
def IndexSafe {α} (xs : List α) (i : Int) : Prop :=
  0 ≤ i ∧ i < xs.length

/-- ``d[k]`` (dict access) is safe iff ``k`` is a key of ``d``. -/
def KeySafe {α β} (d : Std.HashMap α β) (k : α) : Prop :=
  d.contains k = true

/-- ``getattr(o, n)`` is safe iff the object has the attribute. -/
def AttrSafe (P : Prop) : Prop := P

/-- ``next(it)`` is safe iff the iterator has a next element.  Stays
opaque until the user supplies a model of the iterator. -/
def NextSafe (P : Prop) : Prop := P

/-- A generic "this expression cannot raise" predicate the
pipeline emits when no canonical predicate applies.  The body is the
exact safety predicate the analyzer extracted, so Lean must prove
the same Prop the user would have proved manually. -/
def Safe (P : Prop) : Prop := P


/-! ## Optional / Maybe helpers

The type translator turns ``Optional[T]`` into Lean's ``Option T``.
These lemmas / definitions cover the common safety-predicate
shapes that arise after a None-check.
-/

/-- An Optional value is "usable" iff it is ``some``.  Aliases
``Option.isSome``. -/
@[simp] def Some? {α} (x : Option α) : Prop := x.isSome

theorem some_neq_none {α} (x : α) : (Option.some x) ≠ Option.none := by
  intro h; cases h

/-! ## Automation tactic combinator

``deppy_safe`` tries (in order) the strongest tactics Lean has for
runtime-safety obligations: ``decide`` (decidable propositions),
``omega`` (linear integer arithmetic), ``simp`` (normalisation),
``tauto`` (propositional logic), and ``aesop`` (general).  The
combinator falls through silently — when no tactic closes the goal
the user is told and can refine.
-/

macro "deppy_safe" : tactic => `(tactic| (
  first
  | decide
  | omega
  | simp_all
  | tauto
  | aesop
  | rfl
))

/-! ## Bridge from Z3 to Lean

When the deppy pipeline discharged a predicate via Z3, it asks the
emitter to use ``by omega`` (Z3's linear arithmetic ≈ omega's
territory).  When Z3 disagreed and the user has not supplied a
manual proof, the emitter writes ``by sorry`` — which Lean rejects,
giving the user a clear signal.

There's nothing to define here; ``omega`` is built into Lean.
The presence of this section in the certificate makes the
correspondence explicit.
-/

end Deppy
