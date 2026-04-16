/-
  C4/Syntax.lean
  Deep syntactic embedding of the C⁴ core fragment.

  We embed the novel C⁴ rules (refinement types, fiber restriction,
  descent) as a deep inductive type.  Variables are represented using
  De Bruijn indices.  The CIC and cubical fragments are axiomatized
  (they are studied in the established literature).

  Fragment covered:
  - Sorts (Prop, Type n)
  - Π-types and λ-abstractions
  - Refinement types {x : A | φ(x)}
  - Fiber restriction t|_φ
  - Descent fill(cover, {t_α}, {p_αβ})
  - Path types and transport (represented abstractly)
-/
import C4.Basic

namespace C4.Syntax

-- ── De Bruijn indices ──────────────────────────────────────────
abbrev Idx := Nat

-- ── Types (pre-types) ──────────────────────────────────────────
inductive Ty : Type where
  | sort    : Sort' → Ty                      -- Prop, Type n
  | pi      : Ty → Ty → Ty                   -- Π(x:A).B
  | sigma   : Ty → Ty → Ty                   -- Σ(x:A).B
  | path    : Ty → Tm → Tm → Ty             -- Path_A a b
  | refin   : Ty → (Tm → Bool) → Ty         -- {x:A | φ(x)} (φ decidable)
  | descent : List Ty → Ty → Ty             -- descent type (fibered)
  | nat     : Ty                              -- base type: natural numbers
  | bool    : Ty                              -- base type: booleans
  deriving Repr

-- ── Terms ─────────────────────────────────────────────────────
inductive Tm : Type where
  | var     : Idx → Tm                        -- De Bruijn variable
  | sort    : Sort' → Tm                      -- universe as term
  | lam     : Ty → Tm → Tm                   -- λ(x:A).t
  | app     : Tm → Tm → Tm                   -- f u
  | pair    : Tm → Tm → Tm                   -- (t, u)
  | fst     : Tm → Tm                         -- π₁ p
  | snd     : Tm → Tm                         -- π₂ p
  | refinI  : Ty → Tm → Tm → Tm            -- ⟨a, h⟩_φ (intro)
  | refinE  : Tm → Tm                         -- r.1 (elim)
  | refl    : Tm → Tm                         -- refl a
  | restr   : Tm → (Tm → Bool) → Tm         -- t|_φ (restriction)
  | desc    : List Tm → List Tm → Tm        -- fill({t_α}, {p_αβ})
  | transp  : Tm → Tm → Tm                   -- transport
  -- Base type literals
  | zero    : Tm                               -- 0 : Nat
  | succ    : Tm → Tm                         -- S n : Nat
  | btrue   : Tm                               -- true : Bool
  | bfalse  : Tm                               -- false : Bool
  | propTrue  : Tm                             -- ⊤ : Prop
  | propFalse : Tm                             -- ⊥ : Prop
  deriving Repr

-- ── Contexts ──────────────────────────────────────────────────
abbrev Ctx := List Ty

-- ── Shifting (De Bruijn index management) ─────────────────────

/-- Shift all free variables in a term by d starting from cutoff c. -/
def Tm.shift (t : Tm) (d : Int) (c : Nat := 0) : Tm :=
  match t with
  | .var k       => if k >= c then .var (k + d.toNat) else .var k
  | .sort s      => .sort s
  | .lam A body  => .lam A (body.shift d (c + 1))
  | .app f u     => .app (f.shift d c) (u.shift d c)
  | .pair a b    => .pair (a.shift d c) (b.shift d c)
  | .fst p       => .fst (p.shift d c)
  | .snd p       => .snd (p.shift d c)
  | .refinI A a h => .refinI A (a.shift d c) (h.shift d c)
  | .refinE r    => .refinE (r.shift d c)
  | .refl a      => .refl (a.shift d c)
  | .restr t' φ  => .restr (t'.shift d c) φ
  | .desc ts ps  => .desc (ts.map (·.shift d c)) (ps.map (·.shift d c))
  | .transp p t' => .transp (p.shift d c) (t'.shift d c)
  | .zero        => .zero
  | .succ n      => .succ (n.shift d c)
  | .btrue       => .btrue
  | .bfalse      => .bfalse
  | .propTrue    => .propTrue
  | .propFalse   => .propFalse

/-- Substitute term s for De Bruijn variable 0 in t. -/
def Tm.subst (t : Tm) (s : Tm) (k : Nat := 0) : Tm :=
  match t with
  | .var n       => if n == k then s.shift (Int.ofNat k)
                   else if n > k then .var (n - 1)
                   else .var n
  | .sort u      => .sort u
  | .lam A body  => .lam A (body.subst (s.shift 1) (k + 1))
  | .app f u     => .app (f.subst s k) (u.subst s k)
  | .pair a b    => .pair (a.subst s k) (b.subst s k)
  | .fst p       => .fst (p.subst s k)
  | .snd p       => .snd (p.subst s k)
  | .refinI A a h => .refinI A (a.subst s k) (h.subst s k)
  | .refinE r    => .refinE (r.subst s k)
  | .refl a      => .refl (a.subst s k)
  | .restr t' φ  => .restr (t'.subst s k) φ
  | .desc ts ps  => .desc (ts.map (·.subst s k)) (ps.map (·.subst s k))
  | .transp p t' => .transp (p.subst s k) (t'.subst s k)
  | .zero        => .zero
  | .succ n      => .succ (n.subst s k)
  | .btrue       => .btrue
  | .bfalse      => .bfalse
  | .propTrue    => .propTrue
  | .propFalse   => .propFalse

end C4.Syntax
