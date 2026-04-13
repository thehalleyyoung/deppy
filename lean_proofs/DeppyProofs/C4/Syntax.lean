/-
  C4/Syntax.lean — C⁴ (Cohomological Calculus of Constructions) Term Language

  Defines the core syntax of the C⁴ type theory:
  - SiteObj: objects of the finite typed fiber site
  - SiteKind: classifiers for site-decorated universes
  - OTermRepr: operational term language (Python-level computations)
  - C4Term: full C⁴ term language with cubical, sheaf, and oracle extensions
-/

import Mathlib.Data.Fintype.Basic

set_option autoImplicit false

namespace C4

/-- Objects of the CCTT site — Python runtime types as a finite category. -/
inductive SiteObj where
  | TInt | TFloat | TStr | TBool | TList | TDict | TSet | TTuple | TNone | TCallable | TAny
  deriving DecidableEq, Repr, Inhabited

/-- Site kind classifiers for site-decorated universes. -/
inductive SiteKind where
  | structural   -- Z3-decidable structural properties
  | semantic     -- LLM-oracle semantic properties
  | hybrid       -- combined structural ∧ semantic
  deriving DecidableEq, Repr, Inhabited

/-- OTerm representation — operational terms for Python-level computation.
    Uses binary application instead of List to keep the inductive well-behaved. -/
inductive OTermRepr where
  | ovar : String → OTermRepr
  | olit : Int → OTermRepr
  | oop : String → OTermRepr → OTermRepr → OTermRepr  -- binary op
  | ofold : String → OTermRepr → OTermRepr → OTermRepr
  | ocase : OTermRepr → OTermRepr → OTermRepr → OTermRepr
  | oapp : OTermRepr → OTermRepr → OTermRepr
  | ofix : String → OTermRepr → OTermRepr
  | ocomp : OTermRepr → String → OTermRepr → OTermRepr
  | onil : OTermRepr  -- empty arg list / unit
  deriving DecidableEq, Repr, Inhabited

/-- The full C⁴ term language.
    descent uses a pair of Nat (count of local sections/patches) rather than List
    to keep the inductive type simple. The actual data is tracked in contexts. -/
inductive C4Term where
  | var : String → C4Term
  | universe : Nat → C4Term
  | siteUniverse : Nat → SiteKind → C4Term
  | pi : String → C4Term → C4Term → C4Term
  | lam : String → C4Term → C4Term → C4Term
  | app : C4Term → C4Term → C4Term
  | sigma : String → C4Term → C4Term → C4Term
  | pair : C4Term → C4Term → C4Term
  | fst : C4Term → C4Term
  | snd : C4Term → C4Term
  | interval : C4Term
  | i0 : C4Term
  | i1 : C4Term
  | pathType : C4Term → C4Term → C4Term → C4Term
  | pathAbs : String → C4Term → C4Term
  | pathApp : C4Term → C4Term → C4Term
  | transp : String → C4Term → C4Term → C4Term
  | restrict : C4Term → SiteObj → C4Term
  | descent : Nat → Nat → C4Term  -- desc(n_locals, n_patches)
  | oterm : OTermRepr → C4Term
  | mathlibImport : String → C4Term
  deriving DecidableEq, Repr, Inhabited

/-- Size measure for C4Term — counts constructors. -/
def C4Term.size : C4Term → Nat
  | .var _ => 1
  | .universe _ => 1
  | .siteUniverse _ _ => 1
  | .pi _ a b => 1 + a.size + b.size
  | .lam _ ty body => 1 + ty.size + body.size
  | .app fn arg => 1 + fn.size + arg.size
  | .sigma _ a b => 1 + a.size + b.size
  | .pair a b => 1 + a.size + b.size
  | .fst t => 1 + t.size
  | .snd t => 1 + t.size
  | .interval => 1
  | .i0 => 1
  | .i1 => 1
  | .pathType ty a b => 1 + ty.size + a.size + b.size
  | .pathAbs _ body => 1 + body.size
  | .pathApp p r => 1 + p.size + r.size
  | .transp _ ty base => 1 + ty.size + base.size
  | .restrict t _ => 1 + t.size
  | .descent _ _ => 1
  | .oterm _ => 1
  | .mathlibImport _ => 1

theorem C4Term.size_pos (t : C4Term) : 0 < t.size := by
  cases t <;> simp only [C4Term.size] <;> omega

/-- Count the number of descent constructors in a term. -/
def C4Term.descentCount : C4Term → Nat
  | .descent _ _ => 1
  | .pi _ a b => a.descentCount + b.descentCount
  | .lam _ ty body => ty.descentCount + body.descentCount
  | .app fn arg => fn.descentCount + arg.descentCount
  | .sigma _ a b => a.descentCount + b.descentCount
  | .pair a b => a.descentCount + b.descentCount
  | .fst t => t.descentCount
  | .snd t => t.descentCount
  | .pathType ty a b => ty.descentCount + a.descentCount + b.descentCount
  | .pathAbs _ body => body.descentCount
  | .pathApp p r => p.descentCount + r.descentCount
  | .transp _ ty base => ty.descentCount + base.descentCount
  | .restrict t _ => t.descentCount
  | _ => 0

/-- Maximum nesting depth of restrict constructors. -/
def C4Term.restrictDepth : C4Term → Nat
  | .restrict t _ => 1 + t.restrictDepth
  | .pi _ a b => max a.restrictDepth b.restrictDepth
  | .lam _ ty body => max ty.restrictDepth body.restrictDepth
  | .app fn arg => max fn.restrictDepth arg.restrictDepth
  | .sigma _ a b => max a.restrictDepth b.restrictDepth
  | .pair a b => max a.restrictDepth b.restrictDepth
  | .fst t => t.restrictDepth
  | .snd t => t.restrictDepth
  | .pathType ty a b => max (max ty.restrictDepth a.restrictDepth) b.restrictDepth
  | .pathAbs _ body => body.restrictDepth
  | .pathApp p r => max p.restrictDepth r.restrictDepth
  | .transp _ ty base => max ty.restrictDepth base.restrictDepth
  | _ => 0

/-- Lexicographic measure μ(t) = (descentCount, restrictDepth, size). -/
def C4Term.measure (t : C4Term) : Nat × Nat × Nat :=
  (t.descentCount, t.restrictDepth, t.size)

/-- A term is in the CIC fragment if it contains no restrictions, descent, oterms, or imports. -/
def C4Term.isCICFragment : C4Term → Bool
  | .var _ => true
  | .universe _ => true
  | .siteUniverse _ _ => false
  | .pi _ a b => a.isCICFragment && b.isCICFragment
  | .lam _ ty body => ty.isCICFragment && body.isCICFragment
  | .app fn arg => fn.isCICFragment && arg.isCICFragment
  | .sigma _ a b => a.isCICFragment && b.isCICFragment
  | .pair a b => a.isCICFragment && b.isCICFragment
  | .fst t => t.isCICFragment
  | .snd t => t.isCICFragment
  | .interval => true
  | .i0 => true
  | .i1 => true
  | .pathType ty a b => ty.isCICFragment && a.isCICFragment && b.isCICFragment
  | .pathAbs _ body => body.isCICFragment
  | .pathApp p r => p.isCICFragment && r.isCICFragment
  | .transp _ ty base => ty.isCICFragment && base.isCICFragment
  | .restrict _ _ => false
  | .descent _ _ => false
  | .oterm _ => false
  | .mathlibImport _ => false

/-- Enumerate all SiteObj values — the site is finite. -/
def SiteObj.all : List SiteObj :=
  [.TInt, .TFloat, .TStr, .TBool, .TList, .TDict, .TSet, .TTuple, .TNone, .TCallable, .TAny]

theorem SiteObj.all_complete (s : SiteObj) : s ∈ SiteObj.all := by
  cases s <;> simp [SiteObj.all]

instance : Fintype SiteObj where
  elems := ⟨↑SiteObj.all, by decide⟩
  complete := SiteObj.all_complete

instance : Fintype SiteKind where
  elems := ⟨↑([SiteKind.structural, .semantic, .hybrid] : List SiteKind), by decide⟩
  complete s := by cases s <;> decide

end C4
