module

public import Mathlib.Order.Atoms
public import Mathlib.Order.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Definiteness

This file gives the frame-free vocabulary of definiteness. A nominal is definite or indefinite,
as Heim distinguishes them, and on the continuum of definiteness, or specificity, that Comrie,
Aissen and Haspelmath share, a definite ranks above a specific indefinite above a non-specific
one; Farkas and Brasoveanu separate the kinds of specificity, scopal, epistemic and partitive.
A definite article has one of two strengths, uniqueness and familiarity, after Schwarz, ordered
uniqueness below familiarity since the strong article narrows the weak one. The strength a use of a
definite calls for, after Hawkins and Schwarz, and the strength of a bridging relation are recorded
as data here; which strengths a language's determiner inventory marks is derived in
`Syntax/Category/Determiner/Basic.lean`, and the descriptions themselves denote in
`Semantics/Reference/Description.lean`.

## Main definitions

* `Definiteness`: definite or indefinite, as a two-element bounded linear order.
* `DefinitenessDegree`: the continuum of definiteness, with its cut
  `DefinitenessDegree.definiteness`.
* `DefiniteDescription.Strength`, `NominalKind`: the strength of a definite article
  and the kind of nominal an inventory realizes, with `Strength.toKind` and `NominalKind.strength`.
* `DefiniteDescription.Use`, `DefiniteDescription.Bridging`: the uses of a definite
  description and the bridging relations, each with the strength it calls for.

## References

* [aissen-2003]
* [comrie-1989]
* [farkas-brasoveanu-2020]
* [haspelmath-2021]
* [schwarz-2009]
* [schwarz-2013]
* [hawkins-1978]
* [heim-1982]
* [jenks-2018]
* [moroney-2021]
* [patel-grosz-grosz-2017]
-/

@[expose] public section

/-- A nominal is definite or indefinite. A definite retrieves a unique or familiar referent, an
indefinite introduces a new one ([heim-1982]). -/
inductive Definiteness where
  | indefinite
  | definite
  deriving DecidableEq, Repr, Fintype

namespace Definiteness

/-- The rank on the definiteness scale, higher for definite. -/
def rank : Definiteness → ℕ
  | .indefinite => 0
  | .definite   => 1

/-- The order `indefinite < definite` is the definiteness scale of differential argument marking
in its binary form ([aissen-2003]). -/
instance : LinearOrder Definiteness := LinearOrder.lift' rank (by decide)

/-- `⊥ = indefinite`, `⊤ = definite`. -/
instance : BoundedOrder Definiteness where
  top := .definite
  le_top := by decide
  bot := .indefinite
  bot_le := by decide

instance : IsSimpleOrder Definiteness where
  exists_pair_ne := ⟨.indefinite, .definite, by decide⟩
  eq_bot_or_eq_top := by decide

end Definiteness

/-- The degree of definiteness of a nominal ranks a definite above a specific indefinite above a
non-specific indefinite. A specific indefinite is one of whichever kind of specificity a
language's marking tracks. -/
inductive DefinitenessDegree where
  | nonSpecific
  | specific
  | definite
  deriving DecidableEq, Repr, Fintype

namespace DefinitenessDegree

/-- The rank on the continuum, 0 for a non-specific indefinite up to 2 for a definite. -/
def rank : DefinitenessDegree → ℕ
  | .nonSpecific => 0
  | .specific => 1
  | .definite => 2

instance : LinearOrder DefinitenessDegree := LinearOrder.lift' rank (by decide)

/-- A degree is definite at the top of the continuum and indefinite below it. -/
def definiteness (d : DefinitenessDegree) : Definiteness :=
  if .definite ≤ d then .definite else .indefinite

theorem definiteness_monotone : Monotone definiteness := by
  intro a b; revert a b; decide

end DefinitenessDegree

namespace DefiniteDescription

/-- A definite article's strength is uniqueness, which the weak article presupposes, or
familiarity, which the strong article presupposes ([schwarz-2009]). -/
inductive Strength where
  | uniqueness
  | familiarity
  deriving DecidableEq, Repr, Fintype

/-- The strong article is the weak article over a narrowed restrictor
(`DefiniteDescription.denote_unique_restrictor`), so the strengths form the chain
uniqueness < familiarity. -/
instance : LinearOrder Strength := LinearOrder.lift' Strength.ctorIdx (by decide)

/-- A set of strengths is an upper set iff it contains familiarity whenever it contains
uniqueness. -/
theorem Strength.isUpperSet_iff {s : Set Strength} :
    IsUpperSet s ↔ (.uniqueness ∈ s → .familiarity ∈ s) :=
  ⟨fun h hu ↦ h (by decide) hu, fun h a b hab ha ↦ by
    cases a <;> cases b
    exacts [ha, h ha, absurd hab (by decide), ha]⟩

/-- A bridging relation is part–whole, as from a fridge to its crisper, or relational, as from a
play to its author ([schwarz-2013]). -/
inductive Bridging where
  | partWhole
  | relational
  deriving DecidableEq, Repr

/-- Part–whole bridging calls for the weak article and relational bridging for the strong one
([schwarz-2009]). -/
def Bridging.strength : Bridging → Strength
  | .partWhole  => .uniqueness
  | .relational => .familiarity

/-- A use of a definite description is one of [hawkins-1978]'s, with bridging split by its relation.
A covarying use is not a further use, since uses of every kind covary under quantification
([schwarz-2009]). -/
inductive Use where
  | anaphoric
  | immediateSituation
  | largerSituation
  | bridging (b : Bridging)
  deriving DecidableEq, Repr

/-- The anaphoric use calls for the strong article, the situational uses for the weak one, and a
bridging use for the strength of its relation ([schwarz-2009], [schwarz-2013]). -/
def Use.strength : Use → Strength
  | .anaphoric => .familiarity
  | .immediateSituation | .largerSituation => .uniqueness
  | .bridging b => b.strength

end DefiniteDescription

/-- A kind of nominal that a determiner inventory may realize is one of the forms of
`DefiniteDescription`, or the indefinite, which denotes no partial individual. -/
inductive NominalKind where
  | bare
  | indefinite
  | unique
  | anaphoric
  | demonstrative
  | possessive
  deriving DecidableEq, Repr

/-- The weak article realizes the unique description and the strong article the anaphoric
one. -/
def DefiniteDescription.Strength.toKind : DefiniteDescription.Strength → NominalKind
  | .uniqueness  => .unique
  | .familiarity => .anaphoric

/-- The strength a kind of nominal presupposes, where it is definite. -/
def NominalKind.strength : NominalKind → Option DefiniteDescription.Strength
  | .bare | .indefinite         => none
  | .unique | .possessive       => some .uniqueness
  | .anaphoric | .demonstrative => some .familiarity

@[simp] theorem DefiniteDescription.Strength.strength_toKind (p : DefiniteDescription.Strength) :
    p.toKind.strength = some p := by
  cases p <;> rfl
