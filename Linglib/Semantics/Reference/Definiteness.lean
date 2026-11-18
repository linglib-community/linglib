module

public import Mathlib.Order.Atoms
public import Mathlib.Order.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Definiteness

This file gives the frame-free vocabulary of definiteness. The definiteness of a nominal places
it on the scale that Comrie, Aissen and Haspelmath share, a definite above a specific indefinite
above a non-specific one, and definite against indefinite is the cut of that scale at its top
rung. Farkas and Brasoveanu take specificity to be stability of reference across alternatives,
scopal, epistemic or partitive according to the alternatives.
A definite article has one of two strengths, uniqueness and familiarity, after Schwarz, ordered
uniqueness below familiarity since the strong article narrows the weak one. The strength a use of a
definite calls for, after Hawkins and Schwarz, and the strength of a bridging relation are recorded
as data here; which strengths a language's determiner inventory marks is derived in
`Syntax/Category/Determiner/Basic.lean`, and the descriptions themselves denote in
`Semantics/Reference/Description.lean`.

## Main definitions

* `Definiteness`: the definiteness scale, whose definites are the cut `Set.Ici .definite`.
* `Definite.Strength`, `NominalKind`: the strength of a definite article
  and the kind of nominal an inventory realizes, with `Strength.toKind` and `NominalKind.strength`.
* `Definite.Use`, `Definite.Bridging`: the uses of a definite
  description and the bridging relations, each with the strength it calls for.

## References

* [aissen-2003]
* [comrie-1989]
* [farkas-brasoveanu-2020]
* [haspelmath-2021]
* [schwarz-2009]
* [schwarz-2013]
* [hawkins-1978]
* [jenks-2018]
* [moroney-2021]
* [patel-grosz-grosz-2017]
-/

@[expose] public section

/-- The definiteness of a nominal ranks a definite above a specific indefinite above a
non-specific indefinite, the definiteness scale of [haspelmath-2021] and that of [aissen-2003]
without its pronoun and proper-name rungs; definite against indefinite is its cut at the
definites. A specific indefinite has stable reference across the alternatives a language's marking
tracks, scopal, epistemic or partitive; [farkas-brasoveanu-2020] leave open where each kind sits
on the scale, so a consumer states which it means. -/
inductive Definiteness where
  | nonSpecific
  | specific
  | definite
  deriving DecidableEq, Repr, Fintype

namespace Definiteness

/-- The rank on the scale, 0 for a non-specific indefinite up to 2 for a definite. -/
def rank : Definiteness → ℕ
  | .nonSpecific => 0
  | .specific => 1
  | .definite => 2

instance : LinearOrder Definiteness := LinearOrder.lift' rank (by decide)

end Definiteness

namespace Definite

/-- A definite article's strength is uniqueness, which the weak article presupposes, or
familiarity, which the strong article presupposes ([schwarz-2009]). -/
inductive Strength where
  | uniqueness
  | familiarity
  deriving DecidableEq, Repr, Fintype

/-- The strong article is the weak article over a narrowed restrictor (`Definite.anaphoric`), so
the strengths form the chain uniqueness < familiarity. -/
instance : LinearOrder Strength := LinearOrder.lift' Strength.ctorIdx (by decide)

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

end Definite

/-- A kind of nominal that a determiner inventory may realize is one of the forms a definite
description takes, or the indefinite, which denotes no partial individual. -/
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
def Definite.Strength.toKind : Definite.Strength → NominalKind
  | .uniqueness  => .unique
  | .familiarity => .anaphoric

/-- The strength a kind of nominal presupposes, where it is definite. -/
def NominalKind.strength : NominalKind → Option Definite.Strength
  | .bare | .indefinite         => none
  | .unique | .possessive       => some .uniqueness
  | .anaphoric | .demonstrative => some .familiarity

@[simp] theorem Definite.Strength.strength_toKind (p : Definite.Strength) :
    p.toKind.strength = some p := by
  cases p <;> rfl
