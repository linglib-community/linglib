module

public import Mathlib.Order.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Tactic.DeriveFintype

/-!
# The Agreement Hierarchy

This file defines the four positions of Corbett's Agreement Hierarchy, the attributive
modifier, the predicate, the relative pronoun and the personal pronoun, as a chain with the
attributive on top; the availability of semantic agreement at a position; the hybrid nouns
whose availability varies from position to position; and what it is for a map along a
hierarchy to respect it.

A target agrees syntactically when its form follows the feature value the controller is
assigned, and semantically when it follows the controller's meaning. A hybrid noun, such as
Russian *vrač* 'doctor' denoting a woman or British English *committee*, admits both at some
positions, and the Agreement Hierarchy predicts that the likelihood of semantic agreement
never decreases from the attributive towards the personal pronoun, so a map respects the
hierarchy when it is antitone on the positions where it is recorded. A finite verb agrees at
the predicate position; Comrie's Predicate Hierarchy, which grades the verb, participle,
adjective and noun within the predicate, is `Corbett2000.PredicateTarget`.

## Main definitions

* `Agreement.Position`: the four positions, a chain from the personal pronoun up.
* `Agreement.Kind`: syntactic or semantic agreement.
* `Agreement.Availability`: the five degrees of availability of semantic agreement, from
  syntactic only to semantic only, linearly ordered.
* `Agreement.RespectsHierarchy`: a map recorded at some positions of a hierarchy is
  antitone where it is recorded.
* `Agreement.Hybrid`: a hybrid noun, the availability of semantic agreement at the
  positions of a hierarchy for which there are data.

## Implementation notes

`RespectsHierarchy` takes any preorder of positions and any preorder of values, so that it
serves the Agreement Hierarchy on `Position`, the Predicate Hierarchy on the sub-positions of
the predicate, and refinements of the attributive position alike, and corpus proportions of
semantic agreement as well as availabilities. A position carrying no value is skipped: values
are compared only across comparable positions that both carry one.

## References

* [corbett-1979] — the Agreement Hierarchy
* [corbett-1983] — hierarchies, targets and controllers
* [corbett-1991] — the hierarchy applied to gender, chapter 8
* [corbett-2006] — the standard monograph on agreement
-/

@[expose] public section

namespace Agreement

/-- A position of the Agreement Hierarchy ([corbett-1979]), declared from the bottom of the
hierarchy. -/
inductive Position where
  /-- The personal pronoun (English *he ~ she ~ it*). -/
  | personalPronoun
  /-- The relative pronoun (German *der ~ die ~ das*). -/
  | relativePronoun
  /-- The predicate, a finite verb or a predicate adjective (Russian *kniga interesna*). -/
  | predicate
  /-- The attributive modifier (French *un bon livre*). -/
  | attributive
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The Agreement Hierarchy as a chain:
`personalPronoun < relativePronoun < predicate < attributive`. -/
instance : LinearOrder Position := LinearOrder.lift' Position.ctorIdx (by decide)

/-- Whether an agreement form follows the feature value the controller is assigned or the
controller's meaning. -/
inductive Kind where
  | syntactic
  | semantic
  deriving DecidableEq, Repr, Fintype

/-- The availability of semantic agreement at a position of a hierarchy, the five categories
of [corbett-1991]'s summary of hybrid nouns, ordered by the likelihood of semantic
agreement. -/
inductive Availability where
  | syntacticOnly
  | mostlySyntactic
  | both
  | mostlySemantic
  | semanticOnly
  deriving DecidableEq, Repr, Fintype

namespace Availability

/-- Availabilities are ordered by the likelihood of semantic agreement. -/
instance : LinearOrder Availability := LinearOrder.lift' Availability.ctorIdx (by decide)

/-- Which agreement an availability admits. -/
def Allows : Availability → Kind → Prop
  | .syntacticOnly, k => k = .syntactic
  | .semanticOnly, k => k = .semantic
  | _, _ => True

instance (a : Availability) (k : Kind) : Decidable (a.Allows k) := by
  cases a <;> simp only [Allows] <;> infer_instance

end Availability

section Hierarchy

variable {ι α : Type*} [Preorder ι] [Preorder α]

/-- A map recording a value at some positions of a hierarchy respects it when the value
never decreases down the hierarchy: of two comparable positions that both carry a value, the
lower carries the larger. -/
def RespectsHierarchy (f : ι → Option α) : Prop :=
  ∀ ⦃i j⦄, i ≤ j → ∀ a ∈ f i, ∀ b ∈ f j, b ≤ a

instance [Fintype ι] [DecidableLE ι] [DecidableLE α] (f : ι → Option α) :
    Decidable (RespectsHierarchy f) := by
  unfold RespectsHierarchy; infer_instance

theorem respectsHierarchy_some_comp_iff_antitone {g : ι → α} :
    RespectsHierarchy (some ∘ g) ↔ Antitone g := by
  simp [RespectsHierarchy, Antitone]

end Hierarchy

/-- A hybrid noun, as the availability of semantic agreement at each position of a hierarchy
at which agreement in the feature applies and there are data; it respects the hierarchy when
`RespectsHierarchy` holds of it. -/
abbrev Hybrid (ι : Type*) := ι → Option Availability

end Agreement
