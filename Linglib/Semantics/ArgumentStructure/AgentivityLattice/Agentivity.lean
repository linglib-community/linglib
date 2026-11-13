module

public import Linglib.Core.Order.UpperLower.Finset
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Sublattice
public import Mathlib.Tactic.DeriveFintype

/-!
# Grimm's agentivity features

Grimm reformulates Dowty's Proto-Agent entailments as four privative features, volition,
sentience, instigation and motion, the Proto-Patient being the unmarked pole of each, and
decomposes Dowty's relational causation into instigation, which is bound to a single participant.
An argument's agentivity is the set of features its predicate entails, ordered by inclusion. The
only relation among the features, that volition entails sentience, orders them as Dowty's
entailments are ordered, and the combinations Grimm organizes into a lattice are the sets closed
under it, [the lower sets](##ArgumentStructure.Agentivity.isLowerSet_iff), which
[form a sublattice](##ArgumentStructure.Agentivity.entailmentClosed) of all feature sets. Grimm
reserves the name agentivity lattice for its product with the persistence lattice.

## Implementation notes

The persistence features are `Persistence.Feature`, their product with the agentivity
features is `ParticipantType`, and the projection from Dowty's profiles is
`EntailmentProfile.toAgentivity`.

## References

* [grimm-2011]
* [dowty-1991]
-/

@[expose] public section

namespace ArgumentStructure

/-- The four agentivity features ([grimm-2011] Table 2), each privative: its absence is the
non-agentive pole. -/
inductive Agentivity.Feature where
  /-- The participant intends to bring about the event. -/
  | volition
  /-- Conscious involvement in the action or state. -/
  | sentience
  /-- Prior independent action whose effects can be attributed to the participant, Grimm's
  replacement for Dowty's causation. -/
  | instigation
  /-- The participant is in motion during the event. -/
  | motion
  deriving DecidableEq, Repr, Fintype

/-- The agentivity features a predicate entails for an argument. -/
abbrev Agentivity := Finset Agentivity.Feature

namespace Agentivity

/-- One feature is below another when an argument with the second has the first: volition entails
sentience ([grimm-2011] p.523), and the other features are independent. -/
instance : PartialOrder Feature where
  le a b := a = b ∨ a = .sentience ∧ b = .volition
  le_refl _ := .inl rfl
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableLE Feature := fun a b ↦
  inferInstanceAs (Decidable (a = b ∨ a = .sentience ∧ b = .volition))

theorem Feature.sentience_le_volition : Feature.sentience ≤ .volition := .inr ⟨rfl, rfl⟩

/-- A combination of features is closed under entailment exactly when it has sentience wherever it
has volition. -/
theorem isLowerSet_iff (a : Agentivity) :
    IsLowerSet (a : Set Feature) ↔ (.volition ∈ a → .sentience ∈ a) := by
  refine ⟨fun h hv ↦ h Feature.sentience_le_volition hv, ?_⟩
  rintro h b c (rfl | ⟨rfl, rfl⟩) hb
  exacts [hb, h hb]

/-- The combinations of features closed under entailment form a sublattice of the feature sets,
Grimm's lattice of agentivity properties (Fig. 1), with union and intersection as join and meet. -/
def entailmentClosed : Sublattice Agentivity where
  carrier := {a | IsLowerSet (a : Set Feature)}
  supClosed' a ha b hb := by simpa using IsLowerSet.union ha hb
  infClosed' a ha b hb := by simpa using IsLowerSet.inter ha hb

@[simp] theorem mem_entailmentClosed {a : Agentivity} :
    a ∈ entailmentClosed ↔ IsLowerSet (a : Set Feature) :=
  Iff.rfl

instance : DecidablePred (· ∈ entailmentClosed) := fun a ↦
  inferInstanceAs (Decidable (IsLowerSet (a : Set Feature)))

theorem card_entailmentClosed : (Finset.univ.filter (· ∈ entailmentClosed)).card = 12 := by decide

end Agentivity

end ArgumentStructure
