module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Sublattice
public import Mathlib.Tactic.DeriveFintype

/-!
# Grimm's agentivity features

Grimm reformulates Dowty's Proto-Agent entailments as four privative features, volition,
sentience, instigation and motion, the Proto-Patient being the unmarked pole of each, and
decomposes Dowty's relational causation into instigation, which is bound to a single participant.
An argument's agentivity is the set of features its predicate entails, ordered by inclusion. The
only relation among the features, that volition entails sentience, picks out the combinations
Grimm organizes into a lattice, and they are closed under union and intersection. Grimm reserves
the name agentivity lattice for its product with the persistence lattice.

## Main definitions

* `Agentivity`: the agentivity features of an argument.
* `Agentivity.Valid`: volition entails sentience.
* `Agentivity.lattice`: the valid combinations, as a sublattice of all feature sets.

## Implementation notes

The persistence features are `PersistenceLevel.Feature`, their product with the agentivity
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

/-- Volition entails sentience. -/
def Valid (a : Agentivity) : Prop := .volition ∈ a → .sentience ∈ a

instance : DecidablePred Valid := fun _ ↦ inferInstanceAs (Decidable (_ → _))

/-- The valid combinations of features form a sublattice of the feature sets, Grimm's lattice of
agentivity properties, with union and intersection as join and meet. -/
def lattice : Sublattice Agentivity where
  carrier := {a | a.Valid}
  supClosed' _ ha _ hb h := (Finset.mem_union.1 h).elim
    (fun h ↦ Finset.mem_union_left _ (ha h)) fun h ↦ Finset.mem_union_right _ (hb h)
  infClosed' _ ha _ hb h :=
    Finset.mem_inter.2 ⟨ha (Finset.mem_inter.1 h).1, hb (Finset.mem_inter.1 h).2⟩

@[simp] theorem mem_lattice {a : Agentivity} : a ∈ lattice ↔ a.Valid := Iff.rfl

theorem card_valid : (Finset.univ.filter Valid).card = 12 := by decide

end Agentivity

end ArgumentStructure
