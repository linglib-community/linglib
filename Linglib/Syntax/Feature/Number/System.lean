module

public import Linglib.Syntax.Feature.Number.Basic

/-!
# Number systems

A number system is the set of number values a language distinguishes. Not every set of values is
a system: a value may require another, as the dual requires the singular and the paucal the
plural. `Number.universals` lists these implications, and a set of values
`Number.SatisfiesUniversals` when it has, with the antecedent of each, one of its consequents.

## References

* [harbour-2014]
* [corbett-2000]
-/

@[expose] public section

namespace Number

/-- An implication says that a system with its antecedent has one of its consequents. -/
structure Implication where
  /-- The number that requires another. -/
  antecedent : Number
  /-- The numbers one of which it requires. -/
  consequents : Finset Number
  deriving DecidableEq

/-- A system satisfies an implication when, with its antecedent, it has one of its
consequents. -/
def Implication.Holds (u : Implication) (s : Finset Number) : Prop :=
  u.antecedent ∈ s → ∃ v ∈ u.consequents, v ∈ s

instance (u : Implication) (s : Finset Number) : Decidable (u.Holds s) := by
  unfold Implication.Holds; infer_instance

/-- The implicational universals of number, as [harbour-2014] tabulates them; the greater and the
global plural have an implication each. -/
def universals : List Implication :=
  [⟨.trial, {.dual}⟩, ⟨.dual, {.singular}⟩, ⟨.singular, {.plural}⟩,
    ⟨.plural, {.singular, .minimal}⟩, ⟨.unitAugmented, {.augmented}⟩,
    ⟨.minimal, {.augmented, .plural}⟩, ⟨.augmented, {.minimal}⟩, ⟨.greaterPaucal, {.paucal}⟩,
    ⟨.paucal, {.plural}⟩, ⟨.greaterPlural, {.plural, .augmented}⟩,
    ⟨.globalPlural, {.plural, .augmented}⟩]

/-- A system satisfies the universals when it satisfies each implication. -/
def SatisfiesUniversals (s : Finset Number) : Prop := ∀ u ∈ universals, u.Holds s

instance (s : Finset Number) : Decidable (SatisfiesUniversals s) := by
  unfold SatisfiesUniversals; infer_instance

end Number
