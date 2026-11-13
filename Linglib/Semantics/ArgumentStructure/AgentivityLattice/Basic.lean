module

public import Linglib.Semantics.ArgumentStructure.AgentivityLattice.Agentivity
public import Linglib.Semantics.ArgumentStructure.AgentivityLattice.Persistence
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Sublattice

/-!
# The agentivity lattice

Grimm combines the lattice of agentivity properties with the persistence lattice by taking their
Cartesian product, ordered componentwise, and excludes the conceptually impossible nodes: an
argument not entailed to exist when the event begins has no agentivity property. Each remaining node
is a participant type, and together they form
[the agentivity lattice](##ArgumentStructure.ParticipantType.agentivityLattice), a sublattice of
the product with the maximal agent at its top.

## References

* [grimm-2011]
-/

@[expose] public section

namespace ArgumentStructure

/-- A participant type, a node of the product of the agentivity and persistence lattices. -/
abbrev ParticipantType := Agentivity × Persistence

namespace ParticipantType

/-- A participant type is valid when it respects both the relation among the agentivity properties
and the dependence of agentivity on initial existence. -/
@[mk_iff]
structure Valid (n : ParticipantType) : Prop where
  /-- The agentivity is closed under entailment. -/
  agentivity_mem : n.1 ∈ Agentivity.entailmentClosed
  /-- An argument not entailed to exist when the event begins has no agentivity property. -/
  existsAtBeginning_mem_or_eq_empty : .existsAtBeginning ∈ n.2 ∨ n.1 = ∅

instance : DecidablePred Valid := fun n ↦ decidable_of_iff' _ (valid_iff n)

open Persistence in
/-- The valid participant types form a sublattice of the product, Grimm's agentivity lattice. -/
def agentivityLattice : Sublattice ParticipantType where
  carrier := {n | n.Valid}
  supClosed' a ha b hb := ⟨Agentivity.entailmentClosed.supClosed ha.1 hb.1, by
    simp only [existsAtBeginning_mem_iff_le]
    rcases ha.2 with h | h
    · exact .inl (le_sup_of_le_left (existsAtBeginning_mem_iff_le.1 h))
    rcases hb.2 with h' | h'
    · exact .inl (le_sup_of_le_right (existsAtBeginning_mem_iff_le.1 h'))
    · exact .inr (by simp [h, h'])⟩
  infClosed' a ha b hb := ⟨Agentivity.entailmentClosed.infClosed ha.1 hb.1, by
    simp only [existsAtBeginning_mem_iff_le]
    rcases ha.2 with h | h
    · rcases hb.2 with h' | h'
      · exact .inl (le_inf (existsAtBeginning_mem_iff_le.1 h) (existsAtBeginning_mem_iff_le.1 h'))
      · exact .inr (by simp [h'])
    · exact .inr (by simp [h])⟩

@[simp] theorem mem_agentivityLattice {n : ParticipantType} :
    n ∈ agentivityLattice ↔ n.Valid := Iff.rfl

theorem card_agentivityLattice : (Finset.univ.filter Valid).card = 38 := by decide

end ParticipantType

end ArgumentStructure
