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
[the agentivity lattice](##ArgumentStructure.ParticipantType.lattice), a sublattice of the product
with the maximal agent at its top.

## References

* [grimm-2011]
-/

@[expose] public section

namespace ArgumentStructure

/-- A participant type, a node of the product of the agentivity and persistence lattices. -/
abbrev ParticipantType := Agentivity × PersistenceLevel

namespace ParticipantType

/-- An argument not entailed to exist when the event begins has no agentivity property. -/
def CrossValid (n : ParticipantType) : Prop := .exPB ∈ n.2 ∨ n.1 = ∅

instance : DecidablePred CrossValid := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- A participant type respects both the relation among the agentivity properties and the
dependence of agentivity on initial existence. -/
def Valid (n : ParticipantType) : Prop := n.1 ∈ Agentivity.lattice ∧ n.CrossValid

instance : DecidablePred Valid := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

open PersistenceLevel in
/-- The valid participant types form a sublattice of the product, Grimm's agentivity lattice. -/
def lattice : Sublattice ParticipantType where
  carrier := {n | n.Valid}
  supClosed' a ha b hb := ⟨Agentivity.lattice.supClosed ha.1 hb.1, by
    rcases ha.2 with h | h
    · exact .inl (exPB_mem_iff.2 (le_sup_of_le_left (exPB_mem_iff.1 h)))
    rcases hb.2 with h' | h'
    · exact .inl (exPB_mem_iff.2 (le_sup_of_le_right (exPB_mem_iff.1 h')))
    · exact .inr (by simp [h, h'])⟩
  infClosed' a ha b hb := ⟨Agentivity.lattice.infClosed ha.1 hb.1, by
    rcases ha.2 with h | h
    · rcases hb.2 with h' | h'
      · exact .inl (exPB_mem_iff.2 (le_inf (exPB_mem_iff.1 h) (exPB_mem_iff.1 h')))
      · exact .inr (by simp [h'])
    · exact .inr (by simp [h])⟩

@[simp] theorem mem_lattice {n : ParticipantType} : n ∈ lattice ↔ n.Valid := Iff.rfl

theorem card_valid : (Finset.univ.filter Valid).card = 38 := by decide

end ParticipantType

end ArgumentStructure
