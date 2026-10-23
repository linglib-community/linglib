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
is a participant type, and together they form the agentivity lattice, a sublattice of the product.
The named participant types anchor the case regions, `CaseRegion`, and Tsunoda's transitivity
hierarchy places a canonical patient for each class.

## Main definitions

* `ParticipantType`: an agentivity and a persistence level.
* `ParticipantType.lattice`: the valid participant types, Grimm's agentivity lattice.
* `maximalAgent`, `maximalPatient`, `effectorAgent`, `sentientNonInstigator`: named nodes.
* `TransitivityRank`: Tsunoda's transitivity hierarchy.

## References

* [grimm-2011]
* [tsunoda-1985]
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
def Valid (n : ParticipantType) : Prop := n.1.Valid ∧ n.CrossValid

instance : DecidablePred Valid := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

private theorem exPB_mem_inf {l m : PersistenceLevel} (hl : .exPB ∈ l) (hm : .exPB ∈ m) :
    .exPB ∈ l ⊓ m := by
  revert l m; decide

/-- The valid participant types form a sublattice of the product, Grimm's agentivity lattice. -/
def lattice : Sublattice ParticipantType where
  carrier := {n | n.Valid}
  supClosed' a ha b hb := ⟨Agentivity.lattice.supClosed ha.1 hb.1, by
    rcases ha.2 with h | h
    · exact .inl (IsConcreteLE.le_iff.1 le_sup_left h)
    rcases hb.2 with h' | h'
    · exact .inl (IsConcreteLE.le_iff.1 le_sup_right h')
    · exact .inr (by simp [h, h'])⟩
  infClosed' a ha b hb := ⟨Agentivity.lattice.infClosed ha.1 hb.1, by
    rcases ha.2 with h | h
    · rcases hb.2 with h' | h'
      · exact .inl (exPB_mem_inf h h')
      · exact .inr (by simp [h'])
    · exact .inr (by simp [h])⟩

@[simp] theorem mem_lattice {n : ParticipantType} : n ∈ lattice ↔ n.Valid := Iff.rfl

theorem card_valid : (Finset.univ.filter Valid).card = 38 := by decide

end ParticipantType

/-! ### Named participant types -/

/-- The maximal agent has every agentivity property at total persistence; it is the top of the
lattice and the prototypical transitive subject. -/
def maximalAgent : ParticipantType := ⊤

/-- The maximal patient has no agentivity property and exists when the event begins but not
after it, as the object of *break* or *destroy* does. -/
def maximalPatient : ParticipantType := (∅, .exPersBeginning)

/-- The effector has instigation and motion at total persistence, as the agent of the effective
action verbs *kill* and *break* does ([grimm-2011] §3, Ia and IIa in Fig. 5). -/
def effectorAgent : ParticipantType := ({.instigation, .motion}, .totalPersistence)

/-- Sentience without instigation at qualitative persistence (beginning), where Grimm's dative
uses converge: recipients, dative experiencers and the second arguments of two-place
communication and service verbs (§5.1, Fig. 7). -/
def sentientNonInstigator : ParticipantType := ({.sentience}, .quPersBeginning)

/-! ### The transitivity region -/

/-- A participant type is in the transitivity region when the argument exists at the beginning of
the event, which both participants of the prototypical transitive event do ([grimm-2011]
pp.529–530). -/
def ParticipantType.InTransitiveRegion (n : ParticipantType) : Prop := .exPB ∈ n.2

instance : DecidablePred ParticipantType.InTransitiveRegion := fun _ ↦
  inferInstanceAs (Decidable (_ ∈ _))

/-- Tsunoda's transitivity hierarchy ([grimm-2011] §3, example 8), distinct from the Burzio
classification `AuxiliarySelection.TransitivityClass`. -/
inductive TransitivityRank where
  /-- Resultative effective action, *kill* and *break*: the object is destroyed. -/
  | resultativeEffective
  /-- Contact, *shoot* and *hit*: the object is affected but persists. -/
  | contact
  /-- Pursuit, *search* and *seek*: the object need not exist. -/
  | pursuit
  deriving DecidableEq, Repr

/-- The canonical patient of each transitivity class (Fig. 5); the agent of classes I and II is
`effectorAgent`, and the agent of class III adds sentience to it. -/
def TransitivityRank.patientType : TransitivityRank → ParticipantType
  | .resultativeEffective => (∅, .exPersBeginning)
  | .contact => (∅, .quPersBeginning)
  | .pursuit => (∅, .totalNonPersistence)

end ArgumentStructure
