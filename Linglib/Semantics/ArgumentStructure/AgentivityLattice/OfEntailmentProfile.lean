module

public import Linglib.Semantics.ArgumentStructure.EntailmentProfile.Selection
public import Linglib.Semantics.ArgumentStructure.AgentivityLattice.Basic
public import Mathlib.Data.Finset.Preimage

/-!
# From Dowty's entailments to Grimm's lattice

Grimm keeps volition and sentience from Dowty's Proto-Agent entailments, recasts causation as
instigation, bound to a single participant, and movement as motion, and moves independent
existence to the persistence axis. The four agentivity features thus embed in Dowty's
entailments, and the agentivity of a profile is its preimage under that embedding.
The projection is monotone, and Dowty's inclusion of Proto-Agent entailments is exactly Grimm's
order on agentivity together with independent existence, so Grimm's dominance criterion selects a
subject wherever it strictly dominates.

## Main definitions

* `Agentivity.Feature.toProtoRole`: the agentivity features as Dowty's entailments.
* `EntailmentProfile.toAgentivity`: the agentivity of a profile.
* `EntailmentProfile.Admits`: Grimm's correspondences between Proto-Patient entailments and
  persistence.

## Main results

* `EntailmentProfile.protoAgent_subset_iff`: Dowty's inclusion is Grimm's order plus independent
  existence.
* `outranks_of_lattice_dominance`: strict dominance on the agentivity lattice selects a subject.

## Implementation notes

Grimm states the persistence counterparts of Dowty's Proto-Patient entailments as two constraints,
not as a function, so a profile is related to the levels it admits rather than mapped to one.

## References

* [grimm-2011]
* [dowty-1991]
-/

@[expose] public section

namespace ArgumentStructure

/-- The agentivity features as Dowty's Proto-Agent entailments ([grimm-2011] p.521). -/
def Agentivity.Feature.toProtoRole : Agentivity.Feature ↪ ProtoRoleFeature where
  toFun
    | .volition => .volition
    | .sentience => .sentience
    | .instigation => .causation
    | .motion => .movement
  inj' := by decide

namespace EntailmentProfile

open Agentivity.Feature

variable {p q : EntailmentProfile}

/-- The agentivity of a profile, the features whose Dowty counterparts it entails. -/
def toAgentivity (p : EntailmentProfile) : Agentivity := Finset.univ.filter (·.toProtoRole ∈ p)

@[simp] theorem mem_toAgentivity {f : Agentivity.Feature} :
    f ∈ p.toAgentivity ↔ f.toProtoRole ∈ p := by
  simp [toAgentivity]

theorem toAgentivity_eq_preimage (p : EntailmentProfile) :
    p.toAgentivity = p.preimage toProtoRole toProtoRole.injective.injOn := by
  ext; simp

theorem toAgentivity_monotone : Monotone toAgentivity := fun _ _ h _ ↦ by
  simpa using @h _

theorem protoAgent_subset_iff :
    q.protoAgent ⊆ p.protoAgent ↔
      q.toAgentivity ⊆ p.toAgentivity ∧
        (.independentExistence ∈ q → .independentExistence ∈ p) := by
  simp only [Finset.subset_iff, protoAgent, Finset.mem_inter, mem_toAgentivity]
  constructor
  · intro h
    exact ⟨fun f hf ↦ (h ⟨hf, by cases f <;> decide⟩).1, fun hq ↦ (h ⟨hq, by decide⟩).1⟩
  · rintro ⟨h, hie⟩ f ⟨hf, hc⟩
    refine ⟨?_, hc⟩
    simp only [ProtoRoleFeature.agentCluster, Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    exacts [@h .volition hf, @h .sentience hf, @h .instigation hf, @h .motion hf, hie hf]

end EntailmentProfile

open EntailmentProfile

theorem outranks_of_lattice_dominance {subj obj : EntailmentProfile}
    (hlt : obj.toAgentivity ⊂ subj.toAgentivity)
    (hie : .independentExistence ∈ obj → .independentExistence ∈ subj) :
    OutranksForSubject subj obj :=
  .inl (Finset.ssubset_def.2 ⟨protoAgent_subset_iff.2 ⟨hlt.subset, hie⟩,
    fun h ↦ hlt.not_subset (protoAgent_subset_iff.1 h).1⟩)

/-- A profile admits a persistence level when the level respects Grimm's two correspondences with
Dowty's Proto-Patient entailments: an argument entailed to change state is not entailed to persist
qualitatively at the end ([grimm-2011] p.522), and one whose existence depends on the event,
created, destroyed or not entailed to exist, does not persist existentially at both ends
(p.524). -/
def EntailmentProfile.Admits (p : EntailmentProfile) (l : PersistenceLevel) : Prop :=
  (.changeOfState ∈ p → .quPE ∉ l) ∧ (.dependentExistence ∈ p → ¬ (.exPB ∈ l ∧ .exPE ∈ l))

instance (p : EntailmentProfile) : DecidablePred p.Admits := fun _ ↦
  inferInstanceAs (Decidable (_ ∧ _))

end ArgumentStructure
