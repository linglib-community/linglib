module

public import Linglib.Semantics.ArgumentStructure.EntailmentProfile.ArgumentSelection
public import Linglib.Semantics.ArgumentStructure.AgentivityLattice.Basic
public import Mathlib.Data.Finset.Preimage
public import Mathlib.Order.Hom.BoundedLattice

/-!
# From Dowty's entailments to Grimm's lattice

Grimm keeps volition and sentience from Dowty's Proto-Agent entailments, recasts causation as
instigation, bound to a single participant, and movement as motion, and moves independent
existence to the persistence axis. The four agentivity features thus embed in Dowty's entailments
with their order, an agentivity is
[the profile of its counterparts](##ArgumentStructure.Agentivity.toEntailmentProfile), and the
agentivity of a profile is its preimage. The two maps are
[adjoint](##ArgumentStructure.EntailmentProfile.gc_toEntailmentProfile_toAgentivity), the
projection undoing the embedding, so the projection is monotone and [preserves unions and
intersections](##ArgumentStructure.EntailmentProfile.toAgentivityLatticeHom), and a profile is
closed under entailment exactly when [its agentivity is a node of Grimm's
lattice](##ArgumentStructure.EntailmentProfile.toAgentivity_mem_entailmentClosed_iff). The
agentivity of a profile is [its Proto-Agent entailments other than independent
existence](##ArgumentStructure.EntailmentProfile.toEntailmentProfile_toAgentivity), so an
argument that dominates another in agentivity without losing independent existence [is selected as
subject by Dowty's
principle](##ArgumentStructure.EntailmentProfile.outranks_of_toAgentivity_ssubset).

On the Proto-Patient side a profile [admits](##ArgumentStructure.EntailmentProfile.Admits) the
persistence levels compatible with its entailments, a down-set of the persistence lattice:
[the levels strictly below qualitative persistence
(beginning)](##ArgumentStructure.EntailmentProfile.admits_iff_lt) when the argument both changes
state and depends on the event for its existence.

## Implementation notes

Mathlib's `Finset.preimage` is noncomputable, so `EntailmentProfile.toAgentivity` filters the
features and `EntailmentProfile.toAgentivity_eq_preimage` identifies the two. Grimm relates the
Proto-Patient entailments to persistence by conditions on levels, not by a function, so a profile
is related to the levels it admits. Only the condition on change of state is stated outright; the
condition on dependent existence formalizes the remark that Dowty's entailment conflates creation
and destruction.

## References

* [grimm-2011]
* [dowty-1991]
-/

@[expose] public section

namespace ArgumentStructure

namespace Agentivity

/-- The agentivity features as Dowty's Proto-Agent entailments ([grimm-2011] pp.520–521), with
the entailment of sentience by volition on both sides. -/
def Feature.toProtoRoleFeature : Feature ↪o ProtoRoleFeature where
  toFun
    | .volition => .volition
    | .sentience => .sentience
    | .instigation => .causation
    | .motion => .movement
  inj' := by decide
  map_rel_iff' := by decide

/-- An agentivity as an entailment profile, the Dowty counterparts of its features. -/
def toEntailmentProfile : Agentivity ↪o EntailmentProfile :=
  Finset.mapEmbedding Feature.toProtoRoleFeature.toEmbedding

@[simp] theorem mem_toEntailmentProfile {a : Agentivity} {f : ProtoRoleFeature} :
    f ∈ toEntailmentProfile a ↔ ∃ g ∈ a, Feature.toProtoRoleFeature g = f := by
  simp [toEntailmentProfile]

/-- The counterparts of the agentivity features are Dowty's Proto-Agent entailments other than
independent existence. -/
theorem toEntailmentProfile_top :
    toEntailmentProfile ⊤ = ProtoRoleFeature.agentCluster.erase .independentExistence := by
  decide

end Agentivity

namespace EntailmentProfile

open Agentivity

variable {p q : EntailmentProfile} {l m : Persistence}

/-- The agentivity of a profile, the features whose Dowty counterparts it entails. -/
def toAgentivity (p : EntailmentProfile) : Agentivity :=
  Finset.univ.filter (Feature.toProtoRoleFeature · ∈ p)

@[simp] theorem mem_toAgentivity {f : Agentivity.Feature} :
    f ∈ p.toAgentivity ↔ Feature.toProtoRoleFeature f ∈ p := by
  simp [toAgentivity]

theorem toAgentivity_eq_preimage (p : EntailmentProfile) :
    p.toAgentivity =
      p.preimage Feature.toProtoRoleFeature Feature.toProtoRoleFeature.injective.injOn := by
  ext; simp

/-! ### The adjunction -/

/-- An agentivity's counterparts are among a profile's entailments exactly when the agentivity is
below the profile's. -/
theorem gc_toEntailmentProfile_toAgentivity :
    GaloisConnection toEntailmentProfile toAgentivity := fun a p ↦ by
  rw [toAgentivity_eq_preimage]; exact Finset.map_subset_iff_subset_preimage

/-- The agentivities are a retract of the profiles. -/
def gciToEntailmentProfileToAgentivity : GaloisCoinsertion toEntailmentProfile toAgentivity :=
  gc_toEntailmentProfile_toAgentivity.toGaloisCoinsertion fun a f ↦ by simp

@[simp] theorem toAgentivity_toEntailmentProfile (a : Agentivity) :
    (toEntailmentProfile a).toAgentivity = a :=
  gciToEntailmentProfileToAgentivity.u_l_eq a

theorem toAgentivity_monotone : Monotone toAgentivity :=
  gc_toEntailmentProfile_toAgentivity.monotone_u

theorem toAgentivity_surjective : Function.Surjective toAgentivity :=
  gciToEntailmentProfileToAgentivity.u_surjective

/-! ### The projection as a lattice homomorphism -/

@[simp] theorem toAgentivity_union (p q : EntailmentProfile) :
    (p ∪ q).toAgentivity = p.toAgentivity ∪ q.toAgentivity := by
  ext; simp

@[simp] theorem toAgentivity_inter (p q : EntailmentProfile) :
    (p ∩ q).toAgentivity = p.toAgentivity ∩ q.toAgentivity := by
  ext; simp

@[simp] theorem toAgentivity_empty : toAgentivity ∅ = ∅ := by ext; simp

@[simp] theorem toAgentivity_univ : toAgentivity Finset.univ = Finset.univ := by ext; simp

/-- `toAgentivity` as a bounded lattice homomorphism: bundling two roles joins their
agentivities. -/
def toAgentivityLatticeHom : BoundedLatticeHom EntailmentProfile Agentivity where
  toFun := toAgentivity
  map_sup' := toAgentivity_union
  map_inf' := toAgentivity_inter
  map_top' := toAgentivity_univ
  map_bot' := toAgentivity_empty

@[simp] theorem coe_toAgentivityLatticeHom : ⇑toAgentivityLatticeHom = toAgentivity := rfl

/-- A profile is closed under entailment exactly when its agentivity is a node of Grimm's lattice
of agentivity properties. -/
theorem toAgentivity_mem_entailmentClosed_iff :
    p.toAgentivity ∈ Agentivity.entailmentClosed ↔ IsLowerSet (p : Set ProtoRoleFeature) := by
  rw [Agentivity.mem_entailmentClosed, Agentivity.isLowerSet_iff, isLowerSet_iff]
  simp only [mem_toAgentivity]; rfl

/-! ### Proto-Agent entailments -/

/-- The counterparts of a profile's agentivity are its Proto-Agent entailments other than
independent existence, which Grimm moves to the persistence axis. -/
theorem toEntailmentProfile_toAgentivity (p : EntailmentProfile) :
    toEntailmentProfile p.toAgentivity = p.protoAgent.erase .independentExistence := by
  rw [protoAgent, ← Finset.inter_erase, ← toEntailmentProfile_top]
  ext f; simp only [mem_toEntailmentProfile, mem_toAgentivity, Finset.mem_inter, Finset.top_eq_univ,
    Finset.mem_univ, true_and]
  exact ⟨fun ⟨g, hg, h⟩ ↦ ⟨h ▸ hg, g, h⟩, fun ⟨hf, g, h⟩ ↦ ⟨g, h ▸ hf, h⟩⟩

/-- Dowty's inclusion of Proto-Agent entailments is Grimm's order on agentivity together with
independent existence. -/
theorem protoAgent_subset_iff :
    q.protoAgent ⊆ p.protoAgent ↔
      q.toAgentivity ⊆ p.toAgentivity ∧
        (.independentExistence ∈ q → .independentExistence ∈ p) := by
  have h (r : EntailmentProfile) : .independentExistence ∈ r.protoAgent ↔
      .independentExistence ∈ r := by simp [protoAgent, ProtoRoleFeature.agentCluster]
  rw [← toEntailmentProfile.le_iff_le, toEntailmentProfile_toAgentivity,
    toEntailmentProfile_toAgentivity, ← h q, ← h p]
  simp only [Finset.subset_iff, Finset.mem_erase]
  grind

/-- An argument that dominates another in agentivity, and exists independently of the event if the
other does, is selected as subject by Dowty's principle. -/
theorem outranks_of_toAgentivity_ssubset (h : q.toAgentivity ⊂ p.toAgentivity)
    (hie : .independentExistence ∈ q → .independentExistence ∈ p) : p.Outranks q :=
  .inl <| Finset.card_lt_card
    ⟨protoAgent_subset_iff.2 ⟨h.1, hie⟩, fun h' ↦ h.2 (protoAgent_subset_iff.1 h').1⟩

/-! ### Proto-Patient entailments and persistence -/

/-- A profile admits a persistence level when the level respects Grimm's two correspondences with
Dowty's Proto-Patient entailments. -/
@[mk_iff]
structure Admits (p : EntailmentProfile) (l : Persistence) : Prop where
  /-- An argument entailed to change state is not entailed to persist qualitatively at the end
  ([grimm-2011] p.522). -/
  of_changeOfState : .changeOfState ∈ p → .qualitiesAtEnd ∉ l
  /-- An argument whose existence depends on the event, created or destroyed in it, does not
  persist existentially at both ends (p.524). -/
  of_dependentExistence : .dependentExistence ∈ p → ¬ (.existsAtBeginning ∈ l ∧ .existsAtEnd ∈ l)

instance (p : EntailmentProfile) : DecidablePred p.Admits := fun l ↦
  decidable_of_iff' _ (admits_iff p l)

/-- Admission in the order of the persistence lattice: change of state keeps the level at or below
qualitative persistence (beginning), and dependent existence keeps it from reaching it. -/
theorem admits_iff_le_and_not_le : p.Admits l ↔
    (.changeOfState ∈ p → l ≤ .qualitativeBeginning) ∧
      (.dependentExistence ∈ p → ¬ .qualitativeBeginning ≤ l) := by
  rw [admits_iff, Persistence.qualitiesAtEnd_notMem_iff_le, Persistence.existsAtBothEnds_iff_le]

/-- A profile with fewer entailments admits more levels. -/
theorem Admits.anti (h : p ⊆ q) (hq : q.Admits l) : p.Admits l :=
  ⟨fun hc ↦ hq.of_changeOfState (h hc), fun hd ↦ hq.of_dependentExistence (h hd)⟩

/-- The levels a profile admits are closed downward. -/
theorem isLowerSet_setOf_admits (p : EntailmentProfile) : IsLowerSet {l | p.Admits l} :=
  fun _ _ hml hl ↦ admits_iff_le_and_not_le.2
    ⟨fun hc ↦ hml.trans ((admits_iff_le_and_not_le.1 hl).1 hc),
      fun hd h ↦ (admits_iff_le_and_not_le.1 hl).2 hd (h.trans hml)⟩

theorem admits_bot (p : EntailmentProfile) : p.Admits ⊥ :=
  admits_iff_le_and_not_le.2 ⟨fun _ ↦ bot_le, fun _ ↦ by decide⟩

/-- An argument that changes state and whose existence depends on the event is admitted exactly
strictly below qualitative persistence (beginning). -/
theorem admits_iff_lt (hc : .changeOfState ∈ p) (hd : .dependentExistence ∈ p) :
    p.Admits l ↔ l < .qualitativeBeginning := by
  simp [admits_iff_le_and_not_le, hc, hd, lt_iff_le_not_ge]

end EntailmentProfile

end ArgumentStructure
