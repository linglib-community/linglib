module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Proto-role entailment profiles

An `EntailmentProfile` is the set of Dowty's ten proto-role entailments a verb imposes on one of
its arguments. Proto-Agent and Proto-Patient are cluster concepts: each is a set of five
entailments, and an argument's agenthood and patienthood are the parts of its profile that fall in
each cluster, `protoAgent` and `protoPatient`. The entailments are ordered by entailment, volition
entailing sentience, and a profile is well formed when it is closed under entailment, a lower set.

## Main definitions

* `EntailmentProfile`: the entailments a verb imposes on an argument.
* `EntailmentProfile.protoAgent`, `EntailmentProfile.protoPatient`: its parts in the two
  clusters.
* `EntailmentProfile.IsComplexRole`: entailments from both clusters.

## Main results

* `EntailmentProfile.isLowerSet_iff`: a profile is closed under entailment iff it imposes sentience
  wherever it imposes volition.

## Implementation notes

Since profiles are sets, `p ⊆ q` is entailment inclusion and `p ∪ q` imposes both profiles'
entailments, Reinhart and Siloni's role bundling. Dowty's argument selection principle is
`EntailmentProfile.Outranks`, the traditional labels are `ThetaRole`, the class templates are
`RoleList`, and the projection to Grimm's agentivity lattice is `EntailmentProfile.toAgentivity`.

## References

* [dowty-1991]
* [levin-2019]
* [reinhart-siloni-2005]
-/

@[expose] public section

namespace ArgumentStructure

/-- The ten entailments defining the proto-roles ([dowty-1991] pp.572–573): the first five are
Proto-Agent, the last five Proto-Patient. -/
inductive ProtoRoleFeature where
  /-- Volitional involvement in the event. -/
  | volition
  /-- Sentience or perception. -/
  | sentience
  /-- Causes an event or change of state in another participant. -/
  | causation
  /-- Movement relative to another participant. -/
  | movement
  /-- Exists independently of the event named by the verb. -/
  | independentExistence
  /-- Undergoes a change of state. -/
  | changeOfState
  /-- The argument is an incremental theme, measuring out the event. -/
  | incrementalTheme
  /-- Causally affected by another participant. -/
  | causallyAffected
  /-- Stationary relative to another participant. -/
  | stationary
  /-- Does not exist independently of the event. -/
  | dependentExistence
  deriving DecidableEq, Repr, Fintype

/-- One entailment is below another when an argument with the second has the first: volition
entails sentience, since only sentient entities act volitionally ([dowty-1991] p.607,
[levin-2019] §2.1), and the other entailments are independent. -/
instance : PartialOrder ProtoRoleFeature where
  le a b := a = b ∨ a = .sentience ∧ b = .volition
  le_refl _ := .inl rfl
  le_trans := by
    rintro a b c (rfl | ⟨rfl, rfl⟩) (rfl | ⟨h, rfl⟩)
    · exact .inl rfl
    · exact .inr ⟨h, rfl⟩
    · exact .inr ⟨rfl, rfl⟩
    · cases h
  le_antisymm := by
    rintro a b (rfl | ⟨rfl, rfl⟩) h
    · rfl
    · rcases h with h | ⟨h, -⟩ <;> cases h

instance : DecidableLE ProtoRoleFeature := fun a b ↦
  inferInstanceAs (Decidable (a = b ∨ a = .sentience ∧ b = .volition))

namespace ProtoRoleFeature

/-- Dowty's five Proto-Agent entailments. -/
def agentCluster : Finset ProtoRoleFeature :=
  {.volition, .sentience, .causation, .movement, .independentExistence}

/-- Dowty's five Proto-Patient entailments. -/
def patientCluster : Finset ProtoRoleFeature :=
  {.changeOfState, .incrementalTheme, .causallyAffected, .stationary, .dependentExistence}

theorem disjoint_agentCluster_patientCluster : Disjoint agentCluster patientCluster := by
  decide

theorem agentCluster_union_patientCluster : agentCluster ∪ patientCluster = Finset.univ := by
  decide

end ProtoRoleFeature

open ProtoRoleFeature

/-- The proto-role entailments a verb imposes on one of its arguments. -/
abbrev EntailmentProfile := Finset ProtoRoleFeature

/-- A profile is printed as the list of its entailments in Dowty's order. -/
instance : Repr EntailmentProfile where
  reprPrec p _ := repr ([ProtoRoleFeature.volition, .sentience, .causation, .movement,
    .independentExistence, .changeOfState, .incrementalTheme, .causallyAffected, .stationary,
    .dependentExistence].filter (· ∈ p))

namespace EntailmentProfile

variable {p q : EntailmentProfile}

/-- The Proto-Agent entailments of a profile. -/
def protoAgent (p : EntailmentProfile) : Finset ProtoRoleFeature := p ∩ agentCluster

/-- The Proto-Patient entailments of a profile. -/
def protoPatient (p : EntailmentProfile) : Finset ProtoRoleFeature := p ∩ patientCluster

theorem protoAgent_mono : Monotone protoAgent := fun _ _ h ↦ Finset.inter_subset_inter_right h

theorem protoPatient_mono : Monotone protoPatient := fun _ _ h ↦ Finset.inter_subset_inter_right h

/-- The profile imposes entailments from both proto-role clusters, [reinhart-siloni-2005]'s
complex role. -/
def IsComplexRole (p : EntailmentProfile) : Prop := p.protoAgent.Nonempty ∧ p.protoPatient.Nonempty

instance : DecidablePred IsComplexRole := fun p ↦
  inferInstanceAs (Decidable (p.protoAgent.Nonempty ∧ p.protoPatient.Nonempty))

theorem isComplexRole_union (ha : p.protoAgent.Nonempty) (hp : q.protoPatient.Nonempty) :
    IsComplexRole (p ∪ q) :=
  ⟨ha.mono (protoAgent_mono Finset.subset_union_left),
    hp.mono (protoPatient_mono Finset.subset_union_right)⟩

end EntailmentProfile

/-! ### Well-formedness -/

namespace EntailmentProfile

/-- A profile is closed under entailment exactly when it imposes sentience wherever it imposes
volition. -/
theorem isLowerSet_iff (p : EntailmentProfile) :
    IsLowerSet (p : Set ProtoRoleFeature) ↔ (.volition ∈ p → .sentience ∈ p) := by
  refine ⟨fun h hv ↦ h (show ProtoRoleFeature.sentience ≤ .volition from .inr ⟨rfl, rfl⟩) hv, ?_⟩
  rintro h a b (rfl | ⟨rfl, rfl⟩) ha
  · exact ha
  · exact h ha

end EntailmentProfile

end ArgumentStructure
