module

public import Linglib.Semantics.ArgumentStructure.EntailmentProfile.Basic
public import Linglib.Core.Order.UpperLower.Finset

/-!
# Theta roles as proto-role clusters

This file defines the traditional thematic-role labels and, for each, the set of proto-role
entailments it stands for. The label of an argument is computed from the entailments the verb
imposes on it (`EntailmentProfile.toRole`), so a role is a derived classification and never a
stored primitive.

## Main declarations

* `ArgumentStructure.ThetaRole`: the nine traditional labels.
* `ThetaRole.canonicalProfile`: the entailments a label stands for.
* `ThetaRole.IsDefined`: the label stands for some entailments.
* `EntailmentProfile.toRole`: the label of a profile, if any.
* `toRole_eq_some_agent_iff` and its siblings: the profiles that receive each label.
* `ThetaRole.toRole_canonicalProfile`: a defined label is the label of its own profile.

## Implementation notes

The classifier tests volition, then sentience, then causation, then causal affectedness, so a
profile with sentience and causation but no volition, which Dowty's definitions do not name, has
no label. Independent existence, which Dowty parenthesizes, never decides a label. Dowty's role
hierarchies follow from the selection principle over these profiles in `Studies/Dowty1991.lean`.

## References

* [dowty-1991]
* [levin-rappaport-hovav-2005]
* [primus-1999]
-/

@[expose] public section

namespace ArgumentStructure

/-- The traditional thematic-role labels, read as clusters of proto-role entailments. -/
inductive ThetaRole where
  | agent
  | patient
  | theme
  | experiencer
  | goal
  | source
  | instrument
  | stimulus
  /-- The recipient of a transfer, for which [primus-1999] introduces a Recipient Proto-role
  ([levin-rappaport-hovav-2005], p. 60). -/
  | recipient
  deriving DecidableEq, Repr, Fintype

namespace ThetaRole

/-- The proto-role entailments a label stands for in Dowty's reading of the traditional roles;
empty for source, goal and recipient. -/
def canonicalProfile : ThetaRole → EntailmentProfile
  | .agent => {.volition, .sentience, .causation, .movement}
  | .experiencer => {.sentience}
  | .stimulus => {.causation}
  | .instrument => {.causation, .movement}
  | .theme => {.changeOfState, .incrementalTheme, .dependentExistence}
  | .patient => {.changeOfState, .incrementalTheme, .causallyAffected, .dependentExistence}
  | .goal | .source | .recipient => ∅

/-- A label is defined by proto-role entailments; source, goal and recipient are not. -/
def IsDefined (r : ThetaRole) : Prop := r ≠ .source ∧ r ≠ .goal ∧ r ≠ .recipient

instance : DecidablePred IsDefined := fun r ↦
  inferInstanceAs (Decidable (r ≠ .source ∧ r ≠ .goal ∧ r ≠ .recipient))

@[simp] theorem canonicalProfile_source : canonicalProfile .source = ∅ := rfl

@[simp] theorem canonicalProfile_goal : canonicalProfile .goal = ∅ := rfl

@[simp] theorem canonicalProfile_recipient : canonicalProfile .recipient = ∅ := rfl

theorem isDefined_iff_canonicalProfile_nonempty (r : ThetaRole) :
    r.IsDefined ↔ r.canonicalProfile.Nonempty := by
  cases r <;> decide

theorem canonicalProfile_theme_le_patient :
    canonicalProfile .theme ⊆ canonicalProfile .patient := by
  decide

theorem isLowerSet_canonicalProfile (r : ThetaRole) :
    IsLowerSet (r.canonicalProfile : Set ProtoRoleFeature) := by
  cases r <;> decide

end ThetaRole

namespace EntailmentProfile

/-- The label of the profile `p` is agent if it is volitional; otherwise experiencer if it is
sentient and not causing (no label if causing); otherwise instrument or stimulus if it is causing,
as it moves or not; otherwise patient if it is causally affected; otherwise theme if it has some
other Proto-Patient entailment or movement. -/
def toRole (p : EntailmentProfile) : Option ThetaRole :=
  if .volition ∈ p then some .agent
  else if .sentience ∈ p then if .causation ∈ p then none else some .experiencer
  else if .causation ∈ p then some (if .movement ∈ p then .instrument else .stimulus)
  else if .causallyAffected ∈ p then some .patient
  else if .changeOfState ∈ p ∨ .incrementalTheme ∈ p ∨ .dependentExistence ∈ p ∨ .movement ∈ p
  then some .theme
  else none

variable {p : EntailmentProfile}

theorem toRole_eq_some_agent_iff : p.toRole = some .agent ↔ .volition ∈ p := by
  unfold toRole; split_ifs <;> simp_all

theorem toRole_eq_some_experiencer_iff : p.toRole = some .experiencer ↔
    .volition ∉ p ∧ .sentience ∈ p ∧ .causation ∉ p := by
  unfold toRole; split_ifs <;> simp_all

theorem toRole_eq_some_instrument_iff : p.toRole = some .instrument ↔
    .volition ∉ p ∧ .sentience ∉ p ∧ .causation ∈ p ∧ .movement ∈ p := by
  unfold toRole; split_ifs <;> simp_all

theorem toRole_eq_some_stimulus_iff : p.toRole = some .stimulus ↔
    .volition ∉ p ∧ .sentience ∉ p ∧ .causation ∈ p ∧ .movement ∉ p := by
  unfold toRole; split_ifs <;> simp_all

theorem toRole_eq_some_patient_iff : p.toRole = some .patient ↔
    .volition ∉ p ∧ .sentience ∉ p ∧ .causation ∉ p ∧ .causallyAffected ∈ p := by
  unfold toRole; split_ifs <;> simp_all

theorem toRole_eq_some_theme_iff : p.toRole = some .theme ↔
    .volition ∉ p ∧ .sentience ∉ p ∧ .causation ∉ p ∧ .causallyAffected ∉ p ∧
      (.changeOfState ∈ p ∨ .incrementalTheme ∈ p ∨ .dependentExistence ∈ p ∨ .movement ∈ p) := by
  unfold toRole; split_ifs <;> simp_all

theorem toRole_ne_some_source : p.toRole ≠ some .source := by
  unfold toRole; split_ifs <;> simp

theorem toRole_ne_some_goal : p.toRole ≠ some .goal := by
  unfold toRole; split_ifs <;> simp

theorem toRole_ne_some_recipient : p.toRole ≠ some .recipient := by
  unfold toRole; split_ifs <;> simp

theorem isDefined_of_toRole_eq_some {r : ThetaRole} (h : p.toRole = some r) : r.IsDefined :=
  ⟨fun hr ↦ toRole_ne_some_source (hr ▸ h), fun hr ↦ toRole_ne_some_goal (hr ▸ h),
    fun hr ↦ toRole_ne_some_recipient (hr ▸ h)⟩

theorem causation_mem_of_toRole_eq_some_stimulus (h : p.toRole = some .stimulus) :
    .causation ∈ p :=
  (toRole_eq_some_stimulus_iff.mp h).2.2.1

end EntailmentProfile

namespace ThetaRole

/-- The classifier recovers every defined label from its canonical profile. -/
theorem toRole_canonicalProfile {r : ThetaRole} (h : r.IsDefined) :
    r.canonicalProfile.toRole = some r := by
  cases r <;> first | rfl | exact absurd rfl h.1 | exact absurd rfl h.2.1 | exact absurd rfl h.2.2

theorem canonicalProfile_injOn : Set.InjOn canonicalProfile {r | r.IsDefined} := by
  intro r hr s hs h
  have hr' := toRole_canonicalProfile hr
  rw [h, toRole_canonicalProfile hs] at hr'
  exact (Option.some.inj hr').symm

end ThetaRole

end ArgumentStructure
