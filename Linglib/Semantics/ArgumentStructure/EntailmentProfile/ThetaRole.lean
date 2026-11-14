module

public import Linglib.Semantics.ArgumentStructure.EntailmentProfile.Basic
public import Linglib.Core.Order.UpperLower.Finset
public import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Theta roles as classes of entailment profiles

A traditional thematic-role label names a class of arguments, and [dowty-1991] says which: each
label stands for a combination of proto-role entailments, an Experiencer being sentient without
volition or causation and an Instrument a moving cause without volition or sentience. A label is
therefore the set of entailment profiles it applies to, `ThetaRole.profiles`, and the labels of a
profile, `EntailmentProfile.roles`, are derived from the entailments a verb imposes and never
stored.

The classes are not the disjoint roles of the tradition but broader and narrower ones. The four
labels defined by Proto-Agent entailments
[exclude one another](##ArgumentStructure.ThetaRole.pairwiseDisjoint_profiles), whereas a Patient
is a Theme that is causally affected, so that
[every Patient is a Theme](##ArgumentStructure.ThetaRole.profiles_patient_subset_theme), and an
argument that acts volitionally and changes state is both an Agent and a Theme. Every class is
[convex](##ArgumentStructure.ThetaRole.ordConnected_profiles) in the order of profiles by
inclusion. Source, Goal and Recipient are not defined by proto-role entailments and apply to no
profile.

## Implementation notes

A label is a set of profiles and not the value of a function from profiles to labels, because such
a function makes the classes disjoint and has to order its tests, which the source does not.
A class that requires some entailments and excludes others is the interval `Set.Icc s tᶜ` of
profiles between the required `s` and the complement of the excluded `t`.

Of Dowty's four senses of Agent the class is that of volition alone; the typical profile
`ThetaRole.canonicalProfile` is the fullest sense. Dowty gives Theme no criterion and treats it as
a cluster concept, so its class is the profiles with at least one of the entailments he lists for
it, and movement, a Proto-Agent entailment that Agents and Instruments share, is not one of them.
Independent existence, which Dowty parenthesizes, decides no label. Dowty's role hierarchies follow
from the selection principle over the typical profiles in `Studies/Dowty1991.lean`.

## References

* [dowty-1991]
* [levin-rappaport-hovav-2005]
* [primus-1999]
-/

@[expose] public section

namespace ArgumentStructure

/-- The traditional thematic-role labels, read as classes of proto-role entailment profiles. -/
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

variable {r : ThetaRole} {p : EntailmentProfile}

/-! ### Typical profiles -/

/-- The entailments an argument bearing the label most typically has ([dowty-1991] p. 577); empty
for source, goal and recipient. -/
def canonicalProfile : ThetaRole → EntailmentProfile
  | .agent => {.volition, .sentience, .causation, .movement}
  | .experiencer => {.sentience}
  | .stimulus => {.causation}
  | .instrument => {.causation, .movement}
  | .theme => {.changeOfState, .incrementalTheme, .dependentExistence}
  | .patient => {.changeOfState, .incrementalTheme, .causallyAffected, .dependentExistence}
  | .goal | .source | .recipient => ∅

@[simp] theorem canonicalProfile_source : canonicalProfile .source = ∅ := rfl

@[simp] theorem canonicalProfile_goal : canonicalProfile .goal = ∅ := rfl

@[simp] theorem canonicalProfile_recipient : canonicalProfile .recipient = ∅ := rfl

theorem canonicalProfile_theme_subset_patient :
    canonicalProfile .theme ⊆ canonicalProfile .patient := by
  decide

theorem isLowerSet_canonicalProfile (r : ThetaRole) :
    IsLowerSet (r.canonicalProfile : Set ProtoRoleFeature) := by
  cases r <;> decide

/-! ### The class of a label -/

/-- The entailment profiles a label applies to ([dowty-1991] pp. 577–579). An Agent is volitional;
an Experiencer is sentient without volition or causation; an Instrument is a moving cause without
volition or sentience; a Stimulus causes and has no other Proto-Agent entailment; a Patient is
causally affected; a Theme has one of the Proto-Patient entailments of the typical Patient. -/
def profiles : ThetaRole → Set EntailmentProfile
  | .agent => Set.Ici {.volition}
  | .experiencer => Set.Icc {.sentience} {.volition, .causation}ᶜ
  | .instrument => Set.Icc {.causation, .movement} {.volition, .sentience}ᶜ
  | .stimulus => Set.Icc {.causation} {.volition, .sentience, .movement}ᶜ
  | .patient => Set.Ici {.causallyAffected}
  | .theme => {p | ¬ Disjoint p (canonicalProfile .patient)}
  | .goal | .source | .recipient => ∅

instance (r : ThetaRole) (p : EntailmentProfile) : Decidable (p ∈ r.profiles) := by
  cases r <;> unfold profiles <;> infer_instance

@[simp] theorem profiles_source : profiles .source = ∅ := rfl

@[simp] theorem profiles_goal : profiles .goal = ∅ := rfl

@[simp] theorem profiles_recipient : profiles .recipient = ∅ := rfl

theorem mem_profiles_agent : p ∈ profiles .agent ↔ .volition ∈ p := by
  simp [profiles]

theorem mem_profiles_experiencer :
    p ∈ profiles .experiencer ↔ .sentience ∈ p ∧ .volition ∉ p ∧ .causation ∉ p := by
  simp only [profiles, Set.mem_Icc, Finset.subset_compl_iff_disjoint_right,
    Finset.singleton_subset_iff, Finset.disjoint_insert_right, Finset.disjoint_singleton_right]

theorem mem_profiles_instrument : p ∈ profiles .instrument ↔
    (.causation ∈ p ∧ .movement ∈ p) ∧ .volition ∉ p ∧ .sentience ∉ p := by
  simp only [profiles, Set.mem_Icc, Finset.subset_compl_iff_disjoint_right,
    Finset.singleton_subset_iff, Finset.insert_subset_iff, Finset.disjoint_insert_right,
    Finset.disjoint_singleton_right]

theorem mem_profiles_stimulus : p ∈ profiles .stimulus ↔
    .causation ∈ p ∧ .volition ∉ p ∧ .sentience ∉ p ∧ .movement ∉ p := by
  simp only [profiles, Set.mem_Icc, Finset.subset_compl_iff_disjoint_right,
    Finset.singleton_subset_iff, Finset.disjoint_insert_right, Finset.disjoint_singleton_right]

theorem mem_profiles_patient : p ∈ profiles .patient ↔ .causallyAffected ∈ p := by
  simp [profiles]

theorem mem_profiles_theme : p ∈ profiles .theme ↔ ¬ Disjoint p (canonicalProfile .patient) :=
  .rfl

theorem canonicalProfile_mem_profiles (h : r.canonicalProfile.Nonempty) :
    r.canonicalProfile ∈ r.profiles := by
  cases r <;> first | decide | simp at h

theorem profiles_nonempty_iff : r.profiles.Nonempty ↔ r.canonicalProfile.Nonempty := by
  refine ⟨fun ⟨p, hp⟩ ↦ ?_, fun h ↦ ⟨_, canonicalProfile_mem_profiles h⟩⟩
  cases r <;> first | decide | exact hp.elim

theorem canonicalProfile_injOn :
    Set.InjOn canonicalProfile {r | r.canonicalProfile.Nonempty} :=
  fun r hr s _ ↦ (by decide : ∀ r s : ThetaRole,
    r.canonicalProfile.Nonempty → r.canonicalProfile = s.canonicalProfile → r = s) r s hr

/-! ### Broader and narrower classes -/

/-- A Patient is a Theme: the Patients are the Themes that are causally affected. -/
theorem profiles_patient_subset_theme : profiles .patient ⊆ profiles .theme := fun _ hp h ↦
  Finset.disjoint_left.1 h (Finset.singleton_subset_iff.1 hp) (by decide)

theorem isUpperSet_profiles_theme : IsUpperSet (profiles .theme) := fun _ _ hpq hp hq ↦
  hp (hq.mono_left hpq)

/-- A profile between two profiles of a class is in the class. -/
instance ordConnected_profiles (r : ThetaRole) : r.profiles.OrdConnected := by
  cases r
  case theme => exact isUpperSet_profiles_theme.ordConnected
  all_goals unfold profiles; infer_instance

/-- The labels defined by Proto-Agent entailments apply to no common profile. -/
theorem pairwiseDisjoint_profiles :
    ({.agent, .experiencer, .instrument, .stimulus} : Set ThetaRole).PairwiseDisjoint
      profiles := by
  intro r hr s hs hrs
  refine Set.disjoint_left.2 fun p hp hq ↦ hrs ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr hs
  rcases hr with rfl | rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl | rfl <;>
    first
    | rfl
    | (simp only [mem_profiles_agent, mem_profiles_experiencer, mem_profiles_instrument,
        mem_profiles_stimulus] at hp hq
       tauto)

end ThetaRole

namespace EntailmentProfile

variable {r : ThetaRole} {p : EntailmentProfile}

/-- The labels that apply to a profile. -/
def roles (p : EntailmentProfile) : Finset ThetaRole := {r | p ∈ r.profiles}

@[simp] theorem mem_roles : r ∈ p.roles ↔ p ∈ r.profiles := by simp [roles]

end EntailmentProfile

end ArgumentStructure
