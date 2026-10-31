module

public import Linglib.Syntax.Minimalist.Verbal.Voice.Diathesis
public import Linglib.Semantics.ArgumentStructure.EntailmentProfile.Basic
public import Linglib.Fragments.Romance.French.Verbs
public import Linglib.Semantics.Reference.Animacy

/-!
# Martin, Schäfer and Kastner (2025): The Lexical Pragmatics of Reflexive Marking

This file formalizes the pragmatic account of French anticausative marking of
Martin, Schäfer and Kastner. Anticausatives marked with *se* and unmarked ones do not
differ in meaning; the *se* form is ambiguous between anticausative and reflexive voice while
the bare form is not (`Form.voiceOptions`, `se_ambiguous`), and cooperative speakers manage
that ambiguity under the Manner supermaxim. With a human argument the reflexive parse is
salient, by the bias to read humans as agents; for a limited-control verb, *rougir* 'blush',
the parse misleads, so the unmarked form is preferred, the unmarked limited-control
preference (4), and for an in-control verb, *(se) plier* 'bend', the bare form's inference
that no agentive construal was intended misleads instead, so the marked form is preferred,
the marked in-control preference (5). With a nonhuman argument no parse is salient and no
preference arises, unless the speaker means to present the nonhuman as responsible, when
the marked form is preferred since the reflexive parse is the only way to assign it agency,
the marked responsibility preference (`preference`, `generalizations`). The control level is
not read off the entailment profile, limited-control and in-control property-change verbs
sharing one (`control_level_not_from_entailments`), and the opposite preferences of the two
classes falsify any uniform semantic difference between the two forms
(`opposite_preferences_falsify_uniform_semantics`). Preferences arise only for verbs with
both forms (`SeMarking.HasChoice`).

## Implementation notes

The two parses are the paper's diatheses, the anticausative and the reflexive, which expletive
Voice and agentive Voice over an object understood as the subject derive after Schäfer (2008); the
entailments of an anticausative's sole argument are those of the French fragment's entries; the
account presupposes the reflexive–anticausative syncretism of Koontz-Garboden. The
experiments' rating means are described in the paper and not represented.

## References

* [martin-schaefer-kastner-2025]
* [schaefer-2008]
* [koontz-garboden-2009]
* [davis-koenig-2000]
* [dowty-1991]
-/

@[expose] public section

namespace MartinSchaeferKastner2025

open Minimalist.Voice ArgumentStructure French.Verbs

/-! ### The classes -/

/-- The morphological class of an anticausative is whether it has the bare form only, as
*changer de position*, the *se* form only, as *s'affaiblir*, or both, as *casser*, *plier* and
*rougir*. -/
inductive SeMarking where
  | minusSe
  | plusSe
  | plusMinusSe
  deriving DecidableEq

/-- The speaker has a choice of form only for a verb with both forms. -/
def SeMarking.HasChoice : SeMarking → Prop
  | .plusMinusSe => True
  | _ => False

instance : DecidablePred SeMarking.HasChoice := fun m ↦ by
  cases m <;> unfold SeMarking.HasChoice <;> infer_instance

/-- Whether the change a verb names is typically under its human undergoer's control (§1.1):
*rougir* 'blush' and *pâlir* 'get pale' are limited-control, *plier* 'bend' and
*s'approcher* 'get close' in-control. The distinction is world knowledge, not entailment. -/
inductive ControlLevel where
  | limitedControl
  | inControl
  deriving DecidableEq

/-- Whether the speaker means to present the entity as responsible for the change. -/
inductive ResponsibilityGoal where
  | neutral
  | conveyResponsibility
  deriving DecidableEq

theorem control_level_not_from_entailments :
    rougir.slotProfile? .external = refroidir.slotProfile? .external := by decide

theorem movement_sufficient_not_necessary :
    approcher.slotProfile? .external = some movingUndergoer ∧
      refroidir.slotProfile? .external = some undergoer ∧
      .movement ∈ movingUndergoer ∧ .movement ∉ undergoer := by
  decide

/-! ### The voice ambiguity of *se* -/

/-- The two forms of a verb with a choice. -/
inductive Form where
  | bare
  | se
  deriving DecidableEq

/-- The voices a form admits, of the paper's two diatheses for a French anticausative: the
anticausative and the semantically reflexive voice, whose sole argument is both undergoer and
agent. The bare form admits only the anticausative and the *se* form the reflexive as well, the
syncretism of [schaefer-2008] and [koontz-garboden-2009]. -/
def Form.voiceOptions : Form → List Voice
  | .bare => [Voice.anticausative]
  | .se => [Voice.anticausative, Voice.reflexive]

theorem se_ambiguous :
    (∀ f : Form, Voice.anticausative ∈ f.voiceOptions) ∧
      Voice.reflexive ∈ Form.se.voiceOptions ∧ Voice.reflexive ∉ Form.bare.voiceOptions := by
  refine ⟨fun f ↦ ?_, by decide, by decide⟩
  cases f <;> decide

/-- The *se* form's voices are those expletive Voice and agentive Voice over an object understood
as the subject derive. -/
example : Form.se.voiceOptions = [Minimalist.Voice.anticausative.diathesis none,
    Minimalist.Voice.agentive.diathesis (some (.implicit (some .reflexive)))] := by
  rw [Minimalist.Voice.Head.diathesis_of_not_isThematic _ (by decide),
    Minimalist.Voice.Head.diathesis_reflexive (by decide)]; rfl

/-! ### Managing the ambiguity (§2) -/

/-- The agent bias makes the reflexive parse of the *se* form salient for a human argument. -/
def ReflexiveSalient (a : Animacy) : Prop := a = .human

/-- The reflexive parse clashes with shared assumptions for a limited-control verb, whose
change is not under the undergoer's control, and aligns with them for an in-control verb. -/
def ReflexiveClashes : ControlLevel → Prop
  | .limitedControl => True
  | .inControl => False

instance : DecidablePred ReflexiveSalient := fun a ↦ inferInstanceAs (Decidable (a = .human))

instance : DecidablePred ReflexiveClashes := fun c ↦ by
  cases c <;> unfold ReflexiveClashes <;> infer_instance

/-- The preferred form of a verb with a choice. -/
inductive Preference where
  | unmarked
  | marked
  deriving DecidableEq

/-- The preference the Manner supermaxim predicts. Where the reflexive parse is salient, the
speaker avoids the ambiguous form when that parse misleads and keeps it when the bare form's
inference that no agent was intended misleads instead; where no parse is salient, the marked
form is preferred only when the speaker means to convey responsibility, the reflexive parse
being the only way to assign a nonhuman agency. -/
def preference (ctrl : ControlLevel) (anim : Animacy) (goal : ResponsibilityGoal) :
    Option Preference :=
  if ReflexiveSalient anim then some (if ReflexiveClashes ctrl then .unmarked else .marked)
  else match goal with
    | .neutral => none
    | .conveyResponsibility => some .marked

/-- The three generalizations hold. With a human argument the limited-control verbs prefer the
unmarked form and the in-control verbs the marked one, with a nonhuman argument the marked
form is preferred to convey responsibility, and otherwise a nonhuman argument yields no
preference. -/
theorem generalizations (g : ResponsibilityGoal) (c : ControlLevel) {a : Animacy}
    (ha : a ≠ .human) :
    preference .limitedControl .human g = some .unmarked ∧
      preference .inControl .human g = some .marked ∧
      preference c a .conveyResponsibility = some .marked ∧
      preference c a .neutral = none := by
  cases g <;> cases c <;> cases a <;> simp_all <;> decide

/-- Against the causation claim of [labelle-1992] and [labelle-doron-2010], the same class of
verbs with a choice shows opposite preferences by control level, which no uniform semantic
difference between the two forms could produce. -/
theorem opposite_preferences_falsify_uniform_semantics (g : ResponsibilityGoal) :
    preference .limitedControl .human g ≠ preference .inControl .human g := by
  cases g <;> decide

/-! ### Unaccusativity -/

/-- A profile predicts unaccusativity when it lacks the priority Proto-Agent entailments, volition
and causation ([davis-koenig-2000]), and bears at least one Proto-Patient entailment
([dowty-1991] (28), p. 572). -/
def PredictsUnaccusative (p : EntailmentProfile) : Prop :=
  .volition ∉ p ∧ .causation ∉ p ∧ p.protoPatient.Nonempty

instance : DecidablePred PredictsUnaccusative := fun _ ↦
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem cos_profiles_unaccusative :
    PredictsUnaccusative undergoer ∧ PredictsUnaccusative movingUndergoer := by
  decide

end MartinSchaeferKastner2025
