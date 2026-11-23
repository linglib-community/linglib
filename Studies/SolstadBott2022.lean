module

public import Linglib.Data.Statistics.SolstadBott2022
public import Linglib.Discourse.Coherence
public import Linglib.Semantics.ArgumentStructure.EventStructure.Denotation
public import Linglib.Semantics.ArgumentStructure.RoleList
public import Mathlib.Logic.Equiv.Defs

/-!
# Solstad & Bott (2022): On the Nature of Implicit Causality and Consequentiality

A continuation of *Name₁ verb-ed Name₂ because …* tends to be about one argument of the verb,
its implicit causality (I-Caus) bias, and a continuation of *… and so …* about one argument, its
implicit consequentiality (I-Cons) bias. This file states the Two-Mechanism Account of the two
biases over the proto-role grid of a verb class.

An argument carries a slot, `CarriesSlot`, when the verb entails that it causes and nothing about
how: its profile has causation without volition, sentience or movement, the Stimulus of Dowty. An
explanation fills the slot, so `ICaus r a` holds of a position whose profile carries one. An
argument holds the end state, `HoldsEndState`, when it is the experiencer of a state or is
causally affected. A consequence continues from the end state of the prompt's eventuality, so
`ICons r a` holds of a position whose profile holds it. `Bias r ρ a` is the bias of a
continuation that stands in the coherence relation `ρ` to the prompt, `ICaus` for Explanation
and `ICons` for Result.

The grids of stimulus-experiencer and experiencer-stimulus verbs exchange subject and object, so
their biases are mirror images under every relation (`psych_mirror`). On the One-Mechanism
Account of Crinean and Garnham the I-Caus argument is whichever argument the verb entails to
cause, `ICausOne`, which includes every slot argument (`icausOne_of_icaus`) and also the agent of
an agent-patient verb, which carries no slot (`not_icaus_mannerContact`).

The mechanisms read the event structure of the verb. A stimulus-experiencer verb is a caused
change of state with an individual causer, `[x CAUSE [BECOME [y ⟨STATE⟩]]]`, and an
experiencer-stimulus verb a caused state with no change, `[x CAUSE [y ⟨STATE⟩]]`. The slot is the
causing subevent, which has no content beyond its effector (`HasSlot`): the slot argument is the
actor of a template with a slot and the end-state argument its undergoer (`icaus_iff_actor`,
`icons_iff_undergoer`). Giving the causing subevent a manner yields the accomplishment
`[[x ACT⟨MANNER⟩] CAUSE [BECOME [y ⟨STATE⟩]]]`, which has no slot (`denote_accomplishment_iff`).
Only the stimulus-experiencer template has a change, the end point a consequence continues from,
and consequences after a full stop are more frequent for that class
(`consequence_lt_iff_result`).

The paper's four continuation experiments on German psych verbs are read from the generated
tables. The referent of most continuations is the one `Bias` gives, after *weil* and *sodass*
(`bias_iff_coreference`) and for explanations and consequences after a full stop
(`bias_iff_coreferenceByRelation`). Under forced reference, explanations about the end-state
argument outnumber consequences about the slot argument (`consequence_swap_lt_explanation`),
where a single causal relation read in both directions would have them alike. Explanations
specify the cause of the psychological state just when they are about the slot argument
(`specifying_iff_congruent`).

## Implementation notes

* A position's profile is read from a role list, whose object is optional, so `ICaus` and `ICons`
  quantify over the profile at a position.
* The slots of psych verbs and of agent-evocator verbs have different sources in the paper, the
  unspecified cause of a psychological state and the presupposition of an earlier eventuality.
  The grid `judgment` follows the paper's report of Crinean and Garnham, on which the evocator is
  causally affected and the non-agentive cause of the agent's intention, so that one predicate
  on profiles covers both.
* The paper takes the end state to belong to the eventuality and its correlation with thematic
  roles to be derivative. A role list has no eventuality, so `HoldsEndState` names the roles the
  end state falls to.
* Under forced reference to the object of a stimulus-experiencer verb, the printed consequences
  (44.2%) exceed the explanations (42.9%). The precedence of slot filling over contiguity is
  therefore stated of the two arguments together (`consequence_lt_explanation`), as the paper
  tests it.

## TODO

* The slot of an agent-evocator verb is not derived from its presupposition.
* The biases are stated of the role lists and shown to agree with the templates on the two
  classes tested; no map from a template to the profiles of its actor and undergoer derives
  one from the other.

## References

* [solstad-bott-2022]
* [crinean-garnham-2006]
* [dowty-1991]
* [kehler-2002]
-/

@[expose] public section

universe u

namespace SolstadBott2022

open ArgumentStructure Data.Statistics

/-! ### Positions -/

/-- The other argument of the prompt. -/
def Position.swap : Position → Position
  | .subject => .object
  | .object => .subject

@[simp] theorem Position.swap_swap (a : Position) : a.swap.swap = a := by cases a <;> rfl

/-- The exchange of the two arguments, as a permutation. -/
def Position.swapEquiv : Equiv.Perm Position := Function.Involutive.toPerm swap swap_swap

@[simp] theorem Position.coe_swapEquiv : ⇑Position.swapEquiv = Position.swap := rfl

@[simp] theorem Position.symm_swapEquiv : Position.swapEquiv.symm = Position.swapEquiv := rfl

/-- The proto-role profile a grid assigns to a position. -/
def profileAt (r : RoleList) : Position → Option EntailmentProfile
  | .subject => some r.subjectProfile
  | .object => r.objectProfile

theorem profileAt_psychState (a : Position) :
    profileAt psychState a = profileAt psychCausal a.swap := by
  cases a <;> rfl

/-! ### The two mechanisms -/

variable {r r' : RoleList} {p : EntailmentProfile} {a : Position}

/-- An argument carries a slot when the verb entails that it causes and nothing about how. An
agent causes by the action the verb names and carries none. -/
def CarriesSlot (p : EntailmentProfile) : Prop := p ∈ ThetaRole.profiles .stimulus

/-- An argument holds the end state of the eventuality when it is the experiencer of a state or
is causally affected. -/
def HoldsEndState (p : EntailmentProfile) : Prop :=
  p ∈ ThetaRole.profiles .experiencer ∨ .causallyAffected ∈ p

instance : DecidablePred CarriesSlot := fun p ↦
  inferInstanceAs (Decidable (p ∈ ThetaRole.profiles .stimulus))

instance : DecidablePred HoldsEndState := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

theorem CarriesSlot.causation_mem (h : CarriesSlot p) : .causation ∈ p :=
  (ThetaRole.mem_profiles_stimulus.1 h).1

theorem CarriesSlot.holdsEndState_iff (h : CarriesSlot p) :
    HoldsEndState p ↔ .causallyAffected ∈ p :=
  or_iff_right fun he ↦ Set.disjoint_left.1
    (ThetaRole.pairwiseDisjoint_profiles (by simp) (by simp) (by decide)) he h

/-- The I-Caus argument of a grid, the one that carries a slot. -/
def ICaus (r : RoleList) (a : Position) : Prop := ∃ p ∈ profileAt r a, CarriesSlot p

/-- The I-Cons argument of a grid, the one that holds the end state. -/
def ICons (r : RoleList) (a : Position) : Prop := ∃ p ∈ profileAt r a, HoldsEndState p

/-- The I-Caus argument on the One-Mechanism Account, whichever argument the verb entails to
cause. -/
def ICausOne (r : RoleList) (a : Position) : Prop := ∃ p ∈ profileAt r a, .causation ∈ p

instance (r : RoleList) (a : Position) : Decidable (ICaus r a) := by
  unfold ICaus; infer_instance

instance (r : RoleList) (a : Position) : Decidable (ICons r a) := by
  unfold ICons; infer_instance

instance (r : RoleList) (a : Position) : Decidable (ICausOne r a) := by
  unfold ICausOne; infer_instance

theorem icausOne_of_icaus (h : ICaus r a) : ICausOne r a :=
  let ⟨p, hp, hs⟩ := h; ⟨p, hp, hs.causation_mem⟩

/-- The bias of a continuation that stands in a coherence relation to the prompt: toward the slot
argument when the continuation explains the prompt, toward the end-state argument when it is a
result of it, and none otherwise. -/
def Bias (r : RoleList) : Coherence.Relation → Position → Prop
  | .explanation, a => ICaus r a
  | .result, a => ICons r a
  | _, _ => False

@[simp] theorem bias_explanation : Bias r .explanation a ↔ ICaus r a := Iff.rfl

@[simp] theorem bias_result : Bias r .result a ↔ ICons r a := Iff.rfl

instance (r : RoleList) (ρ : Coherence.Relation) (a : Position) : Decidable (Bias r ρ a) := by
  unfold Bias; split <;> infer_instance

theorem bias_congr (h : ∀ a, profileAt r' a = profileAt r a.swap) (ρ : Coherence.Relation)
    (a : Position) : Bias r' ρ a ↔ Bias r ρ a.swap := by
  unfold Bias; split <;> simp [ICaus, ICons, h]

/-! ### The psych verbs -/

/-- Stimulus-experiencer and experiencer-stimulus verbs have mirror-image biases under every
coherence relation. -/
theorem psych_mirror (ρ : Coherence.Relation) (a : Position) :
    Bias psychState ρ a ↔ Bias psychCausal ρ a.swap :=
  bias_congr profileAt_psychState ρ a

theorem bias_psychCausal (a : Position) :
    (Bias psychCausal .explanation a ↔ a = .subject) ∧
      (Bias psychCausal .result a ↔ a = .object) := by
  cases a <;> decide

/-- The proto-role grid of a class of psych verbs. -/
def VerbClass.roles : VerbClass → RoleList
  | .stimExp => psychCausal
  | .expStim => psychState

/-- The coherence relation a connective signals. -/
def Connective.relation : Connective → Coherence.Relation
  | .because => .explanation
  | .andSo => .result

/-- The relation a connective signals, as an embedding. -/
def Connective.relationEmbedding : Connective ↪ Coherence.Relation :=
  ⟨relation, by decide⟩

@[simp] theorem Connective.coe_relationEmbedding :
    ⇑Connective.relationEmbedding = Connective.relation := rfl

/-- The paper's discourse relations in Kehler's classification. -/
def Relation.toCoherence : Relation → Coherence.Relation
  | .explanation => .explanation
  | .consequence => .result
  | .contrast => .contrast

/-- The paper's discourse relations, as an embedding into Kehler's. -/
def Relation.toCoherenceEmbedding : Relation ↪ Coherence.Relation :=
  ⟨toCoherence, by decide⟩

@[simp] theorem Relation.coe_toCoherenceEmbedding :
    ⇑Relation.toCoherenceEmbedding = Relation.toCoherence := rfl

/-! ### Event structure -/

section EventStructure

open EventStructure

/-- The event structure of a class of psych verbs: a caused change of state with an individual
causer, `[x CAUSE [BECOME [y ⟨STATE⟩]]]`, or a caused state with no change,
`[x CAUSE [y ⟨STATE⟩]]`. -/
def VerbClass.template : VerbClass → Template .event
  | .stimExp => .cause .effector .achievement
  | .expStim => .cause .effector .state

/-- The position of the template's actor, the stimulus. -/
def VerbClass.actor : VerbClass → Position
  | .stimExp => .subject
  | .expStim => .object

/-- A template has a slot when its causing subevent has no content beyond its effector. -/
def HasSlot : Template .event → Prop
  | .cause .effector _ => True
  | _ => False

instance : DecidablePred HasSlot := fun t ↦ by
  unfold HasSlot; split <;> infer_instance

theorem hasSlot_template (v : VerbClass) : HasSlot v.template := by cases v <;> trivial

theorem not_hasSlot_accomplishment : ¬ HasSlot .accomplishment := id

theorem icaus_iff_actor (v : VerbClass) (a : Position) :
    ICaus v.roles a ↔ HasSlot v.template ∧ a = v.actor := by
  cases v <;> cases a <;> decide

theorem icons_iff_undergoer (v : VerbClass) (a : Position) :
    ICons v.roles a ↔ a = v.actor.swap := by
  cases v <;> cases a <;> decide

/-- A stimulus-experiencer verb whose causing eventuality is given a manner denotes as the
accomplishment with that manner, which has no slot. -/
theorem denote_accomplishment_iff {Entity : Type*} {State Event : Type u}
    {M : Model State Event} {θ : Entity → Event → Prop} {P : Entity → State → Prop}
    {Q : Event → Prop} {y x : Entity} {v : Event} :
    Template.accomplishment.denote M θ P Q y x v ↔
      VerbClass.stimExp.template.denote M θ P Q y x v ∧ Q v :=
  Template.denote_cause_act

-- Section 3.3
theorem consequence_lt_iff_result (v w : VerbClass) :
    (relations v .consequence).percent.toRat < (relations w .consequence).percent.toRat ↔
      .result ∉ v.template.kinds ∧ .result ∈ w.template.kinds := by
  revert v w; decide +kernel

end EventStructure

/-! ### Coreference (Experiments 1 and 2) -/

/-- After *weil* and after *sodass*, more continuations refer to an argument than to the other
exactly when the connective's relation is biased to it, for both verb classes. -/
theorem bias_iff_coreference (c : Connective) (v : VerbClass) (a : Position) :
    Bias v.roles c.relation a ↔
      (coreference c v a.swap).count < (coreference c v a).count := by
  cases c <;> cases v <;> cases a <;> decide

-- Table 3
theorem bias_iff_coreferenceByRelation {ρ : Relation} (hρ : ρ ≠ .contrast) (v : VerbClass)
    (a : Position) :
    Bias v.roles ρ.toCoherence a ↔
      (coreferenceByRelation ρ v a.swap).count < (coreferenceByRelation ρ v a).count := by
  cases ρ <;> cases v <;> cases a <;> first | decide | exact absurd rfl hρ

-- Table 3
theorem contrast_object (v : VerbClass) :
    (coreferenceByRelation .contrast v .subject).count <
      (coreferenceByRelation .contrast v .object).count := by
  cases v <;> decide

-- Tables 1 and 3
theorem roundsPercent_coreference :
    (∀ c v a, (coreference c v a).percent.RoundsPercent (coreference c v a).count
      ((coreference c v .subject).count + (coreference c v .object).count)) ∧
    ∀ ρ v a, (coreferenceByRelation ρ v a).percent.RoundsPercent
      (coreferenceByRelation ρ v a).count
      ((coreferenceByRelation ρ v .subject).count + (coreferenceByRelation ρ v .object).count) := by
  decide

/-! ### Coherence (Experiments 2 and 3) -/

-- Section 3.3
theorem half_lt_explanation (v : VerbClass) :
    50 < (relations v .explanation).percent.toRat := by
  revert v; decide +kernel


/-- When a continuation must be about a given argument, explanations about the end-state argument
outnumber consequences about the other argument, for both verb classes. -/
theorem consequence_swap_lt_explanation (v : VerbClass) (a : Position) (h : ICons v.roles a) :
    (forcedReference v a.swap).consequence.toRat < (forcedReference v a).explanation.toRat := by
  revert v a; decide +kernel

-- Section 4.4
theorem explanation_swap_lt_of_icaus (v : VerbClass) (a : Position) (h : ICaus v.roles a) :
    (forcedReference v a.swap).explanation.toRat < (forcedReference v a).explanation.toRat := by
  revert v a; decide +kernel

-- Section 4.4
theorem consequence_lt_explanation (v : VerbClass) :
    (forcedReference v .subject).consequence.toRat +
        (forcedReference v .object).consequence.toRat <
      (forcedReference v .subject).explanation.toRat +
        (forcedReference v .object).explanation.toRat := by
  revert v; decide +kernel

/-! ### Specifications (Experiment 4) -/

/-- Most explanations give the cause of the psychological state exactly when the prompt's pronoun
is congruent with the bias, and most consequences do not restate the state in either case. -/
theorem specifying_iff_congruent (v : VerbClass) (c : Congruency) :
    ((specifications v c).explanationOther < (specifications v c).explanationSpecifying ↔
        c = .congruent) ∧
      (specifications v c).consequenceSpecifying < (specifications v c).consequenceOther := by
  cases v <;> cases c <;> decide

-- Table 4
theorem roundsPercent_specifications (v : VerbClass) (c : Congruency) :
    (specifications v c).explanationSpecifyingPercent.RoundsPercent
        (specifications v c).explanationSpecifying
        ((specifications v c).explanationSpecifying + (specifications v c).explanationOther) ∧
      (specifications v c).consequenceSpecifyingPercent.RoundsPercent
        (specifications v c).consequenceSpecifying
        ((specifications v c).consequenceSpecifying + (specifications v c).consequenceOther) := by
  cases v <;> cases c <;> decide

/-! ### Agent-evocator and agent-patient verbs -/

/-- The evocator argument of judgement verbs (*criticise*, *congratulate*): affected by the
agent's act and, through the verb's presupposition of an earlier eventuality it took part in,
the non-agentive cause of the agent's intention. -/
def evocator : EntailmentProfile :=
  {.causation, .causallyAffected, .independentExistence}

/-- Agent-evocator verbs: an agent acting on an evocator. -/
def judgment : RoleList := ⟨accomplishmentSubjectProfile, some evocator⟩

theorem icaus_icons_judgment : ICaus judgment .object ∧ ICons judgment .object := by decide

theorem not_icaus_mannerContact :
    ICausOne mannerContact .subject ∧ (∀ a, ¬ ICaus mannerContact a) ∧
      ICons mannerContact .object := by
  decide

end SolstadBott2022
