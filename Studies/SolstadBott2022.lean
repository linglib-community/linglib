module

public import Linglib.Data.Statistics.SolstadBott2022
public import Linglib.Discourse.Coherence
public import Linglib.Semantics.ArgumentStructure.EventStructure.Nucleus
public import Linglib.Semantics.ArgumentStructure.RoleList
public import Mathlib.Logic.Equiv.Defs

/-!
# Solstad & Bott (2022): On the Nature of Implicit Causality and Consequentiality

A continuation of *Name₁ verb-ed Name₂ because …* tends to be about one argument of the verb,
its implicit causality (I-Caus) bias, and a continuation of *… and so …* about one argument, its
implicit consequentiality (I-Cons) bias. This file states the Two-Mechanism Account of the two
biases and tests it on the paper's four continuation experiments.

For a verb class with role list `r` and an argument position `a`:

* `ICaus r a` holds when the argument carries a slot: the verb entails that it causes and
  nothing about how;
* `ICons r a` holds when the argument holds the end state: it is the experiencer of a state or
  is causally affected;
* `Bias r ρ a` is the bias of a continuation in the coherence relation `ρ`: `ICaus` for
  Explanation and `ICons` for Result.

Stimulus-experiencer and experiencer-stimulus verbs have mirror-image biases. In event structure
the slot is a causing subevent with no content, and filling it with a manner gives the
accomplishment, which has none.

We prove four things about the printed results:

* after *weil* and *sodass*, and for explanations and consequences after a full stop, most
  continuations are about the argument `Bias` gives;
* under forced reference, explanations about the end-state argument outnumber consequences about
  the slot argument;
* most explanations give the cause of the psychological state exactly when they are about the
  slot argument;
* consequences are more frequent after the class whose template has a change.

## Implementation notes

* A role list has an optional object, so `ICaus` and `ICons` quantify over the profile at a
  position.
* The grid `judgment` of agent-evocator verbs follows the paper's report of
  [crinean-garnham-2006]: the evocator is causally affected and is the non-agentive cause of the
  agent's intention. The paper derives its slot from a presupposition instead.
* `HoldsEndState` names the roles the end state falls to. The paper takes the end state to
  belong to the eventuality; a role list has none.
* An experiencer-stimulus verb is given the template `[x CAUSE [y ⟨STATE⟩]]`, a caused state
  with no change.
* Under forced reference to the object of a stimulus-experiencer verb the printed consequences
  (44.2%) exceed the explanations (42.9%), so the precedence of slot filling is stated of the
  two arguments together.

## TODO

* The slot of an agent-evocator verb is not derived from its presupposition.
* The biases are stated of the role lists and shown to agree with the templates on the two
  classes tested. No map from a template to the profiles of its participants derives one from
  the other.

## References

* [solstad-bott-2022]
* [crinean-garnham-2006]
* [dowty-1991]
* [kehler-2002]
* [moens-steedman-1988]
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

/-- An argument carries a slot when its profile has causation and no volition, sentience or
movement. -/
def CarriesSlot (p : EntailmentProfile) : Prop := p ∈ ThetaRole.profiles .stimulus

/-- An argument holds the end state when it is an experiencer or is causally affected. -/
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

/-- The I-Caus argument on the One-Mechanism Account: an argument the verb entails to cause. -/
def ICausOne (r : RoleList) (a : Position) : Prop := ∃ p ∈ profileAt r a, .causation ∈ p

instance (r : RoleList) (a : Position) : Decidable (ICaus r a) := by
  unfold ICaus; infer_instance

instance (r : RoleList) (a : Position) : Decidable (ICons r a) := by
  unfold ICons; infer_instance

instance (r : RoleList) (a : Position) : Decidable (ICausOne r a) := by
  unfold ICausOne; infer_instance

theorem icausOne_of_icaus (h : ICaus r a) : ICausOne r a :=
  let ⟨p, hp, hs⟩ := h; ⟨p, hp, hs.causation_mem⟩

/-- The bias of a continuation in a coherence relation: the slot argument for Explanation, the
end-state argument for Result, and none otherwise. -/
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

/-- Stimulus-experiencer and experiencer-stimulus verbs have mirror-image biases. -/
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

/-- The accomplishment is the stimulus-experiencer template with a manner on its causing
event. -/
theorem denote_accomplishment_iff {Entity : Type*} {State Event : Type u}
    {M : Model State Event} {θ : Entity → Event → Prop} {P : Entity → State → Prop}
    {Q : Event → Prop} {y x : Entity} {v : Event} :
    Template.accomplishment.denote M θ P Q y x v ↔
      VerbClass.stimExp.template.denote M θ P Q y x v ∧ Q v :=
  Template.denote_cause_act

-- Figure 1
theorem denote_template_stimExp_iff {Entity : Type*} {State Event : Type u}
    {M : Model State Event} {θ : Entity → Event → Prop} {P : Entity → State → Prop}
    {Q : Event → Prop} {y x : Entity} {v : Event} :
    VerbClass.stimExp.template.denote M θ P Q y x v ↔
      θ y v ∧ ∃ n : Nucleus M.cause M.become, n.preparation = v ∧ P x n.consequent :=
  Template.denote_cause_achievement_iff

-- Section 3.3
theorem consequence_lt_iff_result (v w : VerbClass) :
    (relations v .consequence).percent.toRat < (relations w .consequence).percent.toRat ↔
      .result ∉ v.template.kinds ∧ .result ∈ w.template.kinds := by
  revert v w; decide +kernel

end EventStructure

/-! ### Coreference (Experiments 1 and 2) -/

/-- After each connective, more continuations refer to an argument than to the other iff the
relation of the connective is biased to it. -/
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


/-- Under forced reference, explanations about the end-state argument outnumber consequences
about the other argument. -/
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

/-- Most explanations give the cause of the psychological state iff the pronoun is congruent
with the bias, and most consequences do not restate the state. -/
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
