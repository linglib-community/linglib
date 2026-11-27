module

public import Linglib.Data.Statistics.SolstadBott2022
public import Linglib.Discourse.Coherence
public import Linglib.Semantics.ArgumentStructure.EventStructure.Nucleus
public import Linglib.Semantics.ArgumentStructure.EventStructure.Position
public import Linglib.Semantics.ArgumentStructure.RoleList
public import Mathlib.Logic.Equiv.Defs

/-!
# Solstad & Bott (2022): On the Nature of Implicit Causality and Consequentiality

A continuation of *Name₁ verb-ed Name₂ because …* tends to be about one argument of the verb,
its implicit causality (I-Caus) bias, and a continuation of *… and so …* about one argument, its
implicit consequentiality (I-Cons) bias. This file states two accounts of the biases, each in
its own terms, and tests them on the paper's four continuation experiments.

On the One-Mechanism Account both biases are read off thematic roles. For a role list `r` and
an argument position `a`, `RoleCause r a` holds when the verb entails that the argument causes,
`RoleEffect r a` when it is an experiencer or is causally affected, and `roleBias r` assigns the
first to Explanation and the second to Result.

On the Two-Mechanism Account the biases are read off the event structure of the verb. A template
has a slot, `HasSlot`, when one of its positions is the event of an individual causer, which has
no content for an explanation to repeat. `VerbClass.Bias` assigns Explanation to the actor of a
template with a slot and Result to the undergoer, the holder of the state the eventuality ends
in.

The two accounts give the psych verbs the same biases, mirror images of each other in the two
classes. They part on agent-patient verbs, whose agent causes and has no slot, and on which
relation a continuation stands in: we prove that under forced reference explanations about the
end-state argument outnumber consequences about the slot argument, that most explanations give
the cause of the psychological state exactly when they are about the slot argument, and that
consequences are more frequent after the class whose template has a change.

## Implementation notes

* A stimulus-experiencer verb is given the template `[x CAUSE [BECOME [y ⟨STATE⟩]]]` and an
  experiencer-stimulus verb `[x CAUSE [y ⟨STATE⟩]]`, a caused state with no change, after the
  paper's remark that only the former have an end point.
* The grid `judgment` of agent-evocator verbs follows the paper's report of
  [crinean-garnham-2006]: the evocator is causally affected and is the non-agentive cause of the
  agent's intention.
* Under forced reference to the object of a stimulus-experiencer verb the printed consequences
  (44.2%) exceed the explanations (42.9%), so the precedence of slot filling is stated of the
  two arguments together.

## TODO

* The slot of an agent-evocator verb, which the paper derives from a presupposition, has no
  template.
* The role lists of the two classes are stated beside their templates. No map from a template to
  the profiles of its participants derives one from the other.

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

open ArgumentStructure ArgumentStructure.EventStructure Data.Statistics

/-! ### Positions and relations -/

/-- The other argument of the prompt. -/
def Position.swap : Position → Position
  | .subject => .object
  | .object => .subject

@[simp] theorem Position.swap_swap (a : Position) : a.swap.swap = a := by cases a <;> rfl

/-- The exchange of the two arguments, as a permutation. -/
def Position.swapEquiv : Equiv.Perm Position := Function.Involutive.toPerm swap swap_swap

@[simp] theorem Position.coe_swapEquiv : ⇑Position.swapEquiv = Position.swap := rfl

@[simp] theorem Position.symm_swapEquiv : Position.swapEquiv.symm = Position.swapEquiv := rfl

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

/-! ### The One-Mechanism Account: thematic roles -/

/-- The proto-role profile a role list assigns to a position. -/
def profileAt (r : RoleList) : Position → Option EntailmentProfile
  | .subject => some r.subjectProfile
  | .object => r.objectProfile

/-- The verb entails that the argument causes, as an agent or a stimulus does. -/
def RoleCause (r : RoleList) (a : Position) : Prop := ∃ p ∈ profileAt r a, .causation ∈ p

/-- The argument is an experiencer or is causally affected. -/
def RoleEffect (r : RoleList) (a : Position) : Prop :=
  ∃ p ∈ profileAt r a, p ∈ ThetaRole.profiles .experiencer ∨ .causallyAffected ∈ p

instance (r : RoleList) (a : Position) : Decidable (RoleCause r a) := by
  unfold RoleCause; infer_instance

instance (r : RoleList) (a : Position) : Decidable (RoleEffect r a) := by
  unfold RoleEffect; infer_instance

/-- The bias of a continuation on the One-Mechanism Account: a cause argument for Explanation,
an effect argument for Result, and none otherwise. -/
def roleBias (r : RoleList) : Coherence.Relation → Position → Prop
  | .explanation, a => RoleCause r a
  | .result, a => RoleEffect r a
  | _, _ => False

instance (r : RoleList) (ρ : Coherence.Relation) (a : Position) : Decidable (roleBias r ρ a) := by
  unfold roleBias; split <;> infer_instance

/-- The role list of a class of psych verbs. -/
def VerbClass.roles : VerbClass → RoleList
  | .stimExp => psychCausal
  | .expStim => psychState

/-! ### The Two-Mechanism Account: event structure -/

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

/-- A template has a slot when one of its positions is the event of an individual causer. -/
def HasSlot (t : Template .event) : Prop :=
  ∃ p : Template.Position t .event, p.subterm = .effector

theorem hasSlot_cause_effector {σ : Eventuality} (e : Template σ) :
    HasSlot (.cause .effector e) :=
  ⟨.causing (.here _), rfl⟩

theorem hasSlot_template (v : VerbClass) : HasSlot v.template := by
  cases v <;> exact hasSlot_cause_effector _

-- an agent causes by the action the verb names
theorem not_hasSlot_accomplishment : ¬ HasSlot .accomplishment := by
  rintro ⟨p, hp⟩
  rcases p with _ | _ | ⟨_ | _⟩ | ⟨_ | ⟨_ | _⟩⟩ <;> cases hp

/-- The bias of a continuation on the Two-Mechanism Account: the actor of a template with a slot
for Explanation, the undergoer for Result, and none otherwise. -/
def VerbClass.Bias (v : VerbClass) : Coherence.Relation → Position → Prop
  | .explanation, a => HasSlot v.template ∧ a = v.actor
  | .result, a => a = v.actor.swap
  | _, _ => False

@[simp] theorem VerbClass.bias_explanation {v : VerbClass} {a : Position} :
    v.Bias .explanation a ↔ a = v.actor :=
  and_iff_right (hasSlot_template v)

@[simp] theorem VerbClass.bias_result {v : VerbClass} {a : Position} :
    v.Bias .result a ↔ a = v.actor.swap := Iff.rfl

instance (v : VerbClass) (ρ : Coherence.Relation) (a : Position) : Decidable (v.Bias ρ a) := by
  unfold VerbClass.Bias
  split
  · exact decidable_of_iff _ VerbClass.bias_explanation.symm
  · infer_instance
  · infer_instance

/-- Stimulus-experiencer and experiencer-stimulus verbs have mirror-image biases. -/
theorem psych_mirror (ρ : Coherence.Relation) (a : Position) :
    VerbClass.expStim.Bias ρ a ↔ VerbClass.stimExp.Bias ρ a.swap := by
  unfold VerbClass.Bias
  split <;> cases a <;> simp [hasSlot_template, VerbClass.actor, Position.swap]

-- the mirror biases do not tell the two accounts apart
theorem bias_iff_roleBias (v : VerbClass) (c : Connective) (a : Position) :
    v.Bias c.relation a ↔ roleBias v.roles c.relation a := by
  cases v <;> cases c <;> cases a <;> decide

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

/-! ### Coreference (Experiments 1 and 2) -/

/-- After each connective, more continuations refer to an argument than to the other iff the
relation of the connective is biased to it. -/
theorem bias_iff_coreference (c : Connective) (v : VerbClass) (a : Position) :
    v.Bias c.relation a ↔
      (coreference c v a.swap).count < (coreference c v a).count := by
  cases c <;> cases v <;> cases a <;> decide

-- Table 3
theorem bias_iff_coreferenceByRelation {ρ : Relation} (hρ : ρ ≠ .contrast) (v : VerbClass)
    (a : Position) :
    v.Bias ρ.toCoherence a ↔
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
theorem consequence_swap_lt_explanation (v : VerbClass) (a : Position) (h : v.Bias .result a) :
    (forcedReference v a.swap).consequence.toRat < (forcedReference v a).explanation.toRat := by
  revert v a; decide +kernel

-- Section 4.4
theorem explanation_swap_lt_of_bias (v : VerbClass) (a : Position) (h : v.Bias .explanation a) :
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

theorem roleCause_roleEffect_judgment :
    RoleCause judgment .object ∧ RoleEffect judgment .object := by
  decide

-- the agent of an agent-patient verb is a cause on its role and has no slot
theorem roleCause_mannerContact :
    RoleCause mannerContact .subject ∧ RoleEffect mannerContact .object := by
  decide

end SolstadBott2022
