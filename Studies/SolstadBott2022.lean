module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Semantics.ArgumentStructure.RoleList
public import Linglib.Discourse.Coherence

/-!
# Solstad & Bott (2022): On the Nature of Implicit Causality and Consequentiality

This file formalizes the Two-Mechanism Account of Solstad and Bott. Implicit causality
(I-Caus), the coreference bias of a continuation after *because*, is verb-semantic: on the
authors' Empty Slot Theory, a stimulus argument causes the psychological state the verb
names without the verb saying how, so the argument carries an underspecified proposition
that an explanation fills. Implicit consequentiality (I-Cons), the bias after *and so*, is
discourse-structural: on the Contiguity Principle of Kehler, a consequence continues
from the final state of the prompt's eventuality, held by the experiencer of the state or by
the participant the action affects. Both mechanisms read off a verb class's proto-role grid
(Dowty): `CarriesSlot` is the stimulus label, `HoldsEndState` the experiencer label or
causal affectedness, `ICaus` and `ICons` the resulting coreference predictions, and `Bias`
routes them through the direction of the cause–effect relation a connective signals.

The rival One-Mechanism Account of Crinean and Garnham reads both biases off one causal
decomposition, causes with agents and stimuli alike, consequences with experiencers and
patients, so a continuation about the end-state argument should be a consequence. The
Two-Mechanism Account lets slot filling take precedence over contiguity, so a slot predicate
is continued by an explanation whichever argument the continuation is about. `oneMechanism`
and `twoMechanism` state the two coherence predictions; they agree on the slot argument and
diverge exactly on the end-state argument of a slot predicate, the paper's Asymmetry
Hypothesis. The accounts also part on agent-patient verbs, whose agent is a cause on the
One-Mechanism reading but carries no slot, since it causes by the very action the verb names.

Four sentence-continuation experiments on German stimulus-experiencer (*ärgern*) and
experiencer-stimulus (*bewundern*) verbs test the hypothesis. Experiment 1 confirms the mirror
coreference biases: after *weil* the stimulus argument, after *sodass* the experiencer, with the
two per-verb biases almost perfectly anticorrelated. Experiment 2 (full stop) finds
explanations the most frequent relation for both classes, about three times as frequent as
consequences. Experiment 3 (forced reference) finds explanations at least as frequent as
consequences even when the continuation is forced onto the I-Cons argument, against the
One-Mechanism symmetry. Experiment 4 finds explanatory specifications, continuations giving
the direct cause of the psychological state, almost only in I-Caus-congruent explanations,
and consequence specifications, restatements of the experiencer's state, essentially never:
consequences introduce an eventuality subsequent to the prompt's, as contiguity predicts.

## Implementation notes

The experimental results are reported in prose above; the library's format for
experimental data is pending. The psych grids are the substrate's `psychCausal` and
`psychState`, which are each other's `flip`, so the mirror theorem is one instance of
`bias_flip`. The agent-evocator grid `judgment` follows the paper's description of
Crinean and Garnham: the evocator is causally affected by the agent's act and, through
the verb's presupposition of a preceding eventuality it took part in, the non-agentive cause
of the agent's intention, so it is both the slot argument and the end-state argument.
Agent-patient verbs take the manner-contact grid `mannerContact`.

## References

* [solstad-bott-2022]
* [crinean-garnham-2006]
* [dowty-1991]
* [kehler-2002]
-/

@[expose] public section

namespace SolstadBott2022

open ArgumentStructure Discourse.Coherence

/-- The argument positions of a prompt *Name₁ verb-ed Name₂*. -/
inductive Argument where
  | np1
  | np2
  deriving DecidableEq, Fintype, Repr

/-- The other argument position. -/
def Argument.swap : Argument → Argument
  | .np1 => .np2
  | .np2 => .np1

/-- The proto-role profile a grid assigns to a position. -/
def profileAt (r : RoleList) : Argument → Option EntailmentProfile
  | .np1 => some r.subjectProfile
  | .np2 => r.objectProfile

/-- The grid with subject and object exchanged, when there is an object. -/
def flip (r : RoleList) : Option RoleList :=
  r.objectProfile.map fun o ↦ ⟨o, some r.subjectProfile⟩

theorem profileAt_flip {r r' : RoleList} (h : flip r = some r') (a : Argument) :
    profileAt r' a = profileAt r a.swap := by
  obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 h
  cases a <;> simp [profileAt, Argument.swap, ho]

/-! ### The two mechanisms -/

/-- Mechanism 1, the empty slot. A stimulus causes the psychological state the verb names
without the verb saying how, so it carries an underspecified proposition that an
explanation fills. An agent causes by the action the verb names and carries no slot. -/
def CarriesSlot (p : EntailmentProfile) : Prop := p.toRole = some .stimulus

/-- Mechanism 2, the Contiguity Principle. A consequence continues from the final state of
the prompt's eventuality, held by the experiencer of the psychological state or by the
participant the action affects. -/
def HoldsEndState (p : EntailmentProfile) : Prop :=
  p.toRole = some .experiencer ∨ .causallyAffected ∈ p

instance (p : EntailmentProfile) : Decidable (CarriesSlot p) :=
  inferInstanceAs (Decidable (p.toRole = some .stimulus))

instance (p : EntailmentProfile) : Decidable (HoldsEndState p) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem causation_mem_of_carriesSlot {p : EntailmentProfile} (h : CarriesSlot p) :
    .causation ∈ p :=
  EntailmentProfile.causation_mem_of_toRole_eq_some_stimulus h

theorem holdsEndState_iff_of_carriesSlot {p : EntailmentProfile} (h : CarriesSlot p) :
    HoldsEndState p ↔ .causallyAffected ∈ p := by
  simp [HoldsEndState, CarriesSlot] at *; simp [h]

/-- I-Caus coreference goes to the slot argument. -/
def ICaus (r : RoleList) (a : Argument) : Prop := ∃ p ∈ profileAt r a, CarriesSlot p

/-- I-Cons coreference goes to the end-state argument. -/
def ICons (r : RoleList) (a : Argument) : Prop := ∃ p ∈ profileAt r a, HoldsEndState p

instance (r : RoleList) (a : Argument) : Decidable (ICaus r a) := by
  unfold ICaus; infer_instance

instance (r : RoleList) (a : Argument) : Decidable (ICons r a) := by
  unfold ICons; infer_instance

/-- The connectives of the continuation prompts, German *weil* and *sodass*, the paper's *because*
and *and so*. -/
inductive Connective where
  | because
  | andSo
  deriving DecidableEq, Fintype, Repr

/-- The cause–effect relation a connective signals. -/
def Connective.relation : Connective → Relation
  | .because => .explanation
  | .andSo => .result

/-- A connective elicits a coreference bias toward the slot argument when the relation it signals
seeks its cause in the continuation, and toward the end-state argument when it seeks its effect
there. -/
def Bias (r : RoleList) (c : Connective) (a : Argument) : Prop :=
  match c.relation.causalDirection with
  | some .backward => ICaus r a
  | some .forward => ICons r a
  | none => False

@[simp] theorem bias_because (r : RoleList) (a : Argument) : Bias r .because a ↔ ICaus r a :=
  Iff.rfl

@[simp] theorem bias_andSo (r : RoleList) (a : Argument) : Bias r .andSo a ↔ ICons r a :=
  Iff.rfl

instance (r : RoleList) (c : Connective) (a : Argument) : Decidable (Bias r c a) := by
  cases c
  exacts [decidable_of_iff _ (bias_because r a).symm, decidable_of_iff _ (bias_andSo r a).symm]

theorem icaus_flip {r r' : RoleList} (h : flip r = some r') (a : Argument) :
    ICaus r' a ↔ ICaus r a.swap := by
  simp [ICaus, profileAt_flip h]

theorem icons_flip {r r' : RoleList} (h : flip r = some r') (a : Argument) :
    ICons r' a ↔ ICons r a.swap := by
  simp [ICons, profileAt_flip h]

theorem bias_flip {r r' : RoleList} (h : flip r = some r') (c : Connective) (a : Argument) :
    Bias r' c a ↔ Bias r c a.swap := by
  cases c <;> simp [icaus_flip h, icons_flip h]

/-! ### The psych doublets -/

theorem psychState_eq_flip : flip psychCausal = some psychState := rfl

theorem psych_mirror (c : Connective) (a : Argument) :
    Bias psychState c a ↔ Bias psychCausal c a.swap :=
  bias_flip psychState_eq_flip c a

theorem stimExp_bias (a : Argument) :
    (Bias psychCausal .because a ↔ a = .np1) ∧ (Bias psychCausal .andSo a ↔ a = .np2) := by
  cases a <;> decide

theorem expStim_bias (a : Argument) :
    (Bias psychState .because a ↔ a = .np2) ∧ (Bias psychState .andSo a ↔ a = .np1) := by
  cases a <;> decide

/-! ### The two accounts and the Asymmetry Hypothesis -/

/-- The One-Mechanism Account's I-Caus argument: whichever argument the verb entails to
cause, agent or stimulus alike. -/
def ICausOne (r : RoleList) (a : Argument) : Prop :=
  ∃ p ∈ profileAt r a, .causation ∈ p

instance (r : RoleList) (a : Argument) : Decidable (ICausOne r a) := by
  unfold ICausOne; infer_instance

theorem icausOne_of_icaus {r : RoleList} {a : Argument} (h : ICaus r a) : ICausOne r a :=
  let ⟨p, hp, hs⟩ := h; ⟨p, hp, causation_mem_of_carriesSlot hs⟩

/-- The coherence relation the One-Mechanism Account predicts for a continuation about `a`:
an explanation about a cause argument, a consequence about an end-state argument. -/
def oneMechanism (r : RoleList) (a : Argument) : Option Relation :=
  if ICausOne r a then some .explanation else if ICons r a then some .result else none

/-- The coherence relation the Two-Mechanism Account predicts: slot filling takes
precedence over contiguity, so a slot predicate is continued by an explanation whichever
argument the continuation is about, and a slotless predicate has no preferred relation. -/
def twoMechanism (r : RoleList) : Option Relation :=
  if ∃ a, ICaus r a then some .explanation else none

theorem oneMechanism_of_icaus {r : RoleList} {a : Argument} (h : ICaus r a) :
    oneMechanism r a = some .explanation := by
  simp [oneMechanism, icausOne_of_icaus h]

theorem twoMechanism_of_icaus {r : RoleList} {a : Argument} (h : ICaus r a) :
    twoMechanism r = some .explanation := by
  simp [twoMechanism, (⟨a, h⟩ : ∃ a, ICaus r a)]

theorem asymmetry {r : RoleList} {a b : Argument} (hb : ICaus r b) (ha : ¬ ICausOne r a)
    (he : ICons r a) :
    oneMechanism r a = some .result ∧ twoMechanism r = some .explanation :=
  ⟨by simp [oneMechanism, ha, he], twoMechanism_of_icaus hb⟩

theorem psych_asymmetry :
    oneMechanism psychCausal .np2 = some .result ∧ twoMechanism psychCausal = some .explanation ∧
    oneMechanism psychState .np1 = some .result ∧ twoMechanism psychState = some .explanation := by
  decide

/-! ### The four verb classes -/

/-- The evocator argument of judgement verbs (*criticise*, *congratulate*): affected by the
agent's act and, through the verb's presupposition of a preceding eventuality it took part in,
the non-agentive cause of the agent's intention. -/
def evocator : EntailmentProfile :=
  {.causation, .causallyAffected, .independentExistence}

/-- Agent-evocator verbs: an agent acting on an evocator. -/
def judgment : RoleList := ⟨accomplishmentSubjectProfile, some evocator⟩

/-- The verb classes of the implicit-causality literature. -/
inductive VerbClass where
  | stimExp
  | expStim
  | agentEvocator
  | agentPat
  deriving DecidableEq, Repr

/-- The proto-role grid of each class. -/
def VerbClass.roles : VerbClass → RoleList
  | .stimExp => psychCausal
  | .expStim => psychState
  | .agentEvocator => judgment
  | .agentPat => mannerContact

/-- The class's I-Caus bias, the slot argument if any. -/
def VerbClass.icausBias (c : VerbClass) : Option Argument :=
  [Argument.np1, .np2].find? (decide <| ICaus c.roles ·)

/-- The class's I-Cons bias, the end-state argument if any. -/
def VerbClass.iconsBias (c : VerbClass) : Option Argument :=
  [Argument.np1, .np2].find? (decide <| ICons c.roles ·)

theorem icausBias_eq :
    VerbClass.stimExp.icausBias = some .np1 ∧ VerbClass.expStim.icausBias = some .np2 ∧
    VerbClass.agentEvocator.icausBias = some .np2 ∧ VerbClass.agentPat.icausBias = none := by
  decide

theorem iconsBias_eq :
    VerbClass.stimExp.iconsBias = some .np2 ∧ VerbClass.expStim.iconsBias = some .np1 ∧
    VerbClass.agentEvocator.iconsBias = some .np2 ∧ VerbClass.agentPat.iconsBias = some .np2 := by
  decide

theorem agentEvocator_dual : ICaus judgment .np2 ∧ ICons judgment .np2 := by decide

/-- Where the accounts part on agent-patient verbs: the agent is a cause on the
One-Mechanism reading, so that account predicts a subject bias, but no argument carries a
slot, so the Two-Mechanism Account predicts no I-Caus bias and no preferred relation. -/
theorem agentPat_balanced :
    ICausOne mannerContact .np1 ∧ (∀ a, ¬ ICaus mannerContact a) ∧
    twoMechanism mannerContact = none := by
  decide

end SolstadBott2022
