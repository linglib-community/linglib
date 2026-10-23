module

public import Mathlib.Order.Bounds.Basic
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Core.Relation.ReflTransGen
public import Studies.Pesetsky1995

/-!
# Kim (2024): On the Argument Structure of Object Experiencer Verbs

This file formalizes the Uniform Projection Hypothesis of [kim-2024] for the object-experiencer
verbs, [belletti-rizzi-1988]'s Class II. Like causatives in general, every such verb projects just
a Cause and an Experiencer. The standard view since [pesetsky-1995] adds a Target or Subject
Matter as a third role. On the uniform view, the eventive–stative ambiguity that runs through the
class does not come from the arguments projected. It comes from what the Cause refers to. An emotion
arises along a causal chain, (185): the Experiencer evaluates a percept, the evaluation yields a
subject matter, the Experiencer's mind-internal counterpart of the percept, and attention to the
subject matter gives rise to the emotion. The eventive reading denotes the whole chain, its Cause
the percept, and the stative reading the compact chain from the subject matter on, a maintenance
relation: *The doctor's letter worried John* against *His declining health worried John*.

The thesis reads three properties off where the Cause sits on this chain.

* A reading is eventive when its chain contains the evaluation, the change that brings a new
  subject matter into being, which is when the Cause names the percept
  (`EmotionChain.isEventive_iff`).
* The subject is intensional when the Cause is mind-internal. The mind-internal causes are the
  members of the chain past the percept, so intensionality and stativity coincide
  (`EmotionChain.isMindInternal_iff_not_isEventive`). Chapter 4 reports this correlation as a new
  finding.
* The Onset Condition (316) maps every causal participant of a causal predicate to the onset of
  the chain the predicate denotes (`OnsetCondition`). The thesis motivates it on causatives in
  general: events integrated into one predicate coincide, so a causal *by*-phrase is controlled
  by the Cause (`OnsetCondition.eq`), and an event downstream of the onset cannot be integrated
  (`not_onsetCondition_of_lt`), as in *\*John killed the water deer by the poacher shooting them*
  (`not_onsetCondition_shooting`). On the eventive reading the subject matter lies downstream of the
  percept, so a Subject Matter cannot join the Cause (`tsm_restriction`), while it heads the chain
  of a predicate without a Cause (`subjectMatter_onset_without_cause`). The T/SM restriction thus
  follows without a ban of its own, and the thesis rules out a Target alongside a Cause just as
  [pesetsky-1995] does (`tsm_restriction_agrees`).

## Implementation notes

The Onset Condition is stated for any causal chain, a set of events partially ordered by causal
precedence, whose onset is its least event, `IsLeast`. Each chain of the thesis is drawn as a
relation of immediate causation (`Causes`), and ordered by its reflexive transitive closure. The
chain of an emotion is `EmotionChain`, and the chain a Class II predicate denotes is the final
segment `Set.Ici` from the member its Cause refers to. The thesis finds no reliable diagnostic that
tells Target from Subject Matter and calls every object of emotion a Subject Matter, so both of
[pesetsky-1995]'s stimulus types refer to the one member `EmotionChain.subjectMatter`. The agentive
reading, which the thesis sets aside with the literature, is not represented.

## TODO

The maintenance relation that the stative reading denotes, (148), is not formalized: its
maintaining eventuality is contemporaneous with the maintained state, which continues only as
long as the maintaining eventuality does. The Onset Condition is stated here over the members of
the chain, and on the stative reading the Cause itself refers to the subject matter. Excluding a
Subject Matter adjunct there needs participants mapped to eventualities rather than to members of
the chain. The thesis derives the restriction for a Cause that refers to the percept (§5.3).

## References

* [kim-2024]
* [belletti-rizzi-1988]
* [pesetsky-1995]
-/

@[expose] public section

namespace Kim2024

/-! ### The Onset Condition -/

section Onset

variable {E : Type*} [PartialOrder E] {s : Set E} {e e' : E}

/-- The Onset Condition (316): an event semantically integrated into a causal predicate is mapped
to the onset of the causal chain `s` that the predicate denotes, the least event of `s` in causal
precedence. -/
def OnsetCondition (s : Set E) (e : E) : Prop := IsLeast s e

/-- Events integrated into one causal predicate are the same event, the onset of its chain (323). -/
theorem OnsetCondition.eq (h : OnsetCondition s e) (h' : OnsetCondition s e') : e = e' :=
  IsLeast.unique h h'

theorem not_onsetCondition_of_lt (h : OnsetCondition s e) (hlt : e < e') : ¬ OnsetCondition s e' :=
  fun h' ↦ (h.eq h' ▸ hlt).false

end Onset

/-! ### A killing, (312)–(314) -/

/-- The events of (312): John hires a poacher, the poacher shoots the water deer, and the deer
die. -/
inductive KillingEvent where
  | hiring
  | shooting
  | dying
  deriving DecidableEq, Fintype, Repr

/-- The causal chain of (312): the hiring causes the shooting, which causes the dying. -/
def KillingEvent.Causes (a b : KillingEvent) : Prop :=
  a = .hiring ∧ b = .shooting ∨ a = .shooting ∧ b = .dying

instance : DecidableRel KillingEvent.Causes := fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The events in order of causal precedence. -/
instance : LinearOrder KillingEvent :=
  linearOrderOfCovers KillingEvent.Causes (OrderDual.toDual ∘ KillingEvent.ctorIdx) (by decide)
    (by decide)

/-- In (313) *John killed the water deer by hiring a poacher*, the hiring is the onset of the
denoted chain. -/
theorem onsetCondition_hiring : OnsetCondition (Set.univ : Set KillingEvent) .hiring :=
  isLeast_univ_iff.2 fun e ↦ by cases e <;> decide

/-- In (314a) *\*John killed the water deer by the poacher shooting them*, the shooting is not the
onset of the chain. -/
theorem not_onsetCondition_shooting : ¬ OnsetCondition (Set.univ : Set KillingEvent) .shooting :=
  not_onsetCondition_of_lt onsetCondition_hiring (by decide)

/-! ### The causal chain of an emotion -/

/-- The members of the causal chain along which an emotion arises, (185): a percept, the subject
matter that the Experiencer's evaluation of the percept yields, and the emotion that the
Experiencer's attention to the subject matter gives rise to. -/
inductive EmotionChain where
  /-- The percept, a mind-external stimulus. -/
  | percept
  /-- The subject matter, the Experiencer-internal counterpart of the percept. -/
  | subjectMatter
  /-- The Experiencer's emotional state. -/
  | emotion
  deriving DecidableEq, Fintype, Repr

variable {c : EmotionChain}

namespace EmotionChain

/-- The arrows of (185): the Experiencer's evaluation of the percept yields the subject matter,
and the Experiencer's attention to the subject matter gives rise to the emotion. -/
def Causes (a b : EmotionChain) : Prop :=
  a = .percept ∧ b = .subjectMatter ∨ a = .subjectMatter ∧ b = .emotion

instance : DecidableRel Causes := fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The members of the chain in order of causal precedence. -/
instance : LinearOrder EmotionChain :=
  linearOrderOfCovers Causes (OrderDual.toDual ∘ EmotionChain.ctorIdx) (by decide) (by decide)

/-- A reading is eventive when the chain from the member its Cause refers to contains the
Experiencer's evaluation of a percept. The evaluation brings a new subject matter into being and
so changes the Experiencer's state. The chain of a stative reading starts after the evaluation,
and the subject matter maintains the emotion as long as the Experiencer's attention dwells on
it. -/
def IsEventive (c : EmotionChain) : Prop := percept ∈ Set.Ici c

/-- A member of the chain is mind-internal when the Experiencer's evaluation of the percept
produced it. Its content then reflects the Experiencer's knowledge state, which is why a Cause
referring to it is intensional (§4.5). -/
def IsMindInternal (c : EmotionChain) : Prop := percept < c

instance : DecidablePred IsEventive := fun c ↦ inferInstanceAs (Decidable (c ≤ percept))

instance : DecidablePred IsMindInternal := fun c ↦ inferInstanceAs (Decidable (percept < c))

theorem eq_percept_or_eq_subjectMatter (h : c < emotion) : c = percept ∨ c = subjectMatter := by
  revert c; decide

theorem isEventive_iff : c.IsEventive ↔ c = percept := by
  revert c; decide

/-- The subject of a Class II verb is intensional exactly when the verb is stative (Chapter 4). -/
theorem isMindInternal_iff_not_isEventive : c.IsMindInternal ↔ ¬ c.IsEventive :=
  lt_iff_not_ge

theorem subjectMatter_mem_Ici (h : c < emotion) : subjectMatter ∈ Set.Ici c := by
  revert c; decide

end EmotionChain

open EmotionChain

/-! ### The T/SM restriction -/

/-- On the eventive reading a Subject Matter cannot satisfy the Onset Condition, which is the T/SM
restriction (42), (262). -/
theorem tsm_restriction (h : c.IsEventive) : ¬ OnsetCondition (Set.Ici c) subjectMatter :=
  not_onsetCondition_of_lt isLeast_Ici (h.trans_lt (by decide))

/-- A predicate without a Cause (43) lets a Subject Matter satisfy the Onset Condition. -/
theorem subjectMatter_onset_without_cause : OnsetCondition (Set.Ici subjectMatter) subjectMatter :=
  isLeast_Ici

/-! ### The comparison with Pesetsky (1995) -/

/-- Both [pesetsky-1995] and the Onset Condition rule out a Cause alongside a Target (42a) or a
Subject Matter (42c). -/
theorem tsm_restriction_agrees (s : Pesetsky1995.StimulusType) (h : c.IsEventive) :
    ¬ Pesetsky1995.canReachV (Pesetsky1995.stimulusCascade s).spine 1 ∧
      ¬ OnsetCondition (Set.Ici c) subjectMatter :=
  ⟨Pesetsky1995.tsm_restriction s, tsm_restriction h⟩

end Kim2024
