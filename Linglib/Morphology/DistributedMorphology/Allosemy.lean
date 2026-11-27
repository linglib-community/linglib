module

public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Data.Fintype.Option
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Linglib.Morphology.DistributedMorphology.Basic

/-!
# Allosemy

Allosemy is contextual variation in the meaning of one functional head, the counterpart at LF of
allomorphy: the denotations of a head are listed with the contexts they are inserted in, as its
exponents are, so an alloseme is a `VocabularyItem` whose exponent is a denotation. A head may be
semantically zero, the identity function, and its allosemes are its contentful ones with a zero
adjoined. The allosemes `licensed` in a context are those whose items apply, and
[a richer context licenses more of them](##licensed_subset_licensed); where the items compete,
the Subset Principle [picks a licensed one](##mem_licensed_of_subsetPrinciple). The readings of a
deverbal noun [are the allosemes of n](##Nominalizer.Alloseme.readingEquiv), the complex event
reading being the zero alloseme, under which the noun has the meaning of the verb.

## Implementation notes

* Which allosemes of v and n combine is not listed. Every combination is possible whose result is
  interpretable ([wood-2023]), and that is decided by composing the denotations of
  `Nominalization.lean`, on which the accounts of eventive v differ.
* The zero alloseme is `0` and a contentful alloseme `↑c`, the forms of `WithZero`. Nothing is
  multiplied: the zero alloseme is the identity under composition.
* The context of the engineer alloseme of Voice mentions two terminals, the copula below Voice
  and the eventive VoiceP below the copula, as [myler-2016] states the rule.
* On this view one Voice head is thematic or expletive by its context. `Minimalist.Voice.Head`
  is the other view, of [schaefer-2008], on which the thematic feature is part of the head; no
  map between the two is given.

## TODO

* The sources condition an alloseme on the interpretation of its sister, computed first
  ([wood-2015]); here the condition is a feature of the neighbouring terminal.
* The allosemes of v are one eventive alloseme and zero, where [wood-2015] has an activity, a
  state and a causative.

## References

* [wood-2023]
* [benz-2025]
* [myler-2016]
* [kratzer-1996]
* [grimshaw-1990]
* [wood-2015]
* [schaefer-2008]
-/

@[expose] public section

namespace DistributedMorphology.Allosemy

open Morphology

/-! ### Allosemic entries -/

/-- A condition an alloseme places on a neighbouring terminal: its category, or the sort of
eventuality it describes. -/
inductive Feature where
  | cat (c : Minimalist.Cat)
  /-- The terminal describes events. -/
  | eventive
  /-- The terminal describes events with an agent. -/
  | agentive
  /-- The terminal describes states. -/
  | stative
  deriving DecidableEq, Repr

/-- A specification on the complement, the terminal below the head. -/
def complement (fs : Finset Feature) : Neighborhood (Finset Feature) := ⟨∅, [fs], []⟩

/-- A specification on the embedding head, the terminal above. -/
def embedding (fs : Finset Feature) : Neighborhood (Finset Feature) := ⟨∅, [], [fs]⟩

section Licensed

variable {F Sem : Type*} [DecidableEq F] {v : RuleSet (VocabularyItem F Sem)}
  {n n' : Neighborhood (Finset F)} {s : Sem}

/-- The denotations a vocabulary licenses in a context, the exponents of its applicable items. A
head is ambiguous in a context that licenses several. -/
def licensed (v : RuleSet (VocabularyItem F Sem)) (n : Neighborhood (Finset F)) : List Sem :=
  (v.applicable n).map (·.exponent)

@[simp] theorem mem_licensed : s ∈ licensed v n ↔ ∃ i ∈ v, Applies i n ∧ i.exponent = s := by
  simp [licensed, and_assoc]

theorem licensed_subset_licensed (h : n ⊆ n') : licensed v n ⊆ licensed v n' := fun s hs ↦ by
  obtain ⟨i, hi, hin, rfl⟩ := mem_licensed.1 hs
  exact mem_licensed.2 ⟨i, hi, VocabularyItem.applies_mono hin h, rfl⟩

theorem mem_licensed_of_subsetPrinciple (h : subsetPrinciple v n = some s) :
    s ∈ licensed v n := by
  obtain ⟨i, hi, rfl, hin⟩ := subsetPrinciple_winner_mem h
  exact mem_licensed.2 ⟨i, hi, hin, rfl⟩

end Licensed

/-! ### v allosemy -/

/-- The contentful alloseme of v, which introduces the event variable. -/
inductive Verbalizer.Contentful where
  | eventive
  deriving DecidableEq, Repr, Fintype

/-- The allosemes of v. Under the zero alloseme the verbalizer of a deverbal noun contributes
nothing, as on the referential reading of *observation*. -/
abbrev Verbalizer.Alloseme := WithZero Verbalizer.Contentful

/-- v interpreted as in the verbal domain. -/
@[match_pattern] def Verbalizer.Alloseme.eventive : Verbalizer.Alloseme := WithZero.coe .eventive

/-- The alloseme vocabulary of v. The eventive alloseme requires an eventive complement and the
zero alloseme is the elsewhere case. -/
def Verbalizer.vocabulary : RuleSet (VocabularyItem Feature Verbalizer.Alloseme) :=
  [⟨(complement {.eventive}).toFinset, .eventive⟩, ∅ ⟷ 0]

/-! ### n allosemy -/

/-- The contentful allosemes of n over a verbal base. -/
inductive Nominalizer.Contentful where
  /-- Propositional content, the reading of a content nominal. -/
  | content
  /-- Picks out the entities that are events, the reading of a simple event nominal. -/
  | simpleEvent
  /-- Picks out the entity an event produced. -/
  | result
  /-- Picks out states. -/
  | state
  /-- Picks out entities with no connection to an event. -/
  | entity
  deriving DecidableEq, Repr, Fintype

/-- The allosemes of n. Under the zero alloseme the noun inherits the meaning of the verb. -/
abbrev Nominalizer.Alloseme := WithZero Nominalizer.Contentful

namespace Nominalizer.Alloseme

@[match_pattern] def content : Nominalizer.Alloseme := WithZero.coe .content
@[match_pattern] def simpleEvent : Nominalizer.Alloseme := WithZero.coe .simpleEvent
@[match_pattern] def result : Nominalizer.Alloseme := WithZero.coe .result
@[match_pattern] def state : Nominalizer.Alloseme := WithZero.coe .state
@[match_pattern] def entity : Nominalizer.Alloseme := WithZero.coe .entity

end Nominalizer.Alloseme

/-- The alloseme vocabulary of n. Every alloseme requires a verbal complement, and the zero and
result allosemes an eventive one. -/
def Nominalizer.vocabulary : RuleSet (VocabularyItem Feature Nominalizer.Alloseme) :=
  [⟨(complement {.cat .v}).toFinset, .content⟩,
    ⟨(complement {.cat .v, .eventive}).toFinset, 0⟩,
    ⟨(complement {.cat .v}).toFinset, .simpleEvent⟩,
    ⟨(complement {.cat .v, .eventive}).toFinset, .result⟩,
    ⟨(complement {.cat .v}).toFinset, .state⟩,
    ⟨(complement {.cat .v}).toFinset, .entity⟩]

/-! ### Voice allosemy -/

/-- The θ-assigning allosemes of Voice. -/
inductive Voice.Contentful where
  /-- Relates an agent to an agentive, dynamic event. -/
  | agent
  /-- Relates a holder to a state. -/
  | holder
  /-- Relates to an event the one who brought it about through another agent, the subject of
  *have* over an eventive VoiceP. -/
  | engineer
  deriving DecidableEq, Repr, Fintype

/-- The allosemes of Voice. The zero alloseme is expletive Voice, which assigns no θ-role and
passes the meaning of its complement up, as with relational *have*. -/
abbrev Voice.Alloseme := WithZero Voice.Contentful

namespace Voice.Alloseme

@[match_pattern] def agent : Voice.Alloseme := WithZero.coe .agent
@[match_pattern] def holder : Voice.Alloseme := WithZero.coe .holder
@[match_pattern] def engineer : Voice.Alloseme := WithZero.coe .engineer

end Voice.Alloseme

/-- The alloseme vocabulary of Voice. The agent takes an agentive complement and the holder a
stative one; the engineer takes the copula over an eventive VoiceP; expletive Voice is the
elsewhere case. -/
def Voice.vocabulary : RuleSet (VocabularyItem Feature Voice.Alloseme) :=
  [⟨(⟨∅, [{.cat .v}, {.cat .Voice, .eventive}], []⟩ : Neighborhood (Finset Feature)).toFinset,
      .engineer⟩,
    ⟨(complement {.agentive}).toFinset, .agent⟩,
    ⟨(complement {.stative}).toFinset, .holder⟩, ∅ ⟷ 0]

/-! ### Nominalization readings -/

/-- The readings of a deverbal nominalization: the complex event, simple event and result
nominals of [grimshaw-1990], with the states and entities of [wood-2023] and the content reading of
[benz-2025]. -/
inductive NominalizationReading where
  /-- The complex event reading, with the verb's event and its argument structure. -/
  | complexEvent
  /-- The simple event reading, an event without argument structure. -/
  | simpleEvent
  /-- An entity whose existence results from an event. -/
  | result
  /-- A state. -/
  | simpleState
  /-- An entity with no connection to an event. -/
  | simpleEntity
  /-- Propositional content, with a clausal complement. -/
  | content
  deriving DecidableEq, Repr, Fintype

namespace Nominalizer.Alloseme

/-- The reading a deverbal noun has by its alloseme of n: the complex event reading under the
zero alloseme, and otherwise the reading the alloseme contributes. -/
def reading : Nominalizer.Alloseme → NominalizationReading
  | 0 => .complexEvent
  | .content => .content
  | .simpleEvent => .simpleEvent
  | .result => .result
  | .state => .simpleState
  | .entity => .simpleEntity

/-- The readings of a deverbal noun are the allosemes of its n. -/
def readingEquiv : Nominalizer.Alloseme ≃ NominalizationReading where
  toFun := reading
  invFun
    | .complexEvent => 0
    | .content => .content
    | .simpleEvent => .simpleEvent
    | .result => .result
    | .simpleState => .state
    | .simpleEntity => .entity
  left_inv := by rintro (_ | ⟨⟨⟩⟩) <;> rfl
  right_inv r := by cases r <;> rfl

@[simp] theorem coe_readingEquiv : ⇑readingEquiv = reading := rfl

@[simp] theorem reading_zero : reading 0 = .complexEvent := rfl

theorem reading_injective : Function.Injective reading := readingEquiv.injective

@[simp] theorem reading_eq_complexEvent_iff {a : Nominalizer.Alloseme} :
    a.reading = .complexEvent ↔ a = 0 :=
  reading_injective.eq_iff' reading_zero

end Nominalizer.Alloseme

end DistributedMorphology.Allosemy
