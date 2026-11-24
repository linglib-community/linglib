module

public import Linglib.Discourse.Gameboard.Basic
public import Linglib.Discourse.Gameboard.Utterance
public import Linglib.Core.Relation.Reads

/-!
# Conversational rules

A conversational rule of Ginzburg's theory of dialogue, KoS, pairs preconditions on a dialogue
gameboard with effects, a description of the gameboards that may follow. A system of rules is a
labelled relation `R d l d'` between gameboards: `l` is `some m` when the step integrates the move
`m` as LatestMove, and `none` when the step is the participant's own bookkeeping, such as
QUD-incrementation or the instantiation of a contextual parameter. A study defines its system as
an inductive relation with one constructor for each rule, its preconditions as hypotheses and its
effect in the conclusion. A move `m` is coherent on a gameboard `d` when `∃ d', R d (some m) d'`,
and a conversation develops by `Relation.Reads R`.

A move records who speaks and to whom, so a rule that leaves the turn underspecified is one with
no hypothesis on the speaker of its move.

## Main definitions

* `Gameboard.Move`: an utterance with its speaker and addressee.
* `Gameboard.say`: a move is integrated as LatestMove, and its speaker holds the turn.
* `Gameboard.IsReply`, `Gameboard.IsContinuation`: the addressee takes the turn, or the speaker
  keeps it.
* `Gameboard.Clarification`: the Clarification Context Update Rules.

## Main results

* `Gameboard.exists_clarification_iff`: a move can be integrated by a Clarification Context
  Update Rule exactly when the rule's constituent is one of MaxPending and the move is
  co-propositional with the accommodated question.

## Implementation notes

* A system of rules is a relation and not a partial function with the open fields of its effects
  as arguments: an utterance may be integrated in more than one way, and a rule whose
  preconditions are semantic, such as co-propositionality, need not be decidable.
* Co-propositionality is an explicit relation between a move's content and a question, as
  resolution is in `Gameboard/Basic.lean`.

## References

* [ginzburg-2012]
* [ginzburg-fernandez-schlangen-2014]
-/

@[expose] public section

namespace Gameboard

variable {P F U I Q S Φ K Λ Δ C : Type*}

/-- A move is an utterance with its speaker and addressee. -/
structure Move (P U : Type*) where
  /-- The speaker. -/
  speaker : P
  /-- The addressee. -/
  addressee : P
  /-- The utterance. -/
  utterance : U

section Say

variable (d : Gameboard P F U I) (m : Move P U)

/-- A move is integrated as LatestMove, and its speaker holds the turn. -/
def say : Gameboard P F U I :=
  { d with speaker := m.speaker, addressee := m.addressee, moves := m.utterance :: d.moves }

@[simp] theorem latestMove_say : (d.say m).latestMove = some m.utterance := rfl

@[simp] theorem speaker_say : (d.say m).speaker = m.speaker := rfl

@[simp] theorem addressee_say : (d.say m).addressee = m.addressee := rfl

@[simp] theorem facts_say : (d.say m).facts = d.facts := rfl

@[simp] theorem qud_say : (d.say m).qud = d.qud := rfl

@[simp] theorem pending_say : (d.say m).pending = d.pending := rfl

/-- The addressee takes the turn. -/
def IsReply : Prop :=
  m.speaker = d.addressee ∧ m.addressee = d.speaker

/-- The speaker keeps the turn. -/
def IsContinuation : Prop :=
  m.speaker = d.speaker ∧ m.addressee = d.addressee

end Say

section Clarification

variable {r : C → Q → Prop} {u : SubUtterance Φ K Δ}
  {i : LocutionaryProposition Φ K Λ Δ C → InformationStructure Q (SubUtterance Φ K Δ)}
  {d d' : Gameboard P F (LocutionaryProposition Φ K Λ Δ C)
    (InformationStructure Q (SubUtterance Φ K Δ))}
  {m : Move P (LocutionaryProposition Φ K Λ Δ C)}

/-- A Clarification Context Update Rule merged with Utterance Interpolation ([ginzburg-2012]
(67) p. 190 and (71) p. 192, [ginzburg-fernandez-schlangen-2014] p. 9:31): given a constituent
`u` of MaxPending `v`, the information structure `i v` is accommodated as MaxQUD and a move
co-propositional with its question under `r` is integrated. -/
def Clarification (r : C → Q → Prop) (u : SubUtterance Φ K Δ)
    (i : LocutionaryProposition Φ K Λ Δ C → InformationStructure Q (SubUtterance Φ K Δ))
    (d : Gameboard P F (LocutionaryProposition Φ K Λ Δ C)
      (InformationStructure Q (SubUtterance Φ K Δ)))
    (m : Move P (LocutionaryProposition Φ K Λ Δ C))
    (d' : Gameboard P F (LocutionaryProposition Φ K Λ Δ C)
      (InformationStructure Q (SubUtterance Φ K Δ))) : Prop :=
  ∃ v ∈ d.maxPending, u ∈ v.constituents ∧ r m.utterance.content (i v).question ∧
    d' = (d.pushQud (i v)).say m

theorem Clarification.qud (h : Clarification r u i d m d') :
    ∃ v ∈ d.maxPending, u ∈ v.constituents ∧ d'.qud = i v :: d.qud :=
  let ⟨v, hv, hu, _, h⟩ := h
  ⟨v, hv, hu, h ▸ rfl⟩

/-- A move can be integrated by a Clarification Context Update Rule exactly when the rule's
constituent is one of MaxPending and the move is co-propositional with the accommodated
question. -/
theorem exists_clarification_iff : (∃ d', Clarification r u i d m d') ↔
    ∃ v ∈ d.maxPending, u ∈ v.constituents ∧ r m.utterance.content (i v).question :=
  ⟨fun ⟨_, v, hv, hu, hr, _⟩ ↦ ⟨v, hv, hu, hr⟩, fun ⟨v, hv, hu, hr⟩ ↦ ⟨_, v, hv, hu, hr, rfl⟩⟩

end Clarification

end Gameboard
