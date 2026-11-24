module

public import Linglib.Discourse.Gameboard.Basic
public import Linglib.Discourse.Gameboard.Utterance
public import Mathlib.Order.Closure
public import Mathlib.Logic.Relation

/-!
# Conversational rules

A conversational rule of Ginzburg's theory of dialogue, KoS, pairs preconditions on a dialogue
gameboard with effects, a description of the gameboards that may follow. We define a rule as a
relation `Gameboard.Rule` between gameboards: `R d d'` holds when `d` meets the preconditions of
`R` and `d'` its effects. A field the effects leave open, such as the move made or who speaks
next, is a choice among the gameboards related to `d`. A set of rules is their supremum, and the
gameboards a conversation can reach are those related by `Relation.ReflTransGen`.

A rule followed by a change of turn is `Gameboard.passTurn R`, and a rule that leaves the turn
underspecified is `Gameboard.turnUnderspec R`, the supremum of `R` and `passTurn R`. A move is
coherent for a rule on a gameboard when the rule allows a gameboard with that move as LatestMove.

## Main definitions

* `Gameboard.Rule`: relations between gameboards.
* `Gameboard.passTurn`, `Gameboard.turnUnderspec`, `Gameboard.turnUnderspecClosure`: a rule
  followed by a change of turn, a rule with the turn left open, and the latter as a closure
  operator on rules.
* `Gameboard.Coherent`: a move that a rule allows as LatestMove.
* `Gameboard.PendingDowndate`, `Gameboard.PendingReplacement`: MaxPending is integrated as
  LatestMove, or replaced.
* `Gameboard.QudIncrementation`: the question the latest move contributes becomes MaxQUD.
* `Gameboard.Interpolation`, `Gameboard.Clarification`: Utterance Interpolation and the
  Clarification Context Update Rules.

## Main results

* `Gameboard.passTurn_passTurn`: passing the turn twice is the rule itself.
* `Gameboard.turnUnderspec_swapTurn_iff`: a rule with the turn left open relates a gameboard to
  another exactly when it relates it to the other with the turn swapped.
* `Gameboard.coherent_turnUnderspec_iff`: leaving the turn open does not change which moves are
  coherent.
* `Gameboard.coherent_clarification_iff`: a move is coherent for a Clarification Context Update
  Rule exactly when the rule's constituent is one of MaxPending and the move is co-propositional
  with the accommodated question.

## Implementation notes

* A rule is a relation and not a partial function with the open fields of its effects as
  arguments: the effects of a rule are a type of gameboards, and a rule whose preconditions are
  semantic, such as co-propositionality, need not be decidable.
* Co-propositionality is an explicit relation between a move's content and a question, as
  resolution is in `Gameboard/Basic.lean`.

## References

* [ginzburg-2012]
* [ginzburg-fernandez-schlangen-2014]
-/

@[expose] public section

namespace Gameboard

variable {P F U I Q S Φ K Λ Δ C : Type*}

/-- A conversational rule relates a gameboard that meets its preconditions to the gameboards its
effects describe. -/
abbrev Rule (P F U I : Type*) := Gameboard P F U I → Gameboard P F U I → Prop

section Turn

variable {R R' : Rule P F U I} {d d' : Gameboard P F U I} {m : U}

/-- The rule `R` followed by a change of turn. -/
def passTurn (R : Rule P F U I) : Rule P F U I :=
  fun d d' ↦ ∃ e, R d e ∧ e.swapTurn = d'

theorem passTurn_iff : passTurn R d d' ↔ R d d'.swapTurn :=
  ⟨by rintro ⟨e, h, rfl⟩; exact h, fun h ↦ ⟨_, h, rfl⟩⟩

@[simp] theorem passTurn_passTurn : passTurn (passTurn R) = R := by
  funext d d'
  simp only [passTurn_iff, swapTurn_swapTurn]

@[gcongr]
theorem passTurn_mono (h : R ≤ R') : passTurn R ≤ passTurn R' :=
  fun _ _ ⟨e, he, h'⟩ ↦ ⟨e, h _ _ he, h'⟩

theorem passTurn_sup : passTurn (R ⊔ R') = passTurn R ⊔ passTurn R' := by
  funext d d'
  simp only [passTurn_iff, Pi.sup_apply]

/-- The rule `R` with the turn underspecified ([ginzburg-fernandez-schlangen-2014] fn. 17): the
speaker keeps the turn or the addressee takes it. -/
def turnUnderspec (R : Rule P F U I) : Rule P F U I :=
  R ⊔ passTurn R

theorem turnUnderspec_iff : turnUnderspec R d d' ↔ R d d' ∨ R d d'.swapTurn :=
  or_congr_right passTurn_iff

theorem le_turnUnderspec : R ≤ turnUnderspec R :=
  le_sup_left

theorem turnUnderspec_of (h : R d d') : turnUnderspec R d d' :=
  .inl h

theorem turnUnderspec_swapTurn_of (h : R d d') : turnUnderspec R d d'.swapTurn :=
  .inr ⟨d', h, rfl⟩

theorem passTurn_le_turnUnderspec : passTurn R ≤ turnUnderspec R :=
  le_sup_right

@[gcongr]
theorem turnUnderspec_mono (h : R ≤ R') : turnUnderspec R ≤ turnUnderspec R' :=
  sup_le_sup h (passTurn_mono h)

@[simp] theorem passTurn_turnUnderspec : passTurn (turnUnderspec R) = turnUnderspec R := by
  rw [turnUnderspec, passTurn_sup, passTurn_passTurn, sup_comm]

@[simp] theorem turnUnderspec_turnUnderspec :
    turnUnderspec (turnUnderspec R) = turnUnderspec R := by
  rw [turnUnderspec, passTurn_turnUnderspec, sup_idem]

/-- A rule with the turn left open relates `d` to `d'` exactly when it relates `d` to `d'` with
the turn swapped. -/
theorem turnUnderspec_swapTurn_iff : turnUnderspec R d d'.swapTurn ↔ turnUnderspec R d d' := by
  rw [← passTurn_iff (R := turnUnderspec R), passTurn_turnUnderspec]

/-- Leaving the turn open, as a closure operator on rules. -/
def turnUnderspecClosure : ClosureOperator (Rule P F U I) :=
  .mk' turnUnderspec (fun _ _ ↦ turnUnderspec_mono) (fun _ ↦ le_turnUnderspec)
    fun _ ↦ turnUnderspec_turnUnderspec.le

@[simp] theorem turnUnderspecClosure_apply :
    turnUnderspecClosure R = turnUnderspec R := rfl

/-- A move is coherent for a rule on a gameboard when the rule allows a gameboard with that move
as LatestMove ([ginzburg-2012] Ch. 4, M-Coherence). -/
def Coherent (R : Rule P F U I) (d : Gameboard P F U I) (m : U) : Prop :=
  ∃ d', R d d' ∧ d'.latestMove = some m

theorem Coherent.mono (h : R ≤ R') (hm : Coherent R d m) : Coherent R' d m :=
  let ⟨d', hd, hm⟩ := hm
  ⟨d', h _ _ hd, hm⟩

@[simp] theorem coherent_passTurn_iff : Coherent (passTurn R) d m ↔ Coherent R d m :=
  ⟨fun ⟨_, ⟨e, he, h⟩, hm⟩ ↦ ⟨e, he, by subst h; exact hm⟩,
    fun ⟨e, he, hm⟩ ↦ ⟨e.swapTurn, ⟨e, he, rfl⟩, hm⟩⟩

theorem coherent_sup_iff : Coherent (R ⊔ R') d m ↔ Coherent R d m ∨ Coherent R' d m :=
  ⟨fun ⟨d', h, hm⟩ ↦ h.imp (⟨d', ·, hm⟩) (⟨d', ·, hm⟩),
    fun h ↦ h.elim (.mono le_sup_left) (.mono le_sup_right)⟩

/-- Leaving the turn open does not change which moves are coherent. -/
@[simp] theorem coherent_turnUnderspec_iff : Coherent (turnUnderspec R) d m ↔ Coherent R d m := by
  rw [turnUnderspec, coherent_sup_iff, coherent_passTurn_iff, or_self]

/-- For a rule that keeps the turn, a move can be made by a given participant under the rule
with the turn left open exactly when it is coherent for the rule. -/
theorem exists_turnUnderspec_speaker_iff {a : P}
    (hR : ∀ d', R d d' → d'.speaker = d.speaker ∧ d'.addressee = d.addressee)
    (ha : a = d.speaker ∨ a = d.addressee) :
    (∃ d', turnUnderspec R d d' ∧ d'.latestMove = some m ∧ d'.speaker = a) ↔ Coherent R d m := by
  refine ⟨fun ⟨d', h, hm, _⟩ ↦ (turnUnderspec_iff.mp h).elim (⟨d', ·, hm⟩) (⟨_, ·, hm⟩), ?_⟩
  rintro ⟨e, he, hm⟩
  rcases ha with rfl | rfl
  · exact ⟨e, le_turnUnderspec _ _ he, hm, (hR e he).1⟩
  · exact ⟨e.swapTurn, passTurn_le_turnUnderspec _ _ ⟨e, he, rfl⟩, hm, (hR e he).2⟩

end Turn

section Pending

variable {d d' : Gameboard P F U I}

/-- Move update/Pending downdate ([ginzburg-fernandez-schlangen-2014] (31)): MaxPending is
integrated as LatestMove. -/
def PendingDowndate : Rule P F U I :=
  fun d d' ↦ ∃ v rest, d.pending = v :: rest ∧ d' = { d.recordMove v with pending := rest }

/-- Pending replacement ([ginzburg-fernandez-schlangen-2014] (40)): MaxPending is replaced by an
utterance that `r` relates it to. -/
def PendingReplacement (r : U → U → Prop) : Rule P F U I :=
  fun d d' ↦ ∃ v rest w, d.pending = v :: rest ∧ r v w ∧ d' = { d with pending := w :: rest }

theorem pendingDowndate_iff {v : U} {rest : List U} (h : d.pending = v :: rest) :
    PendingDowndate d d' ↔ d' = { d.recordMove v with pending := rest } := by
  refine ⟨?_, fun h' ↦ ⟨v, rest, h, h'⟩⟩
  rintro ⟨v', rest', h', rfl⟩
  cases h.symm.trans h'
  rfl

theorem PendingReplacement.mono {r r' : U → U → Prop} (h : r ≤ r') :
    PendingReplacement (P := P) (F := F) (I := I) r ≤ PendingReplacement r' :=
  fun _ _ ⟨v, rest, w, hp, hr, hd⟩ ↦ ⟨v, rest, w, hp, h _ _ hr, hd⟩

theorem PendingReplacement.moves {r : U → U → Prop} (h : PendingReplacement r d d') :
    d'.moves = d.moves := by
  obtain ⟨_, _, _, -, -, rfl⟩ := h
  rfl

theorem PendingReplacement.qud {r : U → U → Prop} (h : PendingReplacement r d d') :
    d'.qud = d.qud := by
  obtain ⟨_, _, _, -, -, rfl⟩ := h
  rfl

end Pending

section Increment

variable {contrib : C → Option Q} {q : Q}
  {d d' : Gameboard P F (LocutionaryProposition Φ K Λ Δ C) (InformationStructure Q S)}

/-- QUD-incrementation: the question the latest move contributes under `contrib` becomes MaxQUD,
with no focus-establishing constituent. -/
def QudIncrementation (contrib : C → Option Q) :
    Rule P F (LocutionaryProposition Φ K Λ Δ C) (InformationStructure Q S) :=
  fun d d' ↦ ∃ q ∈ d.latestContent.bind contrib, d' = d.pushQud ⟨q, ∅⟩

/-- QUD-incrementation keeps `non-resolve-cond` exactly when no fact resolves the question the
latest move contributes. -/
theorem QudIncrementation.nonResolveCond_iff (R : F → Q → Prop)
    (hq : q ∈ d.latestContent.bind contrib) (h : QudIncrementation contrib d d') :
    d'.NonResolveCond R ↔ (¬∃ f ∈ d.facts, R f q) ∧ d.NonResolveCond R := by
  obtain ⟨q', hq', rfl⟩ := h
  cases Option.mem_unique hq hq'
  exact d.nonResolveCond_pushQud_iff R

end Increment

section Interpolation

variable {r : C → Q → Prop} {i : InformationStructure Q S}
  {d d' : Gameboard P F (LocutionaryProposition Φ K Λ Δ C) (InformationStructure Q S)}
  {m : LocutionaryProposition Φ K Λ Δ C}

/-- Utterance Interpolation with Question Accommodation ([ginzburg-2012] (67) p. 190): `i` is
accommodated as MaxQUD and a move co-propositional with its question under `r` becomes
LatestMove. -/
def Interpolation (r : C → Q → Prop) (i : InformationStructure Q S) :
    Rule P F (LocutionaryProposition Φ K Λ Δ C) (InformationStructure Q S) :=
  fun d d' ↦ ∃ m, r m.content i.question ∧ d' = (d.pushQud i).recordMove m

theorem Interpolation.qud (h : Interpolation r i d d') : d'.qud = i :: d.qud := by
  obtain ⟨_, -, rfl⟩ := h
  rfl

theorem Interpolation.speaker (h : Interpolation r i d d') : d'.speaker = d.speaker := by
  obtain ⟨_, -, rfl⟩ := h
  rfl

theorem Interpolation.addressee (h : Interpolation r i d d') : d'.addressee = d.addressee := by
  obtain ⟨_, -, rfl⟩ := h
  rfl

theorem coherent_interpolation_iff :
    Coherent (Interpolation r i) d m ↔ r m.content i.question :=
  ⟨by rintro ⟨_, ⟨m', hr, rfl⟩, hm⟩; cases hm; exact hr, fun h ↦ ⟨_, ⟨m, h, rfl⟩, rfl⟩⟩

end Interpolation

section Clarification

variable {r : C → Q → Prop} {u : SubUtterance Φ K Δ}
  {i : LocutionaryProposition Φ K Λ Δ C → InformationStructure Q (SubUtterance Φ K Δ)}
  {d d' : Gameboard P F (LocutionaryProposition Φ K Λ Δ C)
    (InformationStructure Q (SubUtterance Φ K Δ))}
  {m : LocutionaryProposition Φ K Λ Δ C}

/-- A Clarification Context Update Rule ([ginzburg-2012] (71) p. 192,
[ginzburg-fernandez-schlangen-2014] p. 9:31): given a constituent `u` of MaxPending `v`, the
information structure `i v` is accommodated by Utterance Interpolation. -/
def Clarification (r : C → Q → Prop) (u : SubUtterance Φ K Δ)
    (i : LocutionaryProposition Φ K Λ Δ C → InformationStructure Q (SubUtterance Φ K Δ)) :
    Rule P F (LocutionaryProposition Φ K Λ Δ C) (InformationStructure Q (SubUtterance Φ K Δ)) :=
  fun d d' ↦ ∃ v ∈ d.maxPending, u ∈ v.constituents ∧ Interpolation r (i v) d d'

theorem Clarification.qud (h : Clarification r u i d d') :
    ∃ v ∈ d.maxPending, u ∈ v.constituents ∧ d'.qud = i v :: d.qud :=
  let ⟨v, hv, hu, h⟩ := h
  ⟨v, hv, hu, h.qud⟩

theorem Clarification.speaker (h : Clarification r u i d d') : d'.speaker = d.speaker :=
  let ⟨_, _, _, h⟩ := h
  h.speaker

theorem Clarification.addressee (h : Clarification r u i d d') : d'.addressee = d.addressee :=
  let ⟨_, _, _, h⟩ := h
  h.addressee

/-- A move is coherent for a Clarification Context Update Rule exactly when the rule's
constituent is one of MaxPending and the move is co-propositional with the accommodated
question. -/
theorem coherent_clarification_iff : Coherent (Clarification r u i) d m ↔
    ∃ v ∈ d.maxPending, u ∈ v.constituents ∧ r m.content (i v).question :=
  ⟨fun ⟨d', ⟨v, hv, hu, h⟩, hm⟩ ↦ ⟨v, hv, hu, coherent_interpolation_iff.mp ⟨d', h, hm⟩⟩,
    fun ⟨v, hv, hu, h⟩ ↦
      let ⟨d', hd, hm⟩ := coherent_interpolation_iff.mpr h
      ⟨d', ⟨v, hv, hu, hd⟩, hm⟩⟩

end Clarification

end Gameboard
