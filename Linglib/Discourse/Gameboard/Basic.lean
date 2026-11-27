module

public import Linglib.Discourse.Gameboard.Defs

/-!
# Dialogue gameboard updates

This file defines the updates of the dialogue gameboard of Ginzburg's theory of dialogue, KoS:
pushing a question onto QUD, adding a fact, and recording a move or a pending utterance.
QUD-downdate removes from QUD every question that some fact resolves, and a gameboard
satisfies `non-resolve-cond` when no fact resolves a question under discussion.

## Main definitions

* `Gameboard.pushQud`, `Gameboard.addFact`, `Gameboard.recordMove`, `Gameboard.pushPending`,
  `Gameboard.pendingUpdate`: the updates of QUD, FACTS, MOVES and PENDING.
* `Gameboard.NonResolveCond`, `Gameboard.downdateQud`: `non-resolve-cond` and QUD-downdate.

## Main results

* `Gameboard.downdateQud_eq_self_iff`: downdate is idle exactly on the gameboards that satisfy
  `non-resolve-cond`.
* `Gameboard.sublist_qud_downdateQud_iff`: the downdated QUD is the largest sublist of QUD free
  of resolved questions.
* `Gameboard.nonResolveCond_pushQud_iff`: pushing a question keeps `non-resolve-cond` exactly
  when no fact resolves that question.

## Implementation notes

* The updates of FACTS, MOVES, PENDING and QUD hold of every gameboard. The
  operations that read a question are stated for gameboards whose QUD holds information
  structures, and those that read a content for gameboards whose utterances are locutionary
  propositions.
* Resolution is an explicit relation between facts and questions, not an instance on their types:
  resolvedness is "not purely semantic" but agent-relative, so the types do not determine it.
* MOVES, PENDING and QUD are lists with their maximal element first, as Ginzburg writes them.
* Ginzburg states `non-resolve-cond` as resolution by FACTS as a whole, where the rules that use
  it quantify over its members; `NonResolveCond` follows the members, so that downdate
  establishes it.

## References

* [ginzburg-2012]
-/

@[expose] public section

namespace Gameboard

variable {P F U I Q S Φ K Λ Δ C : Type*}

section Update

variable (d : Gameboard P F U I)

/-- The gameboard of a conversation with no moves yet, `speaker` addressing `addressee` against
the common ground `facts` ([ginzburg-2012] (55) p. 90). -/
def initial (speaker addressee : P) (facts : Finset F) : Gameboard P F U I where
  speaker := speaker
  addressee := addressee
  facts := facts

/-- The latest move. -/
def latestMove : Option U :=
  d.moves.head?

/-- MaxPending, the latest ungrounded utterance. -/
def maxPending : Option U :=
  d.pending.head?

/-- Push a question onto QUD, as MaxQUD. -/
def pushQud (i : I) : Gameboard P F U I :=
  { d with qud := i :: d.qud }

/-- Add a fact to FACTS. -/
def addFact [DecidableEq F] (p : F) : Gameboard P F U I :=
  { d with facts := insert p d.facts }

/-- Record a move as LatestMove. -/
def recordMove (m : U) : Gameboard P F U I :=
  { d with moves := m :: d.moves }

/-- Push an ungrounded utterance onto PENDING, as MaxPending. -/
def pushPending (m : U) : Gameboard P F U I :=
  { d with pending := m :: d.pending }

/-- Pending update: `u`, uttered by `speaker` to `addressee`, becomes MaxPending. -/
def pendingUpdate (u : U) (speaker addressee : P) : Gameboard P F U I :=
  { d.pushPending u with speaker, addressee }

section Initial

variable (s a : P) (cg : Finset F)

@[simp] theorem facts_initial : (initial s a cg : Gameboard P F U I).facts = cg := rfl

@[simp] theorem moves_initial : (initial s a cg : Gameboard P F U I).moves = [] := rfl

@[simp] theorem qud_initial : (initial s a cg : Gameboard P F U I).qud = [] := rfl

@[simp] theorem latestMove_initial : (initial s a cg : Gameboard P F U I).latestMove = none :=
  rfl

end Initial

@[simp] theorem facts_addFact [DecidableEq F] (p : F) :
    (d.addFact p).facts = insert p d.facts := rfl

@[simp] theorem latestMove_recordMove (m : U) : (d.recordMove m).latestMove = some m := rfl

end Update

section Downdate

variable (d : Gameboard P F U (InformationStructure Q S)) (R : F → Q → Prop)
  {i : InformationStructure Q S} {l : List (InformationStructure Q S)}

/-- The question of MaxQUD. -/
def maxQud : Option Q :=
  d.qud.head?.map (·.question)

/-- `non-resolve-cond` ([ginzburg-2012] (100) p. 111) holds when no fact resolves a question
under discussion, `R` being the resolution relation. -/
def NonResolveCond : Prop :=
  ∀ i ∈ d.qud, ¬∃ f ∈ d.facts, R f i.question

instance [DecidableRel R] : Decidable (d.NonResolveCond R) :=
  inferInstanceAs (Decidable (∀ i ∈ d.qud, _))

theorem nonResolveCond_initial (s a : P) (cg : Finset F) :
    (initial s a cg : Gameboard P F U (InformationStructure Q S)).NonResolveCond R :=
  fun _ h ↦ absurd h List.not_mem_nil

/-- The Question Introduction Appropriateness Condition ([ginzburg-2012] (52) p. 89): pushing a
question keeps `non-resolve-cond` exactly when no fact resolves it. -/
theorem nonResolveCond_pushQud_iff :
    (d.pushQud i).NonResolveCond R ↔
      (¬∃ f ∈ d.facts, R f i.question) ∧ d.NonResolveCond R :=
  List.forall_mem_cons

variable [DecidableRel R]

/-- QUD-downdate removes from QUD every question that some fact resolves (NonResolve,
[ginzburg-2012] (44) p. 86). -/
def downdateQud : Gameboard P F U (InformationStructure Q S) :=
  { d with qud := d.qud.filter fun i ↦ ¬∃ f ∈ d.facts, R f i.question }

@[simp] theorem facts_downdateQud : (d.downdateQud R).facts = d.facts := rfl

@[simp] theorem mem_qud_downdateQud :
    i ∈ (d.downdateQud R).qud ↔ i ∈ d.qud ∧ ¬∃ f ∈ d.facts, R f i.question := by
  simp [downdateQud]

open scoped List in
/-- The sub-posets of QUD free of resolved questions, which the NonResolve of [ginzburg-2012]
Appendix B (16b) p. 370 may return, are exactly the sublists of the downdated QUD; its further
condition, that no fact resolve whether the participant wishes to discuss a question, is a choice
of `R`. -/
theorem sublist_qud_downdateQud_iff :
    l <+ (d.downdateQud R).qud ↔ l <+ d.qud ∧ ∀ i ∈ l, ¬∃ f ∈ d.facts, R f i.question := by
  refine ⟨fun h ↦ ⟨h.trans List.filter_sublist, fun i hi ↦ ?_⟩, fun ⟨h, hl⟩ ↦ ?_⟩
  · exact ((d.mem_qud_downdateQud R).1 (h.subset hi)).2
  · have := h.filter fun i ↦ decide ¬∃ f ∈ d.facts, R f i.question
    rwa [List.filter_eq_self.2 fun i hi ↦ decide_eq_true (hl i hi)] at this

theorem nonResolveCond_downdateQud : (d.downdateQud R).NonResolveCond R :=
  fun _ h ↦ ((d.mem_qud_downdateQud R).1 h).2

/-- Downdate is idle exactly on gameboards satisfying `non-resolve-cond`. -/
theorem downdateQud_eq_self_iff : d.downdateQud R = d ↔ d.NonResolveCond R := by
  cases d
  simp [downdateQud, NonResolveCond, List.filter_eq_self]

end Downdate

/-- The content of the latest move. -/
def latestContent (d : Gameboard P F (LocutionaryProposition Φ K Λ Δ C) I) : Option C :=
  d.latestMove.map (·.content)

end Gameboard
