module

public import Linglib.Discourse.Gameboard.Defs
public import Linglib.Discourse.QUD.Issue
public import Mathlib.Order.Filter.Finite

/-!
# Dialogue gameboard operations

This file defines the updates of the dialogue gameboard of Ginzburg's theory of dialogue, KoS:
pushing a question with its focus-establishing constituents onto QUD, adding a fact, recording a
move or a pending utterance, changing the turn, and QUD-downdate, which removes from QUD every
question that some fact resolves. A gameboard satisfies `non-resolve-cond` when no fact resolves a
question under discussion; downdate establishes the condition and is idle exactly on the gameboards
that satisfy it, and pushing a question keeps it exactly when no fact resolves that question, which
is Ginzburg's Question Introduction Appropriateness Condition. Contextual instantiation witnesses
some of an utterance's contextual parameters, and the utterances it produces are exactly Ginzburg's
contextual extensions.

A gameboard whose facts have common grounds has the meet of them as its common ground, and adding
a fact is Stalnakerian assertion of it; a gameboard whose questions have issues has the issue of
MaxQUD.

## Main definitions

* `Discourse.LocutionaryProposition.instantiate`: contextual instantiation of an utterance.
* `Discourse.Gameboard.pushQud`, `Discourse.Gameboard.addFact`, `Discourse.Gameboard.recordMove`,
  `Discourse.Gameboard.swapTurn`: updates of a gameboard.
* `Discourse.Gameboard.NonResolveCond`, `Discourse.Gameboard.downdateQud`: `non-resolve-cond` and
  QUD-downdate.

## Main results

* `Discourse.LocutionaryProposition.exists_eq_instantiate_iff`: contextual instantiation yields
  exactly the contextual extensions.
* `Discourse.Gameboard.downdateQud_eq_self_iff`, `Discourse.Gameboard.nonResolveCond_pushQud_iff`.
* `Discourse.Gameboard.commonGround_addFact`: adding a fact meets the common ground with it.

## Implementation notes

* Resolution is an explicit relation `R : D.Fact → D.Question → Prop`, not an instance on the
  domain: resolvedness is "not purely semantic" but agent-relative, so the types of facts and
  questions do not determine it.
* The downdate is that of Ginzburg's (44). His Appendix B version lets NonResolve return any
  sub-poset of QUD free of resolved questions, and also removes a question once a fact resolves
  whether the participant wishes to discuss it.
* Ginzburg states `non-resolve-cond` as resolution by FACTS as a whole, where (44) and (52)
  quantify over its members; `NonResolveCond` follows the members, so that downdate establishes
  it.

## References

* [ginzburg-2012]
-/

@[expose] public section

universe u

namespace Discourse

namespace LocutionaryProposition

variable {G : GrammaticalDomain.{u}} {C : Type u} (w u : LocutionaryProposition G C)
  (s t : Finset G.Label)

/-- Contextual instantiation ([ginzburg-2012] (48) p. 178): the parameters labelled in `s` have
been witnessed and leave the utterance's contextual parameters. -/
def instantiate : LocutionaryProposition G C :=
  { u with parameters := u.parameters \ s }

@[simp] theorem parameters_instantiate : (u.instantiate s).parameters = u.parameters \ s := rfl

@[simp] theorem form_instantiate : (u.instantiate s).form = u.form := rfl

@[simp] theorem category_instantiate : (u.instantiate s).category = u.category := rfl

@[simp] theorem content_instantiate : (u.instantiate s).content = u.content := rfl

@[simp] theorem constituents_instantiate :
    (u.instantiate s).constituents = u.constituents := rfl

@[simp] theorem instantiate_empty : u.instantiate ∅ = u := by
  simp [instantiate]

theorem instantiate_instantiate : (u.instantiate s).instantiate t = u.instantiate (s ∪ t) := by
  simp [instantiate, sdiff_sdiff_left]

/-- Contextual instantiation yields exactly the contextual extensions of [ginzburg-2012] (47)
p. 178: the utterances agreeing on every field but the contextual parameters, of which they
leave fewer unwitnessed. -/
theorem exists_eq_instantiate_iff :
    (∃ s, w = u.instantiate s) ↔ w.form = u.form ∧ w.category = u.category ∧
      w.content = u.content ∧ w.constituents = u.constituents ∧ w.parameters ⊆ u.parameters := by
  refine ⟨?_, fun ⟨hf, hc, hn, hs, hp⟩ ↦ ⟨u.parameters \ w.parameters, ?_⟩⟩
  · rintro ⟨s, rfl⟩
    exact ⟨rfl, rfl, rfl, rfl, Finset.sdiff_subset⟩
  · cases w
    simp_all [instantiate, Finset.sdiff_sdiff_eq_self hp]

end LocutionaryProposition

namespace Gameboard

variable {D : Gameboard.Domain.{u}} (d : Gameboard D)

/-- The gameboard of a conversation with no moves yet, `speaker` addressing `addressee`. -/
def initial (speaker addressee : D.Participant) : Gameboard D where
  speaker := speaker
  addressee := addressee

/-- The latest move. -/
def latestMove : Option (LocutionaryProposition D.toGrammaticalDomain D.Content) :=
  d.moves.getLast?

/-- The question of MaxQUD. -/
def maxQud : Option D.Question :=
  d.qud.head?.map (·.question)

/-- The content of the latest move. -/
def latestContent : Option D.Content :=
  d.latestMove.map (·.content)

/-- Push a question with its focus-establishing constituents onto QUD, as MaxQUD. -/
def pushQud (i : InformationStructure D.toGrammaticalDomain D.Question) : Gameboard D :=
  { d with qud := i :: d.qud }

/-- Add a fact to FACTS. -/
def addFact (p : D.Fact) : Gameboard D :=
  { d with facts := insert p d.facts }

/-- Record a move as the latest in MOVES. -/
def recordMove (m : LocutionaryProposition D.toGrammaticalDomain D.Content) : Gameboard D :=
  { d with moves := d.moves ++ [m] }

/-- Push an ungrounded utterance onto PENDING, as MaxPending. -/
def pushPending (m : LocutionaryProposition D.toGrammaticalDomain D.Content) : Gameboard D :=
  { d with pending := m :: d.pending }

/-- The addressee takes the turn. -/
def swapTurn : Gameboard D :=
  { d with speaker := d.addressee, addressee := d.speaker }

section Initial

variable (s a : D.Participant)

@[simp] theorem facts_initial : (initial s a : Gameboard D).facts = ∅ := rfl

@[simp] theorem moves_initial : (initial s a : Gameboard D).moves = [] := rfl

@[simp] theorem qud_initial : (initial s a : Gameboard D).qud = [] := rfl

@[simp] theorem latestMove_initial : (initial s a : Gameboard D).latestMove = none := rfl

end Initial

@[simp] theorem facts_addFact (p : D.Fact) : (d.addFact p).facts = insert p d.facts := rfl

@[simp] theorem swapTurn_pushQud (i : InformationStructure D.toGrammaticalDomain D.Question) :
    d.swapTurn.pushQud i = (d.pushQud i).swapTurn := rfl

@[simp] theorem swapTurn_recordMove (m : LocutionaryProposition D.toGrammaticalDomain D.Content) :
    d.swapTurn.recordMove m = (d.recordMove m).swapTurn := rfl

@[simp] theorem latestMove_recordMove
    (m : LocutionaryProposition D.toGrammaticalDomain D.Content) :
    (d.recordMove m).latestMove = some m := by
  simp [latestMove, recordMove]

section Downdate

variable (R : D.Fact → D.Question → Prop)

/-- `non-resolve-cond` ([ginzburg-2012] (100) p. 111) holds when no fact resolves a question
under discussion, `R` being the resolution relation. -/
def NonResolveCond : Prop :=
  ∀ i ∈ d.qud, ¬∃ f ∈ d.facts, R f i.question

instance [DecidableRel R] : Decidable (d.NonResolveCond R) :=
  inferInstanceAs (Decidable (∀ i ∈ d.qud, _))

theorem nonResolveCond_initial (s a : D.Participant) :
    (initial s a : Gameboard D).NonResolveCond R :=
  fun _ h ↦ absurd h List.not_mem_nil

/-- The Question Introduction Appropriateness Condition ([ginzburg-2012] (52) p. 89): pushing a
question keeps `non-resolve-cond` exactly when no fact resolves it. -/
theorem nonResolveCond_pushQud_iff {i : InformationStructure D.toGrammaticalDomain D.Question} :
    (d.pushQud i).NonResolveCond R ↔
      (¬∃ f ∈ d.facts, R f i.question) ∧ d.NonResolveCond R :=
  List.forall_mem_cons

variable [DecidableRel R]

/-- QUD-downdate removes from QUD every question that some fact resolves (NonResolve,
[ginzburg-2012] (44) p. 86). -/
def downdateQud : Gameboard D :=
  { d with qud := d.qud.filter fun i ↦ ¬∃ f ∈ d.facts, R f i.question }

@[simp] theorem facts_downdateQud : (d.downdateQud R).facts = d.facts := rfl

@[simp] theorem mem_qud_downdateQud {i : InformationStructure D.toGrammaticalDomain D.Question} :
    i ∈ (d.downdateQud R).qud ↔ i ∈ d.qud ∧ ¬∃ f ∈ d.facts, R f i.question := by
  simp [downdateQud]

theorem length_qud_downdateQud_le : (d.downdateQud R).qud.length ≤ d.qud.length :=
  List.length_filter_le _ _

theorem nonResolveCond_downdateQud : (d.downdateQud R).NonResolveCond R :=
  fun _ h ↦ ((d.mem_qud_downdateQud R).1 h).2

/-- Downdate is idle exactly on gameboards satisfying `non-resolve-cond`. -/
theorem downdateQud_eq_self_iff : d.downdateQud R = d ↔ d.NonResolveCond R := by
  cases d
  simp [downdateQud, NonResolveCond, List.filter_eq_self]

end Downdate

section CommonGround

variable {W : Type*} [HasCommonGround D.Fact W]

/-- A gameboard whose facts have common grounds has their meet as its common ground. -/
instance : HasCommonGround (Gameboard D) W where
  commonGround d := ⨅ p ∈ d.facts, commonGround p

/-- Adding a fact to FACTS meets the common ground with the fact's, Stalnakerian assertion when
facts are sets of worlds. -/
theorem commonGround_addFact (p : D.Fact) :
    commonGround (d.addFact p) = commonGround p ⊓ commonGround d :=
  Finset.iInf_insert p d.facts _

@[simp] theorem commonGround_initial (s a : D.Participant) :
    commonGround (initial s a : Gameboard D) = ⊤ := by
  simp [HasCommonGround.commonGround, initial]

end CommonGround

section Issue

variable {W : Type*} [HasIssue D.Question W]

/-- The issue of a gameboard is that of MaxQUD, the trivial issue when QUD is empty
([ginzburg-2012] §4.3.3 p. 68). -/
instance : HasIssue (Gameboard D) W where
  toIssue d := (d.qud.head?.map fun i ↦ HasIssue.toIssue i.question).getD ⊤

@[simp] theorem toIssue_pushQud (i : InformationStructure D.toGrammaticalDomain D.Question) :
    HasIssue.toIssue (d.pushQud i) = HasIssue.toIssue i.question := rfl

@[simp] theorem toIssue_addFact (p : D.Fact) :
    HasIssue.toIssue (d.addFact p) = HasIssue.toIssue d := rfl

@[simp] theorem toIssue_initial (s a : D.Participant) :
    HasIssue.toIssue (initial s a : Gameboard D) = ⊤ := rfl

end Issue

end Gameboard

end Discourse
