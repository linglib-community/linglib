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
contextual extensions. Utterance Interpolation accommodates a question as MaxQUD and records a move
co-propositional with it, and a Clarification Context Update Rule does so for a question built from
a constituent of the maximal pending utterance, with the turn kept or passed on.

A gameboard whose facts have common grounds has the meet of them as its common ground, and adding
a fact is Stalnakerian assertion of it; a gameboard whose questions have issues has the issue of
MaxQUD.

## Main definitions

* `Discourse.LocutionaryProposition.instantiate`: contextual instantiation of an utterance.
* `Discourse.Gameboard.pushQud`, `Discourse.Gameboard.addFact`, `Discourse.Gameboard.recordMove`,
  `Discourse.Gameboard.swapTurn`: updates of a gameboard.
* `Discourse.Gameboard.NonResolveCond`, `Discourse.Gameboard.downdateQud`: `non-resolve-cond` and
  QUD-downdate.
* `Discourse.Gameboard.interpolate`, `Discourse.Gameboard.clarify`: Utterance Interpolation and
  the Clarification Context Update Rules.

## Main results

* `Discourse.LocutionaryProposition.exists_eq_instantiate_iff`: contextual instantiation yields
  exactly the contextual extensions.
* `Discourse.Gameboard.downdateQud_eq_self_iff`, `Discourse.Gameboard.nonResolveCond_pushQud_iff`.
* `Discourse.Gameboard.sublist_qud_downdateQud_iff`: the downdate of (44) is the largest of the
  downdates Appendix B allows.
* `Discourse.Gameboard.commonGround_addFact`: adding a fact meets the common ground with it.
* `Discourse.Gameboard.clarify_eq_some_iff`.

## Implementation notes

* Resolution is an explicit relation `R : D.Fact → D.Question → Prop`, not an instance on the
  domain: resolvedness is "not purely semantic" but agent-relative, so the types of facts and
  questions do not determine it.
* MOVES, PENDING and QUD are lists with their maximal element first, as Ginzburg writes them.
* Co-propositionality is likewise an explicit relation between a move's content and a question,
  which each study defines from its own contents.
* A rule that leaves the turn underspecified takes the turn as an argument (`Gameboard.Turn`).
* Ginzburg states `non-resolve-cond` as resolution by FACTS as a whole, where (44) and (52)
  quantify over its members; `NonResolveCond` follows the members, so that downdate establishes
  it.

## References

* [ginzburg-2012]
* [ginzburg-fernandez-schlangen-2014]
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

/-- Contextual instantiation yields exactly the contextual extensions of [ginzburg-2012] (47) p.
178. -/
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

/-- The gameboard of a conversation with no moves yet, `speaker` addressing `addressee` against
the common ground `facts` ([ginzburg-2012] (55) p. 90). -/
def initial (speaker addressee : D.Participant) (facts : Finset D.Fact) : Gameboard D where
  speaker := speaker
  addressee := addressee
  facts := facts

/-- The latest move. -/
def latestMove : Option (LocutionaryProposition D.toGrammaticalDomain D.Content) :=
  d.moves.head?

/-- The question of MaxQUD. -/
def maxQud : Option D.Question :=
  d.qud.head?.map (·.question)

/-- MaxPending, the latest ungrounded utterance. -/
def maxPending : Option (LocutionaryProposition D.toGrammaticalDomain D.Content) :=
  d.pending.head?

/-- The content of the latest move. -/
def latestContent : Option D.Content :=
  d.latestMove.map (·.content)

/-- Push a question with its focus-establishing constituents onto QUD, as MaxQUD. -/
def pushQud (i : InformationStructure D.toGrammaticalDomain D.Question) : Gameboard D :=
  { d with qud := i :: d.qud }

/-- Add a fact to FACTS. -/
def addFact (p : D.Fact) : Gameboard D :=
  { d with facts := insert p d.facts }

/-- Record a move as LatestMove. -/
def recordMove (m : LocutionaryProposition D.toGrammaticalDomain D.Content) : Gameboard D :=
  { d with moves := m :: d.moves }

/-- Push an ungrounded utterance onto PENDING, as MaxPending. -/
def pushPending (m : LocutionaryProposition D.toGrammaticalDomain D.Content) : Gameboard D :=
  { d with pending := m :: d.pending }

/-- The addressee takes the turn. -/
def swapTurn : Gameboard D :=
  { d with speaker := d.addressee, addressee := d.speaker }

/-- Who speaks after a rule: the speaker keeps the turn or the addressee takes it. A rule that
underspecifies the turn holder ([ginzburg-fernandez-schlangen-2014] fn. 17) takes either. -/
inductive Turn
  | keep
  | change
  deriving DecidableEq, Repr

/-- Effect the turn on a gameboard. -/
def Turn.act : Turn → Gameboard D → Gameboard D
  | .keep, d => d
  | .change, d => d.swapTurn

section Initial

variable (s a : D.Participant) (cg : Finset D.Fact)

@[simp] theorem facts_initial : (initial s a cg).facts = cg := rfl

@[simp] theorem moves_initial : (initial s a cg).moves = [] := rfl

@[simp] theorem qud_initial : (initial s a cg).qud = [] := rfl

@[simp] theorem latestMove_initial : (initial s a cg).latestMove = none := rfl

end Initial

@[simp] theorem facts_addFact (p : D.Fact) : (d.addFact p).facts = insert p d.facts := rfl

@[simp] theorem swapTurn_pushQud (i : InformationStructure D.toGrammaticalDomain D.Question) :
    d.swapTurn.pushQud i = (d.pushQud i).swapTurn := rfl

@[simp] theorem swapTurn_recordMove (m : LocutionaryProposition D.toGrammaticalDomain D.Content) :
    d.swapTurn.recordMove m = (d.recordMove m).swapTurn := rfl

@[simp] theorem latestMove_recordMove
    (m : LocutionaryProposition D.toGrammaticalDomain D.Content) :
    (d.recordMove m).latestMove = some m := rfl

section Downdate

variable (R : D.Fact → D.Question → Prop)
  {i : InformationStructure D.toGrammaticalDomain D.Question}
  {l : List (InformationStructure D.toGrammaticalDomain D.Question)}

/-- `non-resolve-cond` ([ginzburg-2012] (100) p. 111) holds when no fact resolves a question
under discussion, `R` being the resolution relation. -/
def NonResolveCond : Prop :=
  ∀ i ∈ d.qud, ¬∃ f ∈ d.facts, R f i.question

instance [DecidableRel R] : Decidable (d.NonResolveCond R) :=
  inferInstanceAs (Decidable (∀ i ∈ d.qud, _))

theorem nonResolveCond_initial (s a : D.Participant) (cg : Finset D.Fact) :
    (initial s a cg).NonResolveCond R :=
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
def downdateQud : Gameboard D :=
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

section Interpolation

variable (C : D.Content → D.Question → Prop) [DecidableRel C] {d' : Gameboard D}

/-- Utterance Interpolation with Question Accommodation ([ginzburg-2012] (67) p. 190): `i` is
accommodated as MaxQUD and `m`, co-propositional with its question under `C`, becomes
LatestMove. -/
def interpolate (i : InformationStructure D.toGrammaticalDomain D.Question)
    (m : LocutionaryProposition D.toGrammaticalDomain D.Content) : Option (Gameboard D) :=
  if C m.content i.question then some ((d.pushQud i).recordMove m) else none

/-- A Clarification Context Update Rule ([ginzburg-2012] (71) p. 192,
[ginzburg-fernandez-schlangen-2014] p. 9:31): given a constituent `u` of MaxPending `v`, the turn
`t` is taken and the information structure `i v u` is accommodated by Utterance Interpolation. -/
def clarify (t : Turn) (i : LocutionaryProposition D.toGrammaticalDomain D.Content →
      SubUtterance D.toGrammaticalDomain → InformationStructure D.toGrammaticalDomain D.Question)
    (u : SubUtterance D.toGrammaticalDomain)
    (m : LocutionaryProposition D.toGrammaticalDomain D.Content) : Option (Gameboard D) :=
  d.maxPending.bind fun v ↦ if u ∈ v.constituents then (t.act d).interpolate C (i v u) m else none

variable {C} {t : Turn} {i : LocutionaryProposition D.toGrammaticalDomain D.Content →
    SubUtterance D.toGrammaticalDomain → InformationStructure D.toGrammaticalDomain D.Question}
  {u : SubUtterance D.toGrammaticalDomain}
  {m : LocutionaryProposition D.toGrammaticalDomain D.Content}

theorem clarify_eq_some_iff : d.clarify C t i u m = some d' ↔
    ∃ v ∈ d.maxPending, u ∈ v.constituents ∧ C m.content (i v u).question ∧
      ((t.act d).pushQud (i v u)).recordMove m = d' := by
  unfold clarify
  cases d.maxPending with
  | none => simp
  | some v => by_cases hu : u ∈ v.constituents <;> simp [hu, interpolate]

theorem speaker_clarify (h : d.clarify C t i u m = some d') : d'.speaker = (t.act d).speaker := by
  obtain ⟨_, _, _, _, rfl⟩ := d.clarify_eq_some_iff.1 h
  rfl

theorem qud_clarify (h : d.clarify C t i u m = some d') :
    ∃ v ∈ d.maxPending, u ∈ v.constituents ∧ d'.qud = i v u :: d.qud := by
  obtain ⟨v, hv, hu, -, rfl⟩ := d.clarify_eq_some_iff.1 h
  exact ⟨v, hv, hu, by cases t <;> rfl⟩

end Interpolation

section CommonGround

variable {W : Type*} [HasCommonGround D.Fact W]

/-- FACTS is the common ground ([ginzburg-2012] (55) p. 90), a set of facts rather than their
conjunction (p. 67), so the common ground of a gameboard is the meet of its facts'. -/
instance : HasCommonGround (Gameboard D) W where
  commonGround d := ⨅ p ∈ d.facts, commonGround p

/-- Adding a fact to FACTS meets the common ground with the fact's, Stalnakerian assertion when
facts are sets of worlds. -/
theorem commonGround_addFact (p : D.Fact) :
    commonGround (d.addFact p) = commonGround p ⊓ commonGround d :=
  Finset.iInf_insert p d.facts _

end CommonGround

section Issue

variable {W : Type*} [HasIssue D.Question W]

/-- The issue of a gameboard is that of MaxQUD ([ginzburg-2012] §4.3.3 p. 68), and the trivial
issue when QUD is empty. -/
instance : HasIssue (Gameboard D) W where
  toIssue d := (d.maxQud.map HasIssue.toIssue).getD ⊤

@[simp] theorem toIssue_pushQud (i : InformationStructure D.toGrammaticalDomain D.Question) :
    HasIssue.toIssue (d.pushQud i) = HasIssue.toIssue i.question := rfl

@[simp] theorem toIssue_addFact (p : D.Fact) :
    HasIssue.toIssue (d.addFact p) = HasIssue.toIssue d := rfl

@[simp] theorem toIssue_initial (s a : D.Participant) (cg : Finset D.Fact) :
    HasIssue.toIssue (initial s a cg) = ⊤ := rfl

end Issue

end Gameboard

end Discourse
