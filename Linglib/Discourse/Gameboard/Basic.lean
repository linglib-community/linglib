module

public import Linglib.Discourse.Gameboard.Defs

/-!
# Dialogue gameboard operations

This file defines the updates of the dialogue gameboard of Ginzburg's theory of dialogue, KoS:
pushing a question onto QUD, adding a fact, recording a move or a pending utterance, replacing
the maximal pending utterance, and changing the turn. QUD-downdate removes from QUD every
question that some fact resolves, and a gameboard satisfies `non-resolve-cond` when no fact
resolves a question under discussion. Contextual instantiation witnesses some of an utterance's
contextual parameters. Utterance Interpolation accommodates a question as MaxQUD and records a
move co-propositional with it, and a Clarification Context Update Rule does so for a question
built from a constituent of the maximal pending utterance, with the turn kept or passed on.

## Main definitions

* `Gameboard.pushQud`, `Gameboard.addFact`, `Gameboard.recordMove`, `Gameboard.pushPending`,
  `Gameboard.replaceMaxPending`: the updates of QUD, FACTS, MOVES and PENDING.
* `Gameboard.swapTurn`, `Gameboard.swapTurnEquiv`, `Gameboard.Turn`: the addressee takes the turn,
  and a rule's choice between keeping the turn and passing it on.
* `Gameboard.NonResolveCond`, `Gameboard.downdateQud`: `non-resolve-cond` and QUD-downdate.
* `Gameboard.LocutionaryProposition.instantiate`: contextual instantiation.
* `Gameboard.incrementQud`: QUD-incrementation by the question the latest move contributes.
* `Gameboard.interpolate`, `Gameboard.clarify`: Utterance Interpolation and the Clarification
  Context Update Rules.

## Main results

* `Gameboard.downdateQud_eq_self_iff`: downdate is idle exactly on the gameboards that satisfy
  `non-resolve-cond`.
* `Gameboard.sublist_qud_downdateQud_iff`: the downdated QUD is the largest sublist of QUD free
  of resolved questions.
* `Gameboard.nonResolveCond_pushQud_iff`: pushing a question keeps `non-resolve-cond` exactly
  when no fact resolves that question.
* `Gameboard.LocutionaryProposition.exists_eq_instantiate_iff`: contextual instantiation yields
  exactly the contextual extensions of an utterance.
* `Gameboard.clarify_eq_some_iff`: a Clarification Context Update Rule applies exactly when its
  constituent is one of MaxPending and the move is co-propositional with the accommodated
  question.
* `Gameboard.clarify_eq_map_act`: the turn a Clarification Context Update Rule takes changes only
  who holds the turn afterwards.

## Implementation notes

* Turn taking and the updates of FACTS, MOVES, PENDING and QUD hold of every gameboard. The
  operations that read a question are stated for gameboards whose QUD holds information
  structures, and those that read a content or a constituent for gameboards whose utterances are
  locutionary propositions.
* Resolution is an explicit relation between facts and questions, not an instance on their types:
  resolvedness is "not purely semantic" but agent-relative, so the types do not determine it.
  Co-propositionality is likewise an explicit relation between a move's content and a question.
* MOVES, PENDING and QUD are lists with their maximal element first, as Ginzburg writes them.
* A rule that leaves the turn underspecified takes the turn as an argument (`Gameboard.Turn`).
* Ginzburg states `non-resolve-cond` as resolution by FACTS as a whole, where (44) and (52)
  quantify over its members; `NonResolveCond` follows the members, so that downdate establishes
  it.

## References

* [ginzburg-2012]
* [ginzburg-fernandez-schlangen-2014]
-/

@[expose] public section

namespace Gameboard

variable {P F U I Q S Φ K Λ Δ C : Type*}

namespace LocutionaryProposition

variable [DecidableEq Λ] (w u : LocutionaryProposition Φ K Λ Δ C) (s t : Finset Λ)

/-- Contextual instantiation ([ginzburg-2012] (48) p. 178): the parameters labelled in `s` have
been witnessed and leave the utterance's contextual parameters. -/
def instantiate : LocutionaryProposition Φ K Λ Δ C :=
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

/-- Replace MaxPending by `w`, on a gameboard with a pending utterance. -/
def replaceMaxPending (w : U) : Option (Gameboard P F U I) :=
  match d.pending with
  | _ :: rest => some { d with pending := w :: rest }
  | [] => none

theorem replaceMaxPending_eq_some_iff {w : U} {d' : Gameboard P F U I} :
    d.replaceMaxPending w = some d' ↔
      ∃ v rest, d.pending = v :: rest ∧ { d with pending := w :: rest } = d' := by
  unfold replaceMaxPending
  split <;> simp_all

/-- The addressee takes the turn. -/
def swapTurn : Gameboard P F U I :=
  { d with speaker := d.addressee, addressee := d.speaker }

/-- Who speaks after a rule: the speaker keeps the turn or the addressee takes it. A rule that
underspecifies the turn holder ([ginzburg-fernandez-schlangen-2014] fn. 17) takes either. -/
inductive Turn
  | keep
  | change
  deriving DecidableEq, Repr

/-- Effect the turn on a gameboard. -/
def Turn.act : Turn → Gameboard P F U I → Gameboard P F U I
  | .keep, d => d
  | .change, d => d.swapTurn

@[simp] theorem Turn.act_keep : Turn.keep.act d = d := rfl

@[simp] theorem Turn.act_change : Turn.change.act d = d.swapTurn := rfl

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

@[simp] theorem swapTurn_swapTurn : d.swapTurn.swapTurn = d := rfl

theorem swapTurn_involutive : Function.Involutive (swapTurn (P := P) (F := F) (U := U) (I := I)) :=
  swapTurn_swapTurn

/-- Swapping the turn, as a permutation of gameboards. -/
@[simps! apply symm_apply]
def swapTurnEquiv : Gameboard P F U I ≃ Gameboard P F U I :=
  swapTurn_involutive.toPerm

@[simp] theorem swapTurnEquiv_symm :
    (swapTurnEquiv : Gameboard P F U I ≃ Gameboard P F U I).symm = swapTurnEquiv := rfl

@[simp] theorem swapTurn_pushQud (i : I) : d.swapTurn.pushQud i = (d.pushQud i).swapTurn := rfl

@[simp] theorem swapTurn_recordMove (m : U) :
    d.swapTurn.recordMove m = (d.recordMove m).swapTurn := rfl

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

section Increment

variable (d : Gameboard P F (LocutionaryProposition Φ K Λ Δ C) (InformationStructure Q S))
  {d' : Gameboard P F (LocutionaryProposition Φ K Λ Δ C) (InformationStructure Q S)}
  (contrib : C → Option Q) {q : Q}

/-- QUD-incrementation: the question the latest move contributes under `contrib` becomes MaxQUD,
with no focus-establishing constituent. -/
def incrementQud :
    Option (Gameboard P F (LocutionaryProposition Φ K Λ Δ C) (InformationStructure Q S)) :=
  (d.latestContent.bind contrib).map fun q ↦ d.pushQud ⟨q, ∅⟩

variable {contrib}

theorem incrementQud_eq_some_iff : d.incrementQud contrib = some d' ↔
    ∃ q ∈ d.latestContent.bind contrib, d.pushQud ⟨q, ∅⟩ = d' := by
  simp only [incrementQud, Option.map_eq_some_iff, Option.mem_def]

/-- QUD-incrementation keeps `non-resolve-cond` exactly when no fact resolves the question the
latest move contributes. -/
theorem nonResolveCond_incrementQud_iff (R : F → Q → Prop)
    (hq : q ∈ d.latestContent.bind contrib) (h : d.incrementQud contrib = some d') :
    d'.NonResolveCond R ↔ (¬∃ f ∈ d.facts, R f q) ∧ d.NonResolveCond R := by
  obtain ⟨q', hq', rfl⟩ := d.incrementQud_eq_some_iff.1 h
  cases Option.mem_unique hq hq'
  exact d.nonResolveCond_pushQud_iff R

end Increment

section Interpolation

variable (r : C → Q → Prop) [DecidableRel r]

/-- Utterance Interpolation with Question Accommodation ([ginzburg-2012] (67) p. 190): `i` is
accommodated as MaxQUD and `m`, co-propositional with its question under `r`, becomes
LatestMove. -/
def interpolate (d : Gameboard P F (LocutionaryProposition Φ K Λ Δ C) (InformationStructure Q S))
    (i : InformationStructure Q S) (m : LocutionaryProposition Φ K Λ Δ C) :
    Option (Gameboard P F (LocutionaryProposition Φ K Λ Δ C) (InformationStructure Q S)) :=
  if r m.content i.question then some ((d.pushQud i).recordMove m) else none

variable [DecidableEq Φ] [DecidableEq K] [DecidableEq Δ]
  (d : Gameboard P F (LocutionaryProposition Φ K Λ Δ C)
    (InformationStructure Q (SubUtterance Φ K Δ)))
  {d' : Gameboard P F (LocutionaryProposition Φ K Λ Δ C)
    (InformationStructure Q (SubUtterance Φ K Δ))}

/-- A Clarification Context Update Rule ([ginzburg-2012] (71) p. 192,
[ginzburg-fernandez-schlangen-2014] p. 9:31): given a constituent `u` of MaxPending `v`, the turn
`t` is taken and the information structure `i v u` is accommodated by Utterance Interpolation. -/
def clarify (t : Turn) (i : LocutionaryProposition Φ K Λ Δ C → SubUtterance Φ K Δ →
      InformationStructure Q (SubUtterance Φ K Δ))
    (u : SubUtterance Φ K Δ) (m : LocutionaryProposition Φ K Λ Δ C) :
    Option (Gameboard P F (LocutionaryProposition Φ K Λ Δ C)
      (InformationStructure Q (SubUtterance Φ K Δ))) :=
  d.maxPending.bind fun v ↦ if u ∈ v.constituents then (t.act d).interpolate r (i v u) m else none

variable {r} {t : Turn} {i : LocutionaryProposition Φ K Λ Δ C → SubUtterance Φ K Δ →
    InformationStructure Q (SubUtterance Φ K Δ)}
  {u : SubUtterance Φ K Δ} {m : LocutionaryProposition Φ K Λ Δ C}

theorem clarify_eq_some_iff : d.clarify r t i u m = some d' ↔
    ∃ v ∈ d.maxPending, u ∈ v.constituents ∧ r m.content (i v u).question ∧
      ((t.act d).pushQud (i v u)).recordMove m = d' := by
  unfold clarify
  cases d.maxPending with
  | none => simp
  | some v => by_cases hu : u ∈ v.constituents <;> simp [hu, interpolate]

theorem isSome_clarify_iff : (d.clarify r t i u m).isSome ↔
    ∃ v ∈ d.maxPending, u ∈ v.constituents ∧ r m.content (i v u).question := by
  simp only [Option.isSome_iff_exists, clarify_eq_some_iff]
  exact ⟨fun ⟨_, v, hv, hu, hr, _⟩ ↦ ⟨v, hv, hu, hr⟩, fun ⟨v, hv, hu, hr⟩ ↦ ⟨_, v, hv, hu, hr, rfl⟩⟩

/-- The turn a Clarification Context Update Rule takes changes only who holds the turn
afterwards. -/
theorem clarify_eq_map_act (t : Turn) :
    d.clarify r t i u m = (d.clarify r .keep i u m).map t.act := by
  unfold clarify
  cases d.maxPending with
  | none => rfl
  | some v => cases t <;> simp only [Option.bind_some, interpolate] <;> split_ifs <;> rfl

theorem speaker_clarify (h : d.clarify r t i u m = some d') : d'.speaker = (t.act d).speaker := by
  obtain ⟨_, _, _, _, rfl⟩ := d.clarify_eq_some_iff.1 h
  rfl

theorem qud_clarify (h : d.clarify r t i u m = some d') :
    ∃ v ∈ d.maxPending, u ∈ v.constituents ∧ d'.qud = i v u :: d.qud := by
  obtain ⟨v, hv, hu, -, rfl⟩ := d.clarify_eq_some_iff.1 h
  exact ⟨v, hv, hu, by cases t <;> rfl⟩

end Interpolation

end Gameboard
