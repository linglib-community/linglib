module

public import Linglib.Discourse.Gameboard.Basic
public import Linglib.Data.Examples.GinzburgFernandezSchlangen2014
public import Mathlib.Data.Fintype.Option
public import Mathlib.Tactic.DeriveFintype

/-!
# Ginzburg, Fernández and Schlangen (2014): Disfluencies as intra-utterance dialogue moves

This file formalizes the account of disfluencies of [ginzburg-fernandez-schlangen-2014], on which
a self-correction or a hesitation is a dialogue move made inside an utterance and licensed as a
clarification request is: the utterance in progress sits in PENDING, a question about one of its
constituents is accommodated as MaxQUD, and what follows must be co-propositional with that
question. Backward Looking Appropriateness Repair (48) accommodates what the speaker meant by a
constituent `u0`, with `u0` as focus-establishing constituent; the Forward Looking Utterance Rule
(65), triggered by an editing phrase such as *uh*, accommodates what the speaker means to say after
`u0`, with none. Both are clarification rules of the gameboard (`Gameboard.clarify`) that leave the
turn open, so the alteration may come from either participant, and Pending replacement (40) then
replaces the utterance in progress.

Co-propositionality (34) is derived rather than stipulated: questions denote partial functions from
records to propositions, two questions are co-propositional when some record makes them the same
proposition, and a move is co-propositional with a question when the question it contributes to
QUD is. Since what the speaker meant by `u0` ranges over the type of `u0`'s denotation, *quite a
bit* answers the question what was meant by *a little bit* and *swimming* does not
(`Act.copropositional_mean_iff`), and the examples of §§3–5 are licensed exactly when acceptable
(`rows_licensed`). The derivations of (41) and (49) reach the gameboards (43) and (52)
(`Ex41.dgb2`, `Ex49.dgb2`). A self addressed query such as *what's his name?* (72a) is not
co-propositional with what the speaker means to say next (`not_copropositional_named`,
`rows_selfAddressed`), against the paper's claim.

## Implementation notes

* A record is empty or has one field (`Option Entity`). A polar question is defined on every
  record, any record being of the empty record type, and a wh-question on the records of its
  domain. A proposition predicates a body of an entity, so propositions are equal when predicate and
  argument are, as the examples of (34b) assume.
* Fragments carry the content short-answer resolution gives them (*Boston* asserts
  `MeanNextUtt(A, in, Boston)`); resolution itself is not modelled.
* An utterance in progress has no represented content (`Act.inProgress`), and its constituents
  list only the sub-utterances the examples repair, which covers the non-constituent reparandum of
  (63c) too.
* Grounding (31) asks that the locutionary proposition be true, which is not represented: Move
  update/Pending downdate (`Rule.ground`) integrates MaxPending unconditionally, and the facts
  Utterance Interpolation adds about the speech event are left out.
* SubstInst (40b) holds of any two utterances whose fields have fixed types, so Pending replacement
  constrains only which utterance is replaced; that the replacement reflects the speaker's
  intention is its argument.
* The paper licenses (41) by Parameter identification (36), whose simplified formulation leaves the
  turn open; with the turn change of [ginzburg-2012] (70), A's own continuation is Backward Looking
  Appropriateness Repair with the turn kept.

## Errata

* (43)'s second QUD element `λx Mean(A, u0, x)` and (44)'s move `Assert(A, Mean(A, u0, jacques))`
  print `u0` where the prose and (43)'s own move have `u_georges`.
* (44) drops `Named(Georges, georges)` from FACTS, which no rule removes and which the prose
  (p. 9:37) says stays accessible.
* The entry for *uh* (66) has the content `FLDEdit(spkr, addr, MaxPending) : Prop`, where the
  Forward Looking Utterance Rule (65) requires `FLDEdit(spkr, u0) : IllocProp` and (67) writes
  `FLDEdit(A, B, in)`; (66) and (51) also use the labels `c1` and `c2` twice each.
* Self addressed queries (72)–(73) are said to be licensed because they are co-propositional with
  `λx MeanNextUtt(A, u0, x)` (p. 9:53), but under (34b) a query such as `λx Named(him, x)` yields a
  different proposition on every record. The *what did you/I say?* rows of Table 1 fit the question
  of Utterance repetition (38b) instead.

## TODO

* (44) and (53) show QUD empty after an acceptance that MOVES does not record; the derivations here
  stop at Pending replacement, with QUD as Utterance Interpolation left it.
* The short answer *Boston* (67) resolves against an empty FEC, which the fragment rule of
  [ginzburg-2012], matching the fragment's category against the FEC's, does not allow; the paper
  does not address this.
* (57), whose alteration *that's red* is sentential, needs the inference from answer to Pending
  replacement the paper mentions, and the embedded correction (62) needs *the first place* to refer
  to `u1`.
* The universal (14) on negation as an editing phrase, the counts of Table 1, and the type
  refinement of Pending extension (39b) are not represented.

## References

* [ginzburg-fernandez-schlangen-2014]
* [ginzburg-2012]
-/

@[expose] public section

namespace GinzburgFernandezSchlangen2014

open Discourse
open Discourse.Gameboard (Turn)

/-- The two participants. -/
inductive Agent
  | A
  | B
  deriving DecidableEq, Repr

/-- The semantic types of the denotations of the examples' sub-utterances. -/
inductive SemType
  | individual
  | relation
  | kind
  | degree
  | activity
  | property
  | copula
  deriving DecidableEq, Repr

/-- The denotations of the examples' sub-utterances. -/
inductive Entity
  | bo
  | jo
  | georges
  | jacques
  | boston
  | him
  | «in»
  | «from»
  | earphones
  | headphones
  | aLittleBit
  | quiteABit
  | swimming
  | aBigSeller
  | been
  | its
  deriving DecidableEq, Repr, Fintype

/-- The semantic type of an entity. -/
def Entity.type : Entity → SemType
  | .bo | .jo | .georges | .jacques | .boston | .him => .individual
  | .«in» | .«from» => .relation
  | .earphones | .headphones => .kind
  | .aLittleBit | .quiteABit => .degree
  | .swimming => .activity
  | .aBigSeller => .property
  | .been | .its => .copula

/-- The syntactic categories of the examples' utterances and sub-utterances. -/
inductive Category
  | s
  | np
  | n
  | p
  | adv
  | v
  | interjection
  deriving DecidableEq, Repr

/-- The grammatical domain of the examples, whose contextual parameters are not at issue. -/
abbrev grammar : GrammaticalDomain :=
  { Form := String, Category := Category, Label := Empty, Denotation := Entity }

/-- The predicates the examples' propositions and questions are built from. -/
inductive Body
  /-- `Mean(a, u, ·)`, what `a` meant by `u`. -/
  | mean (a : Agent) (u : SubUtterance grammar)
  /-- `MeanNextUtt(a, u, ·)`, what `a` means to say after `u`. -/
  | meanNext (a : Agent) (u : SubUtterance grammar)
  /-- `Named(y, ·)`, the name of `y`. -/
  | named (y : Entity)
  /-- `Leave(·)`. -/
  | left
  /-- `In(l, ·)`, being here. -/
  | here
  deriving DecidableEq

/-- A proposition predicates a body of an entity. -/
structure Proposition where
  body : Body
  arg : Entity
  deriving DecidableEq

/-- A question: polar, or abstracting over the entities of a domain. -/
inductive Question
  | polar (p : Proposition)
  | which (b : Body) (dom : Finset Entity)
  deriving DecidableEq

namespace Question

/-- A question applied to a record, `none` outside its domain. -/
def apply : Question → Option Entity → Option Proposition
  | .polar p, _ => some p
  | .which b dom, some x => if x ∈ dom then some ⟨b, x⟩ else none
  | .which _ _, none => none

/-- Co-propositionality (34b): some record makes the two questions the same proposition. -/
def Copropositional (q₀ q₁ : Question) : Prop :=
  ∃ r, ∃ p ∈ q₀.apply r, p ∈ q₁.apply r

instance : DecidableRel Copropositional := fun _ _ ↦ by unfold Copropositional; infer_instance

/-- What `a` meant by `u`, ranging over the type of `u`'s denotation. -/
def meant (a : Agent) (u : SubUtterance grammar) : Question :=
  .which (.mean a u) {x | x.type = u.denotation.type}

/-- What `a` means to say after `u`. -/
def meantNext (a : Agent) (u : SubUtterance grammar) : Question :=
  .which (.meanNext a u) .univ

end Question

/-- The contents of moves. -/
inductive Act
  | assert (p : Proposition)
  | ask (q : Question)
  /-- `FLDEdit(spkr, u)`, the speaker searching for what to say after `u` (65). -/
  | fldEdit (u : SubUtterance grammar)
  /-- The content of an utterance in progress. -/
  | inProgress
  deriving DecidableEq

namespace Act

/-- The question a move contributes to QUD (34a): `q` for `Ask(q)`, `p?` for `Assert(p)`. -/
def qudContrib : Act → Option Question
  | .assert p => some (.polar p)
  | .ask q => some q
  | _ => none

/-- Co-propositionality of a move with a question (34a). -/
def Copropositional (m : Act) (q : Question) : Prop :=
  ∃ q₀ ∈ m.qudContrib, q₀.Copropositional q

instance : DecidableRel Copropositional := fun _ _ ↦ by unfold Copropositional; infer_instance

/-- An assertion that `a` meant `x` by `u` answers what `a` meant by `u` exactly when `x` is of the
type of `u`'s denotation. -/
theorem copropositional_mean_iff {a : Agent} {u : SubUtterance grammar} {x : Entity} :
    (assert ⟨.mean a u, x⟩).Copropositional (.meant a u) ↔ x.type = u.denotation.type := by
  simp [Copropositional, qudContrib, Question.Copropositional, Question.apply, Question.meant,
    Option.exists]

theorem copropositional_meanNext (a : Agent) (u : SubUtterance grammar) (x : Entity) :
    (assert ⟨.meanNext a u, x⟩).Copropositional (.meantNext a u) := by
  simp [Copropositional, qudContrib, Question.Copropositional, Question.apply, Question.meantNext,
    Option.exists]

end Act

/-- No query for a name is co-propositional with what `a` means to say after `u`: the two
questions yield different propositions on every record. -/
theorem not_copropositional_named (y : Entity) (dom : Finset Entity) (a : Agent)
    (u : SubUtterance grammar) :
    ¬ (Act.ask (.which (.named y) dom)).Copropositional (.meantNext a u) := by
  simp [Act.Copropositional, Act.qudContrib, Question.Copropositional, Question.apply,
    Question.meantNext, Option.forall]

/-- The domain of the examples' gameboards. -/
abbrev domain : Gameboard.Domain :=
  { toGrammaticalDomain := grammar, Participant := Agent, Fact := Proposition,
    Question := Question, Content := Act }

/-- A gameboard of the examples. -/
abbrev Board := Gameboard domain

/-- An utterance of the examples. -/
abbrev Utterance := LocutionaryProposition grammar Act

/-- The rules the derivations use, with the turn a rule leaves open made an argument: Pending
update and Move update/Pending downdate (31), Backward Looking Appropriateness Repair (48), the
Forward Looking Utterance Rule (65), Assert QUD-incrementation (22c), and Pending replacement
(40). -/
inductive Rule
  | pendingUpdate (u : Utterance) (speaker addressee : Agent)
  | ground
  | backwardRepair (t : Turn) (u : SubUtterance grammar) (m : Utterance)
  | forwardUtterance (t : Turn) (u : SubUtterance grammar) (m : Utterance)
  | assertQud
  | replacePending (w : Utterance)

/-- A rule as a partial map, `none` when the gameboard fails its preconditions. -/
def Rule.apply : Rule → Board → Option Board
  | .pendingUpdate u s a, d => some { d.pushPending u with speaker := s, addressee := a }
  | .ground, d => match d.pending with
    | v :: rest => some { d.recordMove v with pending := rest }
    | [] => none
  | .backwardRepair t u m, d =>
    d.clarify Act.Copropositional t (fun _ u ↦ ⟨.meant d.speaker u, {u}⟩) u m
  | .forwardUtterance t u m, d =>
    if d.latestContent = some (.fldEdit u) then
      d.clarify Act.Copropositional t (fun _ u ↦ ⟨.meantNext d.speaker u, ∅⟩) u m
    else none
  | .assertQud, d => match d.latestContent with
    | some (.assert p) => some (d.pushQud ⟨.polar p, ∅⟩)
    | _ => none
  | .replacePending w, d => match d.pending with
    | _ :: rest => some { d with pending := w :: rest }
    | [] => none

/-- Apply a derivation of rules in sequence. -/
def run (trace : List Rule) (d : Board) : Option Board :=
  trace.foldlM (fun d r ↦ r.apply d) d

/-- The initial gameboard: `A` addressing `B`. -/
def initial : Board := Gameboard.initial .A .B ∅

/-- An utterance with only its content recorded. -/
def utterance (m : Act) : Utterance :=
  { form := "", category := .s, content := m }

/-- An editing phrase such as *uh* after `u`. -/
def editing (u : SubUtterance grammar) : Utterance :=
  { form := "uh", category := .interjection, content := .fldEdit u }

example {t : Turn} {u : SubUtterance grammar} {m : Utterance} {d d' : Board}
    (h : (Rule.backwardRepair t u m).apply d = some d') :
    ∃ v ∈ d.maxPending, u ∈ v.constituents ∧ d'.qud = ⟨.meant d.speaker u, {u}⟩ :: d.qud := by
  simp only [Rule.apply] at h
  exact d.qud_clarify h

example {t : Turn} {u : SubUtterance grammar} {m : Utterance} {d d' : Board}
    (h : (Rule.forwardUtterance t u m).apply d = some d') :
    ∃ v ∈ d.maxPending, u ∈ v.constituents ∧ d'.qud = ⟨.meantNext d.speaker u, ∅⟩ :: d.qud := by
  simp only [Rule.apply] at h
  split_ifs at h
  exact d.qud_clarify h

example {w : Utterance} {d d' : Board} (h : (Rule.replacePending w).apply d = some d') :
    d'.facts = d.facts ∧ d'.qud = d.qud ∧ d'.moves = d.moves := by
  simp only [Rule.apply] at h
  split at h <;> cases h
  exact ⟨rfl, rfl, rfl⟩

-- p. 9
theorem copropositional_left :
    let whether : Question := .polar ⟨.left, .bo⟩
    let who : Question := .which .left {x | x.type = .individual}
    let which : Question := .which .left {.bo, .jo}
    whether.Copropositional who ∧ whether.Copropositional which ∧ who.Copropositional which := by
  decide

/-! ### The examples -/

/-- The words of the examples. -/
def lexicon : List (String × SubUtterance grammar) :=
  [("Bo", ⟨"Bo", .np, .bo⟩), ("Jo", ⟨"Jo", .np, .jo⟩),
    ("Georges", ⟨"Georges", .np, .georges⟩), ("Jacques", ⟨"Jacques", .np, .jacques⟩),
    ("Boston", ⟨"Boston", .np, .boston⟩), ("in", ⟨"in", .p, .«in»⟩),
    ("from", ⟨"from", .p, .«from»⟩), ("earphones", ⟨"earphones", .n, .earphones⟩),
    ("headphones", ⟨"headphones", .n, .headphones⟩),
    ("a little bit", ⟨"a little bit", .adv, .aLittleBit⟩),
    ("quite a bit", ⟨"quite a bit", .adv, .quiteABit⟩),
    ("swimming", ⟨"swimming", .v, .swimming⟩),
    ("a big seller", ⟨"a big seller", .np, .aBigSeller⟩), ("been", ⟨"been", .v, .been⟩),
    ("it's", ⟨"it's", .v, .its⟩)]

/-- The self addressed queries of the examples. -/
def queries : List (String × Question) :=
  [("what's his name", .which (.named .him) .univ)]

/-- Whether the rule looks back to a constituent already uttered or forward to what comes next. -/
inductive Direction
  | backward
  | forward
  deriving DecidableEq, Repr

/-- What follows the moment of interruption: an answer to the accommodated question, or a self
addressed query. -/
inductive FollowUp
  | answer (x : Entity)
  | selfAddressed (q : Question)
  deriving DecidableEq

/-- The follow-up answers the accommodated question. -/
def FollowUp.IsAnswer : FollowUp → Prop
  | .answer _ => True
  | .selfAddressed _ => False

instance : DecidablePred FollowUp.IsAnswer := fun f ↦ by
  cases f <;> unfold FollowUp.IsAnswer <;> infer_instance

/-- A row: the rule, who continues, the constituent `u0`, the follow-up, and the judgment. -/
structure Row where
  direction : Direction
  turn : Turn
  u0 : SubUtterance grammar
  followUp : FollowUp
  judgment : Judgment
  deriving DecidableEq

def Row.ofDatum (ex : Datum) : Option Row := do
  let dir ← ex.parse? "rule" [("backward looking", .backward), ("forward looking", .forward)]
  let turn ← ex.parse? "turn" [("kept", .keep), ("taken", .change)]
  let u0 ← ex.parse? "u0" lexicon
  let f ← (ex.parse? "answer" lexicon).map (.answer ·.denotation) <|>
    (ex.parse? "query" queries).map .selfAddressed
  pure ⟨dir, turn, u0, f, ex.judgment⟩

/-- The content of the follow-up, an answer resolved against the accommodated question. -/
def Row.content (r : Row) : Act :=
  match r.followUp, r.direction with
  | .answer x, .backward => .assert ⟨.mean .A r.u0, x⟩
  | .answer x, .forward => .assert ⟨.meanNext .A r.u0, x⟩
  | .selfAddressed q, _ => .ask q

/-- A's utterance in progress, with `u0` among its constituents. -/
def Row.pending (r : Row) : Utterance :=
  { form := "", category := .s, content := .inProgress, constituents := {r.u0} }

/-- The derivation of a row: A's utterance in progress, the editing phrase grounded after it for a
forward looking disfluency, and the rule licensing the follow-up. -/
def Row.trace (r : Row) : List Rule :=
  match r.direction with
  | .backward => [.pendingUpdate r.pending .A .B, .backwardRepair r.turn r.u0 (utterance r.content)]
  | .forward =>
    [.pendingUpdate r.pending .A .B, .pendingUpdate (editing r.u0) .A .B, .ground,
      .forwardUtterance r.turn r.u0 (utterance r.content)]

/-- The rule licenses the row's follow-up. -/
def Row.Licensed (r : Row) : Prop := run r.trace initial ≠ none

instance : DecidablePred Row.Licensed := fun _ ↦ by unfold Row.Licensed; infer_instance

/-- The nine rows of §§3–5. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

example : rows.length = 9 := by decide

/-- A follow-up answering the accommodated question is licensed exactly when the paper judges it
acceptable, whichever participant continues. -/
theorem rows_licensed :
    ∀ r ∈ rows, r.followUp.IsAnswer → (r.Licensed ↔ r.judgment = .acceptable) := by
  decide

/-- The self addressed query (72a) is attested but not licensed by the Forward Looking Utterance
Rule under (34). -/
theorem rows_selfAddressed : ∀ r ∈ rows, ¬ r.followUp.IsAnswer →
    r.judgment = .acceptable ∧ ¬ r.Licensed := by
  decide

/-! ### Cross-turn self-correction: (41) p. 9:35 -/

namespace Ex41

/-- The sub-utterance *Georges*. -/
def georges : SubUtterance grammar := ⟨"Georges", .np, .georges⟩

/-- A's question. -/
def u₀ : Utterance :=
  { form := "Is Georges here?", category := .s, content := .ask (.polar ⟨.here, .georges⟩),
    constituents := {georges} }

/-- A's correction. -/
def u₁ : Utterance :=
  { form := "I meant Jacques", category := .s, content := .assert ⟨.mean .A georges, .jacques⟩ }

/-- The corrected question. -/
def v₀ : Utterance :=
  { form := "Is Jacques here?", category := .s, content := .ask (.polar ⟨.here, .jacques⟩),
    constituents := {⟨"Jacques", .np, .jacques⟩} }

/-- (43): the correction answers what A meant by *Georges*, and its polar question is pushed. -/
theorem dgb2 :
    run [.pendingUpdate u₀ .A .B, .backwardRepair .keep georges u₁, .assertQud] initial = some
      { speaker := .A, addressee := .B, pending := [u₀], moves := [u₁],
        qud := [⟨.polar ⟨.mean .A georges, .jacques⟩, ∅⟩, ⟨.meant .A georges, {georges}⟩] } := by
  decide

-- (44)
theorem dgb3 :
    (run [.pendingUpdate u₀ .A .B, .backwardRepair .keep georges u₁, .assertQud,
      .replacePending v₀] initial).map (fun d ↦ (d.pending, d.moves)) = some ([v₀], [u₁]) := by
  decide

end Ex41

/-! ### Mid-utterance self-correction: (49) p. 9:43 -/

namespace Ex49

/-- The sub-utterance *in*. -/
def «in» : SubUtterance grammar := ⟨"in", .p, .«in»⟩

/-- *Take that book in*, in progress. -/
def u₀ : Utterance :=
  { form := "Take that book in", category := .s, content := .inProgress, constituents := {«in»} }

/-- *I meant from*. -/
def u₁ : Utterance :=
  { form := "I meant from", category := .s, content := .assert ⟨.mean .A «in», .«from»⟩ }

/-- *Take that book from*, in progress. -/
def v₀ : Utterance :=
  { form := "Take that book from", category := .s, content := .inProgress,
    constituents := {⟨"from", .p, .«from»⟩} }

/-- (52): what A meant by *in* is MaxQUD with *in* as FEC, and *I meant from* is LatestMove. -/
theorem dgb2 :
    run [.pendingUpdate u₀ .A .B, .backwardRepair .keep «in» u₁] initial = some
      { speaker := .A, addressee := .B, pending := [u₀], moves := [u₁],
        qud := [⟨.meant .A «in», {«in»}⟩] } := by
  decide

-- (53)
theorem dgb3 :
    (run [.pendingUpdate u₀ .A .B, .backwardRepair .keep «in» u₁, .replacePending v₀]
      initial).map (fun d ↦ (d.pending, d.moves)) = some ([v₀], [u₁]) := by
  decide

end Ex49

end GinzburgFernandezSchlangen2014
