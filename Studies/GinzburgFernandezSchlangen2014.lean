module

public import Linglib.Discourse.Gameboard.Rule
public import Linglib.Discourse.Gameboard.Question
public import Linglib.Data.Examples.GinzburgFernandezSchlangen2014
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Gloss
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Tactic.DeriveFintype

/-!
# Ginzburg, Fernández and Schlangen (2014): Disfluencies as intra-utterance dialogue moves

In [ginzburg-fernandez-schlangen-2014] a self-correction or a hesitation is a dialogue move made
inside an utterance and licensed as a clarification request is. The utterance in progress sits in
PENDING, a question about one of its constituents `u₀` is accommodated as MaxQUD, and what follows
must be co-propositional with that question. Backward Looking Appropriateness Repair accommodates
$\lambda x.\mathrm{Mean}(A, u_0, x)$, what the speaker meant by `u₀`, with `u₀` as
focus-establishing constituent. The Forward Looking Utterance Rule applies after an editing phrase
such as *uh*, whose content is `FLDEdit(A, u₀)`, and accommodates
$\lambda x.\mathrm{MeanNextUtt}(A, u_0, x)$, what the speaker means to say after `u₀`, with no
focus-establishing constituent. Both are Clarification Context Update Rules of the gameboard that
leave the turn open, and Pending replacement then replaces the utterance in progress.

Questions are partial functions from entities to propositions, and co-propositionality is
`Gameboard.Copropositional`. What the speaker meant by `u₀` is defined on the entities of the type
of `u₀`'s denotation. We prove that an assertion that the speaker meant `x` by `u₀` is
co-propositional with that question exactly when `x` is of that type, so *quite a bit* answers
what was meant by *a little bit* and *swimming* does not; that whether a follow-up is licensed
does not depend on which participant utters it; and that a wh-question is co-propositional with
what the speaker means to say next only if it is built from the same abstract. The examples are
licensed exactly when acceptable, and the derivations of the cross-turn and the mid-utterance
self-correction reach the paper's gameboards.

## Implementation notes

* A record has one field, so a question is a partial function `Entity →. Proposition`: a polar
  question is `PFun.pure p` and a wh-question `PFun.res f s`. A proposition predicates a body of
  an entity, so that propositions are equal when predicate and argument are.
* A self addressed query such as *what's his name?* is represented as what the speaker means to
  say next restricted to the entities the query asks for, a question that differs from MaxQUD in
  its domain. A question with an abstract of its own, such as $\lambda x.\mathrm{Named}(y, x)$,
  is co-propositional with MaxQUD only where the two abstracts have a common value.
* Fragments carry the content short-answer resolution gives them (*Boston* asserts
  `MeanNextUtt(A, in, Boston)`); resolution itself is not modelled.
* An utterance in progress has no represented content, and its constituents list only the
  sub-utterances the examples repair.
* A rule is a relation between gameboards, so `Disfluency.Licensed` is an existential over the
  gameboards a rule allows and is decided through its characterizations.
* Grounding asks that the locutionary proposition be true, which is not represented: `Gameboard.PendingDowndate`
  integrates MaxPending unconditionally, and the facts Utterance Interpolation adds about the
  speech event are left out.
* Pending replacement asks that the replacement be a substitution instance of MaxPending that
  reflects the speaker's intention. The first holds of any two utterances whose fields have fixed
  types and the second is not represented, so the rule is `Gameboard.PendingReplacement ⊤`.

## TODO

* The paper's gameboards after Pending replacement show QUD empty after an acceptance that MOVES
  does not record; the derivations here stop at Pending replacement.
* The short answer *Boston* resolves against an empty focus-establishing constituent, which the
  fragment rule of [ginzburg-2012], matching the fragment's category against that constituent's,
  does not allow.
* A sentential alteration (*From yellow down to brown — no — that's red*) needs the inference
  from answer to Pending replacement, and an embedded correction needs reference to a
  sub-utterance.
* The distribution of self addressed queries over the category of the context, the universal on
  negation as an editing phrase, and the type refinement of Pending extension are not
  represented.

## References

* [ginzburg-fernandez-schlangen-2014]
* [ginzburg-2012]
-/

@[expose] public section

namespace GinzburgFernandezSchlangen2014

open Gameboard

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
  | .bo | .jo | .georges | .jacques | .boston => .individual
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

/-- A sub-utterance of the examples has an orthographic form, a category and the entity it
denotes. -/
abbrev Constituent := SubUtterance String Category Entity

/-- The predicates the examples' propositions and questions are built from. -/
inductive Body
  /-- `Mean(a, u, ·)`, what `a` meant by `u`. -/
  | mean (a : Agent) (u : Constituent)
  /-- `MeanNextUtt(a, u, ·)`, what `a` means to say after `u`. -/
  | meanNext (a : Agent) (u : Constituent)
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

theorem Proposition.mk_injective (b : Body) : Function.Injective (Proposition.mk b) :=
  fun _ _ h ↦ (Proposition.mk.injEq ..).mp h |>.2

/-- A question is a partial function from entities to propositions. -/
abbrev Question := Entity →. Proposition

/-- $\lambda x.\mathrm{Mean}(a, u, x)$, what `a` meant by `u`, on the entities of the type of
`u`'s denotation. -/
def meant (a : Agent) (u : Constituent) : Question :=
  PFun.res (Proposition.mk (.mean a u)) {x | x.type = u.denotation.type}

/-- $\lambda x.\mathrm{MeanNextUtt}(a, u, x)$, what `a` means to say after `u`, on the entities
in `s`. -/
def meantNext (a : Agent) (u : Constituent) (s : Set Entity := Set.univ) : Question :=
  PFun.res (Proposition.mk (.meanNext a u)) s

/-- The contents of moves. -/
inductive Act
  | assert (p : Proposition)
  | ask (q : Question)
  /-- `FLDEdit(spkr, u)`, the speaker searching for what to say after `u`. -/
  | fldEdit (u : Constituent)
  /-- The content of an utterance in progress. -/
  | inProgress

namespace Act

variable {a : Agent} {u : Constituent} {x : Entity} {p : Proposition} {q q₀ : Question}
  {b : Body} {s : Set Entity}

/-- (34a): the question a move contributes to QUD, `q` for `Ask(q)` and `p?` for `Assert(p)`. -/
def qudContrib : Act → Option Question
  | .assert p => some (PFun.pure p)
  | .ask q => some q
  | _ => none

/-- (34a): a move is co-propositional with a question when the question it contributes to QUD
is. -/
def Copropositional (m : Act) (q : Question) : Prop :=
  ∃ q₀ ∈ m.qudContrib, Gameboard.Copropositional q₀ q

theorem copropositional_assert :
    (assert p).Copropositional q ↔ Gameboard.Copropositional (PFun.pure p) q := by
  simp [Copropositional, qudContrib]

@[simp] theorem copropositional_ask :
    (ask q₀).Copropositional q ↔ Gameboard.Copropositional q₀ q := by
  simp [Copropositional, qudContrib]

@[simp] theorem not_copropositional_fldEdit : ¬(fldEdit u).Copropositional q := by
  simp [Copropositional, qudContrib]

@[simp] theorem not_copropositional_inProgress : ¬inProgress.Copropositional q := by
  simp [Copropositional, qudContrib]

/-- An assertion that `a` meant `x` by `u` is co-propositional with what `a` meant by `u` exactly
when `x` is of the type of `u`'s denotation. -/
theorem copropositional_assert_meant :
    (assert ⟨.mean a u, x⟩).Copropositional (meant a u) ↔ x.type = u.denotation.type :=
  copropositional_assert.trans (copropositional_pure_res_of_injective (Proposition.mk_injective _))

-- p. 9:51
theorem copropositional_assert_meantNext :
    (assert ⟨.meanNext a u, x⟩).Copropositional (meantNext a u s) ↔ x ∈ s :=
  copropositional_assert.trans (copropositional_pure_res_of_injective (Proposition.mk_injective _))

-- p. 9:53
theorem copropositional_ask_meantNext :
    (ask (meantNext a u s)).Copropositional (meantNext a u) ↔ s.Nonempty := by
  simp [meantNext, copropositional_res_res_self]

/-- A wh-question on an inhabited type is co-propositional with what `a` means to say after `u`
only if it is built from the same abstract. -/
theorem body_eq_of_copropositional_meantNext
    (h : (ask (PFun.res (Proposition.mk b) s)).Copropositional (meantNext a u)) :
    b = .meanNext a u := by
  obtain ⟨_, _, h⟩ := copropositional_res_res.mp (copropositional_ask.mp h)
  exact ((Proposition.mk.injEq ..).mp h).1

theorem not_copropositional_ask_meantNext_meant :
    ¬(ask (meantNext a u s)).Copropositional (meant a u) := by
  simp [meantNext, meant, copropositional_res_res]

end Act

/-- An utterance of the examples, whose contextual parameters are not at issue. -/
abbrev Utterance := LocutionaryProposition String Category Empty Entity Act

/-- A gameboard of the examples. -/
abbrev Board := Gameboard Agent Proposition Utterance (InformationStructure Question Constituent)

/-! ### The rules -/

/-- (48): Backward Looking Appropriateness Repair accommodates what the speaker meant by a
constituent `u` of MaxPending, with `u` as focus-establishing constituent, and leaves the turn
open. -/
def BackwardRepair : Board → Board → Prop :=
  turnUnderspec fun d d' ↦
    ∃ u, Clarification Act.Copropositional u (fun _ ↦ ⟨meant d.speaker u, {u}⟩) d d'

/-- (65): the Forward Looking Utterance Rule accommodates, after an editing phrase following a
constituent `u` of MaxPending, what the speaker means to say next, with no focus-establishing
constituent, and leaves the turn open. -/
def ForwardUtterance : Board → Board → Prop :=
  turnUnderspec fun d d' ↦ ∃ u, d.latestContent = some (.fldEdit u) ∧
    Clarification Act.Copropositional u (fun _ ↦ ⟨meantNext d.speaker u, ∅⟩) d d'

/-- (22c): Assert QUD-incrementation, which makes `p?` MaxQUD once `p` is asserted. -/
def AssertQud : Board → Board → Prop :=
  QudIncrementation fun
    | .assert p => some (PFun.pure p)
    | _ => none

/-- The initial gameboard: `A` addressing `B`. -/
def initial : Board := Gameboard.initial .A .B ∅

/-- An utterance with only its content recorded. -/
def utterance (m : Act) : Utterance :=
  { form := "", category := .s, content := m }

/-- (66): an editing phrase such as *uh* after `u`. -/
def editing (u : Constituent) : Utterance :=
  { form := "uh", category := .interjection, content := .fldEdit u }

section

variable {m : Utterance} {d d' : Board} {a : Agent}

theorem backwardRepair_swapTurn_iff : BackwardRepair d d'.swapTurn ↔ BackwardRepair d d' :=
  turnUnderspec_swapTurn_iff

theorem forwardUtterance_swapTurn_iff : ForwardUtterance d d'.swapTurn ↔ ForwardUtterance d d' :=
  turnUnderspec_swapTurn_iff

theorem exists_backwardRepair_iff (ha : a = d.speaker ∨ a = d.addressee) :
    (∃ d', BackwardRepair d d' ∧ d'.latestMove = some m ∧ d'.speaker = a) ↔
      ∃ u, ∃ v ∈ d.maxPending, u ∈ v.constituents ∧
        m.content.Copropositional (meant d.speaker u) := by
  rw [BackwardRepair, exists_turnUnderspec_speaker_iff
    (fun _ ⟨_, h⟩ ↦ ⟨h.speaker, h.addressee⟩) ha]
  exact ⟨fun ⟨d', ⟨u, h⟩, hm⟩ ↦ ⟨u, coherent_clarification_iff.mp ⟨d', h, hm⟩⟩,
    fun ⟨u, h⟩ ↦
      let ⟨d', hd, hm⟩ := coherent_clarification_iff.mpr h
      ⟨d', ⟨u, hd⟩, hm⟩⟩

theorem exists_forwardUtterance_iff (ha : a = d.speaker ∨ a = d.addressee) :
    (∃ d', ForwardUtterance d d' ∧ d'.latestMove = some m ∧ d'.speaker = a) ↔
      ∃ u, d.latestContent = some (.fldEdit u) ∧ ∃ v ∈ d.maxPending, u ∈ v.constituents ∧
        m.content.Copropositional (meantNext d.speaker u) := by
  rw [ForwardUtterance, exists_turnUnderspec_speaker_iff
    (fun _ ⟨_, _, h⟩ ↦ ⟨h.speaker, h.addressee⟩) ha]
  exact ⟨fun ⟨d', ⟨u, hu, h⟩, hm⟩ ↦ ⟨u, hu, coherent_clarification_iff.mp ⟨d', h, hm⟩⟩,
    fun ⟨u, hu, h⟩ ↦
      let ⟨d', hd, hm⟩ := coherent_clarification_iff.mpr h
      ⟨d', ⟨u, hu, hd⟩, hm⟩⟩

end

-- p. 9:30
theorem copropositional_left :
    let whether : Question := PFun.pure ⟨.left, .bo⟩
    let who : Question := PFun.res (Proposition.mk .left) {x | x.type = .individual}
    let which : Question := PFun.res (Proposition.mk .left) {.bo, .jo}
    Gameboard.Copropositional whether who ∧ Gameboard.Copropositional whether which ∧
      Gameboard.Copropositional who which := by
  refine ⟨?_, ?_, ?_⟩
  · exact (copropositional_pure_res_of_injective (Proposition.mk_injective _)).mpr rfl
  · exact (copropositional_pure_res_of_injective (Proposition.mk_injective _)).mpr (.inl rfl)
  · exact copropositional_res_res_self.mpr ⟨.bo, rfl, .inl rfl⟩

/-! ### The examples -/

/-- What follows the moment of interruption. -/
inductive FollowUp
  /-- A fragment denoting `x`, resolved as an answer to the accommodated question. -/
  | answer (x : Entity)
  /-- A self addressed query for what the speaker means to say next among the entities in `s`. -/
  | query (s : Finset Entity)
  deriving DecidableEq

/-- A disfluency: its direction, who utters what follows, the constituent `u₀` the accommodated
question is about, and what follows. -/
structure Disfluency where
  direction : Examples.Direction
  continuer : Agent
  u₀ : Constituent
  followUp : FollowUp
  deriving DecidableEq

namespace Disfluency

variable (i : Disfluency)

/-- The content of the follow-up. -/
def content : Act :=
  match i.followUp, i.direction with
  | .answer x, .backward => .assert ⟨.mean .A i.u₀, x⟩
  | .answer x, .forward => .assert ⟨.meanNext .A i.u₀, x⟩
  | .query s, _ => .ask (meantNext .A i.u₀ s)

/-- A's utterance in progress, with `u₀` among its constituents. -/
def pending : Utterance :=
  { form := "", category := .s, content := .inProgress, constituents := {i.u₀} }

/-- The gameboard at the moment of interruption: A's utterance in progress is pending. -/
def board : Board := initial.pendingUpdate i.pending .A .B

/-- The disfluency's rule licenses its follow-up, uttered by its continuer: Backward Looking
Appropriateness Repair at the moment of interruption, or the Forward Looking Utterance Rule once
an editing phrase has been uttered and grounded. -/
def Licensed : Prop :=
  match i.direction with
  | .backward => ∃ d', BackwardRepair i.board d' ∧ d'.latestMove = some (utterance i.content) ∧
      d'.speaker = i.continuer
  | .forward => ∃ d₁ d', PendingDowndate (i.board.pendingUpdate (editing i.u₀) .A .B) d₁ ∧
      ForwardUtterance d₁ d' ∧ d'.latestMove = some (utterance i.content) ∧
      d'.speaker = i.continuer

variable {a a' : Agent} {u : Constituent} {x : Entity} {s : Finset Entity} {f : FollowUp}

private theorem agent_cases (a : Agent) : a = .A ∨ a = .B := by cases a <;> simp

theorem licensed_backward_iff : Licensed ⟨.backward, a, u, f⟩ ↔
    (content ⟨.backward, a, u, f⟩).Copropositional (meant .A u) := by
  refine (exists_backwardRepair_iff (agent_cases a)).trans ⟨?_, fun h ↦ ⟨u, _, rfl, ?_, h⟩⟩
  · rintro ⟨u', v, hv, hu, h⟩
    cases hv
    cases Finset.mem_singleton.mp hu
    exact h
  · exact Finset.mem_singleton_self u

theorem licensed_forward_iff : Licensed ⟨.forward, a, u, f⟩ ↔
    (content ⟨.forward, a, u, f⟩).Copropositional (meantNext .A u) := by
  let d₀ : Board := (board ⟨.forward, a, u, f⟩).pendingUpdate (editing u) .A .B
  let d₁ : Board := { d₀.recordMove (editing u) with pending := [pending ⟨.forward, a, u, f⟩] }
  have h₁ : ∀ e, PendingDowndate d₀ e ↔ e = d₁ := fun _ ↦ pendingDowndate_iff rfl
  have h₂ := exists_forwardUtterance_iff (d := d₁)
    (m := utterance (content ⟨.forward, a, u, f⟩)) (agent_cases a)
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨e, d', he, hd⟩
    obtain rfl := (h₁ e).mp he
    obtain ⟨u', hu', v, hv, -, h⟩ := h₂.mp ⟨d', hd⟩
    cases hu'
    exact h
  · obtain ⟨d', hd⟩ := h₂.mpr ⟨u, rfl, _, rfl, Finset.mem_singleton_self u, h⟩
    exact ⟨d₁, d', (h₁ d₁).mpr rfl, hd⟩

-- p. 9:38
theorem licensed_backward_answer_iff :
    Licensed ⟨.backward, a, u, .answer x⟩ ↔ x.type = u.denotation.type :=
  licensed_backward_iff.trans Act.copropositional_assert_meant

theorem not_licensed_backward_query : ¬Licensed ⟨.backward, a, u, .query s⟩ :=
  fun h ↦ Act.not_copropositional_ask_meantNext_meant (licensed_backward_iff.mp h)

theorem licensed_forward_answer : Licensed ⟨.forward, a, u, .answer x⟩ :=
  licensed_forward_iff.mpr (Act.copropositional_assert_meantNext.mpr trivial)

theorem licensed_forward_query_iff : Licensed ⟨.forward, a, u, .query s⟩ ↔ s.Nonempty :=
  licensed_forward_iff.trans (Act.copropositional_ask_meantNext.trans Finset.coe_nonempty)

instance : DecidablePred Licensed
  | ⟨.backward, _, _, .answer _⟩ => decidable_of_iff _ licensed_backward_answer_iff.symm
  | ⟨.backward, _, _, .query _⟩ => .isFalse not_licensed_backward_query
  | ⟨.forward, _, _, .answer _⟩ => .isTrue licensed_forward_answer
  | ⟨.forward, _, _, .query _⟩ => decidable_of_iff _ licensed_forward_query_iff.symm

/-- Whether a follow-up is licensed does not depend on which participant utters it. -/
theorem licensed_continuer_iff {dir : Examples.Direction} :
    Licensed ⟨dir, a, u, f⟩ ↔ Licensed ⟨dir, a', u, f⟩ := by
  cases dir
  · exact licensed_backward_iff.trans (licensed_backward_iff (a := a')).symm
  · exact licensed_forward_iff.trans (licensed_forward_iff (a := a')).symm

end Disfluency

/-- The sub-utterance a lexeme of the examples names. -/
def _root_.GinzburgFernandezSchlangen2014.Examples.Lexeme.constituent :
    Examples.Lexeme → Constituent
  | .bo => ⟨"Bo", .np, .bo⟩
  | .jo => ⟨"Jo", .np, .jo⟩
  | .georges => ⟨"Georges", .np, .georges⟩
  | .jacques => ⟨"Jacques", .np, .jacques⟩
  | .boston => ⟨"Boston", .np, .boston⟩
  | .inP => ⟨"in", .p, .«in»⟩
  | .fromP => ⟨"from", .p, .«from»⟩
  | .earphones => ⟨"earphones", .n, .earphones⟩
  | .headphones => ⟨"headphones", .n, .headphones⟩
  | .aLittleBit => ⟨"a little bit", .adv, .aLittleBit⟩
  | .quiteABit => ⟨"quite a bit", .adv, .quiteABit⟩
  | .swimming => ⟨"swimming", .v, .swimming⟩
  | .aBigSeller => ⟨"a big seller", .np, .aBigSeller⟩
  | .been => ⟨"been", .v, .been⟩
  | .its => ⟨"it's", .v, .its⟩

/-- The entities a kind of self addressed query asks for. -/
def _root_.GinzburgFernandezSchlangen2014.Examples.Query.domain : Examples.Query → Finset Entity
  | .name => {x | x.type = .individual}

/-- Who utters the follow-up: A, whose utterance is interrupted, or B. -/
def _root_.GinzburgFernandezSchlangen2014.Examples.Continuer.agent : Examples.Continuer → Agent
  | .kept => .A
  | .taken => .B

/-- The disfluency of an example: the reparandum, and the alteration or else the query. -/
def disfluency (x : Examples.Example) : Option Disfluency := do
  let u₀ ← (x.lexemes .reparandum).head?
  let f ← ((x.lexemes .alteration).head?.map fun l ↦ FollowUp.answer l.constituent.denotation) <|>
    x.query.map fun q ↦ .query q.domain
  pure ⟨← x.direction, (← x.continuer).agent, u₀.constituent, f⟩

-- every example is read
example : ∀ x : Examples.Example, (disfluency x).isSome := by decide

-- every span that names a lexeme is printed as its sub-utterance is written
example : ∀ x : Examples.Example, ∀ s ∈ x.datum.spans, ∀ l ∈ Examples.lexeme? s,
    (s.words x.datum).map (·.wordform) = Gloss.formTokens l.constituent.form := by
  decide

/-- A follow-up is licensed exactly when the paper judges the example acceptable. -/
theorem licensed_iff_acceptable : ∀ x : Examples.Example, ∀ i ∈ disfluency x,
    (i.Licensed ↔ x.datum.judgment = .acceptable) := by
  decide

/-! ### Cross-turn self-correction: (41) -/

namespace Ex41

/-- The sub-utterance *Georges*. -/
def georges : Constituent := ⟨"Georges", .np, .georges⟩

/-- A's question. -/
def u₀ : Utterance :=
  { form := "Is Georges here?", category := .s, content := .ask (PFun.pure ⟨.here, .georges⟩),
    constituents := {georges} }

/-- A's correction. -/
def u₁ : Utterance :=
  { form := "I meant Jacques", category := .s, content := .assert ⟨.mean .A georges, .jacques⟩ }

/-- The corrected question. -/
def v₀ : Utterance :=
  { form := "Is Jacques here?", category := .s, content := .ask (PFun.pure ⟨.here, .jacques⟩),
    constituents := {⟨"Jacques", .np, .jacques⟩} }

/-- (42): A's question is pending. -/
def dgb1 : Board := initial.pendingUpdate u₀ .A .B

/-- (43): what A meant by *Georges* and the polar question of the correction are under
discussion, and the correction is LatestMove. -/
def dgb2 : Board :=
  { speaker := .A, addressee := .B, pending := [u₀], moves := [u₁],
    qud := [⟨PFun.pure ⟨.mean .A georges, .jacques⟩, ∅⟩, ⟨meant .A georges, {georges}⟩] }

/-- (44): the corrected question is pending. -/
def dgb3 : Board := { dgb2 with pending := [v₀] }

theorem comp_dgb1_dgb2 : Relation.Comp BackwardRepair AssertQud dgb1 dgb2 :=
  ⟨_, le_turnUnderspec _ _ ⟨georges, u₀, rfl, Finset.mem_singleton_self _, u₁,
    Act.copropositional_assert_meant.mpr rfl, rfl⟩, _, rfl, rfl⟩

theorem pendingReplacement_dgb2_dgb3 : PendingReplacement ⊤ dgb2 dgb3 :=
  ⟨u₀, [], v₀, rfl, trivial, rfl⟩

end Ex41

/-! ### Mid-utterance self-correction: (49) -/

namespace Ex49

/-- The sub-utterance *in*. -/
def «in» : Constituent := ⟨"in", .p, .«in»⟩

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

/-- (50): *Take that book in* is pending. -/
def dgb1 : Board := initial.pendingUpdate u₀ .A .B

/-- (52): what A meant by *in* is MaxQUD with *in* as focus-establishing constituent, and
*I meant from* is LatestMove. -/
def dgb2 : Board :=
  { speaker := .A, addressee := .B, pending := [u₀], moves := [u₁],
    qud := [⟨meant .A «in», {«in»}⟩] }

/-- (53): *Take that book from* is pending. -/
def dgb3 : Board := { dgb2 with pending := [v₀] }

theorem backwardRepair_dgb1_dgb2 : BackwardRepair dgb1 dgb2 :=
  le_turnUnderspec _ _ ⟨«in», u₀, rfl, Finset.mem_singleton_self _, u₁,
    Act.copropositional_assert_meant.mpr rfl, rfl⟩

theorem pendingReplacement_dgb2_dgb3 : PendingReplacement ⊤ dgb2 dgb3 :=
  ⟨u₀, [], v₀, rfl, trivial, rfl⟩

end Ex49

end GinzburgFernandezSchlangen2014
