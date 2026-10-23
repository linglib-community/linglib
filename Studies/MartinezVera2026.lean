module

public import Linglib.Data.Examples.MartinezVera2026
public import Linglib.Discourse.Commitment.Basic
public import Linglib.Discourse.Role
public import Linglib.Fragments.Quechua.SaraguroKichwa.Evidentiality
public import Linglib.Semantics.ConventionalImplicature
public import Linglib.Semantics.Evidential.Basic
public import Linglib.Semantics.Exhaustification.InnocentExclusion
public import Linglib.Semantics.Questions.Resolution

/-!
# Martínez Vera (2026)

Martínez Vera analyzes the Saraguro Kichwa enclitic *=mi* as a focus marker. A sentence with
*=mi* and scope `p` presupposes an alternative to `p` that is highlighted in the context and that,
exhaustified relative to the alternatives, entails `¬p`; a proposition is highlighted when a move
on record addresses the question under discussion with it. A declarative with the direct
evidential *-rka* is an assertion and addresses that question by `p`, while one with the
reportative *-shka* presents `p` and addresses it by `p` or `¬p`, so only the latter can be
confirmed with *=mi*. In a correction the highlighted proposition is the corrected one, and
exhaustifying it relative to the alternatives of the constituent *=mi* marks yields `¬p`.

## Main definitions

* `withEvidential`: an evidential applied to a sentence.
* `Move.assert`, `Move.present`, `Move.declare`: the illocutionary operators, and the one a
  declarative with a given evidential performs.
* `Highlighted`, `MiDefined`: highlighting, and the presupposition of *=mi*.

## Main statements

* `miDefined_univ_iff`: for *=mi* on a clause exhaustification is vacuous, and *=mi* needs a
  highlighted proposition entailing `¬p`.
* `miDefined_update_present`, `miDefined_update_assert_iff`: presenting `p` licenses *=mi* on
  `p`, and asserting it does not.
* `miDefined_of_isInnocentlyExcludable`: corrections.
* `judgment_eq_acceptable_iff_miDefined`, `judgment_eq_acceptable_iff_nonempty`: an example is
  acceptable exactly when the analysis licenses its *=mi*, or its speaker stays consistent.

## Implementation notes

The paper's composition rule I is the bind of `TwoDim`, whose `⊤` plays the empty not-at-issue
layer. An illocutionary operator is the move it puts on record: its speaker's commitments,
without their addressee, and the propositions by which it addresses the question under
discussion, addressing being partial answerhood. Exhaustification is innocent exclusion; the
paper glosses the alternatives it may deny as those entailing the prejacent, under which a
correction would not entail `¬p`. Highlighting is the paper's notion, not the compositional
highlighting of `Semantics/Questions/Highlighting.lean`. The operator name `present` is
Faller's. The examples are evaluated in a model whose worlds are sets of events. The paper's
survey of *=mi* across Quechuan, after Faller, Sánchez, Tellings, Grzech and Bendezú, finds the
analyses hard to compare at present and is not formalized.

## TODO

* The paper describes *=mi* in (27d) as marking the verb; with alternatives varying the verb
  phrase, which include buying a pig, (37) would license it.
* Footnote 7's use of *-rka* by an authority without direct perception, and the past tense of
  *-rka* and *-shka*, are not modelled.

## References

* [martinez-vera-2026]
* [bendezu-2023]
* [faller-2002]
* [fox-2007]
* [grzech-2020]
* [krifka-2014]
* [krifka-2017]
* [murray-2014]
* [sanchez-2010]
* [simons-tonhauser-beaver-roberts-2010]
* [tellings-2014]
-/

@[expose] public section

namespace MartinezVera2026

open ConventionalImplicature (TwoDim)
open Exhaustification (exhIE IsInnocentlyExcludable)
open Quechua.SaraguroKichwa.Evidentiality (rka shka shi)

variable {A W : Type*}

/-! ### Evidentials -/

/-- `evidence ev s e p` is the not-at-issue proposition of the evidential `e` ((40b), (42b)),
that `s` has evidence for `p` from a source `e` covers, where `ev s π p` is the set of worlds in
which `s` has evidence of kind `π` for `p`. For *-rka* this is direct perceptual evidence and for
*-shka* reportative evidence. -/
def evidence (ev : A → Evidential.Parameter → Set W → Set W) (s : A) (e : Evidential)
    (p : Set W) : Set W :=
  {w | ∃ π ∈ e.covers, w ∈ ev s π p}

/-- `withEvidential ev s e S` applies the evidential `e` to the sentence `S` by rule I ((40a),
(42a)), keeping the scope at issue and adding the speaker's evidence for it not at issue. -/
def withEvidential (ev : A → Evidential.Parameter → Set W → Set W) (s : A) (e : Evidential)
    (S : TwoDim W (Set W)) : TwoDim W (Set W) :=
  S >>= fun p ↦ ⟨p, (· ∈ evidence ev s e p)⟩

variable (ev : A → Evidential.Parameter → Set W → Set W) (s : A) (e : Evidential)

@[simp] theorem withEvidential_atIssue (S : TwoDim W (Set W)) :
    (withEvidential ev s e S).atIssue = S.atIssue := rfl

@[simp] theorem ofPred_notAtIssue_withEvidential_pure (p : Set W) :
    Set.ofPred (withEvidential ev s e (pure p)).notAtIssue = evidence ev s e p := by
  ext; simp [withEvidential]

/-! ### Moves and contexts -/

/-- A move on the conversational record has a speaker, the propositions the speaker commits to,
and the propositions by means of which it addresses the question under discussion. -/
structure Move (A W : Type*) where
  /-- The speaker. -/
  speaker : A
  /-- The propositions the speaker commits to. -/
  commitments : Set (Set W)
  /-- The propositions by means of which the move addresses the question under discussion. -/
  addressers : Set (Set W)

namespace Move

/-- The operator `assert` (39) commits the speaker to the scope, by means of which she addresses
the question under discussion, and to the not-at-issue content. -/
def assert (s : A) (S : TwoDim W (Set W)) : Move A W where
  speaker := s
  commitments := {S.atIssue, Set.ofPred S.notAtIssue}
  addressers := {S.atIssue}

/-- The operator `present` (41) brings the scope to the addressee's attention, addresses the
question under discussion by means of it or its negation, and commits the speaker only to the
not-at-issue content. -/
def present (s : A) (S : TwoDim W (Set W)) : Move A W where
  speaker := s
  commitments := {Set.ofPred S.notAtIssue}
  addressers := {S.atIssue, S.atIssueᶜ}

/-- A question biased toward `q` steers the exchange toward adopting `q`, and so addresses the
question under discussion by means of it (§4.2). -/
def biasedQuestion (s : A) (q : Set W) : Move A W := ⟨s, ∅, {q}⟩

/-- A declarative with a direct evidential is asserted and one with a reportative is presented
((40c), (42c)), and `declare s e S` is the move of a declarative with evidential `e`, if the paper
analyzes `e`. -/
def declare (s : A) (e : Evidential) (S : TwoDim W (Set W)) : Option (Move A W) :=
  match e.evidenceType? with
  | some .attested => some (assert s S)
  | some .reported => some (present s S)
  | _ => none

theorem declare_of_isDirect {e : Evidential} (he : e.IsDirect) (S : TwoDim W (Set W)) :
    declare s e S = some (assert s S) := by
  simp [declare, Evidential.evidenceType?_eq_some_iff.2 he]

theorem declare_of_isReportative {e : Evidential} (he : e.IsReportative)
    (S : TwoDim W (Set W)) : declare s e S = some (present s S) := by
  simp [declare, Evidential.evidenceType?_eq_some_iff.2 he]

@[simp] theorem declare_rka (S : TwoDim W (Set W)) : declare s rka S = some (assert s S) :=
  declare_of_isDirect s (by decide) S

@[simp] theorem declare_shka (S : TwoDim W (Set W)) : declare s shka S = some (present s S) :=
  declare_of_isReportative s (by decide) S

-- The paper does not analyze the inferential *-shi* (footnote 6).
example (S : TwoDim W (Set W)) : declare s shi S = none := rfl

end Move

/-- A context of utterance consists of the moves on record and the question under discussion. -/
structure Context (A W : Type*) where
  /-- The moves on record. -/
  moves : Set (Move A W)
  /-- The question under discussion. -/
  qud : Question W

namespace Context

/-- `c.update m` puts the move `m` on record. -/
def update (c : Context A W) (m : Move A W) : Context A W := ⟨insert m c.moves, c.qud⟩

/-- `c.declare s e S` puts on record the move of a declarative with evidential `e`, if the paper
analyzes `e`. -/
def declare (c : Context A W) (s : A) (e : Evidential) (S : TwoDim W (Set W)) : Context A W :=
  ((Move.declare s e S).map c.update).getD c

/-- Asking a question that addresses no prior one makes it the question under discussion. -/
def ask (c : Context A W) (Q : Question W) : Context A W := ⟨c.moves, Q⟩

/-- The commitment state of the record commits the speaker of each move to each of its
commitments. -/
def commitments (c : Context A W) : Commitment.State A W :=
  {k | ∃ m ∈ c.moves, ∃ p ∈ m.commitments, k = Commitment.commit m.speaker p}

/-- `c.contextSetOf s` is the set of worlds compatible with the commitments of `s`. -/
def contextSetOf (c : Context A W) (s : A) : Set W :=
  Commitment.contextSet (Commitment.ofCommitter c.commitments s)

theorem mem_contextSetOf {c : Context A W} {s : A} {w : W} :
    w ∈ c.contextSetOf s ↔ ∀ m ∈ c.moves, m.speaker = s → ∀ p ∈ m.commitments, w ∈ p := by
  simp only [contextSetOf, Commitment.contextSet, Commitment.contents, Commitment.ofCommitter,
    commitments, Set.mem_sInter, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · intro h m hm hs p hp
    exact h p ⟨_, ⟨⟨⟨m, hm, p, hp, rfl⟩, hs⟩, rfl⟩, rfl⟩
  · rintro h _ ⟨_, ⟨⟨⟨m, hm, p, hp, rfl⟩, hs⟩, -⟩, rfl⟩
    exact h m hm hs p hp

end Context

/-- A proposition is highlighted (38) when a move on record addresses the question under
discussion by means of it and it partially answers that question. -/
def Highlighted (c : Context A W) (q : Set W) : Prop :=
  (∃ m ∈ c.moves, q ∈ m.addressers) ∧ c.qud.PartiallyAnsweredBy q

/-- The presupposition of *=mi* (37) holds when some alternative to the scope `p` is highlighted
and, exhaustified relative to the alternatives, entails `¬p`. Where defined, *=mi* is the
identity on its argument. -/
def MiDefined (c : Context A W) (ALT : Set (Set W)) (p : Set W) : Prop :=
  ∃ q ∈ ALT, Highlighted c q ∧ exhIE ALT q ⊆ pᶜ

variable {c : Context A W} {ALT : Set (Set W)} {p q : Set W}

/-- The witness of (37) differs from the scope, as the paper's prose requires, whenever its
exhaustification is consistent. -/
theorem ne_of_exhIE_subset_compl (h : exhIE ALT q ⊆ pᶜ) (hne : (exhIE ALT q).Nonempty) :
    q ≠ p := by
  rintro rfl
  obtain ⟨w, hw⟩ := hne
  exact h hw (Exhaustification.exhIE_subset ALT q hw)

/-- When nothing on record addresses the question under discussion, *=mi* is undefined ((7), (28),
(8), (29)). -/
theorem not_miDefined_of_addressers (h : ∀ m ∈ c.moves, m.addressers = ∅) :
    ¬ MiDefined c ALT p := by
  rintro ⟨q, -, ⟨⟨m, hm, hq⟩, -⟩, -⟩
  simp [h m hm] at hq

/-- For clausal *=mi* the alternatives are all propositions ((44d), (51d)), exhaustification is
vacuous, and (37) asks for a highlighted proposition entailing `¬p`. -/
theorem miDefined_univ_iff : MiDefined c Set.univ p ↔ ∃ q, Highlighted c q ∧ q ⊆ pᶜ := by
  simp [MiDefined, Exhaustification.exhIE_univ]

/-- A highlighted `¬p` licenses clausal *=mi* on `p` ((43), (44)). -/
theorem miDefined_of_highlighted_compl (h : Highlighted c pᶜ) : MiDefined c Set.univ p :=
  miDefined_univ_iff.2 ⟨pᶜ, h, subset_rfl⟩

theorem highlighted_update_iff {m : Move A W} :
    Highlighted (c.update m) q ↔ (q ∈ m.addressers ∨ ∃ m' ∈ c.moves, q ∈ m'.addressers) ∧
      c.qud.PartiallyAnsweredBy q := by
  simp [Highlighted, Context.update]

/-- Presenting `p` licenses clausal *=mi* on `p` ((48), (50), (51)), wherever `¬p` addresses the
question under discussion. -/
theorem miDefined_update_present (S : TwoDim W (Set W))
    (h : c.qud.PartiallyAnsweredBy S.atIssueᶜ) :
    MiDefined (c.update (.present s S)) Set.univ S.atIssue :=
  miDefined_of_highlighted_compl (highlighted_update_iff.2 ⟨.inl (by simp [Move.present]), h⟩)

/-- Asserting a consistent `p` adds nothing that licenses clausal *=mi* on `p` ((47), (49)). -/
theorem miDefined_update_assert_iff (S : TwoDim W (Set W)) (hp : S.atIssue.Nonempty) :
    MiDefined (c.update (.assert s S)) Set.univ S.atIssue ↔ MiDefined c Set.univ S.atIssue := by
  simp only [miDefined_univ_iff, highlighted_update_iff, Move.assert, Set.mem_singleton_iff]
  constructor
  · rintro ⟨q, ⟨rfl | hq, hqud⟩, hsub⟩
    · obtain ⟨w, hw⟩ := hp
      exact absurd hw (hsub hw)
    · exact ⟨q, ⟨hq, hqud⟩, hsub⟩
  · rintro ⟨q, ⟨hq, hqud⟩, hsub⟩
    exact ⟨q, ⟨.inr hq, hqud⟩, hsub⟩

/-- A highlighted alternative that innocently excludes the scope licenses *=mi* ((45), (46)). -/
theorem miDefined_of_isInnocentlyExcludable (hq : q ∈ ALT) (hh : Highlighted c q)
    (h : IsInnocentlyExcludable ALT q p) : MiDefined c ALT p :=
  ⟨q, hq, hh, h.exhIE_subset_compl⟩

/-- When no highlighted proposition is among the alternatives, *=mi* is undefined, as in the
corrections (27c) and (27d). -/
theorem not_miDefined_of_disjoint (h : ∀ q, Highlighted c q → q ∉ ALT) :
    ¬ MiDefined c ALT p := by
  rintro ⟨q, hq, hh, -⟩
  exact h q hh hq

/-! ### Commitments -/

theorem contextSetOf_eq_empty {s : A} {m m' : Move A W} (hm : m ∈ c.moves) (hm' : m' ∈ c.moves)
    (hs : m.speaker = s) (hs' : m'.speaker = s) (hp : p ∈ m.commitments)
    (hp' : pᶜ ∈ m'.commitments) : c.contextSetOf s = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hw ↦
    Context.mem_contextSetOf.1 hw m' hm' hs' _ hp' (Context.mem_contextSetOf.1 hw m hm hs p hp)

theorem contextSetOf_update {m : Move A W} {w : W} :
    w ∈ (c.update m).contextSetOf s ↔
      (m.speaker = s → ∀ p ∈ m.commitments, w ∈ p) ∧ w ∈ c.contextSetOf s := by
  simp [Context.mem_contextSetOf, Context.update]

variable (S : TwoDim W (Set W))

/-- Asserting `p` and then `¬p` is inconsistent (18a), as is the *-rka* counterpart of footnote 9.
-/
theorem contextSetOf_assert_assert_compl :
    ((c.update (.assert s S)).update (.assert s (pure S.atIssueᶜ))).contextSetOf s = ∅ :=
  contextSetOf_eq_empty (m := .assert s S) (m' := .assert s (pure S.atIssueᶜ)) (p := S.atIssue)
    (by simp [Context.update]) (by simp [Context.update]) rfl rfl (by simp [Move.assert])
    (by simp [Move.assert])

/-- Presenting `p` and then asserting `¬p` is consistent wherever the speaker's evidence for `p`
is compatible with `¬p` (19a). -/
theorem mem_contextSetOf_present_assert_compl {w : W} (hc : w ∈ c.contextSetOf s)
    (hN : S.notAtIssue w) (hA : w ∉ S.atIssue) :
    w ∈ ((c.update (.present s S)).update (.assert s (pure S.atIssueᶜ))).contextSetOf s := by
  simp [contextSetOf_update, Move.assert, Move.present, hc, hN, hA]

/-- Denying the evidence a declarative commits to is inconsistent, after an assertion (18b) or a
presentation (19b). -/
theorem contextSetOf_update_assert_compl_notAtIssue {m : Move A W} (hs : m.speaker = s)
    (hm : Set.ofPred S.notAtIssue ∈ m.commitments) :
    ((c.update m).update (.assert s (pure (Set.ofPred S.notAtIssue)ᶜ))).contextSetOf s = ∅ :=
  contextSetOf_eq_empty (m' := .assert s (pure (Set.ofPred S.notAtIssue)ᶜ))
    (by simp [Context.update]) (by simp [Context.update]) hs rfl hm (by simp [Move.assert])

/-- Confirming a presented `p` with *=mi* asserts it, so denying it afterwards is inconsistent
(footnote 10). -/
theorem contextSetOf_present_assert_assert_compl :
    (((c.update (.present s S)).update (.assert s (pure S.atIssue))).update
      (.assert s (pure S.atIssueᶜ))).contextSetOf s = ∅ :=
  contextSetOf_assert_assert_compl s (pure S.atIssue)

/-! ### The examples

The examples are evaluated in a model whose worlds are sets of events: an event fixes a value at
each constituent site of the scope sentence, a world is the set of events that happened, and the
question under discussion asks which event happened. The scope is that the scope event happened,
and a correction asserts that its variant at the contrasted site did. The propositions in play
are the scope, its negation and the variants, named by `Answer`; `miDefined_iff` reduces the
presupposition of *=mi* in each example's context to a check on these names, and
`judgment_eq_acceptable_iff_miDefined` compares it with the paper's judgments. -/

open Discourse (Role)

/-- A `Site` is a constituent that *=mi* marks or a correction contrasts in the examples. -/
inductive Site
  | subject | object | goal | verbPhrase | verb | modifier
  deriving DecidableEq

/-- An event fixes a value at each site. -/
abbrev Event := Site → Bool

/-- `happened e` is the proposition that the event `e` happened. -/
def happened (e : Event) : Set (Set Event) := {w | e ∈ w}

/-- `vary k b` is the scope event with the value at `k` set to `b`, the scope event itself when
`b` is `true`. -/
def vary (k : Site) (b : Bool) : Event := Function.update (fun _ ↦ true) k b

/-- An `Answer` names a proposition in play, the scope, its negation, or the variant at a
site. -/
inductive Answer
  | scope | negation | variant (k : Site)
  deriving DecidableEq

/-- `a.prop` is the proposition the answer `a` names. -/
def Answer.prop : Answer → Set (Set Event)
  | scope => happened fun _ ↦ true
  | negation => (happened fun _ ↦ true)ᶜ
  | variant k => happened (vary k false)

/-- The question under discussion of the model asks which event happened. -/
def whichEvent : Question (Set Event) := Question.which Set.univ happened

/-- The alternatives of *=mi* on a clause are all propositions ((44d), (51d)), and those of *=mi*
on the constituent at a site are the variants at that site ((46d)). -/
def alternatives : Option Site → Set (Set (Set Event))
  | none => Set.univ
  | some k => Set.range fun b ↦ happened (vary k b)

/-- The model's speaker has evidence of every kind for everything. -/
def evModel (_ : Role) (_ : Evidential.Parameter) (_ : Set (Set Event)) : Set (Set Event) :=
  Set.univ

/-- `sentence s e p` is the declarative of `s` with evidential `e` and scope `p`. -/
def sentence (s : Role) (e : Evidential) (p : Set (Set Event)) :
    TwoDim (Set Event) (Set (Set Event)) :=
  withEvidential evModel s e (pure p)

/-- A `Prior` is the discourse before a *=mi* sentence as the paper describes its examples. It is
empty, an assertion of the negated scope (6), a debate between the scope and its negation ((9),
(11)), a declarative of the scope with *-rka* (20) or *-shka* (21), or a correction asserting a
variant ((22)–(30)). -/
inductive Prior
  | none | assertedNegation | debate | direct | reportative | correction (k : Site)
  deriving DecidableEq

/-- An `Asked` is the question asked right before the *=mi* sentence, an unbiased polar question
((8), (9)), a constituent question (29), or a question biased toward the negation (10) or toward
the scope (11). -/
inductive Asked
  | polar | constituent | negativeBiased | positiveBiased
  deriving DecidableEq

/-- `p.context` is the context the prior discourse `p` sets up. -/
def Prior.context : Prior → Context Role (Set Event)
  | none => ⟨∅, whichEvent⟩
  | assertedNegation => (⟨∅, whichEvent⟩ : Context _ _).declare .addressee rka
      (sentence .addressee rka Answer.negation.prop)
  | debate => ((⟨∅, whichEvent⟩ : Context _ _).update (.assert .addressee
      (pure Answer.negation.prop))).update (.assert .speaker (pure Answer.scope.prop))
  | direct => (⟨∅, whichEvent⟩ : Context _ _).declare .speaker rka
      (sentence .speaker rka Answer.scope.prop)
  | reportative => (⟨∅, whichEvent⟩ : Context _ _).declare .speaker shka
      (sentence .speaker shka Answer.scope.prop)
  | correction k => (⟨∅, whichEvent⟩ : Context _ _).declare .addressee rka
      (sentence .addressee rka (Answer.variant k).prop)

/-- `a.context c` asks the question `a` in the context `c`. -/
def Asked.context : Asked → Context Role (Set Event) → Context Role (Set Event)
  | polar, c => c.ask (.polar Answer.scope.prop)
  | constituent, c => c.ask whichEvent
  | negativeBiased, c => (c.ask (.polar Answer.scope.prop)).update
      (.biasedQuestion .addressee Answer.negation.prop)
  | positiveBiased, c => (c.ask (.polar Answer.scope.prop)).update
      (.biasedQuestion .addressee Answer.scope.prop)

/-- A *=mi* example records its prior discourse, the question asked, the constituent *=mi* marks,
and the polarity of its scope. -/
structure MiExample where
  /-- The discourse before the *=mi* sentence. -/
  prior : Prior
  /-- The question asked right before it, if any. -/
  asked : Option Asked
  /-- The constituent *=mi* marks, or none for the clause. -/
  focus : Option Site
  /-- The polarity of the scope. -/
  polarity : Polarity
  deriving DecidableEq

namespace MiExample

variable (r : MiExample)

/-- `r.context` is the context of the *=mi* sentence. -/
def context : Context Role (Set Event) := (r.asked.map Asked.context).getD id r.prior.context

/-- `r.scope` names the scope of the *=mi* sentence. -/
def scope : Answer := match r.polarity with
  | .positive => .scope
  | .negative => .negation

/-- `r.addressers` lists the answers by means of which the moves on record address the question
under discussion. -/
def addressers : List Answer :=
  (match r.prior with
    | .none => []
    | .assertedNegation => [.negation]
    | .debate => [.negation, .scope]
    | .direct => [.scope]
    | .reportative => [.scope, .negation]
    | .correction k => [.variant k]) ++
  (match r.asked with
    | some .negativeBiased => [.negation]
    | some .positiveBiased => [.scope]
    | _ => [])

/-- Every answer in play addresses the question under discussion, except that a variant does not
address a polar question about the scope. -/
def Addresses : Answer → Prop
  | .variant _ => r.asked = none ∨ r.asked = some .constituent
  | _ => True

/-- An answer fits the *=mi* sentence when it is one of its alternatives and its exhaustification
entails the negated scope, as `fits_iff` shows. -/
def Fits (a : Answer) : Prop := match r.focus, r.polarity with
  | none, .positive => a = .negation
  | none, .negative => a = .scope
  | some k, .positive => a = .variant k
  | some _, .negative => a = .scope

/-- The analysis licenses the *=mi* sentence when some answer on record addresses the question
under discussion and fits it. -/
def Licensed : Prop := ∃ a ∈ r.addressers, r.Addresses a ∧ r.Fits a

instance (a : Answer) : Decidable (r.Addresses a) := by
  cases a <;> unfold Addresses <;> infer_instance

instance (a : Answer) : Decidable (r.Fits a) := by
  unfold Fits; split <;> infer_instance

instance : Decidable r.Licensed := by
  unfold Licensed; infer_instance

end MiExample

/-! #### The model's propositions -/

theorem happened_subset_happened {e e' : Event} : happened e ⊆ happened e' ↔ e = e' := by
  refine ⟨fun h ↦ (Set.mem_singleton_iff.1 (h (Set.mem_singleton e))).symm, fun h ↦ h ▸ subset_rfl⟩

theorem vary_true (k : Site) : vary k true = fun _ ↦ true := Function.update_eq_self k _

theorem vary_false_ne (k : Site) : vary k false ≠ fun _ ↦ true :=
  fun h ↦ by simpa [vary] using congrFun h k

theorem vary_false_inj {j k : Site} : vary j false = vary k false ↔ j = k := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  by_contra hjk
  simpa [vary, hjk] using congrFun h j

theorem empty_mem_negation : ∅ ∈ Answer.negation.prop :=
  Set.notMem_empty (fun _ ↦ true : Event)

theorem empty_notMem_happened (e : Event) : ∅ ∉ happened e := Set.notMem_empty e

theorem mem_alternatives_iff {a : Answer} {k : Site} :
    a.prop ∈ alternatives (some k) ↔ a = .scope ∨ a = .variant k := by
  refine ⟨?_, ?_⟩
  · rintro ⟨b, hb⟩
    cases a with
    | scope =>
      exact .inl rfl
    | negation =>
      exact absurd (hb ▸ empty_mem_negation) (empty_notMem_happened _)
    | variant j =>
      have h := happened_subset_happened.1 hb.subset
      cases b
      · exact .inr (congrArg Answer.variant (vary_false_inj.1 h.symm))
      · exact (vary_false_ne j ((vary_true k).symm.trans h).symm).elim
  · rintro (rfl | rfl)
    · exact ⟨true, by simp [Answer.prop, vary_true]⟩
    · exact ⟨false, rfl⟩

theorem happened_mem_alt_whichEvent (e : Event) : happened e ∈ whichEvent.alt :=
  Question.mem_alt_which_of_maximal e trivial ⟨{e}, Set.mem_singleton e⟩
    fun _ _ h ↦ by rw [happened_subset_happened.1 h]

theorem partiallyAnsweredBy_whichEvent (a : Answer) : whichEvent.PartiallyAnsweredBy a.prop := by
  cases a with
  | scope => exact Question.partiallyAnsweredBy_of_mem_alt (happened_mem_alt_whichEvent _)
  | negation => exact Question.partiallyAnsweredBy_compl_of_mem_alt (happened_mem_alt_whichEvent _)
  | variant k => exact Question.partiallyAnsweredBy_of_mem_alt (happened_mem_alt_whichEvent _)

theorem partiallyAnsweredBy_polar_iff (a : Answer) :
    (Question.polar Answer.scope.prop).PartiallyAnsweredBy a.prop ↔ ∀ k, a ≠ .variant k := by
  have hne : Answer.scope.prop ≠ ∅ := Set.nonempty_iff_ne_empty.1 ⟨{fun _ ↦ true}, rfl⟩
  have hnu : Answer.scope.prop ≠ Set.univ := fun h ↦
    empty_notMem_happened (fun _ ↦ true) (show ∅ ∈ Answer.scope.prop by rw [h]; trivial)
  rw [Question.partiallyAnsweredBy_polar_iff hne hnu]
  cases a with
  | scope => simp
  | negation => simp [Answer.prop]
  | variant k =>
    simp only [ne_eq, Answer.variant.injEq, forall_eq', iff_false, not_or]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · exact vary_false_ne k (Set.mem_singleton_iff.1 (h (Set.mem_singleton _)))
    · exact h (show _ ∈ ({vary k false, fun _ ↦ true} : Set Event) from .inl rfl) (.inr rfl)

theorem finite_alternatives (k : Site) : (alternatives (some k)).Finite := Set.finite_range _

theorem forall_mem_alternatives {k : Site} {P : Set (Set Event) → Prop} :
    (∀ a ∈ alternatives (some k), P a) ↔ P Answer.scope.prop ∧ P (Answer.variant k).prop := by
  simp [alternatives, Answer.prop, vary_true, and_comm]

theorem singleton_mem_happened (e : Event) : {e} ∈ happened e := Set.mem_singleton e

theorem exhIE_variant_subset (k : Site) :
    exhIE (alternatives (some k)) (Answer.variant k).prop ⊆ Answer.scope.propᶜ :=
  IsInnocentlyExcludable.exhIE_subset_compl
    (.of_forall_subset_or_notMem (w := {vary k false}) (mem_alternatives_iff.2 (.inl rfl))
      (singleton_mem_happened _) (fun h ↦ vary_false_ne k (Set.mem_singleton_iff.1 h).symm)
      (forall_mem_alternatives.2 ⟨.inr fun h ↦ vary_false_ne k (Set.mem_singleton_iff.1 h).symm,
        .inl subset_rfl⟩))

theorem singleton_mem_exhIE_variant (k : Site) :
    {vary k false} ∈ exhIE (alternatives (some k)) (Answer.variant k).prop :=
  Exhaustification.mem_exhIE_of_forall_subset_or_notMem _ _ (finite_alternatives k)
    (singleton_mem_happened _)
    (forall_mem_alternatives.2 ⟨.inr fun h ↦ vary_false_ne k (Set.mem_singleton_iff.1 h).symm,
      .inl subset_rfl⟩)

theorem singleton_mem_exhIE_scope (k : Site) :
    {fun _ ↦ true} ∈ exhIE (alternatives (some k)) Answer.scope.prop :=
  Exhaustification.mem_exhIE_of_forall_subset_or_notMem _ _ (finite_alternatives k)
    (singleton_mem_happened _)
    (forall_mem_alternatives.2
      ⟨.inl subset_rfl, .inr fun h ↦ vary_false_ne k (Set.mem_singleton_iff.1 h)⟩)

theorem prop_negation : Answer.negation.prop = Answer.scope.propᶜ := rfl

theorem compl_negation : Answer.negation.propᶜ = Answer.scope.prop := compl_compl _

theorem scope_ne_empty : Answer.scope.prop ≠ ∅ :=
  Set.nonempty_iff_ne_empty.1 ⟨_, singleton_mem_happened _⟩

theorem variant_not_subset_compl (k : Site) : ¬ (Answer.variant k).prop ⊆ Answer.scope.propᶜ :=
  fun h ↦ h (a := {vary k false, fun _ ↦ true}) (Set.mem_insert _ _)
    (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem negation_not_subset_scope : ¬ Answer.negation.prop ⊆ Answer.scope.prop :=
  fun h ↦ empty_notMem_happened _ (h empty_mem_negation)

theorem variant_not_subset_scope (k : Site) : ¬ (Answer.variant k).prop ⊆ Answer.scope.prop :=
  fun h ↦ vary_false_ne k (Set.mem_singleton_iff.1 (h (singleton_mem_happened _))).symm

namespace MiExample

variable (r : MiExample)

theorem fits_iff (a : Answer) :
    (a.prop ∈ alternatives r.focus ∧ exhIE (alternatives r.focus) a.prop ⊆ r.scope.propᶜ) ↔
      r.Fits a := by
  obtain ⟨prior, asked, focus, polarity⟩ := r
  rcases focus with _ | k <;> cases polarity <;>
    simp only [Fits, scope, alternatives, Set.mem_univ, true_and, Exhaustification.exhIE_univ,
      compl_negation]
  · cases a <;> simp [scope_ne_empty, variant_not_subset_compl, prop_negation]
  · cases a <;> simp [negation_not_subset_scope, variant_not_subset_scope]
  · rw [← alternatives, mem_alternatives_iff]
    cases a with
    | scope => exact iff_of_false (fun h ↦ h.2 (singleton_mem_exhIE_scope k)
        (Exhaustification.exhIE_subset _ _ (singleton_mem_exhIE_scope k))) (by simp)
    | negation => simp
    | variant j =>
      simp only [reduceCtorEq, false_or, Answer.variant.injEq]
      exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, h ▸ exhIE_variant_subset k⟩⟩
  · rw [← alternatives, mem_alternatives_iff]
    cases a with
    | scope => exact iff_of_true ⟨.inl rfl, Exhaustification.exhIE_subset _ _⟩ rfl
    | negation => simp
    | variant j =>
      refine iff_of_false ?_ (by simp)
      rintro ⟨h | h, hsub⟩
      · cases h
      · obtain rfl := Answer.variant.inj h
        have := hsub (singleton_mem_exhIE_variant j)
        exact vary_false_ne j (Set.mem_singleton_iff.1 this).symm

theorem exists_mem_moves_iff (q : Set (Set Event)) :
    (∃ m ∈ r.context.moves, q ∈ m.addressers) ↔ ∃ a ∈ r.addressers, a.prop = q := by
  obtain ⟨prior, asked, focus, polarity⟩ := r
  cases prior <;> rcases asked with _ | _ | _ | _ | _ <;>
    simp [context, Prior.context, Asked.context, Context.declare, Context.update, Context.ask,
      Move.assert, Move.present, Move.biasedQuestion, addressers, sentence, eq_comm,
      prop_negation] <;> tauto

theorem qud_context : r.context.qud = if r.asked = none ∨ r.asked = some .constituent then
    whichEvent else .polar Answer.scope.prop := by
  obtain ⟨prior, asked, focus, polarity⟩ := r
  cases prior <;> rcases asked with _ | _ | _ | _ | _ <;>
    simp [context, Prior.context, Asked.context, Context.declare, Context.update, Context.ask]

theorem highlighted_context_iff (q : Set (Set Event)) :
    Highlighted r.context q ↔ ∃ a ∈ r.addressers, r.Addresses a ∧ a.prop = q := by
  simp only [Highlighted, exists_mem_moves_iff, qud_context]
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, hq⟩
    refine ⟨a, ha, ?_, rfl⟩
    split_ifs at hq with h
    · cases a <;> simp [Addresses, h]
    · cases a <;> simp_all [Addresses, partiallyAnsweredBy_polar_iff]
  · rintro ⟨a, ha, hadd, rfl⟩
    refine ⟨⟨a, ha, rfl⟩, ?_⟩
    split_ifs with h
    · exact partiallyAnsweredBy_whichEvent a
    · rw [partiallyAnsweredBy_polar_iff]
      rintro k rfl
      exact h hadd

theorem miDefined_iff :
    MiDefined r.context (alternatives r.focus) r.scope.prop ↔ r.Licensed := by
  simp only [MiDefined, highlighted_context_iff, Licensed]
  constructor
  · rintro ⟨_, hq, ⟨a, ha, hadd, rfl⟩, hexh⟩
    exact ⟨a, ha, hadd, (r.fits_iff a).1 ⟨hq, hexh⟩⟩
  · rintro ⟨a, ha, hadd, hfit⟩
    obtain ⟨hq, hexh⟩ := (r.fits_iff a).2 hfit
    exact ⟨a.prop, hq, ⟨a, ha, hadd, rfl⟩, hexh⟩

end MiExample

/-- The examples name sites by their constructors. -/
def siteLabels : List (String × Site) :=
  [("subject", .subject), ("object", .object), ("goal", .goal), ("verbPhrase", .verbPhrase),
    ("verb", .verb), ("modifier", .modifier)]

/-- The examples name the constituent *=mi* marks, the clause or a site. -/
def focusLabels : List (String × Option Site) :=
  ("clause", none) :: siteLabels.map fun (l, k) ↦ (l, some k)

/-- The examples name prior discourses other than a correction by their constructors. -/
def priorLabels : List (String × Prior) :=
  [("none", .none), ("assertedNegation", .assertedNegation), ("debate", .debate),
    ("directEvidential", .direct), ("reportativeEvidential", .reportative)]

/-- The examples name the questions asked by their constructors. -/
def askedLabels : List (String × Asked) :=
  [("polar", .polar), ("constituent", .constituent), ("negativeBiased", .negativeBiased),
    ("positiveBiased", .positiveBiased)]

/-- The examples name the polarity of a negative scope. -/
def polarityLabels : List (String × Polarity) := [("negative", .negative)]

namespace MiExample

/-- `ofDatum? x` is the *=mi* example the row `x` records, if it records one, a correction
naming its contrasted site. -/
def ofDatum? (x : Datum) : Option MiExample := do
  let prior ← if x.feature? "prior" = some "correction" then
      (x.parse? "contrast" siteLabels).map .correction
    else x.parse? "prior" priorLabels
  let focus ← x.parse? "focus" focusLabels
  pure ⟨prior, x.parse? "question" askedLabels, focus,
    (x.parse? "polarity" polarityLabels).getD .positive⟩

end MiExample

/-- Every *=mi* example is acceptable exactly when its presupposition holds in its context. -/
theorem judgment_eq_acceptable_iff_miDefined :
    ∀ x ∈ Examples.all, ∀ r ∈ MiExample.ofDatum? x,
      (x.judgment = .acceptable ↔ MiDefined r.context (alternatives r.focus) r.scope.prop) := by
  have h : ∀ x ∈ Examples.all, ∀ r ∈ MiExample.ofDatum? x,
      (x.judgment = .acceptable ↔ r.Licensed) := by
    decide +kernel
  intro x hx r hr
  rw [h x hx r hr, r.miDefined_iff]

/-- A `Continuation` is how the speaker continues her declarative in a commitment test. She denies
its scope ((18a), (19a)), denies her evidence ((18b), (19b)), or confirms the scope with *=mi*
and then denies it (footnote 10). -/
inductive Continuation
  | deniesScope | deniesEvidence | confirmsThenDeniesScope
  deriving DecidableEq

/-- A commitment test is a declarative of the scope with an evidential, continued by its
speaker. -/
structure CommitmentExample where
  /-- The evidential of the declarative. -/
  evidential : Evidential
  /-- How the speaker continues. -/
  continuation : Continuation

namespace CommitmentExample

variable (r : CommitmentExample)

/-- `r.context` is the record after the declarative and its continuation. -/
def context : Context Role (Set Event) :=
  let c := (⟨∅, whichEvent⟩ : Context _ _).declare .speaker r.evidential
    (sentence .speaker r.evidential Answer.scope.prop)
  match r.continuation with
  | .deniesScope => c.update (.assert .speaker (pure Answer.negation.prop))
  | .deniesEvidence => c.update
      (.assert .speaker (pure (evidence evModel .speaker r.evidential Answer.scope.prop)ᶜ))
  | .confirmsThenDeniesScope => (c.update (.assert .speaker (pure Answer.scope.prop))).update
      (.assert .speaker (pure Answer.negation.prop))

theorem nonempty_contextSetOf_iff (he : r.evidential.IsDirect ∨ r.evidential.IsReportative) :
    (r.context.contextSetOf .speaker).Nonempty ↔
      r.evidential.IsReportative ∧ r.continuation = .deniesScope := by
  obtain ⟨e, k⟩ := r
  rcases he with he | he
  · have hne : ¬ e.IsReportative := fun h ↦ by cases he.eq h
    refine iff_of_false ?_ (by simp [hne])
    rw [Set.not_nonempty_iff_eq_empty]
    cases k <;> simp only [context, Context.declare, Move.declare_of_isDirect _ he, Option.map_some,
      Option.getD_some]
    · exact contextSetOf_assert_assert_compl _ _
    · rw [← ofPred_notAtIssue_withEvidential_pure evModel]
      exact contextSetOf_update_assert_compl_notAtIssue _ _ rfl
        (by simp [Move.assert, sentence, ofPred_notAtIssue_withEvidential_pure])
    · exact contextSetOf_eq_empty (m := .assert .speaker (pure Answer.scope.prop))
        (m' := .assert .speaker (pure Answer.negation.prop)) (p := Answer.scope.prop)
        (by simp [Context.update]) (by simp [Context.update]) rfl rfl (by simp [Move.assert])
        (by simp [Move.assert, prop_negation])
  · cases k <;> simp only [context, Context.declare, Move.declare_of_isReportative _ he,
      Option.map_some, Option.getD_some, he, true_and, reduceCtorEq, iff_false, iff_true,
      Set.not_nonempty_iff_eq_empty]
    · refine ⟨∅, mem_contextSetOf_present_assert_compl _ _ (by simp [Context.mem_contextSetOf])
        ?_ (empty_notMem_happened _)⟩
      simpa [sentence, withEvidential, evidence, evModel] using he.1.exists_mem
    · rw [← ofPred_notAtIssue_withEvidential_pure evModel]
      exact contextSetOf_update_assert_compl_notAtIssue _ _ rfl
        (by simp [Move.present, sentence, ofPred_notAtIssue_withEvidential_pure])
    · exact contextSetOf_present_assert_assert_compl _ _

/-- The examples name the evidentials of the commitment tests by their evidence type. -/
def evidentialLabels : List (String × Evidential) := [("direct", rka), ("reportative", shka)]

/-- The examples name the continuations by their constructors. -/
def continuationLabels : List (String × Continuation) :=
  [("deniesScope", .deniesScope), ("deniesEvidence", .deniesEvidence),
    ("confirmsThenDeniesScope", .confirmsThenDeniesScope)]

/-- `ofDatum? x` is the commitment test the row `x` records, if it records one. -/
def ofDatum? (x : Datum) : Option CommitmentExample :=
  return ⟨← x.parse? "evidential" evidentialLabels, ← x.parse? "continuation" continuationLabels⟩

end CommitmentExample

/-- Every commitment test is acceptable exactly when its speaker's commitments are consistent
((18), (19), footnote 10). -/
theorem judgment_eq_acceptable_iff_nonempty :
    ∀ x ∈ Examples.all, ∀ r ∈ CommitmentExample.ofDatum? x,
      (x.judgment = .acceptable ↔ (r.context.contextSetOf .speaker).Nonempty) := by
  have h : ∀ x ∈ Examples.all, ∀ r ∈ CommitmentExample.ofDatum? x,
      (r.evidential.IsDirect ∨ r.evidential.IsReportative) ∧
        (x.judgment = .acceptable ↔
          r.evidential.IsReportative ∧ r.continuation = .deniesScope) := by
    decide +kernel
  intro x hx r hr
  rw [(h x hx r hr).2, r.nonempty_contextSetOf_iff (h x hx r hr).1]

-- Every example is read as a *=mi* example or as a commitment test.
example : ∀ x ∈ Examples.all,
    (MiExample.ofDatum? x).isSome ∨ (CommitmentExample.ofDatum? x).isSome := by
  decide +kernel

end MartinezVera2026
