module

public import Mathlib.Order.UpperLower.Closure
public import Linglib.Discourse.Commitment.Space
public import Linglib.Discourse.Commitment.Table
public import Linglib.Discourse.Role
public import Linglib.Pragmatics.DecisionTheoretic.Basic
public import Studies.BuringGunlogson2000

/-!
# Krifka (2015): Bias in Commitment Space Semantics

Krifka models a conversation as a commitment space, the current commitment state with the
continuations it projects, all of them coherent. A commitment state is a set of propositions,
among them the commitments `S⊢φ`, which are propositions in their own right, and an assertion
keeps the states that carry the speaker's commitment. A question keeps the root and proposes
continuations. A monopolar question proposes the addressee's commitment to `φ`, a bipolar question
that commitment or the one to `¬φ`, and a question with high negation the addressee's refusal to
commit to `φ`, the complement of `S⊢φ`; a question with low negation is a monopolar question about
`¬φ`. An answer is performed in the space the question left, so it lands on a state that also
carries what the question proposed, and an answer that no such state carries needs a prior
rejection, which returns to the space before the question. This is the bias of a question. A
matching question tag conjoins an assertion with the monopolar question of the same content, and
a reverse tag disjoins it with the monopolar question of the negation.

## Main statements

* `not_coherent_committed_compl`, `not_coherent_committed_committed_compl`: committing to `φ`
  while refusing to is incoherent, and so is committing to `φ` and to `¬φ`, which the paper
  stipulates and which follow here from commitments being propositions and consistent.
* `not_admits_monopolarQuestion_no`, `admits_bipolarQuestion_no`: *no* needs a prior rejection
  after a monopolar question and none after a bipolar one.
* `root_highNegationQuestion_update_no`, `not_admits_highNegationQuestion_yes`: after a question
  with high negation *no* is admitted and keeps the refusal, while *yes* needs a rejection.
* `root_reject_matchingTag_no`, `committed_speaker_mem_root_assert_assert`: rejecting an
  assertion with a matching tag removes the speaker's commitment, which a plain assertion keeps
  when the addressee contradicts it.
* `sInter_root_assert_raining`, `sInter_root_update_assert_raining`: an assertion adds the
  speaker's commitment to `φ` but not `φ`, which enters only with the second update (19).

## Implementation notes

* A commitment `S⊢φ` is the proposition `Commitment.committed O S φ` over an accessibility for
  each participant. Coherence is satisfiability of the state, with each participant's commitments
  consistent (`O S` serial), after Cohen and Krifka's requirement that commitments be consistent
  with each other. The initial space has every coherent state.
* The general statements carry the coherence of the states they reach as hypotheses. The model
  has indices that pair the weather with each participant's commitment set
  (`Commitment.Index`), where every combination of consistent commitments is realized and the
  hypotheses hold.
* Developments record the spaces passed through and not who acted, since no statement here
  depends on the actor of a stage.
* The licensing conditions behind the table of acceptable uses are stated on the evidence and
  are not derived from the spaces. Contextual evidence is the set of worlds it leaves open, which
  is the proposition, everything, or its complement, and under any prior on which the issue is
  live it has the relevance sign it is built from (`relevanceSign_evidence`).

## TODO

* After the second update of an assertion, contradicting it needs a rejection in the paper,
  which undoes only that update (22). The clash between `φ` and the addressee's commitment to
  `¬φ` needs a principle tying the common ground to commitments, which is not modelled, so
  contradiction is stated here after the first update only.
* The reaction *I don't know* is left out, since its clash with either answer is a fact about
  knowledge that coherence does not see.
* The paper prints the addressee's commitment to `φ` in the last stage of (28b); since *no*
  asserts the negation, it is the commitment to `¬φ` here.

## References

* [krifka-2015]
* [cohen-krifka-2014]
* [farkas-bruce-2010]
* [buring-gunlogson-2000]
* [merin-1999-relevance]
-/

@[expose] public section

namespace Krifka2015

open Commitment Space Question

/-! ### Questions as meta-speech acts -/

section Questions

variable {X : Type*} (C : Space (Set X)) {P : Set (Set X)} {k l p d : Set X}

/-- A question keeps the root and proposes the continuations that carry one of the acts in
`P`. -/
def question (P : Set (Set X)) : Space (Set X) := C.restrict (upperClosure P)

theorem mem_question : d ∈ question C P ↔ d = C.root ∨ d ∈ C ∧ ∃ p ∈ P, p ⊆ d := Iff.rfl

-- (27)
theorem question_singleton (p : Set X) : question C {p} = C.restrict (C.update p) := by
  rw [question, restrict_coe_update, upperClosure_singleton, UpperSet.coe_Ici]

-- (31), (34)
theorem coe_question_union (P Q : Set (Set X)) :
    (question C (P ∪ Q) : Set (Set X)) = ↑(question C P) ∪ ↑(question C Q) := by
  rw [question, upperClosure_union, UpperSet.coe_inf, coe_restrict_union]
  rfl

/-! ### Answers -/

-- (24), (28)
theorem question_update_of_mem (hp : p ∈ P) : (question C P).update p = C.update p :=
  C.update_restrict_of_subset fun _ hd ↦ ⟨p, hp, hd.2⟩

theorem question_update_of_forall (hk : ¬ k ⊆ C.root) (hp : p ∈ P)
    (h : ∀ q ∈ P, q ≠ p → ∀ d ∈ C, ¬ k ∪ q ⊆ d) :
    (question C P).update k = C.update (k ∪ p) :=
  update_congr _ <| Set.ext fun d ↦ by
    constructor
    · rintro ⟨rfl | ⟨hd, q, hq, hqd⟩, hkd⟩
      · exact absurd hkd hk
      · by_cases e : q = p
        · exact ⟨hd, Set.union_subset hkd (e ▸ hqd)⟩
        · exact absurd (Set.union_subset hkd hqd) (h q hq e d hd)
    · exact fun hd ↦ ⟨Or.inr ⟨hd.1, p, hp, Set.subset_union_right.trans hd.2⟩,
        Set.subset_union_left.trans hd.2⟩

/-- A space admits an act when the states that carry it have a least member, so that the update
is again a commitment space (2), (3). An act the space does not admit needs a prior
rejection. -/
def Admits (C : Space (Set X)) (k : Set X) : Prop := (C.update k).root ∈ C

theorem admits_question_iff_of_mem (hp : p ∈ P) : Admits (question C P) p ↔ Admits C p := by
  rw [Admits, question_update_of_mem C hp]
  exact ⟨fun h ↦ show _ ∈ C from h.elim (fun e ↦ e ▸ C.root_mem) And.left,
    fun h ↦ Or.inr ⟨h, p, hp, C.le_root_update p⟩⟩

theorem admits_question_iff_of_forall (hk : ¬ k ⊆ C.root) (hp : p ∈ P)
    (h : ∀ q ∈ P, q ≠ p → ∀ d ∈ C, ¬ k ∪ q ⊆ d) :
    Admits (question C P) k ↔ Admits C (k ∪ p) := by
  rw [Admits, question_update_of_forall C hk hp h]
  exact ⟨fun h' ↦ show _ ∈ C from h'.elim (fun e ↦ e ▸ C.root_mem) And.left,
    fun h' ↦ Or.inr ⟨h', p, hp, Set.subset_union_right.trans (C.le_root_update _)⟩⟩

theorem question_singleton_update (hk : ¬ k ⊆ C.root) (p : Set X) :
    (question C {p}).update k = C.update (k ∪ p) :=
  question_update_of_forall C hk (P := {p}) rfl fun _ hq hne ↦ absurd hq hne

theorem admits_question_singleton_iff (hk : ¬ k ⊆ C.root) (p : Set X) :
    Admits (question C {p}) k ↔ Admits C (k ∪ p) :=
  admits_question_iff_of_forall C hk (P := {p}) rfl fun _ hq hne ↦ absurd hq hne

theorem admits_update_iff (h : Admits C k) : Admits (C.update k) l ↔ Admits C (l ∪ k) := by
  rw [Admits, C.update_update h]
  exact ⟨fun h' ↦ C.update_le h h',
    fun h' ↦ Or.inr ⟨h', Set.subset_union_right.trans (C.le_root_update _)⟩⟩

end Questions

/-! ### Questions about commitments -/

section Commitments

variable {A W : Type*} (O : A → SetRel W W) (C : Space (Set (Set W))) (a : A) (φ : Set W)
  {d : Set (Set W)}

/-- A monopolar question proposes `a`'s commitment to `φ` (27). -/
def monopolarQuestion : Space (Set (Set W)) := question C {{committed O a φ}}

/-- A bipolar question proposes `a`'s commitment to `φ` or to `¬φ` (23). -/
def bipolarQuestion : Space (Set (Set W)) :=
  question C {{committed O a φ}, {committed O a φᶜ}}

/-- A question with high negation proposes `a`'s refusal to commit to `φ`, the complement of
`a⊢φ` (39). -/
def highNegationQuestion : Space (Set (Set W)) := question C {{(committed O a φ)ᶜ}}

theorem mem_monopolarQuestion :
    d ∈ monopolarQuestion O C a φ ↔ d = C.root ∨ d ∈ C ∧ committed O a φ ∈ d := by
  simp [monopolarQuestion, mem_question]

-- (31)
theorem coe_bipolarQuestion :
    (bipolarQuestion O C a φ : Set (Set (Set W))) =
      ↑(monopolarQuestion O C a φ) ∪ ↑(monopolarQuestion O C a φᶜ) := by
  rw [bipolarQuestion, Set.insert_eq, coe_question_union]
  rfl

-- (28a)
theorem monopolarQuestion_update_yes :
    (monopolarQuestion O C a φ).update {committed O a φ} = C.assert O a φ :=
  question_update_of_mem C (P := {{committed O a φ}}) rfl

end Commitments

/-! ### Coherent states -/

section Coherent

variable {W : Type*} {c d k : Set (Set W)} {x : Set W}

/-- A commitment state is coherent when its propositions hold together at some world (pp. 329,
340). -/
def Coherent (c : Set (Set W)) : Prop := (⋂₀ c).Nonempty

theorem Coherent.mono (h : c ⊆ d) (hd : Coherent d) : Coherent c :=
  Set.Nonempty.mono (Set.sInter_subset_sInter h) hd

@[simp] theorem coherent_singleton : Coherent {x} ↔ x.Nonempty := by simp [Coherent]

theorem coherent_pair {y : Set W} : Coherent {x, y} ↔ (x ∩ y).Nonempty := by
  simp [Coherent]

variable {A : Type*} {O : A → SetRel W W} {a : A} {φ : Set W}

/-- Committing to `φ` while refusing to commit to it is incoherent (p. 340). -/
theorem not_coherent_committed_compl : ¬ Coherent {committed O a φ, (committed O a φ)ᶜ} := by
  simp [coherent_pair]

/-- Committing to `φ` and to `¬φ` is incoherent, since commitments are consistent (p. 329). -/
theorem not_coherent_committed_committed_compl [ModalLogic.IsSerial (O a)] :
    ¬ Coherent {committed O a φ, committed O a φᶜ} := by
  rw [coherent_pair, Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty]
  exact disjoint_committed_compl

theorem coherent_committed_compl_compl [ModalLogic.IsSerial (O a)]
    (h : (committed O a φᶜ).Nonempty) : Coherent {committed O a φᶜ, (committed O a φ)ᶜ} := by
  rw [coherent_pair, Set.inter_eq_left.2 (disjoint_committed_compl (φ := φ)).subset_compl_left]
  exact h

variable (W) in
/-- The space of coherent states, with no commitments at the root. -/
def coherent [Nonempty W] : Space (Set (Set W)) :=
  ⟨{c | Coherent c}, ∅, by simp [Coherent], fun _ _ ↦ Set.empty_subset _⟩

variable [Nonempty W]

theorem root_update_coherent (h : Coherent k) : ((coherent W).update k).root = k :=
  IsLeast.csInf_eq ⟨⟨h, Set.Subset.rfl⟩, fun _ hd ↦ hd.2⟩

theorem admits_coherent_iff : Admits (coherent W) k ↔ Coherent k :=
  ⟨fun h ↦ Coherent.mono ((coherent W).le_root_update k) h,
    fun h ↦ by rw [Admits, root_update_coherent h]; exact h⟩

theorem not_subset_root_coherent (x : Set W) : ¬ ({x} : Set (Set W)) ⊆ (coherent W).root :=
  fun h ↦ h rfl

end Coherent

/-! ### Which answers a question admits -/

section Predictions

variable {A W : Type*} [Nonempty W] (O : A → SetRel W W) (a : A) (φ : Set W)

-- (28a)
theorem admits_monopolarQuestion_yes (h : (committed O a φ).Nonempty) :
    Admits (monopolarQuestion O (coherent W) a φ) {committed O a φ} :=
  (admits_question_iff_of_mem (coherent W) (P := {{committed O a φ}}) rfl).2
    (admits_coherent_iff.2 (coherent_singleton.2 h))

/-- *No* to a monopolar question is not admitted, so it needs a prior rejection (28b). -/
theorem not_admits_monopolarQuestion_no [ModalLogic.IsSerial (O a)] :
    ¬ Admits (monopolarQuestion O (coherent W) a φ) {committed O a φᶜ} := fun h ↦
  not_coherent_committed_committed_compl <| Coherent.mono (Set.pair_comm _ _).le <|
    admits_coherent_iff.1 <|
      (admits_question_singleton_iff _ (not_subset_root_coherent _) {committed O a φ}).1 h

-- (24)
theorem admits_bipolarQuestion_yes (h : (committed O a φ).Nonempty) :
    Admits (bipolarQuestion O (coherent W) a φ) {committed O a φ} :=
  (admits_question_iff_of_mem (coherent W) (P := {{committed O a φ}, {committed O a φᶜ}})
    (Or.inl rfl)).2 (admits_coherent_iff.2 (coherent_singleton.2 h))

/-- *No* to a bipolar question is admitted (24). -/
theorem admits_bipolarQuestion_no (h : (committed O a φᶜ).Nonempty) :
    Admits (bipolarQuestion O (coherent W) a φ) {committed O a φᶜ} :=
  (admits_question_iff_of_mem (coherent W) (P := {{committed O a φ}, {committed O a φᶜ}})
    (Or.inr rfl)).2 (admits_coherent_iff.2 (coherent_singleton.2 h))

-- p. 340
theorem highNegationQuestion_update_no :
    (highNegationQuestion O (coherent W) a φ).update {committed O a φᶜ} =
      (coherent W).update {committed O a φᶜ, (committed O a φ)ᶜ} :=
  question_singleton_update _ (not_subset_root_coherent _) {(committed O a φ)ᶜ}

/-- *No* to a question with high negation lands on the state that keeps the refusal. -/
theorem root_highNegationQuestion_update_no [ModalLogic.IsSerial (O a)]
    (h : (committed O a φᶜ).Nonempty) :
    ((highNegationQuestion O (coherent W) a φ).update {committed O a φᶜ}).root =
      {committed O a φᶜ, (committed O a φ)ᶜ} := by
  rw [highNegationQuestion_update_no, root_update_coherent (coherent_committed_compl_compl h)]

-- p. 340
theorem admits_highNegationQuestion_no [ModalLogic.IsSerial (O a)]
    (h : (committed O a φᶜ).Nonempty) :
    Admits (highNegationQuestion O (coherent W) a φ) {committed O a φᶜ} :=
  (admits_question_singleton_iff _ (not_subset_root_coherent _) {(committed O a φ)ᶜ}).2
    (admits_coherent_iff.2 (coherent_committed_compl_compl h))

/-- *Yes* to a question with high negation needs a prior rejection (p. 340). -/
theorem not_admits_highNegationQuestion_yes :
    ¬ Admits (highNegationQuestion O (coherent W) a φ) {committed O a φ} := fun h ↦
  not_coherent_committed_compl <| admits_coherent_iff.1 <|
    (admits_question_singleton_iff _ (not_subset_root_coherent _) {(committed O a φ)ᶜ}).1 h

end Predictions

/-! ### Developments and rejection -/

/-- A commitment space development (8) is the current space with the spaces the conversation
has passed through, the latest first. -/
structure Development (S : Type*) [LE S] where
  current : Space S
  past : List (Space S) := []

namespace Development

variable {S : Type*} [LE S] (D : Development S)

/-- Performing an act extends the development by its result (8). -/
def perform (act : Space S → Space S) : Development S := ⟨act D.current, D.current :: D.past⟩

/-- Rejecting the last act returns to the space before it and keeps the record (10). -/
def reject : Development S := ⟨D.past.headD D.current, D.current :: D.past⟩

@[simp] theorem current_perform (act : Space S → Space S) :
    (D.perform act).current = act D.current := rfl

@[simp] theorem current_reject_perform (act : Space S → Space S) :
    (D.perform act).reject.current = D.current := rfl

end Development

/-- A conversation starting from the coherent space. -/
def start (W : Type*) [Nonempty W] : Development (Set (Set W)) := ⟨coherent W, []⟩

-- (28b)
theorem root_reject_monopolarQuestion_no {A W : Type*} [Nonempty W] (O : A → SetRel W W) (a : A)
    (φ : Set W) (h : (committed O a φᶜ).Nonempty) :
    (((start W).perform (monopolarQuestion O · a φ)).reject.perform
      (·.assert O a φᶜ)).current.root = {committed O a φᶜ} :=
  root_update_coherent (coherent_singleton.2 h)

/-! ### The issue a space raises -/

section Issue

variable {W : Type*} (C : Space (Set (Set W)))

/-- The continuations of a space are its states other than the root. -/
def continuations : Set (Set (Set W)) := ↑C \ {C.root}

open scoped Classical in
/-- The issue a space raises is settled by the information states inside what some continuation
entails, or inside what the root entails when the space has no continuations. -/
noncomputable def toIssue : Question W :=
  if continuations C = ∅ then Question.ofSet (⋂₀ C.root)
  else ⨆ c ∈ continuations C, Question.ofSet (⋂₀ c)

theorem mem_toIssue_iff {i : Set W} :
    i ∈ toIssue C ↔
      (continuations C = ∅ ∧ i ⊆ ⋂₀ C.root) ∨ ∃ c ∈ continuations C, i ⊆ ⋂₀ c := by
  unfold toIssue
  split_ifs with h
  · simp [h, Question.mem_ofSet]
  · simp only [h, false_and, false_or, Question.mem_biSup_iff, Question.mem_ofSet]
    refine ⟨fun h' ↦ h'.elim (fun e ↦ ?_) id, Or.inr⟩
    obtain ⟨c, hc⟩ := Set.nonempty_iff_ne_empty.2 h
    exact ⟨c, hc, e ▸ Set.empty_subset _⟩

theorem sInter_subset_of_mem_continuations_monopolarQuestion {A : Type*} {O : A → SetRel W W}
    {a : A} {φ : Set W} {c : Set (Set W)} (hc : c ∈ continuations (monopolarQuestion O C a φ)) :
    ⋂₀ c ⊆ committed O a φ := by
  obtain ⟨hc, hne⟩ := hc
  rcases (mem_monopolarQuestion ..).1 hc with rfl | ⟨-, hc⟩
  · exact absurd rfl hne
  · exact Set.sInter_subset_of_mem hc

end Issue

/-! ### A model of the weather and the participants' commitments -/

/-- In one world it is raining and in the other it is not. -/
inductive Weather
  | rain
  | noRain
  deriving DecidableEq

instance : Nonempty Weather := ⟨.rain⟩

/-- It is raining. -/
def raining : Set Weather := {.rain}

/-- An index fixes the weather and what each participant's commitments leave open about it. -/
abbrev World := Index Discourse.Role Weather

/-- The index at which it rains and each participant's commitments leave open the weathers in
`s`. -/
def World.mk (w : Weather) (s : Discourse.Role → Set Weather) (hs : ∀ r, (s r).Nonempty) :
    World :=
  ⟨w, s, hs⟩

instance : Nonempty World := ⟨.mk .rain (fun _ ↦ Set.univ) fun _ ↦ Set.univ_nonempty⟩

/-- The initial commitment space has every coherent state. -/
abbrev C₀ : Space (Set (Set World)) := coherent World

/-- That a participant is committed to the weather being in `s`. -/
abbrev commitsTo (r : Discourse.Role) (s : Set Weather) : Set World :=
  committed Index.access r (Index.fact ⁻¹' s)

theorem mem_commitsTo {r : Discourse.Role} {s : Set Weather} {w : World} :
    w ∈ commitsTo r s ↔ w.commitmentSet r ⊆ s := by
  rw [commitsTo, Index.committed_access_preimage]
  rfl

/-- The index at which it rains and the speaker and the addressee are committed to `s` and `t`. -/
def committing (w : Weather) (s t : Set Weather) (hs : s.Nonempty) (ht : t.Nonempty) : World :=
  ⟨w, fun r ↦ match r with | .speaker => s | .addressee => t, fun r ↦ by cases r <;> assumption⟩

theorem raining_nonempty : raining.Nonempty := ⟨.rain, rfl⟩

theorem raining_compl_nonempty : rainingᶜ.Nonempty := ⟨.noRain, fun h ↦ Weather.noConfusion h⟩

theorem committing_mem_commitsTo_speaker {w : Weather} {s t : Set Weather} (hs : s.Nonempty)
    (ht : t.Nonempty) : committing w s t hs ht ∈ commitsTo .speaker s :=
  mem_commitsTo.2 subset_rfl

theorem committing_mem_commitsTo_addressee {w : Weather} {s t : Set Weather} (hs : s.Nonempty)
    (ht : t.Nonempty) : committing w s t hs ht ∈ commitsTo .addressee t :=
  mem_commitsTo.2 subset_rfl

theorem coherent_commitsTo_commitsTo {s t : Set Weather} (hs : s.Nonempty) (ht : t.Nonempty) :
    Coherent {commitsTo .addressee s, commitsTo .speaker t} :=
  coherent_pair.2 ⟨committing .rain t s ht hs, committing_mem_commitsTo_addressee ht hs,
    committing_mem_commitsTo_speaker ht hs⟩

/-- Asserting that it rains adds the speaker's commitment, and the root then entails that the
speaker is committed to rain but not that it rains (19), while the Table of [farkas-bruce-2010]
leaves the common ground as it was until the proposal is accepted. -/
theorem sInter_root_assert_raining :
    ⋂₀ (C₀.assert Index.access .speaker (Index.fact ⁻¹' raining)).root =
        commitsTo .speaker raining ∧
      ¬ commitsTo .speaker raining ⊆ Index.fact ⁻¹' raining ∧
      ((Table.empty : Table Discourse.Role World).assert .speaker
        (Index.fact ⁻¹' raining)).commonGround = ⊤ := by
  refine ⟨?_, fun h ↦ ?_, rfl⟩
  · rw [assert, root_update_coherent (coherent_singleton.2 ⟨_, committing_mem_commitsTo_speaker
      (w := .rain) raining_nonempty raining_nonempty⟩), Set.sInter_singleton]
  · exact Weather.noConfusion
      (h (committing_mem_commitsTo_speaker (w := .noRain) raining_nonempty raining_nonempty))

/-- The second update of an assertion, by the proposition itself, is what puts it into what the
root entails (19). -/
theorem sInter_root_update_assert_raining :
    ⋂₀ ((C₀.assert Index.access .speaker (Index.fact ⁻¹' raining)).update
        {Index.fact ⁻¹' raining}).root = commitsTo .speaker raining ∩ Index.fact ⁻¹' raining := by
  have hw := committing_mem_commitsTo_speaker (w := .rain) raining_nonempty raining_nonempty
  have hc : Coherent {commitsTo .speaker raining} := coherent_singleton.2 ⟨_, hw⟩
  have hc' : Coherent {Index.fact ⁻¹' raining, commitsTo .speaker raining} :=
    coherent_pair.2 ⟨_, rfl, hw⟩
  rw [assert, (coherent World).update_update (admits_coherent_iff.2 hc),
    root_update_coherent (k := {Index.fact ⁻¹' raining} ⊔ {commitsTo .speaker raining}) hc']
  exact (Set.sInter_pair _ _).trans (Set.inter_comm _ _)

theorem singleton_commitsTo_mem_continuations {s : Set Weather} (hs : s.Nonempty) :
    {commitsTo .addressee s} ∈ continuations (monopolarQuestion Index.access C₀ .addressee
      (Index.fact ⁻¹' s)) :=
  ⟨(mem_monopolarQuestion ..).2 (Or.inr ⟨coherent_singleton.2
    ⟨_, committing_mem_commitsTo_addressee (w := .rain) hs hs⟩, rfl⟩),
    (Set.singleton_nonempty _).ne_empty⟩

theorem monopolar_not_inquisitive :
    ¬ (toIssue (monopolarQuestion Index.access C₀ .addressee
      (Index.fact ⁻¹' raining))).IsInquisitive := by
  intro h
  have hmem : commitsTo .addressee raining ∈
      toIssue (monopolarQuestion Index.access C₀ .addressee (Index.fact ⁻¹' raining)) :=
    (mem_toIssue_iff _).2 (Or.inr ⟨_, singleton_commitsTo_mem_continuations raining_nonempty,
      (Set.sInter_singleton _).ge⟩)
  refine h ?_
  have : (toIssue (monopolarQuestion Index.access C₀ .addressee
      (Index.fact ⁻¹' raining))).info = commitsTo .addressee raining := by
    refine Set.Subset.antisymm (Set.sUnion_subset fun i hi ↦ ?_) (Set.subset_sUnion_of_mem hmem)
    rcases (mem_toIssue_iff _).1 hi with ⟨h0, -⟩ | ⟨c, hc, hic⟩
    · exact absurd (singleton_commitsTo_mem_continuations raining_nonempty)
        (h0 ▸ Set.notMem_empty _)
    · exact hic.trans (sInter_subset_of_mem_continuations_monopolarQuestion _ hc)
  rw [this]
  exact hmem

theorem bipolar_inquisitive :
    (toIssue (bipolarQuestion Index.access C₀ .addressee
      (Index.fact ⁻¹' raining))).IsInquisitive := by
  intro hinfo
  have hy : {commitsTo .addressee raining} ∈
      continuations (bipolarQuestion Index.access C₀ .addressee (Index.fact ⁻¹' raining)) :=
    ⟨(coe_bipolarQuestion ..).ge
      (Or.inl (singleton_commitsTo_mem_continuations raining_nonempty).1),
      (Set.singleton_nonempty _).ne_empty⟩
  have hn : {commitsTo .addressee rainingᶜ} ∈
      continuations (bipolarQuestion Index.access C₀ .addressee (Index.fact ⁻¹' raining)) :=
    ⟨(coe_bipolarQuestion ..).ge
      (Or.inr (singleton_commitsTo_mem_continuations raining_compl_nonempty).1),
      (Set.singleton_nonempty _).ne_empty⟩
  have hyes := (mem_toIssue_iff _).2 (Or.inr ⟨_, hy, (Set.sInter_singleton _).ge⟩)
  have hno := (mem_toIssue_iff _).2 (Or.inr ⟨_, hn, (Set.sInter_singleton _).ge⟩)
  let wy := committing .rain raining raining raining_nonempty raining_nonempty
  let wn := committing .rain rainingᶜ rainingᶜ raining_compl_nonempty raining_compl_nonempty
  have hwy : wy ∈ (toIssue (bipolarQuestion Index.access C₀ .addressee
      (Index.fact ⁻¹' raining))).info :=
    Set.subset_sUnion_of_mem hyes (committing_mem_commitsTo_addressee _ _)
  have hwn : wn ∈ (toIssue (bipolarQuestion Index.access C₀ .addressee
      (Index.fact ⁻¹' raining))).info :=
    Set.subset_sUnion_of_mem hno (committing_mem_commitsTo_addressee _ _)
  rcases (mem_toIssue_iff _).1 hinfo with ⟨h0, -⟩ | ⟨c, hc, hsub⟩
  · exact absurd hy (h0 ▸ Set.notMem_empty _)
  · rcases ((coe_bipolarQuestion ..).le hc.1).imp
        (fun h ↦ sInter_subset_of_mem_continuations_monopolarQuestion _ ⟨h, hc.2⟩)
        (fun h ↦ sInter_subset_of_mem_continuations_monopolarQuestion _ ⟨h, hc.2⟩) with h | h
    · exact Weather.noConfusion (mem_commitsTo.1 (h (hsub hwn))
        (show Weather.noRain ∈ wn.commitmentSet .addressee from fun e ↦ Weather.noConfusion e))
    · exact (mem_commitsTo (s := rainingᶜ)).1 (h (hsub hwy))
        (show Weather.rain ∈ wy.commitmentSet .addressee from rfl) rfl

/-! ### Table 1 -/

/-- The contextual evidence of [buring-gunlogson-2000] leaves open `φ`, its complement, or every
world, according to the sign of `φ` it supports. -/
def evidence (φ : Set Weather) : SignType → Set Weather
  | .pos => φ
  | .neg => φᶜ
  | .zero => Set.univ

/-- A monopolar question proposing `S₂⊢φ` is licensed by evidence for `φ`. -/
def MonopolarLicensed (E φ : Set Weather) : Prop := E ⊆ φ

/-- A bipolar question is licensed by neutral evidence. -/
def BipolarLicensed (E φ : Set Weather) : Prop := ¬ E ⊆ φ ∧ ¬ E ⊆ φᶜ

/-- The high-negation question, proposing the refusal `¬S₂⊢φ`, is licensed wherever the
evidence is not for `φ`. -/
def HighNegationLicensed (E φ : Set Weather) : Prop := ¬ E ⊆ φ

/-- Each question is licensed on particular readings. The question without negation, `none`, is
licensed on either of its readings; the question with low negation, about `¬φ`
(`some .negative`), only on the monopolar reading of `¬φ`; the question with high negation,
about `φ` (`some .positive`), as such. -/
def Licensed (E φ : Set Weather) : Option Polarity → Prop
  | none => MonopolarLicensed E φ ∨ BipolarLicensed E φ
  | some .negative => MonopolarLicensed E φᶜ
  | some .positive => HighNegationLicensed E φ

theorem raining_ne_empty : raining ≠ ∅ := (Set.singleton_nonempty _).ne_empty

theorem raining_ne_univ : raining ≠ Set.univ := fun h ↦
  Weather.noConfusion (Set.eq_univ_iff_forall.1 h .noRain)

-- Table 1
theorem table1 (e : SignType) :
    (Licensed (evidence raining e) raining none ↔ e ≠ -1) ∧
      (Licensed (evidence raining e) raining (some .negative) ↔ e = -1) ∧
      (Licensed (evidence raining e) raining (some .positive) ↔ e ≠ 1) := by
  cases e <;> simp [Licensed, MonopolarLicensed, BipolarLicensed,
    HighNegationLicensed, evidence, raining_ne_empty, raining_ne_univ]

open BuringGunlogson2000 in
theorem licensed_iff_felicitous (r : Option Polarity) (e : SignType) :
    Licensed (evidence raining e) raining r ↔ BuringGunlogson2000.Felicitous r e := by
  rcases r with _ | _ | _
  exacts [(table1 e).1.trans (felicitous_none_iff_ne e).symm,
    (table1 e).2.2.trans (felicitous_some_positive_iff_ne e).symm,
    (table1 e).2.1.trans (felicitous_some_negative_iff_eq e).symm]

instance : MeasurableSpace Weather := ⊤

instance : DiscreteMeasurableSpace Weather := ⟨fun _ ↦ trivial⟩

theorem relevanceSign_evidence (μ : MeasureTheory.Measure Weather)
    [MeasureTheory.IsFiniteMeasure μ] [h : DTS.Context.Nondegenerate ⟨raining, .of_discrete, μ⟩]
    (e : SignType) : DTS.relevanceSign ⟨raining, .of_discrete, μ⟩ (evidence raining e) = e := by
  cases e
  · exact DTS.relevanceSign_univ _
  · exact DTS.relevanceSign_eq_neg_one_of_subset_compl subset_rfl h.compl_ne_zero
  · exact DTS.relevanceSign_eq_one_of_subset subset_rfl h.topic_ne_zero

/-! ### Question tags (44), (45) -/

section Tags

variable {W : Type*} (O : Discourse.Role → SetRel W W) (C : Space (Set (Set W))) (φ : Set W)

/-- A matching tag conjoins the assertion with the monopolar question of the same content
(44). -/
def matchingTag : Set (Set (Set W)) :=
  ↑(C.assert O .speaker φ) ∩ ↑(monopolarQuestion O C .addressee φ)

/-- A reverse tag disjoins the assertion with the monopolar question of the negation (45). -/
def reverseTag : Set (Set (Set W)) :=
  ↑(C.assert O .speaker φ) ∪ ↑(monopolarQuestion O C .addressee φᶜ)

-- p. 342
theorem matchingTag_eq (hk : committed O .speaker φ ∉ C.root)
    (h : Admits C {committed O .addressee φ, committed O .speaker φ}) :
    matchingTag O C φ = ↑(C.update {committed O .addressee φ, committed O .speaker φ}) := by
  rw [C.coe_update_of_root_mem h]
  ext d
  simp only [matchingTag, Set.mem_inter_iff, SetLike.mem_coe, mem_monopolarQuestion, Set.mem_Ici]
  constructor
  · rintro ⟨hs, rfl | ⟨hd, ha⟩⟩
    · exact absurd ((C.root_mem_assert_iff _ _ _).1 hs) hk
    · have hks : committed O .speaker φ ∈ d :=
        ((C.mem_assert _ _ _).1 hs).elim (fun e ↦ e ▸ C.committed_mem_root_assert _ _ _)
          And.right
      exact ⟨hd, Set.insert_subset ha (Set.singleton_subset_iff.2 hks)⟩
  · rintro ⟨hd, hsub⟩
    exact ⟨(C.mem_assert _ _ _).2 (Or.inr ⟨hd, hsub (Or.inr rfl)⟩),
      Or.inr ⟨hd, hsub (Or.inl rfl)⟩⟩

theorem reverseTag_eq (h : Admits C {committed O .speaker φ}) :
    reverseTag O C φ =
      ↑(question C {{committed O .speaker φ}, {committed O .addressee φᶜ}}) := by
  ext d
  constructor
  · rintro (hd | hd)
    · exact Or.inr ⟨C.update_le h hd, _, Or.inl rfl, Set.singleton_subset_iff.2 <|
        ((C.mem_assert _ _ _).1 hd).elim (fun e ↦ e ▸ C.committed_mem_root_assert _ _ _)
          And.right⟩
    · exact ((mem_monopolarQuestion ..).1 hd).imp id fun hd ↦
        ⟨hd.1, _, Or.inr rfl, Set.singleton_subset_iff.2 hd.2⟩
  · rintro (rfl | ⟨hd, q, (rfl | rfl), hq⟩)
    · exact Or.inr (Space.root_mem _)
    · exact Or.inl ((C.mem_assert _ _ _).2 (Or.inr ⟨hd, hq rfl⟩))
    · exact Or.inr ((mem_monopolarQuestion ..).2 (Or.inr ⟨hd, hq rfl⟩))

theorem isLeast_reverseTag : IsLeast (reverseTag O C φ) C.root :=
  ⟨Or.inr (Space.root_mem _), by
    rintro d (hd | hd)
    · exact (C.root_le_root_update _).trans ((C.assert O .speaker φ).root_le hd)
    · exact (monopolarQuestion O C .addressee φᶜ).root_le hd⟩

/-- When the addressee contradicts a plain assertion, the speaker is still committed
(p. 342). -/
theorem committed_speaker_mem_root_assert_assert (ψ : Set W) :
    committed O .speaker φ ∈ ((C.assert O .speaker φ).assert O .addressee ψ).root :=
  (C.assert O .speaker φ).root_le_root_update _ (C.committed_mem_root_assert _ _ _)

variable [Nonempty W] {O φ}

theorem isLeast_matchingTag (h : Coherent {committed O .addressee φ, committed O .speaker φ}) :
    IsLeast (matchingTag O (coherent W) φ)
      {committed O .addressee φ, committed O .speaker φ} := by
  rw [matchingTag_eq _ _ φ (Set.notMem_empty _) (admits_coherent_iff.2 h)]
  have h' := ((coherent W).update {committed O .addressee φ, committed O .speaker φ}).isLeast
  rwa [root_update_coherent h] at h'

-- p. 342
theorem not_admits_matchingTag_no [ModalLogic.IsSerial (O .addressee)]
    (h : Coherent {committed O .addressee φ, committed O .speaker φ}) :
    ¬ Admits ((coherent W).update {committed O .addressee φ, committed O .speaker φ})
      {committed O .addressee φᶜ} := fun h' ↦
  not_coherent_committed_committed_compl (O := O) (a := .addressee) (φ := φ) <|
    Coherent.mono (Set.insert_subset (Or.inr (Or.inl rfl)) (Set.singleton_subset_iff.2
      (Or.inl rfl))) <| admits_coherent_iff.1 <|
        (admits_update_iff _ (admits_coherent_iff.2 h)).1 h'

/-- Rejecting an assertion with a matching tag and answering *no* leaves only the addressee's
commitment, the speaker's being rejected with the tag (p. 342). -/
theorem root_reject_matchingTag_no (h : (committed O .addressee φᶜ).Nonempty) :
    (((start W).perform
        (·.update {committed O .addressee φ, committed O .speaker φ})).reject.perform
      (·.assert O .addressee φᶜ)).current.root = {committed O .addressee φᶜ} :=
  root_update_coherent (coherent_singleton.2 h)

theorem admits_assert_no (hs : (committed O .speaker φ).Nonempty)
    (h : Coherent {committed O .addressee φᶜ, committed O .speaker φ}) :
    Admits ((coherent W).assert O .speaker φ) {committed O .addressee φᶜ} :=
  (admits_update_iff _ (admits_coherent_iff.2 (coherent_singleton.2 hs))).2
    (admits_coherent_iff.2 h)

-- p. 343
theorem root_reverseTag_update_yes [ModalLogic.IsSerial (O .addressee)]
    (h : Coherent {committed O .addressee φ, committed O .speaker φ}) :
    ((question (coherent W) {{committed O .speaker φ}, {committed O .addressee φᶜ}}).update
        {committed O .addressee φ}).root =
      {committed O .addressee φ, committed O .speaker φ} := by
  have h' : ∀ q ∈ ({{committed O .speaker φ}, {committed O .addressee φᶜ}} : Set (Set (Set W))),
      q ≠ {committed O .speaker φ} → ∀ d ∈ coherent W, ¬ {committed O .addressee φ} ∪ q ⊆ d := by
    rintro q (rfl | rfl) hne d hd hsub
    · exact absurd rfl hne
    · exact not_coherent_committed_committed_compl (O := O) (a := .addressee) (φ := φ)
        (Coherent.mono hsub hd)
  rw [question_update_of_forall _ (not_subset_root_coherent _) (Or.inl rfl) h']
  exact root_update_coherent h

-- p. 343
theorem root_reverseTag_update_no (h : (committed O .addressee φᶜ).Nonempty) :
    ((question (coherent W) {{committed O .speaker φ}, {committed O .addressee φᶜ}}).update
        {committed O .addressee φᶜ}).root = {committed O .addressee φᶜ} := by
  rw [question_update_of_mem (coherent W)
    (P := {{committed O .speaker φ}, {committed O .addressee φᶜ}}) (Or.inr rfl)]
  exact root_update_coherent (coherent_singleton.2 h)

end Tags

/-! ### The tags in the model -/

theorem coherent_addressee_speaker_raining :
    Coherent {commitsTo .addressee raining, commitsTo .speaker raining} :=
  coherent_commitsTo_commitsTo raining_nonempty raining_nonempty

/-- In the model, after a reverse tag the addressee's *yes* brings the speaker's commitment
with it. -/
example :
    ((question C₀ {{commitsTo .speaker raining}, {commitsTo .addressee rainingᶜ}}).update
        {commitsTo .addressee raining}).root =
      {commitsTo .addressee raining, commitsTo .speaker raining} :=
  root_reverseTag_update_yes coherent_addressee_speaker_raining

/-- In the model, *no* to an assertion is admitted, and the contradiction is coherent. -/
example : Admits (C₀.assert Index.access .speaker (Index.fact ⁻¹' raining))
    {commitsTo .addressee rainingᶜ} :=
  admits_assert_no ⟨_, committing_mem_commitsTo_speaker (w := .rain) raining_nonempty
      raining_nonempty⟩ (coherent_commitsTo_commitsTo raining_compl_nonempty raining_nonempty)

end Krifka2015
