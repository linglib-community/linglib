module

public import Mathlib.Order.UpperLower.Closure
public import Linglib.Discourse.Commitment.Space
public import Linglib.Discourse.Commitment.Table
public import Linglib.Discourse.QUD.Issue
public import Linglib.Discourse.Role
public import Studies.BuringGunlogson2000

/-!
# Krifka (2015): Bias in Commitment Space Semantics

Krifka models a conversation as a commitment space, the current commitment state with the
continuations it projects, all of them coherent. An assertion keeps the states that carry the
speaker's commitment. A question keeps the root and proposes continuations: a monopolar
question the addressee's assertion of `φ`, a bipolar question that assertion or the one of
`¬φ`, a question with high negation the addressee's refusal to commit to `φ`; a question with
low negation is a monopolar question about `¬φ`. An answer is performed in the space the
question left, so it lands on a state that also carries what the question proposed, and an
answer that no such state carries needs a prior rejection, which returns to the space before
the question. This is the bias of a question. A matching question tag conjoins an assertion
with the monopolar question of the same content, and a reverse tag disjoins it with the
monopolar question of the negation.

## Main statements

* `not_admits_monopolarQuestion_no`, `admits_bipolarQuestion_no`: *no* needs a prior rejection
  after a monopolar question and none after a bipolar one.
* `root_highNegationQuestion_update_no`, `not_admits_highNegationQuestion_yes`: after a question
  with high negation *no* is admitted and keeps the refusal, while *yes* needs a rejection.
* `root_reject_matchingTag_no`, `commit_speaker_mem_root_assert_assert`: rejecting an assertion
  with a matching tag removes the speaker's commitment, which a plain assertion keeps when the
  addressee contradicts it.
* `root_reverseTag_update_yes`: after a reverse tag, the addressee's commitment to `φ` brings
  the speaker's with it.

## Implementation notes

* Coherence is the paper's ban on blatant inconsistency: nobody is committed to a proposition
  while committed to its negation or refusing to commit to it. The initial space has every
  coherent state.
* Developments record the spaces passed through and not who acted, since no statement here
  depends on the actor of a stage.
* The licensing conditions behind the table of acceptable uses are stated on the evidence and
  are not derived from the spaces. Contextual evidence is the set of worlds it leaves open: the
  proposition, everything, or its complement.

## TODO

* The second update of an assertion, by the proposition itself, is not modelled, so
  contradicting a plain assertion needs no rejection here; in the paper the rejection undoes
  only that update, and the speaker's commitment stays, as here.
* The reaction *I don't know* is left out: its clash with either answer is a fact about
  knowledge that coherence does not see.
* The paper prints the addressee's commitment to `φ` in the last stage of (28b); since *no*
  asserts the negation, it is the commitment to `¬φ` here.

## References

* [M. Krifka, *Bias in Commitment Space Semantics: Declarative Questions, Negated Questions,
  and Question Tags* (2015)][krifka-2015]
* [D. F. Farkas and K. B. Bruce, *On Reacting to Assertions and Polar Questions*
  (2010)][farkas-bruce-2010]
* [D. Büring and C. Gunlogson, *Aren't Positive and Negative Polar Questions the Same?*
  (2000)][buring-gunlogson-2000]
-/

@[expose] public section

namespace Krifka2015

open Commitment Space Question

/-! ### Questions as meta-speech acts -/

section Questions

variable {A W : Type*} (C : Space (State A W)) (a : A) (φ : Set W) {P : Set (State A W)}
  {k l p d : State A W}

/-- A question keeps the root and proposes the continuations that carry one of the acts in
`P`. -/
def question (P : Set (State A W)) : Space (State A W) := C.restrict (upperClosure P)

theorem mem_question : d ∈ question C P ↔ d = C.root ∨ d ∈ C ∧ ∃ p ∈ P, p ⊆ d := Iff.rfl

/-- A question proposing one act is the root together with the update by that act (27). -/
theorem question_singleton (p : State A W) : question C {p} = C.restrict (C.update p) := by
  rw [question, restrict_coe_update, upperClosure_singleton, UpperSet.coe_Ici]

/-- A question is the disjunction of the questions proposing its acts (31), (34). -/
theorem coe_question_union (P Q : Set (State A W)) :
    (question C (P ∪ Q) : Set (State A W)) = ↑(question C P) ∪ ↑(question C Q) := by
  rw [question, upperClosure_union, UpperSet.coe_inf, coe_restrict_union]
  rfl

/-- A monopolar question proposes `a`'s assertion of `φ` (27). -/
def monopolarQuestion : Space (State A W) := question C {{commit a φ}}

/-- A bipolar question proposes `a`'s assertion of `φ` or of `¬φ` (23). -/
def bipolarQuestion : Space (State A W) := question C {{commit a φ}, {commit a φᶜ}}

/-- A question with high negation proposes `a`'s refusal `¬S⊢φ` (39). -/
def highNegationQuestion : Space (State A W) := question C {{refuse a φ}}

theorem mem_monopolarQuestion :
    d ∈ monopolarQuestion C a φ ↔ d = C.root ∨ d ∈ C ∧ commit a φ ∈ d := by
  simp [monopolarQuestion, mem_question]

/-- A bipolar question is the disjunction of the two monopolar questions (31). -/
theorem coe_bipolarQuestion :
    (bipolarQuestion C a φ : Set (State A W)) =
      ↑(monopolarQuestion C a φ) ∪ ↑(monopolarQuestion C a φᶜ) := by
  rw [bipolarQuestion, Set.insert_eq, coe_question_union]
  rfl

/-! ### Answers -/

/-- A proposed act is performed as it would have been before the question (24), (28). -/
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
def Admits (C : Space (State A W)) (k : State A W) : Prop := (C.update k).root ∈ C

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

theorem question_singleton_update (hk : ¬ k ⊆ C.root) (p : State A W) :
    (question C {p}).update k = C.update (k ∪ p) :=
  question_update_of_forall C hk (P := {p}) rfl fun _ hq hne ↦ absurd hq hne

theorem admits_question_singleton_iff (hk : ¬ k ⊆ C.root) (p : State A W) :
    Admits (question C {p}) k ↔ Admits C (k ∪ p) :=
  admits_question_iff_of_forall C hk (P := {p}) rfl fun _ hq hne ↦ absurd hq hne

theorem admits_update_iff (h : Admits C k) : Admits (C.update k) l ↔ Admits C (l ∪ k) := by
  rw [Admits, C.update_update h]
  exact ⟨fun h' ↦ C.update_le h h',
    fun h' ↦ Or.inr ⟨h', Set.subset_union_right.trans (C.le_root_update _)⟩⟩

end Questions

/-! ### Coherent states -/

section Coherent

variable {A W : Type*} {a b : A} {φ : Set W} {c d k : State A W}

/-- A commitment state is coherent when nobody is committed to a proposition while committed to
its negation or refusing to commit to it (pp. 329, 340). -/
def Coherent (c : State A W) : Prop :=
  ∀ a φ, commit a φ ∈ c → commit a φᶜ ∉ c ∧ refuse a φ ∉ c

theorem Coherent.mono (h : c ⊆ d) (hd : Coherent d) : Coherent c := fun a φ hc ↦
  ⟨fun h' ↦ (hd a φ (h hc)).1 (h h'), fun h' ↦ (hd a φ (h hc)).2 (h h')⟩

variable (A W) in
/-- The space of coherent states, with no commitments at the root. -/
def coherent : Space (State A W) :=
  ⟨{c | Coherent c}, ∅, fun _ _ h ↦ (Set.notMem_empty _ h).elim, fun _ _ ↦ Set.empty_subset _⟩

theorem root_update_coherent (h : Coherent k) : ((coherent A W).update k).root = k :=
  IsLeast.csInf_eq ⟨⟨h, Set.Subset.rfl⟩, fun _ hd ↦ hd.2⟩

theorem admits_coherent_iff : Admits (coherent A W) k ↔ Coherent k :=
  ⟨fun h ↦ Coherent.mono ((coherent A W).le_root_update k) h,
    fun h ↦ by rw [Admits, root_update_coherent h]; exact h⟩

theorem not_subset_root_coherent (x : Commitment A W) :
    ¬ ({x} : State A W) ⊆ (coherent A W).root := fun h ↦ h rfl

theorem coherent_commit [Nonempty W] : Coherent ({commit a φ} : State A W) := by
  simp [Coherent, commit, refuse, compl_ne_self]

theorem coherent_commit_compl_refuse [Nonempty W] :
    Coherent ({commit a φᶜ, refuse a φ} : State A W) := by
  simp [Coherent, commit, refuse, compl_ne_self]

theorem coherent_commit_commit [Nonempty W] :
    Coherent ({commit a φ, commit b φ} : State A W) := by
  simp only [Coherent, commit, refuse, Set.mem_insert_iff, Set.mem_singleton_iff,
    Commitment.mk.injEq, and_true, reduceCtorEq, and_false, or_self, not_false_eq_true]
  rintro _ _ (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [compl_ne_self]

theorem coherent_commit_compl_commit [Nonempty W] (hab : a ≠ b) :
    Coherent ({commit a φᶜ, commit b φ} : State A W) := by
  simp only [Coherent, commit, refuse, Set.mem_insert_iff, Set.mem_singleton_iff,
    Commitment.mk.injEq, and_true, reduceCtorEq, and_false, or_self, not_false_eq_true]
  rintro _ _ (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [compl_ne_self, hab, hab.symm]

theorem contextSet_singleton_commit (a : A) (φ : Set W) :
    contextSet ({commit a φ} : State A W) = φ := by
  rw [show ({commit a φ} : State A W) = insert (commit a φ) ∅ from (Set.union_empty _).symm,
    contextSet_insert_of_commit rfl, contextSet_empty, Set.inter_univ]
  rfl

end Coherent

/-! ### Which answers a question admits -/

section Predictions

variable {A W : Type*} (C : Space (State A W)) (a : A) (φ : Set W)

/-- Answering *yes* to a monopolar question is asserting `φ` (28a). -/
theorem monopolarQuestion_update_yes :
    (monopolarQuestion C a φ).update {commit a φ} = C.assert a φ :=
  question_update_of_mem C (P := {{commit a φ}}) rfl

variable (A W)

/-- *Yes* to a monopolar question is admitted (28a). -/
theorem admits_monopolarQuestion_yes [Nonempty W] :
    Admits (monopolarQuestion (coherent A W) a φ) {commit a φ} :=
  (admits_question_iff_of_mem (coherent A W) (P := {{commit a φ}}) rfl).2
    (admits_coherent_iff.2 coherent_commit)

/-- *No* to a monopolar question is not admitted, so it needs a prior rejection (28b). -/
theorem not_admits_monopolarQuestion_no :
    ¬ Admits (monopolarQuestion (coherent A W) a φ) {commit a φᶜ} := fun h ↦
  have hc := admits_coherent_iff.1 <|
    (admits_question_singleton_iff _ (not_subset_root_coherent _) {commit a φ}).1 h
  (hc a φ (Or.inr rfl)).1 (Or.inl rfl)

/-- *Yes* to a bipolar question is admitted (24). -/
theorem admits_bipolarQuestion_yes [Nonempty W] :
    Admits (bipolarQuestion (coherent A W) a φ) {commit a φ} :=
  (admits_question_iff_of_mem (coherent A W) (P := {{commit a φ}, {commit a φᶜ}})
    (Or.inl rfl)).2 (admits_coherent_iff.2 coherent_commit)

/-- *No* to a bipolar question is admitted (24). -/
theorem admits_bipolarQuestion_no [Nonempty W] :
    Admits (bipolarQuestion (coherent A W) a φ) {commit a φᶜ} :=
  (admits_question_iff_of_mem (coherent A W) (P := {{commit a φ}, {commit a φᶜ}})
    (Or.inr rfl)).2 (admits_coherent_iff.2 coherent_commit)

/-- Answering *no* to a question with high negation is committing to `¬φ` while refusing to
commit to `φ` (p. 340). -/
theorem highNegationQuestion_update_no :
    (highNegationQuestion (coherent A W) a φ).update {commit a φᶜ} =
      (coherent A W).update {commit a φᶜ, refuse a φ} :=
  question_singleton_update _ (not_subset_root_coherent _) {refuse a φ}

/-- *No* to a question with high negation lands on the state that keeps the refusal. -/
theorem root_highNegationQuestion_update_no [Nonempty W] :
    ((highNegationQuestion (coherent A W) a φ).update {commit a φᶜ}).root =
      {commit a φᶜ, refuse a φ} := by
  rw [highNegationQuestion_update_no, root_update_coherent coherent_commit_compl_refuse]

/-- *No* to a question with high negation is admitted (p. 340). -/
theorem admits_highNegationQuestion_no [Nonempty W] :
    Admits (highNegationQuestion (coherent A W) a φ) {commit a φᶜ} :=
  (admits_question_singleton_iff _ (not_subset_root_coherent _) {refuse a φ}).2
    (admits_coherent_iff.2 coherent_commit_compl_refuse)

/-- *Yes* to a question with high negation needs a prior rejection (p. 340). -/
theorem not_admits_highNegationQuestion_yes :
    ¬ Admits (highNegationQuestion (coherent A W) a φ) {commit a φ} := fun h ↦
  have hc := admits_coherent_iff.1 <|
    (admits_question_singleton_iff _ (not_subset_root_coherent _) {refuse a φ}).1 h
  (hc a φ (Or.inl rfl)).2 (Or.inr rfl)

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
def start (A W : Type*) : Development (State A W) := ⟨coherent A W, []⟩

/-- Rejecting a monopolar question and answering *no* leaves the addressee committed to `¬φ`
and to nothing else (28b). -/
theorem root_reject_monopolarQuestion_no {A W : Type*} [Nonempty W] (a : A) (φ : Set W) :
    (((start A W).perform (monopolarQuestion · a φ)).reject.perform
      (·.assert a φᶜ)).current.root = {commit a φᶜ} :=
  root_update_coherent coherent_commit

/-! ### The issue a space raises -/

section Issue

variable {A W : Type*} (C : Space (State A W))

/-- The continuations of a space are its states other than the root. -/
def continuations : Set (State A W) := ↑C \ {C.root}

open scoped Classical in
/-- The issue a space raises is settled by the information states inside some continuation's
context set, or inside the root's when the space has no continuations. -/
noncomputable def toIssue : Question W :=
  if continuations C = ∅ then Question.ofSet (contextSet C.root)
  else ⨆ c ∈ continuations C, Question.ofSet (contextSet c)

noncomputable instance : Discourse.HasIssue (Space (State A W)) W := ⟨toIssue⟩

theorem mem_toIssue_iff {i : Set W} :
    i ∈ toIssue C ↔
      (continuations C = ∅ ∧ i ⊆ contextSet C.root) ∨ ∃ c ∈ continuations C, i ⊆ contextSet c := by
  unfold toIssue
  split_ifs with h
  · simp [h, Question.mem_ofSet]
  · simp only [h, false_and, false_or, Question.mem_biSup_iff, Question.mem_ofSet]
    refine ⟨fun h' ↦ h'.elim (fun e ↦ ?_) id, Or.inr⟩
    obtain ⟨c, hc⟩ := Set.nonempty_iff_ne_empty.2 h
    exact ⟨c, hc, e ▸ Set.empty_subset _⟩

end Issue

/-! ### A two-world model -/

/-- In one world it is raining and in the other it is not. -/
inductive Weather
  | rain
  | noRain
  deriving DecidableEq

instance : Nonempty Weather := ⟨.rain⟩

/-- It is raining. -/
def raining : Set Weather := {.rain}

/-- The initial commitment space has every coherent state. -/
def C₀ : Space (State Discourse.Role Weather) := coherent _ _

/-- An assertion narrows the root at once, while the Table of [farkas-bruce-2010] leaves the
common ground as it was until the proposal is accepted. -/
theorem assert_contextSet_vs_farkasBruce_cg :
    contextSet (C₀.assert .speaker raining).root = raining ∧
      ((Table.empty : Table Discourse.Role Weather).assert .speaker raining).commonGround = ⊤ :=
  ⟨(congrArg contextSet (root_update_coherent coherent_commit)).trans
    (contextSet_singleton_commit _ _), rfl⟩

theorem monopolar_continuation_subset {φ : Set Weather} {c : State Discourse.Role Weather}
    (hc : c ∈ continuations (monopolarQuestion C₀ .addressee φ)) : contextSet c ⊆ φ := by
  obtain ⟨hc, hne⟩ := hc
  rcases (mem_monopolarQuestion ..).1 hc with rfl | ⟨-, hc⟩
  · exact absurd rfl hne
  · exact contextSet_subset_of_mem_contents _ ⟨_, ⟨hc, rfl⟩, rfl⟩

theorem singleton_commit_mem_continuations (φ : Set Weather) :
    {commit .addressee φ} ∈ continuations (monopolarQuestion C₀ .addressee φ) :=
  ⟨(mem_monopolarQuestion ..).2 (Or.inr ⟨coherent_commit, rfl⟩),
    (Set.singleton_nonempty _).ne_empty⟩

theorem monopolar_not_inquisitive :
    ¬ (toIssue (monopolarQuestion C₀ .addressee raining)).IsInquisitive := by
  intro h
  have hmem : raining ∈ toIssue (monopolarQuestion C₀ .addressee raining) :=
    (mem_toIssue_iff _).2 (Or.inr ⟨_, singleton_commit_mem_continuations raining,
      (contextSet_singleton_commit _ _).ge⟩)
  refine h ?_
  have : (toIssue (monopolarQuestion C₀ .addressee raining)).info = raining := by
    refine Set.Subset.antisymm (Set.sUnion_subset fun i hi ↦ ?_) (Set.subset_sUnion_of_mem hmem)
    rcases (mem_toIssue_iff _).1 hi with ⟨h0, -⟩ | ⟨c, hc, hic⟩
    · exact absurd (singleton_commit_mem_continuations raining) (h0 ▸ Set.notMem_empty _)
    · exact hic.trans (monopolar_continuation_subset hc)
  rw [this]
  exact hmem

theorem bipolar_continuation_subset {c : State Discourse.Role Weather}
    (hc : c ∈ continuations (bipolarQuestion C₀ .addressee raining)) :
    contextSet c ⊆ raining ∨ contextSet c ⊆ rainingᶜ :=
  ((coe_bipolarQuestion ..).le hc.1).imp
    (fun h ↦ monopolar_continuation_subset ⟨h, hc.2⟩)
    (fun h ↦ monopolar_continuation_subset ⟨h, hc.2⟩)

theorem bipolar_inquisitive :
    (toIssue (bipolarQuestion C₀ .addressee raining)).IsInquisitive := by
  intro hinfo
  have hy : {commit .addressee raining} ∈
      continuations (bipolarQuestion C₀ .addressee raining) :=
    ⟨(coe_bipolarQuestion ..).ge (Or.inl (singleton_commit_mem_continuations raining).1),
      (Set.singleton_nonempty _).ne_empty⟩
  have hn : {commit .addressee rainingᶜ} ∈
      continuations (bipolarQuestion C₀ .addressee raining) :=
    ⟨(coe_bipolarQuestion ..).ge (Or.inr (singleton_commit_mem_continuations rainingᶜ).1),
      (Set.singleton_nonempty _).ne_empty⟩
  have hyes : raining ∈ toIssue (bipolarQuestion C₀ .addressee raining) :=
    (mem_toIssue_iff _).2 (Or.inr ⟨_, hy, (contextSet_singleton_commit _ _).ge⟩)
  have hno : rainingᶜ ∈ toIssue (bipolarQuestion C₀ .addressee raining) :=
    (mem_toIssue_iff _).2 (Or.inr ⟨_, hn, (contextSet_singleton_commit _ _).ge⟩)
  have hrain : Weather.rain ∈ (toIssue (bipolarQuestion C₀ .addressee raining)).info :=
    Set.subset_sUnion_of_mem hyes rfl
  have hnoRain : Weather.noRain ∈ (toIssue (bipolarQuestion C₀ .addressee raining)).info :=
    Set.subset_sUnion_of_mem hno fun h ↦ Weather.noConfusion h
  rcases (mem_toIssue_iff _).1 hinfo with ⟨h0, -⟩ | ⟨c, hc, hsub⟩
  · exact absurd hy (h0 ▸ Set.notMem_empty _)
  · rcases bipolar_continuation_subset hc with h | h
    · exact Weather.noConfusion (h (hsub hnoRain))
    · exact h (hsub hrain) rfl

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

/-- Licensing reproduces Table 1. With evidence for `φ` only the question without negation is
licensed, read monopolar; with neutral evidence the question without negation, read bipolar, and
the high-negation question; with evidence against `φ` both negated questions and not the
question without negation. -/
theorem table1 (e : SignType) :
    (Licensed (evidence raining e) raining none ↔ e ≠ -1) ∧
      (Licensed (evidence raining e) raining (some .negative) ↔ e = -1) ∧
      (Licensed (evidence raining e) raining (some .positive) ↔ e ≠ 1) := by
  cases e <;> simp [Licensed, MonopolarLicensed, BipolarLicensed,
    HighNegationLicensed, evidence, raining_ne_empty, raining_ne_univ]

theorem licensed_iff_felicitous (r : Option Polarity) (e : SignType) :
    Licensed (evidence raining e) raining r ↔ BuringGunlogson2000.Felicitous r e := by
  have h : ∀ e : SignType, (e ≠ -1 ↔ BuringGunlogson2000.Felicitous none e) ∧
      (e = -1 ↔ BuringGunlogson2000.Felicitous (some .negative) e) ∧
      (e ≠ 1 ↔ BuringGunlogson2000.Felicitous (some .positive) e) := by decide
  rcases r with _ | _ | _
  exacts [(table1 e).1.trans (h e).1, (table1 e).2.2.trans (h e).2.2,
    (table1 e).2.1.trans (h e).2.1]

/-! ### Question tags (44), (45) -/

section Tags

variable {W : Type*} (C : Space (State Discourse.Role W)) (φ : Set W)

/-- A matching tag conjoins the assertion with the monopolar question of the same content
(44). -/
def matchingTag : Set (State Discourse.Role W) :=
  ↑(C.assert .speaker φ) ∩ ↑(monopolarQuestion C .addressee φ)

/-- A reverse tag disjoins the assertion with the monopolar question of the negation (45). -/
def reverseTag : Set (State Discourse.Role W) :=
  ↑(C.assert .speaker φ) ∪ ↑(monopolarQuestion C .addressee φᶜ)

/-- A matching tag is the single act committing both participants (p. 342). -/
theorem matchingTag_eq (hk : commit .speaker φ ∉ C.root)
    (h : Admits C {commit .addressee φ, commit .speaker φ}) :
    matchingTag C φ = ↑(C.update {commit .addressee φ, commit .speaker φ}) := by
  rw [C.coe_update_of_root_mem h]
  ext d
  simp only [matchingTag, Set.mem_inter_iff, SetLike.mem_coe, mem_monopolarQuestion, Set.mem_Ici]
  constructor
  · rintro ⟨hs, rfl | ⟨hd, ha⟩⟩
    · exact absurd ((C.root_mem_assert_iff _ _ _).1 hs) hk
    · have hks : commit .speaker φ ∈ d :=
        ((C.mem_assert _ _ _).1 hs).elim (fun e ↦ e ▸ C.commit_mem_root_assert _ _ _) And.right
      exact ⟨hd, Set.insert_subset ha (Set.singleton_subset_iff.2 hks)⟩
  · rintro ⟨hd, hsub⟩
    exact ⟨(C.mem_assert _ _ _).2 (Or.inr ⟨hd, hsub (Or.inr rfl)⟩),
      Or.inr ⟨hd, hsub (Or.inl rfl)⟩⟩

theorem reverseTag_eq (h : Admits C {commit .speaker φ}) :
    reverseTag C φ = ↑(question C {{commit .speaker φ}, {commit .addressee φᶜ}}) := by
  ext d
  constructor
  · rintro (hd | hd)
    · exact Or.inr ⟨C.update_le h hd, _, Or.inl rfl, Set.singleton_subset_iff.2 <|
        ((C.mem_assert _ _ _).1 hd).elim (fun e ↦ e ▸ C.commit_mem_root_assert _ _ _) And.right⟩
    · exact ((mem_monopolarQuestion ..).1 hd).imp id fun hd ↦
        ⟨hd.1, _, Or.inr rfl, Set.singleton_subset_iff.2 hd.2⟩
  · rintro (rfl | ⟨hd, q, (rfl | rfl), hq⟩)
    · exact Or.inr (Space.root_mem _)
    · exact Or.inl ((C.mem_assert _ _ _).2 (Or.inr ⟨hd, hq rfl⟩))
    · exact Or.inr ((mem_monopolarQuestion ..).2 (Or.inr ⟨hd, hq rfl⟩))

theorem isLeast_reverseTag : IsLeast (reverseTag C φ) C.root :=
  ⟨Or.inr (Space.root_mem _), by
    rintro d (hd | hd)
    · exact (C.root_le_root_update _).trans ((C.assert .speaker φ).root_le hd)
    · exact (monopolarQuestion C .addressee φᶜ).root_le hd⟩

/-- When the addressee contradicts a plain assertion, the speaker is still committed
(p. 342). -/
theorem commit_speaker_mem_root_assert_assert (ψ : Set W) :
    commit .speaker φ ∈ ((C.assert .speaker φ).assert .addressee ψ).root :=
  (C.assert .speaker φ).root_le_root_update _ (C.commit_mem_root_assert _ _ _)

variable (W)

theorem isLeast_matchingTag [Nonempty W] :
    IsLeast (matchingTag (coherent Discourse.Role W) φ)
      {commit .addressee φ, commit .speaker φ} := by
  rw [matchingTag_eq _ φ (Set.notMem_empty _) (admits_coherent_iff.2 coherent_commit_commit)]
  have h := ((coherent Discourse.Role W).update {commit .addressee φ, commit .speaker φ}).isLeast
  rwa [root_update_coherent coherent_commit_commit] at h

/-- After a matching tag *no* needs a prior rejection (p. 342). -/
theorem not_admits_matchingTag_no [Nonempty W] :
    ¬ Admits ((coherent Discourse.Role W).update {commit .addressee φ, commit .speaker φ})
      {commit .addressee φᶜ} := fun h ↦
  have hc := admits_coherent_iff.1 <|
    (admits_update_iff _ (admits_coherent_iff.2 coherent_commit_commit)).1 h
  (hc .addressee φ (Or.inr (Or.inl rfl))).1 (Or.inl rfl)

/-- Rejecting an assertion with a matching tag and answering *no* leaves only the addressee's
commitment, the speaker's being rejected with the tag (p. 342). -/
theorem root_reject_matchingTag_no [Nonempty W] :
    (((start Discourse.Role W).perform
        (·.update {commit .addressee φ, commit .speaker φ})).reject.perform
      (·.assert .addressee φᶜ)).current.root = {commit .addressee φᶜ} :=
  root_update_coherent coherent_commit

theorem admits_assert_no [Nonempty W] :
    Admits ((coherent Discourse.Role W).assert .speaker φ) {commit .addressee φᶜ} :=
  (admits_update_iff _ (admits_coherent_iff.2 coherent_commit)).2
    (admits_coherent_iff.2 (coherent_commit_compl_commit (by decide)))

/-- After a reverse tag, the addressee's commitment to `φ` brings the speaker's with it
(p. 343). -/
theorem root_reverseTag_update_yes [Nonempty W] :
    ((question (coherent Discourse.Role W)
        {{commit .speaker φ}, {commit .addressee φᶜ}}).update {commit .addressee φ}).root =
      {commit .addressee φ, commit .speaker φ} := by
  have h : ∀ q ∈ ({{commit .speaker φ}, {commit .addressee φᶜ}} : Set (State Discourse.Role W)),
      q ≠ {commit .speaker φ} → ∀ d ∈ coherent Discourse.Role W,
        ¬ {commit .addressee φ} ∪ q ⊆ d := by
    rintro q (rfl | rfl) hne d hd hsub
    exacts [absurd rfl hne, (hd .addressee φ (hsub (Or.inl rfl))).1 (hsub (Or.inr rfl))]
  rw [question_update_of_forall _ (not_subset_root_coherent _) (Or.inl rfl) h]
  exact root_update_coherent coherent_commit_commit

/-- After a reverse tag, the addressee's *no* leaves the speaker uncommitted (p. 343). -/
theorem root_reverseTag_update_no [Nonempty W] :
    ((question (coherent Discourse.Role W)
        {{commit .speaker φ}, {commit .addressee φᶜ}}).update {commit .addressee φᶜ}).root =
      {commit .addressee φᶜ} := by
  rw [question_update_of_mem (coherent Discourse.Role W)
    (P := {{commit .speaker φ}, {commit .addressee φᶜ}}) (Or.inr rfl)]
  exact root_update_coherent coherent_commit

end Tags

end Krifka2015
