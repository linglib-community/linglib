module

public import Linglib.Semantics.Questions.Hamblin
public import Linglib.Semantics.Questions.Resolution
public import Linglib.Data.Examples.Belnap1982

/-!
# Belnap (1982): Questions and Answers in Montague Grammar

Belnap's answerhood essay: answers are propositions, a question offers a
set of possible answers, and two theses organize the field. The **Unique
Answer Fallacy** (§2.2): it is fallacious to build into the foundations —
as Tichy's answer-functions and [karttunen-1977]'s jointly-constituted
denotations do — that every question has exactly one complete true
answer; *Where is a place at which I can get gas on a Sunday?* has
several, each full, complete, and true. The **Distributivity Principle
and Test** (§2.4): to know an indirect question is to know some answer to
it, so if *Sally knows that P but Sally doesn't know IQ* is consistent, P
is not an answer to IQ — a necessary condition only, since P may entail
an answer without being one. Formalized on the Hamblin-style reading
Belnap prefers ([hamblin-1973b]): the possible answers are the maximal
alternatives `Question.alt`, and an information state knows Q at w when
it settles an alternative true at w.

## Main statements

* `unique_answer_fallacy`: a mention-some `which` question with two
  distinct complete true answers at a single world;
  `joint_answer_not_an_answer`: the jointly-constituted [karttunen-1977]
  denotation is not itself among the possible answers there.
* `distributivity_test`: if some information state entails P without
  knowing Q at w, then P is not a true answer to Q at w (p. 176–177).
* `test_only_necessary`: the converse fails — the joint answer entails an
  answer, so knowing it always yields knowledge of Q, yet it is not an
  answer (§2.4's caveat).

## References

* [belnap-1982]: Questions and Answers in Montague Grammar.
* [karttunen-1977]: Syntax and semantics of questions.
* [hamblin-1973b]: Questions in Montague English.
-/

@[expose] public section

namespace Belnap1982

open Question

variable {W : Type*}

/-- An information state σ knows question Q at world w when it settles
some alternative true at w — the Distributivity Principle (§2.4), "to
know IQ is to know some answer to the question as to IQ", as a semantic
rendering of *know* + indirect question. Dropping the truth conjunct
gives resolution of the question, `σ ∈ Q`. -/
def KnowsAnswer (σ : Set W) (Q : Question W) (w : W) : Prop :=
  ∃ p ∈ alt Q, w ∈ p ∧ σ ⊆ p

/-- Knowing an answer resolves the question. -/
theorem KnowsAnswer.resolves {σ : Set W} {Q : Question W} {w : W}
    (h : KnowsAnswer σ Q w) : σ ∈ Q :=
  let ⟨p, hp, _, hσ⟩ := h
  mem_of_exists_alt_subset ⟨p, hp, hσ⟩

/-! ### The Unique Answer Fallacy (§2.2)

Tichy makes the question a function delivering one entity per world;
Karttunen has it denote "the set of propositions which in that situation
jointly constitute a complete and true answer" — on both, uniqueness is
built in, and neither can state a question that asks for examples. On the
Hamblin/Bennett reading the members of the set are each answers, and
mention-some questions have several true ones at once. -/

/-- Station A is open in worlds 0 and 1. -/
def stationA : Set (Fin 3) := {w | w.val ≤ 1}

/-- Station B is open in worlds 0 and 2. -/
def stationB : Set (Fin 3) := {w | w.val ≠ 1}

instance : DecidablePred (· ∈ stationA) :=
  fun w => inferInstanceAs (Decidable (w.val ≤ 1))

instance : DecidablePred (· ∈ stationB) :=
  fun w => inferInstanceAs (Decidable (w.val ≠ 1))

/-- *Where is a place at which I can get gas on a Sunday?* (p. 172) as a
mention-some `which` over the two stations. -/
def gasQuestion : Question (Fin 3) :=
  which Set.univ (fun b : Bool => if b then stationA else stationB)

theorem stationA_mem_alt : stationA ∈ alt gasQuestion :=
  mem_alt_which_of_maximal true trivial
    ⟨0, show (0 : Fin 3) ∈ stationA by decide⟩ fun e' _ hsub => by
    cases e' with
    | false =>
        exact absurd (hsub (show (1 : Fin 3) ∈ stationA by decide))
          (show (1 : Fin 3) ∉ stationB by decide)
    | true => rfl

theorem stationB_mem_alt : stationB ∈ alt gasQuestion :=
  mem_alt_which_of_maximal false trivial
    ⟨0, show (0 : Fin 3) ∈ stationB by decide⟩ fun e' _ hsub => by
    cases e' with
    | false => rfl
    | true =>
        exact absurd (hsub (show (2 : Fin 3) ∈ stationB by decide))
          (show (2 : Fin 3) ∉ stationA by decide)

/-- **The Unique Answer Fallacy** (§2.2): at world 0 both stations are
open, and each is a full, complete, true answer — two distinct complete
true answers to one question at one world. -/
theorem unique_answer_fallacy :
    ∃ p q : Set (Fin 3), p ∈ alt gasQuestion ∧ q ∈ alt gasQuestion ∧
      p ≠ q ∧ (0 : Fin 3) ∈ p ∧ (0 : Fin 3) ∈ q :=
  ⟨stationA, stationB, stationA_mem_alt, stationB_mem_alt,
    fun h => absurd (h ▸ show (1 : Fin 3) ∈ stationA by decide)
      (show (1 : Fin 3) ∉ stationB by decide),
    show (0 : Fin 3) ∈ stationA by decide,
    show (0 : Fin 3) ∈ stationB by decide⟩

/-- The [karttunen-1977] denotation — the true propositions taken
*jointly* — is here the intersection of the two stations' propositions,
and it is not itself among the question's possible answers: uniqueness is
an artifact of taking the set itself as the answer. -/
theorem joint_answer_not_an_answer :
    stationA ∩ stationB ∉ alt gasQuestion := fun h => by
  have hA : stationA ∈ gasQuestion :=
    mem_which.mpr (Or.inr ⟨true, trivial, subset_rfl⟩)
  have heq := h.2 stationA hA Set.inter_subset_left
  have h1 : (1 : Fin 3) ∈ stationA := by decide
  rw [← heq] at h1
  exact absurd h1.2 (show (1 : Fin 3) ∉ stationB by decide)

/-! ### The Distributivity Test (§2.4, pp. 176–177) -/

/-- **The Distributivity Test**: "For any P and IQ, let the following
inference fail: Sally knows that P, therefore Sally knows IQ. Then P is
not an answer to IQ." A failing instance is an information state that
entails P without knowing Q — its existence rules P out as a true
answer. -/
theorem distributivity_test {p : Set W} {Q : Question W} {w : W}
    (h : ∃ σ, σ ⊆ p ∧ ¬KnowsAnswer σ Q w) :
    ¬(p ∈ alt Q ∧ w ∈ p) :=
  fun ⟨hpQ, hwp⟩ =>
    let ⟨_, hσp, hnk⟩ := h
    hnk ⟨p, hpQ, hwp, hσp⟩

/-- The p. 177 example pattern: an irrelevant truth (*China is populous*,
here the trivial proposition) supports no alternative, so the test rules
it out as an answer. -/
theorem irrelevant_fact_not_answer :
    ¬(Set.univ ∈ alt gasQuestion ∧ (0 : Fin 3) ∈ Set.univ) :=
  distributivity_test
    ⟨Set.univ, subset_rfl, fun ⟨p, hp, _, hsub⟩ => by
      rcases mem_which.mp (mem_of_mem_alt hp) with rfl | ⟨e, _, hpe⟩
      · exact hsub (Set.mem_univ 0)
      · cases e with
        | true =>
            exact absurd ((hsub.trans hpe) (Set.mem_univ 2))
              (show (2 : Fin 3) ∉ stationA by decide)
        | false =>
            exact absurd ((hsub.trans hpe) (Set.mem_univ 1))
              (show (1 : Fin 3) ∉ stationB by decide)⟩

/-- The test is necessary, not sufficient: "P might obviously entail some
answer to IQ without itself being such an answer" (p. 177). The joint
answer is the witness: any state that knows it knows the question, yet it
is not an answer. -/
theorem test_only_necessary :
    ∃ p : Set (Fin 3),
      (∀ σ, σ ⊆ p → KnowsAnswer σ gasQuestion 0) ∧ p ∉ alt gasQuestion :=
  ⟨stationA ∩ stationB,
    fun _ hσ => ⟨stationA, stationA_mem_alt,
      show (0 : Fin 3) ∈ stationA by decide,
      hσ.trans Set.inter_subset_left⟩,
    joint_answer_not_an_answer⟩

end Belnap1982
