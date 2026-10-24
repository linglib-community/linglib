module

public import Linglib.Semantics.Questions.Polar
public import Linglib.Semantics.Questions.Constituent
public import Linglib.Semantics.Questions.HamblinSet

/-!
# Karttunen (1977): Syntax and Semantics of Questions

This file formalizes the semantics of [karttunen-1977]: an indirect question denotes the set
of its true answers, the propositions among its alternatives that hold at the world of
evaluation, which is `Question.trueAnswers` of the question's Hamblin set. The yes/no rule
(26) gives *whether p* the alternatives `p` and its negation, so that at each world the
question denotes the singleton of the true one (`trueAnswers_pair`); the WH-quantification
rule (33) gives *which girl sleeps* one alternative per girl, so that the question denotes the
propositions that a sleeping girl sleeps, (34), and the empty set when no girl sleeps
(`trueAnswers_image_eq_empty_iff`), the existential implicature the paper leaves to
[karttunen-peters-1976] in its footnote 13. Since every member of the denotation is true, a
verb like *tell* is veridical with an indirect question where it is not with a *that*-clause,
(19) (`told_true`).

Footnote 11's meaning postulate relates the question-embedding *know* to the
proposition-embedding one: an agent knows a question when she knows each of its true answers,
and knows that it has none when it has none (`Knows`). The first conjunct is the substrate's
`Question.KnowsAnswer`, knowledge of the intersection of the true answers, and the second is
what keeps knowledge of an empty question from being trivial (`knows_iff_of_no_witness`).
Knowing *whether p* is knowing `p` where it holds and its negation elsewhere
(`knows_pair_iff`).

## Implementation notes

The substrate's `Question` is a downward-closed set of propositions whose alternatives
`Question.alt` are its maximal members, so `Question.polar` and `Question.which` reproduce
the paper's alternative sets only up to maximality: the polar identification holds for a
non-trivial proposition (`trueAnswers_alt_polar`) and the wh one when the answers form an
antichain (`trueAnswers_alt_which`). The paper's syntax, the proto-questions and the rules
building questions from them, is not represented, nor are the multiple-wh and scope
ambiguities of its later sections.

## References

* [karttunen-1977]
* [hamblin-1973b], [karttunen-peters-1976]
-/

@[expose] public section

open Question
open scoped SetRel

namespace Karttunen1977

variable {W : Type*} (w : W)

/-! ### The denotation -/

/-- (26): *whether p* has the alternatives `p` and its negation, and at a `p`-world denotes
the singleton of `p`. -/
theorem trueAnswers_pair_of_mem {p : Set W} (h : w ∈ p) : trueAnswers {p, pᶜ} w = {p} := by
  ext q
  simp only [mem_trueAnswers, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨rfl | rfl, hq⟩
    · rfl
    · exact absurd h hq
  · rintro rfl
    exact ⟨Or.inl rfl, h⟩

theorem trueAnswers_pair_of_notMem {p : Set W} (h : w ∉ p) :
    trueAnswers {p, pᶜ} w = {pᶜ} := by
  ext q
  simp only [mem_trueAnswers, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨rfl | rfl, hq⟩
    · exact absurd hq h
    · rfl
  · rintro rfl
    exact ⟨Or.inr rfl, h⟩

theorem trueAnswers_alt_polar {p : Set W} (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    trueAnswers (alt (polar p)) w = trueAnswers {p, pᶜ} w := by
  rw [alt_polar_of_nontrivial hne hnu]

variable {E : Type*} (D : Set E) (P : E → Set W)

/-- (34): *which girl sleeps*, with one alternative per girl, denotes the propositions that a
sleeping girl sleeps. -/
theorem mem_trueAnswers_image_iff (q : Set W) :
    q ∈ trueAnswers (P '' D) w ↔ ∃ e ∈ D, w ∈ P e ∧ q = P e := by
  simp only [mem_trueAnswers, Set.mem_image]
  constructor
  · rintro ⟨⟨e, he, rfl⟩, hw⟩
    exact ⟨e, he, hw, rfl⟩
  · rintro ⟨e, he, hw, rfl⟩
    exact ⟨⟨e, he, rfl⟩, hw⟩

/-- When no girl sleeps, the question denotes the empty set: the existential implicature of
footnote 13 is not part of the denotation. -/
theorem trueAnswers_image_eq_empty_iff :
    trueAnswers (P '' D) w = ∅ ↔ ∀ e ∈ D, w ∉ P e := by
  simp only [Set.eq_empty_iff_forall_notMem, mem_trueAnswers_image_iff, not_exists, not_and]
  exact ⟨fun h e he hw ↦ h (P e) e he hw rfl, fun h _ e he hw _ ↦ h e he hw⟩

theorem trueAnswers_alt_which (hD : D.Nonempty) (hA : IsAntichain (· ⊆ ·) (P '' D)) :
    trueAnswers (alt (which D P)) w = trueAnswers (P '' D) w := by
  rw [alt_which_of_antichain hD hA]

/-- (19): what is told with an indirect question is true, as what is told with a
*that*-clause need not be. -/
theorem told_true {H : Set (Set W)} {p : Set W} (hp : p ∈ trueAnswers H w) : w ∈ p := hp.2

/-! ### Knowing a question (footnote 11) -/

variable (Dox : SetRel W W)

/-- Footnote 11's meaning postulate, with the proposition-embedding *know* read through the
agent's doxastic alternatives `Dox`, says that the agent knows every true answer and, when there
is none, knows that there is none. -/
def Knows (H : Set (Set W)) (w : W) (Dox : SetRel W W) : Prop :=
  KnowsAnswer H w Dox ∧ (trueAnswers H w = ∅ → w ∈ Dox.core {v | trueAnswers H v = ∅})

/-- Knowing *whether p* is knowing `p` at a `p`-world and its negation at another, (31). -/
theorem knows_pair_iff (p : Set W) :
    Knows {p, pᶜ} w Dox ↔ ∀ v, w ~[Dox] v → (v ∈ p ↔ w ∈ p) := by
  by_cases h : w ∈ p
  · simp [Knows, KnowsAnswer, weakAnswer, trueAnswers_pair_of_mem w h, h]
  · simp [Knows, KnowsAnswer, weakAnswer, trueAnswers_pair_of_notMem w h, h]

theorem knows_iff_of_no_witness (h : ∀ e ∈ D, w ∉ P e) :
    Knows (P '' D) w Dox ↔ ∀ v, w ~[Dox] v → ∀ e ∈ D, v ∉ P e := by
  have h0 : trueAnswers (P '' D) w = ∅ := (trueAnswers_image_eq_empty_iff w D P).mpr h
  simp only [Knows, KnowsAnswer, weakAnswer, h0, Set.sInter_empty, Set.mem_univ, imp_true_iff,
    true_and, true_imp_iff, trueAnswers_image_eq_empty_iff, SetRel.mem_core,
    Set.mem_ofPred_eq]

end Karttunen1977
