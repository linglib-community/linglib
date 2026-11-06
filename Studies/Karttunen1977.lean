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
rule (33) gives *which girl sleeps* one alternative per girl, the common noun read at the world
of evaluation, so that the question denotes there the propositions that a sleeping girl sleeps,
(34) (`wh`), and the empty set when no girl sleeps (`wh_eq_empty_iff`), the existential
implicature the paper leaves to
[karttunen-peters-1976] in its footnote 13. Since every member of the denotation is true, a
verb like *tell* is veridical with an indirect question where it is not with a *that*-clause,
(19) (`told_true`).

Footnote 11's meaning postulate relates the question-embedding *know* to the
proposition-embedding one: an agent knows a question when she knows each of its true answers,
and knows that it has none when it has none (`Knows`). The postulate quantifies over question
intensions, and `wh` is not the true answers of one Hamblin set, since its alternatives change
with the girls. On a Hamblin set the first conjunct is the substrate's `Question.KnowsAnswer`,
knowledge of the intersection of the true answers, and the second is what keeps knowledge of an
empty question from being trivial (`knows_wh_iff_of_no_witness`).
Knowing *whether p* is knowing `p` where it holds and its negation elsewhere
(`knows_pair_iff`).

## Implementation notes

The substrate's `Question` is a downward-closed set of propositions whose alternatives
`Question.alt` are its maximal members, so `Question.polar` and `Question.which` reproduce
the paper's alternative sets only up to maximality: the polar identification holds for a
non-trivial proposition (`trueAnswers_alt_polar`) and the wh one when the domain is fixed
across worlds and the answers form an antichain (`trueAnswers_alt_which`). The paper's syntax,
the proto-questions and the rules building questions from them, is not represented, nor are the
multiple-wh and scope ambiguities of its later sections.

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

-- (26)
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

variable {E : Type*} (S P : E → Set W)

/-- The WH-quantification rule (33) makes *which S P* denote at `w` the true ones among the
propositions that `x` is `P`, for each `x` that is `S` at `w`, (34b): the common noun is
extensional, read at the world of evaluation. -/
def wh (w : W) : Set (Set W) := trueAnswers (P '' {x | w ∈ S x}) w

-- (34)
theorem mem_wh_iff {q : Set W} : q ∈ wh S P w ↔ ∃ x, w ∈ S x ∧ w ∈ P x ∧ q = P x := by
  simp only [wh, mem_trueAnswers, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hw⟩
    exact ⟨x, hx, hw, rfl⟩
  · rintro ⟨x, hx, hw, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, hw⟩

theorem wh_eq_image : wh S P w = P '' {x | w ∈ S x ∧ w ∈ P x} := by
  rw [wh, trueAnswers_image]
  rfl

theorem isVeridical_wh : IsVeridical (wh S P) := fun w ↦ isVeridical_trueAnswers _ w

/-- When no girl sleeps, the question denotes the empty set: the existential implicature of
footnote 13 is not part of the denotation. -/
theorem wh_eq_empty_iff : wh S P w = ∅ ↔ ∀ x, w ∈ S x → w ∉ P x := by
  simp only [Set.eq_empty_iff_forall_notMem, mem_wh_iff, not_exists, not_and]
  exact ⟨fun h x hx hw ↦ h (P x) x hx hw rfl, fun h _ x hx hw _ ↦ h x hx hw⟩

variable (D : Set E)

theorem trueAnswers_alt_which (hD : D.Nonempty) (hA : IsAntichain (· ⊆ ·) (P '' D)) :
    trueAnswers (alt (which D P)) w = trueAnswers (P '' D) w := by
  rw [alt_which_of_antichain hD hA]

/-- (19): what is told with an indirect question is true, as what is told with a
*that*-clause need not be. -/
theorem told_true {H : Set (Set W)} {p : Set W} (hp : p ∈ trueAnswers H w) : w ∈ p := hp.2

/-! ### Knowing a question (footnote 11) -/

variable (Dox : SetRel W W)

/-- Footnote 11's meaning postulate, with the proposition-embedding *know* read through the
agent's doxastic alternatives `Dox`, says that the agent knows every answer the question `q` gives
at `w` and, when it gives none, knows that it gives none. -/
def Knows (q : W → Set (Set W)) (w : W) (Dox : SetRel W W) : Prop :=
  w ∈ Dox.core (⋂₀ q w) ∧ (q w = ∅ → w ∈ Dox.core {v | q v = ∅})

/-- Knowing *whether p* is knowing `p` at a `p`-world and its negation at another, (31). -/
theorem knows_pair_iff (p : Set W) :
    Knows (trueAnswers {p, pᶜ}) w Dox ↔ ∀ v, w ~[Dox] v → (v ∈ p ↔ w ∈ p) := by
  by_cases h : w ∈ p
  · simp [Knows, trueAnswers_pair_of_mem w h, h]
  · simp [Knows, trueAnswers_pair_of_notMem w h, h]

/-- When no girl sleeps, knowing which girl sleeps is believing that no girl sleeps, where the
girls are those of each belief world. -/
theorem knows_wh_iff_of_no_witness (h : ∀ x, w ∈ S x → w ∉ P x) :
    Knows (wh S P) w Dox ↔ ∀ v, w ~[Dox] v → ∀ x, v ∈ S x → v ∉ P x := by
  simp only [Knows, (wh_eq_empty_iff w S P).2 h, Set.sInter_empty, SetRel.core_univ,
    Set.mem_univ, true_and, true_imp_iff, SetRel.mem_core, Set.mem_ofPred_eq, wh_eq_empty_iff]

end Karttunen1977
