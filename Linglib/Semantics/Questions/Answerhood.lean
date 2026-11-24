module

public import Mathlib.Data.Set.Sups
public import Mathlib.Order.UpperLower.Closure
public import Mathlib.Order.BooleanAlgebra.Basic

/-!
# Answerhood

A question determines a set `A` of propositions, its instantiations, and the notions of
answerhood are closures of that set. A proposition resolves the question when it entails an
instantiation, `p ∈ lowerClosure A`. A simple answer is an instantiation or the negation of one,
and a proposition is about the question when it entails a disjunction of two simple answers.

The negation of an instantiation and the entailment order need not live on one type: a theory
may negate structured propositions and compare what they denote. So `simpleAnswers` is defined
for any type with a negation, and `about D` for any set `D` of elements of a join-semilattice.
When both are the operations of one Boolean algebra, a simple answer and its negation exhaust
the cases, and every proposition is about every question that has an instantiation.

## Main definitions

* `Answerhood.simpleAnswers`: the instantiations of a question and their negations.
* `Answerhood.about`: the elements that entail a join of two members of a set.

## Main results

* `Answerhood.lowerClosure_le_about`: entailing a member of a set implies entailing a join of
  two.
* `Answerhood.about_simpleAnswers_eq_top`: in a Boolean algebra every proposition is about every
  question that has an instantiation.

## References

* [ginzburg-2012]
-/

@[expose] public section

open scoped SetFamily

namespace Answerhood

variable {P : Type*}

section Compl

variable [Compl P] {A B : Set P} {p : P}

/-- The simple answers to a question are its instantiations and their negations. -/
def simpleAnswers (A : Set P) : Set P :=
  A ∪ compl '' A

theorem subset_simpleAnswers : A ⊆ simpleAnswers A :=
  Set.subset_union_left

theorem compl_mem_simpleAnswers (h : p ∈ A) : pᶜ ∈ simpleAnswers A :=
  .inr ⟨p, h, rfl⟩

theorem mem_simpleAnswers : p ∈ simpleAnswers A ↔ p ∈ A ∨ ∃ a ∈ A, aᶜ = p :=
  Iff.rfl

@[gcongr]
theorem simpleAnswers_mono (h : A ⊆ B) : simpleAnswers A ⊆ simpleAnswers B :=
  Set.union_subset_union h (Set.image_mono h)

@[simp] theorem simpleAnswers_empty : simpleAnswers (∅ : Set P) = ∅ := by
  simp [simpleAnswers]

theorem simpleAnswers_nonempty : (simpleAnswers A).Nonempty ↔ A.Nonempty := by
  simp [simpleAnswers, Set.union_nonempty]

end Compl

section SemilatticeSup

variable [SemilatticeSup P] {D E : Set P} {p : P}

/-- The elements that entail a join of two members of `D`. With `D` the simple answers to a
question, these are the propositions about it. -/
def about (D : Set P) : LowerSet P :=
  lowerClosure (D ⊻ D)

theorem mem_about : p ∈ about D ↔ ∃ a ∈ D, ∃ b ∈ D, p ≤ a ⊔ b := by
  simp only [about, mem_lowerClosure, Set.mem_sups]
  exact ⟨fun ⟨_, ⟨a, ha, b, hb, h⟩, hp⟩ ↦ ⟨a, ha, b, hb, h ▸ hp⟩,
    fun ⟨a, ha, b, hb, hp⟩ ↦ ⟨_, ⟨a, ha, b, hb, rfl⟩, hp⟩⟩

@[gcongr]
theorem about_mono (h : D ⊆ E) : about D ≤ about E :=
  lowerClosure_mono (Set.sups_subset h h)

/-- An element that entails a member of `D` entails a join of two. -/
theorem lowerClosure_le_about : lowerClosure D ≤ about D :=
  lowerClosure_mono fun a ha ↦ Set.mem_sups.mpr ⟨a, ha, a, ha, sup_idem a⟩

@[simp] theorem about_empty : about (∅ : Set P) = ⊥ := by
  simp [about]

end SemilatticeSup

section BooleanAlgebra

variable [BooleanAlgebra P] {A : Set P}

/-- In a Boolean algebra every proposition is about every question that has an instantiation. -/
theorem about_simpleAnswers_eq_top (h : A.Nonempty) : about (simpleAnswers A) = ⊤ := by
  obtain ⟨a, ha⟩ := h
  refine top_unique fun p _ ↦ mem_about.mpr
    ⟨a, subset_simpleAnswers ha, aᶜ, compl_mem_simpleAnswers ha, ?_⟩
  simp

theorem about_simpleAnswers_eq_top_iff [Nonempty P] :
    about (simpleAnswers A) = ⊤ ↔ A.Nonempty := by
  refine ⟨fun h ↦ ?_, about_simpleAnswers_eq_top⟩
  by_contra hA
  obtain ⟨p⟩ := ‹Nonempty P›
  have hp : p ∈ about (simpleAnswers A) := h ▸ LowerSet.mem_top
  simp [Set.not_nonempty_iff_eq_empty.mp hA] at hp

end BooleanAlgebra

end Answerhood
