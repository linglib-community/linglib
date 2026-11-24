module

public import Mathlib.Data.Set.Sups
public import Mathlib.Order.UpperLower.Closure
public import Mathlib.Order.BooleanAlgebra.Basic
public import Linglib.Logic.Truthmaker.Bilateral

/-!
# Answerhood

A question determines a set `A` of propositions, its instantiations, and the notions of
answerhood are closures of that set. A proposition resolves the question when it entails an
instantiation, `p ∈ lowerClosure A`. A simple answer is an instantiation or the negation of one,
and a proposition is about the question when it entails a disjunction of two simple answers. We
define both for propositions in any type with an entailment order, a disjunction and a negation,
so that the choice of the algebra of propositions is a parameter.

Resolving, entailing a simple answer and being about the question form a chain in every algebra.
In a Boolean algebra a simple answer and its negation exhaust the cases, so every proposition is
about every question that has an instantiation. For bilateral truthmaker propositions under the
order of the product bilattice this fails: an atom is not about the question whose only
instantiation is another atom, although the excluded middle of that atom is true at every world.

## Main definitions

* `Answerhood.simpleAnswers`: the instantiations of a question and their negations.
* `Answerhood.about`: the propositions that entail a disjunction of two simple answers.

## Main results

* `Answerhood.lowerClosure_le_lowerClosure_simpleAnswers`,
  `Answerhood.lowerClosure_simpleAnswers_le_about`: resolving implies entailing a simple answer,
  which implies aboutness.
* `Answerhood.about_eq_top`: in a Boolean algebra every proposition is about every question that
  has an instantiation.
* `Answerhood.atom_notMem_about_singleton_atom`: among bilateral truthmaker propositions an atom
  is not about the question whose only instantiation is a different atom.

## Implementation notes

The disjunction is the join of the entailment order. Fine's disjunction of bilateral propositions
has the verifiers of that join and fuses the falsifiers where the join intersects them.

## References

* [ginzburg-2012]
* [fine-2017a]
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

variable [SemilatticeSup P] [Compl P] {A B : Set P} {p : P}

/-- The propositions about a question are those that entail a disjunction of two simple answers
to it. -/
def about (A : Set P) : LowerSet P :=
  lowerClosure (simpleAnswers A ⊻ simpleAnswers A)

theorem mem_about : p ∈ about A ↔
    ∃ a ∈ simpleAnswers A, ∃ b ∈ simpleAnswers A, p ≤ a ⊔ b := by
  simp only [about, mem_lowerClosure, Set.mem_sups]
  exact ⟨fun ⟨_, ⟨a, ha, b, hb, h⟩, hp⟩ ↦ ⟨a, ha, b, hb, h ▸ hp⟩,
    fun ⟨a, ha, b, hb, hp⟩ ↦ ⟨_, ⟨a, ha, b, hb, rfl⟩, hp⟩⟩

@[gcongr]
theorem about_mono (h : A ⊆ B) : about A ≤ about B :=
  lowerClosure_mono (Set.sups_subset (simpleAnswers_mono h) (simpleAnswers_mono h))

/-- A proposition that resolves a question entails a simple answer to it. -/
theorem lowerClosure_le_lowerClosure_simpleAnswers :
    lowerClosure A ≤ lowerClosure (simpleAnswers A) :=
  lowerClosure_mono subset_simpleAnswers

/-- A proposition that entails a simple answer to a question is about it. -/
theorem lowerClosure_simpleAnswers_le_about : lowerClosure (simpleAnswers A) ≤ about A :=
  lowerClosure_mono fun a ha ↦ Set.mem_sups.mpr ⟨a, ha, a, ha, sup_idem a⟩

@[simp] theorem about_empty : about (∅ : Set P) = ⊥ := by
  simp [about]

end SemilatticeSup

/-- In a Boolean algebra every proposition is about every question that has an instantiation. -/
theorem about_eq_top [BooleanAlgebra P] {A : Set P} (h : A.Nonempty) : about A = ⊤ := by
  obtain ⟨a, ha⟩ := h
  refine top_unique fun p _ ↦ mem_about.mpr
    ⟨a, subset_simpleAnswers ha, aᶜ, compl_mem_simpleAnswers ha, ?_⟩
  simp

theorem about_eq_top_iff [BooleanAlgebra P] [Nonempty P] {A : Set P} :
    about A = ⊤ ↔ A.Nonempty := by
  refine ⟨fun h ↦ ?_, about_eq_top⟩
  by_contra hA
  obtain ⟨p⟩ := ‹Nonempty P›
  have hp : p ∈ about A := h ▸ LowerSet.mem_top
  simp [Set.not_nonempty_iff_eq_empty.mp hA] at hp

/-! ### Bilateral truthmaker propositions -/

section Truthmaker

open Truthmaker.Canonical

variable {α : Type*} {a b : α}

/-- An atom is about the question whose only instantiation it is. -/
theorem atom_mem_about_singleton_atom : atom a ∈ about {atom a} :=
  lowerClosure_simpleAnswers_le_about (subset_lowerClosure (subset_simpleAnswers rfl))

/-- Among bilateral truthmaker propositions, an atom is not about the question whose only
instantiation is a different atom. -/
theorem atom_notMem_about_singleton_atom (h : b ≠ a) : atom b ∉ about {atom a} := by
  intro hmem
  obtain ⟨x, hx, y, hy, hle⟩ := mem_about.mp hmem
  have key : ∀ z ∈ simpleAnswers {atom a}, ∀ s ∈ z.pro, s = {(a, true)} ∨ s = {(a, false)} := by
    rintro z (rfl | ⟨_, rfl, rfl⟩) s hs
    · exact .inl hs
    · exact .inr hs
  have hb : ({(b, true)} : Set (α × Bool)) ∈ (x ⊔ y).pro :=
    (Bilattice.Product.le_def.mp hle).1 rfl
  rcases hb with hb | hb
  · rcases key x hx _ hb with e | e <;> simp [Set.singleton_eq_singleton_iff, h] at e
  · rcases key y hy _ hb with e | e <;> simp [Set.singleton_eq_singleton_iff, h] at e

end Truthmaker

end Answerhood
