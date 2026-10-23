/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Logic.Function.DependsOn`.
-/
module

public import Mathlib.Logic.Function.DependsOn
public import Mathlib.Data.Set.Finite.Lattice

/-!
# The least set a function depends on

Lemmas on mathlib's `DependsOn`. The sets a function depends on are closed under binary
intersection, so a function that depends on a finite set depends on a least one: the coordinates
it does not ignore, those at which changing the argument alone can change the value.

Closure under infinite intersections fails. A function of a set of natural numbers that says
whether the set is infinite depends exactly on the cofinite sets, and they have no least element.

## Main results

* `DependsOn.inter`: a function that depends on `s` and on `t` depends on `s ∩ t`.
* `dependsOn_compl_singleton_iff`: a function ignores a coordinate when updating it never changes
  the value.
* `isLeast_dependsOn`: a function that depends on a finite set depends on the coordinates it does
  not ignore, and these lie in every set it depends on.
-/

@[expose] public section

open Function Set

variable {ι : Type*} {α : ι → Type*} {β : Type*} {f : (Π i, α i) → β} {s t : Set ι}

/-- A function that depends on `s` and on `t` depends on `s ∩ t`. -/
theorem DependsOn.inter (hs : DependsOn f s) (ht : DependsOn f t) : DependsOn f (s ∩ t) := by
  classical
  intro x y h
  refine (hs (y := fun i ↦ if i ∈ s then x i else y i) fun i hi ↦ by simp [hi]).trans
    (ht fun i hi ↦ ?_)
  by_cases his : i ∈ s
  · simp [his, h i ⟨his, hi⟩]
  · simp [his]

theorem DependsOn.biInter {κ : Type*} {u : Set κ} (hu : u.Finite) {t : κ → Set ι}
    (h : ∀ k ∈ u, DependsOn f (t k)) : DependsOn f (⋂ k ∈ u, t k) := by
  induction u, hu using Set.Finite.induction_on with
  | empty => simpa using dependsOn_univ f
  | insert _ _ ih =>
    rw [biInter_insert]
    exact (h _ (mem_insert _ _)).inter (ih fun k hk ↦ h k (mem_insert_of_mem _ hk))

/-- A function ignores the coordinate `i` when updating it never changes the value. -/
theorem dependsOn_compl_singleton_iff [DecidableEq ι] {i : ι} :
    DependsOn f {i}ᶜ ↔ ∀ x (a : α i), f (update x i a) = f x := by
  refine ⟨fun h x a ↦ h fun j hj ↦ update_of_ne hj a x, fun h x y hxy ↦ ?_⟩
  rw [← h x (y i)]
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [update_of_ne hj, hxy j hj]

/-- A function that depends on a finite set depends on the coordinates it does not ignore, and
every set it depends on contains them. -/
theorem isLeast_dependsOn (hs : s.Finite) (hf : DependsOn f s) :
    IsLeast {t | DependsOn f t} {i | ¬ DependsOn f {i}ᶜ} := by
  refine ⟨(hf.inter (DependsOn.biInter (hs.inter_of_left {i | DependsOn f {i}ᶜ})
    fun i hi ↦ hi.2)).mono ?_, fun t ht i hi ↦ by_contra fun hit ↦ hi (ht.mono ?_)⟩
  · rintro i ⟨his, hi⟩ hdep
    exact (mem_iInter₂.1 hi i ⟨his, hdep⟩) rfl
  · simpa using hit

theorem isLeast_dependsOn_of_finite [Finite ι] (f : (Π i, α i) → β) :
    IsLeast {t | DependsOn f t} {i | ¬ DependsOn f {i}ᶜ} :=
  isLeast_dependsOn finite_univ (dependsOn_univ f)
