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
* `Set.DependsOn`: a function of a set depends on `s` when its value at a set is its value at the
  part of the set in `s`. This is [dependence of the function of the set's
  predicate](##Set.dependsOn_iff_dependsOn_ofPred), stated without taking a set for a predicate.
-/

public section

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

/-! ### Functions of a set -/

section Set

variable {ι κ β : Type*} {f : Set ι → β} {s t : Set ι}

/-- A function of a set depends on `s` if its value at `X` is its value at `s ∩ X`, the part of
`X` in `s`. -/
@[expose] protected def Set.DependsOn (f : Set ι → β) (s : Set ι) : Prop :=
  ∀ X, f (s ∩ X) = f X

namespace Set.DependsOn

theorem congr (hf : Set.DependsOn f s) {X Y : Set ι} (h : s ∩ X = s ∩ Y) : f X = f Y := by
  rw [← hf X, h, hf Y]

theorem mono (hst : s ⊆ t) (hf : Set.DependsOn f s) : Set.DependsOn f t := fun X ↦ by
  rw [← hf (t ∩ X), ← inter_assoc, inter_eq_left.2 hst, hf X]

/-- A function of a set that depends on `s` and on `t` depends on `s ∩ t`. -/
theorem inter (hs : Set.DependsOn f s) (ht : Set.DependsOn f t) : Set.DependsOn f (s ∩ t) :=
  fun X ↦ by rw [inter_assoc, hs, ht]

/-- A function of the preimage of a set depends on the image of what the function depends on. -/
theorem comp_preimage {g : Set κ → β} {u : Set κ} (hg : Set.DependsOn g u) (φ : κ → ι) :
    Set.DependsOn (fun d ↦ g (φ ⁻¹' d)) (φ '' u) :=
  fun d ↦ hg.congr (by ext k; simp only [mem_inter_iff, mem_preimage, mem_image]; grind)

end Set.DependsOn

theorem Set.dependsOn_univ (f : Set ι → β) : Set.DependsOn f univ := fun X ↦ by rw [univ_inter]

/-- A function of a set depends on `s` iff it agrees on two sets with the same members in `s`. -/
theorem Set.dependsOn_iff_forall_mem :
    Set.DependsOn f s ↔ ∀ ⦃X Y : Set ι⦄, (∀ i ∈ s, i ∈ X ↔ i ∈ Y) → f X = f Y :=
  ⟨fun h X Y hXY ↦ h.congr (by ext i; simpa using fun hi ↦ hXY i hi),
    fun h X ↦ h fun i hi ↦ by simp [hi]⟩

/-- A function of a set depends on `s` iff, as a function of the predicate of the set, it depends
on `s`. -/
theorem Set.dependsOn_iff_dependsOn_ofPred :
    Set.DependsOn f s ↔ _root_.DependsOn (fun p : ι → Prop ↦ f {i | p i}) s := by
  rw [Set.dependsOn_iff_forall_mem]
  refine ⟨fun h p q hpq ↦ h fun i hi ↦ by simp [hpq i hi], fun h X Y hXY ↦ ?_⟩
  simpa using h (x := (· ∈ X)) (y := (· ∈ Y)) fun i hi ↦ propext (hXY i hi)

/-- A function of a set ignores `i` when removing it never changes the value. -/
theorem Set.dependsOn_compl_singleton_iff {i : ι} :
    Set.DependsOn f {i}ᶜ ↔ ∀ X, f (X \ {i}) = f X := by
  simp only [Set.DependsOn, inter_comm _ᶜ, sdiff_eq]

/-- A function of a set that depends on a finite set depends on the elements it does not ignore,
and every set it depends on contains them. -/
theorem Set.isLeast_dependsOn (hs : s.Finite) (hf : Set.DependsOn f s) :
    IsLeast {t | Set.DependsOn f t} {i | ¬ Set.DependsOn f {i}ᶜ} := by
  simp only [Set.dependsOn_iff_dependsOn_ofPred] at hf ⊢
  exact _root_.isLeast_dependsOn hs hf

end Set
