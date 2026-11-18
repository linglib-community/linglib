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
# Dependence of a function of a set

A function of a set [depends on `s`](##Set.DependsOn) when its value at a set is its value at the
part of the set in `s`. This is [dependence of the function of the set's
predicate](##Set.dependsOn_iff_dependsOn_ofPred) in the sense of mathlib's `DependsOn`, stated
without taking a set for a predicate. A function that depends on a finite set [depends on the
elements it does not ignore](##Set.isLeast_dependsOn), the least set it depends on.
-/

public section

open Function Set

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
  refine ⟨fun X ↦ ?_, fun t ht i hi ↦ by_contra fun hit ↦
    hi (ht.mono (subset_compl_singleton_iff.2 hit))⟩
  have key {D : Set ι} (hD : D.Finite) (h : ∀ i ∈ D, Set.DependsOn f {i}ᶜ) (X : Set ι) :
      f (X \ D) = f X := by
    induction D, hD using Set.Finite.induction_on generalizing X with
    | empty => simp
    | insert _ _ ih =>
      rw [← union_singleton, ← sdiff_sdiff,
        Set.dependsOn_compl_singleton_iff.1 (h _ (mem_insert ..)),
        ih fun i hi ↦ h i (mem_insert_of_mem _ hi)]
  rw [← hf X, ← hf (_ ∩ X), ← key (hs.sdiff (t := {i | ¬ Set.DependsOn f {i}ᶜ}))
    (fun i hi ↦ not_not.1 hi.2) (s ∩ X)]
  congr 1
  ext i
  simp only [mem_sdiff, mem_inter_iff, mem_ofPred_eq]
  tauto

end Set
