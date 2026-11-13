/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Antichain
public import Mathlib.Order.Minimal

/-!
# Minimality under a key

Among elements none of which lies below another, minimality under a key depends only on the key's
strict order between incomparable elements: when that order is an irreflexive relation `r`, the
minimal elements are those that nothing is `r`-related to. Under a key no value of which lies
strictly below another every element is minimal, and under a strictly antitone key on a linear
order the minimal elements are the greatest.

## Main statements

* `minimalFor_iff_of_isAntichain`
* `minimalFor_iff_of_forall_not_lt`
* `StrictAnti.minimalFor_iff_isGreatest`
-/

public section

variable {ι β : Type*} [Preorder ι] [Preorder β] {P : ι → Prop} {f : ι → β} {r : ι → ι → Prop}
  {i : ι}

/-- Among elements of `P` none of which lies below another, an element is minimal under a key
whose strict order between incomparable elements is the irreflexive relation `r` exactly when no
element of `P` is `r`-related to it. -/
theorem minimalFor_iff_of_isAntichain (hP : IsAntichain (· ≤ ·) {j | P j}) (hr : ∀ j, ¬ r j j)
    (h : ∀ ⦃j k⦄, ¬ j ≤ k → ¬ k ≤ j → (f j < f k ↔ r j k)) :
    MinimalFor P f i ↔ P i ∧ ∀ ⦃j⦄, P j → ¬ r j i := by
  rw [minimalFor_iff_forall_lt]
  refine and_congr_right fun hi ↦ forall_congr' fun j ↦ ?_
  by_cases hj : P j
  · obtain rfl | hne := eq_or_ne j i
    · simp [hj, hr]
    · simp [hj, h (hP hj hi hne) (hP hi hj hne.symm)]
  · simp [hj]

omit [Preorder ι] in
/-- Under a key no value of which lies strictly below another, every element of `P` is
minimal. -/
theorem minimalFor_iff_of_forall_not_lt (h : ∀ j k, ¬ f j < f k) : MinimalFor P f i ↔ P i :=
  ⟨fun hi ↦ hi.1, fun hi ↦ ⟨hi, fun j _ ↦ not_lt_iff_le_imp_ge.1 (h j i)⟩⟩

/-- Under a strictly antitone key on a linear order, the minimal elements of `P` are its
greatest. -/
theorem StrictAnti.minimalFor_iff_isGreatest {κ γ : Type*} [LinearOrder κ] [Preorder γ]
    {P : κ → Prop} {f : κ → γ} {i : κ} (hf : StrictAnti f) :
    MinimalFor P f i ↔ IsGreatest {j | P j} i :=
  and_congr_right fun _ ↦ forall₂_congr fun j _ ↦ by
    rw [hf.le_iff_ge, hf.le_iff_ge]
    exact ⟨fun h ↦ (le_total j i).elim id h, fun h _ ↦ h⟩
