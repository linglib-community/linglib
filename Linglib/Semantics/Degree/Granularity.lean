/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Order.Interval.Set.OrdConnected
public import Linglib.Core.Algebra.Order.Round
public import Linglib.Core.Order.Interval.Set.LinearOrder
public import Linglib.Core.Data.Setoid.Basic
public import Linglib.Semantics.Questions.Partition.Basic

/-!
# Scale granularity

A granularity function of width $w$ maps each degree to an interval of width $w$ containing it,
the properties Sauerland and Stateva collect in [`IsGranularity`](##IsGranularity). The grain of
width $ε$ reports a degree by [the nearest multiple of $ε$](##abs_sub_nearestMultiple_le_abs_sub),
as Krifka's levels of precision do, and its cells, which Deo and Thomas take as the answers to a
degree question, are [the half-open intervals of width $ε$ centred on the
multiples](##cell_grain). A finer grain is a narrower one, not a refinement: on a dense scale
[no wider cell fits inside a narrower one](##IsGranularity.not_subset), and a grain refines the
grain $k$ times as wide [exactly when $k$ is odd](##grain_le_grain_iff_odd), so halving, Krifka's
optimal refinement, nests the multiples but never the cells.

## Implementation notes

Cells are half-open, as Deo and Thomas write them, since closed cells (Sauerland and Stateva) or
open ones (Thomas and Deo) of one width do not partition the scale. `IsGranularity` places each
cell between the open and the closed interval of its width, agnostic about the endpoints as
Thomas and Deo are after Gyarmathy, and needs no `sSup`, which `ℚ` lacks.

## References

* [krifka-2007]
* [sauerland-stateva-2011]
* [gyarmathy-2017]
* [thomas-deo-2020]
* [deo-thomas-2025]
-/

@[expose] public section

open Set

section IsGranularity

variable {D : Type*} [AddCommGroup D] [LinearOrder D]
  {γ γ₁ γ₂ : D → Set D} {w w₁ w₂ : D}

/-- A granularity function of width `w` maps each degree to a set that contains it and lies
between the open and the closed interval of width `w` with a common left end. -/
structure IsGranularity (γ : D → Set D) (w : D) : Prop where
  /-- Every degree lies in its own cell. -/
  mem_self (s : D) : s ∈ γ s
  /-- Every cell is an interval of width `w`, whichever of its endpoints it contains. -/
  exists_Ioo_subset_subset_Icc (s : D) : ∃ a, Ioo a (a + w) ⊆ γ s ∧ γ s ⊆ Icc a (a + w)

theorem IsGranularity.ordConnected (h : IsGranularity γ w) (s : D) : (γ s).OrdConnected := by
  obtain ⟨a, h₁, h₂⟩ := h.exists_Ioo_subset_subset_Icc s
  exact ordConnected_of_Ioo fun x hx y hy _ ↦ (Ioo_subset_Ioo (h₂ hx).1 (h₂ hy).2).trans h₁

/-- The granularity function of width zero is the exact reading, every cell a single degree. -/
theorem isGranularity_zero_iff : IsGranularity γ 0 ↔ γ = fun s ↦ {s} := by
  refine ⟨fun h ↦ funext fun s ↦ ?_, by rintro rfl; exact ⟨fun s ↦ rfl, fun s ↦ ⟨s, by simp⟩⟩⟩
  obtain ⟨a, -, h₂⟩ := h.exists_Ioo_subset_subset_Icc s
  rw [add_zero, Icc_self] at h₂
  obtain rfl := mem_singleton_iff.1 (h₂ (h.mem_self s))
  exact h₂.antisymm (singleton_subset_iff.2 (h.mem_self _))

variable [IsOrderedAddMonoid D]

theorem IsGranularity.nonneg (h : IsGranularity γ w) : 0 ≤ w := by
  obtain ⟨a, -, h₂⟩ := h.exists_Ioo_subset_subset_Icc 0
  obtain ⟨h₃, h₄⟩ := h₂ (h.mem_self 0)
  exact (le_add_iff_nonneg_right a).1 (h₃.trans h₄)

/-- A cell of a wider granularity function never lies inside a cell of a narrower one. -/
theorem IsGranularity.not_subset [DenselyOrdered D] (h₁ : IsGranularity γ₁ w₁)
    (h₂ : IsGranularity γ₂ w₂) (hlt : w₁ < w₂) (s t : D) : ¬ γ₂ t ⊆ γ₁ s := fun hsub ↦ by
  obtain ⟨a, ha, -⟩ := h₂.exists_Ioo_subset_subset_Icc t
  obtain ⟨b, -, hb⟩ := h₁.exists_Ioo_subset_subset_Icc s
  obtain ⟨hab, hba⟩ := (Ioo_subset_Icc_iff (lt_add_of_pos_right a (h₁.nonneg.trans_lt hlt))).1
    ((ha.trans hsub).trans hb)
  exact not_le.2 hlt ((add_le_add_iff_left b).1 ((add_le_add_left hab w₂).trans hba))

end IsGranularity

section Grain

variable {α : Type*} [Field α] [LinearOrder α] [FloorRing α] {ε ε₁ ε₂ d d' : α}

/-- The grain of width `ε` identifies two degrees when they have the same nearest multiple of
`ε`. -/
def grain (ε : α) : Setoid α := Setoid.ker fun d ↦ round (d / ε)

/-- The multiple of `ε` nearest to `d`. -/
def nearestMultiple (ε d : α) : α := round (d / ε) • ε

theorem grain_iff : grain ε d d' ↔ round (d / ε) = round (d' / ε) := Iff.rfl

theorem nearestMultiple_mem_zmultiples (ε d : α) : nearestMultiple ε d ∈ AddSubgroup.zmultiples ε :=
  AddSubgroup.mem_zmultiples_iff.2 ⟨_, rfl⟩

theorem preimage_nearestMultiple_of_notMem {d : α} (hd : d ∉ AddSubgroup.zmultiples ε) :
    nearestMultiple ε ⁻¹' {d} = ∅ :=
  eq_empty_of_forall_notMem fun v hv ↦ hd (hv ▸ nearestMultiple_mem_zmultiples ε v)

theorem nearestMultiple_eq_self_of_mem_zmultiples (hε : ε ≠ 0)
    (hd : d ∈ AddSubgroup.zmultiples ε) : nearestMultiple ε d = d := by
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hd
  simp only [nearestMultiple, zsmul_eq_mul]
  rw [mul_div_cancel_right₀ _ hε, round_intCast]

variable [IsStrictOrderedRing α]

theorem ker_nearestMultiple (hε : ε ≠ 0) : Setoid.ker (nearestMultiple ε) = grain ε :=
  Setoid.ker_comp_of_injective (fun d ↦ round (d / ε)) (g := (· • ε)) fun m n h ↦ by
    simpa [zsmul_eq_mul, hε] using h

theorem abs_sub_nearestMultiple_le (hε : 0 < ε) (d : α) : |d - nearestMultiple ε d| ≤ ε / 2 :=
  abs_sub_round_div_zsmul_le hε d

theorem abs_sub_nearestMultiple_le_abs_sub (hε : ε ≠ 0) (d : α) (n : ℤ) :
    |d - nearestMultiple ε d| ≤ |d - n • ε| :=
  abs_sub_round_div_zsmul_le_abs_sub_zsmul hε d n

/-- The cell of `d` is the half-open interval of width `ε` centred on its nearestMultiple. -/
theorem cell_grain (hε : 0 < ε) (d : α) :
    (grain ε).cell d = Ico (nearestMultiple ε d - ε / 2) (nearestMultiple ε d + ε / 2) := by
  ext x
  rw [Setoid.mem_cell, grain_iff, round_eq_iff, mem_Ico, mem_Ico, le_div_iff₀ hε,
    div_lt_iff₀ hε, nearestMultiple, zsmul_eq_mul, sub_mul, add_mul, one_div_mul_eq_div]

theorem cell_grain_of_mem_zmultiples (hε : 0 < ε) (hd : d ∈ AddSubgroup.zmultiples ε) :
    (grain ε).cell d = Ico (d - ε / 2) (d + ε / 2) := by
  rw [cell_grain hε, nearestMultiple_eq_self_of_mem_zmultiples hε.ne' hd]

theorem cell_grain_zero (hε : 0 < ε) : (grain ε).cell 0 = Ico (-(ε / 2)) (ε / 2) := by
  rw [cell_grain_of_mem_zmultiples hε (zero_mem _), zero_sub, zero_add]

/-- The degrees farthest from their nearest multiple are the lower ends of the cells. -/
theorem abs_sub_nearestMultiple_eq_half_iff (hε : 0 < ε) :
    |d - nearestMultiple ε d| = ε / 2 ↔ d + ε / 2 ∈ AddSubgroup.zmultiples ε := by
  have hd := (grain ε).mem_cell_self d
  rw [cell_grain hε] at hd
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [show d + ε / 2 = nearestMultiple ε d by
      rcases (abs_eq (by positivity)).1 h with h | h <;> linarith [hd.2]]
    exact nearestMultiple_mem_zmultiples ε d
  · have hmem : d ∈ (grain ε).cell (d + ε / 2) := by
      rw [cell_grain_of_mem_zmultiples hε h]
      constructor <;> linarith
    rw [← ker_nearestMultiple hε.ne', Setoid.mem_cell, Setoid.ker_def,
      nearestMultiple_eq_self_of_mem_zmultiples hε.ne' h] at hmem
    rw [hmem, sub_add_cancel_left, abs_neg, abs_of_pos (by positivity)]

theorem preimage_nearestMultiple (hε : 0 < ε) {d : α} (hd : d ∈ AddSubgroup.zmultiples ε) :
    nearestMultiple ε ⁻¹' {d} = Ico (d - ε / 2) (d + ε / 2) := by
  rw [← cell_grain_of_mem_zmultiples hε hd, ← ker_nearestMultiple hε.ne']
  ext v
  rw [mem_preimage, mem_singleton_iff, Setoid.mem_cell, Setoid.ker_def,
    nearestMultiple_eq_self_of_mem_zmultiples hε.ne' hd]

theorem abs_sub_lt_of_grain (hε : 0 < ε) (h : grain ε d d') : |d - d'| < ε := by
  have hd : d ∈ (grain ε).cell d' := h
  have hd' := (grain ε).mem_cell_self d'
  rw [cell_grain hε] at hd hd'
  rw [abs_sub_lt_iff]
  constructor <;> linarith [hd.1, hd.2, hd'.1, hd'.2]

theorem isGranularity_cell (hε : 0 < ε) : IsGranularity (grain ε).cell ε where
  mem_self := (grain ε).mem_cell_self
  exists_Ioo_subset_subset_Icc d := ⟨nearestMultiple ε d - ε / 2, by
    rw [cell_grain hε, show nearestMultiple ε d - ε / 2 + ε = nearestMultiple ε d + ε / 2 by ring]
    exact ⟨Ioo_subset_Ico_self, Ico_subset_Icc_self⟩⟩

/-- Around a common multiple of two widths, the cell of the finer grain lies inside the cell of
the coarser one. -/
theorem cell_grain_subset_cell_grain (hε₁ : 0 < ε₁) (h : ε₁ ≤ ε₂)
    (h₁ : d ∈ AddSubgroup.zmultiples ε₁) (h₂ : d ∈ AddSubgroup.zmultiples ε₂) :
    (grain ε₁).cell d ⊆ (grain ε₂).cell d := by
  rw [cell_grain_of_mem_zmultiples hε₁ h₁, cell_grain_of_mem_zmultiples (hε₁.trans_le h) h₂]
  exact Ico_subset_Ico (by linarith) (by linarith)

theorem grain_le_grain_of_odd (j : ℕ) : grain ε ≤ grain ((2 * j + 1 : ℕ) * ε) := by
  have : (fun d : α ↦ round (d / ((2 * j + 1 : ℕ) * ε))) =
      (fun n : ℤ ↦ (n + j) / (2 * j + 1 : ℕ)) ∘ fun d ↦ round (d / ε) := by
    funext d
    rw [Function.comp_apply, ← round_div_two_mul_add_one, div_mul_eq_div_div, div_right_comm]
  rw [grain, grain, this]
  exact Setoid.ker_le_ker_comp _ _

theorem not_grain_le_grain_of_even (hε : 0 < ε) {j : ℕ} (hj : 0 < j) :
    ¬ grain ε ≤ grain ((2 * j : ℕ) * ε) := fun h ↦ by
  set K : α := (2 * j : ℕ) * ε with hK
  have hj : (1 : α) ≤ j := by exact_mod_cast hj
  have hK' : K = 2 * (j * ε) := by rw [hK]; push_cast; ring
  have hfine := cell_grain_of_mem_zmultiples hε (d := j * ε)
    (AddSubgroup.mem_zmultiples_iff.2 ⟨j, by rw [zsmul_eq_mul, Int.cast_natCast]⟩)
  have hcoarse := cell_grain_zero (by rw [hK']; positivity : 0 < K)
  have hlo : j * ε - ε / 4 ∈ (grain ε).cell (j * ε) := hfine ▸ ⟨by linarith, by linarith⟩
  have hhi : j * ε + ε / 4 ∈ (grain ε).cell (j * ε) := hfine ▸ ⟨by linarith, by linarith⟩
  have h0 : j * ε - ε / 4 ∈ (grain K).cell 0 := hcoarse ▸ ⟨by nlinarith, by linarith⟩
  have h1 : j * ε + ε / 4 ∈ (grain K).cell 0 :=
    (grain K).trans (Setoid.le_def.1 h ((grain ε).trans hhi ((grain ε).symm hlo))) h0
  rw [hcoarse] at h1
  exact absurd h1.2 (by linarith)

/-- The grain of width `ε` refines the grain of width `k * ε` exactly when `k` is odd. -/
theorem grain_le_grain_iff_odd (hε : 0 < ε) {k : ℕ} (hk : 0 < k) :
    grain ε ≤ grain (k * ε) ↔ Odd k := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · exact iff_of_false (not_grain_le_grain_of_even hε (by omega))
      (Nat.not_odd_iff_even.2 (even_two_mul j))
  · exact iff_of_true (grain_le_grain_of_odd j) (odd_two_mul_add_one j)

end Grain
