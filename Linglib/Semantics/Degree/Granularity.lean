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

A granularity function of width `w` maps each degree to an interval of width `w` that contains
it. The grain of width `ε` is the granularity function that reports each degree by the nearest
multiple of `ε`: degrees with the same nearest multiple are indistinguishable, and the cell of a
degree is the half-open interval of width `ε` centred on that multiple. Krifka builds levels of
precision this way, Sauerland and Stateva define granularity functions by the properties
collected in `IsGranularity`, and Deo and Thomas take the cells of a grain as the answers to a
degree question.

A finer grain is a narrower one, not a refinement. No cell of a wider granularity function fits
inside a cell of a narrower one, and a grain refines the grain `k` times as wide exactly when `k`
is odd, so halving the width never refines. Around a common multiple of two widths the cells are
nested.

## Main definitions

* `Degree.IsGranularity`: a granularity function of a given width.
* `Degree.grain`: the partition of the scale by nearest multiple of `ε`.
* `Degree.representative`: the nearest multiple of `ε`.

## Main results

* `Degree.cell_grain`: a cell is the half-open interval of width `ε` centred on its
  representative.
* `Degree.IsGranularity.not_subset`: a cell of a wider granularity function never
  fits inside a cell of a narrower one.
* `Degree.isGranularity_zero_iff`: the granularity function of width zero is the exact reading,
  every cell a single degree.
* `Degree.cell_grain_subset_cell_grain`: around a common multiple, a finer cell lies inside a
  coarser one.
* `Degree.grain_le_grain_iff_odd`: the grain of width `ε` refines the grain of width
  `k * ε` exactly when `k` is odd.

## Implementation notes

Cells are half-open, the only choice of endpoints that partitions the scale; Sauerland and Stateva
write closed intervals and Thomas and Deo open ones. `IsGranularity` states the width by placing
each cell between the open and the closed interval of that width, which leaves the endpoints
open, as Thomas and Deo recommend, and needs no `sSup`, which `ℚ` lacks.

## References

* [krifka-2007]
* [sauerland-stateva-2011]
* [thomas-deo-2020]
* [deo-thomas-2025]
-/

@[expose] public section

namespace Degree

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
  refine ⟨fun x hx y hy z ⟨hxz, hzy⟩ ↦ ?_⟩
  rcases ((h₂ hx).1.trans hxz).eq_or_lt with rfl | hlt
  · exact le_antisymm hxz (h₂ hx).1 ▸ hx
  rcases (hzy.trans (h₂ hy).2).eq_or_lt with rfl | hlt'
  · exact le_antisymm (h₂ hy).2 hzy ▸ hy
  exact h₁ ⟨hlt, hlt'⟩

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
  exact le_of_add_le_add_left (a := a) (by simpa using h₃.trans h₄)

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

/-- The representative of `d` at width `ε` is the nearest multiple of `ε`. -/
def representative (ε d : α) : α := round (d / ε) • ε

theorem grain_iff : grain ε d d' ↔ round (d / ε) = round (d' / ε) := Iff.rfl

theorem representative_mem_zmultiples (ε d : α) : representative ε d ∈ AddSubgroup.zmultiples ε :=
  AddSubgroup.mem_zmultiples_iff.2 ⟨_, rfl⟩

theorem preimage_representative_of_notMem {d : α} (hd : d ∉ AddSubgroup.zmultiples ε) :
    representative ε ⁻¹' {d} = ∅ :=
  eq_empty_of_forall_notMem fun v hv ↦ hd (hv ▸ representative_mem_zmultiples ε v)

theorem representative_eq_self_of_mem_zmultiples (hε : ε ≠ 0)
    (hd : d ∈ AddSubgroup.zmultiples ε) : representative ε d = d := by
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hd
  simp only [representative, zsmul_eq_mul]
  rw [mul_div_cancel_right₀ _ hε, round_intCast]

variable [IsStrictOrderedRing α]

theorem grain_iff_representative (hε : ε ≠ 0) :
    grain ε d d' ↔ representative ε d = representative ε d' := by
  simp only [grain_iff, representative, zsmul_eq_mul]
  exact ⟨fun h ↦ by rw [h], fun h ↦ by exact_mod_cast mul_right_cancel₀ hε h⟩

theorem abs_sub_representative_le (hε : 0 < ε) (d : α) : |d - representative ε d| ≤ ε / 2 :=
  abs_sub_round_div_zsmul_le hε d

theorem abs_sub_representative_le_abs_sub (hε : ε ≠ 0) (d : α) (n : ℤ) :
    |d - representative ε d| ≤ |d - n • ε| :=
  abs_sub_round_div_zsmul_le_abs_sub_zsmul hε d n

/-- The cell of `d` is the half-open interval of width `ε` centred on its representative. -/
theorem cell_grain (hε : 0 < ε) (d : α) :
    (grain ε).cell d = Ico (representative ε d - ε / 2) (representative ε d + ε / 2) := by
  ext x
  rw [Setoid.mem_cell, grain_iff, round_eq_iff, mem_Ico, mem_Ico, le_div_iff₀ hε,
    div_lt_iff₀ hε, representative, zsmul_eq_mul, sub_mul, add_mul, one_div_mul_eq_div]

theorem abs_sub_representative_eq_half_iff (hε : 0 < ε) {d : α} :
    |d - representative ε d| = ε / 2 ↔
      d ∈ AddSubgroup.zmultiples (ε / 2) ∧ d ∉ AddSubgroup.zmultiples ε := by
  have key : |d - representative ε d| = ε * |d / ε - round (d / ε)| := by
    rw [representative, zsmul_eq_mul, ← abs_of_pos hε, ← abs_mul, abs_of_pos hε]
    congr 1
    field_simp
  rw [key, show ε / 2 = ε * (1 / 2) by ring, mul_right_inj' hε.ne', abs_sub_round_eq_half_iff,
    AddSubgroup.mem_zmultiples_iff, AddSubgroup.mem_zmultiples_iff]
  simp only [zsmul_eq_mul]
  constructor
  · rintro ⟨k, hk⟩
    rw [div_eq_iff hε.ne'] at hk
    refine ⟨⟨2 * k + 1, by rw [hk]; push_cast; ring⟩, ?_⟩
    rintro ⟨j, hj⟩
    have h2 : (j : α) = k + 1 / 2 :=
      mul_right_cancel₀ hε.ne' (hj.trans hk)
    have : ((2 * (j - k) : ℤ) : α) = 1 := by push_cast; linarith
    have := Int.cast_eq_one.1 this
    omega
  · rintro ⟨⟨m, hm⟩, hn⟩
    obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' m
    · exact absurd ⟨k, by rw [← hm]; push_cast; ring⟩ hn
    · refine ⟨k, ?_⟩
      rw [div_eq_iff hε.ne', ← hm]
      push_cast
      ring

theorem preimage_representative (hε : 0 < ε) {d : α} (hd : d ∈ AddSubgroup.zmultiples ε) :
    representative ε ⁻¹' {d} = Ico (d - ε / 2) (d + ε / 2) := by
  have hrep := representative_eq_self_of_mem_zmultiples hε.ne' hd
  rw [← hrep, ← cell_grain hε, hrep]
  ext v
  rw [mem_preimage, mem_singleton_iff, Setoid.mem_cell, grain_iff_representative hε.ne', hrep]

theorem abs_sub_lt_of_grain (hε : 0 < ε) (h : grain ε d d') : |d - d'| < ε := by
  have hd : d ∈ (grain ε).cell d' := h
  have hd' := (grain ε).mem_cell_self d'
  rw [cell_grain hε] at hd hd'
  rw [abs_sub_lt_iff]
  constructor <;> linarith [hd.1, hd.2, hd'.1, hd'.2]

theorem isGranularity_cell (hε : 0 < ε) : IsGranularity (grain ε).cell ε where
  mem_self := (grain ε).mem_cell_self
  exists_Ioo_subset_subset_Icc d := ⟨representative ε d - ε / 2, by
    rw [cell_grain hε, show representative ε d - ε / 2 + ε = representative ε d + ε / 2 by ring]
    exact ⟨Ioo_subset_Ico_self, Ico_subset_Icc_self⟩⟩

/-- Around a common multiple of two widths, the cell of the finer grain lies inside the cell of
the coarser one. -/
theorem cell_grain_subset_cell_grain (hε₁ : 0 < ε₁) (h : ε₁ ≤ ε₂)
    (h₁ : d ∈ AddSubgroup.zmultiples ε₁) (h₂ : d ∈ AddSubgroup.zmultiples ε₂) :
    (grain ε₁).cell d ⊆ (grain ε₂).cell d := by
  have hε₂ := hε₁.trans_le h
  rw [cell_grain hε₁, cell_grain hε₂, representative_eq_self_of_mem_zmultiples hε₁.ne' h₁,
    representative_eq_self_of_mem_zmultiples hε₂.ne' h₂]
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
  have hfine := cell_grain hε (j * ε)
  rw [representative_eq_self_of_mem_zmultiples hε.ne'
    (AddSubgroup.mem_zmultiples_iff.2 ⟨j, by rw [zsmul_eq_mul, Int.cast_natCast]⟩)] at hfine
  have hcoarse := cell_grain (by rw [hK']; positivity : 0 < K) 0
  rw [representative_eq_self_of_mem_zmultiples (by rw [hK']; positivity) (zero_mem _)] at hcoarse
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
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · refine ⟨fun h ↦ absurd h (not_grain_le_grain_of_even hε (by omega)), fun h ↦ ?_⟩
    exact absurd h (Nat.not_odd_iff_even.2 (even_two_mul j))
  · exact ⟨fun _ ↦ odd_two_mul_add_one j, fun _ ↦ grain_le_grain_of_odd j⟩

end Grain

end Degree
