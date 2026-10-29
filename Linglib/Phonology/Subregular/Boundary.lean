/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.List.Chain
public import Linglib.Core.Data.List.Factors
public import Linglib.Core.Data.List.TakeDrop
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.List.OfFn

/-!
# Subregular Languages: Boundary Augmentation

Boundary augmentation pads a string with `k - 1` boundary markers on each side, so that the
`k`-factors of the padded string see the edges of the word. The strictly local, locally testable,
and tier-based classes are built on it; the contiguous `k`-factors themselves are the generic
`List.kFactors`. A word read at integer positions is a two-sided family blank outside
`[0, w.length)`, and its width-`k` window at `i` lists its entries on `[i, i + k)`. The entries of
the padded word are those of the word shifted by the pad width, so
[the `k`-factors of the augmented word are exactly its windows](##mem_kFactors_boundary_iff)
starting in `[1 - k, w.length)`.

## Implementation notes

The standard subregular convention extends the alphabet with two edge markers
`⋊`, `⋉` and studies the `k`-factors of `⋊ᵏ⁻¹ · w · ⋉ᵏ⁻¹`. We instead use the
one-fresh-symbol extension `Option α` (`none` = boundary, `some a` = original
symbol): a single marker suffices because boundary symbols only ever occur at
fixed positions, so the two edges are never confused.

Integer positions are a lawful `GetElem? (List α) ℤ α` instance, `w[i]?` being `none` at every
negative `i` rather than counting from the end, so position arithmetic across the left edge is
ordinary `ℤ` arithmetic rather than a case split on `ℕ` subtraction. Being lawful, the instance
gets the generic `getElem?_pos`, `getElem?_neg` and `getElem?_eq_some_iff`.

## References

* [rogers-pullum-2011]
* [heinz-rogers-2010]
* [lambert-2022]
-/

@[expose] public section

variable {α : Type*}

/-! ### Boundary augmentation -/

/-- A boundary-augmented string has the original symbols (`some a`) and the boundary marker
`none`. -/
abbrev Augmented (α : Type*) := List (Option α)

section Boundary

variable (k : ℕ) (w : List α)

/-- `w` padded with `k - 1` boundary markers (`none`) on each side. -/
def boundary : Augmented α :=
  List.replicate (k - 1) none ++ w.map some ++ List.replicate (k - 1) none

@[simp] lemma boundary_one : boundary 1 w = w.map some := by
  simp [boundary]

lemma length_boundary : (boundary k w).length = w.length + 2 * (k - 1) := by
  simp [boundary]; omega

end Boundary

/-! ### Integer indexing -/

namespace List

variable {w y u v : List α} {i : ℤ}

instance instGetElem?Int : GetElem? (List α) ℤ α fun w i ↦ 0 ≤ i ∧ i < w.length where
  getElem w i h := w[i.toNat]'(by omega)
  getElem? w i := if 0 ≤ i then w[i.toNat]? else none

instance : LawfulGetElem (List α) ℤ α fun w i ↦ 0 ≤ i ∧ i < w.length where
  getElem?_def w i _ := by
    show (if 0 ≤ i then w[i.toNat]? else none) = _
    split_ifs with h1 h2 h2
    · exact getElem?_eq_getElem (by omega)
    · exact getElem?_eq_none (by omega)
    · exact absurd h2.1 h1
    · rfl

theorem getElem_int (h : 0 ≤ i ∧ i < w.length) : w[i] = w[i.toNat]'(by omega) := rfl

theorem getElem?_int : w[i]? = if 0 ≤ i then w[i.toNat]? else none := rfl

theorem getElem?_int_of_nonneg (h : 0 ≤ i) : w[i]? = w[i.toNat]? := ite_eq_left h

theorem getElem?_int_of_neg (h : i < 0) : w[i]? = none := ite_eq_right (by omega)

@[simp] theorem getElem?_natCast (w : List α) (n : ℕ) : w[(n : ℤ)]? = w[n]? := by
  simp [getElem?_int]

@[simp] theorem getElem?_int_nil : ([] : List α)[i]? = none := by simp

theorem getElem?_int_eq_none_iff : w[i]? = none ↔ i < 0 ∨ (w.length : ℤ) ≤ i := by
  rw [_root_.getElem?_eq_none_iff]
  omega

/-- Agreement of integer-indexed entries up to the length of `w` forces equality. -/
theorem ext_getElem?_int (h : ∀ j : ℤ, j ≤ (w.length : ℤ) → y[j]? = w[j]?) : y = w := by
  have hy : y.length ≤ w.length := by
    have h1 := h (w.length : ℤ) (Int.le_refl _)
    rwa [getElem?_natCast, getElem?_natCast, getElem?_eq_none (Nat.le_refl _),
      getElem?_eq_none_iff] at h1
  refine ext_getElem? fun n ↦ ?_
  rcases Nat.lt_or_ge n w.length with hn | hn
  · simpa using h n (by omega)
  · rw [getElem?_eq_none hn, getElem?_eq_none (by omega)]

/-- Agreement of integer-indexed entries below `c` transfers prefixes of length `c`. -/
theorem ext_take_getElem?_int {c : ℕ} (h : ∀ j : ℤ, j < (c : ℤ) → y[j]? = w[j]?) :
    y.take c = w.take c :=
  ext_take_getElem? fun n hn ↦ by simpa using h n (by omega)

theorem getElem?_int_append_left (h : i < (u.length : ℤ)) : (u ++ v)[i]? = u[i]? := by
  by_cases h0 : 0 ≤ i
  · rw [getElem?_int_of_nonneg h0, getElem?_int_of_nonneg h0, getElem?_append_left (by omega)]
  · rw [getElem?_int_of_neg (by omega), getElem?_int_of_neg (by omega)]

theorem getElem?_int_take_of_lt {c : ℕ} (h : i < (c : ℤ)) : (w.take c)[i]? = w[i]? := by
  by_cases h0 : 0 ≤ i
  · rw [getElem?_int_of_nonneg h0, getElem?_int_of_nonneg h0, getElem?_take_of_lt (by omega)]
  · rw [getElem?_int_of_neg (by omega), getElem?_int_of_neg (by omega)]

end List

/-! ### Position discrimination and windows

Entries of `boundary k y` are integer-indexed entries of the word (`w[i]?` with `i : ℤ`, blank
outside `[0, w.length)`), shifted by the pad width; consequently the `k`-factors of the augmented
word are exactly its windows (`window`). -/

section Pinning

/-- The width-`k` window of `w` at `i` lists its integer-indexed entries on `[i, i + k)`. -/
def window (k : ℕ) (w : List α) (i : ℤ) : List (Option α) :=
  List.ofFn fun j : Fin k ↦ w[i + (j : ℕ)]?

@[simp] lemma length_window {k : ℕ} {w : List α} {i : ℤ} : (window k w i).length = k := by
  simp [window]

lemma getElem?_window {k j : ℕ} {w : List α} {i : ℤ} (h : j < k) :
    (window k w i)[j]? = some w[i + j]? := by
  simp [window, h]

lemma window_eq_window_iff {k : ℕ} {w y : List α} {i q : ℤ} :
    window k w i = window k y q ↔ ∀ j : ℕ, j < k → w[i + j]? = y[q + j]? := by
  simp [window, List.ofFn_inj, funext_iff, Fin.forall_iff]

variable {k : ℕ} {w y l : List α}

lemma getElem?_boundary (j : ℕ) :
    (boundary k w)[j]? =
      if j < k - 1 then some none
      else if j < k - 1 + w.length then (w[j - (k - 1)]?).map some
      else if j < w.length + 2 * (k - 1) then some none
      else none := by
  unfold boundary
  rcases lt_or_ge j (k - 1) with h1 | h1
  · rw [ite_eq_left h1, List.getElem?_append_left (by simp; omega),
      List.getElem?_append_left (by simpa using h1), List.getElem?_replicate, ite_eq_left h1]
  rcases lt_or_ge j (k - 1 + w.length) with h2 | h2
  · rw [ite_eq_right (by omega), ite_eq_left h2, List.getElem?_append_left (by simp; omega),
      List.getElem?_append_right (by simpa using h1), List.getElem?_map,
      List.length_replicate]
  rcases lt_or_ge j (w.length + 2 * (k - 1)) with h3 | h3
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h3,
      List.getElem?_append_right (by simp; omega), List.getElem?_replicate,
      ite_eq_left (by simp; omega)]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      List.getElem?_eq_none (by simp; omega)]

lemma of_getElem?_boundary_eq_some {j : ℕ} {a : α}
    (h : (boundary k w)[j]? = some (some a)) :
    k - 1 ≤ j ∧ w[j - (k - 1)]? = some a := by
  rw [getElem?_boundary] at h
  split_ifs at h with h1 h2 h3
  · exact absurd h (by simp)
  · exact ⟨by omega, by simpa using h⟩
  · exact absurd h (by simp)

lemma of_getElem?_boundary_eq_none {j : ℕ}
    (h : (boundary k w)[j]? = some (none : Option α)) :
    j < k - 1 ∨ k - 1 + w.length ≤ j := by
  rw [getElem?_boundary] at h
  split_ifs at h with h1 h2 h3
  · exact .inl h1
  · exact absurd h (by simp)
  · exact .inr (by omega)

lemma getElem?_boundary_eq_getElem?_int {q : ℕ} (h : q < w.length + 2 * (k - 1)) :
    (boundary k w)[q]? = some (w[(q : ℤ) - (k - 1 : ℕ)]?) := by
  rw [getElem?_boundary]
  split_ifs with h1 h2
  · rw [List.getElem?_int_of_neg (by omega)]
  · have hlt : q - (k - 1) < w.length := by omega
    rw [show ((q : ℤ) - (k - 1 : ℕ)) = ((q - (k - 1) : ℕ) : ℤ) by omega,
      List.getElem?_natCast, List.getElem?_eq_getElem hlt, Option.map_some]
  · rw [List.getElem?_int_eq_none_iff.mpr (.inr (by omega))]

/-- The `k`-factors of the augmented word are exactly its windows over
`[1 - k, w.length)`. -/
lemma mem_kFactors_boundary_iff {f : List (Option α)} (hk : 1 ≤ k) :
    f ∈ List.kFactors k (boundary k y) ↔
      ∃ i : ℤ, 1 - k ≤ i ∧ i < y.length ∧ f = window k y i := by
  rw [List.mem_kFactors]
  constructor
  · rintro ⟨hinf, hlen⟩
    obtain ⟨δ, hbound, hδ⟩ := List.infix_iff_getElem?.mp hinf
    rw [length_boundary] at hbound
    refine ⟨(δ : ℤ) - (k - 1 : ℕ), by omega, by omega, ?_⟩
    apply List.ext_getElem?
    intro j
    rcases lt_or_ge j k with hj | hj
    · rw [getElem?_window hj, List.getElem?_eq_getElem (show j < f.length by omega)]
      have h1 := (hδ j (by omega)).symm
      rw [getElem?_boundary_eq_getElem?_int (q := j + δ) (by omega)] at h1
      rw [h1, show ((j + δ : ℕ) : ℤ) - ((k - 1 : ℕ) : ℤ) = (δ : ℤ) - (k - 1 : ℕ) + (j : ℕ)
        by omega]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simpa using hj)]
  · rintro ⟨i, h1, h2, rfl⟩
    refine ⟨List.infix_iff_getElem?.mpr ⟨(i + (k - 1 : ℕ)).toNat,
      by rw [length_window, length_boundary]; omega, fun j hj ↦ ?_⟩, by simp⟩
    rw [← List.getElem?_eq_getElem hj, length_window] at *
    rw [getElem?_window hj,
      getElem?_boundary_eq_getElem?_int (q := j + (i + (k - 1 : ℕ)).toNat) (by omega),
      show ((j + (i + (k - 1 : ℕ)).toNat : ℕ) : ℤ) - ((k - 1 : ℕ) : ℤ) = i + (j : ℕ)
        by omega]

end Pinning
