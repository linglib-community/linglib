/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.List.TakeDrop
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.List.Infix
public import Mathlib.Data.List.OfFn

/-!
# Subregular Languages: Boundary Augmentation

Boundary augmentation pads a string with `k - 1` boundary markers on each side, so that the
`k`-factors of the padded string, its infixes of length `k`, see the edges of the word. The strictly
local, locally testable, and tier-based classes are built on it. A word read at integer positions
is a two-sided family blank outside `[0, w.length)`, and its width-`k` window at `i` lists its
entries on `[i, i + k)`. The entries of the padded word are those of the word shifted by the pad
width, so [the `k`-factors of the augmented word are exactly its
windows](##infix_boundary_and_length_eq_iff) starting in `[1 - k, w.length)`.

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
lemma infix_boundary_and_length_eq_iff {f : List (Option α)} (hk : 1 ≤ k) :
    f <:+: boundary k y ∧ f.length = k ↔
      ∃ i : ℤ, 1 - k ≤ i ∧ i < y.length ∧ f = window k y i := by
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

/-! ### The edges of a padded word

A boundary marker stands before a symbol only at the left edge of a padded word, and after one
only at the right edge, so an infix that shows an edge is pinned to it. -/

lemma boundary_reverse (k : ℕ) (w : List α) : (boundary k w).reverse = boundary k w.reverse := by
  simp [boundary, List.append_assoc]

lemma map_some_infix_boundary (k : ℕ) (w : List α) : w.map some <:+: boundary k w :=
  ⟨_, _, rfl⟩

private lemma replicate_append_cons {β : Type*} (n : ℕ) (a : β) (l : List β) :
    List.replicate n a ++ a :: l = a :: (List.replicate n a ++ l) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

/-- The word between one marker on each side lies in every wider padding. -/
lemma boundary_two_infix_boundary (hk : 2 ≤ k) (w : List α) : boundary 2 w <:+: boundary k w := by
  refine ⟨List.replicate (k - 2) none, List.replicate (k - 2) none, ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  simp [boundary, List.replicate_succ, replicate_append_cons]

lemma infix_of_map_some_infix_boundary {s : List α} (h : s.map some <:+: boundary k y) :
    s <:+: y := by
  simpa [boundary, List.filterMap_map] using h.filterMap id

/-- A marker before a symbol stands at the left edge, which fixes where the infix lies. -/
private lemma getElem?_boundary_of_cons_none_infix {s : List α} {t : List (Option α)}
    (hs : s ≠ []) (h : none :: (s.map some ++ t) <:+: boundary k y) :
    ∀ i (hi : i < (s.map some ++ t).length),
      (boundary k y)[i + (k - 1)]? = some ((s.map some ++ t)[i]) := by
  obtain ⟨δ, -, hδ⟩ := List.infix_iff_getElem?.1 h
  have hpos : 0 < s.length := List.length_pos_iff.2 hs
  have h₀ := of_getElem?_boundary_eq_none (by simpa using hδ 0 (by simp))
  have h₁ := hδ (0 + 1) (by simp; omega)
  simp only [List.getElem_cons_succ] at h₁
  rw [List.getElem_append_left (by simpa using hpos), List.getElem_map] at h₁
  obtain ⟨_, h₁⟩ := of_getElem?_boundary_eq_some h₁
  have := (List.getElem?_eq_some_iff.1 h₁).1
  intro i hi
  have hi' := hδ (i + 1) (by simpa using hi)
  simp only [List.getElem_cons_succ] at hi'
  rwa [show i + 1 + δ = i + (k - 1) by omega] at hi'

/-- A marker before symbols pins them to the left edge. -/
lemma prefix_of_cons_none_infix_boundary {s : List α} (hs : s ≠ [])
    (h : none :: s.map some <:+: boundary k y) : s <+: y := by
  have key (i : ℕ) (hi : i < s.length) : y[i]? = some s[i] := by
    have := getElem?_boundary_of_cons_none_infix (t := []) hs (by simpa using h) i (by simpa)
    simp only [List.append_nil, List.getElem_map] at this
    simpa using (of_getElem?_boundary_eq_some this).2
  refine List.prefix_iff_eq_take.2 (List.ext_getElem? fun i ↦ ?_)
  rcases lt_or_ge i s.length with hi | hi
  · rw [List.getElem?_take_of_lt hi, key i hi, List.getElem?_eq_getElem hi]
  · rw [List.getElem?_eq_none hi, List.getElem?_eq_none (by simp; omega)]

/-- A marker after symbols pins them to the right edge. -/
lemma suffix_of_concat_none_infix_boundary {s : List α} (hs : s ≠ [])
    (h : s.map some ++ [none] <:+: boundary k y) : s <:+ y := by
  have h' := List.reverse_infix.2 h
  rw [boundary_reverse] at h'
  exact List.reverse_prefix.1
    (prefix_of_cons_none_infix_boundary (by simpa using hs) (by simpa using h'))

/-- A nonempty word between its two markers occurs in the padding of that word alone. -/
lemma eq_of_boundary_two_infix_boundary {s : List α} (hs : s ≠ [])
    (h : boundary 2 s <:+: boundary k y) : s = y := by
  have h' : none :: (s.map some ++ [none]) <:+: boundary k y := by simpa [boundary] using h
  have hpre : s <+: y := prefix_of_cons_none_infix_boundary hs
    ((List.cons_prefix_cons.2 ⟨rfl, List.prefix_append _ _⟩).isInfix.trans h')
  have hlast := getElem?_boundary_of_cons_none_infix hs h' s.length (by simp)
  have := of_getElem?_boundary_eq_none (by simpa using hlast)
  exact hpre.eq_of_length_le (by omega)

/-- Only the padding of the empty word has `k` markers in a row. -/
lemma eq_nil_of_replicate_none_infix_boundary (hk : 1 ≤ k)
    (h : List.replicate k none <:+: boundary k y) : y = [] := by
  obtain ⟨δ, hlen, hδ⟩ := List.infix_iff_getElem?.1 h
  rw [List.length_replicate, length_boundary] at hlen
  by_contra hy
  have hpos : 0 < y.length := List.length_pos_iff.2 hy
  rcases Nat.lt_or_ge δ k with hδk | hδk
  · have h₁ := hδ (k - 1 - δ) (by simp; omega)
    rw [List.getElem_replicate, show k - 1 - δ + δ = k - 1 by omega] at h₁
    have := of_getElem?_boundary_eq_none h₁
    omega
  · have h₀ := hδ 0 (by simp; omega)
    rw [List.getElem_replicate, Nat.zero_add] at h₀
    have := of_getElem?_boundary_eq_none h₀
    omega

end Pinning
