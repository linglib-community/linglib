/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.Basic

/-!
# Realization of strings as representations

Each symbol denotes a primitive representation, and a string denotes the product of its
symbols' primitives, `(w.map g₀).prod`. This is Jardine's mapping `g`, the monoid hom
`FreeMonoid.lift g₀` out of the free monoid on the symbols, without the melody merge of
`AR.collapse` and `MergeAR`.

## Main definitions

* `AR.tierOffset`: the tier content of the symbols before a given one.

The tokens of the `k`th symbol stand on each tier at that symbol's offset
(`getElem?_word_prod_map`), offsets tell apart the symbols that have a token on a tier
(`eq_of_tierOffset_eq`), and when the primitives have at most one token on each of two tiers the
lines of the realization between them are those of its symbols
(`link_prod_map_of_length_le_one`).

## Main results

* `AR.word_prod`: the words of a product are the concatenated words of its factors.
* `AR.NoCrossing.prod`: a product of representations obeying the NCC obeys it.
* `AR.link_prod_map`: each line of a realization lies inside one symbol's primitive, at that
  symbol's tier offsets.

## References

* [jardine-2019]
* [jardine-2016b]
-/

@[expose] public section

namespace Autosegmental

variable {ι : Type*} {τ : ι → Type*}

namespace AR

/-- The words of a product are the concatenated words of its factors. -/
theorem word_prod (l : List (AR τ)) (i : ι) : l.prod.word i = (l.map (·.word i)).flatten := by
  induction l with
  | nil => rfl
  | cons X l ih => simp [ih]

/-- A product of representations obeying the NCC obeys it ([jardine-2016b] Theorem 4). -/
theorem NoCrossing.prod {l : List (AR τ)} (h : ∀ X ∈ l, X.NoCrossing) : l.prod.NoCrossing := by
  induction l with
  | nil => exact NoCrossing.one
  | cons X l ih =>
    rw [List.prod_cons]
    exact (h X (by simp)).mul (ih fun Y hY ↦ h Y (by simp [hY]))

variable {S : Type*} (g₀ : S → AR τ)

/-- The tier-`i` offset of the `k`-th symbol of `w`: the tier-`i` content of the symbols before
it. -/
def tierOffset (i : ι) (w : List S) (k : ℕ) : ℕ :=
  ((w.take k).map fun s ↦ ((g₀ s).word i).length).sum

@[simp] theorem tierOffset_zero (i : ι) (w : List S) : tierOffset g₀ i w 0 = 0 := by
  simp [tierOffset]

@[simp] theorem tierOffset_cons_succ (i : ι) (a : S) (w : List S) (k : ℕ) :
    tierOffset g₀ i (a :: w) (k + 1) = ((g₀ a).word i).length + tierOffset g₀ i w k := by
  simp [tierOffset]

/-- A line of a realization lies inside one symbol's primitive, at that symbol's tier offsets. -/
theorem link_prod_map (i j : ι) (w : List S) (p q : ℕ) :
    (w.map g₀).prod.Link i j p q ↔
      ∃ k, ∃ hk : k < w.length, tierOffset g₀ i w k ≤ p ∧ tierOffset g₀ j w k ≤ q ∧
        (g₀ w[k]).Link i j (p - tierOffset g₀ i w k) (q - tierOffset g₀ j w k) := by
  induction w generalizing p q with
  | nil => simp
  | cons a w ih =>
    rw [List.map_cons, List.prod_cons, link_mul, ih]
    constructor
    · rintro (h | ⟨hp, hq, k, hk, hpk, hqk, h⟩)
      · exact ⟨0, by simp, by simp, by simp, by simpa using h⟩
      · exact ⟨k + 1, by simpa using hk, by simp; omega, by simp; omega,
          by simpa [Nat.sub_sub] using h⟩
    · rintro ⟨_ | k, hk, hpk, hqk, h⟩
      · exact .inl (by simpa using h)
      · simp only [tierOffset_cons_succ, List.getElem_cons_succ] at hpk hqk h
        exact .inr ⟨by omega, by omega, k, by simpa using hk, by omega, by omega,
          by simpa [Nat.sub_sub] using h⟩

theorem link_prod_map_of_length_eq_one {j : ι} (hj : ∀ s, ((g₀ s).word j).length = 1)
    (i : ι) (w : List S) (p q : ℕ) :
    (w.map g₀).prod.Link i j p q ↔
      ∃ hq : q < w.length, tierOffset g₀ i w q ≤ p ∧
        (g₀ w[q]).Link i j (p - tierOffset g₀ i w q) 0 := by
  have hoff : ∀ k ≤ w.length, tierOffset g₀ j w k = k := fun k hk ↦ by
    simp [tierOffset, hj, hk]
  rw [link_prod_map]
  constructor
  · rintro ⟨k, hk, hpk, hqk, h⟩
    rw [hoff k hk.le] at hqk h
    have hlt := h.lt_right
    rw [hj] at hlt
    obtain rfl : k = q := by omega
    exact ⟨hk, hpk, by simpa using h⟩
  · rintro ⟨hq, hpq, h⟩
    exact ⟨q, hq, hpq, by rw [hoff q hq.le], by simpa [hoff q hq.le] using h⟩

/-! ### Tier offsets -/

section Offset

variable (i : ι) (w : List S)

theorem tierOffset_succ {k : ℕ} (hk : k < w.length) :
    tierOffset g₀ i w (k + 1) = tierOffset g₀ i w k + ((g₀ w[k]).word i).length := by
  unfold tierOffset
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.map_append,
    List.sum_append, List.map_singleton, List.sum_singleton]

theorem tierOffset_mono : Monotone (tierOffset g₀ i w) :=
  monotone_nat_of_le_succ fun k ↦ by
    by_cases hk : k < w.length
    · rw [tierOffset_succ g₀ i w hk]
      exact Nat.le_add_right _ _
    · simp [tierOffset, List.take_of_length_le (not_lt.1 hk),
        List.take_of_length_le (Nat.le_succ_of_le (not_lt.1 hk))]

/-- The tokens of a symbol on a tier stand before those of every later symbol. -/
theorem tierOffset_add_length_le {k k' : ℕ} (h : k < k') (hk : k < w.length) :
    tierOffset g₀ i w k + ((g₀ w[k]).word i).length ≤ tierOffset g₀ i w k' := by
  rw [← tierOffset_succ g₀ i w hk]
  exact tierOffset_mono g₀ i w h

theorem tierOffset_length :
    tierOffset g₀ i w w.length = ((w.map g₀).prod.word i).length := by
  simp [tierOffset, word_prod, List.length_flatten, Function.comp_def]

/-- On a tier where every primitive has one token, a symbol's offset is its index. -/
theorem tierOffset_of_length_eq_one (h : ∀ s, ((g₀ s).word i).length = 1) {k : ℕ}
    (hk : k ≤ w.length) : tierOffset g₀ i w k = k := by
  simp [tierOffset, h, hk]

theorem length_word_prod_map_of_length_eq_one (h : ∀ s, ((g₀ s).word i).length = 1) :
    ((w.map g₀).prod.word i).length = w.length := by
  rw [← tierOffset_length, tierOffset_of_length_eq_one g₀ i w h le_rfl]

/-- A token of the `k`th symbol stands at that symbol's offset. -/
theorem getElem?_word_prod_map {k : ℕ} (hk : k < w.length) {r : ℕ}
    (hr : r < ((g₀ w[k]).word i).length) :
    ((w.map g₀).prod.word i)[tierOffset g₀ i w k + r]? = ((g₀ w[k]).word i)[r]? := by
  induction w generalizing k with
  | nil => simp at hk
  | cons a w ih =>
    rw [List.map_cons, List.prod_cons, word_mul]
    cases k with
    | zero =>
      simp only [tierOffset_zero, Nat.zero_add, List.getElem_cons_zero] at hr ⊢
      exact List.getElem?_append_left hr
    | succ k =>
      simp only [tierOffset_cons_succ, List.getElem_cons_succ] at hr ⊢
      rw [Nat.add_assoc, List.getElem?_append_right (Nat.le_add_right _ _),
        Nat.add_sub_cancel_left]
      exact ih (Nat.lt_of_succ_lt_succ hk) hr

/-- Symbols with a token on a tier are told apart by their offsets there. -/
theorem eq_of_tierOffset_eq {k k' : ℕ} (hk : k < w.length) (hk' : k' < w.length)
    (h : (g₀ w[k]).word i ≠ []) (h' : (g₀ w[k']).word i ≠ [])
    (he : tierOffset g₀ i w k = tierOffset g₀ i w k') : k = k' := by
  rcases Nat.lt_trichotomy k k' with hlt | rfl | hlt
  · have := tierOffset_add_length_le g₀ i w hlt hk
    have := List.length_pos_iff.2 h
    omega
  · rfl
  · have := tierOffset_add_length_le g₀ i w hlt hk'
    have := List.length_pos_iff.2 h'
    omega

theorem tierOffset_lt_length {k : ℕ} (hk : k < w.length)
    (h : (g₀ w[k]).word i ≠ []) :
    tierOffset g₀ i w k < ((w.map g₀).prod.word i).length := by
  rw [← tierOffset_length]
  exact lt_of_lt_of_le (Nat.lt_add_of_pos_right (List.length_pos_iff.2 h))
    (tierOffset_add_length_le g₀ i w hk hk)


variable {g₀ w} {i j : ι} {p q : ℕ}

/-- When the primitives have at most one token on each of two tiers, the lines of a
realization between them are the lines of its symbols, each at that symbol's offsets. -/
theorem link_prod_map_of_length_le_one (hi : ∀ s, ((g₀ s).word i).length ≤ 1)
    (hj : ∀ s, ((g₀ s).word j).length ≤ 1) :
    (w.map g₀).prod.Link i j p q ↔ ∃ k, ∃ hk : k < w.length,
      p = tierOffset g₀ i w k ∧ q = tierOffset g₀ j w k ∧ (g₀ w[k]).Link i j 0 0 := by
  rw [link_prod_map]
  constructor
  · rintro ⟨k, hk, hp, hq, h⟩
    have h₁ := h.lt_left
    have h₂ := h.lt_right
    have := hi w[k]
    have := hj w[k]
    obtain rfl : p = tierOffset g₀ i w k := by omega
    obtain rfl : q = tierOffset g₀ j w k := by omega
    exact ⟨k, hk, rfl, rfl, by simpa using h⟩
  · rintro ⟨k, hk, rfl, rfl, h⟩
    exact ⟨k, hk, le_rfl, le_rfl, by simpa using h⟩


end Offset

end AR

end Autosegmental
