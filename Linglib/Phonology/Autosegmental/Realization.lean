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

/-- With one tier-`j` position per symbol, the tier-`j` positions of a realization are the
string's positions: a line at position `q` lies inside the `q`-th symbol's primitive. -/
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

end AR

end Autosegmental
