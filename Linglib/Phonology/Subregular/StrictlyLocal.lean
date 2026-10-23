/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Computability.Language
public import Linglib.Phonology.Subregular.Boundary
public import Linglib.Core.Computability.LocallyTestable
public import Linglib.Core.Data.List.Factors

/-!
# Strictly local languages (SL_k)

A language `L` is **strictly `k`-local** when membership is determined by the
length-`k` substrings of the boundary-augmented input: a grammar is a set `G` of
permitted `k`-factors, and `w ∈ L` iff every `k`-factor of `boundary k w` lies in
`G`. The forbidden-factor dual (`G = Fᶜ`) is finite even over an infinite alphabet.

## Main definitions

* `StrictlyLocalGrammar α`: a grammar is just a set of permitted factors over
  `Augmented α`; the locality width `k` is supplied to `language`, not baked in.
* `StrictlyLocalGrammar.language k`: the `Language α` it generates at width `k`.
* `StrictlyLocalGrammar.ofForbidden`: the grammar of a forbidden-factor set (its
  complement).
* `Language.IsStrictlyLocal L k`: `L` is strictly `k`-local.
* `Language.SuffixSubstitutionClosed L k`: members sharing a length-`(k − 1)` window
  admit suffix crossover.

## Main results

* `Language.isStrictlyLocal_iff_suffixSubstitutionClosed`: for `k ≥ 2`, strict
  `k`-locality is exactly closure under suffix substitution: the crossover's factors
  split into the two members' shared parts, and conversely the canonical grammar of
  licensed factors regenerates the language by stitching a member window-by-window.

* `Language.IsStrictlyLocal.toIsLocallyTestable`: `SL_k ⊆ LT_k`.
* `Language.IsStrictlyLocal.isStarFree`: `SL_k ⊆ SF` over a finite alphabet.

## References

* [rogers-pullum-2011]
* [mcnaughton-papert-1971]
-/

@[expose] public section

variable {α : Type*}

/-- A **strictly-local grammar** over `α` is a set of *permitted* factors over the
boundary-augmented alphabet `Option α`, with `none` the boundary. The locality width `k` is an
argument of `language`. -/
abbrev StrictlyLocalGrammar (α : Type*) := Set (Augmented α)

namespace StrictlyLocalGrammar

/-- The language generated at width `k` consists of the strings whose boundary-augmented form
has every `k`-factor permitted. -/
def language (k : ℕ) (G : StrictlyLocalGrammar α) : Language α :=
  {w | ∀ f ∈ List.kFactors k (boundary k w), f ∈ G}

@[simp] lemma mem_language (k : ℕ) (G : StrictlyLocalGrammar α) (w : List α) :
    w ∈ G.language k ↔ ∀ f ∈ List.kFactors k (boundary k w), f ∈ G :=
  Iff.rfl

/-- The grammar of a **forbidden**-factor set is its complement: a string is
accepted iff none of its `k`-factors are forbidden. -/
def ofForbidden (forbidden : Set (Augmented α)) : StrictlyLocalGrammar α := forbiddenᶜ

@[simp] lemma mem_ofForbidden_language (forbidden : Set (Augmented α)) (k : ℕ)
    (w : List α) :
    w ∈ (ofForbidden forbidden).language k
      ↔ ∀ f ∈ List.kFactors k (boundary k w), f ∉ forbidden :=
  Iff.rfl

theorem mem_language_iff_window {k : ℕ} {G : StrictlyLocalGrammar α} {w : List α} (hk : 1 ≤ k) :
    w ∈ G.language k ↔ ∀ i : ℤ, 1 - k ≤ i → i < w.length → window k w i ∈ G := by
  rw [mem_language]
  constructor
  · intro h i h1 h2
    exact h _ ((mem_kFactors_boundary_iff hk).mpr ⟨i, h1, h2, rfl⟩)
  · intro h f hf
    obtain ⟨i, h1, h2, rfl⟩ := (mem_kFactors_boundary_iff hk).mp hf
    exact h i h1 h2

/-! ### Count-vector characterisation

Membership in a forbidden-factor SL language is a zero-test of a single
linear functional of the word's `k`-factor count vector — the total count of
forbidden factors — with unit margin on nonmembers. Strict locality is thus
linearly detectable on the factor-count (cue) representation. -/

variable [DecidableEq α]

theorem mem_ofForbidden_language_iff_sum_count_eq_zero
    (F : Finset (Augmented α)) (k : ℕ) (w : List α) :
    w ∈ (ofForbidden ↑F).language k
      ↔ ∑ f ∈ F, (List.kFactors k (boundary k w)).count f = 0 := by
  simp only [mem_ofForbidden_language, Finset.mem_coe, Finset.sum_eq_zero_iff,
             List.count_eq_zero]
  exact ⟨fun h f hf hmem ↦ h f hmem hf, fun h f hmem hf ↦ h f hf hmem⟩

theorem one_le_sum_count_of_not_mem_ofForbidden_language
    {F : Finset (Augmented α)} {k : ℕ} {w : List α}
    (h : w ∉ (ofForbidden ↑F).language k) :
    1 ≤ ∑ f ∈ F, (List.kFactors k (boundary k w)).count f :=
  Nat.one_le_iff_ne_zero.mpr fun h0 ↦
    h ((mem_ofForbidden_language_iff_sum_count_eq_zero F k w).mpr h0)

end StrictlyLocalGrammar

namespace Language

variable {α : Type*}


/-- A language `L` is **strictly `k`-local** iff some `StrictlyLocalGrammar α` generates it at
width `k`. Witness-style, mirroring `Language.IsRegular`/`Language.IsContextFree`
("L is regular iff some DFA accepts L"). -/
def IsStrictlyLocal (L : Language α) (k : ℕ) : Prop :=
  ∃ G : StrictlyLocalGrammar α, G.language k = L

/-! ### Suffix substitution closure -/

/-- `L` is closed under *suffix substitution* at width `k` when two members sharing a
length-`(k − 1)` window admit the crossover of their suffixes at it. -/
def SuffixSubstitutionClosed (L : Language α) (k : ℕ) : Prop :=
  ∀ u₁ v₁ u₂ v₂ x : List α, x.length = k - 1 →
    u₁ ++ x ++ v₁ ∈ L → u₂ ++ x ++ v₂ ∈ L → u₁ ++ x ++ v₂ ∈ L

theorem IsStrictlyLocal.suffixSubstitutionClosed {L : Language α} {k : ℕ}
    (h : L.IsStrictlyLocal k) : L.SuffixSubstitutionClosed k := by
  obtain ⟨G, rfl⟩ := h
  intro u₁ v₁ u₂ v₂ x hx h₁ h₂ f hf
  rw [List.mem_kFactors] at hf
  obtain ⟨⟨s, t, hst⟩, hlen⟩ := hf
  have hPfx : ∀ v : List α, (List.replicate (k - 1) none ++ (u₁ ++ x).map some)
      <+: boundary k (u₁ ++ x ++ v) := fun v ↦
    ⟨v.map some ++ List.replicate (k - 1) none, by simp [boundary, List.append_assoc]⟩
  have hSfx : ∀ u : List α, ((x ++ v₂).map some ++ List.replicate (k - 1) none)
      <:+ boundary k (u ++ x ++ v₂) := fun u ↦
    ⟨List.replicate (k - 1) none ++ u.map some, by simp [boundary, List.append_assoc]⟩
  rcases le_or_gt (s.length + k) (k - 1 + (u₁.length + x.length)) with hcase | hcase
  · apply h₁
    rw [List.mem_kFactors]
    refine ⟨List.IsInfix.trans ?_ (hPfx v₁).isInfix, hlen⟩
    have hsf : s ++ f <+: List.replicate (k - 1) none ++ (u₁ ++ x).map some := by
      refine List.prefix_of_prefix_length_le
        ⟨t, by simpa [List.append_assoc] using hst⟩ (hPfx v₂) ?_
      simp only [List.length_append, List.length_replicate, List.length_map, hlen]
      omega
    exact (List.suffix_append s f).isInfix.trans hsf.isInfix
  · apply h₂
    rw [List.mem_kFactors]
    refine ⟨List.IsInfix.trans ?_ (hSfx u₂).isInfix, hlen⟩
    have hft : f ++ t <:+ (x ++ v₂).map some ++ List.replicate (k - 1) none := by
      refine List.suffix_of_suffix_length_le
        ⟨s, by simpa [List.append_assoc] using hst⟩ (hSfx u₁) ?_
      have hL := congrArg List.length hst
      simp only [List.length_append, length_boundary, hlen] at hL
      simp only [List.length_append, List.length_map, List.length_replicate, hlen]
      omega
    exact (List.prefix_append f t).isInfix.trans hft.isInfix

theorem SuffixSubstitutionClosed.isStrictlyLocal {L : Language α} {k : ℕ} (hk : 2 ≤ k)
    (h : L.SuffixSubstitutionClosed k) : L.IsStrictlyLocal k := by
  refine ⟨{f | ∃ z ∈ L, f ∈ List.kFactors k (boundary k z)}, ?_⟩
  ext w
  rw [StrictlyLocalGrammar.mem_language_iff_window (by omega)]
  refine ⟨fun hw ↦ ?_, fun hw i h1 h2 ↦
    ⟨w, hw, (mem_kFactors_boundary_iff (by omega)).mpr ⟨i, h1, h2, rfl⟩⟩⟩
  have hwin : ∀ i : ℤ, 1 - (k : ℤ) ≤ i → i < w.length →
      ∃ y ∈ L, ∃ q : ℤ, 1 - (k : ℤ) ≤ q ∧ q < y.length ∧
        ∀ j : ℕ, j < k → y[q + j]? = w[i + j]? := by
    intro i hi1 hi2
    obtain ⟨y, hy, hf⟩ := hw i hi1 hi2
    obtain ⟨q, hq1, hq2, hq3⟩ := (mem_kFactors_boundary_iff (by omega)).mp hf
    exact ⟨y, hy, q, hq1, hq2, fun j hj ↦ (window_eq_window_iff.mp hq3 j hj).symm⟩
  clear hw
  rcases eq_or_ne w [] with rfl | hne
  · -- the empty word: any witness for its all-blank window is itself empty
    obtain ⟨y, hy, q, hq1, hq2, hmatch⟩ := hwin (1 - k) le_rfl (by simp; omega)
    have hall : ∀ j : ℕ, j < k → y[q + j]? = none := fun j hj ↦ by
      rw [hmatch j hj, List.getElem?_int_nil]
    have hnil : y = [] := by
      rcases lt_or_ge q 0 with hq0 | hq0
      · have h0 := hall (-q).toNat (by omega)
        rw [show q + (((-q).toNat : ℕ) : ℤ) = 0 by omega] at h0
        have hc := List.getElem?_int_eq_none_iff.mp h0
        exact List.length_eq_zero_iff.mp (by omega)
      · have hc := List.getElem?_int_eq_none_iff.mp (by simpa using hall 0 (by omega))
        exact List.length_eq_zero_iff.mp (by omega)
    exact hnil ▸ hy
  have hn1 : 0 < w.length := List.length_pos_of_ne_nil hne
  rcases lt_or_ge w.length (k - 1) with hsmall | hbig
  · -- short word: the window at `w.length + 1 - k` shows both edges, pinning its
    -- witness to the whole word
    obtain ⟨y, hy, q, hq1, hq2, hmatch⟩ := hwin ((w.length : ℤ) + 1 - k)
      (by omega) (by omega)
    have hnone : y[q + ((k - 2 - w.length : ℕ) : ℤ)]? = none := by
      rw [hmatch _ (by omega),
        show ((w.length : ℤ) + 1 - k) + ((k - 2 - w.length : ℕ) : ℤ) = -1 by omega,
        List.getElem?_int_of_neg (show (-1 : ℤ) < 0 by omega)]
    have hsome : y[q + ((k - 1 - w.length : ℕ) : ℤ)]? = w[(0 : ℤ)]? := by
      rw [hmatch _ (by omega),
        show ((w.length : ℤ) + 1 - k) + ((k - 1 - w.length : ℕ) : ℤ) = 0 by omega]
    obtain ⟨a, ha⟩ : ∃ a, w[(0 : ℤ)]? = some a := by
      rw [List.getElem?_int_of_nonneg le_rfl]
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨hb1, hb2⟩ := (getElem?_eq_some_iff.mp (hsome.trans ha)).1
    have hpin : q = (w.length : ℤ) + 1 - k := by
      rcases List.getElem?_int_eq_none_iff.mp hnone with hc | hc <;> omega
    suffices hyw : y = w by exact hyw ▸ hy
    apply List.ext_getElem?_int
    intro j hj
    rcases lt_or_ge j ((w.length : ℤ) + 1 - k) with hji | hji
    · rw [List.getElem?_int_of_neg (by omega), List.getElem?_int_of_neg (by omega)]
    · have hjw : ((j - ((w.length : ℤ) + 1 - k)).toNat) < k := by omega
      have hmt := hmatch _ hjw
      rwa [hpin, show ((w.length : ℤ) + 1 - k)
          + (((j - ((w.length : ℤ) + 1 - k)).toNat : ℕ) : ℤ) = j by omega] at hmt
  · -- long word: march a member along the word, then cut its tail
    have march : ∀ c : ℕ, c ≤ w.length →
        ∃ z ∈ L, ∀ j : ℤ, j < (c : ℤ) → z[j]? = w[j]? := by
      intro c
      induction c with
      | zero =>
        intro _
        obtain ⟨y, hy, -⟩ := hwin (1 - k) le_rfl (by omega)
        exact ⟨y, hy, fun j hj ↦ by
          rw [List.getElem?_int_of_neg (by omega), List.getElem?_int_of_neg (by omega)]⟩
      | succ c ih =>
        intro hc1
        obtain ⟨y, hy, q, hq1, hq2, hmatch⟩ := hwin ((c : ℤ) + 1 - k)
          (by omega) (by omega)
        rcases lt_or_ge c (k - 1) with hcA | hcB
        · -- pin phase: the window shows the left edge, so the match is aligned
          have hnone : y[q + ((k - 2 - c : ℕ) : ℤ)]? = none := by
            rw [hmatch _ (by omega),
              show ((c : ℤ) + 1 - k) + ((k - 2 - c : ℕ) : ℤ) = -1 by omega,
              List.getElem?_int_of_neg (show (-1 : ℤ) < 0 by omega)]
          have hsome : y[q + ((k - 1 - c : ℕ) : ℤ)]? = w[(0 : ℤ)]? := by
            rw [hmatch _ (by omega),
              show ((c : ℤ) + 1 - k) + ((k - 1 - c : ℕ) : ℤ) = 0 by omega]
          obtain ⟨a, ha⟩ : ∃ a, w[(0 : ℤ)]? = some a := by
            rw [List.getElem?_int_of_nonneg le_rfl]
            exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
          obtain ⟨hb1, hb2⟩ := (getElem?_eq_some_iff.mp (hsome.trans ha)).1
          have hpin : q = (c : ℤ) + 1 - k := by
            rcases List.getElem?_int_eq_none_iff.mp hnone with hc0 | hc0 <;> omega
          refine ⟨y, hy, fun j hj ↦ ?_⟩
          rcases lt_or_ge j ((c : ℤ) + 1 - k) with hji | hji
          · rw [List.getElem?_int_of_neg (by omega), List.getElem?_int_of_neg (by omega)]
          · have hjw : ((j - ((c : ℤ) + 1 - k)).toNat) < k := by omega
            have hmt := hmatch _ hjw
            rwa [hpin, show ((c : ℤ) + 1 - k)
                + (((j - ((c : ℤ) + 1 - k)).toNat : ℕ) : ℤ) = j by omega] at hmt
        · -- crossover phase: an all-letter window; substitute its suffix into the
          -- marched member
          obtain ⟨z, hz, hzag⟩ := ih (by omega)
          have hq0 : 0 ≤ q := by
            have h0 := hmatch 0 (by omega)
            rw [List.getElem?_int_of_nonneg (w := w) (by omega)] at h0
            have h3 := h0.trans (List.getElem?_eq_getElem (by omega))
            have := ((getElem?_eq_some_iff.mp h3).1).1
            omega
          have hqtop : q + k ≤ y.length := by
            have hlast := hmatch (k - 1) (by omega)
            rw [List.getElem?_int_of_nonneg (w := w) (by omega)] at hlast
            have h3 := hlast.trans (List.getElem?_eq_getElem (by omega))
            have := ((getElem?_eq_some_iff.mp h3).1).2
            omega
          have hmid : (y.drop q.toNat).take k = (w.drop (c + 1 - k)).take k := by
            apply List.ext_getElem?
            intro t
            rcases lt_or_ge t k with ht | ht
            · rw [List.getElem?_take_of_lt ht, List.getElem?_take_of_lt ht,
                List.getElem?_drop, List.getElem?_drop]
              have hmt := hmatch t ht
              rwa [show q + (t : ℕ) = ((q.toNat + t : ℕ) : ℤ) by omega,
                show ((c : ℤ) + 1 - k) + (t : ℕ) = ((c + 1 - k + t : ℕ) : ℤ) by omega,
                List.getElem?_natCast, List.getElem?_natCast] at hmt
            · rw [List.getElem?_take_eq_none ht, List.getElem?_take_eq_none ht]
          have hwmid : (w.drop (c + 1 - k)).take (k - 1) ++ [w[c]'(by omega)]
              = (w.drop (c + 1 - k)).take k := by
            rw [show ([w[c]'(by omega)] : List α)
                = ((w.drop (c + 1 - k)).drop (k - 1)).take 1 from by
              rw [List.drop_drop, show (c + 1 - k) + (k - 1) = c by omega,
                List.drop_eq_getElem_cons (show c < w.length by omega)]
              rfl]
            rw [← List.take_add, show (k - 1) + 1 = k by omega]
          have hysplit : y = y.take q.toNat
              ++ ((w.drop (c + 1 - k)).take k ++ y.drop (q.toNat + k)) := by
            conv_lhs => rw [← List.take_append_drop q.toNat y,
              ← List.take_append_drop k (y.drop q.toNat)]
            rw [hmid, List.drop_drop]
          have hzsplit : z = (w.take (c + 1 - k) ++ (w.drop (c + 1 - k)).take (k - 1))
              ++ z.drop c := by
            conv_lhs => rw [← List.take_append_drop c z]
            rw [List.ext_take_getElem?_int hzag,
              show w.take c = w.take (c + 1 - k) ++ (w.drop (c + 1 - k)).take (k - 1)
                from by rw [← List.take_add, show (c + 1 - k) + (k - 1) = c by omega]]
          have hxlen : ((w.drop (c + 1 - k)).take (k - 1)).length = k - 1 := by
            simp
            omega
          have hy2 : (y.take q.toNat ++ (w.drop (c + 1 - k)).take (k - 1))
              ++ ([w[c]'(by omega)] ++ y.drop (q.toNat + k)) ∈ L := by
            have hyass : y = (y.take q.toNat ++ (w.drop (c + 1 - k)).take (k - 1))
                ++ ([w[c]'(by omega)] ++ y.drop (q.toNat + k)) := by
              conv_lhs => rw [hysplit, ← hwmid]
              simp [List.append_assoc]
            exact hyass ▸ hy
          have hnew := h (w.take (c + 1 - k)) (z.drop c) (y.take q.toNat)
            ([w[c]'(by omega)] ++ y.drop (q.toNat + k))
            ((w.drop (c + 1 - k)).take (k - 1)) hxlen (hzsplit ▸ hz) hy2
          have htake : w.take (c + 1 - k) ++ (w.drop (c + 1 - k)).take k
              = w.take (c + 1) := by
            rw [← List.take_add, show (c + 1 - k) + k = c + 1 by omega]
          have hz' : w.take (c + 1) ++ y.drop (q.toNat + k) ∈ L := by
            have heq : w.take (c + 1) ++ y.drop (q.toNat + k)
                = (w.take (c + 1 - k) ++ (w.drop (c + 1 - k)).take (k - 1))
                  ++ ([w[c]'(by omega)] ++ y.drop (q.toNat + k)) := by
              rw [← htake, ← hwmid]
              simp [List.append_assoc]
            exact heq ▸ hnew
          refine ⟨w.take (c + 1) ++ y.drop (q.toNat + k), hz', fun j hj ↦ ?_⟩
          rcases lt_or_ge j 0 with hj0 | hj0
          · rw [List.getElem?_int_of_neg hj0, List.getElem?_int_of_neg hj0]
          · rw [List.getElem?_int_append_left (by simp; omega),
              List.getElem?_int_take_of_lt (by omega)]
    -- cut the marched member's tail with the final window
    obtain ⟨z, hz, hzag⟩ := march w.length le_rfl
    obtain ⟨y, hy, q, hq1, hq2, hmatch⟩ := hwin ((w.length : ℤ) + 1 - k)
      (by omega) (by omega)
    have hq0 : 0 ≤ q := by
      have h0 := hmatch 0 (by omega)
      rw [List.getElem?_int_of_nonneg (w := w) (by omega)] at h0
      have h3 := h0.trans (List.getElem?_eq_getElem (by omega))
      have := ((getElem?_eq_some_iff.mp h3).1).1
      omega
    have hnone : y[q + ((k - 1 : ℕ) : ℤ)]? = none := by
      rw [hmatch _ (by omega), List.getElem?_int_of_nonneg (by omega),
        List.getElem?_eq_none (by omega)]
    have hsome : y[q + ((k - 2 : ℕ) : ℤ)]? = w[((w.length - 1 : ℕ) : ℤ)]? := by
      rw [hmatch _ (by omega),
        show ((w.length : ℤ) + 1 - k) + ((k - 2 : ℕ) : ℤ) = ((w.length - 1 : ℕ) : ℤ)
          by omega]
    obtain ⟨a, ha⟩ : ∃ a, w[((w.length - 1 : ℕ) : ℤ)]? = some a := by
      rw [List.getElem?_natCast]
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨hb1, hb2⟩ := (getElem?_eq_some_iff.mp (hsome.trans ha)).1
    have hylen : (y.length : ℤ) = q + k - 1 := by
      rcases List.getElem?_int_eq_none_iff.mp hnone with hc | hc <;> omega
    have hyfin : y = y.take q.toNat ++ w.drop (w.length + 1 - k) := by
      conv_lhs => rw [← List.take_append_drop q.toNat y]
      congr 1
      apply List.ext_getElem?
      intro t
      rcases lt_or_ge t (k - 1) with ht | ht
      · rw [List.getElem?_drop, List.getElem?_drop]
        have hmt := hmatch t (by omega)
        rwa [show q + (t : ℕ) = ((q.toNat + t : ℕ) : ℤ) by omega,
          show ((w.length : ℤ) + 1 - k) + (t : ℕ) = ((w.length + 1 - k + t : ℕ) : ℤ)
            by omega, List.getElem?_natCast, List.getElem?_natCast] at hmt
      · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
    have hzw : z = w ++ z.drop w.length := by
      conv_lhs => rw [← List.take_append_drop w.length z]
      rw [List.ext_take_getElem?_int hzag, List.take_length]
    have hxlen : (w.drop (w.length + 1 - k)).length = k - 1 := by
      simp
      omega
    have hnew := h (w.take (w.length + 1 - k)) (z.drop w.length) (y.take q.toNat) []
      (w.drop (w.length + 1 - k)) hxlen
      (by rw [List.take_append_drop]; exact hzw ▸ hz)
      (by rw [List.append_nil]; exact hyfin ▸ hy)
    rwa [List.take_append_drop, List.append_nil] at hnew

/-- For widths `k ≥ 2`, a language is strictly `k`-local if and only if it is closed under
suffix substitution at `k`. -/
theorem isStrictlyLocal_iff_suffixSubstitutionClosed {L : Language α} {k : ℕ}
    (hk : 2 ≤ k) : L.IsStrictlyLocal k ↔ L.SuffixSubstitutionClosed k :=
  ⟨IsStrictlyLocal.suffixSubstitutionClosed, fun hL ↦ hL.isStrictlyLocal hk⟩

/-! ### Local testability -/

/-- A strictly `k`-local language is locally `k`-testable. Padding a word with boundary markers
pulls it back from the words over the augmented alphabet whose factors of length `k` are all
permitted, and that language is locally `k`-testable outright. -/
theorem IsStrictlyLocal.toIsLocallyTestable {L : Language α} {k : ℕ} (h : L.IsStrictlyLocal k) :
    L.IsLocallyTestable k := by
  obtain ⟨G, rfl⟩ := h
  exact (((isLocallyTestable_setOf_kFactors k {S | S ⊆ G}).rightQuotient
    (List.replicate (k - 1) none)).leftQuotient (List.replicate (k - 1) none)).preimage_map some

/-- Over a finite alphabet strictly local languages are star-free. -/
theorem IsStrictlyLocal.isStarFree [Finite α] {L : Language α} {k : ℕ}
    (h : L.IsStrictlyLocal k) : L.IsStarFree :=
  h.toIsLocallyTestable.isStarFree

end Language
