/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Multiset
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Data.Multiset.Bind

/-!
# Inverse-power sums over multisets of naturals

`Multiset.invPowSum α m` is the sum of `n⁻ᵅ` over a multiset `m` of naturals. A multiset `t`
dominates `s` when some submultiset of `t` matches `s` entry for entry, each matched entry of
`t` being at most its partner in `s`. Then `s.invPowSum α ≤ t.invPowSum α` at every exponent
`0 ≤ α`, and strictly so at every `0 < α` when `s` does not dominate `t` in turn.

Dominance is equivalent to a counting condition of Hall type, that `s` has no more entries below
any threshold than `t` has, so it is first-order stochastic dominance of the counting
distributions, and it is decidable. At a natural exponent `k`, when every entry divides a common
denominator `D`, the sum times `Dᵏ` is the natural number `divPowSum D k m`.

## Main definitions

* `Multiset.invPowSum α m`: the sum of `n⁻ᵅ` over `m`.
* `Multiset.Dominates`, `Multiset.StrictDominates`: dominance and its strict part.
* `Multiset.prodMul s t`: the multiset of pairwise products.
* `Multiset.divPowSum D k m`: the sum of `(D / n)ᵏ` over `m`.

## Main results

* `Multiset.Dominates.invPowSum_le`, `Multiset.StrictDominates.invPowSum_lt`: dominance orders
  the inverse-power sums at every exponent.
* `Multiset.dominates_iff_forall`: dominance is the counting condition.
* `Multiset.invPowSum_prodMul`: the sum over pairwise products is the product of the sums.
* `Multiset.invPowSum_mul_pow_eq_divPowSum`: clearing the common denominator.
-/

@[expose] public section

open scoped ENNReal

namespace Multiset

variable {α : ℝ} {m s t : Multiset ℕ}

/-! ### Inverse-power sums -/

/-- The sum of `n⁻ᵅ` over `m`. Entries equal to `0` contribute `⊤`. -/
noncomputable def invPowSum (α : ℝ) (m : Multiset ℕ) : ℝ≥0∞ :=
  (m.map fun n : ℕ ↦ (n : ℝ≥0∞)⁻¹ ^ α).sum

@[simp] theorem invPowSum_zero (α : ℝ) : (0 : Multiset ℕ).invPowSum α = 0 := rfl

@[simp]
theorem invPowSum_cons (α : ℝ) (n : ℕ) (m : Multiset ℕ) :
    (n ::ₘ m).invPowSum α = (n : ℝ≥0∞)⁻¹ ^ α + m.invPowSum α := by
  simp [invPowSum]

@[simp]
theorem invPowSum_singleton (α : ℝ) (n : ℕ) :
    ({n} : Multiset ℕ).invPowSum α = (n : ℝ≥0∞)⁻¹ ^ α := by
  simp [invPowSum]

@[simp]
theorem invPowSum_add (α : ℝ) (m₁ m₂ : Multiset ℕ) :
    (m₁ + m₂).invPowSum α = m₁.invPowSum α + m₂.invPowSum α := by
  simp [invPowSum]

@[gcongr]
theorem invPowSum_mono (h : s ≤ t) : s.invPowSum α ≤ t.invPowSum α := by
  obtain ⟨u, rfl⟩ := le_iff_exists_add.1 h
  simp

theorem invPowSum_pos (hα : 0 ≤ α) (hm : m ≠ 0) : 0 < m.invPowSum α := by
  obtain ⟨n, hn⟩ := exists_mem_of_ne_zero hm
  obtain ⟨m', rfl⟩ := exists_cons_of_mem hn
  rw [invPowSum_cons]
  exact lt_of_lt_of_le
    (ENNReal.rpow_pos_of_nonneg (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top n)) hα) le_self_add

theorem invPowSum_ne_top (hα : 0 ≤ α) (hs : 0 ∉ s) : s.invPowSum α ≠ ⊤ := by
  refine ne_top_of_le_ne_top (by simp) (sum_le_card_nsmul _ 1 ?_)
  intro x hx
  obtain ⟨n, hn, rfl⟩ := mem_map.1 hx
  have hn' : (1 : ℝ≥0∞) ≤ n := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 fun h ↦ hs (h ▸ hn)
  simpa using ENNReal.rpow_le_rpow (ENNReal.inv_le_one.2 hn') hα

/-! ### Domination -/

/-- A multiset `t` dominates `s` when some submultiset of `t` matches `s` entry for entry, each
matched entry of `t` being at most its partner in `s`. -/
def Dominates (t s : Multiset ℕ) : Prop := ∃ t' ≤ t, Rel (· ≤ ·) t' s

/-- A multiset `t` strictly dominates `s` when it dominates `s` and `s` does not dominate it. It
does so as soon as `t` has a spare entry over the matching, or some matched entry strictly below
its partner. -/
def StrictDominates (t s : Multiset ℕ) : Prop := t.Dominates s ∧ ¬ s.Dominates t

theorem StrictDominates.dominates (h : t.StrictDominates s) : t.Dominates s := h.1

theorem StrictDominates.ne_zero (h : t.StrictDominates s) : t ≠ 0 := by
  rintro rfl
  obtain ⟨⟨t', ht', hrel⟩, hnd⟩ := h
  obtain rfl := le_zero.mp ht'
  obtain rfl := rel_zero_left.mp hrel
  exact hnd ⟨0, le_rfl, Rel.zero⟩

theorem invPowSum_le_invPowSum_of_rel (hα : 0 ≤ α) (h : Rel (· ≤ ·) t s) :
    s.invPowSum α ≤ t.invPowSum α := by
  induction h with
  | zero => simp
  | cons hab _ ih =>
    rw [invPowSum_cons, invPowSum_cons]
    exact add_le_add (ENNReal.rpow_le_rpow (ENNReal.inv_le_inv.2 (Nat.cast_le.2 hab)) hα) ih

theorem Dominates.invPowSum_le (h : t.Dominates s) (hα : 0 ≤ α) :
    s.invPowSum α ≤ t.invPowSum α := by
  obtain ⟨t', ht', hrel⟩ := h
  exact (invPowSum_le_invPowSum_of_rel hα hrel).trans (invPowSum_mono ht')

/-! ### The Hall criterion -/

private theorem exists_min (hs : s ≠ 0) : ∃ x ∈ s, ∀ y ∈ s, x ≤ y :=
  let h := exists_mem_of_ne_zero hs
  ⟨Nat.find h, Nat.find_spec h, fun _ hy ↦ Nat.find_min' h hy⟩

theorem card_filter_le_card_filter_of_rel (h : Rel (· ≤ ·) t s) (k : ℕ) :
    card (s.filter (· ≤ k)) ≤ card (t.filter (· ≤ k)) := by
  induction h with
  | zero => simp
  | @cons a b as bs hab _ ih =>
    by_cases hb : b ≤ k
    · have h₁ : (b ::ₘ bs).filter (· ≤ k) = b ::ₘ bs.filter (· ≤ k) := filter_cons_of_pos _ hb
      have h₂ : (a ::ₘ as).filter (· ≤ k) = a ::ₘ as.filter (· ≤ k) :=
        filter_cons_of_pos _ (hab.trans hb)
      simpa [h₁, h₂] using ih
    · have h₁ : (b ::ₘ bs).filter (· ≤ k) = bs.filter (· ≤ k) := filter_cons_of_neg _ hb
      exact h₁ ▸ ih.trans (card_le_card (filter_le_filter _ (le_cons_self _ _)))

theorem Dominates.card_filter_le (h : t.Dominates s) (k : ℕ) :
    card (s.filter (· ≤ k)) ≤ card (t.filter (· ≤ k)) := by
  obtain ⟨t', ht', hrel⟩ := h
  exact (card_filter_le_card_filter_of_rel hrel k).trans (card_le_card (filter_le_filter _ ht'))

theorem dominates_of_forall_mem
    (h : ∀ k ∈ s, card (s.filter (· ≤ k)) ≤ card (t.filter (· ≤ k))) : t.Dominates s := by
  induction s using Multiset.strongInductionOn generalizing t with
  | _ s ih =>
  rcases eq_or_ne s 0 with rfl | hs
  · exact ⟨0, zero_le _, Rel.zero⟩
  obtain ⟨x, hx, hmin⟩ := exists_min hs
  have hxx : x ∈ s.filter (· ≤ x) := mem_filter.2 ⟨hx, le_rfl⟩
  obtain ⟨y, hy⟩ := card_pos_iff_exists_mem.1 <|
    lt_of_lt_of_le (card_pos_iff_exists_mem.2 ⟨x, hxx⟩) (h x hx)
  obtain ⟨hyt, hyx⟩ := mem_filter.1 hy
  obtain ⟨t', ht', hrel⟩ := @ih (s.erase x) (erase_lt.2 hx) (t.erase y) fun k hk ↦ by
    have hxk : x ≤ k := hmin k (mem_of_mem_erase hk)
    have hsk : s.filter (· ≤ k) = x ::ₘ (s.erase x).filter (· ≤ k) := by
      conv_lhs => rw [← cons_erase hx]
      exact filter_cons_of_pos _ hxk
    have htk : t.filter (· ≤ k) = y ::ₘ (t.erase y).filter (· ≤ k) := by
      conv_lhs => rw [← cons_erase hyt]
      exact filter_cons_of_pos _ (hyx.trans hxk)
    have := h k (mem_of_mem_erase hk)
    rw [hsk, htk, card_cons, card_cons] at this
    omega
  exact ⟨y ::ₘ t', cons_erase hyt ▸ cons_le_cons _ ht', cons_erase hx ▸ Rel.cons hyx hrel⟩

theorem dominates_iff_forall_mem :
    t.Dominates s ↔ ∀ k ∈ s, card (s.filter (· ≤ k)) ≤ card (t.filter (· ≤ k)) :=
  ⟨fun h k _ ↦ h.card_filter_le k, dominates_of_forall_mem⟩

theorem dominates_iff_forall :
    t.Dominates s ↔ ∀ k, card (s.filter (· ≤ k)) ≤ card (t.filter (· ≤ k)) :=
  ⟨Dominates.card_filter_le, fun h ↦ dominates_of_forall_mem fun k _ ↦ h k⟩

instance decidableDominates : DecidableRel Dominates :=
  fun _ _ ↦ decidable_of_iff _ dominates_iff_forall_mem.symm

instance decidableStrictDominates : DecidableRel StrictDominates :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

theorem dominates_refl (s : Multiset ℕ) : s.Dominates s :=
  dominates_iff_forall.2 fun _ ↦ le_rfl

/-! ### Strict domination is strict on inverse-power sums -/

private theorem invPowSum_lt_of_rel_of_ne (hα : 0 < α) :
    ∀ {t s : Multiset ℕ}, Rel (· ≤ ·) t s → t ≠ s → 0 ∉ s →
      s.invPowSum α < t.invPowSum α := by
  intro t s hrel
  induction hrel with
  | zero => exact fun hne _ ↦ absurd rfl hne
  | @cons a b as bs hab hrest ih =>
    intro hne hs
    have hb : b ≠ 0 := fun h ↦ hs (h ▸ mem_cons_self b bs)
    have hbs : 0 ∉ bs := fun h ↦ hs (mem_cons_of_mem h)
    have hbfin : (b : ℝ≥0∞)⁻¹ ^ α ≠ ⊤ :=
      invPowSum_singleton α b ▸ invPowSum_ne_top hα.le (by simpa [eq_comm] using hb)
    rcases eq_or_lt_of_le hab with rfl | hlt
    · rw [invPowSum_cons, invPowSum_cons]
      exact ENNReal.add_lt_add_left hbfin (ih (fun h ↦ hne (by rw [h])) hbs)
    · rw [invPowSum_cons, invPowSum_cons]
      have hhead : (b : ℝ≥0∞)⁻¹ ^ α < (a : ℝ≥0∞)⁻¹ ^ α :=
        ENNReal.rpow_lt_rpow (ENNReal.inv_lt_inv.2 (by exact_mod_cast hlt)) hα
      calc (b : ℝ≥0∞)⁻¹ ^ α + bs.invPowSum α
          < (a : ℝ≥0∞)⁻¹ ^ α + bs.invPowSum α :=
            ENNReal.add_lt_add_right (invPowSum_ne_top hα.le hbs) hhead
        _ ≤ (a : ℝ≥0∞)⁻¹ ^ α + as.invPowSum α :=
            add_le_add le_rfl (invPowSum_le_invPowSum_of_rel hα.le hrest)

theorem StrictDominates.invPowSum_lt (h : t.StrictDominates s) (hα : 0 < α) (hs : 0 ∉ s) :
    s.invPowSum α < t.invPowSum α := by
  obtain ⟨⟨t', ht', hrel⟩, hnd⟩ := h
  rcases eq_or_lt_of_le ht' with rfl | hlt
  · exact invPowSum_lt_of_rel_of_ne hα hrel
      (fun h ↦ hnd (by rw [← h]; exact dominates_refl t')) hs
  · obtain ⟨a, ha⟩ := lt_iff_cons_le.mp hlt
    have hle : s.invPowSum α ≤ t'.invPowSum α := invPowSum_le_invPowSum_of_rel hα.le hrel
    rcases eq_or_ne (t'.invPowSum α) ⊤ with h₁ | h₁
    · exact ((invPowSum_ne_top hα.le hs).lt_top).trans_le
        (le_trans (le_of_eq h₁.symm) (invPowSum_mono ((le_cons_self t' a).trans ha)))
    · have hpos : 0 < (a : ℝ≥0∞)⁻¹ ^ α := by
        simpa using invPowSum_pos (m := {a}) hα.le (by simp)
      calc s.invPowSum α ≤ t'.invPowSum α := hle
        _ < (a ::ₘ t').invPowSum α := by
            rw [invPowSum_cons, add_comm]
            exact ENNReal.lt_add_right h₁ hpos.ne'
        _ ≤ t.invPowSum α := invPowSum_mono ha

/-! ### Pairwise products -/

/-- The multiset of pairwise products of `s` and `t`. -/
def prodMul (s t : Multiset ℕ) : Multiset ℕ := (s ×ˢ t).map fun p ↦ p.1 * p.2

@[simp] theorem zero_prodMul (t : Multiset ℕ) : prodMul 0 t = 0 := rfl

@[simp]
theorem cons_prodMul (n : ℕ) (s t : Multiset ℕ) :
    prodMul (n ::ₘ s) t = t.map (n * ·) + prodMul s t := by
  simp [prodMul]

@[simp]
theorem card_prodMul (s t : Multiset ℕ) : card (prodMul s t) = card s * card t := by
  simp [prodMul]

theorem prodMul_eq_zero_iff {s t : Multiset ℕ} : prodMul s t = 0 ↔ s = 0 ∨ t = 0 := by
  rw [← card_eq_zero, card_prodMul, Nat.mul_eq_zero, card_eq_zero, card_eq_zero]

private theorem natCast_inv_rpow_mul (hα : 0 ≤ α) (a b : ℕ) :
    ((a * b : ℕ) : ℝ≥0∞)⁻¹ ^ α = (a : ℝ≥0∞)⁻¹ ^ α * (b : ℝ≥0∞)⁻¹ ^ α := by
  rw [Nat.cast_mul, ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top b))
    (Or.inl (ENNReal.natCast_ne_top a)), ENNReal.mul_rpow_of_nonneg _ _ hα]

theorem invPowSum_map_mul (hα : 0 ≤ α) (n : ℕ) (t : Multiset ℕ) :
    (t.map (n * ·)).invPowSum α = (n : ℝ≥0∞)⁻¹ ^ α * t.invPowSum α := by
  simp only [invPowSum, map_map, Function.comp_def, natCast_inv_rpow_mul hα, sum_map_mul_left]

theorem invPowSum_prodMul (hα : 0 ≤ α) (s t : Multiset ℕ) :
    (prodMul s t).invPowSum α = s.invPowSum α * t.invPowSum α := by
  induction s using Multiset.induction with
  | empty => simp
  | cons n s ih =>
    rw [cons_prodMul, invPowSum_add, ih, invPowSum_map_mul hα, invPowSum_cons, add_mul]

theorem zero_notMem_prodMul (hs : 0 ∉ s) (ht : 0 ∉ t) : 0 ∉ prodMul s t := by
  simp only [prodMul, Multiset.mem_map, not_exists, not_and]
  intro p hp h0
  rcases Nat.mul_eq_zero.mp h0 with h | h
  · exact hs (h ▸ (Multiset.mem_product.mp hp).1)
  · exact ht (h ▸ (Multiset.mem_product.mp hp).2)

/-! ### Common-denominator power sums -/

/-- The sum of `(D / n)ᵏ` over `m`. When every entry divides `D` it is `invPowSum k m` with the
common denominator `Dᵏ` cleared. -/
def divPowSum (D k : ℕ) (m : Multiset ℕ) : ℕ := (m.map fun n ↦ (D / n) ^ k).sum

@[simp] theorem divPowSum_zero (D k : ℕ) : divPowSum D k 0 = 0 := rfl

theorem ne_zero_of_divPowSum_ne_zero {D k : ℕ} (h : divPowSum D k m ≠ 0) : m ≠ 0 :=
  fun h0 ↦ h (h0 ▸ rfl)

theorem divPowSum_pos {D k : ℕ} (hD : D ≠ 0) (h : ∀ n ∈ m, n ∣ D) (hm : m ≠ 0) :
    0 < divPowSum D k m := by
  obtain ⟨n, hn⟩ := exists_mem_of_ne_zero hm
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h0 ↦ hD (Nat.eq_zero_of_zero_dvd (h0 ▸ h n hn))
  exact lt_of_lt_of_le
    (pow_pos (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hD) (h n hn)) hn0) k)
    (single_le_sum (fun x _ ↦ Nat.zero_le x) _ (mem_map_of_mem _ hn))

/-- At a natural exponent, `invPowSum` times the common denominator `Dᵏ` is `divPowSum`. -/
theorem invPowSum_mul_pow_eq_divPowSum {D : ℕ} (hD : D ≠ 0) (k : ℕ) {m : Multiset ℕ}
    (h : ∀ n ∈ m, n ∣ D) :
    m.invPowSum k * (D : ℝ≥0∞) ^ k = divPowSum D k m := by
  induction m using Multiset.induction with
  | empty => simp
  | cons n m ih =>
    have hn : n ∣ D := h n (mem_cons_self n m)
    have hn0 : n ≠ 0 := fun h0 ↦ hD (Nat.eq_zero_of_zero_dvd (h0 ▸ hn))
    have hD_eq : (D : ℝ≥0∞) ^ k = ((D / n : ℕ) : ℝ≥0∞) ^ k * (n : ℝ≥0∞) ^ k := by
      rw [← mul_pow, ← Nat.cast_mul, Nat.div_mul_cancel hn]
    rw [invPowSum_cons, add_mul, ih fun x hx ↦ h x (mem_cons_of_mem hx),
      ENNReal.rpow_natCast, ← ENNReal.inv_pow, hD_eq, ← mul_assoc,
      mul_comm ((n : ℝ≥0∞) ^ k)⁻¹, mul_assoc,
      ENNReal.inv_mul_cancel (by positivity) (by simp), mul_one]
    simp [divPowSum]

theorem invPowSum_replicate (α : ℝ) (m n : ℕ) :
    (Multiset.replicate m n).invPowSum α = m * (n : ℝ≥0∞)⁻¹ ^ α := by
  rw [invPowSum, map_replicate, sum_replicate, nsmul_eq_mul]

theorem invPowSum_toReal (hα : 0 ≤ α) (hm : 0 ∉ m) :
    (m.invPowSum α).toReal = (m.map fun n : ℕ ↦ ((n : ℝ))⁻¹ ^ α).sum := by
  induction m using Multiset.induction with
  | empty => simp [invPowSum]
  | cons n m ih =>
    have hn : n ≠ 0 := fun h ↦ hm (h ▸ Multiset.mem_cons_self n m)
    have hhead : ((n : ℝ≥0∞))⁻¹ ^ α ≠ ⊤ := by
      rw [ne_eq, ENNReal.rpow_eq_top_iff]
      rintro (⟨-, hneg⟩ | ⟨htop, -⟩)
      · exact absurd hα (not_le.mpr hneg)
      · exact hn (by simpa [ENNReal.inv_eq_top] using htop)
    rw [invPowSum_cons, Multiset.map_cons, Multiset.sum_cons,
      ENNReal.toReal_add hhead (invPowSum_ne_top hα fun h ↦ hm (Multiset.mem_cons_of_mem h)),
      ih fun h ↦ hm (Multiset.mem_cons_of_mem h)]
    congr 1
    rw [← ENNReal.toReal_rpow, ENNReal.toReal_inv, ENNReal.toReal_natCast]

theorem invPowSum_toReal_eq {D : ℕ} (hD : D ≠ 0) (k : ℕ) {m : Multiset ℕ}
    (h : ∀ n ∈ m, n ∣ D) :
    (m.invPowSum k).toReal = (m.divPowSum D k : ℝ) / (D : ℝ) ^ k := by
  have hc := congrArg ENNReal.toReal (invPowSum_mul_pow_eq_divPowSum hD k h)
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast] at hc
  rw [eq_div_iff (pow_ne_zero k (Nat.cast_ne_zero.mpr hD))]
  exact hc

end Multiset
