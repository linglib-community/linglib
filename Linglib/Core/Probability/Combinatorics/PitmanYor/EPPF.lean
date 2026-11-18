/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.RingTheory.Polynomial.Pochhammer
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Multiset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# The Pitman–Yor partition probability function

`pitmanYorEPPF α θ s` is the probability the Pitman–Yor partition with discount `α` and
concentration `θ` gives to a partition whose multiset of block sizes is `s`,
$∏_{1 ≤ i < k} (θ + i α) ∏_i ∏_{1 ≤ j < n_i} (j - α) / ∏_{1 ≤ i < n} (θ + i)$ for `k` blocks of
sizes $n_i$ summing to $n$. A new singleton block
[multiplies it](##ProbabilityTheory.pitmanYorEPPF_cons_one) by $(θ + k α) / (n + θ)$ and one more
element in a block of size $m$ [multiplies it](##ProbabilityTheory.pitmanYorEPPF_cons_succ_erase)
by $(m - α) / (n + θ)$. At $α = 0$ it is the
[Ewens sampling formula](##ProbabilityTheory.pitmanYorEPPF_zero_left).

## Implementation notes

The products run over `Ico 1 m`, as in $(θ + α)_{k-1↑α} = ∏_{1 ≤ i < k} (θ + i α)$, avoiding
truncated subtraction. The function is defined for all real `α` and `θ` and all multisets.

## References

* [pitman-2006]
-/

@[expose] public section

open Finset
open scoped Nat

namespace ProbabilityTheory

variable {α θ : ℝ}

/-- The *exchangeable partition probability function* of the Pitman–Yor partition
([pitman-2006] (3.6)): the probability that the seating of `n` customers is a given set
partition whose multiset of block sizes is `s`, where `n = s.sum`. -/
noncomputable def pitmanYorEPPF (α θ : ℝ) (s : Multiset ℕ) : ℝ :=
  (∏ i ∈ Ico 1 s.card, (θ + i * α)) * (s.map fun m : ℕ ↦ ∏ j ∈ Ico 1 m, ((j : ℝ) - α)).prod /
    ∏ i ∈ Ico 1 s.sum, (θ + i)

@[simp]
theorem pitmanYorEPPF_zero : pitmanYorEPPF α θ 0 = 1 := by
  simp [pitmanYorEPPF]

/-- Opening a new table multiplies the EPPF by `(θ + k α) / (n + θ)` ([pitman-2006] p. 61). -/
theorem pitmanYorEPPF_cons_one {s : Multiset ℕ} (hs : s.sum ≠ 0) :
    pitmanYorEPPF α θ (1 ::ₘ s) = pitmanYorEPPF α θ s * ((θ + s.card * α) / (s.sum + θ)) := by
  have hk : 1 ≤ s.card := Multiset.card_pos.mpr (by rintro rfl; simp at hs)
  rw [pitmanYorEPPF, pitmanYorEPPF, div_mul_div_comm, Multiset.card_cons, Multiset.map_cons,
    Multiset.prod_cons, Multiset.sum_cons, Ico_self, prod_empty, one_mul, prod_Ico_succ_top hk,
    add_comm 1, prod_Ico_succ_top (Nat.one_le_iff_ne_zero.mpr hs)]
  congr 1 <;> push_cast <;> ring

/-- Joining a table of `m` customers multiplies the EPPF by `(m - α) / (n + θ)` ([pitman-2006]
(3.22)). -/
theorem pitmanYorEPPF_cons_succ_erase {s : Multiset ℕ} {m : ℕ} (hm : m ∈ s) (hm₀ : m ≠ 0) :
    pitmanYorEPPF α θ ((m + 1) ::ₘ s.erase m) = pitmanYorEPPF α θ s * ((m - α) / (s.sum + θ)) := by
  have hm₁ : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm₀
  rw [pitmanYorEPPF, pitmanYorEPPF, div_mul_div_comm, Multiset.card_cons,
    Multiset.card_erase_add_one hm, Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons,
    ← Multiset.prod_map_erase hm, prod_Ico_succ_top hm₁, add_right_comm, Multiset.sum_erase hm,
    prod_Ico_succ_top (hm₁.trans (Multiset.le_sum_of_mem hm))]
  congr 1 <;> push_cast <;> ring

/-- At `α = 0` the EPPF is the Ewens sampling formula ([pitman-2006] (2.19)). -/
theorem pitmanYorEPPF_zero_left {s : Multiset ℕ} (hθ : θ ≠ 0) (hs : s.sum ≠ 0) :
    pitmanYorEPPF 0 θ s =
      θ ^ s.card / (ascPochhammer ℝ s.sum).eval θ * (s.map fun m ↦ ((m - 1)! : ℝ)).prod := by
  obtain ⟨k, hk⟩ : ∃ k, s.card = k + 1 :=
    Nat.exists_eq_succ_of_ne_zero (by rintro h; simp [Multiset.card_eq_zero.mp h] at hs)
  have hfact (m : ℕ) : ∏ j ∈ Ico 1 m, ((j : ℝ) - 0) = ((m - 1)! : ℝ) := by
    cases m with
    | zero => simp
    | succ m =>
      rw [Nat.add_sub_cancel, ← prod_Ico_id_eq_factorial, Nat.cast_prod]
      simp
  rw [pitmanYorEPPF, ascPochhammer_eval_eq_prod_range,
    prod_range_eq_mul_Ico _ (Nat.pos_of_ne_zero hs), Multiset.map_congr rfl fun m _ ↦ hfact m]
  simp only [mul_zero, add_zero, prod_const, Nat.card_Ico, hk, Nat.add_sub_cancel,
    CharP.cast_eq_zero, pow_succ]
  field_simp

theorem pitmanYorEPPF_one_replicate_one (hθ : -1 < θ) (k : ℕ) :
    pitmanYorEPPF 1 θ (Multiset.replicate k 1) = 1 := by
  simp only [pitmanYorEPPF, Multiset.card_replicate, Multiset.sum_replicate, smul_eq_mul, mul_one,
    Multiset.map_replicate, Ico_self, prod_empty, Multiset.prod_replicate, one_pow]
  refine div_self (prod_ne_zero_iff.mpr fun i hi ↦ ?_)
  have : (1 : ℝ) ≤ i := by exact_mod_cast (mem_Ico.mp hi).1
  linarith

theorem pitmanYorEPPF_nonneg (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (hθ : -α < θ) (s : Multiset ℕ) :
    0 ≤ pitmanYorEPPF α θ s := by
  refine div_nonneg (mul_nonneg (prod_nonneg fun i hi ↦ ?_) (Multiset.prod_nonneg fun x hx ↦ ?_))
    (prod_nonneg fun i hi ↦ ?_)
  · have : (1 : ℝ) ≤ i := by exact_mod_cast (mem_Ico.mp hi).1
    nlinarith
  · obtain ⟨m, -, rfl⟩ := Multiset.mem_map.mp hx
    refine prod_nonneg fun j hj ↦ ?_
    have : (1 : ℝ) ≤ j := by exact_mod_cast (mem_Ico.mp hj).1
    linarith
  · have : (1 : ℝ) ≤ i := by exact_mod_cast (mem_Ico.mp hi).1
    linarith

end ProbabilityTheory
