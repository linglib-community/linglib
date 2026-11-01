/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# The Pólya urn

This file defines the prediction rule of the Pólya urn and the probability of a sequence of draws
from it. After draws in which colour `c` came up `x c` times, the urn with positive weights `θ`
draws `c` next with probability proportional to `θ c + x c`. The probability of a sequence
depends only on its counts and is a ratio of rising factorials. The law of the sequence is in
`Linglib.Core.Probability.Distributions.PolyaUrn`.

## Main definitions

* `ProbabilityTheory.countVec`: how often each colour occurs in a sequence.
* `ProbabilityTheory.polyaUrnPredictive`: the probability of each colour on the next draw.
* `ProbabilityTheory.polyaUrnProb`: the probability of a sequence with given counts.

## Main statements

* `ProbabilityTheory.polyaUrnProb_add`: conjugacy, the urn after the counts `x` is the urn with
  weights `θ + x`.
* `ProbabilityTheory.polyaUrnProb_countVec_snoc`: each draw multiplies the probability of the
  sequence by the probability the prediction rule gives it.
* `ProbabilityTheory.sum_polyaUrnPredictive`: the prediction rule is a probability.

## Implementation notes

The weights are a plain function `θ : α → ℝ`, and results that need them positive assume it. One
draw of `c` adds `Pi.single c 1` to the counts, so each step of a sequence is conjugacy there.

## TODO

* The limiting frequencies have the Dirichlet law with parameters `θ`, of which the probability
  of counts `x` is the moment `∫ ∏ c, p c ^ x c`; mathlib has no Dirichlet law yet.
* With `m` colours of weight `κ`, the partition of the draws by colour is the Pitman–Yor
  partition with discount `-κ` and concentration `m κ`.

## References

* [pitman-2006]
-/

@[expose] public section

open Finset

namespace ProbabilityTheory

variable {α : Type*}

/-! ### Count vectors -/

section CountVec

variable [DecidableEq α] {n : ℕ}

/-- The count vector of a sequence records how often each colour occurs in it. -/
def countVec (s : Fin n → α) (c : α) : ℕ :=
  #{i | s i = c}

@[simp]
theorem countVec_zero (s : Fin 0 → α) : countVec s = 0 := by
  funext c; simp [countVec]

theorem countVec_cons (c : α) (s : Fin n → α) :
    countVec (Fin.cons c s : Fin (n + 1) → α) = countVec s + Pi.single c 1 := by
  funext d
  simp only [countVec, card_filter, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Pi.add_apply]
  obtain rfl | hd := eq_or_ne d c
  · simp [add_comm]
  · simp [hd, Ne.symm hd]

theorem countVec_snoc (c : α) (s : Fin n → α) :
    countVec (Fin.snoc s c : Fin (n + 1) → α) = countVec s + Pi.single c 1 := by
  funext d
  simp only [countVec, card_filter, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    Pi.add_apply]
  obtain rfl | hd := eq_or_ne d c
  · simp
  · simp [hd, Ne.symm hd]

theorem countVec_comp_perm (s : Fin n → α) (σ : Equiv.Perm (Fin n)) :
    countVec (s ∘ σ) = countVec s := by
  funext c
  exact card_bij (fun i _ ↦ σ i) (by simp) (fun _ _ _ _ h ↦ σ.injective h)
    (fun j hj ↦ ⟨σ.symm j, by simpa using hj, by simp⟩)

theorem sum_countVec [Fintype α] (s : Fin n → α) : ∑ c, countVec s c = n := by
  simp only [countVec]
  rw [← card_eq_sum_card_fiberwise (f := s) (t := univ) fun _ _ ↦ mem_univ _, card_univ,
    Fintype.card_fin]

end CountVec

/-! ### The prediction rule and the probability of a sequence -/

variable [Fintype α] (θ : α → ℝ)

/-- The probability that the urn with weights `θ` draws colour `c` after draws with counts `x`,
`(θ c + x c) / (∑ θ + ∑ x)` ([pitman-2006] Exercise 2.2.2). -/
noncomputable def polyaUrnPredictive (x : α → ℕ) (c : α) : ℝ :=
  (θ c + x c) / (∑ i, θ i + ∑ i, (x i : ℝ))

/-- The probability that the urn with weights `θ` draws a given sequence with counts `x`. -/
noncomputable def polyaUrnProb (x : α → ℕ) : ℝ :=
  (∏ c, (ascPochhammer ℝ (x c)).eval (θ c)) / (ascPochhammer ℝ (∑ c, x c)).eval (∑ c, θ c)

@[simp]
theorem polyaUrnProb_zero : polyaUrnProb θ 0 = 1 := by
  simp [polyaUrnProb]

theorem polyaUrnPredictive_zero (c : α) : polyaUrnPredictive θ 0 c = θ c / ∑ i, θ i := by
  simp [polyaUrnPredictive]

theorem polyaUrnProb_single [DecidableEq α] (c : α) :
    polyaUrnProb θ (Pi.single c 1) = polyaUrnPredictive θ 0 c := by
  rw [polyaUrnProb, Fintype.prod_eq_single c fun i hi ↦ by simp [hi]]
  simp [polyaUrnPredictive]

/-- The probability of the counts `x + y` is the probability of `x` times the probability of `y`
under the urn whose weights are raised by `x`. -/
theorem polyaUrnProb_add (x y : α → ℕ) :
    polyaUrnProb θ (x + y) = polyaUrnProb θ x * polyaUrnProb (θ + fun c ↦ (x c : ℝ)) y := by
  have hasc (a : ℝ) (m k : ℕ) : (ascPochhammer ℝ (m + k)).eval a =
      (ascPochhammer ℝ m).eval a * (ascPochhammer ℝ k).eval (a + m) := by
    rw [← ascPochhammer_mul, Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_natCast]
  simp only [polyaUrnProb, Pi.add_apply, sum_add_distrib, hasc, prod_mul_distrib, Nat.cast_sum]
  rw [div_mul_div_comm]

/-- After the counts `x`, the urn with weights `θ + x` predicts as the original urn does after the
counts `x + y`. -/
theorem polyaUrnPredictive_add (x y : α → ℕ) :
    polyaUrnPredictive (θ + fun c ↦ (x c : ℝ)) y = polyaUrnPredictive θ (x + y) := by
  funext c
  simp only [polyaUrnPredictive, Pi.add_apply, sum_add_distrib, Nat.cast_add, add_assoc]

/-- Drawing colour `c` multiplies the probability of the counts by the probability of drawing
`c`. -/
theorem polyaUrnProb_add_single [DecidableEq α] (x : α → ℕ) (c : α) :
    polyaUrnProb θ (x + Pi.single c 1) = polyaUrnProb θ x * polyaUrnPredictive θ x c := by
  rw [polyaUrnProb_add, polyaUrnProb_single, polyaUrnPredictive_add, add_zero]

theorem polyaUrnProb_countVec_snoc [DecidableEq α] (c : α) {n : ℕ} (s : Fin n → α) :
    polyaUrnProb θ (countVec (Fin.snoc s c : Fin (n + 1) → α)) =
      polyaUrnProb θ (countVec s) * polyaUrnPredictive θ (countVec s) c := by
  rw [countVec_snoc, polyaUrnProb_add_single]

theorem polyaUrnProb_countVec_cons [DecidableEq α] (c : α) {n : ℕ} (s : Fin n → α) :
    polyaUrnProb θ (countVec (Fin.cons c s : Fin (n + 1) → α)) =
      polyaUrnProb θ (countVec s) * polyaUrnPredictive θ (countVec s) c := by
  rw [countVec_cons, polyaUrnProb_add_single]

theorem polyaUrnProb_eq_prod_pow_of_sum_le_one {x : α → ℕ} (hx : ∑ c, x c ≤ 1) :
    polyaUrnProb θ x = ∏ c, polyaUrnPredictive θ 0 c ^ x c := by
  have hpow (a : ℝ) {m : ℕ} (hm : m ≤ 1) : (ascPochhammer ℝ m).eval a = a ^ m := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm with rfl | rfl <;> simp
  rw [polyaUrnProb, hpow _ hx, prod_congr rfl fun c _ ↦
    hpow (θ c) ((single_le_sum (fun _ _ ↦ Nat.zero_le _) (mem_univ c)).trans hx)]
  simp only [polyaUrnPredictive_zero, div_pow, prod_div_distrib, prod_pow_eq_pow_sum]

variable {θ}

private theorem sum_add_sum_pos [Nonempty α] (hθ : ∀ i, 0 < θ i) (x : α → ℕ) :
    0 < ∑ i, θ i + ∑ i, (x i : ℝ) :=
  add_pos_of_pos_of_nonneg (sum_pos (fun i _ ↦ hθ i) univ_nonempty)
    (sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)

theorem polyaUrnPredictive_nonneg (hθ : ∀ i, 0 ≤ θ i) (x : α → ℕ) (c : α) :
    0 ≤ polyaUrnPredictive θ x c :=
  div_nonneg (add_nonneg (hθ c) (Nat.cast_nonneg _))
    (add_nonneg (sum_nonneg fun i _ ↦ hθ i) (sum_nonneg fun _ _ ↦ Nat.cast_nonneg _))

theorem polyaUrnPredictive_pos (hθ : ∀ i, 0 < θ i) (x : α → ℕ) (c : α) :
    0 < polyaUrnPredictive θ x c :=
  have : Nonempty α := ⟨c⟩
  div_pos (add_pos_of_pos_of_nonneg (hθ c) (Nat.cast_nonneg _)) (sum_add_sum_pos hθ x)

/-- The prediction rule is a probability on the colours. -/
theorem sum_polyaUrnPredictive [Nonempty α] (hθ : ∀ i, 0 < θ i) (x : α → ℕ) :
    ∑ c, polyaUrnPredictive θ x c = 1 := by
  simp only [polyaUrnPredictive, ← sum_div, sum_add_distrib]
  exact div_self (sum_add_sum_pos hθ x).ne'

theorem polyaUrnProb_pos (hθ : ∀ i, 0 < θ i) (x : α → ℕ) : 0 < polyaUrnProb θ x := by
  refine div_pos (prod_pos fun i _ ↦ ascPochhammer_pos _ _ (hθ i)) ?_
  cases isEmpty_or_nonempty α
  · simp
  · exact ascPochhammer_pos _ _ (sum_pos (fun i _ ↦ hθ i) univ_nonempty)

end ProbabilityTheory
