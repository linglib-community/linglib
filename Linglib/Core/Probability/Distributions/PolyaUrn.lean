/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Analysis.SpecialFunctions.Gamma.Basic
public import Linglib.Core.MeasureTheory.Measure.Dirac
public import Linglib.Core.Order.Argmax
public import Linglib.Core.Probability.Exchangeable
public import Linglib.Core.Probability.Kernel.IonescuTulcea.SeqLaw
public import Linglib.Core.RingTheory.Polynomial.Pochhammer
public import Mathlib.MeasureTheory.Measure.Real

/-!
# The Pólya urn

This file defines the Pólya urn and the law of its draws. The urn holds balls of the colours in
`α` with positive weights `θ`. After draws in which colour `c` came up `x c` times, the next draw
is `c` with probability proportional to `θ c + x c`, and the law of the first `n` draws is the
sequence law of this prediction rule. The probability of a sequence depends only on its counts,
so the sequence is exchangeable. It is a ratio of rising factorials, and in Gamma functions the
Dirichlet-multinomial formula.

## Main definitions

* `ProbabilityTheory.countVec`: how often each colour occurs in a sequence.
* `ProbabilityTheory.polyaUrnPredictive`: the probability of each colour on the next draw.
* `ProbabilityTheory.polyaUrnProb`: the probability of a sequence with given counts.
* `ProbabilityTheory.polyaUrn θ n`: the law of the first `n` draws.

## Main statements

* `ProbabilityTheory.polyaUrnProb_add`: conjugacy, the urn after the counts `x` is the urn with
  weights `θ + x`.
* `ProbabilityTheory.polyaUrn_real_singleton`: the probability of a sequence.
* `ProbabilityTheory.polyaUrnProb_eq_prod_Gamma_div`: that probability in Gamma functions.
* `ProbabilityTheory.exchangeable_polyaUrn`: the drawn sequence is exchangeable.

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

open Finset MeasureTheory

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

section Prob

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

/-- The probability of a sequence with counts `x` in Gamma functions: each rising factorial
`(a)_m` of `polyaUrnProb` is the ratio `Γ(a + m) / Γ(a)`. -/
theorem polyaUrnProb_eq_prod_Gamma_div [Nonempty α] (hθ : ∀ c, 0 < θ c) (x : α → ℕ) :
    polyaUrnProb θ x = (∏ c, Real.Gamma (θ c + x c) / Real.Gamma (θ c)) /
      (Real.Gamma (∑ c, θ c + (∑ c, x c : ℕ)) / Real.Gamma (∑ c, θ c)) := by
  have hne {a : ℝ} (ha : 0 < a) (k : ℕ) : a ≠ -k := ((neg_nonpos.2 k.cast_nonneg).trans_lt ha).ne'
  rw [polyaUrnProb, Real.Gamma_add_nat_div_Gamma_eq _
    (hne (sum_pos (fun c _ ↦ hθ c) univ_nonempty))]
  exact congrArg (· / _) (prod_congr rfl fun c _ ↦
    (Real.Gamma_add_nat_div_Gamma_eq _ (hne (hθ c))).symm)

end Prob

/-! ### The law of the draws -/

section Law

variable [DecidableEq α] [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  (θ : α → ℝ)

/-- The Pólya urn prediction rule as a kernel: after the draws `s`, colour `c` is drawn with
probability `polyaUrnPredictive θ (countVec s) c`. -/
noncomputable def polyaUrnRule (n : ℕ) : Kernel (Fin n → α) α :=
  Kernel.ofFunOfCountable fun s ↦
    Measure.ofRealWeights (polyaUrnPredictive θ (countVec s))

/-- The *Pólya urn*: the law of the first `n` draws from the urn with weights `θ`. -/
noncomputable def polyaUrn (n : ℕ) : Measure (Fin n → α) :=
  seqLaw (polyaUrnRule θ) n

theorem polyaUrnRule_apply_singleton {n : ℕ} (s : Fin n → α) (c : α) :
    polyaUrnRule θ n s {c} = ENNReal.ofReal (polyaUrnPredictive θ (countVec s) c) :=
  Measure.ofWeights_apply_singleton _ c

variable {θ} [Nonempty α] (hθ : ∀ i, 0 < θ i)
include hθ

theorem isMarkovKernel_polyaUrnRule (n : ℕ) : IsMarkovKernel (polyaUrnRule θ n) :=
  ⟨fun _ ↦ Measure.isProbabilityMeasure_sum_ofReal_smul_dirac
    (fun c ↦ polyaUrnPredictive_nonneg (fun i ↦ (hθ i).le) _ c) (sum_polyaUrnPredictive hθ _)⟩

theorem isProbabilityMeasure_polyaUrn (n : ℕ) : IsProbabilityMeasure (polyaUrn θ n) :=
  have := isMarkovKernel_polyaUrnRule hθ
  isProbabilityMeasure_seqLaw n

theorem polyaUrn_singleton : ∀ {n : ℕ} (s : Fin n → α),
    polyaUrn θ n {s} = ENNReal.ofReal (polyaUrnProb θ (countVec s))
  | 0, s => by simp [polyaUrn, Subsingleton.elim s default]
  | n + 1, s => by
    have := isMarkovKernel_polyaUrnRule hθ
    rw [polyaUrn, ← Fin.snoc_init_self s, seqLaw_succ_singleton_snoc, ← polyaUrn,
      polyaUrn_singleton, polyaUrnRule_apply_singleton,
      ← ENNReal.ofReal_mul (polyaUrnProb_pos hθ _).le, polyaUrnProb_countVec_snoc]

theorem polyaUrn_real_singleton {n : ℕ} (s : Fin n → α) :
    (polyaUrn θ n).real {s} = polyaUrnProb θ (countVec s) := by
  rw [measureReal_def, polyaUrn_singleton hθ, ENNReal.toReal_ofReal (polyaUrnProb_pos hθ _).le]

/-- The sequence drawn from a Pólya urn is exchangeable ([pitman-2006] Exercise 2.2.2). -/
theorem exchangeable_polyaUrn (n : ℕ) : Exchangeable (polyaUrn θ n) :=
  exchangeable_of_measure_singleton fun s σ ↦ by
    rw [polyaUrn_singleton hθ, polyaUrn_singleton hθ, countVec_comp_perm]

end Law

section Argmax

variable [DecidableEq α] [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α]

/-- Under the same positive weight on every colour, the most probable sequences of `n` draws from
the Pólya urn are the constant ones. -/
theorem argmax_polyaUrn_const {a : ℝ} (ha : 0 < a) (n : ℕ) :
    univ.argmax (fun s : Fin n → α ↦ polyaUrn (fun _ ↦ a) n {s}) = univ.image fun c _ ↦ c := by
  have hk : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hD : 0 < (ascPochhammer ℝ n).eval (Fintype.card α * a) :=
    ascPochhammer_pos _ _ (mul_pos hk ha)
  have hF (s : Fin n → α) : 0 < ∏ c, (ascPochhammer ℝ (countVec s c)).eval a :=
    prod_pos fun _ _ ↦ ascPochhammer_pos _ _ ha
  have hmass (s : Fin n → α) : polyaUrn (fun _ ↦ a) n {s} = ENNReal.ofReal
      ((∏ c, (ascPochhammer ℝ (countVec s c)).eval a) /
        (ascPochhammer ℝ n).eval (Fintype.card α * a)) := by
    rw [polyaUrn_singleton (fun _ ↦ ha), polyaUrnProb, sum_countVec, sum_const, card_univ,
      nsmul_eq_mul]
  have hconst (c₀ : α) :
      ∏ c, (ascPochhammer ℝ (countVec (fun _ : Fin n ↦ c₀) c)).eval a =
        (ascPochhammer ℝ n).eval a := by
    rw [prod_eq_single c₀ (fun c _ hc ↦ by simp [countVec, Ne.symm hc]) (by simp)]
    simp [countVec]
  have hlt (s : Fin n → α) {i₁ i₂ : Fin n} (hne : s i₁ ≠ s i₂) :
      ∏ c, (ascPochhammer ℝ (countVec s c)).eval a < (ascPochhammer ℝ n).eval a := by
    have hc₁ : countVec s (s i₁) ≠ 0 := card_ne_zero.2 ⟨i₁, by simp⟩
    have hS : ∑ c ∈ univ.erase (s i₁), countVec s c ≠ 0 :=
      (Nat.pos_of_ne_zero (card_ne_zero.2 ⟨i₂, by simp⟩ : countVec s (s i₂) ≠ 0)).trans_le
        (single_le_sum (f := fun c ↦ countVec s c) (fun _ _ ↦ Nat.zero_le _)
          (mem_erase.2 ⟨hne.symm, mem_univ _⟩)) |>.ne'
    calc ∏ c, (ascPochhammer ℝ (countVec s c)).eval a
        = (ascPochhammer ℝ (countVec s (s i₁))).eval a *
            ∏ c ∈ univ.erase (s i₁), (ascPochhammer ℝ (countVec s c)).eval a :=
          (mul_prod_erase univ _ (mem_univ _)).symm
      _ ≤ (ascPochhammer ℝ (countVec s (s i₁))).eval a *
            (ascPochhammer ℝ (∑ c ∈ univ.erase (s i₁), countVec s c)).eval a :=
          mul_le_mul_of_nonneg_left (prod_ascPochhammer_eval_le ha.le _ _)
            (ascPochhammer_pos _ _ ha).le
      _ < (ascPochhammer ℝ (countVec s (s i₁) + ∑ c ∈ univ.erase (s i₁), countVec s c)).eval a :=
          ascPochhammer_eval_mul_lt ha hc₁ hS
      _ = (ascPochhammer ℝ n).eval a := by rw [add_sum_erase _ _ (mem_univ _), sum_countVec]
  ext s
  simp only [mem_argmax, mem_univ, true_and, mem_image]
  refine ⟨fun hmax ↦ ?_, ?_⟩
  · by_contra hnc
    obtain ⟨i₁, i₂, hne⟩ : ∃ i₁ i₂, s i₁ ≠ s i₂ := by
      by_contra! hall
      rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨i₀⟩⟩
      · exact hnc ⟨Classical.arbitrary α, funext fun i ↦ isEmptyElim i⟩
      · exact hnc ⟨s i₀, funext fun i ↦ hall i₀ i⟩
    have := hmax (fun _ ↦ s i₁) trivial
    rw [hmass, hmass, ENNReal.ofReal_le_ofReal_iff (div_pos (hF s) hD).le,
      div_le_div_iff_of_pos_right hD, hconst] at this
    exact (hlt s hne).not_ge this
  · rintro ⟨c, rfl⟩ s' _
    rw [hmass, hmass, hconst]
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
      (by simpa [sum_countVec] using prod_ascPochhammer_eval_le ha.le univ (countVec s')) hD.le)

end Argmax

end ProbabilityTheory
