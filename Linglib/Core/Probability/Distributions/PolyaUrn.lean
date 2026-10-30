/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.MeasureTheory.Measure.Dirac
public import Linglib.Core.Order.Argmax
public import Linglib.Core.Probability.Exchangeable
public import Linglib.Core.Probability.Kernel.IonescuTulcea.SeqLaw
public import Linglib.Core.Probability.PolyaUrn
public import Linglib.Core.RingTheory.Polynomial.Pochhammer
public import Mathlib.MeasureTheory.Measure.Real

/-!
# The law of the Pólya urn

`polyaUrn θ n` is the law of the first `n` draws from the Pólya urn with weights `θ`: the
sequence drawn, by `seqLaw`, from the prediction rule `polyaUrnPredictive`. Each sequence has
probability `polyaUrnProb θ (countVec s)` (`polyaUrn_real_singleton`), which depends only on the
counts, so the sequence is exchangeable (`exchangeable_polyaUrn`). When every colour has the same
positive weight, the most probable sequences are the constant ones (`argmax_polyaUrn_const`).

## Main definitions

* `ProbabilityTheory.polyaUrnRule θ n`: the prediction rule as a kernel.
* `ProbabilityTheory.polyaUrn θ n`: the law of the first `n` draws.

## Main results

* `ProbabilityTheory.polyaUrn_real_singleton`: the probability of a sequence.
* `ProbabilityTheory.exchangeable_polyaUrn`: the drawn sequence is exchangeable.
* `ProbabilityTheory.argmax_polyaUrn_const`: under equal weights the modes are the constant
  sequences.

## References

* [pitman-2006]
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {α : Type*} [DecidableEq α] [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
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

end ProbabilityTheory

namespace ProbabilityTheory

variable {α : Type*} [DecidableEq α] [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α]

open Finset in
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

end ProbabilityTheory
