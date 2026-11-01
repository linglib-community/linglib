/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.Distributions.Beta
public import Linglib.Core.Probability.Distributions.PolyaUrn

/-!
# The Dirichlet distribution

This file defines the Dirichlet distribution with positive parameters `θ` on the finite type `ι`,
the law of a random probability vector on `ι`, and computes its moments. The moment
`∫ ∏ i, p i ^ x i` is the probability that the Pólya urn with weights `θ` draws a given sequence
with counts `x`, so the draws of the urn are a Dirichlet mixture of independent draws.

## Main definitions

* `ProbabilityTheory.dirichletFin n θ`: the Dirichlet distribution on `Fin n → ℝ`.
* `ProbabilityTheory.dirichlet θ`: the Dirichlet distribution on `ι → ℝ`.

## Main statements

* `ProbabilityTheory.ae_nonneg_sum_eq_one_dirichlet`: the Dirichlet distribution lives on the
  probability vectors.
* `ProbabilityTheory.lintegral_prod_pow_dirichlet`: the moments are Pólya urn probabilities.
* `ProbabilityTheory.isProbabilityMeasure_dirichlet`: the Dirichlet distribution is a probability
  measure.
* `ProbabilityTheory.polyaUrn_singleton_eq_lintegral_dirichlet`: the Pólya urn is a Dirichlet
  mixture of independent draws.

## Implementation notes

The distribution is built by stick-breaking: the first coordinate is beta-distributed with
parameters `θ 0` and the sum of the other parameters, and the other coordinates are `1 - p 0`
times an independent Dirichlet vector with the other parameters. On a general finite type the
construction follows the enumeration `Fintype.equivFin ι`, and the moments do not depend on it.

## References

* [pitman-2006]
-/

@[expose] public section

open MeasureTheory Finset

namespace ProbabilityTheory

/-! ### Stick-breaking on `Fin n` -/

theorem measurable_fin_cons_one_sub_smul {n : ℕ} :
    Measurable fun vq : ℝ × (Fin n → ℝ) ↦
      (Fin.cons vq.1 ((1 - vq.1) • vq.2) : Fin (n + 1) → ℝ) := by
  refine measurable_pi_iff.2 fun i ↦ ?_
  cases i using Fin.cases with
  | zero => simp only [Fin.cons_zero]; fun_prop
  | succ j => simp only [Fin.cons_succ, Pi.smul_apply, smul_eq_mul]; fun_prop

/-- The Dirichlet distribution on `Fin n → ℝ` with parameters `θ`, by stick-breaking. -/
noncomputable def dirichletFin : (n : ℕ) → (Fin n → ℝ) → Measure (Fin n → ℝ)
  | 0, _ => Measure.dirac 0
  | 1, _ => Measure.dirac 1
  | n + 2, θ =>
    ((betaMeasure (θ 0) (∑ i : Fin (n + 1), θ i.succ)).prod (dirichletFin (n + 1) (Fin.tail θ))).map
      fun vq ↦ Fin.cons vq.1 ((1 - vq.1) • vq.2)

theorem sFinite_dirichletFin : ∀ (n : ℕ) (θ : Fin n → ℝ), SFinite (dirichletFin n θ)
  | 0, _ => by rw [dirichletFin]; infer_instance
  | 1, _ => by rw [dirichletFin]; infer_instance
  | n + 2, θ => by
    have := sFinite_dirichletFin (n + 1) (Fin.tail θ)
    rw [dirichletFin]
    infer_instance

instance {n : ℕ} {θ : Fin n → ℝ} : SFinite (dirichletFin n θ) :=
  sFinite_dirichletFin n θ

theorem lintegral_prod_pow_dirichletFin : ∀ {n : ℕ} {θ : Fin n → ℝ}, (∀ i, 0 < θ i) →
    ∀ x : Fin n → ℕ,
      ∫⁻ p, ∏ i, ENNReal.ofReal (p i) ^ x i ∂dirichletFin n θ = ENNReal.ofReal (polyaUrnProb θ x)
  | 0, θ, _, x => by simp [dirichletFin, polyaUrnProb]
  | 1, θ, hθ, x => by
    rw [dirichletFin, lintegral_dirac' _ (by fun_prop)]
    simp [polyaUrnProb, (ascPochhammer_pos (x 0) _ (hθ 0)).ne']
  | n + 2, θ, hθ, x => by
    have hR : 0 < ∑ i : Fin (n + 1), θ i.succ := sum_pos (fun i _ ↦ hθ _) univ_nonempty
    have hle : ∀ᵐ z ∂(betaMeasure (θ 0) (∑ i : Fin (n + 1), θ i.succ)).prod
        (dirichletFin (n + 1) (Fin.tail θ)), z.1 ≤ 1 :=
      Measure.quasiMeasurePreserving_fst.ae
        ((ae_mem_Ioo_betaMeasure _ _).mono fun v hv ↦ hv.2.le)
    have hB := lintegral_pow_mul_one_sub_pow_betaMeasure (hθ 0) hR (x 0)
      (∑ i : Fin (n + 1), x i.succ)
    calc ∫⁻ p, ∏ i, ENNReal.ofReal (p i) ^ x i ∂dirichletFin (n + 2) θ
        = ∫⁻ z, ∏ i, ENNReal.ofReal ((Fin.cons z.1 ((1 - z.1) • z.2) : Fin (n + 2) → ℝ) i) ^ x i
            ∂(betaMeasure (θ 0) (∑ i : Fin (n + 1), θ i.succ)).prod
              (dirichletFin (n + 1) (Fin.tail θ)) := by
          rw [dirichletFin, lintegral_map (by fun_prop) measurable_fin_cons_one_sub_smul]
      _ = ∫⁻ z, (ENNReal.ofReal z.1 ^ x 0 *
              ENNReal.ofReal (1 - z.1) ^ ∑ i : Fin (n + 1), x i.succ) *
            ∏ i, ENNReal.ofReal (z.2 i) ^ Fin.tail x i
            ∂(betaMeasure (θ 0) (∑ i : Fin (n + 1), θ i.succ)).prod
              (dirichletFin (n + 1) (Fin.tail θ)) := by
          refine lintegral_congr_ae (hle.mono fun z hz ↦ ?_)
          simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Pi.smul_apply,
            smul_eq_mul, ENNReal.ofReal_mul (sub_nonneg.2 hz), mul_pow, prod_mul_distrib,
            prod_pow_eq_pow_sum, Fin.tail, mul_assoc]
      _ = (∫⁻ v, ENNReal.ofReal v ^ x 0 * ENNReal.ofReal (1 - v) ^ ∑ i : Fin (n + 1), x i.succ
              ∂betaMeasure (θ 0) (∑ i : Fin (n + 1), θ i.succ)) *
            ∫⁻ q, ∏ i, ENNReal.ofReal (q i) ^ Fin.tail x i ∂dirichletFin (n + 1) (Fin.tail θ) :=
          lintegral_prod_mul (f := fun v : ℝ ↦ ENNReal.ofReal v ^ x 0 *
              ENNReal.ofReal (1 - v) ^ ∑ i : Fin (n + 1), x i.succ)
            (g := fun q : Fin (n + 1) → ℝ ↦ ∏ i, ENNReal.ofReal (q i) ^ Fin.tail x i) (by fun_prop)
            (Measurable.aemeasurable (by fun_prop))
      _ = ENNReal.ofReal (polyaUrnProb θ x) := by
          rw [hB, lintegral_prod_pow_dirichletFin (θ := Fin.tail θ) (fun i ↦ hθ i.succ),
            ← ENNReal.ofReal_mul (div_pos (mul_pos (ascPochhammer_pos _ _ (hθ 0))
              (ascPochhammer_pos _ _ hR)) (ascPochhammer_pos _ _ (add_pos (hθ 0) hR))).le,
            polyaUrnProb_eq_mul_tail hθ]

theorem measurableSet_nonneg_sum_eq_one (ι : Type*) [Fintype ι] :
    MeasurableSet {p : ι → ℝ | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1} := by
  simp only [Set.ofPred_and, Set.ofPred_forall]
  exact (MeasurableSet.iInter fun i ↦
    measurableSet_le measurable_const (measurable_pi_apply i)).inter
      (measurableSet_eq_fun (by fun_prop) measurable_const)

theorem ae_nonneg_sum_eq_one_dirichletFin : ∀ {n : ℕ} (θ : Fin n → ℝ), n ≠ 0 →
    ∀ᵐ p ∂dirichletFin n θ, (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1
  | 0, _, h => absurd rfl h
  | 1, _, _ => by
    rw [dirichletFin, ae_dirac_iff (measurableSet_nonneg_sum_eq_one _)]
    exact ⟨fun _ ↦ zero_le_one, by simp⟩
  | n + 2, θ, _ => by
    rw [dirichletFin, ae_map_iff measurable_fin_cons_one_sub_smul.aemeasurable
      (measurableSet_nonneg_sum_eq_one _)]
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_mem_Ioo_betaMeasure _ _),
      Measure.quasiMeasurePreserving_snd.ae
        (ae_nonneg_sum_eq_one_dirichletFin (Fin.tail θ) n.succ_ne_zero)] with z hv hq
    refine ⟨fun i ↦ ?_, ?_⟩
    · cases i using Fin.cases with
      | zero => simpa using hv.1.le
      | succ j => simpa using mul_nonneg (sub_nonneg.2 hv.2.le) (hq.1 j)
    · simp [Fin.sum_univ_succ, ← mul_sum, hq.2]

/-! ### The Dirichlet distribution on a finite type -/

variable {ι : Type*} [Fintype ι]

/-- The Dirichlet distribution on `ι → ℝ` with parameters `θ`. -/
noncomputable def dirichlet (θ : ι → ℝ) : Measure (ι → ℝ) :=
  (dirichletFin _ (θ ∘ (Fintype.equivFin ι).symm)).map fun q ↦ q ∘ Fintype.equivFin ι

/-- The moments of the Dirichlet distribution are the probabilities of the Pólya urn with the same
weights. -/
theorem lintegral_prod_pow_dirichlet {θ : ι → ℝ} (hθ : ∀ i, 0 < θ i) (x : ι → ℕ) :
    ∫⁻ p, ∏ i, ENNReal.ofReal (p i) ^ x i ∂dirichlet θ = ENNReal.ofReal (polyaUrnProb θ x) := by
  rw [dirichlet, lintegral_map (by fun_prop) (by fun_prop),
    ← polyaUrnProb_comp_equiv θ (Fintype.equivFin ι).symm,
    ← lintegral_prod_pow_dirichletFin (θ := θ ∘ (Fintype.equivFin ι).symm) (fun j ↦ hθ _)]
  exact lintegral_congr fun q ↦ Fintype.prod_equiv (Fintype.equivFin ι) _ _ fun i ↦ by simp

/-- The Dirichlet distribution is the law of a random probability vector. -/
theorem ae_nonneg_sum_eq_one_dirichlet [Nonempty ι] (θ : ι → ℝ) :
    ∀ᵐ p ∂dirichlet θ, (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 := by
  rw [dirichlet, ae_map_iff (Measurable.aemeasurable (by fun_prop))
    (measurableSet_nonneg_sum_eq_one ι)]
  filter_upwards [ae_nonneg_sum_eq_one_dirichletFin _ Fintype.card_ne_zero] with q hq
  exact ⟨fun i ↦ hq.1 _, (Equiv.sum_comp (Fintype.equivFin ι) q).trans hq.2⟩

theorem isProbabilityMeasure_dirichlet {θ : ι → ℝ} (hθ : ∀ i, 0 < θ i) :
    IsProbabilityMeasure (dirichlet θ) :=
  ⟨by simpa using lintegral_prod_pow_dirichlet hθ 0⟩

/-- The probability that the Pólya urn draws a sequence is the probability of drawing it
independently from a Dirichlet-distributed probability vector, the mixture form of
[pitman-2006] Exercise 2.2.2. -/
theorem polyaUrn_singleton_eq_lintegral_dirichlet {α : Type*} [DecidableEq α] [Fintype α]
    [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] {θ : α → ℝ}
    (hθ : ∀ i, 0 < θ i) {n : ℕ} (s : Fin n → α) :
    polyaUrn θ n {s} = ∫⁻ p, ∏ i, ENNReal.ofReal (p (s i)) ∂dirichlet θ := by
  rw [polyaUrn_singleton hθ, ← lintegral_prod_pow_dirichlet hθ]
  refine lintegral_congr fun p ↦ (prod_congr rfl fun c _ ↦ ?_).trans
    (prod_fiberwise univ s fun i ↦ ENNReal.ofReal (p (s i)))
  exact (prod_eq_pow_card fun i hi ↦ by rw [(mem_filter.1 hi).2]).symm

end ProbabilityTheory
