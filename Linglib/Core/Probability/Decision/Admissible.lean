module

public import Linglib.Core.LinearAlgebra.Matrix.Farkas
public import Linglib.Core.MeasureTheory.Measure.Dirac
public import Linglib.Core.MeasureTheory.Measure.Real
public import Mathlib.Probability.Decision.BayesEstimator
public import Mathlib.Probability.Decision.Risk.Basic

/-!
# Admissible actions in finite decision problems

A decision problem without data has parameters `Θ`, actions `𝓨` and a loss `ℓ : Θ → 𝓨 → ℝ≥0∞`. A
randomized action `ν` is the estimator `Kernel.const Unit ν` for the data kernel `Kernel.discard Θ`,
which observes nothing, and its risk at `θ` is `∫⁻ y, ℓ θ y ∂ν`. With finitely many parameters and
actions and finite losses, being a Bayes action and escaping domination coincide. An action is a
Bayes estimator for some prior iff no randomized action has smaller risk at every parameter, and it
is admissible iff it is a Bayes estimator for a prior that charges every parameter, the complete
class theorem. Both come from theorems of the alternative for the matrix of risk differences.
Against nature in game theory these are Pearce's lemmas, an act that is never a best response is
strictly dominated and an act that no mixture weakly dominates is a best response to a belief of
full support, and the payoff versions state them for utilities. `[UPSTREAM]` candidate for
`Mathlib/Probability/Decision/`.

## Main definitions

* `ProbabilityTheory.IsStrictlyDominated`: another randomized action has smaller risk at every
  parameter.
* `ProbabilityTheory.IsAdmissible`: no randomized action has risk at most as large everywhere and
  smaller somewhere.

## Main statements

* `ProbabilityTheory.exists_isBayesEstimator_iff_not_isStrictlyDominated`: an action is Bayes for
  some prior iff it is not strictly dominated.
* `ProbabilityTheory.isAdmissible_iff_exists_isBayesEstimator`: an action is admissible iff it is
  Bayes for a prior of full support.
* `ProbabilityTheory.exists_maximizesPayoff_iff_not_isStrictlyPayoffDominated`,
  `ProbabilityTheory.not_isWeaklyPayoffDominated_iff_exists_maximizesPayoff`: the payoff versions,
  Pearce's lemmas.

## References

* [pearce-1984]
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

open MeasureTheory.Measure (ofRealWeights ofRealWeights_real_singleton
  isProbabilityMeasure_ofRealWeights)

variable {Θ 𝓨 : Type*}

/-! ### Helpers on finite types -/

private theorem exists_bound [Fintype Θ] [Fintype 𝓨] (U : 𝓨 → Θ → ℝ) : ∃ C, ∀ y θ, U y θ ≤ C :=
  ⟨∑ y, ∑ θ, |U y θ|, fun y θ ↦ (le_abs_self _).trans <|
    (Finset.single_le_sum (f := fun θ ↦ |U y θ|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ θ)).trans
      (Finset.single_le_sum (f := fun y ↦ ∑ θ, |U y θ|)
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (Finset.mem_univ y))⟩

/-- The regret `C − U` at a bound `C` on the payoffs. -/
private noncomputable def regret (U : 𝓨 → Θ → ℝ) (C : ℝ) : Θ → 𝓨 → ℝ≥0∞ :=
  fun θ y ↦ ENNReal.ofReal (C - U y θ)

private theorem regret_ne_top (U : 𝓨 → Θ → ℝ) (C : ℝ) (θ : Θ) (y : 𝓨) : regret U C θ y ≠ ∞ :=
  ENNReal.ofReal_ne_top

variable [MeasurableSpace 𝓨]

/-! ### Dominance and admissibility -/

section Defs

variable (ℓ : Θ → 𝓨 → ℝ≥0∞) (U : 𝓨 → Θ → ℝ)

/-- A randomized action is strictly dominated when another has smaller risk at every
parameter. -/
def IsStrictlyDominated (ν : Measure 𝓨) : Prop :=
  ∃ ν' : Measure 𝓨, IsProbabilityMeasure ν' ∧ ∀ θ, ∫⁻ y, ℓ θ y ∂ν' < ∫⁻ y, ℓ θ y ∂ν

/-- A randomized action is admissible when every action whose risk is nowhere larger has the same
risk everywhere. -/
def IsAdmissible (ν : Measure 𝓨) : Prop :=
  ∀ ν' : Measure 𝓨, IsProbabilityMeasure ν' → (∀ θ, ∫⁻ y, ℓ θ y ∂ν' ≤ ∫⁻ y, ℓ θ y ∂ν) →
    ∀ θ, ∫⁻ y, ℓ θ y ∂ν' = ∫⁻ y, ℓ θ y ∂ν

/-- The payoff of the randomized action `ν` at the parameter `θ`. -/
noncomputable def mixedPayoff (ν : Measure 𝓨) (θ : Θ) : ℝ := ∫ y, U y θ ∂ν

/-- `ν` is strictly dominated in payoff when another randomized action pays more at every
parameter. -/
def IsStrictlyPayoffDominated (ν : Measure 𝓨) : Prop :=
  ∃ ν' : Measure 𝓨, IsProbabilityMeasure ν' ∧ ∀ θ, mixedPayoff U ν θ < mixedPayoff U ν' θ

/-- `ν` is weakly dominated in payoff when another randomized action pays at least as much at
every parameter and more at some. -/
def IsWeaklyPayoffDominated (ν : Measure 𝓨) : Prop :=
  ∃ ν' : Measure 𝓨, IsProbabilityMeasure ν' ∧ (∀ θ, mixedPayoff U ν θ ≤ mixedPayoff U ν' θ) ∧
    ∃ θ, mixedPayoff U ν θ < mixedPayoff U ν' θ

end Defs

/-! ### Risks and payoffs on reals -/

section Risk

variable [Fintype 𝓨] [MeasurableSingletonClass 𝓨] {ℓ : Θ → 𝓨 → ℝ≥0∞} (hℓ : ∀ θ y, ℓ θ y ≠ ∞)
  (U : 𝓨 → Θ → ℝ)

include hℓ in
private theorem risk_ne_top (ν : Measure 𝓨) [IsFiniteMeasure ν] (θ : Θ) :
    ∫⁻ y, ℓ θ y ∂ν ≠ ∞ := by
  rw [lintegral_fintype]
  exact ENNReal.sum_ne_top.2 fun y _ ↦ ENNReal.mul_ne_top (hℓ θ y) (measure_ne_top _ _)

include hℓ in
private theorem toReal_risk (ν : Measure 𝓨) [IsFiniteMeasure ν] (θ : Θ) :
    (∫⁻ y, ℓ θ y ∂ν).toReal = ∑ y, ν.real {y} * (ℓ θ y).toReal := by
  rw [lintegral_fintype, ENNReal.toReal_sum fun y _ ↦ ENNReal.mul_ne_top (hℓ θ y)
    (measure_ne_top _ _)]
  exact Finset.sum_congr rfl fun y _ ↦ by rw [ENNReal.toReal_mul, mul_comm, measureReal_def]

theorem mixedPayoff_eq_sum (ν : Measure 𝓨) [IsFiniteMeasure ν] (θ : Θ) :
    mixedPayoff U ν θ = ∑ y, ν.real {y} * U y θ := by
  simp [mixedPayoff, integral_fintype .of_finite]

private theorem toReal_risk_regret {C : ℝ} (hC : ∀ y θ, U y θ ≤ C) (ν : Measure 𝓨)
    [IsProbabilityMeasure ν] (θ : Θ) :
    (∫⁻ y, regret U C θ y ∂ν).toReal = C - mixedPayoff U ν θ := by
  rw [toReal_risk (regret_ne_top U C), mixedPayoff_eq_sum]
  simp_rw [regret, ENNReal.toReal_ofReal (sub_nonneg.2 (hC _ θ)), mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, sum_measureReal_singleton_eq_one, one_mul]

private theorem risk_regret_lt_iff {C : ℝ} (hC : ∀ y θ, U y θ ≤ C) {ν ν' : Measure 𝓨}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν'] (θ : Θ) :
    ∫⁻ y, regret U C θ y ∂ν' < ∫⁻ y, regret U C θ y ∂ν ↔
      mixedPayoff U ν θ < mixedPayoff U ν' θ := by
  rw [← ENNReal.toReal_lt_toReal (risk_ne_top (regret_ne_top U C) ν' θ)
    (risk_ne_top (regret_ne_top U C) ν θ), toReal_risk_regret U hC, toReal_risk_regret U hC,
    sub_lt_sub_iff_left]

private theorem risk_regret_le_iff {C : ℝ} (hC : ∀ y θ, U y θ ≤ C) {ν ν' : Measure 𝓨}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν'] (θ : Θ) :
    ∫⁻ y, regret U C θ y ∂ν' ≤ ∫⁻ y, regret U C θ y ∂ν ↔
      mixedPayoff U ν θ ≤ mixedPayoff U ν' θ := by
  rw [← ENNReal.toReal_le_toReal (risk_ne_top (regret_ne_top U C) ν' θ)
    (risk_ne_top (regret_ne_top U C) ν θ), toReal_risk_regret U hC, toReal_risk_regret U hC,
    sub_le_sub_iff_left]

end Risk

variable [MeasurableSpace Θ]

/-! ### Bayes actions -/

section Belief

variable (U : 𝓨 → Θ → ℝ)

/-- The expected payoff of the randomized action `ν` under the belief `P`. -/
noncomputable def expectedPayoff (P : Measure Θ) (ν : Measure 𝓨) : ℝ :=
  ∫ θ, mixedPayoff U ν θ ∂P

/-- `ν` maximizes the expected payoff under `P` among the randomized actions. -/
def MaximizesPayoff (P : Measure Θ) (ν : Measure 𝓨) : Prop :=
  ∀ ν' : Measure 𝓨, IsProbabilityMeasure ν' → expectedPayoff U P ν' ≤ expectedPayoff U P ν

theorem isBayesEstimator_discard_const_iff {ℓ : Θ → 𝓨 → ℝ≥0∞} {ν : Measure 𝓨}
    [IsProbabilityMeasure ν] {π : Measure Θ} :
    IsBayesEstimator ℓ (Kernel.discard Θ) (Kernel.const Unit ν) π ↔
      ∀ ν' : Measure 𝓨, IsProbabilityMeasure ν' →
        ∫⁻ θ, ∫⁻ y, ℓ θ y ∂ν ∂π ≤ ∫⁻ θ, ∫⁻ y, ℓ θ y ∂ν' ∂π := by
  have : Nonempty 𝓨 := nonempty_of_isProbabilityMeasure ν
  have h (ν' : Measure 𝓨) : avgRisk ℓ (Kernel.discard Θ) (Kernel.const Unit ν') π =
      ∫⁻ θ, ∫⁻ y, ℓ θ y ∂ν' ∂π := by
    simp [avgRisk_const_right']
  rw [IsBayesEstimator, bayesRisk_eq_iInf_measure_of_subsingleton, h]
  simp_rw [h]
  refine ⟨fun heq ν' hν' ↦ heq ▸ iInf₂_le ν' hν', fun hle ↦ le_antisymm (le_iInf₂ hle) ?_⟩
  exact iInf₂_le ν (inferInstanceAs (IsProbabilityMeasure ν))

end Belief

section Avg

variable [Fintype Θ] [MeasurableSingletonClass Θ] (U : 𝓨 → Θ → ℝ)

private theorem toReal_avg {f : Θ → ℝ≥0∞} (hf : ∀ θ, f θ ≠ ∞) (π : Measure Θ)
    [IsFiniteMeasure π] : (∫⁻ θ, f θ ∂π).toReal = ∑ θ, π.real {θ} * (f θ).toReal := by
  rw [lintegral_fintype, ENNReal.toReal_sum fun θ _ ↦ ENNReal.mul_ne_top (hf θ)
    (measure_ne_top _ _)]
  exact Finset.sum_congr rfl fun θ _ ↦ by rw [ENNReal.toReal_mul, mul_comm, measureReal_def]

private theorem avg_ne_top {f : Θ → ℝ≥0∞} (hf : ∀ θ, f θ ≠ ∞) (π : Measure Θ)
    [IsFiniteMeasure π] : ∫⁻ θ, f θ ∂π ≠ ∞ := by
  rw [lintegral_fintype]
  exact ENNReal.sum_ne_top.2 fun θ _ ↦ ENNReal.mul_ne_top (hf θ) (measure_ne_top _ _)

theorem expectedPayoff_eq_sum (P : Measure Θ) [IsFiniteMeasure P] (ν : Measure 𝓨) :
    expectedPayoff U P ν = ∑ θ, P.real {θ} * mixedPayoff U ν θ := by
  simp [expectedPayoff, integral_fintype .of_finite]

theorem expectedPayoff_lt_of_forall_lt (P : Measure Θ) [IsProbabilityMeasure P]
    {ν ν' : Measure 𝓨} (h : ∀ θ, mixedPayoff U ν θ < mixedPayoff U ν' θ) :
    expectedPayoff U P ν < expectedPayoff U P ν' := by
  rw [expectedPayoff_eq_sum, expectedPayoff_eq_sum]
  obtain ⟨θ₀, -, hθ₀⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ) (f := fun _ ↦ (0 : ℝ))
    (g := fun θ ↦ P.real {θ}) (by rw [sum_measureReal_singleton_eq_one P]; simp)
  exact Finset.sum_lt_sum (fun θ _ ↦ mul_le_mul_of_nonneg_left (h θ).le measureReal_nonneg)
    ⟨θ₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (h θ₀) hθ₀⟩

end Avg

variable [Fintype Θ] [MeasurableSingletonClass Θ] [Fintype 𝓨] [MeasurableSingletonClass 𝓨]

/-! ### Strict dominance and Bayes actions -/

section Loss

variable {ℓ : Θ → 𝓨 → ℝ≥0∞} (hℓ : ∀ θ y, ℓ θ y ≠ ∞)

include hℓ in
private theorem not_isStrictlyDominated_of_bayes {ν : Measure 𝓨} [IsProbabilityMeasure ν]
    {π : Measure Θ} [IsProbabilityMeasure π]
    (hπ : ∀ ν' : Measure 𝓨, IsProbabilityMeasure ν' →
      ∫⁻ θ, ∫⁻ y, ℓ θ y ∂ν ∂π ≤ ∫⁻ θ, ∫⁻ y, ℓ θ y ∂ν' ∂π) :
    ¬ IsStrictlyDominated ℓ ν := by
  rintro ⟨ν', hν', hlt⟩
  have h := hπ ν' hν'
  rw [← ENNReal.toReal_le_toReal (avg_ne_top (risk_ne_top hℓ ν) π)
    (avg_ne_top (risk_ne_top hℓ ν') π), toReal_avg (risk_ne_top hℓ ν),
    toReal_avg (risk_ne_top hℓ ν')] at h
  have hlt' : ∀ θ, (∫⁻ y, ℓ θ y ∂ν').toReal < (∫⁻ y, ℓ θ y ∂ν).toReal := fun θ ↦
    (ENNReal.toReal_lt_toReal (risk_ne_top hℓ ν' θ) (risk_ne_top hℓ ν θ)).2 (hlt θ)
  obtain ⟨θ₀, -, hθ₀⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ) (f := fun _ ↦ (0 : ℝ))
    (g := fun θ ↦ π.real {θ}) (by rw [sum_measureReal_singleton_eq_one π]; simp)
  refine absurd h (not_le.2 ?_)
  exact Finset.sum_lt_sum (fun θ _ ↦ mul_le_mul_of_nonneg_left (hlt' θ).le measureReal_nonneg)
    ⟨θ₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (hlt' θ₀) hθ₀⟩

include hℓ in
private theorem bayes_of_real {ν : Measure 𝓨} [IsProbabilityMeasure ν] {x : Θ → ℝ}
    (hx : ∀ θ, 0 ≤ x θ) (hx1 : ∑ θ, x θ = 1)
    (hD : ∀ y, ∑ θ, x θ * ((∫⁻ y, ℓ θ y ∂ν).toReal - (ℓ θ y).toReal) ≤ 0) :
    ∀ ν' : Measure 𝓨, IsProbabilityMeasure ν' →
      ∫⁻ θ, ∫⁻ y, ℓ θ y ∂ν ∂(ofRealWeights x) ≤ ∫⁻ θ, ∫⁻ y, ℓ θ y ∂ν' ∂(ofRealWeights x) := by
  intro ν' hν'
  have := isProbabilityMeasure_ofRealWeights hx hx1
  rw [← ENNReal.toReal_le_toReal (avg_ne_top (risk_ne_top hℓ ν) _)
    (avg_ne_top (risk_ne_top hℓ ν') _), toReal_avg (risk_ne_top hℓ ν),
    toReal_avg (risk_ne_top hℓ ν')]
  simp_rw [ofRealWeights_real_singleton hx, toReal_risk hℓ ν']
  calc ∑ θ, x θ * (∫⁻ y, ℓ θ y ∂ν).toReal
      = ∑ y, ν'.real {y} * ∑ θ, x θ * (∫⁻ y, ℓ θ y ∂ν).toReal := by
        rw [← Finset.sum_mul, sum_measureReal_singleton_eq_one, one_mul]
    _ ≤ ∑ y, ν'.real {y} * ∑ θ, x θ * (ℓ θ y).toReal :=
        Finset.sum_le_sum fun y _ ↦ mul_le_mul_of_nonneg_left (by
          have := hD y
          simp only [mul_sub, Finset.sum_sub_distrib] at this
          linarith) measureReal_nonneg
    _ = ∑ θ, x θ * ∑ y, ν'.real {y} * (ℓ θ y).toReal := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun θ _ ↦ Finset.sum_congr rfl fun y _ ↦ by ring

include hℓ in
theorem exists_isBayesEstimator_iff_not_isStrictlyDominated (ν : Measure 𝓨)
    [IsProbabilityMeasure ν] :
    (∃ π : Measure Θ, IsProbabilityMeasure π ∧
        IsBayesEstimator ℓ (Kernel.discard Θ) (Kernel.const Unit ν) π) ↔
      ¬ IsStrictlyDominated ℓ ν := by
  simp_rw [isBayesEstimator_discard_const_iff]
  refine ⟨fun ⟨π, hπ, h⟩ ↦ not_isStrictlyDominated_of_bayes hℓ h, fun hnd ↦ ?_⟩
  let D : Matrix 𝓨 Θ ℝ := .of fun y θ ↦ (∫⁻ y, ℓ θ y ∂ν).toReal - (ℓ θ y).toReal
  rcases Matrix.gordan D with ⟨w, hw, hpos⟩ | ⟨x, hx, hx1, hxD⟩
  · exfalso
    rcases isEmpty_or_nonempty Θ with hΘ | hne
    · exact hnd ⟨ν, inferInstance, fun θ ↦ (IsEmpty.false θ).elim⟩
    obtain ⟨θ₁⟩ := hne
    have hs : 0 < ∑ y, w y := by
      by_contra hle
      have hzero : ∀ y, w y = 0 := fun y ↦ le_antisymm
        (by linarith [Finset.single_le_sum (fun y _ ↦ hw y) (Finset.mem_univ y)]) (hw y)
      have := hpos θ₁
      simp [Matrix.vecMul, dotProduct, hzero] at this
    have hw' (y : 𝓨) : 0 ≤ w y * (∑ y, w y)⁻¹ := mul_nonneg (hw y) (inv_nonneg.2 hs.le)
    have := isProbabilityMeasure_ofRealWeights hw'
      (by rw [← Finset.sum_mul, mul_inv_cancel₀ hs.ne'])
    refine hnd ⟨ofRealWeights fun y ↦ w y * (∑ y, w y)⁻¹, this, fun θ ↦ ?_⟩
    rw [← ENNReal.toReal_lt_toReal (risk_ne_top hℓ _ θ) (risk_ne_top hℓ ν θ), toReal_risk hℓ]
    simp_rw [ofRealWeights_real_singleton hw']
    have hθ := hpos θ
    simp only [Matrix.vecMul, dotProduct, D, Matrix.of_apply, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul] at hθ
    have : ∑ y, w y * (∑ y, w y)⁻¹ * (ℓ θ y).toReal =
        (∑ y, w y)⁻¹ * ∑ y, w y * (ℓ θ y).toReal := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ ↦ by ring
    rw [this, inv_mul_lt_iff₀ hs]
    linarith
  · exact ⟨ofRealWeights x, isProbabilityMeasure_ofRealWeights hx hx1,
      bayes_of_real hℓ hx hx1 fun y ↦ by
        simpa [Matrix.mulVec, dotProduct, D, mul_comm] using hxD y⟩

/-! ### Admissibility and the complete class theorem -/

include hℓ in
theorem isAdmissible_iff_exists_isBayesEstimator [Nonempty Θ] (ν : Measure 𝓨)
    [IsProbabilityMeasure ν] :
    IsAdmissible ℓ ν ↔ ∃ π : Measure Θ, IsProbabilityMeasure π ∧ (∀ θ, π {θ} ≠ 0) ∧
      IsBayesEstimator ℓ (Kernel.discard Θ) (Kernel.const Unit ν) π := by
  simp_rw [isBayesEstimator_discard_const_iff]
  classical
  let D : Matrix 𝓨 Θ ℝ := .of fun y θ ↦ (∫⁻ y, ℓ θ y ∂ν).toReal - (ℓ θ y).toReal
  constructor
  · intro hadm
    let A : Matrix (𝓨 ⊕ Θ) Θ ℝ := .of fun r θ ↦ match r with
      | .inl y => D y θ
      | .inr θ' => if θ' = θ then -1 else 0
    let b : 𝓨 ⊕ Θ → ℝ := fun r ↦ match r with
      | .inl _ => 0
      | .inr _ => -1
    rcases Matrix.farkas A b with ⟨x, hx⟩ | ⟨z, hz, hzA, hzb⟩
    · have hx1 : ∀ θ, 1 ≤ x θ := fun θ ↦ by
        have := hx (.inr θ)
        simp [Matrix.mulVec, dotProduct, A, b] at this
        linarith
      have hD : ∀ y, ∑ θ, x θ * D y θ ≤ 0 := fun y ↦ by
        simpa [Matrix.mulVec, dotProduct, A, b, mul_comm] using hx (.inl y)
      have hS : 0 < ∑ θ, x θ :=
        Finset.sum_pos (fun θ _ ↦ by linarith [hx1 θ]) Finset.univ_nonempty
      have hp (θ : Θ) : 0 ≤ x θ * (∑ θ, x θ)⁻¹ :=
        mul_nonneg (by linarith [hx1 θ]) (inv_nonneg.2 hS.le)
      have hp1 : ∑ θ, x θ * (∑ θ, x θ)⁻¹ = 1 := by
        rw [← Finset.sum_mul, mul_inv_cancel₀ hS.ne']
      refine ⟨ofRealWeights fun θ ↦ x θ * (∑ θ, x θ)⁻¹,
        isProbabilityMeasure_ofRealWeights hp hp1, fun θ ↦ ?_, bayes_of_real hℓ hp hp1 fun y ↦ ?_⟩
      · rw [ofRealWeights, Measure.ofWeights_apply_singleton, ne_eq, ENNReal.ofReal_eq_zero,
          not_le]
        exact mul_pos (by linarith [hx1 θ]) (inv_pos.2 hS)
      · have h : ∑ θ, x θ * (∑ θ, x θ)⁻¹ * ((∫⁻ y, ℓ θ y ∂ν).toReal - (ℓ θ y).toReal) =
            (∑ θ, x θ)⁻¹ * ∑ θ, x θ * D y θ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun θ _ ↦ by simp only [D, Matrix.of_apply]; ring
        rw [h]
        exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hS.le) (hD y)
    · exfalso
      have hcol : ∀ θ, ∑ y, z (.inl y) * D y θ = z (.inr θ) := fun θ ↦ by
        have := congrFun hzA θ
        simp [Matrix.vecMul, dotProduct, A, Fintype.sum_sum_type] at this
        linarith
      have hsum : 0 < ∑ θ, z (.inr θ) := by
        simp [dotProduct, b, Fintype.sum_sum_type] at hzb
        linarith
      obtain ⟨θ₀, -, hθ₀⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ) (f := fun _ ↦ (0 : ℝ))
        (g := fun θ ↦ z (.inr θ)) (by simpa using hsum)
      have hw : 0 < ∑ y, z (.inl y) := by
        refine lt_of_le_of_ne (Finset.sum_nonneg fun y _ ↦ hz _) fun h0 ↦ ?_
        have hzero : ∀ y, z (.inl y) = 0 := fun y ↦ le_antisymm
          (by linarith [Finset.single_le_sum (fun y _ ↦ hz (.inl y)) (Finset.mem_univ y)])
          (hz _)
        have := hcol θ₀
        simp [hzero] at this
        linarith
      have hw' (y : 𝓨) : 0 ≤ z (.inl y) * (∑ y, z (.inl y))⁻¹ :=
        mul_nonneg (hz _) (inv_nonneg.2 hw.le)
      have hw1 : ∑ y, z (.inl y) * (∑ y, z (.inl y))⁻¹ = 1 := by
        rw [← Finset.sum_mul, mul_inv_cancel₀ hw.ne']
      have := isProbabilityMeasure_ofRealWeights hw' hw1
      have hrisk (θ : Θ) : (∫⁻ y, ℓ θ y ∂(ofRealWeights fun y ↦ z (.inl y) *
          (∑ y, z (.inl y))⁻¹)).toReal =
            (∫⁻ y, ℓ θ y ∂ν).toReal - (∑ y, z (.inl y))⁻¹ * z (.inr θ) := by
        rw [toReal_risk hℓ, ← hcol θ]
        simp_rw [ofRealWeights_real_singleton hw']
        set R := (∫⁻ y, ℓ θ y ∂ν).toReal
        set c := ∑ y, z (.inl y)
        simp only [D, Matrix.of_apply]
        rw [eq_sub_iff_add_eq, Finset.mul_sum, ← Finset.sum_add_distrib]
        rw [Finset.sum_congr rfl fun y _ ↦ show z (.inl y) * c⁻¹ * (ℓ θ y).toReal +
            c⁻¹ * (z (.inl y) * (R - (ℓ θ y).toReal)) = z (.inl y) * c⁻¹ * R by ring,
          ← Finset.sum_mul, hw1, one_mul]
      have hle : ∀ θ, ∫⁻ y, ℓ θ y ∂(ofRealWeights fun y ↦ z (.inl y) * (∑ y, z (.inl y))⁻¹) ≤
          ∫⁻ y, ℓ θ y ∂ν := fun θ ↦ by
        rw [← ENNReal.toReal_le_toReal (risk_ne_top hℓ _ θ) (risk_ne_top hℓ ν θ), hrisk]
        linarith [mul_nonneg (inv_nonneg.2 hw.le) (hz (.inr θ))]
      have heq := congrArg ENNReal.toReal (hadm _ this hle θ₀)
      rw [hrisk] at heq
      linarith [mul_pos (inv_pos.2 hw) hθ₀]
  · rintro ⟨π, hπ, hπ0, h⟩ ν' hν' hle θ
    by_contra hne
    have hlt : ∫⁻ y, ℓ θ y ∂ν' < ∫⁻ y, ℓ θ y ∂ν := lt_of_le_of_ne (hle θ) hne
    have hπθ : 0 < π.real {θ} := ENNReal.toReal_pos (hπ0 θ) (measure_ne_top _ _)
    have h' := h ν' hν'
    rw [← ENNReal.toReal_le_toReal (avg_ne_top (risk_ne_top hℓ ν) π)
      (avg_ne_top (risk_ne_top hℓ ν') π), toReal_avg (risk_ne_top hℓ ν),
      toReal_avg (risk_ne_top hℓ ν')] at h'
    refine absurd h' (not_le.2 (Finset.sum_lt_sum (fun θ' _ ↦ ?_) ⟨θ, Finset.mem_univ _, ?_⟩))
    · exact mul_le_mul_of_nonneg_left ((ENNReal.toReal_le_toReal (risk_ne_top hℓ ν' θ')
        (risk_ne_top hℓ ν θ')).2 (hle θ')) measureReal_nonneg
    · exact mul_lt_mul_of_pos_left ((ENNReal.toReal_lt_toReal (risk_ne_top hℓ ν' θ)
        (risk_ne_top hℓ ν θ)).2 hlt) hπθ

end Loss

/-! ### Payoffs

A payoff table `U : 𝓨 → Θ → ℝ` is a loss with the sign reversed: the regret `C − U` at a bound `C`
on the payoffs ranks randomized actions as their payoffs do, the other way round. -/

section Payoff

variable (U : 𝓨 → Θ → ℝ)

private theorem toReal_avg_regret {C : ℝ} (hC : ∀ y θ, U y θ ≤ C) (ν : Measure 𝓨)
    [IsProbabilityMeasure ν] (P : Measure Θ) [IsProbabilityMeasure P] :
    (∫⁻ θ, ∫⁻ y, regret U C θ y ∂ν ∂P).toReal = C - expectedPayoff U P ν := by
  rw [toReal_avg (risk_ne_top (regret_ne_top U C) ν), expectedPayoff_eq_sum]
  simp_rw [toReal_risk_regret U hC, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    sum_measureReal_singleton_eq_one, one_mul]

private theorem maximizesPayoff_iff_regret {C : ℝ} (hC : ∀ y θ, U y θ ≤ C) {ν : Measure 𝓨}
    [IsProbabilityMeasure ν] {P : Measure Θ} [IsProbabilityMeasure P] :
    MaximizesPayoff U P ν ↔ ∀ ν' : Measure 𝓨, IsProbabilityMeasure ν' →
      ∫⁻ θ, ∫⁻ y, regret U C θ y ∂ν ∂P ≤ ∫⁻ θ, ∫⁻ y, regret U C θ y ∂ν' ∂P := by
  refine forall₂_congr fun ν' hν' ↦ ?_
  rw [← ENNReal.toReal_le_toReal (avg_ne_top (risk_ne_top (regret_ne_top U C) ν) P)
    (avg_ne_top (risk_ne_top (regret_ne_top U C) ν') P), toReal_avg_regret U hC,
    toReal_avg_regret U hC, sub_le_sub_iff_left]

theorem exists_maximizesPayoff_iff_not_isStrictlyPayoffDominated (ν : Measure 𝓨)
    [IsProbabilityMeasure ν] :
    (∃ P : Measure Θ, IsProbabilityMeasure P ∧ MaximizesPayoff U P ν) ↔
      ¬ IsStrictlyPayoffDominated U ν := by
  obtain ⟨C, hC⟩ := exists_bound U
  have h := exists_isBayesEstimator_iff_not_isStrictlyDominated (regret_ne_top U C) ν
  simp_rw [isBayesEstimator_discard_const_iff] at h
  refine Iff.trans ?_ (h.trans (not_congr ?_))
  · exact exists_congr fun P ↦ ⟨fun ⟨hP, hm⟩ ↦ ⟨hP, (maximizesPayoff_iff_regret U hC).1 hm⟩,
      fun ⟨hP, hm⟩ ↦ ⟨hP, (maximizesPayoff_iff_regret U hC).2 hm⟩⟩
  · exact exists_congr fun ν' ↦
      ⟨fun ⟨hν', hlt⟩ ↦ ⟨hν', fun θ ↦ (risk_regret_lt_iff U hC θ).1 (hlt θ)⟩,
        fun ⟨hν', hlt⟩ ↦ ⟨hν', fun θ ↦ (risk_regret_lt_iff U hC θ).2 (hlt θ)⟩⟩

theorem not_isWeaklyPayoffDominated_iff_exists_maximizesPayoff [Nonempty Θ] (ν : Measure 𝓨)
    [IsProbabilityMeasure ν] :
    ¬ IsWeaklyPayoffDominated U ν ↔
      ∃ P : Measure Θ, IsProbabilityMeasure P ∧ (∀ θ, P {θ} ≠ 0) ∧ MaximizesPayoff U P ν := by
  obtain ⟨C, hC⟩ := exists_bound U
  have h := isAdmissible_iff_exists_isBayesEstimator (regret_ne_top U C) ν
  simp_rw [isBayesEstimator_discard_const_iff] at h
  refine Iff.trans ?_ (h.trans (exists_congr fun P ↦ ⟨fun ⟨hP, h0, hm⟩ ↦
    ⟨hP, h0, (maximizesPayoff_iff_regret U hC).2 hm⟩, fun ⟨hP, h0, hm⟩ ↦
    ⟨hP, h0, (maximizesPayoff_iff_regret U hC).1 hm⟩⟩))
  simp only [IsWeaklyPayoffDominated, IsAdmissible, not_exists, not_and]
  refine forall₂_congr fun ν' hν' ↦ ?_
  simp_rw [risk_regret_le_iff U hC]
  refine ⟨fun hnd hle θ ↦ ?_, fun hadm hle θ hlt ↦ ?_⟩
  · have := hnd hle θ
    refine le_antisymm ((risk_regret_le_iff U hC θ).2 (hle θ)) ?_
    rw [← ENNReal.toReal_le_toReal (risk_ne_top (regret_ne_top U C) ν θ)
      (risk_ne_top (regret_ne_top U C) ν' θ), toReal_risk_regret U hC, toReal_risk_regret U hC]
    linarith
  · have := congrArg ENNReal.toReal (hadm hle θ)
    rw [toReal_risk_regret U hC, toReal_risk_regret U hC] at this
    linarith

end Payoff

end ProbabilityTheory
