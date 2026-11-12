/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.InformationTheory.KullbackLeibler.Basic
public import Linglib.Core.MeasureTheory.Measure.AbsolutelyContinuous
public import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# Unbalanced optimal transport

A plan is a measure on a product. Its cost against two reference marginals is the transported cost
plus three penalties, each a Kullback–Leibler divergence with a weight: of the plan from the
counting measure, which is minus its entropy up to a constant, and of each marginal of the plan
from its reference. A weight of `∞` makes its penalty a constraint, since the cost is then
infinite unless the divergence vanishes, so that [a finite cost forces the
marginal](##InformationTheory.fst_eq_of_transportCost_ne_top). Entropic optimal transport is the
case of two infinite marginal weights. Scaling the cost function and the three weights together
[scales the cost](##InformationTheory.transportCost_smul), and so leaves the optimal plans
unchanged.

On a finite product the transported cost and the entropy penalty together are [a divergence from
the Gibbs measure](##InformationTheory.lintegral_add_mul_klDiv_count) of the cost, so the cost of a
plan is a sum of three divergences. With one marginal fixed and the other free, the chain rule
for the divergence then gives the cost of a plan as [its divergence from the plan built on the
conditional kernel of the Gibbs measure](##InformationTheory.transportCost_compProd), which is
therefore the [least costly](##InformationTheory.transportCost_compProd_condKernel_le) and the
[only such](##InformationTheory.transportCost_compProd_eq_iff).

## Implementation notes

The entropy of a plan `ρ` on a finite product is usually written `-∑ ρ (log ρ - 1)`, which is the
number of points less `klDiv ρ count`. The cost here uses the divergence, so it is an extended
nonnegative real and differs from the usual objective by the weight times the number of points.

## References

* [liero-mielke-savare-2018]
* [chizat-peyre-schmitzer-vialard-2018]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace InformationTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The cost of the plan `ρ` in unbalanced optimal transport: the transported cost `∫⁻ c ∂ρ`, plus
`ε` times the divergence of the plan from the counting measure, plus the divergences of its two
marginals from `μ` and `ν` with weights `εfst` and `εsnd`. -/
noncomputable def transportCost (c : α × β → ℝ≥0∞) (ε εfst εsnd : ℝ≥0∞) (μ : Measure α)
    (ν : Measure β) (ρ : Measure (α × β)) : ℝ≥0∞ :=
  ∫⁻ x, c x ∂ρ + ε * klDiv ρ .count + εfst * klDiv ρ.fst μ + εsnd * klDiv ρ.snd ν

variable {c : α × β → ℝ≥0∞} {ε εfst εsnd : ℝ≥0∞} {μ : Measure α} {ν : Measure β}
  {ρ : Measure (α × β)}

/-- Scaling the cost function and the three weights by `t` scales the cost of every plan by `t`. -/
theorem transportCost_smul (hc : Measurable c) (t : ℝ≥0∞) :
    transportCost (t • c) (t * ε) (t * εfst) (t * εsnd) μ ν ρ =
      t * transportCost c ε εfst εsnd μ ν ρ := by
  simp only [transportCost, Pi.smul_apply, smul_eq_mul, lintegral_const_mul t hc, mul_add,
    mul_assoc]

/-- A plan of finite cost under an infinite weight on the first marginal has that marginal. -/
theorem fst_eq_of_transportCost_ne_top [IsFiniteMeasure ρ] [IsFiniteMeasure μ]
    (h : transportCost c ε ∞ εsnd μ ν ρ ≠ ∞) : ρ.fst = μ := by
  by_contra hne
  refine h (ENNReal.add_eq_top.2 (.inl (ENNReal.add_eq_top.2 (.inr ?_))))
  exact ENNReal.top_mul (mt klDiv_eq_zero_iff.1 hne)

/-- A plan of finite cost under an infinite weight on the second marginal has that marginal. -/
theorem snd_eq_of_transportCost_ne_top [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (h : transportCost c ε εfst ∞ μ ν ρ ≠ ∞) : ρ.snd = ν := by
  by_contra hne
  exact h (ENNReal.add_eq_top.2 (.inr (ENNReal.top_mul (mt klDiv_eq_zero_iff.1 hne))))

/-- With the first marginal right, an infinite weight on it costs nothing. -/
theorem transportCost_top_of_fst_eq [IsFiniteMeasure μ] (h : ρ.fst = μ) :
    transportCost c ε ∞ εsnd μ ν ρ =
      ∫⁻ x, c x ∂ρ + ε * klDiv ρ .count + εsnd * klDiv ρ.snd ν := by
  rw [transportCost, h, klDiv_self, mul_zero, add_zero]

/-! ### The Gibbs measure

The transported cost and the entropy penalty together are a divergence from one reference measure,
whose density against the counting measure is the exponential of minus the cost over `ε`. -/

section Gibbs

variable {γ : Type*} [MeasurableSpace γ]

/-- The Gibbs measure of a cost function at temperature `ε` has density `exp (-c / ε)` against the
counting measure, and no mass where the cost is infinite. -/
noncomputable def gibbs (c : γ → ℝ≥0∞) (ε : ℝ≥0∞) : Measure γ :=
  Measure.count.withDensity fun x ↦ EReal.exp (-((c x / ε : ℝ≥0∞) : EReal))

variable [Fintype γ] [MeasurableSingletonClass γ] (c : γ → ℝ≥0∞)

omit [Fintype γ] in
theorem gibbs_apply_singleton (ε : ℝ≥0∞) (x : γ) :
    gibbs c ε {x} = EReal.exp (-((c x / ε : ℝ≥0∞) : EReal)) := by
  rw [gibbs, withDensity_apply _ (measurableSet_singleton x), Measure.restrict_singleton,
    Measure.count_singleton, one_smul, lintegral_dirac]

omit [Fintype γ] in
theorem gibbs_apply_singleton_le_one (ε : ℝ≥0∞) (x : γ) : gibbs c ε {x} ≤ 1 := by
  rw [gibbs_apply_singleton, EReal.exp_le_one_iff, EReal.neg_le, neg_zero]
  exact EReal.coe_ennreal_nonneg _

instance (ε : ℝ≥0∞) : IsFiniteMeasure (gibbs c ε) :=
  ⟨by
    rw [← Finset.coe_univ, ← sum_measure_singleton]
    exact ENNReal.sum_lt_top.2 fun x _ ↦
      (gibbs_apply_singleton_le_one c ε x).trans_lt ENNReal.one_lt_top⟩

variable {c} {e : ℝ}

omit [Fintype γ] in
theorem gibbs_apply_singleton_eq_zero_iff (he : 0 < e) {x : γ} :
    gibbs c (.ofReal e) {x} = 0 ↔ c x = ∞ := by
  rw [gibbs_apply_singleton, EReal.exp_eq_zero_iff, EReal.neg_eq_bot_iff,
    EReal.coe_ennreal_eq_top_iff, ENNReal.div_eq_top]
  simp [(ENNReal.ofReal_pos.2 he).ne']

omit [Fintype γ] in
theorem log_gibbs_real_singleton (he : 0 < e) {x : γ} (hx : c x ≠ ∞) :
    log ((gibbs c (.ofReal e)).real {x}) = -((c x).toReal / e) := by
  have hdiv : c x / ENNReal.ofReal e ≠ ∞ :=
    ENNReal.div_ne_top hx (ENNReal.ofReal_pos.2 he).ne'
  rw [measureReal_def, gibbs_apply_singleton, ← EReal.coe_ennreal_toReal hdiv, ← EReal.coe_neg,
    EReal.exp_coe, ENNReal.toReal_ofReal (exp_pos _).le, log_exp, ENNReal.toReal_div,
    ENNReal.toReal_ofReal he.le]

/-- The transported cost of a plan and `ε` times its divergence from the counting measure add up
to `ε` times its divergence from the Gibbs measure, and a constant. -/
theorem lintegral_add_mul_klDiv_count (c : γ → ℝ≥0∞) (he : 0 < e) (ρ : Measure γ)
    [IsFiniteMeasure ρ] :
    ∫⁻ x, c x ∂ρ + ENNReal.ofReal e * klDiv ρ .count =
      ENNReal.ofReal e * klDiv ρ (gibbs c (.ofReal e)) +
        ENNReal.ofReal (e * (Fintype.card γ - (gibbs c (.ofReal e)).real Set.univ)) := by
  have he' : ENNReal.ofReal e ≠ 0 := (ENNReal.ofReal_pos.2 he).ne'
  by_cases h : ∀ x, ρ {x} ≠ 0 → c x ≠ ∞
  · have hρG : ρ ≪ gibbs c (.ofReal e) :=
      Measure.absolutelyContinuous_of_forall_singleton fun x hx ↦ by_contra fun hρ ↦
        h x hρ ((gibbs_apply_singleton_eq_zero_iff he).1 hx)
    have hρc : ρ ≪ Measure.count :=
      Measure.absolutelyContinuous_of_forall_singleton fun x hx ↦ by simp at hx
    have hint : ∫⁻ x, c x ∂ρ = ENNReal.ofReal (∑ x, (c x).toReal * ρ.real {x}) := by
      rw [lintegral_fintype, ENNReal.ofReal_sum_of_nonneg fun x _ ↦
        mul_nonneg ENNReal.toReal_nonneg measureReal_nonneg]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rcases eq_or_ne (ρ {x}) 0 with h0 | h0
      · simp [measureReal_def, h0]
      · rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (h x h0),
          measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    have hcount : (Measure.count : Measure γ).real Set.univ = Fintype.card γ := by
      simp [measureReal_def]
    have hGle : (gibbs c (.ofReal e)).real Set.univ ≤ Fintype.card γ := by
      rw [← hcount]
      refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
      rw [← Finset.coe_univ, ← sum_measure_singleton, ← sum_measure_singleton]
      exact Finset.sum_le_sum fun x _ ↦ by
        simpa using gibbs_apply_singleton_le_one c (.ofReal e) x
    have hterm (x : γ) : ρ.real {x} * log (ρ.real {x} / (gibbs c (.ofReal e)).real {x}) =
        ρ.real {x} * log (ρ.real {x} / (Measure.count : Measure γ).real {x}) +
          (c x).toReal * ρ.real {x} / e := by
      rcases eq_or_ne (ρ {x}) 0 with h0 | h0
      · simp [measureReal_def, h0]
      · have hρx : ρ.real {x} ≠ 0 := (measureReal_ne_zero_iff (measure_ne_top _ _)).2 h0
        have hGx : (gibbs c (.ofReal e)).real {x} ≠ 0 :=
          (measureReal_ne_zero_iff (measure_ne_top _ _)).2 fun h0' ↦ h0 (hρG h0')
        have h1 : (Measure.count : Measure γ).real {x} = 1 := by simp [measureReal_def]
        rw [h1, div_one, log_div hρx hGx, log_gibbs_real_singleton he (h x h0)]
        ring
    rw [hint, ← ENNReal.ofReal_toReal (klDiv_ne_top hρc .of_finite),
      ← ENNReal.ofReal_toReal (klDiv_ne_top hρG .of_finite), ← ENNReal.ofReal_mul he.le,
      ← ENNReal.ofReal_mul he.le,
      ← ENNReal.ofReal_add (Finset.sum_nonneg fun x _ ↦
        mul_nonneg ENNReal.toReal_nonneg measureReal_nonneg)
        (mul_nonneg he.le ENNReal.toReal_nonneg),
      ← ENNReal.ofReal_add (mul_nonneg he.le ENNReal.toReal_nonneg)
        (mul_nonneg he.le (sub_nonneg.2 hGle)),
      toReal_klDiv_eq_sum_log_div_add hρc, toReal_klDiv_eq_sum_log_div_add hρG,
      Finset.sum_congr rfl fun x _ ↦ hterm x, Finset.sum_add_distrib, ← Finset.sum_div, hcount]
    congr 1
    field_simp
    ring
  · push Not at h
    obtain ⟨x, hρx, hcx⟩ := h
    have hL : ∫⁻ x, c x ∂ρ = ∞ := by
      rw [lintegral_fintype]
      exact ENNReal.sum_eq_top.2 ⟨x, Finset.mem_univ x, by rw [hcx]; exact ENNReal.top_mul hρx⟩
    have hR : klDiv ρ (gibbs c (.ofReal e)) = ∞ :=
      klDiv_of_not_ac fun hac ↦ hρx (hac ((gibbs_apply_singleton_eq_zero_iff he).2 hcx))
    rw [hL, hR, ENNReal.mul_top he', top_add, top_add]

end Gibbs

/-! ### One marginal fixed, the other free

With an infinite weight on the first marginal and none on the second, the plans of finite cost are
the composition-products of `μ` with a kernel, and the chain rule for the divergence gives the
cost of any of them as its divergence from the one built on the conditional kernel of the Gibbs
measure. -/

section HardFst

variable [Fintype α] [Fintype β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  [StandardBorelSpace β] [Nonempty β] (c : α × β → ℝ≥0∞) {e : ℝ} (μ : Measure α)
  [IsFiniteMeasure μ] (ν : Measure β) (κ : Kernel α β) [IsMarkovKernel κ]

/-- With the first marginal fixed at `μ` and the second free, the cost of the plan `μ ⊗ₘ κ` is `ε`
times its divergence from `μ ⊗ₘ (gibbs c ε).condKernel`, and a constant. -/
theorem transportCost_compProd (he : 0 < e) :
    transportCost c (.ofReal e) ∞ 0 μ ν (μ ⊗ₘ κ) =
      ENNReal.ofReal e * klDiv (μ ⊗ₘ κ) (μ ⊗ₘ (gibbs c (.ofReal e)).condKernel) +
        (ENNReal.ofReal e * klDiv μ (gibbs c (.ofReal e)).fst +
          ENNReal.ofReal (e * (Fintype.card (α × β) - (gibbs c (.ofReal e)).real Set.univ))) := by
  have hchain : klDiv (μ ⊗ₘ κ) (gibbs c (.ofReal e)) =
      klDiv μ (gibbs c (.ofReal e)).fst +
        klDiv (μ ⊗ₘ κ) (μ ⊗ₘ (gibbs c (.ofReal e)).condKernel) := by
    conv_lhs => rw [← (gibbs c (.ofReal e)).disintegrate (gibbs c (.ofReal e)).condKernel]
    exact klDiv_compProd_eq_add _ _ _ _
  rw [transportCost_top_of_fst_eq (Measure.fst_compProd μ κ), zero_mul, add_zero,
    lintegral_add_mul_klDiv_count c he, hchain, mul_add]
  ring

/-- With the first marginal fixed and the second free, the plan built on the conditional kernel
of the Gibbs measure costs least. -/
theorem transportCost_compProd_condKernel_le (he : 0 < e) :
    transportCost c (.ofReal e) ∞ 0 μ ν (μ ⊗ₘ (gibbs c (.ofReal e)).condKernel) ≤
      transportCost c (.ofReal e) ∞ 0 μ ν (μ ⊗ₘ κ) := by
  rw [transportCost_compProd c μ ν κ he, transportCost_compProd c μ ν _ he, klDiv_self, mul_zero,
    zero_add]
  exact le_add_self

/-- With the first marginal fixed and the second free, only that plan costs least, when its cost is
finite. -/
theorem transportCost_compProd_eq_iff (he : 0 < e)
    (hμ : klDiv μ (gibbs c (.ofReal e)).fst ≠ ∞) :
    transportCost c (.ofReal e) ∞ 0 μ ν (μ ⊗ₘ κ) =
        transportCost c (.ofReal e) ∞ 0 μ ν (μ ⊗ₘ (gibbs c (.ofReal e)).condKernel) ↔
      μ ⊗ₘ κ = μ ⊗ₘ (gibbs c (.ofReal e)).condKernel := by
  rw [transportCost_compProd c μ ν κ he, transportCost_compProd c μ ν _ he, klDiv_self, mul_zero,
    zero_add]
  refine ⟨fun h ↦ klDiv_eq_zero_iff.1 ?_, fun h ↦ by rw [h, klDiv_self, mul_zero, zero_add]⟩
  have h0 := (ENNReal.add_left_inj (ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμ, ENNReal.ofReal_ne_top⟩)).1
      (h.trans (zero_add _).symm)
  exact (mul_eq_zero.1 h0).resolve_left (ENNReal.ofReal_pos.2 he).ne'

end HardFst

end InformationTheory
