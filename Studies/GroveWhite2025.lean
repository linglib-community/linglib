/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.Distributions.Bernoulli
public import Linglib.Semantics.Attitudes.Factivity
public import Linglib.Data.Examples.GroveWhite2025
public import Mathlib.Probability.ConditionalProbability

/-!
# Grove and White (2025): Factivity, Presupposition Projection, and Discrete Knowledge

This file formalizes the response models of Grove and White, who ask whether the gradience of
projection judgments comes from resolved indeterminacy, factivity being a discrete property of
token occurrences, or from unresolved indeterminacy. A model is a distribution over answers in
the unit interval to *how likely is it that φ?*. Factivity is resolved when a reading of the
predicate is drawn and the answer computed under it, and unresolved when it enters the
probability of the answer. World knowledge is gradient when the answer is the complement's
probability and discrete when it is the complement's truth at a drawn index. The four
combinations are the models the paper fits to Degen and Tonhauser's projection data; they share
their mean answer and differ in spread.

## Main definitions

* `likely`: the probability of a proposition under a distribution over indices.
* `update`: the common ground conditioned on a reading of the lexical entry (13).
* `resolvedFactivity`, `unresolvedFactivity`: the completions of a norming model by factivity.
* `discreteFactivity`, `whollyDiscrete`, `whollyGradient`, `discreteWorld`: the four models.

* `integral_discreteFactivity` and its siblings: the four share the mean answer.
* `variance_whollyGradient` and its siblings: only the models with a discrete component spread.

## Implementation notes

Updating the common ground conditions a prior over `Factivity.World` on a reading's content,
belief and the complement being independent under the prior; under unresolved factivity the
factivity value of an index is likewise independent of the complement. The response noise of
section 4.1, the truncated normal likelihood, is not modeled, so each model is the distribution
of the intended answer. The paper's illustrative sentences are rows of `GroveWhite2025.Examples`.

## References

* [grove-white-2025]
* [degen-tonhauser-2021]
-/

@[expose] public section

open MeasureTheory Measure ProbabilityTheory Factivity unitInterval

namespace GroveWhite2025

/-! ### Likelihood -/

/-- `likely μ s` is the probability of the proposition `s` under the distribution `μ` over
indices, as a point of the unit interval. -/
noncomputable def likely {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ] (s : Set Ω) : I :=
  ⟨μ.real s, measureReal_nonneg, measureReal_le_one⟩

@[simp] theorem coe_likely {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ] (s : Set Ω) : (likely μ s : ℝ) = μ.real s := rfl

/-! ### The lexical entry (13) -/

/-- A clause-embedding predicate has two readings in (13). -/
inductive FactivityReading where
  /-- The reading `m`, which triggers the projective inference. -/
  | factive
  /-- The reading `n`, which does not. -/
  | nonfactive
  deriving DecidableEq

instance : MeasurableSpace FactivityReading := ⊤
instance : DiscreteMeasurableSpace FactivityReading := ⟨fun _ ↦ trivial⟩

/-- The content of *know* under its factive reading is `Factivity.World.Knows`, belief together
with the complement, and under its non-factive reading `Factivity.World.Thinks`, belief alone. -/
def clauseEmbeddingSem : FactivityReading → World → Prop
  | .factive => World.Knows
  | .nonfactive => World.Thinks

/-- The common ground is a prior over worlds under which belief and the complement are
independent, with probabilities `b` and `p`. -/
noncomputable def commonGround (b p : I) : Measure World :=
  Ber(true, false, b).prod Ber(true, false, p)

instance (b p : I) : IsProbabilityMeasure (commonGround b p) := by
  unfold commonGround; infer_instance

/-- Updating the common ground with a reading conditions it on the reading's content. -/
noncomputable def update (b p : I) (r : FactivityReading) : Measure World :=
  (commonGround b p)[|{w | clauseEmbeddingSem r w}]

instance (b p : I) (r : FactivityReading) : IsZeroOrProbabilityMeasure (update b p r) := by
  unfold update; infer_instance

section Update

variable {b p : I}

private theorem toNNReal_ne_zero {x : I} (hx : x ≠ 0) : toNNReal x ≠ 0 :=
  fun h ↦ hx (Subtype.ext (by simpa using congrArg NNReal.toReal h))

theorem update_factive (hb : b ≠ 0) (hp : p ≠ 0) : update b p .factive = dirac (true, true) := by
  have hK : {w : World | clauseEmbeddingSem .factive w} = {true} ×ˢ {true} := by
    ext ⟨x, y⟩; simp [clauseEmbeddingSem, World.Knows]
  have h0 : commonGround b p {(true, true)} ≠ 0 := by
    rw [← Set.singleton_prod_singleton, commonGround, Measure.prod_prod]
    simp [toNNReal_ne_zero hb, toNNReal_ne_zero hp]
  refine Measure.ext_of_singleton fun w ↦ ?_
  rw [update, hK, cond_apply (by measurability)]
  obtain ⟨x, y⟩ := w
  cases x <;> cases y <;> simp [ENNReal.inv_mul_cancel h0 (measure_ne_top _ _)]

theorem update_nonfactive (hb : b ≠ 0) :
    update b p .nonfactive = (dirac true).prod Ber(true, false, p) := by
  have hT : {w : World | clauseEmbeddingSem .nonfactive w} = {true} ×ˢ Set.univ := by
    ext ⟨x, y⟩; simp [clauseEmbeddingSem, World.Thinks]
  refine Measure.ext_of_singleton fun w ↦ ?_
  rw [update, hT, cond_apply (by measurability)]
  obtain ⟨x, y⟩ := w
  rw [← Set.singleton_prod_singleton, Set.prod_inter_prod, commonGround, Measure.prod_prod,
    Measure.prod_prod, Measure.prod_prod]
  cases x <;> cases y <;> simp
  all_goals rw [← mul_assoc, ENNReal.inv_mul_cancel (by simp [toNNReal_ne_zero hb])
    ENNReal.coe_ne_top, one_mul]

private theorem setOf_complement : {w : World | w.complement} = Set.univ ×ˢ {true} := by
  ext ⟨_, _⟩; simp

theorem likely_update_factive (hb : b ≠ 0) (hp : p ≠ 0) :
    likely (update b p .factive) {w | w.complement} = 1 := by
  ext; simp [update_factive hb hp]

theorem likely_update_nonfactive (hb : b ≠ 0) :
    likely (update b p .nonfactive) {w | w.complement} = p := by
  ext; simp [update_nonfactive hb, setOf_complement, measureReal_def, Measure.prod_prod]

end Update

/-! ### Norming models, section 4.2 -/

/-- World knowledge as unresolved indeterminacy answers with the complement's probability `p`
under the common ground. -/
noncomputable abbrev normingGradient (p : I) : Measure I := dirac p

/-- World knowledge as resolved indeterminacy answers with the complement's truth at an index
drawn from the common ground, true with probability `p`. -/
noncomputable abbrev normingDiscrete (p : I) : Measure I := Ber(1, 0, p)

/-! ### Completing a norming model by factivity, section 4.3 -/

/-- Resolved factivity draws a reading of (13), the factive one with probability `τ`, and
answers `1` under it and as the norming model `ν` does otherwise. -/
noncomputable def resolvedFactivity (τ : I) (ν : Measure I) : Measure I :=
  Ber(FactivityReading.factive, FactivityReading.nonfactive, τ).bind fun
    | .factive => dirac 1
    | .nonfactive => ν

/-- `disjunction τ d` is the probability that an index is factive or the complement true there,
the two independent with probabilities `τ` and `d`. -/
noncomputable def disjunction (τ d : I) : I :=
  likely (Ber(true, false, τ).prod Ber(true, false, d)) {x | x.1 = true ∨ x.2 = true}

theorem disjunction_eq (τ d : I) : disjunction τ d = σ (σ τ * σ d) := by
  have : {x : Bool × Bool | x.1 = true ∨ x.2 = true} = ({false} ×ˢ {false})ᶜ := by
    ext ⟨x, y⟩; cases x <;> cases y <;> simp
  ext
  rw [disjunction, coe_likely, this, probReal_compl_eq_one_sub (by measurability), measureReal_def,
    Measure.prod_prod]
  simp [coe_symm_eq]

theorem measurable_disjunction (τ : I) : Measurable (disjunction τ) := by
  rw [show disjunction τ = fun d ↦ σ (σ τ * σ d) from funext (disjunction_eq τ)]
  exact Measurable.subtype_mk (by fun_prop : Measurable fun d : I ↦ 1 - (1 - (τ : ℝ)) * (1 - d))

/-- Unresolved factivity, the lexical entry (14), answers with the probability that the index
is factive or the complement true there, given the norming model's answer. -/
noncomputable def unresolvedFactivity (τ : I) (ν : Measure I) : Measure I :=
  ν.map (disjunction τ)

/-- Discrete factivity with gradient world knowledge is the model of section 4.3.1. -/
noncomputable abbrev discreteFactivity (τ p : I) : Measure I :=
  resolvedFactivity τ (normingGradient p)

/-- Discrete factivity with discrete world knowledge is the other model of section 4.3.1. -/
noncomputable abbrev whollyDiscrete (τ p : I) : Measure I :=
  resolvedFactivity τ (normingDiscrete p)

/-- Gradient factivity with gradient world knowledge is the model of section 4.3.2. -/
noncomputable abbrev whollyGradient (τ p : I) : Measure I :=
  unresolvedFactivity τ (normingGradient p)

/-- Gradient factivity with discrete world knowledge is the other model of section 4.3.2. -/
noncomputable abbrev discreteWorld (τ p : I) : Measure I :=
  unresolvedFactivity τ (normingDiscrete p)

section Completion

variable (τ : I) (ν : Measure I)

theorem resolvedFactivity_eq : resolvedFactivity τ ν = toNNReal τ • dirac 1 + toNNReal (σ τ) • ν :=
  bernoulliMeasure_bind _ _ _ .of_discrete

theorem unresolvedFactivity_eq : unresolvedFactivity τ ν = ν.map fun d ↦ σ (σ τ * σ d) := by
  rw [unresolvedFactivity, show disjunction τ = fun d ↦ σ (σ τ * σ d) from
    funext (disjunction_eq τ)]

instance [IsProbabilityMeasure ν] : IsProbabilityMeasure (resolvedFactivity τ ν) :=
  ⟨by simp [resolvedFactivity_eq]⟩

instance [IsProbabilityMeasure ν] : IsProbabilityMeasure (unresolvedFactivity τ ν) :=
  (isProbabilityMeasure_map_iff (measurable_disjunction τ).aemeasurable).mpr ‹_›

@[simp] theorem resolvedFactivity_zero : resolvedFactivity 0 ν = ν := by
  simp [resolvedFactivity_eq]

@[simp] theorem resolvedFactivity_one : resolvedFactivity 1 ν = dirac 1 := by
  simp [resolvedFactivity_eq]

@[simp] theorem unresolvedFactivity_zero : unresolvedFactivity 0 ν = ν := by
  simp [unresolvedFactivity_eq]

@[simp] theorem unresolvedFactivity_one [IsProbabilityMeasure ν] :
    unresolvedFactivity 1 ν = dirac 1 := by
  simp [unresolvedFactivity_eq, Measure.map_const]

end Completion

/-! ### The resolved models from the lexical entry -/

/-- The answer at an index under discrete world knowledge is the complement's truth value. -/
def complementValue (w : World) : I := bif w.complement then 1 else 0

section Derivation

variable (τ : I) {b p : I}

/-- The discrete-factivity model draws a reading of (13) and answers with the probability of
the complement under the common ground updated with it. -/
theorem discreteFactivity_eq_bind_update (hb : b ≠ 0) (hp : p ≠ 0) :
    discreteFactivity τ p = Ber(FactivityReading.factive, .nonfactive, τ).bind
      fun r ↦ dirac (likely (update b p r) {w | w.complement}) := by
  rw [discreteFactivity, resolvedFactivity]
  congr 1
  funext r
  cases r
  · rw [likely_update_factive hb hp]
  · rw [likely_update_nonfactive hb]

/-- The wholly-discrete model draws a reading of (13) and answers with the complement's truth
at an index drawn from the common ground updated with it. -/
theorem whollyDiscrete_eq_bind_update (hb : b ≠ 0) (hp : p ≠ 0) :
    whollyDiscrete τ p = Ber(FactivityReading.factive, .nonfactive, τ).bind
      fun r ↦ (update b p r).map complementValue := by
  rw [whollyDiscrete, resolvedFactivity]
  congr 1
  funext r
  cases r
  · simp [update_factive hb hp, map_dirac' (f := complementValue) .of_discrete, complementValue]
  · rw [update_nonfactive hb, show complementValue = (fun c ↦ bif c then 1 else 0) ∘ Prod.snd
      from rfl, ← Measure.map_map .of_discrete measurable_snd, Measure.map_snd_prod]
    simp [normingDiscrete]

end Derivation

/-! ### The four models in closed form -/

section Models

variable (τ p : I)

/-- The models in closed form. -/
theorem discreteFactivity_eq : discreteFactivity τ p = Ber(1, p, τ) := by
  rw [discreteFactivity, resolvedFactivity_eq, normingGradient, bernoulliMeasure_def]

theorem whollyDiscrete_eq : whollyDiscrete τ p = Ber(1, 0, σ (σ τ * σ p)) := by
  have h₁ : toNNReal τ + toNNReal (σ τ) * toNNReal p = toNNReal (σ (σ τ * σ p)) :=
    NNReal.eq (by simp [coe_symm_eq]; ring)
  have h₂ : toNNReal (σ τ) * toNNReal (σ p) = toNNReal (σ τ * σ p) := NNReal.eq (by simp)
  rw [whollyDiscrete, resolvedFactivity_eq, normingDiscrete, bernoulliMeasure_def,
    bernoulliMeasure_def, symm_symm, smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul, h₁,
    h₂]

theorem whollyGradient_eq : whollyGradient τ p = dirac (σ (σ τ * σ p)) := by
  rw [whollyGradient, unresolvedFactivity, normingGradient,
    Measure.map_dirac' (measurable_disjunction τ), disjunction_eq]

theorem discreteWorld_eq : discreteWorld τ p = Ber(1, τ, p) := by
  simp [unresolvedFactivity_eq]

/-! ### Mean answer

The four models share the mean `τ + (1 - τ) * p`. -/

theorem integral_discreteFactivity : ∫ d, (d : ℝ) ∂discreteFactivity τ p = τ + (1 - τ) * p := by
  simp [discreteFactivity_eq, integral_bernoulliMeasure]

theorem integral_whollyDiscrete : ∫ d, (d : ℝ) ∂whollyDiscrete τ p = τ + (1 - τ) * p := by
  simp [whollyDiscrete_eq, integral_bernoulliMeasure, coe_symm_eq]; ring

theorem integral_whollyGradient : ∫ d, (d : ℝ) ∂whollyGradient τ p = τ + (1 - τ) * p := by
  simp [whollyGradient_eq, coe_symm_eq]; ring

theorem integral_discreteWorld : ∫ d, (d : ℝ) ∂discreteWorld τ p = τ + (1 - τ) * p := by
  simp [discreteWorld_eq, integral_bernoulliMeasure]; ring

/-! ### Spread of the answer

The wholly gradient model is a single degenerate distribution; the models with a discrete
component are mixtures with a component at the endpoint `1`, the shape that section 4.4 credits
with capturing the dips in the middle of the scale. -/

theorem variance_discreteFactivity :
    Var[fun d : I ↦ (d : ℝ); discreteFactivity τ p] = τ * (1 - τ) * (1 - p) ^ 2 := by
  simp [discreteFactivity_eq, variance_bernoulliMeasure _ _ _ measurable_subtype_coe.aemeasurable]

theorem variance_whollyDiscrete :
    Var[fun d : I ↦ (d : ℝ); whollyDiscrete τ p] = (τ + (1 - τ) * p) * (1 - τ) * (1 - p) := by
  simp [whollyDiscrete_eq, variance_bernoulliMeasure _ _ _ measurable_subtype_coe.aemeasurable,
    coe_symm_eq]
  ring

theorem variance_whollyGradient : Var[fun d : I ↦ (d : ℝ); whollyGradient τ p] = 0 := by
  simp [whollyGradient_eq]

theorem variance_discreteWorld :
    Var[fun d : I ↦ (d : ℝ); discreteWorld τ p] = p * (1 - p) * (1 - τ) ^ 2 := by
  simp [discreteWorld_eq, variance_bernoulliMeasure _ _ _ measurable_subtype_coe.aemeasurable]

end Models

end GroveWhite2025
