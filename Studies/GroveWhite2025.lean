/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.Distributions.Bernoulli
public import Linglib.Logic.Modal.Defs
public import Linglib.Data.Examples.GroveWhite2025
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Independence.Basic

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

The epistemic relation of (13) is an accessibility relation for each holder and the holder's
knowledge of the complement is necessity along it. Updating the common ground conditions it on a
reading's content; the non-factive reading leaves the complement's probability alone when the
common ground makes the complement independent of what the holder knows, a hypothesis of the
theorems that derive the resolved models. Under unresolved factivity the factivity value of an
index is likewise independent of the complement. The response noise of
section 4.1, the truncated normal likelihood, is not modeled, so each model is the distribution
of the intended answer. The paper's illustrative sentences are rows of `GroveWhite2025.Examples`.

## References

* [grove-white-2025]
* [degen-tonhauser-2021]
-/

@[expose] public section

open MeasureTheory Measure ProbabilityTheory ModalLogic unitInterval
open scoped ENNReal

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

section LexicalEntry

variable {Ω E : Type*}

/-- The lexical entry (13) of *know*, at a complement, a holder and an index: under either
reading the complement holds throughout the holder's epistemic alternatives at the index, and
under the factive reading it holds at the index as well. -/
def clauseEmbeddingSem (epi : E → SetRel Ω Ω) : FactivityReading → (Ω → Prop) → E → Ω → Prop
  | .factive, φ, x, i => □[epi x] φ i ∧ φ i
  | .nonfactive, φ, x, i => □[epi x] φ i

variable [MeasurableSpace Ω] (cg : Measure Ω) (epi : E → SetRel Ω Ω) (φ : Ω → Prop) (x : E)

/-- Updating the common ground with a reading conditions it on the reading's content. -/
noncomputable def update (r : FactivityReading) : Measure Ω :=
  cg[|{i | clauseEmbeddingSem epi r φ x i}]

instance (r : FactivityReading) : IsZeroOrProbabilityMeasure (update cg epi φ x r) := by
  unfold update; infer_instance

theorem update_factive :
    update cg epi φ x .factive = cg[|{i | □[epi x] φ i} ∩ {i | φ i}] := rfl

theorem update_nonfactive : update cg epi φ x .nonfactive = cg[|{i | □[epi x] φ i}] := rfl

variable {cg epi φ x} [IsProbabilityMeasure cg]

theorem likely_update_factive (hK : MeasurableSet {i | □[epi x] φ i})
    (hφ : MeasurableSet {i | φ i}) (h : cg {i | □[epi x] φ i ∧ φ i} ≠ 0) :
    likely (update cg epi φ x .factive) {i | φ i} = 1 := by
  have h' : cg ({i | □[epi x] φ i} ∩ {i | φ i}) ≠ 0 := h
  ext
  rw [coe_likely, measureReal_def, update_factive, cond_apply (hK.inter hφ),
    Set.inter_eq_left.2 Set.inter_subset_right, ENNReal.inv_mul_cancel h' (measure_ne_top _ _)]
  rfl

/-- Under the non-factive reading the complement keeps its probability, when the common ground
makes it independent of what the holder knows. -/
theorem likely_update_nonfactive (hK : MeasurableSet {i | □[epi x] φ i})
    (hind : IndepSet {i | □[epi x] φ i} {i | φ i} cg) (h : cg {i | □[epi x] φ i} ≠ 0) :
    likely (update cg epi φ x .nonfactive) {i | φ i} = likely cg {i | φ i} := by
  ext
  rw [coe_likely, coe_likely, measureReal_def, measureReal_def, update_nonfactive, cond_apply hK,
    hind.measure_inter_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel h (measure_ne_top _ _), one_mul]

end LexicalEntry

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

section Derivation

variable {Ω E : Type*} [MeasurableSpace Ω] {cg : Measure Ω} [IsProbabilityMeasure cg]
  {epi : E → SetRel Ω Ω} {φ : Ω → Prop} {x : E} (τ : I)

open Classical in
/-- The answer at an index under discrete world knowledge is the complement's truth value. -/
noncomputable def complementValue (φ : Ω → Prop) (i : Ω) : I := if φ i then 1 else 0

/-- The norming-discrete model is the distribution of the complement's truth value at an index
drawn from the common ground. -/
theorem map_complementValue (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hφ : MeasurableSet {i | φ i}) :
    μ.map (complementValue φ) = normingDiscrete (likely μ {i | φ i}) := by
  classical
  have hcv : Measurable (complementValue φ) := Measurable.ite hφ measurable_const measurable_const
  have h1 : (toNNReal (likely μ {i | φ i}) : ℝ≥0∞) = μ {i | φ i} :=
    (ENNReal.toReal_eq_toReal_iff' ENNReal.coe_ne_top (measure_ne_top μ _)).1
      (by simp [measureReal_def])
  have h0 : (toNNReal (σ (likely μ {i | φ i})) : ℝ≥0∞) = μ {i | φ i}ᶜ :=
    (ENNReal.toReal_eq_toReal_iff' ENNReal.coe_ne_top (measure_ne_top μ _)).1
      (by simp [coe_symm_eq, ← measureReal_def, probReal_compl_eq_one_sub hφ])
  ext s hs
  rw [Measure.map_apply hcv hs, normingDiscrete, bernoulliMeasure_apply _ hs, h1, h0]
  have hpre : complementValue φ ⁻¹' s =
      (if (1 : I) ∈ s then {i | φ i} else ∅) ∪ (if (0 : I) ∈ s then {i | φ i}ᶜ else ∅) := by
    ext i
    by_cases hi : φ i <;> by_cases h1s : (1 : I) ∈ s <;> by_cases h0s : (0 : I) ∈ s <;>
      simp [complementValue, hi, h1s, h0s]
  rw [hpre]
  by_cases h1s : (1 : I) ∈ s <;> by_cases h0s : (0 : I) ∈ s <;>
    simp [h1s, h0s]

/-- The discrete-factivity model draws a reading of (13) and answers with the probability of
the complement under the common ground updated with it. -/
theorem discreteFactivity_eq_bind_update (hK : MeasurableSet {i | □[epi x] φ i})
    (hφ : MeasurableSet {i | φ i}) (hind : IndepSet {i | □[epi x] φ i} {i | φ i} cg)
    (h : cg {i | □[epi x] φ i ∧ φ i} ≠ 0) :
    discreteFactivity τ (likely cg {i | φ i}) = Ber(FactivityReading.factive, .nonfactive, τ).bind
      fun r ↦ dirac (likely (update cg epi φ x r) {i | φ i}) := by
  have hK0 : cg {i | □[epi x] φ i} ≠ 0 := fun h0 ↦ h (measure_mono_null (fun _ hi ↦ hi.1) h0)
  rw [discreteFactivity, resolvedFactivity]
  congr 1
  funext r
  cases r
  · rw [likely_update_factive hK hφ h]
  · rw [likely_update_nonfactive hK hind hK0]

/-- The wholly-discrete model draws a reading of (13) and answers with the complement's truth
at an index drawn from the common ground updated with it. -/
theorem whollyDiscrete_eq_bind_update (hK : MeasurableSet {i | □[epi x] φ i})
    (hφ : MeasurableSet {i | φ i}) (hind : IndepSet {i | □[epi x] φ i} {i | φ i} cg)
    (h : cg {i | □[epi x] φ i ∧ φ i} ≠ 0) :
    whollyDiscrete τ (likely cg {i | φ i}) = Ber(FactivityReading.factive, .nonfactive, τ).bind
      fun r ↦ (update cg epi φ x r).map (complementValue φ) := by
  have hK0 : cg {i | □[epi x] φ i} ≠ 0 := fun h0 ↦ h (measure_mono_null (fun _ hi ↦ hi.1) h0)
  rw [whollyDiscrete, resolvedFactivity]
  congr 1
  funext r
  cases r
  · have : IsProbabilityMeasure (update cg epi φ x .factive) := cond_isProbabilityMeasure h
    rw [map_complementValue _ hφ, likely_update_factive hK hφ h]
    simp [normingDiscrete]
  · have : IsProbabilityMeasure (update cg epi φ x .nonfactive) := cond_isProbabilityMeasure hK0
    rw [map_complementValue _ hφ, likely_update_nonfactive hK hind hK0]

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
