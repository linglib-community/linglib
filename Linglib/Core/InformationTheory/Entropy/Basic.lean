/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.InformationTheory.Entropy.Measure
public import Linglib.Core.Probability.ConditionalProbability
public import Mathlib.Probability.IdentDistrib

/-!
# Entropy of random variables

Random variables carry the quantities of a measure through their laws: the entropy `H[X ; μ]` and
mutual information `I[X : Y ; μ]`, and their expectations over the values of a third variable, the
conditional entropy `H[X | Y ; μ]` and conditional mutual information `I[X : Y | Z ; μ]`. On finite
types these obey the [chain rule](##entropy_pair_eq_add_condEntropy) and vanish, for mutual
information, exactly on [independent](##mutualInfo_eq_zero_iff) and
[conditionally independent](##condMutualInfo_eq_zero_iff) variables, so
[conditioning leaves entropy unchanged only under independence](##condEntropy_eq_entropy_iff).

## Implementation notes

`[UPSTREAM]` candidate: mathlib has no entropy of a random variable and no mutual information,
conditional or not.

## References

* [cover-thomas-2006], chapter 2.
* The PFR project, `PFR/ForMathlib/Entropy/Basic.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal ProbabilityTheory

namespace InformationTheory

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

section entropy

variable {Ω : Type*} [MeasurableSpace Ω] {X : Ω → S} {Y : Ω → T}

/-- The entropy of a random variable is the entropy of its law. -/
noncomputable def entropy (X : Ω → S) (μ : Measure Ω) : ℝ := Hm[μ.map X]

@[inherit_doc entropy] scoped notation3:max "H[" X " ; " μ "]" => entropy X μ

theorem entropy_def (X : Ω → S) (μ : Measure Ω) : H[X ; μ] = Hm[μ.map X] := rfl

theorem entropy_nonneg (X : Ω → S) (μ : Measure Ω) : 0 ≤ H[X ; μ] := measureEntropy_nonneg _

@[simp] theorem entropy_zero_measure (X : Ω → S) : H[X ; (0 : Measure Ω)] = 0 := by
  simp [entropy]

theorem entropy_le_log_card [Fintype S] [MeasurableSingletonClass S] (X : Ω → S)
    (μ : Measure Ω) : H[X ; μ] ≤ log (Fintype.card S) :=
  measureEntropy_le_log_card _

theorem entropy_eq_sum [Fintype S] [MeasurableSingletonClass S] (hX : Measurable X)
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] :
    H[X ; μ] = ∑ s, negMulLog (μ.real (X ⁻¹' {s})) := by
  rw [entropy, measureEntropy_eq_sum]
  simp_rw [map_measureReal_apply hX (.singleton _)]

/-- The entropy of a random variable valued in a finite set is a sum over that set. -/
theorem entropy_eq_sum_finset [MeasurableSingletonClass S] (hX : Measurable X) (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ] {A : Finset S} (hA : ∀ ω, X ω ∈ A) :
    H[X ; μ] = ∑ s ∈ A, negMulLog (μ.real (X ⁻¹' {s})) := by
  rw [entropy, measureEntropy_eq_sum_finset (A := A)]
  · simp_rw [map_measureReal_apply hX (.singleton _)]
  · rw [Measure.map_apply hX A.measurableSet.compl]
    convert measure_empty (μ := μ)
    ext ω
    simpa using hA ω

/-- A random variable with at most one value has no entropy. -/
theorem entropy_of_subsingleton [Fintype S] [MeasurableSingletonClass S] [Subsingleton S]
    (X : Ω → S) (μ : Measure Ω) : H[X ; μ] = 0 :=
  le_antisymm ((entropy_le_log_card X μ).trans <| log_nonpos (Nat.cast_nonneg _) <|
    Nat.cast_le_one.mpr (Fintype.card_le_one_iff_subsingleton.mpr ‹_›)) (entropy_nonneg X μ)

/-- A constant random variable has no entropy. -/
theorem entropy_const [MeasurableSingletonClass S] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : S) : H[fun _ ↦ x ; μ] = 0 := by
  rw [entropy_def, Measure.map_const, measure_univ, one_smul, measureEntropy_dirac]

/-- A random variable has zero entropy iff it is almost surely constant. -/
theorem entropy_eq_zero_iff [Fintype S] [MeasurableSingletonClass S] (hX : Measurable X)
    (μ : Measure Ω) [IsProbabilityMeasure μ] : H[X ; μ] = 0 ↔ ∃ x, ∀ᵐ ω ∂μ, X ω = x := by
  have : IsProbabilityMeasure (μ.map X) :=
    (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).2 ‹_›
  rw [entropy_def, measureEntropy_eq_zero_iff]
  refine exists_congr fun x ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h1 : μ (X ⁻¹' {x}) = 1 := by
      have := congrArg (· {x}) h
      simpa [Measure.map_apply hX (.singleton x), Measure.dirac_apply_of_mem] using this
    rw [ae_iff, show {ω | ¬ X ω = x} = (X ⁻¹' {x})ᶜ from rfl,
      prob_compl_eq_zero_iff (hX (.singleton x))]
    exact h1
  · rw [Measure.map_congr (h.mono fun ω hω ↦ hω : X =ᵐ[μ] fun _ ↦ x), Measure.map_const,
      measure_univ, one_smul]

/-- Entropy is invariant under an injective recoding of the values. -/
theorem entropy_comp_of_injective [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    (μ : Measure Ω) (hX : Measurable X) {f : S → T} (hf : Measurable f) (hinj : f.Injective) :
    H[f ∘ X ; μ] = H[X ; μ] := by
  rw [entropy_def, ← Measure.map_map hf hX, measureEntropy_map_of_injective hf hinj, entropy_def]

theorem entropy_comm [MeasurableSingletonClass S] [MeasurableSingletonClass T] (μ : Measure Ω)
    (hX : Measurable X) (hY : Measurable Y) :
    H[fun ω ↦ (X ω, Y ω) ; μ] = H[fun ω ↦ (Y ω, X ω) ; μ] :=
  (entropy_comp_of_injective μ (hX.prodMk hY) measurable_swap Prod.swap_injective).symm

theorem _root_.ProbabilityTheory.IdentDistrib.entropy_eq {Ω' : Type*} [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} {X' : Ω' → S} (h : IdentDistrib X X' μ ν) :
    H[X ; μ] = H[X' ; ν] := by
  rw [entropy_def, entropy_def, h.map_eq]

/-- The conditional entropy of `X` given `Y` is the expectation, under the law of `Y`, of the
entropy of `X` conditioned on `Y = y`. -/
noncomputable def condEntropy (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) : ℝ :=
  ∫ y, H[X ; μ[|Y ⁻¹' {y}]] ∂(μ.map Y)

@[inherit_doc condEntropy]
scoped notation3:max "H[" X " | " Y " ; " μ "]" => condEntropy X Y μ

theorem condEntropy_nonneg (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) : 0 ≤ H[X | Y ; μ] :=
  integral_nonneg fun _ ↦ entropy_nonneg _ _

theorem condEntropy_eq_sum [Fintype T] [MeasurableSingletonClass T] (X : Ω → S)
    (hY : Measurable Y) (μ : Measure Ω) [IsFiniteMeasure μ] :
    H[X | Y ; μ] = ∑ y, μ.real (Y ⁻¹' {y}) * H[X ; μ[|Y ⁻¹' {y}]] := by
  rw [condEntropy, integral_fintype .of_finite]
  simp_rw [smul_eq_mul, map_measureReal_apply hY (.singleton _)]

/-- Recoding `X` injectively leaves its entropy given `Y` unchanged. -/
theorem condEntropy_comp_of_injective [MeasurableSingletonClass S] {U : Type*} [MeasurableSpace U]
    [MeasurableSingletonClass U] (Y : Ω → T) (μ : Measure Ω) (hX : Measurable X) {f : S → U}
    (hf : Measurable f) (hinj : f.Injective) : H[f ∘ X | Y ; μ] = H[X | Y ; μ] := by
  simp only [condEntropy, entropy_comp_of_injective _ hX hf hinj]

/-- Recoding `Y` by a measurable embedding leaves the entropy of `X` given `Y` unchanged. -/
theorem condEntropy_comp_right_of_measurableEmbedding {U : Type*} [MeasurableSpace U]
    (X : Ω → S) (μ : Measure Ω) (hY : Measurable Y) {g : T → U} (hg : MeasurableEmbedding g) :
    H[X | g ∘ Y ; μ] = H[X | Y ; μ] := by
  rw [condEntropy, ← Measure.map_map hg.measurable hY, hg.integral_map, condEntropy]
  congr with y
  rw [Set.preimage_comp, ← Set.image_singleton, hg.injective.preimage_image]

/-- Mutual information of two random variables. -/
noncomputable def mutualInfo (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) : ℝ :=
  H[X ; μ] + H[Y ; μ] - H[fun ω ↦ (X ω, Y ω) ; μ]

@[inherit_doc mutualInfo]
scoped notation3:max "I[" X " : " Y " ; " μ "]" => mutualInfo X Y μ

theorem mutualInfo_def (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
    I[X : Y ; μ] = H[X ; μ] + H[Y ; μ] - H[fun ω ↦ (X ω, Y ω) ; μ] := rfl

/-- The mutual information of two random variables is that of their joint law. -/
theorem mutualInfo_eq_measureMutualInfo (hX : Measurable X) (hY : Measurable Y)
    (μ : Measure Ω) : I[X : Y ; μ] = Im[μ.map fun ω ↦ (X ω, Y ω)] := by
  rw [mutualInfo, measureMutualInfo, Measure.fst_map_prodMk hX hY, Measure.snd_map_prodMk hX hY]
  rfl

/-- Mutual information is symmetric. -/
theorem mutualInfo_comm [MeasurableSingletonClass S] [MeasurableSingletonClass T] (μ : Measure Ω)
    (hX : Measurable X) (hY : Measurable Y) : I[X : Y ; μ] = I[Y : X ; μ] := by
  rw [mutualInfo_def, mutualInfo_def, entropy_comm μ hX hY]
  ring

/-- The conditional mutual information of `X` and `Y` given `Z` is the expectation, under the law of
`Z`, of the mutual information of `X` and `Y` conditioned on `Z = z`. -/
noncomputable def condMutualInfo {U : Type*} [MeasurableSpace U] (X : Ω → S) (Y : Ω → T)
    (Z : Ω → U) (μ : Measure Ω) : ℝ :=
  ∫ z, I[X : Y ; μ[|Z ⁻¹' {z}]] ∂(μ.map Z)

@[inherit_doc condMutualInfo]
scoped notation3:max "I[" X " : " Y " | " Z " ; " μ "]" => condMutualInfo X Y Z μ

variable [Fintype S] [Fintype T] [MeasurableSingletonClass S] [MeasurableSingletonClass T]
  (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem mutualInfo_nonneg (hX : Measurable X) (hY : Measurable Y) : 0 ≤ I[X : Y ; μ] := by
  have := (Measure.isProbabilityMeasure_map_iff (hX.prodMk hY).aemeasurable).2 ‹_›
  rw [mutualInfo_eq_measureMutualInfo hX hY]
  exact measureMutualInfo_nonneg _

/-- **Chain rule.** The entropy of a pair is `H[X, Y] = H[Y] + H[X | Y]`. -/
theorem entropy_pair_eq_add_condEntropy (hX : Measurable X) (hY : Measurable Y) :
    H[fun ω ↦ (X ω, Y ω) ; μ] = H[Y ; μ] + H[X | Y ; μ] := by
  have hfib (x : S) (y : T) :
      Y ⁻¹' {y} ∩ X ⁻¹' {x} = (fun ω ↦ (X ω, Y ω)) ⁻¹' {(x, y)} := by
    ext ω; simp [and_comm]
  have hcond (x : S) (y : T) : (μ[|Y ⁻¹' {y}]).real (X ⁻¹' {x})
      = μ.real ((fun ω ↦ (X ω, Y ω)) ⁻¹' {(x, y)}) / μ.real (Y ⁻¹' {y}) := by
    rw [measureReal_def, cond_apply (hY (.singleton y)), ENNReal.toReal_mul,
      ENNReal.toReal_inv, hfib, div_eq_inv_mul]
    rfl
  have hsum (y : T) :
      ∑ x, μ.real ((fun ω ↦ (X ω, Y ω)) ⁻¹' {(x, y)}) = μ.real (Y ⁻¹' {y}) := by
    simp_rw [← map_measureReal_apply (hX.prodMk hY) (.singleton _),
      ← Measure.snd_real_singleton_eq_sum, Measure.snd_map_prodMk hX hY,
      map_measureReal_apply hY (.singleton _)]
  have key (y : T) : μ.real (Y ⁻¹' {y}) * H[X ; μ[|Y ⁻¹' {y}]]
      = ∑ x, negMulLog (μ.real ((fun ω ↦ (X ω, Y ω)) ⁻¹' {(x, y)}))
        - negMulLog (μ.real (Y ⁻¹' {y})) := by
    obtain hy | hy := eq_or_ne (μ (Y ⁻¹' {y})) 0
    · have h0 (x : S) : μ ((fun ω ↦ (X ω, Y ω)) ⁻¹' {(x, y)}) = 0 :=
        measure_mono_null (hfib x y ▸ Set.inter_subset_left) hy
      simp [cond_eq_zero_of_meas_eq_zero hy, measureReal_def, hy, h0]
    · have := cond_isProbabilityMeasure (μ := μ) hy
      have hq : μ.real (Y ⁻¹' {y}) ≠ 0 :=
        (measureReal_eq_zero_iff (measure_ne_top _ _)).not.mpr hy
      have h (x : S) : μ.real (Y ⁻¹' {y})
            * negMulLog (μ.real ((fun ω ↦ (X ω, Y ω)) ⁻¹' {(x, y)}) / μ.real (Y ⁻¹' {y}))
          = negMulLog (μ.real ((fun ω ↦ (X ω, Y ω)) ⁻¹' {(x, y)}))
            - μ.real ((fun ω ↦ (X ω, Y ω)) ⁻¹' {(x, y)}) / μ.real (Y ⁻¹' {y})
              * negMulLog (μ.real (Y ⁻¹' {y})) := by
        rw [eq_sub_iff_add_eq, add_comm, ← negMulLog_mul]
        congr 1
        field_simp
      rw [entropy_eq_sum hX, Finset.mul_sum]
      simp_rw [hcond, h, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_div, hsum,
        div_self hq, one_mul]
  rw [entropy_eq_sum (hX.prodMk hY), entropy_eq_sum hY, condEntropy_eq_sum X hY]
  simp_rw [key, Finset.sum_sub_distrib, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  ring

theorem mutualInfo_eq_entropy_sub_condEntropy (hX : Measurable X) (hY : Measurable Y) :
    I[X : Y ; μ] = H[X ; μ] - H[X | Y ; μ] := by
  rw [mutualInfo, entropy_pair_eq_add_condEntropy μ hX hY]
  ring

/-- Conditioning reduces entropy, `H[X | Y] ≤ H[X]`. -/
theorem condEntropy_le_entropy (hX : Measurable X) (hY : Measurable Y) :
    H[X | Y ; μ] ≤ H[X ; μ] :=
  sub_nonneg.mp (mutualInfo_eq_entropy_sub_condEntropy μ hX hY ▸ mutualInfo_nonneg μ hX hY)

/-- On finite types, mutual information is the expected logarithm of the ratio of the joint mass to
the product of the marginal masses. -/
theorem mutualInfo_eq_sum_log (hX : Measurable X) (hY : Measurable Y) :
    I[X : Y ; μ] = ∑ x, ∑ y, μ.real (X ⁻¹' {x} ∩ Y ⁻¹' {y}) *
      log (μ.real (X ⁻¹' {x} ∩ Y ⁻¹' {y}) / (μ.real (X ⁻¹' {x}) * μ.real (Y ⁻¹' {y}))) := by
  have := (Measure.isProbabilityMeasure_map_iff (hX.prodMk hY).aemeasurable).2 ‹_›
  have hj (x : S) (y : T) : (μ.map fun ω ↦ (X ω, Y ω)).real {(x, y)}
      = μ.real (X ⁻¹' {x} ∩ Y ⁻¹' {y}) := by
    rw [map_measureReal_apply (hX.prodMk hY) (.singleton _)]
    congr 1
    ext ω
    simp
  rw [mutualInfo_eq_measureMutualInfo hX hY, measureMutualInfo_eq_toReal_klDiv,
    toReal_klDiv_eq_sum_log_div (Measure.absolutelyContinuous_fst_prod_snd _),
    Fintype.sum_prod_type]
  simp_rw [hj, Measure.prod_real_singleton, Measure.fst_map_prodMk hX hY,
    Measure.snd_map_prodMk hX hY, map_measureReal_apply hX (.singleton _),
    map_measureReal_apply hY (.singleton _)]

/-- Mutual information vanishes exactly on independent random variables. -/
theorem mutualInfo_eq_zero_iff (hX : Measurable X) (hY : Measurable Y) :
    I[X : Y ; μ] = 0 ↔ X ⟂ᵢ[μ] Y := by
  rw [mutualInfo_eq_measureMutualInfo hX hY, measureMutualInfo_eq_toReal_klDiv,
    ENNReal.toReal_eq_zero_iff, or_iff_left (klDiv_ne_top_iff.mpr
      ⟨(μ.map fun ω ↦ (X ω, Y ω)).absolutelyContinuous_fst_prod_snd, .of_finite⟩),
    klDiv_eq_zero_iff, Measure.fst_map_prodMk hX hY, Measure.snd_map_prodMk hX hY,
    indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable]

variable {μ} in
/-- The entropy of a pair of independent random variables is the sum of their entropies. -/
theorem _root_.ProbabilityTheory.IndepFun.entropy_pair_eq_add (h : X ⟂ᵢ[μ] Y)
    (hX : Measurable X) (hY : Measurable Y) :
    H[fun ω ↦ (X ω, Y ω) ; μ] = H[X ; μ] + H[Y ; μ] := by
  have := (mutualInfo_eq_zero_iff μ hX hY).mpr h
  rw [mutualInfo_def] at this
  linarith

/-- Conditioning leaves the entropy of `X` unchanged exactly when `Y` is independent of `X`. -/
theorem condEntropy_eq_entropy_iff (hX : Measurable X) (hY : Measurable Y) :
    H[X | Y ; μ] = H[X ; μ] ↔ X ⟂ᵢ[μ] Y := by
  rw [← mutualInfo_eq_zero_iff μ hX hY, mutualInfo_eq_entropy_sub_condEntropy μ hX hY, sub_eq_zero,
    eq_comm]

variable {μ} in
theorem _root_.ProbabilityTheory.IndepFun.condEntropy_eq_entropy (h : X ⟂ᵢ[μ] Y)
    (hX : Measurable X) (hY : Measurable Y) : H[X | Y ; μ] = H[X ; μ] :=
  (condEntropy_eq_entropy_iff μ hX hY).2 h

/-- Conditioning also on a random variable independent of the pair `(X, Y)` leaves the entropy
of `X` given `Y` unchanged. -/
theorem condEntropy_prod_eq_of_indepFun {U : Type*} [MeasurableSpace U] [Fintype U]
    [MeasurableSingletonClass U] {Z : Ω → U} (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (h : (fun ω ↦ (X ω, Y ω)) ⟂ᵢ[μ] Z) :
    H[X | fun ω ↦ (Y ω, Z ω) ; μ] = H[X | Y ; μ] := by
  have e : H[fun ω ↦ ((X ω, Y ω), Z ω) ; μ] = H[fun ω ↦ (X ω, Y ω, Z ω) ; μ] :=
    entropy_comp_of_injective μ (hX.prodMk (hY.prodMk hZ)) (f := (Equiv.prodAssoc S T U).symm)
      (measurable_of_finite _) (Equiv.prodAssoc S T U).symm.injective
  have hYZ : Y ⟂ᵢ[μ] Z := h.comp measurable_snd measurable_id
  linarith [entropy_pair_eq_add_condEntropy μ hX (hY.prodMk hZ),
    entropy_pair_eq_add_condEntropy μ hX hY,
    h.entropy_pair_eq_add (hX.prodMk hY) hZ, hYZ.entropy_pair_eq_add hY hZ]

section condMutualInfo

variable {U : Type*} [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U] {Z : Ω → U}

omit [Fintype S] [Fintype T] [MeasurableSingletonClass S] [MeasurableSingletonClass T] in
theorem condMutualInfo_eq_sum (X : Ω → S) (Y : Ω → T) (hZ : Measurable Z) :
    I[X : Y | Z ; μ] = ∑ z, μ.real (Z ⁻¹' {z}) * I[X : Y ; μ[|Z ⁻¹' {z}]] := by
  rw [condMutualInfo, integral_fintype .of_finite]
  simp_rw [smul_eq_mul, map_measureReal_apply hZ (.singleton _)]

omit [Fintype S] [Fintype T] [MeasurableSingletonClass S] [MeasurableSingletonClass T] in
theorem condMutualInfo_eq_condEntropy_add_sub (X : Ω → S) (Y : Ω → T) (hZ : Measurable Z) :
    I[X : Y | Z ; μ] = H[X | Z ; μ] + H[Y | Z ; μ] - H[fun ω ↦ (X ω, Y ω) | Z ; μ] := by
  simp_rw [condMutualInfo_eq_sum μ X Y hZ, condEntropy_eq_sum _ hZ, mutualInfo_def, mul_sub,
    mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]

theorem condMutualInfo_eq_condEntropy_sub_condEntropy (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) : I[X : Y | Z ; μ] = H[X | Z ; μ] - H[X | fun ω ↦ (Y ω, Z ω) ; μ] := by
  have e : H[fun ω ↦ ((X ω, Y ω), Z ω) ; μ] = H[fun ω ↦ (X ω, Y ω, Z ω) ; μ] :=
    entropy_comp_of_injective μ (hX.prodMk (hY.prodMk hZ)) (f := (Equiv.prodAssoc S T U).symm)
      (measurable_of_finite _) (Equiv.prodAssoc S T U).symm.injective
  linarith [condMutualInfo_eq_condEntropy_add_sub μ X Y hZ,
    entropy_pair_eq_add_condEntropy μ hX (hY.prodMk hZ),
    entropy_pair_eq_add_condEntropy μ (hX.prodMk hY) hZ, entropy_pair_eq_add_condEntropy μ hY hZ]

omit [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U] in
theorem condMutualInfo_nonneg [MeasurableSpace U] (hX : Measurable X) (hY : Measurable Y) :
    0 ≤ I[X : Y | Z ; μ] :=
  integral_nonneg fun z ↦ by
    obtain hz | hz := eq_or_ne (μ (Z ⁻¹' {z})) 0
    · simp [cond_eq_zero_of_meas_eq_zero hz, mutualInfo_def]
    · have := cond_isProbabilityMeasure (μ := μ) hz
      exact mutualInfo_nonneg _ hX hY

/-- Conditional mutual information vanishes exactly when `X` and `Y` are independent given each
value of `Z`. -/
theorem condMutualInfo_eq_zero_iff (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    I[X : Y | Z ; μ] = 0 ↔ ∀ z, X ⟂ᵢ[μ[|Z ⁻¹' {z}]] Y := by
  have hfib (z : U) : 0 ≤ μ.real (Z ⁻¹' {z}) * I[X : Y ; μ[|Z ⁻¹' {z}]] ∧
      (μ.real (Z ⁻¹' {z}) * I[X : Y ; μ[|Z ⁻¹' {z}]] = 0 ↔ X ⟂ᵢ[μ[|Z ⁻¹' {z}]] Y) := by
    obtain hz | hz := eq_or_ne (μ (Z ⁻¹' {z})) 0
    · rw [cond_eq_zero_of_meas_eq_zero hz]
      exact ⟨by simp [measureReal_def, hz], by simp [measureReal_def, hz,
        indepFun_iff_measure_inter_preimage_eq_mul]⟩
    · have := cond_isProbabilityMeasure (μ := μ) hz
      exact ⟨mul_nonneg measureReal_nonneg (mutualInfo_nonneg _ hX hY), by
        rw [mul_eq_zero, or_iff_right ((measureReal_eq_zero_iff (measure_ne_top _ _)).not.2 hz),
          mutualInfo_eq_zero_iff _ hX hY]⟩
  rw [condMutualInfo_eq_sum μ X Y hZ, Finset.sum_eq_zero_iff_of_nonneg fun z _ ↦ (hfib z).1]
  simp only [Finset.mem_univ, forall_const, (hfib _).2]

/-- On finite types, conditional mutual information is the expected logarithm of the ratio of the
conditional joint mass to the product of the conditional marginal masses. -/
theorem condMutualInfo_eq_sum_log (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    I[X : Y | Z ; μ] = ∑ x, ∑ y, ∑ z, μ.real (X ⁻¹' {x} ∩ Y ⁻¹' {y} ∩ Z ⁻¹' {z}) *
      log ((μ[|Z ⁻¹' {z}]).real (X ⁻¹' {x} ∩ Y ⁻¹' {y}) /
        ((μ[|Z ⁻¹' {z}]).real (X ⁻¹' {x}) * (μ[|Z ⁻¹' {z}]).real (Y ⁻¹' {y}))) := by
  have hw (z : U) (A : Set Ω) :
      μ.real (Z ⁻¹' {z}) * (μ[|Z ⁻¹' {z}]).real A = μ.real (A ∩ Z ⁻¹' {z}) := by
    obtain hq | hq := eq_or_ne (μ.real (Z ⁻¹' {z})) 0
    · rw [hq, zero_mul, measureReal_mono_null Set.inter_subset_right hq (measure_ne_top _ _)]
    · rw [cond_real_apply μ (hZ (.singleton z)), Set.inter_comm]
      field_simp
  have hz (z : U) : μ.real (Z ⁻¹' {z}) * I[X : Y ; μ[|Z ⁻¹' {z}]] =
      ∑ x, ∑ y, μ.real (X ⁻¹' {x} ∩ Y ⁻¹' {y} ∩ Z ⁻¹' {z}) *
        log ((μ[|Z ⁻¹' {z}]).real (X ⁻¹' {x} ∩ Y ⁻¹' {y}) /
          ((μ[|Z ⁻¹' {z}]).real (X ⁻¹' {x}) * (μ[|Z ⁻¹' {z}]).real (Y ⁻¹' {y}))) := by
    simp_rw [← hw z, mul_assoc, ← Finset.mul_sum]
    obtain hq | hq := eq_or_ne (μ (Z ⁻¹' {z})) 0
    · simp [measureReal_def, hq]
    · have := cond_isProbabilityMeasure (μ := μ) hq
      rw [mutualInfo_eq_sum_log _ hX hY]
  rw [condMutualInfo_eq_sum μ X Y hZ]
  simp_rw [hz]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ ↦ Finset.sum_comm

end condMutualInfo

section comp

variable {U : Type*} [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U]

/-- Conditioning on a function of `Y` leaves at least the entropy that conditioning on `Y`
leaves. -/
theorem condEntropy_le_condEntropy_comp (hX : Measurable X) (hY : Measurable Y) (f : T → U) :
    H[X | Y ; μ] ≤ H[X | f ∘ Y ; μ] := by
  have he : MeasurableEmbedding fun y ↦ (y, f y) :=
    ⟨fun _ _ h ↦ (Prod.mk.inj h).1, measurable_of_finite _,
      fun _ _ ↦ (Set.toFinite _).measurableSet⟩
  have h := condMutualInfo_nonneg (Z := f ∘ Y) μ hX hY
  rw [condMutualInfo_eq_condEntropy_sub_condEntropy μ hX hY ((measurable_of_finite f).comp hY),
    show (fun ω ↦ (Y ω, (f ∘ Y) ω)) = (fun y ↦ (y, f y)) ∘ Y from rfl,
    condEntropy_comp_right_of_measurableEmbedding X μ hY he] at h
  linarith

/-- Recoding `X` injectively, in a way that may depend on `Y`, leaves the entropy of `X` given
`Y` unchanged. -/
theorem condEntropy_of_injective (hX : Measurable X) (hY : Measurable Y) (f : T → S → U)
    (hf : ∀ t, (f t).Injective) : H[fun ω ↦ f (Y ω) (X ω) | Y ; μ] = H[X | Y ; μ] := by
  have hfXY : Measurable fun ω ↦ f (Y ω) (X ω) :=
    (measurable_of_finite (Function.uncurry f)).comp (hY.prodMk hX)
  have he : (fun p : S × T ↦ (f p.2 p.1, p.2)).Injective := fun p q h ↦ by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (hf p.2 (h.2 ▸ h.1)) h.2
  have h := entropy_pair_eq_add_condEntropy μ hfXY hY
  rw [show (fun ω ↦ (f (Y ω) (X ω), Y ω)) = (fun p : S × T ↦ (f p.2 p.1, p.2)) ∘
    fun ω ↦ (X ω, Y ω) from rfl, entropy_comp_of_injective μ (hX.prodMk hY)
      (measurable_of_finite _) he, entropy_pair_eq_add_condEntropy μ hX hY] at h
  linarith

/-- A function of `Y` has no entropy given `Y`. -/
theorem condEntropy_comp_self (hY : Measurable Y) (f : T → U) : H[f ∘ Y | Y ; μ] = 0 := by
  have h := entropy_pair_eq_add_condEntropy μ ((measurable_of_finite f).comp hY) hY
  rw [show (fun ω ↦ ((f ∘ Y) ω, Y ω)) = (fun t ↦ (f t, t)) ∘ Y from rfl,
    entropy_comp_of_injective μ hY (measurable_of_finite _) fun _ _ h ↦ (Prod.mk.inj h).2] at h
  linarith

/-- A function of a random variable has at most its entropy. -/
theorem entropy_comp_le (hX : Measurable X) (f : S → U) : H[f ∘ X ; μ] ≤ H[X ; μ] := by
  have hf : Measurable (f ∘ X) := (measurable_of_finite f).comp hX
  have h₁ := entropy_pair_eq_add_condEntropy μ hf hX
  have h₂ := entropy_pair_eq_add_condEntropy μ hX hf
  have h₃ := condEntropy_comp_self μ hX f
  have h₄ := entropy_comm μ hf hX
  have h₅ := condEntropy_nonneg X (f ∘ X) μ
  linarith

/-- A random variable has at most the entropy of its sample-space measure. -/
theorem entropy_le_measureEntropy [Fintype Ω] [MeasurableSingletonClass Ω] (X : Ω → S) :
    H[X ; μ] ≤ Hm[μ] := by
  have h := entropy_comp_le (X := id) μ measurable_id X
  rwa [Function.comp_id, entropy_def id μ, Measure.map_id] at h

end comp

variable {μ} in
/-- Conditional entropy is determined by the joint law. -/
theorem _root_.ProbabilityTheory.IdentDistrib.condEntropy_eq {Ω' : Type*} [MeasurableSpace Ω']
    {ν : Measure Ω'} [IsProbabilityMeasure ν] {X' : Ω' → S} {Y' : Ω' → T} (hX : Measurable X)
    (hY : Measurable Y) (hX' : Measurable X') (hY' : Measurable Y')
    (h : IdentDistrib (fun ω ↦ (X ω, Y ω)) (fun ω ↦ (X' ω, Y' ω)) μ ν) :
    H[X | Y ; μ] = H[X' | Y' ; ν] := by
  have hY : H[Y ; μ] = H[Y' ; ν] := (h.comp measurable_snd).entropy_eq
  linarith [entropy_pair_eq_add_condEntropy μ hX ‹_›, entropy_pair_eq_add_condEntropy ν hX' hY',
    h.entropy_eq]

/-- On finite types, conditional entropy vanishes exactly when `X` is almost surely a function
of `Y`. -/
theorem condEntropy_eq_zero_iff [Nonempty S] (hX : Measurable X) (hY : Measurable Y) :
    H[X | Y ; μ] = 0 ↔ ∃ f : T → S, ∀ᵐ ω ∂μ, X ω = f (Y ω) := by
  classical
  refine ⟨fun h ↦ ?_, fun ⟨f, hf⟩ ↦ ?_⟩
  · rw [condEntropy_eq_sum X hY μ] at h
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun y _ ↦
      mul_nonneg measureReal_nonneg (entropy_nonneg _ _)).1 h
    have key : ∀ y : T, μ (Y ⁻¹' {y}) ≠ 0 → ∃ x : S, ∀ᵐ ω ∂μ[|Y ⁻¹' {y}], X ω = x := by
      intro y hy
      have : IsProbabilityMeasure (μ[|Y ⁻¹' {y}]) := cond_isProbabilityMeasure hy
      refine (entropy_eq_zero_iff hX _).1 ?_
      rcases mul_eq_zero.1 (hzero y (Finset.mem_univ y)) with h0 | h0
      · exact absurd ((measureReal_eq_zero_iff (measure_ne_top _ _)).1 h0) hy
      · exact h0
    choose g hg using key
    refine ⟨fun y ↦ if hy : μ (Y ⁻¹' {y}) ≠ 0 then g y hy else Classical.arbitrary S, ?_⟩
    rw [ae_iff]
    refine measure_mono_null (fun ω hω ↦ ?_)
      (measure_iUnion_null fun y : T ↦ ?_ :
        μ (⋃ y : T, Y ⁻¹' {y} ∩ {ω | X ω ≠
          if hy : μ (Y ⁻¹' {y}) ≠ 0 then g y hy else Classical.arbitrary S}) = 0)
    · exact Set.mem_iUnion.2 ⟨Y ω, rfl, hω⟩
    · rcases eq_or_ne (μ (Y ⁻¹' {y})) 0 with hy | hy
      · exact measure_mono_null Set.inter_subset_left hy
      · have hae := hg y hy
        rw [ae_iff, cond_apply (hY (.singleton y))] at hae
        rcases mul_eq_zero.1 hae with h0 | h0
        · exact absurd (ENNReal.inv_eq_zero.1 h0) (measure_ne_top _ _)
        · simpa [dite_eq_left hy] using h0
  · have hfY : Measurable fun ω ↦ f (Y ω) := (measurable_of_finite f).comp hY
    have hpair : (fun ω ↦ (X ω, Y ω)) =ᵐ[μ] fun ω ↦ (f (Y ω), Y ω) :=
      hf.mono fun ω hω ↦ by simp [hω]
    have hid : IdentDistrib (fun ω ↦ (X ω, Y ω)) (fun ω ↦ (f (Y ω), Y ω)) μ μ :=
      ⟨(hX.prodMk hY).aemeasurable, (hfY.prodMk hY).aemeasurable, Measure.map_congr hpair⟩
    rw [hid.condEntropy_eq hX hY hfY hY]
    exact condEntropy_comp_self μ hY f

/-- On a joint law, the conditional entropy of the first coordinate given the second is the
entropy of the first marginal less the mutual information. -/
theorem condEntropy_fst_snd (ρ : Measure (S × T)) [IsProbabilityMeasure ρ] :
    H[Prod.fst | Prod.snd ; ρ] = Hm[ρ.fst] - Im[ρ] := by
  have h := mutualInfo_eq_entropy_sub_condEntropy ρ measurable_fst measurable_snd
  rw [mutualInfo_eq_measureMutualInfo measurable_fst measurable_snd,
    show (fun p : S × T ↦ (p.1, p.2)) = id from rfl, Measure.map_id] at h
  show _ = H[Prod.fst ; ρ] - Im[ρ]
  linarith

/-- Mutual information is at most the entropy of the second marginal. -/
theorem measureMutualInfo_le_measureEntropy_snd (ρ : Measure (S × T)) [IsProbabilityMeasure ρ] :
    Im[ρ] ≤ Hm[ρ.snd] := by
  have h := mutualInfo_eq_entropy_sub_condEntropy ρ measurable_snd measurable_fst
  rw [mutualInfo_comm ρ measurable_snd measurable_fst,
    mutualInfo_eq_measureMutualInfo measurable_fst measurable_snd,
    show (fun p : S × T ↦ (p.1, p.2)) = id from rfl, Measure.map_id] at h
  rw [h]
  exact sub_le_self _ (condEntropy_nonneg _ _ _)

end entropy

end InformationTheory
