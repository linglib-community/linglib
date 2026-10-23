/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.InformationTheory.Entropy
public import Linglib.Core.MeasureTheory.MeasurableSpace.Constructions
public import Linglib.Processing.Surprisal.LossyContext

/-!
# Futrell, Gibson and Levy (2020): Lossy-Context Surprisal

Futrell, Gibson and Levy take the difficulty of a word to be its expected surprisal under a lossy
memory representation of its context (`LossyContext.MemoryProcess`). Their comprehender of
section 3.3 predicts the next word by Bayesian inversion of the memory kernel (`bayes`). Averaged
over contexts, its difficulty is the conditional entropy of the word given the representation,
and it exceeds the difficulty of the lossless comprehender of surprisal theory by exactly the
predictive information memory loses (`averageDifficulty_bayes_sub_lossless`).

Information locality (section 5) is proved for a single dependency under erasure noise
(`erasure`), where the paper's first-order approximation is exact. Difficulty is then the unigram
surprisal less the surviving fraction of the pointwise mutual information, so it grows with
distance when the words are positively associated and shrinks when they are negatively
associated (`locality`, `antilocality`).

## Implementation notes

* Pointwise mutual information is taken relative to the unigram distribution of the next word,
  the language model averaged over the context prior, and the erasure process reads an erased
  word as that prior.
* Structural forgetting (section 4) is a parameter-space simulation over toy grammars, with
  forgetting at low verb-final relative-clause rates as for English and none at the German
  rate; it stays in prose.

## References

* [futrell-gibson-levy-2020]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory LossyContext
open scoped ProbabilityTheory unitInterval

namespace FutrellGibsonLevy2020

variable {W : Type*} [MeasurableSpace W]

section AverageForm

/-! ### The Bayes-optimal comprehender and the average form -/

variable {C R : Type*} [MeasurableSpace C] [MeasurableSingletonClass C] [MeasurableSpace R]
  [MeasurableSingletonClass R] [MeasurableSingletonClass W]
  (L : Kernel C W) [IsMarkovKernel L] (π : Measure C) [IsProbabilityMeasure π]
  (mem : Kernel C R) [IsMarkovKernel mem]

/-- The joint law of the next word and its context under the language model `L` and the
context prior `π`. -/
noncomputable def joint : Measure (W × C) := (π ⊗ₘ L).map Prod.swap

instance : IsProbabilityMeasure (joint L π) := by
  unfold joint; infer_instance

/-- The joint law of the next word and the memory representation of its context. -/
noncomputable def memJoint : Measure (W × R) := (Kernel.id ∥ₖ mem) ∘ₘ joint L π

instance : IsProbabilityMeasure (memJoint L π mem) :=
  inferInstanceAs (IsProbabilityMeasure ((Kernel.id ∥ₖ mem) ∘ₘ joint L π))

theorem joint_real_singleton (w : W) (c : C) :
    (joint L π).real {(w, c)} = π.real {c} * (L c).real {w} := by
  rw [joint, map_measureReal_apply measurable_swap (.singleton _),
    show Prod.swap ⁻¹' {(w, c)} = {(c, w)} from by ext ⟨_, _⟩; simp [and_comm],
    Measure.compProd_real_singleton]

variable [Fintype C] [Fintype W]

theorem memJoint_real_singleton (w : W) (r : R) :
    (memJoint L π mem).real {(w, r)} = ∑ c, π.real {c} * (L c).real {w} * (mem c).real {r} := by
  simp_rw [memJoint, Measure.parallelComp_id_comp_real_singleton, joint_real_singleton]

theorem measureMutualInfo_memJoint_le [Fintype R] : Im[memJoint L π mem] ≤ Im[joint L π] :=
  measureMutualInfo_parallelComp_id_comp_le _ mem

theorem averageDifficulty_of_lossless {mp : MemoryProcess C R W} (h : mp.IsLosslessFor L) :
    mp.averageDifficulty L π = H[Prod.fst | Prod.snd ; joint L π] := by
  have hsnd (c : C) : (joint L π) (Prod.snd ⁻¹' {c}) = π {c} := by
    rw [← Measure.snd_apply (.singleton c), joint, Measure.snd_map_swap, Measure.fst_compProd]
  have hcond (c : C) (w : W) (hc : π.real {c} ≠ 0) :
      ((joint L π)[|Prod.snd ⁻¹' {c}]).real (Prod.fst ⁻¹' {w}) = (L c).real {w} := by
    rw [cond_real_apply _ (measurable_snd (.singleton c)), Set.inter_comm, ← Set.prod_eq,
      Set.singleton_prod_singleton, joint_real_singleton, measureReal_def _ (Prod.snd ⁻¹' {c}),
      hsnd, ← measureReal_def, mul_div_cancel_left₀ _ hc]
  rw [condEntropy_eq_sum_negLog _ measurable_fst measurable_snd, MemoryProcess.averageDifficulty]
  simp only [integral_fintype, Integrable.of_finite,
    MemoryProcess.expectedSurprisal_eq_surprisal_of_lossless h, smul_eq_mul, ← Set.prod_eq,
    Set.singleton_prod_singleton, joint_real_singleton, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ ↦ Finset.sum_congr rfl fun c _ ↦ ?_
  obtain hc | hc := eq_or_ne (π.real {c}) 0
  · simp [hc]
  · rw [hcond c w hc, surprisal]
    ring

variable [Fintype R]

/-- The Bayes-optimal comprehender pairs the memory kernel with the posterior predictive of the
next word given the representation. -/
noncomputable def bayes : MemoryProcess C R W where
  encode := mem
  predict := Kernel.ofFunOfCountable fun r ↦ ((memJoint L π mem)[|Prod.snd ⁻¹' {r}]).map Prod.fst

theorem averageDifficulty_bayes :
    (bayes L π mem).averageDifficulty L π = H[Prod.fst | Prod.snd ; memJoint L π mem] := by
  rw [condEntropy_eq_sum_negLog _ measurable_fst measurable_snd, MemoryProcess.averageDifficulty]
  simp only [integral_fintype, Integrable.of_finite, MemoryProcess.expectedSurprisal, bayes,
    ← Set.prod_eq, Set.singleton_prod_singleton, memJoint_real_singleton, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun c _ ↦ ?_
  simp only [MemoryProcess.perStateSurprisal, surprisal, Kernel.ofFunOfCountable,
    Kernel.coe_mk, map_measureReal_apply measurable_fst (.singleton _)]
  ring

theorem averageDifficulty_bayes_sub_lossless {mp : MemoryProcess C R W}
    (h : mp.IsLosslessFor L) : (bayes L π mem).averageDifficulty L π - mp.averageDifficulty L π
      = Im[joint L π] - Im[memJoint L π mem] := by
  have : Nonempty C := π.nonempty_of_neZero
  rw [averageDifficulty_bayes, averageDifficulty_of_lossless L π h, condEntropy_fst_snd,
    condEntropy_fst_snd, memJoint, Measure.fst_parallelComp_id_comp]
  ring

theorem averageDifficulty_lossless_le_bayes {mp : MemoryProcess C R W} (h : mp.IsLosslessFor L) :
    mp.averageDifficulty L π ≤ (bayes L π mem).averageDifficulty L π := by
  have := averageDifficulty_bayes_sub_lossless L π mem h
  have := measureMutualInfo_memJoint_le L π mem
  linarith

end AverageForm

section Erasure

/-! ### Erasure noise and information locality -/

variable (L : Kernel W W) (π : Measure W)

/-- The pointwise mutual information of the next word `w` with the context word `y`, relative to
the unigram distribution of the next word. -/
noncomputable def pmi (y w : W) : ℝ := Real.log ((L y).real {w} / (L ∘ₘ π).real {w})

theorem surprisal_eq_sub_pmi {y w : W} (h0 : (L ∘ₘ π).real {w} ≠ 0) (hy : (L y).real {w} ≠ 0) :
    surprisal (L y) w = surprisal (L ∘ₘ π) w - pmi L π y w := by
  unfold surprisal pmi
  rw [Real.log_div hy h0]
  ring

variable [MeasurableSingletonClass W] [Countable W]

/-- The erasure-noise memory process erases the context word with probability `e`, and its
predictor reads a retained word through the language model and an erased one as the unigram
distribution. -/
noncomputable def erasure (e : I) : MemoryProcess W (W ⊕ Unit) W where
  encode := Kernel.ofFunOfCountable fun y ↦ Ber(Sum.inr (), Sum.inl y, e)
  predict := Kernel.ofFunOfCountable (Sum.elim (⇑L) fun _ ↦ L ∘ₘ π)

variable {e e' : I} {y w : W}

theorem expectedSurprisal_erasure (h0 : (L ∘ₘ π).real {w} ≠ 0) (hy : (L y).real {w} ≠ 0) :
    (erasure L π e).expectedSurprisal y w
      = surprisal (L ∘ₘ π) w - (1 - (e : ℝ)) * pmi L π y w := by
  rw [MemoryProcess.expectedSurprisal_of_bernoulli (mp := erasure L π e) (c := y) rfl]
  show (e : ℝ) * surprisal (L ∘ₘ π) w + (1 - e) * surprisal (L y) w = _
  rw [surprisal_eq_sub_pmi L π h0 hy]
  ring

theorem expectedSurprisal_erasure_sub_surprisal (h0 : (L ∘ₘ π).real {w} ≠ 0)
    (hy : (L y).real {w} ≠ 0) :
    (erasure L π e).expectedSurprisal y w - surprisal (L y) w = (e : ℝ) * pmi L π y w := by
  rw [expectedSurprisal_erasure L π h0 hy, surprisal_eq_sub_pmi L π h0 hy]
  ring

/-- Under progressive noise, where a more distant context word has a larger erasure rate,
difficulty increases with distance when the words are positively associated. -/
theorem locality (h : e ≤ e') (hpmi : 0 ≤ pmi L π y w) (h0 : (L ∘ₘ π).real {w} ≠ 0)
    (hy : (L y).real {w} ≠ 0) :
    (erasure L π e).expectedSurprisal y w ≤ (erasure L π e').expectedSurprisal y w := by
  rw [expectedSurprisal_erasure L π h0 hy, expectedSurprisal_erasure L π h0 hy]
  have : (e : ℝ) ≤ e' := h
  nlinarith

theorem antilocality (h : e ≤ e') (hpmi : pmi L π y w ≤ 0) (h0 : (L ∘ₘ π).real {w} ≠ 0)
    (hy : (L y).real {w} ≠ 0) :
    (erasure L π e').expectedSurprisal y w ≤ (erasure L π e).expectedSurprisal y w := by
  rw [expectedSurprisal_erasure L π h0 hy, expectedSurprisal_erasure L π h0 hy]
  have : (e : ℝ) ≤ e' := h
  nlinarith

theorem erasure_zero_isLosslessFor : (erasure L π 0).IsLosslessFor L :=
  ⟨Sum.inl, measurable_inl,
    Kernel.ext fun _ ↦ (bernoulliMeasure_zero _ _).trans (Kernel.deterministic_apply _ _).symm,
    Kernel.ext fun _ ↦ rfl⟩

theorem erasure_zero : (erasure L π 0).expectedSurprisal y w = surprisal (L y) w :=
  MemoryProcess.expectedSurprisal_eq_surprisal_of_lossless (erasure_zero_isLosslessFor L π) y w

theorem erasure_one : (erasure L π 1).expectedSurprisal y w = surprisal (L ∘ₘ π) w :=
  MemoryProcess.expectedSurprisal_of_dirac (mp := erasure L π 1) (c := y)
    (bernoulliMeasure_one _ _) w

end Erasure

end FutrellGibsonLevy2020
