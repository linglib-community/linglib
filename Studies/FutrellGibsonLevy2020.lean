/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.InformationTheory.Entropy.Basic
public import Linglib.Core.InformationTheory.Entropy.Surprisal
public import Linglib.Core.MeasureTheory.MeasurableSpace.Constructions
public import Linglib.Core.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Futrell, Gibson and Levy (2020): Lossy-Context Surprisal

Futrell, Gibson and Levy take the difficulty of a word to be its expected surprisal under a lossy
memory representation of its context. A memory process (`MemoryProcess`) encodes a context as a
distribution over memory representations and predicts the next word from the representation
alone. A process whose encoder is deterministic and whose predictor, read through the encoder, is
the language model has the surprisal of the language model: surprisal theory is the lossless
special case (`MemoryProcess.expectedSurprisal_eq_surprisal_of_lossless`).

Their comprehender of section 3.3 predicts the next word by Bayesian inversion of the memory
kernel (`bayes`). Given the encoder, any other predictor's average difficulty exceeds its own by
the expected divergence of the Bayesian prediction from the other one
(`averageDifficulty_eq_bayes_add`), so among predictors that are Markov kernels the Bayesian one is
the unique one of least average difficulty, up to representations of probability zero
(`averageDifficulty_bayes_eq_iff`). Averaged over contexts, its difficulty is the conditional
entropy of the word given the representation (`averageDifficulty_bayes`). A lossless process has
the conditional entropy of the word given the context (`averageDifficulty_of_lossless`), and the
Bayesian comprehender exceeds it by exactly the predictive information memory loses
(`averageDifficulty_bayes_eq_add`).

Information locality (section 5) is proved for a single dependency under erasure noise
(`erasure`), whose predictor is the Bayesian one at every representation of positive probability
(`bayes_erasure_predict`) and where the paper's first-order approximation is exact. Difficulty is
then the unigram surprisal less the surviving fraction of the pointwise mutual information
(`toReal_expectedSurprisal_erasure`), so it grows with distance when the words are positively
associated and shrinks when they are negatively associated (`locality`, `antilocality`).

## Implementation notes

* Surprisal is extended nonnegative: a representation that rules out a word its context allows
  makes the difficulty infinite. The erasure lemmas assume the word has positive probability and
  state the paper's real arithmetic through real parts.
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

open MeasureTheory ProbabilityTheory InformationTheory unitInterval
open scoped ENNReal

namespace FutrellGibsonLevy2020

/-! ### Memory processes -/

/-- A memory process: a lossy encoder from contexts to memory representations and a predictor
from memory representations to next words. The representation mediates all information flow
from the context to the prediction. -/
structure MemoryProcess (C R W : Type*) [MeasurableSpace C] [MeasurableSpace R]
    [MeasurableSpace W] where
  /-- The distribution over memory representations a context produces. -/
  encode : Kernel C R
  /-- The next-word distribution a memory representation predicts. -/
  predict : Kernel R W

namespace MemoryProcess

variable {C R W : Type*} [MeasurableSpace C] [MeasurableSpace R] [MeasurableSpace W]
  (mp : MemoryProcess C R W)

/-- The surprisal of the word `w` at the memory representation `r`. -/
noncomputable def perStateSurprisal (r : R) (w : W) : ℝ≥0∞ := surprisal (mp.predict r) w

/-- The expected surprisal of `w` in the context `c`: the difficulty of `w` under the process. -/
noncomputable def expectedSurprisal (c : C) (w : W) : ℝ≥0∞ :=
  ∫⁻ r, mp.perStateSurprisal r w ∂(mp.encode c)

/-- The average difficulty of the process under the language model `L` and the context prior
`π`: expected surprisal averaged over contexts and the words they predict. -/
noncomputable def averageDifficulty (L : Kernel C W) (π : Measure C) : ℝ≥0∞ :=
  ∫⁻ c, ∫⁻ w, mp.expectedSurprisal c w ∂(L c) ∂π

/-- The process realizes the language model `L` through the summary `f`: the encoder is
deterministic at `f`, and the predictor pulled back along `f` is `L`. -/
def IsLosslessFor (L : Kernel C W) : Prop :=
  ∃ (f : C → R) (hf : Measurable f), mp.encode = Kernel.deterministic f hf ∧
    mp.predict.comap f hf = L

variable {mp}

theorem isLosslessFor_comap {f : C → R} {hf : Measurable f}
    (h : mp.encode = Kernel.deterministic f hf) : mp.IsLosslessFor (mp.predict.comap f hf) :=
  ⟨f, hf, h, rfl⟩

variable [MeasurableSingletonClass R] {c : C}

theorem expectedSurprisal_of_dirac {r : R} (h : mp.encode c = Measure.dirac r) (w : W) :
    mp.expectedSurprisal c w = mp.perStateSurprisal r w := by
  rw [expectedSurprisal, h, lintegral_dirac]

-- Expected surprisal under a Bernoulli encoder, which produces `r₁` with probability `p`.
theorem expectedSurprisal_of_bernoulli {r₁ r₂ : R} {p : I} (h : mp.encode c = Ber(r₁, r₂, p))
    (w : W) : mp.expectedSurprisal c w
      = toNNReal p * mp.perStateSurprisal r₁ w + toNNReal (σ p) * mp.perStateSurprisal r₂ w := by
  rw [expectedSurprisal, h, lintegral_bernoulliMeasure]

theorem expectedSurprisal_of_deterministic {f : C → R} {hf : Measurable f}
    (h : mp.encode = Kernel.deterministic f hf) (c : C) (w : W) :
    mp.expectedSurprisal c w = mp.perStateSurprisal (f c) w :=
  expectedSurprisal_of_dirac (h ▸ Kernel.deterministic_apply hf c) w

-- A lossless process has the surprisal of the language model it realizes: surprisal theory is
-- the lossless special case of lossy-context surprisal.
theorem expectedSurprisal_eq_surprisal_of_lossless {L : Kernel C W} (h : mp.IsLosslessFor L)
    (c : C) (w : W) : mp.expectedSurprisal c w = surprisal (L c) w := by
  obtain ⟨f, hf, he, hp⟩ := h
  rw [expectedSurprisal_of_deterministic he, perStateSurprisal, ← hp, Kernel.comap_apply]

end MemoryProcess

open MemoryProcess

variable {W : Type*} [MeasurableSpace W]

private theorem snd_mul_map_fst_cond {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    [MeasurableSingletonClass S] [MeasurableSingletonClass T] (ρ : Measure (S × T))
    [IsFiniteMeasure ρ] (s : S) (t : T) :
    ρ.snd {t} * ((ρ[|Prod.snd ⁻¹' {t}]).map Prod.fst) {s} = ρ {(s, t)} := by
  rw [Measure.map_apply measurable_fst (.singleton s), mul_comm, Measure.snd_apply (.singleton t),
    cond_mul_eq_inter' (measurable_snd (.singleton t)) (measure_ne_top _ _)]
  congr 1
  ext ⟨a, b⟩
  simp [and_comm]

section AverageForm

/-! ### The Bayesian comprehender and the average form -/

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

theorem joint_singleton (w : W) (c : C) : joint L π {(w, c)} = π {c} * L c {w} := by
  rw [joint, Measure.map_apply measurable_swap (.singleton _),
    show Prod.swap ⁻¹' {(w, c)} = {(c, w)} from by ext ⟨_, _⟩; simp [and_comm],
    Measure.compProd_apply_singleton]

omit [MeasurableSingletonClass C] [MeasurableSingletonClass W] in
theorem snd_joint : (joint L π).snd = π := by
  rw [joint, Measure.snd_map_swap, Measure.fst_compProd]

variable [Fintype C] [Fintype W]

theorem memJoint_singleton (w : W) (r : R) :
    memJoint L π mem {(w, r)} = ∑ c, π {c} * L c {w} * mem c {r} := by
  simp_rw [memJoint, Measure.parallelComp_id_comp_apply_singleton, joint_singleton]

theorem measureMutualInfo_memJoint_le [Fintype R] : Im[memJoint L π mem] ≤ Im[joint L π] :=
  measureMutualInfo_parallelComp_id_comp_le _ mem

omit [Fintype C] in
theorem map_fst_cond_joint {c : C} (hc : π {c} ≠ 0) :
    ((joint L π)[|Prod.snd ⁻¹' {c}]).map Prod.fst = L c := by
  refine Measure.ext_of_singleton fun w ↦ ?_
  have h := snd_mul_map_fst_cond (joint L π) w c
  rw [snd_joint, joint_singleton] at h
  exact (ENNReal.mul_right_inj hc (measure_ne_top _ _)).1 h

theorem averageDifficulty_of_lossless {mp : MemoryProcess C R W} (h : mp.IsLosslessFor L) :
    mp.averageDifficulty L π = ENNReal.ofReal H[Prod.fst | Prod.snd ; joint L π] := by
  have hL (c : C) : ∫⁻ w, surprisal (L c) w ∂(L c) = ENNReal.ofReal (Hm[L c]) := by
    rw [lintegral_surprisal_eq_ofReal_add_klDiv, klDiv_self, add_zero]
  simp only [averageDifficulty, expectedSurprisal_eq_surprisal_of_lossless h]
  simp only [hL]
  rw [lintegral_fintype, condEntropy_eq_sum _ measurable_snd,
    ENNReal.ofReal_sum_of_nonneg fun c _ ↦ mul_nonneg measureReal_nonneg (entropy_nonneg _ _)]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [ENNReal.ofReal_mul measureReal_nonneg, measureReal_def, ← Measure.snd_apply (.singleton c),
    snd_joint, ENNReal.ofReal_toReal (measure_ne_top _ _), mul_comm]
  rcases eq_or_ne (π {c}) 0 with hc | hc
  · rw [hc, zero_mul, zero_mul]
  · rw [entropy_def, map_fst_cond_joint L π hc]

variable [Fintype R]

/-- The comprehender of section 3.3 pairs the memory kernel with the posterior predictive of the
next word given the representation, obtained by Bayes' rule. -/
noncomputable def bayes : MemoryProcess C R W where
  encode := mem
  predict := Kernel.ofFunOfCountable fun r ↦ ((memJoint L π mem)[|Prod.snd ⁻¹' {r}]).map Prod.fst

omit [MeasurableSingletonClass C] [MeasurableSingletonClass W] [IsMarkovKernel L]
  [IsProbabilityMeasure π] [IsMarkovKernel mem] [Fintype C] [Fintype W] in
theorem bayes_predict (r : R) :
    (bayes L π mem).predict r = ((memJoint L π mem)[|Prod.snd ⁻¹' {r}]).map Prod.fst :=
  rfl

omit [MeasurableSingletonClass C] [MeasurableSingletonClass W] [Fintype C] [Fintype W] in
private theorem isProbabilityMeasure_bayes_predict {r : R} (hr : (memJoint L π mem).snd {r} ≠ 0) :
    IsProbabilityMeasure ((bayes L π mem).predict r) := by
  rw [Measure.snd_apply (.singleton r)] at hr
  have := cond_isProbabilityMeasure hr
  rw [bayes_predict]
  infer_instance

theorem averageDifficulty_eq_sum_snd {mp : MemoryProcess C R W} (h : mp.encode = mem) :
    mp.averageDifficulty L π = ∑ r, (memJoint L π mem).snd {r} *
      ∫⁻ w, surprisal (mp.predict r) w ∂((bayes L π mem).predict r) := by
  have key (r : R) (w : W) : (memJoint L π mem).snd {r} *
      (surprisal (mp.predict r) w * (bayes L π mem).predict r {w}) =
      surprisal (mp.predict r) w * ∑ c, π {c} * L c {w} * mem c {r} := by
    rw [mul_left_comm, bayes_predict, snd_mul_map_fst_cond, memJoint_singleton]
  simp only [averageDifficulty, expectedSurprisal, perStateSurprisal, h, lintegral_fintype,
    Finset.mul_sum, key]
  calc _ = ∑ c, ∑ w, ∑ r, surprisal (mp.predict r) w * (π {c} * L c {w} * mem c {r}) := by
        simp only [Finset.sum_mul]
        exact Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun w _ ↦
          Finset.sum_congr rfl fun r _ ↦ by ring
    _ = ∑ w, ∑ c, ∑ r, surprisal (mp.predict r) w * (π {c} * L c {w} * mem c {r}) :=
        Finset.sum_comm
    _ = ∑ w, ∑ r, ∑ c, surprisal (mp.predict r) w * (π {c} * L c {w} * mem c {r}) :=
        Finset.sum_congr rfl fun w _ ↦ Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem averageDifficulty_bayes :
    (bayes L π mem).averageDifficulty L π =
      ENNReal.ofReal H[Prod.fst | Prod.snd ; memJoint L π mem] := by
  rw [averageDifficulty_eq_sum_snd L π mem rfl, condEntropy_eq_sum _ measurable_snd,
    ENNReal.ofReal_sum_of_nonneg fun r _ ↦ mul_nonneg measureReal_nonneg (entropy_nonneg _ _)]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [ENNReal.ofReal_mul measureReal_nonneg, measureReal_def, ← Measure.snd_apply (.singleton r),
    ENNReal.ofReal_toReal (measure_ne_top _ _), entropy_def, ← bayes_predict]
  rcases eq_or_ne ((memJoint L π mem).snd {r}) 0 with hr | hr
  · rw [hr, zero_mul, zero_mul]
  · have := isProbabilityMeasure_bayes_predict L π mem hr
    rw [lintegral_surprisal_eq_ofReal_add_klDiv, klDiv_self, add_zero]

/-- Given the encoder, a predictor's average difficulty is the Bayesian comprehender's plus the
expected divergence of the Bayesian prediction from its own. -/
theorem averageDifficulty_eq_bayes_add {mp : MemoryProcess C R W} [IsMarkovKernel mp.predict]
    (h : mp.encode = mem) :
    mp.averageDifficulty L π = (bayes L π mem).averageDifficulty L π +
      ∑ r, (memJoint L π mem).snd {r} * klDiv ((bayes L π mem).predict r) (mp.predict r) := by
  rw [averageDifficulty_eq_sum_snd L π mem h, averageDifficulty_eq_sum_snd L π mem rfl,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rcases eq_or_ne ((memJoint L π mem).snd {r}) 0 with hr | hr
  · rw [hr, zero_mul, zero_mul, zero_mul, add_zero]
  · have := isProbabilityMeasure_bayes_predict L π mem hr
    rw [← mul_add, lintegral_surprisal_eq_ofReal_add_klDiv, lintegral_surprisal_eq_ofReal_add_klDiv,
      klDiv_self, add_zero]

theorem averageDifficulty_bayes_le {mp : MemoryProcess C R W} [IsMarkovKernel mp.predict]
    (h : mp.encode = mem) :
    (bayes L π mem).averageDifficulty L π ≤ mp.averageDifficulty L π := by
  rw [averageDifficulty_eq_bayes_add L π mem h]
  exact le_self_add

/-- Given the encoder, the Bayesian comprehender is the unique Markov predictor of least average
difficulty, up to representations of probability zero. -/
theorem averageDifficulty_bayes_eq_iff {mp : MemoryProcess C R W} [IsMarkovKernel mp.predict]
    (h : mp.encode = mem) :
    mp.averageDifficulty L π = (bayes L π mem).averageDifficulty L π ↔
      ∀ r, (memJoint L π mem).snd {r} ≠ 0 → mp.predict r = (bayes L π mem).predict r := by
  rw [averageDifficulty_eq_bayes_add L π mem h, averageDifficulty_bayes]
  conv_lhs => rhs; rw [← add_zero (ENNReal.ofReal _)]
  rw [ENNReal.add_right_inj ENNReal.ofReal_ne_top, Finset.sum_eq_zero_iff]
  refine forall_congr' fun r ↦ ?_
  have : IsFiniteMeasure ((bayes L π mem).predict r) := by rw [bayes_predict]; infer_instance
  rw [← or_iff_not_imp_left, mul_eq_zero, klDiv_eq_zero_iff,
    eq_comm (a := (bayes L π mem).predict r)]
  simp

/-- The Bayesian comprehender's difficulty exceeds the conditional entropy of the word given its
context, the difficulty of a lossless process, by the predictive information that memory loses. -/
theorem averageDifficulty_bayes_eq_add :
    (bayes L π mem).averageDifficulty L π = ENNReal.ofReal H[Prod.fst | Prod.snd ; joint L π] +
      ENNReal.ofReal (Im[joint L π] - Im[memJoint L π mem]) := by
  have : Nonempty C := π.nonempty_of_neZero
  have hH : H[Prod.fst | Prod.snd ; memJoint L π mem] =
      H[Prod.fst | Prod.snd ; joint L π] + (Im[joint L π] - Im[memJoint L π mem]) := by
    rw [condEntropy_fst_snd, condEntropy_fst_snd, memJoint, Measure.fst_parallelComp_id_comp]
    ring
  rw [averageDifficulty_bayes, hH, ENNReal.ofReal_add (condEntropy_nonneg _ _ _)
    (sub_nonneg.2 (measureMutualInfo_memJoint_le L π mem))]

theorem averageDifficulty_lossless_le_bayes {R' : Type*} [MeasurableSpace R']
    [MeasurableSingletonClass R'] {mp : MemoryProcess C R' W} (h : mp.IsLosslessFor L) :
    mp.averageDifficulty L π ≤ (bayes L π mem).averageDifficulty L π := by
  rw [averageDifficulty_of_lossless L π h, averageDifficulty_bayes_eq_add]
  exact le_self_add

-- Every language model has a lossless process, reading the context itself.
example : (⟨Kernel.deterministic id measurable_id, L⟩ : MemoryProcess C C W).IsLosslessFor L :=
  ⟨id, measurable_id, rfl, rfl⟩

end AverageForm

section Erasure

/-! ### Erasure noise and information locality -/

variable (L : Kernel W W) (π : Measure W)

/-- The pointwise mutual information of the next word `w` with the context word `y`, relative to
the unigram distribution of the next word. -/
noncomputable def pmi (y w : W) : ℝ := Real.log ((L y).real {w} / (L ∘ₘ π).real {w})

variable [MeasurableSingletonClass W] [Countable W]

/-- The erasure-noise memory process erases the context word with probability `e`, and its
predictor reads a retained word through the language model and an erased one as the unigram
distribution. -/
noncomputable def erasure (e : I) : MemoryProcess W (W ⊕ Unit) W where
  encode := Kernel.ofFunOfCountable fun y ↦ Ber(Sum.inr (), Sum.inl y, e)
  predict := Kernel.ofFunOfCountable (Sum.elim (⇑L) fun _ ↦ L ∘ₘ π)

variable {e e' : I} {y w : W}

instance (e : I) : IsMarkovKernel (erasure L π e).encode :=
  ⟨fun y ↦ inferInstanceAs (IsProbabilityMeasure Ber(Sum.inr (), Sum.inl y, e))⟩

theorem erasure_encode_inl [DecidableEq W] (c y : W) :
    (erasure L π e).encode c {Sum.inl y} = if c = y then (toNNReal (σ e) : ℝ≥0∞) else 0 := by
  rcases eq_or_ne c y with rfl | hcy
  · simp [erasure, Kernel.ofFunOfCountable, Kernel.coe_mk, bernoulliMeasure_def]
  · simp [erasure, Kernel.ofFunOfCountable, Kernel.coe_mk, bernoulliMeasure_def, hcy]

theorem erasure_encode_inr (c : W) (u : Unit) :
    (erasure L π e).encode c {Sum.inr u} = toNNReal e := by
  simp [erasure, Kernel.ofFunOfCountable, Kernel.coe_mk, bernoulliMeasure_def]

theorem erasure_zero_isLosslessFor : (erasure L π 0).IsLosslessFor L :=
  ⟨Sum.inl, measurable_inl,
    Kernel.ext fun _ ↦ (bernoulliMeasure_zero _ _).trans (Kernel.deterministic_apply _ _).symm,
    Kernel.ext fun _ ↦ rfl⟩

theorem erasure_zero : (erasure L π 0).expectedSurprisal y w = surprisal (L y) w :=
  expectedSurprisal_eq_surprisal_of_lossless (erasure_zero_isLosslessFor L π) y w

theorem erasure_one : (erasure L π 1).expectedSurprisal y w = surprisal (L ∘ₘ π) w :=
  expectedSurprisal_of_dirac (mp := erasure L π 1) (c := y) (bernoulliMeasure_one _ _) w

theorem expectedSurprisal_erasure (y w : W) :
    (erasure L π e).expectedSurprisal y w =
      toNNReal e * surprisal (L ∘ₘ π) w + toNNReal (σ e) * surprisal (L y) w :=
  expectedSurprisal_of_bernoulli (mp := erasure L π e) (c := y) rfl w

variable [IsMarkovKernel L] [IsProbabilityMeasure π]

omit [MeasurableSingletonClass W] [Countable W] in
theorem surprisal_eq_sub_pmi (h0 : (L ∘ₘ π).real {w} ≠ 0) (hy : (L y).real {w} ≠ 0) :
    (surprisal (L y) w).toReal = (surprisal (L ∘ₘ π) w).toReal - pmi L π y w := by
  rw [toReal_surprisal prob_le_one, toReal_surprisal prob_le_one, pmi, Real.log_div hy h0]
  ring

omit [MeasurableSingletonClass W] [Countable W] in
private theorem measure_ne_zero_of_real {μ : Measure W} {w : W} (h : μ.real {w} ≠ 0) :
    μ {w} ≠ 0 :=
  fun h0 ↦ h (by rw [measureReal_def, h0, ENNReal.toReal_zero])

omit [IsMarkovKernel L] [IsProbabilityMeasure π] in
theorem expectedSurprisal_erasure_ne_top (h0 : (L ∘ₘ π).real {w} ≠ 0)
    (hy : (L y).real {w} ≠ 0) : (erasure L π e).expectedSurprisal y w ≠ ∞ := by
  rw [expectedSurprisal_erasure]
  exact ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top (surprisal_ne_top_iff.2 (measure_ne_zero_of_real h0)),
      ENNReal.mul_ne_top ENNReal.coe_ne_top (surprisal_ne_top_iff.2 (measure_ne_zero_of_real hy))⟩

theorem toReal_expectedSurprisal_erasure (h0 : (L ∘ₘ π).real {w} ≠ 0)
    (hy : (L y).real {w} ≠ 0) : ((erasure L π e).expectedSurprisal y w).toReal
      = (surprisal (L ∘ₘ π) w).toReal - (1 - (e : ℝ)) * pmi L π y w := by
  rw [expectedSurprisal_erasure, ENNReal.toReal_add
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (surprisal_ne_top_iff.2 (measure_ne_zero_of_real h0)))
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (surprisal_ne_top_iff.2 (measure_ne_zero_of_real hy))),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal, coe_toNNReal,
    coe_toNNReal, coe_symm_eq, surprisal_eq_sub_pmi L π h0 hy]
  ring

theorem toReal_expectedSurprisal_erasure_sub (h0 : (L ∘ₘ π).real {w} ≠ 0)
    (hy : (L y).real {w} ≠ 0) :
    ((erasure L π e).expectedSurprisal y w).toReal - (surprisal (L y) w).toReal
      = (e : ℝ) * pmi L π y w := by
  rw [toReal_expectedSurprisal_erasure L π h0 hy, surprisal_eq_sub_pmi L π h0 hy]
  ring

/-- The erasure process is the Bayesian comprehender of its own encoder: at every representation
of positive probability its predictor is the posterior predictive of section 3.3. -/
theorem bayes_erasure_predict [Fintype W] {r : W ⊕ Unit}
    (hr : (memJoint L π (erasure L π e).encode).snd {r} ≠ 0) :
    (bayes L π (erasure L π e).encode).predict r = (erasure L π e).predict r := by
  classical
  have : Nonempty W := π.nonempty_of_neZero
  have hsnd : (memJoint L π (erasure L π e).encode).snd {r} =
      ∑ c, π {c} * (erasure L π e).encode c {r} := by
    rw [memJoint, Measure.snd_parallelComp_id_comp, snd_joint, Measure.comp_apply_singleton]
  have hjoint (w : W) : memJoint L π (erasure L π e).encode {(w, r)} =
      (memJoint L π (erasure L π e).encode).snd {r} * (erasure L π e).predict r {w} := by
    rw [memJoint_singleton, hsnd]
    rcases r with y | u
    · simp only [erasure_encode_inl, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true]
      show _ = _ * L y {w}
      ring
    · have hπ : ∑ c, π {c} * (toNNReal e : ℝ≥0∞) = toNNReal e := by
        rw [← Finset.sum_mul, sum_measure_singleton, Finset.coe_univ, measure_univ, one_mul]
      simp only [erasure_encode_inr]
      show _ = _ * (L ∘ₘ π) {w}
      rw [hπ, Measure.comp_apply_singleton, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ ↦ by ring
  refine Measure.ext_of_singleton fun w ↦ ?_
  have h := snd_mul_map_fst_cond (memJoint L π (erasure L π e).encode) w r
  rw [hjoint] at h
  exact (ENNReal.mul_right_inj hr (measure_ne_top _ _)).1 h

/-- Under progressive noise, where a more distant context word has a larger erasure rate,
difficulty increases with distance when the words are positively associated. -/
theorem locality (h : e ≤ e') (hpmi : 0 ≤ pmi L π y w) (h0 : (L ∘ₘ π).real {w} ≠ 0)
    (hy : (L y).real {w} ≠ 0) :
    (erasure L π e).expectedSurprisal y w ≤ (erasure L π e').expectedSurprisal y w := by
  rw [← ENNReal.toReal_le_toReal (expectedSurprisal_erasure_ne_top L π h0 hy)
      (expectedSurprisal_erasure_ne_top L π h0 hy), toReal_expectedSurprisal_erasure L π h0 hy,
    toReal_expectedSurprisal_erasure L π h0 hy]
  have : (e : ℝ) ≤ e' := h
  nlinarith

theorem antilocality (h : e ≤ e') (hpmi : pmi L π y w ≤ 0) (h0 : (L ∘ₘ π).real {w} ≠ 0)
    (hy : (L y).real {w} ≠ 0) :
    (erasure L π e').expectedSurprisal y w ≤ (erasure L π e).expectedSurprisal y w := by
  rw [← ENNReal.toReal_le_toReal (expectedSurprisal_erasure_ne_top L π h0 hy)
      (expectedSurprisal_erasure_ne_top L π h0 hy), toReal_expectedSurprisal_erasure L π h0 hy,
    toReal_expectedSurprisal_erasure L π h0 hy]
  have : (e : ℝ) ≤ e' := h
  nlinarith

end Erasure

end FutrellGibsonLevy2020
