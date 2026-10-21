module

public import Linglib.Phonology.HarmonicGrammar.MaxEnt

/-!
# Berger, Della Pietra and Della Pietra (1996): A Maximum Entropy Approach to Natural Language Processing

Berger, Della Pietra and Della Pietra model a process that outputs `y` in a context `x` by the
most uniform conditional distribution consistent with the statistics of a sample. A statistic is
the expectation of a feature `f(x, y)`; a model satisfies its constraint when its expectation of
the feature, averaged over the sample's contexts, is the sample's (4), and among the models
satisfying every constraint the maximum entropy principle chooses the one of greatest conditional
entropy (5)–(6). The maximizer of the Lagrangian (7) for fixed multipliers `λ` has the
exponential form (10), and the maximum entropy model is the member of that family that maximizes
the likelihood of the sample (§3.5).

The motivating example (§2) translates English *in* by one of five French phrases. With only the
phrases known the most uniform model is uniform; requiring `p(dans) + p(en) = 3/10` makes it
`3/20, 3/20, 7/30, 7/30, 7/30`; adding `p(dans) + p(à) = 1/2` gives the solution the paper leaves
to the reader (§3.4), with `p(dans) = (9 − √51)/10`.

## Main results

* `isGreatest_uniform`, `isGreatest_two`, `isGreatest_three`: the maximum entropy models of §2.
* `lagrangian_le_lagrangian_model`: the model `p_λ` of (10) maximizes the Lagrangian (8).
* `lagrangian_model_eq_neg_logLik`: the value of the Lagrangian at `p_λ` is minus the
  log-likelihood (13) of `p_λ`.
* `model_mem_constraints`, `isGreatest_condEntropy_model`, `condEntropy_model_eq_neg_logLik`: the
  Kuhn–Tucker conclusion of §3.5. The parameters of greatest likelihood give the maximum entropy
  model in `C`, whose entropy is minus that likelihood.
* `eq_model_of_condEntropy_eq`: the maximum entropy model is unique at the observed contexts.
* `concaveOn_logLik_model`: the log-likelihood is concave in the parameters (§3.6).

## Implementation notes

* Features are real-valued, `f : X × Y → ι → ℝ`, binary in the paper. The model (10) is
  `HarmonicGrammar.condMaxEnt f (-λ)`, the substrate's harmony being minus the weighted
  statistic, and the paper's conditional entropy (5) is `H[Prod.snd | Prod.fst ; p̃.fst ⊗ₘ q]`,
  its footnote 1's `H(Y | X)` under the joint `p̃(x) p(y|x)`.
* With the Lagrangian (7), the value at its maximizer is `∑ p̃(x) log Z_λ(x) − λ · p̃(f)`, which is
  `−L(p_λ)`; (11) prints this dual function with the opposite sign, as `L(p_λ)` (14), and so poses
  the dual as a maximization. The dual of (7) is minimized; maximizing `L(p_λ)` is the same
  problem.
* §3.3 says the maximum entropy model in `C` is unique; it is unique at the contexts of positive
  empirical mass, and unconstrained at the others.

## TODO

* Footnote 2's unattained case, where the maximum entropy model is a limit of models `p_λ`.
* Improved iterative scaling (§3.6), feature selection (§4) and the applications of §5.

## References

* [berger-della-pietra-della-pietra-1996]
-/

@[expose] public section

namespace BergerDellaPietraDellaPietra1996

open MeasureTheory ProbabilityTheory InformationTheory HarmonicGrammar Real Finset
open scoped ENNReal

/-! ### The translation example (§2) -/

/-- The French renderings of *in* in the expert's sample. -/
inductive Phrase
  | dans
  | en
  | à
  | auCoursDe
  | pendant
  deriving DecidableEq, Fintype, Inhabited

instance : MeasurableSpace Phrase := ⊤
instance : MeasurableSingletonClass Phrase := ⟨fun _ ↦ trivial⟩

namespace Phrase

theorem sum_eq {M : Type*} [AddCommMonoid M] (g : Phrase → M) :
    ∑ φ, g φ = g dans + g en + g à + g auCoursDe + g pendant := by
  show ∑ φ ∈ ({dans, en, à, auCoursDe, pendant} : Finset Phrase), g φ = _
  simp [sum_insert, add_assoc]

/-- The feature of the second constraint, the expert choosing *dans* or *en*. -/
def dansOrEn : Phrase → ℝ
  | dans | en => 1
  | _ => 0

/-- The feature of the third constraint, the expert choosing *dans* or *à*. -/
def dansOrÀ : Phrase → ℝ
  | dans | à => 1
  | _ => 0

end Phrase

open Phrase

theorem integral_eq (q : Measure Phrase) [IsFiniteMeasure q] (g : Phrase → ℝ) :
    ∫ φ, g φ ∂q = q.real {dans} * g dans + q.real {en} * g en + q.real {à} * g à +
      q.real {auCoursDe} * g auCoursDe + q.real {pendant} * g pendant := by
  rw [integral_fintype .of_finite, sum_eq]
  simp only [smul_eq_mul]

/-- Knowing only the five phrases, the maximum entropy model is uniform. With no features, every
distribution satisfies the constraints, and the uniform one has the greatest entropy. -/
theorem isGreatest_uniform :
    IsGreatest (measureEntropy '' {q : Measure Phrase | IsProbabilityMeasure q})
      (Hm[maxEnt (fun _ : Phrase ↦ (0 : Fin 0 → ℝ)) 0]) ∧
      ∀ φ, (maxEnt (fun _ : Phrase ↦ (0 : Fin 0 → ℝ)) 0).real {φ} = 1 / 5 := by
  refine ⟨?_, fun φ ↦ ?_⟩
  · convert isGreatest_measureEntropy_maxEnt (fun _ : Phrase ↦ (0 : Fin 0 → ℝ)) 0 using 3
    ext q
    exact ⟨fun h ↦ ⟨h, Subsingleton.elim _ _⟩, And.left⟩
  · rw [maxEnt_real_singleton]
    simp [harmony, softmax_apply, show Fintype.card Phrase = 5 from rfl]

/-- The statistic of the first two constraints. -/
def twoFeatures (φ : Phrase) : Fin 1 → ℝ := ![dansOrEn φ]

/-- The model maximizing entropy subject to `p(dans) + p(en) = 3/10`. -/
noncomputable abbrev twoModel : Measure Phrase := maxEnt twoFeatures ![log (14 / 9)]

theorem twoModel_real_singleton :
    twoModel.real {dans} = 3 / 20 ∧ twoModel.real {en} = 3 / 20 ∧ twoModel.real {à} = 7 / 30 ∧
      twoModel.real {auCoursDe} = 7 / 30 ∧ twoModel.real {pendant} = 7 / 30 := by
  have he : exp (-log (14 / 9 : ℝ)) = 9 / 14 := by rw [exp_neg, exp_log (by norm_num)]; norm_num
  simp only [twoModel, maxEnt_real_singleton, softmax_apply, sum_eq]
  norm_num [harmony, twoFeatures, dansOrEn, dotProduct, he]

/-- Requiring `p(dans) + p(en) = 3/10`, the most uniform model gives *dans* and *en* `3/20` each
and the other three phrases `7/30` each. -/
theorem isGreatest_two :
    IsGreatest (measureEntropy '' {q : Measure Phrase | IsProbabilityMeasure q ∧
      q.real {dans} + q.real {en} = 3 / 10}) (Hm[twoModel]) := by
  have hT (q : Measure Phrase) [IsFiniteMeasure q] :
      ∫ φ, twoFeatures φ ∂q = ![q.real {dans} + q.real {en}] := by
    rw [integral_eq_sum, sum_eq]
    funext i
    fin_cases i
    simp [twoFeatures, dansOrEn]
  have hP : twoModel.real {dans} + twoModel.real {en} = 3 / 10 := by
    rw [twoModel_real_singleton.1, twoModel_real_singleton.2.1]; norm_num
  convert isGreatest_measureEntropy_maxEnt twoFeatures ![log (14 / 9)] using 3
  ext q
  refine and_congr_right fun hq ↦ ?_
  rw [hT, ← twoModel, hT, hP]
  simp

/-- The statistic of all three constraints. -/
def threeFeatures (φ : Phrase) : Fin 2 → ℝ := ![dansOrEn φ, dansOrÀ φ]

/-- A positive distribution of the five phrases in which *au cours de* and *pendant* are equally
likely and `p(en) p(à) = p(dans) p(au cours de)` is the exponential model of `threeFeatures`, the
exponentials of the two multipliers being `p(en)/p(au cours de)` and `p(à)/p(au cours de)`. -/
theorem maxEnt_three_real_singleton {d e a c : ℝ} (he : 0 < e) (ha : 0 < a) (hc : 0 < c)
    (hR : e * a = d * c) (hN : d + e + a + 2 * c = 1) :
    (maxEnt threeFeatures ![-log (e / c), -log (a / c)]).real {dans} = d ∧
      (maxEnt threeFeatures ![-log (e / c), -log (a / c)]).real {en} = e ∧
      (maxEnt threeFeatures ![-log (e / c), -log (a / c)]).real {à} = a ∧
      (maxEnt threeFeatures ![-log (e / c), -log (a / c)]).real {auCoursDe} = c ∧
      (maxEnt threeFeatures ![-log (e / c), -log (a / c)]).real {pendant} = c := by
  have hH : harmony threeFeatures ![-log (e / c), -log (a / c)] =
      fun φ ↦ log (e / c) * dansOrEn φ + log (a / c) * dansOrÀ φ := by
    funext φ
    simp [harmony, threeFeatures, dotProduct, Fin.sum_univ_two]
    ring
  have hd : exp (log (e / c) + log (a / c)) = d / c := by
    rw [exp_add, exp_log (div_pos he hc), exp_log (div_pos ha hc)]
    field_simp
    linear_combination hR
  have hZ : ∑ φ, exp (log (e / c) * dansOrEn φ + log (a / c) * dansOrÀ φ) = 1 / c := by
    rw [sum_eq]
    simp only [dansOrEn, dansOrÀ, mul_one, mul_zero, add_zero, zero_add, exp_zero, hd,
      exp_log (div_pos he hc), exp_log (div_pos ha hc)]
    field_simp
    linear_combination hN
  simp only [maxEnt_real_singleton, softmax_apply, hH, hZ]
  simp only [dansOrEn, dansOrÀ, mul_one, mul_zero, add_zero, zero_add, exp_zero, hd,
    exp_log (div_pos he hc), exp_log (div_pos ha hc)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> field_simp

/-- The model maximizing entropy subject to all three constraints, which §3.4 leaves to the
reader. -/
noncomputable abbrev threeModel : Measure Phrase :=
  maxEnt threeFeatures ![-log (((√51 - 6) / 10) / ((11 - √51) / 20)),
    -log (((√51 - 4) / 10) / ((11 - √51) / 20))]

theorem threeModel_real_singleton :
    threeModel.real {dans} = (9 - √51) / 10 ∧ threeModel.real {en} = (√51 - 6) / 10 ∧
      threeModel.real {à} = (√51 - 4) / 10 ∧ threeModel.real {auCoursDe} = (11 - √51) / 20 ∧
      threeModel.real {pendant} = (11 - √51) / 20 := by
  have hs : √51 ^ 2 = 51 := sq_sqrt (by norm_num)
  have h7 : 7 < √51 := lt_sqrt (by norm_num) |>.2 (by norm_num)
  have h8 : √51 < 8 := (sqrt_lt' (by norm_num)).2 (by norm_num)
  exact maxEnt_three_real_singleton (by linarith) (by linarith) (by linarith)
    (by linear_combination hs / 200) (by ring)

/-- Requiring also `p(dans) + p(à) = 1/2`, the most uniform model gives *dans* `(9 − √51)/10`. -/
theorem isGreatest_three :
    IsGreatest (measureEntropy '' {q : Measure Phrase | IsProbabilityMeasure q ∧
      q.real {dans} + q.real {en} = 3 / 10 ∧ q.real {dans} + q.real {à} = 1 / 2})
      (Hm[threeModel]) := by
  have hT (q : Measure Phrase) [IsFiniteMeasure q] :
      ∫ φ, threeFeatures φ ∂q = ![q.real {dans} + q.real {en}, q.real {dans} + q.real {à}] := by
    rw [integral_eq_sum, sum_eq]
    funext i
    fin_cases i <;> simp [threeFeatures, dansOrEn, dansOrÀ]
  obtain ⟨h1, h2, h3, -, -⟩ := threeModel_real_singleton
  convert isGreatest_measureEntropy_maxEnt threeFeatures _ using 3
  ext q
  refine and_congr_right fun hq ↦ ?_
  rw [hT, ← threeModel, hT, h1, h2, h3]
  constructor
  · rintro ⟨hen, hà⟩
    rw [hen, hà]
    funext i
    fin_cases i <;> simp <;> ring
  · intro h
    have h0 := congrFun h 0
    have h1' := congrFun h 1
    simp at h0 h1'
    exact ⟨by linarith, by linarith⟩

/-! ### Maximum entropy modeling (§3) -/

section Modeling

variable {X Y ι : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace Y] [Fintype ι] (f : X × Y → ι → ℝ) (p : Measure (X × Y))

/-- The models satisfying the constraints (4), conditional distributions whose expectations of
the features, averaged over the sample's contexts, are the sample's. -/
def constraints : Set (Kernel X Y) :=
  {q | IsMarkovKernel q ∧ ∫ z, f z ∂(p.fst ⊗ₘ q) = ∫ z, f z ∂p}

/-- The exponential model (10) with multipliers `θ`, the paper's `λ`. -/
noncomputable def model (θ : ι → ℝ) : Kernel X Y :=
  condMaxEnt f (-θ)

/-- The Lagrangian (7), the conditional entropy (5) plus each multiplier times its constraint's
violation. -/
noncomputable def lagrangian (q : Kernel X Y) (θ : ι → ℝ) : ℝ :=
  H[Prod.snd | Prod.fst ; p.fst ⊗ₘ q] + θ ⬝ᵥ ((∫ z, f z ∂(p.fst ⊗ₘ q)) - ∫ z, f z ∂p)

/-- The log-likelihood (13) of a conditional model on the sample. -/
noncomputable def logLik (q : Kernel X Y) : ℝ :=
  ∫ z, log ((q z.1).real {z.2}) ∂p

theorem logLik_model (θ : ι → ℝ) : logLik p (model f θ) = condLogLikelihood f p (-θ) :=
  rfl

private theorem isMaxOn_condLogLikelihood_neg {θ : ι → ℝ}
    (h : IsMaxOn (fun θ ↦ logLik p (model f θ)) Set.univ θ) :
    IsMaxOn (condLogLikelihood f p) Set.univ (-θ) :=
  isMaxOn_iff.2 fun w _ ↦ by simpa [logLik_model] using h (Set.mem_univ (-w))

variable [Fintype Y] [MeasurableSingletonClass Y] [Nonempty Y] [IsProbabilityMeasure p]

/-- The model `p_θ` maximizes the Lagrangian for fixed multipliers (8), (10). -/
theorem lagrangian_le_lagrangian_model (θ : ι → ℝ) (q : Kernel X Y) [IsMarkovKernel q] :
    lagrangian f p q θ ≤ lagrangian f p (model f θ) θ := by
  have h₁ := sum_toReal_klDiv_condMaxEnt_add_condEntropy f (-θ) p.fst q
  have h₂ := condEntropy_condMaxEnt f (-θ) p.fst
  have h₃ : 0 ≤ ∑ x, p.fst.real {x} * (klDiv (q x) (condMaxEnt f (-θ) x)).toReal :=
    sum_nonneg fun x _ ↦ mul_nonneg measureReal_nonneg ENNReal.toReal_nonneg
  simp only [lagrangian, model, dotProduct_sub, neg_dotProduct] at h₁ h₂ ⊢
  linarith

/-- The value of the Lagrangian at its maximizer is minus the log-likelihood of `p_θ`. -/
theorem lagrangian_model_eq_neg_logLik (θ : ι → ℝ) :
    lagrangian f p (model f θ) θ = -logLik p (model f θ) := by
  have h := condEntropy_condMaxEnt f (-θ) p.fst
  rw [logLik_model, condLogLikelihood_eq]
  simp only [lagrangian, model, dotProduct_sub, neg_dotProduct] at h ⊢
  linarith

variable {f p} {θ : ι → ℝ}

/-- The parameters of greatest likelihood give a model satisfying the constraints. -/
theorem model_mem_constraints (h : IsMaxOn (fun θ ↦ logLik p (model f θ)) Set.univ θ) :
    model f θ ∈ constraints f p :=
  ⟨inferInstanceAs (IsMarkovKernel (condMaxEnt f (-θ))),
    (isMaxOn_condLogLikelihood_iff f (-θ) p).1 (isMaxOn_condLogLikelihood_neg f p h)⟩

/-- The Kuhn–Tucker conclusion of §3.5. The model in the parametric family that maximizes the
likelihood of the sample is the maximum entropy model in `C`. -/
theorem isGreatest_condEntropy_model (h : IsMaxOn (fun θ ↦ logLik p (model f θ)) Set.univ θ) :
    IsGreatest ((fun q : Kernel X Y ↦ H[Prod.snd | Prod.fst ; p.fst ⊗ₘ q]) '' constraints f p)
      (H[Prod.snd | Prod.fst ; p.fst ⊗ₘ model f θ]) :=
  isGreatest_condEntropy_of_isMaxOn f (-θ) p (isMaxOn_condLogLikelihood_neg f p h)

/-- The primal and dual values agree, the greatest entropy in `C` being minus the greatest
log-likelihood. -/
theorem condEntropy_model_eq_neg_logLik
    (h : IsMaxOn (fun θ ↦ logLik p (model f θ)) Set.univ θ) :
    H[Prod.snd | Prod.fst ; p.fst ⊗ₘ model f θ] = -logLik p (model f θ) := by
  rw [logLik_model, condLogLikelihood_eq_neg_condEntropy f (-θ) p
    (model_mem_constraints h).2, neg_neg]
  rfl

/-- A model in `C` with the greatest entropy is the maximum entropy model at every context of
positive empirical mass. -/
theorem eq_model_of_condEntropy_eq (h : IsMaxOn (fun θ ↦ logLik p (model f θ)) Set.univ θ)
    {q : Kernel X Y} (hq : q ∈ constraints f p)
    (hH : H[Prod.snd | Prod.fst ; p.fst ⊗ₘ q] = H[Prod.snd | Prod.fst ; p.fst ⊗ₘ model f θ])
    {x : X} (hx : p.fst {x} ≠ 0) : q x = model f θ x := by
  have := hq.1
  exact eq_condMaxEnt_of_condEntropy_eq f (-θ) p.fst
    (hq.2.trans (model_mem_constraints h).2.symm) hH hx

variable (f p)

/-- The log-likelihood of the model is concave in the multipliers (§3.6). -/
theorem concaveOn_logLik_model : ConcaveOn ℝ Set.univ fun θ ↦ logLik p (model f θ) := by
  simpa [Function.comp_def, logLik_model] using
    (concaveOn_condLogLikelihood f p).comp_linearMap (-LinearMap.id)

end Modeling

end BergerDellaPietraDellaPietra1996
