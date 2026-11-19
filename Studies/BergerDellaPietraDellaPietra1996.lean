module

public import Linglib.Phonology.HarmonicGrammar.MaxEnt

/-!
# Berger, Della Pietra and Della Pietra (1996): A Maximum Entropy Approach to Natural Language Processing

Berger, Della Pietra and Della Pietra model a process that outputs $y$ in a context $x$ by the
most uniform conditional distribution consistent with the statistics of a sample $\tilde p$. A
statistic is the expectation of a feature $f(x, y)$, and a model satisfies its constraint when its
expectation of the feature, averaged over the sample's contexts, is the sample's. Among the
models satisfying every constraint the maximum entropy principle chooses the one of greatest
conditional entropy. For fixed multipliers $\lambda$ the Lagrangian of this problem [is greatest
at](##lagrangian_le_lagrangian_model) the exponential model $p_\lambda(y \mid x) \propto
\exp(\lambda \cdot f(x, y))$, so every model satisfying the constraints [has entropy at
most](##condEntropy_le_neg_logLik) minus the log-likelihood of every $p_\lambda$, and the
$p_\lambda$ of greatest likelihood [is the maximum entropy
model](##isGreatest_condEntropy_model), [the only one](##eq_model_of_condEntropy_eq) at the
contexts the sample contains.

The motivating example translates English *in* by one of five French phrases. Requiring
$p(\textit{dans}) + p(\textit{en}) = 3/10$ makes the most uniform model $3/20, 3/20, 7/30, 7/30,
7/30$; adding $p(\textit{dans}) + p(\textit{à}) = 1/2$ gives [the
solution](##isGreatest_three) the paper leaves to the reader, [with](##threeModel_real_singleton) $p(\textit{dans}) = (9 -
\sqrt{51})/10$.

## Implementation notes

* Features are real-valued, `f : X × Y → ι → ℝ`, binary in the paper. The exponential model is
  `HarmonicGrammar.condMaxEnt f (-λ)`, the substrate's harmony being minus the weighted
  statistic, and the paper's conditional entropy is `H[Prod.snd | Prod.fst ; p̃.fst ⊗ₘ q]`, the
  `H(Y | X)` of its first footnote under the joint `p̃(x) p(y|x)`.
* With the paper's Lagrangian, entropy plus each multiplier times its constraint's violation, the
  value at the maximizer is `∑ p̃(x) log Z_λ(x) − λ · p̃(f)`, which
  [is](##lagrangian_model_eq_neg_logLik) `−L(p_λ)`. The paper's dual function is `L(p_λ)` and its dual problem a maximization; the dual
  of the Lagrangian as formalized is minimized, which is the same problem.
* The maximum entropy model is determined at the contexts of positive empirical mass and
  unconstrained at the others.
* In the example a model is a distribution of the phrases, the counting measure tilted by the
  weighted features, and each constraint enters only through the expected value of that
  potential.

## TODO

* The unattained case of the paper's second footnote, where the maximum entropy model is a limit
  of models `p_λ`.
* Improved iterative scaling, feature selection and the applications.

## References

* [berger-della-pietra-della-pietra-1996]
-/

@[expose] public section

namespace BergerDellaPietraDellaPietra1996

open MeasureTheory ProbabilityTheory InformationTheory HarmonicGrammar Real Finset
open scoped ENNReal

/-! ### The translation example -/

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

-- p. 41, the first model
theorem isGreatest_uniform :
    IsGreatest (measureEntropy '' {q : Measure Phrase | IsProbabilityMeasure q})
      (Hm[uniformOn (Set.univ : Set Phrase)]) := by
  have h : Hm[uniformOn (Set.univ : Set Phrase)] = log (Fintype.card Phrase) := by
    simpa using measureEntropy_uniformOn (S := Phrase) univ_nonempty
  refine ⟨⟨_, isProbabilityMeasure_uniformOn Set.finite_univ Set.univ_nonempty, rfl⟩, ?_⟩
  rintro _ ⟨q, -, rfl⟩
  exact h ▸ measureEntropy_le_log_card q

/-- The model with weight `u` on *dans* or *en* and `v` on *dans* or *à*. -/
noncomputable abbrev expModel (u v : ℝ) : Measure Phrase :=
  Measure.count.tilted fun φ ↦ u * dansOrEn φ + v * dansOrÀ φ

-- the model giving *en*, *à* and each of the other two phrases the probabilities `e`, `a`, `c`
-- gives *dans* the `d` with `d * c = e * a`
theorem expModel_real_singleton {d e a c : ℝ} (he : 0 < e) (ha : 0 < a) (hc : 0 < c)
    (hR : e * a = d * c) (hN : d + e + a + 2 * c = 1) (φ : Phrase) :
    (expModel (log (e / c)) (log (a / c))).real {φ} =
      match φ with
      | dans => d
      | en => e
      | à => a
      | auCoursDe | pendant => c := by
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
  rw [count_tilted_real_singleton, softmax_apply, hZ]
  cases φ <;>
    simp only [dansOrEn, dansOrÀ, mul_one, mul_zero, add_zero, zero_add, exp_zero, hd,
      exp_log (div_pos he hc), exp_log (div_pos ha hc)] <;> field_simp

theorem integral_expModel (u v : ℝ) (q : Measure Phrase) [IsFiniteMeasure q] :
    ∫ φ, u * dansOrEn φ + v * dansOrÀ φ ∂q =
      u * (q.real {dans} + q.real {en}) + v * (q.real {dans} + q.real {à}) := by
  rw [integral_eq]
  simp only [dansOrEn, dansOrÀ]
  ring

/-- The model maximizing entropy subject to `p(dans) + p(en) = 3/10`. -/
noncomputable abbrev twoModel : Measure Phrase := expModel (log (9 / 14)) 0

theorem twoModel_real_singleton (φ : Phrase) :
    twoModel.real {φ} = match φ with
      | dans | en => 3 / 20
      | _ => 7 / 30 := by
  have h := expModel_real_singleton (d := 3 / 20) (e := 3 / 20) (a := 7 / 30) (c := 7 / 30)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) φ
  rw [show (3 / 20 : ℝ) / (7 / 30) = 9 / 14 by norm_num, div_self (by norm_num), log_one] at h
  rw [h]
  cases φ <;> rfl

-- p. 41, the second model
theorem isGreatest_two :
    IsGreatest (measureEntropy '' {q : Measure Phrase | IsProbabilityMeasure q ∧
      q.real {dans} + q.real {en} = 3 / 10}) (Hm[twoModel]) := by
  have h2 : twoModel.real {dans} + twoModel.real {en} = 3 / 10 := by
    rw [twoModel_real_singleton, twoModel_real_singleton]; norm_num
  refine ⟨⟨_, ⟨inferInstance, h2⟩, rfl⟩, ?_⟩
  rintro _ ⟨q, ⟨hq, h⟩, rfl⟩
  refine measureEntropy_le_measureEntropy_count_tilted ?_
  rw [integral_expModel, integral_expModel, h, h2]
  simp

/-- The model maximizing entropy subject to all three constraints. -/
noncomputable abbrev threeModel : Measure Phrase :=
  expModel (log (((√51 - 6) / 10) / ((11 - √51) / 20)))
    (log (((√51 - 4) / 10) / ((11 - √51) / 20)))

theorem threeModel_real_singleton (φ : Phrase) :
    threeModel.real {φ} = match φ with
      | dans => (9 - √51) / 10
      | en => (√51 - 6) / 10
      | à => (√51 - 4) / 10
      | auCoursDe | pendant => (11 - √51) / 20 := by
  have hs : √51 ^ 2 = 51 := sq_sqrt (by norm_num)
  have h7 : 7 < √51 := lt_sqrt (by norm_num) |>.2 (by norm_num)
  have h8 : √51 < 8 := (sqrt_lt' (by norm_num)).2 (by norm_num)
  exact expModel_real_singleton (by linarith) (by linarith) (by linarith)
    (by linear_combination hs / 200) (by ring) φ

/-- Requiring `p(dans) + p(en) = 3/10` and `p(dans) + p(à) = 1/2`, the most uniform model is the
exponential one giving *dans* the probability `(9 − √51)/10`, the solution §3.4 leaves to the
reader. -/
theorem isGreatest_three :
    IsGreatest (measureEntropy '' {q : Measure Phrase | IsProbabilityMeasure q ∧
      q.real {dans} + q.real {en} = 3 / 10 ∧ q.real {dans} + q.real {à} = 1 / 2})
      (Hm[threeModel]) := by
  have h2 : threeModel.real {dans} + threeModel.real {en} = 3 / 10 := by
    rw [threeModel_real_singleton, threeModel_real_singleton]; ring
  have h3 : threeModel.real {dans} + threeModel.real {à} = 1 / 2 := by
    rw [threeModel_real_singleton, threeModel_real_singleton]; ring
  refine ⟨⟨_, ⟨inferInstance, h2, h3⟩, rfl⟩, ?_⟩
  rintro _ ⟨q, ⟨hq, h, h'⟩, rfl⟩
  refine measureEntropy_le_measureEntropy_count_tilted ?_
  rw [integral_expModel, integral_expModel, h, h', h2, h3]

/-! ### Maximum entropy modeling -/

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

-- (10)
theorem model_apply (θ : ι → ℝ) (x : X) :
    model f θ x = Measure.count.tilted fun y ↦ θ ⬝ᵥ f (x, y) :=
  congrArg Measure.count.tilted (funext fun y ↦ by simp [harmony])

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

-- (9), (11), (14)
theorem lagrangian_model_eq_neg_logLik (θ : ι → ℝ) :
    lagrangian f p (model f θ) θ = -logLik p (model f θ) := by
  have h := condEntropy_condMaxEnt f (-θ) p.fst
  rw [logLik_model, condLogLikelihood_eq]
  simp only [lagrangian, model, dotProduct_sub, neg_dotProduct] at h ⊢
  linarith

/-- Weak duality: a model satisfying the constraints has entropy at most minus the log-likelihood
of each exponential model. -/
theorem condEntropy_le_neg_logLik (θ : ι → ℝ) {q : Kernel X Y} (hq : q ∈ constraints f p) :
    H[Prod.snd | Prod.fst ; p.fst ⊗ₘ q] ≤ -logLik p (model f θ) := by
  have := hq.1
  have h := lagrangian_le_lagrangian_model f p θ q
  rw [lagrangian_model_eq_neg_logLik] at h
  simpa [lagrangian, hq.2] using h

variable {f p} {θ : ι → ℝ}

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

-- §3.6
theorem concaveOn_logLik_model : ConcaveOn ℝ Set.univ fun θ ↦ logLik p (model f θ) := by
  simpa [Function.comp_def, logLik_model] using
    (concaveOn_condLogLikelihood f p).comp_linearMap (-LinearMap.id)

end Modeling

end BergerDellaPietraDellaPietra1996
