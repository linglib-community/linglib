module

public import Linglib.Phonology.HarmonicGrammar.MaxEnt

/-!
# Berger, Della Pietra and Della Pietra (1996): A Maximum Entropy Approach to Natural Language Processing

The paper models a process that produces an output $y$ in a context $x$, from a sample with
empirical distribution $\tilde p$. Among the conditional models under which each feature
$f(x, y)$ has its sample mean, the maximum entropy principle selects the one of greatest
conditional entropy. For fixed multipliers $\lambda$ the Lagrangian of this problem [is greatest
at](##lagrangian_le_lagrangian_model) the exponential model $p_\lambda(y \mid x) \propto
\exp(\lambda \cdot f(x, y))$. Hence every model satisfying the constraints [has entropy at
most](##condEntropy_le_neg_logLik) minus the log-likelihood of each $p_\lambda$. The $p_\lambda$
of greatest likelihood [is the maximum entropy model](##isGreatest_condEntropy_model), and [the
only one](##eq_model_of_condEntropy_eq) at the contexts in the sample. In the opening example,
which translates English *in* into five French phrases under two constraints, [the
solution](##isGreatest_three) that the paper leaves to the reader
[has](##threeModel_real_singleton) $p(\textit{dans}) = (9 - \sqrt{51})/10$.

## Implementation notes

* Features are real-valued, `f : X × Y → ι → ℝ`; in the paper they are binary.
* The exponential model with multipliers `λ` is the softmax kernel of `λ ⬝ᵥ f (x, y)`, which [at
  each context](##model_apply) is the counting measure tilted by `λ ⬝ᵥ f (x, ·)`. It
  [is](##model_eq_condMaxEnt) `HarmonicGrammar.condMaxEnt f (-λ)`, harmony being minus the
  weighted statistic; only the statements about the weights of greatest likelihood use that
  identification.
* The conditional entropy of a model `q` is `H[Prod.snd | Prod.fst ; p̃.fst ⊗ₘ q]`, the entropy
  of the output given the context under the joint distribution `p̃(x) q(y | x)`.
* The Lagrangian is the entropy plus each multiplier times the violation of its constraint, as
  in the paper. Its value at the maximizer [is](##lagrangian_model_eq_neg_logLik) `-L(p_λ)`. The
  paper's dual function is `L(p_λ)`, which it maximizes; minimizing `-L(p_λ)` is the same
  problem.
* The maximum entropy model is determined only at the contexts of positive empirical mass.
* In the example a model is a distribution of the five phrases, the counting measure tilted by
  the weighted features.

## TODO

* The case of the paper's second footnote: when no `λ` has greatest likelihood, the maximum
  entropy model is a limit of the models `p_λ`.
* Improved iterative scaling, feature selection, and the applications.

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

/-- The exponential model of the phrases with multiplier `u` for *dans* or *en* and `v` for
*dans* or *à*. -/
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

/-- The maximum entropy model under the constraint `p(dans) + p(en) = 3/10`. -/
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

/-- The maximum entropy model under the constraints `p(dans) + p(en) = 3/10` and
`p(dans) + p(à) = 1/2`. -/
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

/-- Among the distributions of the phrases with `p(dans) + p(en) = 3/10` and
`p(dans) + p(à) = 1/2`, the exponential model `threeModel` has the greatest entropy. This is the
exercise of §3.4; the model gives *dans* the probability `(9 − √51)/10`. -/
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
  [MeasurableSpace Y] [Fintype Y] [MeasurableSingletonClass Y] [Fintype ι] (f : X × Y → ι → ℝ)
  (p : Measure (X × Y))

/-- The set `C` of (4): the conditional models under which each feature has the same expected
value, with contexts drawn from the sample, as in the sample. -/
def constraints : Set (Kernel X Y) :=
  {q | IsMarkovKernel q ∧ ∫ z, f z ∂(p.fst ⊗ₘ q) = ∫ z, f z ∂p}

/-- The exponential model `p_λ` of (10), the softmax kernel of the weighted features. The
multipliers are written `θ`. -/
noncomputable def model (θ : ι → ℝ) : Kernel X Y :=
  Kernel.softmax fun x y ↦ ((θ ⬝ᵥ f (x, y) : ℝ) : EReal)

instance [Nonempty Y] (θ : ι → ℝ) : IsMarkovKernel (model f θ) :=
  inferInstanceAs (IsMarkovKernel (Kernel.softmax fun x y ↦ ((θ ⬝ᵥ f (x, y) : ℝ) : EReal)))

-- (10)
theorem model_apply [Nonempty Y] (θ : ι → ℝ) (x : X) :
    model f θ x = Measure.count.tilted fun y ↦ θ ⬝ᵥ f (x, y) :=
  Kernel.softmax_coe_eq_count_tilted _ x

omit [MeasurableSingletonClass Y] in
theorem model_eq_condMaxEnt (θ : ι → ℝ) : model f θ = condMaxEnt f (-θ) := by
  simp [model, condMaxEnt, harmony]

/-- The Lagrangian (7): the conditional entropy (5) of the model plus, for each feature, its
multiplier times the difference between the model's and the sample's expected value. -/
noncomputable def lagrangian (q : Kernel X Y) (θ : ι → ℝ) : ℝ :=
  H[Prod.snd | Prod.fst ; p.fst ⊗ₘ q] + θ ⬝ᵥ ((∫ z, f z ∂(p.fst ⊗ₘ q)) - ∫ z, f z ∂p)

/-- The log-likelihood (13) of the sample under a conditional model. -/
noncomputable def logLik (q : Kernel X Y) : ℝ :=
  ∫ z, log ((q z.1).real {z.2}) ∂p

omit [MeasurableSingletonClass Y] in
theorem logLik_model (θ : ι → ℝ) : logLik p (model f θ) = condLogLikelihood f p (-θ) := by
  rw [logLik, model_eq_condMaxEnt, condLogLikelihood]

omit [MeasurableSingletonClass Y] in
private theorem isMaxOn_condLogLikelihood_neg {θ : ι → ℝ}
    (h : IsMaxOn (fun θ ↦ logLik p (model f θ)) Set.univ θ) :
    IsMaxOn (condLogLikelihood f p) Set.univ (-θ) :=
  isMaxOn_iff.2 fun w _ ↦ by simpa [logLik_model] using h (Set.mem_univ (-w))

private theorem integral_dotProduct (θ : ι → ℝ) (μ : Measure (X × Y)) [IsFiniteMeasure μ] :
    ∫ z, θ ⬝ᵥ f (z.1, z.2) ∂μ = θ ⬝ᵥ ∫ z, f z ∂μ := by
  rw [integral_fintype .of_finite, integral_fintype .of_finite]
  simp [dotProduct_sum, dotProduct_smul]

variable [Nonempty Y] [IsProbabilityMeasure p]

/-- For fixed multipliers, the Lagrangian is greatest at the exponential model: (8) and (10). -/
theorem lagrangian_le_lagrangian_model (θ : ι → ℝ) (q : Kernel X Y) [IsMarkovKernel q] :
    lagrangian f p q θ ≤ lagrangian f p (model f θ) θ := by
  have h₁ := sum_toReal_klDiv_softmax_add_condEntropy (fun x y ↦ θ ⬝ᵥ f (x, y)) p.fst q
  have h₂ := condEntropy_softmax (fun x y ↦ θ ⬝ᵥ f (x, y)) p.fst
  have h₃ : 0 ≤ ∑ x, p.fst.real {x} * (klDiv (q x) (model f θ x)).toReal :=
    sum_nonneg fun x _ ↦ mul_nonneg measureReal_nonneg ENNReal.toReal_nonneg
  rw [integral_dotProduct] at h₁ h₂
  simp only [lagrangian, model, dotProduct_sub] at h₃ ⊢
  linarith

-- (9), (11), (14)
theorem lagrangian_model_eq_neg_logLik (θ : ι → ℝ) :
    lagrangian f p (model f θ) θ = -logLik p (model f θ) := by
  have h₁ := condEntropy_softmax (fun x y ↦ θ ⬝ᵥ f (x, y)) p.fst
  have h₂ := integral_log_softmax_real_singleton (fun x y ↦ θ ⬝ᵥ f (x, y)) p
  rw [integral_dotProduct] at h₁ h₂
  simp only [lagrangian, logLik, model, dotProduct_sub]
  linarith

/-- **Weak duality**: if `q` satisfies the constraints, then for every `θ` its conditional entropy
is at most minus the log-likelihood of the exponential model `p_θ`. -/
theorem condEntropy_le_neg_logLik (θ : ι → ℝ) {q : Kernel X Y} (hq : q ∈ constraints f p) :
    H[Prod.snd | Prod.fst ; p.fst ⊗ₘ q] ≤ -logLik p (model f θ) := by
  have := hq.1
  have h := lagrangian_le_lagrangian_model f p θ q
  rw [lagrangian_model_eq_neg_logLik] at h
  simpa [lagrangian, hq.2] using h

variable {f p} {θ : ι → ℝ}

theorem model_mem_constraints (h : IsMaxOn (fun θ ↦ logLik p (model f θ)) Set.univ θ) :
    model f θ ∈ constraints f p :=
  ⟨inferInstance, model_eq_condMaxEnt f θ ▸
    (isMaxOn_condLogLikelihood_iff f (-θ) p).1 (isMaxOn_condLogLikelihood_neg f p h)⟩

/-- **Maximum entropy is maximum likelihood** (§3.5): if `θ` maximizes the likelihood of the
sample among the exponential models, then `p_θ` has the greatest conditional entropy in `C`. -/
theorem isGreatest_condEntropy_model (h : IsMaxOn (fun θ ↦ logLik p (model f θ)) Set.univ θ) :
    IsGreatest ((fun q : Kernel X Y ↦ H[Prod.snd | Prod.fst ; p.fst ⊗ₘ q]) '' constraints f p)
      (H[Prod.snd | Prod.fst ; p.fst ⊗ₘ model f θ]) :=
  ⟨⟨_, model_mem_constraints h, rfl⟩, by
    rintro _ ⟨q, hq, rfl⟩
    have := lagrangian_model_eq_neg_logLik f p θ
    simp only [lagrangian, (model_mem_constraints h).2, sub_self, dotProduct_zero,
      add_zero] at this
    exact this ▸ condEntropy_le_neg_logLik f p θ hq⟩

theorem condEntropy_model_eq_neg_logLik
    (h : IsMaxOn (fun θ ↦ logLik p (model f θ)) Set.univ θ) :
    H[Prod.snd | Prod.fst ; p.fst ⊗ₘ model f θ] = -logLik p (model f θ) := by
  simpa [lagrangian, (model_mem_constraints h).2] using lagrangian_model_eq_neg_logLik f p θ

/-- **Uniqueness**: if `θ` maximizes the likelihood and `q ∈ C` has the conditional entropy of
`p_θ`, then `q` agrees with `p_θ` at every context that occurs in the sample. -/
theorem eq_model_of_condEntropy_eq (h : IsMaxOn (fun θ ↦ logLik p (model f θ)) Set.univ θ)
    {q : Kernel X Y} (hq : q ∈ constraints f p)
    (hH : H[Prod.snd | Prod.fst ; p.fst ⊗ₘ q] = H[Prod.snd | Prod.fst ; p.fst ⊗ₘ model f θ])
    {x : X} (hx : p.fst {x} ≠ 0) : q x = model f θ x := by
  have := hq.1
  refine eq_softmax_of_condEntropy_eq ?_ hH hx
  rw [integral_dotProduct, integral_dotProduct, hq.2]
  exact congrArg _ (model_mem_constraints h).2.symm

variable (f p)

-- §3.6
theorem concaveOn_logLik_model : ConcaveOn ℝ Set.univ fun θ ↦ logLik p (model f θ) := by
  simpa [Function.comp_def, logLik_model] using
    (concaveOn_condLogLikelihood f p).comp_linearMap (-LinearMap.id)

end Modeling

end BergerDellaPietraDellaPietra1996
