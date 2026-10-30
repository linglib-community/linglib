module

public import Linglib.Core.Order.Argmax
public import Linglib.Core.Probability.Kernel.Composition.Lemmas
public import Linglib.Core.Probability.Kernel.Posterior
public import Linglib.Core.Probability.UniformOn
public import Linglib.Core.MeasureTheory.Measure.Dirac

/-!
# Griffiths and Kalish (2007): Language Evolution by Iterated Learning With Bayesian Agents

With a production kernel $\kappa$ and a learning kernel $L$, the languages of successive learners
form a Markov chain with transition $L \circ \kappa$. Learners who sample from the posterior under
a prior $\mu$ [keep the prior stationary](##ProbabilityTheory.invariant_posterior_comp). Between
two languages with noisy production, learners who take a language of greatest posterior mass have
[one stationary distribution, the same for every bias the model
allows](##invariant_mapLearner_comp_produce_iff), so they [keep the prior only when it already has
that value](##invariant_mapLearner_comp_produce_prior_iff), and their chain [converges to that
distribution](##tendsto_pow_comp_real_one) from any start.

## Implementation notes

* Stationarity is mathlib's `Kernel.Invariant`; the chains are compositions of kernels, so they get
  no definitions. The sampling results hold for any likelihood on a standard Borel space of
  languages, as the paper's first note says finiteness is not necessary, so they live with the
  posterior in `Linglib/Core/Probability/Kernel/Posterior.lean`. There the sampler also keeps the
  data at the prior predictive (`ProbabilityTheory.invariant_comp_posterior`) and, as a Gibbs
  sampler, the joint (`ProbabilityTheory.invariant_id_prod_comp_prodMkLeft_posterior`).
* The sampling learner is mathlib's posterior `κ†μ`, which is fixed only up to a null set of data.
  `ProbabilityTheory.invariant_comp_of_ae_eq_posterior` therefore takes any learner that agrees
  with it on the data the prior predicts.
* The MAP learner (eq. (41)) chooses uniformly among tied languages. On a datum no language
  produces, every language ties.
* In the two-language model the parameters are real: the prior `α` of `L₁`, the production noise
  `ε`, and the agreement `s`, the mass of the objects on which the languages agree. The paper's
  conditions `α > 1/2` and `ε < 1 - α` already give `ε < 1/2`. The characterization of the MAP
  chain's stationary distribution assumes `0 < ε`, which makes `q₁₂ + q₂₁ = s + 2 (1 - s) ε`
  positive.

## Errata

* The display for `q₂₁` under MAP estimation (§5.2) is `R(ε(1-α)/(ε(1-α)+(1-ε)α))(1-s)(1-ε)`, the
  chance of moving to `L₂` on data favouring `L₁`. Since `ε < 1/2 < α` its argument is below `1/2`,
  so it gives `q₂₁ = 0`, against Table 1. The data favouring `L₂` have chance `(1-s)ε` and move the
  learner to `L₂` exactly when `ε < 1 - α`, which gives Table 1's
  [`(1-s)ε`](##mapLearner_comp_real_one_two).
* The first denominator of eq. (38) prints `εp` for `εα`.

## TODO

* Eq. (8), convergence of an ergodic finite chain to its stationary distribution from any start,
  is imported by the paper from Markov chain theory. Mathlib has `Kernel.IsIrreducible` and
  `Matrix.IsPrimitive` but no Perron–Frobenius or Doeblin convergence theorem for finite Markov
  kernels; once it does, the sampler's convergence to the prior follows. Here only the two-state
  case is proved.
* §6's compositionality simulations (eqs. (44)–(45)) and §7's population dynamics are not
  formalized.

## References

* [griffiths-kalish-2007]
-/

@[expose] public section

namespace GriffithsKalish2007

open MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal Topology

/-! ### The MAP learner -/

section MAP

variable {H D : Type*} [MeasurableSpace H] [MeasurableSpace D] [Fintype H] [Countable D]
  [MeasurableSingletonClass D]

/-- Eq. (41): the MAP learner chooses uniformly among the languages that maximize prior times
likelihood. -/
noncomputable def mapLearner (κ : Kernel H D) (μ : Measure H) : Kernel D H :=
  Kernel.ofFunOfCountable fun d ↦ uniformOn ↑(univ.argmax fun h ↦ μ {h} * κ h {d})

theorem mapLearner_apply (κ : Kernel H D) (μ : Measure H) (d : D) :
    mapLearner κ μ d = uniformOn ↑(univ.argmax fun h ↦ μ {h} * κ h {d}) := rfl

instance [MeasurableSingletonClass H] [Nonempty H] (κ : Kernel H D) (μ : Measure H) :
    IsMarkovKernel (mapLearner κ μ) :=
  ⟨fun _ ↦ isProbabilityMeasure_uniformOn (finite_toSet _)
    (coe_nonempty.2 (argmax_nonempty univ_nonempty))⟩

end MAP

/-! ### Two languages -/

/-- The two languages `L₁` and `L₂` of §2.3. -/
inductive Language
  | one
  | two
  deriving DecidableEq, Fintype, Inhabited

namespace Language

instance : MeasurableSpace Language := ⊤

instance : DiscreteMeasurableSpace Language := ⟨fun _ ↦ trivial⟩

theorem univ_eq : (univ : Finset Language) = {one, two} := by decide

theorem argmax_eq (v : Language → ℝ≥0∞) :
    univ.argmax v = if v two < v one then {one} else if v one < v two then {two} else univ := by
  ext i
  simp only [mem_argmax, univ_eq, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
  split_ifs with h₁ h₂
  · cases i <;> simp [h₁.le, not_le.2 h₁]
  · cases i <;> simp [h₂.le, not_le.2 h₂]
  · cases i <;> simp [not_lt.1 h₁, not_lt.1 h₂]

theorem real_one_add_real_two (ρ : Measure Language) [IsProbabilityMeasure ρ] :
    ρ.real {one} + ρ.real {two} = 1 :=
  measureReal_singleton_add_singleton_of_pair ρ (by decide) fun i _ ↦ by cases i <;> simp

theorem real_two_eq_one_sub (ρ : Measure Language) [IsProbabilityMeasure ρ] :
    ρ.real {two} = 1 - ρ.real {one} := by
  linarith [real_one_add_real_two ρ]

theorem ext_of_real_one {ρ ν : Measure Language} [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν]
    (h : ρ.real {one} = ν.real {one}) : ρ = ν := by
  have h₂ : ρ.real {two} = ν.real {two} := by rw [real_two_eq_one_sub, real_two_eq_one_sub, h]
  refine Measure.ext_of_singleton fun i ↦ ?_
  cases i
  · exact (measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _)).1 h
  · exact (measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _)).1 h₂

/-! #### Two-state chains

A Markov kernel `Q` on the two languages is fixed by `q₁₂ = Q two {one}` and
`q₂₁ = Q one {two}`, the paper's notation for the chance of moving to the first index from the
second. -/

variable (Q : Kernel Language Language) [IsMarkovKernel Q] (ν : Measure Language)
  [IsProbabilityMeasure ν]

theorem comp_real_one :
    (Q ∘ₘ ν).real {one} =
      (Q two).real {one} + (1 - (Q two).real {one} - (Q one).real {two}) * ν.real {one} := by
  rw [Measure.comp_real_singleton, univ_eq, sum_pair (by decide), real_two_eq_one_sub ν,
    show (Q one).real {one} = 1 - (Q one).real {two} by linarith [real_one_add_real_two (Q one)]]
  ring

-- Eq. (13): detailed balance at the two atoms, the two-state case of mathlib's
-- `Kernel.IsReversible`.
theorem invariant_iff :
    Q.Invariant ν ↔ ν.real {one} * (Q one).real {two} = ν.real {two} * (Q two).real {one} := by
  rw [real_two_eq_one_sub ν]
  refine ⟨fun h ↦ ?_, fun h ↦ ext_of_real_one ?_⟩
  · have := comp_real_one Q ν
    rw [h.def] at this
    linarith
  · rw [comp_real_one]
    linarith

-- Eq. (14)
theorem real_one_eq_of_invariant (h : Q.Invariant ν)
    (h₀ : (Q two).real {one} + (Q one).real {two} ≠ 0) :
    ν.real {one} = (Q two).real {one} / ((Q two).real {one} + (Q one).real {two}) := by
  rw [eq_div_iff h₀]
  have := (invariant_iff Q ν).1 h
  rw [real_two_eq_one_sub ν] at this
  linarith

-- Eq. (15): the distance to the stationary probability shrinks by `λ₂ = 1 - q₁₂ - q₂₁` per step.
theorem pow_comp_real_one_sub (n : ℕ) (h₀ : (Q two).real {one} + (Q one).real {two} ≠ 0) :
    ((Q ^ n) ∘ₘ ν).real {one} - (Q two).real {one} / ((Q two).real {one} + (Q one).real {two}) =
      (1 - (Q two).real {one} - (Q one).real {two}) ^ n *
        (ν.real {one} - (Q two).real {one} / ((Q two).real {one} + (Q one).real {two})) := by
  induction n with
  | zero =>
    rw [pow_zero, Kernel.one_def, Measure.id_comp]
    simp
  | succ n ih =>
    rw [pow_succ', Kernel.mul_def, ← Measure.comp_assoc, comp_real_one, pow_succ,
      mul_comm (_ ^ n), mul_assoc, ← ih]
    field_simp
    ring

/-- Eqs. (14)–(15): a two-state chain whose second eigenvalue `1 - q₁₂ - q₂₁` has modulus below
one converges, from any start, to the stationary probability `q₁₂ / (q₁₂ + q₂₁)` of the first
state. -/
theorem tendsto_pow_comp_real_one (h₀ : 0 < (Q two).real {one} + (Q one).real {two})
    (h₂ : (Q two).real {one} + (Q one).real {two} < 2) :
    Tendsto (fun n : ℕ ↦ ((Q ^ n) ∘ₘ ν).real {one}) atTop
      (𝓝 ((Q two).real {one} / ((Q two).real {one} + (Q one).real {two}))) := by
  have h := ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one
    (r := 1 - (Q two).real {one} - (Q one).real {two})
    (abs_lt.2 ⟨by linarith, by linarith⟩)).mul_const
      (ν.real {one} - (Q two).real {one} / ((Q two).real {one} + (Q one).real {two}))).add_const
      ((Q two).real {one} / ((Q two).real {one} + (Q one).real {two}))
  rw [zero_mul, zero_add] at h
  refine h.congr fun n ↦ ?_
  rw [← pow_comp_real_one_sub Q ν n h₀.ne']
  ring

end Language

open Language

/-! #### The two-language model

The learners see one object `x`, drawn from `P` whatever the language, and whether it elicits the
utterance (`y`). Language `i` elicits the utterance on the objects of `G i`, and a speaker answers
correctly with chance `1 - ε`. -/

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
  (P : Measure X) (G : Language → Set X) [∀ i, DecidablePred (· ∈ G i)] (ε : ℝ)

/-- Eq. (20): the production kernel of the two-language model. -/
noncomputable def produce : Kernel Language (X × Bool) :=
  Kernel.ofFunOfCountable fun i ↦ Measure.ofRealWeights fun d ↦
    P.real {d.1} * if d.2 = decide (d.1 ∈ G i) then 1 - ε else ε

/-- §3.2: the prior gives `L₁` probability `α`. -/
noncomputable def prior (α : ℝ) : Measure Language :=
  Measure.ofRealWeights fun | .one => α | .two => 1 - α

instance (i : Language) : IsFiniteMeasure (produce P G ε i) :=
  inferInstanceAs (IsFiniteMeasure (Measure.ofRealWeights _))

instance : IsFiniteKernel (produce P G ε) :=
  ⟨⟨∑ i, produce P G ε i Set.univ, ENNReal.sum_lt_top.2 fun _ _ ↦ measure_lt_top _ _,
    fun i ↦ single_le_sum (f := fun i ↦ produce P G ε i Set.univ) (fun _ _ ↦ zero_le)
      (mem_univ i)⟩⟩

instance (α : ℝ) : IsFiniteMeasure (prior α) :=
  inferInstanceAs (IsFiniteMeasure (Measure.ofRealWeights _))

theorem produce_apply_singleton (i : Language) (d : X × Bool) :
    produce P G ε i {d} =
      ENNReal.ofReal (P.real {d.1} * if d.2 = decide (d.1 ∈ G i) then 1 - ε else ε) :=
  Measure.ofWeights_apply_singleton _ _

theorem isMarkovKernel_produce [IsProbabilityMeasure P] (h₀ : 0 ≤ ε) (h₁ : ε ≤ 1) :
    IsMarkovKernel (produce P G ε) := by
  refine ⟨fun i ↦ Measure.isProbabilityMeasure_ofRealWeights
    (fun d ↦ mul_nonneg measureReal_nonneg (by split_ifs <;> linarith)) ?_⟩
  have (x : X) : (P.real {x} * if true = decide (x ∈ G i) then 1 - ε else ε) +
      (P.real {x} * if false = decide (x ∈ G i) then 1 - ε else ε) = P.real {x} := by
    by_cases h : x ∈ G i <;> simp [h, ← mul_add]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_bool, this]
  rw [sum_measureReal_singleton, coe_univ, probReal_univ]

theorem prior_apply_singleton (α : ℝ) (i : Language) :
    prior α {i} = ENNReal.ofReal (match i with | .one => α | .two => 1 - α) :=
  Measure.ofWeights_apply_singleton _ _

theorem isProbabilityMeasure_prior {α : ℝ} (h₀ : 0 ≤ α) (h₁ : α ≤ 1) :
    IsProbabilityMeasure (prior α) :=
  Measure.isProbabilityMeasure_ofRealWeights (fun i ↦ by cases i <;> dsimp <;> linarith)
    (by simp [univ_eq])

theorem prior_real_one {α : ℝ} (h : 0 ≤ α) : (prior α).real {one} = α := by
  rw [measureReal_def, prior_apply_singleton]
  exact ENNReal.toReal_ofReal h

theorem prior_real_two {α : ℝ} (h : α ≤ 1) : (prior α).real {two} = 1 - α := by
  rw [measureReal_def, prior_apply_singleton]
  exact ENNReal.toReal_ofReal (sub_nonneg.2 h)

theorem prior_inj {α α' : ℝ} (h : 0 ≤ α) (h' : 0 ≤ α') : prior α = prior α' ↔ α = α' :=
  ⟨fun he ↦ by rw [← prior_real_one h, ← prior_real_one h', he], congrArg prior⟩

variable {P G ε}

theorem produce_real_singleton (h₀ : 0 ≤ ε) (h₁ : ε ≤ 1) (i : Language) (d : X × Bool) :
    (produce P G ε i).real {d} = P.real {d.1} * if d.2 = decide (d.1 ∈ G i) then 1 - ε else ε :=
  Measure.ofRealWeights_real_singleton
    (fun d ↦ mul_nonneg measureReal_nonneg (by split_ifs <;> linarith)) d

/-! #### MAP estimation with two languages -/

-- Which language has the greater weight at a datum does not depend on `α` in the range
-- `1/2 < α < 1 - ε`: it is the comparison of the likelihoods `p w₁` and `p w₂`.
private theorem cmp_iff {α ε p w₁ w₂ : ℝ} (hα : 1 / 2 < α) (hαε : ε < 1 - α) (hε : 0 ≤ ε)
    (hp : 0 ≤ p) (hw₁ : w₁ = 1 - ε ∨ w₁ = ε) (hw₂ : w₂ = 1 - ε ∨ w₂ = ε) :
    ((1 - α) * (p * w₂) < α * (p * w₁) ∧ 0 < α * (p * w₁) ↔ p * w₂ ≤ p * w₁ ∧ 0 < p * w₁) ∧
      (α * (p * w₁) < (1 - α) * (p * w₂) ∧ 0 < (1 - α) * (p * w₂) ↔ p * w₁ < p * w₂) := by
  have h₁ : ε < 1 - ε := by linarith
  have h₂ : 0 < α - ε := by linarith
  refine ⟨⟨fun ⟨h, h'⟩ ↦ ⟨?_, ?_⟩, fun ⟨h, h'⟩ ↦ ⟨?_, ?_⟩⟩,
    ⟨fun ⟨h, h'⟩ ↦ ?_, fun h ↦ ⟨?_, ?_⟩⟩⟩ <;>
    rcases hw₁ with rfl | rfl <;> rcases hw₂ with rfl | rfl <;> nlinarith

private theorem ite_eq_or (ε : ℝ) (c : Prop) [Decidable c] :
    (if c then 1 - ε else ε) = 1 - ε ∨ (if c then 1 - ε else ε) = ε := by
  split_ifs <;> simp

-- §5.2: the MAP choice at each datum, in a form free of `α`.
theorem argmax_prior_mul_produce {α : ℝ} (hα : 1 / 2 < α) (hαε : ε < 1 - α) (hε : 0 ≤ ε)
    (d : X × Bool) :
    univ.argmax (fun i ↦ prior α {i} * produce P G ε i {d}) =
      if (produce P G ε two).real {d} ≤ (produce P G ε one).real {d} ∧
          0 < (produce P G ε one).real {d} then {one}
      else if (produce P G ε one).real {d} < (produce P G ε two).real {d} then {two}
      else univ := by
  obtain ⟨hA, hB⟩ := cmp_iff hα hαε hε (measureReal_nonneg (μ := P) (s := {d.1}))
    (ite_eq_or ε (d.2 = decide (d.1 ∈ G one))) (ite_eq_or ε (d.2 = decide (d.1 ∈ G two)))
  rw [Language.argmax_eq, produce_real_singleton hε (by linarith),
    produce_real_singleton hε (by linarith)]
  simp only [prior_apply_singleton, produce_apply_singleton,
    ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ α by linarith),
    ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1 - α by linarith), ENNReal.ofReal_lt_ofReal_iff', hA, hB]

-- Table 1: the MAP learner is the same for every prior with `1/2 < α < 1 - ε`.
theorem mapLearner_prior_eq {α α' : ℝ} (hα : 1 / 2 < α) (hα' : 1 / 2 < α') (hαε : ε < 1 - α)
    (hα'ε : ε < 1 - α') (hε : 0 ≤ ε) :
    mapLearner (produce P G ε) (prior α) = mapLearner (produce P G ε) (prior α') :=
  Kernel.ext fun d ↦ by
    rw [mapLearner_apply, mapLearner_apply, argmax_prior_mul_produce hα hαε hε,
      argmax_prior_mul_produce hα' hα'ε hε]

-- At a datum either language produces, the MAP learner takes the language of greater likelihood,
-- `L₁` on ties; a datum neither language produces does not count.
private theorem mul_uniformOn_real {l₁ l₂ l : ℝ} (h₁ : 0 ≤ l₁) (h₂ : 0 ≤ l₂) (hl : l = l₁ ∨ l = l₂)
    (k : Language) :
    l * (uniformOn ↑(if l₂ ≤ l₁ ∧ 0 < l₁ then {one} else if l₁ < l₂ then {two} else
      (univ : Finset Language))).real {k} = l * if (l₁ < l₂ ↔ k = two) then 1 else 0 := by
  rw [uniformOn_finset_real_singleton]
  by_cases hA : l₂ ≤ l₁ ∧ 0 < l₁
  · cases k <;> simp [hA, not_lt.2 hA.1]
  by_cases hB : l₁ < l₂
  · cases k <;> simp [hA, hB]
  have hl₁ : l₁ = 0 := le_antisymm (not_lt.1 fun h ↦ hA ⟨not_lt.1 hB, h⟩) h₁
  have hl₂ : l₂ = 0 := le_antisymm ((not_lt.1 hB).trans hl₁.le) h₂
  rcases hl with rfl | rfl <;> simp [hl₁, hl₂]

private theorem mul_uniformOn_real_two {l₁ l₂ l : ℝ} (h₁ : 0 ≤ l₁) (h₂ : 0 ≤ l₂)
    (hl : l = l₁ ∨ l = l₂) :
    l * (uniformOn ↑(if l₂ ≤ l₁ ∧ 0 < l₁ then {one} else if l₁ < l₂ then {two} else
      (univ : Finset Language))).real {two} = l * if l₁ < l₂ then 1 else 0 := by
  simpa using mul_uniformOn_real h₁ h₂ hl two

private theorem mul_uniformOn_real_one {l₁ l₂ l : ℝ} (h₁ : 0 ≤ l₁) (h₂ : 0 ≤ l₂)
    (hl : l = l₁ ∨ l = l₂) :
    l * (uniformOn ↑(if l₂ ≤ l₁ ∧ 0 < l₁ then {one} else if l₁ < l₂ then {two} else
      (univ : Finset Language))).real {one} = l * if l₂ ≤ l₁ then 1 else 0 := by
  simpa using mul_uniformOn_real h₁ h₂ hl one

private theorem sum_q₂₁ {ε p : ℝ} (hε : 0 ≤ ε) (hε' : ε < 1 / 2) (hp : 0 ≤ p) (b₁ b₂ : Bool) :
    ∑ y : Bool, (p * if y = b₁ then 1 - ε else ε) *
      (if (p * if y = b₁ then 1 - ε else ε) < p * if y = b₂ then 1 - ε else ε then 1 else 0) =
      p * if b₁ = b₂ then 0 else ε := by
  cases b₁ <;> cases b₂ <;> simp only [Fintype.sum_bool, Bool.true_eq_false, Bool.false_eq_true,
    ite_true, ite_false, lt_irrefl, mul_zero, add_zero] <;> split_ifs <;> nlinarith

private theorem sum_q₁₂ {ε p : ℝ} (hε : 0 ≤ ε) (hε' : ε < 1 / 2) (hp : 0 ≤ p) (b₁ b₂ : Bool) :
    ∑ y : Bool, (p * if y = b₂ then 1 - ε else ε) *
      (if (p * if y = b₂ then 1 - ε else ε) ≤ p * if y = b₁ then 1 - ε else ε then 1 else 0) =
      p * if b₁ = b₂ then 1 else ε := by
  cases b₁ <;> cases b₂ <;> simp only [Fintype.sum_bool, Bool.true_eq_false, Bool.false_eq_true,
    ite_true, ite_false, le_refl] <;> (try split_ifs) <;> nlinarith

private theorem sum_mul_ite_agree [IsProbabilityMeasure P] (a b : ℝ) :
    ∑ x : X, P.real {x} * (if decide (x ∈ G one) = decide (x ∈ G two) then a else b) =
      P.real {x | x ∈ G one ↔ x ∈ G two} * a +
        (1 - P.real {x | x ∈ G one ↔ x ∈ G two}) * b := by
  simp only [decide_eq_decide, mul_ite, sum_ite, ← sum_mul, sum_measureReal_singleton]
  rw [← probReal_compl_eq_one_sub .of_discrete, coe_filter, coe_filter]
  simp [Set.compl_ofPred]

-- Table 1, `ε < 1 - α`: `q₂₁ = (1 - s) ε`.
theorem mapLearner_comp_real_one_two [IsProbabilityMeasure P] {α : ℝ} (hα : 1 / 2 < α)
    (hαε : ε < 1 - α) (hε : 0 ≤ ε) :
    ((mapLearner (produce P G ε) (prior α) ∘ₖ produce P G ε) one).real {two} =
      (1 - P.real {x | x ∈ G one ↔ x ∈ G two}) * ε := by
  have := isMarkovKernel_produce P G ε hε (by linarith)
  rw [Kernel.comp_real_singleton]
  simp_rw [mapLearner_apply, argmax_prior_mul_produce hα hαε hε,
    mul_uniformOn_real_two measureReal_nonneg measureReal_nonneg (.inl rfl),
    produce_real_singleton hε (by linarith : ε ≤ 1), Fintype.sum_prod_type]
  rw [sum_congr rfl fun x _ ↦ sum_q₂₁ hε (by linarith) (measureReal_nonneg (μ := P) (s := {x}))
    (decide (x ∈ G one)) (decide (x ∈ G two)), sum_mul_ite_agree]
  ring

-- Table 1, `ε < 1 - α`: `q₁₂ = s + (1 - s) ε`.
theorem mapLearner_comp_real_two_one [IsProbabilityMeasure P] {α : ℝ} (hα : 1 / 2 < α)
    (hαε : ε < 1 - α) (hε : 0 ≤ ε) :
    ((mapLearner (produce P G ε) (prior α) ∘ₖ produce P G ε) two).real {one} =
      P.real {x | x ∈ G one ↔ x ∈ G two} + (1 - P.real {x | x ∈ G one ↔ x ∈ G two}) * ε := by
  have := isMarkovKernel_produce P G ε hε (by linarith)
  rw [Kernel.comp_real_singleton]
  simp_rw [mapLearner_apply, argmax_prior_mul_produce hα hαε hε,
    mul_uniformOn_real_one measureReal_nonneg measureReal_nonneg (.inr rfl),
    produce_real_singleton hε (by linarith : ε ≤ 1), Fintype.sum_prod_type]
  rw [sum_congr rfl fun x _ ↦ sum_q₁₂ hε (by linarith) (measureReal_nonneg (μ := P) (s := {x}))
    (decide (x ∈ G one)) (decide (x ∈ G two)), sum_mul_ite_agree]
  ring

/-- Table 1, `ε < 1 - α`: with noise, MAP learners between two languages have exactly one
stationary distribution. It gives `L₁` probability `(s + (1 - s) ε) / (s + 2 (1 - s) ε)`, where
`s` is the mass of the objects on which the languages agree, and does not depend on the prior
`α`. -/
theorem invariant_mapLearner_comp_produce_iff [IsProbabilityMeasure P] {α : ℝ} (hα : 1 / 2 < α)
    (hαε : ε < 1 - α) (hε : 0 < ε) (ν : Measure Language) [IsProbabilityMeasure ν] :
    (mapLearner (produce P G ε) (prior α) ∘ₖ produce P G ε).Invariant ν ↔
      ν = prior ((P.real {x | x ∈ G one ↔ x ∈ G two} +
          (1 - P.real {x | x ∈ G one ↔ x ∈ G two}) * ε) /
        (P.real {x | x ∈ G one ↔ x ∈ G two} +
          2 * (1 - P.real {x | x ∈ G one ↔ x ∈ G two}) * ε)) := by
  have q₂₁ := mapLearner_comp_real_one_two (P := P) (G := G) hα hαε hε.le
  have q₁₂ := mapLearner_comp_real_two_one (P := P) (G := G) hα hαε hε.le
  have hs₀ : 0 ≤ P.real {x | x ∈ G one ↔ x ∈ G two} := measureReal_nonneg
  have hs₁ : P.real {x | x ∈ G one ↔ x ∈ G two} ≤ 1 := measureReal_le_one (μ := P)
  have := isMarkovKernel_produce P G ε hε.le (by linarith)
  set Q := mapLearner (produce P G ε) (prior α) ∘ₖ produce P G ε
  generalize P.real {x | x ∈ G one ↔ x ∈ G two} = s at *
  have hD : 0 < s + 2 * (1 - s) * ε := by nlinarith
  have hN : 0 ≤ s + (1 - s) * ε := by nlinarith
  have hθ₀ : 0 ≤ (s + (1 - s) * ε) / (s + 2 * (1 - s) * ε) := div_nonneg hN hD.le
  have hθ₁ : (s + (1 - s) * ε) / (s + 2 * (1 - s) * ε) ≤ 1 :=
    div_le_one_of_le₀ (by nlinarith) hD.le
  have := isProbabilityMeasure_prior hθ₀ hθ₁
  refine ⟨fun h ↦ ext_of_real_one ?_, fun h ↦ ?_⟩
  · rw [real_one_eq_of_invariant Q ν h (by rw [q₁₂, q₂₁]; exact ne_of_gt (by linarith)), q₁₂, q₂₁,
      prior_real_one hθ₀]
    ring
  · rw [h, invariant_iff, q₂₁, q₁₂, prior_real_one hθ₀, prior_real_two hθ₁, one_sub_div hD.ne',
      div_mul_eq_mul_div, div_mul_eq_mul_div, div_left_inj' hD.ne']
    ring

-- MAP learners keep the prior `α` stationary only when it already gives `L₁` the stationary
-- probability.
theorem invariant_mapLearner_comp_produce_prior_iff [IsProbabilityMeasure P] {α : ℝ}
    (hα : 1 / 2 < α) (hαε : ε < 1 - α) (hε : 0 < ε) :
    (mapLearner (produce P G ε) (prior α) ∘ₖ produce P G ε).Invariant (prior α) ↔
      α = (P.real {x | x ∈ G one ↔ x ∈ G two} + (1 - P.real {x | x ∈ G one ↔ x ∈ G two}) * ε) /
        (P.real {x | x ∈ G one ↔ x ∈ G two} +
          2 * (1 - P.real {x | x ∈ G one ↔ x ∈ G two}) * ε) := by
  have := isProbabilityMeasure_prior (α := α) (by linarith) (by linarith)
  have hs₀ : 0 ≤ P.real {x | x ∈ G one ↔ x ∈ G two} := measureReal_nonneg
  have hs₁ : P.real {x | x ∈ G one ↔ x ∈ G two} ≤ 1 := measureReal_le_one (μ := P)
  rw [invariant_mapLearner_comp_produce_iff hα hαε hε]
  exact prior_inj (by linarith) (div_nonneg (by nlinarith) (by nlinarith))

/-- When the languages agree on no object, sampling learners keep the prior `α`, while MAP
learners spread over both languages evenly, whatever the bias toward `L₁`, and so do not keep
it. -/
example [IsProbabilityMeasure P] {α : ℝ} (hα : 1 / 2 < α) (hαε : ε < 1 - α) (hε : 0 < ε)
    (hG : ∀ x, x ∈ G one ↔ x ∉ G two) :
    ((produce P G ε)†(prior α) ∘ₖ produce P G ε).Invariant (prior α) ∧
      (mapLearner (produce P G ε) (prior α) ∘ₖ produce P G ε).Invariant (prior (1 / 2)) ∧
      ¬ (mapLearner (produce P G ε) (prior α) ∘ₖ produce P G ε).Invariant (prior α) := by
  have := isMarkovKernel_produce P G ε hε.le (by linarith)
  have := isProbabilityMeasure_prior (α := 1 / 2) (by norm_num) (by norm_num)
  have hs : P.real {x | x ∈ G one ↔ x ∈ G two} = 0 := by
    rw [show {x | x ∈ G one ↔ x ∈ G two} = ∅ by ext x; simp [hG x]]
    simp
  have hθ : (P.real {x | x ∈ G one ↔ x ∈ G two} + (1 - P.real {x | x ∈ G one ↔ x ∈ G two}) * ε) /
      (P.real {x | x ∈ G one ↔ x ∈ G two} + 2 * (1 - P.real {x | x ∈ G one ↔ x ∈ G two}) * ε) =
        1 / 2 := by
    rw [hs]
    field_simp
    ring
  refine ⟨invariant_posterior_comp, ?_, ?_⟩
  · rw [invariant_mapLearner_comp_produce_iff hα hαε hε, hθ]
  · rw [invariant_mapLearner_comp_produce_prior_iff hα hαε hε, hθ]
    exact fun h ↦ by linarith

/-- With noise, the MAP chain on two languages converges from any start to its stationary
probability of `L₁`, which does not involve the prior. -/
example [IsProbabilityMeasure P] (ν : Measure Language) [IsProbabilityMeasure ν] {α : ℝ}
    (hα : 1 / 2 < α) (hαε : ε < 1 - α) (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦
      (((mapLearner (produce P G ε) (prior α) ∘ₖ produce P G ε) ^ n) ∘ₘ ν).real {one}) atTop
      (𝓝 ((P.real {x | x ∈ G one ↔ x ∈ G two} + (1 - P.real {x | x ∈ G one ↔ x ∈ G two}) * ε) /
        (P.real {x | x ∈ G one ↔ x ∈ G two} +
          2 * (1 - P.real {x | x ∈ G one ↔ x ∈ G two}) * ε))) := by
  have := isMarkovKernel_produce P G ε hε.le (by linarith)
  have hs₀ : 0 ≤ P.real {x | x ∈ G one ↔ x ∈ G two} := measureReal_nonneg
  have hs₁ : P.real {x | x ∈ G one ↔ x ∈ G two} ≤ 1 := measureReal_le_one (μ := P)
  have h := tendsto_pow_comp_real_one (mapLearner (produce P G ε) (prior α) ∘ₖ produce P G ε) ν
  rw [mapLearner_comp_real_one_two hα hαε hε.le, mapLearner_comp_real_two_one hα hαε hε.le] at h
  convert h (by nlinarith) (by nlinarith) using 2
  ring

/-- One object, which `L₁` names and `L₂` does not, with prior `3/5` on `L₁` and noise `1/20`: MAP
learners are stationary at probability `1/2` for `L₁`. -/
example : (mapLearner (produce (Measure.dirac ()) (fun i ↦ {_x : Unit | i = one}) (1 / 20))
      (prior (3 / 5)) ∘ₖ
        produce (Measure.dirac ()) (fun i ↦ {_x : Unit | i = one}) (1 / 20)).Invariant
      (prior (1 / 2)) := by
  have := isProbabilityMeasure_prior (α := 1 / 2) (by norm_num) (by norm_num)
  have hs : (Measure.dirac ()).real {x : Unit | x ∈ {_x : Unit | one = one} ↔
      x ∈ {_x : Unit | two = one}} = 0 := by simp
  have h := invariant_mapLearner_comp_produce_iff (P := Measure.dirac ())
    (G := fun i ↦ {_x : Unit | i = one}) (α := 3 / 5) (ε := 1 / 20) (by norm_num) (by norm_num)
    (by norm_num) (prior (1 / 2))
  rw [hs] at h
  exact h.2 (by congr 1; norm_num)

end GriffithsKalish2007
