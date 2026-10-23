module

public import Linglib.Core.Probability.Decision.ValueOfInformation
public import Linglib.Core.MeasureTheory.Measure.Dirac

/-!
# Dong et al. (2026): Value of Information: A Framework for Human–Agent Communication

This file formalizes the clarify-or-commit policy of [dong-etal-2026]. An agent holds a belief
`b` over a user's latent intent `θ`, may commit to an action `a` of utility `U(θ, a)`, or may
ask a closed-ended question `q` whose answer `y` it predicts by an answer model `p(y ∣ q, θ)`
and which costs the user `c`. The expected utility of committing, (1), is an integral against
the belief, and the value of acting now, (2), is its best value, `decisionValue`. The value of a
question, (3), is the answer-marginal expectation of the value of the posterior belief, so the
value of information, (4), `VoI(q) = Vpost(b, q) − V(b)`, is the value of information of the
question as an experiment under the decision value, the notion the paper takes from
[raiffa-schlaifer-1961], and the net value, (5), subtracts the cost. The agent clarifies with a
question of positive net value and commits when none has one. Information cannot have negative
value, `voi_nonneg`, so an uninformative question is never asked, `not_clarifies_of_const`;
scaling the stakes scales the value of information, `voi_smul`, so a question worth asking at
low stakes is worth asking at higher stakes, `clarifies_smul`, and a costlier question is asked
less, `clarifies_of_le`. Appendix A shows this risk awareness on its 20 Questions task, where a
correct animal guess is worth `1` and a correct diagnosis `10`; `appendixA` reproduces the
contrast on a two-candidate task with a yes/no question of reliability `r`, whose value of
information is `r − 1/2` by `voi_reliability`.

## Implementation notes

The belief is a probability measure on intents and each question an answer kernel, so (1) to (4)
are integrals, posteriors and values of information of the library, and the clarify-or-commit
decision is the only new object. The policy's choice among the questions of positive net value,
the sequential loop of Algorithm 1 with its clarification budget and linear cost `T · c`, and the
language-model estimates of belief and answer distributions of §4.2 are not represented: the
theorems concern the decision at one turn, at a fixed belief. Stakes are a scalar on the utility.
The two-candidate task and the reliability `27/50` are this file's illustration, not the paper's.

## References

* [dong-etal-2026]
* [raiffa-schlaifer-1961]
-/

@[expose] public section

namespace DongEtAl2026

open MeasureTheory ProbabilityTheory Finset

variable {Θ A Q Y : Type*} [MeasurableSpace Θ] [MeasurableSpace Y] [StandardBorelSpace Θ]
  [Nonempty Θ]

/-! ### The value of information and the clarify-or-commit decision, (3) to (5) -/

variable (U : Θ → A → ℝ) (b : Measure Θ) [IsProbabilityMeasure b] (P : Q → Kernel Θ Y)
  [∀ q, IsMarkovKernel (P q)]

/-- The value of asking question `q`, (3), is the expected value of the posterior belief. -/
noncomputable def postValue (q : Q) : ℝ :=
  ∫ y, decisionValue U (((P q)†b) y) ∂(P q ∘ₘ b)

/-- The value of information of question `q`, (4), is the value of information of the question
as an experiment under the decision value. -/
noncomputable def voi (q : Q) : ℝ := valueOfInformation (decisionValue U) (P q) b

theorem voi_eq (q : Q) : voi U b P q = postValue U b P q - decisionValue U b := rfl

/-- The net value of information of question `q` at cost `c`, (5), is its value of information
less the cost. -/
noncomputable def netVoi (c : ℝ) (q : Q) : ℝ := voi U b P q - c

/-- The agent clarifies when some question of `questions` has positive net value, and commits
otherwise. -/
def Clarifies (c : ℝ) (questions : Finset Q) : Prop := ∃ q ∈ questions, 0 < netVoi U b P c q

theorem not_clarifies_iff (c : ℝ) (questions : Finset Q) :
    ¬ Clarifies U b P c questions ↔ ∀ q ∈ questions, netVoi U b P c q ≤ 0 := by
  simp only [Clarifies, not_exists, not_and, not_lt]

theorem not_clarifies_iff_sup'_le (c : ℝ) {questions : Finset Q} (h : questions.Nonempty) :
    ¬ Clarifies U b P c questions ↔ questions.sup' h (netVoi U b P c) ≤ 0 := by
  rw [not_clarifies_iff, sup'_le_iff]

theorem value_add_lt_postValue {c : ℝ} {q : Q} (h : 0 < netVoi U b P c q) :
    decisionValue U b + c < postValue U b P q := by
  rw [netVoi, voi_eq] at h
  linarith

theorem clarifies_of_le {c c' : ℝ} (hcc' : c ≤ c') {questions : Finset Q}
    (h : Clarifies U b P c' questions) : Clarifies U b P c questions := by
  obtain ⟨q, hq, hpos⟩ := h
  exact ⟨q, hq, by unfold netVoi at hpos ⊢; linarith⟩

theorem voi_smul {s : ℝ} (hs : 0 ≤ s) (q : Q) : voi (s • U) b P q = s * voi U b P q := by
  rw [voi, voi, ← valueOfInformation_smul, show decisionValue (s • U) = s • decisionValue U from
    funext (decisionValue_smul hs)]

theorem not_clarifies_of_const {c : ℝ} (hc : 0 ≤ c) {questions : Finset Q}
    (hP : ∀ q ∈ questions, ∃ ν, P q = Kernel.const Θ ν) : ¬ Clarifies U b P c questions := by
  rw [not_clarifies_iff]
  intro q hq
  obtain ⟨ν, hν⟩ := hP q hq
  have : IsProbabilityMeasure ν := by
    obtain ⟨θ⟩ := ‹Nonempty Θ›
    rw [← Kernel.const_apply ν θ, ← hν]
    infer_instance
  simp only [netVoi, voi, hν, valueOfInformation_const]
  linarith

variable [Finite Θ] [MeasurableSingletonClass Y] [Finite Y] [Finite A]

theorem voi_nonneg (q : Q) : 0 ≤ voi U b P q :=
  valueOfInformation_decisionValue_nonneg U (P q) b

theorem clarifies_smul {s s' : ℝ} (hs : 0 ≤ s) (hss' : s ≤ s') {c : ℝ} {questions : Finset Q}
    (h : Clarifies (s • U) b P c questions) : Clarifies (s' • U) b P c questions := by
  obtain ⟨q, hq, hpos⟩ := h
  refine ⟨q, hq, ?_⟩
  unfold netVoi at hpos ⊢
  rw [voi_smul U b P hs] at hpos
  rw [voi_smul U b P (hs.trans hss')]
  nlinarith [voi_nonneg U b P q]

/-! ### A two-candidate task with a yes/no question -/

/-- A correct guess is worth `1` and an incorrect one `0`. -/
def correct (θ a : Bool) : ℝ := if a = θ then 1 else 0

/-- `answer r θ y` is the probability that a yes/no question of reliability `r` answers `y` at
`θ`. -/
def answer (r : ℝ) (θ y : Bool) : ℝ := if y = θ then r else 1 - r

/-- A yes/no question of reliability `r` answers correctly with probability `r`. -/
noncomputable def question (r : ℝ) : Kernel Bool Bool :=
  Kernel.ofFunOfCountable fun θ ↦ ∑ y, ENNReal.ofReal (answer r θ y) • Measure.dirac y

theorem decisionValue_correct (μ : Measure Bool) [IsFiniteMeasure μ] :
    decisionValue correct μ = max (μ.real {true}) (μ.real {false}) := by
  have h a : ∫ θ, correct θ a ∂μ = μ.real {a} := by
    rw [integral_fintype .of_finite]
    cases a <;> simp [correct]
  have hb : BddAbove (Set.range fun a : Bool ↦ μ.real {a}) := (Set.finite_range _).bddAbove
  simp only [decisionValue, h]
  exact le_antisymm (ciSup_le fun a ↦ by cases a <;> simp) (max_le (le_ciSup hb _) (le_ciSup hb _))

section Reliability

variable {r : ℝ} (h₀ : 0 ≤ r) (h₁ : r ≤ 1)
include h₀ h₁

theorem answer_nonneg (θ y : Bool) : 0 ≤ answer r θ y := by
  unfold answer
  split <;> linarith

theorem question_real_singleton (θ y : Bool) : (question r θ).real {y} = answer r θ y := by
  have : question r θ = ∑ y', ENNReal.ofReal (answer r θ y') • Measure.dirac y' := rfl
  rw [measureReal_def, this, Measure.sum_smul_dirac_apply_singleton,
    ENNReal.toReal_ofReal (answer_nonneg h₀ h₁ θ y)]

theorem isMarkovKernel_question : IsMarkovKernel (question r) :=
  ⟨fun θ ↦ Measure.isProbabilityMeasure_sum_ofReal_smul_dirac (answer_nonneg h₀ h₁ θ)
    (by cases θ <;> simp [answer])⟩

theorem comp_question_real (y : Bool) :
    (question r ∘ₘ uniformOn Set.univ).real {y} = 1 / 2 := by
  have := isMarkovKernel_question h₀ h₁
  rw [Measure.comp_real_singleton, Fintype.sum_bool]
  simp only [uniformOn_univ_real_singleton, question_real_singleton h₀ h₁]
  cases y <;> simp [answer] <;> ring

theorem posterior_question_real (y θ : Bool) :
    haveI := isMarkovKernel_question h₀ h₁
    (((question r)†(uniformOn Set.univ)) y).real {θ} = answer r θ y := by
  have := isMarkovKernel_question h₀ h₁
  have hy : (question r ∘ₘ uniformOn Set.univ) {y} ≠ 0 := by
    rw [← measureReal_ne_zero_iff (measure_ne_top _ _), comp_question_real h₀ h₁]
    norm_num
  rw [posterior_real_singleton _ _ hy, uniformOn_univ_real_singleton,
    question_real_singleton h₀ h₁, comp_question_real h₀ h₁, Fintype.card_bool]
  ring

theorem voi_reliability (hr : 1 / 2 ≤ r) :
    haveI := isMarkovKernel_question h₀ h₁
    valueOfInformation (decisionValue correct) (question r) (uniformOn Set.univ) = r - 1 / 2 := by
  have := isMarkovKernel_question h₀ h₁
  have hr' : 1 - r ≤ r := by linarith
  rw [valueOfInformation, integral_fintype .of_finite, Fintype.sum_bool]
  simp only [decisionValue_correct, posterior_question_real h₀ h₁, comp_question_real h₀ h₁,
    uniformOn_univ_real_singleton, smul_eq_mul, answer]
  simp [max_eq_left hr', max_eq_right hr']
  ring

end Reliability

/-- As in Appendix A, at cost `1/20` a question of reliability `27/50` is skipped when a correct
guess is worth `1` and asked when it is worth `10`. -/
theorem appendixA :
    haveI := isMarkovKernel_question (r := 27 / 50) (by norm_num) (by norm_num)
    ¬ Clarifies correct (uniformOn Set.univ) (fun _ : Unit ↦ question (27 / 50)) (1 / 20) {()} ∧
      Clarifies ((10 : ℝ) • correct) (uniformOn Set.univ) (fun _ : Unit ↦ question (27 / 50))
        (1 / 20) {()} := by
  have := isMarkovKernel_question (r := 27 / 50) (by norm_num) (by norm_num)
  have h := voi_reliability (r := 27 / 50) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · rw [not_clarifies_iff]
    rintro ⟨⟩ -
    rw [netVoi, voi, h]
    norm_num
  · refine ⟨(), mem_singleton_self _, ?_⟩
    rw [netVoi, voi_smul _ _ _ (by norm_num), voi, h]
    norm_num

end DongEtAl2026
