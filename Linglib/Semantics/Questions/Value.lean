module

public import Linglib.Core.Order.Partition.Finpartition
public import Linglib.Core.Probability.Decision.ValueOfInformation

/-!
# The value of a question

Relative to a decision problem, a prior over worlds and a utility for each action in each world,
an answer is worth the gain in decision value from learning it, and a question, a partition of
the worlds, is worth the expected gain from learning its answer. That expectation is the value of
information of the experiment revealing the answer, it is never negative, it vanishes exactly
when no answer changes the best action, and it reaches the value of perfect information when the
answer settles the utilities. One question refines another exactly when it is at least as useful
in every decision problem. A wh-question over a domain partitions the worlds by the predicate's
extension within the domain, so widening the domain cannot lower the question's value, and once
the domain holds every individual the utilities depend on, widening it further only makes the
question worse.

## Main statements

* `Question.utility_eq_valueOfInformation`: a question's value is the value of information of
  revealing its answer.
* `Question.utility_eq_zero_iff`: a question is worthless exactly when the best action stays best
  whatever the answer.
* `Question.le_iff_forall_utility_le`: one question refines another exactly when it is at least
  as useful in every decision problem.
* `Question.better_wh_of_factorsThrough`: a wh-domain should contain only the individuals the
  decision depends on.

## References

* [van-rooy-2003]
* [blackwell-1953]
* [raiffa-schlaifer-1961]
-/

@[expose] public section

namespace Question

open MeasureTheory ProbabilityTheory

universe u

variable {W : Type u} {A : Type*}

/-! ### The value of answers -/

section Answer

variable [MeasurableSpace W]

/-- The utility value of learning `C` is the decision value of the prior conditioned on `C`, less
the decision value of the prior. -/
noncomputable def utilityValue (U : W → A → ℝ) (μ : Measure W) (C : Set W) : ℝ :=
  decisionValue U μ[|C] - decisionValue U μ

/-- An answer is better than another when it has a higher utility value, or the same value and
is strictly less informative. -/
def BetterAnswer (U : W → A → ℝ) (μ : Measure W) (C D : Set W) : Prop :=
  toLex (utilityValue U μ D, D) < toLex (utilityValue U μ C, C)

theorem betterAnswer_iff {U : W → A → ℝ} {μ : Measure W} {C D : Set W} :
    BetterAnswer U μ C D ↔ utilityValue U μ D < utilityValue U μ C ∨
      utilityValue U μ C = utilityValue U μ D ∧ D ⊂ C := by
  simp [BetterAnswer, Prod.Lex.toLex_lt_toLex, eq_comm]

/-- The value of sample information of learning `C` compares the best action after learning `C`
with the action `a` taken now. -/
noncomputable def valueSampleInfo (U : W → A → ℝ) (μ : Measure W) (a : A) (C : Set W) : ℝ :=
  decisionValue U μ[|C] - ∫ w, U w a ∂μ[|C]

theorem valueSampleInfo_nonneg [Finite A] (U : W → A → ℝ) (μ : Measure W) (a : A) (C : Set W) :
    0 ≤ valueSampleInfo U μ a C :=
  sub_nonneg.2 (integral_le_decisionValue _ a)

private theorem decisionValue_cond_eq_integral [MeasurableSingletonClass W] (U : W → A → ℝ)
    (μ : Measure W) [IsFiniteMeasure μ] {s : Set W} {w₀ : W} (hs : ∀ w ∈ s, U w = U w₀)
    (hsm : MeasurableSet s) (hμ : μ s ≠ 0) :
    decisionValue U μ[|s] = ∫ w, ⨆ a, U w a ∂μ[|s] := by
  have := cond_isProbabilityMeasure (μ := μ) hμ
  have hae : ∀ᵐ w ∂μ[|s], U w = U w₀ := (ae_cond_mem hsm).mono fun w hw ↦ hs w hw
  have h (f : (A → ℝ) → ℝ) : ∫ w, f (U w) ∂μ[|s] = f (U w₀) := by
    rw [integral_congr_ae (g := fun _ ↦ f (U w₀)) (hae.mono fun w hw ↦ by simp only [hw])]
    simp
  rw [decisionValue, h fun u ↦ ⨆ a, u a]
  exact congrArg _ (funext fun a ↦ h fun u ↦ u a)

end Answer

/-! ### The utility of questions -/

section Utility

variable [MeasurableSpace W] [Fintype W] [DecidableEq W]

/-- The expected utility value of a question weights the utility value of each answer by its
probability. -/
noncomputable def utility (U : W → A → ℝ) (μ : Measure W)
    (Q : Finpartition (Finset.univ : Finset W)) : ℝ :=
  ∑ c ∈ Q.parts, μ.real c * utilityValue U μ c

/-- Relative to a decision problem, a question is better than another when it is more useful, or
as useful and strictly coarser, since one should not ask for irrelevant information. -/
def Better (U : W → A → ℝ) (μ : Measure W) (Q Q' : Finpartition (Finset.univ : Finset W)) :
    Prop :=
  toLex (utility U μ Q', Q') < toLex (utility U μ Q, Q)

theorem better_iff {U : W → A → ℝ} {μ : Measure W} {Q Q' : Finpartition (Finset.univ : Finset W)} :
    Better U μ Q Q' ↔
      utility U μ Q' < utility U μ Q ∨
        utility U μ Q = utility U μ Q' ∧ Q' < Q := by
  simp [Better, Prod.Lex.toLex_lt_toLex, eq_comm]

variable [DiscreteMeasurableSpace W] (U : W → A → ℝ) (μ : Measure W) [IsProbabilityMeasure μ]

private theorem utility_eq (Q : Finpartition (Finset.univ : Finset W)) :
    utility U μ Q =
      ∑ c, μ.real (Q.part ⁻¹' {c}) * decisionValue U μ[|Q.part ⁻¹' {c}] - decisionValue U μ := by
  have hmass : ∑ c ∈ Q.parts, μ.real c = 1 := by
    rw [Q.sum_parts_eq_sum_preimage_part (F := μ.real) measureReal_empty,
      sum_measureReal_preimage_singleton _ fun _ _ ↦ .of_discrete]
    simp
  simp only [utility, utilityValue, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    hmass, one_mul]
  rw [Q.sum_parts_eq_sum_preimage_part (F := fun c ↦ μ.real c * decisionValue U μ[|c]) (by simp)]

/-- The expected utility value of a question is the value of information of the experiment that
reveals its answer. -/
theorem utility_eq_valueOfInformation [Nonempty W] [MeasurableSpace (Finset W)]
    [MeasurableSingletonClass (Finset W)] (Q : Finpartition (Finset.univ : Finset W)) :
    utility U μ Q =
      valueOfInformation (decisionValue U) (Kernel.deterministic Q.part .of_discrete) μ := by
  rw [utility_eq, valueOfInformation_deterministic]

theorem utility_eq_valueOfInformation_id [Nonempty W]
    (Q : Finpartition (Finset.univ : Finset W)) (hQ : U.FactorsThrough Q.part) :
    utility U μ Q = valueOfInformation (decisionValue U) Kernel.id μ := by
  rw [utility_eq, valueOfInformation_id]
  simp only [decisionValue_dirac]
  congr 1
  rw [← sum_measureReal_mul_integral_cond (fun w ↦ ⨆ a, U w a) Q.part μ]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rcases eq_or_ne (μ (Q.part ⁻¹' {c})) 0 with h | h
  · simp [measureReal_def, h]
  obtain ⟨w₀, hw₀⟩ := nonempty_of_measure_ne_zero h
  rw [decisionValue_cond_eq_integral U μ (fun w hw ↦ hQ (hw.trans hw₀.symm)) .of_discrete h]

theorem utility_bot [Nonempty W] :
    utility U μ ⊥ = valueOfInformation (decisionValue U) Kernel.id μ :=
  utility_eq_valueOfInformation_id U μ ⊥ fun w v h ↦ by
    rw [Finpartition.part_bot (Finset.mem_univ w), Finpartition.part_bot (Finset.mem_univ v),
      Finset.singleton_inj] at h
    rw [h]

theorem utility_nonneg [Finite A] [Nonempty W] (Q : Finpartition (Finset.univ : Finset W)) :
    0 ≤ utility U μ Q := by
  let _ : MeasurableSpace (Finset W) := ⊤
  have : MeasurableSingletonClass (Finset W) := ⟨fun _ ↦ trivial⟩
  rw [utility_eq_valueOfInformation]
  exact valueOfInformation_decisionValue_nonneg U _ μ

theorem utility_anti [Finite A] [Nonempty W] {P Q : Finpartition (Finset.univ : Finset W)}
    (h : P ≤ Q) : utility U μ Q ≤ utility U μ P := by
  let _ : MeasurableSpace (Finset W) := ⊤
  have : MeasurableSingletonClass (Finset W) := ⟨fun _ ↦ trivial⟩
  rw [utility_eq_valueOfInformation, utility_eq_valueOfInformation]
  exact valueOfInformation_decisionValue_le_of_factorsThrough U _ _
    (Finpartition.le_iff_factorsThrough_part.1 h) μ

theorem utility_le_bot [Finite A] [Nonempty W]
    (Q : Finpartition (Finset.univ : Finset W)) :
    utility U μ Q ≤ utility U μ ⊥ :=
  utility_anti U μ bot_le

theorem utility_eq_sum_valueSampleInfo [Nonempty W]
    (Q : Finpartition (Finset.univ : Finset W)) {a : A}
    (ha : ∫ w, U w a ∂μ = decisionValue U μ) :
    utility U μ Q = ∑ c ∈ Q.parts, μ.real c * valueSampleInfo U μ a c := by
  simp only [valueSampleInfo, mul_sub, Finset.sum_sub_distrib]
  rw [utility_eq,
    Q.sum_parts_eq_sum_preimage_part (F := fun c ↦ μ.real c * decisionValue U μ[|c]) (by simp),
    Q.sum_parts_eq_sum_preimage_part (F := fun c ↦ μ.real c * ∫ w, U w a ∂μ[|c]) (by simp),
    sum_measureReal_mul_integral_cond, ha]

/-- A question is worthless exactly when the action that is best now stays best whatever the
answer. -/
theorem utility_eq_zero_iff [Finite A] [Nonempty W] (Q : Finpartition (Finset.univ : Finset W))
    {a : A} (ha : ∫ w, U w a ∂μ = decisionValue U μ) :
    utility U μ Q = 0 ↔
      ∀ c ∈ Q.parts, μ c ≠ 0 → ∫ w, U w a ∂μ[|c] = decisionValue U μ[|c] := by
  rw [utility_eq_sum_valueSampleInfo U μ Q ha, Finset.sum_eq_zero_iff_of_nonneg fun c _ ↦
    mul_nonneg measureReal_nonneg (valueSampleInfo_nonneg U μ a _)]
  refine forall₂_congr fun c _ ↦ ?_
  rw [mul_eq_zero, measureReal_eq_zero_iff, valueSampleInfo, sub_eq_zero, or_iff_not_imp_left]
  exact imp_congr_right fun _ ↦ eq_comm

variable {U μ}

/-- One question refines another exactly when it is at least as useful in every decision problem
with a probability prior, the special case of [blackwell-1953] stated in section 4.1. -/
theorem le_iff_forall_utility_le [Nonempty W]
    (P Q : Finpartition (Finset.univ : Finset W)) :
    P ≤ Q ↔ ∀ {B : Type u} [Fintype B] (U : W → B → ℝ) (μ : Measure W) [IsProbabilityMeasure μ],
      utility U μ Q ≤ utility U μ P := by
  refine ⟨fun h _ _ U μ _ ↦ utility_anti U μ h, fun h ↦ ?_⟩
  let _ : MeasurableSpace (Finset W) := ⊤
  have : MeasurableSingletonClass (Finset W) := ⟨fun _ ↦ trivial⟩
  obtain ⟨ψ, hψ⟩ := exists_eq_comp_of_forall_valueOfInformation_le P.part Q.part fun U ↦ by
    simpa only [utility_eq_valueOfInformation] using h U (uniformOn Set.univ)
  exact Finpartition.le_iff_factorsThrough_part.2 fun a b hab ↦ by simp [hψ, hab]

end Utility

/-! ### The domain of a wh-phrase -/

section Domain

variable [Fintype W] [DecidableEq W] {D : Type*} [DecidableEq D]

/-- The partition a wh-question induces over a domain puts two worlds together when the
predicate's extension agrees on the domain. -/
def wh (P : W → Finset D) (dom : Finset D) : Finpartition (Finset.univ : Finset W) :=
  Finpartition.ofFun fun w ↦ dom ∩ P w

theorem wh_anti (P : W → Finset D) {dom dom' : Finset D} (h : dom ⊆ dom') :
    wh P dom' ≤ wh P dom :=
  Finpartition.ofFun_le_ofFun_iff.2 fun w v hwv ↦ by
    rw [← Finset.inter_eq_left.2 h, Finset.inter_assoc, Finset.inter_assoc, hwv]

variable [MeasurableSpace W] (U : W → A → ℝ) (μ : Measure W)

/-- Of two domains yielding equally useful but different questions, the smaller gives the better
question, so the domain relevance selects contains only individuals that could affect the
decision. -/
theorem better_wh (P : W → Finset D) {dom dom' : Finset D} (h : dom ⊆ dom')
    (heq : utility U μ (wh P dom) = utility U μ (wh P dom'))
    (hne : wh P dom' ≠ wh P dom) :
    Better U μ (wh P dom) (wh P dom') :=
  better_iff.2 (.inr ⟨heq, (wh_anti P h).lt_of_ne hne⟩)

variable [DiscreteMeasurableSpace W] [IsProbabilityMeasure μ]

theorem utility_wh_mono [Finite A] [Nonempty W] (P : W → Finset D)
    {dom dom' : Finset D} (h : dom ⊆ dom') :
    utility U μ (wh P dom) ≤ utility U μ (wh P dom') :=
  utility_anti U μ (wh_anti P h)

/-- When the utilities depend only on which individuals of `dom` satisfy `P`, every larger domain
yielding a different question gives a worse one. -/
theorem better_wh_of_factorsThrough [Nonempty W] (P : W → Finset D) {dom dom' : Finset D}
    (h : dom ⊆ dom') (hU : U.FactorsThrough (wh P dom).part) (hne : wh P dom' ≠ wh P dom) :
    Better U μ (wh P dom) (wh P dom') := by
  have hU' : U.FactorsThrough (wh P dom').part := fun w v hwv ↦
    hU (Finpartition.le_iff_factorsThrough_part.1 (wh_anti P h) hwv)
  exact better_wh U μ P h (by rw [utility_eq_valueOfInformation_id U μ _ hU,
    utility_eq_valueOfInformation_id U μ _ hU']) hne

end Domain

end Question
