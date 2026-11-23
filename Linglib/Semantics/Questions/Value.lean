module

public import Linglib.Core.Probability.Decision.ValueOfInformation
public import Linglib.Semantics.Questions.HamblinSet

/-!
# The value of a question

A decision problem is a prior `μ` over worlds together with a utility `U w a` for each action `a`
in each world `w`. Its value is `decisionValue U μ`, the best expected utility of an action.
Learning a proposition `C` replaces the prior by `μ[|C]`, and we define the utility value of `C`
as the change in the value of the problem,
`utilityValue U μ C = decisionValue U μ[|C] - decisionValue U μ`.

A question is a partition of the worlds, a `Setoid W`, whose answer in the world `w` is the cell
`Q.cell w`. We define the expected utility value of a question as the expected utility value of
its true answer, `utility U μ Q = ∫ w, utilityValue U μ (Q.cell w) ∂μ`. On finitely many worlds
this is the sum of the utility values of the cells weighted by their probabilities
(`utility_eq_sum`), and it is the value of information of the experiment that observes the cell
(`utility_eq_valueOfInformation`).

The trivial question `⊤` is worth nothing and the finest question `⊥` is worth the value of
perfect information, as is every question that settles the utilities, `Q ≤ Setoid.ker U`. A
finer question is worth at least as much (`utility_anti`), so questions have nonnegative value,
and refinement is exactly being at least as useful in every decision problem
(`le_iff_forall_utility_le`). A question is worth nothing exactly when an action that is best now
stays best at the answer in almost every world (`utility_eq_zero_iff`).

Relative to a decision problem, `Better U μ Q Q'` holds when `Q` is worth more than `Q'`, or as
much and strictly coarser. A question that settles the utilities is better than every strictly
finer one (`better_of_lt_of_le_ker`). The wh-question over a domain `D` of individuals with
property `P` is the partition `partition (P '' D)` of the worlds by which individuals of `D` have
the property; widening the domain cannot lower its value (`utility_partition_image_mono`), and
once the domain settles the utilities, widening it gives a worse question
(`better_partition_image`).

## Implementation notes

The expected utility value is an integral over worlds and not a sum over cells, so the definition
needs neither finiteness nor decidability, and the cells of probability zero that a sum has to
set aside are a null set. The theorems assume finitely many worlds and actions, as the value of
information they rest on does.

## References

* [van-rooy-2003]
* [blackwell-1953]
* [raiffa-schlaifer-1961]
* [groenendijk-stokhof-1984]
-/

@[expose] public section

namespace Question

open MeasureTheory ProbabilityTheory

universe u

variable {W : Type u} {A : Type*} [MeasurableSpace W]

/-! ### The value of answers -/

section Answer

/-- The utility value of learning `C` is the decision value of the prior conditioned on `C`, less
the decision value of the prior. -/
noncomputable def utilityValue (U : W → A → ℝ) (μ : Measure W) (C : Set W) : ℝ :=
  decisionValue U μ[|C] - decisionValue U μ

@[simp]
theorem utilityValue_univ (U : W → A → ℝ) (μ : Measure W) [IsProbabilityMeasure μ] :
    utilityValue U μ Set.univ = 0 := by
  simp [utilityValue]

/-- An answer is better than another when it has a higher utility value, or the same value and
is strictly less informative. -/
def BetterAnswer (U : W → A → ℝ) (μ : Measure W) (C D : Set W) : Prop :=
  toLex (utilityValue U μ D, D) < toLex (utilityValue U μ C, C)

theorem betterAnswer_iff {U : W → A → ℝ} {μ : Measure W} {C D : Set W} :
    BetterAnswer U μ C D ↔ utilityValue U μ D < utilityValue U μ C ∨
      utilityValue U μ C = utilityValue U μ D ∧ D ⊂ C := by
  simp [BetterAnswer, Prod.Lex.toLex_lt_toLex, eq_comm]

instance (U : W → A → ℝ) (μ : Measure W) : IsStrictOrder (Set W) (BetterAnswer U μ) where
  irrefl _ := lt_irrefl _
  trans _ _ _ h h' := lt_trans h' h

/-- The value of sample information of learning `C` compares the best action after learning `C`
with the action `a` taken now. -/
noncomputable def valueSampleInfo (U : W → A → ℝ) (μ : Measure W) (a : A) (C : Set W) : ℝ :=
  decisionValue U μ[|C] - ∫ w, U w a ∂μ[|C]

theorem valueSampleInfo_nonneg [Finite A] (U : W → A → ℝ) (μ : Measure W) (a : A) (C : Set W) :
    0 ≤ valueSampleInfo U μ a C :=
  sub_nonneg.2 (integral_le_decisionValue _ a)

/-- Where the utilities are constant on `s`, the decision value of the prior conditioned on `s`
is the utility of the best action there. -/
theorem decisionValue_cond_of_forall_eq (U : W → A → ℝ) (μ : Measure W) [IsFiniteMeasure μ]
    {s : Set W} {w : W} (hs : ∀ v ∈ s, U v = U w) (hsm : MeasurableSet s) (hμ : μ s ≠ 0) :
    decisionValue U μ[|s] = ⨆ a, U w a := by
  have := cond_isProbabilityMeasure (μ := μ) hμ
  refine iSup_congr fun a ↦ ?_
  rw [integral_congr_ae (g := fun _ ↦ U w a)
    ((ae_cond_mem hsm).mono fun v hv ↦ by simp only [hs v hv])]
  simp

end Answer

/-! ### The utility of questions -/

section Utility

/-- The expected utility value of a question is the expected utility value of its true
answer. -/
noncomputable def utility (U : W → A → ℝ) (μ : Measure W) (Q : Setoid W) : ℝ :=
  ∫ w, utilityValue U μ (Q.cell w) ∂μ

/-- Relative to a decision problem, a question is better than another when it is more useful, or
as useful and strictly coarser, since one should not ask for irrelevant information. -/
def Better (U : W → A → ℝ) (μ : Measure W) (Q Q' : Setoid W) : Prop :=
  toLex (utility U μ Q', Q') < toLex (utility U μ Q, Q)

theorem better_iff {U : W → A → ℝ} {μ : Measure W} {Q Q' : Setoid W} :
    Better U μ Q Q' ↔ utility U μ Q' < utility U μ Q ∨ utility U μ Q = utility U μ Q' ∧ Q' < Q := by
  simp [Better, Prod.Lex.toLex_lt_toLex, eq_comm]

instance (U : W → A → ℝ) (μ : Measure W) : IsStrictOrder (Setoid W) (Better U μ) where
  irrefl _ := lt_irrefl _
  trans _ _ _ h h' := lt_trans h' h

variable (U : W → A → ℝ) (μ : Measure W) [IsProbabilityMeasure μ]

/-- The trivial question is worth nothing. -/
@[simp]
theorem utility_top : utility U μ ⊤ = 0 := by
  simp [utility]

variable [Finite W] [DiscreteMeasurableSpace W]

private theorem integral_cell (F : Set W → ℝ) (Q : Setoid W) [Fintype (Quotient Q)] :
    ∫ w, F (Q.cell w) ∂μ =
      ∑ c : Quotient Q, μ.real (Quotient.mk Q ⁻¹' {c}) * F (Quotient.mk Q ⁻¹' {c}) := by
  simp_rw [Setoid.cell_eq_preimage_mk]
  rw [← integral_map (φ := Quotient.mk Q) Measurable.of_discrete.aemeasurable
      (f := fun c ↦ F (Quotient.mk Q ⁻¹' {c})) Integrable.of_finite.aestronglyMeasurable,
    integral_fintype .of_finite]
  exact Finset.sum_congr rfl fun c _ ↦ by
    rw [smul_eq_mul, map_measureReal_apply .of_discrete (measurableSet_singleton c)]

/-- The expected utility value of a question is the sum of the utility values of its cells
weighted by their probabilities. -/
theorem utility_eq_sum (Q : Setoid W) [Fintype (Quotient Q)] :
    utility U μ Q = ∑ c : Quotient Q,
      μ.real (Quotient.mk Q ⁻¹' {c}) * utilityValue U μ (Quotient.mk Q ⁻¹' {c}) :=
  integral_cell μ _ Q

theorem utility_eq_integral_sub (Q : Setoid W) :
    utility U μ Q = ∫ w, decisionValue U μ[|Q.cell w] ∂μ - decisionValue U μ := by
  simp [utility, utilityValue, integral_sub (μ := μ) .of_finite .of_finite]

/-- The expected utility value of a question is the value of information of the experiment that
observes its answer. -/
theorem utility_eq_valueOfInformation [Nonempty W] (Q : Setoid W) :
    utility U μ Q = valueOfInformation (decisionValue U)
      (Kernel.deterministic (Quotient.mk Q) .of_discrete) μ := by
  cases nonempty_fintype (Quotient Q)
  rw [utility_eq_integral_sub, valueOfInformation_deterministic,
    integral_cell μ (fun c ↦ decisionValue U μ[|c])]

/-- A question that settles the utilities is worth the value of perfect information. -/
theorem utility_eq_valueOfInformation_id [Nonempty W] {Q : Setoid W} (hQ : Q ≤ Setoid.ker U) :
    utility U μ Q = valueOfInformation (decisionValue U) Kernel.id μ := by
  rw [utility_eq_integral_sub, valueOfInformation_id]
  simp only [decisionValue_dirac]
  congr 1
  refine integral_congr_ae (ae_iff_of_countable.2 fun w hw ↦ ?_)
  exact decisionValue_cond_of_forall_eq U μ (fun v hv ↦ hQ hv) .of_discrete fun h ↦
    hw (measure_mono_null (Set.singleton_subset_iff.2 (Q.mem_cell_self w)) h)

theorem utility_bot [Nonempty W] :
    utility U μ ⊥ = valueOfInformation (decisionValue U) Kernel.id μ :=
  utility_eq_valueOfInformation_id U μ bot_le

theorem utility_eq_utility_bot [Nonempty W] {Q : Setoid W} (hQ : Q ≤ Setoid.ker U) :
    utility U μ Q = utility U μ ⊥ :=
  (utility_eq_valueOfInformation_id U μ hQ).trans (utility_bot U μ).symm

/-- A finer question is worth at least as much. -/
theorem utility_anti [Finite A] [Nonempty W] : Antitone (utility U μ) := fun Q Q' h ↦ by
  rw [utility_eq_valueOfInformation, utility_eq_valueOfInformation]
  cases nonempty_fintype (Quotient Q)
  exact valueOfInformation_decisionValue_le_of_factorsThrough U _ _
    (fun _ _ hab ↦ Quotient.sound (h (Quotient.exact hab))) μ

/-- The expected utility value as a monotone map into the dual of the reals. -/
noncomputable def utilityOrderHom [Finite A] [Nonempty W] : Setoid W →o ℝᵒᵈ where
  toFun Q := OrderDual.toDual (utility U μ Q)
  monotone' := utility_anti U μ

@[simp]
theorem utilityOrderHom_apply [Finite A] [Nonempty W] (Q : Setoid W) :
    utilityOrderHom U μ Q = OrderDual.toDual (utility U μ Q) := rfl

theorem utility_nonneg [Finite A] [Nonempty W] (Q : Setoid W) : 0 ≤ utility U μ Q :=
  (utility_top U μ).ge.trans (utility_anti U μ le_top)

theorem utility_le_bot [Finite A] [Nonempty W] (Q : Setoid W) : utility U μ Q ≤ utility U μ ⊥ :=
  utility_anti U μ bot_le

/-- The expected utility value of a question is its expected value of sample information over an
action that is best now. -/
theorem utility_eq_integral_valueSampleInfo [Nonempty W] (Q : Setoid W) {a : A}
    (ha : ∫ w, U w a ∂μ = decisionValue U μ) :
    utility U μ Q = ∫ w, valueSampleInfo U μ a (Q.cell w) ∂μ := by
  cases nonempty_fintype (Quotient Q)
  have h : ∫ w, ∫ v, U v a ∂μ[|Q.cell w] ∂μ = decisionValue U μ := by
    rw [integral_cell μ (fun c ↦ ∫ v, U v a ∂μ[|c]), sum_measureReal_mul_integral_cond, ha]
  simp only [valueSampleInfo]
  rw [integral_sub .of_finite .of_finite, h, utility_eq_integral_sub]

/-- A question is worthless exactly when an action that is best now stays best at the answer in
almost every world. -/
theorem utility_eq_zero_iff [Finite A] [Nonempty W] (Q : Setoid W) {a : A}
    (ha : ∫ w, U w a ∂μ = decisionValue U μ) :
    utility U μ Q = 0 ↔
      ∀ᵐ w ∂μ, ∫ v, U v a ∂μ[|Q.cell w] = decisionValue U μ[|Q.cell w] := by
  rw [utility_eq_integral_valueSampleInfo U μ Q ha,
    integral_eq_zero_iff_of_nonneg (fun w ↦ valueSampleInfo_nonneg U μ a _) .of_finite]
  exact Filter.eventually_congr (.of_forall fun w ↦ sub_eq_zero.trans eq_comm)

variable {U μ}

/-- One question refines another exactly when it is at least as useful in every decision problem
with a probability prior, a case of the comparison of experiments of [blackwell-1953]. -/
theorem le_iff_forall_utility_le [Nonempty W] (Q Q' : Setoid W) :
    Q ≤ Q' ↔ ∀ {B : Type u} [Finite B] (U : W → B → ℝ) (μ : Measure W) [IsProbabilityMeasure μ],
      utility U μ Q' ≤ utility U μ Q := by
  refine ⟨fun h _ _ U μ _ ↦ utility_anti U μ h, fun h ↦ ?_⟩
  cases nonempty_fintype W
  cases nonempty_fintype (Quotient Q)
  cases nonempty_fintype (Quotient Q')
  have : Nonempty (Quotient Q') := Nonempty.map (Quotient.mk Q') inferInstance
  obtain ⟨ψ, hψ⟩ := exists_eq_comp_of_forall_valueOfInformation_le (Quotient.mk Q)
    (Quotient.mk Q') fun U ↦ by
      simpa only [utility_eq_valueOfInformation] using h U (uniformOn Set.univ)
  exact fun a b hab ↦ Quotient.exact <| by
    rw [show Quotient.mk Q' a = ψ (Quotient.mk Q a) from congrFun hψ a,
      show Quotient.mk Q' b = ψ (Quotient.mk Q b) from congrFun hψ b, Quotient.sound hab]

variable (U μ)

/-- A question that settles the utilities is better than every strictly finer question. -/
theorem better_of_lt_of_le_ker [Nonempty W] {Q Q' : Setoid W} (hQ : Q ≤ Setoid.ker U)
    (h : Q' < Q) : Better U μ Q Q' :=
  better_iff.2 (.inr ⟨by rw [utility_eq_utility_bot U μ hQ,
    utility_eq_utility_bot U μ (h.le.trans hQ)], h⟩)

end Utility

/-! ### The domain of a wh-phrase -/

section Domain

variable [Finite W] [DiscreteMeasurableSpace W] [Nonempty W] (U : W → A → ℝ) (μ : Measure W)
  [IsProbabilityMeasure μ] {E : Type*} (P : E → Set W) {D D' : Set E}

/-- Widening the domain of a wh-question cannot lower its value. -/
theorem utility_partition_image_mono [Finite A] (h : D ⊆ D') :
    utility U μ (partition (P '' D)) ≤ utility U μ (partition (P '' D')) :=
  utility_anti U μ (partition_anti (Set.image_mono h))

/-- When the wh-question over `D` settles the utilities, every larger domain yielding a
different question gives a worse one. -/
theorem better_partition_image (h : D ⊆ D') (hU : partition (P '' D) ≤ Setoid.ker U)
    (hne : partition (P '' D') ≠ partition (P '' D)) :
    Better U μ (partition (P '' D)) (partition (P '' D')) :=
  better_of_lt_of_le_ker U μ hU ((partition_anti (Set.image_mono h)).lt_of_ne hne)

end Domain

end Question
