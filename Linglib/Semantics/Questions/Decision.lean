module

public import Linglib.Core.Probability.Decision.ValueOfInformation
public import Linglib.Semantics.Questions.Hamblin.Basic

/-!
# The value of a question

A decision problem is a prior `μ` over worlds together with a utility `U w a` for each action `a`
in each world `w`. Its value is `decisionValue U μ`, the best expected utility of an action.
Information `C` resolves the problem when some action is at least as good as every other
throughout `C` (`IsResolved`). Learning `C` replaces the prior by `μ[|C]`, and we define the
utility value of `C` as the change in the value of the problem,
`utilityValue U μ C = decisionValue U μ[|C] - decisionValue U μ`.

A question is a partition of the worlds, a `Setoid W`, whose answer in the world `w` is the cell
`Q.cell w`. We define the expected utility value `utility U μ Q` of a question as the value of
information of the experiment that observes the cell, `Quotient.mk Q`. On finitely many worlds it
is the expected utility value of the true answer, `∫ w, utilityValue U μ (Q.cell w) ∂μ`
(`utility_eq_integral`), which is the sum of the utility values of the cells weighted by their
probabilities (`utility_eq_sum`).

The trivial question `⊤` is worth nothing and the finest question `⊥` is worth the value of
perfect information, as is every question each of whose answers resolves the problem
(`utility_eq_utility_bot`). A finer question is worth at least as much (`utility_anti`), so
questions have nonnegative value, and refinement is exactly being at least as useful in every
decision problem (`le_iff_forall_utility_le`). A question is worth nothing exactly when an action
that is best now stays best at the answer in almost every world (`utility_eq_zero_iff`).

Relative to a decision problem, `Better U μ Q Q'` holds when `Q` is worth more than `Q'`, or as
much and strictly coarser. A question whose answers resolve the problem is better than every
strictly finer one (`better_of_isResolved_of_lt`). The wh-question over a domain `D` of
individuals with property `P` is the partition `Setoid.ofProps (P '' D)` of the worlds by which
individuals of `D` have the property; widening the domain cannot lower its value
(`utility_ofProps_image_mono`), and once the answers over the domain resolve the problem,
widening it gives a worse question (`better_ofProps_image`).

## Implementation notes

The value of a question is defined through the posterior of an experiment and not as a sum or
integral over cells of the prior conditioned on the cell. The two agree when the cells of
probability zero form a null set, as they do for countably many cells, and only the posterior is
defined beyond that. The theorems assume finitely many worlds and actions, as the value of
information they rest on does.

## TODO

* The converse of `utility_eq_utility_bot`: a question worth the value of perfect information
  has an answer resolving the problem, up to a null set, in almost every world.
* The value of a question whose answers overlap, through an experiment that draws a true answer.

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

variable {W : Type u} {A : Type*}

/-! ### Resolving a decision problem -/

section Resolved

variable {U : W → A → ℝ} {C D : Set W}

variable (U C) in
/-- Information `C` resolves the decision problem with utility `U` when some action is at least
as good as every other in every world of `C`. -/
def IsResolved : Prop := ∃ a, ∀ b, ∀ w ∈ C, U w b ≤ U w a

variable (U) in
/-- The proposition an action induces is the set of worlds where no action is strictly
better. -/
def optimalityRegion (a : A) : Set W := {w | ∀ b, U w b ≤ U w a}

/-- Information resolves the decision problem exactly when it lies within the optimality
region of some action. -/
theorem isResolved_iff_exists_subset_optimalityRegion :
    IsResolved U C ↔ ∃ a, C ⊆ optimalityRegion U a :=
  ⟨fun ⟨a, h⟩ ↦ ⟨a, fun _ hw b ↦ h b _ hw⟩, fun ⟨a, h⟩ ↦ ⟨a, fun _ _ hw ↦ h hw _⟩⟩

theorem IsResolved.mono (h : IsResolved U D) (hCD : C ⊆ D) : IsResolved U C :=
  h.imp fun _ ha b w hw ↦ ha b w (hCD hw)

end Resolved

variable [MeasurableSpace W]

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
noncomputable def valueOfSampleInformation (U : W → A → ℝ) (μ : Measure W) (a : A) (C : Set W) :
    ℝ :=
  decisionValue U μ[|C] - ∫ w, U w a ∂μ[|C]

theorem valueOfSampleInformation_nonneg [Finite A] (U : W → A → ℝ) (μ : Measure W) (a : A)
    (C : Set W) : 0 ≤ valueOfSampleInformation U μ a C :=
  sub_nonneg.2 (integral_le_decisionValue _ a)

variable (U : W → A → ℝ) (μ : Measure W) [IsFiniteMeasure μ] {s : Set W}

/-- Where the utilities are constant on `s`, the decision value of the prior conditioned on `s`
is the utility of the best action there. -/
theorem decisionValue_cond_of_forall_eq {w : W} (hs : ∀ v ∈ s, U v = U w)
    (hsm : MeasurableSet s) (hμ : μ s ≠ 0) : decisionValue U μ[|s] = ⨆ a, U w a := by
  have := cond_isProbabilityMeasure (μ := μ) hμ
  refine iSup_congr fun a ↦ ?_
  rw [integral_congr_ae (g := fun _ ↦ U w a)
    ((ae_cond_mem hsm).mono fun v hv ↦ by simp only [hs v hv])]
  simp

/-- Conditioned on information that resolves the problem, the decision value is the expected
utility of the best action in each world. -/
theorem decisionValue_cond_of_isResolved [Finite W] [DiscreteMeasurableSpace W] [Finite A]
    (hs : IsResolved U s) (hμ : μ s ≠ 0) :
    decisionValue U μ[|s] = ∫ w, ⨆ a, U w a ∂μ[|s] := by
  obtain ⟨a, ha⟩ := hs
  have : Nonempty A := ⟨a⟩
  have := cond_isProbabilityMeasure (μ := μ) hμ
  have hsup : ∀ᵐ w ∂μ[|s], ⨆ b, U w b = U w a := (ae_cond_mem .of_discrete).mono fun w hw ↦
    le_antisymm (ciSup_le fun b ↦ ha b w hw) (le_ciSup (Set.finite_range _).bddAbove a)
  rw [integral_congr_ae hsup]
  exact le_antisymm (ciSup_le fun b ↦ integral_mono_ae .of_finite .of_finite
    ((ae_cond_mem .of_discrete).mono fun w hw ↦ ha b w hw)) (integral_le_decisionValue _ a)

end Answer

/-! ### The utility of questions -/

section Utility

variable [StandardBorelSpace W] [Nonempty W]

/-- The expected utility value of a question is the value of information of the experiment that
observes its answer. -/
noncomputable def utility (U : W → A → ℝ) (μ : Measure W) [IsFiniteMeasure μ] (Q : Setoid W) :
    ℝ :=
  valueOfInformation (decisionValue U)
    (Kernel.deterministic (Quotient.mk Q) (measurable_quotient_mk'' (s := Q))) μ

/-- Relative to a decision problem, a question is better than another when it is more useful, or
as useful and strictly coarser, since one should not ask for irrelevant information. -/
def Better (U : W → A → ℝ) (μ : Measure W) [IsFiniteMeasure μ] (Q Q' : Setoid W) : Prop :=
  toLex (utility U μ Q', Q') < toLex (utility U μ Q, Q)

theorem better_iff {U : W → A → ℝ} {μ : Measure W} [IsFiniteMeasure μ] {Q Q' : Setoid W} :
    Better U μ Q Q' ↔ utility U μ Q' < utility U μ Q ∨ utility U μ Q = utility U μ Q' ∧ Q' < Q := by
  simp [Better, Prod.Lex.toLex_lt_toLex, eq_comm]

instance (U : W → A → ℝ) (μ : Measure W) [IsFiniteMeasure μ] :
    IsStrictOrder (Setoid W) (Better U μ) where
  irrefl _ := lt_irrefl _
  trans _ _ _ h h' := lt_trans h' h

variable (U : W → A → ℝ) (μ : Measure W) [IsProbabilityMeasure μ]

/-- The trivial question is worth nothing. -/
@[simp]
theorem utility_top : utility U μ ⊤ = 0 := by
  have h : Kernel.deterministic (Quotient.mk (⊤ : Setoid W)) (measurable_quotient_mk'' (s := ⊤)) =
      Kernel.const W (Measure.dirac (Quotient.mk ⊤ (Classical.arbitrary W))) :=
    Kernel.ext fun w ↦ by
      rw [Kernel.deterministic_apply, Kernel.const_apply]
      exact congrArg _ (Quotient.eq.2 (by simp [Setoid.top_def]))
  simp only [utility, h, valueOfInformation_const]

variable [Finite W] [DiscreteMeasurableSpace W]

omit [StandardBorelSpace W] [Nonempty W] in
private theorem integral_cell (F : Set W → ℝ) (Q : Setoid W) [Fintype (Quotient Q)] :
    ∫ w, F (Q.cell w) ∂μ =
      ∑ c : Quotient Q, μ.real (Quotient.mk Q ⁻¹' {c}) * F (Quotient.mk Q ⁻¹' {c}) := by
  simp_rw [Setoid.cell_eq_preimage_mk]
  exact integral_preimage_singleton F .of_discrete μ

omit [DiscreteMeasurableSpace W] in
private theorem integral_integral_cond_cell (g : W → ℝ) (Q : Setoid W) :
    ∫ w, ∫ v, g v ∂μ[|Q.cell w] ∂μ = ∫ w, g w ∂μ := by
  cases nonempty_fintype (Quotient Q)
  simp_rw [Setoid.cell_eq_preimage_mk]
  exact integral_integral_cond_preimage g _ μ

theorem utility_eq_integral_sub (Q : Setoid W) :
    utility U μ Q = ∫ w, decisionValue U μ[|Q.cell w] ∂μ - decisionValue U μ := by
  cases nonempty_fintype (Quotient Q)
  rw [utility, valueOfInformation_deterministic,
    integral_cell μ (fun c ↦ decisionValue U μ[|c])]

/-- The expected utility value of a question is the expected utility value of its true
answer. -/
theorem utility_eq_integral (Q : Setoid W) :
    utility U μ Q = ∫ w, utilityValue U μ (Q.cell w) ∂μ := by
  simp [utility_eq_integral_sub, utilityValue, integral_sub (μ := μ) .of_finite .of_finite]

/-- The expected utility value of a question is the sum of the utility values of its cells
weighted by their probabilities. -/
theorem utility_eq_sum (Q : Setoid W) [Fintype (Quotient Q)] :
    utility U μ Q = ∑ c : Quotient Q,
      μ.real (Quotient.mk Q ⁻¹' {c}) * utilityValue U μ (Quotient.mk Q ⁻¹' {c}) :=
  (utility_eq_integral U μ Q).trans (integral_cell μ _ Q)

/-- The finest question is worth the value of perfect information. -/
theorem utility_bot : utility U μ ⊥ = valueOfInformation (decisionValue U) Kernel.id μ := by
  rw [utility_eq_integral_sub, valueOfInformation_id]
  simp only [decisionValue_dirac, Setoid.cell_bot]
  congr 1
  exact integral_congr_ae (ae_iff_of_countable.2 fun w hw ↦
    decisionValue_cond_of_forall_eq U μ (fun v hv ↦ by rw [Set.mem_singleton_iff.1 hv])
      .of_discrete hw)

/-- A question each of whose answers resolves the decision problem is worth the value of perfect
information. -/
theorem utility_eq_utility_bot [Finite A] {Q : Setoid W} (hQ : ∀ w, IsResolved U (Q.cell w)) :
    utility U μ Q = utility U μ ⊥ := by
  rw [utility_bot, utility_eq_integral_sub, valueOfInformation_id]
  simp only [decisionValue_dirac]
  rw [← integral_integral_cond_cell μ (fun w ↦ ⨆ a, U w a) Q]
  congr 1
  exact integral_congr_ae (ae_iff_of_countable.2 fun w hw ↦
    decisionValue_cond_of_isResolved U μ (hQ w) fun h ↦
      hw (measure_mono_null (Set.singleton_subset_iff.2 (Q.mem_cell_self w)) h))

/-- A finer question is worth at least as much. -/
theorem utility_anti [Finite A] : Antitone (utility U μ) := fun Q Q' h ↦ by
  cases nonempty_fintype (Quotient Q)
  exact valueOfInformation_decisionValue_le_of_factorsThrough U _ _
    (fun _ _ hab ↦ Quotient.sound (h (Quotient.exact hab))) μ

/-- The expected utility value as a monotone map into the dual of the reals. -/
noncomputable def utilityOrderHom [Finite A] : Setoid W →o ℝᵒᵈ where
  toFun Q := OrderDual.toDual (utility U μ Q)
  monotone' := utility_anti U μ

@[simp]
theorem utilityOrderHom_apply [Finite A] (Q : Setoid W) :
    utilityOrderHom U μ Q = OrderDual.toDual (utility U μ Q) := rfl

theorem utility_nonneg [Finite A] (Q : Setoid W) : 0 ≤ utility U μ Q :=
  (utility_top U μ).ge.trans (utility_anti U μ le_top)

theorem utility_le_utility_bot [Finite A] (Q : Setoid W) : utility U μ Q ≤ utility U μ ⊥ :=
  utility_anti U μ bot_le

/-- The expected utility value of a question is its expected value of sample information over an
action that is best now. -/
theorem utility_eq_integral_valueOfSampleInformation (Q : Setoid W) {a : A}
    (ha : ∫ w, U w a ∂μ = decisionValue U μ) :
    utility U μ Q = ∫ w, valueOfSampleInformation U μ a (Q.cell w) ∂μ := by
  simp only [valueOfSampleInformation]
  rw [integral_sub .of_finite .of_finite, integral_integral_cond_cell μ (fun v ↦ U v a) Q, ha,
    utility_eq_integral_sub]

/-- A question is worthless exactly when an action that is best now stays best at the answer in
almost every world. -/
theorem utility_eq_zero_iff [Finite A] (Q : Setoid W) {a : A}
    (ha : ∫ w, U w a ∂μ = decisionValue U μ) :
    utility U μ Q = 0 ↔
      ∀ᵐ w ∂μ, ∫ v, U v a ∂μ[|Q.cell w] = decisionValue U μ[|Q.cell w] := by
  rw [utility_eq_integral_valueOfSampleInformation U μ Q ha, integral_eq_zero_iff_of_nonneg
    (fun w ↦ valueOfSampleInformation_nonneg U μ a _) .of_finite]
  exact Filter.eventually_congr (.of_forall fun w ↦ sub_eq_zero.trans eq_comm)

/-- One question refines another exactly when it is at least as useful in every decision problem
with a probability prior, a case of the comparison of experiments of [blackwell-1953]. -/
theorem le_iff_forall_utility_le (Q Q' : Setoid W) :
    Q ≤ Q' ↔ ∀ {B : Type u} [Finite B] (U : W → B → ℝ) (μ : Measure W) [IsProbabilityMeasure μ],
      utility U μ Q' ≤ utility U μ Q := by
  refine ⟨fun h _ _ U μ _ ↦ utility_anti U μ h, fun h ↦ ?_⟩
  cases nonempty_fintype W
  cases nonempty_fintype (Quotient Q)
  cases nonempty_fintype (Quotient Q')
  have : Nonempty (Quotient Q') := Nonempty.map (Quotient.mk Q') inferInstance
  obtain ⟨ψ, hψ⟩ := exists_eq_comp_of_forall_valueOfInformation_le (Quotient.mk Q)
    (Quotient.mk Q') fun U ↦ h U (uniformOn Set.univ)
  exact fun a b hab ↦ Quotient.exact <| by
    rw [show Quotient.mk Q' a = ψ (Quotient.mk Q a) from congrFun hψ a,
      show Quotient.mk Q' b = ψ (Quotient.mk Q b) from congrFun hψ b, Quotient.sound hab]

/-- A question each of whose answers resolves the decision problem is better than every strictly
finer question. -/
theorem better_of_isResolved_of_lt [Finite A] {Q Q' : Setoid W}
    (hQ : ∀ w, IsResolved U (Q.cell w)) (h : Q' < Q) : Better U μ Q Q' :=
  better_iff.2 (.inr ⟨by rw [utility_eq_utility_bot U μ hQ,
    utility_eq_utility_bot U μ fun w ↦ (hQ w).mono fun _ hv ↦ h.le hv], h⟩)

end Utility

/-! ### The domain of a wh-phrase -/

section Domain

variable [Finite W] [DiscreteMeasurableSpace W] [Nonempty W] [Finite A] (U : W → A → ℝ)
  (μ : Measure W) [IsProbabilityMeasure μ] {E : Type*} (P : E → Set W) {D D' : Set E}

/-- Widening the domain of a wh-question cannot lower its value. -/
theorem utility_ofProps_image_mono (h : D ⊆ D') :
    utility U μ (Setoid.ofProps (P '' D)) ≤ utility U μ (Setoid.ofProps (P '' D')) :=
  utility_anti U μ (Setoid.ofProps_anti (Set.image_mono h))

/-- When every answer to the wh-question over `D` resolves the decision problem, every larger
domain yielding a different question gives a worse one. -/
theorem better_ofProps_image (h : D ⊆ D')
    (hU : ∀ w, IsResolved U ((Setoid.ofProps (P '' D)).cell w))
    (hne : Setoid.ofProps (P '' D') ≠ Setoid.ofProps (P '' D)) :
    Better U μ (Setoid.ofProps (P '' D)) (Setoid.ofProps (P '' D')) :=
  better_of_isResolved_of_lt U μ hU ((Setoid.ofProps_anti (Set.image_mono h)).lt_of_ne hne)

end Domain

end Question
