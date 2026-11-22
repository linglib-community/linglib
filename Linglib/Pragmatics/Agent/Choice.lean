module

public import Linglib.Core.Probability.Choice.ChoiceAxiom
public import Linglib.Pragmatics.Agent.Basic

/-!
# Choice from a menu

An agent confined to a menu of actions, `Agent.restrict`, is the same agent with every action off
the menu ruled out, so the feasible actions of the confined agent are the feasible actions on the
menu. The policy of an unconstrained agent confined to a menu is its policy conditioned on the
menu (`Agent.restrict_policy_eq_cond`): what it chooses from a menu does not depend on what else
it might have been offered.

The choices of such an agent from every menu therefore form a system of choice probabilities with
a ratio scale, its policy (`Agent.hasRatioScale_choiceFn`), and satisfy the constant-ratio rule
(`Agent.hasPairwiseIIA_choiceFn`). Conversely a system of choice probabilities with a ratio scale
is the choices of an agent (`Agent.exists_restrict_policy_eq_of_hasRatioScale`), so by
`ProbabilityTheory.ChoiceFn.hasRatioScale_iff_hasPairwiseIIA` the systems that satisfy the
constant-ratio rule and choose every alternative with positive probability are the choices of
agents.

## References

* [luce-1959]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Agent

variable {O S A : Type*} [MeasurableSpace O] [MeasurableSpace S] (a : Agent O S A)

open Classical in
/-- The agent confined to a menu: every action off the menu is ruled out at every state. -/
noncomputable def restrict (T : Finset A) : Agent O S A :=
  ⟨a.belief, fun s x ↦ if x ∈ T then a.utility s x else ⊥⟩

variable {a} {o : O} {x : A} {T : Finset A}

theorem restrict_value_of_mem (hx : x ∈ T) : (a.restrict T).value o x = a.value o x := by
  simp [restrict, value, hx]

/-- The feasible actions of an unconstrained agent confined to a menu are the actions on it. -/
theorem restrict_feasible_iff [a.IsUnconstrained] [NeZero (a.belief o)] :
    (a.restrict T).Feasible o x ↔ x ∈ T := by
  classical
  unfold Feasible restrict
  by_cases hx : x ∈ T
  · simp only [hx, ↓reduceIte, iff_true]
    exact IsUnconstrained.feasible o x
  · simp only [hx, ↓reduceIte, Set.ofPred_true, iff_false]
    exact Measure.measure_univ_ne_zero.2 (NeZero.ne _)

variable [Countable O] [MeasurableSingletonClass O] [Fintype A] [MeasurableSpace A]
  [MeasurableSingletonClass A] {β : ℝ}

/-- The policy of an unconstrained agent confined to a menu is its policy conditioned on the
menu. -/
theorem restrict_policy_eq_cond [a.IsUnconstrained] [NeZero (a.belief o)] (hβ : 0 < β)
    (hT : T.Nonempty) : (a.restrict T).policy β o = (a.policy β o)[|↑T] := by
  classical
  obtain ⟨x₀, -⟩ := hT.exists_mem
  have : Nonempty A := ⟨x₀⟩
  have hw (y : A) : EReal.exp (β * if (a.restrict T).Feasible o y then
      ((a.restrict T).value o y : EReal) else ⊥) =
      if y ∈ T then ENNReal.ofReal (Real.exp (β * a.value o y)) else 0 := by
    by_cases hy : y ∈ T
    · simp only [restrict_feasible_iff, hy, ↓reduceIte, restrict_value_of_mem hy]
      rw [← EReal.coe_mul, EReal.exp_coe]
    · simp only [restrict_feasible_iff, hy, ↓reduceIte]
      rw [EReal.coe_mul_bot_of_pos hβ, EReal.exp_bot]
  have hL (y : A) : (if y ∈ T then ENNReal.ofReal (Real.exp (β * a.value o y)) else 0).toReal =
      if y ∈ T then Real.exp (β * a.value o y) else 0 := by
    split_ifs <;> simp [(Real.exp_pos _).le]
  have hP (y : A) : (a.policy β o).real {y} =
      Real.exp (β * a.value o y) / ∑ z, Real.exp (β * a.value o z) := by
    rw [policy_real_singleton, Real.softmax_apply]
  have hPT : (a.policy β o).real ↑T =
      (∑ y ∈ T, Real.exp (β * a.value o y)) / ∑ z, Real.exp (β * a.value o z) := by
    rw [← sum_measureReal_singleton, Finset.sum_div]
    exact Finset.sum_congr rfl fun y _ ↦ hP y
  have hT0 : 0 < ∑ y ∈ T, Real.exp (β * a.value o y) :=
    Finset.sum_pos (fun y _ ↦ Real.exp_pos _) hT
  have hZ : 0 < ∑ z, Real.exp (β * a.value o z) :=
    Finset.sum_pos (fun y _ ↦ Real.exp_pos _) Finset.univ_nonempty
  refine Measure.ext_of_singleton fun y ↦ ?_
  have hlhs : ((a.restrict T).policy β o).real {y} =
      (if y ∈ T then Real.exp (β * a.value o y) else 0) /
        ∑ z ∈ T, Real.exp (β * a.value o z) := by
    unfold policy Kernel.softmax
    rw [Kernel.ofWeights_real_singleton _ _ fun z ↦ by rw [hw]; split_ifs <;> simp]
    simp only [hw, hL, Finset.sum_ite_mem, Finset.univ_inter]
  have hrhs : ((a.policy β o)[|↑T]).real {y} =
      (if y ∈ T then Real.exp (β * a.value o y) else 0) /
        ∑ z ∈ T, Real.exp (β * a.value o z) := by
    rw [cond_real_apply _ T.measurableSet, hPT]
    by_cases hy : y ∈ T
    · rw [Set.inter_singleton_of_mem (Finset.mem_coe.2 hy), hP]
      simp only [hy, ↓reduceIte]
      field_simp
    · rw [Set.inter_singleton_eq_empty.2 (by simpa using hy), measureReal_empty]
      simp only [hy, ↓reduceIte, zero_div]
  rw [← ofReal_measureReal (measure_ne_top _ _), ← ofReal_measureReal (measure_ne_top _ _), hlhs,
    hrhs]

section ChoiceFn

variable (a) [a.IsUnconstrained] (o) [NeZero (a.belief o)] (β)

/-- The choices of an unconstrained agent from every menu at an observation. -/
noncomputable def choiceFn (hβ : 0 < β) : ChoiceFn A where
  prob T := (a.restrict T).policy β o
  isProbabilityMeasure_prob T hT := by
    obtain ⟨x₀, hx₀⟩ := hT.exists_mem
    have : Nonempty A := ⟨x₀⟩
    rw [restrict_policy_eq_cond hβ hT]
    exact cond_isProbabilityMeasure fun h ↦
      a.policy_apply_singleton_ne_zero β o x₀
        (measure_mono_null (Set.singleton_subset_iff.2 (Finset.mem_coe.2 hx₀)) h)
  prob_compl T := by
    rw [measure_null_iff_singleton (Set.to_countable _)]
    intro y hy
    by_contra h
    exact hy (Finset.mem_coe.2 (restrict_feasible_iff.1
      (((a.restrict T).policy_apply_singleton_ne_zero_iff hβ o y).1 h)))

/-- The choices of an unconstrained agent have a ratio scale, its policy. -/
theorem hasRatioScale_choiceFn (hβ : 0 < β) : (a.choiceFn o β hβ).HasRatioScale :=
  ⟨a.policy β o, fun y ↦ a.policy_apply_singleton_ne_zero β o y, fun _ ↦ measure_ne_top _ _,
    fun _ hT ↦ restrict_policy_eq_cond hβ hT⟩

/-- The choices of an unconstrained agent satisfy the constant-ratio rule. -/
theorem hasPairwiseIIA_choiceFn [DecidableEq A] (hβ : 0 < β) :
    (a.choiceFn o β hβ).HasPairwiseIIA :=
  (a.hasRatioScale_choiceFn o β hβ).hasPairwiseIIA

end ChoiceFn

/-- A system of choice probabilities with a ratio scale is the choices of an agent, who values an
alternative at the logarithm of its scale value. -/
theorem exists_restrict_policy_eq_of_hasRatioScale {cf : ChoiceFn A} (h : cf.HasRatioScale) :
    ∃ a : Agent Unit Unit A, a.IsUnconstrained ∧
      ∀ T : Finset A, T.Nonempty → cf.prob T = (a.restrict T).policy 1 () := by
  obtain ⟨μ, h0, htop, hμ⟩ := h
  rcases isEmpty_or_nonempty A with hA | hA
  · exact ⟨⟨Kernel.const Unit (Measure.dirac ()), fun _ x ↦ ((0 : ℝ) : EReal)⟩, inferInstance,
      fun T hT ↦ (hA.false hT.choose).elim⟩
  have hfin : μ Set.univ ≠ ∞ := by
    rw [← Finset.coe_univ, ← sum_measure_singleton]
    exact ENNReal.sum_ne_top.2 fun x _ ↦ htop x
  have : IsFiniteMeasure μ := ⟨hfin.lt_top⟩
  have hpos (x : A) : 0 < μ.real {x} := ENNReal.toReal_pos (h0 x) (htop x)
  have huniv : μ Set.univ ≠ 0 := fun h ↦ h0 hA.some (measure_mono_null (Set.subset_univ _) h)
  refine ⟨⟨Kernel.const Unit (Measure.dirac ()), fun _ x ↦ ((Real.log (μ.real {x}) : ℝ) : EReal)⟩,
    inferInstance, fun T hT ↦ ?_⟩
  have hpol : (Agent.mk (Kernel.const Unit (Measure.dirac ()))
      fun _ x ↦ ((Real.log (μ.real {x}) : ℝ) : EReal)).policy 1 () = (μ Set.univ)⁻¹ • μ := by
    refine Measure.ext_of_singleton fun x ↦ ?_
    rw [← ofReal_measureReal (measure_ne_top _ _), policy_real_singleton, Real.softmax_apply]
    simp only [value_coe, Kernel.const_apply, integral_dirac, one_mul, Real.exp_log (hpos _)]
    rw [sum_measureReal_singleton, Finset.coe_univ, smul_apply, smul_eq_mul, measureReal_def,
      measureReal_def, ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos huniv hfin),
      ENNReal.ofReal_toReal (htop x), ENNReal.ofReal_toReal hfin, ENNReal.div_eq_inv_mul]
  have : NeZero ((Agent.mk (Kernel.const Unit (Measure.dirac ()))
      fun _ x ↦ ((Real.log (μ.real {x}) : ℝ) : EReal)).belief ()) :=
    inferInstanceAs (NeZero (Measure.dirac ()))
  rw [restrict_policy_eq_cond one_pos hT, hpol, hμ T hT,
    cond_smul (ENNReal.inv_ne_zero.2 hfin) (ENNReal.inv_ne_top.2 huniv)]

end Agent
