/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.AutoregressiveSequenceModel.Tight
public import Linglib.Core.Probability.Kernel.IonescuTulcea.SeqLaw
public import Mathlib.Data.List.ReduceOption

/-!
# The trajectory of an autoregressive sequence model

The model is a prediction rule on the extended alphabet, the end of the string absorbing, and the
Ionescu–Tulcea theorem gives the law of its whole trajectory, a probability measure on infinite
sequences of symbols or ends. Survival is the probability that none of the first `n` symbols is
the end, a string's probability is that of the trajectories that spell it and then end, and the
model is tight exactly when the trajectory ends almost surely, which is how [du-etal-2023] define
tightness.

## Main definitions

* `rule`: the model as a prediction rule on the extended alphabet.
* `trajectory`: the law of its whole trajectory.

## Main results

* `trajectory_setOf_forall_lt_ne_none`, `trajectory_cylinder`: survival and string probabilities
  as probabilities of the trajectory.
* `isTight_iff_trajectory_setOf_forall_ne_none`: tight exactly when the trajectory ends almost
  surely.

## References

* [du-etal-2023]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Preorder

namespace AutoregressiveSequenceModel

private theorem reduceOption_map_some {α : Type*} (l : List α) :
    (l.map some).reduceOption = l := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, List.reduceOption_cons_of_some, ih]


variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  (M : AutoregressiveSequenceModel α)

theorem measurableSet_setOf_forall_lt_ne_none (n : ℕ) :
    MeasurableSet {ω : ℕ → Option α | ∀ i < n, ω i ≠ none} := by
  have hi (i : ℕ) : MeasurableSet {ω : ℕ → Option α | ω i ≠ none} :=
    (measurableSet_singleton (none : Option α)).compl.preimage (measurable_pi_apply i)
  simp_rw [Set.ofPred_forall]
  exact .iInter fun i ↦ .iInter fun _ ↦ hi i


variable [Countable α]

/-! ### The trajectory

The model is a prediction rule on the extended alphabet, with the end absorbing, and the law of
its whole trajectory is the Ionescu–Tulcea trajectory measure of that rule. -/

open Classical in
/-- The model as a prediction rule on the extended alphabet: after a history of units it draws
the next unit, and after the end of the string it stays at the end. -/
noncomputable def rule (n : ℕ) : Kernel (Fin n → Option α) (Option α) :=
  Kernel.ofFunOfCountable fun h ↦
    if ∀ i, h i ≠ none then M.next (List.ofFn h).reduceOption else Measure.dirac none

instance (n : ℕ) : IsMarkovKernel (M.rule n) :=
  ⟨fun h ↦ by
    change IsProbabilityMeasure (if ∀ i, h i ≠ none then _ else _)
    split_ifs <;> infer_instance⟩

/-- After a history of units the rule is the model's next-unit distribution. -/
theorem rule_apply_some {n : ℕ} (f : Fin n → α) :
    M.rule n (some ∘ f) = M.next (List.ofFn f) := by
  change (if ∀ i, (some ∘ f) i ≠ none then _ else _) = _
  simp only [Function.comp_apply, ne_eq, Option.some_ne_none, not_false_eq_true, implies_true,
    ite_true, ← List.map_ofFn, reduceOption_map_some]

/-- The mass of a history of units is its prefix probability. -/
theorem seqLaw_rule_singleton_some : ∀ {n : ℕ} (f : Fin n → α),
    seqLaw M.rule n {some ∘ f} = M.prefixProb (List.ofFn f)
  | 0, f => by
    rw [seqLaw_zero, Measure.dirac_apply_of_mem (Set.mem_singleton_iff.2 (Subsingleton.elim _ _)),
      List.ofFn_zero, prefixProb_nil]
  | n + 1, f => by
    conv_lhs => rw [← Fin.snoc_init_self (some ∘ f)]
    rw [seqLaw_succ_singleton_snoc, show Fin.init (some ∘ f) = some ∘ Fin.init f from rfl,
      seqLaw_rule_singleton_some, rule_apply_some, List.ofFn_succ', List.concat_eq_append,
      prefixProb_concat]
    rfl

/-- Survival to `n` is the law of the first `n` draws on the histories of units. -/
theorem survival_eq_seqLaw (n : ℕ) :
    M.survival n = seqLaw M.rule n {h | ∀ i, h i ≠ none} := by
  have hU : {h : Fin n → Option α | ∀ i, h i ≠ none} = Set.range (some ∘ ·) := by
    ext h
    simp [Option.ne_none_iff_exists, Classical.skolem, funext_iff]
  rw [hU, measure_range_eq_tsum (Option.some_injective α).comp_left, survival]
  show ∑' x : List.Vector α n, M.prefixProb x.1 = _
  rw [← (Equiv.vectorEquivFin α n).symm.tsum_eq]
  exact tsum_congr fun f ↦ by
    rw [seqLaw_rule_singleton_some]
    exact congrArg M.prefixProb (List.Vector.toList_ofFn f)

/-- The law of the whole trajectory of the model: the units it generates one after another,
with the end of the string absorbing. -/
noncomputable def trajectory : Measure (ℕ → Option α) := seqTrajectory M.rule

instance : IsProbabilityMeasure M.trajectory := by
  unfold trajectory; infer_instance

/-- Survival to `n` is the probability that none of the first `n` units is the end. -/
theorem trajectory_setOf_forall_lt_ne_none (n : ℕ) :
    M.trajectory {ω | ∀ i < n, ω i ≠ none} = M.survival n := by
  cases n with
  | zero => simp
  | succ n =>
    have hpre : (trajEquivFin n ∘ frestrictLe (π := fun _ : ℕ ↦ Option α) n) ⁻¹'
        {h : Fin (n + 1) → Option α | ∀ i, h i ≠ none} =
          {ω : ℕ → Option α | ∀ i < n + 1, ω i ≠ none} := by
      ext ω
      simp only [Set.mem_preimage, Function.comp_apply, Set.mem_ofPred_eq, trajEquivFin_apply,
        frestrictLe_apply, Fin.forall_iff]
    rw [survival_eq_seqLaw, trajectory, ← seqTrajectory_map_frestrictLe,
      Measure.map_apply ((trajEquivFin n).measurable.comp (measurable_frestrictLe n))
        (Set.to_countable _).measurableSet, hpre]

/-- The probability that the string never ends is the infimum of survival. -/
theorem trajectory_setOf_forall_ne_none :
    M.trajectory {ω | ∀ i, ω i ≠ none} = ⨅ n, M.survival n := by
  have h : {ω : ℕ → Option α | ∀ i, ω i ≠ none} = ⋂ n, {ω | ∀ i < n, ω i ≠ none} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨fun h n i _ ↦ h i, fun h i ↦ h (i + 1) i i.lt_succ_self⟩
  rw [h, Antitone.measure_iInter (s := fun n ↦ {ω : ℕ → Option α | ∀ i < n, ω i ≠ none})
    (fun m n hmn ω hω i hi ↦ hω i (hi.trans_le hmn))
    (fun n ↦ (measurableSet_setOf_forall_lt_ne_none n).nullMeasurableSet)
    ⟨0, measure_ne_top _ _⟩]
  exact iInf_congr M.trajectory_setOf_forall_lt_ne_none

/-- A model is tight exactly when its trajectory ends almost surely, [du-etal-2023]'s definition
of tightness. -/
theorem isTight_iff_trajectory_setOf_forall_ne_none :
    M.IsTight ↔ M.trajectory {ω | ∀ i, ω i ≠ none} = 0 := by
  rw [trajectory_setOf_forall_ne_none, isTight_iff_tendsto_survival]
  have hinf := tendsto_atTop_iInf M.survival_antitone
  exact ⟨fun h ↦ tendsto_nhds_unique hinf h, fun h ↦ h ▸ hinf⟩

/-- The probability of generating exactly the string `List.ofFn f` is the probability that the
trajectory begins with its units and then ends. -/
theorem trajectory_cylinder {n : ℕ} (f : Fin n → α) :
    M.trajectory {ω | (∀ i : Fin n, ω i = some (f i)) ∧ ω n = none} =
      M.stringProb (List.ofFn f) := by
  have hpre : (trajEquivFin n ∘ frestrictLe (π := fun _ : ℕ ↦ Option α) n) ⁻¹'
      {Fin.snoc (some ∘ f) none} =
        {ω : ℕ → Option α | (∀ i : Fin n, ω i = some (f i)) ∧ ω n = none} := by
    ext ω
    simp only [Set.mem_preimage, Function.comp_apply, Set.mem_singleton_iff, funext_iff,
      trajEquivFin_apply, frestrictLe_apply, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨fun i ↦ by simpa using h i.castSucc, by simpa using h (Fin.last n)⟩
    · rintro ⟨h₁, h₂⟩ j
      induction j using Fin.lastCases with
      | last => simpa using h₂
      | cast i => simpa using h₁ i
  rw [trajectory, ← hpre, ← Measure.map_apply ((trajEquivFin n).measurable.comp
    (measurable_frestrictLe n)) (measurableSet_singleton _), seqTrajectory_map_frestrictLe,
    seqLaw_succ_singleton_snoc, seqLaw_rule_singleton_some, rule_apply_some, stringProb]

end AutoregressiveSequenceModel
