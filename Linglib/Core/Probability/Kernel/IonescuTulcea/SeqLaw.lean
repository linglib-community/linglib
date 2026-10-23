/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.Kernel.IonescuTulcea.PartialTraj
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Take
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Sequences drawn from a prediction rule

A *prediction rule* gives, after every finite sequence of draws, the distribution of the next
draw: a family of kernels `κ n : Kernel (Fin n → α) α` ([pitman-2006] p. 45 and p. 58).
`seqLaw κ n` is the law of the first `n` draws, built one draw at a time: the empty sequence,
then the joint law of the sequence so far and the next draw, appended with `Fin.snoc`.

On a countable space the mass of a sequence is the product, along the sequence, of the
probability of each draw given the ones before it (`seqLaw_singleton`). This is the `Fin`-indexed
form of the Ionescu–Tulcea partial trajectory: after the first draw, the law of the next `n` is
`ProbabilityTheory.Kernel.partialTraj` of the prediction rule read on trajectories
(`seqLaw_succ_eq_map_partialTraj`).

## Main definitions

* `ProbabilityTheory.seqLaw κ n`: the law of the first `n` draws of the prediction rule `κ`.
* `ProbabilityTheory.seqTrajectory κ`: the law of the whole sequence of draws, the Ionescu–Tulcea
  trajectory measure started at the first draw.

## Main results

* `ProbabilityTheory.isProbabilityMeasure_seqLaw`: a Markov prediction rule gives probability
  laws.
* `ProbabilityTheory.seqLaw_succ_singleton_snoc`, `ProbabilityTheory.seqLaw_singleton`: the chain
  rule on a countable space.
* `ProbabilityTheory.integral_seqLaw_succ`: the chain rule for expectations.
* `ProbabilityTheory.seqLaw_succ_eq_map_partialTraj`: the law as a partial trajectory.
* `ProbabilityTheory.seqTrajectory_map_frestrictLe`: the first draws of the whole sequence have
  the law of the first draws.

## References

* [pitman-2006]
-/

@[expose] public section

open MeasureTheory Finset Preorder
open scoped ENNReal

namespace ProbabilityTheory

variable {α : Type*} [MeasurableSpace α] {κ : (n : ℕ) → Kernel (Fin n → α) α}

theorem measurable_snoc_prod {n : ℕ} :
    Measurable fun p : (Fin n → α) × α ↦ (Fin.snoc p.1 p.2 : Fin (n + 1) → α) :=
  .of_eval fun i ↦ by
    cases i using Fin.lastCases with
    | last => simpa using measurable_snd
    | cast i => simpa using measurable_fst.eval

variable (κ) in
/-- The law of the first `n` draws of the sequence with prediction rule `κ`: each draw is
sampled from `κ` at the sequence so far and appended to it. -/
noncomputable def seqLaw : (n : ℕ) → Measure (Fin n → α)
  | 0 => Measure.dirac default
  | n + 1 => (seqLaw n ⊗ₘ κ n).map fun p ↦ Fin.snoc p.1 p.2

@[simp] theorem seqLaw_zero : seqLaw κ 0 = Measure.dirac default := by
  rw [seqLaw]

theorem seqLaw_succ (n : ℕ) :
    seqLaw κ (n + 1) = (seqLaw κ n ⊗ₘ κ n).map fun p ↦ Fin.snoc p.1 p.2 := by
  rw [seqLaw]

theorem sFinite_seqLaw [∀ n, IsSFiniteKernel (κ n)] : ∀ n, SFinite (seqLaw κ n)
  | 0 => by rw [seqLaw_zero]; infer_instance
  | n + 1 => by
    have := sFinite_seqLaw n
    rw [seqLaw_succ]; infer_instance

instance [∀ n, IsSFiniteKernel (κ n)] (n : ℕ) : SFinite (seqLaw κ n) := sFinite_seqLaw n

theorem isProbabilityMeasure_seqLaw [∀ n, IsMarkovKernel (κ n)] :
    ∀ n, IsProbabilityMeasure (seqLaw κ n)
  | 0 => by rw [seqLaw_zero]; infer_instance
  | n + 1 => by
    have := isProbabilityMeasure_seqLaw n
    rw [seqLaw_succ]
    exact (Measure.isProbabilityMeasure_map_iff measurable_snoc_prod.aemeasurable).2 inferInstance

instance [∀ n, IsMarkovKernel (κ n)] (n : ℕ) : IsProbabilityMeasure (seqLaw κ n) :=
  isProbabilityMeasure_seqLaw n

theorem integral_seqLaw_succ [∀ n, IsSFiniteKernel (κ n)] {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : (Fin (n + 1) → α) → E}
    (hf : Integrable f (seqLaw κ (n + 1))) :
    ∫ s, f s ∂seqLaw κ (n + 1) = ∫ s, ∫ x, f (Fin.snoc s x) ∂κ n s ∂seqLaw κ n := by
  rw [seqLaw_succ] at hf ⊢
  rw [integral_map measurable_snoc_prod.aemeasurable hf.aestronglyMeasurable]
  exact Measure.integral_compProd
    ((integrable_map_measure hf.aestronglyMeasurable measurable_snoc_prod.aemeasurable).1 hf)

section Singleton

variable [MeasurableSingletonClass α] [∀ n, IsSFiniteKernel (κ n)]

theorem seqLaw_succ_singleton_snoc {n : ℕ} (s : Fin n → α) (c : α) :
    seqLaw κ (n + 1) {Fin.snoc s c} = seqLaw κ n {s} * κ n s {c} := by
  rw [seqLaw_succ, Measure.map_apply measurable_snoc_prod (measurableSet_singleton _),
    show (fun p : (Fin n → α) × α ↦ (Fin.snoc p.1 p.2 : Fin (n + 1) → α)) ⁻¹' {Fin.snoc s c} =
        {s} ×ˢ {c} from Set.ext fun p ↦ by
      simp [Prod.ext_iff, Fin.snoc_injective2.eq_iff],
    Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _),
    Measure.restrict_singleton, lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

theorem seqLaw_singleton : ∀ {n : ℕ} (x : Fin n → α),
    seqLaw κ n {x} = ∏ i : Fin n, κ i (Fin.take i i.2.le x) {x i}
  | 0, x => by simp [Subsingleton.elim x default]
  | n + 1, x => by
    conv_lhs => rw [← Fin.snoc_init_self x]
    rw [seqLaw_succ_singleton_snoc, seqLaw_singleton, Fin.prod_univ_castSucc]
    rfl

end Singleton

/-! ### The law as a partial trajectory -/

section Traj

/-- The times `0, …, n` are the indices of the first `n + 1` draws. -/
def _root_.Nat.iicEquivFin (n : ℕ) : (Iic n : Finset ℕ) ≃ Fin (n + 1) where
  toFun i := ⟨i, Nat.lt_succ_of_le (mem_Iic.1 i.2)⟩
  invFun j := ⟨j, mem_Iic.2 (Nat.le_of_lt_succ j.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A trajectory up to time `n` as the sequence of its first `n + 1` draws. -/
noncomputable def trajEquivFin (n : ℕ) : (Π _ : Iic n, α) ≃ᵐ (Fin (n + 1) → α) :=
  MeasurableEquiv.piCongrLeft (fun _ ↦ α) (Nat.iicEquivFin n)

@[simp] theorem trajEquivFin_apply (n : ℕ) (x : Π _ : Iic n, α) (j : Fin (n + 1)) :
    trajEquivFin n x j = x ⟨j, mem_Iic.2 (Nat.le_of_lt_succ j.2)⟩ := by
  simp [trajEquivFin, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rfl

variable (κ) in
/-- The prediction rule read on trajectories: after the draws at times `0, …, n`, the law of the
draw at time `n + 1`. -/
noncomputable def trajRule (n : ℕ) : Kernel (Π _ : Iic n, α) α :=
  (κ (n + 1)).comap (trajEquivFin n) (trajEquivFin n).measurable

variable [Countable α] [MeasurableSingletonClass α] [∀ n, IsMarkovKernel (κ n)]

instance (n : ℕ) : IsMarkovKernel (trajRule κ n) := by
  unfold trajRule; infer_instance

omit [∀ n, IsMarkovKernel (κ n)] in
private theorem comp_apply_singleton {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    [Countable β] [MeasurableSingletonClass β] [MeasurableSingletonClass γ] (η : Kernel β γ)
    (μ : Measure β) (z : γ) : (η ∘ₘ μ) {z} = ∑' x, μ {x} * η x {z} := by
  rw [Measure.comp_eq_sum_of_countable, Measure.sum_apply _ (measurableSet_singleton z)]
  rfl

private theorem partialTraj_comp_singleton (n : ℕ) (z : Π _ : Iic n, α) :
    (Kernel.partialTraj (X := fun _ ↦ α) (trajRule κ) 0 n ∘ₘ
      (κ 0 default).map (fun a (_ : Iic 0) ↦ a)) {z} = seqLaw κ (n + 1) {trajEquivFin n z} := by
  induction n with
  | zero =>
    have hpre : (fun a (_ : Iic 0) ↦ a) ⁻¹' {z} = {z ⟨0, mem_Iic.2 le_rfl⟩} :=
      Set.ext fun a ↦ ⟨fun h ↦ h ▸ rfl, fun h ↦ funext fun ⟨i, hi⟩ ↦ by
        obtain rfl := Nat.le_zero.1 (mem_Iic.1 hi)
        exact h⟩
    have he : trajEquivFin 0 z = Fin.snoc (default : Fin 0 → α) (z ⟨0, mem_Iic.2 le_rfl⟩) :=
      funext fun j ↦ by obtain rfl : j = Fin.last 0 := Fin.ext (by omega); simp; rfl
    rw [Kernel.partialTraj_self, Measure.id_comp, Measure.map_apply (by fun_prop)
      (measurableSet_singleton z), hpre, he, seqLaw_succ_singleton_snoc, seqLaw_zero,
      Measure.dirac_apply_of_mem (Set.mem_singleton _), one_mul]
  | succ n ih =>
    rw [comp_apply_singleton]
    simp_rw [Kernel.partialTraj_succ_apply_singleton (Nat.zero_le n), ← mul_assoc]
    rw [ENNReal.tsum_mul_right, ← comp_apply_singleton, ih]
    conv_rhs => rw [← Fin.snoc_init_self (trajEquivFin (n + 1) z)]
    rw [seqLaw_succ_singleton_snoc]
    rfl

theorem seqLaw_succ_eq_map_partialTraj (n : ℕ) :
    seqLaw κ (n + 1) = (Kernel.partialTraj (X := fun _ ↦ α) (trajRule κ) 0 n ∘ₘ
      (κ 0 default).map (fun a (_ : Iic 0) ↦ a)).map (trajEquivFin n) :=
  Measure.ext_of_singleton fun y ↦ by
    obtain ⟨z, rfl⟩ := (trajEquivFin n).surjective y
    rw [MeasurableEquiv.map_apply, show trajEquivFin n ⁻¹' {trajEquivFin n z} = {z} from
      Set.ext fun _ ↦ (trajEquivFin n).injective.eq_iff, partialTraj_comp_singleton]

variable (κ) in
/-- The law of the whole sequence of draws of the prediction rule `κ`: the Ionescu–Tulcea
trajectory measure started at the first draw. -/
noncomputable def seqTrajectory : Measure (ℕ → α) :=
  Kernel.trajMeasure (κ 0 default) (trajRule κ)

instance : IsProbabilityMeasure (seqTrajectory κ) := by
  unfold seqTrajectory; infer_instance

theorem seqTrajectory_map_frestrictLe (n : ℕ) :
    (seqTrajectory κ).map (trajEquivFin n ∘ frestrictLe n) = seqLaw κ (n + 1) := by
  rw [seqLaw_succ_eq_map_partialTraj, seqTrajectory, Kernel.trajMeasure,
    ← Measure.map_map (trajEquivFin n).measurable (measurable_frestrictLe n),
    Measure.map_comp _ _ (measurable_frestrictLe n), Kernel.traj_map_frestrictLe]
  rfl

end Traj

end ProbabilityTheory
