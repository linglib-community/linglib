/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.Kernel.IonescuTulcea.SeqLaw
public import Linglib.Core.Probability.Moments.Variance
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Pierrehumbert (2001): Exemplar dynamics: Word frequency, lenition and contrast

This file formalizes Pierrehumbert's exemplar model of production. A category is a list of
remembered tokens, each weighted by its age. To produce the category a speaker picks a target,
either an exemplar drawn with probability proportional to its weight or, under entrenchment, the
memory-weighted mean, and adds production noise and a constant lenition bias. Every produced token
is stored, so the list is drawn from a prediction rule and its law is `ProbabilityTheory.seqLaw`.

The paper presents its results as simulations; here they are exact statements about the expected
memory-weighted mean and spread. [A production moves the expected mean by the bias over the total
memory weight](##integral_memoryMean), so [a leniting change advances with
use](##lenition_advances_with_use). With one memory time in clock time, [a more frequent word is
further along](##lenition_advances_with_frequency) by [a small lead](##lenition_lead_le). The
expected spread [grows at every production](##spread_grows),
[without bound exactly when memory does not decay](##bddAbove_integral_memorySpread_iff), and
[entrenchment narrows it](##entrenchment_narrows).

## Implementation notes

* Every production is stored, the idealization of the paper's one-label figures. The single-label
  loop of its appendix stores a token only if its score is nonzero, a filter the theorems leave
  out.
* Entrenchment is the memory-weighted mean of the whole list. That is the paper's rule exactly
  whenever the neighborhood holds at least as many exemplars as the list, so for the first 500
  productions of its simulations; the mean of the 500 nearest of a longer list is not formalized.
* The decay factor `γ` is `exp (-1/τ)` for the paper's memory time `τ`, and `γ = 1` is no decay.
  The paper's score and recency decay in clock time, so a word used every `r` ticks has exemplars
  `r` ticks apart, its own tokens decay by `γ ^ r`, and `rule (γ ^ r)` is its law. Words picked at
  random, as in the paper's two-label loop, are not formalized.
* The noise is any centered square-integrable law, and [the paper's is one](##memLp_noise).
* `spreadGrowth` takes the share of the memory spread that a target inherits as a real, so that the
  two targets share one recursion; only the values 0 and 1 are the paper's.
* Locators are those of the author's manuscript of June 2000.

## TODO

* The score function (1), the two-label loop of the appendix, and the neutralization of §4 (Fig. 5),
  in which a leniting marked category is absorbed by a stable unmarked one.
* The predictions that the distribution of a word in change is skewed according to the velocity of
  the change (§3.2), and that it approaches a Gaussian (§3.1).

## References

* [pierrehumbert-2001]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Filter
open scoped NNReal Topology

namespace Pierrehumbert2001

/-! ### The memory -/

section Memory

variable (γ : ℝ≥0) {n : ℕ}

private theorem sum_pow_rev {R : Type*} [CommSemiring R] (x : R) :
    ∑ i : Fin n, x ^ (i.rev : ℕ) = ∑ i ∈ range n, x ^ i :=
  (Equiv.sum_comp Fin.revPerm fun i : Fin n ↦ x ^ (i : ℕ)).trans (Fin.sum_univ_eq_sum_range _ n)

/-- The total weight of `n` exemplars, the `i`th youngest of which has weight `γ ^ i`. -/
noncomputable def totalWeight (n : ℕ) : ℝ := ∑ i ∈ range n, (γ : ℝ) ^ i

theorem totalWeight_succ : totalWeight γ (n + 1) = γ * totalWeight γ n + 1 := geom_sum_succ

theorem totalWeight_succ' : totalWeight γ (n + 1) = γ ^ n + totalWeight γ n := geom_sum_succ'

theorem totalWeight_nonneg : 0 ≤ totalWeight γ n := sum_nonneg fun _ _ ↦ by positivity

theorem one_le_totalWeight (hn : n ≠ 0) : 1 ≤ totalWeight γ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [totalWeight_succ]
  linarith [mul_nonneg γ.coe_nonneg (totalWeight_nonneg γ (n := m))]

theorem totalWeight_pos (hn : n ≠ 0) : 0 < totalWeight γ n :=
  one_pos.trans_le (one_le_totalWeight γ hn)

theorem totalWeight_mono : Monotone (totalWeight γ) :=
  monotone_nat_of_le_succ fun n ↦ by
    rw [totalWeight_succ']; exact le_add_of_nonneg_left (by positivity)

variable {γ} in
theorem totalWeight_strictMono (hγ0 : 0 < γ) : StrictMono (totalWeight γ) :=
  strictMono_nat_of_lt_succ fun n ↦ by
    have := NNReal.coe_pos.2 hγ0
    rw [totalWeight_succ']; exact lt_add_of_pos_left _ (by positivity)

variable {γ} in
theorem totalWeight_le_inv (hγ : γ < 1) : totalWeight γ n ≤ (1 - (γ : ℝ))⁻¹ := by
  have h : (0 : ℝ) < 1 - γ := sub_pos.2 (NNReal.coe_lt_one.2 hγ)
  rw [← one_div, le_div_iff₀ h, totalWeight, geom_sum_mul_neg]
  exact sub_le_self _ (by positivity)

variable {γ} in
theorem tendsto_totalWeight (hγ : γ < 1) : Tendsto (totalWeight γ) atTop (𝓝 (1 - (γ : ℝ))⁻¹) :=
  (hasSum_geometric_of_lt_one γ.coe_nonneg (NNReal.coe_lt_one.2 hγ)).tendsto_sum_nat

theorem totalWeight_one : totalWeight 1 n = n := by simp [totalWeight]

variable {γ} in
theorem totalWeight_le (hγ : γ ≤ 1) : totalWeight γ n ≤ n :=
  (sum_le_card_nsmul _ _ 1 fun _ _ ↦ pow_le_one₀ γ.coe_nonneg (NNReal.coe_le_one.2 hγ)).trans
    (by simp)

-- A block of `r` exemplars one tick apart weighs `totalWeight γ r`, and blocks decay by `γ ^ r`.
private theorem totalWeight_pow_mul (r k : ℕ) :
    totalWeight (γ ^ r) k * totalWeight γ r = totalWeight γ (r * k) := by
  induction k with
  | zero => simp [totalWeight]
  | succ k ih =>
    rw [totalWeight_succ', add_mul, ih, Nat.mul_succ, totalWeight, totalWeight, totalWeight,
      sum_range_add, add_comm, mul_sum]
    simp [pow_add, pow_mul]

/-- The recency distribution of the appendix, picking a position with probability proportional
to its weight. -/
noncomputable def recency (n : ℕ) : Measure (Fin n) :=
  ∑ i, (γ ^ (i.rev : ℕ) / ∑ j ∈ range n, γ ^ j : ℝ≥0) • Measure.dirac i

theorem integral_recency (f : Fin n → ℝ) :
    ∫ i, f i ∂recency γ n = ∑ i, (γ : ℝ) ^ (i.rev : ℕ) / totalWeight γ n * f i := by
  rw [recency, integral_finsetSum_measure fun i _ ↦ .of_finite]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [integral_smul_nnreal_measure, integral_dirac, NNReal.smul_def, smul_eq_mul]
  simp [totalWeight]

instance (n : ℕ) : IsProbabilityMeasure (recency γ (n + 1)) := by
  constructor
  rw [recency, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul,
    mul_one, ENNReal.smul_def]
  rw [← ENNReal.ofNNReal_finsetSum, ← sum_div, sum_pow_rev,
    div_self (geom_sum_pos zero_le (Nat.succ_ne_zero n)).ne']
  simp

-- Storing a token mixes the older exemplars, discounted once more, with a point mass at the
-- new one.
theorem recency_succ (n : ℕ) :
    recency γ (n + 1) =
      (γ * (∑ j ∈ range n, γ ^ j) / ∑ j ∈ range (n + 1), γ ^ j) • (recency γ n).map Fin.castSucc +
        (∑ j ∈ range (n + 1), γ ^ j)⁻¹ • Measure.dirac (Fin.last n) := by
  have hmap : (recency γ n).map Fin.castSucc =
      ∑ i : Fin n, (γ ^ (i.rev : ℕ) / ∑ j ∈ range n, γ ^ j : ℝ≥0) •
        Measure.dirac (Fin.castSucc i) := by
    rw [recency, Measure.map_finset_sum' Measurable.of_discrete.aemeasurable]
    simp [Measure.map_smul, Measurable.of_discrete.aemeasurable, Measure.map_dirac' .of_discrete]
  rw [hmap, recency, Fin.sum_univ_castSucc, smul_sum]
  simp only [Fin.rev_castSucc, Fin.rev_last, Fin.val_succ, Fin.val_zero, pow_zero, one_div,
    smul_smul]
  congr 2
  funext i
  have hS : ∑ j ∈ range n, γ ^ j ≠ 0 :=
    (geom_sum_pos zero_le (Fin.pos i).ne').ne'
  congr 1
  rw [pow_succ]
  field_simp

/-- The memory-weighted mean of an exemplar list, its mean under the recency distribution. -/
noncomputable def memoryMean (e : Fin n → ℝ) : ℝ := ∫ i, e i ∂recency γ n

/-- The memory-weighted spread of an exemplar list, its variance under the recency
distribution. -/
noncomputable def memorySpread (e : Fin n → ℝ) : ℝ := Var[e; recency γ n]

theorem memoryMean_eq_sum (e : Fin n → ℝ) :
    memoryMean γ e = (∑ i, (γ : ℝ) ^ (i.rev : ℕ) * e i) / totalWeight γ n := by
  rw [memoryMean, integral_recency, sum_div]
  exact sum_congr rfl fun i _ ↦ by ring

theorem memorySpread_eq_sum (e : Fin n → ℝ) :
    memorySpread γ e =
      (∑ i, (γ : ℝ) ^ (i.rev : ℕ) * (e i - memoryMean γ e) ^ 2) / totalWeight γ n := by
  rw [memorySpread, variance_eq_integral (by fun_prop), integral_recency, sum_div]
  exact sum_congr rfl fun i _ ↦ by rw [memoryMean]; ring

theorem totalWeight_mul_memoryMean (e : Fin n → ℝ) :
    totalWeight γ n * memoryMean γ e = ∑ i, (γ : ℝ) ^ (i.rev : ℕ) * e i := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [totalWeight]
  · rw [memoryMean_eq_sum, mul_div_cancel₀ _ (totalWeight_pos γ hn.ne').ne']

theorem memoryMean_snoc (e : Fin n → ℝ) (x : ℝ) :
    memoryMean γ (Fin.snoc e x : Fin (n + 1) → ℝ) =
      (γ * totalWeight γ n * memoryMean γ e + x) / totalWeight γ (n + 1) := by
  rw [memoryMean_eq_sum, mul_assoc, totalWeight_mul_memoryMean, mul_sum]
  simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, Fin.rev_castSucc,
    Fin.rev_last, Fin.val_succ, Fin.val_zero, pow_zero, one_mul, pow_succ]
  congr 2
  exact sum_congr rfl fun i _ ↦ by ring

theorem memorySpread_snoc (e : Fin n → ℝ) (x : ℝ) :
    memorySpread γ (Fin.snoc e x : Fin (n + 1) → ℝ) =
      γ * totalWeight γ n / totalWeight γ (n + 1) * memorySpread γ e +
        γ * totalWeight γ n / totalWeight γ (n + 1) ^ 2 * (x - memoryMean γ e) ^ 2 := by
  cases n with
  | zero => simp [memorySpread, recency, totalWeight]
  | succ n =>
    have : IsProbabilityMeasure ((recency γ (n + 1)).map Fin.castSucc) :=
      (Measure.isProbabilityMeasure_map_iff Measurable.of_discrete.aemeasurable).2 inferInstance
    have hS : ∑ j ∈ range (n + 2), γ ^ j ≠ 0 := (geom_sum_pos zero_le (by omega)).ne'
    rw [memorySpread, recency_succ, variance_smul_add_smul_measure
        (by rw [inv_eq_one_div, ← add_div, ← geom_sum_succ, div_self hS]) .of_discrete .of_discrete,
      variance_map .of_discrete .of_discrete, integral_map .of_discrete .of_discrete,
      integral_dirac, variance_dirac]
    simp only [Function.comp_def, Fin.snoc_castSucc, Fin.snoc_last]
    rw [memorySpread, memoryMean]
    simp only [totalWeight]
    push_cast
    ring

@[fun_prop] theorem measurable_memoryMean : Measurable (memoryMean γ : (Fin n → ℝ) → ℝ) := by
  rw [funext (memoryMean_eq_sum γ)]
  fun_prop

end Memory

/-! ### Production -/

section Production

variable (γ : ℝ≥0) {n : ℕ}

/-- The production target of the appendix, an exemplar picked by recency or the memory-weighted
mean, to which entrenchment fixes the target in the limit of a large neighborhood. -/
inductive Target
  | exemplar
  | average

/-- The share of the memory spread that a target inherits: all of it for a picked exemplar, none for
the mean. -/
noncomputable def Target.inherited : Target → ℝ
  | .exemplar => 1
  | .average => 0

theorem Target.inherited_nonneg (tgt : Target) : 0 ≤ tgt.inherited := by
  cases tgt <;> simp [Target.inherited]

theorem Target.inherited_le_one (tgt : Target) : tgt.inherited ≤ 1 := by
  cases tgt <;> simp [Target.inherited]

/-- The law of the production target given the exemplar list. -/
noncomputable def target : Target → Kernel (Fin n → ℝ) ℝ
  | .exemplar => (Kernel.id ×ₖ Kernel.const _ (recency γ n)).map
      fun p : (Fin n → ℝ) × Fin n ↦ p.1 p.2
  | .average => Kernel.deterministic (memoryMean γ) (measurable_memoryMean γ)

theorem target_exemplar_apply (e : Fin n → ℝ) : target γ .exemplar e = (recency γ n).map e := by
  rw [target, Kernel.map_apply _ (measurable_from_prod_countable_left measurable_pi_apply),
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (measurable_from_prod_countable_left measurable_pi_apply) (by fun_prop)]
  rfl

theorem target_average_apply (e : Fin n → ℝ) :
    target γ .average e = Measure.dirac (memoryMean γ e) := rfl

instance (tgt : Target) : IsMarkovKernel (target γ tgt : Kernel (Fin (n + 1) → ℝ) ℝ) := by
  cases tgt
  · exact Kernel.IsMarkovKernel.map _ (measurable_from_prod_countable_left measurable_pi_apply)
  · exact inferInstanceAs (IsMarkovKernel (Kernel.deterministic _ (measurable_memoryMean γ)))

/-- Production as in (2), the target plus noise drawn from `ν` plus the lenition bias. -/
noncomputable def produce (tgt : Target) (ν : Measure ℝ) (bias : ℝ) : Kernel (Fin n → ℝ) ℝ :=
  (target γ tgt ×ₖ Kernel.const _ ν).map fun p ↦ p.1 + p.2 + bias

variable {ν : Measure ℝ} [IsProbabilityMeasure ν] (tgt : Target) (bias : ℝ)

instance : IsMarkovKernel (produce γ tgt ν bias : Kernel (Fin (n + 1) → ℝ) ℝ) :=
  Kernel.IsMarkovKernel.map _ (by fun_prop)

theorem produce_apply (e : Fin (n + 1) → ℝ) :
    produce γ tgt ν bias e = ((target γ tgt e).prod ν).map fun p ↦ p.1 + p.2 + bias := by
  rw [produce, Kernel.map_apply _ (by fun_prop), Kernel.prod_apply, Kernel.const_apply]

theorem memLp_target (e : Fin (n + 1) → ℝ) : MemLp id 2 (target γ tgt e) := by
  cases tgt
  · rw [target_exemplar_apply, memLp_map_measure_iff (by fun_prop) (by fun_prop)]
    exact MemLp.of_bound (by fun_prop) (∑ i, |e i|) (.of_forall fun i ↦ by
      simpa using single_le_sum (f := fun i ↦ |e i|) (fun _ _ ↦ abs_nonneg _) (mem_univ i))
  · exact MemLp.of_bound (by fun_prop) |memoryMean γ e|
      (by simp [target_average_apply, ae_dirac_eq])

theorem integral_target (e : Fin (n + 1) → ℝ) : ∫ t, t ∂target γ tgt e = memoryMean γ e := by
  cases tgt
  · rw [target_exemplar_apply, integral_map (by fun_prop) (by fun_prop),
      memoryMean]
  · simp [target_average_apply]

theorem variance_target (e : Fin (n + 1) → ℝ) :
    Var[id; target γ tgt e] = tgt.inherited * memorySpread γ e := by
  cases tgt
  · rw [target_exemplar_apply, variance_id_map (by fun_prop), Target.inherited, one_mul,
      memorySpread]
  · simp [target_average_apply, Target.inherited]

variable (hν : MemLp id 2 ν) (hν0 : ∫ x, x ∂ν = 0)
include hν

theorem memLp_produce (e : Fin (n + 1) → ℝ) : MemLp id 2 (produce γ tgt ν bias e) := by
  rw [produce_apply, memLp_map_measure_iff (by fun_prop) (by fun_prop)]
  exact (((memLp_target γ tgt e).comp_fst ν).add (hν.comp_snd _)).add (memLp_const bias)

-- A production inherits the spread of its target and adds the spread of the noise.
theorem variance_produce (e : Fin (n + 1) → ℝ) :
    Var[id; produce γ tgt ν bias e] = tgt.inherited * memorySpread γ e + Var[id; ν] := by
  rw [produce_apply, variance_id_map (by fun_prop),
    variance_add_const (X := fun p : ℝ × ℝ ↦ p.1 + p.2) (by fun_prop), ← variance_target]
  exact variance_add_prod (X := id) (Y := id) (memLp_target γ tgt e) hν

include hν0

theorem integral_produce (e : Fin (n + 1) → ℝ) :
    ∫ x, x ∂produce γ tgt ν bias e = memoryMean γ e + bias := by
  have h1 : Integrable (fun p : ℝ × ℝ ↦ p.1) ((target γ tgt e).prod ν) :=
    ((memLp_target γ tgt e).integrable one_le_two).comp_fst ν
  have h2 : Integrable (fun p : ℝ × ℝ ↦ p.2) ((target γ tgt e).prod ν) :=
    (hν.integrable one_le_two).comp_snd _
  rw [produce_apply, integral_map (by fun_prop) (by fun_prop),
    integral_add (f := fun p : ℝ × ℝ ↦ p.1 + p.2) (h1.add h2) (integrable_const _),
    integral_add h1 h2, integral_fun_fst (fun t : ℝ ↦ t), integral_fun_snd (fun t : ℝ ↦ t),
    integral_target, hν0]
  simp

theorem integral_produce_sub_sq (e : Fin (n + 1) → ℝ) :
    ∫ x, (x - memoryMean γ e) ^ 2 ∂produce γ tgt ν bias e =
      tgt.inherited * memorySpread γ e + Var[id; ν] + bias ^ 2 := by
  have h := integral_sub_const_sq (memLp_produce γ tgt bias hν e) (memoryMean γ e)
  simp only [id] at h
  rw [h, variance_produce γ tgt bias hν, integral_produce γ tgt bias hν hν0]
  ring

end Production

/-! ### The exemplar list -/

section Law

variable {γ : ℝ≥0} {tgt : Target} {ν : Measure ℝ} {bias seed : ℝ}

variable (γ tgt ν bias seed) in
/-- The prediction rule of the exemplar list, which starts from the seed and stores every
production. -/
noncomputable def rule : (n : ℕ) → Kernel (Fin n → ℝ) ℝ
  | 0 => Kernel.const _ (Measure.dirac seed)
  | _ + 1 => produce γ tgt ν bias

theorem rule_succ (n : ℕ) : rule γ tgt ν bias seed (n + 1) = produce γ tgt ν bias := rfl

theorem seqLaw_rule_one : seqLaw (rule γ tgt ν bias seed) 1 = Measure.dirac fun _ ↦ seed := by
  have h : (Fin.snoc (default : Fin 0 → ℝ) seed : Fin 1 → ℝ) = fun _ ↦ seed := by
    funext i
    rw [Fin.fin_one_eq_zero i]
    exact Fin.snoc_last (α := fun _ ↦ ℝ) seed default
  rw [seqLaw_succ, seqLaw_zero, rule, Measure.compProd_const, Measure.dirac_prod_dirac]
  ext s hs
  rw [Measure.map_apply measurable_snoc_prod hs, Measure.dirac_apply' _ (measurable_snoc_prod hs),
    Measure.dirac_apply' _ hs, ← h]
  rfl

variable [IsProbabilityMeasure ν]

instance : ∀ n, IsMarkovKernel (rule γ tgt ν bias seed n)
  | 0 => inferInstanceAs (IsMarkovKernel (Kernel.const _ _))
  | _ + 1 => inferInstanceAs (IsMarkovKernel (produce γ tgt ν bias))

section ListMoments

variable {n : ℕ} {μ : Measure (Fin n → ℝ)} (h : ∀ i, MemLp (fun e ↦ e i) 2 μ)
include h

theorem memLp_memoryMean : MemLp (memoryMean γ) 2 μ := by
  convert (memLp_finsetSum _ fun i _ ↦ (h i).const_mul ((γ : ℝ) ^ (i.rev : ℕ))).mul_const
    (totalWeight γ n)⁻¹ using 1
  funext e
  rw [memoryMean_eq_sum, div_eq_mul_inv]

theorem integrable_memorySpread : Integrable (memorySpread γ) μ := by
  refine (integrable_congr (.of_forall (memorySpread_eq_sum γ))).2 ?_
  exact (integrable_finsetSum _ fun i _ ↦
    (((h i).sub (memLp_memoryMean h)).integrable_sq).const_mul _).div_const _

end ListMoments

variable (hν : MemLp id 2 ν) (hν0 : ∫ x, x ∂ν = 0)
include hν hν0

theorem memLp_apply :
    ∀ (n : ℕ) (i : Fin (n + 1)), MemLp (fun e ↦ e i) 2 (seqLaw (rule γ tgt ν bias seed) (n + 1))
  | 0, i => by
    rw [seqLaw_rule_one]
    exact MemLp.of_bound (measurable_pi_apply i).aestronglyMeasurable |seed|
      (by simp [ae_dirac_eq])
  | n + 1, i => by
    have ih := memLp_apply n
    set μ := seqLaw (rule γ tgt ν bias seed) (n + 1)
    set κ := rule γ tgt ν bias seed (n + 1)
    have hfst {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Measurable f) (h : MemLp f 2 μ) :
        MemLp (fun p : (Fin (n + 1) → ℝ) × ℝ ↦ f p.1) 2 (μ ⊗ₘ κ) := by
      rw [← Measure.fst_compProd μ κ, Measure.fst, memLp_map_measure_iff hf.aestronglyMeasurable
        measurable_fst.aemeasurable] at h
      exact h
    rw [seqLaw_succ, memLp_map_measure_iff (measurable_pi_apply i).aestronglyMeasurable
      measurable_snoc_prod.aemeasurable]
    induction i using Fin.lastCases with
    | cast j => simpa [Function.comp_def] using hfst (measurable_pi_apply j) (ih j)
    | last =>
      have hm : Measurable fun p : (Fin (n + 1) → ℝ) × ℝ ↦ p.2 - memoryMean γ p.1 := by fun_prop
      have hD : MemLp (fun p : (Fin (n + 1) → ℝ) × ℝ ↦ p.2 - memoryMean γ p.1) 2 (μ ⊗ₘ κ) := by
        rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable,
          Measure.integrable_compProd_iff (hm.pow_const 2).aestronglyMeasurable]
        refine ⟨.of_forall fun e ↦ ?_, ?_⟩
        · simpa [κ, rule_succ] using
            ((memLp_produce γ tgt bias hν e).sub (memLp_const (memoryMean γ e))).integrable_sq
        simp only [norm_pow, Real.norm_eq_abs, sq_abs, κ, rule_succ,
          integral_produce_sub_sq γ tgt bias hν hν0]
        exact (((integrable_memorySpread ih).const_mul _).add (integrable_const _)).add
          (integrable_const _)
      convert hD.add (hfst (measurable_memoryMean γ) (memLp_memoryMean ih)) using 1
      funext p
      simp

theorem integral_memoryMean_snoc {n : ℕ} (e : Fin (n + 1) → ℝ) :
    ∫ x, memoryMean γ (Fin.snoc e x : Fin (n + 2) → ℝ) ∂rule γ tgt ν bias seed (n + 1) e =
      memoryMean γ e + bias / totalWeight γ (n + 2) := by
  have hx : Integrable (fun x : ℝ ↦ x) (produce γ tgt ν bias e) :=
    (memLp_produce γ tgt bias hν e).integrable one_le_two
  have hS := totalWeight_pos γ (Nat.succ_ne_zero n)
  simp_rw [memoryMean_snoc, rule_succ]
  rw [integral_div, integral_add (integrable_const _) hx, integral_const,
    integral_produce γ tgt bias hν hν0, totalWeight_succ (n := n + 1)]
  simp only [probReal_univ, one_smul]
  field_simp
  ring

-- §3.2
theorem integral_memoryMean (n : ℕ) :
    ∫ e, memoryMean γ e ∂seqLaw (rule γ tgt ν bias seed) (n + 1) =
      seed + bias * ∑ k ∈ range n, (totalWeight γ (k + 2))⁻¹ := by
  induction n with
  | zero =>
    rw [seqLaw_rule_one, integral_dirac]
    simp [memoryMean_eq_sum, totalWeight]
  | succ n ih =>
    rw [integral_seqLaw_succ ((memLp_memoryMean (memLp_apply hν hν0 (n + 1))).integrable
      one_le_two)]
    simp_rw [integral_memoryMean_snoc hν hν0]
    rw [integral_add ((memLp_memoryMean (memLp_apply hν hν0 n)).integrable one_le_two)
      (integrable_const _), ih, integral_const, sum_range_succ]
    simp only [probReal_univ, one_smul]
    ring

theorem integral_memorySpread_snoc {n : ℕ} (e : Fin (n + 1) → ℝ) :
    ∫ x, memorySpread γ (Fin.snoc e x : Fin (n + 2) → ℝ) ∂rule γ tgt ν bias seed (n + 1) e =
      γ * totalWeight γ (n + 1) / totalWeight γ (n + 2) * memorySpread γ e +
        γ * totalWeight γ (n + 1) / totalWeight γ (n + 2) ^ 2 *
          (tgt.inherited * memorySpread γ e + Var[id; ν] + bias ^ 2) := by
  have hx : Integrable (fun x : ℝ ↦ (x - memoryMean γ e) ^ 2) (produce γ tgt ν bias e) :=
    ((memLp_produce γ tgt bias hν e).sub (memLp_const _)).integrable_sq
  simp_rw [memorySpread_snoc, rule_succ]
  rw [integral_add (integrable_const _) (hx.const_mul _), integral_const, integral_const_mul,
    integral_produce_sub_sq γ tgt bias hν hν0]
  simp only [probReal_univ, one_smul]

end Law

/-! ### Growth of the spread -/

section Growth

variable (γ : ℝ≥0) {κ κ' : ℝ}

/-- The expected spread after `n` productions in units of the variance that noise and bias add at
a production, for a target that inherits the share `κ` of the memory spread. A production keeps the
older exemplars' share of the spread and adds the new token's deviation from the mean. -/
noncomputable def spreadGrowth (κ : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
    γ * totalWeight γ (n + 1) / totalWeight γ (n + 2) * spreadGrowth κ n +
      γ * totalWeight γ (n + 1) / totalWeight γ (n + 2) ^ 2 * (κ * spreadGrowth κ n + 1)

private theorem mul_totalWeight_nonneg (n : ℕ) : 0 ≤ (γ : ℝ) * totalWeight γ n :=
  mul_nonneg γ.coe_nonneg (totalWeight_nonneg γ)

private theorem older_share_nonneg (n : ℕ) :
    0 ≤ (γ : ℝ) * totalWeight γ (n + 1) / totalWeight γ (n + 2) :=
  div_nonneg (mul_totalWeight_nonneg γ _) (totalWeight_nonneg γ)

private theorem new_share_nonneg (n : ℕ) :
    0 ≤ (γ : ℝ) * totalWeight γ (n + 1) / totalWeight γ (n + 2) ^ 2 :=
  div_nonneg (mul_totalWeight_nonneg γ _) (pow_nonneg (totalWeight_nonneg γ) 2)

theorem spreadGrowth_succ (n : ℕ) :
    spreadGrowth γ κ (n + 1) = spreadGrowth γ κ n +
      (γ * totalWeight γ (n + 1) - (1 + (1 - κ) * (γ * totalWeight γ (n + 1))) *
        spreadGrowth γ κ n) / totalWeight γ (n + 2) ^ 2 := by
  have hS := totalWeight_pos γ (Nat.succ_ne_zero (n + 1))
  rw [spreadGrowth, totalWeight_succ (n := n + 1)] at *
  field_simp
  ring

theorem spreadGrowth_nonneg (hκ0 : 0 ≤ κ) (n : ℕ) : 0 ≤ spreadGrowth γ κ n := by
  induction n with
  | zero => simp [spreadGrowth]
  | succ n ih =>
    rw [spreadGrowth]
    exact add_nonneg (mul_nonneg (older_share_nonneg γ n) ih)
      (mul_nonneg (new_share_nonneg γ n) (add_nonneg (mul_nonneg hκ0 ih) zero_le_one))

variable {γ} in
theorem spreadGrowth_pos (hγ0 : 0 < γ) (hκ0 : 0 ≤ κ) (n : ℕ) : 0 < spreadGrowth γ κ (n + 1) := by
  have hB : 0 < (γ : ℝ) * totalWeight γ (n + 1) / totalWeight γ (n + 2) ^ 2 :=
    div_pos (mul_pos (NNReal.coe_pos.2 hγ0) (totalWeight_pos γ (by omega)))
      (pow_pos (totalWeight_pos γ (by omega)) 2)
  have hg := spreadGrowth_nonneg γ hκ0 n
  rw [spreadGrowth]
  exact add_pos_of_nonneg_of_pos (mul_nonneg (older_share_nonneg γ n) hg)
    (mul_pos hB (add_pos_of_nonneg_of_pos (mul_nonneg hκ0 hg) one_pos))

-- The level a production moves the spread toward, for a memory of `x` besides the new token.
private noncomputable def level (κ x : ℝ) : ℝ := x / (1 + (1 - κ) * x)

private theorem level_lt (hκ : κ ≤ 1) {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    level κ x < level κ y := by
  have hc : 0 ≤ 1 - κ := sub_nonneg.2 hκ
  have h1 : 0 < 1 + (1 - κ) * x := by positivity
  have h2 : 0 < 1 + (1 - κ) * y := by nlinarith [mul_nonneg hc hx, mul_nonneg hc (hx.trans hxy.le)]
  rw [level, level, div_lt_div_iff₀ h1 h2]
  nlinarith

private theorem spreadGrowth_succ_level (hκ : κ ≤ 1) (n : ℕ) :
    spreadGrowth γ κ (n + 1) = spreadGrowth γ κ n +
      (level κ (γ * totalWeight γ (n + 1)) - spreadGrowth γ κ n) /
        ((γ * totalWeight γ (n + 1) + 1) ^ 2 / (1 + (1 - κ) * (γ * totalWeight γ (n + 1)))) := by
  have ha := mul_totalWeight_nonneg γ (n + 1)
  have hc : 0 ≤ 1 - κ := sub_nonneg.2 hκ
  rw [spreadGrowth_succ, totalWeight_succ (n := n + 1), level]
  generalize (γ : ℝ) * totalWeight γ (n + 1) = a at *
  have h1 : 0 < 1 + (1 - κ) * a := by positivity
  have h2 : 0 < a + 1 := by positivity
  field_simp

private theorem one_le_rate (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1) {a : ℝ} (ha : 0 ≤ a) :
    1 ≤ (a + 1) ^ 2 / (1 + (1 - κ) * a) := by
  have hc : 0 ≤ 1 - κ := sub_nonneg.2 hκ
  rw [one_le_div (by positivity)]
  nlinarith [mul_nonneg ha ha, mul_nonneg hκ0 ha]

variable {γ} in
private theorem spreadGrowth_le_level (hγ0 : 0 < γ) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1) (n : ℕ) :
    spreadGrowth γ κ n ≤ level κ (γ * totalWeight γ n) := by
  induction n with
  | zero => simp [spreadGrowth, totalWeight, level]
  | succ n ih =>
    have hlt := level_lt hκ (mul_totalWeight_nonneg γ n)
      (mul_lt_mul_of_pos_left (totalWeight_strictMono hγ0 n.lt_succ_self) (NNReal.coe_pos.2 hγ0))
    have := div_le_self (sub_nonneg.2 (ih.trans hlt.le))
      (one_le_rate hκ0 hκ (mul_totalWeight_nonneg γ (n + 1)))
    rw [spreadGrowth_succ_level γ hκ]
    linarith

variable {γ} in
theorem spreadGrowth_strictMono (hγ0 : 0 < γ) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1) :
    StrictMono (spreadGrowth γ κ) := by
  refine strictMono_nat_of_lt_succ fun n ↦ ?_
  have hlt := (spreadGrowth_le_level hγ0 hκ0 hκ n).trans_lt
    (level_lt hκ (mul_totalWeight_nonneg γ n)
      (mul_lt_mul_of_pos_left (totalWeight_strictMono hγ0 n.lt_succ_self) (NNReal.coe_pos.2 hγ0)))
  rw [spreadGrowth_succ_level γ hκ]
  exact lt_add_of_pos_right _ (div_pos (sub_pos.2 hlt)
    (one_pos.trans_le (one_le_rate hκ0 hκ (mul_totalWeight_nonneg γ (n + 1)))))

-- A monotone bounded sequence moving toward a convergent target converges to that target.
private theorem tendsto_of_recursion {x a b : ℕ → ℝ} {A B : ℝ} (hx : Monotone x)
    (hbdd : BddAbove (Set.range x)) (hrec : ∀ n, x (n + 1) = x n + (a n - x n) / b n)
    (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 B)) (hB : B ≠ 0) :
    Tendsto x atTop (𝓝 A) := by
  have hl := tendsto_atTop_ciSup hx hbdd
  have h := tendsto_nhds_unique ((tendsto_add_atTop_iff_nat 1).2 hl)
    ((hl.add ((ha.sub hl).div hb hB)).congr fun n ↦ (hrec n).symm)
  have hA : A = ⨆ n, x n := by
    field_simp at h
    linarith
  rwa [hA]

variable {γ} in
theorem tendsto_spreadGrowth (hγ0 : 0 < γ) (hγ : γ < 1) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1) :
    Tendsto (spreadGrowth γ κ) atTop (𝓝 (γ / (1 - κ * γ))) := by
  have h1 := NNReal.coe_lt_one.2 hγ
  have h0 := NNReal.coe_pos.2 hγ0
  have hu : 0 < 1 - (γ : ℝ) := sub_pos.2 h1
  have hv : 0 < 1 - κ * (γ : ℝ) := by nlinarith
  have hL : Tendsto (fun n ↦ (γ : ℝ) * totalWeight γ (n + 1)) atTop (𝓝 (γ * (1 - (γ : ℝ))⁻¹)) :=
    ((tendsto_add_atTop_iff_nat 1).2 (tendsto_totalWeight hγ)).const_mul _
  have hw : 1 + (1 - κ) * (γ * (1 - (γ : ℝ))⁻¹) ≠ 0 := by
    have : 0 ≤ (γ : ℝ) * (1 - (γ : ℝ))⁻¹ := by positivity
    have : 0 ≤ 1 - κ := sub_nonneg.2 hκ
    positivity
  have hlim : level κ (γ * (1 - (γ : ℝ))⁻¹) = γ / (1 - κ * γ) := by
    have e : 1 + (1 - κ) * ((γ : ℝ) * (1 - (γ : ℝ))⁻¹) = (1 - κ * γ) * (1 - (γ : ℝ))⁻¹ := by
      field_simp
      ring
    rw [level, e, mul_div_mul_right _ _ (inv_ne_zero hu.ne')]
  rw [← hlim]
  have hden := (hL.const_mul (1 - κ)).const_add 1
  refine tendsto_of_recursion (spreadGrowth_strictMono hγ0 hκ0 hκ).monotone
    ⟨level κ (γ * (1 - (γ : ℝ))⁻¹), ?_⟩ (spreadGrowth_succ_level γ hκ) (hL.div hden hw)
    (((hL.add_const 1).pow 2).div hden hw) (div_ne_zero (pow_ne_zero 2 (by positivity)) hw)
  rintro _ ⟨n, rfl⟩
  refine (spreadGrowth_le_level hγ0 hκ0 hκ n).trans ?_
  rcases (mul_le_mul_of_nonneg_left (totalWeight_le_inv (n := n) hγ) γ.coe_nonneg).eq_or_lt
    with h | h
  · rw [h]
  · exact (level_lt hκ (mul_totalWeight_nonneg γ n) h).le

theorem spreadGrowth_le_of_le (hκ0 : 0 ≤ κ) (hκκ' : κ ≤ κ') (n : ℕ) :
    spreadGrowth γ κ n ≤ spreadGrowth γ κ' n := by
  induction n with
  | zero => simp [spreadGrowth]
  | succ n ih =>
    have hk := mul_le_mul hκκ' ih (spreadGrowth_nonneg γ hκ0 n) (hκ0.trans hκκ')
    simp only [spreadGrowth]
    exact add_le_add (mul_le_mul_of_nonneg_left ih (older_share_nonneg γ n))
      (mul_le_mul_of_nonneg_left (by linarith) (new_share_nonneg γ n))

variable {γ} in
theorem spreadGrowth_lt_of_lt (hγ0 : 0 < γ) (hκ0 : 0 ≤ κ) (hκκ' : κ < κ') (n : ℕ) :
    spreadGrowth γ κ (n + 2) < spreadGrowth γ κ' (n + 2) := by
  have hg := spreadGrowth_pos hγ0 (hκ0.trans hκκ'.le) n
  have hle := spreadGrowth_le_of_le γ hκ0 hκκ'.le (n + 1)
  have hB : 0 < (γ : ℝ) * totalWeight γ (n + 1 + 1) / totalWeight γ (n + 1 + 2) ^ 2 :=
    div_pos (mul_pos (NNReal.coe_pos.2 hγ0) (totalWeight_pos γ (by omega)))
      (pow_pos (totalWeight_pos γ (by omega)) 2)
  have hk : κ * spreadGrowth γ κ (n + 1) < κ' * spreadGrowth γ κ' (n + 1) :=
    (mul_le_mul_of_nonneg_left hle hκ0).trans_lt (mul_lt_mul_of_pos_right hκκ' hg)
  rw [show spreadGrowth γ κ (n + 2) = _ by rw [spreadGrowth],
    show spreadGrowth γ κ' (n + 2) = _ by rw [spreadGrowth]]
  exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hle (older_share_nonneg γ (n + 1)))
    (mul_lt_mul_of_pos_left (by linarith) hB)

private theorem tendsto_sum_inv_add_two :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ range n, ((k : ℝ) + 2)⁻¹) atTop atTop := by
  refine (tendsto_atTop_add_const_right atTop (-1 : ℝ) ((tendsto_add_atTop_iff_nat 1).2
    Real.tendsto_sum_range_one_div_nat_succ_atTop)).congr fun n ↦ ?_
  rw [sum_range_succ']
  simp only [Nat.cast_zero, zero_add, div_one, add_neg_cancel_right]
  exact sum_congr rfl fun k _ ↦ by push_cast; rw [one_div]; ring_nf

theorem tendsto_spreadGrowth_one_one : Tendsto (spreadGrowth 1 1) atTop atTop := by
  have hrec (n : ℕ) : spreadGrowth 1 1 (n + 1) = spreadGrowth 1 1 n +
      ((n + 1) - spreadGrowth 1 1 n) / ((n : ℝ) + 2) ^ 2 := by
    rw [spreadGrowth_succ, totalWeight_one, totalWeight_one]
    push_cast
    ring_nf
  have hle (n : ℕ) : spreadGrowth 1 1 n ≤ ((n : ℝ) + 1) / 2 := by
    induction n with
    | zero => simp [spreadGrowth]
    | succ n ih =>
      have hn : (0 : ℝ) ≤ n := n.cast_nonneg
      rw [hrec]
      push_cast
      have hd : (0 : ℝ) < ((n : ℝ) + 2) ^ 2 := by positivity
      rw [add_div' _ _ _ hd.ne', div_le_iff₀ hd]
      nlinarith [mul_nonneg (sub_nonneg.2 ih) (by nlinarith : 0 ≤ ((n : ℝ) + 2) ^ 2 - 1)]
  have hge (n : ℕ) : (∑ k ∈ range n, ((k : ℝ) + 2)⁻¹) / 4 ≤ spreadGrowth 1 1 n := by
    induction n with
    | zero => simp [spreadGrowth]
    | succ n ih =>
      have hn : (0 : ℝ) ≤ n := n.cast_nonneg
      have hstep : ((n : ℝ) + 2)⁻¹ / 4 ≤
          ((n + 1) - spreadGrowth 1 1 n) / ((n : ℝ) + 2) ^ 2 := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity), inv_mul_eq_div,
          div_le_iff₀ (by positivity)]
        nlinarith [hle n]
      rw [hrec, sum_range_succ, add_div]
      linarith
  exact tendsto_atTop_mono hge (tendsto_sum_inv_add_two.atTop_div_const (by norm_num))

variable {γ} in
-- `r` ticks of a word used at every tick against one token of a word used every `r` ticks.
private theorem inv_totalWeight_pow_lt (hγ0 : 0 < γ) (hγ : γ ≤ 1) {r : ℕ} (hr : 1 < r) (k : ℕ) :
    (totalWeight (γ ^ r) (k + 2))⁻¹ < ∑ j ∈ range r, (totalWeight γ (r * k + j + 2))⁻¹ := by
  have hT := totalWeight_pos γ (n := r * (k + 2)) (by positivity)
  have hSr := totalWeight_pos γ (n := r) (by omega)
  have hS := totalWeight_pos (γ ^ r) (n := k + 2) (by omega)
  have hle : totalWeight γ r * (totalWeight γ (r * (k + 2)))⁻¹ ≤
      r * (totalWeight γ (r * (k + 2)))⁻¹ :=
    mul_le_mul_of_nonneg_right (totalWeight_le hγ) (inv_nonneg.2 hT.le)
  have heq : (totalWeight (γ ^ r) (k + 2))⁻¹ =
      totalWeight γ r * (totalWeight γ (r * (k + 2)))⁻¹ := by
    rw [← totalWeight_pow_mul γ r (k + 2)]
    field_simp
  rw [heq]
  refine hle.trans_lt ?_
  have h : ∑ _j ∈ range r, (totalWeight γ (r * (k + 2)))⁻¹ <
      ∑ j ∈ range r, (totalWeight γ (r * k + j + 2))⁻¹ := by
    refine sum_lt_sum (fun j hj ↦ inv_anti₀ (totalWeight_pos γ (by omega))
      (totalWeight_mono γ ?_)) ⟨0, mem_range.2 (by omega), ?_⟩
    · have := mem_range.1 hj
      nlinarith
    · exact inv_strictAnti₀ (totalWeight_pos γ (by omega))
        (totalWeight_strictMono hγ0 (by nlinarith))
  simpa using h

variable {γ} in
private theorem sum_inv_totalWeight_pow_lt (hγ0 : 0 < γ) (hγ : γ ≤ 1) {r n : ℕ} (hr : 1 < r)
    (hn : n ≠ 0) :
    ∑ k ∈ range n, (totalWeight (γ ^ r) (k + 2))⁻¹ <
      ∑ k ∈ range (r * n), (totalWeight γ (k + 2))⁻¹ := by
  have hsplit (f : ℕ → ℝ) (m : ℕ) :
      ∑ k ∈ range (r * m), f k = ∑ k ∈ range m, ∑ j ∈ range r, f (r * k + j) := by
    induction m with
    | zero => simp
    | succ m ih => rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]
  rw [hsplit]
  exact sum_lt_sum_of_nonempty (nonempty_range_iff.2 hn) fun k _ ↦
    inv_totalWeight_pow_lt hγ0 hγ hr k

variable {γ} in
-- Block `k + 2` of a word used at every tick against one token of a word used every `r` ticks.
private theorem sum_inv_totalWeight_block_le {r : ℕ} (hr : r ≠ 0) (k : ℕ) :
    ∑ j ∈ range r, (totalWeight γ (r * (k + 2) + j + 2))⁻¹ ≤
      r / totalWeight γ r * (totalWeight (γ ^ r) (k + 2))⁻¹ := by
  have hT := totalWeight_pos γ (n := r * (k + 2)) (by positivity)
  have hb : ∑ j ∈ range r, (totalWeight γ (r * (k + 2) + j + 2))⁻¹ ≤
      r * (totalWeight γ (r * (k + 2)))⁻¹ := by
    simpa using sum_le_card_nsmul (range r) (fun j ↦ (totalWeight γ (r * (k + 2) + j + 2))⁻¹)
      (totalWeight γ (r * (k + 2)))⁻¹ fun j _ ↦ inv_anti₀ hT (totalWeight_mono γ (by omega))
  rwa [← totalWeight_pow_mul γ r (k + 2), mul_inv, mul_comm (_)⁻¹, ← mul_assoc, ← div_eq_mul_inv]
    at hb

variable {γ} in
private theorem sum_inv_totalWeight_le {r : ℕ} (hr : r ≠ 0) (n : ℕ) :
    ∑ k ∈ range (r * n), (totalWeight γ (k + 2))⁻¹ ≤ ∑ k ∈ range r, (totalWeight γ (k + 2))⁻¹ +
      r / totalWeight γ r * (1 + ∑ k ∈ range n, (totalWeight (γ ^ r) (k + 2))⁻¹) := by
  have hSr := totalWeight_pos γ hr
  have hc : 0 ≤ (r : ℝ) / totalWeight γ r := by positivity
  have hinv (k : ℕ) : 0 ≤ (totalWeight γ (k + 2))⁻¹ := inv_nonneg.2 (totalWeight_nonneg γ)
  have hsplit (m : ℕ) : ∑ k ∈ range (r * (m + 2)), (totalWeight γ (k + 2))⁻¹ ≤
      ∑ k ∈ range r, (totalWeight γ (k + 2))⁻¹ +
        r / totalWeight γ r * (1 + ∑ k ∈ range m, (totalWeight (γ ^ r) (k + 2))⁻¹) := by
    induction m with
    | zero =>
      have hb : ∑ j ∈ range r, (totalWeight γ (r + j + 2))⁻¹ ≤ r / totalWeight γ r := by
        simpa [div_eq_mul_inv] using sum_le_card_nsmul (range r)
          (fun j ↦ (totalWeight γ (r + j + 2))⁻¹) (totalWeight γ r)⁻¹
          fun j _ ↦ inv_anti₀ hSr (totalWeight_mono γ (by omega))
      rw [show r * (0 + 2) = r + r by ring, sum_range_add]
      simp only [range_zero, sum_empty, add_zero, mul_one]
      linarith
    | succ m ih =>
      have hb := sum_inv_totalWeight_block_le (γ := γ) hr m
      rw [show r * (m + 1 + 2) = r * (m + 2) + r by ring, sum_range_add,
        sum_range_succ (fun k ↦ (totalWeight (γ ^ r) (k + 2))⁻¹)]
      linarith
  have hsub : ∑ k ∈ range (r * n), (totalWeight γ (k + 2))⁻¹ ≤
      ∑ k ∈ range (r * (n + 2)), (totalWeight γ (k + 2))⁻¹ :=
    sum_le_sum_of_subset_of_nonneg (range_mono (Nat.mul_le_mul_left r (by omega)))
      fun k _ _ ↦ hinv k
  exact hsub.trans (hsplit n)

variable {γ} in
theorem totalWeight_div_mem_Icc (hγ : γ ≤ 1) {r : ℕ} (hr : r ≠ 0) :
    totalWeight γ r / r ∈ Set.Icc ((γ : ℝ) ^ (r - 1)) 1 := by
  have hr0 : (0 : ℝ) < r := Nat.cast_pos.2 (Nat.pos_of_ne_zero hr)
  refine ⟨?_, (div_le_one hr0).2 (totalWeight_le hγ)⟩
  rw [le_div_iff₀ hr0, mul_comm]
  simpa [totalWeight] using card_nsmul_le_sum (range r) (fun i ↦ (γ : ℝ) ^ i) ((γ : ℝ) ^ (r - 1))
    fun i hi ↦ pow_le_pow_of_le_one γ.coe_nonneg (NNReal.coe_le_one.2 hγ)
      (Nat.le_sub_one_of_lt (mem_range.1 hi))

variable {γ} in
theorem div_one_sub_mem_Icc_of_eq_exp {τ : ℝ} (hτ : 0 < τ) (hγτ : (γ : ℝ) = Real.exp (-τ⁻¹)) :
    (γ : ℝ) / (1 - γ) ∈ Set.Icc (τ - 1) τ := by
  have hu : 0 < τ⁻¹ := inv_pos.2 hτ
  have h1 : (γ : ℝ) < 1 := by rw [hγτ]; exact Real.exp_lt_one_iff.2 (neg_lt_zero.2 hu)
  have hd : 0 < 1 - (γ : ℝ) := sub_pos.2 h1
  have hlow : -τ⁻¹ + 1 ≤ γ := hγτ ▸ Real.add_one_le_exp _
  have hup : (γ : ℝ) * (τ⁻¹ + 1) ≤ 1 := by
    rw [hγτ, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _), mul_one]
    exact Real.add_one_le_exp _
  have hττ : τ * τ⁻¹ = 1 := mul_inv_cancel₀ hτ.ne'
  constructor
  · rw [le_div_iff₀ hd]
    nlinarith
  · rw [div_le_iff₀ hd]
    nlinarith

end Growth

/-! ### Predictions -/

section Predictions

variable {γ : ℝ≥0} {tgt : Target} {ν : Measure ℝ} [IsProbabilityMeasure ν] {bias seed : ℝ}
  (hν : MemLp id 2 ν) (hν0 : ∫ x, x ∂ν = 0)
include hν hν0

theorem integral_memorySpread (n : ℕ) :
    ∫ e, memorySpread γ e ∂seqLaw (rule γ tgt ν bias seed) (n + 1) =
      (Var[id; ν] + bias ^ 2) * spreadGrowth γ tgt.inherited n := by
  induction n with
  | zero =>
    rw [seqLaw_rule_one, integral_dirac]
    simp [memorySpread_eq_sum, memoryMean_eq_sum, totalWeight, spreadGrowth]
  | succ n ih =>
    have hV : Integrable (memorySpread γ) (seqLaw (rule γ tgt ν bias seed) (n + 1)) :=
      integrable_memorySpread (memLp_apply hν hν0 n)
    rw [integral_seqLaw_succ (integrable_memorySpread (memLp_apply hν hν0 (n + 1)))]
    simp_rw [integral_memorySpread_snoc hν hν0]
    set A := (γ : ℝ) * totalWeight γ (n + 1) / totalWeight γ (n + 2)
    set B := (γ : ℝ) * totalWeight γ (n + 1) / totalWeight γ (n + 2) ^ 2
    set c := Var[id; ν] + bias ^ 2
    simp only [show ∀ V, A * V + B * (tgt.inherited * V + Var[id; ν] + bias ^ 2) =
      (A + B * tgt.inherited) * V + B * c from fun V ↦ by ring]
    rw [integral_add (hV.const_mul _) (integrable_const _), integral_const_mul, ih]
    simp only [integral_const, probReal_univ, one_smul, spreadGrowth, A, B, c]
    ring

/-- Under a leniting bias the expected memory mean falls with each production of a word (§3.2, Fig.
3), which is how Fig. 3 reads word frequency: more productions under one decay per own token. -/
theorem lenition_advances_with_use (hbias : bias < 0) :
    StrictAnti fun n ↦ ∫ e, memoryMean γ e ∂seqLaw (rule γ tgt ν bias seed) (n + 1) := by
  refine strictAnti_nat_of_succ_lt fun n ↦ ?_
  simp only [integral_memoryMean hν hν0, sum_range_succ, mul_add, add_lt_iff_neg_left,
    ← add_assoc]
  exact mul_neg_of_neg_of_pos hbias (inv_pos.2 (totalWeight_pos γ (by omega)))

-- "an unbounded drift", §4
theorem tendsto_integral_memoryMean_atBot (hγ : γ ≤ 1) (hbias : bias < 0) :
    Tendsto (fun n ↦ ∫ e, memoryMean γ e ∂seqLaw (rule γ tgt ν bias seed) (n + 1)) atTop atBot := by
  simp only [integral_memoryMean hν hν0]
  refine tendsto_atBot_add_const_left _ _ (Tendsto.const_mul_atTop_of_neg hbias
    (tendsto_atTop_mono (fun n ↦ sum_le_sum fun k _ ↦ ?_) tendsto_sum_inv_add_two))
  refine inv_anti₀ (totalWeight_pos γ (by omega)) ((totalWeight_le hγ).trans_eq ?_)
  push_cast
  rfl

theorem integral_memoryMean_succ_sub (n : ℕ) :
    ∫ e, memoryMean γ e ∂seqLaw (rule γ tgt ν bias seed) (n + 2) -
      ∫ e, memoryMean γ e ∂seqLaw (rule γ tgt ν bias seed) (n + 1) =
        bias / totalWeight γ (n + 2) := by
  rw [integral_memoryMean hν hν0, integral_memoryMean hν hν0, sum_range_succ]
  ring

-- §3.2, the older speaker
theorem lenition_slows_with_experience (hγ0 : 0 < γ) (hbias : bias ≠ 0) :
    StrictAnti fun n ↦ |∫ e, memoryMean γ e ∂seqLaw (rule γ tgt ν bias seed) (n + 2) -
      ∫ e, memoryMean γ e ∂seqLaw (rule γ tgt ν bias seed) (n + 1)| := by
  refine strictAnti_nat_of_succ_lt fun n ↦ ?_
  simp only [integral_memoryMean_succ_sub hν hν0, abs_div,
    abs_of_nonneg (totalWeight_nonneg γ)]
  exact div_lt_div_of_pos_left (abs_pos.2 hbias) (totalWeight_pos γ (by omega))
    (totalWeight_strictMono hγ0 (by omega))

-- The slowing of §3.2 "depends on the assumption that memories decay slowly": it stops at this
-- speed.
theorem tendsto_integral_memoryMean_succ_sub (hγ : γ < 1) :
    Tendsto (fun n ↦ ∫ e, memoryMean γ e ∂seqLaw (rule γ tgt ν bias seed) (n + 2) -
      ∫ e, memoryMean γ e ∂seqLaw (rule γ tgt ν bias seed) (n + 1)) atTop
      (𝓝 (bias * (1 - γ))) := by
  simp only [integral_memoryMean_succ_sub hν hν0]
  have h := (tendsto_const_nhds (x := bias)).div
    ((tendsto_add_atTop_iff_nat 2).2 (tendsto_totalWeight hγ))
    (inv_pos.2 (sub_pos.2 (NNReal.coe_lt_one.2 hγ))).ne'
  rwa [div_inv_eq_mul] at h

/-- With the memory time of (1) fixed in clock time, a word used every `r > 1` ticks is at any
moment less advanced than a word used at every tick, though it forgets its own tokens faster. -/
theorem lenition_advances_with_frequency (hγ0 : 0 < γ) (hγ : γ ≤ 1) (hbias : bias < 0) {r n : ℕ}
    (hr : 1 < r) (hn : n ≠ 0) :
    ∫ e, memoryMean γ e ∂seqLaw (rule γ tgt ν bias seed) (r * n + 1) <
      ∫ e, memoryMean (γ ^ r) e ∂seqLaw (rule (γ ^ r) tgt ν bias seed) (n + 1) := by
  rw [integral_memoryMean hν hν0, integral_memoryMean hν hν0]
  linarith [mul_lt_mul_of_neg_left (sum_inv_totalWeight_pow_lt hγ0 hγ hr hn) hbias]

/-- The lead of the frequent word is small at every moment: it has moved at most `r / S` times as
far as the word used every `r` ticks, for `S` the weight of `r` exemplars, plus a term that does not
grow with time. -/
theorem lenition_lead_le (hbias : bias < 0) {r : ℕ} (hr : r ≠ 0) (n : ℕ) :
    seed - ∫ e, memoryMean γ e ∂seqLaw (rule γ tgt ν bias seed) (r * n + 1) ≤
      r / totalWeight γ r *
          (seed - ∫ e, memoryMean (γ ^ r) e ∂seqLaw (rule (γ ^ r) tgt ν bias seed) (n + 1)) -
        bias * (∑ k ∈ range r, (totalWeight γ (k + 2))⁻¹ + r / totalWeight γ r) := by
  rw [integral_memoryMean hν hν0, integral_memoryMean hν hν0]
  have h := mul_le_mul_of_nonpos_left (sum_inv_totalWeight_le (γ := γ) hr n) hbias.le
  linarith

-- Once its memory is full, a word used every `r` ticks moves per tick at the speed of a word used
-- at every tick times `totalWeight γ r / r`, which `totalWeight_div_mem_Icc` keeps near one until
-- `r` nears the memory time.
theorem tendsto_clockSpeed (hγ : γ < 1) {r : ℕ} (hr : r ≠ 0) :
    Tendsto (fun n ↦ (∫ e, memoryMean (γ ^ r) e ∂seqLaw (rule (γ ^ r) tgt ν bias seed) (n + 2) -
      ∫ e, memoryMean (γ ^ r) e ∂seqLaw (rule (γ ^ r) tgt ν bias seed) (n + 1)) / r) atTop
      (𝓝 (bias * (1 - γ) * (totalWeight γ r / r))) := by
  have h := (tendsto_integral_memoryMean_succ_sub (γ := γ ^ r) (tgt := tgt) (bias := bias)
    (seed := seed) hν hν0 (pow_lt_one₀ zero_le hγ hr)).div_const (r : ℝ)
  convert h using 2
  rw [NNReal.coe_pow, ← geom_sum_mul_neg, totalWeight]
  ring

-- §3.1–3.2, Figs. 2 and 3; §3.3 for the entrenched target
theorem spread_grows (hγ0 : 0 < γ) (hc : 0 < Var[id; ν] + bias ^ 2) :
    StrictMono fun n ↦ ∫ e, memorySpread γ e ∂seqLaw (rule γ tgt ν bias seed) (n + 1) := by
  simp only [integral_memorySpread hν hν0]
  exact (spreadGrowth_strictMono hγ0 tgt.inherited_nonneg tgt.inherited_le_one).const_mul hc

-- "much as a photograph of a moving object shows a blur", §3.2
theorem lenition_blurs (hγ0 : 0 < γ) (hbias : bias ≠ 0) (n : ℕ) :
    ∫ e, memorySpread γ e ∂seqLaw (rule γ tgt ν 0 seed) (n + 2) <
      ∫ e, memorySpread γ e ∂seqLaw (rule γ tgt ν bias seed) (n + 2) := by
  rw [integral_memorySpread hν hν0, integral_memorySpread hν hν0]
  exact mul_lt_mul_of_pos_right (by simpa using sq_pos_of_ne_zero hbias)
    (spreadGrowth_pos hγ0 tgt.inherited_nonneg n)

theorem tendsto_integral_memorySpread (hγ0 : 0 < γ) (hγ : γ < 1) :
    Tendsto (fun n ↦ ∫ e, memorySpread γ e ∂seqLaw (rule γ tgt ν bias seed) (n + 1)) atTop
      (𝓝 ((Var[id; ν] + bias ^ 2) * (γ / (1 - tgt.inherited * γ)))) := by
  simp only [integral_memorySpread hν hν0]
  exact (tendsto_spreadGrowth hγ0 hγ tgt.inherited_nonneg tgt.inherited_le_one).const_mul _

/-- Without entrenchment the expected spread is bounded exactly when memory decays, against the
claim of §3.3 that the bare model cannot fill out a category without spreading it indefinitely. -/
theorem bddAbove_integral_memorySpread_iff (hγ0 : 0 < γ) (hγ : γ ≤ 1)
    (hc : 0 < Var[id; ν] + bias ^ 2) :
    BddAbove (Set.range fun n ↦
      ∫ e, memorySpread γ e ∂seqLaw (rule γ .exemplar ν bias seed) (n + 1)) ↔ γ < 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ (tendsto_integral_memorySpread hν hν0 hγ0 h).bddAbove_range⟩
  by_contra hlt
  obtain rfl := hγ.eq_of_not_lt hlt
  simp only [integral_memorySpread hν hν0] at h
  exact not_bddAbove_of_tendsto_atTop (tendsto_spreadGrowth_one_one.const_mul_atTop hc) h

/-- Entrenchment narrows the category from the second production on, since averaging over the
memory removes the spread a picked exemplar would inherit (§3.3, Fig. 4). -/
theorem entrenchment_narrows (hγ0 : 0 < γ) (hc : 0 < Var[id; ν] + bias ^ 2) (n : ℕ) :
    ∫ e, memorySpread γ e ∂seqLaw (rule γ .average ν bias seed) (n + 3) <
      ∫ e, memorySpread γ e ∂seqLaw (rule γ .exemplar ν bias seed) (n + 3) := by
  rw [integral_memorySpread hν hν0, integral_memorySpread hν hν0]
  exact mul_lt_mul_of_pos_left (spreadGrowth_lt_of_lt hγ0 le_rfl zero_lt_one n) hc

end Predictions

/-! ### The paper's noise -/

section Noise

/-- The production noise of (2), uniform on `[-0.1, 0.1]`. -/
noncomputable def noise : Measure ℝ := ProbabilityTheory.cond volume (Set.Icc (-(1 / 10)) (1 / 10))

instance : IsProbabilityMeasure noise :=
  cond_isProbabilityMeasure_of_finite (by norm_num [Real.volume_Icc]) (by simp [Real.volume_Icc])

private theorem integral_noise_eq (f : ℝ → ℝ) :
    ∫ x, f x ∂noise = 5 * ∫ x in (-(1 / 10) : ℝ)..(1 / 10), f x := by
  rw [noise, ProbabilityTheory.cond, integral_smul_measure, Real.volume_Icc,
    intervalIntegral.integral_of_le (by norm_num), integral_Icc_eq_integral_Ioc]
  norm_num [smul_eq_mul]

theorem memLp_noise : MemLp id 2 noise := by
  refine MemLp.of_bound (by fun_prop) (1 / 10) ?_
  have h : ∀ᵐ x ∂(volume.restrict (Set.Icc (-(1 / 10) : ℝ) (1 / 10))), ‖id x‖ ≤ 1 / 10 :=
    ae_restrict_of_forall_mem measurableSet_Icc fun x hx ↦ by
      simpa [abs_le] using hx
  exact Measure.ae_smul_measure h _

theorem integral_noise : ∫ x, x ∂noise = 0 := by
  rw [integral_noise_eq, integral_id]
  norm_num

theorem variance_noise : Var[id; noise] = 1 / 300 := by
  rw [variance_eq_sub memLp_noise]
  simp only [id, Pi.pow_apply]
  rw [integral_noise, integral_noise_eq, integral_pow]
  norm_num

-- Fig. 3, the paper's noise and bias from its seed: the mean falls at every production.
example (γ : ℝ≥0) (tgt : Target) :
    StrictAnti fun n ↦ ∫ e, memoryMean γ e ∂seqLaw (rule γ tgt noise (-(1 / 100)) 1) (n + 1) :=
  lenition_advances_with_use memLp_noise integral_noise (by norm_num)

-- Fig. 2, no bias: the mean stays at the seed.
example (γ : ℝ≥0) (tgt : Target) (n : ℕ) :
    ∫ e, memoryMean γ e ∂seqLaw (rule γ tgt noise 0 1) (n + 1) = 1 := by
  rw [integral_memoryMean memLp_noise integral_noise]
  simp

-- At the paper's noise and bias: no decay spreads without bound.
example : ¬ BddAbove (Set.range fun n ↦
    ∫ e, memorySpread 1 e ∂seqLaw (rule 1 .exemplar noise (-(1 / 100)) 1) (n + 1)) := by
  rw [bddAbove_integral_memorySpread_iff memLp_noise integral_noise one_pos le_rfl
    (by rw [variance_noise]; norm_num)]
  simp

-- At the paper's memory time of 2000: the expected spread converges, to between
-- 1999 and 2000 times what noise and bias add, a standard deviation of about 2.6.
example {γ : ℝ≥0} (hγ : (γ : ℝ) = Real.exp (-(2000 : ℝ)⁻¹)) :
    ∃ L ∈ Set.Icc (1999 * (103 / 30000) : ℝ) (2000 * (103 / 30000)), Tendsto (fun n ↦
      ∫ e, memorySpread γ e ∂seqLaw (rule γ .exemplar noise (-(1 / 100)) 1) (n + 1)) atTop
        (𝓝 L) := by
  have hpos : 0 < γ := NNReal.coe_pos.1 (hγ ▸ Real.exp_pos _)
  have hlt : γ < 1 := NNReal.coe_lt_one.1 (hγ ▸ Real.exp_lt_one_iff.2 (by norm_num))
  have hI := div_one_sub_mem_Icc_of_eq_exp (by norm_num : (0 : ℝ) < 2000) hγ
  refine ⟨_, ?_, tendsto_integral_memorySpread memLp_noise integral_noise hpos hlt⟩
  rw [variance_noise, Target.inherited, one_mul]
  constructor <;> nlinarith [hI.1, hI.2]

-- What noise and bias add at a production, the unit of the expected spread.
example : Var[id; noise] + (-(1 / 100) : ℝ) ^ 2 = 103 / 30000 := by
  rw [variance_noise]; norm_num

end Noise

end Pierrehumbert2001
