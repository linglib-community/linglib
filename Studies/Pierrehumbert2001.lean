/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.Kernel.IonescuTulcea.SeqLaw
public import Linglib.Core.Probability.Moments.Convolution
public import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Pierrehumbert (2001): Exemplar dynamics: Word frequency, lenition and contrast

This file formalizes Pierrehumbert's exemplar model of production. A category is a
list of remembered tokens, each weighted by its age. To produce the category a speaker picks a
target, either an exemplar drawn with probability proportional to its weight or, under
entrenchment, the memory-weighted mean, and adds production noise and a constant lenition bias.
Every produced token is stored, so the list is drawn from a prediction rule (`rule`) and its law
is `ProbabilityTheory.seqLaw`.

The paper presents its results as simulations. Here they are exact statements about the expected
memory-weighted mean and spread. Each production moves the expected mean by the bias divided by
the total memory weight (`integral_memoryMean`), so a leniting change is further advanced the
more a word is used, and slows as memory accumulates. Without entrenchment the expected spread
grows at every production, and lenition adds to it; with entrenchment it stays below the variance
that noise and bias add at a production, and below the spread without entrenchment.

## Main statements

* `lenition_advances_with_use`: under a leniting bias the expected mean falls with every use.
* `spread_grows`, `lenition_blurs`: without entrenchment the expected spread grows with every
  use, and lenition widens it.
* `entrenchment_narrows`: entrenchment keeps the expected spread below the bare model's.

## Implementation notes

* Every production is stored, the idealization of §3.1. The single-label loop of the appendix
  stores a token only if its score (1) is nonzero, a filter the theorems leave out.
* Entrenchment is its large-neighborhood limit, the memory-weighted mean (appendix); the rule of
  Fig. 4, the mean of the 500 nearest exemplars, is not formalized.
* The decay factor `γ` is `exp (-1/τ)` for the paper's memory time `τ`, and `γ = 1` is no decay.
  The noise is any centered square-integrable law; the paper's is uniform on `[-0.1, 0.1]`.
* Section, figure and equation numbers are those of the author's manuscript of June 2000.

## TODO

* The score function (1), the two-label loop of the appendix, and the neutralization of §4
  (Fig. 5), in which a leniting marked category is absorbed by a stable unmarked one.

## References

* [pierrehumbert-2001]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace Pierrehumbert2001

/-! ### The memory -/

section Memory

variable (γ : ℝ≥0) {n : ℕ}

/-- The total weight of `n` exemplars, the `i`th of which has age `n - 1 - i`. -/
noncomputable def totalWeight (n : ℕ) : ℝ := ∑ i : Fin n, (γ : ℝ) ^ (i.rev : ℕ)

/-- The memory-weighted mean of an exemplar list. -/
noncomputable def memoryMean (e : Fin n → ℝ) : ℝ :=
  (∑ i, (γ : ℝ) ^ (i.rev : ℕ) * e i) / totalWeight γ n

/-- The memory-weighted spread of an exemplar list about its mean. -/
noncomputable def memorySpread (e : Fin n → ℝ) : ℝ :=
  (∑ i, (γ : ℝ) ^ (i.rev : ℕ) * (e i - memoryMean γ e) ^ 2) / totalWeight γ n

theorem totalWeight_succ : totalWeight γ (n + 1) = γ * totalWeight γ n + 1 := by
  simp only [totalWeight, Fin.sum_univ_castSucc, Fin.rev_castSucc, Fin.rev_last, Fin.val_zero,
    pow_zero, Fin.val_succ, pow_succ, mul_sum]
  congr 1
  exact sum_congr rfl fun i _ ↦ by ring

theorem totalWeight_succ' : totalWeight γ (n + 1) = totalWeight γ n + γ ^ n := by
  rw [totalWeight, Fin.sum_univ_succ, Fin.rev_zero, Fin.val_last, add_comm]
  simp only [Fin.rev_succ, Fin.val_castSucc]
  rfl

theorem totalWeight_nonneg : 0 ≤ totalWeight γ n := sum_nonneg fun _ _ ↦ by positivity

theorem one_le_totalWeight (hn : n ≠ 0) : 1 ≤ totalWeight γ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [totalWeight_succ]
  linarith [mul_nonneg γ.coe_nonneg (totalWeight_nonneg γ (n := m))]

theorem totalWeight_pos (hn : n ≠ 0) : 0 < totalWeight γ n :=
  one_pos.trans_le (one_le_totalWeight γ hn)

theorem totalWeight_mono : Monotone (totalWeight γ) :=
  monotone_nat_of_le_succ fun n ↦ by
    rw [totalWeight_succ']; exact le_add_of_nonneg_right (by positivity)

theorem totalWeight_mul_one_sub_le (hγ : γ ≤ 1) : totalWeight γ n * (1 - γ) ≤ 1 := by
  induction n with
  | zero => simp [totalWeight]
  | succ n ih =>
    have := totalWeight_nonneg γ (n := n)
    have : (γ : ℝ) ≤ 1 := by exact_mod_cast hγ
    rw [totalWeight_succ]
    nlinarith [γ.coe_nonneg]

theorem totalWeight_mul_one_sub_lt (hγ0 : 0 < γ) (hγ : γ ≤ 1) :
    totalWeight γ n * (1 - γ) < 1 := by
  induction n with
  | zero => simp [totalWeight]
  | succ n ih =>
    have := totalWeight_nonneg γ (n := n)
    have : (γ : ℝ) ≤ 1 := by exact_mod_cast hγ
    have : (0 : ℝ) < γ := by exact_mod_cast hγ0
    rw [totalWeight_succ]
    nlinarith

theorem totalWeight_mul_memoryMean (e : Fin n → ℝ) :
    totalWeight γ n * memoryMean γ e = ∑ i, (γ : ℝ) ^ (i.rev : ℕ) * e i := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [totalWeight]
  · exact mul_div_cancel₀ _ (totalWeight_pos γ hn.ne').ne'

theorem totalWeight_mul_memorySpread (e : Fin n → ℝ) :
    totalWeight γ n * memorySpread γ e =
      ∑ i, (γ : ℝ) ^ (i.rev : ℕ) * (e i - memoryMean γ e) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [totalWeight]
  · exact mul_div_cancel₀ _ (totalWeight_pos γ hn.ne').ne'

theorem sum_mul_sub_sq (e : Fin n → ℝ) (c : ℝ) :
    ∑ i, (γ : ℝ) ^ (i.rev : ℕ) * (e i - c) ^ 2 =
      totalWeight γ n * memorySpread γ e + totalWeight γ n * (memoryMean γ e - c) ^ 2 := by
  have h : ∑ i, (γ : ℝ) ^ (i.rev : ℕ) * (e i - c) ^ 2 =
      ∑ i, (γ : ℝ) ^ (i.rev : ℕ) * (e i - memoryMean γ e) ^ 2 +
        2 * (memoryMean γ e - c) * (∑ i, (γ : ℝ) ^ (i.rev : ℕ) * e i -
          totalWeight γ n * memoryMean γ e) + totalWeight γ n * (memoryMean γ e - c) ^ 2 := by
    simp only [totalWeight, mul_sum, sum_mul, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun i _ ↦ by ring
  rw [h, totalWeight_mul_memoryMean, sub_self, mul_zero, add_zero, totalWeight_mul_memorySpread]

theorem memoryMean_snoc (e : Fin n → ℝ) (x : ℝ) :
    memoryMean γ (Fin.snoc e x : Fin (n + 1) → ℝ) =
      (γ * totalWeight γ n * memoryMean γ e + x) / totalWeight γ (n + 1) := by
  rw [memoryMean, mul_assoc, totalWeight_mul_memoryMean, mul_sum]
  simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, Fin.rev_castSucc,
    Fin.rev_last, Fin.val_succ, Fin.val_zero, pow_zero, one_mul, pow_succ]
  congr 2
  exact sum_congr rfl fun i _ ↦ by ring

theorem memorySpread_snoc (e : Fin n → ℝ) (x : ℝ) :
    memorySpread γ (Fin.snoc e x : Fin (n + 1) → ℝ) =
      γ * totalWeight γ n / totalWeight γ (n + 1) * memorySpread γ e +
        γ * totalWeight γ n / totalWeight γ (n + 1) ^ 2 * (x - memoryMean γ e) ^ 2 := by
  have hS := totalWeight_pos γ (Nat.succ_ne_zero n)
  have hsum : ∑ i : Fin (n + 1), (γ : ℝ) ^ (i.rev : ℕ) * ((Fin.snoc e x : Fin (n + 1) → ℝ) i -
      memoryMean γ (Fin.snoc e x : Fin (n + 1) → ℝ)) ^ 2 =
      γ * (totalWeight γ n * memorySpread γ e + totalWeight γ n *
        (memoryMean γ e - memoryMean γ (Fin.snoc e x : Fin (n + 1) → ℝ)) ^ 2) +
      (x - memoryMean γ (Fin.snoc e x : Fin (n + 1) → ℝ)) ^ 2 := by
    rw [← sum_mul_sub_sq, mul_sum]
    simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, Fin.rev_castSucc,
      Fin.rev_last, Fin.val_succ, Fin.val_zero, pow_zero, one_mul, pow_succ]
    congr 1
    exact sum_congr rfl fun i _ ↦ by ring
  rw [memorySpread, hsum, memoryMean_snoc, totalWeight_succ]
  rw [totalWeight_succ] at hS
  generalize totalWeight γ n = S at *
  generalize memoryMean γ e = M
  generalize memorySpread γ e = V
  field_simp
  ring

@[fun_prop] theorem measurable_memoryMean : Measurable (memoryMean γ : (Fin n → ℝ) → ℝ) := by
  unfold memoryMean
  fun_prop

end Memory

/-! ### Production -/

section Production

variable (γ : ℝ≥0) {n : ℕ}

/-- The recency distribution of the appendix, picking a position with probability proportional
to its weight. -/
noncomputable def recency (n : ℕ) : Measure (Fin n) :=
  ∑ i, ((γ : ℝ) ^ (i.rev : ℕ) / totalWeight γ n).toNNReal • Measure.dirac i

theorem integral_recency (f : Fin n → ℝ) :
    ∫ i, f i ∂recency γ n = ∑ i, (γ : ℝ) ^ (i.rev : ℕ) / totalWeight γ n * f i := by
  rw [recency, integral_finsetSum_measure fun i _ ↦ .of_finite]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [integral_smul_nnreal_measure, integral_dirac, NNReal.smul_def, Real.coe_toNNReal _
    (div_nonneg (by positivity) (totalWeight_nonneg γ)), smul_eq_mul]

instance (n : ℕ) : IsProbabilityMeasure (recency γ (n + 1)) := by
  constructor
  rw [recency, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul,
    mul_one, ENNReal.smul_def]
  rw [← ENNReal.ofNNReal_finsetSum, ← Real.toNNReal_sum_of_nonneg fun i _ ↦
    div_nonneg (by positivity) (totalWeight_nonneg γ), ← sum_div,
    show ∑ i : Fin (n + 1), (γ : ℝ) ^ (i.rev : ℕ) = totalWeight γ (n + 1) from rfl,
    div_self (totalWeight_pos γ (Nat.succ_ne_zero n)).ne']
  simp

/-- The production target of the appendix, an exemplar picked by recency or the memory-weighted
mean, to which entrenchment fixes the target in the limit of a large neighborhood. -/
inductive Target
  | exemplar
  | average

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
    produce γ tgt ν bias e = (target γ tgt e ∗ ν).map (· + bias) := by
  rw [produce, Kernel.map_apply _ (by fun_prop), Kernel.prod_apply, Kernel.const_apply,
    Measure.conv, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem memLp_target (e : Fin (n + 1) → ℝ) : MemLp id 2 (target γ tgt e) := by
  cases tgt
  · rw [target_exemplar_apply, memLp_map_measure_iff (by fun_prop) (by fun_prop)]
    exact MemLp.of_bound (by fun_prop) (∑ i, |e i|) (.of_forall fun i ↦ by
      simpa using single_le_sum (f := fun i ↦ |e i|) (fun _ _ ↦ abs_nonneg _) (mem_univ i))
  · exact MemLp.of_bound (by fun_prop) |memoryMean γ e|
      (by simp [target_average_apply, ae_dirac_eq])

theorem integral_target (e : Fin (n + 1) → ℝ) : ∫ t, t ∂target γ tgt e = memoryMean γ e := by
  cases tgt
  · rw [target_exemplar_apply, integral_map (by fun_prop) (by fun_prop), integral_recency,
      memoryMean, sum_div]
    exact sum_congr rfl fun i _ ↦ by ring
  · simp [target_average_apply]

theorem variance_target (e : Fin (n + 1) → ℝ) :
    Var[id; target γ tgt e] = match tgt with
      | .exemplar => memorySpread γ e
      | .average => 0 := by
  cases tgt
  · rw [target_exemplar_apply, variance_id_map (by fun_prop),
      variance_eq_integral (by fun_prop), integral_recency, memorySpread, sum_div]
    have : ∫ i, e i ∂recency γ (n + 1) = memoryMean γ e := by
      rw [integral_recency, memoryMean, sum_div]
      exact sum_congr rfl fun i _ ↦ by ring
    simp only [this]
    exact sum_congr rfl fun i _ ↦ by ring
  · simp [target_average_apply]

variable (hν : MemLp id 2 ν) (hν0 : ∫ x, x ∂ν = 0)
include hν

theorem memLp_produce (e : Fin (n + 1) → ℝ) : MemLp id 2 (produce γ tgt ν bias e) := by
  rw [produce_apply, memLp_map_measure_iff (by fun_prop) (by fun_prop)]
  exact (memLp_id_conv (memLp_target γ tgt e) hν).add (memLp_const bias)

include hν0

theorem integral_produce (e : Fin (n + 1) → ℝ) :
    ∫ x, x ∂produce γ tgt ν bias e = memoryMean γ e + bias := by
  have h : Integrable (fun x : ℝ ↦ x) (target γ tgt e ∗ ν) :=
    (memLp_id_conv (memLp_target γ tgt e) hν).integrable one_le_two
  rw [produce_apply, integral_map (by fun_prop) (by fun_prop), integral_add h (integrable_const _),
    integral_id_conv ((memLp_target γ tgt e).integrable one_le_two) (hν.integrable one_le_two),
    integral_target, hν0]
  simp

theorem integral_produce_sub_sq (e : Fin (n + 1) → ℝ) :
    ∫ x, (x - memoryMean γ e) ^ 2 ∂produce γ tgt ν bias e =
      (match tgt with | .exemplar => memorySpread γ e | .average => 0) + Var[id; ν] + bias ^ 2 := by
  have h := memLp_id_conv (memLp_target γ tgt e) hν
  rw [produce_apply, integral_map (by fun_prop) (by fun_prop)]
  simp only [show ∀ y, y + bias - memoryMean γ e = y - (memoryMean γ e - bias) from
    fun y ↦ by ring]
  rw [integral_sub_sq h, variance_id_conv (memLp_target γ tgt e) hν,
    integral_id_conv ((memLp_target γ tgt e).integrable one_le_two) (hν.integrable one_le_two),
    integral_target, hν0, variance_target]
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
  rw [memoryMean, div_eq_mul_inv]

theorem integrable_memorySpread : Integrable (memorySpread γ) μ := by
  unfold memorySpread
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
        cases tgt
        · exact ((integrable_memorySpread ih).add (integrable_const _)).add (integrable_const _)
        · simp
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

/-- The expected memory-weighted mean after `n` productions: each production moves it by the
bias divided by the total memory weight (§3.2). -/
theorem integral_memoryMean (n : ℕ) :
    ∫ e, memoryMean γ e ∂seqLaw (rule γ tgt ν bias seed) (n + 1) =
      seed + bias * ∑ k ∈ range n, (totalWeight γ (k + 2))⁻¹ := by
  induction n with
  | zero =>
    rw [seqLaw_rule_one, integral_dirac]
    simp [memoryMean, totalWeight]
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
          ((match tgt with | .exemplar => memorySpread γ e | .average => 0) + Var[id; ν] +
            bias ^ 2) := by
  have hx : Integrable (fun x : ℝ ↦ (x - memoryMean γ e) ^ 2) (produce γ tgt ν bias e) :=
    ((memLp_produce γ tgt bias hν e).sub (memLp_const _)).integrable_sq
  simp_rw [memorySpread_snoc, rule_succ]
  rw [integral_add (integrable_const _) (hx.const_mul _), integral_const, integral_const_mul,
    integral_produce_sub_sq γ tgt bias hν hν0]
  simp only [probReal_univ, one_smul]

end Law

/-! ### Growth of the spread -/

section Growth

variable (γ : ℝ≥0)

/-- The expected spread after `n` productions in units of the variance that noise and bias add at
a production. A production keeps the older exemplars' share of the spread and adds the new
token's deviation from the mean, which a picked exemplar inherits from the memory and the mean
target does not. -/
noncomputable def spreadGrowth : Target → ℕ → ℝ
  | _, 0 => 0
  | .exemplar, n + 1 =>
    γ * totalWeight γ (n + 1) / totalWeight γ (n + 2) * spreadGrowth .exemplar n +
      γ * totalWeight γ (n + 1) / totalWeight γ (n + 2) ^ 2 * (spreadGrowth .exemplar n + 1)
  | .average, n + 1 =>
    γ * totalWeight γ (n + 1) / totalWeight γ (n + 2) * spreadGrowth .average n +
      γ * totalWeight γ (n + 1) / totalWeight γ (n + 2) ^ 2

private theorem coeff_nonneg (n k : ℕ) :
    0 ≤ (γ : ℝ) * totalWeight γ (n + 1) / totalWeight γ (n + 2) ^ k :=
  div_nonneg (mul_nonneg γ.coe_nonneg (totalWeight_nonneg γ)) (pow_nonneg (totalWeight_nonneg γ) k)

theorem spreadGrowth_nonneg (tgt : Target) (n : ℕ) : 0 ≤ spreadGrowth γ tgt n := by
  induction n with
  | zero => cases tgt <;> simp [spreadGrowth]
  | succ n ih =>
    have h1 := coeff_nonneg γ n 1
    have h2 := coeff_nonneg γ n 2
    rw [pow_one] at h1
    cases tgt
    · exact add_nonneg (mul_nonneg h1 ih) (mul_nonneg h2 (by linarith))
    · exact add_nonneg (mul_nonneg h1 ih) h2

theorem spreadGrowth_pos (hγ0 : 0 < γ) (tgt : Target) (n : ℕ) : 0 < spreadGrowth γ tgt (n + 1) := by
  have hA := coeff_nonneg γ n 1
  rw [pow_one] at hA
  have hB : 0 < (γ : ℝ) * totalWeight γ (n + 1) / totalWeight γ (n + 2) ^ 2 :=
    div_pos (mul_pos (by exact_mod_cast hγ0) (totalWeight_pos γ (by omega)))
      (pow_pos (totalWeight_pos γ (by omega)) 2)
  have hg := spreadGrowth_nonneg γ tgt n
  cases tgt
  · exact add_pos_of_nonneg_of_pos (mul_nonneg hA hg) (mul_pos hB (by linarith))
  · exact add_pos_of_nonneg_of_pos (mul_nonneg hA hg) hB

theorem spreadGrowth_exemplar_succ (n : ℕ) :
    spreadGrowth γ .exemplar (n + 1) = spreadGrowth γ .exemplar n +
      (γ * totalWeight γ (n + 1) - spreadGrowth γ .exemplar n) / totalWeight γ (n + 2) ^ 2 := by
  have hS := totalWeight_pos γ (Nat.succ_ne_zero (n + 1))
  rw [spreadGrowth, totalWeight_succ (n := n + 1)] at *
  field_simp
  ring

theorem spreadGrowth_exemplar_le (hγ : γ ≤ 1) (n : ℕ) :
    spreadGrowth γ .exemplar n ≤ totalWeight γ (n + 1) - 1 := by
  induction n with
  | zero => simp [spreadGrowth, totalWeight]
  | succ n ih =>
    have hS1 := one_le_totalWeight γ (Nat.succ_ne_zero n)
    have hu := totalWeight_mul_one_sub_le γ hγ (n := n + 1)
    rw [spreadGrowth_exemplar_succ, totalWeight_succ (n := n + 1)]
    set S := totalWeight γ (n + 1)
    have hx : 0 ≤ (γ : ℝ) * S := mul_nonneg γ.coe_nonneg (zero_le_one.trans hS1)
    have hS' : 0 < (γ * S + 1) ^ 2 := by positivity
    have hS'1 : 0 ≤ (γ * S + 1) ^ 2 - 1 := by nlinarith
    rw [add_div' _ _ _ hS'.ne', div_le_iff₀ hS']
    nlinarith [mul_nonneg hS'1 (sub_nonneg.2 hu), mul_nonneg hS'1 (sub_nonneg.2 ih)]

theorem spreadGrowth_exemplar_strictMono (hγ0 : 0 < γ) (hγ : γ ≤ 1) :
    StrictMono (spreadGrowth γ .exemplar) := by
  refine strictMono_nat_of_lt_succ fun n ↦ ?_
  have hu := totalWeight_mul_one_sub_lt γ hγ0 hγ (n := n + 1)
  have := spreadGrowth_exemplar_le γ hγ n
  have hS := totalWeight_pos γ (Nat.succ_ne_zero (n + 1))
  rw [spreadGrowth_exemplar_succ, lt_add_iff_pos_right]
  exact div_pos (by nlinarith) (by positivity)

theorem spreadGrowth_average_le_one (n : ℕ) : spreadGrowth γ .average n ≤ 1 := by
  induction n with
  | zero => simp [spreadGrowth]
  | succ n ih =>
    have hS1 := one_le_totalWeight γ (Nat.succ_ne_zero n)
    simp only [spreadGrowth]
    rw [totalWeight_succ (n := n + 1)]
    set S := totalWeight γ (n + 1)
    have hx : 0 ≤ (γ : ℝ) * S := mul_nonneg γ.coe_nonneg (zero_le_one.trans hS1)
    have hS' : 0 < γ * S + 1 := by positivity
    rw [div_mul_eq_mul_div, div_add_div _ _ hS'.ne' (by positivity), div_le_one (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hx (sq_nonneg (γ * S + 1))) (sub_nonneg.2 ih),
      mul_nonneg hx hS'.le]

theorem spreadGrowth_average_le_exemplar (n : ℕ) :
    spreadGrowth γ .average n ≤ spreadGrowth γ .exemplar n := by
  induction n with
  | zero => simp [spreadGrowth]
  | succ n ih =>
    have hA := coeff_nonneg γ n 1
    rw [pow_one] at hA
    simp only [spreadGrowth]
    nlinarith [mul_le_mul_of_nonneg_left ih hA,
      mul_nonneg (coeff_nonneg γ n 2) (spreadGrowth_nonneg γ .exemplar n)]

end Growth

/-! ### Predictions -/

section Predictions

variable {γ : ℝ≥0} {tgt : Target} {ν : Measure ℝ} [IsProbabilityMeasure ν] {bias seed : ℝ}
  (hν : MemLp id 2 ν) (hν0 : ∫ x, x ∂ν = 0)
include hν hν0

theorem integral_memorySpread (n : ℕ) :
    ∫ e, memorySpread γ e ∂seqLaw (rule γ tgt ν bias seed) (n + 1) =
      (Var[id; ν] + bias ^ 2) * spreadGrowth γ tgt n := by
  induction n with
  | zero =>
    rw [seqLaw_rule_one, integral_dirac]
    simp [memorySpread, memoryMean, totalWeight, spreadGrowth]
  | succ n ih =>
    have hV : Integrable (memorySpread γ) (seqLaw (rule γ tgt ν bias seed) (n + 1)) :=
      integrable_memorySpread (memLp_apply hν hν0 n)
    rw [integral_seqLaw_succ (integrable_memorySpread (memLp_apply hν hν0 (n + 1)))]
    simp_rw [integral_memorySpread_snoc hν hν0]
    set A := (γ : ℝ) * totalWeight γ (n + 1) / totalWeight γ (n + 2)
    set B := (γ : ℝ) * totalWeight γ (n + 1) / totalWeight γ (n + 2) ^ 2
    set c := Var[id; ν] + bias ^ 2
    cases tgt
    · simp only [show ∀ V, A * V + B * (V + Var[id; ν] + bias ^ 2) = (A + B) * V + B * c from
        fun V ↦ by ring]
      rw [integral_add (hV.const_mul _) (integrable_const _), integral_const_mul, ih]
      simp only [integral_const, probReal_univ, one_smul, spreadGrowth, A, B, c]
      ring
    · simp only [show ∀ V, A * V + B * (0 + Var[id; ν] + bias ^ 2) = A * V + B * c from
        fun V ↦ by ring]
      rw [integral_add (hV.const_mul _) (integrable_const _), integral_const_mul, ih]
      simp only [integral_const, probReal_univ, one_smul, spreadGrowth, A, B, c]
      ring

/-- Under a leniting bias the expected memory mean falls with every production, so a change in
progress is further advanced in a word the more it is used (§3.2, Fig. 3). -/
theorem lenition_advances_with_use (hbias : bias < 0) :
    StrictAnti fun n ↦ ∫ e, memoryMean γ e ∂seqLaw (rule γ tgt ν bias seed) (n + 1) := by
  refine strictAnti_nat_of_succ_lt fun n ↦ ?_
  simp only [integral_memoryMean hν hν0, sum_range_succ, mul_add, add_lt_iff_neg_left,
    ← add_assoc]
  exact mul_neg_of_neg_of_pos hbias (inv_pos.2 (totalWeight_pos γ (by omega)))

theorem integral_memoryMean_succ_sub (n : ℕ) :
    ∫ e, memoryMean γ e ∂seqLaw (rule γ tgt ν bias seed) (n + 2) -
      ∫ e, memoryMean γ e ∂seqLaw (rule γ tgt ν bias seed) (n + 1) =
        bias / totalWeight γ (n + 2) := by
  rw [integral_memoryMean hν hν0, integral_memoryMean hν hν0, sum_range_succ]
  ring

/-- The more exemplars a speaker has stored, the less a production moves the expected mean
(§3.2). -/
theorem lenition_slows_with_experience :
    Antitone fun n ↦ |∫ e, memoryMean γ e ∂seqLaw (rule γ tgt ν bias seed) (n + 2) -
      ∫ e, memoryMean γ e ∂seqLaw (rule γ tgt ν bias seed) (n + 1)| := by
  refine antitone_nat_of_succ_le fun n ↦ ?_
  simp only [integral_memoryMean_succ_sub hν hν0, abs_div,
    abs_of_nonneg (totalWeight_nonneg γ)]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (totalWeight_pos γ (by omega))
    (totalWeight_mono γ (by omega))

/-- Without entrenchment the expected spread grows with every production, noise and bias alike
widening the category (§3.1–3.2, Figs. 2 and 3). -/
theorem spread_grows (hγ0 : 0 < γ) (hγ : γ ≤ 1) (hc : 0 < Var[id; ν] + bias ^ 2) :
    StrictMono fun n ↦ ∫ e, memorySpread γ e ∂seqLaw (rule γ .exemplar ν bias seed) (n + 1) := by
  simp only [integral_memorySpread hν hν0]
  exact (spreadGrowth_exemplar_strictMono γ hγ0 hγ).const_mul hc

/-- Lenition widens the category as well as shifting it, "much as a photograph of a moving object
shows a blur" (§3.2). -/
theorem lenition_blurs (hγ0 : 0 < γ) (hbias : bias ≠ 0) (n : ℕ) :
    ∫ e, memorySpread γ e ∂seqLaw (rule γ tgt ν 0 seed) (n + 2) <
      ∫ e, memorySpread γ e ∂seqLaw (rule γ tgt ν bias seed) (n + 2) := by
  rw [integral_memorySpread hν hν0, integral_memorySpread hν hν0]
  exact mul_lt_mul_of_pos_right (by simpa using sq_pos_of_ne_zero hbias)
    (spreadGrowth_pos γ hγ0 tgt n)

theorem integral_memorySpread_le (hγ : γ ≤ 1) (n : ℕ) :
    ∫ e, memorySpread γ e ∂seqLaw (rule γ .exemplar ν bias seed) (n + 1) ≤
      (Var[id; ν] + bias ^ 2) * (totalWeight γ (n + 1) - 1) := by
  rw [integral_memorySpread hν hν0]
  exact mul_le_mul_of_nonneg_left (spreadGrowth_exemplar_le γ hγ n)
    (add_nonneg (variance_nonneg _ _) (sq_nonneg _))

/-- Entrenchment narrows the category, since averaging over the memory keeps the expected spread
below the spread of the bare model (§3.3, Fig. 4). -/
theorem entrenchment_narrows (n : ℕ) :
    ∫ e, memorySpread γ e ∂seqLaw (rule γ .average ν bias seed) (n + 1) ≤
      ∫ e, memorySpread γ e ∂seqLaw (rule γ .exemplar ν bias seed) (n + 1) := by
  simp only [integral_memorySpread hν hν0]
  exact mul_le_mul_of_nonneg_left (spreadGrowth_average_le_exemplar γ n)
    (add_nonneg (variance_nonneg _ _) (sq_nonneg _))

/-- With entrenchment the expected spread never exceeds what noise and bias add at a single
production, however long the change runs (§3.3). -/
theorem integral_memorySpread_average_le (n : ℕ) :
    ∫ e, memorySpread γ e ∂seqLaw (rule γ .average ν bias seed) (n + 1) ≤
      Var[id; ν] + bias ^ 2 := by
  rw [integral_memorySpread hν hν0]
  exact mul_le_of_le_one_right (add_nonneg (variance_nonneg _ _) (sq_nonneg _))
    (spreadGrowth_average_le_one γ n)

end Predictions

end Pierrehumbert2001
