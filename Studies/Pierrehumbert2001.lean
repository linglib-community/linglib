/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.Kernel.IonescuTulcea.SeqLaw
public import Linglib.Core.Probability.Moments.Convolution
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
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
further along](##lenition_advances_with_frequency) but [hardly moves
faster](##tendsto_clockSpeed). The expected spread [grows at every production](##spread_grows),
[without bound exactly when memory does not decay](##bddAbove_integral_memorySpread_iff), and
[entrenchment narrows it](##entrenchment_narrows).

## Implementation notes

* Every production is stored, the idealization of the paper's one-label figures. The single-label
  loop of its appendix stores a token only if its score is nonzero, a filter the theorems leave
  out.
* Entrenchment is its large-neighborhood limit, the memory-weighted mean; the rule of the paper's
  simulations, the mean of the 500 nearest exemplars, is not formalized.
* The decay factor `γ` is `exp (-1/τ)` for the paper's memory time `τ`, and `γ = 1` is no decay.
  The paper's score and recency decay in clock time, so a word used every `r` ticks has exemplars
  `r` ticks apart, its own tokens decay by `γ ^ r`, and `rule (γ ^ r)` is its law. Words picked at
  random, as in the paper's two-label loop, are not formalized.
* The noise is any centered square-integrable law, and [the paper's is one](##memLp_noise).
* Locators are those of the author's manuscript of June 2000.

## Errata

* The bare model is said to admit no parameter setting on which a category fills out without the
  spreading going on indefinitely (§3.3). In fact its expected spread is [bounded whenever memory
  decays](##bddAbove_integral_memorySpread_iff) and
  [converges](##tendsto_integral_memorySpread_exemplar) to $\gamma/(1-\gamma)$ times what noise and
  bias add at a production, over some $\tau^2$ productions. With the paper's noise and bias a memory
  time of 50 settles at a standard deviation of .41 within some 10,000 tokens. Its own 2000 settles
  at 2.6, over millions.
* Fig. 3 is read synchronically as words of 10,000 to 100,000 tokens (§3.2), which takes one decay
  per own token for every word. The appendix instead holds $\tau$ fixed for all labels in clock
  time and notes without quantifying that rare words then reach less of their list. That effect
  almost cancels the fewer applications of the bias: [the clock speed](##tendsto_clockSpeed) of a
  word used every $r$ ticks is within a factor [$\gamma^{r-1}$](##totalWeight_div_mem_Icc)
  of the most frequent word's. By the closed form the means at 100,000 and 10,000 tokens differ by
  .45 at one decay per token, but by .024 at $\tau = 2000$ ticks and the same clock time.
* A larger neighborhood is said to give the high-count case less variance than the low-count case
  (§3.3). In the limit of the largest neighborhood [the expected spread still rises with every
  production](##spread_grows), toward [$\gamma$ times what noise and bias
  add](##tendsto_integral_memorySpread_average), so there the order of the two is not reversed.

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

theorem sum_pow_rev {R : Type*} [CommSemiring R] (x : R) :
    ∑ i : Fin n, x ^ (i.rev : ℕ) = ∑ i ∈ range n, x ^ i :=
  (Equiv.sum_comp Fin.revPerm fun i : Fin n ↦ x ^ (i : ℕ)).trans (Fin.sum_univ_eq_sum_range _ n)

/-- The total weight of `n` exemplars, the `i`th youngest of which has weight `γ ^ i`. -/
noncomputable def totalWeight (n : ℕ) : ℝ := ∑ i ∈ range n, (γ : ℝ) ^ i

/-- The memory-weighted mean of an exemplar list. -/
noncomputable def memoryMean (e : Fin n → ℝ) : ℝ :=
  (∑ i, (γ : ℝ) ^ (i.rev : ℕ) * e i) / totalWeight γ n

/-- The memory-weighted spread of an exemplar list about its mean. -/
noncomputable def memorySpread (e : Fin n → ℝ) : ℝ :=
  (∑ i, (γ : ℝ) ^ (i.rev : ℕ) * (e i - memoryMean γ e) ^ 2) / totalWeight γ n

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
    have : (0 : ℝ) < γ := by exact_mod_cast hγ0
    rw [totalWeight_succ']; exact lt_add_of_pos_left _ (by positivity)

variable {γ} in
theorem totalWeight_le_inv (hγ : γ < 1) : totalWeight γ n ≤ (1 - (γ : ℝ))⁻¹ := by
  have h : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
  rw [← one_div, le_div_iff₀ h, totalWeight, geom_sum_mul_neg]
  exact sub_le_self _ (by positivity)

variable {γ} in
theorem tendsto_totalWeight (hγ : γ < 1) : Tendsto (totalWeight γ) atTop (𝓝 (1 - (γ : ℝ))⁻¹) :=
  (hasSum_geometric_of_lt_one γ.coe_nonneg (by exact_mod_cast hγ)).tendsto_sum_nat

theorem totalWeight_one : totalWeight 1 n = n := by simp [totalWeight]

variable {γ} in
theorem totalWeight_le (hγ : γ ≤ 1) : totalWeight γ n ≤ n :=
  (sum_le_card_nsmul _ _ 1 fun _ _ ↦ pow_le_one₀ γ.coe_nonneg (by exact_mod_cast hγ)).trans
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
    simp only [totalWeight, ← sum_pow_rev, mul_sum, sum_mul, ← sum_sub_distrib, ← sum_add_distrib]
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
  ∑ i, (γ ^ (i.rev : ℕ) / ∑ j ∈ range n, γ ^ j : ℝ≥0) • Measure.dirac i

theorem integral_recency (f : Fin n → ℝ) :
    ∫ i, f i ∂recency γ n = ∑ i, (γ : ℝ) ^ (i.rev : ℕ) / totalWeight γ n * f i := by
  rw [recency, integral_finsetSum_measure fun i _ ↦ .of_finite]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [integral_smul_nnreal_measure, integral_dirac, NNReal.smul_def, smul_eq_mul]
  simp [totalWeight]

theorem integral_recency_eq_memoryMean (e : Fin n → ℝ) :
    ∫ i, e i ∂recency γ n = memoryMean γ e := by
  rw [integral_recency, memoryMean, sum_div]
  exact sum_congr rfl fun i _ ↦ by ring

instance (n : ℕ) : IsProbabilityMeasure (recency γ (n + 1)) := by
  constructor
  rw [recency, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul,
    mul_one, ENNReal.smul_def]
  rw [← ENNReal.ofNNReal_finsetSum, ← sum_div, sum_pow_rev,
    div_self (geom_sum_pos zero_le (Nat.succ_ne_zero n)).ne']
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
  · rw [target_exemplar_apply, integral_map (by fun_prop) (by fun_prop),
      integral_recency_eq_memoryMean]
  · simp [target_average_apply]

theorem variance_target_exemplar (e : Fin (n + 1) → ℝ) :
    Var[id; target γ .exemplar e] = memorySpread γ e := by
  rw [target_exemplar_apply, variance_id_map (by fun_prop),
    variance_eq_integral (by fun_prop), integral_recency, memorySpread, sum_div]
  simp only [integral_recency_eq_memoryMean]
  exact sum_congr rfl fun i _ ↦ by ring

theorem variance_target_average (e : Fin (n + 1) → ℝ) : Var[id; target γ .average e] = 0 := by
  simp [target_average_apply]

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
      Var[id; target γ tgt e] + Var[id; ν] + bias ^ 2 := by
  have h := memLp_id_conv (memLp_target γ tgt e) hν
  rw [produce_apply, integral_map (by fun_prop) (by fun_prop)]
  simp only [show ∀ y, y + bias - memoryMean γ e = y - (memoryMean γ e - bias) from
    fun y ↦ by ring]
  rw [integral_sub_sq h, variance_id_conv (memLp_target γ tgt e) hν,
    integral_id_conv ((memLp_target γ tgt e).integrable one_le_two) (hν.integrable one_le_two),
    integral_target, hν0]
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
        · simp only [variance_target_exemplar]
          exact ((integrable_memorySpread ih).add (integrable_const _)).add (integrable_const _)
        · simp [variance_target_average]
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
          (Var[id; target γ tgt e] + Var[id; ν] + bias ^ 2) := by
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

theorem spreadGrowth_average_succ (n : ℕ) :
    spreadGrowth γ .average (n + 1) = spreadGrowth γ .average n +
      (γ * totalWeight γ (n + 1) / totalWeight γ (n + 2) - spreadGrowth γ .average n) /
        totalWeight γ (n + 2) := by
  have hS := totalWeight_pos γ (Nat.succ_ne_zero (n + 1))
  rw [spreadGrowth, totalWeight_succ (n := n + 1)] at *
  field_simp
  ring

theorem spreadGrowth_exemplar_le (n : ℕ) : spreadGrowth γ .exemplar n ≤ γ * totalWeight γ n := by
  induction n with
  | zero => simp [spreadGrowth, totalWeight]
  | succ n ih =>
    have h := ih.trans (mul_le_mul_of_nonneg_left (totalWeight_mono γ n.le_succ) γ.coe_nonneg)
    have := div_le_self (sub_nonneg.2 h)
      (one_le_pow₀ (one_le_totalWeight γ (n := n + 2) (by omega)) : 1 ≤ totalWeight γ (n + 2) ^ 2)
    rw [spreadGrowth_exemplar_succ]
    linarith

-- The target of the entrenched recursion at `n` lies below its target at `n + 1`.
private theorem ratio_lt (hγ0 : 0 < γ) (n : ℕ) :
    totalWeight γ n / totalWeight γ (n + 1) <
      totalWeight γ (n + 1) / totalWeight γ (n + 2) := by
  have hS₁ := totalWeight_pos γ (Nat.succ_ne_zero n)
  have hS₂ := totalWeight_pos γ (Nat.succ_ne_zero (n + 1))
  have h := totalWeight_strictMono hγ0 n.lt_succ_self
  have e := totalWeight_succ γ (n := n)
  rw [div_lt_div_iff₀ hS₁ hS₂, totalWeight_succ (n := n + 1)]
  linear_combination h - totalWeight γ (n + 1) * e

variable {γ} in
theorem spreadGrowth_average_le_ratio (hγ0 : 0 < γ) (n : ℕ) :
    spreadGrowth γ .average n ≤ γ * totalWeight γ n / totalWeight γ (n + 1) := by
  have h0 : (0 : ℝ) < γ := by exact_mod_cast hγ0
  induction n with
  | zero => simp [spreadGrowth, totalWeight]
  | succ n ih =>
    have hr : γ * totalWeight γ n / totalWeight γ (n + 1) ≤
        γ * totalWeight γ (n + 1) / totalWeight γ (n + 2) := by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left (ratio_lt γ hγ0 n).le h0.le
    have := div_le_self (sub_nonneg.2 (ih.trans hr)) (one_le_totalWeight γ (n := n + 2) (by omega))
    rw [spreadGrowth_average_succ]
    linarith

variable {γ} in
theorem spreadGrowth_average_le_gamma (hγ0 : 0 < γ) (n : ℕ) : spreadGrowth γ .average n ≤ γ := by
  refine (spreadGrowth_average_le_ratio hγ0 n).trans ?_
  rw [mul_div_assoc]
  exact mul_le_of_le_one_right γ.coe_nonneg
    (div_le_one_of_le₀ (totalWeight_mono γ n.le_succ) (totalWeight_nonneg γ))

variable {γ} in
theorem spreadGrowth_strictMono (hγ0 : 0 < γ) (tgt : Target) :
    StrictMono (spreadGrowth γ tgt) := by
  refine strictMono_nat_of_lt_succ fun n ↦ ?_
  have hS := totalWeight_pos γ (n := n + 2) (by omega)
  have h0 : (0 : ℝ) < γ := by exact_mod_cast hγ0
  cases tgt
  · have h := (spreadGrowth_exemplar_le γ n).trans_lt
      (mul_lt_mul_of_pos_left (totalWeight_strictMono hγ0 n.lt_succ_self) h0)
    rw [spreadGrowth_exemplar_succ]
    exact lt_add_of_pos_right _ (div_pos (sub_pos.2 h) (by positivity))
  · have h : spreadGrowth γ .average n < γ * totalWeight γ (n + 1) / totalWeight γ (n + 2) :=
      (spreadGrowth_average_le_ratio hγ0 n).trans_lt (by
        simpa only [mul_div_assoc] using mul_lt_mul_of_pos_left (ratio_lt γ hγ0 n) h0)
    rw [spreadGrowth_average_succ]
    exact lt_add_of_pos_right _ (div_pos (sub_pos.2 h) hS)

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

variable {γ} in
theorem spreadGrowth_average_lt_exemplar (hγ0 : 0 < γ) (n : ℕ) :
    spreadGrowth γ .average (n + 2) < spreadGrowth γ .exemplar (n + 2) := by
  have hA := coeff_nonneg γ (n + 1) 1
  rw [pow_one] at hA
  have hB : 0 < (γ : ℝ) * totalWeight γ (n + 1 + 1) / totalWeight γ (n + 1 + 2) ^ 2 :=
    div_pos (mul_pos (by exact_mod_cast hγ0) (totalWeight_pos γ (by omega)))
      (pow_pos (totalWeight_pos γ (by omega)) 2)
  have hle := spreadGrowth_average_le_exemplar γ (n + 1)
  have hpos := spreadGrowth_pos γ hγ0 .exemplar n
  rw [show spreadGrowth γ .average (n + 2) = _ by rw [spreadGrowth],
    show spreadGrowth γ .exemplar (n + 2) = _ by rw [spreadGrowth]]
  nlinarith [mul_le_mul_of_nonneg_left hle hA, mul_pos hB hpos]

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
theorem tendsto_spreadGrowth_exemplar (hγ0 : 0 < γ) (hγ : γ < 1) :
    Tendsto (spreadGrowth γ .exemplar) atTop (𝓝 (γ * (1 - (γ : ℝ))⁻¹)) := by
  have hL := tendsto_totalWeight hγ
  have hL0 : (1 - (γ : ℝ))⁻¹ ≠ 0 := (inv_pos.2 (sub_pos.2 (by exact_mod_cast hγ))).ne'
  refine tendsto_of_recursion (spreadGrowth_strictMono hγ0 .exemplar).monotone
    ⟨γ * (1 - (γ : ℝ))⁻¹, ?_⟩ (spreadGrowth_exemplar_succ γ)
    (((tendsto_add_atTop_iff_nat 1).2 hL).const_mul _)
    (((tendsto_add_atTop_iff_nat 2).2 hL).pow 2) (pow_ne_zero 2 hL0)
  rintro _ ⟨n, rfl⟩
  exact (spreadGrowth_exemplar_le γ n).trans
    (mul_le_mul_of_nonneg_left (totalWeight_le_inv hγ) γ.coe_nonneg)

variable {γ} in
theorem tendsto_spreadGrowth_average (hγ0 : 0 < γ) (hγ : γ < 1) :
    Tendsto (spreadGrowth γ .average) atTop (𝓝 γ) := by
  have hL := tendsto_totalWeight hγ
  have hL0 : (1 - (γ : ℝ))⁻¹ ≠ 0 := (inv_pos.2 (sub_pos.2 (by exact_mod_cast hγ))).ne'
  have ha : Tendsto (fun n ↦ (γ : ℝ) * totalWeight γ (n + 1) / totalWeight γ (n + 2)) atTop
      (𝓝 γ) := by
    have h := (((tendsto_add_atTop_iff_nat 1).2 hL).const_mul (γ : ℝ)).div
      ((tendsto_add_atTop_iff_nat 2).2 hL) hL0
    rwa [mul_div_assoc, div_self hL0, mul_one] at h
  exact tendsto_of_recursion (spreadGrowth_strictMono hγ0 .average).monotone
    ⟨γ, by rintro _ ⟨n, rfl⟩; exact spreadGrowth_average_le_gamma hγ0 n⟩
    (spreadGrowth_average_succ γ) ha ((tendsto_add_atTop_iff_nat 2).2 hL) hL0

private theorem tendsto_sum_inv_add_two :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ range n, ((k : ℝ) + 2)⁻¹) atTop atTop := by
  refine (tendsto_atTop_add_const_right atTop (-1 : ℝ) ((tendsto_add_atTop_iff_nat 1).2
    Real.tendsto_sum_range_one_div_nat_succ_atTop)).congr fun n ↦ ?_
  rw [sum_range_succ']
  simp only [Nat.cast_zero, zero_add, div_one, add_neg_cancel_right]
  exact sum_congr rfl fun k _ ↦ by push_cast; rw [one_div]; ring_nf

theorem tendsto_spreadGrowth_exemplar_one : Tendsto (spreadGrowth 1 .exemplar) atTop atTop := by
  have hrec (n : ℕ) : spreadGrowth 1 .exemplar (n + 1) = spreadGrowth 1 .exemplar n +
      ((n + 1) - spreadGrowth 1 .exemplar n) / ((n : ℝ) + 2) ^ 2 := by
    rw [spreadGrowth_exemplar_succ, totalWeight_one, totalWeight_one]
    push_cast
    ring_nf
  have hle (n : ℕ) : spreadGrowth 1 .exemplar n ≤ ((n : ℝ) + 1) / 2 := by
    induction n with
    | zero => simp [spreadGrowth]
    | succ n ih =>
      have hn : (0 : ℝ) ≤ n := n.cast_nonneg
      rw [hrec]
      push_cast
      have hd : (0 : ℝ) < ((n : ℝ) + 2) ^ 2 := by positivity
      rw [add_div' _ _ _ hd.ne', div_le_iff₀ hd]
      nlinarith [mul_nonneg (sub_nonneg.2 ih) (by nlinarith : 0 ≤ ((n : ℝ) + 2) ^ 2 - 1)]
  have hge (n : ℕ) : (∑ k ∈ range n, ((k : ℝ) + 2)⁻¹) / 4 ≤ spreadGrowth 1 .exemplar n := by
    induction n with
    | zero => simp [spreadGrowth]
    | succ n ih =>
      have hn : (0 : ℝ) ≤ n := n.cast_nonneg
      have hstep : ((n : ℝ) + 2)⁻¹ / 4 ≤
          ((n + 1) - spreadGrowth 1 .exemplar n) / ((n : ℝ) + 2) ^ 2 := by
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
theorem totalWeight_div_mem_Icc (hγ : γ ≤ 1) {r : ℕ} (hr : r ≠ 0) :
    totalWeight γ r / r ∈ Set.Icc ((γ : ℝ) ^ (r - 1)) 1 := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero hr
  refine ⟨?_, (div_le_one hr0).2 (totalWeight_le hγ)⟩
  rw [le_div_iff₀ hr0, mul_comm]
  simpa [totalWeight] using card_nsmul_le_sum (range r) (fun i ↦ (γ : ℝ) ^ i) ((γ : ℝ) ^ (r - 1))
    fun i hi ↦ pow_le_pow_of_le_one γ.coe_nonneg (by exact_mod_cast hγ)
      (Nat.le_sub_one_of_lt (mem_range.1 hi))

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
    · simp only [variance_target_exemplar,
        show ∀ V, A * V + B * (V + Var[id; ν] + bias ^ 2) = (A + B) * V + B * c from
          fun V ↦ by ring]
      rw [integral_add (hV.const_mul _) (integrable_const _), integral_const_mul, ih]
      simp only [integral_const, probReal_univ, one_smul, spreadGrowth, A, B, c]
      ring
    · simp only [variance_target_average,
        show ∀ V, A * V + B * (0 + Var[id; ν] + bias ^ 2) = A * V + B * c from fun V ↦ by ring]
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
  have hL0 : (1 - (γ : ℝ))⁻¹ ≠ 0 := (inv_pos.2 (sub_pos.2 (by exact_mod_cast hγ))).ne'
  have h := (tendsto_const_nhds (x := bias)).div
    ((tendsto_add_atTop_iff_nat 2).2 (tendsto_totalWeight hγ)) hL0
  rwa [div_inv_eq_mul] at h

/-- With the memory time of (1) fixed in clock time, a word used every `r > 1` ticks is at any
moment less advanced than a word used at every tick, though it forgets its own tokens faster. -/
theorem lenition_advances_with_frequency (hγ0 : 0 < γ) (hγ : γ ≤ 1) (hbias : bias < 0) {r n : ℕ}
    (hr : 1 < r) (hn : n ≠ 0) :
    ∫ e, memoryMean γ e ∂seqLaw (rule γ tgt ν bias seed) (r * n + 1) <
      ∫ e, memoryMean (γ ^ r) e ∂seqLaw (rule (γ ^ r) tgt ν bias seed) (n + 1) := by
  rw [integral_memoryMean hν hν0, integral_memoryMean hν hν0]
  linarith [mul_lt_mul_of_neg_left (sum_inv_totalWeight_pow_lt hγ0 hγ hr hn) hbias]

/-- Once its memory is full, a word used every `r` ticks moves per tick at the speed of a word used
at every tick times `totalWeight γ r / r`, which [stays near one until `r` nears the memory
time](##totalWeight_div_mem_Icc): frequency hardly changes the rate of the change. -/
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
  exact (spreadGrowth_strictMono hγ0 tgt).const_mul hc

-- "much as a photograph of a moving object shows a blur", §3.2
theorem lenition_blurs (hγ0 : 0 < γ) (hbias : bias ≠ 0) (n : ℕ) :
    ∫ e, memorySpread γ e ∂seqLaw (rule γ tgt ν 0 seed) (n + 2) <
      ∫ e, memorySpread γ e ∂seqLaw (rule γ tgt ν bias seed) (n + 2) := by
  rw [integral_memorySpread hν hν0, integral_memorySpread hν hν0]
  exact mul_lt_mul_of_pos_right (by simpa using sq_pos_of_ne_zero hbias)
    (spreadGrowth_pos γ hγ0 tgt n)

theorem tendsto_integral_memorySpread_exemplar (hγ0 : 0 < γ) (hγ : γ < 1) :
    Tendsto (fun n ↦ ∫ e, memorySpread γ e ∂seqLaw (rule γ .exemplar ν bias seed) (n + 1)) atTop
      (𝓝 ((Var[id; ν] + bias ^ 2) * (γ * (1 - (γ : ℝ))⁻¹))) := by
  simp only [integral_memorySpread hν hν0]
  exact (tendsto_spreadGrowth_exemplar hγ0 hγ).const_mul _

/-- Without entrenchment the expected spread is bounded exactly when memory decays, against the
claim of §3.3 that the bare model cannot fill out a category without spreading it indefinitely. -/
theorem bddAbove_integral_memorySpread_iff (hγ0 : 0 < γ) (hγ : γ ≤ 1)
    (hc : 0 < Var[id; ν] + bias ^ 2) :
    BddAbove (Set.range fun n ↦
      ∫ e, memorySpread γ e ∂seqLaw (rule γ .exemplar ν bias seed) (n + 1)) ↔ γ < 1 := by
  constructor
  · intro h
    by_contra hlt
    obtain rfl := hγ.eq_of_not_lt hlt
    simp only [integral_memorySpread hν hν0] at h
    exact not_bddAbove_of_tendsto_atTop
      (tendsto_spreadGrowth_exemplar_one.const_mul_atTop hc) h
  · intro h
    exact (tendsto_integral_memorySpread_exemplar hν hν0 hγ0 h).bddAbove_range

/-- Entrenchment narrows the category from the second production on, since averaging over the
memory removes the spread a picked exemplar would inherit (§3.3, Fig. 4). -/
theorem entrenchment_narrows (hγ0 : 0 < γ) (hc : 0 < Var[id; ν] + bias ^ 2) (n : ℕ) :
    ∫ e, memorySpread γ e ∂seqLaw (rule γ .average ν bias seed) (n + 3) <
      ∫ e, memorySpread γ e ∂seqLaw (rule γ .exemplar ν bias seed) (n + 3) := by
  rw [integral_memorySpread hν hν0, integral_memorySpread hν hν0]
  exact mul_lt_mul_of_pos_left (spreadGrowth_average_lt_exemplar hγ0 n) hc

-- §3.3
theorem integral_memorySpread_average_le (hγ0 : 0 < γ) (n : ℕ) :
    ∫ e, memorySpread γ e ∂seqLaw (rule γ .average ν bias seed) (n + 1) ≤
      (Var[id; ν] + bias ^ 2) * γ := by
  rw [integral_memorySpread hν hν0]
  exact mul_le_mul_of_nonneg_left (spreadGrowth_average_le_gamma hγ0 n)
    (add_nonneg (variance_nonneg _ _) (sq_nonneg _))

theorem tendsto_integral_memorySpread_average (hγ0 : 0 < γ) (hγ : γ < 1) :
    Tendsto (fun n ↦ ∫ e, memorySpread γ e ∂seqLaw (rule γ .average ν bias seed) (n + 1)) atTop
      (𝓝 ((Var[id; ν] + bias ^ 2) * γ)) := by
  simp only [integral_memorySpread hν hν0]
  exact (tendsto_spreadGrowth_average hγ0 hγ).const_mul _

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

-- The first erratum at the paper's noise and bias: no decay spreads without bound.
example : ¬ BddAbove (Set.range fun n ↦
    ∫ e, memorySpread 1 e ∂seqLaw (rule 1 .exemplar noise (-(1 / 100)) 1) (n + 1)) := by
  rw [bddAbove_integral_memorySpread_iff memLp_noise integral_noise one_pos le_rfl
    (by rw [variance_noise]; norm_num)]
  simp

end Noise

end Pierrehumbert2001
