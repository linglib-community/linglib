/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.Partition.MinLabel
public import Linglib.Core.Probability.Combinatorics.PitmanYor.EPPF
public import Linglib.Core.Probability.Combinatorics.PolyaUrn
public import Linglib.Core.Probability.Exchangeable.Partition
public import Linglib.Core.Probability.Kernel.IonescuTulcea.SeqLaw
public import Mathlib.MeasureTheory.Measure.Real

/-!
# The Pitman–Yor partition

In the Chinese restaurant process with the $(α, θ)$ seating plan the first customer sits alone,
and when $n$ customers sit at $k$ tables, $n_i$ of them at table $i$, the next one joins table
$i$ with probability $(n_i - α) / (n + θ)$ and opens a new table with probability
$(θ + k α) / (n + θ)$. `pitmanYor α θ n` is the law of the partition of the first `n` customers
by table. For $0 ≤ α ≤ 1$ and $-α < θ$ it is a probability measure that
[gives each partition the probability](##ProbabilityTheory.pitmanYor_singleton) `pitmanYorEPPF`
of its block sizes, so it is [exchangeable](##ProbabilityTheory.smulInvariantMeasure_pitmanYor),
and [forgetting the last customer](##ProbabilityTheory.pitmanYor_succ_map) leaves the partition
of the customers before. At $α = 0$ the probabilities are the
[Ewens sampling formula](##ProbabilityTheory.pitmanYorEPPF_zero_left).

## Implementation notes

The seating is a sequence of table labels drawn from the prediction rule `crpRule`, each customer
labelled by the first customer at their table, so a new table opened by customer `n` is labelled
`n`. The label sequences of positive probability are the labellings of partitions by least
elements (`Finpartition.minLabel_ofFun_eq_iff`), one for each partition, which gives the law of
the partition from that of the labels. The rule for the first customer is the point mass at
label `0`, where the general formula would read $θ / θ$. The measure is defined for all real `α`
and `θ`, and the constraints are hypotheses of the theorems that need them.

## TODO

* The parameters $α < 0$, $θ = m (-α)$ for a positive integer $m$ also give a probability
  measure, on partitions with at most $m$ blocks. `crpRule` truncates a negative weight to `0`,
  so there it is not a Markov kernel at seatings with more than $m$ tables, which have
  probability zero.
* The consistent partitions are the restrictions of one exchangeable random partition of `ℕ`,
  the image of `seqTrajectory (crpRule α θ)`.

## References

* [pitman-2006]
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal Nat

namespace ProbabilityTheory

variable {α θ : ℝ} {n : ℕ}

/-! ### The Chinese restaurant -/

variable (α θ) in
/-- The `(α, θ)` seating plan on table labels, each customer labelled by the first customer at
their table. The first customer opens table `0`. When customers `0, …, n` sit at `k` tables,
label `c` used `n_c` times, customer `n + 1` opens a new table, labelled `n + 1`, with
probability `(θ + k α) / (n + 1 + θ)`, and joins the table labelled `c` with probability
`(n_c - α) / (n + 1 + θ)`. -/
noncomputable def crpRule : (n : ℕ) → Kernel (Fin n → ℕ) ℕ
  | 0 => Kernel.const _ (Measure.dirac 0)
  | n + 1 => Kernel.ofFunOfCountable fun s ↦
      ENNReal.ofReal ((θ + #(univ.image s) * α) / (n + 1 + θ)) • Measure.dirac (n + 1) +
        ∑ c ∈ univ.image s, ENNReal.ofReal ((countVec s c - α) / (n + 1 + θ)) • Measure.dirac c

variable (α θ n) in
/-- The *Pitman–Yor partition*: the law of the partition of `n` customers by table under the
`(α, θ)` seating plan. -/
noncomputable def pitmanYor : Measure (Finpartition (univ : Finset (Fin n))) :=
  (seqLaw (crpRule α θ) n).map Finpartition.ofFun

theorem crpRule_zero_apply (s : Fin 0 → ℕ) : crpRule α θ 0 s = Measure.dirac 0 := rfl

theorem crpRule_succ_apply_singleton (s : Fin (n + 1) → ℕ) (c : ℕ) :
    crpRule α θ (n + 1) s {c} =
      (if c = n + 1 then ENNReal.ofReal ((θ + #(univ.image s) * α) / (n + 1 + θ)) else 0) +
        if c ∈ univ.image s then ENNReal.ofReal ((countVec s c - α) / (n + 1 + θ)) else 0 := by
  simp only [crpRule, Kernel.ofFunOfCountable, Kernel.coe_mk, Measure.add_apply,
    Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul,
    Measure.dirac_apply' _ (measurableSet_singleton c), Set.indicator_apply,
    Set.mem_singleton_iff, Pi.one_apply, mul_ite, mul_one, mul_zero, eq_comm (a := c)]
  congr 1
  rw [Finset.sum_ite_eq']

section Constraints

variable (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (hθ : -α < θ)
include hα₀ hα₁ hθ

theorem isMarkovKernel_crpRule : ∀ n, IsMarkovKernel (crpRule α θ n)
  | 0 => by rw [crpRule]; infer_instance
  | n + 1 => by
    refine ⟨fun s ↦ ⟨?_⟩⟩
    have hn : (0 : ℝ) < n + 1 + θ := by have := (n.cast_nonneg : (0 : ℝ) ≤ n); linarith
    have hK : (1 : ℝ) ≤ #(univ.image s) := by
      exact_mod_cast card_pos.2 (univ_nonempty.image s)
    have hsum : ∑ c ∈ univ.image s, (countVec s c : ℝ) = n + 1 := by
      have := (card_eq_sum_card_image s univ).symm
      rw [card_univ, Fintype.card_fin] at this
      exact_mod_cast this
    simp only [crpRule, Kernel.ofFunOfCountable, Kernel.coe_mk, Measure.add_apply,
      Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
      mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg fun c hc ↦ div_nonneg ?_ hn.le,
      ← ENNReal.ofReal_add (div_nonneg (by nlinarith) hn.le)
        (sum_nonneg fun c hc ↦ div_nonneg ?_ hn.le), ← sum_div, ← add_div, sum_sub_distrib, hsum,
      sum_const, nsmul_eq_mul, show θ + #(univ.image s) * α + (n + 1 - #(univ.image s) * α) =
        n + 1 + θ by ring, div_self hn.ne', ENNReal.ofReal_one]
    all_goals
      have : (1 : ℝ) ≤ countVec s c := by
        exact_mod_cast card_pos.2 (by obtain ⟨i, -, rfl⟩ := mem_image.1 hc; exact ⟨i, by simp⟩)
      linarith

theorem isProbabilityMeasure_seqLaw_crpRule (n : ℕ) :
    IsProbabilityMeasure (seqLaw (crpRule α θ) n) :=
  have := isMarkovKernel_crpRule hα₀ hα₁ hθ
  isProbabilityMeasure_seqLaw n

theorem isProbabilityMeasure_pitmanYor (n : ℕ) : IsProbabilityMeasure (pitmanYor α θ n) :=
  have := isProbabilityMeasure_seqLaw_crpRule hα₀ hα₁ hθ n
  (Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable).2 inferInstance

/-- **The seating plan on labels.** A sequence of table labels has the probability
`pitmanYorEPPF` of the partition it generates if each label is the first customer at its table,
and probability `0` otherwise. -/
theorem seqLaw_crpRule_singleton : ∀ {n : ℕ} (s : Fin n → ℕ),
    seqLaw (crpRule α θ) n {s} =
      if (Finpartition.ofFun s).minLabel = s then
        ENNReal.ofReal (pitmanYorEPPF α θ (Finpartition.ofFun s).partSizes) else 0
  | 0, s => by
    have hv : (Finpartition.ofFun s).minLabel = s := funext fun i ↦ i.elim0
    have hp : (Finpartition.ofFun s).partSizes = 0 := by
      simp [Finpartition.partSizes_ofFun]
    rw [ite_eq_left hv, hp, seqLaw_zero,
      Measure.dirac_apply_of_mem (Set.mem_singleton_iff.2 (Subsingleton.elim _ _))]
    simp
  | n + 1, s => by
    have := isMarkovKernel_crpRule hα₀ hα₁ hθ
    obtain ⟨t, c, rfl⟩ : ∃ t c, s = Fin.snoc t c :=
      ⟨Fin.init s, s (Fin.last n), (Fin.snoc_init_self s).symm⟩
    rw [seqLaw_succ_singleton_snoc, seqLaw_crpRule_singleton t]
    simp only [Finpartition.minLabel_ofFun_snoc_eq_iff]
    by_cases ht : (Finpartition.ofFun t).minLabel = t
    swap
    · rw [ite_eq_right ht, zero_mul, ite_eq_right fun h ↦ ht h.1]
    rw [ite_eq_left ht]
    by_cases hc : c ∈ univ.image t ∨ c = n
    swap
    · rw [ite_eq_right fun h ↦ hc h.2]
      have hcn : c ≠ n := fun h ↦ hc (Or.inr h)
      have hci : c ∉ univ.image t := fun h ↦ hc (Or.inl h)
      cases n with
      | zero =>
        rw [crpRule_zero_apply, Measure.dirac_apply' _ (measurableSet_singleton _),
          Set.indicator_of_notMem (fun h ↦ hcn (Set.mem_singleton_iff.1 h).symm), mul_zero]
      | succ m =>
        rw [crpRule_succ_apply_singleton, ite_eq_right hcn, ite_eq_right hci, add_zero, mul_zero]
    rw [ite_eq_left ⟨ht, hc⟩]
    have hE := pitmanYorEPPF_nonneg hα₀ hα₁ hθ (Finpartition.ofFun t).partSizes
    rcases hc with hc | hc
    · obtain ⟨k, -, rfl⟩ := mem_image.1 hc
      have hlt : t k < n := (Finpartition.le_of_minLabel_ofFun_eq ht k).trans_lt k.2
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
      have hmem : #{i | t i = t k} ∈ (Finpartition.ofFun t).partSizes := by
        rw [Finpartition.partSizes_ofFun]
        exact Multiset.mem_map_of_mem _ hc
      have hpos : #{i | t i = t k} ≠ 0 := (card_pos.2 ⟨k, by simp⟩).ne'
      rw [crpRule_succ_apply_singleton, ite_eq_right hlt.ne, ite_eq_left hc, zero_add,
        ← ENNReal.ofReal_mul hE, Finpartition.partSizes_ofFun_snoc_of_mem hc,
        pitmanYorEPPF_cons_succ_erase hmem hpos, Finpartition.sum_partSizes, card_univ,
        Fintype.card_fin]
      push_cast
      rfl
    · subst c
      have hnotin : n ∉ univ.image t := fun h ↦ by
        obtain ⟨k, -, hk⟩ := mem_image.1 h
        have := Finpartition.le_of_minLabel_ofFun_eq ht k
        omega
      rw [Finpartition.partSizes_ofFun_snoc_of_notMem hnotin]
      cases n with
      | zero =>
        rw [crpRule_zero_apply, Measure.dirac_apply_of_mem (Set.mem_singleton _), mul_one]
        congr 1
        simp [Finpartition.partSizes_ofFun, pitmanYorEPPF]
      | succ m =>
        rw [crpRule_succ_apply_singleton, ite_eq_left rfl, ite_eq_right hnotin, add_zero,
          ← ENNReal.ofReal_mul hE, pitmanYorEPPF_cons_one (by simp),
          Finpartition.sum_partSizes, Finpartition.card_partSizes_ofFun, card_univ,
          Fintype.card_fin]
        push_cast
        rfl

/-- **Pitman's Theorem 3.2**: the Pitman–Yor partition gives each partition of `Fin n` the
probability `pitmanYorEPPF` of its block sizes ([pitman-2006] (3.6)). -/
theorem pitmanYor_singleton (P : Finpartition (univ : Finset (Fin n))) :
    pitmanYor α θ n {P} = ENNReal.ofReal (pitmanYorEPPF α θ P.partSizes) := by
  have hm : Finpartition.ofFun P.minLabel = P := Finpartition.ofFun_minLabel P
  have hnull : seqLaw (crpRule α θ) n (Finpartition.ofFun ⁻¹' {P} \ {P.minLabel}) = 0 := by
    rw [← Set.biUnion_of_singleton (Finpartition.ofFun ⁻¹' {P} \ {P.minLabel}),
      measure_biUnion_null_iff (Set.to_countable _)]
    rintro s ⟨hs, hne⟩
    rw [seqLaw_crpRule_singleton hα₀ hα₁ hθ]
    refine ite_eq_right fun hv ↦ hne ?_
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hs
    rw [Set.mem_singleton_iff, ← hv, hs]
  have hmem : P.minLabel ∈ Finpartition.ofFun ⁻¹' {P} := hm
  have hae : Finpartition.ofFun ⁻¹' {P} =ᵐ[seqLaw (crpRule α θ) n] {P.minLabel} :=
    ae_eq_set.2 ⟨hnull, by rw [Set.sdiff_eq_empty.2 (Set.singleton_subset_iff.2 hmem),
      measure_empty]⟩
  rw [pitmanYor, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton P),
    measure_congr hae, seqLaw_crpRule_singleton hα₀ hα₁ hθ, hm, ite_eq_left rfl]

/-- **Pitman's Theorem 3.2**, real form. -/
theorem pitmanYor_real_singleton (P : Finpartition (univ : Finset (Fin n))) :
    (pitmanYor α θ n).real {P} = pitmanYorEPPF α θ P.partSizes := by
  rw [measureReal_def, pitmanYor_singleton hα₀ hα₁ hθ,
    ENNReal.toReal_ofReal (pitmanYorEPPF_nonneg hα₀ hα₁ hθ _)]

/-- The Pitman–Yor partition is exchangeable: relabelling the customers by a permutation does
not change its law ([pitman-2006] Theorem 3.2). -/
theorem smulInvariantMeasure_pitmanYor (n : ℕ) :
    SMulInvariantMeasure (Equiv.Perm (Fin n)) (Finpartition (univ : Finset (Fin n)))
      (pitmanYor α θ n) :=
  smulInvariantMeasure_of_measure_singleton fun σ P ↦ by
    rw [pitmanYor_singleton hα₀ hα₁ hθ, pitmanYor_singleton hα₀ hα₁ hθ,
      Finpartition.partSizes_smul]

/-- The Pitman–Yor partitions are consistent: forgetting the last customer leaves the Pitman–Yor
partition of the customers before ([pitman-2006] Theorem 3.2). -/
theorem pitmanYor_succ_map (n : ℕ) :
    (pitmanYor α θ (n + 1)).map (fun P ↦ Finpartition.ofFun (P.part ∘ Fin.castSucc)) =
      pitmanYor α θ n := by
  have := isMarkovKernel_crpRule hα₀ hα₁ hθ
  have h : (fun P : Finpartition (univ : Finset (Fin (n + 1))) ↦
      Finpartition.ofFun (P.part ∘ Fin.castSucc)) ∘ Finpartition.ofFun =
        (Finpartition.ofFun : (Fin n → ℕ) → _) ∘ Fin.init :=
    funext fun s ↦ Finpartition.ofFun_congr fun _ _ ↦ Finpartition.part_ofFun_eq_part_ofFun_iff
  rw [pitmanYor, pitmanYor, Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    h, ← Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    seqLaw_succ_map_init]

end Constraints

end ProbabilityTheory
