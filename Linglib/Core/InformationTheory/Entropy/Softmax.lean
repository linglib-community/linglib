/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.InformationTheory.ChannelCapacity

/-!
# Conditional entropy and the softmax kernel

Let `g : α → β → ℝ` be a score on finite types, `σ` the softmax kernel of `g`, and `ν` a
distribution of the inputs. For a Markov kernel `q`, write `H(q)` for the conditional entropy of
the output given the input under `ν ⊗ₘ q`. Averaging the Gibbs identity of each row
[gives](##InformationTheory.sum_toReal_klDiv_softmax_add_condEntropy)
`∑ a, ν a * KL(q a ‖ σ a) + H(q) = ∑ a, ν a * log ∑ b, exp (g a b) - ∫ g ∂(ν ⊗ₘ q)`.
The log-likelihood of a sample `p` of pairs under `σ`
[is](##InformationTheory.integral_log_softmax_real_singleton) the expected score minus the same
average log-normalizer.

Suppose `g` has the same expected value under `ν ⊗ₘ q` as under `ν ⊗ₘ σ`. Then `H(q)` [falls
short](##InformationTheory.condEntropy_add_sum_toReal_klDiv_softmax) of `H(σ)` by the average
divergence of the rows of `q` from those of `σ`. So `σ` [has the greatest conditional
entropy](##InformationTheory.isGreatest_condEntropy_softmax) among such kernels, and a kernel with
that entropy [agrees with `σ`](##InformationTheory.eq_softmax_of_condEntropy_eq) at every input of
positive mass.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

namespace InformationTheory

variable {α β : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype β]
  [MeasurableSpace β] [MeasurableSingletonClass β] (g : α → β → ℝ) (ν : Measure α)
  [IsProbabilityMeasure ν]

instance [Nonempty β] : IsMarkovKernel (Kernel.softmax fun a b ↦ (g a b : EReal)) :=
  Kernel.isMarkovKernel_softmax (fun _ ↦ ⟨Classical.arbitrary β, EReal.coe_ne_bot _⟩)
    fun _ _ ↦ EReal.coe_ne_top _

/-- The expected log-probability, under the softmax kernel, of the outputs of pairs drawn from `p`
is the expected score minus the average log-normalizer. -/
theorem integral_log_softmax_real_singleton (p : Measure (α × β)) [IsProbabilityMeasure p] :
    ∫ z, log ((Kernel.softmax (fun a b ↦ (g a b : EReal)) z.1).real {z.2}) ∂p =
      ∫ z, g z.1 z.2 ∂p - ∑ a, p.fst.real {a} * log (∑ b, exp (g a b)) := by
  have : Nonempty β := (nonempty_of_isProbabilityMeasure p).map Prod.snd
  simp_rw [Kernel.softmax_coe_real_singleton, log_softmax]
  rw [integral_sub .of_finite .of_finite]
  congr 1
  simp only [integral_fintype (μ := p) .of_finite, Fintype.sum_prod_type, smul_eq_mul,
    Measure.fst_real_singleton_eq_sum, sum_mul]

/-- The average divergence of the rows of `q` from the rows of the softmax kernel, plus the
conditional entropy of `q`, is the average log-normalizer minus the expected score. -/
theorem sum_toReal_klDiv_softmax_add_condEntropy (q : Kernel α β) [IsMarkovKernel q] :
    ∑ a, ν.real {a} * (klDiv (q a) (Kernel.softmax (fun a b ↦ (g a b : EReal)) a)).toReal +
        H[Prod.snd | Prod.fst ; ν ⊗ₘ q] =
      ∑ a, ν.real {a} * log (∑ b, exp (g a b)) - ∫ z, g z.1 z.2 ∂(ν ⊗ₘ q) := by
  rw [condEntropy_snd_fst_compProd q ν, Measure.integral_compProd_eq_sum, ← sum_add_distrib,
    ← sum_sub_distrib]
  refine sum_congr rfl fun a _ ↦ ?_
  have := nonempty_of_isProbabilityMeasure (q a)
  rw [Kernel.softmax_coe_eq_count_tilted, ← mul_add, toReal_klDiv_count_tilted_add_measureEntropy,
    smul_eq_mul, mul_sub]

variable [Nonempty β]

/-- The conditional entropy of the softmax kernel is the average log-normalizer minus the expected
score. -/
theorem condEntropy_softmax :
    H[Prod.snd | Prod.fst ; ν ⊗ₘ Kernel.softmax fun a b ↦ (g a b : EReal)] =
      ∑ a, ν.real {a} * log (∑ b, exp (g a b)) -
        ∫ z, g z.1 z.2 ∂(ν ⊗ₘ Kernel.softmax fun a b ↦ (g a b : EReal)) := by
  simpa using
    sum_toReal_klDiv_softmax_add_condEntropy g ν (Kernel.softmax fun a b ↦ (g a b : EReal))

variable {g ν} {q : Kernel α β} [IsMarkovKernel q]

/-- If the score has the same expected value under `ν ⊗ₘ q` as under `ν ⊗ₘ σ`, then the
conditional entropy of `q` falls short of that of `σ` by the average divergence of its rows from
those of `σ`. -/
theorem condEntropy_add_sum_toReal_klDiv_softmax
    (h : ∫ z, g z.1 z.2 ∂(ν ⊗ₘ q) =
      ∫ z, g z.1 z.2 ∂(ν ⊗ₘ Kernel.softmax fun a b ↦ (g a b : EReal))) :
    H[Prod.snd | Prod.fst ; ν ⊗ₘ q] +
        ∑ a, ν.real {a} * (klDiv (q a) (Kernel.softmax (fun a b ↦ (g a b : EReal)) a)).toReal =
      H[Prod.snd | Prod.fst ; ν ⊗ₘ Kernel.softmax fun a b ↦ (g a b : EReal)] := by
  linarith [sum_toReal_klDiv_softmax_add_condEntropy g ν q, condEntropy_softmax g ν]

/-- If the score has the same expected value under `ν ⊗ₘ q` as under `ν ⊗ₘ σ`, then `q` has at
most the conditional entropy of `σ`. -/
theorem condEntropy_le_condEntropy_softmax
    (h : ∫ z, g z.1 z.2 ∂(ν ⊗ₘ q) =
      ∫ z, g z.1 z.2 ∂(ν ⊗ₘ Kernel.softmax fun a b ↦ (g a b : EReal))) :
    H[Prod.snd | Prod.fst ; ν ⊗ₘ q] ≤
      H[Prod.snd | Prod.fst ; ν ⊗ₘ Kernel.softmax fun a b ↦ (g a b : EReal)] := by
  rw [← condEntropy_add_sum_toReal_klDiv_softmax h]
  exact le_add_of_nonneg_right <| sum_nonneg fun a _ ↦
    mul_nonneg measureReal_nonneg ENNReal.toReal_nonneg

/-- If the score has the same expected value under `ν ⊗ₘ q` as under `ν ⊗ₘ σ` and `q` has the
conditional entropy of `σ`, then `q` agrees with `σ` at every input of positive mass. -/
theorem eq_softmax_of_condEntropy_eq
    (h : ∫ z, g z.1 z.2 ∂(ν ⊗ₘ q) =
      ∫ z, g z.1 z.2 ∂(ν ⊗ₘ Kernel.softmax fun a b ↦ (g a b : EReal)))
    (hH : H[Prod.snd | Prod.fst ; ν ⊗ₘ q] =
      H[Prod.snd | Prod.fst ; ν ⊗ₘ Kernel.softmax fun a b ↦ (g a b : EReal)])
    {a : α} (ha : ν {a} ≠ 0) : q a = Kernel.softmax (fun a b ↦ (g a b : EReal)) a := by
  have hkl := condEntropy_add_sum_toReal_klDiv_softmax h
  rw [hH, add_eq_left, sum_eq_zero_iff_of_nonneg fun a _ ↦
    mul_nonneg measureReal_nonneg ENNReal.toReal_nonneg] at hkl
  have ha' := (mul_eq_zero.1 (hkl a (mem_univ a))).resolve_left
    ((measureReal_ne_zero_iff (measure_ne_top _ _)).2 ha)
  rw [Kernel.softmax_coe_eq_count_tilted] at ha' ⊢
  exact klDiv_eq_zero_iff.1 (((ENNReal.toReal_eq_zero_iff _).1 ha').resolve_right
    (klDiv_ne_top (absolutelyContinuous_count_tilted (q a) _) .of_finite))

variable (g ν) in
/-- **Maximum conditional entropy**: among the Markov kernels `q` under which the score has the
same expected value as under the softmax kernel, the softmax kernel has the greatest conditional
entropy. -/
theorem isGreatest_condEntropy_softmax :
    IsGreatest ((fun q : Kernel α β ↦ H[Prod.snd | Prod.fst ; ν ⊗ₘ q]) ''
      {q | IsMarkovKernel q ∧ ∫ z, g z.1 z.2 ∂(ν ⊗ₘ q) =
        ∫ z, g z.1 z.2 ∂(ν ⊗ₘ Kernel.softmax fun a b ↦ (g a b : EReal))})
      (H[Prod.snd | Prod.fst ; ν ⊗ₘ Kernel.softmax fun a b ↦ (g a b : EReal)]) :=
  ⟨⟨_, ⟨inferInstance, rfl⟩, rfl⟩, by
    rintro _ ⟨q, ⟨hq, h⟩, rfl⟩
    exact condEntropy_le_condEntropy_softmax h⟩

end InformationTheory
