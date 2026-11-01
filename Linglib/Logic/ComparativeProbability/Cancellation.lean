module

public import Linglib.Logic.ComparativeProbability.Representability
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fin.VecNotation

/-!
# Scott's cancellation condition

This file defines Scott's cancellation condition. Two families of events `x₀, …, xₙ` and
`y₀, …, yₙ` are *balanced* when every state lies in as many `xᵢ` as `yᵢ`, that is, when the
indicator functions of the two families have the same sum. Cancellation says that when the
families are balanced and `xᵢ ≿ yᵢ` for every `i > 0`, then `y₀ ≿ x₀`. The order a finite measure
induces satisfies it, since a balanced pair of families has equal total measure on its two sides,
and on a nontrivial total relation that puts every set above `∅` it gives de Finetti's axioms.
Together these conditions characterize representability (`Scott.lean`).

## Main definitions

* `Cancellation`: Scott's cancellation condition.

## Main statements

* `MeasureTheory.Measure.cancellation`, `Representable.cancellation`: soundness.
* `MeasureTheory.Measure.not_asymmRel_of_balanced`: a balanced family of comparisons is never
  satisfied with one strict.
* `Cancellation.isQualitativeProbability`: cancellation gives de Finetti's axioms.

## References

* [scott-1964]
* [kraft-pratt-seidenberg-1959]
-/

@[expose] public section

namespace ComparativeProbability

variable {W : Type*}

/-- **Scott's cancellation condition** (4_B): whenever every state lies in as many of
    `x₀, …, xₙ` as of `y₀, …, yₙ`, and `xᵢ ≿ yᵢ` for every `i > 0`, then `y₀ ≿ x₀`
    ([scott-1964], p. 246). -/
def Cancellation (r : Set W → Set W → Prop) : Prop :=
  ∀ (n : ℕ) (x y : Fin (n + 1) → Set W),
    (∀ s, ∑ i, (x i).indicator 1 s = ∑ i, (y i).indicator (1 : W → ℕ) s) →
      (∀ i : Fin n, r (x i.succ) (y i.succ)) → r (y 0) (x 0)

/-! ### De Finetti's axioms from cancellation -/

/-- Cancellation gives de Finetti's axioms to a nontrivial total relation that puts every set at
    least as high as `∅`. These are Scott's conditions; [scott-1964] (p. 247) derives additivity
    from totality and cancellation. -/
theorem Cancellation.isQualitativeProbability {r : Set W → Set W → Prop} [IsNontrivial r]
    (hnn : ∀ A, r A ∅) [Std.Total r] (h : Cancellation r) : IsQualitativeProbability r where
  trans A B C hab hbc := h 2 ![C, A, B] ![A, B, C]
    (fun s ↦ by simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]; simp; omega)
    (fun i ↦ by fin_cases i; exacts [hab, hbc])
  total := Std.Total.total
  rel_bot' := hnn
  qadd A B :=
    ⟨fun hab ↦ h 1 ![B \ A, A] ![A \ B, B] (fun s ↦ by
        by_cases hA : s ∈ A <;> by_cases hB : s ∈ B <;> simp [Fin.sum_univ_succ, hA, hB])
        (fun i ↦ by fin_cases i; exact hab),
      fun hd ↦ h 1 ![B, A \ B] ![A, B \ A] (fun s ↦ by
        by_cases hA : s ∈ A <;> by_cases hB : s ∈ B <;> simp [Fin.sum_univ_succ, hA, hB])
        (fun i ↦ by fin_cases i; exact hd)⟩
  bot_not_ge_top := IsNontrivial.bot_not_ge_top

/-! ### Measures satisfy cancellation -/

section

open MeasureTheory

variable [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W] (μ : Measure W)
  [IsFiniteMeasure μ]

/-- Balanced families of events have equal total measure. -/
private lemma sum_measureReal_eq_of_balanced {ι : Type*} [Fintype ι] {A B : ι → Set W}
    (hbal : ∀ s, ∑ i, (A i).indicator 1 s = ∑ i, (B i).indicator (1 : W → ℕ) s) :
    ∑ i, μ.real (A i) = ∑ i, μ.real (B i) := by
  classical
  have key (C : ι → Set W) :
      ∑ i, μ.real (C i) = ∑ s, ((∑ i, (C i).indicator (1 : W → ℕ) s : ℕ) : ℝ) * μ.real {s} := by
    simp only [Nat.cast_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    conv_lhs => rw [show C i = ↑(Finset.univ.filter (· ∈ C i)) by ext; simp]
    rw [← sum_measureReal_singleton, Finset.sum_filter]
    exact Finset.sum_congr rfl fun s _ ↦ by by_cases hs : s ∈ C i <;> simp [hs]
  rw [key, key]
  exact Finset.sum_congr rfl fun s _ ↦ by rw [hbal s]

/-- The order a finite measure induces satisfies cancellation, since a balanced pair of families
    has equal total measure on its two sides. -/
theorem _root_.MeasureTheory.Measure.cancellation : Cancellation (inducedGe μ) := by
  intro n x y hbal hprem
  have hsum := sum_measureReal_eq_of_balanced μ hbal
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hsum
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ μ.inducedGe_iff_real.mp (hprem i)
  rw [μ.inducedGe_iff_real]
  linarith

/-- In the order a finite measure induces, the comparisons `A i ≿ B i` of a balanced family, every
    state lying in as many `A i` as `B i`, cannot all hold with one strict. -/
theorem _root_.MeasureTheory.Measure.not_asymmRel_of_balanced {ι : Type*} [Fintype ι]
    {A B : ι → Set W} (hbal : ∀ s, ∑ i, (A i).indicator 1 s = ∑ i, (B i).indicator (1 : W → ℕ) s)
    (hle : ∀ i, inducedGe μ (A i) (B i)) (i : ι) : ¬AsymmRel (inducedGe μ) (A i) (B i) :=
  fun h ↦ (Finset.sum_lt_sum (fun j _ ↦ μ.inducedGe_iff_real.mp (hle j))
    ⟨i, Finset.mem_univ _, μ.strict_inducedGe_iff_real.mp h⟩).ne'
    (sum_measureReal_eq_of_balanced μ hbal)

end

/-- A representable relation satisfies cancellation (the soundness half of Scott's theorem). -/
theorem Representable.cancellation [Fintype W] [MeasurableSpace W]
    [DiscreteMeasurableSpace W] {r : Set W → Set W → Prop} (h : Representable r) :
    Cancellation r := by
  obtain ⟨μ, _, rfl⟩ := h
  exact μ.cancellation

end ComparativeProbability
