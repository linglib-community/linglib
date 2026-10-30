module

public import Linglib.Core.Probability.Exchangeable
public import Linglib.Core.Probability.Kernel.Invariance
public import Mathlib.Probability.ConditionalProbability

/-!
# Maslova (2000): A dynamic approach to the verification of distributional universals

A type-shift process moves each language among the types of a typology, a language of type $T_k$
being of type $T_i$ after a small interval with probability $p(T_k \to T_i)$. Its distributional
universal is its stationary law, the one law that independently changing languages keep once they
reach it, and a law is [stationary exactly when the languages leaving each type balance those
entering it](##invariant_iff_flow). A typology [has a universal that gives every type a positive
probability exactly when its types are strongly
connected](##isIrreducible_iff_exists_isDistributionalUniversal). The universal of interdependent
typologies [sums to the universal of each](##IsDistributionalUniversal.apply_eq_sum), and of two
types [the more probable is the one the process leaves with the lower
probability](##lt_iff_of_invariant). Splitting and dying that ignore type [keep the expected
frequency of a type among the surviving languages at its ancestral
frequency](##integral_frequency_cond).

## Implementation notes

* A typology is a finite type with measurable singletons and its type-shift process a Markov
  kernel; `typeShift P` is the process with transition probabilities `P`. Strong connection is
  irreducibility with respect to the counting measure. The paper's small time interval, over which
  a language most likely keeps its type, is not imposed.
* That the shifts of a coarser typology depend on the coarse type alone is the condition
  `κ (g s) = (κS s).map g` on the coarsening `g` of a finer typology.
* The birth-and-death process enters only through the law of the numbers of descendants of the
  $N_0$ ancestral languages, which need only be exchangeable; independent lineages make it so
  (`integral_frequency_cond_pi`). Where no descendant survives, the frequency is `0 / 0 = 0`, and
  the expectation is taken given survival.

## Errata

* (A10) computes the expected frequency $N^+ / (N^+ + N^-)$ as the ratio of the expected numbers.
  The equation holds nonetheless, because the ancestral languages are exchangeable
  (`integral_frequency_cond`).
* The second term of (A11) lacks its square; (A12) is what the squared term gives.
* At $f_0 = 1/2$, (6) gives $\sigma = \sqrt{\alpha}/(2\sqrt{K})$ with $\alpha = 1 + p(D)/p(B)$,
  more than the $1/(2\sqrt{K})$ of (4) whenever $p(D) > 0$. The appendix obtains (4) as the limit
  $N_0 \to K$, in which every ancestral language leaves descendants, and the bound $1/\sqrt{K}$ of
  (5) is $2\sigma$ only in that limit.
* The paper says that a stationary distribution exists only for an ergodic system. With finitely
  many types every type-shift process has one
  (`ProbabilityTheory.Kernel.exists_isProbabilityMeasure_invariant`), and a process that never
  shifts keeps every law, so it has no distributional universal
  (`not_exists_isDistributionalUniversal_id`); what strong connection adds is uniqueness.
* Strong connection is necessary for a distributional universal that gives every type a positive
  probability, but not for a distributional universal: a process with a path from one type to
  another and none back has one, concentrated on the second type
  (`isDistributionalUniversal_absorbing`, `not_isIrreducible_absorbing`).
* The paper takes the notion of a distributional universal to imply that a shift from a preferred
  type to a dispreferred one is less probable than the reverse shift. This holds of two types and
  of any process in detailed balance (`lt_iff_of_isReversible`), but not in general: of three
  types moving around a cycle, the more probable of two can be one the process shifts to the
  other and never directly back (`cycle_counterexample`).

## TODO

* The independence of the initial type that the definition rests on: `(κ ^ n) a` tends to the
  universal for a strongly connected process that keeps each type with positive probability, and
  with it the tests that compare the distributions within genetic groupings and within areas.
* The Feller–Arley process of the appendix, (A1) to (A9) and (A11) to (A12), and with it the
  variance estimates (4) to (6), Tables 1 to 3 and Figures 1 to 3.
* The estimation of transition probabilities from genetic groupings of small time depth and from
  shifts in progress.

## References

* [maslova-2000]
-/

@[expose] public section

namespace Maslova2000

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel Finset
open scoped ENNReal

variable {T : Type*} [MeasurableSpace T] [Fintype T] [MeasurableSingletonClass T]
  {κ : Kernel T T} {π : Measure T}

/-! ### Type-shift processes and distributional universals -/

/-- The type-shift process with transition probabilities `P k i`, the probability that a language
of type `k` is of type `i` after a small time interval. -/
noncomputable def typeShift (P : T → T → ℝ) : Kernel T T :=
  Kernel.ofFunOfCountable fun k ↦ Measure.ofRealWeights (P k)

theorem typeShift_apply_singleton (P : T → T → ℝ) (k i : T) :
    typeShift P k {i} = ENNReal.ofReal (P k i) :=
  Measure.ofWeights_apply_singleton _ i

theorem typeShift_real_singleton {P : T → T → ℝ} (hP : ∀ k i, 0 ≤ P k i) (k i : T) :
    (typeShift P k).real {i} = P k i :=
  Measure.ofRealWeights_real_singleton (hP k) i

theorem isMarkovKernel_typeShift {P : T → T → ℝ} (hP : ∀ k i, 0 ≤ P k i)
    (hrow : ∀ k, ∑ i, P k i = 1) : IsMarkovKernel (typeShift P) :=
  ⟨fun k ↦ Measure.isProbabilityMeasure_ofRealWeights (hP k) (hrow k)⟩

/-- A distributional universal is the stationary law of the type-shift process, the one law that
languages changing independently keep once they reach it. -/
def IsDistributionalUniversal (κ : Kernel T T) (π : Measure T) : Prop :=
  IsProbabilityMeasure π ∧ κ.Invariant π ∧
    ∀ ν : Measure T, IsProbabilityMeasure ν → κ.Invariant ν → ν = π

/-- (1): a law is stationary exactly when, for each type, the languages leaving the type balance
the languages entering it. -/
theorem invariant_iff_flow [IsMarkovKernel κ] [IsFiniteMeasure π] :
    κ.Invariant π ↔ ∀ i, ∫⁻ k in {i}, κ k {i}ᶜ ∂π = ∫⁻ k in {i}ᶜ, κ k {i} ∂π := by
  refine ⟨fun h i ↦ h.setLIntegral_compl (measurableSet_singleton i), fun h ↦ ?_⟩
  exact Measure.ext_of_singleton fun i ↦
    (comp_apply_eq_iff_setLIntegral_compl (measurableSet_singleton i)).2 (h i)

/-- Strong connection holds exactly when the typology has a distributional universal and the
universal gives every type a positive probability. -/
theorem isIrreducible_iff_exists_isDistributionalUniversal [Nonempty T] [IsMarkovKernel κ] :
    IsIrreducible Measure.count κ ↔ ∃ π, IsDistributionalUniversal κ π ∧ ∀ i, π {i} ≠ 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨π, ⟨hπp, hπ, hu⟩, hpos⟩ ↦ ?_⟩
  · obtain ⟨π, hπp, hπ⟩ := exists_isProbabilityMeasure_invariant κ
    exact ⟨π, ⟨hπp, hπ, fun ν _ hν ↦ hν.eq_of_isIrreducible hπ⟩,
      hπ.measure_singleton_ne_zero (IsProbabilityMeasure.ne_zero π)⟩
  · exact isIrreducible_count_of_measure_singleton_ne_zero fun ν hνp hν ↦ hu ν hνp hν ▸ hpos

omit [Fintype T] in
/-- (2): when the shifts of a coarser typology `T` depend on the coarse type alone, its universal
gives each coarse type the sum of what the universal of the finer typology `S` gives to the fine
types inside it. -/
theorem IsDistributionalUniversal.apply_eq_sum [DecidableEq T] {S : Type*} [MeasurableSpace S]
    [Fintype S] [MeasurableSingletonClass S] {κS : Kernel S S} {πS : Measure S} {g : S → T}
    (hg : ∀ s, κ (g s) = (κS s).map g) (hS : IsDistributionalUniversal κS πS)
    (hT : IsDistributionalUniversal κ π) (t : T) : π {t} = ∑ s with g s = t, πS {s} := by
  have := hS.1
  have hgm : Measurable g := measurable_of_countable g
  rw [← hT.2.2 (πS.map g) inferInstance (hS.2.1.map hgm hg),
    Measure.map_apply hgm (measurableSet_singleton t), sum_measure_singleton, coe_filter]
  congr 1
  ext s
  simp

/-! ### Preferred types -/

/-- Of two types, the more probable under a stationary law is the one the process leaves with the
lower probability. -/
theorem lt_iff_of_invariant {κ : Kernel Bool Bool} [IsMarkovKernel κ] {π : Measure Bool}
    [IsProbabilityMeasure π] (hπ : κ.Invariant π)
    (h : 0 < (κ false).real {true} + (κ true).real {false}) :
    π.real {false} < π.real {true} ↔ (κ true).real {false} < (κ false).real {true} := by
  have hb := invariant_iff_forall_real_singleton.1 hπ true
  have hsum : ∀ ρ : Measure Bool, IsProbabilityMeasure ρ → ρ.real {true} + ρ.real {false} = 1 :=
    fun ρ _ ↦ by
      rw [← probReal_univ (μ := ρ), ← coe_univ, ← sum_measureReal_singleton]
      simp [Fintype.univ_bool, add_comm]
  have hπ1 := hsum π inferInstance
  have hκ1 := hsum (κ true) inferInstance
  simp only [Fintype.univ_bool, mem_singleton, Bool.true_eq_false, not_false_eq_true,
    sum_insert, sum_singleton] at hb
  set x := π.real {true}
  set y := π.real {false}
  set p := (κ false).real {true}
  set q := (κ true).real {false}
  have key : y * (p + q) = q := by
    rw [show (κ true).real {true} = 1 - q by linarith, show x = 1 - y by linarith] at hb
    linarith
  constructor
  · intro hlt
    nlinarith [mul_lt_mul_of_pos_right (show 2 * y < 1 by linarith) h]
  · intro hlt
    by_contra hge
    nlinarith [mul_le_mul_of_nonneg_right (show 1 ≤ 2 * y by linarith) h.le]

omit [Fintype T] in
-- p. 313: under detailed balance, as for any two types, the comparison holds pairwise
theorem lt_iff_of_isReversible [IsMarkovKernel κ] [IsFiniteMeasure π] (hπ : IsReversible κ π)
    {i j : T} (hi : 0 < π.real {i}) (hj : 0 < π.real {j})
    (h : 0 < (κ i).real {j} + (κ j).real {i}) :
    π.real {j} < π.real {i} ↔ (κ i).real {j} < (κ j).real {i} := by
  have h₁ := hπ (measurableSet_singleton i) (measurableSet_singleton j)
  rw [lintegral_singleton, lintegral_singleton] at h₁
  have h₂ := congrArg ENNReal.toReal h₁
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def,
    ← measureReal_def, ← measureReal_def] at h₂
  have hq₁ : 0 ≤ (κ i).real {j} := measureReal_nonneg
  have hq₂ : 0 ≤ (κ j).real {i} := measureReal_nonneg
  constructor
  · intro hlt
    by_contra! hge
    nlinarith [mul_le_mul_of_nonneg_left hge hj.le, mul_lt_mul_of_pos_left hlt
      (show 0 < (κ i).real {j} by nlinarith)]
  · intro hlt
    by_contra! hge
    nlinarith [mul_le_mul_of_nonneg_left hge hq₂, mul_lt_mul_of_pos_left hlt hi]

/-! ### Three processes -/

-- p. 314: a process that never shifts has a stationary law but no distributional universal
theorem not_exists_isDistributionalUniversal_id :
    ¬ ∃ π, IsDistributionalUniversal (Kernel.id : Kernel Bool Bool) π := by
  rintro ⟨π, -, -, h⟩
  have h₁ := (h (Measure.dirac true) inferInstance Measure.id_comp).trans
    (h (Measure.dirac false) inferInstance Measure.id_comp).symm
  simpa using congrArg (· {true}) h₁

/-- A process that shifts a language of type `true` to type `false` with probability one half and
never shifts back. -/
noncomputable def absorbing : Kernel Bool Bool :=
  typeShift fun k i ↦ bif k then 1 / 2 else bif i then 0 else 1

private theorem absorbing_nonneg (k i : Bool) :
    (0 : ℝ) ≤ bif k then 1 / 2 else bif i then 0 else 1 := by
  cases k <;> cases i <;> norm_num

instance : IsMarkovKernel absorbing :=
  isMarkovKernel_typeShift absorbing_nonneg fun k ↦ by cases k <;> norm_num [Fintype.univ_bool]

-- §2.2: a process with a path from `true` to `false` and none back has a distributional universal
theorem isDistributionalUniversal_absorbing :
    IsDistributionalUniversal absorbing (Measure.dirac false) := by
  have hfalse : absorbing false = Measure.dirac false :=
    Measure.ext_of_singleton fun i ↦ by cases i <;> simp [absorbing, typeShift_apply_singleton]
  refine ⟨inferInstance, by rw [Invariant, Measure.dirac_bind absorbing.measurable, hfalse],
    fun ν hν hinv ↦ Measure.eq_dirac_of_ae_eq (ae_iff.2 ?_)⟩
  have h := invariant_iff_forall_real_singleton.1 hinv true
  simp only [Fintype.univ_bool, mem_singleton, Bool.true_eq_false, not_false_eq_true,
    sum_insert, sum_singleton, absorbing, typeShift_real_singleton absorbing_nonneg] at h
  norm_num at h
  rw [show {x : Bool | ¬ x = false} = {true} by ext x; cases x <;> simp]
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 (by linarith)

-- §2.2: but it is not strongly connected
theorem not_isIrreducible_absorbing : ¬ IsIrreducible Measure.count absorbing := fun h ↦ by
  have := h
  exact isDistributionalUniversal_absorbing.2.1.measure_singleton_ne_zero
    (IsProbabilityMeasure.ne_zero _) true (by simp)

/-- A three-type process that moves only forward around the cycle `0 → 1 → 2 → 0`. -/
noncomputable def cycle : Kernel (Fin 3) (Fin 3) :=
  typeShift ![![1 / 2, 1 / 2, 0], ![0, 1 / 10, 9 / 10], ![1 / 10, 0, 9 / 10]]

private theorem cycle_nonneg (k i : Fin 3) :
    (0 : ℝ) ≤ ![![1 / 2, 1 / 2, 0], ![0, 1 / 10, 9 / 10], ![1 / 10, 0, 9 / 10]] k i := by
  fin_cases k <;> fin_cases i <;> norm_num

instance : IsMarkovKernel cycle :=
  isMarkovKernel_typeShift cycle_nonneg fun k ↦ by fin_cases k <;> norm_num [Fin.sum_univ_three]

private theorem cycle_isIrreducible : IsIrreducible Measure.count cycle := by
  refine isIrreducible_count_iff.2 fun a b ↦ ⟨2, ?_⟩
  set c : Fin 3 := if b = a + 2 then a + 1 else a
  have h₁ : cycle a {c} ≠ 0 := by
    fin_cases a <;> fin_cases b <;> norm_num [c, cycle, typeShift_apply_singleton]
  have h₂ : cycle c {b} ≠ 0 := by
    fin_cases a <;> fin_cases b <;> norm_num [c, cycle, typeShift_apply_singleton]
  exact pow_succ_apply_singleton_ne_zero (n := 1) (by rwa [pow_one]) h₂

-- p. 313: type 0 is more probable than type 1, though the process shifts 0 to 1 and never 1 to 0
theorem cycle_counterexample :
    IsDistributionalUniversal cycle (Measure.ofRealWeights ![9 / 59, 5 / 59, 45 / 59]) ∧
      (Measure.ofRealWeights ![9 / 59, 5 / 59, 45 / 59] : Measure (Fin 3)).real {1} <
        (Measure.ofRealWeights ![9 / 59, 5 / 59, 45 / 59] : Measure (Fin 3)).real {0} ∧
      (cycle 1).real {0} < (cycle 0).real {1} := by
  have hw (i : Fin 3) : (0 : ℝ) ≤ ![9 / 59, 5 / 59, 45 / 59] i := by fin_cases i <;> norm_num
  have : IsProbabilityMeasure (Measure.ofRealWeights ![(9 : ℝ) / 59, 5 / 59, 45 / 59]) :=
    Measure.isProbabilityMeasure_ofRealWeights hw (by norm_num [Fin.sum_univ_three])
  have hinv : cycle.Invariant (Measure.ofRealWeights ![9 / 59, 5 / 59, 45 / 59]) :=
    invariant_iff_forall_real_singleton.2 fun b ↦ by
      fin_cases b <;> norm_num [Fin.sum_univ_three, Measure.ofRealWeights_real_singleton hw,
        cycle, typeShift_real_singleton cycle_nonneg]
  have hirr := cycle_isIrreducible
  refine ⟨⟨inferInstance, hinv, fun ν _ hν ↦ hν.eq_of_isIrreducible hinv⟩, ?_, ?_⟩
  · norm_num [Measure.ofRealWeights_real_singleton hw]
  · norm_num [cycle, typeShift_real_singleton cycle_nonneg]

/-! ### Birth and death -/

/-- (A10): when languages split and die independently of their type, the expected frequency of a
type among the descendants of `N₀` ancestral languages, given that some descendant survives, is its
frequency `#A / N₀` among the ancestors. -/
theorem integral_frequency_cond {N₀ : ℕ} {μ : Measure (Fin N₀ → ℕ)} [IsProbabilityMeasure μ]
    (hμ : Exchangeable μ) (A : Finset (Fin N₀)) (hS : μ {x | ∑ i, (x i : ℝ) ≠ 0} ≠ 0) :
    ∫ x, (∑ i ∈ A, (x i : ℝ)) / ∑ i, (x i : ℝ) ∂μ[|{x | ∑ i, (x i : ℝ) ≠ 0}] = #A / N₀ := by
  have hS' : μ.real {x | ∑ i, (x i : ℝ) ≠ 0} ≠ 0 :=
    (ENNReal.toReal_ne_zero).2 ⟨hS, measure_ne_top μ _⟩
  rw [ProbabilityTheory.cond, integral_smul_measure, setIntegral_eq_integral_of_forall_compl_eq_zero
    fun x hx ↦ by simp [not_not.1 hx], hμ.integral_sum_div_sum (f := Nat.cast)
    (measurable_of_countable _) (fun _ ↦ Nat.cast_nonneg _) A, Fintype.card_fin,
    ENNReal.toReal_inv, ← measureReal_def, smul_eq_mul]
  field_simp

-- (A10) for independent lineages that each leave a descendant with positive probability
theorem integral_frequency_cond_pi {N₀ : ℕ} (hN : N₀ ≠ 0) (ν : Measure ℕ) [IsProbabilityMeasure ν]
    (hν : ν {0} ≠ 1) (A : Finset (Fin N₀)) :
    ∫ x, (∑ i ∈ A, (x i : ℝ)) / ∑ i, (x i : ℝ)
      ∂(Measure.pi fun _ : Fin N₀ ↦ ν)[|{x | ∑ i, (x i : ℝ) ≠ 0}] = #A / N₀ := by
  refine integral_frequency_cond (exchangeable_pi ν) A fun h0 ↦ hν ?_
  have hc : {x : Fin N₀ → ℕ | ∑ i, (x i : ℝ) ≠ 0}ᶜ = Set.univ.pi fun _ ↦ {0} := by
    ext x
    simp [Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ Nat.cast_nonneg (x i)]
  have h1 := prob_compl_eq_one_sub (μ := Measure.pi fun _ : Fin N₀ ↦ ν)
    (s := {x : Fin N₀ → ℕ | ∑ i, (x i : ℝ) ≠ 0}) (Set.to_countable _).measurableSet
  rw [h0, tsub_zero, hc, Measure.pi_pi, Finset.prod_const, card_univ, Fintype.card_fin] at h1
  by_contra hne
  exact ((pow_lt_one_iff hN).2 (lt_of_le_of_ne prob_le_one hne)).ne h1

end Maslova2000
