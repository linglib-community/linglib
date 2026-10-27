module

public import Linglib.Core.Probability.Decision.Admissible
public import Linglib.Logic.ComparativeProbability.Completeness
public import Linglib.Core.MeasureTheory.Measure.Dirac
public import Linglib.Core.MeasureTheory.Measure.Real
public import Linglib.Core.Probability.UniformOn
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp

/-!
# Icard (2016): Pragmatic considerations on comparative probability

Icard asks what is wrong with comparative probability judgments that no probability measure
represents, and answers with a Money Pump without its diachronic step. A subject who prefers
gambles on the events judged likelier, would pay for that preference, and agglomerates the
preferences faces a canonical decision problem against nature, in which the acts gambling on
the likelier side of every strict comparison cost `c`. Theorem 1 says the uniform mixture `Q★`
of those acts avoids strict dominance for some cost iff the judgments are representable
(`representable_iff_exists_not_dominated`), through the Main Lemma (`represents_iff_maximizes`)
and Pearce's lemma (`neverBest_iff_strictlyDominated`).

A measure represents the judgments when the order it induces agrees with them (`Agree`), so each
of the paper's examples fails an axiom of comparative probability. The explorer's cyclic
judgments fail transitivity, Ellsberg's fail de Finetti's quasi-additivity, and the World Cup
judgments of Kraft, Pratt and Seidenberg, which Holliday and Icard also use, satisfy every
de Finetti axiom but are balanced, a failure of Scott's cancellation. When every pair is
judged, representability is the comparative-probability substrate's, and Theorem 1 with Scott's
theorem makes the dominance criterion cancellation (`cancellation_iff_exists_not_dominated`).

## Implementation notes

* Judgments are a finite family of compared pairs with a `Finset` of strict indices, the
  paper's `ℰ ⊆ ℘(Ω) × ℘(Ω)` with `X` and `Y`; the family may repeat a pair, and `X ≠ ∅` is a
  hypothesis where the paper assumes it. A pure act picks a side of each pair, so the paper's
  `Σ` is `ι → Bool`.
* Mixed acts and beliefs are probability measures. A mixed act's payoff and its expected
  utility are integrals against them, the latter the appendix's `𝔼U(Q) = ∑_σ Q(σ) 𝔼U(σ)`, and
  `Q★` is the uniform measure on the preferred acts.
* In the refutation direction of the Main Lemma the better mixed act is the pushforward of
  `Q★` along a change of one coordinate rather than the appendix's mixtures `Q★*`.
* Raiffa's options are read through the paper's weights as probabilities that a choice becomes
  effective (p. 356): with the coin's weights the preferred act pays `50 − c` in every state.

## TODO

* The appendix's mixtures `Q★*` for the two cases of the Main Lemma, with the expected-utility
  differences it displays (p. 369).
* Note 25's variant for almost representability, without the cost.

## References

* [icard-2016]
* [pearce-1984]
* [davidson-mckinsey-suppes-1955]
* [ellsberg-1961]
* [raiffa-1961]
* [kraft-pratt-seidenberg-1959]
* [scott-1964]
* [holliday-icard-2013]
-/

@[expose] public section

namespace Icard2016

open ComparativeProbability MeasureTheory ProbabilityTheory
open scoped Matrix

variable {Ω : Type*} [Fintype Ω]

/-! ### Decision problems against nature -/

section Game

variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

variable (U : A → Ω → ℝ)

omit [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype A] in
@[simp] theorem mixedPayoff_dirac (a : A) (ω : Ω) :
    mixedPayoff U (Measure.dirac a) ω = U a ω := by
  simp [mixedPayoff]

omit [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem mixedPayoff_uniformOn [DecidableEq A] (s : Finset A) (ω : Ω) :
    mixedPayoff U (uniformOn ↑s) ω = (∑ a ∈ s, U a ω) / s.card := by
  simp only [mixedPayoff_eq_sum, measureReal_def, uniformOn_finset_apply_singleton,
    apply_ite ENNReal.toReal, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_zero,
    ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_div]
  exact Finset.sum_congr rfl fun a _ ↦ by ring

theorem expectedPayoff_eq_sum_sum (P : Measure Ω) [IsFiniteMeasure P] (μ : Measure A)
    [IsFiniteMeasure μ] : expectedPayoff U P μ = ∑ a, μ.real {a} * ∑ ω, P.real {ω} * U a ω := by
  simp only [expectedPayoff_eq_sum, mixedPayoff_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun ω _ ↦ by ring

/-- In a finite decision problem against nature, a mixed act is a best response to no belief iff it
is strictly dominated (Lemma 2, p. 361; [pearce-1984]'s Lemma 3). -/
theorem neverBest_iff_strictlyDominated (σ : Measure A) [IsProbabilityMeasure σ] :
    (∀ P : Measure Ω, IsProbabilityMeasure P →
        ∃ ν : Measure A, IsProbabilityMeasure ν ∧ expectedPayoff U P σ < expectedPayoff U P ν) ↔
      IsStrictlyPayoffDominated U σ := by
  rw [← not_iff_not, ← exists_maximizesPayoff_iff_not_isStrictlyPayoffDominated]
  simp [MaximizesPayoff]

end Game

/-! ### Judgments and the canonical decision problem -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A subject's comparative judgments judge, for each compared pair `(left i, right i)` of
events, `left i` strictly more likely when `i ∈ strict` and the two equally likely
otherwise. -/
structure Judgments (Ω ι : Type*) where
  /-- The event on the left of comparison `i`. -/
  left : ι → Set Ω
  /-- The event on the right of comparison `i`. -/
  right : ι → Set Ω
  /-- The comparisons judged strict, the paper's `X`. -/
  strict : Finset ι

/-- A pure act picks, for each compared pair, the side it gambles on, `true` for `left`. -/
abbrev Act (ι : Type*) := ι → Bool

/-- The stakes of the canonical decision problem are a positive weight and a pair of utilities,
good above bad, for each comparison. -/
structure Stakes (ι : Type*) where
  /-- The weight of comparison `i`. -/
  weight : ι → ℝ
  /-- The utility of the good outcome of comparison `i`. -/
  good : ι → ℝ
  /-- The utility of the bad outcome of comparison `i`. -/
  bad : ι → ℝ
  weight_pos : ∀ i, 0 < weight i
  bad_lt_good : ∀ i, bad i < good i

/-- `Stakes.const w g b` gives every comparison the weight `w` and the utilities `g` above `b`. -/
def Stakes.const (w g b : ℝ) (hw : 0 < w) (hgb : b < g) : Stakes ι :=
  ⟨fun _ ↦ w, fun _ ↦ g, fun _ ↦ b, fun _ ↦ hw, fun _ ↦ hgb⟩

namespace Judgments

variable (J : Judgments Ω ι)

omit [Fintype Ω] [Fintype ι] [DecidableEq ι] in
/-- The event on side `t` of comparison `i`. -/
def side (i : ι) : Bool → Set Ω
  | true => J.left i
  | false => J.right i

omit [Fintype Ω] [Fintype ι] [DecidableEq ι] in
/-- The acts the subject prefers, the paper's `Σ★`, are those gambling on the left of every
strict comparison. -/
def Preferred (φ : Act ι) : Prop := ∀ i ∈ J.strict, φ i = true

omit [Fintype Ω] [Fintype ι] [DecidableEq ι] in
instance : DecidablePred J.Preferred := fun _ ↦ Finset.decidableDforallFinset

omit [Fintype Ω] [Fintype ι] [DecidableEq ι] in
theorem preferred_const_true : J.Preferred fun _ ↦ true := fun _ _ ↦ rfl

omit [Fintype Ω] [Fintype ι] [DecidableEq ι] in
theorem not_preferred_const_false (hX : J.strict.Nonempty) : ¬J.Preferred fun _ ↦ false :=
  fun h ↦ let ⟨i, hi⟩ := hX; Bool.false_ne_true (h i hi)

omit [Fintype Ω] [DecidableEq ι] in
open scoped Classical in
/-- The preutility of act `φ` in state `ω` is the weighted payoff of its gambles. -/
noncomputable def preutility (s : Stakes ι) (φ : Act ι) (ω : Ω) : ℝ :=
  ∑ i, s.weight i * if ω ∈ J.side i (φ i) then s.good i else s.bad i

omit [Fintype Ω] [DecidableEq ι] in
/-- The canonical decision problem `D_{w,c}` charges the preferred acts the cost `c`. -/
noncomputable def utility (s : Stakes ι) (c : ℝ) (φ : Act ι) (ω : Ω) : ℝ :=
  J.preutility s φ ω - if J.Preferred φ then c else 0

omit [Fintype Ω] [DecidableEq ι] in
/-- The number of preferred acts. -/
def preferredCard : ℕ := (Finset.univ.filter J.Preferred).card

omit [Fintype Ω] in
theorem preferredCard_pos : 0 < J.preferredCard :=
  Finset.card_pos.2 ⟨fun _ ↦ true, Finset.mem_filter.2 ⟨Finset.mem_univ _, J.preferred_const_true⟩⟩

omit [Fintype Ω] [DecidableEq ι] in
/-- The uniform mixture `Q★` over the preferred acts. -/
noncomputable def uniformPreferred : Measure (Act ι) :=
  uniformOn ↑(Finset.univ.filter J.Preferred)

omit [Fintype Ω] [DecidableEq ι] in
instance : IsProbabilityMeasure J.uniformPreferred :=
  isProbabilityMeasure_uniformOn (Finset.finite_toSet _)
    ⟨fun _ ↦ true, by simpa using J.preferred_const_true⟩

omit [Fintype Ω] in
theorem uniformPreferred_real_singleton (φ : Act ι) :
    J.uniformPreferred.real {φ} = if J.Preferred φ then 1 / (J.preferredCard : ℝ) else 0 := by
  rw [measureReal_def, uniformPreferred, uniformOn_finset_apply_singleton]
  by_cases h : J.Preferred φ <;> simp [h, preferredCard]

omit [Fintype Ω] in
theorem uniformPreferred_eq_dirac_of_strict_eq_univ (h : J.strict = Finset.univ) :
    J.uniformPreferred = Measure.dirac fun _ ↦ true := by
  have hfilter : Finset.univ.filter J.Preferred = {fun _ ↦ true} := by
    ext φ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Preferred, h]
    exact ⟨fun hφ ↦ funext fun i ↦ by simpa using hφ i, fun hφ i ↦ by simp [hφ]⟩
  classical
  ext t ht
  rw [uniformPreferred, hfilter, Finset.coe_singleton, uniformOn_singleton,
    Measure.dirac_apply' _ ht, Set.indicator_apply]
  rfl

omit [Fintype Ω] [Fintype ι] [DecidableEq ι] in
/-- A relation `r` on events **agrees** with the judgments, the paper's word for a measure
(p. 368), when it makes each strict comparison strict and each indifference hold both ways. -/
def Agree (r : Set Ω → Set Ω → Prop) : Prop :=
  ∀ i, (i ∈ J.strict → AsymmRel r (J.left i) (J.right i)) ∧
    (i ∉ J.strict → r (J.left i) (J.right i) ∧ r (J.right i) (J.left i))

variable [MeasurableSpace Ω]

omit [Fintype Ω] [Fintype ι] [DecidableEq ι] in
/-- `P` represents the judgments (p. 359), `P(E) > P(F)` on strict comparisons and
`P(E) = P(F)` on indifferences, when the order it induces agrees with them. -/
def Represents (P : Measure Ω) : Prop := J.Agree P.inducedGe

omit [Fintype Ω] [Fintype ι] [DecidableEq ι] in
/-- The judgments are probabilistically representable. -/
def Representable : Prop := ∃ P : Measure Ω, IsProbabilityMeasure P ∧ J.Represents P

omit [Fintype Ω] [Fintype ι] [DecidableEq ι] in
theorem Agree.representable {J : Judgments Ω ι} {r : Set Ω → Set Ω → Prop} (h : J.Agree r)
    (hr : ComparativeProbability.Representable r) : J.Representable := by
  obtain ⟨μ, hμ, hm⟩ := hr
  obtain rfl : r = μ.inducedGe := funext₂ fun A B ↦ propext (hm A B)
  exact ⟨μ, hμ, h⟩

/-! ### The Main Lemma -/

section MainLemma

variable [MeasurableSingletonClass Ω] (s : Stakes ι) (P : Measure Ω)

omit [Fintype Ω] [MeasurableSingletonClass Ω] [Fintype ι] [DecidableEq ι] in
/-- The `P`-expected payoff of the unit gamble on side `t` of comparison `i`, the paper's
`b_{E_i}` and `b_{F_i}`. -/
noncomputable def sideValue (i : ι) (t : Bool) : ℝ :=
  P.real (J.side i t) * s.good i + (1 - P.real (J.side i t)) * s.bad i

omit [Fintype Ω] [MeasurableSingletonClass Ω] [Fintype ι] [DecidableEq ι] in
theorem sideValue_true_sub_false (i : ι) :
    J.sideValue s P i true - J.sideValue s P i false =
      (P.real (J.left i) - P.real (J.right i)) * (s.good i - s.bad i) := by
  simp only [sideValue, side]; ring

variable [IsProbabilityMeasure P]

omit [Fintype ι] [DecidableEq ι] in
open scoped Classical in
private theorem sum_mu_ite (A : Set Ω) (a b : ℝ) :
    ∑ ω, P.real {ω} * (if ω ∈ A then a else b) = P.real A * a + (1 - P.real A) * b := by
  classical
  have h1 : ∑ ω, P.real {ω} = 1 := sum_measureReal_singleton_eq_one P
  have h2 : ∑ ω, (if ω ∈ A then P.real {ω} else 0) = P.real A := by
    rw [← Finset.sum_filter, sum_measureReal_singleton]
    congr 1
    ext ω; simp
  calc ∑ ω, P.real {ω} * (if ω ∈ A then a else b)
      = ∑ ω, ((if ω ∈ A then P.real {ω} else 0) * (a - b) + P.real {ω} * b) := by
        refine Finset.sum_congr rfl fun ω _ ↦ ?_
        split_ifs <;> ring
    _ = P.real A * a + (1 - P.real A) * b := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, h1, h2]; ring

omit [DecidableEq ι] in
open scoped Classical in
theorem sum_mu_utility (c : ℝ) (φ : Act ι) :
    ∑ ω, P.real {ω} * J.utility s c φ ω =
      ∑ i, s.weight i * J.sideValue s P i (φ i) - if J.Preferred φ then c else 0 := by
  simp only [utility, mul_sub, Finset.sum_sub_distrib]
  congr 1
  · simp only [preutility, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [show ∑ ω, P.real {ω} * (s.weight i * if ω ∈ J.side i (φ i) then s.good i else s.bad i) =
        s.weight i * ∑ ω, P.real {ω} * if ω ∈ J.side i (φ i) then s.good i else s.bad i by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun ω _ ↦ by ring]
    rw [sum_mu_ite]
    rfl
  · rw [← Finset.sum_mul, sum_measureReal_singleton_eq_one, one_mul]

theorem expectedUtility_eq_sum_sideValue (c : ℝ) (μ : Measure (Act ι)) [IsFiniteMeasure μ] :
    expectedPayoff (J.utility s c) P μ =
      ∑ φ, μ.real {φ} *
        (∑ i, s.weight i * J.sideValue s P i (φ i) - if J.Preferred φ then c else 0) := by
  rw [expectedPayoff_eq_sum_sum]
  exact Finset.sum_congr rfl fun φ _ ↦ by rw [J.sum_mu_utility]

omit [Fintype Ω] [MeasurableSingletonClass Ω] [DecidableEq ι] [IsProbabilityMeasure P] in
/-- The value of the preferred acts before the cost. -/
noncomputable def preferredValue : ℝ := ∑ i, s.weight i * J.sideValue s P i true

omit [Fintype Ω] [MeasurableSingletonClass Ω] [Fintype ι] [DecidableEq ι]
  [IsProbabilityMeasure P] in
theorem sideValue_eq_of_represents (hP : J.Represents P) {i : ι} (hi : i ∉ J.strict)
    (t : Bool) :
    J.sideValue s P i t = J.sideValue s P i true := by
  cases t
  · have := J.sideValue_true_sub_false s P i
    rw [measureReal_def, measureReal_def, le_antisymm ((hP i).2 hi).2 ((hP i).2 hi).1, sub_self,
      zero_mul] at this
    linarith
  · rfl

omit [Fintype Ω] [MeasurableSingletonClass Ω] [Fintype ι] [DecidableEq ι] in
theorem sideValue_false_lt_true_of_represents (hP : J.Represents P) {i : ι}
    (hi : i ∈ J.strict) : J.sideValue s P i false < J.sideValue s P i true := by
  have := J.sideValue_true_sub_false s P i
  have hlt : P.real (J.right i) < P.real (J.left i) := P.strict_inducedGe_iff_real.1 ((hP i).1 hi)
  have hu := s.bad_lt_good i
  nlinarith

omit [Fintype Ω] [MeasurableSingletonClass Ω] [Fintype ι] [DecidableEq ι]
  [IsProbabilityMeasure P] in
/-- The margin by which the preferred acts beat any deviation on a strict comparison. -/
noncomputable def margin (hX : J.strict.Nonempty) : ℝ :=
  J.strict.inf' hX fun i ↦ s.weight i * (J.sideValue s P i true - J.sideValue s P i false)

omit [Fintype Ω] [MeasurableSingletonClass Ω] [Fintype ι] [DecidableEq ι] in
theorem margin_pos (hP : J.Represents P) (hX : J.strict.Nonempty) : 0 < J.margin s P hX := by
  rw [margin, Finset.lt_inf'_iff]
  intro i hi
  exact mul_pos (s.weight_pos i) (sub_pos.2 (J.sideValue_false_lt_true_of_represents s P hP hi))

omit [Fintype Ω] [MeasurableSingletonClass Ω] [Fintype ι] [DecidableEq ι]
  [IsProbabilityMeasure P] in
theorem margin_le (hX : J.strict.Nonempty) {i : ι} (hi : i ∈ J.strict) :
    J.margin s P hX ≤ s.weight i * (J.sideValue s P i true - J.sideValue s P i false) :=
  Finset.inf'_le _ hi

omit [Fintype Ω] [MeasurableSingletonClass Ω] [IsProbabilityMeasure P] in
/-- A preferred act is worth the preferred value under a representing measure. -/
theorem pureValue_of_preferred (hP : J.Represents P) {φ : Act ι} (hφ : J.Preferred φ) :
    ∑ i, s.weight i * J.sideValue s P i (φ i) = J.preferredValue s P := by
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases hi : i ∈ J.strict
  · rw [hφ i hi]
  · rw [J.sideValue_eq_of_represents s P hP hi]

omit [Fintype Ω] [MeasurableSingletonClass Ω] in
/-- A non-preferred act loses at least the margin under a representing measure. -/
theorem pureValue_le_of_not_preferred (hP : J.Represents P) (hX : J.strict.Nonempty)
    {φ : Act ι} (hφ : ¬J.Preferred φ) :
    ∑ i, s.weight i * J.sideValue s P i (φ i) ≤ J.preferredValue s P - J.margin s P hX := by
  simp only [Preferred, not_forall] at hφ
  obtain ⟨h, hh, hfalse⟩ := hφ
  have hfalse' : φ h = false := by simpa using hfalse
  have hle : ∀ i, s.weight i * J.sideValue s P i (φ i) ≤ s.weight i * J.sideValue s P i true := by
    intro i
    refine mul_le_mul_of_nonneg_left ?_ (s.weight_pos i).le
    by_cases hi : i ∈ J.strict
    · cases hφi : φ i
      · exact (J.sideValue_false_lt_true_of_represents s P hP hi).le
      · exact le_rfl
    · rw [J.sideValue_eq_of_represents s P hP hi]
  have hgap : J.margin s P hX ≤
      ∑ i, (s.weight i * J.sideValue s P i true - s.weight i * J.sideValue s P i (φ i)) := by
    refine (J.margin_le s P hX hh).trans ?_
    refine (Finset.single_le_sum (f := fun i ↦
      s.weight i * J.sideValue s P i true - s.weight i * J.sideValue s P i (φ i))
      (fun i _ ↦ sub_nonneg.2 (hle i)) (Finset.mem_univ h)).trans' ?_
    rw [hfalse']; ring_nf; exact le_rfl
  rw [Finset.sum_sub_distrib] at hgap
  unfold preferredValue
  linarith

/-- Under a representing measure the expected utility of a mixed act is at most the preferred
value less the cost, with equality on `Q★`. -/
theorem expectedUtility_le_of_represents (hP : J.Represents P) (hX : J.strict.Nonempty)
    {c : ℝ} (hcm : c ≤ J.margin s P hX) (μ : Measure (Act ι)) [IsProbabilityMeasure μ] :
    expectedPayoff (J.utility s c) P μ ≤ J.preferredValue s P - c := by
  rw [J.expectedUtility_eq_sum_sideValue]
  calc ∑ φ, μ.real {φ} *
        (∑ i, s.weight i * J.sideValue s P i (φ i) - if J.Preferred φ then c else 0)
      ≤ ∑ φ, μ.real {φ} * (J.preferredValue s P - c) := by
        refine Finset.sum_le_sum fun φ _ ↦ mul_le_mul_of_nonneg_left ?_ measureReal_nonneg
        by_cases hφ : J.Preferred φ
        · rw [J.pureValue_of_preferred s P hP hφ, ite_eq_left hφ]
        · rw [ite_eq_right hφ, sub_zero]
          linarith [J.pureValue_le_of_not_preferred s P hP hX hφ]
    _ = J.preferredValue s P - c := by
        rw [← Finset.sum_mul, sum_measureReal_singleton_eq_one, one_mul]

theorem expectedUtility_uniformPreferred_of_represents (hP : J.Represents P) (c : ℝ) :
    expectedPayoff (J.utility s c) P J.uniformPreferred = J.preferredValue s P - c := by
  rw [J.expectedUtility_eq_sum_sideValue]
  have hN : (J.preferredCard : ℝ) ≠ 0 := by exact_mod_cast J.preferredCard_pos.ne'
  calc ∑ φ, J.uniformPreferred.real {φ} *
        (∑ i, s.weight i * J.sideValue s P i (φ i) - if J.Preferred φ then c else 0)
      = ∑ φ, if J.Preferred φ then 1 / (J.preferredCard : ℝ) * (J.preferredValue s P - c)
          else 0 := by
        refine Finset.sum_congr rfl fun φ _ ↦ ?_
        rw [J.uniformPreferred_real_singleton]
        by_cases hφ : J.Preferred φ
        · rw [ite_eq_left hφ, ite_eq_left hφ, ite_eq_left hφ, J.pureValue_of_preferred s P hP hφ]
        · simp [hφ]
    _ = J.preferredValue s P - c := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        change (J.preferredCard : ℝ) * _ = _
        field_simp

/-- The pushforward of `Q★` along a change of one coordinate beats `Q★` when the change never
hurts a preferred act and helps one. -/
theorem expectedUtility_map_gt {c : ℝ} (f : Act ι → Act ι)
    (hle : ∀ φ, J.Preferred φ →
      ∑ ω, P.real {ω} * J.utility s c φ ω ≤ ∑ ω, P.real {ω} * J.utility s c (f φ) ω)
    (hlt : ∃ φ, J.Preferred φ ∧
      ∑ ω, P.real {ω} * J.utility s c φ ω < ∑ ω, P.real {ω} * J.utility s c (f φ) ω) :
    expectedPayoff (J.utility s c) P J.uniformPreferred <
      expectedPayoff (J.utility s c) P (J.uniformPreferred.map f) := by
  classical
  have hmap : expectedPayoff (J.utility s c) P (J.uniformPreferred.map f) =
      ∑ φ, J.uniformPreferred.real {φ} * ∑ ω, P.real {ω} * J.utility s c (f φ) ω := by
    rw [expectedPayoff_eq_sum_sum]
    have : ∀ ψ, (J.uniformPreferred.map f).real {ψ} =
        ∑ φ ∈ Finset.univ.filter (fun φ ↦ f φ = ψ), J.uniformPreferred.real {φ} := fun ψ ↦ by
      rw [map_measureReal_apply .of_discrete (.singleton ψ), sum_measureReal_singleton]
      congr 1
      ext φ; simp
    simp only [this, Finset.sum_mul]
    conv_rhs => rw [← Finset.sum_fiberwise Finset.univ f]
    refine Finset.sum_congr rfl fun ψ _ ↦ Finset.sum_congr rfl fun φ hφ ↦ ?_
    rw [(Finset.mem_filter.1 hφ).2]
  rw [hmap, expectedPayoff_eq_sum_sum]
  obtain ⟨φ₀, hφ₀, hlt₀⟩ := hlt
  refine Finset.sum_lt_sum (fun φ _ ↦ ?_) ⟨φ₀, Finset.mem_univ _, ?_⟩
  · by_cases hφ : J.Preferred φ
    · exact mul_le_mul_of_nonneg_left (hle φ hφ) measureReal_nonneg
    · rw [J.uniformPreferred_real_singleton, ite_eq_right hφ, zero_mul, zero_mul]
  · refine mul_lt_mul_of_pos_left hlt₀ ?_
    rw [J.uniformPreferred_real_singleton, ite_eq_left hφ₀]
    have : (0 : ℝ) < J.preferredCard := by exact_mod_cast J.preferredCard_pos
    exact div_pos one_pos this

/-- A measure represents the judgments iff, for some cost, the uniform preferred act maximizes
expected utility in the canonical decision problem (Lemma 1). -/
theorem represents_iff_maximizes (hX : J.strict.Nonempty) :
    J.Represents P ↔ ∃ c, 0 < c ∧ MaximizesPayoff (J.utility s c) P J.uniformPreferred := by
  constructor
  · intro hP
    refine ⟨J.margin s P hX, J.margin_pos s P hP hX, fun ν _ ↦ ?_⟩
    rw [J.expectedUtility_uniformPreferred_of_represents s P hP]
    exact J.expectedUtility_le_of_represents s P hP hX le_rfl ν
  · rintro ⟨c, hc, hmax⟩ i
    have hval : ∀ φ t, ∑ ω, P.real {ω} * J.utility s c (Function.update φ i t) ω -
        ∑ ω, P.real {ω} * J.utility s c φ ω =
        s.weight i * (J.sideValue s P i t - J.sideValue s P i (φ i)) -
          ((if J.Preferred (Function.update φ i t) then c else 0) -
            if J.Preferred φ then c else 0) := by
      intro φ t
      rw [J.sum_mu_utility, J.sum_mu_utility]
      have : ∑ j, s.weight j * J.sideValue s P j (Function.update φ i t j) -
          ∑ j, s.weight j * J.sideValue s P j (φ j) =
          s.weight i * (J.sideValue s P i t - J.sideValue s P i (φ i)) := by
        rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
        · rw [Function.update_self, mul_sub]
        · intro j _ hj; rw [Function.update_of_ne hj, sub_self]
        · intro h; exact absurd (Finset.mem_univ i) h
      rw [← this]
      ring
    constructor
    · intro hi
      rw [P.strict_inducedGe_iff_real]
      by_contra hge
      push Not at hge
      -- flipping a strict comparison drops the cost and loses nothing
      have hgain : ∀ φ, J.Preferred φ → ∑ ω, P.real {ω} * J.utility s c φ ω <
          ∑ ω, P.real {ω} * J.utility s c (Function.update φ i false) ω := by
        intro φ hφ
        have hnot : ¬J.Preferred (Function.update φ i false) := fun h ↦ by
          have := h i hi; simp at this
        have hdiff := J.sideValue_true_sub_false s P i
        have hu := s.bad_lt_good i
        have hw := s.weight_pos i
        have := hval φ false
        rw [ite_eq_right hnot, ite_eq_left hφ, hφ i hi] at this
        have h1 : 0 ≤ J.sideValue s P i false - J.sideValue s P i true := by nlinarith
        have h2 := mul_nonneg hw.le h1
        linarith
      exact absurd (hmax (J.uniformPreferred.map fun φ ↦ Function.update φ i false) inferInstance)
        (not_le.2 (J.expectedUtility_map_gt s P _ (fun φ hφ ↦ (hgain φ hφ).le)
          ⟨_, J.preferred_const_true, hgain _ J.preferred_const_true⟩))
    · intro hi
      rw [P.inducedGe_iff_real, P.inducedGe_iff_real, and_comm, ← le_antisymm_iff]
      by_contra hne
      -- moving an indifferent comparison to its likelier side keeps the cost and gains
      have hpref : ∀ φ t, J.Preferred φ → J.Preferred (Function.update φ i t) := by
        intro φ t hφ j hj
        rw [Function.update_of_ne fun (h : j = i) ↦ hi (h ▸ hj)]
        exact hφ j hj
      obtain ⟨t, ht⟩ : ∃ t, J.sideValue s P i (!t) < J.sideValue s P i t := by
        have hdiff := J.sideValue_true_sub_false s P i
        have hu := s.bad_lt_good i
        rcases lt_or_gt_of_ne hne with h | h
        · exact ⟨false, by simp only [Bool.not_false]; nlinarith⟩
        · exact ⟨true, by simp only [Bool.not_true]; nlinarith⟩
      have hgain : ∀ φ, J.Preferred φ → ∑ ω, P.real {ω} * J.utility s c φ ω ≤
          ∑ ω, P.real {ω} * J.utility s c (Function.update φ i t) ω := by
        intro φ hφ
        have := hval φ t
        rw [ite_eq_left (hpref φ t hφ), ite_eq_left hφ, sub_self, sub_zero] at this
        have hw := s.weight_pos i
        have hle : J.sideValue s P i (φ i) ≤ J.sideValue s P i t := by
          by_cases hφt : φ i = t
          · rw [hφt]
          · have : φ i = !t := by cases t <;> cases hφi : φ i <;> simp_all
            rw [this]; exact ht.le
        nlinarith
      have hstrict : ∑ ω, P.real {ω} * J.utility s c (Function.update (fun _ ↦ true) i (!t)) ω <
          ∑ ω, P.real {ω} * J.utility s c
            (Function.update (Function.update (fun _ ↦ true) i (!t)) i t) ω := by
        have hφ := hpref _ (!t) J.preferred_const_true
        have := hval (Function.update (fun _ ↦ true) i (!t)) t
        rw [ite_eq_left (hpref _ t hφ), ite_eq_left hφ, sub_self, sub_zero,
          Function.update_self] at this
        have hw := s.weight_pos i
        nlinarith
      exact absurd (hmax (J.uniformPreferred.map fun φ ↦ Function.update φ i t) inferInstance)
        (not_le.2 (J.expectedUtility_map_gt s P _ hgain
          ⟨_, hpref _ (!t) J.preferred_const_true, hstrict⟩))

end MainLemma

/-! ### Theorem 1 -/

/-- **Theorem 1.** The judgments are probabilistically representable iff, for some cost, the
uniform preferred act `Q★` is not strictly dominated in the canonical decision problem. -/
theorem representable_iff_exists_not_dominated [MeasurableSingletonClass Ω] (s : Stakes ι)
    (hX : J.strict.Nonempty) :
    J.Representable ↔
      ∃ c, 0 < c ∧ ¬IsStrictlyPayoffDominated (J.utility s c) J.uniformPreferred := by
  constructor
  · rintro ⟨P, hP1, hP⟩
    obtain ⟨c, hc, hmax⟩ := (J.represents_iff_maximizes s P hX).1 hP
    refine ⟨c, hc, fun ⟨ν, hν1, hν⟩ ↦ ?_⟩
    exact absurd (hmax ν hν1) (not_le.2 (expectedPayoff_lt_of_forall_lt _ P hν))
  · rintro ⟨c, hc, hnd⟩
    rw [← neverBest_iff_strictlyDominated] at hnd
    push Not at hnd
    obtain ⟨P, hP1, hP⟩ := hnd
    exact ⟨P, hP1, (J.represents_iff_maximizes s P hX).2 ⟨c, hc, hP⟩⟩

/-! ### Balanced judgments

In each of the paper's examples every state lies in as many left sides as right sides: trading
the preferred gambles for the others "changes nothing whichever team wins" (p. 358). Such
judgments are a failure of Scott's cancellation, so none is representable, and under constant
stakes the trade is a pure act that dominates `Q★`. -/

omit [Fintype Ω] [DecidableEq ι] [MeasurableSpace Ω] in
/-- The judged pairs are **balanced** when every state lies in as many left sides as right
sides. -/
def Balanced : Prop :=
  ∀ ω, ∑ i, (J.left i).indicator (1 : Ω → ℕ) ω = ∑ i, (J.right i).indicator 1 ω

omit [Fintype Ω] [DecidableEq ι] [MeasurableSpace Ω] in
theorem preutility_const_false_of_balanced (hJ : J.Balanced) {w g b : ℝ} (hw : 0 < w)
    (hgb : b < g) (ω : Ω) :
    J.preutility (Stakes.const w g b hw hgb) (fun _ ↦ false) ω =
      J.preutility (Stakes.const w g b hw hgb) (fun _ ↦ true) ω := by
  have key (t : Bool) : J.preutility (Stakes.const w g b hw hgb) (fun _ ↦ t) ω =
      ∑ _i : ι, w * b + w * (g - b) * ∑ i, (((J.side i t).indicator (1 : Ω → ℕ) ω : ℕ) : ℝ) := by
    classical
    rw [preutility, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases h : ω ∈ J.side i t <;> simp [Stakes.const, h]
    ring
  have h : ∑ i, (((J.side i false).indicator (1 : Ω → ℕ) ω : ℕ) : ℝ) =
      ∑ i, (((J.side i true).indicator (1 : Ω → ℕ) ω : ℕ) : ℝ) := by
    exact_mod_cast (hJ ω).symm
  rw [key, key, h]

omit [Fintype Ω] [MeasurableSpace Ω] in
theorem dominated_of_balanced [Nonempty ι] (hJ : J.Balanced) (hX : J.strict = Finset.univ)
    {w g b : ℝ} (hw : 0 < w) (hgb : b < g) {c : ℝ} (hc : 0 < c) :
    IsStrictlyPayoffDominated (J.utility (Stakes.const w g b hw hgb) c) J.uniformPreferred := by
  refine ⟨Measure.dirac fun _ ↦ false, inferInstance, fun ω ↦ ?_⟩
  rw [J.uniformPreferred_eq_dirac_of_strict_eq_univ hX, mixedPayoff_dirac, mixedPayoff_dirac]
  simp only [utility, ite_eq_left J.preferred_const_true,
    ite_eq_right (J.not_preferred_const_false (hX ▸ Finset.univ_nonempty)),
    J.preutility_const_false_of_balanced hJ hw hgb]
  linarith

omit [Fintype Ω] in
theorem not_representable_of_balanced [MeasurableSingletonClass Ω] [Finite Ω] (hJ : J.Balanced)
    (hX : J.strict.Nonempty) : ¬J.Representable := by
  classical
  have := Fintype.ofFinite Ω
  rintro ⟨P, _, hP⟩
  obtain ⟨i₀, hi₀⟩ := hX
  have hle (i : ι) : P.real (J.right i) ≤ P.real (J.left i) := by
    by_cases hi : i ∈ J.strict
    · exact (P.strict_inducedGe_iff_real.1 ((hP i).1 hi)).le
    · exact P.inducedGe_iff_real.1 ((hP i).2 hi).1
  have hmass (S : ι → Set Ω) :
      ∑ i, P.real (S i) = ∑ ω, P.real {ω} * ∑ i, (((S i).indicator (1 : Ω → ℕ) ω : ℕ) : ℝ) := by
    have hA (A : Set Ω) :
        P.real A = ∑ ω, P.real {ω} * (((A.indicator (1 : Ω → ℕ) ω : ℕ)) : ℝ) := by
      simp only [Set.indicator_apply, Pi.one_apply, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
        mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter, sum_measureReal_singleton]
      congr 1
      ext ω; simp
    rw [Finset.sum_congr rfl fun i _ ↦ hA (S i)]
    simp only [Finset.mul_sum]
    exact Finset.sum_comm
  have hsum : ∑ i, P.real (J.left i) = ∑ i, P.real (J.right i) := by
    rw [hmass, hmass]
    exact Finset.sum_congr rfl fun ω _ ↦ by rw [← Nat.cast_sum, ← Nat.cast_sum, hJ ω]
  exact (Finset.sum_lt_sum (fun i _ ↦ hle i)
    ⟨i₀, Finset.mem_univ _, P.strict_inducedGe_iff_real.1 ((hP i₀).1 hi₀)⟩).ne' hsum

/-! ### One weak relation on all pairs

When every pair of events is judged, the paper notes (p. 359) that a single weak relation `≿`
records the judgments, with `≻` and `∼` defined from it. Icard's representability is then the
substrate's, so Theorem 1 joins Scott's characterization by cancellation. -/

omit [Fintype Ω] [DecidableEq ι] [MeasurableSpace Ω] in
/-- `ofRel r` judges each pair `A ≿ B` of a weak relation `r`, strictly when `B ≿ A` fails and
as an indifference otherwise. -/
def ofRel (r : Set Ω → Set Ω → Prop) [DecidableRel r] :
    Judgments Ω {p : Set Ω × Set Ω // r p.1 p.2} :=
  ⟨fun p ↦ p.1.1, fun p ↦ p.1.2, Finset.univ.filter fun p ↦ ¬r p.1.2 p.1.1⟩

theorem ofRel_representable_iff (r : Set Ω → Set Ω → Prop) [DecidableRel r] [Std.Total r] :
    (ofRel r).Representable ↔ ComparativeProbability.Representable r := by
  constructor
  · rintro ⟨P, hP, h⟩
    refine ⟨P, hP, fun A B ↦ ⟨fun hAB ↦ ?_, fun hle ↦ by_contra fun hAB ↦ ?_⟩⟩
    · by_cases hBA : r B A
      · exact ((h ⟨(A, B), hAB⟩).2 (by simpa [ofRel] using hBA)).1
      · exact ((h ⟨(A, B), hAB⟩).1 (by simpa [ofRel] using hBA)).1
    · exact ((h ⟨(B, A), (total_of r A B).resolve_left hAB⟩).1 (by simpa [ofRel] using hAB)).2 hle
  · rintro ⟨P, hP, h⟩
    refine ⟨P, hP, fun p ↦ ⟨fun hs ↦ ⟨(h _ _).1 p.2, fun hBA ↦ ?_⟩, fun hs ↦ ?_⟩⟩
    · simp only [ofRel, Finset.mem_filter, Finset.mem_univ, true_and] at hs
      exact hs ((h _ _).2 hBA)
    · simp only [ofRel, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hs
      exact ⟨(h _ _).1 p.2, (h _ _).1 hs⟩

omit [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω] in
theorem ofRel_strict_nonempty (r : Set Ω → Set Ω → Prop) [DecidableRel r] [IsLikelihoodMono r]
    [IsNontrivial r] : (ofRel r).strict.Nonempty :=
  ⟨⟨(Set.univ, ∅), rel_empty _⟩, by simpa [ofRel] using not_rel_empty_univ (r := r)⟩

end Judgments

open scoped Classical in
/-- For a qualitative probability, Scott's cancellation holds exactly when `Q★` avoids strict
dominance for some cost (Theorem 1, p. 350). -/
theorem cancellation_iff_exists_not_dominated [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    (r : Set Ω → Set Ω → Prop) [IsQualitativeProbability r]
    (s : Stakes {p : Set Ω × Set Ω // r p.1 p.2}) :
    Cancellation r ↔ ∃ c, 0 < c ∧
      ¬IsStrictlyPayoffDominated ((Judgments.ofRel r).utility s c)
        (Judgments.ofRel r).uniformPreferred := by
  rw [← representable_iff_cancellation, ← Judgments.ofRel_representable_iff]
  exact Judgments.representable_iff_exists_not_dominated _ _ (Judgments.ofRel_strict_nonempty r)

/-! ### The examples -/

/-- Unit weights and a unit good outcome, the stakes of the explorer and the World Cup. -/
noncomputable def unitStakes (ι : Type*) : Stakes ι := Stakes.const 1 1 0 one_pos one_pos

/-! #### The explorer (§1, §3, §7) -/

/-- The explorer of §1 judges the treasure likelier on island `A` than `B`, on `B` than `C`, and
on `C` than `A`. -/
def explorer : Judgments (Fin 3) (Fin 3) :=
  ⟨![{0}, {1}, {2}], ![{1}, {2}, {0}], Finset.univ⟩

/-- No transitive relation agrees with cyclic judgments, so "given intransitive judgments, there
can be no numerical probability measure that agrees with these judgments" (p. 349). -/
theorem explorer_not_agree (r : Set (Fin 3) → Set (Fin 3) → Prop) [IsTrans (Set (Fin 3)) r] :
    ¬explorer.Agree r := fun h ↦
  ((h 2).1 (Finset.mem_univ _)).2
    (trans_of r ((h 0).1 (Finset.mem_univ _)).1 ((h 1).1 (Finset.mem_univ _)).1)

theorem explorer_not_representable : ¬explorer.Representable := fun ⟨_, _, h⟩ ↦
  explorer_not_agree _ h

/-- The acts `A2`, `A3`, `A4` of the table in §7, each gambling on exactly one left side; on the
islands `A`, `B`, `C` they pay `0, 1, 2`, `1, 2, 0` and `2, 0, 1`. -/
def explorerMixture : Finset (Act (Fin 3)) :=
  {![false, false, true], ![false, true, false], ![true, false, false]}

/-- The uniform mixture of `A2`, `A3`, `A4` "guarantees payoff 1 in all states" (p. 365). -/
theorem explorer_mixture_payoff (c : ℝ) (ω : Fin 3) :
    mixedPayoff (explorer.utility (unitStakes (Fin 3)) c) (uniformOn ↑explorerMixture) ω = 1 := by
  rw [mixedPayoff_uniformOn]
  fin_cases ω <;>
    simp [explorerMixture, Judgments.utility, Judgments.preutility, Judgments.side,
      Judgments.Preferred, explorer, unitStakes, Stakes.const, Fin.sum_univ_three,
      Fin.forall_fin_succ, -Finset.sum_boole] <;> norm_num

/-- The explorer's preferred act `A1` is strictly dominated by the uniform mixture of `A2`, `A3`,
`A4` (§7). -/
theorem explorer_dominated {c : ℝ} (hc : 0 < c) :
    IsStrictlyPayoffDominated (explorer.utility (unitStakes (Fin 3)) c)
      explorer.uniformPreferred := by
  refine ⟨uniformOn ↑explorerMixture,
    isProbabilityMeasure_uniformOn (Finset.finite_toSet _)
      ⟨![false, false, true], by simp [explorerMixture]⟩,
    fun ω ↦ ?_⟩
  rw [explorer_mixture_payoff, explorer.uniformPreferred_eq_dirac_of_strict_eq_univ rfl,
    mixedPayoff_dirac, Judgments.utility, ite_eq_left explorer.preferred_const_true]
  fin_cases ω <;>
    simp [Judgments.preutility, Judgments.side, explorer, unitStakes, Stakes.const,
      Fin.sum_univ_three, -Finset.sum_boole] <;> linarith

/-! #### Raiffa on Ellsberg (§3) -/

/-- In the Ellsberg urn of §3 ([ellsberg-1961]), with balls red (`0`), black (`1`) and yellow
(`2`), red is judged likelier than black, and black or yellow likelier than red or yellow. -/
def ellsberg : Judgments (Fin 3) (Fin 2) :=
  ⟨![{0}, {1, 2}], ![{1}, {0, 2}], Finset.univ⟩

/-- The coin-flip weights of Raiffa's comment ([raiffa-1961]), with a hundred utiles at stake. -/
noncomputable def coinStakes : Stakes (Fin 2) :=
  Stakes.const (1 / 2) 100 0 (by norm_num) (by norm_num)

theorem ellsberg_not_agree (r : Set (Fin 3) → Set (Fin 3) → Prop) [IsQualitativeAdditive r] :
    ¬ellsberg.Agree r := fun h ↦ by
  have h0 := (h 0).1 (Finset.mem_univ _)
  have h1 := (h 1).1 (Finset.mem_univ _)
  have key : r ({1} ⊔ {2}) ({0} ⊔ {2}) ↔ r {1} {0} := rel_sup_sup_right_iff (by simp) (by simp)
  simp only [Set.sup_eq_union, Set.singleton_union] at key
  exact h0.2 (key.1 h1.1)

theorem ellsberg_not_representable : ¬ellsberg.Representable := fun ⟨_, _, h⟩ ↦
  ellsberg_not_agree _ h

theorem ellsberg_balanced : ellsberg.Balanced := fun ω ↦ by
  fin_cases ω <;> simp [ellsberg]

/-- In Raiffa's argument the preferred act is strictly dominated, paying `50 − c` against option 2's
`50` (p. 355). -/
theorem ellsberg_dominated {c : ℝ} (hc : 0 < c) :
    IsStrictlyPayoffDominated (ellsberg.utility coinStakes c) ellsberg.uniformPreferred :=
  ellsberg.dominated_of_balanced ellsberg_balanced rfl _ _ hc

/-! #### Kraft, Pratt and Seidenberg's World Cup (§4) -/

/-- The World Cup judgments of §4, with Argentina, Brazil, China, Denmark and England as the
worlds `0`–`4`. Denmark is judged likelier than Argentina or China, Argentina or England than
China or Denmark, Brazil or China than Argentina or Denmark, and Argentina, China or Denmark than
Brazil or England. -/
def worldCup : Judgments (Fin 5) (Fin 4) :=
  ⟨![{3}, {0, 4}, {1, 2}, {0, 2, 3}], ![{0, 2}, {2, 3}, {0, 3}, {1, 4}], Finset.univ⟩

theorem worldCup_balanced : worldCup.Balanced := fun ω ↦ by
  fin_cases ω <;> simp [worldCup, Fin.sum_univ_four]

theorem worldCup_not_representable : ¬worldCup.Representable :=
  worldCup.not_representable_of_balanced worldCup_balanced ⟨0, Finset.mem_univ _⟩

/-- In §4's system of bets, trading the four preferred gambles `G1`, `G3`, `G5`, `G7` for the
four others changes nothing whichever team wins, so paying for the trade is strict dominance.
(The paper's `G2` reads "Argentina or Chile", a slip for China.) -/
theorem worldCup_dominated {c : ℝ} (hc : 0 < c) :
    IsStrictlyPayoffDominated (worldCup.utility (unitStakes (Fin 4)) c) worldCup.uniformPreferred :=
  worldCup.dominated_of_balanced worldCup_balanced rfl _ _ hc

/-- The World Cup teams as Kraft, Pratt and Seidenberg's atoms `p, q, r, s, t` (`0`–`4`), with
Argentina `q`, Brazil `r`, China `s`, Denmark `p` and England `t`. -/
def worldCupToKps : Fin 5 ≃ Fin 5 := ⟨![1, 2, 3, 0, 4], ![3, 0, 1, 2, 4], by decide, by decide⟩

private theorem preimage_worldCupToKps_symm (s : Finset (Fin 5)) :
    worldCupToKps.symm ⁻¹' (↑s : Set (Fin 5)) = ↑(s.map worldCupToKps.toEmbedding) := by
  ext x; simp

theorem worldCup_agree_qualitativeProbability :
    ∃ r : Set (Fin 5) → Set (Fin 5) → Prop, IsQualitativeProbability r ∧ worldCup.Agree r ∧
      ¬ComparativeProbability.Representable r := by
  classical
  let r : Set (Fin 5) → Set (Fin 5) → Prop := Set.preimage worldCupToKps.symm ⁻¹'o kpsGe
  have hr (s t : Finset (Fin 5))
      (h : kpsRank (t.map worldCupToKps.toEmbedding) < kpsRank (s.map worldCupToKps.toEmbedding)) :
      AsymmRel r ↑s ↑t := by
    have key (s t : Finset (Fin 5)) : r ↑s ↑t ↔
        kpsRank (t.map worldCupToKps.toEmbedding) ≤ kpsRank (s.map worldCupToKps.toEmbedding) := by
      show kpsGe _ _ ↔ _
      simp only [kpsGe, kpsRankSet, preimage_worldCupToKps_symm, Finset.toFinset_coe]
    exact ⟨(key s t).2 h.le, fun h' ↦ absurd ((key t s).1 h') (not_le.2 h)⟩
  have hagree : worldCup.Agree r := fun i ↦ ⟨fun _ ↦ ?_, fun hi ↦ absurd (Finset.mem_univ i) hi⟩
  · exact ⟨r, inferInstance, hagree, fun h ↦ worldCup_not_representable (hagree.representable h)⟩
  fin_cases i
  · simpa [worldCup] using hr {3} {0, 2} (by decide)
  · simpa [worldCup] using hr {0, 4} {2, 3} (by decide)
  · simpa [worldCup] using hr {1, 2} {0, 3} (by decide)
  · simpa [worldCup] using hr {0, 2, 3} {1, 4} (by decide)

end Icard2016
