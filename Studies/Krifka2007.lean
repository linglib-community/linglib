module

public import Linglib.Data.Experiments.Krifka2007
public import Linglib.Pragmatics.Bidirectional
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Semantics.Degree.Granularity
public import Linglib.Semantics.Quantification.Numerals.Roundness
public import Mathlib.Probability.UniformOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Data.Nat.Dist

/-!
# Krifka (2007): Approximate interpretation of number words

Round number words invite approximate interpretations, *one hundred meters* against *103 meters*.
Krifka derives this without a general bias for approximation. His earlier bidirectional account
paired a preference for simple expressions with one for approximate interpretations; this paper
keeps truthfulness strict and lets expression economy apply only where there is a choice, which
there is only under an approximate reading. A hearer then reasons strategically: a non-shortest
expression signals a precise reading, and a short one is read approximately because the
approximate reading covers more equally likely values. Where number words name points on scales
of different granularity, the same reasoning picks the coarsest salient scale the reported value
lies on, and halving a scale's width is the optimal refinement, adding exactly the values the
coarser scale distorts most.

## Implementation notes

* Approximate readings are intervals, the halo `[i - s, i + s]`, the paper's own simplification
  of its normal distributions; indistinguishability at approximation level 1/10 compares means
  within one standard deviation.
* The hearer's comparisons are stated on the joint measure over scale and value at the report
  events, since the posteriors over scales given one report share a normalizer.
* Each scale is credited with its full cell: the quarter-hour cell around 45 holds fifteen
  minutes where the paper prints `10r`, and the approximate mass of *forty* on the uniform prior
  is `9/100` where the paper prints 0.08; neither difference affects a comparison.
* Expression costs are a parameter, with the paper's cost comparisons as hypotheses; the
  paper's own syllable and occurrence counts are the rows of `Data/Experiments/Krifka2007.json`.

## References

* [krifka-2007]
* [krifka-2009b]
* [krifka-2002]
* [blutner-2000]
* [jansen-pollmann-2001]
* [sigurd-1988]
-/

@[expose] public section

namespace Krifka2007

open BidirectionalOT OptimalityTheory MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- A number word is read precisely or approximately. -/
inductive Reading where
  | precise
  | approximate
  deriving DecidableEq, Repr, Fintype

/-! ### The earlier bidirectional account -/

/-- A simple and a complex number word, *one hundred* and *one hundred and three*. -/
inductive Form where
  | simple
  | complex
  deriving DecidableEq, Repr, Fintype

/-- The preference for simple expressions. -/
def simpleExpression : Form × Reading → ℕ
  | (.simple, _) => 0
  | (.complex, _) => 1

/-- The earlier account's preference for approximate interpretations. -/
def approximateInterpretation : Form × Reading → ℕ
  | (_, .approximate) => 0
  | (_, .precise) => 1

/-- The superoptimal pairs of the earlier account read the simple form approximately and the
complex form precisely, the division of pragmatic labour. -/
theorem division_of_labour :
    superoptimal Finset.univ (profile [simpleExpression, approximateInterpretation]) =
      {(.simple, .approximate), (.complex, .precise)} := by
  decide

theorem division_of_labour_without_simple_precise :
    superoptimal (Finset.univ.erase (.simple, .precise))
      (profile [simpleExpression, approximateInterpretation]) =
      {(.simple, .approximate), (.complex, .precise)} := by
  decide

/-! ### Truthfulness and conditional economy -/

/-- The number words of the paper's tableau. -/
inductive Numeral where
  | thirtyNine
  | forty
  deriving DecidableEq, Repr, Fintype

/-- The value a number word names. -/
def Numeral.value : Numeral → ℕ
  | .thirtyNine => 39
  | .forty => 40

/-- A number word read precisely denotes its value, and read approximately the values within a
deviation of two. -/
def range (p : Numeral × Reading) : Set ℕ :=
  match p.2 with
  | .precise => {p.1.value}
  | .approximate => {v | Nat.dist v p.1.value ≤ 2}

instance (v : ℕ) (p : Numeral × Reading) : Decidable (v ∈ range p) := by
  obtain ⟨n, r⟩ := p
  cases r <;> (simp only [range]; infer_instance)

/-- Truthfulness marks a report whose range misses the true value. -/
def inRange (v : ℕ) (p : Numeral × Reading) : ℕ := if v ∈ range p then 0 else 1

/-- Expression economy marks an approximate report when a word of lower cost `c` covers the same
value, and never marks a precise report, so it is operative only where there is a choice. -/
def economy (c : Numeral → ℕ) (p : Numeral × Reading) : ℕ :=
  match p.2 with
  | .precise => 0
  | .approximate => if ∃ n, Nat.dist n.value p.1.value ≤ 2 ∧ c n < c p.1 then 1 else 0

/-- The paper's tableau ranks truthfulness above economy, over both words on both readings. -/
def reportTableau (c : Numeral → ℕ) (v : ℕ) : Tableau (Numeral × Reading) 2 :=
  Tableau.ofList {(.forty, .approximate), (.forty, .precise), (.thirtyNine, .approximate),
    (.thirtyNine, .precise)} [inRange v, economy c]

private theorem economy_eq {c : Numeral → ℕ} (h : c .forty < c .thirtyNine) :
    economy c = fun p ↦ if p = (.thirtyNine, .approximate) then 1 else 0 := by
  funext ⟨n, r⟩
  cases r with
  | precise => simp [economy]
  | approximate =>
    simp only [economy]
    split_ifs with hx hp hp
    · rfl
    · obtain ⟨m, -, hm⟩ := hx
      cases n <;> cases m <;> simp_all
      omega
    · obtain rfl := (Prod.mk.inj hp).1
      exact absurd ⟨.forty, by decide, h⟩ hx
    · rfl

/-- With *forty* the cheaper word, a true value of 39 is reported as *forty* read approximately
or *thirty-nine* read precisely, and a true value of 40 as *forty* on either reading. -/
theorem winners_of_true_value {c : Numeral → ℕ} (h : c .forty < c .thirtyNine) :
    (reportTableau c 39).optimal = {(.forty, .approximate), (.thirtyNine, .precise)} ∧
      (reportTableau c 40).optimal = {(.forty, .approximate), (.forty, .precise)} := by
  unfold reportTableau
  rw [economy_eq h]
  decide

/-! ### Strategic communication -/

/-- Two reported values are indistinguishable when their distance is within the standard
deviation at approximation level 1/10. -/
def Indistinguishable (i i' : ℕ) : Prop := 10 * Nat.dist i' i ≤ i

instance (i i' : ℕ) : Decidable (Indistinguishable i i') := inferInstanceAs (Decidable (_ ≤ _))

/-- A report of cost `c` is consistent with the approximate reading when the speaker could not
have conveyed an indistinguishable value more cheaply. -/
def ConsistentWithApproximation (c : ℕ → ℕ) (i : ℕ) : Prop :=
  ∀ i', Indistinguishable i i' → c i ≤ c i'

private theorem indistinguishable_forty {i' : ℕ} :
    Indistinguishable 40 i' ↔ 36 ≤ i' ∧ i' ≤ 44 := by
  unfold Indistinguishable Nat.dist
  omega

theorem forty_approximate_thirtyEight_precise {c : ℕ → ℕ}
    (hc : ∀ i, 36 ≤ i → i ≤ 44 → i ≠ 40 → c 40 < c i) :
    ConsistentWithApproximation c 40 ∧ ¬ ConsistentWithApproximation c 38 := by
  refine ⟨fun i' h ↦ ?_, fun h ↦ ?_⟩
  · rw [indistinguishable_forty] at h
    obtain rfl | hne := eq_or_ne i' 40
    · exact le_rfl
    · exact (hc i' h.1 h.2 hne).le
  · have h40 := h 40 (by unfold Indistinguishable Nat.dist; omega)
    have := hc 38 (by omega) (by omega) (by omega)
    omega

private theorem uniformOn_Icc_apply (t : Finset ℕ) :
    uniformOn (Finset.Icc 1 100 : Set ℕ) ↑t = (Finset.Icc 1 100 ∩ t).card / 100 := by
  rw [uniformOn_apply_finset]
  simp

theorem precise_mass : uniformOn (Finset.Icc 1 100 : Set ℕ) {40} = 1 / 100 := by
  rw [← Finset.coe_singleton, uniformOn_Icc_apply,
    Finset.inter_singleton_of_mem (by simp), Finset.card_singleton, Nat.cast_one]

theorem approximate_mass :
    uniformOn (Finset.Icc 1 100 : Set ℕ) (Set.Icc 36 44) = 9 / 100 := by
  rw [← Finset.coe_Icc, uniformOn_Icc_apply,
    Finset.inter_eq_right.2 (Finset.Icc_subset_Icc (by norm_num) (by norm_num))]
  norm_num

/-- Hearing *forty*, the approximate reading is the conservative hypothesis, covering more of
the prior than the precise one. -/
theorem approximate_more_probable :
    uniformOn (Finset.Icc 1 100 : Set ℕ) {40} <
      uniformOn (Finset.Icc 1 100 : Set ℕ) (Set.Icc 36 44) := by
  rw [precise_mass, approximate_mass, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  have h0 : ((100 : ℝ≥0∞))⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (by norm_num)
  have ht : ((100 : ℝ≥0∞))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (by norm_num)
  exact ENNReal.mul_lt_mul_right h0 ht (by exact_mod_cast (by norm_num : (1 : ℝ≥0) < 9))

/-! ### Choosing a scale -/

open Degree Numerals.Roundness

private theorem intCast_mem_zmultiples_iff {w n : ℤ} :
    (n : ℝ) ∈ AddSubgroup.zmultiples (w : ℝ) ↔ w ∣ n := by
  simp only [AddSubgroup.mem_zmultiples_iff, zsmul_eq_mul]
  exact ⟨fun ⟨k, hk⟩ ↦ ⟨k, by rw [mul_comm]; exact_mod_cast hk.symm⟩,
    fun ⟨k, hk⟩ ↦ ⟨k, by push_cast [hk]; ring⟩⟩

variable {W : Finset ℤ} (μs : Measure W) (ν : Measure ℝ) {r : ℝ≥0∞} {I : Set ℝ} {n : ℤ}

/-- The speaker chooses the scale of width `w` and reports the scale point nearest the value as
`n`. -/
def reportedOn (w : W) (n : ℤ) : Set (W × ℝ) :=
  {w} ×ˢ (representative ((w : ℤ) : ℝ) ⁻¹' {(n : ℝ)})

theorem measure_reportedOn_of_dvd [SFinite ν]
    (hν : ∀ ⦃s⦄, MeasurableSet s → s ⊆ I → ν s = r * volume s) {w : W} (hw : 0 < (w : ℤ))
    (hI : Set.Ico ((n : ℝ) - (w : ℤ) / 2) (n + (w : ℤ) / 2) ⊆ I) (h : (w : ℤ) ∣ n) :
    (μs.prod ν) (reportedOn w n) = μs {w} * (r * ENNReal.ofReal ((w : ℤ) : ℝ)) := by
  rw [reportedOn, Measure.prod_prod, preimage_representative (by exact_mod_cast hw)
    (intCast_mem_zmultiples_iff.2 h), hν measurableSet_Ico hI, Real.volume_Ico]
  congr 3
  ring

theorem measure_reportedOn_of_not_dvd {w : W} (h : ¬ (w : ℤ) ∣ n) :
    (μs.prod ν) (reportedOn w n) = 0 := by
  rw [reportedOn, preimage_representative_of_notMem (mt intCast_mem_zmultiples_iff.1 h),
    Set.prod_empty, measure_empty]

/-- Hearing `n` on aligned scales with equal priors, the most probable scale is the coarsest one
through `n`: *forty-five minutes* is read at the quarter hours and *forty* at the five
minutes. -/
theorem coarsest_scale_most_probable [SFinite ν]
    (hν : ∀ ⦃s⦄, MeasurableSet s → s ⊆ I → ν s = r * volume s) (hr : r ≠ 0) (hr' : r ≠ ⊤)
    (hpos : ∀ w ∈ W, 0 < w) (hW : ∀ a ∈ W, ∀ b ∈ W, a ∣ b ∨ b ∣ a)
    (hs : ∀ v w : W, μs {v} = μs {w}) (hs0 : ∀ w : W, μs {w} ≠ 0) (hs' : ∀ w : W, μs {w} ≠ ⊤)
    (hI : ∀ w : W, Set.Ico ((n : ℝ) - (w : ℤ) / 2) (n + (w : ℤ) / 2) ⊆ I)
    (hne : (W.filter (· ∣ n)).Nonempty) {w : W} :
    (∀ v, (μs.prod ν) (reportedOn v n) ≤ (μs.prod ν) (reportedOn w n)) ↔
      (w : ℤ) = scaleLcm W n := by
  obtain ⟨hLW, hLn, hLmax⟩ := scaleLcm_mem_of_aligned hpos hW hne
  have hmass (v : W) (h : (v : ℤ) ∣ n) :=
    measure_reportedOn_of_dvd μs ν hν (hpos v v.2) (hI v) h
  have key : ∀ v u : W, (v : ℤ) ∣ n → (u : ℤ) ∣ n →
      ((μs.prod ν) (reportedOn v n) ≤ (μs.prod ν) (reportedOn u n) ↔ (v : ℤ) ≤ u) := by
    intro v u hv hu
    rw [hmass v hv, hmass u hu, hs v u,
      ENNReal.mul_le_mul_iff_right (hs0 u) (hs' u), ENNReal.mul_le_mul_iff_right hr hr',
      ENNReal.ofReal_le_ofReal_iff (by exact_mod_cast (hpos u u.2).le)]
    exact Int.cast_le
  constructor
  · intro h
    have hw : (w : ℤ) ∣ n := by
      by_contra hw
      have := h ⟨_, hLW⟩
      rw [measure_reportedOn_of_not_dvd μs ν hw, hmass ⟨_, hLW⟩ hLn,
        nonpos_iff_eq_zero] at this
      refine mul_ne_zero (hs0 _) (mul_ne_zero hr ?_) this
      exact (ENNReal.ofReal_pos.2 (by exact_mod_cast hpos _ hLW)).ne'
    exact le_antisymm (hLmax w w.2 hw) ((key ⟨_, hLW⟩ w hLn hw).1 (h _))
  · intro hwL v
    by_cases hv : (v : ℤ) ∣ n
    · exact (key v w hv (hwL ▸ hLn)).2 (hwL ▸ hLmax v v.2 hv)
    · rw [measure_reportedOn_of_not_dvd μs ν hv]
      exact zero_le

/-- The minute scales count hours, half hours, quarter hours, five minutes and minutes. -/
def minuteScales : Finset ℤ := {60, 30, 15, 5, 1}

theorem fortyFive_quarterHours_forty_fiveMinutes :
    scaleLcm minuteScales 45 = 15 ∧ scaleLcm minuteScales 40 = 5 := by decide

/-! ### Simplicity of expression and of representation -/

/-- The average syllables per number word on a scale. -/
def averageSyllables (s : SyllableScale) : ℚ :=
  (syllableCounts s).syllables / (syllableCounts s).words

theorem ser_decimal_scales :
    averageSyllables .tens < averageSyllables .fives ∧
      averageSyllables .fives < averageSyllables .ones ∧
        averageSyllables .ones < averageSyllables .threes := by
  norm_num [averageSyllables, syllableCounts]

theorem months_violate_ser :
    averageSyllables .monthsByOne < averageSyllables .monthsCoarse := by
  norm_num [averageSyllables, syllableCounts]

theorem fifty_follows_the_language :
    ((counts .foerti).count < (counts .femti).count ∧
      (counts .seksti).count < (counts .femti).count) ∧
      (counts .halvtreds).count < (counts .fyrre).count ∧
        (counts .halvtreds).count < (counts .tres).count := by
  decide

/-! ### Refining by half -/

theorem halving_adds_most_distorted {d : ℝ} :
    |d - representative 10 d| = 5 ↔
      d ∈ AddSubgroup.zmultiples (5 : ℝ) ∧ d ∉ AddSubgroup.zmultiples (10 : ℝ) := by
  simpa [show (10 : ℝ) / 2 = 5 by norm_num]
    using abs_sub_representative_eq_half_iff (by norm_num : (0 : ℝ) < 10)

end Krifka2007
