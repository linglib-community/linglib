module

public import Linglib.Pragmatics.DecisionTheoretic.Basic
public import Linglib.Core.MeasureTheory.Measure.Prod
public import Linglib.Semantics.Quantification.Numerals.Roundness
public import Studies.Cummins2015
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# Cummins and Franke (2021): Rational Interpretation of Numerical Quantity in Argumentative Contexts

Cummins and Franke measure the argumentative strength of a numerical utterance toward a
speaker's goal, after Merin, as a log Bayes factor: once on the utterance's truth conditions
and once on its felicitous assertability, which accounts for the implicatures a hearer may
draw. In their conference example the goal is that more than 120 people attend, attendees are
those who registered, registrations are uniform on [0, 200], and the speaker chooses between
*more than 100* and *more than 110*. Semantically the stronger utterance is the stronger
argument, but a hearer who reads *more than 110* as implicating *not more than 120* finds that
reading incompatible with the goal, so pragmatically the utterance is only weak evidence and
the order reverses.

We derive the semantic ordering from the general fact that shedding worlds where the goal
fails only strengthens an argument. When an implicature holds wherever the goal fails, the
pragmatic Bayes factor is the semantic one discounted by the enrichment rate times the
probability, given success, that the implicature fails. The paper asks which stronger
alternative *more than 100* negates. On its granularity account the hearer negates every
numeral above it at least as round on the scale evoked, which leaves *not more than* the next
point of that scale. The order then reverses at no rate on the scale of tens, above sixteen in
seventeen on the scale of 25s, above eight in eleven for the illustration's 150, and above one
in two on the scale of hundreds, the coarsest decimal scale through 100. Cummins's
constraint-based account selects the same alternatives for both numerals. The paper's
high-framing examples, its rules for a sceptical hearer and its corpus study are not
formalized.

## Implementation notes

* Registrations are uniform on the counts from 1 to 200, each count standing for the unit
  interval below it, so at the example's whole-number thresholds every probability is the one
  the paper computes on [0, 200]; *more than n* denotes `Set.Ioi n`.
* For *more than 110* the paper prints log 11, the Bayes factor of *more than 100* toward the
  goal *more than 110*. Its own pragmatic calculation gives *more than 110* probability 1/12
  given failure, so toward the stated goal the factor is 12, which the rate-zero case
  recovers. The ordering is unaffected.
* Strengths are natural logarithms; the paper prints base-ten decimals, and a change of base
  preserves the sign, order and ratios of strengths.

## References

* [cummins-franke-2021]
* [merin-1999-relevance]
* [cummins-sauerland-solt-2012]
* [krifka-2009b]
* [cummins-2015]
-/

@[expose] public section

namespace CumminsFranke2021

open DTS MeasureTheory ProbabilityTheory Set unitInterval Numerals.Roundness
open scoped ENNReal

/-! ### The conference -/

/-- Registrations are uniform on the counts from 1 to 200. -/
noncomputable abbrev prior : Measure ℕ := uniformOn (Icc 1 200)

/-- The conference succeeds iff more than 120 people register, and so attend. -/
noncomputable abbrev success : Context ℕ := ⟨Ioi 120, .of_discrete, prior⟩

private theorem ncard_Ioc (a b : ℕ) : (Ioc a b).ncard = b - a := by
  rw [← Finset.coe_Ioc, Set.ncard_coe_finset, Nat.card_Ioc]

private theorem real_prior (e : Set ℕ) : prior.real e = ((Icc 1 200 : Set ℕ) ∩ e).ncard / 200 := by
  rw [uniformOn_real_apply_of_finite (finite_Icc 1 200), ← Finset.coe_Icc 1 200,
    Set.ncard_coe_finset, Nat.card_Icc, Finset.coe_Icc]
  norm_num

private theorem real_prior_Ioc {a b : ℕ} (hab : a ≤ b) (hb : b ≤ 200) :
    prior.real (Ioc a b) = ((b : ℝ) - a) / 200 := by
  rw [real_prior, inter_eq_right.mpr fun x hx ↦ by simp only [mem_Ioc, mem_Icc] at hx ⊢; omega,
    ncard_Ioc, Nat.cast_sub hab]

private theorem real_prior_Ioi {c : ℕ} (hc : c ≤ 200) :
    prior.real (Ioi c) = (200 - (c : ℝ)) / 200 := by
  rw [real_prior, show (Icc 1 200 : Set ℕ) ∩ Ioi c = Ioc c 200 by
      ext x; simp only [mem_inter_iff, mem_Icc, mem_Ioi, mem_Ioc]; omega,
    ncard_Ioc, Nat.cast_sub hc, Nat.cast_ofNat]

private theorem real_prior_Iic {c : ℕ} (hc : c ≤ 200) : prior.real (Iic c) = c / 200 := by
  rw [real_prior, show (Icc 1 200 : Set ℕ) ∩ Iic c = Ioc 0 c by
      ext x; simp only [mem_inter_iff, mem_Icc, mem_Iic, mem_Ioc]; omega,
    ncard_Ioc, Nat.sub_zero]

theorem real_cond_Ioi {a c : ℕ} (hac : a ≤ c) (hc : c ≤ 200) :
    (prior[|Ioi a]).real (Ioi c) = (200 - (c : ℝ)) / (200 - a) := by
  rw [cond_real_apply _ .of_discrete, Ioi_inter_Ioi, max_eq_right hac, real_prior_Ioi hc,
    real_prior_Ioi (hac.trans hc), div_div_div_cancel_right₀ (by norm_num)]

theorem real_cond_Ioi_of_le {a c : ℕ} (hca : c ≤ a) (ha : a < 200) :
    (prior[|Ioi a]).real (Ioi c) = 1 := by
  rw [cond_real_apply _ .of_discrete, Ioi_inter_Ioi, max_eq_left hca, div_self]
  rw [real_prior_Ioi ha.le]
  exact div_ne_zero (sub_pos.2 (by exact_mod_cast ha)).ne' (by norm_num)

theorem real_cond_Iic {a c : ℕ} (hca : c ≤ a) (ha : a ≤ 200) :
    (prior[|Iic a]).real (Ioi c) = ((a : ℝ) - c) / a := by
  rw [cond_real_apply _ .of_discrete, inter_comm, Ioi_inter_Iic, real_prior_Ioc hca ha,
    real_prior_Iic ha, div_div_div_cancel_right₀ (by norm_num)]

/-! ### Truth conditions -/

theorem cond_moreThan100_le_moreThan110 :
    prior[|Ioi 100] (Ioi 120) ≤ prior[|Ioi 110] (Ioi 120) :=
  cond_le_cond_of_subset _ .of_discrete .of_discrete (Ioi_subset_Ioi (by norm_num))
    (inter_subset_left.trans (Ioi_subset_Ioi (by norm_num)))

theorem bayesFactor_moreThan100_lt_moreThan110 :
    bayesFactor success (Ioi 100) < bayesFactor success (Ioi 110) :=
  bayesFactor_lt_of_subset success .of_discrete (Ioi_subset_Ioi (by norm_num))
    (inter_subset_left.trans (Ioi_subset_Ioi (by norm_num)))
    ((measureReal_ne_zero_iff).mp (by
      rw [Ioi_inter_Ioi, max_eq_left (by norm_num), real_prior_Ioi (by norm_num)]
      norm_num))
    ((measureReal_ne_zero_iff).mp (by
      rw [Ioi_sdiff_Ioi, real_prior_Ioc (by norm_num) (by norm_num)]
      norm_num))

theorem toReal_bayesFactor_moreThan100 : (bayesFactor success (Ioi 100)).toReal = 6 := by
  rw [toReal_bayesFactor, real_cond_Ioi_of_le (by norm_num) (by norm_num), compl_Ioi,
    real_cond_Iic (by norm_num) (by norm_num)]
  norm_num

theorem toReal_bayesFactor_moreThan110 : (bayesFactor success (Ioi 110)).toReal = 12 := by
  rw [toReal_bayesFactor, real_cond_Ioi_of_le (by norm_num) (by norm_num), compl_Ioi,
    real_cond_Iic (by norm_num) (by norm_num)]
  norm_num

theorem relevance_moreThan100 : relevance success (Ioi 100) = Real.log 6 :=
  congrArg Real.log toReal_bayesFactor_moreThan100

theorem relevance_moreThan110 : relevance success (Ioi 110) = Real.log 12 :=
  congrArg Real.log toReal_bayesFactor_moreThan110

theorem relevance_moreThan100_toward110 :
    relevance ⟨Ioi 110, .of_discrete, prior⟩ (Ioi 100) = Real.log 11 := by
  rw [relevance, toReal_bayesFactor, real_cond_Ioi_of_le (by norm_num) (by norm_num),
    compl_Ioi, real_cond_Iic (by norm_num) (by norm_num)]
  norm_num

/-! ### Assertability

Assertability is stochastic: with probability `ρ` the hearer gives the utterance a pragmatic
interpretation, enriching *more than n* with an implicature *not more than c*, and otherwise
a semantic one, so the utterance is felicitously assertable iff it is true on the
interpretation drawn. The joint of registrations and interpretations is the product of the
prior with the hearer's coin. -/

/-- How the hearer resolves the utterance. -/
inductive Interpretation where
  | pragmatic | semantic
  deriving DecidableEq, Fintype

instance : MeasurableSpace Interpretation := ⊤

/-- The hearer interprets pragmatically with probability `ρ` and semantically otherwise. -/
noncomputable abbrev hearer (ρ : I) : Measure Interpretation := Ber(.pragmatic, .semantic, ρ)

/-- The readings of *more than n* whose implicature is *not more than c*. -/
def reading (n c : ℕ) : Interpretation → Set ℕ
  | .pragmatic => Ioc n c
  | .semantic => Ioi n

/-- The assertability model pairs registrations with the hearer's interpretation under the
prior and the hearer's coin, and lifts the goal along the registration. -/
noncomputable abbrev assertability (ρ : I) : Context (ℕ × Interpretation) :=
  ⟨Prod.fst ⁻¹' Ioi 120, measurable_fst .of_discrete, prior.prod (hearer ρ)⟩

/-- *more than n* is felicitously assertable iff it is true on the interpretation drawn. -/
def assertable (n c : ℕ) : Set (ℕ × Interpretation) := {p | p.1 ∈ reading n c p.2}

theorem real_cond_assertable (ρ : I) (s : Set ℕ) (n c : ℕ) :
    ((prior.prod (hearer ρ))[|Prod.fst ⁻¹' s]).real (assertable n c) =
      (prior[|s]).real (Ioc n c) * ρ + (prior[|s]).real (Ioi n) * (1 - ρ) := by
  rw [cond_prod_preimage_fst, assertable,
    Measure.prod_real_fibers _ _ fun _ ↦ .of_discrete,
    Fintype.sum_eq_add .pragmatic .semantic (by decide) (by rintro (_ | _) <;> simp)]
  simp [reading]

theorem real_assertable_of_failure (ρ : I) (n : ℕ) {c : ℕ} (hc : 120 ≤ c) :
    ((assertability ρ).prior[|(assertability ρ).topicᶜ]).real (assertable n c) =
      (prior[|Iic 120]).real (Ioi n) := by
  have hset : Iic 120 ∩ Ioc n c = Iic 120 ∩ Ioi n :=
    inter_congr_left (fun x hx ↦ ⟨hx.2, (hx.1 : x ≤ 120).trans hc⟩) fun _ hx ↦ hx.2.1
  have h : (prior[|Iic 120]).real (Ioc n c) = (prior[|Iic 120]).real (Ioi n) := by
    simp only [cond_real_apply _ .of_discrete, hset]
  rw [← preimage_compl, real_cond_assertable, compl_Ioi, h]
  ring

theorem real_assertable_of_success (ρ : I) {n c : ℕ} (hn : n ≤ 120) (hnc : n ≤ c) :
    ((assertability ρ).prior[|(assertability ρ).topic]).real (assertable n c) =
      1 - ρ * (prior[|Ioi 120]).real (Ioi c) := by
  have hdiff := measureReal_sdiff_add_inter (μ := prior[|Ioi 120]) (s := Ioi n)
    (t := Ioi c) .of_discrete
  rw [Ioi_sdiff_Ioi, Ioi_inter_Ioi, max_eq_right hnc] at hdiff
  rw [real_cond_assertable, real_cond_Ioi_of_le hn (by norm_num)] at *
  linear_combination (ρ : ℝ) * hdiff

theorem toReal_bayesFactor_assertable (ρ : I) {n c : ℕ} (hn : n ≤ 120) (hc : 120 ≤ c) :
    (bayesFactor (assertability ρ) (assertable n c)).toReal =
      (bayesFactor success (Ioi n)).toReal * (1 - ρ * (prior[|Ioi 120]).real (Ioi c)) := by
  rw [toReal_bayesFactor, toReal_bayesFactor, real_assertable_of_success ρ hn (hn.trans hc),
    real_assertable_of_failure ρ n hc, real_cond_Ioi_of_le hn (by norm_num),
    compl_Ioi]
  ring

theorem bayesFactor_assertability_zero (n c : ℕ) :
    bayesFactor (assertability 0) (assertable n c) = bayesFactor success (Ioi n) := by
  have h (s : Set ℕ) : (prior.prod (hearer 0))[|Prod.fst ⁻¹' s] (assertable n c) =
      prior[|s] (Ioi n) := by
    rw [← measureReal_eq_measureReal_iff, real_cond_assertable]
    simp
  rw [bayesFactor_def, bayesFactor_def, ← preimage_compl, h, h]

theorem toReal_bayesFactor_assertable_moreThan100 (ρ : I) {c : ℕ} (hc : 120 ≤ c)
    (hc' : c ≤ 200) :
    (bayesFactor (assertability ρ) (assertable 100 c)).toReal =
      6 * (1 - ρ * ((200 - (c : ℝ)) / 80)) := by
  rw [toReal_bayesFactor_assertable ρ (by norm_num) hc, toReal_bayesFactor_moreThan100,
    real_cond_Ioi hc hc']
  norm_num

theorem toReal_bayesFactor_assertable_moreThan110 (ρ : I) :
    (bayesFactor (assertability ρ) (assertable 110 120)).toReal = 12 * (1 - ρ) := by
  rw [toReal_bayesFactor_assertable ρ (by norm_num) le_rfl, toReal_bayesFactor_moreThan110,
    real_cond_Ioi le_rfl (by norm_num)]
  norm_num

theorem relevance_assertable_moreThan100 (ρ : I) :
    relevance (assertability ρ) (assertable 100 150) = Real.log (6 * (1 - 5 / 8 * ρ)) := by
  rw [relevance, toReal_bayesFactor_assertable_moreThan100 ρ (by norm_num) (by norm_num)]
  ring_nf

theorem relevance_assertable_moreThan110 (ρ : I) :
    relevance (assertability ρ) (assertable 110 120) = Real.log (12 * (1 - ρ)) :=
  congrArg Real.log (toReal_bayesFactor_assertable_moreThan110 ρ)

private theorem bayesFactor_assertable_ne_top (ρ : I) {n c : ℕ} (hn : n < 120) (hc : 120 ≤ c) :
    bayesFactor (assertability ρ) (assertable n c) ≠ ⊤ := by
  refine bayesFactor_ne_top ((measureReal_ne_zero_iff).mp ?_)
  rw [real_assertable_of_failure ρ n hc, real_cond_Iic hn.le (by norm_num)]
  exact div_ne_zero (sub_pos.2 (by exact_mod_cast hn)).ne' (by norm_num)

theorem posRelevant_assertable_moreThan100 (ρ : I) :
    posRelevant (assertability ρ) (assertable 100 150) := by
  rw [posRelevant_iff_one_lt_toReal (bayesFactor_assertable_ne_top ρ (by norm_num)
    (by norm_num)), toReal_bayesFactor_assertable_moreThan100 ρ (by norm_num) (by norm_num)]
  linarith [le_one ρ]

theorem posRelevant_assertable_moreThan110_iff (ρ : I) :
    posRelevant (assertability ρ) (assertable 110 120) ↔ (ρ : ℝ) < 11 / 12 := by
  rw [posRelevant_iff_one_lt_toReal (bayesFactor_assertable_ne_top ρ (by norm_num)
    le_rfl), toReal_bayesFactor_assertable_moreThan110]
  constructor <;> intro <;> linarith

/-! ### The reversal -/

theorem bayesFactor_assertable_lt_iff_of_le (ρ : I) {c : ℕ} (hc : 120 ≤ c) (hc' : c ≤ 200) :
    bayesFactor (assertability ρ) (assertable 110 120) <
        bayesFactor (assertability ρ) (assertable 100 c) ↔ 80 < ρ * ((c : ℝ) - 40) := by
  rw [← ENNReal.toReal_lt_toReal (bayesFactor_assertable_ne_top _ (by norm_num)
    le_rfl) (bayesFactor_assertable_ne_top _ (by norm_num) hc),
    toReal_bayesFactor_assertable_moreThan110, toReal_bayesFactor_assertable_moreThan100 ρ hc hc']
  constructor <;> intro <;> linarith

theorem bayesFactor_assertable_lt_iff (ρ : I) :
    bayesFactor (assertability ρ) (assertable 110 120) <
        bayesFactor (assertability ρ) (assertable 100 150) ↔ 8 / 11 < (ρ : ℝ) := by
  rw [bayesFactor_assertable_lt_iff_of_le ρ (by norm_num) (by norm_num), Nat.cast_ofNat]
  constructor <;> intro <;> linarith

theorem bayesFactor_assertable_moreThan100_tens_le (ρ : I) :
    bayesFactor (assertability ρ) (assertable 100 110) ≤
      bayesFactor (assertability ρ) (assertable 110 120) := by
  have hS : ((assertability ρ).prior[|(assertability ρ).topic]).real (assertable 100 110) =
      1 - ρ := by
    rw [real_assertable_of_success ρ (by norm_num) (by norm_num),
      real_cond_Ioi_of_le (by norm_num) (by norm_num), mul_one]
  have hF : ((assertability ρ).prior[|(assertability ρ).topicᶜ]).real (assertable 100 110) =
      ρ / 12 + (1 - ρ) / 6 := by
    rw [← preimage_compl, real_cond_assertable, compl_Ioi, cond_real_apply _ .of_discrete,
      inter_eq_right.mpr (Ioc_subset_Iic_self.trans (Iic_subset_Iic.2 (by norm_num))),
      real_prior_Ioc (by norm_num) (by norm_num),
      real_prior_Iic (by norm_num), real_cond_Iic (by norm_num) (by norm_num)]
    ring
  have hpos : 0 < (ρ : ℝ) / 12 + (1 - ρ) / 6 := by linarith [le_one ρ, nonneg ρ]
  rw [← ENNReal.toReal_le_toReal (bayesFactor_ne_top ((measureReal_ne_zero_iff).mp
    (hF ▸ hpos.ne'))) (bayesFactor_assertable_ne_top _ (by norm_num) le_rfl),
    toReal_bayesFactor, hS, hF, toReal_bayesFactor_assertable_moreThan110, div_le_iff₀ hpos]
  nlinarith [le_one ρ, nonneg ρ]

theorem reversal_on_scales (ρ : I) :
    ¬ bayesFactor (assertability ρ) (assertable 110 120) <
        bayesFactor (assertability ρ) (assertable 100 110) ∧
      (bayesFactor (assertability ρ) (assertable 110 120) <
          bayesFactor (assertability ρ) (assertable 100 125) ↔ 16 / 17 < (ρ : ℝ)) ∧
      (bayesFactor (assertability ρ) (assertable 110 120) <
          bayesFactor (assertability ρ) (assertable 100 200) ↔ 1 / 2 < (ρ : ℝ)) := by
  refine ⟨not_lt.2 (bayesFactor_assertable_moreThan100_tens_le ρ), ?_, ?_⟩ <;>
    rw [bayesFactor_assertable_lt_iff_of_le ρ (by norm_num) (by norm_num), Nat.cast_ofNat] <;>
    constructor <;> intro <;> linarith

/-! ### Granularity -/

/-- The pragmatic reading of *more than n* on the scales `W` negates *more than m* for every
numeral `m` above `n` at least as round as `n` on them. -/
def enrichment (W : Finset ℕ) (n : ℕ) : Set ℕ :=
  Ioi n \ ⋃ m ∈ {m : ℕ | n < m ∧ AtLeastAsRound (OnScale W) (n : ℤ) m}, Ioi m

theorem enrichment_eq {W : Finset ℕ} (hW : 0 ∉ W) {n w : ℕ} (hw : w = scaleLcm W n) :
    enrichment W n = Ioc n (n + w) := by
  have h := isLeast_atLeastAsRound_onScale hW n
  rw [← hw] at h
  rw [enrichment, ← Ioi_sdiff_Ioi]
  congr 1
  ext x
  simp only [mem_iUnion, mem_Ioi, exists_prop]
  constructor
  · rintro ⟨m, ⟨hnm, hr⟩, hx⟩
    have := h.2 ⟨Int.ofNat_lt.2 hnm, hr⟩
    omega
  · intro hx
    refine ⟨n + w, ⟨?_, by exact_mod_cast h.1.2⟩, hx⟩
    have := h.1.1
    omega

theorem enrichment_singleton {w n : ℕ} (hw : 0 < w) (h : w ∣ n) :
    enrichment {w} n = Ioc n (n + w) :=
  enrichment_eq (fun h0 ↦ hw.ne (Finset.mem_singleton.1 h0)) (by
    rw [scaleLcm, Finset.filter_true_of_mem fun x hx ↦
        Finset.mem_singleton.1 hx ▸ Int.natCast_dvd_natCast.2 h,
      Finset.lcm_singleton, id, normalize_eq])

/-- The aligned decimal scales of units, tens, hundreds and thousands. -/
def decimal : Finset ℕ := {1000, 100, 10, 1}

theorem enrichment_decimal :
    enrichment decimal 110 = Ioc 110 120 ∧ enrichment decimal 100 = Ioc 100 200 :=
  ⟨enrichment_eq (w := 10) (by decide) (by decide),
    enrichment_eq (w := 100) (by decide) (by decide)⟩

private theorem hasKness_one_of_entirelyRound {m : ℕ} (h : Cummins2015.EntirelyRound m) :
    HasKness 1 m := by
  have := Finset.ext_iff.1 (Finset.eq_univ_of_card (profile (Kness.Holds 0) m) h) .ten
  simpa [Kness.Holds] using this

private theorem not_hasKness_one {m : ℕ} (h₁ : 100 < m) (h₂ : m < 200) : ¬ HasKness 1 m := by
  rintro ⟨b, d, hd, hd9, rfl⟩
  rcases Nat.lt_or_ge b 3 with hb | hb
  · interval_cases b <;> omega
  · have : 10 ^ 3 ≤ 10 ^ b := Nat.pow_le_pow_right (by norm_num) hb
    nlinarith

theorem isLeast_strongerAlternative (ctx : Cummins2015.Context) :
    IsLeast {m | Cummins2015.StrongerAlternative ctx 100 m} 200 ∧
      (ctx.granularity ≠ none → IsLeast {m | Cummins2015.StrongerAlternative ctx 110 m} 120) := by
  have h110 : ∀ m ∈ Finset.Ioo 110 120,
      Cummins2015.granularityLevel m ≠ Cummins2015.granularityLevel 110 := by
    decide +kernel
  refine ⟨⟨⟨by norm_num, by decide, .inr (by decide)⟩, fun m ⟨hm, hr, _⟩ ↦ ?_⟩, fun hg ↦
    ⟨⟨by norm_num, by decide, .inr (by decide)⟩, fun m ⟨hm, _, hl⟩ ↦ ?_⟩⟩
  · by_contra h
    refine not_hasKness_one hm (not_le.1 h) (hasKness_one_of_entirelyRound ?_)
    exact le_antisymm (Cummins2015.roundness_le_four m)
      (by simpa [show Cummins2015.roundness 100 = 4 by decide] using hr)
  · by_contra h
    exact h110 m (Finset.mem_Ioo.2 ⟨hm, not_le.1 h⟩) (hl.resolve_left hg)

/-! ### The paper's rate -/

/-- The paper's illustrative enrichment rate of nine in ten. -/
noncomputable abbrev nineTenths : I := ⟨9 / 10, by norm_num, by norm_num⟩

theorem relevance_reversal :
    relevance success (Ioi 100) < relevance success (Ioi 110) ∧
      relevance (assertability nineTenths) (assertable 110 120) <
        relevance (assertability nineTenths) (assertable 100 150) := by
  refine ⟨?_, relevance_lt_relevance ?_
    (bayesFactor_assertable_ne_top _ (by norm_num) (by norm_num))
    ((bayesFactor_assertable_lt_iff _).mpr (by norm_num [nineTenths]))⟩
  · rw [relevance_moreThan100, relevance_moreThan110]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  · exact (ENNReal.toReal_ne_zero.mp (by
      rw [toReal_bayesFactor_assertable_moreThan110]; norm_num [nineTenths])).1

theorem relevance_assertable_moreThan100_nineTenths :
    relevance (assertability nineTenths) (assertable 100 150) = Real.log (21 / 8) := by
  rw [relevance_assertable_moreThan100]
  norm_num [nineTenths]

theorem relevance_assertable_moreThan110_nineTenths :
    relevance (assertability nineTenths) (assertable 110 120) = Real.log (6 / 5) := by
  rw [relevance_assertable_moreThan110]
  norm_num [nineTenths]

end CumminsFranke2021
