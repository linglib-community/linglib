module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Linglib.Phonology.HarmonicGrammar.MaxEnt
public import Linglib.Phonology.HarmonicGrammar.Noise
public import Linglib.Core.Probability.Choice.RandomUtility
public import Linglib.Data.Examples.Flemming2021
public import Linglib.Data.Experiments.Flemming2021

/-!
# Flemming (2021): Comparing MaxEnt and Noisy Harmonic Grammar

Flemming compares the stochastic harmonic grammars as random utility models (Train), in which noise
is added to the candidates' harmonies: Gumbel noise for MaxEnt (Goldwater and Johnson, Hayes and
Wilson), normal noise on the constraint weights for Noisy Harmonic Grammar (Boersma and Pater), and
normal noise on the candidates for normal MaxEnt (Hayes). Between two candidates the probability of
the first is a function of their harmony difference (7), so its logit is the harmony difference in
MaxEnt (10) and its probit the harmony difference over the noise standard deviation `σ_d` in the
normal models (16), (18). That deviation is the constant `√(2v)` in normal MaxEnt, but in NHG it
grows with the violation difference of the two candidates (14). Adding a violation therefore
changes the MaxEnt logit by the constraint's weight (§7.1), while the change in the NHG probit
depends on the harmony difference before the change (38).

The test case is Smith and Pater's French schwa data (19): eight contexts crossing an underlying
schwa or none, a preceding C or CC, and a following monosyllable or disyllable, evaluated by
NoSchwa, \*CCC, \*Clash, Max, Dep and \*Cluster (20)–(28).

## Main results

* `choiceProb_pi_gumbelMeasure_eq_maxEnt`, `logit_choiceProb_pi_gumbelMeasure`: MaxEnt is the
  Gumbel random utility model, with logit (10).
* `probit_weightNoiseChoiceProb`, `probit_choiceProb_pi_gaussianReal`: the probits (16) and (18).
* `probitChange_strictAnti`: the NHG probit gain falls with the initial harmony difference (§7.2).
* `diff_eq`: the difference tableaux (35), derived from the constraint definitions.
* `logit_following`, `logit_onset`, `logit_underlying`: MaxEnt's uniform logit differences
  (§7.1).
* `clash_gain_ordered`: NHG orders the probit gains 1-2 > 5-6 > 3-4 > 7-8 (§8.2).
* `onset_effect_larger_for_words`, `harmonyDiffRevised_onset`: the Max × \*CCC interaction in the
  observed rates, and the revised constraint \*CCC/iP that accounts for it (§8.3).
* `table45_variance_covariance`: in the three-candidate tableau (45) the NHG harmony differences
  have unequal variances and a nonzero covariance (§9).

## Implementation notes

* Candidates are `Fin 2`, `0` the schwa candidate and `1` the schwaless one, so that the
  substrate's `Real.logit_softmax_fin_two` is (10) directly; constraints are `Constraint.binary`
  predicates on the context's three features.
* The fitted weights of Tables 1 and 4 and the deviances of §8 are estimation results and are
  not formalized; the predictions are stated for arbitrary weights with the sign hypotheses the
  fits satisfy. Censored NHG (§7.3) has no closed form and is not formalized.
* `weightNoiseProb` takes the standard deviation `σ` of the weight noise, the paper's parameter,
  so the noise variance is `σ ^ 2`.
* The observed and fitted rates and the deviances of Table 2 are `Data/Experiments/Flemming2021`;
  `observedRate` reads the observed rates in hundredths, and the interaction is stated on odds
  ratios, the exponential of the logit differences MaxEnt predicts equal.

## References

* [flemming-2021]
* [smith-pater-2020]
* [boersma-pater-2016]
* [goldwater-johnson-2003]
* [hayes-wilson-2008]
* [hayes-2017]
* [train-2009]
* [mcfadden-1974]
-/

@[expose] public section

namespace Flemming2021

open Real OptimalityTheory HarmonicGrammar ProbabilityTheory MeasureTheory
open scoped NNReal

/-! ### Stochastic Harmonic Grammars as random utility models (§§4–5) -/

variable {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}

/-- MaxEnt is the Gumbel random utility model (§4). When the candidates' harmonies are perturbed by
independent standard Gumbel noise, the probability that `c` has the highest perturbed harmony is the
MaxEnt probability of (4), by McFadden's Lemma 1. -/
theorem choiceProb_pi_gumbelMeasure_eq_maxEnt [DecidableEq C] [MeasurableSpace C]
    [MeasurableSingletonClass C] (con : ConstraintSet C (Fin n))
    (w : Fin n → ℝ) (c : C) :
    choiceProb (Measure.pi fun c' ↦ gumbelMeasure (harmonyScore con w c') 1) c =
      maxEnt con.violations w {c} := by
  simp [choiceProb_pi_gumbelMeasure _ one_ne_zero c, maxEnt_singleton]

/-- Between two candidates the MaxEnt logit of the first is the harmony difference (10), since under
standard Gumbel noise the choice probability is the logistic function of the difference. -/
theorem logit_choiceProb_pi_gumbelMeasure (con : ConstraintSet (Fin 2) (Fin n)) (w : Fin n → ℝ) :
    logit (choiceProb (Measure.pi fun c ↦ gumbelMeasure (harmonyScore con w c) 1) 0).toReal =
      harmonyScore con w 0 - harmonyScore con w 1 := by
  rw [choiceProb_pi_gumbelMeasure_fin_two _ one_ne_zero, ENNReal.toReal_ofReal (sigmoid_pos _).le]
  simp

/-- Under noise of variance `v` on the weights, the probit of the first candidate is the harmony
difference over the standard deviation `σ_d` of its noise (16). -/
theorem probit_weightNoiseChoiceProb (con : ConstraintSet (Fin 2) (Fin n)) (w : Fin n → ℝ)
    {v : ℝ≥0} (hv : v ≠ 0) (hd : (con.violationDiff 0 1 : Fin n → ℝ) ≠ 0) :
    probit (weightNoiseChoiceProb con w v 0).toReal =
      (harmonyScore con w 0 - harmonyScore con w 1) /
        √(v * (con.violationDiff 0 1 ⬝ᵥ con.violationDiff 0 1 : ℝ)) := by
  rw [weightNoiseChoiceProb_fin_two con w v hv hd,
    ENNReal.toReal_ofReal (normalCDF_pos _).le, probit_normalCDF]

/-- Under independent noise of variance `v` on the candidates' harmonies, the probit of the first
candidate is the harmony difference over the constant `√(2v)` (18). -/
theorem probit_choiceProb_pi_gaussianReal (con : ConstraintSet (Fin 2) (Fin n)) (w : Fin n → ℝ)
    {v : ℝ≥0} (hv : v ≠ 0) :
    probit (choiceProb (Measure.pi fun c ↦ gaussianReal (harmonyScore con w c) v) 0).toReal =
      (harmonyScore con w 0 - harmonyScore con w 1) / √(2 * v) := by
  rw [choiceProb_pi_gaussianReal _ hv, ENNReal.toReal_ofReal (normalCDF_nonneg _),
    probit_normalCDF]

/-! ### The effect of a change in violations on the NHG probit (§7.2) -/

/-- `probitChange h Δh σ σ'` is the change in the NHG probit when the harmony difference `h`
changes by `Δh` and the noise standard deviation from `σ` to `σ'` (38a). -/
noncomputable def probitChange (h Δh σ σ' : ℝ) : ℝ := (h + Δh) / σ' - h / σ

/-- The change decomposes into a term proportional to the initial harmony difference and the
rescaled harmony change (38b). -/
theorem probitChange_eq (h Δh : ℝ) {σ σ' : ℝ} (hσ : 0 < σ) (hσ' : 0 < σ') :
    probitChange h Δh σ σ' = h * (σ - σ') / (σ * σ') + Δh / σ' := by
  unfold probitChange
  field_simp
  ring

/-- When the change enlarges the noise, `σ < σ'`, the probit gain decreases with the initial
harmony difference: the same change in violations has a smaller effect the higher the schwa
candidate already stands (§7.2). -/
theorem probitChange_strictAnti (Δh : ℝ) {σ σ' : ℝ} (hσ : 0 < σ) (hσ' : σ < σ') :
    StrictAnti (probitChange · Δh σ σ') := by
  intro h₁ h₂ hlt
  have hσ'0 : 0 < σ' := hσ.trans hσ'
  have key : probitChange h₂ Δh σ σ' - probitChange h₁ Δh σ σ' =
      (h₂ - h₁) * (1 / σ' - 1 / σ) := by
    unfold probitChange
    field_simp
    ring
  have hneg : 1 / σ' - 1 / σ < 0 := sub_neg.2 (one_div_lt_one_div_of_lt hσ hσ')
  have := mul_neg_of_pos_of_neg (sub_pos.2 hlt) hneg
  linarith

/-! ### French schwa (§6): the contexts of (19) and the constraints of (20)–(23) -/

/-- A context of (19). -/
structure Context where
  underlying : Underlying
  onset : Onset
  following : Following
  deriving DecidableEq, Repr

/-- Each tableau has two candidates, `0` realizing the schwa and `1` not. -/
abbrev Cand := Fin 2

/-- NoSchwa (20) assigns one violation to a schwa in the output. -/
def noSchwa (_ : Context) : Constraint Cand := .binary (· = 0)

/-- \*CCC (21) penalizes the three-consonant cluster the schwaless candidate forms after two
consonants. -/
def starCCC (x : Context) : Constraint Cand := .binary fun c ↦ c = 1 ∧ x.onset = .cc

/-- \*Clash (23) penalizes the schwaless candidate when a stressed monosyllable then follows a
stressed syllable. -/
def starClash (x : Context) : Constraint Cand :=
  .binary fun c ↦ c = 1 ∧ x.following = .monosyllable

/-- Max penalizes the schwaless candidate for deleting an underlying schwa. -/
def maxSchwa (x : Context) : Constraint Cand := .binary fun c ↦ c = 1 ∧ x.underlying = .schwa

/-- Dep penalizes the schwa candidate for inserting a schwa where there is none underlyingly. -/
def depSchwa (x : Context) : Constraint Cand := .binary fun c ↦ c = 0 ∧ x.underlying = .zero

/-- \*Cluster (22) penalizes a two-consonant cluster, which the schwaless candidate always forms and
the schwa candidate forms after two consonants. -/
def starCluster (x : Context) : Constraint Cand := .binary fun c ↦ c = 1 ∨ x.onset = .cc

/-- [smith-pater-2020]'s constraint set in the order of (35). -/
def constraints (x : Context) : ConstraintSet Cand (Fin 6)
  | 0 => noSchwa x
  | 1 => starCCC x
  | 2 => starClash x
  | 3 => maxSchwa x
  | 4 => depSchwa x
  | 5 => starCluster x

/-- The difference tableau records the schwa candidate's violations minus the schwaless candidate's,
signed negatively as in the paper. -/
def diff (x : Context) (k : Fin 6) : ℤ := (constraints x k 1 : ℤ) - constraints x k 0

/-- The difference tableaux of (35), derived from the constraint definitions. -/
theorem diff_eq : ∀ u o f, List.ofFn (diff ⟨u, o, f⟩) =
    match u, o, f with
    | .zero, .c, .disyllable => [-1, 0, 0, 0, -1, 1]
    | .zero, .c, .monosyllable => [-1, 0, 1, 0, -1, 1]
    | .zero, .cc, .disyllable => [-1, 1, 0, 0, -1, 0]
    | .zero, .cc, .monosyllable => [-1, 1, 1, 0, -1, 0]
    | .schwa, .c, .disyllable => [-1, 0, 0, 1, 0, 1]
    | .schwa, .c, .monosyllable => [-1, 0, 1, 1, 0, 1]
    | .schwa, .cc, .disyllable => [-1, 1, 0, 1, 0, 0]
    | .schwa, .cc, .monosyllable => [-1, 1, 1, 1, 0, 0] := by
  decide

/-- `hə − h∅`, the harmony difference of a context under weights `w`. -/
noncomputable def harmonyDiff (x : Context) (w : Fin 6 → ℝ) : ℝ :=
  harmonyScore (constraints x) w 0 - harmonyScore (constraints x) w 1

/-- The harmony difference is the weighted difference tableau, as in (29)–(34). -/
theorem harmonyDiff_eq_sum (x : Context) (w : Fin 6 → ℝ) :
    harmonyDiff x w = ∑ k, w k * diff x k := by
  simp only [harmonyDiff, harmonyScore_sub, dotProduct, ConstraintSet.violationDiff, diff,
    Int.cast_sub, Int.cast_natCast, mul_sub, Finset.sum_sub_distrib]
  ring

private theorem harmonyDiff_closed (u : Underlying) (o : Onset) (f : Following) (w : Fin 6 → ℝ) :
    harmonyDiff ⟨u, o, f⟩ w = -w 0 + (if o = .cc then w 1 else 0)
      + (if f = .monosyllable then w 2 else 0)
      + (if u = .schwa then w 3 else 0) - (if u = .zero then w 4 else 0)
      + (if o = .c then w 5 else 0) := by
  rw [harmonyDiff_eq_sum, Fin.sum_univ_six]
  cases u <;> cases o <;> cases f <;>
    simp [diff, constraints, noSchwa, starCCC, starClash, maxSchwa, depSchwa, starCluster] <;> ring

/-! ### MaxEnt predicts uniform logit differences (§7.1) -/

/-- Adding the \*Clash violation, `–sś` to `–ś`, raises the harmony difference by the weight of
\*Clash whatever the other features. -/
theorem harmonyDiff_following (u : Underlying) (o : Onset) (w : Fin 6 → ℝ) :
    harmonyDiff ⟨u, o, .monosyllable⟩ w - harmonyDiff ⟨u, o, .disyllable⟩ w = w 2 := by
  rw [harmonyDiff_closed, harmonyDiff_closed]; simp

/-- Two preceding consonants add a \*CCC and remove a \*Cluster violation difference. -/
theorem harmonyDiff_onset (u : Underlying) (f : Following) (w : Fin 6 → ℝ) :
    harmonyDiff ⟨u, .cc, f⟩ w - harmonyDiff ⟨u, .c, f⟩ w = w 1 - w 5 := by
  rw [harmonyDiff_closed, harmonyDiff_closed]; simp; ring

/-- An underlying schwa adds a Max and removes a Dep violation difference. -/
theorem harmonyDiff_underlying (o : Onset) (f : Following) (w : Fin 6 → ℝ) :
    harmonyDiff ⟨.schwa, o, f⟩ w - harmonyDiff ⟨.zero, o, f⟩ w = w 3 + w 4 := by
  rw [harmonyDiff_closed, harmonyDiff_closed]; simp

/-- The MaxEnt probability of the schwa candidate. -/
noncomputable def maxEntProb (x : Context) (w : Fin 6 → ℝ) : ℝ :=
  (maxEnt (constraints x).violations w).real {0}

theorem logit_maxEntProb (x : Context) (w : Fin 6 → ℝ) :
    logit (maxEntProb x w) = harmonyDiff x w := by
  rw [maxEntProb, maxEnt_real_singleton, logit_softmax_fin_two]; rfl

/-- MaxEnt predicts the same logit difference, the weight of \*Clash, across the four pairs
1-2, 3-4, 5-6, 7-8. -/
theorem logit_following (u : Underlying) (o : Onset) (w : Fin 6 → ℝ) :
    logit (maxEntProb ⟨u, o, .monosyllable⟩ w) - logit (maxEntProb ⟨u, o, .disyllable⟩ w) =
      w 2 := by
  rw [logit_maxEntProb, logit_maxEntProb, harmonyDiff_following]

/-- … and the same logit difference across the pairs 1-3, 2-4, 5-7, 6-8. -/
theorem logit_onset (u : Underlying) (f : Following) (w : Fin 6 → ℝ) :
    logit (maxEntProb ⟨u, .cc, f⟩ w) - logit (maxEntProb ⟨u, .c, f⟩ w) = w 1 - w 5 := by
  rw [logit_maxEntProb, logit_maxEntProb, harmonyDiff_onset]

/-- … and across the pairs 1-5, 2-6, 3-7, 4-8. -/
theorem logit_underlying (o : Onset) (f : Following) (w : Fin 6 → ℝ) :
    logit (maxEntProb ⟨.schwa, o, f⟩ w) - logit (maxEntProb ⟨.zero, o, f⟩ w) = w 3 + w 4 := by
  rw [logit_maxEntProb, logit_maxEntProb, harmonyDiff_underlying]

/-! ### NHG predicts context-dependent probit differences (§7.2, §8.2) -/

/-- The NHG probability of the schwa candidate under weight noise of standard deviation `σ`. -/
noncomputable def weightNoiseProb (x : Context) (w : Fin 6 → ℝ) (σ : ℝ) : ℝ :=
  (weightNoiseChoiceProb (constraints x) w (.mk (σ ^ 2) (sq_nonneg σ)) 0).toReal

/-- The squared length of the violation difference (37) is the number of differing constraints, 4
with the \*Clash difference and 3 without (Table 3). -/
theorem dotProduct_violationDiff_self (x : Context) :
    ((constraints x).violationDiff 0 1 ⬝ᵥ (constraints x).violationDiff 0 1 : ℝ) =
      if x.following = .monosyllable then 4 else 3 := by
  obtain ⟨u, o, f⟩ := x
  rw [dotProduct, Fin.sum_univ_six]
  cases u <;> cases o <;> cases f <;>
    simp [ConstraintSet.violationDiff, constraints, noSchwa, starCCC, starClash, maxSchwa,
      depSchwa, starCluster] <;> norm_num

/-- The NHG probit of the schwa candidate is its harmony difference over `σ_d` (36). -/
theorem probit_weightNoiseProb (x : Context) (w : Fin 6 → ℝ) {σ : ℝ} (hσ : 0 < σ) :
    probit (weightNoiseProb x w σ) =
      harmonyDiff x w / (σ * √(if x.following = .monosyllable then 4 else 3)) := by
  have hd : ((constraints x).violationDiff 0 1 : Fin 6 → ℝ) ≠ 0 := fun h ↦ by
    have := dotProduct_violationDiff_self x
    rw [h, zero_dotProduct] at this
    split_ifs at this <;> norm_num at this
  rw [weightNoiseProb, probit_weightNoiseChoiceProb _ _ (by simp [← NNReal.coe_eq_zero, hσ.ne']) hd,
    dotProduct_violationDiff_self, NNReal.coe_mk, Real.sqrt_mul (sq_nonneg σ),
    Real.sqrt_sq hσ.le]
  rfl

/-- The probit gain from the \*Clash violation is (38a) with `Δh` the weight of \*Clash, `σ_d = σ√3`
and `σ_d' = 2σ`. -/
theorem probit_gain_following (u : Underlying) (o : Onset) (w : Fin 6 → ℝ) {σ : ℝ}
    (hσ : 0 < σ) :
    probit (weightNoiseProb ⟨u, o, .monosyllable⟩ w σ) -
        probit (weightNoiseProb ⟨u, o, .disyllable⟩ w σ) =
      probitChange (harmonyDiff ⟨u, o, .disyllable⟩ w) (w 2) (σ * √3) (2 * σ) := by
  rw [probit_weightNoiseProb _ _ hσ, probit_weightNoiseProb _ _ hσ, probitChange,
    ← harmonyDiff_following u o w]
  simp only [ite_true, ite_false, reduceCtorEq]
  rw [show √(4 : ℝ) = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  ring

/-- With positive weights and the Max and Dep effect below the \*CCC one, the initial harmony
differences of the four \*Clash pairs are ordered 1 < 5 < 3 < 7, so NHG predicts their probit gains
ordered 1-2 > 5-6 > 3-4 > 7-8, where the data show the same gain in three of the four (§8.2). -/
theorem clash_gain_ordered (w : Fin 6 → ℝ) {σ : ℝ} (hσ : 0 < σ) (hw : 0 < w 3 + w 4)
    (hw' : w 3 + w 4 < w 1 - w 5) :
    let gain u o := probit (weightNoiseProb ⟨u, o, .monosyllable⟩ w σ) -
      probit (weightNoiseProb ⟨u, o, .disyllable⟩ w σ)
    gain .schwa .c < gain .zero .c ∧ gain .zero .cc < gain .schwa .c ∧
      gain .schwa .cc < gain .zero .cc := by
  intro gain
  have hanti := probitChange_strictAnti (w 2) (mul_pos hσ (Real.sqrt_pos.2 (by norm_num)))
    (show σ * √3 < 2 * σ by
      rw [mul_comm]
      exact mul_lt_mul_of_pos_right (Real.sqrt_lt' (by norm_num) |>.2 (by norm_num)) hσ)
  have h15 := harmonyDiff_underlying .c .disyllable w
  have h13 := harmonyDiff_onset .zero .disyllable w
  have h37 := harmonyDiff_underlying .cc .disyllable w
  simp only [gain, probit_gain_following _ _ _ hσ]
  exact ⟨hanti (by linarith), hanti (by linarith), hanti (by linarith)⟩

/-- For the pairs differing in the preceding consonants, `σ_d` is unchanged, so the NHG probit gain
is the rescaled harmony change (41): the same for words and clitics, larger before a monosyllable
than before a disyllable. -/
theorem probit_gain_onset (u : Underlying) (f : Following) (w : Fin 6 → ℝ) {σ : ℝ}
    (hσ : 0 < σ) :
    probit (weightNoiseProb ⟨u, .cc, f⟩ w σ) - probit (weightNoiseProb ⟨u, .c, f⟩ w σ) =
      (w 1 - w 5) / (σ * √(if f = .monosyllable then 4 else 3)) := by
  rw [probit_weightNoiseProb _ _ hσ, probit_weightNoiseProb _ _ hσ, ← sub_div,
    harmonyDiff_onset]

/-! ### The observed rates (Table 2) and the revised constraint set (§8.3) -/

/-- The observed rate of a context, in hundredths. -/
def observedRate (x : Context) : ℕ :=
  (schwaRates x.underlying x.onset x.following).observed.hundredths.toNat

/-- The schwa is pronounced more often before a monosyllable in every pair, as every model with a
positive \*Clash weight predicts. -/
theorem observedRate_following :
    ∀ u o, observedRate ⟨u, o, .disyllable⟩ < observedRate ⟨u, o, .monosyllable⟩ := by
  decide

/-- In MaxEnt a positive \*Clash weight raises the schwa's probability. -/
theorem maxEntProb_following_lt (u : Underlying) (o : Onset) (w : Fin 6 → ℝ) (hw : 0 < w 2) :
    maxEntProb ⟨u, o, .disyllable⟩ w < maxEntProb ⟨u, o, .monosyllable⟩ w := by
  simp only [maxEntProb, maxEnt_real_singleton, harmony_violations, softmax_fin_two]
  exact sigmoid_strictMono
    (by have := harmonyDiff_following u o w; unfold harmonyDiff at this; linarith)

/-- The observed odds of the schwa. -/
def odds (x : Context) : ℚ := observedRate x / (100 - observedRate x)

/-- The effect of the preceding consonants is larger in words than in clitics (§8.2). The odds ratio
across \*CCC is larger with underlying `/∅/` than with `/ə/`, in both stress contexts. MaxEnt with
Smith & Pater's constraints predicts equal odds ratios (`logit_onset`); this is the Max × \*CCC
interaction that motivates \*CCC/iP. -/
theorem onset_effect_larger_for_words : ∀ f,
    odds ⟨.schwa, .cc, f⟩ / odds ⟨.schwa, .c, f⟩ < odds ⟨.zero, .cc, f⟩ / odds ⟨.zero, .c, f⟩ := by
  intro f
  cases f <;> simp only [odds, observedRate] <;> decide +kernel

/-- In the fits of Table 2 censored NHG fits best and MaxEnt next, normal MaxEnt worse, and NHG
worst. -/
theorem deviance_order :
    (deviances .censoredNhg).deviance.toRat < (deviances .maxEnt).deviance.toRat ∧
      (deviances .maxEnt).deviance.toRat < (deviances .normalMaxEnt).deviance.toRat ∧
      (deviances .normalMaxEnt).deviance.toRat < (deviances .nhg).deviance.toRat := by
  decide +kernel

/-- \*CCC/iP (§8.3) penalizes a three-consonant cluster within one intermediate phrase, which the
schwaless candidate forms after two consonants only in the word-final items. -/
def starCCCiP (x : Context) : Constraint Cand :=
  .binary fun c ↦ c = 1 ∧ x.onset = .cc ∧ x.underlying = .zero

/-- Max and Dep collapsed into one correspondence constraint (§8.3). -/
def corr (x : Context) : Constraint Cand :=
  .binary fun c ↦ (c = 1 ∧ x.underlying = .schwa) ∨ (c = 0 ∧ x.underlying = .zero)

/-- The revised constraint set of Table 4 is NoSchwa, \*CCC, \*CCC/iP, \*Clash, Max/Dep and
\*Cluster. -/
def revised (x : Context) : ConstraintSet Cand (Fin 6)
  | 0 => noSchwa x
  | 1 => starCCC x
  | 2 => starCCCiP x
  | 3 => starClash x
  | 4 => corr x
  | 5 => starCluster x

/-- `hə − h∅` under the revised constraint set. -/
noncomputable def harmonyDiffRevised (x : Context) (w : Fin 6 → ℝ) : ℝ :=
  harmonyScore (revised x) w 0 - harmonyScore (revised x) w 1

/-- With \*CCC/iP the effect of the preceding consonants on the harmony difference is larger in
words by the weight of \*CCC/iP, so a MaxEnt grammar can fit the interaction (§8.3). -/
theorem harmonyDiffRevised_onset (u : Underlying) (f : Following) (w : Fin 6 → ℝ) :
    harmonyDiffRevised ⟨u, .cc, f⟩ w - harmonyDiffRevised ⟨u, .c, f⟩ w =
      w 1 - w 5 + if u = .zero then w 2 else 0 := by
  simp only [harmonyDiffRevised, harmonyScore_sub, dotProduct, ConstraintSet.violationDiff,
    Fin.sum_univ_six]
  cases u <;> cases f <;>
    simp [revised, noSchwa, starCCC, starCCCiP, starClash, corr, starCluster] <;> ring

/-! ### Three candidates (§9): tableau (45) -/

/-- The tableau of (1), (3), (5) and (45) has the candidates `a`, `b`, `c` as `0`, `1`, `2`. -/
def tableCon : ConstraintSet (Fin 3) (Fin 3)
  | 0 => fun c ↦ if c = 0 then 1 else 0
  | 1 => fun c ↦ if c = 1 then 2 else if c = 2 then 1 else 0
  | 2 => fun c ↦ if c = 2 then 1 else 0

/-- The weights 15, 8, 8. -/
noncomputable def tableW : Fin 3 → ℝ
  | 0 => 15
  | 1 => 8
  | 2 => 8

/-- Candidates `b` and `c` have equal harmony, `−16`. -/
theorem table45_harmony :
    harmonyScore tableCon tableW 0 = -15 ∧ harmonyScore tableCon tableW 1 = -16 ∧
      harmonyScore tableCon tableW 2 = -16 := by
  simp [harmonyScore_eq_neg_sum, Fin.sum_univ_three, tableCon, tableW]; norm_num

/-- MaxEnt gives `a` the probability `e⁻¹⁵ / (e⁻¹⁵ + 2e⁻¹⁶) = 1 / (1 + 2e⁻¹)`, 0.58, and `b` and
`c` equal probabilities (5). -/
theorem table45_maxent :
    (maxEnt tableCon.violations tableW).real {0} = 1 / (1 + 2 * exp (-1)) ∧
      (maxEnt tableCon.violations tableW).real {1} =
        (maxEnt tableCon.violations tableW).real {2} := by
  obtain ⟨h0, h1, h2⟩ := table45_harmony
  simp only [maxEnt_real_singleton, harmony_violations]
  refine ⟨?_, by simp only [softmax, h1, h2]⟩
  simp only [softmax, Fin.sum_univ_three, h0, h1, h2]
  rw [show (-16 : ℝ) = -15 + -1 by norm_num, exp_add]
  field_simp
  ring

/-- Under weight noise of variance `v`, the harmony differences of `a` and of `c` from `b` have
variances `5v` and `2v` (14) and covariance `2v` (§9), so their joint law is not determined by the
harmonies. The paper computes by numerical integration that `b` and `c`, of equal harmony, then
receive the probabilities 0.260 and 0.141. -/
theorem table45_variance_covariance (v : ℝ≥0) :
    Var[fun η ↦ harmonyScore tableCon (tableW + η) 0 - harmonyScore tableCon (tableW + η) 1;
        weightNoise (Fin 3) v] = 5 * v ∧
      Var[fun η ↦ harmonyScore tableCon (tableW + η) 2 - harmonyScore tableCon (tableW + η) 1;
        weightNoise (Fin 3) v] = 2 * v ∧
      cov[fun η ↦ harmonyScore tableCon (tableW + η) 0 - harmonyScore tableCon (tableW + η) 1,
        fun η ↦ harmonyScore tableCon (tableW + η) 2 - harmonyScore tableCon (tableW + η) 1;
        weightNoise (Fin 3) v] = 2 * v := by
  rw [variance_harmonyScore_sub, variance_harmonyScore_sub, covariance_harmonyScore_sub]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [dotProduct, ConstraintSet.violationDiff, Fin.sum_univ_three, tableCon] <;> ring

end Flemming2021
