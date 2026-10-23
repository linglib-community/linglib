module

public import Linglib.Data.Experiments.BeltramaSoltBurnett2023
public import Linglib.Pragmatics.SocialMeaning.Persona
public import Linglib.Fragments.English.NumeralModifiers
public import Linglib.Semantics.Degree.Granularity
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.NormNum

/-!
# Beltrama, Solt and Burnett (2023): Context, Precision, and Social Perception: A Sociopragmatic Study

Two experiments crossed three variants of a duration, approximate *about fifty minutes*,
underspecified *fifty minutes* and precise *forty-nine minutes*, with four scenarios ranked by
their need for precision, and had the speaker rated on scales that reduce to Status, Solidarity
and anti-Solidarity. Precise speakers are rated above approximate ones on Status and
anti-Solidarity and below them on Solidarity, and the underspecified variant patterns with the
precise one on Status and with the approximate one on anti-Solidarity. The paper reads this in
two ways (pp. 828–829): the underspecified variant is a neutral zero point, so that precision and
approximation are separate indexical loci, or round numbers partake of both ends of a single
opposition.

## Main statements

* `borneOut_contrastField`, `borneOut_neutral`: both readings are borne out by the means of both
  experiments (p. 828), though on the opposition reading the precise and approximate variants are
  antipodal and each fits a single persona, while on the neutral reading they are separate loci
  (`separateLoci_neutral`) and each fits two personae.
* `not_needHypothesis`: no table of cell means that agrees with the cells Experiment 2 reports
  satisfies the hypothesis that raising the need for precision favors the more precise variant;
  the other reported interactions run as it predicts (`favors_exp1`, `favors_exp2`).
* `loadsMostOn_exp1`, `loadsMostOn_exp2_iff`: by maximal loading, the principal components
  recover the planned grouping of the scales in Experiment 1, and in Experiment 2 for every scale
  but *friendly*, which loads most on Status.

## Implementation notes

* Status, Solidarity and anti-Solidarity are read as the competence, warmth and anti-solidarity
  of `SocialMeaning.Dimension`.
* The neutral reading takes the paper's verdict on each comparison with the underspecified
  variant, counting the trend of Experiment 1 on Status as a difference, as the paper does
  (p. 818); no p-value is thresholded.
* The underspecified variant is ranked between the others in precision, being compatible with a
  precise and an imprecise interpretation (p. 809).
* The context hypothesis is stated over full tables of cell means, which the paper only plots
  (Figures 2–4, 9–11); the theorems hold of every table agreeing with the printed cells.

## References

* [beltrama-solt-burnett-2023]
* [beltrama-2018]
* [campbell-kibler-2011]
* [eckert-2008]
* [burnett-2019]
* [fiske-cuddy-glick-2007]
* [krifka-2007]
-/

@[expose] public section

namespace BeltramaSoltBurnett2023

open SocialMeaning Data.Experiments

/-! ### The variants -/

open Degree in
/-- The underspecified durations report the precise ones at the grain of ten minutes, each the
multiple of ten closest to it (p. 807). -/
theorem underspecified_eq_representative (e : Experiment) :
    ((stimuli e .underspecified).before : ℚ) =
        representative 10 ((stimuli e .precise).before : ℚ) ∧
      ((stimuli e .underspecified).after : ℚ) =
        representative 10 ((stimuli e .precise).after : ℚ) := by
  cases e <;> norm_num [stimuli, representative, round_eq, Int.floor_eq_iff]

/-- The numeral modifier an approximator is. -/
def Approximator.modifier : Approximator → Numerals.NumeralModifier
  | .about => English.NumeralModifiers.about
  | .around => English.NumeralModifiers.around

section Truth

open Degree

/-- Of a trip that takes the precise duration, the underspecified description is false read
literally, on the two-sided and on the lower-bounded meaning of the bare numeral (p. 807). -/
theorem precise_not_mem_underspecified (e : Experiment) :
    (stimuli e .precise).after ∉ Comparison.eq.interval (stimuli e .underspecified).after ∪
      Comparison.ge.interval (stimuli e .underspecified).after := by
  cases e <;> simp [stimuli, Comparison.interval_eq, Comparison.interval_ge]

open Semantics in
theorem precise_mem_approximate (e : Experiment) {a : Approximator}
    (ha : (stimuli e .approximate).afterApproximator = some a) {m : Modifier (Set ℕ)}
    (hr : m ∈ ⟦a.modifier⟧)
    (hne : m {(stimuli e .approximate).after} ≠ {(stimuli e .approximate).after}) :
    (stimuli e .precise).after ∈ m {(stimuli e .approximate).after} := by
  cases e <;> cases a <;> simp only [stimuli, reduceCtorEq, Option.some.injEq] at ha ⊢ <;>
    obtain ⟨y, rfl⟩ := hr <;> simp only [Modifier.pointwise_singleton, Set.mem_Icc] at hne ⊢ <;>
    refine ⟨?_, by omega⟩ <;>
    by_contra h <;> exact hne (by
      obtain rfl : y = 0 := by omega
      simp)

end Truth

/-! ### Two readings of the underspecified variant -/

/-- The dimension of social evaluation a composite score measures. -/
def Factor.dimension : Factor ≃ Dimension where
  toFun
    | .status => .competence
    | .solidarity => .warmth
    | .antiSolidarity => .antiSolidarity
  invFun
    | .competence => .status
    | .warmth => .solidarity
    | .antiSolidarity => .antiSolidarity
  left_inv f := by cases f <;> rfl
  right_inv d := by cases d <;> rfl

/-- The mean composite scores of an experiment. -/
def means (e : Experiment) : AssociationField Variant Dimension ℚ :=
  .of fun v d ↦ (ratings e v (Factor.dimension.symm d)).mean.toRat

/-- A sign field is borne out by an experiment when the means order every two variants that the
field orders. -/
def BorneOut (F : AssociationField Variant Dimension SignType) (e : Experiment) : Prop :=
  ∀ d v w, F v d < F w d → means e v d < means e w d

instance (F : AssociationField Variant Dimension SignType) (e : Experiment) :
    Decidable (BorneOut F e) :=
  inferInstanceAs (Decidable (∀ _ _ _, _))

/-- The precise and approximate variants are separate indexical loci when each indexes a
dimension the other does not. -/
def SeparateLoci (F : AssociationField Variant Dimension SignType) : Prop :=
  (∃ d, F .precise d ≠ 0 ∧ F .approximate d = 0) ∧ ∃ d, F .approximate d ≠ 0 ∧ F .precise d = 0

theorem SeparateLoci.not_antipodal {F : AssociationField Variant Dimension SignType}
    (h : SeparateLoci F) : ¬ F.Antipodal .precise .approximate := fun ha ↦ by
  obtain ⟨⟨d, hp, ha0⟩, -⟩ := h
  exact hp (by rw [ha, Pi.neg_apply, ha0, neg_zero])

/-- The underspecified variant is rated strictly between the precise and the approximate ones on
every dimension in both experiments (p. 827). -/
theorem underspecified_mem_uIoo (e : Experiment) (d : Dimension) :
    means e .underspecified d ∈ Set.uIoo (means e .precise d) (means e .approximate d) := by
  cases e <;> cases d <;>
    simp [means, ratings, Factor.dimension, Decimal.toRat, Set.uIoo] <;> norm_num

/-- On the opposition reading the variants are measured against the underspecified one, every
difference of means counting. -/
def contrastField (e : Experiment) : AssociationField Variant Dimension SignType :=
  ((means e).contrast .underspecified).signs

theorem antipodal_contrastField (e : Experiment) :
    (contrastField e).Antipodal .precise .approximate :=
  AssociationField.antipodal_signs_contrast_iff.2 fun d ↦ .inl (underspecified_mem_uIoo e d)

/-- Experiment 2 replicates the opposition of Experiment 1 (p. 825). -/
theorem contrastField_exp2 : contrastField .exp2 = contrastField .exp1 := by
  ext v d; revert v d; decide +kernel

theorem ground_contrastField_precise (e : Experiment) :
    (contrastField e).ground.indexes .precise = {.competent, .cold, .antiSolidary} := by
  cases e <;> decide +kernel

theorem ground_contrastField_approximate (e : Experiment) :
    (contrastField e).ground.indexes .approximate = {.incompetent, .warm, .solidary} := by
  rw [(antipodal_contrastField e).ground_indexes, ground_contrastField_precise]; decide

theorem complementary_contrastField (e : Experiment) :
    (contrastField e).ground.Complementary .precise .approximate :=
  (antipodal_contrastField e).complementary fun d ↦ by revert d; cases e <;> decide +kernel

theorem lift_contrastField_precise (e : Experiment) :
    (contrastField e).ground.lift .precise = {{.competent, .cold, .antiSolidary}} := by
  rw [(complementary_contrastField e).lift_eq_singleton, ground_contrastField_precise]

theorem borneOut_contrastField (e e' : Experiment) : BorneOut (contrastField e) e' := by
  have h : contrastField e = contrastField e' := by
    cases e <;> cases e' <;> simp [contrastField_exp2]
  exact h ▸ fun _ _ _ ↦ AssociationField.lt_of_signs_contrast_lt

/-- The direction of a verdict; a trend counts. -/
def Verdict.sign : Verdict → SignType
  | .higher | .trendHigher => 1
  | .lower => -1
  | .noDifference => 0

/-- On the neutral reading the underspecified variant is the zero point, and a variant indexes a
dimension in the direction of its reported difference from it (p. 828). -/
def neutral (e : Experiment) : AssociationField Variant Dimension SignType :=
  .of fun v d ↦ match v with
    | .precise => (verdicts e (Factor.dimension.symm d) .preciseUnderspecified).verdict.sign
    | .underspecified => 0
    | .approximate =>
      -(verdicts e (Factor.dimension.symm d) .underspecifiedApproximate).verdict.sign

theorem neutral_eq_zero_or_eq_contrastField (e : Experiment) (v : Variant) (d : Dimension) :
    neutral e v d = 0 ∨ neutral e v d = contrastField e v d := by
  revert v d; cases e <;> decide +kernel

/-- In both experiments the Status contrast is driven by approximation alone and the
anti-Solidarity contrast by precision alone (p. 828). -/
theorem separateLoci_neutral (e : Experiment) : SeparateLoci (neutral e) := by
  cases e <;> exact ⟨⟨.antiSolidarity, by decide +kernel⟩, ⟨.competence, by decide +kernel⟩⟩

theorem not_separateLoci_contrastField (e : Experiment) : ¬ SeparateLoci (contrastField e) :=
  fun h ↦ h.not_antipodal (antipodal_contrastField e)

theorem ground_neutral_precise :
    (neutral .exp2).ground.indexes .precise = {.cold, .antiSolidary} := by decide +kernel

theorem ground_neutral_approximate :
    (neutral .exp2).ground.indexes .approximate = {.incompetent, .warm} := by decide +kernel

theorem card_lift_neutral_precise : ((neutral .exp2).ground.lift .precise).card = 2 := by
  decide +kernel

theorem borneOut_neutral (e e' : Experiment) : BorneOut (neutral e) e' := by
  cases e <;> cases e' <;> decide +kernel

/-! ### Scenario modulation -/

/-- The favorable direction of a composite score; the anti-Solidarity scales measure low
solidarity (p. 812). -/
def Factor.valence : Factor → ℚ
  | .status | .solidarity => 1
  | .antiSolidarity => -1

/-- The need for precision of a scenario, highest for the record and lowest in Bonding (p. 811). -/
def Scenario.need : Scenario → ℕ
  | .forTheRecord => 3
  | .persuasive => 2
  | .stranger => 1
  | .bonding => 0

/-- The precision of a variant. -/
def Variant.precision : Variant → ℕ
  | .approximate => 0
  | .underspecified => 1
  | .precise => 2

/-- A table of cell means agrees with the cells an experiment reports. -/
def Agrees (e : Experiment) (T : Scenario → Variant → Factor → ℚ) : Prop :=
  ∀ r ∈ scenarioRatings, r.experiment = e → T r.scenario r.variant r.factor = r.mean.toRat

/-- Scenario `s` favors variant `v` over variant `w` on a composite score more than scenario `s'`
does. -/
def Favors (T : Scenario → Variant → Factor → ℚ) (f : Factor) (s s' : Scenario) (v w : Variant) :
    Prop :=
  f.valence * (T s' v f - T s' w f) < f.valence * (T s v f - T s w f)

/-- The hypothesis of p. 810 is that a scenario that needs precision more favors a more precise
variant more. -/
def NeedHypothesis (T : Scenario → Variant → Factor → ℚ) : Prop :=
  ∀ f s s' v w, s'.need < s.need → w.precision < v.precision → Favors T f s s' v w

theorem favors_exp1 {T : Scenario → Variant → Factor → ℚ} (hT : Agrees .exp1 T) :
    Favors T .status .forTheRecord .bonding .precise .approximate ∧
      Favors T .antiSolidarity .forTheRecord .bonding .underspecified .approximate := by
  simp only [Agrees, scenarioRatings, List.forall_mem_cons, List.not_mem_nil, reduceCtorEq,
    forall_const, imp_true_iff, and_true, IsEmpty.forall_iff] at hT
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hT
  simp only [Favors, Factor.valence, h1, h2, h3, h4, h5, h6, h7, h8]
  norm_num [Decimal.toRat]

/-- In Experiment 2 the For-the-record scenario favors the precise variant over the
underspecified one on Solidarity more than the Stranger scenario does, as the hypothesis
predicts, but the Persuasive scenario favors it on Status more than For-the-record does
(p. 823), against the hypothesis; the paper leaves this unexplained (p. 830). -/
theorem favors_exp2 {T : Scenario → Variant → Factor → ℚ} (hT : Agrees .exp2 T) :
    Favors T .solidarity .forTheRecord .stranger .precise .underspecified ∧
      Favors T .status .persuasive .forTheRecord .precise .underspecified := by
  simp only [Agrees, scenarioRatings, List.forall_mem_cons, List.not_mem_nil, reduceCtorEq,
    forall_const, imp_true_iff, and_true, true_and, IsEmpty.forall_iff] at hT
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hT
  simp only [Favors, Factor.valence, h1, h2, h3, h4, h5, h6, h7, h8]
  norm_num [Decimal.toRat]

theorem not_needHypothesis {T : Scenario → Variant → Factor → ℚ} (hT : Agrees .exp2 T) :
    ¬ NeedHypothesis T := fun h ↦
  (favors_exp2 hT).2.asymm (h .status .forTheRecord .persuasive .precise .underspecified
    (by decide) (by decide))

/-! ### The grouping of the scales -/

/-- A scale loads most on a principal component, the criterion by which the paper assigns a scale
that loads on two (note 2). -/
def LoadsMostOn (e : Experiment) (s : Scale) (f : Factor) : Prop :=
  ∀ g ≠ f, (loadings e s g).loading.toRat < (loadings e s f).loading.toRat

instance (e : Experiment) (s : Scale) (f : Factor) : Decidable (LoadsMostOn e s f) :=
  inferInstanceAs (Decidable (∀ _, _))

theorem loadsMostOn_exp1 (s : Scale) : LoadsMostOn .exp1 s (scales s).dimension := by
  revert s; decide +kernel

/-- In Experiment 2 every scale but *friendly* loads most on the dimension it was included to
measure; *friendly* loads most on Status (Table 3). -/
theorem loadsMostOn_exp2_iff (s : Scale) :
    LoadsMostOn .exp2 s (scales s).dimension ↔ s ≠ .friendly := by
  revert s; decide +kernel

theorem loadsMostOn_friendly_exp2 : LoadsMostOn .exp2 .friendly .status := by decide +kernel

end BeltramaSoltBurnett2023
