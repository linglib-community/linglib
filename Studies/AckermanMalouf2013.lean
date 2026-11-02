module

public import Linglib.Core.InformationTheory.Entropy.Empirical
public import Linglib.Morphology.Paradigm.Complexity
public import Linglib.Fragments.Greek.StandardModern.Declension
public import Linglib.Fragments.Burmeso.ObjectAgreement
public import Linglib.Fragments.Mazatec.Verbs
public import Linglib.Data.Examples.AckermanMalouf2013

/-!
# Ackerman and Malouf (2013): Morphological Organization: The Low Conditional Entropy Conjecture

Ackerman and Malouf separate the enumerative complexity of an inflectional system — how many
cells, realizations, and inflection classes it has — from its integrative complexity, the
average conditional entropy of one paradigm cell given another
(`Morphology.ParadigmSystem.avgCondEntropy`), and conjecture that the latter stays low however
large the former grows. Their Modern Greek nominal fragment carries the argument: its eight
declensions violate paradigm economy and fill a tiny corner of the space its per-cell
realizations allow, while implicative structure keeps the speaker's task small, and the paper's
two worked conditional entropies and Table 2's grand average come out as exact closed forms.
Burmeso's vocabularly clear
object agreement sits at the zero of the measure, and Chiquihuitlán Mazatec's final-vowel and
tone classes sit far from it, the prose claim that only third-person vowels are diagnostic
sharpened to what its Table 6 supports.

## Implementation notes

* Forms are the strings the paper's tables print, *-∅* the Greek zero ending, and outcomes
  carry the discrete σ-algebra on `String`.
* Class probabilities are `uniformOn Set.univ`, the paper's (5), under which every printed
  number is computed; entropies are in nats, the paper's bits are these divided by `log 2`.
* `avgCondEntropy` averages over ordered pairs of distinct cells, which reproduces Table 2's
  expected values and its grand average.
* Table 1 yields five rival genitive singulars and a realization-space of 25600 class
  candidates where pp. 445–446 count six and 46,080 on richer data than Table 1.

## Errata

* (12) prints the product of the marginals where conditional entropy has the joint, and no minus
  sign; (14) and Table 2 are the standard quantity.
* The prose before (13) gives the genitive singulars of the three classes with accusative plural
  *-a* as two *-o* and one *-∅*. In Table 1 they are two *-u* and one *-os*, the same proportions.
* (15) and (17) average with weight `1 / |C|`, which gives 0.629 bits for the nominative singular
  column; Table 2's 0.719 divides by `|C| - 1`. The last line of (18) drops the weights.
* Table 2 prints `H(VOC.SG | NOM.PL)` as 0.591. It is 0.594, as it must be since the accusative and
  vocative singular predict each other, and as the printed row mean 0.411 requires.
* The text after (18) and Table 3 print the grand average as 0.644 bits, and `2^0.644 = 1.56`.
  Table 2 prints 0.664, and the exact value is 0.664.

## TODO

* Table 5's average entropies and the tone system's realization count are computed on the
  appendix's full Table A6 data and do not follow from Tables 6–7, so they are not stated.

## References

* [ackerman-malouf-2013]
* [carstairs-mccarthy-2010]
* [bonami-beniamine-2016]
-/

@[expose] public section

namespace AckermanMalouf2013

open Morphology Morphology.ParadigmSystem MeasureTheory ProbabilityTheory InformationTheory Real
open Greek.StandardModern.Declension Burmeso.ObjectAgreement Mazatec.Verbs

/-! ### Forms as outcomes -/

instance : MeasurableSpace String := ⊤
instance : MeasurableSingletonClass String := ⟨fun _ ↦ trivial⟩

/-! ### Modern Greek: enumerative complexity -/

theorem greek_maxRealizations : nominal.maxRealizations = 5 := by decide

/-- Eight declensions exceed the five rival realizations of the most varied cell. -/
theorem greek_not_paradigmEconomy : ¬ nominal.ParadigmEconomy := by decide

-- Table 3
theorem greek_realization_count : (Finset.univ.biUnion nominal.realizations).card = 12 := by
  decide

-- Table 1
theorem greek_classes_vs_product :
    (Finset.univ.image nominal).card = 8 ∧ ∏ c, (nominal.realizations c).card = 25600 := by
  decide

/-! ### Modern Greek: implicative structure -/

theorem greek_predicts :
    nominal.Predicts {vocSg} accSg ∧ nominal.Predicts {accSg} vocSg ∧
      nominal.Predicts {accPl} nomPl := by
  decide

theorem greek_not_predicts : ¬ nominal.Predicts {accPl} genSg := by decide

theorem greek_accPl_i_genSg : ∀ d, nominal d accPl = "-i" → nominal d genSg = "-us" := by decide

/-- Nominative singular, genitive singular, and accusative plural are principal parts; the
last two alone are not. -/
theorem greek_principalParts :
    nominal.IsPrincipalPartSet {nomSg, genSg, accPl} ∧
      ¬ nominal.IsPrincipalPartSet {genSg, accPl} := by
  decide

theorem greek_not_clear : ¬ nominal.IsVocabularClear := by decide

/-! ### Modern Greek: entropy -/

theorem greek_declensionEntropy : Hm[(uniformOn Set.univ : Measure (Fin 8))] = log 8 := by
  simpa using measureEntropy_uniformOn (A := (Finset.univ : Finset (Fin 8)))
    Finset.univ_nonempty

theorem greek_cellEntropy_genPl : H[(nominal · genPl) ; uniformOn Set.univ] = 0 :=
  entropy_eq_zero_of_card_realizations_le_one _ (by decide)

theorem greek_condEntropy_nomPl_accPl :
    H[(nominal · nomPl) | (nominal · accPl) ; uniformOn Set.univ] = 0 :=
  condEntropy_eq_zero_of_predicts _ (by decide)

/-- In (13), an accusative plural in *-a* leaves the genitive singular with conditional entropy `log
3 − (2/3) log 2` nats. -/
theorem greek_genSg_given_accPl_a :
    H[(nominal · genSg) ; uniformOn ((nominal · accPl) ⁻¹' {"-a"})] =
      log 3 - 2 / 3 * log 2 := by
  have hA : (nominal · accPl) ⁻¹' {"-a"} = ↑({4, 5, 7} : Finset (Fin 8)) := by
    ext d
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff]
    revert d; decide
  rw [hA]
  have := isProbabilityMeasure_uniformOn
    (Set.toFinite (↑({4, 5, 7} : Finset (Fin 8)) : Set (Fin 8))) ⟨4, by simp⟩
  rw [entropy_eq_sum_finset (measurable_of_finite _) _
    (A := {"-u", "-∅", "-s", "-us", "-os"}) (by decide)]
  have key : ∀ r : String,
      ((↑({4, 5, 7} : Finset (Fin 8)) ∩ (nominal · genSg) ⁻¹' {r}).ncard : ℝ)
        = (({4, 5, 7} : Finset (Fin 8)).filter (nominal · genSg = r)).card := fun r ↦ by
    rw [← Set.ncard_coe_finset, Finset.coe_filter]
    congr 2
  have cards : ∀ r ∈ ({"-u", "-∅", "-s", "-us", "-os"} : Finset String),
      (({4, 5, 7} : Finset (Fin 8)).filter (nominal · genSg = r)).card
        = if r = "-u" then 2 else if r = "-os" then 1 else 0 := by decide
  rw [Finset.sum_congr rfl fun r hr ↦ by rw [uniformOn_real_apply, key, cards r hr]]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
  norm_num [negMulLog, log_div]
  ring

/-! The worked conditional entropies are read off the class sizes of Table 1: a conditional
entropy is `8⁻¹ * (log P - log Q)` for two products `P` and `Q` of class sizes, which the kernel
computes. -/

private abbrev GreekCell := Greek.StandardModern.Declension.Row × Greek.StandardModern.Case

/-- The product over the declensions of the size of a declension's class under the realization of
`c₂`. -/
private def classSizes (c₂ : GreekCell) : ℕ :=
  ∏ d, (Finset.univ.filter (nominal · c₂ = nominal d c₂)).card

/-- The product over the declensions of the size of a declension's class under the realizations of
`c₂` and `c₁` together. -/
private def jointClassSizes (c₁ c₂ : GreekCell) : ℕ :=
  ∏ d, (Finset.univ.filter fun d' ↦ nominal d' c₂ = nominal d c₂ ∧
    nominal d' c₁ = nominal d c₁).card

private theorem classSizes_ne_zero : ∀ c, classSizes c ≠ 0 := by decide +kernel

private theorem jointClassSizes_ne_zero : ∀ c₁ c₂, jointClassSizes c₁ c₂ ≠ 0 := by decide +kernel

private theorem condEntropy_eq_log_sub_log (c₁ c₂ : GreekCell) :
    H[(nominal · c₁) | (nominal · c₂) ; uniformOn Set.univ] =
      8⁻¹ * (log (classSizes c₂) - log (jointClassSizes c₁ c₂)) := by
  have hg (d : Fin 8) : (((Finset.univ.filter (nominal · c₂ = nominal d c₂)).card : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨d, by simp⟩)
  have hj (d : Fin 8) : (((Finset.univ.filter fun d' ↦ nominal d' c₂ = nominal d c₂ ∧
      nominal d' c₁ = nominal d c₁).card : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨d, by simp⟩)
  rw [condEntropy_uniformOn_univ_eq_sum_log, Fintype.card_fin, classSizes, jointClassSizes,
    Nat.cast_prod, Nat.cast_prod, log_prod (fun d _ ↦ hg d), log_prod (fun d _ ↦ hj d),
    ← Finset.sum_sub_distrib]
  simp_rw [log_div (hg _) (hj _)]
  norm_num

/-- In the paper's (14), the genitive singular given the accusative plural carries
`(3/8) log 3` nats = 0.594 bits. -/
theorem greek_genSg_given_accPl :
    H[(nominal · genSg) | (nominal · accPl) ; uniformOn Set.univ] = 3 / 8 * log 3 := by
  have h : classSizes accPl = jointClassSizes genSg accPl * 3 ^ 3 := by decide +kernel
  rw [condEntropy_eq_log_sub_log, h, Nat.cast_mul, log_mul
    (Nat.cast_ne_zero.2 (jointClassSizes_ne_zero _ _)) (by positivity), Nat.cast_pow, log_pow]
  push_cast
  ring

/-- Table 2's grand average, the average conditional entropy of the Greek paradigms, equals
this closed form, 0.664 bits. -/
theorem greek_avgCondEntropy :
    nominal.avgCondEntropy (uniformOn Set.univ) =
      69 / 224 * log 2 + 3 / 32 * log 3 + 5 / 56 * log 5 := by
  have hcard : (Fintype.card GreekCell * (Fintype.card GreekCell - 1) : ℕ) = 56 := by decide
  have hprod : (∏ c₁, ∏ c₂ ∈ Finset.univ.erase c₁, classSizes c₂) =
      (∏ c₁, ∏ c₂ ∈ Finset.univ.erase c₁, jointClassSizes c₁ c₂) * (2 ^ 138 * 3 ^ 42 * 5 ^ 40) := by
    decide +kernel
  have hj : ((∏ c₁, ∏ c₂ ∈ Finset.univ.erase c₁, jointClassSizes c₁ c₂ : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun _ _ ↦
      Finset.prod_ne_zero_iff.2 fun _ _ ↦ jointClassSizes_ne_zero _ _)
  have hsum : ∑ c₁, ∑ c₂ ∈ Finset.univ.erase c₁,
      H[(nominal · c₁) | (nominal · c₂) ; uniformOn Set.univ] =
      8⁻¹ * (log ((∏ c₁, ∏ c₂ ∈ Finset.univ.erase c₁, classSizes c₂ : ℕ) : ℝ) -
        log ((∏ c₁, ∏ c₂ ∈ Finset.univ.erase c₁, jointClassSizes c₁ c₂ : ℕ) : ℝ)) := by
    simp only [Nat.cast_prod]
    rw [log_prod fun _ _ ↦ Finset.prod_ne_zero_iff.2 fun _ _ ↦
        Nat.cast_ne_zero.2 (classSizes_ne_zero _),
      log_prod fun _ _ ↦ Finset.prod_ne_zero_iff.2 fun _ _ ↦
        Nat.cast_ne_zero.2 (jointClassSizes_ne_zero _ _), ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c₁ _ ↦ ?_
    rw [log_prod fun _ _ ↦ Nat.cast_ne_zero.2 (classSizes_ne_zero _),
      log_prod fun _ _ ↦ Nat.cast_ne_zero.2 (jointClassSizes_ne_zero _ _),
      ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c₂ _ ↦ condEntropy_eq_log_sub_log c₁ c₂
  have hlog :
      log ((2 ^ 138 * 3 ^ 42 * 5 ^ 40 : ℕ) : ℝ) = 138 * log 2 + 42 * log 3 + 40 * log 5 := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_pow,
      log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity), log_pow,
      log_pow, log_pow]
    norm_num
  rw [avgCondEntropy, hsum, hcard, hprod, Nat.cast_mul, log_mul hj (by positivity), hlog]
  push_cast
  ring

/-! ### Burmeso -/

theorem burmeso_clear : objectAgreement.IsVocabularClear := by decide

-- Table 3
theorem burmeso_realizations :
    (Finset.univ.biUnion objectAgreement.realizations).card = 6 ∧
      objectAgreement.maxRealizations = 2 := by
  decide

/-- Being vocabularly clear, Burmeso has average conditional entropy zero. -/
theorem burmeso_avgCondEntropy : objectAgreement.avgCondEntropy (uniformOn Set.univ) = 0 :=
  avgCondEntropy_eq_zero_of_isVocabularClear _ burmeso_clear

/-! ### Chiquihuitlán Mazatec -/

theorem mazatec_vowels_not_clear : ¬ finalVowels.IsVocabularClear := by decide

theorem mazatec_vowels_constant :
    H[(finalVowels · .pl1) ; uniformOn Set.univ] = 0 ∧
      H[(finalVowels · .pl2) ; uniformOn Set.univ] = 0 :=
  ⟨entropy_eq_zero_of_card_realizations_le_one _ (by decide),
    entropy_eq_zero_of_card_realizations_le_one _ (by decide)⟩

/-- Over Table 6, the third person predicts the second singular without being a principal part, and
the first singular predicts the first inclusive. -/
theorem mazatec_vowels_diagnosticity :
    finalVowels.Predicts {.third} .sg2 ∧ ¬ finalVowels.IsPrincipalPartSet {.third} ∧
      finalVowels.Predicts {.sg1} .incl := by
  decide

/-- No cell of the tone patterns is diagnostic of class membership. -/
theorem mazatec_tones_no_diagnostic_cell : ∀ c, ¬ tones.IsPrincipalPartSet {c} := by decide

end AckermanMalouf2013
