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
two worked conditional entropies come out as exact closed forms. Burmeso's vocabularly clear
object agreement sits at the zero of the measure, and Chiquihuitlán Mazatec's final-vowel and
tone classes sit far from it, the prose claim that only third-person vowels are diagnostic
sharpened to what its Table 6 supports.

## Implementation notes

* Forms are the strings the paper's tables print, *-∅* the Greek zero ending, and outcomes
  carry the discrete σ-algebra on `String`.
* Class probabilities are `uniformOn Set.univ`, the paper's (5), under which every printed
  number is computed; entropies are in nats, the paper's bits are these divided by `log 2`.
* `avgCondEntropy` averages over ordered pairs of distinct cells, which reproduces Table 2's
  expected values and its grand average; the running text prints a different rounding of the
  latter.
* Table 1 yields five rival genitive singulars and a realization-space of 25600 class
  candidates where pp. 445–446 count six and 46,080 on richer data than Table 1.

## TODO

* `greek_avgCondEntropy`: the closed form of Table 2's grand average, provable from
  `condEntropy_uniformOn_univ_finset` with a per-pair count table.
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

/-- In the paper's (14), the genitive singular given the accusative plural carries
`(3/8) log 3` nats = 0.594 bits. -/
theorem greek_genSg_given_accPl :
    H[(nominal · genSg) | (nominal · accPl) ; uniformOn Set.univ] = 3 / 8 * log 3 := by
  rw [condEntropy_uniformOn_univ_finset (A := {"-u", "-∅", "-s", "-us", "-os"})
    (B := {"-us", "-es", "-is", "-a", "-i"}) (by decide) (by decide)]
  have cards1 : ∀ y ∈ ({"-us", "-es", "-is", "-a", "-i"} : Finset String),
      (Finset.univ.filter fun d => nominal d accPl = y).card
        = if y = "-es" then 2 else if y = "-a" then 3 else 1 := by decide
  have cards2 : ∀ y ∈ ({"-us", "-es", "-is", "-a", "-i"} : Finset String),
      ∀ x ∈ ({"-u", "-∅", "-s", "-us", "-os"} : Finset String),
        (Finset.univ.filter fun d => nominal d accPl = y ∧ nominal d genSg = x).card
          = if (y = "-us" ∧ x = "-u") ∨ (y = "-es" ∧ (x = "-∅" ∨ x = "-s")) ∨
              (y = "-is" ∧ x = "-s") ∨ (y = "-a" ∧ x = "-os") ∨ (y = "-i" ∧ x = "-us") then 1
            else if y = "-a" ∧ x = "-u" then 2 else 0 := by decide
  simp only [Fintype.card_fin]
  simp (disch := assumption) only [cards1, cards2]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
  norm_num [negMulLog, log_div]
  ring

/-- Table 2's grand average, the average conditional entropy of the Greek paradigms, equals
this closed form, 0.664 bits. -/
theorem greek_avgCondEntropy :
    nominal.avgCondEntropy (uniformOn Set.univ) =
      69 / 224 * log 2 + 3 / 32 * log 3 + 5 / 56 * log 5 := by
  sorry

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
