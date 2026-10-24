module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Agreement.Bundle
public import Linglib.Fragments.Slavic.Russian.Agreement
public import Linglib.Fragments.Slavic.Russian.Gender
public import Linglib.Fragments.Somali.Gender
public import Linglib.Fragments.Latin.Gender
public import Linglib.Fragments.Chichewa.Gender
public import Linglib.Fragments.CoastalMarind.Gender
public import Linglib.Syntax.Gender.AgreementClasses
public import Linglib.Syntax.Agreement.Resolution
public import Linglib.Data.Examples.Corbett1998

/-!
# Corbett's morphology of agreement

Agreement is the systematic covariance of one element's form with properties of another,
and it is asymmetric: the controller determines the target. Gender, number and person are
the indisputable agreement features because their values originate on the controller, gender
inherent to the noun, person to the pronoun, and number relating primarily to the noun; case
covaries within the noun phrase too, but is imposed on noun and modifier alike by a governor
outside it, and definiteness is imposed on the phrase as a whole, so neither is agreement.
The exponents of agreement are affixes before, after and inside the stem, and a target may
carry several for one controller; the features constrain one another, Russian distinguishing
gender only in the singular in conformity with Greenberg's universal, and their joint
expression may be fusional and syncretic, at its most spectacular in polarity, where the
Somali article of one gender in one number is that of the other gender in the other number.
The target then shapes agreement twice over. The forms available depend on its word class
and even its lexical class, Upper Sorbian finite verbs and participles agreeing in different
features and Latin adjective classes distinguishing three genders, two or none; and the form
selected may depend on
another target or on syncretism, conjoined Chichewa plurals taking the target form they share
rather than the resolved one. The chapter's examples are the rows of
`Data/Examples/Corbett1998.json`.

## Implementation notes

* The asymmetry criterion is read off where a covarying feature's value originates, the
  chapter's classification of the five dimensions carried as data; what a Russian target is
  inflected for is derived from its forms in the fragment, and what it agrees in is the
  inflected dimensions whose origin is the controller.
* Polarity is the substrate's `Morphology.Polar`, which the Somali fragment proves of its
  article (Table 9.1); the verbal prefix is shown not to be polar, the plural prefix
  coinciding with the masculine singular's instead.
* Number-conditioned gender distinctions are the substrate's convergent maps between the
  target genders of two numbers; Chichewa's coordination rules are the substrate's ordered
  resolution rules over fragment nouns, one per target form before the semantic rule.
* The agreement slots of a target, their controllers and their bound of four are described
  in the rows and not modelled.
* The syncretism claims are stated over the languages' own gender carriers, not over the
  cell-to-exponent tables of `Syntax/Agreement/Paradigm.lean`, whose gender cells take the
  comparative labels.

## TODO

* Nichols's hierarchy of the three features by their propensity to be marked only by
  agreement, the default-or-ungrammaticality outcomes of missing morphology, and the
  dependence of one target's form on another in Tigre, in Somali focus constructions and in
  German noun phrases are prose only.
* The Chichewa nouns carry no number, so the restriction of the shared-form rule to plural
  conjuncts, and the triggering of gender resolution by number resolution, are not stated.

## References

* [G. G. Corbett, *Morphology and agreement* (1998)][corbett-1998]
* [G. G. Corbett, *Gender* (1991)][corbett-1991]
* [J. H. Greenberg, *Some universals of grammar* (1963)][greenberg-1963]
* [G. G. Corbett, A. D. Mtenje, *Gender agreement in Chichewa* (1987)][corbett-mtenje-1987]
-/

@[expose] public section

namespace Corbett1998

open Agreement

/-! ### Agreement features (§§1–2) -/

/-- Where the value of a covarying feature originates, on the controller, on a governor outside
the phrase, or on the phrase as a whole. -/
inductive Origin where
  | controller
  | governor
  | phrase
  deriving DecidableEq, Repr, Fintype

/-- The origin of each feature in the chapter's classification. Gender is inherent to the noun and
person to the pronoun, number relates primarily to the noun, case is imposed by government, and
definiteness belongs to the phrase. -/
def origin : Dimension → Origin
  | .gender | .number | .person => .controller
  | .case => .governor
  | .definiteness => .phrase

/-- Covariance is agreement when it is asymmetric, the value originating on the controller. -/
abbrev IsAgreementFeature (d : Dimension) : Prop := origin d = .controller

theorem isAgreementFeature_iff (d : Dimension) :
    IsAgreementFeature d ↔ d = .gender ∨ d = .number ∨ d = .person := by
  cases d <;> decide

/-- The agreement features among the dimensions a target is inflected for. -/
def agreementFeatures (D : Finset Dimension) : Finset Dimension := D.filter IsAgreementFeature

namespace Russian

open _root_.Russian.Agreement

/-- The attributive adjective is inflected for case, (5). -/
theorem case_mem_inflection_longAdjective : .case ∈ longAdjective.inflection := by decide

theorem not_isAgreementFeature_case : ¬ IsAgreementFeature .case := by decide

/-- The attributive adjective agrees in number and gender, (1)–(5). -/
theorem agreementFeatures_longAdjective :
    agreementFeatures longAdjective.inflection = {.number, .gender} := by decide

end Russian

/-! ### The exponents of agreement (§3.1) -/

namespace CoastalMarind

open _root_.CoastalMarind

/-- The infixed vowel of *ak-k* 'light' distinguishes all four genders, (6)–(9). -/
theorem faithful_light : Function.Injective (light · (numberSystem.value .singular)) := by decide

theorem not_faithful_demonstrative :
    ¬ Function.Injective (demonstrative · (numberSystem.value .singular)) := by
  decide

end CoastalMarind

/-! ### Constraints on the co-occurrence of features (§3.2) -/

namespace Russian

open _root_.Russian.Gender _root_.Russian.Agreement

/-- Adjectives distinguish gender only in the singular, (1)–(4), a convergent system, with the
inanimate nouns of the examples. -/
theorem convergent :
    Gender.Convergent (longEnding · .inanimate (numberSystem.value .singular) .nom)
      (longEnding · .inanimate (numberSystem.value .plural) .nom) := by
  decide

theorem card_longEnding_pl_lt :
    Nat.card (Set.range (longEnding · .inanimate (numberSystem.value .plural) .nom)) <
      Nat.card (Set.range (longEnding · .inanimate (numberSystem.value .singular) .nom)) :=
  convergent.card_range_lt

theorem gender_mem_inflection_pastVerb :
    .gender ∈ pastVerb.inflection ∧ ∀ k, .gender ∉ (nonpastVerb k).inflection := by decide

end Russian

namespace Somali

open _root_.Somali.Gender

/-- The verbal prefix is not polar, (11)–(14), the plural prefix of either gender being the
masculine singular's. -/
theorem not_polar_verbPrefix : ¬ Morphology.Polar Value.verbPrefix := by decide

theorem verbPrefix_plural (g : Value) :
    g.verbPrefix (numberSystem.value .plural) =
      Value.masc.verbPrefix (numberSystem.value .singular) := by
  cases g <;> rfl

theorem article_nin :
    nin.article (numberSystem.value .plural) = nin.article (numberSystem.value .singular) := rfl

theorem parallel_article :
    Gender.Parallel (Value.article · (numberSystem.value .singular))
      (Value.article · (numberSystem.value .plural)) :=
  polar_article.parallel (numberSystem.value .singular) (numberSystem.value .plural)

theorem convergent_verbPrefix :
    Gender.Convergent (Value.verbPrefix · (numberSystem.value .singular))
      (Value.verbPrefix · (numberSystem.value .plural)) := by
  decide

end Somali

/-! ### The effect of the target on the forms available (§4) -/

namespace UpperSorbian

/-- The two verbal targets of (17). -/
inductive Target where
  | finiteVerb
  | participle
  deriving DecidableEq, Repr, Fintype

/-- The row key of each target. -/
def Target.key : Target → String
  | .finiteVerb => "finiteVerb"
  | .participle => "participle"

/-- The finite verb agrees in number and person, the participle in number and gender. -/
def features : Target → Finset Dimension
  | .finiteVerb => {.number, .person}
  | .participle => {.number, .gender}

theorem not_uniform : ¬ ∃ D, ∀ t, features t = D :=
  fun ⟨_, h⟩ ↦ absurd ((h .finiteVerb).trans (h .participle).symm) (by decide)

end UpperSorbian

namespace Russian

open _root_.Russian.Agreement

theorem inflection_nonpastVerb_ne_pastVerb (k : Conjugation) :
    (nonpastVerb k).inflection ≠ pastVerb.inflection := by
  cases k <;> decide

end Russian

namespace Latin

open _root_.Latin.Gender

/-- In Table 9.2 the nominative singular forms of *facilis* factor through those of *acer*, not
conversely. -/
theorem facilis_factorsThrough_acer :
    Function.FactorsThrough facilis.nomSg acer.nomSg ∧
      ¬ Function.FactorsThrough acer.nomSg facilis.nomSg := by decide

theorem felix_factorsThrough_facilis :
    Function.FactorsThrough felix.nomSg facilis.nomSg ∧
      ¬ Function.FactorsThrough facilis.nomSg felix.nomSg := by decide

end Latin

/-! ### The effect of the target on the form selected (§5) -/

namespace Chichewa

open _root_.Chichewa.Gender Agreement.ResolutionRule

/-- Coordinated plural nouns that would take one target form take it. -/
def sharedFormRules : List (ResolutionRule Chichewa.Gender.Noun SubjPrefix) :=
  [.all (·.gender.plSubjPrefix = .a) .a, .all (·.gender.plSubjPrefix = .zi) .zi]

/-- The regular rule, by which humans take the plural of gender 1/2 and the rest the plural of
7/8. -/
def semanticRules : List (ResolutionRule Chichewa.Gender.Noun SubjPrefix) :=
  [.all (·.animacy = .human) .a, otherwise .zi]

/-- The shared form is preferred; the regular rule applies where there is none. -/
def rules : List (ResolutionRule Chichewa.Gender.Noun SubjPrefix) :=
  sharedFormRules ++ semanticRules

/-- Syncretism licenses agreement, (18) and (19), conjuncts sharing a form taking it. -/
theorem resolve_of_shared {cs : List Chichewa.Gender.Noun} (hne : cs ≠ []) {f : SubjPrefix}
    (h : ∀ c ∈ cs, c.gender.plSubjPrefix = f) : resolve rules cs = some f := by
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil cs hne
  simp only [rules, sharedFormRules, List.cons_append, List.nil_append]
  cases f
  · exact resolve_cons_of_applies h
  · rw [resolve_cons_of_not_applies fun h' ↦ absurd ((h' c hc).symm.trans (h c hc)) (by decide)]
    exact resolve_cons_of_applies h

theorem resolve_of_ne {cs : List Chichewa.Gender.Noun} (ha : ∃ c ∈ cs, c.gender.plSubjPrefix ≠ .a)
    (hz : ∃ c ∈ cs, c.gender.plSubjPrefix ≠ .zi) : resolve rules cs = resolve semanticRules cs := by
  obtain ⟨a, ha, ha'⟩ := ha
  obtain ⟨z, hz, hz'⟩ := hz
  have h₁ : ¬ ∀ c ∈ cs, c.gender.plSubjPrefix = .a := fun h ↦ ha' (h a ha)
  have h₂ : ¬ ∀ c ∈ cs, c.gender.plSubjPrefix = .zi := fun h ↦ hz' (h z hz)
  simp [rules, sharedFormRules, h₁, h₂]

theorem resolve_semanticRules (cs : List Chichewa.Gender.Noun) :
    resolve semanticRules cs = some (if ∀ c ∈ cs, c.animacy = .human then .a else .zi) := by
  unfold semanticRules
  split_ifs with hh
  · exact resolve_cons_of_applies hh
  · simp [hh]

theorem resolve_mphaka_galu_ana_lalanje :
    resolve rules [mphaka, galu] = some .a ∧ resolve rules [ana, lalanje] = some .a := by decide

end Chichewa

/-! ### The chapter's examples -/

/-- In the Russian adjectives of (1)–(5) the ending is the fragment's by gender, number and case,
the nouns *avtomobil'*, *mašina* and *taksi* being inanimate. -/
theorem russian_rows : ∀ row ∈ Examples.all, row.language = "russ1263" →
    ∀ g ∈ row.parse? "gender"
      [("masc", _root_.Russian.Gender.Value.masc), ("fem", .fem), ("neut", .neut)],
    ∀ n ∈ row.parse? "number" [("sg", _root_.Russian.Gender.numberSystem.value .singular),
      ("pl", _root_.Russian.Gender.numberSystem.value .plural)],
    ∀ c ∈ row.parse? "case" [("nom", _root_.Russian.Case.nom), ("loc", .loc)],
    ∀ e ∈ row.parse? "ending"
      [("yj", _root_.Russian.Agreement.LongEnding.yj), ("aja", .aja), ("oe", .oe), ("ye", .ye),
        ("om", .om)],
      e = _root_.Russian.Agreement.longEnding g .inanimate n c := by
  decide +kernel

/-- In the Russian verbs of §2.3, *beru*, *bereš'* and *beret* 'take', of the first
conjugation, the ending is the fragment's by person and number. -/
theorem russian_verb_rows : ∀ row ∈ Examples.all, row.language = "russ1263" →
    ∀ p ∈ row.parse? "person" [("1", Person.first), ("2", .second), ("3", .third)],
    ∀ n ∈ row.parse? "number" [("sg", _root_.Russian.Gender.numberSystem.value .singular),
      ("pl", _root_.Russian.Gender.numberSystem.value .plural)],
    ∀ e ∈ row.parse? "ending"
      [("u", _root_.Russian.Agreement.NonpastEnding.u), ("eš'", .eš'), ("et", .et)],
      e = _root_.Russian.Agreement.nonpastEnding .first p n := by
  decide +kernel

/-- In the Marind rows (6)–(9) the adjective and the demonstrative are the fragment's by gender. -/
theorem marind_rows : ∀ row ∈ Examples.all, row.language = "nucl1622" →
    ∀ g ∈ row.parse? "gender"
      [("I", CoastalMarind.Gender.gI), ("II", .gII), ("III", .gIII), ("IV", .gIV)],
      (∀ a ∈ row.feature? "adjective",
          a = CoastalMarind.light g (CoastalMarind.numberSystem.value .singular)) ∧
        ∀ d ∈ row.feature? "demonstrative",
          d = CoastalMarind.demonstrative g (CoastalMarind.numberSystem.value .singular) := by
  decide +kernel

/-- In the Upper Sorbian row (17) each target agrees in the features the row records for it. -/
theorem upperSorbian_rows : ∀ row ∈ Examples.all, row.language = "uppe1395" →
    ∀ t : UpperSorbian.Target, ∀ D ∈ row.parse? t.key
      [("number,person", ({.number, .person} : Finset Dimension)),
        ("number,gender", {.number, .gender})],
      UpperSorbian.features t = D := by
  decide +kernel

/-- In the Somali rows (11)–(14) and *nin* the article is the noun's by number and the verbal
prefix the gender's. -/
theorem somali_rows : ∀ row ∈ Examples.all, row.language = "soma1255" →
    ∀ n ∈ row.parse? "noun" (_root_.Somali.Gender.allNouns.map fun n ↦ (n.form, n)),
    ∀ pl ∈ row.parse? "number" [("sg", _root_.Somali.Gender.numberSystem.value .singular),
      ("pl", _root_.Somali.Gender.numberSystem.value .plural)],
      (∀ a ∈ row.parse? "article" [("kii", _root_.Somali.Gender.Article.kii), ("tii", .tii)],
        a = n.article pl) ∧
      ∀ v ∈ row.parse? "verb" [("y", _root_.Somali.Gender.VerbPrefix.y), ("t", .t)],
        v = n.gender.verbPrefix pl := by
  decide +kernel

/-- In the Chichewa rows (18) and (19) the verb's prefix is the rules' resolution of the
conjuncts. -/
theorem chichewa_rows : ∀ row ∈ Examples.all, row.language = "nyan1308" →
    ∀ a ∈ row.parse? "conjunct1" (_root_.Chichewa.Gender.allNouns.map fun n ↦ (n.form, n)),
    ∀ b ∈ row.parse? "conjunct2" (_root_.Chichewa.Gender.allNouns.map fun n ↦ (n.form, n)),
    ∀ p ∈ row.parse? "prefix" [("a", _root_.Chichewa.Gender.SubjPrefix.a), ("zi", .zi)],
      Agreement.ResolutionRule.resolve Chichewa.rules [a, b] = some p := by
  decide +kernel

end Corbett1998
