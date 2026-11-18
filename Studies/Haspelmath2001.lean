module

public import Linglib.Data.Examples.Haspelmath2001
public import Linglib.Data.Examples.Languages
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Statistics.Haspelmath2001
public import Linglib.Fragments.Basque.Relativization
public import Linglib.Fragments.English.Relativization
public import Linglib.Fragments.Finnish.Comparison
public import Linglib.Fragments.Finnish.Relativization
public import Linglib.Fragments.German.Relativization
public import Linglib.Fragments.HindiUrdu.Relativization
public import Linglib.Fragments.Latin.Comparison
public import Linglib.Fragments.Romance.French.Comparison
public import Linglib.Fragments.Romance.French.Relativization
public import Linglib.Fragments.Slavic.Russian.Comparison
public import Linglib.Fragments.Slavic.Russian.Relativization
public import Linglib.Fragments.Turkish.Relativization
public import Linglib.Fragments.Welsh.Relativization
public import Mathlib.Data.Finset.Card
public import Studies.Stassen1985

/-!
# Haspelmath (2001): The European linguistic area: Standard Average European

A structural feature is a Europeanism, §1 says, when the great majority of the core European
languages have it, the adjacent and the eastern Indo-European languages lack it, and most of the
world's languages lack it too; §2 maps twelve such features. The chapter's inferences rest on two
summaries of the table of languages by features. By feature, the share of the core against the share
of the neighbours: [every feature is commoner in the core](##standsOut), though read literally [the
criteria pass three of the twelve](##isEuropeanism_iff). By language, the number of nine features
held: it [reproduces Map 107.13](##clusterScore_eq_printed) and [leaves nothing between two and
five](##clusterScore_gap). Fragments confirm [Map 107.2](##relativePronouns_fragments) and [Map
107.9](##comparative_fragments).

## Implementation notes

* `sample` and `isogloss` are read from page images, each solid line checked by flood fill. The
  numbers beside the names on Maps 107.4 and 107.6 enter only through the lines drawn at their cuts.
* "The great majority" is read as three quarters, and [two thirds selects the same
  features](##twoThirds_iff). "Lack" is literal, and the "perhaps" of Afro-Asiatic excludes it.

## TODO

* The surveys and Table 107.1 of §3, the features of §3.6, and the five origins §5 weighs.

## References

* [haspelmath-2001]
* [keenan-comrie-1977]
* [stassen-1985]
-/

@[expose] public section

namespace Haspelmath2001

/-- The languages of Maps 107.1-107.13, by the abbreviations of §6, with the three eastern
Indo-European languages §2 reports as having a feature. -/
inductive Language where
  | albanian | armenian | baluchi | basque | breton | bulgarian | czech | dutch | english
  | estonian | finnish | french | gaelic | georgian | german | greek | hungarian | icelandic
  | irish | italian | komi | latin | latvian | laz | lezgian | lithuanian | maithili | maltese
  | mari | mordvin | nenets | norwegian | polish | portuguese | punjabi | romanian | russian
  | saami | sardinian | serboCroatian | slovene | spanish | swedish | tatar | turkish | ubykh
  | udmurt | ukrainian | welsh
  deriving DecidableEq, Repr

open Haspelmath2001.Language

/-! ### The table -/

/-- The base map, the languages shared by nine of the twelve maps. -/
def baseMap : Finset Language :=
  {albanian, armenian, basque, breton, bulgarian, czech, dutch, english, estonian, finnish, french,
  georgian, german, greek, hungarian, icelandic, irish, italian, komi, latvian, lezgian, lithuanian,
  maltese, nenets, norwegian, polish, portuguese, romanian, russian, sardinian, serboCroatian,
  slovene, spanish, swedish, tatar, turkish, udmurt, ukrainian, welsh}

/-- The languages a feature's map names. -/
def sample : Feature → Finset Language
  | .nominativeExperiencers =>
    {albanian, basque, breton, bulgarian, czech, dutch, english, estonian, finnish, french,
    georgian, german, greek, hungarian, icelandic, irish, italian, latvian, lezgian, lithuanian,
    maltese, mari, mordvin, norwegian, polish, portuguese, romanian, russian, saami, serboCroatian,
    spanish, swedish, turkish, udmurt, welsh}
  | .anticausativeProminence =>
    {armenian, english, finnish, french, georgian, german, greek, hungarian, lezgian, lithuanian,
    romanian, russian, turkish, udmurt}
  | .particleComparative =>
    {albanian, basque, breton, dutch, english, finnish, french, gaelic, greek, hungarian, latin,
    latvian, laz, nenets, russian, turkish, ubykh}
  | _ => baseMap

/-- The languages inside a map's solid line, the value the chapter calls SAE. -/
def isogloss : Feature → Finset Language
  | .articles =>
    {albanian, breton, dutch, english, french, german, greek, hungarian, italian, norwegian,
    portuguese, romanian, sardinian, spanish, swedish}
  | .relativePronouns =>
    {albanian, armenian, bulgarian, czech, dutch, english, estonian, finnish, french, georgian,
    german, greek, hungarian, icelandic, italian, latvian, lithuanian, norwegian, polish,
    portuguese, romanian, russian, sardinian, serboCroatian, slovene, spanish, swedish, ukrainian}
  | .havePerfect =>
    {albanian, czech, dutch, english, french, german, greek, icelandic, italian, norwegian,
    portuguese, romanian, sardinian, spanish, swedish}
  | .nominativeExperiencers =>
    {basque, breton, bulgarian, czech, dutch, english, french, german, greek, hungarian, italian,
    maltese, norwegian, portuguese, serboCroatian, spanish, swedish, turkish}
  | .participialPassive =>
    {albanian, breton, bulgarian, czech, dutch, english, french, german, greek, hungarian,
    icelandic, irish, italian, latvian, lithuanian, maltese, norwegian, polish, portuguese,
    romanian, russian, sardinian, serboCroatian, slovene, spanish, swedish, ukrainian}
  | .anticausativeProminence =>
    {english, french, german, greek, lithuanian, romanian, russian}
  | .dativeExternalPossessors =>
    {albanian, basque, bulgarian, czech, dutch, french, german, greek, hungarian, italian, latvian,
    lithuanian, maltese, polish, portuguese, romanian, russian, sardinian, serboCroatian, slovene,
    spanish, ukrainian}
  | .negativeIndefinitesWithoutVerbalNegation =>
    {albanian, dutch, english, french, georgian, german, icelandic, italian, norwegian, portuguese,
    sardinian, spanish, swedish}
  | .particleComparative =>
    {albanian, basque, dutch, english, finnish, french, gaelic, greek, hungarian, latin, latvian,
    russian}
  | .relativeBasedEquative =>
    {albanian, bulgarian, czech, dutch, english, french, german, greek, hungarian, italian, latvian,
    lithuanian, polish, portuguese, romanian, russian, sardinian, serboCroatian, slovene, spanish,
    ukrainian}
  | .strictAgreement =>
    {dutch, english, french, german, icelandic, russian, welsh}
  | .intensifierReflexiveDifferentiation =>
    {albanian, basque, bulgarian, czech, french, german, greek, icelandic, italian, latvian,
    lithuanian, norwegian, polish, portuguese, romanian, russian, sardinian, serboCroatian, slovene,
    spanish, swedish, ukrainian}

/-! ### By feature: the criteria of §1 -/

/-- The Slavic languages. -/
def slavic : Finset Language :=
  {bulgarian, czech, polish, russian, serboCroatian, slovene, ukrainian}

/-- The core European languages: Romance, Germanic, Balto-Slavic, the Balkan languages, and the
westernmost Finno-Ugrian languages. -/
def core : Finset Language :=
  slavic ∪ {albanian, dutch, english, estonian, finnish, french, german, greek, hungarian,
    icelandic, italian, latvian, lithuanian, norwegian, portuguese, romanian, sardinian, spanish,
    swedish}

/-- The adjacent languages of criterion (ii): Celtic, Turkic, eastern Uralic, Abkhaz-Adyghean and
Nakh-Daghestanian. -/
def adjacent : Finset Language :=
  {breton, gaelic, irish, komi, lezgian, mari, mordvin, nenets, saami, tatar, turkish, ubykh,
    udmurt, welsh}

/-- The eastern Indo-European languages of criterion (iii) that the chapter places inside a feature:
Armenian on the maps, the others in the prose of §2. -/
def easternIE : Finset Language := {armenian, baluchi, maithili, punjabi}

/-- What the prose of §2 grants eastern Indo-European. It denies Iranian and Indic every other
feature but comparatives and strict agreement, of which it says nothing. -/
def reported : Feature → Finset Language
  | .participialPassive => {baluchi, maithili}
  | .relativeBasedEquative => {punjabi}
  | _ => ∅

variable (f : Feature)

/-- Criterion (i): at least three quarters of the core languages on the map have the feature. -/
def GreatMajorityOfCore : Prop :=
  3 * (sample f ∩ core).card ≤ 4 * (isogloss f ∩ core).card

/-- Criterion (ii): the adjacent languages lack the feature. -/
def AdjacentLack : Prop := isogloss f ∩ adjacent = ∅

/-- Criterion (iii): the eastern Indo-European languages lack the feature. -/
def EasternIELack : Prop := (isogloss f ∪ reported f) ∩ easternIE = ∅

/-- Criterion (iv): the surveys cited for the feature find it in a minority of their sample. -/
def WorldMinority : Prop := ∀ s ∈ surveys, s.feature = f → 2 * s.withFeature < s.sample

/-- A Europeanism meets the four criteria. -/
def IsEuropeanism : Prop :=
  GreatMajorityOfCore f ∧ AdjacentLack f ∧ EasternIELack f ∧ WorldMinority f

instance : Decidable (GreatMajorityOfCore f) := inferInstanceAs (Decidable (_ ≤ _))
instance : Decidable (AdjacentLack f) := inferInstanceAs (Decidable (_ = _))
instance : Decidable (EasternIELack f) := inferInstanceAs (Decidable (_ = _))
instance : Decidable (WorldMinority f) := List.decidableBAll _ _
instance : Decidable (IsEuropeanism f) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

-- Articles, the `have`-perfect and experiencers reach only a majority of the core, and V + NI and
-- strict agreement not even that.
theorem greatMajorityOfCore_iff :
    GreatMajorityOfCore f ↔
      f ∉ ([.articles, .havePerfect, .nominativeExperiencers,
        .negativeIndefinitesWithoutVerbalNegation, .strictAgreement] : List Feature) := by
  revert f; decide

theorem twoThirds_iff :
    2 * (sample f ∩ core).card ≤ 3 * (isogloss f ∩ core).card ↔ GreatMajorityOfCore f := by
  revert f; decide

theorem isogloss_inter_adjacent :
    isogloss f ∩ adjacent =
      match f with
      | .articles => {breton}
      | .nominativeExperiencers => {breton, turkish}
      | .participialPassive => {breton, irish}
      | .particleComparative => {gaelic}
      | .strictAgreement => {welsh}
      | _ => ∅ := by
  revert f; decide

-- Armenian on Map 107.2, against §2.2; Baluchi and Maithili, as §2.5 grants; Punjabi, as §2.10
-- grants.
theorem union_reported_inter_easternIE :
    (isogloss f ∪ reported f) ∩ easternIE =
      match f with
      | .relativePronouns => {armenian}
      | .participialPassive => {baluchi, maithili}
      | .relativeBasedEquative => {punjabi}
      | _ => ∅ := by
  revert f; decide

theorem worldMinority : WorldMinority f := by revert f; decide

/-- Taken literally on the chapter's own maps, the four criteria of §1 select three of the twelve
features of §2, among them the dative external possessor that §2.7 calls a very robust example. -/
theorem isEuropeanism_iff :
    IsEuropeanism f ↔
      f ∈ ([.anticausativeProminence, .dativeExternalPossessors,
        .intensifierReflexiveDifferentiation] : List Feature) := by
  revert f; decide

/-- Every feature has a larger share of the core languages on its map than of the adjacent ones
(cross-multiplied), the profile that makes a linguistic area stand out among the surrounding
languages. -/
theorem standsOut :
    (isogloss f ∩ adjacent).card * (sample f ∩ core).card <
      (isogloss f ∩ core).card * (sample f ∩ adjacent).card := by
  revert f; decide

-- §2: "the nuclear SAE languages are within the SAE isogloss", in each case.
theorem nucleus_mem_isogloss :
    ∀ l ∈ ({french, german} : Finset Language), l ∈ sample f → l ∈ isogloss f := by
  revert f; decide

-- §2.9 says 13 of the 17 European languages of the sample.
theorem card_isogloss_particleComparative : (isogloss .particleComparative).card = 12 := by decide

/-! ### By language: the cluster map of §4 -/

/-- The features whose information is complete, those mapped over the whole base map: §4 combines
these nine because information on the other three is incomplete. -/
def clusterFeatures : Finset Feature := Finset.univ.filter (sample · = baseMap)

theorem clusterFeatures_eq :
    clusterFeatures =
      {.articles, .relativePronouns, .havePerfect, .participialPassive, .dativeExternalPossessors,
       .negativeIndefinitesWithoutVerbalNegation, .relativeBasedEquative, .strictAgreement,
       .intensifierReflexiveDifferentiation} := by
  decide

/-- The number of the nine features a language has. -/
def clusterScore (l : Language) : ℕ := (clusterFeatures.filter (l ∈ isogloss ·)).card

/-- The number Map 107.13 prints in a language's region, none outside its lines. -/
def printedScore : Language → Option ℕ
  | .french | .german => some 9
  | .dutch | .spanish | .portuguese | .sardinian | .italian | .albanian => some 8
  | .english | .romanian | .greek => some 7
  | .icelandic | .norwegian | .swedish | .czech => some 6
  | .latvian | .lithuanian | .polish | .russian | .ukrainian | .hungarian | .slovene
  | .serboCroatian | .bulgarian => some 5
  | .breton | .basque | .maltese => some 2
  | .welsh | .georgian | .armenian => some 1
  | _ => none

/-- Adding up the nine maps gives the number Map 107.13 prints for all but nine languages it leaves
unlabelled and two it prints one lower: Russian and Georgian, each enclosed on one map by a separate
small circle. No inference of §4 turns on the difference. -/
theorem clusterScore_eq_printed :
    (∀ l ∈ baseMap, (printedScore l = some (clusterScore l) ↔
      l ∉ ({russian, georgian, irish, finnish, estonian, nenets, komi, udmurt, tatar, lezgian,
        turkish} : Finset Language))) ∧
    clusterScore russian = 6 ∧ clusterScore georgian = 2 := by
  decide

/-- The area with at least five features stands out from the remaining languages, which have at
most two: no language has three or four. -/
theorem clusterScore_gap : ∀ l ∈ baseMap, clusterScore l ≤ 2 ∨ 5 ≤ clusterScore l := by decide

-- §4 (a): the nucleus is French and German.
theorem clusterScore_eq_nine_iff :
    ∀ l ∈ baseMap, clusterScore l = 9 ↔ l = french ∨ l = german := by
  decide

-- §4 (b): the southern languages are at least as close to the nucleus as the northern ones and
-- English, the Slavic Bulgarian excepted.
theorem north_le_south :
    ∀ n ∈ ({icelandic, norwegian, swedish, english} : Finset Language),
      ∀ s ∈ ({spanish, portuguese, sardinian, italian, romanian, albanian, greek,
        bulgarian} : Finset Language),
        (clusterScore n ≤ clusterScore s ↔ s ≠ bulgarian) := by
  decide

-- §4 (b): the Balkan languages outside Slavic are more SAE than all of Slavic.
theorem slavic_lt_balkan :
    ∀ s ∈ slavic, ∀ b ∈ ({romanian, albanian, greek} : Finset Language),
      clusterScore s < clusterScore b := by
  decide

-- §4 (c): English stands apart from the nucleus and from Dutch.
theorem english_lt_dutch_lt_german :
    clusterScore english < clusterScore dutch ∧ clusterScore dutch < clusterScore german := by
  decide

/-! ### The maps and the rest of the library -/

/-- The relative-pronoun strategy of §2.2, read off a language's relativizers: a postnominal clause
with a relative pronoun at the relativized position. -/
def HasRelativePronounStrategy (L : List Relativizer) : Prop :=
  ∃ z ∈ L, z.placement = .postNominal ∧ ∃ p, Relativization.NPRel.relPronoun ∈ z.realize p

instance (L : List Relativizer) : Decidable (HasRelativePronounStrategy L) :=
  List.decidableBEx _ _

/-- Map 107.2 agrees with the relativizers of every language with a fragment on it, on both sides
of the line. -/
theorem relativePronouns_fragments :
    ∀ x ∈ [(english, English.Relativization.relativizers), (finnish, Finnish.relativizers),
        (french, French.relativizers), (german, German.relativizers),
        (russian, Russian.relativizers), (basque, Basque.relativizers),
        (turkish, Turkish.relativizers), (welsh, Welsh.relativizers)],
      (x.1 ∈ isogloss .relativePronouns ↔ HasRelativePronounStrategy x.2) := by
  decide

-- Against §2.2, Keenan and Comrie's Hindi-Urdu has the strategy, in its postnominal *jo* clause and
-- not its correlative.
theorem hindiUrdu_relativePronoun :
    HasRelativePronounStrategy [HindiUrdu.relJo] ∧
      ¬ HasRelativePronounStrategy [HindiUrdu.relCorrelative] := by
  decide

-- Map 107.9 agrees with the comparatives of the fragments through Stassen's particle type, of
-- which Finnish and Latin have one beside a fixed-case construction.
theorem comparative_fragments :
    ∀ x ∈ [(english, [English.Comparison.than]),
        (finnish, [Finnish.Comparison.kuin, Finnish.Comparison.partitive]),
        (french, [French.Comparison.que]),
        (latin, [Latin.Comparison.quam, Latin.Comparison.ablative]),
        (russian, [Russian.Comparison.chem]), (turkish, [Turkish.Comparison.dan])],
      (x.1 ∈ isogloss .particleComparative ↔
        ∃ c ∈ x.2, Stassen1985.type1985 c = some .particle) := by
  decide

/-! ### The examples -/

/-- The languages of the rows. -/
def rowLanguages : List (Glottocode × Language) :=
  [(Glottocode.bulgarian, bulgarian), (Glottocode.english, english), (Glottocode.finnish, finnish),
   (Glottocode.georgian, georgian), (Glottocode.german, german), (Glottocode.modernGreek, greek),
   (Glottocode.hungarian, hungarian), (Glottocode.irish, irish), (Glottocode.italian, italian),
   (Glottocode.portuguese, portuguese), (Glottocode.russian, russian),
   (Glottocode.spanish, spanish), (Glottocode.swedish, swedish), (Glottocode.welsh, welsh)]

/-- The rows' names for the twelve features. -/
def rowFeatures : List (String × Feature) :=
  [("articles", .articles), ("relativePronouns", .relativePronouns), ("havePerfect", .havePerfect),
   ("nominativeExperiencers", .nominativeExperiencers), ("participialPassive", .participialPassive),
   ("anticausativeProminence", .anticausativeProminence),
   ("dativeExternalPossessors", .dativeExternalPossessors),
   ("negativeIndefinitesWithoutVerbalNegation", .negativeIndefinitesWithoutVerbalNegation),
   ("particleComparative", .particleComparative), ("relativeBasedEquative", .relativeBasedEquative),
   ("strictAgreement", .strictAgreement),
   ("intensifierReflexiveDifferentiation", .intensifierReflexiveDifferentiation)]

/-- The rows' names for the type inside each line. -/
def insideValues : List String := ["sae", "generalizing", "anticausative", "dative", "mixed"]

/-- The cell of the table a row speaks to, if its language is on its feature's map. -/
def rowCell (e : Datum) : Option (Language × Feature) :=
  (e.byLanguage rowLanguages).bind fun l ↦
    (e.parse? "feature" rowFeatures).bind fun f ↦
      if l ∈ sample f then some (l, f) else none

-- An example falls on the side of the line its type says, but for the equatives §2.10 gives for
-- Finnish and Georgian, and for the English particle relative and inverting verb, which exemplify a
-- type beside the one that puts English inside.
theorem rows_agree :
    Datum.ReadCount rowCell Examples.all 34 ∧
      ∀ e ∈ Examples.all, ∀ c ∈ rowCell e,
        ((c.1 ∈ isogloss c.2 ↔ ∃ v ∈ e.feature? "value", v ∈ insideValues) ↔
          e.id ∉ [Examples.equative_fi.id, Examples.equative_ka.id, Examples.relparticle_en.id,
            Examples.invexp_en.id]) := by
  decide

end Haspelmath2001
