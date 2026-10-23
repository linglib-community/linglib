module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Haspelmath (2001): The European linguistic area: Standard Average European

This file formalizes the argument of [haspelmath-2001] that the core European languages form a
linguistic area: a structural feature is a Europeanism when the great majority of the core
languages have it while the geographically adjacent languages, the eastern Indo-European
languages and the majority of the world's languages lack it, §1, and twelve such features are
mapped in §2. `Language` is the sample of Maps 107.1–107.13 and `isogloss` the languages each
map places inside the feature's line, the two gradient features being derived from the figures
the maps print: Bossong's inversion ratios (`experiencerRatio`, Map 107.4) and the percentages
of anticausative pairs (`anticausativePercent`, Map 107.6). `IsEuropeanism` states criteria
(i)–(iii) over the map sample and `WorldMinority` criterion (iv) over the world-wide surveys
the chapter cites.

`clusterScore` is the cluster map of §4, the number of the nine selected features a language
has: `nucleus_eq` derives the Charlemagne nucleus, French and German with all nine;
`eight_eq` and `seven_eq` the next two layers; and `area_eq` the area of at least five
features that stands out from the remaining languages. The criteria hold on the map data with
two exceptions the chapter itself flags, `majorityOfCore_iff`: negative indefinites without
verbal negation and strict subject agreement are not majority features of the core, and
Armenian carries the relative-pronoun strategy on Map 107.2, `easternIELack_iff`.

## Implementation notes

The feature values are read from the maps of the scanned chapter, and the readings are checked
against the layer counts §4 states: the cluster map's isopleths reproduce exactly. "The great
majority" of criterion (i) is read as a majority, and "lack" in (ii) as fewer than half,
relative to the languages a feature's map covers. Map 107.5 places Hungarian inside the
participial-passive line although §2.5 says Hungarian has no passive; the map is followed, as
the cluster count of five for Hungarian requires. Maps 107.4, 107.6 and 107.9 cover different
samples (Bossong's, the 1993 verb-pair survey's and Stassen's), so criteria are evaluated
per map.

## TODO

* §4 says the languages outside the area have at most two of the nine features; on the maps
  Maltese has four and Basque, Finnish and Estonian three, `outside_le_four`.

## References

* [haspelmath-2001]
-/

@[expose] public section

namespace Haspelmath2001

/-- The languages of Maps 107.1–107.13, by the abbreviations of §6, with the languages of
Bossong's sample (Map 107.4) and Stassen's (Map 107.9) that the base map lacks. -/
inductive Language where
  | albanian | armenian | basque | breton | bulgarian | czech | dutch | english | estonian
  | finnish | french | gaelic | georgian | german | greek | hungarian | icelandic | irish
  | italian | komi | latin | latvian | laz | lezgian | lithuanian | maltese | mari | mordvin
  | nenets | norwegian | polish | portuguese | romanian | russian | saami | sardinian
  | serboCroatian | slovene | spanish | swedish | tatar | turkish | ubykh | udmurt | ukrainian
  | welsh
  deriving DecidableEq, Fintype, Repr

/-- The genealogical groups §1 reasons with: the branches of the core, the neighbours of
criterion (ii), and the eastern Indo-European branch of criterion (iii) present on the maps. -/
inductive Family where
  | romance | germanic | slavic | baltic | greek | albanian | westernUralic
  | celtic | basque | turkic | easternUralic | kartvelian | nakhDaghestanian | abkhazAdyghean
  | afroAsiatic | armenian | latin
  deriving DecidableEq, Repr

def Language.family : Language → Family
  | .french | .italian | .spanish | .portuguese | .sardinian | .romanian => .romance
  | .german | .dutch | .english | .norwegian | .swedish | .icelandic => .germanic
  | .russian | .ukrainian | .polish | .czech | .slovene | .serboCroatian | .bulgarian => .slavic
  | .lithuanian | .latvian => .baltic
  | .greek => .greek
  | .albanian => .albanian
  | .hungarian | .finnish | .estonian => .westernUralic
  | .irish | .welsh | .breton | .gaelic => .celtic
  | .basque => .basque
  | .turkish | .tatar => .turkic
  | .saami | .mari | .mordvin | .komi | .udmurt | .nenets => .easternUralic
  | .georgian | .laz => .kartvelian
  | .lezgian => .nakhDaghestanian
  | .ubykh => .abkhazAdyghean
  | .maltese => .afroAsiatic
  | .armenian => .armenian
  | .latin => .latin

/-- The core European languages of §1: Romance, Germanic, Balto-Slavic, the Balkan languages,
and the westernmost Finno-Ugrian languages. -/
def Family.IsCore : Family → Prop
  | .romance | .germanic | .slavic | .baltic | .greek | .albanian | .westernUralic => True
  | _ => False

/-- The geographically adjacent languages of criterion (ii). -/
def Family.IsAdjacent : Family → Prop
  | .celtic | .basque | .turkic | .easternUralic | .kartvelian | .nakhDaghestanian
  | .abkhazAdyghean | .afroAsiatic => True
  | _ => False

instance : DecidablePred Family.IsCore :=
  λ f => by unfold Family.IsCore; cases f <;> infer_instance
instance : DecidablePred Family.IsAdjacent :=
  λ f => by unfold Family.IsAdjacent; cases f <;> infer_instance

/-! ### The twelve features of §2 -/

/-- The Europeanisms of §2.1–§2.12. -/
inductive Feature where
  | articles
  | relativePronouns
  | havePerfect
  | nominativeExperiencers
  | participialPassive
  | anticausativeProminence
  | dativeExternalPossessors
  | negativeIndefinitesWithoutVerbalNegation
  | particleComparative
  | relativeBasedEquative
  | strictAgreement
  | intensifierReflexiveDifferentiation
  deriving DecidableEq, Fintype, Repr

open Language

/-- The languages of the base map shared by Maps 107.1–3, 107.5, 107.7–8 and 107.10–13. -/
def baseMap : Finset Language :=
  {albanian, armenian, basque, breton, bulgarian, czech, dutch, english, estonian, finnish,
   french, georgian, german, greek, hungarian, icelandic, irish, italian, komi, latvian,
   lezgian, lithuanian, maltese, nenets, norwegian, polish, portuguese, romanian, russian,
   sardinian, serboCroatian, slovene, spanish, swedish, tatar, turkish, udmurt, ukrainian,
   welsh}

/-- Bossong's ratio of inverting to generalizing experiential predicates, in hundredths, as
Map 107.4 prints it. -/
def experiencerRatio : Language → Option ℕ
  | icelandic => some 229 | irish => some 221 | welsh => some 92 | norwegian => some 12
  | swedish => some 12 | finnish => some 87 | saami => some 81 | estonian => some 83
  | latvian => some 164 | mari => some 79 | lithuanian => some 83 | mordvin => some 116
  | english => some 0 | dutch => some 64 | german => some 74 | czech => some 76
  | polish => some 88 | russian => some 211 | udmurt => some 109 | breton => some 24
  | french => some 12 | hungarian => some 22 | basque => some 10 | italian => some 48
  | serboCroatian => some 75 | spanish => some 43 | portuguese => some 14 | romanian => some 225
  | albanian => some 102 | bulgarian => some 48 | lezgian => some 500 | georgian => some 308
  | maltese => some 69 | greek => some 27 | turkish => some 46
  | _ => none

/-- The percentage of anticausative inchoative–causative pairs, as Map 107.6 prints it. -/
def anticausativePercent : Language → Option ℕ
  | finnish => some 47 | lithuanian => some 74 | russian => some 100 | udmurt => some 46
  | english => some 100 | german => some 100 | french => some 91 | hungarian => some 44
  | romanian => some 96 | greek => some 100 | lezgian => some 40 | georgian => some 67
  | turkish => some 34 | armenian => some 65
  | _ => none

/-- The languages a feature's map covers. -/
def mapped : Feature → Finset Language
  | .nominativeExperiencers => Finset.univ.filter (experiencerRatio · ≠ none)
  | .anticausativeProminence => Finset.univ.filter (anticausativePercent · ≠ none)
  | .particleComparative =>
    {gaelic, english, dutch, french, basque, latin, finnish, latvian, hungarian, russian,
     albanian, greek, breton, nenets, ubykh, laz, turkish}
  | _ => baseMap

/-- The languages inside a feature's isogloss: the SAE value. Map 107.4 draws the line at
Bossong's ratio 0.8, predominant generalization below it, and Map 107.6 at 70% of
anticausative pairs. -/
def isogloss : Feature → Finset Language
  | .articles =>
    {norwegian, swedish, english, dutch, german, french, breton, basque, spanish, sardinian,
     portuguese, italian, hungarian, romanian, albanian, greek}
  | .relativePronouns =>
    {icelandic, norwegian, swedish, finnish, estonian, latvian, lithuanian, polish, russian,
     english, dutch, german, czech, french, hungarian, ukrainian, slovene, italian,
     serboCroatian, romanian, albanian, bulgarian, greek, spanish, sardinian, portuguese,
     georgian, armenian}
  | .havePerfect =>
    {icelandic, norwegian, swedish, english, dutch, german, czech, french, spanish, sardinian,
     portuguese, italian, romanian, albanian, greek}
  | .nominativeExperiencers =>
    Finset.univ.filter λ l => (experiencerRatio l).any (· < 80)
  | .participialPassive =>
    {icelandic, irish, breton, norwegian, swedish, finnish, estonian, latvian, lithuanian,
     polish, russian, english, dutch, german, czech, french, hungarian, ukrainian, slovene,
     italian, serboCroatian, romanian, albanian, bulgarian, greek, spanish, sardinian,
     portuguese, maltese}
  | .anticausativeProminence =>
    Finset.univ.filter λ l => (anticausativePercent l).any (70 ≤ ·)
  | .dativeExternalPossessors =>
    {dutch, german, czech, polish, latvian, lithuanian, russian, ukrainian, french, hungarian,
     slovene, italian, serboCroatian, romanian, albanian, bulgarian, greek, spanish, sardinian,
     portuguese, basque, maltese}
  | .negativeIndefinitesWithoutVerbalNegation =>
    {icelandic, norwegian, swedish, english, dutch, german, french, spanish, sardinian,
     portuguese, italian, albanian, georgian}
  | .particleComparative =>
    {gaelic, english, dutch, french, basque, latin, finnish, latvian, hungarian, russian,
     albanian, greek}
  | .relativeBasedEquative =>
    {english, dutch, german, czech, polish, latvian, lithuanian, russian, french, hungarian,
     ukrainian, slovene, italian, serboCroatian, romanian, albanian, bulgarian, greek, spanish,
     sardinian, portuguese, maltese}
  | .strictAgreement => {icelandic, welsh, english, dutch, german, french, russian}
  | .intensifierReflexiveDifferentiation =>
    {icelandic, norwegian, swedish, finnish, estonian, latvian, lithuanian, polish, russian,
     german, czech, french, basque, slovene, italian, serboCroatian, romanian, albanian,
     bulgarian, greek, spanish, sardinian, portuguese, maltese, ukrainian}

/-! ### The criteria of §1 -/

variable (f : Feature)

/-- The core languages a feature's map covers. -/
def core : Finset Language := (mapped f).filter (·.family.IsCore)

/-- The adjacent languages a feature's map covers. -/
def adjacent : Finset Language := (mapped f).filter (·.family.IsAdjacent)

/-- Criterion (i): the great majority of the core European languages have the feature, read as
a majority of the core languages on the map. -/
def MajorityOfCore : Prop := (core f).card < 2 * (isogloss f ∩ core f).card

/-- Criterion (ii): the adjacent languages lack the feature, read as fewer than half of the
adjacent languages on the map. -/
def AdjacentLack : Prop := 2 * (isogloss f ∩ adjacent f).card < (adjacent f).card

/-- Criterion (iii): the eastern Indo-European languages lack the feature; Armenian is the one
on the maps. -/
def EasternIELack : Prop := ∀ l ∈ isogloss f, l.family ≠ .armenian

/-- The world-wide surveys the chapter cites for criterion (iv), as the number of languages
with the feature out of the sample: Dryer's languages with both articles, the participle-plus-
auxiliary passives of the 1990 survey, Kahrel's V + NI negation patterns, and Siewierska's
strict-agreement languages. -/
def worldSurvey : Feature → Option (ℕ × ℕ)
  | .articles => some (31, 400)
  | .participialPassive => some (4, 80)
  | .negativeIndefinitesWithoutVerbalNegation => some (5, 40)
  | .strictAgreement => some (2, 272)
  | _ => none

/-- Criterion (iv): the feature is not found in the majority of the world's languages. -/
def WorldMinority : Prop := ∀ s ∈ worldSurvey f, 2 * s.1 < s.2

instance : Decidable (MajorityOfCore f) := inferInstanceAs (Decidable (_ < _))
instance : Decidable (AdjacentLack f) := inferInstanceAs (Decidable (_ < _))
instance : Decidable (EasternIELack f) := Finset.decidableDforallFinset
instance : Decidable (WorldMinority f) := Option.decidableForallMem _

/-- A Europeanism: criteria (i)–(iii) on the map and (iv) on the surveys. -/
structure IsEuropeanism : Prop where
  majorityOfCore : MajorityOfCore f
  adjacentLack : AdjacentLack f
  easternIELack : EasternIELack f
  worldMinority : WorldMinority f

/-- Criterion (i) holds of every feature except the two the chapter describes as narrow: the
V + NI negation of French and Germanic, §2.8, and strict agreement, "characteristic of a few
European languages", §2.11. -/
theorem majorityOfCore_iff :
    MajorityOfCore f ↔
      f ≠ .negativeIndefinitesWithoutVerbalNegation ∧ f ≠ .strictAgreement := by
  revert f; decide

theorem adjacentLack : AdjacentLack f := by revert f; decide

theorem easternIELack_iff : EasternIELack f ↔ f ≠ .relativePronouns := by revert f; decide

theorem worldMinority : WorldMinority f := by revert f; decide

theorem havePerfect_isEuropeanism : IsEuropeanism .havePerfect :=
  ⟨by decide, adjacentLack _, by decide, worldMinority _⟩

/-! ### The cluster map of §4 -/

/-- The nine features Map 107.13 combines, those with complete information. -/
def clusterFeatures : Finset Feature :=
  {.articles, .relativePronouns, .havePerfect, .participialPassive, .dativeExternalPossessors,
   .negativeIndefinitesWithoutVerbalNegation, .relativeBasedEquative, .strictAgreement,
   .intensifierReflexiveDifferentiation}

/-- The number of the nine features a language has: the isopleth of Map 107.13. -/
def clusterScore (l : Language) : ℕ := (clusterFeatures.filter (l ∈ isogloss ·)).card

theorem nucleus_eq : baseMap.filter (clusterScore · = 9) = {french, german} := by decide

theorem eight_eq :
    baseMap.filter (clusterScore · = 8) =
      {dutch, spanish, portuguese, sardinian, italian, albanian} := by
  decide

theorem seven_eq : baseMap.filter (clusterScore · = 7) = {english, greek, romanian} := by
  decide

theorem area_eq :
    baseMap.filter (5 ≤ clusterScore ·) =
      {french, german, dutch, spanish, portuguese, sardinian, italian, albanian, english,
       greek, romanian, icelandic, norwegian, swedish, czech, russian, polish, latvian,
       lithuanian, ukrainian, serboCroatian, slovene, hungarian, bulgarian} := by
  decide

theorem outside_le_four : ∀ l ∈ baseMap, clusterScore l < 5 → clusterScore l ≤ 4 := by
  decide

end Haspelmath2001
