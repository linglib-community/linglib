module

public import Linglib.Data.Examples.Haspelmath2001
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Statistics.Haspelmath2001
public import Linglib.Data.StructureDataset.Haspelmath2001
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
public import Studies.Stassen1985

/-!
# Haspelmath (2001): The European linguistic area: Standard Average European

A structural feature is a Europeanism, §1 says, when the great majority of the core European
languages have it, the adjacent and the eastern Indo-European languages lack it, and most of the
world's languages lack it too; §2 maps twelve such features. Read literally on those maps, [the
four criteria pass three of the twelve](##isEuropeanism_iff), while [every feature is commoner in
the core than next door](##standsOut), the profile by which §1 recognizes a linguistic area. §4 sums
nine of the lines: the sum [gives the number Map 107.13 prints](##clusterScore_eq_printed) for all
languages but two and [leaves nothing between two features and five](##clusterScore_gap). Fragments
confirm [Map 107.2](##relativePronouns_fragments) and [Map 107.9](##comparative_fragments).

## Implementation notes

* `StructureDataset.maps` is read from page images, each solid line checked by flood fill from
  outside. `StructureDataset.prose` is what §2 says of the eastern Indo-European languages.
* "The great majority" is read as three quarters, and [two thirds selects the same
  features](##twoThirds_iff). "Lack" is literal, and the "perhaps" of Afro-Asiatic excludes it.

## Errata

* §2.1 denies neighbouring languages both articles; Map 107.1 encloses Breton.
* §2.2 denies eastern Indo-European the strategy; Map 107.2 encloses Armenian, and [Hindi-Urdu has
  it](##hindiUrdu_relativePronoun).
* §2.5 denies Hungarian a passive and Celtic this one; Map 107.5 encloses Hungarian, Irish, Breton.
* §2.9 prints a sample of 19, less than its own counts need (`surveys` has Stassen's 110), and 13
  European particle comparatives where Map 107.9 encloses 12.
* §2.10 lists Finnish and Georgian as relative-based; [Map 107.10 leaves them out](##rows_agree).
* Map 107.4 leaves out Mari at 0.79, [against its cut of 0.8](##experiencer_side).
* Map 107.13 prints 5 for Russian and 1 for Georgian, [where the lines sum to 6 and
  2](##clusterScore_eq_printed).

## TODO

* The surveys of §3.1 and §3.5, the features of §3.6, and the five origins §5 weighs.
* Map 107.8 against the negative concord items of the polarity fragments.

## References

* [haspelmath-2001]
* [keenan-comrie-1977]
* [stassen-1985]
-/

@[expose] public section

namespace Haspelmath2001

open CLDF.StructureDataset StructureDataset

/-- The side of a map's line a language lies on. -/
inductive Side where
  | inside
  | outside
  deriving DecidableEq, Repr

namespace StructureDataset.Row

/-- The side a language's code puts it on, `sae` being the code inside the line, if it has one. -/
def sideOf? {C : Type*} [DecidableEq C] (sae : C) (l : List (Coded C)) : Option Side :=
  l.head?.map fun c ↦ if c.code = sae then .inside else .outside

/-- The side of the line of `f`'s map a language lies on, `none` if the map does not cover it. -/
def side? (r : Row) : Feature → Option Side
  | .articles => sideOf? .both r.articles
  | .relativePronouns => sideOf? .relativePronoun r.relativeClause
  | .havePerfect => sideOf? .havePerfect r.havePerfect
  | .nominativeExperiencers => sideOf? .generalizing r.experiencer
  | .participialPassive => sideOf? .participial r.participialPassive
  | .anticausativeProminence => sideOf? .high r.anticausative
  | .dativeExternalPossessors => sideOf? .dative r.externalPossessor
  | .negativeIndefinitesWithoutVerbalNegation => sideOf? .withoutVerbalNegation r.negativeIndefinite
  | .particleComparative => sideOf? .particle r.comparativeType
  | .relativeBasedEquative => sideOf? .relativeBased r.equative
  | .strictAgreement => sideOf? .strict r.subjectAgreement
  | .intensifierReflexiveDifferentiation => sideOf? .differentiated r.intensifierReflexive

/-- The language lies inside the line of `f`'s map. -/
def Has (r : Row) (f : Feature) : Prop := r.side? f = some .inside

/-- The map of `f` covers the language. -/
def OnMap (r : Row) (f : Feature) : Prop := (r.side? f).isSome = true

instance (r : Row) : DecidablePred r.Has := fun _ ↦ inferInstanceAs (Decidable (_ = _))
instance (r : Row) : DecidablePred r.OnMap := fun _ ↦ inferInstanceAs (Decidable (_ = _))

end StructureDataset.Row

/-! ### The criteria of §1 -/

/-- The rows of the given branches. -/
def ofBranches (rows : List Row) (bs : List Branch) : List Row :=
  rows.filter fun r ↦ r.branch.any (·.code ∈ bs)

/-- The core European languages: Romance, Germanic, Balto-Slavic, the Balkan languages, and the
westernmost Finno-Ugrian languages. -/
def core : List Row :=
  ofBranches maps [.romance, .germanic, .slavic, .baltic, .greek, .albanian, .westernUralic]

/-- The adjacent languages of criterion (ii). -/
def adjacent : List Row :=
  ofBranches maps [.celtic, .turkic, .easternUralic, .abkhazAdyghean, .nakhDaghestanian]

/-- The eastern Indo-European languages of criterion (iii), on the maps and in the prose. -/
def easternIE : List Row := ofBranches (maps ++ prose) [.armenian, .iranian, .indic]

/-- The languages of `G` that `f`'s map covers. -/
def covered (G : List Row) (f : Feature) : List Row := G.filter (·.OnMap f)

/-- The languages of `G` inside the line of `f`'s map. -/
def inside (G : List Row) (f : Feature) : List Row := G.filter (·.Has f)

variable (f : Feature)

/-- Criterion (i): the great majority of the core languages on the map have the feature, read as
at least three quarters. -/
def GreatMajorityOfCore : Prop := 3 * (covered core f).length ≤ 4 * (inside core f).length

/-- Criterion (ii): the adjacent languages lack the feature. -/
def AdjacentLack : Prop := ∀ r ∈ adjacent, ¬ r.Has f

/-- Criterion (iii): the eastern Indo-European languages lack the feature. -/
def EasternIELack : Prop := ∀ r ∈ easternIE, ¬ r.Has f

/-- Criterion (iv): the surveys cited for the feature find it in a minority of their sample. -/
def WorldMinority : Prop := ∀ s ∈ surveys, s.feature = f → 2 * s.withFeature < s.sample

/-- A Europeanism meets the four criteria. -/
def IsEuropeanism : Prop :=
  GreatMajorityOfCore f ∧ AdjacentLack f ∧ EasternIELack f ∧ WorldMinority f

instance : Decidable (GreatMajorityOfCore f) := inferInstanceAs (Decidable (_ ≤ _))
instance : Decidable (AdjacentLack f) := List.decidableBAll _ _
instance : Decidable (EasternIELack f) := List.decidableBAll _ _
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
    2 * (covered core f).length ≤ 3 * (inside core f).length ↔ GreatMajorityOfCore f := by
  revert f; decide

-- Breton, Turkish, Irish, Gaelic and Welsh are the adjacent languages inside a line.
theorem adjacentLack_iff :
    AdjacentLack f ↔
      f ∉ ([.articles, .nominativeExperiencers, .participialPassive, .particleComparative,
        .strictAgreement] : List Feature) := by
  revert f; decide

-- Armenian on Map 107.2, against §2.2; Baluchi and Maithili, as §2.5 grants; Punjabi, as §2.10
-- grants.
theorem easternIELack_iff :
    EasternIELack f ↔
      f ∉ ([.relativePronouns, .participialPassive, .relativeBasedEquative] : List Feature) := by
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
    (inside adjacent f).length * (covered core f).length <
      (inside core f).length * (covered adjacent f).length := by
  revert f; decide

-- §2: "the nuclear SAE languages are within the SAE isogloss", in each case.
theorem nucleus_inside :
    ∀ r ∈ maps, r.language ∈ [french, german] → r.OnMap f → r.Has f := by
  revert f; decide

/-! ### The printed numbers of Maps 107.4 and 107.6 -/

-- The line of Map 107.4 follows the cut at 0.8 stated in §2.4, except at Mari.
theorem experiencer_side :
    ∀ r ∈ maps, ∀ d ∈ r.experiencerRatio,
      ((r.Has .nominativeExperiencers ↔ d.code.hundredths < 80) ↔ r.language ≠ mari) := by
  decide

-- The solid line of Map 107.6 is its legend's 70%.
theorem anticausative_side :
    ∀ r ∈ maps ++ prose, ∀ d ∈ r.anticausativePercent,
      (r.Has .anticausativeProminence ↔ 7000 ≤ d.code.hundredths) := by
  decide

/-! ### The cluster map of §4 -/

/-- The features with the fullest information: §4 combines nine of the twelve because information
on the other three is incomplete. -/
def clusterFeatures : Finset Feature :=
  Finset.univ.filter fun f ↦ ∀ g, (covered maps g).length ≤ (covered maps f).length

theorem clusterFeatures_eq :
    clusterFeatures =
      {.articles, .relativePronouns, .havePerfect, .participialPassive, .dativeExternalPossessors,
       .negativeIndefinitesWithoutVerbalNegation, .relativeBasedEquative, .strictAgreement,
       .intensifierReflexiveDifferentiation} := by
  decide

/-- The number of the nine features a language has, its isopleth on Map 107.13. -/
def clusterScore (r : Row) : ℕ := (clusterFeatures.filter r.Has).card

/-- Adding up the lines of the nine maps gives the number Map 107.13 prints for every language it
labels but two: Russian, which the maps put at 6 and §2.11's reservation about its past tense
leaves at 5, and Georgian, which they put at 2 and the map at 1. -/
theorem clusterScore_eq_printed :
    ∀ r ∈ maps, ∀ d ∈ r.printedScore,
      ((clusterScore r : ℤ) = d.code.mantissa ↔ r.language ∉ [russian, georgian]) := by
  decide

/-- The area with at least five features stands out from the remaining languages, which have at
most two: no language has three or four. -/
theorem clusterScore_gap : ∀ r ∈ maps, clusterScore r ≤ 2 ∨ 5 ≤ clusterScore r := by
  decide

-- §4 (a): the nucleus is French and German.
theorem clusterScore_eq_nine_iff :
    ∀ r ∈ maps, clusterScore r = 9 ↔ r.language ∈ [french, german] := by
  decide

-- §4 (b): the southern languages are at least as close to the nucleus as the northern ones and
-- English, the Slavic Bulgarian excepted.
theorem north_le_south :
    ∀ n ∈ maps.filter (·.language ∈ [icelandic, norwegian, swedish, english]),
      ∀ s ∈ maps.filter (·.language ∈ [spanish, portuguese, sardinian, italian, romanian, albanian,
        greek, bulgarian]),
        (clusterScore n ≤ clusterScore s ↔ s.language ≠ bulgarian) := by
  decide

-- §4 (b): the Balkan languages outside Slavic are more SAE than all of Slavic.
theorem slavic_lt_balkan :
    ∀ s ∈ ofBranches maps [.slavic], ∀ b ∈ maps.filter (·.language ∈ [romanian, albanian, greek]),
      clusterScore s < clusterScore b := by
  decide

-- §4 (c): English stands apart from the nucleus and from Dutch.
theorem english_lt_dutch_german :
    ∀ e ∈ maps.filter (·.language = english), ∀ r ∈ maps.filter (·.language ∈ [dutch, german]),
      clusterScore e < clusterScore r := by
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
      ∀ r ∈ maps.filter (·.language = x.1),
        (r.Has .relativePronouns ↔ HasRelativePronounStrategy x.2) := by
  decide

-- Against §2.2, Keenan and Comrie's Hindi-Urdu has the strategy the prose denies Indic, in its
-- postnominal *jo* clause and not its correlative.
theorem hindiUrdu_relativePronoun :
    HasRelativePronounStrategy [HindiUrdu.relJo] ∧
      ¬ HasRelativePronounStrategy [HindiUrdu.relCorrelative] ∧
      ∀ r ∈ prose.filter (·.language = indic), ¬ r.Has .relativePronouns := by
  decide

-- Map 107.9 agrees with the comparatives of the fragments through Stassen's particle type, of
-- which Finnish and Latin have one beside a fixed-case construction.
theorem comparative_fragments :
    ∀ x ∈ [(english, [English.Comparison.than]),
        (finnish, [Finnish.Comparison.kuin, Finnish.Comparison.partitive]),
        (french, [French.Comparison.que]),
        (latin, [Latin.Comparison.quam, Latin.Comparison.ablative]),
        (russian, [Russian.Comparison.chem]), (turkish, [Turkish.Comparison.dan])],
      ∀ r ∈ maps.filter (·.language = x.1),
        (r.Has .particleComparative ↔ ∃ c ∈ x.2, Stassen1985.type1985 c = some .particle) := by
  decide

/-! ### The examples -/

/-- The rows' names for the twelve features. -/
def featureNames : List (String × Feature) :=
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

-- An example falls on the side of the line its type says, but for the equatives §2.10 gives for
-- Finnish and Georgian, and for the English particle relative and inverting verb, which exemplify a
-- type beside the one that puts English inside.
theorem rows_agree :
    ∀ e ∈ Examples.all, ∀ r ∈ maps ++ prose, r.language.glottocode = some e.language →
      ∀ f ∈ e.parse? "feature" featureNames, r.OnMap f →
        ((r.Has f ↔ ∃ v ∈ e.feature? "value", v ∈ insideValues) ↔
          e.id ∉ [Examples.equative_fi.id, Examples.equative_ka.id, Examples.relparticle_en.id,
            Examples.invexp_en.id]) := by
  decide

/-! ### Table 107.1 -/

-- §3.4: Europe has far more comitative-instrumental syncretism than the world, Oceania far less.
theorem syncretism_extremes (a : Area) :
    (a ≠ .europe → (table1071 a).syncreticPercent.mantissa <
      (table1071 .europe).syncreticPercent.mantissa) ∧
    (a ≠ .oceania → (table1071 .oceania).syncreticPercent.mantissa <
      (table1071 a).syncreticPercent.mantissa) := by
  revert a; decide

end Haspelmath2001
