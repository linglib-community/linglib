module

public import Mathlib.Data.Finset.Image
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Core.Order.Flat

/-!
# PHOIBLE 2.0

PHOIBLE 2.0 is a database of 3,020 phoneme inventories, drawn from eight source databases, in
which every phoneme is decomposed into distinctive features. Its table has a row for each
phoneme of each inventory. An `Inventory` collects the rows of one inventory, and each of its
`Phoneme`s carries the phoneme's glyph, its `FeatureMatrix` and what the source records about
it. The generated inventories are in `Data/PHOIBLE/Inventories/`, and `Data/PHOIBLE/Chart.lean`
gives the feature matrix of each glyph.

## Main definitions

* `Data.PHOIBLE.Feature`: the features, one column of the table each.
* `Data.PHOIBLE.FeatureMatrix`: an assignment of `+` and `−` to some of the features.
* `Data.PHOIBLE.FeatureRow`, `Data.PHOIBLE.FeatureMatrix.ofRow`: a row of the table on its
  feature columns, and its feature matrix.
* `Data.PHOIBLE.Source`: the source databases.
* `Data.PHOIBLE.Phoneme`, `Data.PHOIBLE.Inventory`: a phoneme of an inventory, and an inventory.
* `Data.PHOIBLE.Inventory.featureMatrices`: the feature matrices of an inventory's phonemes.

## Implementation notes

Where PHOIBLE has `NA`, a field is `none`. This means that the source does not record the value,
not that it records an absence; `Source` says what each source records. A blank dialect, which
the SAPHON source writes in place of `NA`, is `none` too.

The generated feature matrices are given by their rows, so that the value of one at a feature is
read by a single case split. A proof by `decide` about segments built from the chart evaluates
their matrices at every feature, and a search through a list of the specified values made that
its main cost.

A complex segment, such as a prenasalized stop or a diphthong, has a contour value such as `+,-`
on a feature that changes within it. The feature matrix of such a segment takes the meet of the
contour's values in the subsumption order, so it leaves that feature unspecified.

## References

* [moran-mccloy-2019]
* [hayes-2009]
-/

@[expose] public section

namespace Data.PHOIBLE

/-- The class of a segment, the `SegmentClass` column. -/
inductive SegmentClass where
  | consonant
  | vowel
  | tone
  deriving DecidableEq, Fintype

/-- The source database of an inventory, the `Source` column. The sources differ in what they
record. The AA, PH and SPA sources list the allophones of every phoneme and the others of none,
and all but RA, SAPHON and SPA say of every phoneme whether it is marginal. Tones appear only in
inventories from AA, PH, RA and SPA. -/
inductive Source where
  /-- The Stanford Phonology Archive. -/
  | spa
  /-- The UCLA Phonological Segment Inventory Database. -/
  | upsid
  /-- Hartell's *Alphabets des langues africaines*, as digitized by Chanard. -/
  | aa
  /-- The inventories the PHOIBLE contributors took from grammars, articles and theses, with
  Christopher Green and Steven Moran's inventories of African and Southeast Asian languages. -/
  | ph
  /-- Ramaswami's survey of the phonetics of the languages of India. -/
  | ra
  /-- The South American Phonological Inventory Database. -/
  | saphon
  /-- The Database of Eurasian Phonological Inventories. -/
  | ea
  /-- Erich Round's phonemic inventories of Australian languages. -/
  | er
  deriving DecidableEq, Fintype

/-- Each PHOIBLE feature is a column of the table. The feature system is loosely based on Hayes's
and goes beyond it, with features for length, tone and stress among others. -/
inductive Feature where
  | syllabic | short | long | consonantal | sonorant | continuant | delayedRelease
  | approximant | tap | trill | nasal | lateral | labial | round | labiodental | coronal
  | anterior | distributed | strident | dorsal | high | low | front | back | tense
  | retractedTongueRoot | advancedTongueRoot | periodicGlottalSource | epilaryngealSource
  | spreadGlottis | constrictedGlottis | fortis | lenis | raisedLarynxEjective
  | loweredLarynxImplosive | click | tone | stress
  deriving DecidableEq, Fintype

/-- A feature matrix gives some features the value `+` (`true`) or `−` (`false`) and leaves the
others unspecified, as PHOIBLE's value `0`, not applicable, does. -/
abbrev FeatureMatrix := Feature → Flat Bool

/-- A row of the table on its feature columns, a value for each feature, unspecified unless
given. -/
structure FeatureRow where
  syllabic : Flat Bool := ⊥
  short : Flat Bool := ⊥
  long : Flat Bool := ⊥
  consonantal : Flat Bool := ⊥
  sonorant : Flat Bool := ⊥
  continuant : Flat Bool := ⊥
  delayedRelease : Flat Bool := ⊥
  approximant : Flat Bool := ⊥
  tap : Flat Bool := ⊥
  trill : Flat Bool := ⊥
  nasal : Flat Bool := ⊥
  lateral : Flat Bool := ⊥
  labial : Flat Bool := ⊥
  round : Flat Bool := ⊥
  labiodental : Flat Bool := ⊥
  coronal : Flat Bool := ⊥
  anterior : Flat Bool := ⊥
  distributed : Flat Bool := ⊥
  strident : Flat Bool := ⊥
  dorsal : Flat Bool := ⊥
  high : Flat Bool := ⊥
  low : Flat Bool := ⊥
  front : Flat Bool := ⊥
  back : Flat Bool := ⊥
  tense : Flat Bool := ⊥
  retractedTongueRoot : Flat Bool := ⊥
  advancedTongueRoot : Flat Bool := ⊥
  periodicGlottalSource : Flat Bool := ⊥
  epilaryngealSource : Flat Bool := ⊥
  spreadGlottis : Flat Bool := ⊥
  constrictedGlottis : Flat Bool := ⊥
  fortis : Flat Bool := ⊥
  lenis : Flat Bool := ⊥
  raisedLarynxEjective : Flat Bool := ⊥
  loweredLarynxImplosive : Flat Bool := ⊥
  click : Flat Bool := ⊥
  tone : Flat Bool := ⊥
  stress : Flat Bool := ⊥

/-- The feature matrix of a row reads each feature off its column. -/
def FeatureMatrix.ofRow (r : FeatureRow) : FeatureMatrix := fun
  | .syllabic => r.syllabic
  | .short => r.short
  | .long => r.long
  | .consonantal => r.consonantal
  | .sonorant => r.sonorant
  | .continuant => r.continuant
  | .delayedRelease => r.delayedRelease
  | .approximant => r.approximant
  | .tap => r.tap
  | .trill => r.trill
  | .nasal => r.nasal
  | .lateral => r.lateral
  | .labial => r.labial
  | .round => r.round
  | .labiodental => r.labiodental
  | .coronal => r.coronal
  | .anterior => r.anterior
  | .distributed => r.distributed
  | .strident => r.strident
  | .dorsal => r.dorsal
  | .high => r.high
  | .low => r.low
  | .front => r.front
  | .back => r.back
  | .tense => r.tense
  | .retractedTongueRoot => r.retractedTongueRoot
  | .advancedTongueRoot => r.advancedTongueRoot
  | .periodicGlottalSource => r.periodicGlottalSource
  | .epilaryngealSource => r.epilaryngealSource
  | .spreadGlottis => r.spreadGlottis
  | .constrictedGlottis => r.constrictedGlottis
  | .fortis => r.fortis
  | .lenis => r.lenis
  | .raisedLarynxEjective => r.raisedLarynxEjective
  | .loweredLarynxImplosive => r.loweredLarynxImplosive
  | .click => r.click
  | .tone => r.tone
  | .stress => r.stress

/-- A phoneme of an inventory is a glyph with its feature matrix and what the inventory's source
records about it. -/
structure Phoneme where
  /-- The IPA glyph. -/
  glyph : String
  /-- The allophones, among them the glyph itself, and `none` when the source lists none. -/
  allophones : Option (List String)
  /-- Whether the phoneme is marginal in the inventory, `none` when the source does not say. -/
  marginal : Option Bool
  /-- The class of the glyph. -/
  segmentClass : SegmentClass
  /-- The feature matrix of the glyph. -/
  features : FeatureMatrix

/-- An inventory is a list of phonemes with the language variety it describes and its source. -/
structure Inventory where
  /-- The PHOIBLE inventory identifier. -/
  id : ℕ
  /-- The Glottocode of the variety. -/
  glottocode : Option String
  /-- The ISO 639-3 code of the language. -/
  iso : String
  /-- The name of the language. -/
  languageName : String
  /-- The dialect described, when the source names one. -/
  specificDialect : Option String
  /-- The source database. -/
  source : Source
  /-- The phonemes. -/
  phonemes : List Phoneme

namespace Inventory

/-- The feature matrices of an inventory's phonemes. -/
def featureMatrices (I : Inventory) : Finset FeatureMatrix :=
  (I.phonemes.map (·.features)).toFinset

@[simp] theorem mem_featureMatrices {I : Inventory} {m : FeatureMatrix} :
    m ∈ I.featureMatrices ↔ ∃ y ∈ I.phonemes, y.features = m := by
  simp [featureMatrices]

/-- A set lies in an image of the feature matrices when each of its elements is the image of a
phoneme's matrix, a condition `decide` checks without deduplicating the inventory. -/
theorem subset_image_featureMatrices_iff {β : Type*} [DecidableEq β] {I : Inventory}
    {f : FeatureMatrix → β} {S : Finset β} :
    S ⊆ I.featureMatrices.image f ↔ ∀ x ∈ S, ∃ y ∈ I.phonemes, f y.features = x := by
  simp [Finset.subset_iff]

end Inventory

end Data.PHOIBLE
