module

public import Linglib.Data.Wordlist.Schema

/-!
# `ParamoreBennett2026`: word forms

Auto-generated from `Linglib/Data/Wordlist/ParamoreBennett2026.json` by `scripts/gen_wordlist.py`.
Do not edit by hand; edit the JSON and re-run the generator. Declarations live in `namespace
ParamoreBennett2026.Wordlist`.
-/

@[expose] public section

namespace ParamoreBennett2026.Wordlist

open CLDF.Wordlist

/-- The values of `Condition` the source distinguishes. -/
inductive Condition where
  /-- A stem ending in a vowel, a glide and an oral vowel, `oral [VGV]` in the source. -/
  | oral
  /-- A stem ending in a vowel, a glide, a vowel and a nasal consonant of the same morpheme, `pre-N
  [VGṼN]` in the source. -/
  | preN
  /-- A stem ending in a vowel, a glide and a contrastive nasal vowel, with a postposition beginning
  in a nasal consonant, `contrastive nasal [ṼG̃Ṽ=NV]` in the source. -/
  | nasalNV
  /-- A stem ending in a vowel, a glide and a contrastive nasal vowel, with a postposition beginning
  in an oral stop, `contrastive nasal [ṼG̃Ṽ=CV]` in the source. -/
  | nasalCV
  deriving DecidableEq, Repr

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

def Lexemes.pumicestone : Lexeme :=
  { id := "pumicestone", languageId := "west2386", parameterId := "pumicestone" }

def Lexemes.generalPublic : Lexeme :=
  { id := "generalPublic", languageId := "west2386", parameterId := "generalPublic" }

def Lexemes.division : Lexeme :=
  { id := "division", languageId := "west2386", parameterId := "division" }

def Lexemes.branch : Lexeme :=
  { id := "branch", languageId := "west2386", parameterId := "branch" }

def Lexemes.twentySeven : Lexeme :=
  { id := "twentySeven", languageId := "west2386", parameterId := "twentySeven" }

def Lexemes.piousMen : Lexeme :=
  { id := "piousMen", languageId := "west2386", parameterId := "piousMen" }

def Lexemes.air : Lexeme :=
  { id := "air", languageId := "west2386", parameterId := "air" }

def Lexemes.twentyFour : Lexeme :=
  { id := "twentyFour", languageId := "west2386", parameterId := "twentyFour" }

def Lexemes.cotLeg : Lexeme :=
  { id := "cotLeg", languageId := "west2386", parameterId := "cotLeg" }

def Lexemes.widow : Lexeme :=
  { id := "widow", languageId := "west2386", parameterId := "widow" }

def Lexemes.medicine : Lexeme :=
  { id := "medicine", languageId := "west2386", parameterId := "medicine" }

def Lexemes.uncle : Lexeme :=
  { id := "uncle", languageId := "west2386", parameterId := "uncle" }

def Lexemes.boasting : Lexeme :=
  { id := "boasting", languageId := "west2386", parameterId := "boasting" }

def Lexemes.chief : Lexeme :=
  { id := "chief", languageId := "west2386", parameterId := "chief" }

def Lexemes.youth : Lexeme :=
  { id := "youth", languageId := "west2386", parameterId := "youth" }

def Lexemes.omumSeed : Lexeme :=
  { id := "omumSeed", languageId := "west2386", parameterId := "omumSeed" }

def Lexemes.recognition : Lexeme :=
  { id := "recognition", languageId := "west2386", parameterId := "recognition" }

def Lexemes.attention : Lexeme :=
  { id := "attention", languageId := "west2386", parameterId := "attention" }

def Lexemes.taking : Lexeme :=
  { id := "taking", languageId := "west2386", parameterId := "taking" }

def Lexemes.inThatWay : Lexeme :=
  { id := "inThatWay", languageId := "west2386", parameterId := "inThatWay" }

def Lexemes.bothSides : Lexeme :=
  { id := "bothSides", languageId := "west2386", parameterId := "bothSides" }

def Lexemes.somehow : Lexeme :=
  { id := "somehow", languageId := "west2386", parameterId := "somehow" }

def Lexemes.inVain : Lexeme :=
  { id := "inVain", languageId := "west2386", parameterId := "inVain" }

def Lexemes.fish : Lexeme :=
  { id := "fish", languageId := "west2386", parameterId := "fish" }

def Lexemes.woman : Lexeme :=
  { id := "woman", languageId := "west2386", parameterId := "woman" }

def Lexemes.breaths : Lexeme :=
  { id := "breaths", languageId := "west2386", parameterId := "breaths" }

def pumicestone : Form Cell :=
  { id := "paramorebennett2026_pumicestone"
    lexeme := Lexemes.pumicestone
    cell := {}
    form := "tʃɑ̃ɑ̃ʋ̃ẽẽ"
    segments := ["tʃ", "ɑ̃ɑ̃", "ʋ̃", "ẽẽ"]
    source := [
      ⟨"paramore-bennett-2026", "(5a)"⟩
    ] }

def generalPublic : Form Cell :=
  { id := "paramorebennett2026_generalPublic"
    lexeme := Lexemes.generalPublic
    cell := {}
    form := "ɑɑʋɑ̃ɑ̃m"
    segments := ["ɑɑ", "ʋ", "ɑ̃ɑ̃", "m"]
    source := [
      ⟨"paramore-bennett-2026", "(5b)"⟩
    ] }

def division : Form Cell :=
  { id := "paramorebennett2026_division"
    lexeme := Lexemes.division
    cell := {}
    form := "və̃ɳɖɪ̃ʋ̃ɑ̃ɑ̃"
    segments := ["ʋ", "ə̃", "ɳ", "ɖ", "ɪ̃", "ʋ̃", "ɑ̃ɑ̃"]
    source := [
      ⟨"paramore-bennett-2026", "(2c)"⟩
    ] }

def branches : Form Cell :=
  { id := "paramorebennett2026_branches"
    lexeme := Lexemes.branch
    cell := {}
    form := "ʃɑɑxɑ̃ɑ̃"
    segments := ["ʃ", "ɑɑ", "x", "ɑ̃ɑ̃"]
    source := [
      ⟨"paramore-bennett-2026", "(2d)"⟩
    ] }

def twentySevenDa : Form Cell :=
  { id := "paramorebennett2026_twentySevenDa"
    lexeme := Lexemes.twentySeven
    cell := {}
    form := "sət-ɑɑjii də"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

def piousMenDa : Form Cell :=
  { id := "paramorebennett2026_piousMenDa"
    lexeme := Lexemes.piousMen
    cell := {}
    form := "ɔɔlii-jɑɑ də"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

def airDa : Form Cell :=
  { id := "paramorebennett2026_airDa"
    lexeme := Lexemes.air
    cell := {}
    form := "həʋɑɑ də"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

def twentyFourDa : Form Cell :=
  { id := "paramorebennett2026_twentyFourDa"
    lexeme := Lexemes.twentyFour
    cell := {}
    form := "tʃoo-ʋii də"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

def cotLegDa : Form Cell :=
  { id := "paramorebennett2026_cotLegDa"
    lexeme := Lexemes.cotLeg
    cell := {}
    form := "pɑɑʋee də"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

def widowDa : Form Cell :=
  { id := "paramorebennett2026_widowDa"
    lexeme := Lexemes.widow
    cell := {}
    form := "beeʋɑɑ də"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

def medicineDa : Form Cell :=
  { id := "paramorebennett2026_medicineDa"
    lexeme := Lexemes.medicine
    cell := {}
    form := "dəʋɑɑ də"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

def uncleDa : Form Cell :=
  { id := "paramorebennett2026_uncleDa"
    lexeme := Lexemes.uncle
    cell := {}
    form := "tɑɑʋuu də"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

def boastingDa : Form Cell :=
  { id := "paramorebennett2026_boastingDa"
    lexeme := Lexemes.boasting
    cell := {}
    form := "ʋəkʰɑɑʋee də"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

def chiefDa : Form Cell :=
  { id := "paramorebennett2026_chiefDa"
    lexeme := Lexemes.chief
    cell := {}
    form := "mʊkʰiijɑɑ də"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

def youthDa : Form Cell :=
  { id := "paramorebennett2026_youthDa"
    lexeme := Lexemes.youth
    cell := {}
    form := "dʒəʋɑɑɳ də"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

def omumSeedDa : Form Cell :=
  { id := "paramorebennett2026_omumSeedDa"
    lexeme := Lexemes.omumSeed
    cell := {}
    form := "ədʒəʋɛɛɳ də"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

def recognitionDa : Form Cell :=
  { id := "paramorebennett2026_recognitionDa"
    lexeme := Lexemes.recognition
    cell := {}
    form := "siijɑɑɳ də"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

def attentionDa : Form Cell :=
  { id := "paramorebennett2026_attentionDa"
    lexeme := Lexemes.attention
    cell := {}
    form := "teejɑɑɳ də"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

def takingDe : Form Cell :=
  { id := "paramorebennett2026_takingDe"
    lexeme := Lexemes.taking
    cell := {}
    form := "lɛɛ-jɑɑɳ de"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

def generalPublicDa : Form Cell :=
  { id := "paramorebennett2026_generalPublicDa"
    lexeme := Lexemes.generalPublic
    cell := {}
    form := "ɑɑʋɑɑm də"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

def pumicestoneNu : Form Cell :=
  { id := "paramorebennett2026_pumicestoneNu"
    lexeme := Lexemes.pumicestone
    cell := {}
    form := "tʃɑɑʋẽẽ nʊ"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

def inThatWayNu : Form Cell :=
  { id := "paramorebennett2026_inThatWayNu"
    lexeme := Lexemes.inThatWay
    cell := {}
    form := "uu-ʋẽẽ nʊ"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

def bothSidesNu : Form Cell :=
  { id := "paramorebennett2026_bothSidesNu"
    lexeme := Lexemes.bothSides
    cell := {}
    form := "doo-ʋɑ̃ɑ̃ nʊ"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

def somehowNu : Form Cell :=
  { id := "paramorebennett2026_somehowNu"
    lexeme := Lexemes.somehow
    cell := {}
    form := "kii-ʋẽẽ nʊ"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

def inVainNu : Form Cell :=
  { id := "paramorebennett2026_inVainNu"
    lexeme := Lexemes.inVain
    cell := {}
    form := "ɛɛ-ʋẽẽ nʊ"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

def fishNi : Form Cell :=
  { id := "paramorebennett2026_fishNi"
    lexeme := Lexemes.fish
    cell := {}
    form := "matʃii-jɑ̃ɑ̃ nɪ"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

def womanNi : Form Cell :=
  { id := "paramorebennett2026_womanNi"
    lexeme := Lexemes.woman
    cell := {}
    form := "tiiʋĩĩ nɪ"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

def breathsNi : Form Cell :=
  { id := "paramorebennett2026_breathsNi"
    lexeme := Lexemes.breaths
    cell := {}
    form := "sɑɑ-ʋɑ̃ɑ̃ nɪ"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

def pumicestoneDa : Form Cell :=
  { id := "paramorebennett2026_pumicestoneDa"
    lexeme := Lexemes.pumicestone
    cell := {}
    form := "tʃɑɑʋẽẽ də"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

def inThatWayDa : Form Cell :=
  { id := "paramorebennett2026_inThatWayDa"
    lexeme := Lexemes.inThatWay
    cell := {}
    form := "uu-ʋẽẽ də"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

def bothSidesPaase : Form Cell :=
  { id := "paramorebennett2026_bothSidesPaase"
    lexeme := Lexemes.bothSides
    cell := {}
    form := "doo-ʋɑ̃ɑ̃ pɑɑse"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

def somehowDa : Form Cell :=
  { id := "paramorebennett2026_somehowDa"
    lexeme := Lexemes.somehow
    cell := {}
    form := "kii-ʋẽẽ də"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

def inVainDa : Form Cell :=
  { id := "paramorebennett2026_inVainDa"
    lexeme := Lexemes.inVain
    cell := {}
    form := "ɛɛ-ʋẽẽ də"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

def fishDa : Form Cell :=
  { id := "paramorebennett2026_fishDa"
    lexeme := Lexemes.fish
    cell := {}
    form := "matʃii-jɑ̃ɑ̃ də"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

def womanDa : Form Cell :=
  { id := "paramorebennett2026_womanDa"
    lexeme := Lexemes.woman
    cell := {}
    form := "tiiʋĩĩ də"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

def breathsDa : Form Cell :=
  { id := "paramorebennett2026_breathsDa"
    lexeme := Lexemes.breaths
    cell := {}
    form := "sɑɑ-ʋɑ̃ɑ̃ də"
    source := [
      ⟨"paramore-bennett-2026", "Table 3"⟩
    ] }

/-- The source's analysis of a form, its parse rather than data. -/
structure Analysis where
  /-- The form analysed. -/
  form : Form Cell
  /-- The `Underlying` column, the segments of the underlying form the paper gives, the stem of a
  stimulus. -/
  underlying : (List String)
  /-- The `Clitic` column, the segments of the postposition a stimulus was recorded with. -/
  clitic : Option (List String) := none
  /-- The `Condition` column, the condition of Experiment 2 a stimulus belongs to. -/
  condition : Option Condition := none
  deriving DecidableEq, Repr

def pumicestone.analysis : Analysis :=
  { form := pumicestone,
    underlying := ["tʃ", "ɑɑ", "ʋ", "ẽẽ"] }

def generalPublic.analysis : Analysis :=
  { form := generalPublic,
    underlying := ["ɑɑ", "ʋ", "ɑɑ", "m"] }

def division.analysis : Analysis :=
  { form := division,
    underlying := ["ʋ", "ə", "ɳ", "ɖ", "ɪ", "ʋ", "ɑ̃ɑ̃"] }

def branches.analysis : Analysis :=
  { form := branches,
    underlying := ["ʃ", "ɑɑ", "k", "ɑ̃ɑ̃"] }

def twentySevenDa.analysis : Analysis :=
  { form := twentySevenDa,
    underlying := ["s", "ə", "t", "ɑɑ", "j", "ii"],
    clitic := some ["d", "ə"],
    condition := some Condition.oral }

def piousMenDa.analysis : Analysis :=
  { form := piousMenDa,
    underlying := ["ɔɔ", "l", "ii", "j", "ɑɑ"],
    clitic := some ["d", "ə"],
    condition := some Condition.oral }

def airDa.analysis : Analysis :=
  { form := airDa,
    underlying := ["h", "ə", "ʋ", "ɑɑ"],
    clitic := some ["d", "ə"],
    condition := some Condition.oral }

def twentyFourDa.analysis : Analysis :=
  { form := twentyFourDa,
    underlying := ["tʃ", "oo", "ʋ", "ii"],
    clitic := some ["d", "ə"],
    condition := some Condition.oral }

def cotLegDa.analysis : Analysis :=
  { form := cotLegDa,
    underlying := ["p", "ɑɑ", "ʋ", "ee"],
    clitic := some ["d", "ə"],
    condition := some Condition.oral }

def widowDa.analysis : Analysis :=
  { form := widowDa,
    underlying := ["b", "ee", "ʋ", "ɑɑ"],
    clitic := some ["d", "ə"],
    condition := some Condition.oral }

def medicineDa.analysis : Analysis :=
  { form := medicineDa,
    underlying := ["d", "ə", "ʋ", "ɑɑ"],
    clitic := some ["d", "ə"],
    condition := some Condition.oral }

def uncleDa.analysis : Analysis :=
  { form := uncleDa,
    underlying := ["t", "ɑɑ", "ʋ", "uu"],
    clitic := some ["d", "ə"],
    condition := some Condition.oral }

def boastingDa.analysis : Analysis :=
  { form := boastingDa,
    underlying := ["ʋ", "ə", "kʰ", "ɑɑ", "ʋ", "ee"],
    clitic := some ["d", "ə"],
    condition := some Condition.oral }

def chiefDa.analysis : Analysis :=
  { form := chiefDa,
    underlying := ["m", "ʊ", "kʰ", "ii", "j", "ɑɑ"],
    clitic := some ["d", "ə"],
    condition := some Condition.oral }

def youthDa.analysis : Analysis :=
  { form := youthDa,
    underlying := ["dʒ", "ə", "ʋ", "ɑɑ", "ɳ"],
    clitic := some ["d", "ə"],
    condition := some Condition.preN }

def omumSeedDa.analysis : Analysis :=
  { form := omumSeedDa,
    underlying := ["ə", "dʒ", "ə", "ʋ", "ɛɛ", "ɳ"],
    clitic := some ["d", "ə"],
    condition := some Condition.preN }

def recognitionDa.analysis : Analysis :=
  { form := recognitionDa,
    underlying := ["s", "ii", "j", "ɑɑ", "ɳ"],
    clitic := some ["d", "ə"],
    condition := some Condition.preN }

def attentionDa.analysis : Analysis :=
  { form := attentionDa,
    underlying := ["t", "ee", "j", "ɑɑ", "ɳ"],
    clitic := some ["d", "ə"],
    condition := some Condition.preN }

def takingDe.analysis : Analysis :=
  { form := takingDe,
    underlying := ["l", "ɛɛ", "j", "ɑɑ", "ɳ"],
    clitic := some ["d", "ee"],
    condition := some Condition.preN }

def generalPublicDa.analysis : Analysis :=
  { form := generalPublicDa,
    underlying := ["ɑɑ", "ʋ", "ɑɑ", "m"],
    clitic := some ["d", "ə"],
    condition := some Condition.preN }

def pumicestoneNu.analysis : Analysis :=
  { form := pumicestoneNu,
    underlying := ["tʃ", "ɑɑ", "ʋ", "ẽẽ"],
    clitic := some ["n", "ʊ"],
    condition := some Condition.nasalNV }

def inThatWayNu.analysis : Analysis :=
  { form := inThatWayNu,
    underlying := ["uu", "ʋ", "ẽẽ"],
    clitic := some ["n", "ʊ"],
    condition := some Condition.nasalNV }

def bothSidesNu.analysis : Analysis :=
  { form := bothSidesNu,
    underlying := ["d", "oo", "ʋ", "ɑ̃ɑ̃"],
    clitic := some ["n", "ʊ"],
    condition := some Condition.nasalNV }

def somehowNu.analysis : Analysis :=
  { form := somehowNu,
    underlying := ["k", "ii", "ʋ", "ẽẽ"],
    clitic := some ["n", "ʊ"],
    condition := some Condition.nasalNV }

def inVainNu.analysis : Analysis :=
  { form := inVainNu,
    underlying := ["ɛɛ", "ʋ", "ẽẽ"],
    clitic := some ["n", "ʊ"],
    condition := some Condition.nasalNV }

def fishNi.analysis : Analysis :=
  { form := fishNi,
    underlying := ["m", "ə", "tʃ", "ii", "j", "ɑ̃ɑ̃"],
    clitic := some ["n", "ɪ"],
    condition := some Condition.nasalNV }

def womanNi.analysis : Analysis :=
  { form := womanNi,
    underlying := ["t", "ii", "ʋ", "ĩĩ"],
    clitic := some ["n", "ɪ"],
    condition := some Condition.nasalNV }

def breathsNi.analysis : Analysis :=
  { form := breathsNi,
    underlying := ["s", "ɑɑ", "ʋ", "ɑ̃ɑ̃"],
    clitic := some ["n", "ɪ"],
    condition := some Condition.nasalNV }

def pumicestoneDa.analysis : Analysis :=
  { form := pumicestoneDa,
    underlying := ["tʃ", "ɑɑ", "ʋ", "ẽẽ"],
    clitic := some ["d", "ə"],
    condition := some Condition.nasalCV }

def inThatWayDa.analysis : Analysis :=
  { form := inThatWayDa,
    underlying := ["uu", "ʋ", "ẽẽ"],
    clitic := some ["d", "ə"],
    condition := some Condition.nasalCV }

def bothSidesPaase.analysis : Analysis :=
  { form := bothSidesPaase,
    underlying := ["d", "oo", "ʋ", "ɑ̃ɑ̃"],
    clitic := some ["p", "ɑɑ", "s", "ee"],
    condition := some Condition.nasalCV }

def somehowDa.analysis : Analysis :=
  { form := somehowDa,
    underlying := ["k", "ii", "ʋ", "ẽẽ"],
    clitic := some ["d", "ə"],
    condition := some Condition.nasalCV }

def inVainDa.analysis : Analysis :=
  { form := inVainDa,
    underlying := ["ɛɛ", "ʋ", "ẽẽ"],
    clitic := some ["d", "ə"],
    condition := some Condition.nasalCV }

def fishDa.analysis : Analysis :=
  { form := fishDa,
    underlying := ["m", "ə", "tʃ", "ii", "j", "ɑ̃ɑ̃"],
    clitic := some ["d", "ə"],
    condition := some Condition.nasalCV }

def womanDa.analysis : Analysis :=
  { form := womanDa,
    underlying := ["t", "ii", "ʋ", "ĩĩ"],
    clitic := some ["d", "ə"],
    condition := some Condition.nasalCV }

def breathsDa.analysis : Analysis :=
  { form := breathsDa,
    underlying := ["s", "ɑɑ", "ʋ", "ɑ̃ɑ̃"],
    clitic := some ["d", "ə"],
    condition := some Condition.nasalCV }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.pumicestone, Lexemes.generalPublic, Lexemes.division,
  Lexemes.branch, Lexemes.twentySeven, Lexemes.piousMen, Lexemes.air, Lexemes.twentyFour,
  Lexemes.cotLeg, Lexemes.widow, Lexemes.medicine, Lexemes.uncle, Lexemes.boasting, Lexemes.chief,
  Lexemes.youth, Lexemes.omumSeed, Lexemes.recognition, Lexemes.attention, Lexemes.taking,
  Lexemes.inThatWay, Lexemes.bothSides, Lexemes.somehow, Lexemes.inVain, Lexemes.fish,
  Lexemes.woman, Lexemes.breaths]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [pumicestone, generalPublic, division, branches, twentySevenDa,
  piousMenDa, airDa, twentyFourDa, cotLegDa, widowDa, medicineDa, uncleDa, boastingDa, chiefDa,
  youthDa, omumSeedDa, recognitionDa, attentionDa, takingDe, generalPublicDa, pumicestoneNu,
  inThatWayNu, bothSidesNu, somehowNu, inVainNu, fishNi, womanNi, breathsNi, pumicestoneDa,
  inThatWayDa, bothSidesPaase, somehowDa, inVainDa, fishDa, womanDa, breathsDa]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := []

/-- Every analysis of the data. -/
def analyses : List Analysis := [pumicestone.analysis, generalPublic.analysis, division.analysis,
  branches.analysis, twentySevenDa.analysis, piousMenDa.analysis, airDa.analysis,
  twentyFourDa.analysis, cotLegDa.analysis, widowDa.analysis, medicineDa.analysis, uncleDa.analysis,
  boastingDa.analysis, chiefDa.analysis, youthDa.analysis, omumSeedDa.analysis,
  recognitionDa.analysis, attentionDa.analysis, takingDe.analysis, generalPublicDa.analysis,
  pumicestoneNu.analysis, inThatWayNu.analysis, bothSidesNu.analysis, somehowNu.analysis,
  inVainNu.analysis, fishNi.analysis, womanNi.analysis, breathsNi.analysis, pumicestoneDa.analysis,
  inThatWayDa.analysis, bothSidesPaase.analysis, somehowDa.analysis, inVainDa.analysis,
  fishDa.analysis, womanDa.analysis, breathsDa.analysis]

end ParamoreBennett2026.Wordlist
