module

public import Linglib.Data.Forms.Schema

/-!
# `Alderete2001`: word forms

Auto-generated from `Linglib/Data/Forms/Alderete2001.json` by `scripts/gen_forms.py`. Do not edit by
hand; edit the JSON and re-run the generator. Declarations live in `namespace Alderete2001.Forms`.
-/

@[expose] public section

namespace Alderete2001.Forms

open Data.Forms

/-- The values of `OORelation` the source distinguishes. -/
inductive OORelation where
  /-- OO_Dom, the relation of a dominant affix ((20), (54)), `dom` in the source. -/
  | dominant
  /-- OO_Rec, the relation of a recessive affix ((20), (54)), `rec` in the source. -/
  | recessive
  /-- OO_Ex, the relation of the Luo exchange-inducing plural (§2.2.2), `ex` in the source. -/
  | exchange
  deriving DecidableEq, Repr

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

/-- The singular cell, `Number=Sing`. -/
def sg : Cell := { number := ↑UD.Number.Sing }

/-- The plural cell, `Number=Plur`. -/
def pl : Cell := { number := ↑UD.Number.Plur }

/-- The conditional cell, `Mood=Cnd`. -/
def cnd : Cell := { mood := ↑UD.Mood.Cnd }

/-- The masculine cell, `Gender=Masc`. -/
def masc : Cell := { gender := ↑UD.Gender.Masc }

/-- The feminine cell, `Gender=Fem`. -/
def fem : Cell := { gender := ↑UD.Gender.Fem }

/-- The comparative cell, `Degree=Cmp`. -/
def cmp : Cell := { degree := ↑UD.Degree.Cmp }

def Lexemes.arm : Lexeme :=
  { id := "arm", languageId := "luok1236", parameterId := "arm", pos := ↑UD.UPOS.NOUN }

def Lexemes.walking_stick : Lexeme :=
  { id := "walking_stick", languageId := "luok1236", parameterId := "walking_stick",
    pos := ↑UD.UPOS.NOUN }

def Lexemes.bone : Lexeme :=
  { id := "bone", languageId := "luok1236", parameterId := "bone", pos := ↑UD.UPOS.NOUN }

def Lexemes.brother : Lexeme :=
  { id := "brother", languageId := "luok1236", parameterId := "brother", pos := ↑UD.UPOS.NOUN }

def Lexemes.read : Lexeme :=
  { id := "read", languageId := "nucl1643", variety := "Tokyo", parameterId := "read",
    pos := ↑UD.UPOS.VERB }

def Lexemes.call : Lexeme :=
  { id := "call", languageId := "nucl1643", variety := "Tokyo", parameterId := "call",
    pos := ↑UD.UPOS.VERB }

def Lexemes.oily : Lexeme :=
  { id := "oily", languageId := "nucl1643", variety := "Tokyo", parameterId := "oily",
    pos := ↑UD.UPOS.ADJ }

def Lexemes.sniffily : Lexeme :=
  { id := "sniffily", languageId := "nucl1643", variety := "Tokyo", parameterId := "sniffily",
    pos := ↑UD.UPOS.ADJ }

def Lexemes.childish : Lexeme :=
  { id := "childish", languageId := "nucl1643", variety := "Tokyo", parameterId := "childish",
    pos := ↑UD.UPOS.ADJ }

def Lexemes.coquettish : Lexeme :=
  { id := "coquettish", languageId := "nucl1643", variety := "Tokyo", parameterId := "coquettish",
    pos := ↑UD.UPOS.ADJ }

def Lexemes.zealous : Lexeme :=
  { id := "zealous", languageId := "nucl1643", variety := "Tokyo", parameterId := "zealous",
    pos := ↑UD.UPOS.ADJ }

def Lexemes.affected : Lexeme :=
  { id := "affected", languageId := "nucl1643", variety := "Tokyo", parameterId := "affected",
    pos := ↑UD.UPOS.ADJ }

def Lexemes.native_of_tokyo : Lexeme :=
  { id := "native_of_tokyo", languageId := "nucl1643", variety := "Tokyo",
    parameterId := "native_of_tokyo", pos := ↑UD.UPOS.NOUN }

def Lexemes.native_of_nigata : Lexeme :=
  { id := "native_of_nigata", languageId := "nucl1643", variety := "Tokyo",
    parameterId := "native_of_nigata", pos := ↑UD.UPOS.NOUN }

def Lexemes.native_of_osaka : Lexeme :=
  { id := "native_of_osaka", languageId := "nucl1643", variety := "Tokyo",
    parameterId := "native_of_osaka", pos := ↑UD.UPOS.NOUN }

def Lexemes.native_of_kobe : Lexeme :=
  { id := "native_of_kobe", languageId := "nucl1643", variety := "Tokyo",
    parameterId := "native_of_kobe", pos := ↑UD.UPOS.NOUN }

def Lexemes.native_of_nagoya : Lexeme :=
  { id := "native_of_nagoya", languageId := "nucl1643", variety := "Tokyo",
    parameterId := "native_of_nagoya", pos := ↑UD.UPOS.NOUN }

def Lexemes.native_of_new_york : Lexeme :=
  { id := "native_of_new_york", languageId := "nucl1643", variety := "Tokyo",
    parameterId := "native_of_new_york", pos := ↑UD.UPOS.NOUN }

def Lexemes.edge : Lexeme :=
  { id := "edge", languageId := "nucl1643", variety := "Tokyo", parameterId := "edge",
    pos := ↑UD.UPOS.NOUN }

def Lexemes.wise : Lexeme :=
  { id := "wise", languageId := "limb1263", variety := "Maasbracht", parameterId := "wise",
    pos := ↑UD.UPOS.ADJ }

def Lexemes.stiff : Lexeme :=
  { id := "stiff", languageId := "limb1263", variety := "Maasbracht", parameterId := "stiff",
    pos := ↑UD.UPOS.ADJ }

def Lexemes.bald : Lexeme :=
  { id := "bald", languageId := "limb1263", variety := "Maasbracht", parameterId := "bald",
    pos := ↑UD.UPOS.ADJ }

def Lexemes.paralysed : Lexeme :=
  { id := "paralysed", languageId := "limb1263", variety := "Maasbracht",
    parameterId := "paralysed", pos := ↑UD.UPOS.ADJ }

def Lexemes.refined : Lexeme :=
  { id := "refined", languageId := "limb1263", variety := "Maasbracht", parameterId := "refined",
    pos := ↑UD.UPOS.ADJ }

def Lexemes.tough : Lexeme :=
  { id := "tough", languageId := "limb1263", variety := "Maasbracht", parameterId := "tough",
    pos := ↑UD.UPOS.ADJ }

def arm_sg : Form Cell :=
  { id := "alderete2001_arm_sg"
    lexeme := Lexemes.arm
    cell := sg
    form := "bat"
    source := [
      ⟨"alderete-2001", "(6a)"⟩,
      ⟨"alderete-2001", "(7)"⟩,
      ⟨"alderete-2001", "(11a)"⟩
    ] }

def arm_pl : Form Cell :=
  { id := "alderete2001_arm_pl"
    lexeme := Lexemes.arm
    cell := pl
    form := "bed-e"
    source := [
      ⟨"alderete-2001", "(6a)"⟩,
      ⟨"alderete-2001", "(7)"⟩,
      ⟨"alderete-2001", "(11a)"⟩
    ] }

def walking_stick_sg : Form Cell :=
  { id := "alderete2001_walking_stick_sg"
    lexeme := Lexemes.walking_stick
    cell := sg
    form := "luθ"
    source := [
      ⟨"alderete-2001", "(6a)"⟩
    ] }

def walking_stick_pl : Form Cell :=
  { id := "alderete2001_walking_stick_pl"
    lexeme := Lexemes.walking_stick
    cell := pl
    form := "luð-e"
    source := [
      ⟨"alderete-2001", "(6a)"⟩
    ] }

def bone_sg : Form Cell :=
  { id := "alderete2001_bone_sg"
    lexeme := Lexemes.bone
    cell := sg
    form := "čogo"
    source := [
      ⟨"alderete-2001", "(6b)"⟩,
      ⟨"alderete-2001", "(7)"⟩,
      ⟨"alderete-2001", "(11b)"⟩
    ] }

def bone_pl : Form Cell :=
  { id := "alderete2001_bone_pl"
    lexeme := Lexemes.bone
    cell := pl
    form := "čok-e"
    source := [
      ⟨"alderete-2001", "(6b)"⟩,
      ⟨"alderete-2001", "(7)"⟩,
      ⟨"alderete-2001", "(11b)"⟩
    ] }

def brother_sg : Form Cell :=
  { id := "alderete2001_brother_sg"
    lexeme := Lexemes.brother
    cell := sg
    form := "owadu"
    source := [
      ⟨"alderete-2001", "(6b)"⟩
    ] }

def brother_pl : Form Cell :=
  { id := "alderete2001_brother_pl"
    lexeme := Lexemes.brother
    cell := pl
    form := "owet-e"
    source := [
      ⟨"alderete-2001", "(6b)"⟩
    ] }

def yondara : Form Cell :=
  { id := "alderete2001_yondara"
    lexeme := Lexemes.read
    cell := cnd
    form := "yón-dara"
    source := [
      ⟨"alderete-2001", "(1)"⟩
    ] }

def yondara_call : Form Cell :=
  { id := "alderete2001_yondara_call"
    lexeme := Lexemes.call
    cell := cnd
    form := "yon-dára"
    source := [
      ⟨"alderete-2001", "(1)"⟩
    ] }

def aburappoi : Form Cell :=
  { id := "alderete2001_aburappoi"
    lexeme := Lexemes.oily
    cell := {}
    form := "abura-ppó-i"
    source := [
      ⟨"alderete-2001", "(17a)"⟩
    ] }

def kazeppoi : Form Cell :=
  { id := "alderete2001_kazeppoi"
    lexeme := Lexemes.sniffily
    cell := {}
    form := "kaze-ppó-i"
    source := [
      ⟨"alderete-2001", "(2a)"⟩,
      ⟨"alderete-2001", "(17a)"⟩
    ] }

def kodomoppoi : Form Cell :=
  { id := "alderete2001_kodomoppoi"
    lexeme := Lexemes.childish
    cell := {}
    form := "kodomo-ppó-i"
    source := [
      ⟨"alderete-2001", "(17a)"⟩
    ] }

def adappoi : Form Cell :=
  { id := "alderete2001_adappoi"
    lexeme := Lexemes.coquettish
    cell := {}
    form := "ada-ppó-i"
    source := [
      ⟨"alderete-2001", "(2a)"⟩,
      ⟨"alderete-2001", "(17b)"⟩,
      ⟨"alderete-2001", "(21)"⟩
    ] }

def netuppoi : Form Cell :=
  { id := "alderete2001_netuppoi"
    lexeme := Lexemes.zealous
    cell := {}
    form := "netu-ppó-i"
    source := [
      ⟨"alderete-2001", "(17b)"⟩
    ] }

def kizappoi : Form Cell :=
  { id := "alderete2001_kizappoi"
    lexeme := Lexemes.affected
    cell := {}
    form := "kiza-ppó-i"
    source := [
      ⟨"alderete-2001", "(17b)"⟩
    ] }

def edokko : Form Cell :=
  { id := "alderete2001_edokko"
    lexeme := Lexemes.native_of_tokyo
    cell := {}
    form := "edo-kko"
    source := [
      ⟨"alderete-2001", "(2b)"⟩,
      ⟨"alderete-2001", "(18a)"⟩
    ] }

def niigatakko : Form Cell :=
  { id := "alderete2001_niigatakko"
    lexeme := Lexemes.native_of_nigata
    cell := {}
    form := "niigata-kko"
    source := [
      ⟨"alderete-2001", "(18a)"⟩
    ] }

def oosakakko : Form Cell :=
  { id := "alderete2001_oosakakko"
    lexeme := Lexemes.native_of_osaka
    cell := {}
    form := "oosaka-kko"
    source := [
      ⟨"alderete-2001", "(18a)"⟩
    ] }

def koobekko : Form Cell :=
  { id := "alderete2001_koobekko"
    lexeme := Lexemes.native_of_kobe
    cell := {}
    form := "koobe-kko"
    source := [
      ⟨"alderete-2001", "(2b)"⟩,
      ⟨"alderete-2001", "(18b)"⟩,
      ⟨"alderete-2001", "(23)"⟩,
      ⟨"alderete-2001", "(25a)"⟩,
      ⟨"alderete-2001", "(28)"⟩
    ] }

def nagoyakko : Form Cell :=
  { id := "alderete2001_nagoyakko"
    lexeme := Lexemes.native_of_nagoya
    cell := {}
    form := "nagoya-kko"
    source := [
      ⟨"alderete-2001", "(18b)"⟩
    ] }

def nyuuyookukko : Form Cell :=
  { id := "alderete2001_nyuuyookukko"
    lexeme := Lexemes.native_of_new_york
    cell := {}
    form := "nyuuyooku-kko"
    source := [
      ⟨"alderete-2001", "(18b)"⟩
    ] }

def hasi : Form Cell :=
  { id := "alderete2001_hasi"
    lexeme := Lexemes.edge
    cell := {}
    form := "hasi"
    source := [
      ⟨"alderete-2001", "(12)"⟩,
      ⟨"alderete-2001", "(28)"⟩
    ] }

def wise : Form Cell :=
  { id := "alderete2001_wise"
    lexeme := Lexemes.wise
    cell := {}
    form := "wíís"
    source := [
      ⟨"alderete-2001", "(42)"⟩
    ] }

def wise_masc : Form Cell :=
  { id := "alderete2001_wise_masc"
    lexeme := Lexemes.wise
    cell := masc
    form := "wíiz-ə"
    source := [
      ⟨"alderete-2001", "(42)"⟩
    ] }

def wise_fem : Form Cell :=
  { id := "alderete2001_wise_fem"
    lexeme := Lexemes.wise
    cell := fem
    form := "wíis"
    source := [
      ⟨"alderete-2001", "(42)"⟩
    ] }

def wise_cmp : Form Cell :=
  { id := "alderete2001_wise_cmp"
    lexeme := Lexemes.wise
    cell := cmp
    form := "wíiz-ər"
    source := [
      ⟨"alderete-2001", "(42)"⟩
    ] }

def stiff : Form Cell :=
  { id := "alderete2001_stiff"
    lexeme := Lexemes.stiff
    cell := {}
    form := "stííf"
    source := [
      ⟨"alderete-2001", "(42)"⟩
    ] }

def stiff_masc : Form Cell :=
  { id := "alderete2001_stiff_masc"
    lexeme := Lexemes.stiff
    cell := masc
    form := "stíiv-ə"
    source := [
      ⟨"alderete-2001", "(42)"⟩
    ] }

def stiff_fem : Form Cell :=
  { id := "alderete2001_stiff_fem"
    lexeme := Lexemes.stiff
    cell := fem
    form := "stíif"
    source := [
      ⟨"alderete-2001", "(42)"⟩
    ] }

def stiff_cmp : Form Cell :=
  { id := "alderete2001_stiff_cmp"
    lexeme := Lexemes.stiff
    cell := cmp
    form := "stíiv-ər"
    source := [
      ⟨"alderete-2001", "(42)"⟩
    ] }

def bald : Form Cell :=
  { id := "alderete2001_bald"
    lexeme := Lexemes.bald
    cell := {}
    form := "káál"
    source := [
      ⟨"alderete-2001", "(42)"⟩,
      ⟨"alderete-2001", "(48a)"⟩,
      ⟨"alderete-2001", "(50)"⟩,
      ⟨"alderete-2001", "(52)"⟩
    ] }

def bald_masc : Form Cell :=
  { id := "alderete2001_bald_masc"
    lexeme := Lexemes.bald
    cell := masc
    form := "káal-ə"
    source := [
      ⟨"alderete-2001", "(42)"⟩,
      ⟨"alderete-2001", "(48a)"⟩,
      ⟨"alderete-2001", "(50)"⟩,
      ⟨"alderete-2001", "(52)"⟩
    ] }

def bald_fem : Form Cell :=
  { id := "alderete2001_bald_fem"
    lexeme := Lexemes.bald
    cell := fem
    form := "káal"
    source := [
      ⟨"alderete-2001", "(42)"⟩
    ] }

def bald_cmp : Form Cell :=
  { id := "alderete2001_bald_cmp"
    lexeme := Lexemes.bald
    cell := cmp
    form := "káal-ər"
    source := [
      ⟨"alderete-2001", "(42)"⟩
    ] }

def paralysed : Form Cell :=
  { id := "alderete2001_paralysed"
    lexeme := Lexemes.paralysed
    cell := {}
    form := "láám"
    source := [
      ⟨"alderete-2001", "(42)"⟩
    ] }

def paralysed_masc : Form Cell :=
  { id := "alderete2001_paralysed_masc"
    lexeme := Lexemes.paralysed
    cell := masc
    form := "láam-ə"
    source := [
      ⟨"alderete-2001", "(42)"⟩
    ] }

def paralysed_fem : Form Cell :=
  { id := "alderete2001_paralysed_fem"
    lexeme := Lexemes.paralysed
    cell := fem
    form := "láam"
    source := [
      ⟨"alderete-2001", "(42)"⟩
    ] }

def paralysed_cmp : Form Cell :=
  { id := "alderete2001_paralysed_cmp"
    lexeme := Lexemes.paralysed
    cell := cmp
    form := "láam-ər"
    source := [
      ⟨"alderete-2001", "(42)"⟩
    ] }

def refined : Form Cell :=
  { id := "alderete2001_refined"
    lexeme := Lexemes.refined
    cell := {}
    form := "fíín"
    source := [
      ⟨"alderete-2001", "(42)"⟩
    ] }

def refined_masc : Form Cell :=
  { id := "alderete2001_refined_masc"
    lexeme := Lexemes.refined
    cell := masc
    form := "fíin-ə"
    source := [
      ⟨"alderete-2001", "(42)"⟩
    ] }

def refined_fem : Form Cell :=
  { id := "alderete2001_refined_fem"
    lexeme := Lexemes.refined
    cell := fem
    form := "fíin"
    source := [
      ⟨"alderete-2001", "(42)"⟩
    ] }

def refined_cmp : Form Cell :=
  { id := "alderete2001_refined_cmp"
    lexeme := Lexemes.refined
    cell := cmp
    form := "fíin-ər"
    source := [
      ⟨"alderete-2001", "(42)"⟩
    ] }

def tough : Form Cell :=
  { id := "alderete2001_tough"
    lexeme := Lexemes.tough
    cell := {}
    form := "stúur"
    source := [
      ⟨"alderete-2001", "(48b)"⟩,
      ⟨"alderete-2001", "(53)"⟩
    ] }

def tough_masc : Form Cell :=
  { id := "alderete2001_tough_masc"
    lexeme := Lexemes.tough
    cell := masc
    form := "stúur-ə"
    source := [
      ⟨"alderete-2001", "(48b)"⟩,
      ⟨"alderete-2001", "(53)"⟩
    ] }

/-- The source's analysis of a form, its parse rather than data. -/
structure Analysis where
  /-- The form analysed. -/
  form : Form Cell
  /-- The `Underlying` column, the input the paper gives the form. -/
  underlying : Option String := none
  /-- The `Relation` column, the output-output correspondence relation the form's affix
  subcategorizes for. -/
  relation : Option OORelation := none
  deriving DecidableEq, Repr

def arm_sg.analysis : Analysis :=
  { form := arm_sg }

def arm_pl.analysis : Analysis :=
  { form := arm_pl,
    relation := some OORelation.exchange }

def walking_stick_sg.analysis : Analysis :=
  { form := walking_stick_sg }

def walking_stick_pl.analysis : Analysis :=
  { form := walking_stick_pl,
    relation := some OORelation.exchange }

def bone_sg.analysis : Analysis :=
  { form := bone_sg }

def bone_pl.analysis : Analysis :=
  { form := bone_pl,
    relation := some OORelation.exchange }

def brother_sg.analysis : Analysis :=
  { form := brother_sg }

def brother_pl.analysis : Analysis :=
  { form := brother_pl,
    relation := some OORelation.exchange }

def yondara.analysis : Analysis :=
  { form := yondara,
    underlying := some "/yóm+tára/",
    relation := some OORelation.recessive }

def yondara_call.analysis : Analysis :=
  { form := yondara_call,
    underlying := some "/yob+tára/",
    relation := some OORelation.recessive }

def aburappoi.analysis : Analysis :=
  { form := aburappoi,
    underlying := some "/abura+ppó+i/",
    relation := some OORelation.dominant }

def kazeppoi.analysis : Analysis :=
  { form := kazeppoi,
    underlying := some "/kaze+ppó+i/",
    relation := some OORelation.dominant }

def kodomoppoi.analysis : Analysis :=
  { form := kodomoppoi,
    underlying := some "/kodomo+ppó+i/",
    relation := some OORelation.dominant }

def adappoi.analysis : Analysis :=
  { form := adappoi,
    underlying := some "/adá+ppó+i/",
    relation := some OORelation.dominant }

def netuppoi.analysis : Analysis :=
  { form := netuppoi,
    underlying := some "/netú+ppó+i/",
    relation := some OORelation.dominant }

def kizappoi.analysis : Analysis :=
  { form := kizappoi,
    underlying := some "/kíza+ppó+i/",
    relation := some OORelation.dominant }

def edokko.analysis : Analysis :=
  { form := edokko,
    underlying := some "/edo+kko/",
    relation := some OORelation.dominant }

def niigatakko.analysis : Analysis :=
  { form := niigatakko,
    underlying := some "/niigata+kko/",
    relation := some OORelation.dominant }

def oosakakko.analysis : Analysis :=
  { form := oosakakko,
    underlying := some "/oosaka+kko/",
    relation := some OORelation.dominant }

def koobekko.analysis : Analysis :=
  { form := koobekko,
    underlying := some "/kóobe+kko/",
    relation := some OORelation.dominant }

def nagoyakko.analysis : Analysis :=
  { form := nagoyakko,
    underlying := some "/nágoya+kko/",
    relation := some OORelation.dominant }

def nyuuyookukko.analysis : Analysis :=
  { form := nyuuyookukko,
    underlying := some "/nyuuyóoku+kko/",
    relation := some OORelation.dominant }

def hasi.analysis : Analysis :=
  { form := hasi,
    underlying := some "/hasi/" }

def wise.analysis : Analysis :=
  { form := wise }

def wise_masc.analysis : Analysis :=
  { form := wise_masc,
    relation := some OORelation.dominant }

def wise_fem.analysis : Analysis :=
  { form := wise_fem,
    relation := some OORelation.dominant }

def wise_cmp.analysis : Analysis :=
  { form := wise_cmp,
    relation := some OORelation.dominant }

def stiff.analysis : Analysis :=
  { form := stiff }

def stiff_masc.analysis : Analysis :=
  { form := stiff_masc,
    relation := some OORelation.dominant }

def stiff_fem.analysis : Analysis :=
  { form := stiff_fem,
    relation := some OORelation.dominant }

def stiff_cmp.analysis : Analysis :=
  { form := stiff_cmp,
    relation := some OORelation.dominant }

def bald.analysis : Analysis :=
  { form := bald }

def bald_masc.analysis : Analysis :=
  { form := bald_masc,
    relation := some OORelation.dominant }

def bald_fem.analysis : Analysis :=
  { form := bald_fem,
    relation := some OORelation.dominant }

def bald_cmp.analysis : Analysis :=
  { form := bald_cmp,
    relation := some OORelation.dominant }

def paralysed.analysis : Analysis :=
  { form := paralysed }

def paralysed_masc.analysis : Analysis :=
  { form := paralysed_masc,
    relation := some OORelation.dominant }

def paralysed_fem.analysis : Analysis :=
  { form := paralysed_fem,
    relation := some OORelation.dominant }

def paralysed_cmp.analysis : Analysis :=
  { form := paralysed_cmp,
    relation := some OORelation.dominant }

def refined.analysis : Analysis :=
  { form := refined }

def refined_masc.analysis : Analysis :=
  { form := refined_masc,
    relation := some OORelation.dominant }

def refined_fem.analysis : Analysis :=
  { form := refined_fem,
    relation := some OORelation.dominant }

def refined_cmp.analysis : Analysis :=
  { form := refined_cmp,
    relation := some OORelation.dominant }

def tough.analysis : Analysis :=
  { form := tough }

def tough_masc.analysis : Analysis :=
  { form := tough_masc,
    relation := some OORelation.dominant }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.arm, Lexemes.walking_stick, Lexemes.bone, Lexemes.brother,
  Lexemes.read, Lexemes.call, Lexemes.oily, Lexemes.sniffily, Lexemes.childish, Lexemes.coquettish,
  Lexemes.zealous, Lexemes.affected, Lexemes.native_of_tokyo, Lexemes.native_of_nigata,
  Lexemes.native_of_osaka, Lexemes.native_of_kobe, Lexemes.native_of_nagoya,
  Lexemes.native_of_new_york, Lexemes.edge, Lexemes.wise, Lexemes.stiff, Lexemes.bald,
  Lexemes.paralysed, Lexemes.refined, Lexemes.tough]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [arm_sg, arm_pl, walking_stick_sg, walking_stick_pl, bone_sg, bone_pl,
  brother_sg, brother_pl, yondara, yondara_call, aburappoi, kazeppoi, kodomoppoi, adappoi, netuppoi,
  kizappoi, edokko, niigatakko, oosakakko, koobekko, nagoyakko, nyuuyookukko, hasi, wise, wise_masc,
  wise_fem, wise_cmp, stiff, stiff_masc, stiff_fem, stiff_cmp, bald, bald_masc, bald_fem, bald_cmp,
  paralysed, paralysed_masc, paralysed_fem, paralysed_cmp, refined, refined_masc, refined_fem,
  refined_cmp, tough, tough_masc]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := [
  { id := "alderete2001_r_arm_pl", form := arm_sg, target := arm_pl, relation := "plural",
    source := [
      ⟨"alderete-2001", "(6a)"⟩
    ] },
  { id := "alderete2001_r_walking_stick_pl", form := walking_stick_sg, target := walking_stick_pl,
    relation := "plural", source := [
      ⟨"alderete-2001", "(6a)"⟩
    ] },
  { id := "alderete2001_r_bone_pl", form := bone_sg, target := bone_pl, relation := "plural",
    source := [
      ⟨"alderete-2001", "(6b)"⟩
    ] },
  { id := "alderete2001_r_brother_pl", form := brother_sg, target := brother_pl,
    relation := "plural", source := [
      ⟨"alderete-2001", "(6b)"⟩
    ] },
  { id := "alderete2001_r_wise_masc", form := wise, target := wise_masc, relation := "masculine",
    source := [
      ⟨"alderete-2001", "(42)"⟩
    ] },
  { id := "alderete2001_r_wise_fem", form := wise, target := wise_fem, relation := "feminine",
    source := [
      ⟨"alderete-2001", "(42)"⟩
    ] },
  { id := "alderete2001_r_wise_cmp", form := wise, target := wise_cmp, relation := "comparative",
    source := [
      ⟨"alderete-2001", "(42)"⟩
    ] },
  { id := "alderete2001_r_stiff_masc", form := stiff, target := stiff_masc, relation := "masculine",
    source := [
      ⟨"alderete-2001", "(42)"⟩
    ] },
  { id := "alderete2001_r_stiff_fem", form := stiff, target := stiff_fem, relation := "feminine",
    source := [
      ⟨"alderete-2001", "(42)"⟩
    ] },
  { id := "alderete2001_r_stiff_cmp", form := stiff, target := stiff_cmp, relation := "comparative",
    source := [
      ⟨"alderete-2001", "(42)"⟩
    ] },
  { id := "alderete2001_r_bald_masc", form := bald, target := bald_masc, relation := "masculine",
    source := [
      ⟨"alderete-2001", "(42)"⟩
    ] },
  { id := "alderete2001_r_bald_fem", form := bald, target := bald_fem, relation := "feminine",
    source := [
      ⟨"alderete-2001", "(42)"⟩
    ] },
  { id := "alderete2001_r_bald_cmp", form := bald, target := bald_cmp, relation := "comparative",
    source := [
      ⟨"alderete-2001", "(42)"⟩
    ] },
  { id := "alderete2001_r_paralysed_masc", form := paralysed, target := paralysed_masc,
    relation := "masculine", source := [
      ⟨"alderete-2001", "(42)"⟩
    ] },
  { id := "alderete2001_r_paralysed_fem", form := paralysed, target := paralysed_fem,
    relation := "feminine", source := [
      ⟨"alderete-2001", "(42)"⟩
    ] },
  { id := "alderete2001_r_paralysed_cmp", form := paralysed, target := paralysed_cmp,
    relation := "comparative", source := [
      ⟨"alderete-2001", "(42)"⟩
    ] },
  { id := "alderete2001_r_refined_masc", form := refined, target := refined_masc,
    relation := "masculine", source := [
      ⟨"alderete-2001", "(42)"⟩
    ] },
  { id := "alderete2001_r_refined_fem", form := refined, target := refined_fem,
    relation := "feminine", source := [
      ⟨"alderete-2001", "(42)"⟩
    ] },
  { id := "alderete2001_r_refined_cmp", form := refined, target := refined_cmp,
    relation := "comparative", source := [
      ⟨"alderete-2001", "(42)"⟩
    ] },
  { id := "alderete2001_r_tough_masc", form := tough, target := tough_masc, relation := "masculine",
    source := [
      ⟨"alderete-2001", "(48b)"⟩
    ] }]

/-- Every relation the sources assert, between the forms' analyses. -/
def analysisRelations : List (FormRelation Analysis) := [
  { id := "alderete2001_r_arm_pl", form := arm_sg.analysis, target := arm_pl.analysis,
    relation := "plural", source := [
      ⟨"alderete-2001", "(6a)"⟩
    ] },
  { id := "alderete2001_r_walking_stick_pl", form := walking_stick_sg.analysis,
    target := walking_stick_pl.analysis, relation := "plural", source := [
      ⟨"alderete-2001", "(6a)"⟩
    ] },
  { id := "alderete2001_r_bone_pl", form := bone_sg.analysis, target := bone_pl.analysis,
    relation := "plural", source := [
      ⟨"alderete-2001", "(6b)"⟩
    ] },
  { id := "alderete2001_r_brother_pl", form := brother_sg.analysis, target := brother_pl.analysis,
    relation := "plural", source := [
      ⟨"alderete-2001", "(6b)"⟩
    ] },
  { id := "alderete2001_r_wise_masc", form := wise.analysis, target := wise_masc.analysis,
    relation := "masculine", source := [
      ⟨"alderete-2001", "(42)"⟩
    ] },
  { id := "alderete2001_r_wise_fem", form := wise.analysis, target := wise_fem.analysis,
    relation := "feminine", source := [
      ⟨"alderete-2001", "(42)"⟩
    ] },
  { id := "alderete2001_r_wise_cmp", form := wise.analysis, target := wise_cmp.analysis,
    relation := "comparative", source := [
      ⟨"alderete-2001", "(42)"⟩
    ] },
  { id := "alderete2001_r_stiff_masc", form := stiff.analysis, target := stiff_masc.analysis,
    relation := "masculine", source := [
      ⟨"alderete-2001", "(42)"⟩
    ] },
  { id := "alderete2001_r_stiff_fem", form := stiff.analysis, target := stiff_fem.analysis,
    relation := "feminine", source := [
      ⟨"alderete-2001", "(42)"⟩
    ] },
  { id := "alderete2001_r_stiff_cmp", form := stiff.analysis, target := stiff_cmp.analysis,
    relation := "comparative", source := [
      ⟨"alderete-2001", "(42)"⟩
    ] },
  { id := "alderete2001_r_bald_masc", form := bald.analysis, target := bald_masc.analysis,
    relation := "masculine", source := [
      ⟨"alderete-2001", "(42)"⟩
    ] },
  { id := "alderete2001_r_bald_fem", form := bald.analysis, target := bald_fem.analysis,
    relation := "feminine", source := [
      ⟨"alderete-2001", "(42)"⟩
    ] },
  { id := "alderete2001_r_bald_cmp", form := bald.analysis, target := bald_cmp.analysis,
    relation := "comparative", source := [
      ⟨"alderete-2001", "(42)"⟩
    ] },
  { id := "alderete2001_r_paralysed_masc", form := paralysed.analysis,
    target := paralysed_masc.analysis, relation := "masculine", source := [
      ⟨"alderete-2001", "(42)"⟩
    ] },
  { id := "alderete2001_r_paralysed_fem", form := paralysed.analysis,
    target := paralysed_fem.analysis, relation := "feminine", source := [
      ⟨"alderete-2001", "(42)"⟩
    ] },
  { id := "alderete2001_r_paralysed_cmp", form := paralysed.analysis,
    target := paralysed_cmp.analysis, relation := "comparative", source := [
      ⟨"alderete-2001", "(42)"⟩
    ] },
  { id := "alderete2001_r_refined_masc", form := refined.analysis, target := refined_masc.analysis,
    relation := "masculine", source := [
      ⟨"alderete-2001", "(42)"⟩
    ] },
  { id := "alderete2001_r_refined_fem", form := refined.analysis, target := refined_fem.analysis,
    relation := "feminine", source := [
      ⟨"alderete-2001", "(42)"⟩
    ] },
  { id := "alderete2001_r_refined_cmp", form := refined.analysis, target := refined_cmp.analysis,
    relation := "comparative", source := [
      ⟨"alderete-2001", "(42)"⟩
    ] },
  { id := "alderete2001_r_tough_masc", form := tough.analysis, target := tough_masc.analysis,
    relation := "masculine", source := [
      ⟨"alderete-2001", "(48b)"⟩
    ] }]

/-- Every analysis of the data. -/
def analyses : List Analysis := [arm_pl.analysis, walking_stick_pl.analysis, bone_pl.analysis,
  brother_pl.analysis, yondara.analysis, yondara_call.analysis, aburappoi.analysis,
  kazeppoi.analysis, kodomoppoi.analysis, adappoi.analysis, netuppoi.analysis, kizappoi.analysis,
  edokko.analysis, niigatakko.analysis, oosakakko.analysis, koobekko.analysis, nagoyakko.analysis,
  nyuuyookukko.analysis, hasi.analysis, wise_masc.analysis, wise_fem.analysis, wise_cmp.analysis,
  stiff_masc.analysis, stiff_fem.analysis, stiff_cmp.analysis, bald_masc.analysis,
  bald_fem.analysis, bald_cmp.analysis, paralysed_masc.analysis, paralysed_fem.analysis,
  paralysed_cmp.analysis, refined_masc.analysis, refined_fem.analysis, refined_cmp.analysis,
  tough_masc.analysis]

end Alderete2001.Forms
