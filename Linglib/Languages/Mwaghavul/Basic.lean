module

public import Linglib.Phonology.Tone.Grammatical

/-!
# Mwaghavul

Mwaghavul (A3 West Chadic, Plateau State, Nigeria; Glottocode mwag1236) contrasts H, M, and
L level tones and an LH rise, and its tone-bearing unit is the syllable. Verbs are derived
from ideophones by tone alone. This file records the ideophones of Akinbo and Rabo Fwangwar's
dataset: each one's syllables with their lexical tones, and the tones of the singular and
pluractional verbs derived from it, as printed.

## Main definitions

* `Syl`: a syllable, written without tone.
* `Ideophone`: an ideophone with its syllables and the tones of its derived verbs.
* `ideophones`: the dataset.

## References

* [akinbo-fwangwar-2026]
* [fwangwar-2018]
-/

@[expose] public section

namespace Mwaghavul

open Tone (TRN TBU)

/-- Mwaghavul's tone-bearing unit is the syllable. -/
def tbuKind : Tone.TBUKind := .syllable

/-- A Mwaghavul syllable, its segments written without tone. -/
structure Syl where
  ipa : String
  deriving DecidableEq, Repr

/-- An ideophone, with the tones of the verbs derived from it. -/
structure Ideophone where
  /-- The citation form, both copies of an inherently reduplicated ideophone. -/
  form : String
  gloss : String
  /-- The syllables of one copy, each with its lexical tone. -/
  syllables : List (TBU Syl)
  /-- The tones of the singular verb, `none` when only the reduplicated form is verbalised. -/
  verb : Option (List TRN)
  /-- The tones of the pluractional verb, reduplicant then base. -/
  pluractional : List TRN
  /-- Inherently reduplicated: the reduplicant and base are synchronically frozen. -/
  frozen : Bool
  deriving DecidableEq, Repr

/-- The lexical tones of one copy of an ideophone. -/
def Ideophone.tones (i : Ideophone) : List TRN := i.syllables.map TBU.tone

/-! ### The dataset -/

/-- *zùt* ‘how solid substance ejects’ (7a). -/
def zut : Ideophone :=
  ⟨"zùt", "how solid substance ejects", [⟨⟨"zut"⟩, .L⟩], some [.M], [.M, .H], false⟩

/-- *ɗìːs* ‘sound of blood sucking’ (7a). -/
def diis : Ideophone :=
  ⟨"ɗìːs", "sound of blood sucking", [⟨⟨"ɗiːs"⟩, .L⟩], some [.M], [.M, .H], false⟩

/-- *kwàj* ‘sound of bubbling hot water’ (7a). -/
def kwaj : Ideophone :=
  ⟨"kwàj", "sound of bubbling hot water", [⟨⟨"kwaj"⟩, .L⟩], some [.M], [.M, .H], false⟩

/-- *vjàr* ‘pouring of urine’ (7a). -/
def vjar : Ideophone := ⟨"vjàr", "pouring of urine", [⟨⟨"vjar"⟩, .L⟩], some [.M], [.M, .H], false⟩

/-- *ʃwɛ̀r* ‘how water falls’ (7a). -/
def shwer : Ideophone := ⟨"ʃwɛ̀r", "how water falls", [⟨⟨"ʃwɛr"⟩, .L⟩], some [.M], [.M, .H], false⟩

/-- *ʃɔ̀ɣɔ̀p* ‘oily’ (7b). -/
def shoghop : Ideophone :=
  ⟨"ʃɔ̀ɣɔ̀p", "oily", [⟨⟨"ʃɔ"⟩, .L⟩, ⟨⟨"ɣɔp"⟩, .L⟩], some [.M, .M], [.M, .M, .H, .H], false⟩

/-- *vjàɣàp* ‘how liquid ejects from a fruit’ (7b). -/
def vjaghap : Ideophone :=
  ⟨"vjàɣàp", "how liquid ejects from a fruit", [⟨⟨"vja"⟩, .L⟩, ⟨⟨"ɣap"⟩, .L⟩],
    some [.M, .M], [.M, .M, .H, .H], false⟩

/-- *wùlàʃ* ‘wide open’ (7b). -/
def wulash : Ideophone :=
  ⟨"wùlàʃ", "wide open", [⟨⟨"wu"⟩, .L⟩, ⟨⟨"laʃ"⟩, .L⟩], some [.M, .M], [.M, .M, .H, .H], false⟩

/-- *lúɓúk* ‘smooth and soft’ (7c). -/
def lubuk : Ideophone :=
  ⟨"lúɓúk", "smooth and soft", [⟨⟨"lu"⟩, .H⟩, ⟨⟨"ɓuk"⟩, .H⟩],
    some [.M, .M], [.M, .M, .H, .H], false⟩

/-- *wúláʃ* ‘wide open of small thing’ (7c). -/
def wulashSmall : Ideophone :=
  ⟨"wúláʃ", "wide open of small thing", [⟨⟨"wu"⟩, .H⟩, ⟨⟨"laʃ"⟩, .H⟩],
    some [.M, .M], [.M, .M, .H, .H], false⟩

/-- *bɨ̀ʃɔ̀l* ‘shabbily dressed’ (8a). -/
def bishol : Ideophone :=
  ⟨"bɨ̀ʃɔ̀l", "shabbily dressed", [⟨⟨"bɨ"⟩, .L⟩, ⟨⟨"ʃɔl"⟩, .L⟩],
    some [.M, .H], [.M, .M, .H, .H], false⟩

/-- *kɨ̀tìʃ* ‘untidy’ (8a). -/
def kitish : Ideophone :=
  ⟨"kɨ̀tìʃ", "untidy", [⟨⟨"kɨ"⟩, .L⟩, ⟨⟨"tiʃ"⟩, .L⟩], some [.M, .H], [.M, .M, .H, .H], false⟩

/-- *kɔ̀ɗɔ̀ŋ* ‘walking effortfully’ (8a). -/
def kodong : Ideophone :=
  ⟨"kɔ̀ɗɔ̀ŋ", "walking effortfully", [⟨⟨"kɔ"⟩, .L⟩, ⟨⟨"ɗɔŋ"⟩, .L⟩],
    some [.M, .H], [.M, .M, .H, .H], false⟩

/-- *kɨ̀tʃɔ̀r* ‘old-sounding vehicle’ (8a). -/
def kitshor : Ideophone :=
  ⟨"kɨ̀tʃɔ̀r", "old-sounding vehicle", [⟨⟨"kɨ"⟩, .L⟩, ⟨⟨"tʃɔr"⟩, .L⟩],
    some [.M, .H], [.M, .M, .H, .H], false⟩

/-- *kɔ̀rjɔ̀ŋ* ‘crooked’ (8b). -/
def korjong : Ideophone :=
  ⟨"kɔ̀rjɔ̀ŋ", "crooked", [⟨⟨"kɔr"⟩, .L⟩, ⟨⟨"jɔŋ"⟩, .L⟩], some [.M, .H], [.M, .M, .H, .H], false⟩

/-- *mɔ̀ndɔ̀s* ‘big nose’ (8b). -/
def mondos : Ideophone :=
  ⟨"mɔ̀ndɔ̀s", "big nose", [⟨⟨"mɔn"⟩, .L⟩, ⟨⟨"dɔs"⟩, .L⟩], some [.M, .H], [.M, .M, .H, .H], false⟩

/-- *vwàplàs* ‘oversized’ (8b). -/
def vwaplas : Ideophone :=
  ⟨"vwàplàs", "oversized", [⟨⟨"vwap"⟩, .L⟩, ⟨⟨"las"⟩, .L⟩], some [.M, .H], [.M, .M, .H, .H], false⟩

/-- *jàlpàt* ‘hanging loose’ (8b). -/
def jalpat : Ideophone :=
  ⟨"jàlpàt", "hanging loose", [⟨⟨"jal"⟩, .L⟩, ⟨⟨"pat"⟩, .L⟩],
    some [.M, .H], [.M, .M, .H, .H], false⟩

/-- *háŋláɣáp* ‘light-weighted’ (8c). -/
def hanlaghap : Ideophone :=
  ⟨"háŋláɣáp", "light-weighted", [⟨⟨"haŋ"⟩, .H⟩, ⟨⟨"la"⟩, .H⟩, ⟨⟨"ɣap"⟩, .H⟩],
    some [.M, .M, .H], [.M, .M, .M, .H, .H, .H], false⟩

/-- *hámhɔ́ɣɔ́ʃ* ‘dryness of cracked feet’ (8c). -/
def hamhoghosh : Ideophone :=
  ⟨"hámhɔ́ɣɔ́ʃ", "dryness of cracked feet", [⟨⟨"ham"⟩, .H⟩, ⟨⟨"hɔ"⟩, .H⟩, ⟨⟨"ɣɔʃ"⟩, .H⟩],
    some [.M, .M, .H], [.M, .M, .M, .H, .H, .H], false⟩

/-- *dʒɛ́ɣɛ́rɛ́k* ‘thin/fragile’ (8c). -/
def jegherek : Ideophone :=
  ⟨"dʒɛ́ɣɛ́rɛ́k", "thin/fragile", [⟨⟨"dʒɛ"⟩, .H⟩, ⟨⟨"ɣɛ"⟩, .H⟩, ⟨⟨"rɛk"⟩, .H⟩],
    some [.M, .M, .H], [.M, .M, .M, .H, .H, .H], false⟩

/-- *gɔ̀kʃìrɔ̀k* ‘old or abnormal’ (8d). -/
def gokshirok : Ideophone :=
  ⟨"gɔ̀kʃìrɔ̀k", "old or abnormal", [⟨⟨"gɔk"⟩, .L⟩, ⟨⟨"ʃi"⟩, .L⟩, ⟨⟨"rɔk"⟩, .L⟩],
    some [.M, .M, .H], [.M, .M, .M, .H, .H, .H], false⟩

/-- *zɔ̀ngɨ̀lɔ̀ŋ* ‘long and thin’ (8d). -/
def zongilong : Ideophone :=
  ⟨"zɔ̀ngɨ̀lɔ̀ŋ", "long and thin", [⟨⟨"zɔn"⟩, .L⟩, ⟨⟨"gɨ"⟩, .L⟩, ⟨⟨"lɔŋ"⟩, .L⟩],
    some [.M, .M, .H], [.M, .M, .M, .H, .H, .H], false⟩

/-- *sàlmùtàt* ‘sluggish’ (8d). -/
def salmutat : Ideophone :=
  ⟨"sàlmùtàt", "sluggish", [⟨⟨"sal"⟩, .L⟩, ⟨⟨"mu"⟩, .L⟩, ⟨⟨"tat"⟩, .L⟩],
    some [.M, .M, .H], [.M, .M, .M, .H, .H, .H], false⟩

/-- *dɨ̀ɣɨ̀rɨ̀k* ‘being big and lazy’ (8d). -/
def dighirik : Ideophone :=
  ⟨"dɨ̀ɣɨ̀rɨ̀k", "being big and lazy", [⟨⟨"dɨ"⟩, .L⟩, ⟨⟨"ɣɨ"⟩, .L⟩, ⟨⟨"rɨk"⟩, .L⟩],
    some [.M, .M, .H], [.M, .M, .M, .H, .H, .H], false⟩

/-- *dʒùm* ‘heavy water plop’ (9a). -/
def jumHeavy : Ideophone := ⟨"dʒùm", "heavy water plop", [⟨⟨"dʒum"⟩, .L⟩], none, [.M, .H], false⟩

/-- *kùràʃ* ‘slow scratching sound’ (9a). -/
def kurashSlow : Ideophone :=
  ⟨"kùràʃ", "slow scratching sound", [⟨⟨"ku"⟩, .L⟩, ⟨⟨"raʃ"⟩, .L⟩], none, [.M, .M, .H, .H], false⟩

/-- *kwàːs* ‘slow foot-dragging sound’ (9a). -/
def kwaasSlow : Ideophone :=
  ⟨"kwàːs", "slow foot-dragging sound", [⟨⟨"kwaːs"⟩, .L⟩], none, [.M, .H], false⟩

/-- *tɨ̀ràt* ‘sound of sipping’ (9a). -/
def tirat : Ideophone :=
  ⟨"tɨ̀ràt", "sound of sipping", [⟨⟨"tɨ"⟩, .L⟩, ⟨⟨"rat"⟩, .L⟩], none, [.M, .M, .H, .H], false⟩

/-- *dʒúm* ‘light water plop’ (9b). -/
def jumLight : Ideophone := ⟨"dʒúm", "light water plop", [⟨⟨"dʒum"⟩, .H⟩], none, [.M, .H], false⟩

/-- *kúráʃ* ‘fast scratching sound’ (9b). -/
def kurashFast : Ideophone :=
  ⟨"kúráʃ", "fast scratching sound", [⟨⟨"ku"⟩, .H⟩, ⟨⟨"raʃ"⟩, .H⟩], none, [.M, .M, .H, .H], false⟩

/-- *kwáːs* ‘fast foot-dragging sound’ (9b). -/
def kwaasFast : Ideophone :=
  ⟨"kwáːs", "fast foot-dragging sound", [⟨⟨"kwaːs"⟩, .H⟩], none, [.M, .H], false⟩

/-- *wɛ́ŋ* ‘sound of buzzing’ (9b). -/
def weng : Ideophone := ⟨"wɛ́ŋ", "sound of buzzing", [⟨⟨"wɛŋ"⟩, .H⟩], none, [.M, .H], false⟩

/-- *gɨ̀r-gɨ̀r* ‘sound of a moving truck’ (10a). -/
def girgir : Ideophone :=
  ⟨"gɨ̀r-gɨ̀r", "sound of a moving truck", [⟨⟨"gɨr"⟩, .L⟩], none, [.M, .H], true⟩

/-- *wùr-wùr* ‘in a rush’ (10a). -/
def wurwur : Ideophone := ⟨"wùr-wùr", "in a rush", [⟨⟨"wur"⟩, .L⟩], none, [.M, .H], true⟩

/-- *tɛ̀ŋ-tɛ̀ŋ* ‘zigzag’ (10a). -/
def tengteng : Ideophone := ⟨"tɛ̀ŋ-tɛ̀ŋ", "zigzag", [⟨⟨"tɛŋ"⟩, .L⟩], none, [.M, .H], true⟩

/-- *zɛ̀t-zɛ̀t* ‘hurried walk’ (10a). -/
def zetzet : Ideophone := ⟨"zɛ̀t-zɛ̀t", "hurried walk", [⟨⟨"zɛt"⟩, .L⟩], none, [.M, .H], true⟩

/-- *wùrɛ̀t-wùrɛ̀t* ‘fast walk’ (10a). -/
def wuretwuret : Ideophone :=
  ⟨"wùrɛ̀t-wùrɛ̀t", "fast walk", [⟨⟨"wu"⟩, .L⟩, ⟨⟨"rɛt"⟩, .L⟩], none, [.M, .M, .H, .H], true⟩

/-- *ʃùrɛ̀t-ʃùrɛ̀t* ‘profusely crying’ (10a). -/
def shuretshuret : Ideophone :=
  ⟨"ʃùrɛ̀t-ʃùrɛ̀t", "profusely crying", [⟨⟨"ʃu"⟩, .L⟩, ⟨⟨"rɛt"⟩, .L⟩], none, [.M, .M, .H, .H], true⟩

/-- *kɨ́pɛ́t-kɨ́pɛ́t* ‘flip-flop sound’ (10b). -/
def kipetkipet : Ideophone :=
  ⟨"kɨ́pɛ́t-kɨ́pɛ́t", "flip-flop sound", [⟨⟨"kɨ"⟩, .H⟩, ⟨⟨"pɛt"⟩, .H⟩],
    none, [.M, .M, .H, .H], true⟩

/-- *wúlɛ́ŋ-wúlɛ́ŋ* ‘smart look’ (10b). -/
def wulengwuleng : Ideophone :=
  ⟨"wúlɛ́ŋ-wúlɛ́ŋ", "smart look", [⟨⟨"wu"⟩, .H⟩, ⟨⟨"lɛŋ"⟩, .H⟩], none, [.M, .M, .H, .H], true⟩

/-- *zɔ́n-zɔ́n* ‘describe aimless movement’ (10b). -/
def zonzon : Ideophone :=
  ⟨"zɔ́n-zɔ́n", "describe aimless movement", [⟨⟨"zɔn"⟩, .H⟩], none, [.M, .H], true⟩

/-- The dataset; *ram-ram* ‘describes something exciting’ (10c), printed without tone marks, is
omitted. -/
def ideophones : List Ideophone :=
  [zut, diis, kwaj, vjar, shwer, shoghop, vjaghap, wulash, lubuk, wulashSmall,
    bishol, kitish, kodong, kitshor, korjong, mondos, vwaplas, jalpat, hanlaghap, hamhoghosh,
    jegherek, gokshirok, zongilong, salmutat, dighirik,
    jumHeavy, kurashSlow, kwaasSlow, tirat, jumLight, kurashFast, kwaasFast, weng,
    girgir, wurwur, tengteng, zetzet, wuretwuret, shuretshuret, kipetkipet, wulengwuleng,
    zonzon]

end Mwaghavul
