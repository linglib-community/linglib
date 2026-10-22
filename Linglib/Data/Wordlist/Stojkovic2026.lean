module

public import Linglib.Data.Wordlist.Schema

/-!
# `Stojkovic2026`: word forms

Auto-generated from `Linglib/Data/Wordlist/Stojkovic2026.json` by `scripts/gen_wordlist.py`. Do not
edit by hand; edit the JSON and re-run the generator. Declarations live in `namespace
Stojkovic2026.Wordlist`.
-/

@[expose] public section

namespace Stojkovic2026.Wordlist

open CLDF.Wordlist

/-- The values of `Root` the source distinguishes. -/
inductive Root where
  /-- A plain root-final consonant, `plain` in the source. -/
  | plain
  /-- A palatal root-final consonant, `palatal` in the source. -/
  | palatal
  deriving DecidableEq, Repr

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

/-- The l-form.f.sg cell, `VerbForm=Part|Tense=Past|Gender=Fem|Number=Sing`. -/
def l_form_f_sg : Cell :=
  { verbForm := ↑UD.VerbForm.Part, tense := ↑UD.Tense.Past, gender := ↑UD.Gender.Fem,
    number := ↑UD.Number.Sing }

/-- The 2sg.prs cell, `Person=2|Number=Sing|Tense=Pres`. -/
def prs_2sg : Cell :=
  { person := ↑UD.Person.second, number := ↑UD.Number.Sing, tense := ↑UD.Tense.Pres }

def Lexemes.abolish_belarusian : Lexeme :=
  { id := "abolish_belarusian", languageId := "bela1254", variety := "Belarusian",
    parameterId := "abolish" }

def Lexemes.care_for_bos_cro_mon_ser : Lexeme :=
  { id := "care_for_bos_cro_mon_ser", languageId := "sout1528", variety := "Bos/Cro/Mon/Ser",
    parameterId := "care_for" }

def Lexemes.kiss_bulgarian : Lexeme :=
  { id := "kiss_bulgarian", languageId := "bulg1262", variety := "Bulgarian",
    parameterId := "kiss" }

def Lexemes.swear_at_god_bunyev_ac : Lexeme :=
  { id := "swear_at_god_bunyev_ac", languageId := "sout1528", variety := "Bunyev(ac)",
    parameterId := "swear_at_god" }

def Lexemes.talk_carpathian_rusyn : Lexeme :=
  { id := "talk_carpathian_rusyn", languageId := "rusy1239", variety := "Carpathian Rusyn",
    parameterId := "talk" }

def Lexemes.buy_czech : Lexeme :=
  { id := "buy_czech", languageId := "czec1258", variety := "Czech", parameterId := "buy" }

def Lexemes.get_engaged_kashubian : Lexeme :=
  { id := "get_engaged_kashubian", languageId := "kash1274", variety := "Kashubian",
    parameterId := "get_engaged" }

def Lexemes.draw_lemko_rusyn : Lexeme :=
  { id := "draw_lemko_rusyn", languageId := "rusy1239", variety := "Lemko Rusyn",
    parameterId := "draw" }

def Lexemes.paint_lower_sorbian : Lexeme :=
  { id := "paint_lower_sorbian", languageId := "lowe1385", variety := "Lower Sorbian",
    parameterId := "paint" }

def Lexemes.believe_macedonian : Lexeme :=
  { id := "believe_macedonian", languageId := "mace1250", variety := "Macedonian",
    parameterId := "believe" }

def Lexemes.serve_pannonian_rusyn : Lexeme :=
  { id := "serve_pannonian_rusyn", languageId := "pann1240", variety := "Pannonian Rusyn",
    parameterId := "serve" }

def Lexemes.aim_podlachian : Lexeme :=
  { id := "aim_podlachian", languageId := "east1426", variety := "Podlachian",
    parameterId := "aim" }

def Lexemes.work_polish : Lexeme :=
  { id := "work_polish", languageId := "poli1260", variety := "Polish", parameterId := "work" }

def Lexemes.complain_russian : Lexeme :=
  { id := "complain_russian", languageId := "russ1263", variety := "Russian",
    parameterId := "complain" }

def Lexemes.darn_silesian : Lexeme :=
  { id := "darn_silesian", languageId := "sile1253", variety := "Silesian", parameterId := "darn" }

def Lexemes.battle_slovak : Lexeme :=
  { id := "battle_slovak", languageId := "slov1269", variety := "Slovak", parameterId := "battle" }

def Lexemes.travel_slovenian : Lexeme :=
  { id := "travel_slovenian", languageId := "slov1268", variety := "Slovenian",
    parameterId := "travel" }

def Lexemes.squeeze_ukrainian : Lexeme :=
  { id := "squeeze_ukrainian", languageId := "ukra1253", variety := "Ukrainian",
    parameterId := "squeeze" }

def Lexemes.buy_upper_sorbian : Lexeme :=
  { id := "buy_upper_sorbian", languageId := "uppe1395", variety := "Upper Sorbian",
    parameterId := "buy" }

def Lexemes.battle_belarusian : Lexeme :=
  { id := "battle_belarusian", languageId := "bela1254", variety := "Belarusian",
    parameterId := "battle" }

def Lexemes.prune_bunyev_ac : Lexeme :=
  { id := "prune_bunyev_ac", languageId := "sout1528", variety := "Bunyev(ac)",
    parameterId := "prune" }

def Lexemes.whip_czech : Lexeme :=
  { id := "whip_czech", languageId := "czec1258", variety := "Czech", parameterId := "whip" }

def Lexemes.date_kashubian : Lexeme :=
  { id := "date_kashubian", languageId := "kash1274", variety := "Kashubian",
    parameterId := "date" }

def Lexemes.wander_lower_sorbian : Lexeme :=
  { id := "wander_lower_sorbian", languageId := "lowe1385", variety := "Lower Sorbian",
    parameterId := "wander" }

def Lexemes.reign_pannonian_rusyn : Lexeme :=
  { id := "reign_pannonian_rusyn", languageId := "pann1240", variety := "Pannonian Rusyn",
    parameterId := "reign" }

def Lexemes.grub_podlachian : Lexeme :=
  { id := "grub_podlachian", languageId := "east1426", variety := "Podlachian",
    parameterId := "grub" }

def Lexemes.accommodate_polish : Lexeme :=
  { id := "accommodate_polish", languageId := "poli1260", variety := "Polish",
    parameterId := "accommodate" }

def Lexemes.whip_silesian : Lexeme :=
  { id := "whip_silesian", languageId := "sile1253", variety := "Silesian", parameterId := "whip" }

def Lexemes.translate_upper_sorbian : Lexeme :=
  { id := "translate_upper_sorbian", languageId := "uppe1395", variety := "Upper Sorbian",
    parameterId := "translate" }

def Lexemes.be_teacher_bos_cro_mon_ser : Lexeme :=
  { id := "be_teacher_bos_cro_mon_ser", languageId := "sout1528", variety := "Bos/Cro/Mon/Ser",
    parameterId := "be_teacher" }

def Lexemes.compare_carpathian_rusyn : Lexeme :=
  { id := "compare_carpathian_rusyn", languageId := "rusy1239", variety := "Carpathian Rusyn",
    parameterId := "compare" }

def Lexemes.swindle_russian : Lexeme :=
  { id := "swindle_russian", languageId := "russ1263", variety := "Russian",
    parameterId := "swindle" }

def Lexemes.rain_slovenian : Lexeme :=
  { id := "rain_slovenian", languageId := "slov1268", variety := "Slovenian",
    parameterId := "rain" }

def Lexemes.jitter_bulgarian : Lexeme :=
  { id := "jitter_bulgarian", languageId := "bulg1262", variety := "Bulgarian",
    parameterId := "jitter" }

def Lexemes.adore_lemko_rusyn : Lexeme :=
  { id := "adore_lemko_rusyn", languageId := "rusy1239", variety := "Lemko Rusyn",
    parameterId := "adore" }

def Lexemes.spend_night_macedonian : Lexeme :=
  { id := "spend_night_macedonian", languageId := "mace1250", variety := "Macedonian",
    parameterId := "spend_night" }

def Lexemes.be_late_ukrainian : Lexeme :=
  { id := "be_late_ukrainian", languageId := "ukra1253", variety := "Ukrainian",
    parameterId := "be_late" }

def belarusian_plain_lform : Form Cell :=
  { id := "stojkovic2026_belarusian_plain_lform"
    lexeme := Lexemes.abolish_belarusian
    cell := l_form_f_sg
    form := "kasavala"
    morphs := ["kas", "av", "a", "l", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def belarusian_plain_prs : Form Cell :=
  { id := "stojkovic2026_belarusian_plain_prs"
    lexeme := Lexemes.abolish_belarusian
    cell := prs_2sg
    form := "kasujeʃ"
    morphs := ["kas", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def bos_cro_mon_ser_plain_lform : Form Cell :=
  { id := "stojkovic2026_bos_cro_mon_ser_plain_lform"
    lexeme := Lexemes.care_for_bos_cro_mon_ser
    cell := l_form_f_sg
    form := "ɲegovala"
    morphs := ["ɲeg", "ov", "a", "l", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def bos_cro_mon_ser_plain_prs : Form Cell :=
  { id := "stojkovic2026_bos_cro_mon_ser_plain_prs"
    lexeme := Lexemes.care_for_bos_cro_mon_ser
    cell := prs_2sg
    form := "ɲegujeʃ"
    morphs := ["ɲeg", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def bulgarian_plain_lform : Form Cell :=
  { id := "stojkovic2026_bulgarian_plain_lform"
    lexeme := Lexemes.kiss_bulgarian
    cell := l_form_f_sg
    form := "tseluvala"
    morphs := ["tsel", "uv", "a", "l", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def bulgarian_plain_prs : Form Cell :=
  { id := "stojkovic2026_bulgarian_plain_prs"
    lexeme := Lexemes.kiss_bulgarian
    cell := prs_2sg
    form := "tseluvaʃ"
    morphs := ["tsel", "uv", "a", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def bunyev_ac_plain_lform : Form Cell :=
  { id := "stojkovic2026_bunyev_ac_plain_lform"
    lexeme := Lexemes.swear_at_god_bunyev_ac
    cell := l_form_f_sg
    form := "bogovala"
    morphs := ["bog", "ov", "a", "l", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def bunyev_ac_plain_prs : Form Cell :=
  { id := "stojkovic2026_bunyev_ac_plain_prs"
    lexeme := Lexemes.swear_at_god_bunyev_ac
    cell := prs_2sg
    form := "bogujeʃ"
    morphs := ["bog", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def carpathian_rusyn_plain_lform : Form Cell :=
  { id := "stojkovic2026_carpathian_rusyn_plain_lform"
    lexeme := Lexemes.talk_carpathian_rusyn
    cell := l_form_f_sg
    form := "bisidovala"
    morphs := ["bisid", "ov", "a", "l", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def carpathian_rusyn_plain_prs : Form Cell :=
  { id := "stojkovic2026_carpathian_rusyn_plain_prs"
    lexeme := Lexemes.talk_carpathian_rusyn
    cell := prs_2sg
    form := "bisidujeʃ"
    morphs := ["bisid", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def czech_plain_lform : Form Cell :=
  { id := "stojkovic2026_czech_plain_lform"
    lexeme := Lexemes.buy_czech
    cell := l_form_f_sg
    form := "kupovala"
    morphs := ["kup", "ov", "a", "l", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def czech_plain_prs : Form Cell :=
  { id := "stojkovic2026_czech_plain_prs"
    lexeme := Lexemes.buy_czech
    cell := prs_2sg
    form := "kupujeʃ"
    morphs := ["kup", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def kashubian_plain_lform : Form Cell :=
  { id := "stojkovic2026_kashubian_plain_lform"
    lexeme := Lexemes.get_engaged_kashubian
    cell := l_form_f_sg
    form := "brutkovawa"
    morphs := ["brutk", "ov", "a", "w", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def kashubian_plain_prs : Form Cell :=
  { id := "stojkovic2026_kashubian_plain_prs"
    lexeme := Lexemes.get_engaged_kashubian
    cell := prs_2sg
    form := "brutkujeʃ"
    morphs := ["brutk", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def lemko_rusyn_plain_lform : Form Cell :=
  { id := "stojkovic2026_lemko_rusyn_plain_lform"
    lexeme := Lexemes.draw_lemko_rusyn
    cell := l_form_f_sg
    form := "rɨsuvala"
    morphs := ["rɨs", "uv", "a", "l", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def lemko_rusyn_plain_prs : Form Cell :=
  { id := "stojkovic2026_lemko_rusyn_plain_prs"
    lexeme := Lexemes.draw_lemko_rusyn
    cell := prs_2sg
    form := "rɨsujeʃ"
    morphs := ["rɨs", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def lower_sorbian_plain_lform : Form Cell :=
  { id := "stojkovic2026_lower_sorbian_plain_lform"
    lexeme := Lexemes.paint_lower_sorbian
    cell := l_form_f_sg
    form := "molovawa"
    morphs := ["mol", "ov", "a", "w", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def lower_sorbian_plain_prs : Form Cell :=
  { id := "stojkovic2026_lower_sorbian_plain_prs"
    lexeme := Lexemes.paint_lower_sorbian
    cell := prs_2sg
    form := "molujeʃ"
    morphs := ["mol", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def macedonian_plain_lform : Form Cell :=
  { id := "stojkovic2026_macedonian_plain_lform"
    lexeme := Lexemes.believe_macedonian
    cell := l_form_f_sg
    form := "veruvala"
    morphs := ["ver", "uv", "a", "l", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def macedonian_plain_prs : Form Cell :=
  { id := "stojkovic2026_macedonian_plain_prs"
    lexeme := Lexemes.believe_macedonian
    cell := prs_2sg
    form := "veruvaʃ"
    morphs := ["ver", "uv", "a", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def pannonian_rusyn_plain_lform : Form Cell :=
  { id := "stojkovic2026_pannonian_rusyn_plain_lform"
    lexeme := Lexemes.serve_pannonian_rusyn
    cell := l_form_f_sg
    form := "rabovala"
    morphs := ["rab", "ov", "a", "l", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def pannonian_rusyn_plain_prs : Form Cell :=
  { id := "stojkovic2026_pannonian_rusyn_plain_prs"
    lexeme := Lexemes.serve_pannonian_rusyn
    cell := prs_2sg
    form := "rabujeʃ"
    morphs := ["rab", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def podlachian_plain_lform : Form Cell :=
  { id := "stojkovic2026_podlachian_plain_lform"
    lexeme := Lexemes.aim_podlachian
    cell := l_form_f_sg
    form := "tsilovawa"
    morphs := ["tsil", "ov", "a", "w", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def podlachian_plain_prs : Form Cell :=
  { id := "stojkovic2026_podlachian_plain_prs"
    lexeme := Lexemes.aim_podlachian
    cell := prs_2sg
    form := "tsilujeʃ"
    morphs := ["tsil", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def polish_plain_lform : Form Cell :=
  { id := "stojkovic2026_polish_plain_lform"
    lexeme := Lexemes.work_polish
    cell := l_form_f_sg
    form := "pratsovawa"
    morphs := ["prats", "ov", "a", "w", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def polish_plain_prs : Form Cell :=
  { id := "stojkovic2026_polish_plain_prs"
    lexeme := Lexemes.work_polish
    cell := prs_2sg
    form := "pratsujeʃ"
    morphs := ["prats", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def russian_plain_lform : Form Cell :=
  { id := "stojkovic2026_russian_plain_lform"
    lexeme := Lexemes.complain_russian
    cell := l_form_f_sg
    form := "ʒalovalasʲ"
    morphs := ["ʒal", "ov", "a", "l", "a", "sʲ"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def russian_plain_prs : Form Cell :=
  { id := "stojkovic2026_russian_plain_prs"
    lexeme := Lexemes.complain_russian
    cell := prs_2sg
    form := "ʒalujeʃsʲ"
    morphs := ["ʒal", "u", "je", "ʃ", "sʲ"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def silesian_plain_lform : Form Cell :=
  { id := "stojkovic2026_silesian_plain_lform"
    lexeme := Lexemes.darn_silesian
    cell := l_form_f_sg
    form := "ɕtopovawa"
    morphs := ["ɕtop", "ov", "a", "w", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def silesian_plain_prs : Form Cell :=
  { id := "stojkovic2026_silesian_plain_prs"
    lexeme := Lexemes.darn_silesian
    cell := prs_2sg
    form := "ɕtopujeʃ"
    morphs := ["ɕtop", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def slovak_plain_lform : Form Cell :=
  { id := "stojkovic2026_slovak_plain_lform"
    lexeme := Lexemes.battle_slovak
    cell := l_form_f_sg
    form := "bojovala"
    morphs := ["boj", "ov", "a", "l", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def slovak_plain_prs : Form Cell :=
  { id := "stojkovic2026_slovak_plain_prs"
    lexeme := Lexemes.battle_slovak
    cell := prs_2sg
    form := "bojujeʃ"
    morphs := ["boj", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def slovenian_plain_lform : Form Cell :=
  { id := "stojkovic2026_slovenian_plain_lform"
    lexeme := Lexemes.travel_slovenian
    cell := l_form_f_sg
    form := "potovala"
    morphs := ["pot", "ov", "a", "l", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def slovenian_plain_prs : Form Cell :=
  { id := "stojkovic2026_slovenian_plain_prs"
    lexeme := Lexemes.travel_slovenian
    cell := prs_2sg
    form := "potujeʃ"
    morphs := ["pot", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def ukrainian_plain_lform : Form Cell :=
  { id := "stojkovic2026_ukrainian_plain_lform"
    lexeme := Lexemes.squeeze_ukrainian
    cell := l_form_f_sg
    form := "stisuvala"
    morphs := ["stis", "uv", "a", "l", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def ukrainian_plain_prs : Form Cell :=
  { id := "stojkovic2026_ukrainian_plain_prs"
    lexeme := Lexemes.squeeze_ukrainian
    cell := prs_2sg
    form := "stisujeʃ"
    morphs := ["stis", "u", "jeʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def upper_sorbian_plain_lform : Form Cell :=
  { id := "stojkovic2026_upper_sorbian_plain_lform"
    lexeme := Lexemes.buy_upper_sorbian
    cell := l_form_f_sg
    form := "kupovawa"
    morphs := ["kup", "ov", "a", "w", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def upper_sorbian_plain_prs : Form Cell :=
  { id := "stojkovic2026_upper_sorbian_plain_prs"
    lexeme := Lexemes.buy_upper_sorbian
    cell := prs_2sg
    form := "kupujeʃ"
    morphs := ["kup", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ] }

def belarusian_palatal_lform : Form Cell :=
  { id := "stojkovic2026_belarusian_palatal_lform"
    lexeme := Lexemes.battle_belarusian
    cell := l_form_f_sg
    form := "vajavala"
    morphs := ["vaj", "av", "a", "l", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def belarusian_palatal_prs : Form Cell :=
  { id := "stojkovic2026_belarusian_palatal_prs"
    lexeme := Lexemes.battle_belarusian
    cell := prs_2sg
    form := "vajujeʃ"
    morphs := ["vaj", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def bunyev_ac_palatal_lform : Form Cell :=
  { id := "stojkovic2026_bunyev_ac_palatal_lform"
    lexeme := Lexemes.prune_bunyev_ac
    cell := l_form_f_sg
    form := "katʃovala"
    morphs := ["katʃ", "ov", "a", "l", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def bunyev_ac_palatal_prs : Form Cell :=
  { id := "stojkovic2026_bunyev_ac_palatal_prs"
    lexeme := Lexemes.prune_bunyev_ac
    cell := prs_2sg
    form := "katʃujeʃ"
    morphs := ["katʃ", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def czech_palatal_lform : Form Cell :=
  { id := "stojkovic2026_czech_palatal_lform"
    lexeme := Lexemes.whip_czech
    cell := l_form_f_sg
    form := "bitʃovala"
    morphs := ["bitʃ", "ov", "a", "l", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def czech_palatal_prs : Form Cell :=
  { id := "stojkovic2026_czech_palatal_prs"
    lexeme := Lexemes.whip_czech
    cell := prs_2sg
    form := "bitʃujeʃ"
    morphs := ["bitʃ", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def kashubian_palatal_lform : Form Cell :=
  { id := "stojkovic2026_kashubian_palatal_lform"
    lexeme := Lexemes.date_kashubian
    cell := l_form_f_sg
    form := "vrəjovawa"
    morphs := ["vrəj", "ov", "a", "w", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def kashubian_palatal_prs : Form Cell :=
  { id := "stojkovic2026_kashubian_palatal_prs"
    lexeme := Lexemes.date_kashubian
    cell := prs_2sg
    form := "vrəjujeʃ"
    morphs := ["vrəj", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def lower_sorbian_palatal_lform : Form Cell :=
  { id := "stojkovic2026_lower_sorbian_palatal_lform"
    lexeme := Lexemes.wander_lower_sorbian
    cell := l_form_f_sg
    form := "puɕovawa"
    morphs := ["puɕ", "ov", "a", "w", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def lower_sorbian_palatal_prs : Form Cell :=
  { id := "stojkovic2026_lower_sorbian_palatal_prs"
    lexeme := Lexemes.wander_lower_sorbian
    cell := prs_2sg
    form := "puɕujeʃ"
    morphs := ["puɕ", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def pannonian_rusyn_palatal_lform : Form Cell :=
  { id := "stojkovic2026_pannonian_rusyn_palatal_lform"
    lexeme := Lexemes.reign_pannonian_rusyn
    cell := l_form_f_sg
    form := "kraʎovala"
    morphs := ["kraʎ", "ov", "a", "l", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def pannonian_rusyn_palatal_prs : Form Cell :=
  { id := "stojkovic2026_pannonian_rusyn_palatal_prs"
    lexeme := Lexemes.reign_pannonian_rusyn
    cell := prs_2sg
    form := "kraʎujeʃ"
    morphs := ["kraʎ", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def podlachian_palatal_lform : Form Cell :=
  { id := "stojkovic2026_podlachian_palatal_lform"
    lexeme := Lexemes.grub_podlachian
    cell := l_form_f_sg
    form := "kartʃovawa"
    morphs := ["kartʃ", "ov", "a", "w", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def podlachian_palatal_prs : Form Cell :=
  { id := "stojkovic2026_podlachian_palatal_prs"
    lexeme := Lexemes.grub_podlachian
    cell := prs_2sg
    form := "kartʃujeʃ"
    morphs := ["kartʃ", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def polish_palatal_lform : Form Cell :=
  { id := "stojkovic2026_polish_palatal_lform"
    lexeme := Lexemes.accommodate_polish
    cell := l_form_f_sg
    form := "hotel'ovawa"
    morphs := ["hotel'", "ov", "a", "w", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def polish_palatal_prs : Form Cell :=
  { id := "stojkovic2026_polish_palatal_prs"
    lexeme := Lexemes.accommodate_polish
    cell := prs_2sg
    form := "hotel'ujeʃ"
    morphs := ["hotel'", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def slovak_palatal_lform : Form Cell :=
  { id := "stojkovic2026_slovak_palatal_lform"
    lexeme := Lexemes.battle_slovak
    cell := l_form_f_sg
    form := "bojovala"
    morphs := ["boj", "ov", "a", "l", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def slovak_palatal_prs : Form Cell :=
  { id := "stojkovic2026_slovak_palatal_prs"
    lexeme := Lexemes.battle_slovak
    cell := prs_2sg
    form := "bojujeʃ"
    morphs := ["boj", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def silesian_palatal_lform : Form Cell :=
  { id := "stojkovic2026_silesian_palatal_lform"
    lexeme := Lexemes.whip_silesian
    cell := l_form_f_sg
    form := "pajtɕovawa"
    morphs := ["pajtɕ", "ov", "a", "w", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def silesian_palatal_prs : Form Cell :=
  { id := "stojkovic2026_silesian_palatal_prs"
    lexeme := Lexemes.whip_silesian
    cell := prs_2sg
    form := "pajtɕujeʃ"
    morphs := ["pajtɕ", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def upper_sorbian_palatal_lform : Form Cell :=
  { id := "stojkovic2026_upper_sorbian_palatal_lform"
    lexeme := Lexemes.translate_upper_sorbian
    cell := l_form_f_sg
    form := "preloʒovawa"
    morphs := ["preloʒ", "ov", "a", "w", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def upper_sorbian_palatal_prs : Form Cell :=
  { id := "stojkovic2026_upper_sorbian_palatal_prs"
    lexeme := Lexemes.translate_upper_sorbian
    cell := prs_2sg
    form := "preloʒujeʃ"
    morphs := ["preloʒ", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def bos_cro_mon_ser_palatal_lform : Form Cell :=
  { id := "stojkovic2026_bos_cro_mon_ser_palatal_lform"
    lexeme := Lexemes.be_teacher_bos_cro_mon_ser
    cell := l_form_f_sg
    form := "utʃiteʎevala"
    morphs := ["utʃiteʎ", "ev", "a", "l", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def bos_cro_mon_ser_palatal_prs : Form Cell :=
  { id := "stojkovic2026_bos_cro_mon_ser_palatal_prs"
    lexeme := Lexemes.be_teacher_bos_cro_mon_ser
    cell := prs_2sg
    form := "utʃiteʎujeʃ"
    morphs := ["utʃiteʎ", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def carpathian_rusyn_palatal_lform : Form Cell :=
  { id := "stojkovic2026_carpathian_rusyn_palatal_lform"
    lexeme := Lexemes.compare_carpathian_rusyn
    cell := l_form_f_sg
    form := "stupɲevala"
    morphs := ["stupɲ", "ev", "a", "l", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def carpathian_rusyn_palatal_prs : Form Cell :=
  { id := "stojkovic2026_carpathian_rusyn_palatal_prs"
    lexeme := Lexemes.compare_carpathian_rusyn
    cell := prs_2sg
    form := "stupɲujeʃ"
    morphs := ["stupɲ", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def russian_palatal_lform : Form Cell :=
  { id := "stojkovic2026_russian_palatal_lform"
    lexeme := Lexemes.swindle_russian
    cell := l_form_f_sg
    form := "muxlʲevala"
    morphs := ["muxlʲ", "ev", "a", "l", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def russian_palatal_prs : Form Cell :=
  { id := "stojkovic2026_russian_palatal_prs"
    lexeme := Lexemes.swindle_russian
    cell := prs_2sg
    form := "muxlʲujeʃ"
    morphs := ["muxlʲ", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def slovenian_palatal_lform : Form Cell :=
  { id := "stojkovic2026_slovenian_palatal_lform"
    lexeme := Lexemes.rain_slovenian
    cell := l_form_f_sg
    form := "deʒevala"
    morphs := ["deʒ", "ev", "a", "l", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def slovenian_palatal_prs : Form Cell :=
  { id := "stojkovic2026_slovenian_palatal_prs"
    lexeme := Lexemes.rain_slovenian
    cell := prs_2sg
    form := "deʒujeʃ"
    morphs := ["deʒ", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def bulgarian_palatal_lform : Form Cell :=
  { id := "stojkovic2026_bulgarian_palatal_lform"
    lexeme := Lexemes.jitter_bulgarian
    cell := l_form_f_sg
    form := "najeʒuvala"
    morphs := ["najeʒ", "uv", "a", "l", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def bulgarian_palatal_prs : Form Cell :=
  { id := "stojkovic2026_bulgarian_palatal_prs"
    lexeme := Lexemes.jitter_bulgarian
    cell := prs_2sg
    form := "najeʒuvaʃ"
    morphs := ["najeʒ", "uv", "a", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def lemko_rusyn_palatal_lform : Form Cell :=
  { id := "stojkovic2026_lemko_rusyn_palatal_lform"
    lexeme := Lexemes.adore_lemko_rusyn
    cell := l_form_f_sg
    form := "oboʒuvala"
    morphs := ["oboʒ", "uv", "a", "l", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def lemko_rusyn_palatal_prs : Form Cell :=
  { id := "stojkovic2026_lemko_rusyn_palatal_prs"
    lexeme := Lexemes.adore_lemko_rusyn
    cell := prs_2sg
    form := "oboʒujeʃ"
    morphs := ["oboʒ", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def macedonian_palatal_lform : Form Cell :=
  { id := "stojkovic2026_macedonian_palatal_lform"
    lexeme := Lexemes.spend_night_macedonian
    cell := l_form_f_sg
    form := "nocuvala"
    morphs := ["noc", "uv", "a", "l", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def macedonian_palatal_prs : Form Cell :=
  { id := "stojkovic2026_macedonian_palatal_prs"
    lexeme := Lexemes.spend_night_macedonian
    cell := prs_2sg
    form := "nocuvaʃ"
    morphs := ["noc", "uv", "a", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def ukrainian_palatal_lform : Form Cell :=
  { id := "stojkovic2026_ukrainian_palatal_lform"
    lexeme := Lexemes.be_late_ukrainian
    cell := l_form_f_sg
    form := "zapizɲuvala"
    morphs := ["zapizɲ", "uv", "a", "l", "a"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

def ukrainian_palatal_prs : Form Cell :=
  { id := "stojkovic2026_ukrainian_palatal_prs"
    lexeme := Lexemes.be_late_ukrainian
    cell := prs_2sg
    form := "zapizɲujeʃ"
    morphs := ["zapizɲ", "u", "je", "ʃ"]
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ] }

/-- The source's analysis of a form, its parse rather than data. -/
structure Analysis where
  /-- The form analysed. -/
  form : Form Cell
  /-- The `Root` column, the root class the paper assigns. -/
  root : Root
  /-- The `Verbalizer` column. -/
  verbalizer : Option String := none
  deriving DecidableEq, Repr

def belarusian_plain_lform.analysis : Analysis :=
  { form := belarusian_plain_lform,
    root := Root.plain,
    verbalizer := some "orthographic" }

def belarusian_plain_prs.analysis : Analysis :=
  { form := belarusian_plain_prs,
    root := Root.plain }

def bos_cro_mon_ser_plain_lform.analysis : Analysis :=
  { form := bos_cro_mon_ser_plain_lform,
    root := Root.plain }

def bos_cro_mon_ser_plain_prs.analysis : Analysis :=
  { form := bos_cro_mon_ser_plain_prs,
    root := Root.plain }

def bulgarian_plain_lform.analysis : Analysis :=
  { form := bulgarian_plain_lform,
    root := Root.plain }

def bulgarian_plain_prs.analysis : Analysis :=
  { form := bulgarian_plain_prs,
    root := Root.plain }

def bunyev_ac_plain_lform.analysis : Analysis :=
  { form := bunyev_ac_plain_lform,
    root := Root.plain }

def bunyev_ac_plain_prs.analysis : Analysis :=
  { form := bunyev_ac_plain_prs,
    root := Root.plain }

def carpathian_rusyn_plain_lform.analysis : Analysis :=
  { form := carpathian_rusyn_plain_lform,
    root := Root.plain }

def carpathian_rusyn_plain_prs.analysis : Analysis :=
  { form := carpathian_rusyn_plain_prs,
    root := Root.plain }

def czech_plain_lform.analysis : Analysis :=
  { form := czech_plain_lform,
    root := Root.plain }

def czech_plain_prs.analysis : Analysis :=
  { form := czech_plain_prs,
    root := Root.plain }

def kashubian_plain_lform.analysis : Analysis :=
  { form := kashubian_plain_lform,
    root := Root.plain }

def kashubian_plain_prs.analysis : Analysis :=
  { form := kashubian_plain_prs,
    root := Root.plain }

def lemko_rusyn_plain_lform.analysis : Analysis :=
  { form := lemko_rusyn_plain_lform,
    root := Root.plain }

def lemko_rusyn_plain_prs.analysis : Analysis :=
  { form := lemko_rusyn_plain_prs,
    root := Root.plain }

def lower_sorbian_plain_lform.analysis : Analysis :=
  { form := lower_sorbian_plain_lform,
    root := Root.plain }

def lower_sorbian_plain_prs.analysis : Analysis :=
  { form := lower_sorbian_plain_prs,
    root := Root.plain }

def macedonian_plain_lform.analysis : Analysis :=
  { form := macedonian_plain_lform,
    root := Root.plain }

def macedonian_plain_prs.analysis : Analysis :=
  { form := macedonian_plain_prs,
    root := Root.plain }

def pannonian_rusyn_plain_lform.analysis : Analysis :=
  { form := pannonian_rusyn_plain_lform,
    root := Root.plain }

def pannonian_rusyn_plain_prs.analysis : Analysis :=
  { form := pannonian_rusyn_plain_prs,
    root := Root.plain }

def podlachian_plain_lform.analysis : Analysis :=
  { form := podlachian_plain_lform,
    root := Root.plain }

def podlachian_plain_prs.analysis : Analysis :=
  { form := podlachian_plain_prs,
    root := Root.plain }

def polish_plain_lform.analysis : Analysis :=
  { form := polish_plain_lform,
    root := Root.plain }

def polish_plain_prs.analysis : Analysis :=
  { form := polish_plain_prs,
    root := Root.plain }

def russian_plain_lform.analysis : Analysis :=
  { form := russian_plain_lform,
    root := Root.plain,
    verbalizer := some "orthographic" }

def russian_plain_prs.analysis : Analysis :=
  { form := russian_plain_prs,
    root := Root.plain }

def silesian_plain_lform.analysis : Analysis :=
  { form := silesian_plain_lform,
    root := Root.plain }

def silesian_plain_prs.analysis : Analysis :=
  { form := silesian_plain_prs,
    root := Root.plain }

def slovak_plain_lform.analysis : Analysis :=
  { form := slovak_plain_lform,
    root := Root.plain }

def slovak_plain_prs.analysis : Analysis :=
  { form := slovak_plain_prs,
    root := Root.plain }

def slovenian_plain_lform.analysis : Analysis :=
  { form := slovenian_plain_lform,
    root := Root.plain }

def slovenian_plain_prs.analysis : Analysis :=
  { form := slovenian_plain_prs,
    root := Root.plain }

def ukrainian_plain_lform.analysis : Analysis :=
  { form := ukrainian_plain_lform,
    root := Root.plain }

def ukrainian_plain_prs.analysis : Analysis :=
  { form := ukrainian_plain_prs,
    root := Root.plain }

def upper_sorbian_plain_lform.analysis : Analysis :=
  { form := upper_sorbian_plain_lform,
    root := Root.plain }

def upper_sorbian_plain_prs.analysis : Analysis :=
  { form := upper_sorbian_plain_prs,
    root := Root.plain }

def belarusian_palatal_lform.analysis : Analysis :=
  { form := belarusian_palatal_lform,
    root := Root.palatal,
    verbalizer := some "orthographic" }

def belarusian_palatal_prs.analysis : Analysis :=
  { form := belarusian_palatal_prs,
    root := Root.palatal }

def bunyev_ac_palatal_lform.analysis : Analysis :=
  { form := bunyev_ac_palatal_lform,
    root := Root.palatal }

def bunyev_ac_palatal_prs.analysis : Analysis :=
  { form := bunyev_ac_palatal_prs,
    root := Root.palatal }

def czech_palatal_lform.analysis : Analysis :=
  { form := czech_palatal_lform,
    root := Root.palatal }

def czech_palatal_prs.analysis : Analysis :=
  { form := czech_palatal_prs,
    root := Root.palatal }

def kashubian_palatal_lform.analysis : Analysis :=
  { form := kashubian_palatal_lform,
    root := Root.palatal }

def kashubian_palatal_prs.analysis : Analysis :=
  { form := kashubian_palatal_prs,
    root := Root.palatal }

def lower_sorbian_palatal_lform.analysis : Analysis :=
  { form := lower_sorbian_palatal_lform,
    root := Root.palatal }

def lower_sorbian_palatal_prs.analysis : Analysis :=
  { form := lower_sorbian_palatal_prs,
    root := Root.palatal }

def pannonian_rusyn_palatal_lform.analysis : Analysis :=
  { form := pannonian_rusyn_palatal_lform,
    root := Root.palatal }

def pannonian_rusyn_palatal_prs.analysis : Analysis :=
  { form := pannonian_rusyn_palatal_prs,
    root := Root.palatal }

def podlachian_palatal_lform.analysis : Analysis :=
  { form := podlachian_palatal_lform,
    root := Root.palatal }

def podlachian_palatal_prs.analysis : Analysis :=
  { form := podlachian_palatal_prs,
    root := Root.palatal }

def polish_palatal_lform.analysis : Analysis :=
  { form := polish_palatal_lform,
    root := Root.palatal }

def polish_palatal_prs.analysis : Analysis :=
  { form := polish_palatal_prs,
    root := Root.palatal }

def slovak_palatal_lform.analysis : Analysis :=
  { form := slovak_palatal_lform,
    root := Root.palatal }

def slovak_palatal_prs.analysis : Analysis :=
  { form := slovak_palatal_prs,
    root := Root.palatal }

def silesian_palatal_lform.analysis : Analysis :=
  { form := silesian_palatal_lform,
    root := Root.palatal }

def silesian_palatal_prs.analysis : Analysis :=
  { form := silesian_palatal_prs,
    root := Root.palatal }

def upper_sorbian_palatal_lform.analysis : Analysis :=
  { form := upper_sorbian_palatal_lform,
    root := Root.palatal }

def upper_sorbian_palatal_prs.analysis : Analysis :=
  { form := upper_sorbian_palatal_prs,
    root := Root.palatal }

def bos_cro_mon_ser_palatal_lform.analysis : Analysis :=
  { form := bos_cro_mon_ser_palatal_lform,
    root := Root.palatal }

def bos_cro_mon_ser_palatal_prs.analysis : Analysis :=
  { form := bos_cro_mon_ser_palatal_prs,
    root := Root.palatal }

def carpathian_rusyn_palatal_lform.analysis : Analysis :=
  { form := carpathian_rusyn_palatal_lform,
    root := Root.palatal }

def carpathian_rusyn_palatal_prs.analysis : Analysis :=
  { form := carpathian_rusyn_palatal_prs,
    root := Root.palatal }

def russian_palatal_lform.analysis : Analysis :=
  { form := russian_palatal_lform,
    root := Root.palatal,
    verbalizer := some "orthographic" }

def russian_palatal_prs.analysis : Analysis :=
  { form := russian_palatal_prs,
    root := Root.palatal }

def slovenian_palatal_lform.analysis : Analysis :=
  { form := slovenian_palatal_lform,
    root := Root.palatal }

def slovenian_palatal_prs.analysis : Analysis :=
  { form := slovenian_palatal_prs,
    root := Root.palatal }

def bulgarian_palatal_lform.analysis : Analysis :=
  { form := bulgarian_palatal_lform,
    root := Root.palatal }

def bulgarian_palatal_prs.analysis : Analysis :=
  { form := bulgarian_palatal_prs,
    root := Root.palatal }

def lemko_rusyn_palatal_lform.analysis : Analysis :=
  { form := lemko_rusyn_palatal_lform,
    root := Root.palatal }

def lemko_rusyn_palatal_prs.analysis : Analysis :=
  { form := lemko_rusyn_palatal_prs,
    root := Root.palatal }

def macedonian_palatal_lform.analysis : Analysis :=
  { form := macedonian_palatal_lform,
    root := Root.palatal }

def macedonian_palatal_prs.analysis : Analysis :=
  { form := macedonian_palatal_prs,
    root := Root.palatal }

def ukrainian_palatal_lform.analysis : Analysis :=
  { form := ukrainian_palatal_lform,
    root := Root.palatal }

def ukrainian_palatal_prs.analysis : Analysis :=
  { form := ukrainian_palatal_prs,
    root := Root.palatal }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.abolish_belarusian, Lexemes.care_for_bos_cro_mon_ser,
  Lexemes.kiss_bulgarian, Lexemes.swear_at_god_bunyev_ac, Lexemes.talk_carpathian_rusyn,
  Lexemes.buy_czech, Lexemes.get_engaged_kashubian, Lexemes.draw_lemko_rusyn,
  Lexemes.paint_lower_sorbian, Lexemes.believe_macedonian, Lexemes.serve_pannonian_rusyn,
  Lexemes.aim_podlachian, Lexemes.work_polish, Lexemes.complain_russian, Lexemes.darn_silesian,
  Lexemes.battle_slovak, Lexemes.travel_slovenian, Lexemes.squeeze_ukrainian,
  Lexemes.buy_upper_sorbian, Lexemes.battle_belarusian, Lexemes.prune_bunyev_ac, Lexemes.whip_czech,
  Lexemes.date_kashubian, Lexemes.wander_lower_sorbian, Lexemes.reign_pannonian_rusyn,
  Lexemes.grub_podlachian, Lexemes.accommodate_polish, Lexemes.whip_silesian,
  Lexemes.translate_upper_sorbian, Lexemes.be_teacher_bos_cro_mon_ser,
  Lexemes.compare_carpathian_rusyn, Lexemes.swindle_russian, Lexemes.rain_slovenian,
  Lexemes.jitter_bulgarian, Lexemes.adore_lemko_rusyn, Lexemes.spend_night_macedonian,
  Lexemes.be_late_ukrainian]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [belarusian_plain_lform, belarusian_plain_prs,
  bos_cro_mon_ser_plain_lform, bos_cro_mon_ser_plain_prs, bulgarian_plain_lform,
  bulgarian_plain_prs, bunyev_ac_plain_lform, bunyev_ac_plain_prs, carpathian_rusyn_plain_lform,
  carpathian_rusyn_plain_prs, czech_plain_lform, czech_plain_prs, kashubian_plain_lform,
  kashubian_plain_prs, lemko_rusyn_plain_lform, lemko_rusyn_plain_prs, lower_sorbian_plain_lform,
  lower_sorbian_plain_prs, macedonian_plain_lform, macedonian_plain_prs,
  pannonian_rusyn_plain_lform, pannonian_rusyn_plain_prs, podlachian_plain_lform,
  podlachian_plain_prs, polish_plain_lform, polish_plain_prs, russian_plain_lform,
  russian_plain_prs, silesian_plain_lform, silesian_plain_prs, slovak_plain_lform, slovak_plain_prs,
  slovenian_plain_lform, slovenian_plain_prs, ukrainian_plain_lform, ukrainian_plain_prs,
  upper_sorbian_plain_lform, upper_sorbian_plain_prs, belarusian_palatal_lform,
  belarusian_palatal_prs, bunyev_ac_palatal_lform, bunyev_ac_palatal_prs, czech_palatal_lform,
  czech_palatal_prs, kashubian_palatal_lform, kashubian_palatal_prs, lower_sorbian_palatal_lform,
  lower_sorbian_palatal_prs, pannonian_rusyn_palatal_lform, pannonian_rusyn_palatal_prs,
  podlachian_palatal_lform, podlachian_palatal_prs, polish_palatal_lform, polish_palatal_prs,
  slovak_palatal_lform, slovak_palatal_prs, silesian_palatal_lform, silesian_palatal_prs,
  upper_sorbian_palatal_lform, upper_sorbian_palatal_prs, bos_cro_mon_ser_palatal_lform,
  bos_cro_mon_ser_palatal_prs, carpathian_rusyn_palatal_lform, carpathian_rusyn_palatal_prs,
  russian_palatal_lform, russian_palatal_prs, slovenian_palatal_lform, slovenian_palatal_prs,
  bulgarian_palatal_lform, bulgarian_palatal_prs, lemko_rusyn_palatal_lform,
  lemko_rusyn_palatal_prs, macedonian_palatal_lform, macedonian_palatal_prs,
  ukrainian_palatal_lform, ukrainian_palatal_prs]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := []

/-- Every analysis of the data. -/
def analyses : List Analysis := [belarusian_plain_lform.analysis, belarusian_plain_prs.analysis,
  bos_cro_mon_ser_plain_lform.analysis, bos_cro_mon_ser_plain_prs.analysis,
  bulgarian_plain_lform.analysis, bulgarian_plain_prs.analysis, bunyev_ac_plain_lform.analysis,
  bunyev_ac_plain_prs.analysis, carpathian_rusyn_plain_lform.analysis,
  carpathian_rusyn_plain_prs.analysis, czech_plain_lform.analysis, czech_plain_prs.analysis,
  kashubian_plain_lform.analysis, kashubian_plain_prs.analysis, lemko_rusyn_plain_lform.analysis,
  lemko_rusyn_plain_prs.analysis, lower_sorbian_plain_lform.analysis,
  lower_sorbian_plain_prs.analysis, macedonian_plain_lform.analysis, macedonian_plain_prs.analysis,
  pannonian_rusyn_plain_lform.analysis, pannonian_rusyn_plain_prs.analysis,
  podlachian_plain_lform.analysis, podlachian_plain_prs.analysis, polish_plain_lform.analysis,
  polish_plain_prs.analysis, russian_plain_lform.analysis, russian_plain_prs.analysis,
  silesian_plain_lform.analysis, silesian_plain_prs.analysis, slovak_plain_lform.analysis,
  slovak_plain_prs.analysis, slovenian_plain_lform.analysis, slovenian_plain_prs.analysis,
  ukrainian_plain_lform.analysis, ukrainian_plain_prs.analysis, upper_sorbian_plain_lform.analysis,
  upper_sorbian_plain_prs.analysis, belarusian_palatal_lform.analysis,
  belarusian_palatal_prs.analysis, bunyev_ac_palatal_lform.analysis, bunyev_ac_palatal_prs.analysis,
  czech_palatal_lform.analysis, czech_palatal_prs.analysis, kashubian_palatal_lform.analysis,
  kashubian_palatal_prs.analysis, lower_sorbian_palatal_lform.analysis,
  lower_sorbian_palatal_prs.analysis, pannonian_rusyn_palatal_lform.analysis,
  pannonian_rusyn_palatal_prs.analysis, podlachian_palatal_lform.analysis,
  podlachian_palatal_prs.analysis, polish_palatal_lform.analysis, polish_palatal_prs.analysis,
  slovak_palatal_lform.analysis, slovak_palatal_prs.analysis, silesian_palatal_lform.analysis,
  silesian_palatal_prs.analysis, upper_sorbian_palatal_lform.analysis,
  upper_sorbian_palatal_prs.analysis, bos_cro_mon_ser_palatal_lform.analysis,
  bos_cro_mon_ser_palatal_prs.analysis, carpathian_rusyn_palatal_lform.analysis,
  carpathian_rusyn_palatal_prs.analysis, russian_palatal_lform.analysis,
  russian_palatal_prs.analysis, slovenian_palatal_lform.analysis, slovenian_palatal_prs.analysis,
  bulgarian_palatal_lform.analysis, bulgarian_palatal_prs.analysis,
  lemko_rusyn_palatal_lform.analysis, lemko_rusyn_palatal_prs.analysis,
  macedonian_palatal_lform.analysis, macedonian_palatal_prs.analysis,
  ukrainian_palatal_lform.analysis, ukrainian_palatal_prs.analysis]

end Stojkovic2026.Wordlist
