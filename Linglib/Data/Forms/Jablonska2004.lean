module

public import Linglib.Data.Forms.Schema

/-!
# `Jablonska2004`: word forms

Auto-generated from `Linglib/Data/Forms/Jablonska2004.json` by `scripts/gen_forms.py`. Do not edit
by hand; edit the JSON and re-run the generator. Declarations live in `namespace
Jablonska2004.Forms`.
-/

@[expose] public section

namespace Jablonska2004.Forms

open Data.Forms

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

/-- The infinitive cell, `VerbForm=Inf`. -/
def inf : Cell := { verbForm := ↑UD.VerbForm.Inf }

/-- The pst.pl.vir cell, `Tense=Past|Number=Plur`. -/
def pst_pl_vir : Cell := { tense := ↑UD.Tense.Past, number := ↑UD.Number.Plur }

/-- The pst.m.sg.1 cell, `Tense=Past|Gender=Masc|Number=Sing|Person=1`. -/
def pst_m_sg_1 : Cell :=
  { tense := ↑UD.Tense.Past, gender := ↑UD.Gender.Masc, number := ↑UD.Number.Sing,
    person := ↑UD.Person.first }

/-- The pst.f.sg cell, `Tense=Past|Gender=Fem|Number=Sing`. -/
def pst_f_sg : Cell :=
  { tense := ↑UD.Tense.Past, gender := ↑UD.Gender.Fem, number := ↑UD.Number.Sing }

/-- The pst.vir.1pl cell, `Tense=Past|Number=Plur|Person=1`. -/
def pst_vir_1pl : Cell :=
  { tense := ↑UD.Tense.Past, number := ↑UD.Number.Plur, person := ↑UD.Person.first }

/-- The prs.2sg cell, `Tense=Pres|Number=Sing|Person=2`. -/
def prs_2sg : Cell :=
  { tense := ↑UD.Tense.Pres, number := ↑UD.Number.Sing, person := ↑UD.Person.second }

/-- The prs.3sg cell, `Tense=Pres|Number=Sing|Person=3`. -/
def prs_3sg : Cell :=
  { tense := ↑UD.Tense.Pres, number := ↑UD.Number.Sing, person := ↑UD.Person.third }

def Lexemes.posiwiec : Lexeme :=
  { id := "posiwiec", languageId := "poli1260", parameterId := "turn_grey", pos := ↑UD.UPOS.VERB }

def Lexemes.pojasniec : Lexeme :=
  { id := "pojasniec", languageId := "poli1260", parameterId := "get_bright", pos := ↑UD.UPOS.VERB }

def Lexemes.poczerwieniec : Lexeme :=
  { id := "poczerwieniec", languageId := "poli1260", parameterId := "get_red",
    pos := ↑UD.UPOS.VERB }

def Lexemes.posmutniec : Lexeme :=
  { id := "posmutniec", languageId := "poli1260", parameterId := "get_sad", pos := ↑UD.UPOS.VERB }

def Lexemes.drozec : Lexeme :=
  { id := "drozec", languageId := "poli1260", parameterId := "get_expensive", pos := ↑UD.UPOS.VERB }

def Lexemes.zieleniec : Lexeme :=
  { id := "zieleniec", languageId := "poli1260", parameterId := "get_green", pos := ↑UD.UPOS.VERB }

def Lexemes.pociemniec : Lexeme :=
  { id := "pociemniec", languageId := "poli1260", parameterId := "get_dark", pos := ↑UD.UPOS.VERB }

def Lexemes.zciemniec : Lexeme :=
  { id := "zciemniec", languageId := "poli1260", parameterId := "get_dark", pos := ↑UD.UPOS.VERB }

def Lexemes.podrozec : Lexeme :=
  { id := "podrozec", languageId := "poli1260", parameterId := "get_expensive",
    pos := ↑UD.UPOS.VERB }

def Lexemes.zdrozec : Lexeme :=
  { id := "zdrozec", languageId := "poli1260", parameterId := "get_expensive",
    pos := ↑UD.UPOS.VERB }

def Lexemes.postarzec_sie : Lexeme :=
  { id := "postarzec_sie", languageId := "poli1260", parameterId := "get_old",
    pos := ↑UD.UPOS.VERB }

def Lexemes.zestarzec_sie : Lexeme :=
  { id := "zestarzec_sie", languageId := "poli1260", parameterId := "get_old",
    pos := ↑UD.UPOS.VERB }

def Lexemes.pobabieli : Lexeme :=
  { id := "pobabieli", languageId := "poli1260", parameterId := "become_effeminate",
    pos := ↑UD.UPOS.VERB }

def Lexemes.poprzeczytywalem : Lexeme :=
  { id := "poprzeczytywalem", languageId := "poli1260",
    parameterId := "read_through_distributively", pos := ↑UD.UPOS.VERB }

def Lexemes.poprzeczytalem : Lexeme :=
  { id := "poprzeczytalem", languageId := "poli1260", parameterId := "read_through_distributively",
    pos := ↑UD.UPOS.VERB }

def Lexemes.poczytac : Lexeme :=
  { id := "poczytac", languageId := "poli1260", parameterId := "read_for_a_while",
    pos := ↑UD.UPOS.VERB }

def Lexemes.pograc : Lexeme :=
  { id := "pograc", languageId := "poli1260", parameterId := "play_for_a_while",
    pos := ↑UD.UPOS.VERB }

def Lexemes.pochodzic : Lexeme :=
  { id := "pochodzic", languageId := "poli1260", parameterId := "walk_for_a_while",
    pos := ↑UD.UPOS.VERB }

def Lexemes.popalic : Lexeme :=
  { id := "popalic", languageId := "poli1260", parameterId := "smoke_for_a_while",
    pos := ↑UD.UPOS.VERB }

def Lexemes.pochowala : Lexeme :=
  { id := "pochowala", languageId := "poli1260",
    parameterId := "hide_distributively_or_for_a_while", pos := ↑UD.UPOS.VERB }

def Lexemes.poprzepisywala : Lexeme :=
  { id := "poprzepisywala", languageId := "poli1260",
    parameterId := "rewrite_distributively_or_for_a_while", pos := ↑UD.UPOS.VERB }

def Lexemes.pospiewali : Lexeme :=
  { id := "pospiewali", languageId := "poli1260", parameterId := "sing_for_a_while",
    pos := ↑UD.UPOS.VERB }

def Lexemes.powchodzili : Lexeme :=
  { id := "powchodzili", languageId := "poli1260", parameterId := "enter_distributively",
    pos := ↑UD.UPOS.VERB }

def Lexemes.przepisac : Lexeme :=
  { id := "przepisac", languageId := "poli1260", parameterId := "rewrite", pos := ↑UD.UPOS.VERB }

def Lexemes.robiac : Lexeme :=
  { id := "robiac", languageId := "poli1260", parameterId := "make_v_impf_inf",
    pos := ↑UD.UPOS.VERB }

def Lexemes.gwizdywac : Lexeme :=
  { id := "gwizdywac", languageId := "poli1260", parameterId := "whistle_v_impf_inf",
    pos := ↑UD.UPOS.VERB }

def Lexemes.poprzepisywac : Lexeme :=
  { id := "poprzepisywac", languageId := "poli1260", parameterId := "rewrite_for_a_while",
    pos := ↑UD.UPOS.VERB }

def Lexemes.pomarznac : Lexeme :=
  { id := "pomarznac", languageId := "poli1260", parameterId := "freeze_distributively",
    pos := ↑UD.UPOS.VERB }

def Lexemes.pogluchnac : Lexeme :=
  { id := "pogluchnac", languageId := "poli1260", parameterId := "go_deaf_distributively",
    pos := ↑UD.UPOS.VERB }

def Lexemes.powiednac : Lexeme :=
  { id := "powiednac", languageId := "poli1260", parameterId := "wither_distributively",
    pos := ↑UD.UPOS.VERB }

def Lexemes.poslepnac : Lexeme :=
  { id := "poslepnac", languageId := "poli1260", parameterId := "go_blind_distributively",
    pos := ↑UD.UPOS.VERB }

def Lexemes.postracic : Lexeme :=
  { id := "postracic", languageId := "poli1260", parameterId := "po_pref_lose",
    pos := ↑UD.UPOS.VERB }

def Lexemes.poobkopac : Lexeme :=
  { id := "poobkopac", languageId := "poli1260", parameterId := "po_around_dig",
    pos := ↑UD.UPOS.VERB }

def Lexemes.powyrzucic : Lexeme :=
  { id := "powyrzucic", languageId := "poli1260", parameterId := "po_out_throw",
    pos := ↑UD.UPOS.VERB }

def Lexemes.poobkopywac : Lexeme :=
  { id := "poobkopywac", languageId := "poli1260",
    parameterId := "dig_around_distributively_for_a_while", pos := ↑UD.UPOS.VERB }

def Lexemes.powyrzucac : Lexeme :=
  { id := "powyrzucac", languageId := "poli1260",
    parameterId := "throw_out_distributively_for_a_while", pos := ↑UD.UPOS.VERB }

def Lexemes.powarknac : Lexeme :=
  { id := "powarknac", languageId := "poli1260", parameterId := "po_snarl_sem_inf",
    pos := ↑UD.UPOS.VERB }

def Lexemes.pokopnac : Lexeme :=
  { id := "pokopnac", languageId := "poli1260", parameterId := "po_kick_sem_inf",
    pos := ↑UD.UPOS.VERB }

def Lexemes.pomachnac : Lexeme :=
  { id := "pomachnac", languageId := "poli1260", parameterId := "po_wave_sem_inf",
    pos := ↑UD.UPOS.VERB }

def Lexemes.machniesz : Lexeme :=
  { id := "machniesz", languageId := "poli1260", parameterId := "wave_once", pos := ↑UD.UPOS.VERB }

def Lexemes.powarknywac : Lexeme :=
  { id := "powarknywac", languageId := "poli1260", parameterId := "po_snarl_sem_impf_inf",
    pos := ↑UD.UPOS.VERB }

def Lexemes.pojsc : Lexeme :=
  { id := "pojsc", languageId := "poli1260", parameterId := "go_away", pos := ↑UD.UPOS.VERB }

def Lexemes.pobiec : Lexeme :=
  { id := "pobiec", languageId := "poli1260", parameterId := "run_away", pos := ↑UD.UPOS.VERB }

def Lexemes.poleciec : Lexeme :=
  { id := "poleciec", languageId := "poli1260", parameterId := "fly_away", pos := ↑UD.UPOS.VERB }

def Lexemes.pociagnac : Lexeme :=
  { id := "pociagnac", languageId := "poli1260", parameterId := "drag_a_bit", pos := ↑UD.UPOS.VERB }

def Lexemes.pobiegac : Lexeme :=
  { id := "pobiegac", languageId := "poli1260", parameterId := "run_for_a_while",
    pos := ↑UD.UPOS.VERB }

def Lexemes.polatac : Lexeme :=
  { id := "polatac", languageId := "poli1260", parameterId := "fly_for_a_while",
    pos := ↑UD.UPOS.VERB }

def Lexemes.pociagac : Lexeme :=
  { id := "pociagac", languageId := "poli1260", parameterId := "drag_for_a_while",
    pos := ↑UD.UPOS.VERB }

def Lexemes.zajasniec : Lexeme :=
  { id := "zajasniec", languageId := "poli1260", parameterId := "to_start_being_bright",
    pos := ↑UD.UPOS.VERB }

def Lexemes.pokochac : Lexeme :=
  { id := "pokochac", languageId := "poli1260", parameterId := "start_loving",
    pos := ↑UD.UPOS.VERB }

def Lexemes.polubic : Lexeme :=
  { id := "polubic", languageId := "poli1260", parameterId := "start_liking", pos := ↑UD.UPOS.VERB }

def Lexemes.posiedziec : Lexeme :=
  { id := "posiedziec", languageId := "poli1260", parameterId := "sit_for_a_while",
    pos := ↑UD.UPOS.VERB }

def Lexemes.poczytywac : Lexeme :=
  { id := "poczytywac", languageId := "poli1260",
    parameterId := "from_time_to_time_read_for_a_while", pos := ↑UD.UPOS.VERB }

def Lexemes.pogrywac : Lexeme :=
  { id := "pogrywac", languageId := "poli1260", parameterId := "from_time_to_time_play_for_a_while",
    pos := ↑UD.UPOS.VERB }

def Lexemes.pochadzac : Lexeme :=
  { id := "pochadzac", languageId := "poli1260",
    parameterId := "from_time_to_time_walk_for_a_while", pos := ↑UD.UPOS.VERB }

def Lexemes.popalac : Lexeme :=
  { id := "popalac", languageId := "poli1260", parameterId := "from_time_to_time_smoke_for_a_while",
    pos := ↑UD.UPOS.VERB }

def Lexemes.poplakiwac : Lexeme :=
  { id := "poplakiwac", languageId := "poli1260", parameterId := "cry_a_bit_from_time_to_time",
    pos := ↑UD.UPOS.VERB }

def Lexemes.pokaslywac : Lexeme :=
  { id := "pokaslywac", languageId := "poli1260", parameterId := "cough_a_bit_from_time_to_time",
    pos := ↑UD.UPOS.VERB }

def Lexemes.pomiaukiwac : Lexeme :=
  { id := "pomiaukiwac", languageId := "poli1260", parameterId := "meow_a_bit_from_time_to_time",
    pos := ↑UD.UPOS.VERB }

def Lexemes.pogwizdywac : Lexeme :=
  { id := "pogwizdywac", languageId := "poli1260", parameterId := "whistle_a_bit_from_time_to_time",
    pos := ↑UD.UPOS.VERB }

def Lexemes.pokroczac : Lexeme :=
  { id := "pokroczac", languageId := "poli1260", parameterId := "po_step_v_impf_inf",
    pos := ↑UD.UPOS.VERB }

def Lexemes.potanczac : Lexeme :=
  { id := "potanczac", languageId := "poli1260", parameterId := "po_dance_v_impf_inf",
    pos := ↑UD.UPOS.VERB }

def Lexemes.pokochiwac : Lexeme :=
  { id := "pokochiwac", languageId := "poli1260", parameterId := "po_love_v_impf_inf",
    pos := ↑UD.UPOS.VERB }

def Lexemes.grywac : Lexeme :=
  { id := "grywac", languageId := "poli1260", parameterId := "play_regularly_as_a_habit",
    pos := ↑UD.UPOS.VERB }

def Lexemes.popogrywac : Lexeme :=
  { id := "popogrywac", languageId := "poli1260",
    parameterId := "for_some_time_play_irregularly_from_time_to_time", pos := ↑UD.UPOS.VERB }

def Lexemes.popopalac : Lexeme :=
  { id := "popopalac", languageId := "poli1260",
    parameterId := "for_some_time_smoke_from_time_to_time", pos := ↑UD.UPOS.VERB }

def Lexemes.podjesc : Lexeme :=
  { id := "podjesc", languageId := "poli1260", parameterId := "eat_at_low_intensity",
    pos := ↑UD.UPOS.VERB }

def Lexemes.pomiauknac : Lexeme :=
  { id := "pomiauknac", languageId := "poli1260", parameterId := "meow_once_at_low_intensity",
    pos := ↑UD.UPOS.VERB }

def Lexemes.podmuchiwala : Lexeme :=
  { id := "podmuchiwala", languageId := "poli1260", parameterId := "blow_a_bit_from_time_to_time",
    pos := ↑UD.UPOS.VERB }

def Lexemes.stracic : Lexeme :=
  { id := "stracic", languageId := "poli1260", parameterId := "lose", pos := ↑UD.UPOS.VERB }

def Lexemes.zrobic : Lexeme :=
  { id := "zrobic", languageId := "poli1260", parameterId := "make", pos := ↑UD.UPOS.VERB }

def Lexemes.schowac : Lexeme :=
  { id := "schowac", languageId := "poli1260", parameterId := "hide", pos := ↑UD.UPOS.VERB }

def Lexemes.pobrudzic : Lexeme :=
  { id := "pobrudzic", languageId := "poli1260", parameterId := "dirty", pos := ↑UD.UPOS.VERB }

def Lexemes.pobic : Lexeme :=
  { id := "pobic", languageId := "poli1260", parameterId := "beat_up", pos := ↑UD.UPOS.VERB }

def Lexemes.pochwalic : Lexeme :=
  { id := "pochwalic", languageId := "poli1260", parameterId := "praise", pos := ↑UD.UPOS.VERB }

def Lexemes.zdziczac : Lexeme :=
  { id := "zdziczac", languageId := "poli1260", parameterId := "perf_wild_v_impf_inf",
    pos := ↑UD.UPOS.VERB }

def Lexemes.wygasnac : Lexeme :=
  { id := "wygasnac", languageId := "poli1260", parameterId := "expire", pos := ↑UD.UPOS.VERB }

def Lexemes.zgasnac : Lexeme :=
  { id := "zgasnac", languageId := "poli1260", parameterId := "go_out", pos := ↑UD.UPOS.VERB }

def Lexemes.podszepnac : Lexeme :=
  { id := "podszepnac", languageId := "poli1260", parameterId := "make_a_quiet_suggestion",
    pos := ↑UD.UPOS.VERB }

def Lexemes.szeptac : Lexeme :=
  { id := "szeptac", languageId := "poli1260", parameterId := "whisper", pos := ↑UD.UPOS.VERB }

def Lexemes.doplywa : Lexeme :=
  { id := "doplywa", languageId := "poli1260", parameterId := "reach_by_swimming",
    pos := ↑UD.UPOS.VERB }

def Lexemes.ponizyc : Lexeme :=
  { id := "ponizyc", languageId := "poli1260", parameterId := "humiliate", pos := ↑UD.UPOS.VERB }

def Lexemes.pocieszyc : Lexeme :=
  { id := "pocieszyc", languageId := "poli1260", parameterId := "console", pos := ↑UD.UPOS.VERB }

def Lexemes.porownac : Lexeme :=
  { id := "porownac", languageId := "poli1260", parameterId := "compare", pos := ↑UD.UPOS.VERB }

def Lexemes.pozwac : Lexeme :=
  { id := "pozwac", languageId := "poli1260", parameterId := "sue", pos := ↑UD.UPOS.VERB }

def Lexemes.polec : Lexeme :=
  { id := "polec", languageId := "poli1260", parameterId := "die_in_a_battle",
    pos := ↑UD.UPOS.VERB }

def Lexemes.pogrzybiec : Lexeme :=
  { id := "pogrzybiec", languageId := "poli1260", parameterId := "po_mushroom_v_inf",
    pos := ↑UD.UPOS.VERB }

def Lexemes.poporownywalismy : Lexeme :=
  { id := "poporownywalismy", languageId := "poli1260", parameterId := "compare_distributively",
    pos := ↑UD.UPOS.VERB }

def f_3a : Form Cell :=
  { id := "jablonska2004_3a"
    lexeme := Lexemes.posiwiec
    cell := inf
    form := "posiwieć"
    morphs := ["po", "siwi", "e", "ć"]
    source := [
      ⟨"jablonska-2004", "(3a)"⟩
    ] }

def f_3b : Form Cell :=
  { id := "jablonska2004_3b"
    lexeme := Lexemes.pojasniec
    cell := inf
    form := "pojaśnieć"
    morphs := ["po", "jaśni", "e", "ć"]
    source := [
      ⟨"jablonska-2004", "(3b)"⟩
    ] }

def f_3c : Form Cell :=
  { id := "jablonska2004_3c"
    lexeme := Lexemes.poczerwieniec
    cell := inf
    form := "poczerwienieć"
    morphs := ["po", "czerwieni", "e", "ć"]
    source := [
      ⟨"jablonska-2004", "(3c)"⟩
    ] }

def f_3d : Form Cell :=
  { id := "jablonska2004_3d"
    lexeme := Lexemes.posmutniec
    cell := inf
    form := "posmutnieć"
    morphs := ["po", "smutni", "e", "ć"]
    source := [
      ⟨"jablonska-2004", "(3d)"⟩
    ] }

def f_8a : Form Cell :=
  { id := "jablonska2004_8a"
    lexeme := Lexemes.drozec
    cell := inf
    form := "drożeć"
    morphs := ["drożeć"]
    source := [
      ⟨"jablonska-2004", "(8a)"⟩
    ] }

def f_9a : Form Cell :=
  { id := "jablonska2004_9a"
    lexeme := Lexemes.zieleniec
    cell := inf
    form := "zielenieć"
    morphs := ["zielenieć"]
    source := [
      ⟨"jablonska-2004", "(9a)"⟩
    ] }

def f_10a_po : Form Cell :=
  { id := "jablonska2004_10a_po"
    lexeme := Lexemes.pociemniec
    cell := inf
    form := "pociemnieć"
    morphs := ["po", "ciem", "ni", "e", "ć"]
    source := [
      ⟨"jablonska-2004", "(10a)"⟩
    ] }

def f_10a_z : Form Cell :=
  { id := "jablonska2004_10a_z"
    lexeme := Lexemes.zciemniec
    cell := inf
    form := "zciemnieć"
    morphs := ["z", "ciem", "ni", "e", "ć"]
    source := [
      ⟨"jablonska-2004", "(10a)"⟩
    ] }

def f_10b_po : Form Cell :=
  { id := "jablonska2004_10b_po"
    lexeme := Lexemes.podrozec
    cell := inf
    form := "podrożeć"
    morphs := ["po", "droż", "e", "ć"]
    source := [
      ⟨"jablonska-2004", "(10b)"⟩
    ] }

def f_10b_z : Form Cell :=
  { id := "jablonska2004_10b_z"
    lexeme := Lexemes.zdrozec
    cell := inf
    form := "zdrożeć"
    morphs := ["z", "droż", "e", "ć"]
    source := [
      ⟨"jablonska-2004", "(10b)"⟩
    ] }

def f_10c_po : Form Cell :=
  { id := "jablonska2004_10c_po"
    lexeme := Lexemes.postarzec_sie
    cell := inf
    form := "postarzeć się"
    morphs := ["po", "starz", "e", "ć", "się"]
    source := [
      ⟨"jablonska-2004", "(10c)"⟩
    ] }

def f_10c_z : Form Cell :=
  { id := "jablonska2004_10c_z"
    lexeme := Lexemes.zestarzec_sie
    cell := inf
    form := "zestarzeć się"
    morphs := ["ze", "starz", "e", "ć", "się"]
    source := [
      ⟨"jablonska-2004", "(10c)"⟩
    ] }

def f_23a : Form Cell :=
  { id := "jablonska2004_23a"
    lexeme := Lexemes.pobabieli
    cell := pst_pl_vir
    form := "pobabieli"
    morphs := ["po", "babi", "e", "li"]
    source := [
      ⟨"jablonska-2004", "(23a)"⟩
    ] }

def f_24a : Form Cell :=
  { id := "jablonska2004_24a"
    lexeme := Lexemes.poprzeczytywalem
    cell := pst_m_sg_1
    form := "poprzeczytywałem"
    morphs := ["po", "prze", "czyt", "ø", "ywa", "łem"]
    source := [
      ⟨"jablonska-2004", "(24a)"⟩
    ] }

def f_24b : Form Cell :=
  { id := "jablonska2004_24b"
    lexeme := Lexemes.poprzeczytalem
    cell := pst_m_sg_1
    form := "poprzeczytałem"
    morphs := ["po", "prze", "czyt", "a", "łem"]
    judgment := .ungrammatical
    source := [
      ⟨"jablonska-2004", "(24b)"⟩
    ] }

def f_27a : Form Cell :=
  { id := "jablonska2004_27a"
    lexeme := Lexemes.poczytac
    cell := inf
    form := "poczytać"
    morphs := ["po", "czyt", "a", "ć"]
    source := [
      ⟨"jablonska-2004", "(27a)"⟩
    ] }

def f_27b : Form Cell :=
  { id := "jablonska2004_27b"
    lexeme := Lexemes.pograc
    cell := inf
    form := "pograć"
    morphs := ["po", "gr", "a", "ć"]
    source := [
      ⟨"jablonska-2004", "(27b)"⟩
    ] }

def f_27c : Form Cell :=
  { id := "jablonska2004_27c"
    lexeme := Lexemes.pochodzic
    cell := inf
    form := "pochodzić"
    morphs := ["po", "chodz", "i", "ć"]
    source := [
      ⟨"jablonska-2004", "(27c)"⟩,
      ⟨"jablonska-2004", "(51a)"⟩
    ] }

def f_27d : Form Cell :=
  { id := "jablonska2004_27d"
    lexeme := Lexemes.popalic
    cell := inf
    form := "popalić"
    morphs := ["po", "pal", "i", "ć"]
    source := [
      ⟨"jablonska-2004", "(27d)"⟩
    ] }

def f_28a : Form Cell :=
  { id := "jablonska2004_28a"
    lexeme := Lexemes.pochowala
    cell := pst_f_sg
    form := "pochowała"
    morphs := ["po", "chowa", "ła"]
    source := [
      ⟨"jablonska-2004", "(28a)"⟩
    ] }

def f_28b : Form Cell :=
  { id := "jablonska2004_28b"
    lexeme := Lexemes.poprzepisywala
    cell := pst_f_sg
    form := "poprzepisywała"
    morphs := ["po", "prze", "pis", "ywa", "ła"]
    source := [
      ⟨"jablonska-2004", "(28b)"⟩
    ] }

def f_28c : Form Cell :=
  { id := "jablonska2004_28c"
    lexeme := Lexemes.pospiewali
    cell := pst_pl_vir
    form := "pośpiewali"
    morphs := ["po", "śpiewa", "li"]
    source := [
      ⟨"jablonska-2004", "(28c)"⟩
    ] }

def f_28d : Form Cell :=
  { id := "jablonska2004_28d"
    lexeme := Lexemes.powchodzili
    cell := pst_pl_vir
    form := "powchodzili"
    morphs := ["po", "w", "chodzi", "li"]
    source := [
      ⟨"jablonska-2004", "(28d)"⟩
    ] }

def f_30 : Form Cell :=
  { id := "jablonska2004_30"
    lexeme := Lexemes.przepisac
    cell := inf
    form := "przepisać"
    morphs := ["prze", "pisać"]
    source := [
      ⟨"jablonska-2004", "(30)"⟩
    ] }

def f_31a : Form Cell :=
  { id := "jablonska2004_31a"
    lexeme := Lexemes.przepisac
    cell := inf
    form := "przepisywać"
    morphs := ["prze", "pis", "ywa", "ć"]
    source := [
      ⟨"jablonska-2004", "(31a)"⟩
    ] }

def f_32a : Form Cell :=
  { id := "jablonska2004_32a"
    lexeme := Lexemes.robiac
    cell := inf
    form := "robiać"
    morphs := ["rob", "i", "a", "ć"]
    judgment := .ungrammatical
    source := [
      ⟨"jablonska-2004", "(32)"⟩
    ] }

def f_32b : Form Cell :=
  { id := "jablonska2004_32b"
    lexeme := Lexemes.gwizdywac
    cell := inf
    form := "gwizdywać"
    morphs := ["gwizd", "ø", "ywa", "ć"]
    judgment := .ungrammatical
    source := [
      ⟨"jablonska-2004", "(32)"⟩
    ] }

def f_34a : Form Cell :=
  { id := "jablonska2004_34a"
    lexeme := Lexemes.poprzepisywac
    cell := inf
    form := "poprzepisywać"
    morphs := ["po", "prze", "pis", "ywa", "ć"]
    source := [
      ⟨"jablonska-2004", "(34a)"⟩,
      ⟨"jablonska-2004", "(34b)"⟩
    ] }

def f_39a : Form Cell :=
  { id := "jablonska2004_39a"
    lexeme := Lexemes.pomarznac
    cell := inf
    form := "pomarznąć"
    morphs := ["po", "marz", "ną", "ć"]
    source := [
      ⟨"jablonska-2004", "(39a)"⟩
    ] }

def f_39b : Form Cell :=
  { id := "jablonska2004_39b"
    lexeme := Lexemes.pogluchnac
    cell := inf
    form := "pogłuchnąć"
    morphs := ["po", "głuch", "n", "ą", "ć"]
    source := [
      ⟨"jablonska-2004", "(39b)"⟩
    ] }

def f_39c : Form Cell :=
  { id := "jablonska2004_39c"
    lexeme := Lexemes.powiednac
    cell := inf
    form := "powiędnąć"
    morphs := ["po", "więd", "ną", "ć"]
    source := [
      ⟨"jablonska-2004", "(39c)"⟩
    ] }

def f_39d : Form Cell :=
  { id := "jablonska2004_39d"
    lexeme := Lexemes.poslepnac
    cell := inf
    form := "poślepnąć"
    morphs := ["po", "ślep", "ną", "ć"]
    source := [
      ⟨"jablonska-2004", "(39d)"⟩
    ] }

def f_42a : Form Cell :=
  { id := "jablonska2004_42a"
    lexeme := Lexemes.postracic
    cell := inf
    form := "postracić"
    morphs := ["po", "s", "tracić"]
    judgment := .ungrammatical
    source := [
      ⟨"jablonska-2004", "(42)"⟩
    ] }

def f_42b : Form Cell :=
  { id := "jablonska2004_42b"
    lexeme := Lexemes.poobkopac
    cell := inf
    form := "poobkopać"
    morphs := ["po", "ob", "kopać"]
    judgment := .ungrammatical
    source := [
      ⟨"jablonska-2004", "(42)"⟩
    ] }

def f_42c : Form Cell :=
  { id := "jablonska2004_42c"
    lexeme := Lexemes.powyrzucic
    cell := inf
    form := "powyrzucić"
    morphs := ["po", "wy", "rzucić"]
    judgment := .ungrammatical
    source := [
      ⟨"jablonska-2004", "(42)"⟩
    ] }

def f_43a : Form Cell :=
  { id := "jablonska2004_43a"
    lexeme := Lexemes.poobkopywac
    cell := inf
    form := "poobkopywać"
    morphs := ["po", "ob", "kop", "ywa", "ć"]
    source := [
      ⟨"jablonska-2004", "(43)"⟩
    ] }

def f_43b : Form Cell :=
  { id := "jablonska2004_43b"
    lexeme := Lexemes.powyrzucac
    cell := inf
    form := "powyrzucać"
    morphs := ["po", "wy", "rzuc", "a", "ć"]
    source := [
      ⟨"jablonska-2004", "(43)"⟩
    ] }

def f_45a : Form Cell :=
  { id := "jablonska2004_45a"
    lexeme := Lexemes.powarknac
    cell := inf
    form := "powarknąć"
    morphs := ["po", "wark", "ną", "ć"]
    judgment := .ungrammatical
    source := [
      ⟨"jablonska-2004", "(45)"⟩
    ] }

def f_45b : Form Cell :=
  { id := "jablonska2004_45b"
    lexeme := Lexemes.pokopnac
    cell := inf
    form := "pokopnąć"
    morphs := ["po", "kop", "ną", "ć"]
    judgment := .ungrammatical
    source := [
      ⟨"jablonska-2004", "(45)"⟩
    ] }

def f_45c : Form Cell :=
  { id := "jablonska2004_45c"
    lexeme := Lexemes.pomachnac
    cell := inf
    form := "pomachnąć"
    morphs := ["po", "mach", "ną", "ć"]
    judgment := .ungrammatical
    source := [
      ⟨"jablonska-2004", "(45)"⟩
    ] }

def f_46b : Form Cell :=
  { id := "jablonska2004_46b"
    lexeme := Lexemes.machniesz
    cell := prs_2sg
    form := "machniesz"
    morphs := ["mach", "ni", "e", "sz"]
    source := [
      ⟨"jablonska-2004", "(46b)"⟩
    ] }

def f_48 : Form Cell :=
  { id := "jablonska2004_48"
    lexeme := Lexemes.powarknywac
    cell := inf
    form := "powarknywać"
    morphs := ["po", "wark", "n", "ywa", "ć"]
    judgment := .ungrammatical
    source := [
      ⟨"jablonska-2004", "(48)"⟩
    ] }

def f_50a : Form Cell :=
  { id := "jablonska2004_50a"
    lexeme := Lexemes.pojsc
    cell := inf
    form := "pójść"
    morphs := ["pó", "jść"]
    source := [
      ⟨"jablonska-2004", "(50a)"⟩
    ] }

def f_50b : Form Cell :=
  { id := "jablonska2004_50b"
    lexeme := Lexemes.pobiec
    cell := inf
    form := "pobiec"
    morphs := ["po", "biec"]
    source := [
      ⟨"jablonska-2004", "(50b)"⟩
    ] }

def f_50c : Form Cell :=
  { id := "jablonska2004_50c"
    lexeme := Lexemes.poleciec
    cell := inf
    form := "polecieć"
    morphs := ["po", "lecieć"]
    source := [
      ⟨"jablonska-2004", "(50c)"⟩
    ] }

def f_50d : Form Cell :=
  { id := "jablonska2004_50d"
    lexeme := Lexemes.pociagnac
    cell := inf
    form := "pociągnąć"
    morphs := ["po", "ciągnąć"]
    source := [
      ⟨"jablonska-2004", "(50d)"⟩
    ] }

def f_51b : Form Cell :=
  { id := "jablonska2004_51b"
    lexeme := Lexemes.pobiegac
    cell := inf
    form := "pobiegać"
    morphs := ["po", "biegać"]
    source := [
      ⟨"jablonska-2004", "(51b)"⟩
    ] }

def f_51c : Form Cell :=
  { id := "jablonska2004_51c"
    lexeme := Lexemes.polatac
    cell := inf
    form := "polatać"
    morphs := ["po", "latać"]
    source := [
      ⟨"jablonska-2004", "(51c)"⟩
    ] }

def f_51d : Form Cell :=
  { id := "jablonska2004_51d"
    lexeme := Lexemes.pociagac
    cell := inf
    form := "pociągać"
    morphs := ["po", "ciągać"]
    source := [
      ⟨"jablonska-2004", "(51d)"⟩
    ] }

def f_53 : Form Cell :=
  { id := "jablonska2004_53"
    lexeme := Lexemes.zajasniec
    cell := inf
    form := "zajaśnieć"
    morphs := ["za", "jaś", "ni", "e", "ć"]
    source := [
      ⟨"jablonska-2004", "(53)"⟩
    ] }

def f_54a : Form Cell :=
  { id := "jablonska2004_54a"
    lexeme := Lexemes.pokochac
    cell := inf
    form := "pokochać"
    morphs := ["po", "kochać"]
    source := [
      ⟨"jablonska-2004", "(54a)"⟩
    ] }

def f_54b : Form Cell :=
  { id := "jablonska2004_54b"
    lexeme := Lexemes.polubic
    cell := inf
    form := "polubić"
    morphs := ["po", "lubić"]
    source := [
      ⟨"jablonska-2004", "(54b)"⟩
    ] }

def fn21 : Form Cell :=
  { id := "jablonska2004_fn21"
    lexeme := Lexemes.posiedziec
    cell := inf
    form := "posiedzieć"
    morphs := ["po", "siedzieć"]
    source := [
      ⟨"jablonska-2004", "fn. 21"⟩
    ] }

def f_56a : Form Cell :=
  { id := "jablonska2004_56a"
    lexeme := Lexemes.poczytywac
    cell := inf
    form := "poczytywać"
    morphs := ["po", "czyt", "ø", "ywa", "ć"]
    judgment := .marginal
    source := [
      ⟨"jablonska-2004", "(56a)"⟩
    ] }

def f_56b : Form Cell :=
  { id := "jablonska2004_56b"
    lexeme := Lexemes.pogrywac
    cell := inf
    form := "pogrywać"
    morphs := ["po", "gr", "ø", "ywa", "ć"]
    source := [
      ⟨"jablonska-2004", "(56b)"⟩,
      ⟨"jablonska-2004", "(60)"⟩
    ] }

def f_56c : Form Cell :=
  { id := "jablonska2004_56c"
    lexeme := Lexemes.pochadzac
    cell := inf
    form := "pochadzać"
    morphs := ["po", "chadz", "a", "ć"]
    judgment := .ungrammatical
    source := [
      ⟨"jablonska-2004", "(56c)"⟩
    ] }

def f_56d : Form Cell :=
  { id := "jablonska2004_56d"
    lexeme := Lexemes.popalac
    cell := inf
    form := "popalać"
    morphs := ["po", "pal", "ø", "a", "ć"]
    source := [
      ⟨"jablonska-2004", "(56d)"⟩
    ] }

def f_57a : Form Cell :=
  { id := "jablonska2004_57a"
    lexeme := Lexemes.poplakiwac
    cell := inf
    form := "popłakiwać"
    morphs := ["po", "płak", "ø", "iwa", "ć"]
    source := [
      ⟨"jablonska-2004", "(57a)"⟩
    ] }

def f_57b : Form Cell :=
  { id := "jablonska2004_57b"
    lexeme := Lexemes.pokaslywac
    cell := inf
    form := "pokasływać"
    morphs := ["po", "kasł", "ø", "ywa", "ć"]
    source := [
      ⟨"jablonska-2004", "(57b)"⟩
    ] }

def f_57c : Form Cell :=
  { id := "jablonska2004_57c"
    lexeme := Lexemes.pomiaukiwac
    cell := inf
    form := "pomiaukiwać"
    morphs := ["po", "miauk", "ø", "iwa", "ć"]
    source := [
      ⟨"jablonska-2004", "(57c)"⟩
    ] }

def f_57d : Form Cell :=
  { id := "jablonska2004_57d"
    lexeme := Lexemes.pogwizdywac
    cell := inf
    form := "pogwizdywać"
    morphs := ["po", "gwizd", "ø", "ywać"]
    source := [
      ⟨"jablonska-2004", "(57d)"⟩
    ] }

def f_58a : Form Cell :=
  { id := "jablonska2004_58a"
    lexeme := Lexemes.pokroczac
    cell := inf
    form := "pokroczać"
    morphs := ["po", "krocz", "ø", "a", "ć"]
    judgment := .ungrammatical
    source := [
      ⟨"jablonska-2004", "(58a)"⟩
    ] }

def f_58b : Form Cell :=
  { id := "jablonska2004_58b"
    lexeme := Lexemes.potanczac
    cell := inf
    form := "potańczać"
    morphs := ["po", "tańcz", "ø", "a", "ć"]
    judgment := .ungrammatical
    source := [
      ⟨"jablonska-2004", "(58b)"⟩
    ] }

def f_58c : Form Cell :=
  { id := "jablonska2004_58c"
    lexeme := Lexemes.pokochiwac
    cell := inf
    form := "pokochiwać"
    morphs := ["po", "koch", "ø", "iwa", "ć"]
    judgment := .ungrammatical
    source := [
      ⟨"jablonska-2004", "(58c)"⟩
    ] }

def f_59a : Form Cell :=
  { id := "jablonska2004_59a"
    lexeme := Lexemes.posiwiec
    cell := inf
    form := "posiwiać"
    morphs := ["po", "siwi", "a", "ć"]
    judgment := .ungrammatical
    source := [
      ⟨"jablonska-2004", "(59a)"⟩
    ] }

def f_60_bare : Form Cell :=
  { id := "jablonska2004_60_bare"
    lexeme := Lexemes.grywac
    cell := inf
    form := "grywać"
    morphs := ["gr", "ywa", "ć"]
    source := [
      ⟨"jablonska-2004", "(60)"⟩
    ] }

def f_61a : Form Cell :=
  { id := "jablonska2004_61a"
    lexeme := Lexemes.popogrywac
    cell := inf
    form := "popogrywać"
    morphs := ["po", "po", "gr", "ywa", "ć"]
    judgment := .ungrammatical
    source := [
      ⟨"jablonska-2004", "(61a)"⟩
    ] }

def f_61b : Form Cell :=
  { id := "jablonska2004_61b"
    lexeme := Lexemes.popopalac
    cell := inf
    form := "popopalać"
    morphs := ["po", "po", "pal", "a", "ć"]
    judgment := .ungrammatical
    source := [
      ⟨"jablonska-2004", "(61b)"⟩
    ] }

def f_62a : Form Cell :=
  { id := "jablonska2004_62a"
    lexeme := Lexemes.podjesc
    cell := inf
    form := "podjeść"
    morphs := ["pod", "jeść"]
    source := [
      ⟨"jablonska-2004", "(62a)"⟩
    ] }

def f_62b : Form Cell :=
  { id := "jablonska2004_62b"
    lexeme := Lexemes.podjesc
    cell := inf
    form := "podjadać"
    morphs := ["pod", "jad", "a", "ć"]
    source := [
      ⟨"jablonska-2004", "(62b)"⟩
    ] }

def f_63b : Form Cell :=
  { id := "jablonska2004_63b"
    lexeme := Lexemes.pomiauknac
    cell := inf
    form := "pomiauknąć"
    morphs := ["po", "miauk", "ną", "ć"]
    judgment := .ungrammatical
    source := [
      ⟨"jablonska-2004", "(63b)"⟩
    ] }

def f_65a : Form Cell :=
  { id := "jablonska2004_65a"
    lexeme := Lexemes.podmuchiwala
    cell := pst_f_sg
    form := "podmuchiwała"
    morphs := ["po", "dmuch", "iwa", "ła"]
    source := [
      ⟨"jablonska-2004", "(65a)"⟩
    ] }

def f_67a_pf : Form Cell :=
  { id := "jablonska2004_67a_pf"
    lexeme := Lexemes.stracic
    cell := inf
    form := "stracić"
    morphs := ["s", "trac", "i", "ć"]
    source := [
      ⟨"jablonska-2004", "(67a)"⟩
    ] }

def f_67a_si : Form Cell :=
  { id := "jablonska2004_67a_si"
    lexeme := Lexemes.stracic
    cell := inf
    form := "stracać"
    morphs := ["s", "trac", "a", "ć"]
    judgment := .ungrammatical
    source := [
      ⟨"jablonska-2004", "(67a)"⟩
    ] }

def f_67b_pf : Form Cell :=
  { id := "jablonska2004_67b_pf"
    lexeme := Lexemes.zrobic
    cell := inf
    form := "zrobić"
    morphs := ["z", "rob", "i", "ć"]
    source := [
      ⟨"jablonska-2004", "(67b)"⟩
    ] }

def f_67b_si : Form Cell :=
  { id := "jablonska2004_67b_si"
    lexeme := Lexemes.zrobic
    cell := inf
    form := "zrabiać"
    morphs := ["z", "rab", "i", "a", "ć"]
    judgment := .ungrammatical
    source := [
      ⟨"jablonska-2004", "(67b)"⟩
    ] }

def f_67c_pf : Form Cell :=
  { id := "jablonska2004_67c_pf"
    lexeme := Lexemes.schowac
    cell := inf
    form := "schować"
    morphs := ["s", "chow", "a", "ć"]
    source := [
      ⟨"jablonska-2004", "(67c)"⟩
    ] }

def f_67c_si : Form Cell :=
  { id := "jablonska2004_67c_si"
    lexeme := Lexemes.schowac
    cell := inf
    form := "schowywać"
    morphs := ["s", "chow", "ywa", "ć"]
    judgment := .ungrammatical
    source := [
      ⟨"jablonska-2004", "(67c)"⟩
    ] }

def f_69a_pf : Form Cell :=
  { id := "jablonska2004_69a_pf"
    lexeme := Lexemes.pobrudzic
    cell := inf
    form := "pobrudzić"
    morphs := ["po", "brudzić"]
    source := [
      ⟨"jablonska-2004", "(69a)"⟩
    ] }

def f_69a_si : Form Cell :=
  { id := "jablonska2004_69a_si"
    lexeme := Lexemes.pobrudzic
    cell := inf
    form := "pobrudzać"
    morphs := ["po", "brudz", "ø", "a", "ć"]
    judgment := .ungrammatical
    source := [
      ⟨"jablonska-2004", "(69a)"⟩
    ] }

def f_69b_pf : Form Cell :=
  { id := "jablonska2004_69b_pf"
    lexeme := Lexemes.pobic
    cell := inf
    form := "pobić"
    morphs := ["po", "bić"]
    source := [
      ⟨"jablonska-2004", "(69b)"⟩
    ] }

def f_69b_si : Form Cell :=
  { id := "jablonska2004_69b_si"
    lexeme := Lexemes.pobic
    cell := inf
    form := "pobijać"
    morphs := ["po", "bij", "a", "ć"]
    judgment := .ungrammatical
    source := [
      ⟨"jablonska-2004", "(69b)"⟩
    ] }

def f_69c_pf : Form Cell :=
  { id := "jablonska2004_69c_pf"
    lexeme := Lexemes.pochwalic
    cell := inf
    form := "pochwalić"
    morphs := ["po", "chwalić"]
    source := [
      ⟨"jablonska-2004", "(69c)"⟩
    ] }

def f_69c_si : Form Cell :=
  { id := "jablonska2004_69c_si"
    lexeme := Lexemes.pochwalic
    cell := inf
    form := "pochwalać"
    morphs := ["po", "chwal", "ø", "a", "ć"]
    judgment := .ungrammatical
    source := [
      ⟨"jablonska-2004", "(69c)"⟩
    ] }

def f_73a : Form Cell :=
  { id := "jablonska2004_73a"
    lexeme := Lexemes.zdziczac
    cell := inf
    form := "zdziczać"
    morphs := ["z", "dzicz", "ø", "a", "ć"]
    judgment := .ungrammatical
    source := [
      ⟨"jablonska-2004", "(73a)"⟩
    ] }

def f_74 : Form Cell :=
  { id := "jablonska2004_74"
    lexeme := Lexemes.posiwiec
    cell := inf
    form := "posiwać"
    morphs := ["po", "siw", "ø", "a", "ć"]
    judgment := .ungrammatical
    source := [
      ⟨"jablonska-2004", "(74)"⟩
    ] }

def f_75a : Form Cell :=
  { id := "jablonska2004_75a"
    lexeme := Lexemes.wygasnac
    cell := inf
    form := "wygasnąć"
    morphs := ["wy", "gas", "ną", "ć"]
    source := [
      ⟨"jablonska-2004", "(75a)"⟩
    ] }

def f_75b : Form Cell :=
  { id := "jablonska2004_75b"
    lexeme := Lexemes.zgasnac
    cell := inf
    form := "zgasnąć"
    morphs := ["z", "gas", "ną", "ć"]
    source := [
      ⟨"jablonska-2004", "(75b)"⟩
    ] }

def f_76_a : Form Cell :=
  { id := "jablonska2004_76_a"
    lexeme := Lexemes.wygasnac
    cell := inf
    form := "wygasnać"
    morphs := ["wy", "gas", "n", "a", "ć"]
    judgment := .ungrammatical
    source := [
      ⟨"jablonska-2004", "(76)"⟩
    ] }

def f_76_b : Form Cell :=
  { id := "jablonska2004_76_b"
    lexeme := Lexemes.wygasnac
    cell := inf
    form := "wygasnywać"
    morphs := ["wy", "gas", "n", "ywa", "ć"]
    judgment := .ungrammatical
    source := [
      ⟨"jablonska-2004", "(76)"⟩
    ] }

def f_77 : Form Cell :=
  { id := "jablonska2004_77"
    lexeme := Lexemes.wygasnac
    cell := inf
    form := "wygasać"
    morphs := ["wy", "gas", "a", "ć"]
    source := [
      ⟨"jablonska-2004", "(77)"⟩
    ] }

def f_78 : Form Cell :=
  { id := "jablonska2004_78"
    lexeme := Lexemes.zgasnac
    cell := inf
    form := "zgasać"
    morphs := ["z", "gas", "a", "ć"]
    judgment := .ungrammatical
    source := [
      ⟨"jablonska-2004", "(78)"⟩
    ] }

def f_79a : Form Cell :=
  { id := "jablonska2004_79a"
    lexeme := Lexemes.podszepnac
    cell := inf
    form := "podszepnąć"
    morphs := ["pod", "szep", "ną", "ć"]
    source := [
      ⟨"jablonska-2004", "(79a)"⟩
    ] }

def f_79b : Form Cell :=
  { id := "jablonska2004_79b"
    lexeme := Lexemes.podszepnac
    cell := inf
    form := "podszepnywać"
    morphs := ["pod", "szep", "n", "ywa", "ć"]
    judgment := .ungrammatical
    source := [
      ⟨"jablonska-2004", "(79b)"⟩
    ] }

def f_79c : Form Cell :=
  { id := "jablonska2004_79c"
    lexeme := Lexemes.szeptac
    cell := inf
    form := "szeptać"
    morphs := ["szept", "a", "ć"]
    source := [
      ⟨"jablonska-2004", "(79c)"⟩
    ] }

def f_79d : Form Cell :=
  { id := "jablonska2004_79d"
    lexeme := Lexemes.podszepnac
    cell := inf
    form := "podszeptywać"
    morphs := ["pod", "szept", "ø", "ywa", "ć"]
    source := [
      ⟨"jablonska-2004", "(79d)"⟩
    ] }

def f_80b : Form Cell :=
  { id := "jablonska2004_80b"
    lexeme := Lexemes.doplywa
    cell := prs_3sg
    form := "dopływa"
    morphs := ["do", "pływa"]
    source := [
      ⟨"jablonska-2004", "(80b)"⟩
    ] }

def f_81a : Form Cell :=
  { id := "jablonska2004_81a"
    lexeme := Lexemes.ponizyc
    cell := inf
    form := "poniżyć"
    morphs := ["po", "niż", "y", "ć"]
    source := [
      ⟨"jablonska-2004", "(81a)"⟩
    ] }

def f_81b : Form Cell :=
  { id := "jablonska2004_81b"
    lexeme := Lexemes.pocieszyc
    cell := inf
    form := "pocieszyć"
    morphs := ["po", "ciesz", "y", "ć"]
    source := [
      ⟨"jablonska-2004", "(81b)"⟩
    ] }

def f_81c : Form Cell :=
  { id := "jablonska2004_81c"
    lexeme := Lexemes.porownac
    cell := inf
    form := "porównać"
    morphs := ["po", "równ", "a", "ć"]
    source := [
      ⟨"jablonska-2004", "(81c)"⟩
    ] }

def f_81d : Form Cell :=
  { id := "jablonska2004_81d"
    lexeme := Lexemes.pozwac
    cell := inf
    form := "pozwać"
    morphs := ["po", "zw", "ać"]
    source := [
      ⟨"jablonska-2004", "(81d)"⟩
    ] }

def f_81e : Form Cell :=
  { id := "jablonska2004_81e"
    lexeme := Lexemes.polec
    cell := inf
    form := "polec"
    morphs := ["po", "le", "c"]
    source := [
      ⟨"jablonska-2004", "(81e)"⟩
    ] }

def f_81f : Form Cell :=
  { id := "jablonska2004_81f"
    lexeme := Lexemes.pogrzybiec
    cell := inf
    form := "pogrzybieć"
    morphs := ["po", "grzybi", "e", "ć"]
    judgment := .ungrammatical
    source := [
      ⟨"jablonska-2004", "(81f)"⟩
    ] }

def f_82a : Form Cell :=
  { id := "jablonska2004_82a"
    lexeme := Lexemes.ponizyc
    cell := inf
    form := "poniżać"
    morphs := ["po", "niż", "ø", "a", "ć"]
    source := [
      ⟨"jablonska-2004", "(82a)"⟩
    ] }

def f_82b : Form Cell :=
  { id := "jablonska2004_82b"
    lexeme := Lexemes.pocieszyc
    cell := inf
    form := "pocieszać"
    morphs := ["po", "ciesz", "ø", "a", "ć"]
    source := [
      ⟨"jablonska-2004", "(82b)"⟩
    ] }

def f_82c : Form Cell :=
  { id := "jablonska2004_82c"
    lexeme := Lexemes.porownac
    cell := inf
    form := "porównywać"
    morphs := ["po", "równ", "ø", "ywa", "ć"]
    source := [
      ⟨"jablonska-2004", "(82c)"⟩
    ] }

def f_82d : Form Cell :=
  { id := "jablonska2004_82d"
    lexeme := Lexemes.pozwac
    cell := inf
    form := "pozywać"
    morphs := ["po", "zyw", "a", "ć"]
    source := [
      ⟨"jablonska-2004", "(82d)"⟩
    ] }

def f_83a : Form Cell :=
  { id := "jablonska2004_83a"
    lexeme := Lexemes.poporownywalismy
    cell := pst_vir_1pl
    form := "poporównywaliśmy"
    morphs := ["po", "po", "równ", "ywa", "li", "śmy"]
    source := [
      ⟨"jablonska-2004", "(83a)"⟩
    ] }

/-- The source's analysis of a form, its parse rather than data. -/
structure Analysis where
  /-- The form analysed. -/
  form : Form Cell
  /-- The `Verbalizer` column, the verbalizer the paper names for the stem. -/
  verbalizer : Option String := none
  /-- The `Layers` column, the positions the paper assigns the prefixes and the Secondary
  Imperfective. -/
  layers : Option String := none
  /-- The `Reading` column, the reading of po- the paper gives. -/
  reading : Option String := none
  /-- The `Scale` column, the scale of a degree achievement, open or closed. -/
  scale : Option String := none
  deriving DecidableEq, Repr

def f_3a.analysis : Analysis :=
  { form := f_3a,
    verbalizer := some "low -ej-",
    layers := some "po- in Asp1" }

def f_3b.analysis : Analysis :=
  { form := f_3b,
    verbalizer := some "low -ej-",
    layers := some "po- in Asp1" }

def f_3c.analysis : Analysis :=
  { form := f_3c,
    verbalizer := some "low -ej-",
    layers := some "po- in Asp1" }

def f_3d.analysis : Analysis :=
  { form := f_3d,
    verbalizer := some "low -ej-",
    layers := some "po- in Asp1" }

def f_8a.analysis : Analysis :=
  { form := f_8a,
    scale := some "open" }

def f_9a.analysis : Analysis :=
  { form := f_9a,
    scale := some "closed" }

def f_10a_po.analysis : Analysis :=
  { form := f_10a_po,
    verbalizer := some "low -ej-",
    layers := some "po- in Asp1",
    reading := some "considerable change" }

def f_10a_z.analysis : Analysis :=
  { form := f_10a_z,
    verbalizer := some "low -ej-",
    layers := some "purely perfectivizing prefix in Asp2" }

def f_10b_po.analysis : Analysis :=
  { form := f_10b_po,
    verbalizer := some "low -ej-",
    layers := some "po- in Asp1",
    reading := some "considerable change" }

def f_10b_z.analysis : Analysis :=
  { form := f_10b_z,
    verbalizer := some "low -ej-",
    layers := some "purely perfectivizing prefix in Asp2" }

def f_10c_po.analysis : Analysis :=
  { form := f_10c_po,
    verbalizer := some "low -ej-",
    layers := some "po- in Asp1",
    reading := some "considerable change" }

def f_10c_z.analysis : Analysis :=
  { form := f_10c_z,
    verbalizer := some "low -ej-",
    layers := some "purely perfectivizing prefix in Asp2" }

def f_23a.analysis : Analysis :=
  { form := f_23a,
    verbalizer := some "low -ej-",
    layers := some "po- in Asp1",
    reading := some "distributive" }

def f_24a.analysis : Analysis :=
  { form := f_24a,
    verbalizer := some "high -aj-",
    layers := some "lexical prefix, Secondary Imperfective, po- in Asp3",
    reading := some "distributive" }

def f_24b.analysis : Analysis :=
  { form := f_24b,
    verbalizer := some "high -aj-",
    layers := some "lexical prefix, po-" }

def f_27a.analysis : Analysis :=
  { form := f_27a,
    verbalizer := some "high processual",
    layers := some "po- in Asp1",
    reading := some "delimitative" }

def f_27b.analysis : Analysis :=
  { form := f_27b,
    verbalizer := some "high processual",
    layers := some "po- in Asp1",
    reading := some "delimitative" }

def f_27c.analysis : Analysis :=
  { form := f_27c,
    verbalizer := some "high processual",
    layers := some "po- in Asp1",
    reading := some "delimitative" }

def f_27d.analysis : Analysis :=
  { form := f_27d,
    verbalizer := some "high processual",
    layers := some "po- in Asp1",
    reading := some "delimitative" }

def f_28a.analysis : Analysis :=
  { form := f_28a,
    verbalizer := some "high -aj-",
    reading := some "distributive or delimitative" }

def f_28b.analysis : Analysis :=
  { form := f_28b,
    layers := some "lexical prefix, Secondary Imperfective, po- in Asp3",
    reading := some "distributive or delimitative" }

def f_28c.analysis : Analysis :=
  { form := f_28c,
    reading := some "delimitative only: the external argument is outside the scope of po-" }

def f_28d.analysis : Analysis :=
  { form := f_28d,
    reading := some "distributive or delimitative" }

def f_30.analysis : Analysis :=
  { form := f_30,
    layers := some "lexical prefix valuing Asp1: RT after ET" }

def f_31a.analysis : Analysis :=
  { form := f_31a,
    layers := some "lexical prefix, Secondary Imperfective",
    reading := some "progressive: RT within ET" }

def f_32a.analysis : Analysis :=
  { form := f_32a,
    verbalizer := some "high -i-",
    layers := some "Secondary Imperfective on a bare stem" }

def f_32b.analysis : Analysis :=
  { form := f_32b,
    layers := some "Secondary Imperfective on a bare stem" }

def f_34a.analysis : Analysis :=
  { form := f_34a,
    layers := some "lexical prefix, Secondary Imperfective, po- in Asp3",
    reading := some "delimitative" }

def f_39a.analysis : Analysis :=
  { form := f_39a,
    verbalizer := some "low inchoative -n-",
    layers := some "po- in Asp1",
    reading := some "distributive" }

def f_39b.analysis : Analysis :=
  { form := f_39b,
    verbalizer := some "low inchoative -n-",
    layers := some "po- in Asp1",
    reading := some "distributive" }

def f_39c.analysis : Analysis :=
  { form := f_39c,
    verbalizer := some "low inchoative -n-",
    layers := some "po- in Asp1",
    reading := some "distributive" }

def f_39d.analysis : Analysis :=
  { form := f_39d,
    verbalizer := some "low inchoative -n-",
    layers := some "po- in Asp1",
    reading := some "distributive" }

def f_42a.analysis : Analysis :=
  { form := f_42a,
    layers := some "po- over a lexical prefix without SI" }

def f_42b.analysis : Analysis :=
  { form := f_42b,
    layers := some "po- over a lexical prefix without SI" }

def f_42c.analysis : Analysis :=
  { form := f_42c,
    layers := some "po- over a lexical prefix without SI" }

def f_43a.analysis : Analysis :=
  { form := f_43a,
    layers := some "lexical prefix, Secondary Imperfective, po- in Asp3" }

def f_43b.analysis : Analysis :=
  { form := f_43b,
    layers := some "lexical prefix, Secondary Imperfective, po- in Asp3" }

def f_45a.analysis : Analysis :=
  { form := f_45a,
    verbalizer := some "semelfactive",
    layers := some "po- in Asp1" }

def f_45b.analysis : Analysis :=
  { form := f_45b,
    verbalizer := some "semelfactive",
    layers := some "po- in Asp1" }

def f_45c.analysis : Analysis :=
  { form := f_45c,
    verbalizer := some "semelfactive",
    layers := some "po- in Asp1" }

def f_46b.analysis : Analysis :=
  { form := f_46b }

def f_48.analysis : Analysis :=
  { form := f_48,
    verbalizer := some "semelfactive",
    layers := some "Secondary Imperfective" }

def f_50a.analysis : Analysis :=
  { form := f_50a,
    verbalizer := some "directed motion",
    layers := some "po- in Asp1",
    reading := some "centrifugal" }

def f_50b.analysis : Analysis :=
  { form := f_50b,
    verbalizer := some "directed motion",
    layers := some "po- in Asp1",
    reading := some "centrifugal" }

def f_50c.analysis : Analysis :=
  { form := f_50c,
    verbalizer := some "directed motion",
    layers := some "po- in Asp1",
    reading := some "centrifugal" }

def f_50d.analysis : Analysis :=
  { form := f_50d,
    verbalizer := some "directed motion",
    layers := some "po- in Asp1",
    reading := some "centrifugal" }

def f_51b.analysis : Analysis :=
  { form := f_51b,
    verbalizer := some "non-directed motion",
    layers := some "po- in Asp1",
    reading := some "delimitative" }

def f_51c.analysis : Analysis :=
  { form := f_51c,
    verbalizer := some "non-directed motion",
    layers := some "po- in Asp1",
    reading := some "delimitative" }

def f_51d.analysis : Analysis :=
  { form := f_51d,
    verbalizer := some "non-directed motion",
    layers := some "po- in Asp1",
    reading := some "delimitative" }

def f_53.analysis : Analysis :=
  { form := f_53,
    verbalizer := some "low -ej-",
    reading := some "inceptive of a state, not of a becoming" }

def f_54a.analysis : Analysis :=
  { form := f_54a,
    verbalizer := some "stative",
    layers := some "po- in Asp1",
    reading := some "inceptive" }

def f_54b.analysis : Analysis :=
  { form := f_54b,
    verbalizer := some "stative",
    reading := some "inceptive" }

def fn21.analysis : Analysis :=
  { form := fn21,
    verbalizer := some "stative",
    layers := some "po- in Asp1",
    reading := some "delimitative" }

def f_56a.analysis : Analysis :=
  { form := f_56a,
    layers := some "po- in Asp1, Secondary Imperfective",
    reading := some "attenuative-frequentative" }

def f_56b.analysis : Analysis :=
  { form := f_56b,
    layers := some "po- in Asp1, Secondary Imperfective",
    reading := some "attenuative-frequentative" }

def f_56c.analysis : Analysis :=
  { form := f_56c,
    layers := some "po- in Asp1, Secondary Imperfective" }

def f_56d.analysis : Analysis :=
  { form := f_56d,
    layers := some "po- in Asp1, Secondary Imperfective",
    reading := some "attenuative-frequentative" }

def f_57a.analysis : Analysis :=
  { form := f_57a,
    verbalizer := some "-a-",
    layers := some "po- in Asp1, Secondary Imperfective",
    reading := some "attenuative-frequentative" }

def f_57b.analysis : Analysis :=
  { form := f_57b,
    verbalizer := some "-aj-",
    layers := some "po- in Asp1, Secondary Imperfective",
    reading := some "attenuative-frequentative" }

def f_57c.analysis : Analysis :=
  { form := f_57c,
    verbalizer := some "-e-",
    layers := some "po- in Asp1, Secondary Imperfective",
    reading := some "attenuative-frequentative" }

def f_57d.analysis : Analysis :=
  { form := f_57d,
    verbalizer := some "-a-",
    layers := some "po- in Asp1, Secondary Imperfective",
    reading := some "attenuative-frequentative" }

def f_58a.analysis : Analysis :=
  { form := f_58a,
    verbalizer := some "-i-",
    layers := some "po- in Asp1, Secondary Imperfective" }

def f_58b.analysis : Analysis :=
  { form := f_58b,
    verbalizer := some "-i-",
    layers := some "po- in Asp1, Secondary Imperfective" }

def f_58c.analysis : Analysis :=
  { form := f_58c,
    verbalizer := some "-aj-",
    layers := some "po- in Asp1, Secondary Imperfective" }

def f_59a.analysis : Analysis :=
  { form := f_59a,
    verbalizer := some "low -ej-",
    layers := some "po- in Asp1, Secondary Imperfective" }

def f_60_bare.analysis : Analysis :=
  { form := f_60_bare,
    layers := some "Secondary Imperfective" }

def f_61a.analysis : Analysis :=
  { form := f_61a,
    layers := some "po- in Asp1, Secondary Imperfective, po- in Asp3" }

def f_61b.analysis : Analysis :=
  { form := f_61b,
    layers := some "po- in Asp1, Secondary Imperfective, po- in Asp3" }

def f_62a.analysis : Analysis :=
  { form := f_62a,
    layers := some "lexical attenuative prefix pod-" }

def f_62b.analysis : Analysis :=
  { form := f_62b,
    layers := some "lexical prefix, Secondary Imperfective" }

def f_63b.analysis : Analysis :=
  { form := f_63b,
    verbalizer := some "semelfactive" }

def f_65a.analysis : Analysis :=
  { form := f_65a,
    reading := some "progressive of an attenuative-frequentative" }

def f_67a_pf.analysis : Analysis :=
  { form := f_67a_pf,
    layers := some "purely perfectivizing prefix in Asp2" }

def f_67a_si.analysis : Analysis :=
  { form := f_67a_si,
    layers := some "purely perfectivizing prefix, Secondary Imperfective" }

def f_67b_pf.analysis : Analysis :=
  { form := f_67b_pf,
    layers := some "purely perfectivizing prefix in Asp2" }

def f_67b_si.analysis : Analysis :=
  { form := f_67b_si,
    layers := some "purely perfectivizing prefix, Secondary Imperfective" }

def f_67c_pf.analysis : Analysis :=
  { form := f_67c_pf,
    layers := some "purely perfectivizing prefix in Asp2" }

def f_67c_si.analysis : Analysis :=
  { form := f_67c_si,
    layers := some "purely perfectivizing prefix, Secondary Imperfective" }

def f_69a_pf.analysis : Analysis :=
  { form := f_69a_pf,
    layers := some "po- as a purely perfectivizing prefix in Asp2" }

def f_69a_si.analysis : Analysis :=
  { form := f_69a_si,
    layers := some "po- as a purely perfectivizing prefix, Secondary Imperfective" }

def f_69b_pf.analysis : Analysis :=
  { form := f_69b_pf,
    layers := some "po- as a purely perfectivizing prefix in Asp2" }

def f_69b_si.analysis : Analysis :=
  { form := f_69b_si,
    layers := some "po- as a purely perfectivizing prefix, Secondary Imperfective" }

def f_69c_pf.analysis : Analysis :=
  { form := f_69c_pf,
    layers := some "po- as a purely perfectivizing prefix in Asp2" }

def f_69c_si.analysis : Analysis :=
  { form := f_69c_si,
    layers := some "po- as a purely perfectivizing prefix, Secondary Imperfective" }

def f_73a.analysis : Analysis :=
  { form := f_73a,
    verbalizer := some "low -ej-",
    layers := some "purely perfectivizing prefix, Secondary Imperfective" }

def f_74.analysis : Analysis :=
  { form := f_74,
    verbalizer := some "low -ej-",
    layers := some "po- in Asp1, Secondary Imperfective" }

def f_75a.analysis : Analysis :=
  { form := f_75a,
    verbalizer := some "low inchoative -n-",
    layers := some "lexical prefix" }

def f_75b.analysis : Analysis :=
  { form := f_75b,
    verbalizer := some "low inchoative -n-",
    layers := some "purely perfectivizing prefix" }

def f_76_a.analysis : Analysis :=
  { form := f_76_a,
    verbalizer := some "low inchoative -n-",
    layers := some "lexical prefix, Secondary Imperfective" }

def f_76_b.analysis : Analysis :=
  { form := f_76_b,
    verbalizer := some "low inchoative -n-",
    layers := some "lexical prefix, Secondary Imperfective" }

def f_77.analysis : Analysis :=
  { form := f_77 }

def f_78.analysis : Analysis :=
  { form := f_78,
    layers := some "purely perfectivizing prefix, Secondary Imperfective" }

def f_79a.analysis : Analysis :=
  { form := f_79a,
    verbalizer := some "semelfactive",
    layers := some "lexical prefix" }

def f_79b.analysis : Analysis :=
  { form := f_79b,
    verbalizer := some "semelfactive",
    layers := some "lexical prefix, Secondary Imperfective" }

def f_79c.analysis : Analysis :=
  { form := f_79c,
    verbalizer := some "-a-" }

def f_79d.analysis : Analysis :=
  { form := f_79d }

def f_80b.analysis : Analysis :=
  { form := f_80b }

def f_81a.analysis : Analysis :=
  { form := f_81a,
    verbalizer := some "high -i-",
    layers := some "lexical po-" }

def f_81b.analysis : Analysis :=
  { form := f_81b,
    verbalizer := some "high -i-",
    layers := some "lexical po-" }

def f_81c.analysis : Analysis :=
  { form := f_81c,
    verbalizer := some "high -aj-",
    layers := some "lexical po-" }

def f_81d.analysis : Analysis :=
  { form := f_81d,
    verbalizer := some "-C-",
    layers := some "lexical po-" }

def f_81e.analysis : Analysis :=
  { form := f_81e,
    verbalizer := some "-C- or inchoative",
    layers := some "lexical po-" }

def f_81f.analysis : Analysis :=
  { form := f_81f,
    verbalizer := some "low -ej-",
    layers := some "lexical po-" }

def f_82a.analysis : Analysis :=
  { form := f_82a,
    layers := some "lexical po-, Secondary Imperfective" }

def f_82b.analysis : Analysis :=
  { form := f_82b,
    layers := some "lexical po-, Secondary Imperfective" }

def f_82c.analysis : Analysis :=
  { form := f_82c,
    layers := some "lexical po-, Secondary Imperfective" }

def f_82d.analysis : Analysis :=
  { form := f_82d,
    layers := some "lexical po-, Secondary Imperfective" }

def f_83a.analysis : Analysis :=
  { form := f_83a,
    layers := some "lexical po-, Secondary Imperfective, po- in Asp3",
    reading := some "distributive" }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.posiwiec, Lexemes.pojasniec, Lexemes.poczerwieniec,
  Lexemes.posmutniec, Lexemes.drozec, Lexemes.zieleniec, Lexemes.pociemniec, Lexemes.zciemniec,
  Lexemes.podrozec, Lexemes.zdrozec, Lexemes.postarzec_sie, Lexemes.zestarzec_sie,
  Lexemes.pobabieli, Lexemes.poprzeczytywalem, Lexemes.poprzeczytalem, Lexemes.poczytac,
  Lexemes.pograc, Lexemes.pochodzic, Lexemes.popalic, Lexemes.pochowala, Lexemes.poprzepisywala,
  Lexemes.pospiewali, Lexemes.powchodzili, Lexemes.przepisac, Lexemes.robiac, Lexemes.gwizdywac,
  Lexemes.poprzepisywac, Lexemes.pomarznac, Lexemes.pogluchnac, Lexemes.powiednac,
  Lexemes.poslepnac, Lexemes.postracic, Lexemes.poobkopac, Lexemes.powyrzucic, Lexemes.poobkopywac,
  Lexemes.powyrzucac, Lexemes.powarknac, Lexemes.pokopnac, Lexemes.pomachnac, Lexemes.machniesz,
  Lexemes.powarknywac, Lexemes.pojsc, Lexemes.pobiec, Lexemes.poleciec, Lexemes.pociagnac,
  Lexemes.pobiegac, Lexemes.polatac, Lexemes.pociagac, Lexemes.zajasniec, Lexemes.pokochac,
  Lexemes.polubic, Lexemes.posiedziec, Lexemes.poczytywac, Lexemes.pogrywac, Lexemes.pochadzac,
  Lexemes.popalac, Lexemes.poplakiwac, Lexemes.pokaslywac, Lexemes.pomiaukiwac, Lexemes.pogwizdywac,
  Lexemes.pokroczac, Lexemes.potanczac, Lexemes.pokochiwac, Lexemes.grywac, Lexemes.popogrywac,
  Lexemes.popopalac, Lexemes.podjesc, Lexemes.pomiauknac, Lexemes.podmuchiwala, Lexemes.stracic,
  Lexemes.zrobic, Lexemes.schowac, Lexemes.pobrudzic, Lexemes.pobic, Lexemes.pochwalic,
  Lexemes.zdziczac, Lexemes.wygasnac, Lexemes.zgasnac, Lexemes.podszepnac, Lexemes.szeptac,
  Lexemes.doplywa, Lexemes.ponizyc, Lexemes.pocieszyc, Lexemes.porownac, Lexemes.pozwac,
  Lexemes.polec, Lexemes.pogrzybiec, Lexemes.poporownywalismy]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [f_3a, f_3b, f_3c, f_3d, f_8a, f_9a, f_10a_po, f_10a_z, f_10b_po,
  f_10b_z, f_10c_po, f_10c_z, f_23a, f_24a, f_27a, f_27b, f_27c, f_27d, f_28a, f_28b, f_28c, f_28d,
  f_30, f_31a, f_34a, f_39a, f_39b, f_39c, f_39d, f_43a, f_43b, f_46b, f_50a, f_50b, f_50c, f_50d,
  f_51b, f_51c, f_51d, f_53, f_54a, f_54b, fn21, f_56b, f_56d, f_57a, f_57b, f_57c, f_57d,
  f_60_bare, f_62a, f_62b, f_65a, f_67a_pf, f_67b_pf, f_67c_pf, f_69a_pf, f_69b_pf, f_69c_pf, f_75a,
  f_75b, f_77, f_79a, f_79c, f_79d, f_80b, f_81a, f_81b, f_81c, f_81d, f_81e, f_82a, f_82b, f_82c,
  f_82d, f_83a]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := [f_24b, f_32a, f_32b, f_42a, f_42b, f_42c, f_45a, f_45b, f_45c,
  f_48, f_56a, f_56c, f_58a, f_58b, f_58c, f_59a, f_61a, f_61b, f_63b, f_67a_si, f_67b_si, f_67c_si,
  f_69a_si, f_69b_si, f_69c_si, f_73a, f_74, f_76_a, f_76_b, f_78, f_79b, f_81f]

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := [
  { id := "jablonska2004_r_31a_imperfective", form := f_30, target := f_31a,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(31a)"⟩
    ] },
  { id := "jablonska2004_r_59a_imperfective", form := f_3a, target := f_59a,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(59a)"⟩
    ] },
  { id := "jablonska2004_r_62b_imperfective", form := f_62a, target := f_62b,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(62b)"⟩
    ] },
  { id := "jablonska2004_r_67a_si_imperfective", form := f_67a_pf, target := f_67a_si,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(67a)"⟩
    ] },
  { id := "jablonska2004_r_67b_si_imperfective", form := f_67b_pf, target := f_67b_si,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(67b)"⟩
    ] },
  { id := "jablonska2004_r_67c_si_imperfective", form := f_67c_pf, target := f_67c_si,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(67c)"⟩
    ] },
  { id := "jablonska2004_r_69a_si_imperfective", form := f_69a_pf, target := f_69a_si,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(69a)"⟩
    ] },
  { id := "jablonska2004_r_69b_si_imperfective", form := f_69b_pf, target := f_69b_si,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(69b)"⟩
    ] },
  { id := "jablonska2004_r_69c_si_imperfective", form := f_69c_pf, target := f_69c_si,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(69c)"⟩
    ] },
  { id := "jablonska2004_r_74_imperfective", form := f_3a, target := f_74,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(74)"⟩
    ] },
  { id := "jablonska2004_r_76_a_imperfective", form := f_75a, target := f_76_a,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(76)"⟩
    ] },
  { id := "jablonska2004_r_76_b_imperfective", form := f_75a, target := f_76_b,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(76)"⟩
    ] },
  { id := "jablonska2004_r_77_imperfective", form := f_75a, target := f_77,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(77)"⟩
    ] },
  { id := "jablonska2004_r_78_imperfective", form := f_75b, target := f_78,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(78)"⟩
    ] },
  { id := "jablonska2004_r_79b_imperfective", form := f_79a, target := f_79b,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(79b)"⟩
    ] },
  { id := "jablonska2004_r_79d_imperfective", form := f_79a, target := f_79d,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(79d)"⟩
    ] },
  { id := "jablonska2004_r_82a_imperfective", form := f_81a, target := f_82a,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(82a)"⟩
    ] },
  { id := "jablonska2004_r_82b_imperfective", form := f_81b, target := f_82b,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(82b)"⟩
    ] },
  { id := "jablonska2004_r_82c_imperfective", form := f_81c, target := f_82c,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(82c)"⟩
    ] },
  { id := "jablonska2004_r_82d_imperfective", form := f_81d, target := f_82d,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(82d)"⟩
    ] }]

/-- Every relation the sources assert, between the forms' analyses. -/
def analysisRelations : List (FormRelation Analysis) := [
  { id := "jablonska2004_r_31a_imperfective", form := f_30.analysis, target := f_31a.analysis,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(31a)"⟩
    ] },
  { id := "jablonska2004_r_59a_imperfective", form := f_3a.analysis, target := f_59a.analysis,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(59a)"⟩
    ] },
  { id := "jablonska2004_r_62b_imperfective", form := f_62a.analysis, target := f_62b.analysis,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(62b)"⟩
    ] },
  { id := "jablonska2004_r_67a_si_imperfective", form := f_67a_pf.analysis,
    target := f_67a_si.analysis, relation := "imperfective", source := [
      ⟨"jablonska-2004", "(67a)"⟩
    ] },
  { id := "jablonska2004_r_67b_si_imperfective", form := f_67b_pf.analysis,
    target := f_67b_si.analysis, relation := "imperfective", source := [
      ⟨"jablonska-2004", "(67b)"⟩
    ] },
  { id := "jablonska2004_r_67c_si_imperfective", form := f_67c_pf.analysis,
    target := f_67c_si.analysis, relation := "imperfective", source := [
      ⟨"jablonska-2004", "(67c)"⟩
    ] },
  { id := "jablonska2004_r_69a_si_imperfective", form := f_69a_pf.analysis,
    target := f_69a_si.analysis, relation := "imperfective", source := [
      ⟨"jablonska-2004", "(69a)"⟩
    ] },
  { id := "jablonska2004_r_69b_si_imperfective", form := f_69b_pf.analysis,
    target := f_69b_si.analysis, relation := "imperfective", source := [
      ⟨"jablonska-2004", "(69b)"⟩
    ] },
  { id := "jablonska2004_r_69c_si_imperfective", form := f_69c_pf.analysis,
    target := f_69c_si.analysis, relation := "imperfective", source := [
      ⟨"jablonska-2004", "(69c)"⟩
    ] },
  { id := "jablonska2004_r_74_imperfective", form := f_3a.analysis, target := f_74.analysis,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(74)"⟩
    ] },
  { id := "jablonska2004_r_76_a_imperfective", form := f_75a.analysis, target := f_76_a.analysis,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(76)"⟩
    ] },
  { id := "jablonska2004_r_76_b_imperfective", form := f_75a.analysis, target := f_76_b.analysis,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(76)"⟩
    ] },
  { id := "jablonska2004_r_77_imperfective", form := f_75a.analysis, target := f_77.analysis,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(77)"⟩
    ] },
  { id := "jablonska2004_r_78_imperfective", form := f_75b.analysis, target := f_78.analysis,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(78)"⟩
    ] },
  { id := "jablonska2004_r_79b_imperfective", form := f_79a.analysis, target := f_79b.analysis,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(79b)"⟩
    ] },
  { id := "jablonska2004_r_79d_imperfective", form := f_79a.analysis, target := f_79d.analysis,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(79d)"⟩
    ] },
  { id := "jablonska2004_r_82a_imperfective", form := f_81a.analysis, target := f_82a.analysis,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(82a)"⟩
    ] },
  { id := "jablonska2004_r_82b_imperfective", form := f_81b.analysis, target := f_82b.analysis,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(82b)"⟩
    ] },
  { id := "jablonska2004_r_82c_imperfective", form := f_81c.analysis, target := f_82c.analysis,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(82c)"⟩
    ] },
  { id := "jablonska2004_r_82d_imperfective", form := f_81d.analysis, target := f_82d.analysis,
    relation := "imperfective", source := [
      ⟨"jablonska-2004", "(82d)"⟩
    ] }]

/-- Every analysis of the data. -/
def analyses : List Analysis := [f_3a.analysis, f_3b.analysis, f_3c.analysis, f_3d.analysis,
  f_8a.analysis, f_9a.analysis, f_10a_po.analysis, f_10a_z.analysis, f_10b_po.analysis,
  f_10b_z.analysis, f_10c_po.analysis, f_10c_z.analysis, f_23a.analysis, f_24a.analysis,
  f_24b.analysis, f_27a.analysis, f_27b.analysis, f_27c.analysis, f_27d.analysis, f_28a.analysis,
  f_28b.analysis, f_28c.analysis, f_28d.analysis, f_30.analysis, f_31a.analysis, f_32a.analysis,
  f_32b.analysis, f_34a.analysis, f_39a.analysis, f_39b.analysis, f_39c.analysis, f_39d.analysis,
  f_42a.analysis, f_42b.analysis, f_42c.analysis, f_43a.analysis, f_43b.analysis, f_45a.analysis,
  f_45b.analysis, f_45c.analysis, f_48.analysis, f_50a.analysis, f_50b.analysis, f_50c.analysis,
  f_50d.analysis, f_51b.analysis, f_51c.analysis, f_51d.analysis, f_53.analysis, f_54a.analysis,
  f_54b.analysis, fn21.analysis, f_56a.analysis, f_56b.analysis, f_56c.analysis, f_56d.analysis,
  f_57a.analysis, f_57b.analysis, f_57c.analysis, f_57d.analysis, f_58a.analysis, f_58b.analysis,
  f_58c.analysis, f_59a.analysis, f_60_bare.analysis, f_61a.analysis, f_61b.analysis,
  f_62a.analysis, f_62b.analysis, f_63b.analysis, f_65a.analysis, f_67a_pf.analysis,
  f_67a_si.analysis, f_67b_pf.analysis, f_67b_si.analysis, f_67c_pf.analysis, f_67c_si.analysis,
  f_69a_pf.analysis, f_69a_si.analysis, f_69b_pf.analysis, f_69b_si.analysis, f_69c_pf.analysis,
  f_69c_si.analysis, f_73a.analysis, f_74.analysis, f_75a.analysis, f_75b.analysis, f_76_a.analysis,
  f_76_b.analysis, f_78.analysis, f_79a.analysis, f_79b.analysis, f_79c.analysis, f_81a.analysis,
  f_81b.analysis, f_81c.analysis, f_81d.analysis, f_81e.analysis, f_81f.analysis, f_82a.analysis,
  f_82b.analysis, f_82c.analysis, f_82d.analysis, f_83a.analysis]

end Jablonska2004.Forms
