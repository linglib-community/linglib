module

public import Linglib.Data.Wordlist.Schema

/-!
# `AksenovaEtAl2024`: word forms

Auto-generated from `Linglib/Data/Wordlist/AksenovaEtAl2024.json` by `scripts/gen_wordlist.py`. Do
not edit by hand; edit the JSON and re-run the generator. Declarations live in `namespace
AksenovaEtAl2024.Wordlist`.
-/

@[expose] public section

namespace AksenovaEtAl2024.Wordlist

open CLDF.Wordlist

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

def Lexemes.smoke : Lexeme :=
  { id := "smoke", languageId := "loka1252", parameterId := "smoke" }

def Lexemes.housefly : Lexeme :=
  { id := "housefly", languageId := "loka1252", parameterId := "housefly" }

def Lexemes.matriclan : Lexeme :=
  { id := "matriclan", languageId := "loka1252", parameterId := "matriclan" }

def Lexemes.kind_of_plant : Lexeme :=
  { id := "kind_of_plant", languageId := "loka1252", parameterId := "kind_of_plant" }

def Lexemes.fire_loc : Lexeme :=
  { id := "fire_loc", languageId := "kirg1245", parameterId := "fire_loc" }

def Lexemes.who_loc : Lexeme :=
  { id := "who_loc", languageId := "kirg1245", parameterId := "who_loc" }

def Lexemes.house_loc : Lexeme :=
  { id := "house_loc", languageId := "kirg1245", parameterId := "house_loc" }

def Lexemes.fire_gen : Lexeme :=
  { id := "fire_gen", languageId := "kirg1245", parameterId := "fire_gen" }

def Lexemes.who_gen : Lexeme :=
  { id := "who_gen", languageId := "kirg1245", parameterId := "who_gen" }

def Lexemes.house_gen : Lexeme :=
  { id := "house_gen", languageId := "kirg1245", parameterId := "house_gen" }

def Lexemes.enter_perf : Lexeme :=
  { id := "enter_perf", languageId := "russ1264", parameterId := "enter_perf" }

def Lexemes.enter_caus_perf : Lexeme :=
  { id := "enter_caus_perf", languageId := "russ1264", parameterId := "enter_caus_perf" }

def Lexemes.wander_perf : Lexeme :=
  { id := "wander_perf", languageId := "russ1264", parameterId := "wander_perf" }

def Lexemes.wander_caus_perf : Lexeme :=
  { id := "wander_caus_perf", languageId := "russ1264", parameterId := "wander_caus_perf" }

def Lexemes.horse_poss : Lexeme :=
  { id := "horse_poss", languageId := "russ1264", parameterId := "horse_poss" }

def Lexemes.group_poss : Lexeme :=
  { id := "group_poss", languageId := "russ1264", parameterId := "group_poss" }

def Lexemes.child_pl : Lexeme :=
  { id := "child_pl", languageId := "yaku1245", parameterId := "child_pl" }

def Lexemes.wolf_pl : Lexeme :=
  { id := "wolf_pl", languageId := "yaku1245", parameterId := "wolf_pl" }

def Lexemes.child_acc : Lexeme :=
  { id := "child_acc", languageId := "yaku1245", parameterId := "child_acc" }

def Lexemes.wolf_acc : Lexeme :=
  { id := "wolf_acc", languageId := "yaku1245", parameterId := "wolf_acc" }

def Lexemes.nose_acc : Lexeme :=
  { id := "nose_acc", languageId := "yaku1245", parameterId := "nose_acc" }

def Lexemes.window_acc : Lexeme :=
  { id := "window_acc", languageId := "yaku1245", parameterId := "window_acc" }

def Lexemes.shaman_pl : Lexeme :=
  { id := "shaman_pl", languageId := "yaku1245", parameterId := "shaman_pl" }

def Lexemes.window_pl : Lexeme :=
  { id := "window_pl", languageId := "yaku1245", parameterId := "window_pl" }

def Lexemes.attach_appl : Lexeme :=
  { id := "attach_appl", languageId := "koon1247", parameterId := "attach_appl" }

def Lexemes.languish_appl : Lexeme :=
  { id := "languish_appl", languageId := "koon1247", parameterId := "languish_appl" }

def Lexemes.support_appl : Lexeme :=
  { id := "support_appl", languageId := "koon1247", parameterId := "support_appl" }

def Lexemes.surpass_appl : Lexeme :=
  { id := "surpass_appl", languageId := "koon1247", parameterId := "surpass_appl" }

def Lexemes.do_trans : Lexeme :=
  { id := "do_trans", languageId := "koon1247", parameterId := "do_trans" }

def Lexemes.broom_trans : Lexeme :=
  { id := "broom_trans", languageId := "koon1247", parameterId := "broom_trans" }

def Lexemes.move_trans : Lexeme :=
  { id := "move_trans", languageId := "koon1247", parameterId := "move_trans" }

def Lexemes.bribe_trans : Lexeme :=
  { id := "bribe_trans", languageId := "koon1247", parameterId := "bribe_trans" }

def Lexemes.wash_perf_act : Lexeme :=
  { id := "wash_perf_act", languageId := "koon1247", parameterId := "wash_perf_act" }

def Lexemes.ground_perf_act : Lexeme :=
  { id := "ground_perf_act", languageId := "koon1247", parameterId := "ground_perf_act" }

def Lexemes.hate_perf_act : Lexeme :=
  { id := "hate_perf_act", languageId := "koon1247", parameterId := "hate_perf_act" }

def Lexemes.wash_perf_pass : Lexeme :=
  { id := "wash_perf_pass", languageId := "koon1247", parameterId := "wash_perf_pass" }

def Lexemes.ground_perf_pass : Lexeme :=
  { id := "ground_perf_pass", languageId := "koon1247", parameterId := "ground_perf_pass" }

def Lexemes.hate_perf_pass : Lexeme :=
  { id := "hate_perf_pass", languageId := "koon1247", parameterId := "hate_perf_pass" }

def f_3a : Form Cell :=
  { id := "aksenovaetal2024_3a"
    lexeme := Lexemes.smoke
    cell := {}
    form := "èsìsòn"
    segments := ["è", "s", "ì", "s", "ò", "n"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(3a)"⟩,
      ⟨"aksenova-rawski-graf-heinz-2024", "Figure 34.1"⟩
    ] }

def f_3b : Form Cell :=
  { id := "aksenovaetal2024_3b"
    lexeme := Lexemes.housefly
    cell := {}
    form := "ɛ̀sísɔ̀n"
    segments := ["ɛ̀", "s", "í", "s", "ɔ̀", "n"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(3b)"⟩
    ] }

def f_3c : Form Cell :=
  { id := "aksenovaetal2024_3c"
    lexeme := Lexemes.matriclan
    cell := {}
    form := "lèjìmə̀"
    segments := ["l", "è", "j", "ì", "m", "ə̀"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(3c)"⟩
    ] }

def f_3d : Form Cell :=
  { id := "aksenovaetal2024_3d"
    lexeme := Lexemes.kind_of_plant
    cell := {}
    form := "ɛ́kílìkà"
    segments := ["ɛ́", "k", "í", "l", "ì", "k", "à"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(3d)"⟩
    ] }

def f_5a : Form Cell :=
  { id := "aksenovaetal2024_5a"
    lexeme := Lexemes.fire_loc
    cell := {}
    form := "ot-to"
    segments := ["o", "t", "t", "o"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(5a)"⟩
    ] }

def f_5b : Form Cell :=
  { id := "aksenovaetal2024_5b"
    lexeme := Lexemes.who_loc
    cell := {}
    form := "kim-de"
    segments := ["k", "i", "m", "d", "e"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(5b)"⟩
    ] }

def f_5c : Form Cell :=
  { id := "aksenovaetal2024_5c"
    lexeme := Lexemes.house_loc
    cell := {}
    form := "üj-dö"
    segments := ["ü", "j", "d", "ö"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(5c)"⟩,
      ⟨"aksenova-rawski-graf-heinz-2024", "Figure 34.3"⟩
    ] }

def f_5d : Form Cell :=
  { id := "aksenovaetal2024_5d"
    lexeme := Lexemes.fire_gen
    cell := {}
    form := "ot-tun"
    segments := ["o", "t", "t", "u", "n"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(5d)"⟩
    ] }

def f_5e : Form Cell :=
  { id := "aksenovaetal2024_5e"
    lexeme := Lexemes.who_gen
    cell := {}
    form := "kim-din"
    segments := ["k", "i", "m", "d", "i", "n"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(5e)"⟩
    ] }

def f_5f : Form Cell :=
  { id := "aksenovaetal2024_5f"
    lexeme := Lexemes.house_gen
    cell := {}
    form := "üj-dün"
    segments := ["ü", "j", "d", "ü", "n"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(5f)"⟩
    ] }

def f_9a : Form Cell :=
  { id := "aksenovaetal2024_9a"
    lexeme := Lexemes.enter_perf
    cell := {}
    form := "ɔr-ɔːd"
    segments := ["ɔ", "r", "ɔː", "d"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(9a)"⟩
    ] }

def f_9b : Form Cell :=
  { id := "aksenovaetal2024_9b"
    lexeme := Lexemes.enter_caus_perf
    cell := {}
    form := "ɔr-ʊːl-aːd"
    segments := ["ɔ", "r", "ʊː", "l", "aː", "d"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(9b)"⟩
    ] }

def f_9c : Form Cell :=
  { id := "aksenovaetal2024_9c"
    lexeme := Lexemes.wander_perf
    cell := {}
    form := "toːr-oːd"
    segments := ["t", "oː", "r", "oː", "d"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(9c)"⟩,
      ⟨"aksenova-rawski-graf-heinz-2024", "Figure 34.4"⟩
    ] }

def f_9d : Form Cell :=
  { id := "aksenovaetal2024_9d"
    lexeme := Lexemes.wander_caus_perf
    cell := {}
    form := "toːr-uːl-eːd"
    segments := ["t", "oː", "r", "uː", "l", "eː", "d"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(9d)"⟩,
      ⟨"aksenova-rawski-graf-heinz-2024", "Figure 34.4"⟩
    ] }

def f_9e : Form Cell :=
  { id := "aksenovaetal2024_9e"
    lexeme := Lexemes.horse_poss
    cell := {}
    form := "mɔrin-ɔː"
    segments := ["m", "ɔ", "r", "i", "n", "ɔː"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(9e)"⟩
    ] }

def f_9f : Form Cell :=
  { id := "aksenovaetal2024_9f"
    lexeme := Lexemes.group_poss
    cell := {}
    form := "oːrin-goː"
    segments := ["oː", "r", "i", "n", "g", "oː"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(9f)"⟩
    ] }

def f_14a : Form Cell :=
  { id := "aksenovaetal2024_14a"
    lexeme := Lexemes.child_pl
    cell := {}
    form := "oɣo-lor"
    segments := ["o", "ɣ", "o", "l", "o", "r"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(14a)"⟩
    ] }

def f_14b : Form Cell :=
  { id := "aksenovaetal2024_14b"
    lexeme := Lexemes.wolf_pl
    cell := {}
    form := "börö-lör"
    segments := ["b", "ö", "r", "ö", "l", "ö", "r"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(14b)"⟩
    ] }

def f_14c : Form Cell :=
  { id := "aksenovaetal2024_14c"
    lexeme := Lexemes.child_acc
    cell := {}
    form := "oɣo-nu"
    segments := ["o", "ɣ", "o", "n", "u"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(14c)"⟩
    ] }

def f_14d : Form Cell :=
  { id := "aksenovaetal2024_14d"
    lexeme := Lexemes.wolf_acc
    cell := {}
    form := "börö-nü"
    segments := ["b", "ö", "r", "ö", "n", "ü"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(14d)"⟩
    ] }

def f_14e : Form Cell :=
  { id := "aksenovaetal2024_14e"
    lexeme := Lexemes.nose_acc
    cell := {}
    form := "murum-u"
    segments := ["m", "u", "r", "u", "m", "u"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(14e)"⟩,
      ⟨"aksenova-rawski-graf-heinz-2024", "Figure 34.5"⟩
    ] }

def f_14f : Form Cell :=
  { id := "aksenovaetal2024_14f"
    lexeme := Lexemes.window_acc
    cell := {}
    form := "tünnük-ü"
    segments := ["t", "ü", "n", "n", "ü", "k", "ü"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(14f)"⟩
    ] }

def f_14g : Form Cell :=
  { id := "aksenovaetal2024_14g"
    lexeme := Lexemes.shaman_pl
    cell := {}
    form := "ojum-lar"
    segments := ["o", "j", "u", "m", "l", "a", "r"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(14g)"⟩,
      ⟨"aksenova-rawski-graf-heinz-2024", "Figure 34.5"⟩
    ] }

def f_14h : Form Cell :=
  { id := "aksenovaetal2024_14h"
    lexeme := Lexemes.window_pl
    cell := {}
    form := "tünnük-ler"
    segments := ["t", "ü", "n", "n", "ü", "k", "l", "e", "r"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(14h)"⟩
    ] }

def f_16a : Form Cell :=
  { id := "aksenovaetal2024_16a"
    lexeme := Lexemes.attach_appl
    cell := {}
    form := "-somp-el-"
    segments := ["s", "o", "mp", "e", "l"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(16a)"⟩
    ] }

def f_16b : Form Cell :=
  { id := "aksenovaetal2024_16b"
    lexeme := Lexemes.languish_appl
    cell := {}
    form := "-leng-el-"
    segments := ["l", "e", "ng", "e", "l"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(16b)"⟩
    ] }

def f_16c : Form Cell :=
  { id := "aksenovaetal2024_16c"
    lexeme := Lexemes.support_appl
    cell := {}
    form := "-sik-il-"
    segments := ["s", "i", "k", "i", "l"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(16c)"⟩
    ] }

def f_16d : Form Cell :=
  { id := "aksenovaetal2024_16d"
    lexeme := Lexemes.surpass_appl
    cell := {}
    form := "-vur-il-"
    segments := ["v", "u", "r", "i", "l"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(16d)"⟩
    ] }

def f_16e : Form Cell :=
  { id := "aksenovaetal2024_16e"
    lexeme := Lexemes.do_trans
    cell := {}
    form := "-tomb-ol-"
    segments := ["t", "o", "mb", "o", "l"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(16e)"⟩
    ] }

def f_16f : Form Cell :=
  { id := "aksenovaetal2024_16f"
    lexeme := Lexemes.broom_trans
    cell := {}
    form := "-lemb-ol-"
    segments := ["l", "e", "mb", "o", "l"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(16f)"⟩
    ] }

def f_16g : Form Cell :=
  { id := "aksenovaetal2024_16g"
    lexeme := Lexemes.move_trans
    cell := {}
    form := "-vil-ul-"
    segments := ["v", "i", "l", "u", "l"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(16g)"⟩
    ] }

def f_16h : Form Cell :=
  { id := "aksenovaetal2024_16h"
    lexeme := Lexemes.bribe_trans
    cell := {}
    form := "-bub-ul-"
    segments := ["b", "u", "b", "u", "l"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(16h)"⟩
    ] }

def f_18a : Form Cell :=
  { id := "aksenovaetal2024_18a"
    lexeme := Lexemes.wash_perf_act
    cell := {}
    form := "-suk-idi-"
    segments := ["s", "u", "k", "i", "d", "i"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(18a)"⟩
    ] }

def f_18b : Form Cell :=
  { id := "aksenovaetal2024_18b"
    lexeme := Lexemes.ground_perf_act
    cell := {}
    form := "-nik-ini-"
    segments := ["n", "i", "k", "i", "n", "i"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(18b)"⟩
    ] }

def f_18c : Form Cell :=
  { id := "aksenovaetal2024_18c"
    lexeme := Lexemes.hate_perf_act
    cell := {}
    form := "-meng-ene-"
    segments := ["m", "e", "ng", "e", "n", "e"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(18c)"⟩
    ] }

def f_18d : Form Cell :=
  { id := "aksenovaetal2024_18d"
    lexeme := Lexemes.wash_perf_pass
    cell := {}
    form := "-suk-ulu-"
    segments := ["s", "u", "k", "u", "l", "u"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(18d)"⟩
    ] }

def f_18e : Form Cell :=
  { id := "aksenovaetal2024_18e"
    lexeme := Lexemes.ground_perf_pass
    cell := {}
    form := "-nik-unu-"
    segments := ["n", "i", "k", "u", "n", "u"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(18e)"⟩,
      ⟨"aksenova-rawski-graf-heinz-2024", "Figure 34.6"⟩
    ] }

def f_18f : Form Cell :=
  { id := "aksenovaetal2024_18f"
    lexeme := Lexemes.hate_perf_pass
    cell := {}
    form := "-meng-ono-"
    segments := ["m", "e", "ng", "o", "n", "o"]
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(18f)"⟩
    ] }

def f_3a_ill : Form Cell :=
  { id := "aksenovaetal2024_3a_ill"
    lexeme := Lexemes.smoke
    cell := {}
    form := "èsìsɔ̀n"
    judgment := .ungrammatical
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(3a)"⟩,
      ⟨"aksenova-rawski-graf-heinz-2024", "Figure 34.1"⟩
    ] }

def f_3b_ill : Form Cell :=
  { id := "aksenovaetal2024_3b_ill"
    lexeme := Lexemes.housefly
    cell := {}
    form := "ɛ̀sísòn"
    judgment := .ungrammatical
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(3b)"⟩
    ] }

def f_3c_ill : Form Cell :=
  { id := "aksenovaetal2024_3c_ill"
    lexeme := Lexemes.matriclan
    cell := {}
    form := "lèjìmà"
    judgment := .ungrammatical
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(3c)"⟩
    ] }

def f_3d_ill : Form Cell :=
  { id := "aksenovaetal2024_3d_ill"
    lexeme := Lexemes.kind_of_plant
    cell := {}
    form := "ékílìkà"
    judgment := .ungrammatical
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(3d)"⟩
    ] }

def f_5c_ill1 : Form Cell :=
  { id := "aksenovaetal2024_5c_ill1"
    lexeme := Lexemes.house_loc
    cell := {}
    form := "üjde"
    judgment := .ungrammatical
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(5c)"⟩,
      ⟨"aksenova-rawski-graf-heinz-2024", "Figure 34.3"⟩
    ] }

def f_5c_ill2 : Form Cell :=
  { id := "aksenovaetal2024_5c_ill2"
    lexeme := Lexemes.house_loc
    cell := {}
    form := "üjdo"
    judgment := .ungrammatical
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(5c)"⟩,
      ⟨"aksenova-rawski-graf-heinz-2024", "Figure 34.3"⟩
    ] }

def f_9a_ill : Form Cell :=
  { id := "aksenovaetal2024_9a_ill"
    lexeme := Lexemes.enter_perf
    cell := {}
    form := "ɔr-aːd"
    judgment := .ungrammatical
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(9a)"⟩
    ] }

def f_9b_ill : Form Cell :=
  { id := "aksenovaetal2024_9b_ill"
    lexeme := Lexemes.enter_caus_perf
    cell := {}
    form := "ɔr-ʊːl-ɔːd"
    judgment := .ungrammatical
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(9b)"⟩
    ] }

def f_9c_ill : Form Cell :=
  { id := "aksenovaetal2024_9c_ill"
    lexeme := Lexemes.wander_perf
    cell := {}
    form := "toːr-eːd"
    judgment := .ungrammatical
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(9c)"⟩,
      ⟨"aksenova-rawski-graf-heinz-2024", "Figure 34.4"⟩
    ] }

def f_9d_ill : Form Cell :=
  { id := "aksenovaetal2024_9d_ill"
    lexeme := Lexemes.wander_caus_perf
    cell := {}
    form := "toːr-uːl-oːd"
    judgment := .ungrammatical
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(9d)"⟩,
      ⟨"aksenova-rawski-graf-heinz-2024", "Figure 34.4"⟩
    ] }

def f_9e_ill : Form Cell :=
  { id := "aksenovaetal2024_9e_ill"
    lexeme := Lexemes.horse_poss
    cell := {}
    form := "mɔrin-aː"
    judgment := .ungrammatical
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(9e)"⟩
    ] }

def f_9f_ill : Form Cell :=
  { id := "aksenovaetal2024_9f_ill"
    lexeme := Lexemes.group_poss
    cell := {}
    form := "oːrin-geː"
    judgment := .ungrammatical
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(9f)"⟩
    ] }

def f_14a_ill : Form Cell :=
  { id := "aksenovaetal2024_14a_ill"
    lexeme := Lexemes.child_pl
    cell := {}
    form := "oɣo-lar"
    judgment := .ungrammatical
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(14a)"⟩
    ] }

def f_14b_ill : Form Cell :=
  { id := "aksenovaetal2024_14b_ill"
    lexeme := Lexemes.wolf_pl
    cell := {}
    form := "börö-ler"
    judgment := .ungrammatical
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(14b)"⟩
    ] }

def f_14c_ill : Form Cell :=
  { id := "aksenovaetal2024_14c_ill"
    lexeme := Lexemes.child_acc
    cell := {}
    form := "oɣo-nɨ"
    judgment := .ungrammatical
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(14c)"⟩
    ] }

def f_14d_ill : Form Cell :=
  { id := "aksenovaetal2024_14d_ill"
    lexeme := Lexemes.wolf_acc
    cell := {}
    form := "börö-ni"
    judgment := .ungrammatical
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(14d)"⟩
    ] }

def f_14e_ill : Form Cell :=
  { id := "aksenovaetal2024_14e_ill"
    lexeme := Lexemes.nose_acc
    cell := {}
    form := "murum-ɨ"
    judgment := .ungrammatical
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(14e)"⟩,
      ⟨"aksenova-rawski-graf-heinz-2024", "Figure 34.5"⟩
    ] }

def f_14f_ill : Form Cell :=
  { id := "aksenovaetal2024_14f_ill"
    lexeme := Lexemes.window_acc
    cell := {}
    form := "tünnük-i"
    judgment := .ungrammatical
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(14f)"⟩
    ] }

def f_14g_ill : Form Cell :=
  { id := "aksenovaetal2024_14g_ill"
    lexeme := Lexemes.shaman_pl
    cell := {}
    form := "ojum-lor"
    judgment := .ungrammatical
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(14g)"⟩,
      ⟨"aksenova-rawski-graf-heinz-2024", "Figure 34.5"⟩
    ] }

def f_14h_ill : Form Cell :=
  { id := "aksenovaetal2024_14h_ill"
    lexeme := Lexemes.window_pl
    cell := {}
    form := "tünnük-lör"
    judgment := .ungrammatical
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(14h)"⟩
    ] }

def f_18e_ill1 : Form Cell :=
  { id := "aksenovaetal2024_18e_ill1"
    lexeme := Lexemes.ground_perf_pass
    cell := {}
    form := "nikono"
    judgment := .ungrammatical
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(18e)"⟩,
      ⟨"aksenova-rawski-graf-heinz-2024", "Figure 34.6"⟩
    ] }

def f_18e_ill2 : Form Cell :=
  { id := "aksenovaetal2024_18e_ill2"
    lexeme := Lexemes.ground_perf_pass
    cell := {}
    form := "nikulo"
    judgment := .ungrammatical
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(18e)"⟩,
      ⟨"aksenova-rawski-graf-heinz-2024", "Figure 34.6"⟩
    ] }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.smoke, Lexemes.housefly, Lexemes.matriclan,
  Lexemes.kind_of_plant, Lexemes.fire_loc, Lexemes.who_loc, Lexemes.house_loc, Lexemes.fire_gen,
  Lexemes.who_gen, Lexemes.house_gen, Lexemes.enter_perf, Lexemes.enter_caus_perf,
  Lexemes.wander_perf, Lexemes.wander_caus_perf, Lexemes.horse_poss, Lexemes.group_poss,
  Lexemes.child_pl, Lexemes.wolf_pl, Lexemes.child_acc, Lexemes.wolf_acc, Lexemes.nose_acc,
  Lexemes.window_acc, Lexemes.shaman_pl, Lexemes.window_pl, Lexemes.attach_appl,
  Lexemes.languish_appl, Lexemes.support_appl, Lexemes.surpass_appl, Lexemes.do_trans,
  Lexemes.broom_trans, Lexemes.move_trans, Lexemes.bribe_trans, Lexemes.wash_perf_act,
  Lexemes.ground_perf_act, Lexemes.hate_perf_act, Lexemes.wash_perf_pass, Lexemes.ground_perf_pass,
  Lexemes.hate_perf_pass]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [f_3a, f_3b, f_3c, f_3d, f_5a, f_5b, f_5c, f_5d, f_5e, f_5f, f_9a,
  f_9b, f_9c, f_9d, f_9e, f_9f, f_14a, f_14b, f_14c, f_14d, f_14e, f_14f, f_14g, f_14h, f_16a,
  f_16b, f_16c, f_16d, f_16e, f_16f, f_16g, f_16h, f_18a, f_18b, f_18c, f_18d, f_18e, f_18f]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := [f_3a_ill, f_3b_ill, f_3c_ill, f_3d_ill, f_5c_ill1, f_5c_ill2,
  f_9a_ill, f_9b_ill, f_9c_ill, f_9d_ill, f_9e_ill, f_9f_ill, f_14a_ill, f_14b_ill, f_14c_ill,
  f_14d_ill, f_14e_ill, f_14f_ill, f_14g_ill, f_14h_ill, f_18e_ill1, f_18e_ill2]

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := []

end AksenovaEtAl2024.Wordlist
