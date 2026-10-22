module

public import Linglib.Data.Wordlist.Schema

/-!
# `Padgett2002`: word forms

Auto-generated from `Linglib/Data/Wordlist/Padgett2002.json` by `scripts/gen_wordlist.py`. Do not
edit by hand; edit the JSON and re-run the generator. Declarations live in `namespace
Padgett2002.Wordlist`.
-/

@[expose] public section

namespace Padgett2002.Wordlist

open CLDF.Wordlist

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

/-- The nominative singular cell, `Case=Nom|Number=Sing`. -/
def nom_sg : Cell := { case_ := ↑UD.Case.Nom, number := ↑UD.Number.Sing }

/-- The accusative singular cell, `Case=Acc|Number=Sing`. -/
def acc_sg : Cell := { case_ := ↑UD.Case.Acc, number := ↑UD.Number.Sing }

/-- The genitive singular cell, `Case=Gen|Number=Sing`. -/
def gen_sg : Cell := { case_ := ↑UD.Case.Gen, number := ↑UD.Number.Sing }

/-- The nominative plural cell, `Case=Nom|Number=Plur`. -/
def nom_pl : Cell := { case_ := ↑UD.Case.Nom, number := ↑UD.Number.Plur }

/-- The genitive plural cell, `Case=Gen|Number=Plur`. -/
def gen_pl : Cell := { case_ := ↑UD.Case.Gen, number := ↑UD.Number.Plur }

def Lexemes.rope : Lexeme :=
  { id := "rope", languageId := "nucl1301", parameterId := "rope", label := "ip",
    pos := ↑UD.UPOS.NOUN }

def Lexemes.girl : Lexeme :=
  { id := "girl", languageId := "nucl1301", parameterId := "girl", label := "kɨz",
    pos := ↑UD.UPOS.NOUN }

def Lexemes.face : Lexeme :=
  { id := "face", languageId := "nucl1301", parameterId := "face", label := "yüz",
    pos := ↑UD.UPOS.NOUN }

def Lexemes.stamp : Lexeme :=
  { id := "stamp", languageId := "nucl1301", parameterId := "stamp", label := "pul",
    pos := ↑UD.UPOS.NOUN }

def Lexemes.hand : Lexeme :=
  { id := "hand", languageId := "nucl1301", parameterId := "hand", label := "el",
    pos := ↑UD.UPOS.NOUN }

def Lexemes.stalk : Lexeme :=
  { id := "stalk", languageId := "nucl1301", parameterId := "stalk", label := "sap",
    pos := ↑UD.UPOS.NOUN }

def Lexemes.village : Lexeme :=
  { id := "village", languageId := "nucl1301", parameterId := "village", label := "köy",
    pos := ↑UD.UPOS.NOUN }

def Lexemes.end : Lexeme :=
  { id := "end", languageId := "nucl1301", parameterId := "end", label := "son",
    pos := ↑UD.UPOS.NOUN }

def Lexemes.system : Lexeme :=
  { id := "system", languageId := "nucl1301", parameterId := "system", label := "usulʸ",
    pos := ↑UD.UPOS.NOUN }

def Lexemes.petrol : Lexeme :=
  { id := "petrol", languageId := "nucl1301", parameterId := "petrol", label := "petrolʸ",
    pos := ↑UD.UPOS.NOUN }

def Lexemes.question : Lexeme :=
  { id := "question", languageId := "nucl1301", parameterId := "question", label := "sualʸ",
    pos := ↑UD.UPOS.NOUN }

def Lexemes.school : Lexeme :=
  { id := "school", languageId := "nucl1301", parameterId := "school", label := "okul",
    pos := ↑UD.UPOS.NOUN }

def Lexemes.police_station : Lexeme :=
  { id := "police_station", languageId := "nucl1301", parameterId := "police_station",
    label := "karakol", pos := ↑UD.UPOS.NOUN }

def Lexemes.fork : Lexeme :=
  { id := "fork", languageId := "nucl1301", parameterId := "fork", label := "tʃatal",
    pos := ↑UD.UPOS.NOUN }

def ip : Form Cell :=
  { id := "padgett2002_ip"
    lexeme := Lexemes.rope
    cell := nom_sg
    form := "ip"
    segments := ["i", "p"]
    morphs := ["ip"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def ip_i : Form Cell :=
  { id := "padgett2002_ip_i"
    lexeme := Lexemes.rope
    cell := acc_sg
    form := "ipi"
    segments := ["i", "p", "i"]
    morphs := ["ip", "i"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def ip_in : Form Cell :=
  { id := "padgett2002_ip_in"
    lexeme := Lexemes.rope
    cell := gen_sg
    form := "ipin"
    segments := ["i", "p", "i", "n"]
    morphs := ["ip", "in"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def ip_ler : Form Cell :=
  { id := "padgett2002_ip_ler"
    lexeme := Lexemes.rope
    cell := nom_pl
    form := "ipler"
    segments := ["i", "p", "l", "e", "r"]
    morphs := ["ip", "ler"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def kiiz : Form Cell :=
  { id := "padgett2002_kiiz"
    lexeme := Lexemes.girl
    cell := nom_sg
    form := "kɨz"
    segments := ["k", "ɨ", "z"]
    morphs := ["kɨz"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def kiiz_ii : Form Cell :=
  { id := "padgett2002_kiiz_ii"
    lexeme := Lexemes.girl
    cell := acc_sg
    form := "kɨzɨ"
    segments := ["k", "ɨ", "z", "ɨ"]
    morphs := ["kɨz", "ɨ"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def kiiz_iin : Form Cell :=
  { id := "padgett2002_kiiz_iin"
    lexeme := Lexemes.girl
    cell := gen_sg
    form := "kɨzɨn"
    segments := ["k", "ɨ", "z", "ɨ", "n"]
    morphs := ["kɨz", "ɨn"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def kiiz_lar : Form Cell :=
  { id := "padgett2002_kiiz_lar"
    lexeme := Lexemes.girl
    cell := nom_pl
    form := "kɨzlar"
    segments := ["k", "ɨ", "z", "l", "a", "r"]
    morphs := ["kɨz", "lar"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def yuez : Form Cell :=
  { id := "padgett2002_yuez"
    lexeme := Lexemes.face
    cell := nom_sg
    form := "yüz"
    segments := ["y", "ü", "z"]
    morphs := ["yüz"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def yuez_ue : Form Cell :=
  { id := "padgett2002_yuez_ue"
    lexeme := Lexemes.face
    cell := acc_sg
    form := "yüzü"
    segments := ["y", "ü", "z", "ü"]
    morphs := ["yüz", "ü"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def yuez_uen : Form Cell :=
  { id := "padgett2002_yuez_uen"
    lexeme := Lexemes.face
    cell := gen_sg
    form := "yüzün"
    segments := ["y", "ü", "z", "ü", "n"]
    morphs := ["yüz", "ün"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def yuez_ler : Form Cell :=
  { id := "padgett2002_yuez_ler"
    lexeme := Lexemes.face
    cell := nom_pl
    form := "yüzler"
    segments := ["y", "ü", "z", "l", "e", "r"]
    morphs := ["yüz", "ler"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def pul : Form Cell :=
  { id := "padgett2002_pul"
    lexeme := Lexemes.stamp
    cell := nom_sg
    form := "pul"
    segments := ["p", "u", "l"]
    morphs := ["pul"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def pul_u : Form Cell :=
  { id := "padgett2002_pul_u"
    lexeme := Lexemes.stamp
    cell := acc_sg
    form := "pulu"
    segments := ["p", "u", "l", "u"]
    morphs := ["pul", "u"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def pul_un : Form Cell :=
  { id := "padgett2002_pul_un"
    lexeme := Lexemes.stamp
    cell := gen_sg
    form := "pulun"
    segments := ["p", "u", "l", "u", "n"]
    morphs := ["pul", "un"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def pul_lar : Form Cell :=
  { id := "padgett2002_pul_lar"
    lexeme := Lexemes.stamp
    cell := nom_pl
    form := "pullar"
    segments := ["p", "u", "l", "l", "a", "r"]
    morphs := ["pul", "lar"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def el : Form Cell :=
  { id := "padgett2002_el"
    lexeme := Lexemes.hand
    cell := nom_sg
    form := "el"
    segments := ["e", "l"]
    morphs := ["el"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def el_i : Form Cell :=
  { id := "padgett2002_el_i"
    lexeme := Lexemes.hand
    cell := acc_sg
    form := "eli"
    segments := ["e", "l", "i"]
    morphs := ["el", "i"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def el_in : Form Cell :=
  { id := "padgett2002_el_in"
    lexeme := Lexemes.hand
    cell := gen_sg
    form := "elin"
    segments := ["e", "l", "i", "n"]
    morphs := ["el", "in"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def el_ler : Form Cell :=
  { id := "padgett2002_el_ler"
    lexeme := Lexemes.hand
    cell := nom_pl
    form := "eller"
    segments := ["e", "l", "l", "e", "r"]
    morphs := ["el", "ler"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def sap : Form Cell :=
  { id := "padgett2002_sap"
    lexeme := Lexemes.stalk
    cell := nom_sg
    form := "sap"
    segments := ["s", "a", "p"]
    morphs := ["sap"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def sap_ii : Form Cell :=
  { id := "padgett2002_sap_ii"
    lexeme := Lexemes.stalk
    cell := acc_sg
    form := "sapɨ"
    segments := ["s", "a", "p", "ɨ"]
    morphs := ["sap", "ɨ"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def sap_iin : Form Cell :=
  { id := "padgett2002_sap_iin"
    lexeme := Lexemes.stalk
    cell := gen_sg
    form := "sapɨn"
    segments := ["s", "a", "p", "ɨ", "n"]
    morphs := ["sap", "ɨn"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def sap_lar : Form Cell :=
  { id := "padgett2002_sap_lar"
    lexeme := Lexemes.stalk
    cell := nom_pl
    form := "saplar"
    segments := ["s", "a", "p", "l", "a", "r"]
    morphs := ["sap", "lar"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def koey : Form Cell :=
  { id := "padgett2002_koey"
    lexeme := Lexemes.village
    cell := nom_sg
    form := "köy"
    segments := ["k", "ö", "y"]
    morphs := ["köy"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def koey_ue : Form Cell :=
  { id := "padgett2002_koey_ue"
    lexeme := Lexemes.village
    cell := acc_sg
    form := "köyü"
    segments := ["k", "ö", "y", "ü"]
    morphs := ["köy", "ü"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def koey_uen : Form Cell :=
  { id := "padgett2002_koey_uen"
    lexeme := Lexemes.village
    cell := gen_sg
    form := "köyün"
    segments := ["k", "ö", "y", "ü", "n"]
    morphs := ["köy", "ün"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def koey_ler : Form Cell :=
  { id := "padgett2002_koey_ler"
    lexeme := Lexemes.village
    cell := nom_pl
    form := "köyler"
    segments := ["k", "ö", "y", "l", "e", "r"]
    morphs := ["köy", "ler"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def son : Form Cell :=
  { id := "padgett2002_son"
    lexeme := Lexemes.end
    cell := nom_sg
    form := "son"
    segments := ["s", "o", "n"]
    morphs := ["son"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def son_u : Form Cell :=
  { id := "padgett2002_son_u"
    lexeme := Lexemes.end
    cell := acc_sg
    form := "sonu"
    segments := ["s", "o", "n", "u"]
    morphs := ["son", "u"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def son_un : Form Cell :=
  { id := "padgett2002_son_un"
    lexeme := Lexemes.end
    cell := gen_sg
    form := "sonun"
    segments := ["s", "o", "n", "u", "n"]
    morphs := ["son", "un"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def son_lar : Form Cell :=
  { id := "padgett2002_son_lar"
    lexeme := Lexemes.end
    cell := nom_pl
    form := "sonlar"
    segments := ["s", "o", "n", "l", "a", "r"]
    morphs := ["son", "lar"]
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def ip_ler_in : Form Cell :=
  { id := "padgett2002_ip_ler_in"
    lexeme := Lexemes.rope
    cell := gen_pl
    form := "iplerin"
    segments := ["i", "p", "l", "e", "r", "i", "n"]
    morphs := ["ip", "ler", "in"]
    source := [
      ⟨"padgett-2002", "p. 85"⟩
    ] }

def kiiz_lar_iin : Form Cell :=
  { id := "padgett2002_kiiz_lar_iin"
    lexeme := Lexemes.girl
    cell := gen_pl
    form := "kɨzlarɨn"
    segments := ["k", "ɨ", "z", "l", "a", "r", "ɨ", "n"]
    morphs := ["kɨz", "lar", "ɨn"]
    source := [
      ⟨"padgett-2002", "p. 85"⟩
    ] }

def pul_lar_iin : Form Cell :=
  { id := "padgett2002_pul_lar_iin"
    lexeme := Lexemes.stamp
    cell := gen_pl
    form := "pullarɨn"
    segments := ["p", "u", "l", "l", "a", "r", "ɨ", "n"]
    morphs := ["pul", "lar", "ɨn"]
    source := [
      ⟨"padgett-2002", "p. 85"⟩
    ] }

def yuez_ler_in : Form Cell :=
  { id := "padgett2002_yuez_ler_in"
    lexeme := Lexemes.face
    cell := gen_pl
    form := "yüzlerin"
    segments := ["y", "ü", "z", "l", "e", "r", "i", "n"]
    morphs := ["yüz", "ler", "in"]
    source := [
      ⟨"padgett-2002", "p. 85"⟩
    ] }

def pul_lar_un_star : Form Cell :=
  { id := "padgett2002_pul_lar_un_star"
    lexeme := Lexemes.stamp
    cell := gen_pl
    form := "pullarun"
    segments := ["p", "u", "l", "l", "a", "r", "u", "n"]
    morphs := ["pul", "lar", "un"]
    judgment := .ungrammatical
    source := [
      ⟨"padgett-2002", "p. 85"⟩
    ] }

def yuez_ler_uen_star : Form Cell :=
  { id := "padgett2002_yuez_ler_uen_star"
    lexeme := Lexemes.face
    cell := gen_pl
    form := "yüzlerün"
    segments := ["y", "ü", "z", "l", "e", "r", "ü", "n"]
    morphs := ["yüz", "ler", "ün"]
    judgment := .ungrammatical
    source := [
      ⟨"padgett-2002", "p. 85"⟩
    ] }

def usulj : Form Cell :=
  { id := "padgett2002_usulj"
    lexeme := Lexemes.system
    cell := nom_sg
    form := "usulʸ"
    segments := ["u", "s", "u", "lʸ"]
    morphs := ["usulʸ"]
    source := [
      ⟨"padgett-2002", "(21), p. 93"⟩
    ] }

def usulj_ue : Form Cell :=
  { id := "padgett2002_usulj_ue"
    lexeme := Lexemes.system
    cell := acc_sg
    form := "usulʸü"
    segments := ["u", "s", "u", "lʸ", "ü"]
    morphs := ["usulʸ", "ü"]
    source := [
      ⟨"padgett-2002", "(21), p. 93"⟩
    ] }

def petrolj : Form Cell :=
  { id := "padgett2002_petrolj"
    lexeme := Lexemes.petrol
    cell := nom_sg
    form := "petrolʸ"
    segments := ["p", "e", "t", "r", "o", "lʸ"]
    morphs := ["petrolʸ"]
    source := [
      ⟨"padgett-2002", "(21), p. 93"⟩
    ] }

def petrolj_ue : Form Cell :=
  { id := "padgett2002_petrolj_ue"
    lexeme := Lexemes.petrol
    cell := acc_sg
    form := "petrolʸü"
    segments := ["p", "e", "t", "r", "o", "lʸ", "ü"]
    morphs := ["petrolʸ", "ü"]
    source := [
      ⟨"padgett-2002", "(21), p. 93"⟩
    ] }

def sualj : Form Cell :=
  { id := "padgett2002_sualj"
    lexeme := Lexemes.question
    cell := nom_sg
    form := "sualʸ"
    segments := ["s", "u", "a", "lʸ"]
    morphs := ["sualʸ"]
    source := [
      ⟨"padgett-2002", "(21), p. 93"⟩
    ] }

def sualj_i : Form Cell :=
  { id := "padgett2002_sualj_i"
    lexeme := Lexemes.question
    cell := acc_sg
    form := "sualʸi"
    segments := ["s", "u", "a", "lʸ", "i"]
    morphs := ["sualʸ", "i"]
    source := [
      ⟨"padgett-2002", "(21), p. 93"⟩
    ] }

def okul : Form Cell :=
  { id := "padgett2002_okul"
    lexeme := Lexemes.school
    cell := nom_sg
    form := "okul"
    segments := ["o", "k", "u", "l"]
    morphs := ["okul"]
    source := [
      ⟨"padgett-2002", "(21), p. 93"⟩
    ] }

def okul_u : Form Cell :=
  { id := "padgett2002_okul_u"
    lexeme := Lexemes.school
    cell := acc_sg
    form := "okulu"
    segments := ["o", "k", "u", "l", "u"]
    morphs := ["okul", "u"]
    source := [
      ⟨"padgett-2002", "(21), p. 93"⟩
    ] }

def karakol : Form Cell :=
  { id := "padgett2002_karakol"
    lexeme := Lexemes.police_station
    cell := nom_sg
    form := "karakol"
    segments := ["k", "a", "r", "a", "k", "o", "l"]
    morphs := ["karakol"]
    source := [
      ⟨"padgett-2002", "(21), p. 93"⟩
    ] }

def karakol_u : Form Cell :=
  { id := "padgett2002_karakol_u"
    lexeme := Lexemes.police_station
    cell := acc_sg
    form := "karakolu"
    segments := ["k", "a", "r", "a", "k", "o", "l", "u"]
    morphs := ["karakol", "u"]
    source := [
      ⟨"padgett-2002", "(21), p. 93"⟩
    ] }

def tshatal : Form Cell :=
  { id := "padgett2002_tshatal"
    lexeme := Lexemes.fork
    cell := nom_sg
    form := "tʃatal"
    segments := ["tʃ", "a", "t", "a", "l"]
    morphs := ["tʃatal"]
    source := [
      ⟨"padgett-2002", "(21), p. 93"⟩
    ] }

def tshatal_ii : Form Cell :=
  { id := "padgett2002_tshatal_ii"
    lexeme := Lexemes.fork
    cell := acc_sg
    form := "tʃatalɨ"
    segments := ["tʃ", "a", "t", "a", "l", "ɨ"]
    morphs := ["tʃatal", "ɨ"]
    source := [
      ⟨"padgett-2002", "(21), p. 93"⟩
    ] }

def padgett2002_rope.paradigm : Paradigm Cell :=
  { id := "padgett2002_rope", lexeme := Lexemes.rope,
    forms := [ip, ip_i, ip_in, ip_ler, ip_ler_in],
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩,
      ⟨"padgett-2002", "p. 85"⟩
    ] }

def padgett2002_girl.paradigm : Paradigm Cell :=
  { id := "padgett2002_girl", lexeme := Lexemes.girl,
    forms := [kiiz, kiiz_ii, kiiz_iin, kiiz_lar, kiiz_lar_iin],
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩,
      ⟨"padgett-2002", "p. 85"⟩
    ] }

def padgett2002_face.paradigm : Paradigm Cell :=
  { id := "padgett2002_face", lexeme := Lexemes.face,
    forms := [yuez, yuez_ue, yuez_uen, yuez_ler, yuez_ler_in],
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩,
      ⟨"padgett-2002", "p. 85"⟩
    ] }

def padgett2002_stamp.paradigm : Paradigm Cell :=
  { id := "padgett2002_stamp", lexeme := Lexemes.stamp,
    forms := [pul, pul_u, pul_un, pul_lar, pul_lar_iin],
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩,
      ⟨"padgett-2002", "p. 85"⟩
    ] }

def padgett2002_hand.paradigm : Paradigm Cell :=
  { id := "padgett2002_hand", lexeme := Lexemes.hand,
    forms := [el, el_i, el_in, el_ler],
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def padgett2002_stalk.paradigm : Paradigm Cell :=
  { id := "padgett2002_stalk", lexeme := Lexemes.stalk,
    forms := [sap, sap_ii, sap_iin, sap_lar],
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def padgett2002_village.paradigm : Paradigm Cell :=
  { id := "padgett2002_village", lexeme := Lexemes.village,
    forms := [koey, koey_ue, koey_uen, koey_ler],
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def padgett2002_end.paradigm : Paradigm Cell :=
  { id := "padgett2002_end", lexeme := Lexemes.end,
    forms := [son, son_u, son_un, son_lar],
    source := [
      ⟨"padgett-2002", "(6), p. 84"⟩
    ] }

def padgett2002_system.paradigm : Paradigm Cell :=
  { id := "padgett2002_system", lexeme := Lexemes.system,
    forms := [usulj, usulj_ue],
    source := [
      ⟨"padgett-2002", "(21), p. 93"⟩
    ] }

def padgett2002_petrol.paradigm : Paradigm Cell :=
  { id := "padgett2002_petrol", lexeme := Lexemes.petrol,
    forms := [petrolj, petrolj_ue],
    source := [
      ⟨"padgett-2002", "(21), p. 93"⟩
    ] }

def padgett2002_question.paradigm : Paradigm Cell :=
  { id := "padgett2002_question", lexeme := Lexemes.question,
    forms := [sualj, sualj_i],
    source := [
      ⟨"padgett-2002", "(21), p. 93"⟩
    ] }

def padgett2002_school.paradigm : Paradigm Cell :=
  { id := "padgett2002_school", lexeme := Lexemes.school,
    forms := [okul, okul_u],
    source := [
      ⟨"padgett-2002", "(21), p. 93"⟩
    ] }

def padgett2002_police_station.paradigm : Paradigm Cell :=
  { id := "padgett2002_police_station", lexeme := Lexemes.police_station,
    forms := [karakol, karakol_u],
    source := [
      ⟨"padgett-2002", "(21), p. 93"⟩
    ] }

def padgett2002_fork.paradigm : Paradigm Cell :=
  { id := "padgett2002_fork", lexeme := Lexemes.fork,
    forms := [tshatal, tshatal_ii],
    source := [
      ⟨"padgett-2002", "(21), p. 93"⟩
    ] }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.rope, Lexemes.girl, Lexemes.face, Lexemes.stamp, Lexemes.hand,
  Lexemes.stalk, Lexemes.village, Lexemes.end, Lexemes.system, Lexemes.petrol, Lexemes.question,
  Lexemes.school, Lexemes.police_station, Lexemes.fork]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [ip, ip_i, ip_in, ip_ler, kiiz, kiiz_ii, kiiz_iin, kiiz_lar, yuez,
  yuez_ue, yuez_uen, yuez_ler, pul, pul_u, pul_un, pul_lar, el, el_i, el_in, el_ler, sap, sap_ii,
  sap_iin, sap_lar, koey, koey_ue, koey_uen, koey_ler, son, son_u, son_un, son_lar, ip_ler_in,
  kiiz_lar_iin, pul_lar_iin, yuez_ler_in, usulj, usulj_ue, petrolj, petrolj_ue, sualj, sualj_i,
  okul, okul_u, karakol, karakol_u, tshatal, tshatal_ii]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := [pul_lar_un_star, yuez_ler_uen_star]

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := []

/-- Every paradigm of the data. -/
def paradigms : List (Paradigm Cell) := [padgett2002_rope.paradigm, padgett2002_girl.paradigm,
  padgett2002_face.paradigm, padgett2002_stamp.paradigm, padgett2002_hand.paradigm,
  padgett2002_stalk.paradigm, padgett2002_village.paradigm, padgett2002_end.paradigm,
  padgett2002_system.paradigm, padgett2002_petrol.paradigm, padgett2002_question.paradigm,
  padgett2002_school.paradigm, padgett2002_police_station.paradigm, padgett2002_fork.paradigm]

end Padgett2002.Wordlist
