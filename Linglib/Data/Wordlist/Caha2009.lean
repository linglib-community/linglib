module

public import Linglib.Data.Wordlist.Schema

/-!
# `Caha2009`: word forms

Auto-generated from `Linglib/Data/Wordlist/Caha2009.json` by `scripts/gen_wordlist.py`. Do not edit
by hand; edit the JSON and re-run the generator. Declarations live in `namespace Caha2009.Wordlist`.
-/

@[expose] public section

namespace Caha2009.Wordlist

open CLDF.Wordlist

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

/-- The nominative singular cell, `Case=Nom|Number=Sing`. -/
def nom_sg : Cell := { case := ↑UD.Case.Nom, number := ↑UD.Number.Sing }

/-- The nominative singular fem cell, `Case=Nom|Number=Sing|Gender=Fem`. -/
def nom_sg_f : Cell := { case := ↑UD.Case.Nom, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Fem }

/-- The nominative singular masc cell, `Case=Nom|Number=Sing|Gender=Masc`. -/
def nom_sg_m : Cell :=
  { case := ↑UD.Case.Nom, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Masc }

/-- The nominative singular neut cell, `Case=Nom|Number=Sing|Gender=Neut`. -/
def nom_sg_n : Cell :=
  { case := ↑UD.Case.Nom, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Neut }

/-- The accusative singular cell, `Case=Acc|Number=Sing`. -/
def acc_sg : Cell := { case := ↑UD.Case.Acc, number := ↑UD.Number.Sing }

/-- The accusative singular fem cell, `Case=Acc|Number=Sing|Gender=Fem`. -/
def acc_sg_f : Cell := { case := ↑UD.Case.Acc, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Fem }

/-- The accusative singular masc cell, `Case=Acc|Number=Sing|Gender=Masc`. -/
def acc_sg_m : Cell :=
  { case := ↑UD.Case.Acc, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Masc }

/-- The accusative singular neut cell, `Case=Acc|Number=Sing|Gender=Neut`. -/
def acc_sg_n : Cell :=
  { case := ↑UD.Case.Acc, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Neut }

/-- The genitive singular cell, `Case=Gen|Number=Sing`. -/
def gen_sg : Cell := { case := ↑UD.Case.Gen, number := ↑UD.Number.Sing }

/-- The genitive singular fem cell, `Case=Gen|Number=Sing|Gender=Fem`. -/
def gen_sg_f : Cell := { case := ↑UD.Case.Gen, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Fem }

/-- The genitive singular masc cell, `Case=Gen|Number=Sing|Gender=Masc`. -/
def gen_sg_m : Cell :=
  { case := ↑UD.Case.Gen, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Masc }

/-- The genitive singular neut cell, `Case=Gen|Number=Sing|Gender=Neut`. -/
def gen_sg_n : Cell :=
  { case := ↑UD.Case.Gen, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Neut }

/-- The prepositional singular cell, `Case=Loc|Number=Sing`. -/
def prep_sg : Cell := { case := ↑UD.Case.Loc, number := ↑UD.Number.Sing }

/-- The prepositional singular fem cell, `Case=Loc|Number=Sing|Gender=Fem`. -/
def prep_sg_f : Cell :=
  { case := ↑UD.Case.Loc, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Fem }

/-- The prepositional singular masc cell, `Case=Loc|Number=Sing|Gender=Masc`. -/
def prep_sg_m : Cell :=
  { case := ↑UD.Case.Loc, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Masc }

/-- The prepositional singular neut cell, `Case=Loc|Number=Sing|Gender=Neut`. -/
def prep_sg_n : Cell :=
  { case := ↑UD.Case.Loc, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Neut }

/-- The dative singular cell, `Case=Dat|Number=Sing`. -/
def dat_sg : Cell := { case := ↑UD.Case.Dat, number := ↑UD.Number.Sing }

/-- The dative singular fem cell, `Case=Dat|Number=Sing|Gender=Fem`. -/
def dat_sg_f : Cell := { case := ↑UD.Case.Dat, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Fem }

/-- The dative singular masc cell, `Case=Dat|Number=Sing|Gender=Masc`. -/
def dat_sg_m : Cell :=
  { case := ↑UD.Case.Dat, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Masc }

/-- The dative singular neut cell, `Case=Dat|Number=Sing|Gender=Neut`. -/
def dat_sg_n : Cell :=
  { case := ↑UD.Case.Dat, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Neut }

/-- The instrumental singular cell, `Case=Ins|Number=Sing`. -/
def ins_sg : Cell := { case := ↑UD.Case.Ins, number := ↑UD.Number.Sing }

/-- The instrumental singular fem cell, `Case=Ins|Number=Sing|Gender=Fem`. -/
def ins_sg_f : Cell := { case := ↑UD.Case.Ins, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Fem }

/-- The instrumental singular masc cell, `Case=Ins|Number=Sing|Gender=Masc`. -/
def ins_sg_m : Cell :=
  { case := ↑UD.Case.Ins, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Masc }

/-- The instrumental singular neut cell, `Case=Ins|Number=Sing|Gender=Neut`. -/
def ins_sg_n : Cell :=
  { case := ↑UD.Case.Ins, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Neut }

/-- The nominative dual cell, `Case=Nom|Number=Dual`. -/
def nom_du : Cell := { case := ↑UD.Case.Nom, number := ↑UD.Number.Dual }

/-- The nominative dual masc cell, `Case=Nom|Number=Dual|Gender=Masc`. -/
def nom_du_m : Cell :=
  { case := ↑UD.Case.Nom, number := ↑UD.Number.Dual, gender := ↑UD.Gender.Masc }

/-- The accusative dual cell, `Case=Acc|Number=Dual`. -/
def acc_du : Cell := { case := ↑UD.Case.Acc, number := ↑UD.Number.Dual }

/-- The accusative dual masc cell, `Case=Acc|Number=Dual|Gender=Masc`. -/
def acc_du_m : Cell :=
  { case := ↑UD.Case.Acc, number := ↑UD.Number.Dual, gender := ↑UD.Gender.Masc }

/-- The genitive dual cell, `Case=Gen|Number=Dual`. -/
def gen_du : Cell := { case := ↑UD.Case.Gen, number := ↑UD.Number.Dual }

/-- The genitive dual masc cell, `Case=Gen|Number=Dual|Gender=Masc`. -/
def gen_du_m : Cell :=
  { case := ↑UD.Case.Gen, number := ↑UD.Number.Dual, gender := ↑UD.Gender.Masc }

/-- The prepositional dual cell, `Case=Loc|Number=Dual`. -/
def prep_du : Cell := { case := ↑UD.Case.Loc, number := ↑UD.Number.Dual }

/-- The prepositional dual masc cell, `Case=Loc|Number=Dual|Gender=Masc`. -/
def prep_du_m : Cell :=
  { case := ↑UD.Case.Loc, number := ↑UD.Number.Dual, gender := ↑UD.Gender.Masc }

/-- The dative dual cell, `Case=Dat|Number=Dual`. -/
def dat_du : Cell := { case := ↑UD.Case.Dat, number := ↑UD.Number.Dual }

/-- The dative dual masc cell, `Case=Dat|Number=Dual|Gender=Masc`. -/
def dat_du_m : Cell :=
  { case := ↑UD.Case.Dat, number := ↑UD.Number.Dual, gender := ↑UD.Gender.Masc }

/-- The instrumental dual cell, `Case=Ins|Number=Dual`. -/
def ins_du : Cell := { case := ↑UD.Case.Ins, number := ↑UD.Number.Dual }

/-- The instrumental dual masc cell, `Case=Ins|Number=Dual|Gender=Masc`. -/
def ins_du_m : Cell :=
  { case := ↑UD.Case.Ins, number := ↑UD.Number.Dual, gender := ↑UD.Gender.Masc }

/-- The nominative plural cell, `Case=Nom|Number=Plur`. -/
def nom_pl : Cell := { case := ↑UD.Case.Nom, number := ↑UD.Number.Plur }

/-- The nominative plural fem cell, `Case=Nom|Number=Plur|Gender=Fem`. -/
def nom_pl_f : Cell := { case := ↑UD.Case.Nom, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Fem }

/-- The nominative plural masc cell, `Case=Nom|Number=Plur|Gender=Masc`. -/
def nom_pl_m : Cell :=
  { case := ↑UD.Case.Nom, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Masc }

/-- The nominative plural neut cell, `Case=Nom|Number=Plur|Gender=Neut`. -/
def nom_pl_n : Cell :=
  { case := ↑UD.Case.Nom, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Neut }

/-- The accusative plural cell, `Case=Acc|Number=Plur`. -/
def acc_pl : Cell := { case := ↑UD.Case.Acc, number := ↑UD.Number.Plur }

/-- The accusative plural fem cell, `Case=Acc|Number=Plur|Gender=Fem`. -/
def acc_pl_f : Cell := { case := ↑UD.Case.Acc, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Fem }

/-- The accusative plural masc cell, `Case=Acc|Number=Plur|Gender=Masc`. -/
def acc_pl_m : Cell :=
  { case := ↑UD.Case.Acc, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Masc }

/-- The accusative plural neut cell, `Case=Acc|Number=Plur|Gender=Neut`. -/
def acc_pl_n : Cell :=
  { case := ↑UD.Case.Acc, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Neut }

/-- The genitive plural cell, `Case=Gen|Number=Plur`. -/
def gen_pl : Cell := { case := ↑UD.Case.Gen, number := ↑UD.Number.Plur }

/-- The genitive plural fem cell, `Case=Gen|Number=Plur|Gender=Fem`. -/
def gen_pl_f : Cell := { case := ↑UD.Case.Gen, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Fem }

/-- The genitive plural masc cell, `Case=Gen|Number=Plur|Gender=Masc`. -/
def gen_pl_m : Cell :=
  { case := ↑UD.Case.Gen, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Masc }

/-- The genitive plural neut cell, `Case=Gen|Number=Plur|Gender=Neut`. -/
def gen_pl_n : Cell :=
  { case := ↑UD.Case.Gen, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Neut }

/-- The prepositional plural cell, `Case=Loc|Number=Plur`. -/
def prep_pl : Cell := { case := ↑UD.Case.Loc, number := ↑UD.Number.Plur }

/-- The prepositional plural fem cell, `Case=Loc|Number=Plur|Gender=Fem`. -/
def prep_pl_f : Cell :=
  { case := ↑UD.Case.Loc, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Fem }

/-- The prepositional plural masc cell, `Case=Loc|Number=Plur|Gender=Masc`. -/
def prep_pl_m : Cell :=
  { case := ↑UD.Case.Loc, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Masc }

/-- The prepositional plural neut cell, `Case=Loc|Number=Plur|Gender=Neut`. -/
def prep_pl_n : Cell :=
  { case := ↑UD.Case.Loc, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Neut }

/-- The dative plural cell, `Case=Dat|Number=Plur`. -/
def dat_pl : Cell := { case := ↑UD.Case.Dat, number := ↑UD.Number.Plur }

/-- The dative plural fem cell, `Case=Dat|Number=Plur|Gender=Fem`. -/
def dat_pl_f : Cell := { case := ↑UD.Case.Dat, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Fem }

/-- The dative plural masc cell, `Case=Dat|Number=Plur|Gender=Masc`. -/
def dat_pl_m : Cell :=
  { case := ↑UD.Case.Dat, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Masc }

/-- The dative plural neut cell, `Case=Dat|Number=Plur|Gender=Neut`. -/
def dat_pl_n : Cell :=
  { case := ↑UD.Case.Dat, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Neut }

/-- The instrumental plural cell, `Case=Ins|Number=Plur`. -/
def ins_pl : Cell := { case := ↑UD.Case.Ins, number := ↑UD.Number.Plur }

/-- The instrumental plural fem cell, `Case=Ins|Number=Plur|Gender=Fem`. -/
def ins_pl_f : Cell := { case := ↑UD.Case.Ins, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Fem }

/-- The instrumental plural masc cell, `Case=Ins|Number=Plur|Gender=Masc`. -/
def ins_pl_m : Cell :=
  { case := ↑UD.Case.Ins, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Masc }

/-- The instrumental plural neut cell, `Case=Ins|Number=Plur|Gender=Neut`. -/
def ins_pl_n : Cell :=
  { case := ↑UD.Case.Ins, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Neut }

def Lexemes.srp_sin : Lexeme :=
  { id := "srp_sin", languageId := "sout1528", parameterId := "son", label := "sîn" }

def Lexemes.srp_grad : Lexeme :=
  { id := "srp_grad", languageId := "sout1528", parameterId := "city", label := "grâd" }

def Lexemes.srp_muz : Lexeme :=
  { id := "srp_muz", languageId := "sout1528", parameterId := "man", label := "muž" }

def Lexemes.srp_selo : Lexeme :=
  { id := "srp_selo", languageId := "sout1528", parameterId := "village", label := "sèlo" }

def Lexemes.srp_srce : Lexeme :=
  { id := "srp_srce", languageId := "sout1528", parameterId := "heart", label := "srce" }

def Lexemes.srp_ovca : Lexeme :=
  { id := "srp_ovca", languageId := "sout1528", parameterId := "sheep", label := "òvca" }

def Lexemes.srp_smrt : Lexeme :=
  { id := "srp_smrt", languageId := "sout1528", parameterId := "death", label := "smȑt" }

def Lexemes.srp_ja : Lexeme :=
  { id := "srp_ja", languageId := "sout1528", parameterId := "i", label := "ja" }

def Lexemes.srp_ti : Lexeme :=
  { id := "srp_ti", languageId := "sout1528", parameterId := "you", label := "ti" }

def Lexemes.srp_on : Lexeme :=
  { id := "srp_on", languageId := "sout1528", parameterId := "he_it", label := "on/ono" }

def Lexemes.srp_ona : Lexeme :=
  { id := "srp_ona", languageId := "sout1528", parameterId := "she", label := "ona" }

def Lexemes.srp_mi : Lexeme :=
  { id := "srp_mi", languageId := "sout1528", parameterId := "we", label := "mi" }

def Lexemes.srp_vi : Lexeme :=
  { id := "srp_vi", languageId := "sout1528", parameterId := "you", label := "vi" }

def Lexemes.srp_oni : Lexeme :=
  { id := "srp_oni", languageId := "sout1528", parameterId := "they", label := "oni/ona/one" }

def Lexemes.slv_miza : Lexeme :=
  { id := "slv_miza", languageId := "slov1268", parameterId := "table", label := "mízi" }

def Lexemes.slv_breskev : Lexeme :=
  { id := "slv_breskev", languageId := "slov1268", parameterId := "peach", label := "brêskev" }

def Lexemes.slv_jabolko : Lexeme :=
  { id := "slv_jabolko", languageId := "slov1268", parameterId := "apple", label := "jábolko" }

def Lexemes.slv_kmet : Lexeme :=
  { id := "slv_kmet", languageId := "slov1268", parameterId := "farmer", label := "kmèta" }

def Lexemes.slv_jaz : Lexeme :=
  { id := "slv_jaz", languageId := "slov1268", parameterId := "i", label := "jàz" }

def Lexemes.slv_moj : Lexeme :=
  { id := "slv_moj", languageId := "slov1268", parameterId := "my", label := "mój" }

def Lexemes.slv_dva : Lexeme :=
  { id := "slv_dva", languageId := "slov1268", parameterId := "two", label := "dvâ" }

def Lexemes.slv_mi : Lexeme :=
  { id := "slv_mi", languageId := "slov1268", parameterId := "we", label := "mî" }

def Lexemes.slv_midva : Lexeme :=
  { id := "slv_midva", languageId := "slov1268", parameterId := "we_two", label := "mîdva" }

def Lexemes.slv_nit : Lexeme :=
  { id := "slv_nit", languageId := "slov1268", parameterId := "thread", label := "nìt" }

def Lexemes.slv_gospa : Lexeme :=
  { id := "slv_gospa", languageId := "slov1268", parameterId := "lady", label := "gospá" }

def Lexemes.slv_dan : Lexeme :=
  { id := "slv_dan", languageId := "slov1268", parameterId := "day", label := "dní" }

def Lexemes.slv_racunovodja : Lexeme :=
  { id := "slv_racunovodja", languageId := "slov1268", parameterId := "accountant",
    label := "računovodja" }

def Lexemes.slv_ta : Lexeme :=
  { id := "slv_ta", languageId := "slov1268", parameterId := "this", label := "ta" }

def Lexemes.slv_potnik : Lexeme :=
  { id := "slv_potnik", languageId := "slov1268", parameterId := "traveller", label := "pótnik" }

def Lexemes.slv_tisti : Lexeme :=
  { id := "slv_tisti", languageId := "slov1268", parameterId := "that", label := "tîsto" }

def Lexemes.slv_vas : Lexeme :=
  { id := "slv_vas", languageId := "slov1268", parameterId := "your", label := "váše" }

def Lexemes.ces_okno : Lexeme :=
  { id := "ces_okno", languageId := "czec1258", parameterId := "window", label := "okno" }

def Lexemes.ces_ulice : Lexeme :=
  { id := "ces_ulice", languageId := "czec1258", parameterId := "street", label := "ulice" }

def Lexemes.ces_muz : Lexeme :=
  { id := "ces_muz", languageId := "czec1258", parameterId := "man", label := "muži" }

def Lexemes.ces_dobry : Lexeme :=
  { id := "ces_dobry", languageId := "czec1258", parameterId := "good", label := "dobrý" }

def Lexemes.ces_vetsi : Lexeme :=
  { id := "ces_vetsi", languageId := "czec1258", parameterId := "bigger", label := "větší" }

def Lexemes.ces_oba : Lexeme :=
  { id := "ces_oba", languageId := "czec1258", parameterId := "both", label := "oba" }

def Lexemes.ces_stroj : Lexeme :=
  { id := "ces_stroj", languageId := "czec1258", parameterId := "machine", label := "stroj" }

def Lexemes.ces_kost : Lexeme :=
  { id := "ces_kost", languageId := "czec1258", parameterId := "bone", label := "kosti" }

def Lexemes.ces_ten : Lexeme :=
  { id := "ces_ten", languageId := "czec1258", parameterId := "that", label := "ten" }

def Lexemes.ces_vila : Lexeme :=
  { id := "ces_vila", languageId := "czec1258", parameterId := "villa", label := "vila" }

def Lexemes.ces_misa : Lexeme :=
  { id := "ces_misa", languageId := "czec1258", parameterId := "michelle", label := "Míša" }

def Lexemes.ces_vul : Lexeme :=
  { id := "ces_vul", languageId := "czec1258", parameterId := "ox", label := "vůl" }

def Lexemes.ces_hoch : Lexeme :=
  { id := "ces_hoch", languageId := "czec1258", parameterId := "boy", label := "hoch" }

def Lexemes.ces_pan : Lexeme :=
  { id := "ces_pan", languageId := "czec1258", parameterId := "sir", label := "pán" }

def Lexemes.ces_my : Lexeme :=
  { id := "ces_my", languageId := "czec1258", parameterId := "we", label := "my" }

def Lexemes.ces_ona : Lexeme :=
  { id := "ces_ona", languageId := "czec1258", parameterId := "she", label := "ona" }

def Lexemes.ces_nase : Lexeme :=
  { id := "ces_nase", languageId := "czec1258", parameterId := "our", label := "náš" }

def Lexemes.ces_zatez : Lexeme :=
  { id := "ces_zatez", languageId := "czec1258", parameterId := "stress", label := "zátěž" }

def Lexemes.ces_zena : Lexeme :=
  { id := "ces_zena", languageId := "czec1258", parameterId := "woman", label := "žena" }

def Lexemes.ces_kluk : Lexeme :=
  { id := "ces_kluk", languageId := "czec1258", parameterId := "boy", label := "kluk" }

def Lexemes.ces_pisen : Lexeme :=
  { id := "ces_pisen", languageId := "czec1258", parameterId := "song", label := "píseň" }

def Lexemes.ces_hrad : Lexeme :=
  { id := "ces_hrad", languageId := "czec1258", parameterId := "castle", label := "hrad" }

def Lexemes.ces_mesto : Lexeme :=
  { id := "ces_mesto", languageId := "czec1258", parameterId := "city", label := "město" }

def Lexemes.ces_ono : Lexeme :=
  { id := "ces_ono", languageId := "czec1258", parameterId := "it", label := "ono" }

def Lexemes.ces_oni : Lexeme :=
  { id := "ces_oni", languageId := "czec1258", parameterId := "they", label := "oni" }

def Lexemes.ces_dva : Lexeme :=
  { id := "ces_dva", languageId := "czec1258", parameterId := "two", label := "dva" }

def Lexemes.ces_pet : Lexeme :=
  { id := "ces_pet", languageId := "czec1258", parameterId := "five", label := "pět" }

def Lexemes.slk_ona : Lexeme :=
  { id := "slk_ona", languageId := "slov1269", parameterId := "she", label := "ona" }

def Lexemes.slk_nase : Lexeme :=
  { id := "slk_nase", languageId := "slov1269", parameterId := "our", label := "náš" }

def Lexemes.slk_ulica : Lexeme :=
  { id := "slk_ulica", languageId := "slov1269", parameterId := "street", label := "ulica" }

def Lexemes.slk_tlac : Lexeme :=
  { id := "slk_tlac", languageId := "slov1269", parameterId := "press", label := "tlač" }

def Lexemes.ukr_kraj : Lexeme :=
  { id := "ukr_kraj", languageId := "ukra1253", parameterId := "region", label := "kraj" }

def Lexemes.ukr_velykyj : Lexeme :=
  { id := "ukr_velykyj", languageId := "ukra1253", parameterId := "big", label := "velíkıj" }

def Lexemes.ukr_znannja : Lexeme :=
  { id := "ukr_znannja", languageId := "ukra1253", parameterId := "knowledge", label := "znannjá" }

def Lexemes.ukr_my : Lexeme :=
  { id := "ukr_my", languageId := "ukra1253", parameterId := "we", label := "mı" }

def Lexemes.ukr_kasyr : Lexeme :=
  { id := "ukr_kasyr", languageId := "ukra1253", parameterId := "cashier", label := "kasír" }

def Lexemes.ukr_maty : Lexeme :=
  { id := "ukr_maty", languageId := "ukra1253", parameterId := "mother", label := "mátı" }

def Lexemes.ukr_ruka : Lexeme :=
  { id := "ukr_ruka", languageId := "ukra1253", parameterId := "hand", label := "ruká" }

def Lexemes.ukr_ja : Lexeme :=
  { id := "ukr_ja", languageId := "ukra1253", parameterId := "i", label := "ja" }

def Lexemes.ukr_sto : Lexeme :=
  { id := "ukr_sto", languageId := "ukra1253", parameterId := "hundred", label := "sto" }

def Lexemes.ukr_bezkrajij : Lexeme :=
  { id := "ukr_bezkrajij", languageId := "ukra1253", parameterId := "endless",
    label := "bezkrajij" }

def srp_sin_sg_nom : Form Cell :=
  { id := "srp_sin_sg_nom"
    lexeme := Lexemes.srp_sin
    cell := nom_sg
    form := "sîn"
    morphs := ["sîn"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_sin_sg_acc : Form Cell :=
  { id := "srp_sin_sg_acc"
    lexeme := Lexemes.srp_sin
    cell := acc_sg
    form := "sîna"
    morphs := ["sîna"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_sin_sg_gen : Form Cell :=
  { id := "srp_sin_sg_gen"
    lexeme := Lexemes.srp_sin
    cell := gen_sg
    form := "sîna"
    morphs := ["sîna"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_sin_sg_prep : Form Cell :=
  { id := "srp_sin_sg_prep"
    lexeme := Lexemes.srp_sin
    cell := prep_sg
    form := "sînu"
    morphs := ["sînu"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_sin_sg_dat : Form Cell :=
  { id := "srp_sin_sg_dat"
    lexeme := Lexemes.srp_sin
    cell := dat_sg
    form := "sînu"
    morphs := ["sînu"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_sin_sg_ins : Form Cell :=
  { id := "srp_sin_sg_ins"
    lexeme := Lexemes.srp_sin
    cell := ins_sg
    form := "sînom"
    morphs := ["sînom"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_grad_sg_nom : Form Cell :=
  { id := "srp_grad_sg_nom"
    lexeme := Lexemes.srp_grad
    cell := nom_sg
    form := "grâd"
    morphs := ["grâd"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_grad_sg_acc : Form Cell :=
  { id := "srp_grad_sg_acc"
    lexeme := Lexemes.srp_grad
    cell := acc_sg
    form := "grâd"
    morphs := ["grâd"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_grad_sg_gen : Form Cell :=
  { id := "srp_grad_sg_gen"
    lexeme := Lexemes.srp_grad
    cell := gen_sg
    form := "grâda"
    morphs := ["grâda"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_grad_sg_prep : Form Cell :=
  { id := "srp_grad_sg_prep"
    lexeme := Lexemes.srp_grad
    cell := prep_sg
    form := "grádu"
    morphs := ["grádu"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_grad_sg_dat : Form Cell :=
  { id := "srp_grad_sg_dat"
    lexeme := Lexemes.srp_grad
    cell := dat_sg
    form := "grâdu"
    morphs := ["grâdu"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_grad_sg_ins : Form Cell :=
  { id := "srp_grad_sg_ins"
    lexeme := Lexemes.srp_grad
    cell := ins_sg
    form := "grâdom"
    morphs := ["grâdom"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_muz_sg_nom : Form Cell :=
  { id := "srp_muz_sg_nom"
    lexeme := Lexemes.srp_muz
    cell := nom_sg
    form := "muž"
    morphs := ["muž"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_muz_sg_acc : Form Cell :=
  { id := "srp_muz_sg_acc"
    lexeme := Lexemes.srp_muz
    cell := acc_sg
    form := "muža"
    morphs := ["muža"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_muz_sg_gen : Form Cell :=
  { id := "srp_muz_sg_gen"
    lexeme := Lexemes.srp_muz
    cell := gen_sg
    form := "muža"
    morphs := ["muža"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_muz_sg_prep : Form Cell :=
  { id := "srp_muz_sg_prep"
    lexeme := Lexemes.srp_muz
    cell := prep_sg
    form := "mužu"
    morphs := ["mužu"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_muz_sg_dat : Form Cell :=
  { id := "srp_muz_sg_dat"
    lexeme := Lexemes.srp_muz
    cell := dat_sg
    form := "mužu"
    morphs := ["mužu"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_muz_sg_ins : Form Cell :=
  { id := "srp_muz_sg_ins"
    lexeme := Lexemes.srp_muz
    cell := ins_sg
    form := "mužem"
    morphs := ["mužem"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_selo_sg_nom : Form Cell :=
  { id := "srp_selo_sg_nom"
    lexeme := Lexemes.srp_selo
    cell := nom_sg
    form := "sèlo"
    morphs := ["sèlo"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_selo_sg_acc : Form Cell :=
  { id := "srp_selo_sg_acc"
    lexeme := Lexemes.srp_selo
    cell := acc_sg
    form := "sèlo"
    morphs := ["sèlo"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_selo_sg_gen : Form Cell :=
  { id := "srp_selo_sg_gen"
    lexeme := Lexemes.srp_selo
    cell := gen_sg
    form := "sèla"
    morphs := ["sèla"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_selo_sg_prep : Form Cell :=
  { id := "srp_selo_sg_prep"
    lexeme := Lexemes.srp_selo
    cell := prep_sg
    form := "sèlu"
    morphs := ["sèlu"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_selo_sg_dat : Form Cell :=
  { id := "srp_selo_sg_dat"
    lexeme := Lexemes.srp_selo
    cell := dat_sg
    form := "sèlu"
    morphs := ["sèlu"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_selo_sg_ins : Form Cell :=
  { id := "srp_selo_sg_ins"
    lexeme := Lexemes.srp_selo
    cell := ins_sg
    form := "sèlom"
    morphs := ["sèlom"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_srce_sg_nom : Form Cell :=
  { id := "srp_srce_sg_nom"
    lexeme := Lexemes.srp_srce
    cell := nom_sg
    form := "srce"
    morphs := ["srce"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_srce_sg_acc : Form Cell :=
  { id := "srp_srce_sg_acc"
    lexeme := Lexemes.srp_srce
    cell := acc_sg
    form := "srce"
    morphs := ["srce"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_srce_sg_gen : Form Cell :=
  { id := "srp_srce_sg_gen"
    lexeme := Lexemes.srp_srce
    cell := gen_sg
    form := "srca"
    morphs := ["srca"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_srce_sg_prep : Form Cell :=
  { id := "srp_srce_sg_prep"
    lexeme := Lexemes.srp_srce
    cell := prep_sg
    form := "srcu"
    morphs := ["srcu"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_srce_sg_dat : Form Cell :=
  { id := "srp_srce_sg_dat"
    lexeme := Lexemes.srp_srce
    cell := dat_sg
    form := "srcu"
    morphs := ["srcu"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_srce_sg_ins : Form Cell :=
  { id := "srp_srce_sg_ins"
    lexeme := Lexemes.srp_srce
    cell := ins_sg
    form := "srcem"
    morphs := ["srcem"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_ovca_sg_nom : Form Cell :=
  { id := "srp_ovca_sg_nom"
    lexeme := Lexemes.srp_ovca
    cell := nom_sg
    form := "òvca"
    morphs := ["òvca"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_ovca_sg_acc : Form Cell :=
  { id := "srp_ovca_sg_acc"
    lexeme := Lexemes.srp_ovca
    cell := acc_sg
    form := "òvcu"
    morphs := ["òvcu"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_ovca_sg_gen : Form Cell :=
  { id := "srp_ovca_sg_gen"
    lexeme := Lexemes.srp_ovca
    cell := gen_sg
    form := "òvcē"
    morphs := ["òvcē"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_ovca_sg_prep : Form Cell :=
  { id := "srp_ovca_sg_prep"
    lexeme := Lexemes.srp_ovca
    cell := prep_sg
    form := "òvci"
    morphs := ["òvci"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_ovca_sg_dat : Form Cell :=
  { id := "srp_ovca_sg_dat"
    lexeme := Lexemes.srp_ovca
    cell := dat_sg
    form := "òvci"
    morphs := ["òvci"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_ovca_sg_ins : Form Cell :=
  { id := "srp_ovca_sg_ins"
    lexeme := Lexemes.srp_ovca
    cell := ins_sg
    form := "òvcōm"
    morphs := ["òvcōm"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_smrt_sg_nom : Form Cell :=
  { id := "srp_smrt_sg_nom"
    lexeme := Lexemes.srp_smrt
    cell := nom_sg
    form := "smȑt"
    morphs := ["smȑt"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_smrt_sg_acc : Form Cell :=
  { id := "srp_smrt_sg_acc"
    lexeme := Lexemes.srp_smrt
    cell := acc_sg
    form := "smȑt"
    morphs := ["smȑt"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_smrt_sg_gen : Form Cell :=
  { id := "srp_smrt_sg_gen"
    lexeme := Lexemes.srp_smrt
    cell := gen_sg
    form := "smȑti"
    morphs := ["smȑti"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_smrt_sg_prep : Form Cell :=
  { id := "srp_smrt_sg_prep"
    lexeme := Lexemes.srp_smrt
    cell := prep_sg
    form := "smȑti"
    morphs := ["smȑti"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_smrt_sg_dat : Form Cell :=
  { id := "srp_smrt_sg_dat"
    lexeme := Lexemes.srp_smrt
    cell := dat_sg
    form := "smȑti"
    morphs := ["smȑti"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_smrt_sg_ins : Form Cell :=
  { id := "srp_smrt_sg_ins"
    lexeme := Lexemes.srp_smrt
    cell := ins_sg
    form := "smr̀ću"
    morphs := ["smr̀ću"]
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_sin_pl_nom : Form Cell :=
  { id := "srp_sin_pl_nom"
    lexeme := Lexemes.srp_sin
    cell := nom_pl
    form := "sȉnovi"
    morphs := ["sȉnovi"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_sin_pl_acc : Form Cell :=
  { id := "srp_sin_pl_acc"
    lexeme := Lexemes.srp_sin
    cell := acc_pl
    form := "sȉnove"
    morphs := ["sȉnove"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_sin_pl_gen : Form Cell :=
  { id := "srp_sin_pl_gen"
    lexeme := Lexemes.srp_sin
    cell := gen_pl
    form := "sinóvā"
    morphs := ["sinóvā"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_sin_pl_prep : Form Cell :=
  { id := "srp_sin_pl_prep"
    lexeme := Lexemes.srp_sin
    cell := prep_pl
    form := "sȉnovima"
    morphs := ["sȉnovima"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_sin_pl_dat : Form Cell :=
  { id := "srp_sin_pl_dat"
    lexeme := Lexemes.srp_sin
    cell := dat_pl
    form := "sȉnovima"
    morphs := ["sȉnovima"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_sin_pl_ins : Form Cell :=
  { id := "srp_sin_pl_ins"
    lexeme := Lexemes.srp_sin
    cell := ins_pl
    form := "sȉnovima"
    morphs := ["sȉnovima"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_grad_pl_nom : Form Cell :=
  { id := "srp_grad_pl_nom"
    lexeme := Lexemes.srp_grad
    cell := nom_pl
    form := "grȁdovi"
    morphs := ["grȁdovi"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_grad_pl_acc : Form Cell :=
  { id := "srp_grad_pl_acc"
    lexeme := Lexemes.srp_grad
    cell := acc_pl
    form := "grȁdove"
    morphs := ["grȁdove"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_grad_pl_gen : Form Cell :=
  { id := "srp_grad_pl_gen"
    lexeme := Lexemes.srp_grad
    cell := gen_pl
    form := "gradóvā"
    morphs := ["gradóvā"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_grad_pl_prep : Form Cell :=
  { id := "srp_grad_pl_prep"
    lexeme := Lexemes.srp_grad
    cell := prep_pl
    form := "grȁdovima"
    morphs := ["grȁdovima"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_grad_pl_dat : Form Cell :=
  { id := "srp_grad_pl_dat"
    lexeme := Lexemes.srp_grad
    cell := dat_pl
    form := "grȁdovima"
    morphs := ["grȁdovima"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_grad_pl_ins : Form Cell :=
  { id := "srp_grad_pl_ins"
    lexeme := Lexemes.srp_grad
    cell := ins_pl
    form := "grȁdovima"
    morphs := ["grȁdovima"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_muz_pl_nom : Form Cell :=
  { id := "srp_muz_pl_nom"
    lexeme := Lexemes.srp_muz
    cell := nom_pl
    form := "muževi"
    morphs := ["muževi"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_muz_pl_acc : Form Cell :=
  { id := "srp_muz_pl_acc"
    lexeme := Lexemes.srp_muz
    cell := acc_pl
    form := "muževe"
    morphs := ["muževe"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_muz_pl_gen : Form Cell :=
  { id := "srp_muz_pl_gen"
    lexeme := Lexemes.srp_muz
    cell := gen_pl
    form := "mȕžēvā"
    morphs := ["mȕžēvā"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_muz_pl_prep : Form Cell :=
  { id := "srp_muz_pl_prep"
    lexeme := Lexemes.srp_muz
    cell := prep_pl
    form := "muževima"
    morphs := ["muževima"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_muz_pl_dat : Form Cell :=
  { id := "srp_muz_pl_dat"
    lexeme := Lexemes.srp_muz
    cell := dat_pl
    form := "muževima"
    morphs := ["muževima"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_muz_pl_ins : Form Cell :=
  { id := "srp_muz_pl_ins"
    lexeme := Lexemes.srp_muz
    cell := ins_pl
    form := "muževima"
    morphs := ["muževima"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_selo_pl_nom : Form Cell :=
  { id := "srp_selo_pl_nom"
    lexeme := Lexemes.srp_selo
    cell := nom_pl
    form := "sȅla"
    morphs := ["sȅla"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_selo_pl_acc : Form Cell :=
  { id := "srp_selo_pl_acc"
    lexeme := Lexemes.srp_selo
    cell := acc_pl
    form := "sȅla"
    morphs := ["sȅla"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_selo_pl_gen : Form Cell :=
  { id := "srp_selo_pl_gen"
    lexeme := Lexemes.srp_selo
    cell := gen_pl
    form := "sêlā"
    morphs := ["sêlā"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_selo_pl_prep : Form Cell :=
  { id := "srp_selo_pl_prep"
    lexeme := Lexemes.srp_selo
    cell := prep_pl
    form := "sȅlima"
    morphs := ["sȅlima"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_selo_pl_dat : Form Cell :=
  { id := "srp_selo_pl_dat"
    lexeme := Lexemes.srp_selo
    cell := dat_pl
    form := "sȅlima"
    morphs := ["sȅlima"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_selo_pl_ins : Form Cell :=
  { id := "srp_selo_pl_ins"
    lexeme := Lexemes.srp_selo
    cell := ins_pl
    form := "sȅlima"
    morphs := ["sȅlima"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_srce_pl_nom : Form Cell :=
  { id := "srp_srce_pl_nom"
    lexeme := Lexemes.srp_srce
    cell := nom_pl
    form := "srca"
    morphs := ["srca"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_srce_pl_acc : Form Cell :=
  { id := "srp_srce_pl_acc"
    lexeme := Lexemes.srp_srce
    cell := acc_pl
    form := "srca"
    morphs := ["srca"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_srce_pl_gen : Form Cell :=
  { id := "srp_srce_pl_gen"
    lexeme := Lexemes.srp_srce
    cell := gen_pl
    form := "sr̂cā"
    morphs := ["sr̂cā"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_srce_pl_prep : Form Cell :=
  { id := "srp_srce_pl_prep"
    lexeme := Lexemes.srp_srce
    cell := prep_pl
    form := "srcima"
    morphs := ["srcima"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_srce_pl_dat : Form Cell :=
  { id := "srp_srce_pl_dat"
    lexeme := Lexemes.srp_srce
    cell := dat_pl
    form := "srcima"
    morphs := ["srcima"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_srce_pl_ins : Form Cell :=
  { id := "srp_srce_pl_ins"
    lexeme := Lexemes.srp_srce
    cell := ins_pl
    form := "srcima"
    morphs := ["srcima"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_ovca_pl_nom : Form Cell :=
  { id := "srp_ovca_pl_nom"
    lexeme := Lexemes.srp_ovca
    cell := nom_pl
    form := "ôvce"
    morphs := ["ôvce"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_ovca_pl_acc : Form Cell :=
  { id := "srp_ovca_pl_acc"
    lexeme := Lexemes.srp_ovca
    cell := acc_pl
    form := "ôvce"
    morphs := ["ôvce"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_ovca_pl_gen : Form Cell :=
  { id := "srp_ovca_pl_gen"
    lexeme := Lexemes.srp_ovca
    cell := gen_pl
    form := "ovácā"
    morphs := ["ovácā"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_ovca_pl_prep : Form Cell :=
  { id := "srp_ovca_pl_prep"
    lexeme := Lexemes.srp_ovca
    cell := prep_pl
    form := "óvcama"
    morphs := ["óvcama"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_ovca_pl_dat : Form Cell :=
  { id := "srp_ovca_pl_dat"
    lexeme := Lexemes.srp_ovca
    cell := dat_pl
    form := "óvcama"
    morphs := ["óvcama"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_ovca_pl_ins : Form Cell :=
  { id := "srp_ovca_pl_ins"
    lexeme := Lexemes.srp_ovca
    cell := ins_pl
    form := "óvcama"
    morphs := ["óvcama"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_smrt_pl_nom : Form Cell :=
  { id := "srp_smrt_pl_nom"
    lexeme := Lexemes.srp_smrt
    cell := nom_pl
    form := "smȑti"
    morphs := ["smȑti"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_smrt_pl_acc : Form Cell :=
  { id := "srp_smrt_pl_acc"
    lexeme := Lexemes.srp_smrt
    cell := acc_pl
    form := "smȑti"
    morphs := ["smȑti"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_smrt_pl_gen : Form Cell :=
  { id := "srp_smrt_pl_gen"
    lexeme := Lexemes.srp_smrt
    cell := gen_pl
    form := "smr̂tī"
    morphs := ["smr̂tī"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_smrt_pl_prep : Form Cell :=
  { id := "srp_smrt_pl_prep"
    lexeme := Lexemes.srp_smrt
    cell := prep_pl
    form := "smȑtima"
    morphs := ["smȑtima"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_smrt_pl_dat : Form Cell :=
  { id := "srp_smrt_pl_dat"
    lexeme := Lexemes.srp_smrt
    cell := dat_pl
    form := "smȑtima"
    morphs := ["smȑtima"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_smrt_pl_ins : Form Cell :=
  { id := "srp_smrt_pl_ins"
    lexeme := Lexemes.srp_smrt
    cell := ins_pl
    form := "smȑtima"
    morphs := ["smȑtima"]
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_ja_nom : Form Cell :=
  { id := "srp_ja_nom"
    lexeme := Lexemes.srp_ja
    cell := nom_sg
    form := "ja"
    morphs := ["ja"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ja_acc : Form Cell :=
  { id := "srp_ja_acc"
    lexeme := Lexemes.srp_ja
    cell := acc_sg
    form := "mene"
    morphs := ["mene"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ja_gen : Form Cell :=
  { id := "srp_ja_gen"
    lexeme := Lexemes.srp_ja
    cell := gen_sg
    form := "mene"
    morphs := ["mene"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ja_prep : Form Cell :=
  { id := "srp_ja_prep"
    lexeme := Lexemes.srp_ja
    cell := prep_sg
    form := "meni"
    morphs := ["meni"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ja_dat : Form Cell :=
  { id := "srp_ja_dat"
    lexeme := Lexemes.srp_ja
    cell := dat_sg
    form := "meni"
    morphs := ["meni"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ja_ins : Form Cell :=
  { id := "srp_ja_ins"
    lexeme := Lexemes.srp_ja
    cell := ins_sg
    form := "mnom"
    morphs := ["mnom"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ti_nom : Form Cell :=
  { id := "srp_ti_nom"
    lexeme := Lexemes.srp_ti
    cell := nom_sg
    form := "ti"
    morphs := ["ti"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ti_acc : Form Cell :=
  { id := "srp_ti_acc"
    lexeme := Lexemes.srp_ti
    cell := acc_sg
    form := "tebe"
    morphs := ["tebe"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ti_gen : Form Cell :=
  { id := "srp_ti_gen"
    lexeme := Lexemes.srp_ti
    cell := gen_sg
    form := "tebe"
    morphs := ["tebe"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ti_prep : Form Cell :=
  { id := "srp_ti_prep"
    lexeme := Lexemes.srp_ti
    cell := prep_sg
    form := "tebi"
    morphs := ["tebi"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ti_dat : Form Cell :=
  { id := "srp_ti_dat"
    lexeme := Lexemes.srp_ti
    cell := dat_sg
    form := "tebi"
    morphs := ["tebi"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ti_ins : Form Cell :=
  { id := "srp_ti_ins"
    lexeme := Lexemes.srp_ti
    cell := ins_sg
    form := "tobom"
    morphs := ["tobom"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_on_nom : Form Cell :=
  { id := "srp_on_nom"
    lexeme := Lexemes.srp_on
    cell := nom_sg
    form := "on/ono"
    morphs := ["on/ono"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_on_acc : Form Cell :=
  { id := "srp_on_acc"
    lexeme := Lexemes.srp_on
    cell := acc_sg
    form := "njega"
    morphs := ["njega"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_on_gen : Form Cell :=
  { id := "srp_on_gen"
    lexeme := Lexemes.srp_on
    cell := gen_sg
    form := "njega"
    morphs := ["njega"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_on_prep : Form Cell :=
  { id := "srp_on_prep"
    lexeme := Lexemes.srp_on
    cell := prep_sg
    form := "njemu"
    morphs := ["njemu"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_on_dat : Form Cell :=
  { id := "srp_on_dat"
    lexeme := Lexemes.srp_on
    cell := dat_sg
    form := "njemu"
    morphs := ["njemu"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_on_ins : Form Cell :=
  { id := "srp_on_ins"
    lexeme := Lexemes.srp_on
    cell := ins_sg
    form := "njim"
    morphs := ["njim"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ona_nom : Form Cell :=
  { id := "srp_ona_nom"
    lexeme := Lexemes.srp_ona
    cell := nom_sg
    form := "ona"
    morphs := ["ona"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ona_acc : Form Cell :=
  { id := "srp_ona_acc"
    lexeme := Lexemes.srp_ona
    cell := acc_sg
    form := "nju"
    morphs := ["nju"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ona_gen : Form Cell :=
  { id := "srp_ona_gen"
    lexeme := Lexemes.srp_ona
    cell := gen_sg
    form := "nje"
    morphs := ["nje"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ona_prep : Form Cell :=
  { id := "srp_ona_prep"
    lexeme := Lexemes.srp_ona
    cell := prep_sg
    form := "njoj"
    morphs := ["njoj"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ona_dat : Form Cell :=
  { id := "srp_ona_dat"
    lexeme := Lexemes.srp_ona
    cell := dat_sg
    form := "njoj"
    morphs := ["njoj"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ona_ins : Form Cell :=
  { id := "srp_ona_ins"
    lexeme := Lexemes.srp_ona
    cell := ins_sg
    form := "njom"
    morphs := ["njom"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_mi_nom : Form Cell :=
  { id := "srp_mi_nom"
    lexeme := Lexemes.srp_mi
    cell := nom_pl
    form := "mi"
    morphs := ["mi"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_mi_acc : Form Cell :=
  { id := "srp_mi_acc"
    lexeme := Lexemes.srp_mi
    cell := acc_pl
    form := "nas"
    morphs := ["nas"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_mi_gen : Form Cell :=
  { id := "srp_mi_gen"
    lexeme := Lexemes.srp_mi
    cell := gen_pl
    form := "nas"
    morphs := ["nas"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_mi_prep : Form Cell :=
  { id := "srp_mi_prep"
    lexeme := Lexemes.srp_mi
    cell := prep_pl
    form := "nama"
    morphs := ["nama"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_mi_dat : Form Cell :=
  { id := "srp_mi_dat"
    lexeme := Lexemes.srp_mi
    cell := dat_pl
    form := "nama"
    morphs := ["nama"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_mi_ins : Form Cell :=
  { id := "srp_mi_ins"
    lexeme := Lexemes.srp_mi
    cell := ins_pl
    form := "nama"
    morphs := ["nama"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_vi_nom : Form Cell :=
  { id := "srp_vi_nom"
    lexeme := Lexemes.srp_vi
    cell := nom_pl
    form := "vi"
    morphs := ["vi"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_vi_acc : Form Cell :=
  { id := "srp_vi_acc"
    lexeme := Lexemes.srp_vi
    cell := acc_pl
    form := "vas"
    morphs := ["vas"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_vi_gen : Form Cell :=
  { id := "srp_vi_gen"
    lexeme := Lexemes.srp_vi
    cell := gen_pl
    form := "vas"
    morphs := ["vas"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_vi_prep : Form Cell :=
  { id := "srp_vi_prep"
    lexeme := Lexemes.srp_vi
    cell := prep_pl
    form := "vama"
    morphs := ["vama"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_vi_dat : Form Cell :=
  { id := "srp_vi_dat"
    lexeme := Lexemes.srp_vi
    cell := dat_pl
    form := "vama"
    morphs := ["vama"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_vi_ins : Form Cell :=
  { id := "srp_vi_ins"
    lexeme := Lexemes.srp_vi
    cell := ins_pl
    form := "vama"
    morphs := ["vama"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_oni_nom : Form Cell :=
  { id := "srp_oni_nom"
    lexeme := Lexemes.srp_oni
    cell := nom_pl
    form := "oni/ona/one"
    morphs := ["oni/ona/one"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_oni_acc : Form Cell :=
  { id := "srp_oni_acc"
    lexeme := Lexemes.srp_oni
    cell := acc_pl
    form := "njih"
    morphs := ["njih"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_oni_gen : Form Cell :=
  { id := "srp_oni_gen"
    lexeme := Lexemes.srp_oni
    cell := gen_pl
    form := "njih"
    morphs := ["njih"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_oni_prep : Form Cell :=
  { id := "srp_oni_prep"
    lexeme := Lexemes.srp_oni
    cell := prep_pl
    form := "njima"
    morphs := ["njima"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_oni_dat : Form Cell :=
  { id := "srp_oni_dat"
    lexeme := Lexemes.srp_oni
    cell := dat_pl
    form := "njima"
    morphs := ["njima"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_oni_ins : Form Cell :=
  { id := "srp_oni_ins"
    lexeme := Lexemes.srp_oni
    cell := ins_pl
    form := "njima"
    morphs := ["njima"]
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def slv_miza_du_nom : Form Cell :=
  { id := "slv_miza_du_nom"
    lexeme := Lexemes.slv_miza
    cell := nom_du
    form := "mízi"
    morphs := ["míz", "i"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_miza_du_acc : Form Cell :=
  { id := "slv_miza_du_acc"
    lexeme := Lexemes.slv_miza
    cell := acc_du
    form := "mízi"
    morphs := ["míz", "i"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_miza_du_gen : Form Cell :=
  { id := "slv_miza_du_gen"
    lexeme := Lexemes.slv_miza
    cell := gen_du
    form := "mîz"
    morphs := ["mîz"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_miza_du_prep : Form Cell :=
  { id := "slv_miza_du_prep"
    lexeme := Lexemes.slv_miza
    cell := prep_du
    form := "mízah"
    morphs := ["míz", "ah"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_miza_du_dat : Form Cell :=
  { id := "slv_miza_du_dat"
    lexeme := Lexemes.slv_miza
    cell := dat_du
    form := "mízama"
    morphs := ["míz", "ama"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_miza_du_ins : Form Cell :=
  { id := "slv_miza_du_ins"
    lexeme := Lexemes.slv_miza
    cell := ins_du
    form := "mízama"
    morphs := ["míz", "ama"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_breskev_sg_nom : Form Cell :=
  { id := "slv_breskev_sg_nom"
    lexeme := Lexemes.slv_breskev
    cell := nom_sg
    form := "brêskev"
    morphs := ["brêskev", "ø"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_breskev_sg_acc : Form Cell :=
  { id := "slv_breskev_sg_acc"
    lexeme := Lexemes.slv_breskev
    cell := acc_sg
    form := "brêskev"
    morphs := ["brêskev", "ø"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_breskev_sg_gen : Form Cell :=
  { id := "slv_breskev_sg_gen"
    lexeme := Lexemes.slv_breskev
    cell := gen_sg
    form := "brêskve"
    morphs := ["brêskv", "e"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_breskev_sg_prep : Form Cell :=
  { id := "slv_breskev_sg_prep"
    lexeme := Lexemes.slv_breskev
    cell := prep_sg
    form := "brêskvi"
    morphs := ["brêskv", "i"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_breskev_sg_dat : Form Cell :=
  { id := "slv_breskev_sg_dat"
    lexeme := Lexemes.slv_breskev
    cell := dat_sg
    form := "brêskvi"
    morphs := ["brêskv", "i"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_breskev_sg_ins : Form Cell :=
  { id := "slv_breskev_sg_ins"
    lexeme := Lexemes.slv_breskev
    cell := ins_sg
    form := "brêskvijo"
    morphs := ["brêskv", "ijo"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_breskev_pl_nom : Form Cell :=
  { id := "slv_breskev_pl_nom"
    lexeme := Lexemes.slv_breskev
    cell := nom_pl
    form := "brêskve"
    morphs := ["brêskv", "e"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_breskev_pl_acc : Form Cell :=
  { id := "slv_breskev_pl_acc"
    lexeme := Lexemes.slv_breskev
    cell := acc_pl
    form := "brêskve"
    morphs := ["brêskv", "e"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_breskev_pl_gen : Form Cell :=
  { id := "slv_breskev_pl_gen"
    lexeme := Lexemes.slv_breskev
    cell := gen_pl
    form := "brêskv"
    morphs := ["brêskv", "ø"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_breskev_pl_prep : Form Cell :=
  { id := "slv_breskev_pl_prep"
    lexeme := Lexemes.slv_breskev
    cell := prep_pl
    form := "brêskvah"
    morphs := ["brêskv", "ah"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_breskev_pl_dat : Form Cell :=
  { id := "slv_breskev_pl_dat"
    lexeme := Lexemes.slv_breskev
    cell := dat_pl
    form := "brêskvam"
    morphs := ["brêskv", "am"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_breskev_pl_ins : Form Cell :=
  { id := "slv_breskev_pl_ins"
    lexeme := Lexemes.slv_breskev
    cell := ins_pl
    form := "brêskvami"
    morphs := ["brêskv", "ami"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_jabolko_sg_nom : Form Cell :=
  { id := "slv_jabolko_sg_nom"
    lexeme := Lexemes.slv_jabolko
    cell := nom_sg
    form := "jábolko"
    morphs := ["jábolk", "o"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_jabolko_sg_acc : Form Cell :=
  { id := "slv_jabolko_sg_acc"
    lexeme := Lexemes.slv_jabolko
    cell := acc_sg
    form := "jábolko"
    morphs := ["jábolk", "o"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_jabolko_sg_gen : Form Cell :=
  { id := "slv_jabolko_sg_gen"
    lexeme := Lexemes.slv_jabolko
    cell := gen_sg
    form := "jábolka"
    morphs := ["jábolk", "a"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_jabolko_sg_prep : Form Cell :=
  { id := "slv_jabolko_sg_prep"
    lexeme := Lexemes.slv_jabolko
    cell := prep_sg
    form := "jábolku"
    morphs := ["jábolk", "u"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_jabolko_sg_dat : Form Cell :=
  { id := "slv_jabolko_sg_dat"
    lexeme := Lexemes.slv_jabolko
    cell := dat_sg
    form := "jábolku"
    morphs := ["jábolk", "u"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_jabolko_sg_ins : Form Cell :=
  { id := "slv_jabolko_sg_ins"
    lexeme := Lexemes.slv_jabolko
    cell := ins_sg
    form := "jábolkom"
    morphs := ["jábolk", "om"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_kmet_du_nom : Form Cell :=
  { id := "slv_kmet_du_nom"
    lexeme := Lexemes.slv_kmet
    cell := nom_du
    form := "kmèta"
    morphs := ["kmèt", "a"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_kmet_du_acc : Form Cell :=
  { id := "slv_kmet_du_acc"
    lexeme := Lexemes.slv_kmet
    cell := acc_du
    form := "kmèta"
    morphs := ["kmèt", "a"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_kmet_du_gen : Form Cell :=
  { id := "slv_kmet_du_gen"
    lexeme := Lexemes.slv_kmet
    cell := gen_du
    form := "kmêtov"
    morphs := ["kmêt", "ov"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_kmet_du_prep : Form Cell :=
  { id := "slv_kmet_du_prep"
    lexeme := Lexemes.slv_kmet
    cell := prep_du
    form := "kmētih"
    morphs := ["kmēt", "ih"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_kmet_du_dat : Form Cell :=
  { id := "slv_kmet_du_dat"
    lexeme := Lexemes.slv_kmet
    cell := dat_du
    form := "kmétoma"
    morphs := ["kmét", "oma"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_kmet_du_ins : Form Cell :=
  { id := "slv_kmet_du_ins"
    lexeme := Lexemes.slv_kmet
    cell := ins_du
    form := "kmétoma"
    morphs := ["kmét", "oma"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_kmet_sg_nom : Form Cell :=
  { id := "slv_kmet_sg_nom"
    lexeme := Lexemes.slv_kmet
    cell := nom_sg
    form := "kmèt"
    morphs := ["kmèt", "ø"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_kmet_sg_acc : Form Cell :=
  { id := "slv_kmet_sg_acc"
    lexeme := Lexemes.slv_kmet
    cell := acc_sg
    form := "kméta"
    morphs := ["kmét", "a"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_kmet_sg_gen : Form Cell :=
  { id := "slv_kmet_sg_gen"
    lexeme := Lexemes.slv_kmet
    cell := gen_sg
    form := "kméta"
    morphs := ["kmét", "a"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_kmet_sg_prep : Form Cell :=
  { id := "slv_kmet_sg_prep"
    lexeme := Lexemes.slv_kmet
    cell := prep_sg
    form := "kmêtu"
    morphs := ["kmêt", "u"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_kmet_sg_dat : Form Cell :=
  { id := "slv_kmet_sg_dat"
    lexeme := Lexemes.slv_kmet
    cell := dat_sg
    form := "kmétu"
    morphs := ["kmét", "u"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_kmet_sg_ins : Form Cell :=
  { id := "slv_kmet_sg_ins"
    lexeme := Lexemes.slv_kmet
    cell := ins_sg
    form := "kmétom"
    morphs := ["kmét", "om"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_jaz_nom : Form Cell :=
  { id := "slv_jaz_nom"
    lexeme := Lexemes.slv_jaz
    cell := nom_sg
    form := "jàz"
    morphs := ["jàz"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_jaz_acc : Form Cell :=
  { id := "slv_jaz_acc"
    lexeme := Lexemes.slv_jaz
    cell := acc_sg
    form := "mȩ́ne"
    morphs := ["mȩ́n", "e"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_jaz_gen : Form Cell :=
  { id := "slv_jaz_gen"
    lexeme := Lexemes.slv_jaz
    cell := gen_sg
    form := "mȩ́ne"
    morphs := ["mȩ́n", "e"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_jaz_prep : Form Cell :=
  { id := "slv_jaz_prep"
    lexeme := Lexemes.slv_jaz
    cell := prep_sg
    form := "mȩ́ni"
    morphs := ["mȩ́n", "i"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_jaz_dat : Form Cell :=
  { id := "slv_jaz_dat"
    lexeme := Lexemes.slv_jaz
    cell := dat_sg
    form := "mȩ́ni"
    morphs := ["mȩ́n", "i"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_jaz_ins : Form Cell :=
  { id := "slv_jaz_ins"
    lexeme := Lexemes.slv_jaz
    cell := ins_sg
    form := "menój"
    morphs := ["men", "ój"]
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_moj_mpl_nom : Form Cell :=
  { id := "slv_moj_mpl_nom"
    lexeme := Lexemes.slv_moj
    cell := nom_pl_m
    form := "mo̧ji"
    morphs := ["mo̧j", "i"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_moj_mpl_acc : Form Cell :=
  { id := "slv_moj_mpl_acc"
    lexeme := Lexemes.slv_moj
    cell := acc_pl_m
    form := "mo̧ji"
    morphs := ["mo̧j", "i"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_moj_mpl_gen : Form Cell :=
  { id := "slv_moj_mpl_gen"
    lexeme := Lexemes.slv_moj
    cell := gen_pl_m
    form := "mo̧jih"
    morphs := ["mo̧j", "ih"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_moj_mpl_prep : Form Cell :=
  { id := "slv_moj_mpl_prep"
    lexeme := Lexemes.slv_moj
    cell := prep_pl_m
    form := "mo̧jih"
    morphs := ["mo̧j", "ih"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_moj_mpl_dat : Form Cell :=
  { id := "slv_moj_mpl_dat"
    lexeme := Lexemes.slv_moj
    cell := dat_pl_m
    form := "mo̧jim"
    morphs := ["mo̧j", "im"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_moj_mpl_ins : Form Cell :=
  { id := "slv_moj_mpl_ins"
    lexeme := Lexemes.slv_moj
    cell := ins_pl_m
    form := "mo̧jimi"
    morphs := ["mo̧j", "imi"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_dva_nom : Form Cell :=
  { id := "slv_dva_nom"
    lexeme := Lexemes.slv_dva
    cell := nom_du
    form := "dvâ"
    morphs := ["dv", "â"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_dva_acc : Form Cell :=
  { id := "slv_dva_acc"
    lexeme := Lexemes.slv_dva
    cell := acc_du
    form := "dvâ"
    morphs := ["dv", "â"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_dva_gen : Form Cell :=
  { id := "slv_dva_gen"
    lexeme := Lexemes.slv_dva
    cell := gen_du
    form := "dvēh"
    morphs := ["dv", "ēh"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_dva_prep : Form Cell :=
  { id := "slv_dva_prep"
    lexeme := Lexemes.slv_dva
    cell := prep_du
    form := "dvēh"
    morphs := ["dv", "ēh"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_dva_dat : Form Cell :=
  { id := "slv_dva_dat"
    lexeme := Lexemes.slv_dva
    cell := dat_du
    form := "dvēma"
    morphs := ["dv", "ēma"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_dva_ins : Form Cell :=
  { id := "slv_dva_ins"
    lexeme := Lexemes.slv_dva
    cell := ins_du
    form := "dvēma"
    morphs := ["dv", "ēma"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_mi_nom : Form Cell :=
  { id := "slv_mi_nom"
    lexeme := Lexemes.slv_mi
    cell := nom_pl
    form := "mî"
    morphs := ["mî"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_mi_acc : Form Cell :=
  { id := "slv_mi_acc"
    lexeme := Lexemes.slv_mi
    cell := acc_pl
    form := "nàs"
    morphs := ["nà", "s"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_mi_gen : Form Cell :=
  { id := "slv_mi_gen"
    lexeme := Lexemes.slv_mi
    cell := gen_pl
    form := "nàs"
    morphs := ["nà", "s"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_mi_prep : Form Cell :=
  { id := "slv_mi_prep"
    lexeme := Lexemes.slv_mi
    cell := prep_pl
    form := "nàs"
    morphs := ["nà", "s"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_mi_dat : Form Cell :=
  { id := "slv_mi_dat"
    lexeme := Lexemes.slv_mi
    cell := dat_pl
    form := "nàm"
    morphs := ["nàm"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_mi_ins : Form Cell :=
  { id := "slv_mi_ins"
    lexeme := Lexemes.slv_mi
    cell := ins_pl
    form := "na̧mi"
    morphs := ["na̧mi"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_midva_nom : Form Cell :=
  { id := "slv_midva_nom"
    lexeme := Lexemes.slv_midva
    cell := nom_du
    form := "mîdva"
    morphs := ["mîdva"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_midva_acc : Form Cell :=
  { id := "slv_midva_acc"
    lexeme := Lexemes.slv_midva
    cell := acc_du
    form := "náju"
    morphs := ["ná", "ju"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_midva_gen : Form Cell :=
  { id := "slv_midva_gen"
    lexeme := Lexemes.slv_midva
    cell := gen_du
    form := "náju"
    morphs := ["ná", "ju"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_midva_prep : Form Cell :=
  { id := "slv_midva_prep"
    lexeme := Lexemes.slv_midva
    cell := prep_du
    form := "náju"
    morphs := ["ná", "ju"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_midva_dat : Form Cell :=
  { id := "slv_midva_dat"
    lexeme := Lexemes.slv_midva
    cell := dat_du
    form := "náma"
    morphs := ["ná", "ma"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_midva_ins : Form Cell :=
  { id := "slv_midva_ins"
    lexeme := Lexemes.slv_midva
    cell := ins_du
    form := "náma"
    morphs := ["ná", "ma"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_nit_sg_nom : Form Cell :=
  { id := "slv_nit_sg_nom"
    lexeme := Lexemes.slv_nit
    cell := nom_sg
    form := "nìt"
    morphs := ["nìt"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_nit_sg_acc : Form Cell :=
  { id := "slv_nit_sg_acc"
    lexeme := Lexemes.slv_nit
    cell := acc_sg
    form := "nìt"
    morphs := ["nìt"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_nit_sg_gen : Form Cell :=
  { id := "slv_nit_sg_gen"
    lexeme := Lexemes.slv_nit
    cell := gen_sg
    form := "níti"
    morphs := ["nít", "i"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_nit_sg_prep : Form Cell :=
  { id := "slv_nit_sg_prep"
    lexeme := Lexemes.slv_nit
    cell := prep_sg
    form := "níti"
    morphs := ["nít", "i"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_nit_sg_dat : Form Cell :=
  { id := "slv_nit_sg_dat"
    lexeme := Lexemes.slv_nit
    cell := dat_sg
    form := "níti"
    morphs := ["nít", "i"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_nit_sg_ins : Form Cell :=
  { id := "slv_nit_sg_ins"
    lexeme := Lexemes.slv_nit
    cell := ins_sg
    form := "nítjo"
    morphs := ["nít", "jo"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_gospa_sg_nom : Form Cell :=
  { id := "slv_gospa_sg_nom"
    lexeme := Lexemes.slv_gospa
    cell := nom_sg
    form := "gospá"
    morphs := ["gosp", "á"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_gospa_sg_acc : Form Cell :=
  { id := "slv_gospa_sg_acc"
    lexeme := Lexemes.slv_gospa
    cell := acc_sg
    form := "gospó"
    morphs := ["gosp", "ó"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_gospa_sg_gen : Form Cell :=
  { id := "slv_gospa_sg_gen"
    lexeme := Lexemes.slv_gospa
    cell := gen_sg
    form := "gospé"
    morphs := ["gosp", "é"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_gospa_sg_prep : Form Cell :=
  { id := "slv_gospa_sg_prep"
    lexeme := Lexemes.slv_gospa
    cell := prep_sg
    form := "gospé"
    morphs := ["gosp", "é"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_gospa_sg_dat : Form Cell :=
  { id := "slv_gospa_sg_dat"
    lexeme := Lexemes.slv_gospa
    cell := dat_sg
    form := "gospé"
    morphs := ["gosp", "é"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_gospa_sg_ins : Form Cell :=
  { id := "slv_gospa_sg_ins"
    lexeme := Lexemes.slv_gospa
    cell := ins_sg
    form := "gospó"
    morphs := ["gosp", "ó"]
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_dan_du_nom : Form Cell :=
  { id := "slv_dan_du_nom"
    lexeme := Lexemes.slv_dan
    cell := nom_du
    form := "dní"
    morphs := ["dn", "í"]
    source := [
      ⟨"caha-2009", "(17)"⟩
    ] }

def slv_dan_du_acc : Form Cell :=
  { id := "slv_dan_du_acc"
    lexeme := Lexemes.slv_dan
    cell := acc_du
    form := "dní"
    morphs := ["dn", "í"]
    source := [
      ⟨"caha-2009", "(17)"⟩
    ] }

def slv_dan_du_gen : Form Cell :=
  { id := "slv_dan_du_gen"
    lexeme := Lexemes.slv_dan
    cell := gen_du
    form := "dní"
    morphs := ["dn", "í"]
    source := [
      ⟨"caha-2009", "(17)"⟩
    ] }

def slv_dan_du_prep : Form Cell :=
  { id := "slv_dan_du_prep"
    lexeme := Lexemes.slv_dan
    cell := prep_du
    form := "dnéh"
    morphs := ["dn", "éh"]
    source := [
      ⟨"caha-2009", "(17)"⟩
    ] }

def slv_dan_du_dat : Form Cell :=
  { id := "slv_dan_du_dat"
    lexeme := Lexemes.slv_dan
    cell := dat_du
    form := "dnéma"
    morphs := ["dn", "éma"]
    source := [
      ⟨"caha-2009", "(17)"⟩
    ] }

def slv_dan_du_ins : Form Cell :=
  { id := "slv_dan_du_ins"
    lexeme := Lexemes.slv_dan
    cell := ins_du
    form := "dnéma"
    morphs := ["dn", "éma"]
    source := [
      ⟨"caha-2009", "(17)"⟩
    ] }

def slv_racunovodja_sg_nom : Form Cell :=
  { id := "slv_racunovodja_sg_nom"
    lexeme := Lexemes.slv_racunovodja
    cell := nom_sg
    form := "računovodja"
    morphs := ["računovod", "ja"]
    source := [
      ⟨"caha-2009", "(17)"⟩
    ] }

def slv_racunovodja_sg_acc : Form Cell :=
  { id := "slv_racunovodja_sg_acc"
    lexeme := Lexemes.slv_racunovodja
    cell := acc_sg
    form := "računovodja"
    morphs := ["računovod", "ja"]
    source := [
      ⟨"caha-2009", "(17)"⟩
    ] }

def slv_racunovodja_sg_gen : Form Cell :=
  { id := "slv_racunovodja_sg_gen"
    lexeme := Lexemes.slv_racunovodja
    cell := gen_sg
    form := "računovodja"
    morphs := ["računovod", "ja"]
    source := [
      ⟨"caha-2009", "(17)"⟩
    ] }

def slv_racunovodja_sg_prep : Form Cell :=
  { id := "slv_racunovodja_sg_prep"
    lexeme := Lexemes.slv_racunovodja
    cell := prep_sg
    form := "računovodju"
    morphs := ["računovod", "ju"]
    source := [
      ⟨"caha-2009", "(17)"⟩
    ] }

def slv_racunovodja_sg_dat : Form Cell :=
  { id := "slv_racunovodja_sg_dat"
    lexeme := Lexemes.slv_racunovodja
    cell := dat_sg
    form := "računovodju"
    morphs := ["računovod", "ju"]
    source := [
      ⟨"caha-2009", "(17)"⟩
    ] }

def slv_racunovodja_sg_ins : Form Cell :=
  { id := "slv_racunovodja_sg_ins"
    lexeme := Lexemes.slv_racunovodja
    cell := ins_sg
    form := "računovodjem"
    morphs := ["računovod", "jem"]
    source := [
      ⟨"caha-2009", "(17)"⟩
    ] }

def slv_ta_n_nom : Form Cell :=
  { id := "slv_ta_n_nom"
    lexeme := Lexemes.slv_ta
    cell := nom_sg_n
    form := "tô"
    morphs := ["tô"]
    source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_ta_n_acc : Form Cell :=
  { id := "slv_ta_n_acc"
    lexeme := Lexemes.slv_ta
    cell := acc_sg_n
    form := "tô"
    morphs := ["tô"]
    source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_ta_n_gen : Form Cell :=
  { id := "slv_ta_n_gen"
    lexeme := Lexemes.slv_ta
    cell := gen_sg_n
    form := "têga"
    morphs := ["têga"]
    source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_ta_n_prep : Form Cell :=
  { id := "slv_ta_n_prep"
    lexeme := Lexemes.slv_ta
    cell := prep_sg_n
    form := "têm"
    morphs := ["têm"]
    source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_ta_n_dat : Form Cell :=
  { id := "slv_ta_n_dat"
    lexeme := Lexemes.slv_ta
    cell := dat_sg_n
    form := "têmu"
    morphs := ["têmu"]
    source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_ta_n_ins : Form Cell :=
  { id := "slv_ta_n_ins"
    lexeme := Lexemes.slv_ta
    cell := ins_sg_n
    form := "têm"
    morphs := ["têm"]
    source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_potnik_pl_nom : Form Cell :=
  { id := "slv_potnik_pl_nom"
    lexeme := Lexemes.slv_potnik
    cell := nom_pl
    form := "pótniki"
    morphs := ["pótnik", "i"]
    source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_potnik_pl_acc : Form Cell :=
  { id := "slv_potnik_pl_acc"
    lexeme := Lexemes.slv_potnik
    cell := acc_pl
    form := "pótnike"
    morphs := ["pótnik", "e"]
    source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_potnik_pl_gen : Form Cell :=
  { id := "slv_potnik_pl_gen"
    lexeme := Lexemes.slv_potnik
    cell := gen_pl
    form := "pótnikov"
    morphs := ["pótnik", "ov"]
    source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_potnik_pl_prep : Form Cell :=
  { id := "slv_potnik_pl_prep"
    lexeme := Lexemes.slv_potnik
    cell := prep_pl
    form := "pótnikih"
    morphs := ["pótnik", "ih"]
    source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_potnik_pl_dat : Form Cell :=
  { id := "slv_potnik_pl_dat"
    lexeme := Lexemes.slv_potnik
    cell := dat_pl
    form := "pótnikom"
    morphs := ["pótnik", "om"]
    source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_potnik_pl_ins : Form Cell :=
  { id := "slv_potnik_pl_ins"
    lexeme := Lexemes.slv_potnik
    cell := ins_pl
    form := "pótniki"
    morphs := ["pótnik", "i"]
    source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_ta_f_nom : Form Cell :=
  { id := "slv_ta_f_nom"
    lexeme := Lexemes.slv_ta
    cell := nom_sg_f
    form := "tâ"
    morphs := ["tâ"]
    source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_ta_f_acc : Form Cell :=
  { id := "slv_ta_f_acc"
    lexeme := Lexemes.slv_ta
    cell := acc_sg_f
    form := "tô"
    morphs := ["tô"]
    source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_ta_f_gen : Form Cell :=
  { id := "slv_ta_f_gen"
    lexeme := Lexemes.slv_ta
    cell := gen_sg_f
    form := "tê"
    morphs := ["tê"]
    source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_ta_f_prep : Form Cell :=
  { id := "slv_ta_f_prep"
    lexeme := Lexemes.slv_ta
    cell := prep_sg_f
    form := "têj"
    morphs := ["têj"]
    source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_ta_f_dat : Form Cell :=
  { id := "slv_ta_f_dat"
    lexeme := Lexemes.slv_ta
    cell := dat_sg_f
    form := "têj"
    morphs := ["têj"]
    source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_ta_f_ins : Form Cell :=
  { id := "slv_ta_f_ins"
    lexeme := Lexemes.slv_ta
    cell := ins_sg_f
    form := "tô"
    morphs := ["tô"]
    source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_tisti_n_nom : Form Cell :=
  { id := "slv_tisti_n_nom"
    lexeme := Lexemes.slv_tisti
    cell := nom_sg_n
    form := "tîsto"
    morphs := ["tîs", "t", "o"]
    source := [
      ⟨"caha-2009", "(19)"⟩
    ] }

def slv_tisti_n_acc : Form Cell :=
  { id := "slv_tisti_n_acc"
    lexeme := Lexemes.slv_tisti
    cell := acc_sg_n
    form := "tîsto"
    morphs := ["tîs", "t", "o"]
    source := [
      ⟨"caha-2009", "(19)"⟩
    ] }

def slv_tisti_n_gen : Form Cell :=
  { id := "slv_tisti_n_gen"
    lexeme := Lexemes.slv_tisti
    cell := gen_sg_n
    form := "tîstega"
    morphs := ["tîs", "t", "ega"]
    source := [
      ⟨"caha-2009", "(19)"⟩
    ] }

def slv_tisti_n_prep : Form Cell :=
  { id := "slv_tisti_n_prep"
    lexeme := Lexemes.slv_tisti
    cell := prep_sg_n
    form := "tîstem"
    morphs := ["tîs", "t", "em"]
    source := [
      ⟨"caha-2009", "(19)"⟩
    ] }

def slv_tisti_n_dat : Form Cell :=
  { id := "slv_tisti_n_dat"
    lexeme := Lexemes.slv_tisti
    cell := dat_sg_n
    form := "tîstemu"
    morphs := ["tîs", "t", "emu"]
    source := [
      ⟨"caha-2009", "(19)"⟩
    ] }

def slv_tisti_n_ins : Form Cell :=
  { id := "slv_tisti_n_ins"
    lexeme := Lexemes.slv_tisti
    cell := ins_sg_n
    form := "tîstim"
    morphs := ["tîs", "t", "im"]
    source := [
      ⟨"caha-2009", "(19)"⟩
    ] }

def slv_vas_n_nom : Form Cell :=
  { id := "slv_vas_n_nom"
    lexeme := Lexemes.slv_vas
    cell := nom_sg_n
    form := "váše"
    morphs := ["váš", "e"]
    source := [
      ⟨"caha-2009", "(20)"⟩
    ] }

def slv_vas_n_acc : Form Cell :=
  { id := "slv_vas_n_acc"
    lexeme := Lexemes.slv_vas
    cell := acc_sg_n
    form := "váše"
    morphs := ["váš", "e"]
    source := [
      ⟨"caha-2009", "(20)"⟩
    ] }

def slv_vas_n_gen : Form Cell :=
  { id := "slv_vas_n_gen"
    lexeme := Lexemes.slv_vas
    cell := gen_sg_n
    form := "vášega"
    morphs := ["váš", "ega"]
    source := [
      ⟨"caha-2009", "(20)"⟩
    ] }

def slv_vas_n_prep : Form Cell :=
  { id := "slv_vas_n_prep"
    lexeme := Lexemes.slv_vas
    cell := prep_sg_n
    form := "vášem"
    morphs := ["váš", "em"]
    source := [
      ⟨"caha-2009", "(20)"⟩
    ] }

def slv_vas_n_dat : Form Cell :=
  { id := "slv_vas_n_dat"
    lexeme := Lexemes.slv_vas
    cell := dat_sg_n
    form := "vášemu"
    morphs := ["váš", "emu"]
    source := [
      ⟨"caha-2009", "(20)"⟩
    ] }

def slv_vas_n_ins : Form Cell :=
  { id := "slv_vas_n_ins"
    lexeme := Lexemes.slv_vas
    cell := ins_sg_n
    form := "vášim"
    morphs := ["váš", "im"]
    source := [
      ⟨"caha-2009", "(20)"⟩
    ] }

def ces_okno_sg_nom : Form Cell :=
  { id := "ces_okno_sg_nom"
    lexeme := Lexemes.ces_okno
    cell := nom_sg
    form := "okno"
    morphs := ["okn", "o"]
    source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_okno_sg_acc : Form Cell :=
  { id := "ces_okno_sg_acc"
    lexeme := Lexemes.ces_okno
    cell := acc_sg
    form := "okno"
    morphs := ["okn", "o"]
    source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_okno_sg_gen : Form Cell :=
  { id := "ces_okno_sg_gen"
    lexeme := Lexemes.ces_okno
    cell := gen_sg
    form := "okna"
    morphs := ["okn", "a"]
    source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_okno_sg_prep : Form Cell :=
  { id := "ces_okno_sg_prep"
    lexeme := Lexemes.ces_okno
    cell := prep_sg
    form := "okně"
    morphs := ["okn", "ě"]
    source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_okno_sg_dat : Form Cell :=
  { id := "ces_okno_sg_dat"
    lexeme := Lexemes.ces_okno
    cell := dat_sg
    form := "oknu"
    morphs := ["okn", "u"]
    source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_okno_sg_ins : Form Cell :=
  { id := "ces_okno_sg_ins"
    lexeme := Lexemes.ces_okno
    cell := ins_sg
    form := "oknem"
    morphs := ["okn", "em"]
    source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_ulice_sg_nom : Form Cell :=
  { id := "ces_ulice_sg_nom"
    lexeme := Lexemes.ces_ulice
    cell := nom_sg
    form := "ulice"
    morphs := ["ulic", "e"]
    source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_ulice_sg_acc : Form Cell :=
  { id := "ces_ulice_sg_acc"
    lexeme := Lexemes.ces_ulice
    cell := acc_sg
    form := "ulici"
    morphs := ["ulic", "i"]
    source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_ulice_sg_gen : Form Cell :=
  { id := "ces_ulice_sg_gen"
    lexeme := Lexemes.ces_ulice
    cell := gen_sg
    form := "ulice"
    morphs := ["ulic", "e"]
    source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_ulice_sg_prep : Form Cell :=
  { id := "ces_ulice_sg_prep"
    lexeme := Lexemes.ces_ulice
    cell := prep_sg
    form := "ulici"
    morphs := ["ulic", "i"]
    source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_ulice_sg_dat : Form Cell :=
  { id := "ces_ulice_sg_dat"
    lexeme := Lexemes.ces_ulice
    cell := dat_sg
    form := "ulici"
    morphs := ["ulic", "i"]
    source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_ulice_sg_ins : Form Cell :=
  { id := "ces_ulice_sg_ins"
    lexeme := Lexemes.ces_ulice
    cell := ins_sg
    form := "ulicí"
    morphs := ["ulic", "í"]
    source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_muz_pl_nom : Form Cell :=
  { id := "ces_muz_pl_nom"
    lexeme := Lexemes.ces_muz
    cell := nom_pl
    form := "muži"
    morphs := ["muž", "i"]
    source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_muz_pl_acc : Form Cell :=
  { id := "ces_muz_pl_acc"
    lexeme := Lexemes.ces_muz
    cell := acc_pl
    form := "muže"
    morphs := ["muž", "e"]
    source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_muz_pl_gen : Form Cell :=
  { id := "ces_muz_pl_gen"
    lexeme := Lexemes.ces_muz
    cell := gen_pl
    form := "mužů"
    morphs := ["muž", "ů"]
    source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_muz_pl_prep : Form Cell :=
  { id := "ces_muz_pl_prep"
    lexeme := Lexemes.ces_muz
    cell := prep_pl
    form := "mužích"
    morphs := ["muž", "ích"]
    source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_muz_pl_dat : Form Cell :=
  { id := "ces_muz_pl_dat"
    lexeme := Lexemes.ces_muz
    cell := dat_pl
    form := "mužům"
    morphs := ["muž", "ům"]
    source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_muz_pl_ins : Form Cell :=
  { id := "ces_muz_pl_ins"
    lexeme := Lexemes.ces_muz
    cell := ins_pl
    form := "muži"
    morphs := ["muž", "i"]
    source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_muz_sg_nom : Form Cell :=
  { id := "ces_muz_sg_nom"
    lexeme := Lexemes.ces_muz
    cell := nom_sg
    form := "muž"
    morphs := ["muž"]
    source := [
      ⟨"caha-2009", "(23)"⟩
    ] }

def ces_muz_sg_acc : Form Cell :=
  { id := "ces_muz_sg_acc"
    lexeme := Lexemes.ces_muz
    cell := acc_sg
    form := "muže"
    morphs := ["muž", "e"]
    source := [
      ⟨"caha-2009", "(23)"⟩
    ] }

def ces_muz_sg_gen : Form Cell :=
  { id := "ces_muz_sg_gen"
    lexeme := Lexemes.ces_muz
    cell := gen_sg
    form := "muže"
    morphs := ["muž", "e"]
    source := [
      ⟨"caha-2009", "(23)"⟩
    ] }

def ces_muz_sg_prep : Form Cell :=
  { id := "ces_muz_sg_prep"
    lexeme := Lexemes.ces_muz
    cell := prep_sg
    form := "muži"
    morphs := ["muž", "i"]
    source := [
      ⟨"caha-2009", "(23)"⟩
    ] }

def ces_muz_sg_dat : Form Cell :=
  { id := "ces_muz_sg_dat"
    lexeme := Lexemes.ces_muz
    cell := dat_sg
    form := "muži"
    morphs := ["muž", "i"]
    source := [
      ⟨"caha-2009", "(23)"⟩
    ] }

def ces_muz_sg_ins : Form Cell :=
  { id := "ces_muz_sg_ins"
    lexeme := Lexemes.ces_muz
    cell := ins_sg
    form := "mužem"
    morphs := ["muž", "em"]
    source := [
      ⟨"caha-2009", "(23)"⟩
    ] }

def ces_dobry_fsg_nom : Form Cell :=
  { id := "ces_dobry_fsg_nom"
    lexeme := Lexemes.ces_dobry
    cell := nom_sg_f
    form := "dobrá"
    morphs := ["dobr", "á"]
    source := [
      ⟨"caha-2009", "(23)"⟩
    ] }

def ces_dobry_fsg_acc : Form Cell :=
  { id := "ces_dobry_fsg_acc"
    lexeme := Lexemes.ces_dobry
    cell := acc_sg_f
    form := "dobrou"
    morphs := ["dobr", "ou"]
    source := [
      ⟨"caha-2009", "(23)"⟩
    ] }

def ces_dobry_fsg_gen : Form Cell :=
  { id := "ces_dobry_fsg_gen"
    lexeme := Lexemes.ces_dobry
    cell := gen_sg_f
    form := "dobré"
    morphs := ["dobr", "é"]
    source := [
      ⟨"caha-2009", "(23)"⟩
    ] }

def ces_dobry_fsg_prep : Form Cell :=
  { id := "ces_dobry_fsg_prep"
    lexeme := Lexemes.ces_dobry
    cell := prep_sg_f
    form := "dobré"
    morphs := ["dobr", "é"]
    source := [
      ⟨"caha-2009", "(23)"⟩
    ] }

def ces_dobry_fsg_dat : Form Cell :=
  { id := "ces_dobry_fsg_dat"
    lexeme := Lexemes.ces_dobry
    cell := dat_sg_f
    form := "dobré"
    morphs := ["dobr", "é"]
    source := [
      ⟨"caha-2009", "(23)"⟩
    ] }

def ces_dobry_fsg_ins : Form Cell :=
  { id := "ces_dobry_fsg_ins"
    lexeme := Lexemes.ces_dobry
    cell := ins_sg_f
    form := "dobrou"
    morphs := ["dobr", "ou"]
    source := [
      ⟨"caha-2009", "(23)"⟩
    ] }

def ces_dobry_mpl_2_nom : Form Cell :=
  { id := "ces_dobry_mpl_2_nom"
    lexeme := Lexemes.ces_dobry
    cell := nom_pl_m
    form := "dobrý"
    morphs := ["dobrý"]
    source := [
      ⟨"caha-2009", "(24)"⟩
    ] }

def ces_dobry_mpl_2_acc : Form Cell :=
  { id := "ces_dobry_mpl_2_acc"
    lexeme := Lexemes.ces_dobry
    cell := acc_pl_m
    form := "dobrý"
    morphs := ["dobrý"]
    source := [
      ⟨"caha-2009", "(24)"⟩
    ] }

def ces_dobry_mpl_2_gen : Form Cell :=
  { id := "ces_dobry_mpl_2_gen"
    lexeme := Lexemes.ces_dobry
    cell := gen_pl_m
    form := "dobrých"
    morphs := ["dobrý", "ch"]
    source := [
      ⟨"caha-2009", "(24)"⟩
    ] }

def ces_dobry_mpl_2_prep : Form Cell :=
  { id := "ces_dobry_mpl_2_prep"
    lexeme := Lexemes.ces_dobry
    cell := prep_pl_m
    form := "dobrých"
    morphs := ["dobrý", "ch"]
    source := [
      ⟨"caha-2009", "(24)"⟩
    ] }

def ces_dobry_mpl_2_dat : Form Cell :=
  { id := "ces_dobry_mpl_2_dat"
    lexeme := Lexemes.ces_dobry
    cell := dat_pl_m
    form := "dobrým"
    morphs := ["dobrý", "m"]
    source := [
      ⟨"caha-2009", "(24)"⟩
    ] }

def ces_dobry_mpl_2_ins : Form Cell :=
  { id := "ces_dobry_mpl_2_ins"
    lexeme := Lexemes.ces_dobry
    cell := ins_pl_m
    form := "dobrými"
    morphs := ["dobrý", "mi"]
    source := [
      ⟨"caha-2009", "(24)"⟩
    ] }

def ces_vetsi_msg_nom : Form Cell :=
  { id := "ces_vetsi_msg_nom"
    lexeme := Lexemes.ces_vetsi
    cell := nom_sg_m
    form := "větší"
    morphs := ["větš", "í"]
    source := [
      ⟨"caha-2009", "(25)"⟩
    ] }

def ces_vetsi_msg_acc : Form Cell :=
  { id := "ces_vetsi_msg_acc"
    lexeme := Lexemes.ces_vetsi
    cell := acc_sg_m
    form := "většího"
    morphs := ["větš", "ího"]
    source := [
      ⟨"caha-2009", "(25)"⟩
    ] }

def ces_vetsi_msg_gen : Form Cell :=
  { id := "ces_vetsi_msg_gen"
    lexeme := Lexemes.ces_vetsi
    cell := gen_sg_m
    form := "většího"
    morphs := ["větš", "ího"]
    source := [
      ⟨"caha-2009", "(25)"⟩
    ] }

def ces_vetsi_msg_prep : Form Cell :=
  { id := "ces_vetsi_msg_prep"
    lexeme := Lexemes.ces_vetsi
    cell := prep_sg_m
    form := "větším"
    morphs := ["větš", "ím"]
    source := [
      ⟨"caha-2009", "(25)"⟩
    ] }

def ces_vetsi_msg_dat : Form Cell :=
  { id := "ces_vetsi_msg_dat"
    lexeme := Lexemes.ces_vetsi
    cell := dat_sg_m
    form := "většímu"
    morphs := ["větš", "ímu"]
    source := [
      ⟨"caha-2009", "(25)"⟩
    ] }

def ces_vetsi_msg_ins : Form Cell :=
  { id := "ces_vetsi_msg_ins"
    lexeme := Lexemes.ces_vetsi
    cell := ins_sg_m
    form := "větším"
    morphs := ["větš", "ím"]
    source := [
      ⟨"caha-2009", "(25)"⟩
    ] }

def ces_oba_nom : Form Cell :=
  { id := "ces_oba_nom"
    lexeme := Lexemes.ces_oba
    cell := nom_du
    form := "oba"
    morphs := ["ob", "a"]
    source := [
      ⟨"caha-2009", "(26)"⟩
    ] }

def ces_oba_acc : Form Cell :=
  { id := "ces_oba_acc"
    lexeme := Lexemes.ces_oba
    cell := acc_du
    form := "oba"
    morphs := ["ob", "a"]
    source := [
      ⟨"caha-2009", "(26)"⟩
    ] }

def ces_oba_gen : Form Cell :=
  { id := "ces_oba_gen"
    lexeme := Lexemes.ces_oba
    cell := gen_du
    form := "obou"
    morphs := ["ob", "ou"]
    source := [
      ⟨"caha-2009", "(26)"⟩
    ] }

def ces_oba_prep : Form Cell :=
  { id := "ces_oba_prep"
    lexeme := Lexemes.ces_oba
    cell := prep_du
    form := "obou"
    morphs := ["ob", "ou"]
    source := [
      ⟨"caha-2009", "(26)"⟩
    ] }

def ces_oba_dat : Form Cell :=
  { id := "ces_oba_dat"
    lexeme := Lexemes.ces_oba
    cell := dat_du
    form := "oběma"
    morphs := ["ob", "ěma"]
    source := [
      ⟨"caha-2009", "(26)"⟩
    ] }

def ces_oba_ins : Form Cell :=
  { id := "ces_oba_ins"
    lexeme := Lexemes.ces_oba
    cell := ins_du
    form := "oběma"
    morphs := ["ob", "ěma"]
    source := [
      ⟨"caha-2009", "(26)"⟩
    ] }

def ces_stroj_sg_nom : Form Cell :=
  { id := "ces_stroj_sg_nom"
    lexeme := Lexemes.ces_stroj
    cell := nom_sg
    form := "stroj"
    morphs := ["stroj", "ø"]
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_stroj_sg_acc : Form Cell :=
  { id := "ces_stroj_sg_acc"
    lexeme := Lexemes.ces_stroj
    cell := acc_sg
    form := "stroj"
    morphs := ["stroj", "ø"]
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_stroj_sg_gen : Form Cell :=
  { id := "ces_stroj_sg_gen"
    lexeme := Lexemes.ces_stroj
    cell := gen_sg
    form := "stroje"
    morphs := ["stroj", "e"]
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_stroj_sg_prep : Form Cell :=
  { id := "ces_stroj_sg_prep"
    lexeme := Lexemes.ces_stroj
    cell := prep_sg
    form := "stroji"
    morphs := ["stroj", "i"]
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_stroj_sg_dat : Form Cell :=
  { id := "ces_stroj_sg_dat"
    lexeme := Lexemes.ces_stroj
    cell := dat_sg
    form := "stroji"
    morphs := ["stroj", "i"]
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_stroj_sg_ins : Form Cell :=
  { id := "ces_stroj_sg_ins"
    lexeme := Lexemes.ces_stroj
    cell := ins_sg
    form := "strojem"
    morphs := ["stroj", "em"]
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_stroj_pl_nom : Form Cell :=
  { id := "ces_stroj_pl_nom"
    lexeme := Lexemes.ces_stroj
    cell := nom_pl
    form := "stroje"
    morphs := ["stroj", "e"]
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_stroj_pl_acc : Form Cell :=
  { id := "ces_stroj_pl_acc"
    lexeme := Lexemes.ces_stroj
    cell := acc_pl
    form := "stroje"
    morphs := ["stroj", "e"]
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_stroj_pl_gen : Form Cell :=
  { id := "ces_stroj_pl_gen"
    lexeme := Lexemes.ces_stroj
    cell := gen_pl
    form := "strojů"
    morphs := ["stroj", "ů"]
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_stroj_pl_prep : Form Cell :=
  { id := "ces_stroj_pl_prep"
    lexeme := Lexemes.ces_stroj
    cell := prep_pl
    form := "strojích"
    morphs := ["stroj", "ích"]
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_stroj_pl_dat : Form Cell :=
  { id := "ces_stroj_pl_dat"
    lexeme := Lexemes.ces_stroj
    cell := dat_pl
    form := "strojům"
    morphs := ["stroj", "ům"]
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_stroj_pl_ins : Form Cell :=
  { id := "ces_stroj_pl_ins"
    lexeme := Lexemes.ces_stroj
    cell := ins_pl
    form := "stroji"
    morphs := ["stroj", "i"]
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_kost_pl_nom : Form Cell :=
  { id := "ces_kost_pl_nom"
    lexeme := Lexemes.ces_kost
    cell := nom_pl
    form := "kosti"
    morphs := ["kost", "i"]
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_kost_pl_acc : Form Cell :=
  { id := "ces_kost_pl_acc"
    lexeme := Lexemes.ces_kost
    cell := acc_pl
    form := "kosti"
    morphs := ["kost", "i"]
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_kost_pl_gen : Form Cell :=
  { id := "ces_kost_pl_gen"
    lexeme := Lexemes.ces_kost
    cell := gen_pl
    form := "kostí"
    morphs := ["kost", "í"]
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_kost_pl_prep : Form Cell :=
  { id := "ces_kost_pl_prep"
    lexeme := Lexemes.ces_kost
    cell := prep_pl
    form := "kostech"
    morphs := ["kost", "ech"]
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_kost_pl_dat : Form Cell :=
  { id := "ces_kost_pl_dat"
    lexeme := Lexemes.ces_kost
    cell := dat_pl
    form := "kostem"
    morphs := ["kost", "em"]
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_kost_pl_ins : Form Cell :=
  { id := "ces_kost_pl_ins"
    lexeme := Lexemes.ces_kost
    cell := ins_pl
    form := "kostmi"
    morphs := ["kost", "mi"]
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_ty_nom : Form Cell :=
  { id := "ces_ty_nom"
    lexeme := Lexemes.ces_ten
    cell := nom_pl_f
    form := "ty"
    morphs := ["t", "y"]
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_ty_acc : Form Cell :=
  { id := "ces_ty_acc"
    lexeme := Lexemes.ces_ten
    cell := acc_pl_f
    form := "ty"
    morphs := ["t", "y"]
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_ty_gen : Form Cell :=
  { id := "ces_ty_gen"
    lexeme := Lexemes.ces_ten
    cell := gen_pl_f
    form := "těch"
    morphs := ["t", "ěch"]
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_ty_prep : Form Cell :=
  { id := "ces_ty_prep"
    lexeme := Lexemes.ces_ten
    cell := prep_pl_f
    form := "těch"
    morphs := ["t", "ěch"]
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_ty_dat : Form Cell :=
  { id := "ces_ty_dat"
    lexeme := Lexemes.ces_ten
    cell := dat_pl_f
    form := "těm"
    morphs := ["t", "ěm"]
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_ty_ins : Form Cell :=
  { id := "ces_ty_ins"
    lexeme := Lexemes.ces_ten
    cell := ins_pl_f
    form := "těmi"
    morphs := ["t", "ěmi"]
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_vila_sg_nom : Form Cell :=
  { id := "ces_vila_sg_nom"
    lexeme := Lexemes.ces_vila
    cell := nom_sg
    form := "vila"
    morphs := ["vil", "a"]
    source := [
      ⟨"caha-2009", "(31)"⟩
    ] }

def ces_vila_sg_acc : Form Cell :=
  { id := "ces_vila_sg_acc"
    lexeme := Lexemes.ces_vila
    cell := acc_sg
    form := "vilu"
    morphs := ["vil", "u"]
    source := [
      ⟨"caha-2009", "(31)"⟩
    ] }

def ces_vila_sg_gen : Form Cell :=
  { id := "ces_vila_sg_gen"
    lexeme := Lexemes.ces_vila
    cell := gen_sg
    form := "vily"
    morphs := ["vil", "y"]
    source := [
      ⟨"caha-2009", "(31)"⟩
    ] }

def ces_vila_sg_prep : Form Cell :=
  { id := "ces_vila_sg_prep"
    lexeme := Lexemes.ces_vila
    cell := prep_sg
    form := "vile"
    morphs := ["vil", "e"]
    source := [
      ⟨"caha-2009", "(31)"⟩
    ] }

def ces_vila_sg_dat : Form Cell :=
  { id := "ces_vila_sg_dat"
    lexeme := Lexemes.ces_vila
    cell := dat_sg
    form := "vile"
    morphs := ["vil", "e"]
    source := [
      ⟨"caha-2009", "(31)"⟩
    ] }

def ces_vila_sg_ins : Form Cell :=
  { id := "ces_vila_sg_ins"
    lexeme := Lexemes.ces_vila
    cell := ins_sg
    form := "vilou"
    morphs := ["vil", "ou"]
    source := [
      ⟨"caha-2009", "(31)"⟩
    ] }

def ces_misa_sg_nom : Form Cell :=
  { id := "ces_misa_sg_nom"
    lexeme := Lexemes.ces_misa
    cell := nom_sg
    form := "Míša"
    morphs := ["Míš", "a"]
    source := [
      ⟨"caha-2009", "(31)"⟩
    ] }

def ces_misa_sg_acc : Form Cell :=
  { id := "ces_misa_sg_acc"
    lexeme := Lexemes.ces_misa
    cell := acc_sg
    form := "Míšu"
    morphs := ["Míš", "u"]
    source := [
      ⟨"caha-2009", "(31)"⟩
    ] }

def ces_misa_sg_gen : Form Cell :=
  { id := "ces_misa_sg_gen"
    lexeme := Lexemes.ces_misa
    cell := gen_sg
    form := "Míši"
    morphs := ["Míš", "i"]
    source := [
      ⟨"caha-2009", "(31)"⟩
    ] }

def ces_misa_sg_prep : Form Cell :=
  { id := "ces_misa_sg_prep"
    lexeme := Lexemes.ces_misa
    cell := prep_sg
    form := "Míše"
    morphs := ["Míš", "e"]
    source := [
      ⟨"caha-2009", "(31)"⟩
    ] }

def ces_misa_sg_dat : Form Cell :=
  { id := "ces_misa_sg_dat"
    lexeme := Lexemes.ces_misa
    cell := dat_sg
    form := "Míše"
    morphs := ["Míš", "e"]
    source := [
      ⟨"caha-2009", "(31)"⟩
    ] }

def ces_misa_sg_ins : Form Cell :=
  { id := "ces_misa_sg_ins"
    lexeme := Lexemes.ces_misa
    cell := ins_sg
    form := "Míšou"
    morphs := ["Míš", "ou"]
    source := [
      ⟨"caha-2009", "(31)"⟩
    ] }

def ces_vul_pl_nom : Form Cell :=
  { id := "ces_vul_pl_nom"
    lexeme := Lexemes.ces_vul
    cell := nom_pl
    form := "voli"
    morphs := ["vol", "i"]
    source := [
      ⟨"caha-2009", "(35)"⟩
    ] }

def ces_vul_pl_acc : Form Cell :=
  { id := "ces_vul_pl_acc"
    lexeme := Lexemes.ces_vul
    cell := acc_pl
    form := "voly"
    morphs := ["vol", "y"]
    source := [
      ⟨"caha-2009", "(35)"⟩
    ] }

def ces_vul_pl_gen : Form Cell :=
  { id := "ces_vul_pl_gen"
    lexeme := Lexemes.ces_vul
    cell := gen_pl
    form := "volů"
    morphs := ["vol", "ů"]
    source := [
      ⟨"caha-2009", "(35)"⟩
    ] }

def ces_vul_pl_prep : Form Cell :=
  { id := "ces_vul_pl_prep"
    lexeme := Lexemes.ces_vul
    cell := prep_pl
    form := "volech"
    morphs := ["vol", "ech"]
    source := [
      ⟨"caha-2009", "(35)"⟩
    ] }

def ces_vul_pl_dat : Form Cell :=
  { id := "ces_vul_pl_dat"
    lexeme := Lexemes.ces_vul
    cell := dat_pl
    form := "volům"
    morphs := ["vol", "ům"]
    source := [
      ⟨"caha-2009", "(35)"⟩
    ] }

def ces_vul_pl_ins : Form Cell :=
  { id := "ces_vul_pl_ins"
    lexeme := Lexemes.ces_vul
    cell := ins_pl
    form := "voly"
    morphs := ["vol", "y"]
    source := [
      ⟨"caha-2009", "(35)"⟩
    ] }

def ces_hoch_pl_nom : Form Cell :=
  { id := "ces_hoch_pl_nom"
    lexeme := Lexemes.ces_hoch
    cell := nom_pl
    form := "hoši"
    morphs := ["hoš", "i"]
    source := [
      ⟨"caha-2009", "(35)"⟩
    ] }

def ces_hoch_pl_acc : Form Cell :=
  { id := "ces_hoch_pl_acc"
    lexeme := Lexemes.ces_hoch
    cell := acc_pl
    form := "hochy"
    morphs := ["hoch", "y"]
    source := [
      ⟨"caha-2009", "(35)"⟩
    ] }

def ces_hoch_pl_gen : Form Cell :=
  { id := "ces_hoch_pl_gen"
    lexeme := Lexemes.ces_hoch
    cell := gen_pl
    form := "hochů"
    morphs := ["hoch", "ů"]
    source := [
      ⟨"caha-2009", "(35)"⟩
    ] }

def ces_hoch_pl_prep : Form Cell :=
  { id := "ces_hoch_pl_prep"
    lexeme := Lexemes.ces_hoch
    cell := prep_pl
    form := "hoších"
    morphs := ["hoš", "ích"]
    source := [
      ⟨"caha-2009", "(35)"⟩
    ] }

def ces_hoch_pl_dat : Form Cell :=
  { id := "ces_hoch_pl_dat"
    lexeme := Lexemes.ces_hoch
    cell := dat_pl
    form := "hochům"
    morphs := ["hoch", "ům"]
    source := [
      ⟨"caha-2009", "(35)"⟩
    ] }

def ces_hoch_pl_ins : Form Cell :=
  { id := "ces_hoch_pl_ins"
    lexeme := Lexemes.ces_hoch
    cell := ins_pl
    form := "hochy"
    morphs := ["hoch", "y"]
    source := [
      ⟨"caha-2009", "(35)"⟩
    ] }

def ces_pan_sg_nom : Form Cell :=
  { id := "ces_pan_sg_nom"
    lexeme := Lexemes.ces_pan
    cell := nom_sg
    form := "pán"
    morphs := ["pán"]
    source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_pan_sg_acc : Form Cell :=
  { id := "ces_pan_sg_acc"
    lexeme := Lexemes.ces_pan
    cell := acc_sg
    form := "pána"
    morphs := ["pán", "a"]
    source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_pan_sg_gen : Form Cell :=
  { id := "ces_pan_sg_gen"
    lexeme := Lexemes.ces_pan
    cell := gen_sg
    form := "pána"
    morphs := ["pán", "a"]
    source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_pan_sg_prep : Form Cell :=
  { id := "ces_pan_sg_prep"
    lexeme := Lexemes.ces_pan
    cell := prep_sg
    form := "pánovi"
    morphs := ["pán", "ovi"]
    source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_pan_sg_dat : Form Cell :=
  { id := "ces_pan_sg_dat"
    lexeme := Lexemes.ces_pan
    cell := dat_sg
    form := "pánovi"
    morphs := ["pán", "ovi"]
    source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_pan_sg_ins : Form Cell :=
  { id := "ces_pan_sg_ins"
    lexeme := Lexemes.ces_pan
    cell := ins_sg
    form := "pánem"
    morphs := ["pán", "em"]
    source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_ten_nom : Form Cell :=
  { id := "ces_ten_nom"
    lexeme := Lexemes.ces_ten
    cell := nom_sg_m
    form := "ten"
    morphs := ["t", "en"]
    source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_ten_acc : Form Cell :=
  { id := "ces_ten_acc"
    lexeme := Lexemes.ces_ten
    cell := acc_sg_m
    form := "toho"
    morphs := ["t", "oho"]
    source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_ten_gen : Form Cell :=
  { id := "ces_ten_gen"
    lexeme := Lexemes.ces_ten
    cell := gen_sg_m
    form := "toho"
    morphs := ["t", "oho"]
    source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_ten_prep : Form Cell :=
  { id := "ces_ten_prep"
    lexeme := Lexemes.ces_ten
    cell := prep_sg_m
    form := "tom"
    morphs := ["t", "om"]
    source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_ten_dat : Form Cell :=
  { id := "ces_ten_dat"
    lexeme := Lexemes.ces_ten
    cell := dat_sg_m
    form := "tomu"
    morphs := ["t", "omu"]
    source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_ten_ins : Form Cell :=
  { id := "ces_ten_ins"
    lexeme := Lexemes.ces_ten
    cell := ins_sg_m
    form := "tím"
    morphs := ["t", "ím"]
    source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_my_2_nom : Form Cell :=
  { id := "ces_my_2_nom"
    lexeme := Lexemes.ces_my
    cell := nom_pl
    form := "my"
    morphs := ["my"]
    source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_my_2_acc : Form Cell :=
  { id := "ces_my_2_acc"
    lexeme := Lexemes.ces_my
    cell := acc_pl
    form := "nás"
    morphs := ["ná", "s"]
    source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_my_2_gen : Form Cell :=
  { id := "ces_my_2_gen"
    lexeme := Lexemes.ces_my
    cell := gen_pl
    form := "nás"
    morphs := ["ná", "s"]
    source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_my_2_prep : Form Cell :=
  { id := "ces_my_2_prep"
    lexeme := Lexemes.ces_my
    cell := prep_pl
    form := "nás"
    morphs := ["ná", "s"]
    source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_my_2_dat : Form Cell :=
  { id := "ces_my_2_dat"
    lexeme := Lexemes.ces_my
    cell := dat_pl
    form := "nám"
    morphs := ["ná", "m"]
    source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_my_2_ins : Form Cell :=
  { id := "ces_my_2_ins"
    lexeme := Lexemes.ces_my
    cell := ins_pl
    form := "náma"
    morphs := ["ná", "ma"]
    source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_ona_nom : Form Cell :=
  { id := "ces_ona_nom"
    lexeme := Lexemes.ces_ona
    cell := nom_sg
    form := "ona"
    morphs := ["ona"]
    source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_ona_acc : Form Cell :=
  { id := "ces_ona_acc"
    lexeme := Lexemes.ces_ona
    cell := acc_sg
    form := "ji"
    morphs := ["j", "i"]
    source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_ona_gen : Form Cell :=
  { id := "ces_ona_gen"
    lexeme := Lexemes.ces_ona
    cell := gen_sg
    form := "jí"
    morphs := ["j", "í"]
    source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_ona_prep : Form Cell :=
  { id := "ces_ona_prep"
    lexeme := Lexemes.ces_ona
    cell := prep_sg
    form := "jí"
    morphs := ["j", "í"]
    source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_ona_dat : Form Cell :=
  { id := "ces_ona_dat"
    lexeme := Lexemes.ces_ona
    cell := dat_sg
    form := "jí"
    morphs := ["j", "í"]
    source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_ona_ins : Form Cell :=
  { id := "ces_ona_ins"
    lexeme := Lexemes.ces_ona
    cell := ins_sg
    form := "jí"
    morphs := ["j", "í"]
    source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_nase_fsg_nom : Form Cell :=
  { id := "ces_nase_fsg_nom"
    lexeme := Lexemes.ces_nase
    cell := nom_sg_f
    form := "naše"
    morphs := ["naš", "e"]
    source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_nase_fsg_acc : Form Cell :=
  { id := "ces_nase_fsg_acc"
    lexeme := Lexemes.ces_nase
    cell := acc_sg_f
    form := "naši"
    morphs := ["naš", "i"]
    source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_nase_fsg_gen : Form Cell :=
  { id := "ces_nase_fsg_gen"
    lexeme := Lexemes.ces_nase
    cell := gen_sg_f
    form := "naší"
    morphs := ["naš", "í"]
    source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_nase_fsg_prep : Form Cell :=
  { id := "ces_nase_fsg_prep"
    lexeme := Lexemes.ces_nase
    cell := prep_sg_f
    form := "naší"
    morphs := ["naš", "í"]
    source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_nase_fsg_dat : Form Cell :=
  { id := "ces_nase_fsg_dat"
    lexeme := Lexemes.ces_nase
    cell := dat_sg_f
    form := "naší"
    morphs := ["naš", "í"]
    source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_nase_fsg_ins : Form Cell :=
  { id := "ces_nase_fsg_ins"
    lexeme := Lexemes.ces_nase
    cell := ins_sg_f
    form := "naší"
    morphs := ["naš", "í"]
    source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_zatez_sg_nom : Form Cell :=
  { id := "ces_zatez_sg_nom"
    lexeme := Lexemes.ces_zatez
    cell := nom_sg
    form := "zátěž"
    morphs := ["zátěž", "ø"]
    source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_zatez_sg_acc : Form Cell :=
  { id := "ces_zatez_sg_acc"
    lexeme := Lexemes.ces_zatez
    cell := acc_sg
    form := "zátěž"
    morphs := ["zátěž", "ø"]
    source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_zatez_sg_gen : Form Cell :=
  { id := "ces_zatez_sg_gen"
    lexeme := Lexemes.ces_zatez
    cell := gen_sg
    form := "zátěže"
    morphs := ["zátěž", "e"]
    source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_zatez_sg_prep : Form Cell :=
  { id := "ces_zatez_sg_prep"
    lexeme := Lexemes.ces_zatez
    cell := prep_sg
    form := "zátěži"
    morphs := ["zátěž", "i"]
    source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_zatez_sg_dat : Form Cell :=
  { id := "ces_zatez_sg_dat"
    lexeme := Lexemes.ces_zatez
    cell := dat_sg
    form := "zátěži"
    morphs := ["zátěž", "i"]
    source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_zatez_sg_ins : Form Cell :=
  { id := "ces_zatez_sg_ins"
    lexeme := Lexemes.ces_zatez
    cell := ins_sg
    form := "zátěží"
    morphs := ["zátěž", "í"]
    source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_zena_sg_nom : Form Cell :=
  { id := "ces_zena_sg_nom"
    lexeme := Lexemes.ces_zena
    cell := nom_sg
    form := "žena"
    morphs := ["žen", "a"]
    source := [
      ⟨"caha-2009", "(44)"⟩
    ] }

def ces_zena_sg_acc : Form Cell :=
  { id := "ces_zena_sg_acc"
    lexeme := Lexemes.ces_zena
    cell := acc_sg
    form := "ženu"
    morphs := ["žen", "u"]
    source := [
      ⟨"caha-2009", "(44)"⟩
    ] }

def ces_zena_sg_gen : Form Cell :=
  { id := "ces_zena_sg_gen"
    lexeme := Lexemes.ces_zena
    cell := gen_sg
    form := "ženy"
    morphs := ["žen", "y"]
    source := [
      ⟨"caha-2009", "(44)"⟩
    ] }

def ces_zena_sg_prep : Form Cell :=
  { id := "ces_zena_sg_prep"
    lexeme := Lexemes.ces_zena
    cell := prep_sg
    form := "ženě"
    morphs := ["žen", "ě"]
    source := [
      ⟨"caha-2009", "(44)"⟩
    ] }

def ces_zena_sg_dat : Form Cell :=
  { id := "ces_zena_sg_dat"
    lexeme := Lexemes.ces_zena
    cell := dat_sg
    form := "ženě"
    morphs := ["žen", "ě"]
    source := [
      ⟨"caha-2009", "(44)"⟩
    ] }

def ces_zena_sg_ins : Form Cell :=
  { id := "ces_zena_sg_ins"
    lexeme := Lexemes.ces_zena
    cell := ins_sg
    form := "ženou"
    morphs := ["žen", "ou"]
    source := [
      ⟨"caha-2009", "(44)"⟩
    ] }

def ces_kluk_pl_nom : Form Cell :=
  { id := "ces_kluk_pl_nom"
    lexeme := Lexemes.ces_kluk
    cell := nom_pl
    form := "kluci"
    morphs := ["kluc", "i"]
    source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_kluk_pl_acc : Form Cell :=
  { id := "ces_kluk_pl_acc"
    lexeme := Lexemes.ces_kluk
    cell := acc_pl
    form := "kluky"
    morphs := ["kluk", "y"]
    source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_kluk_pl_gen : Form Cell :=
  { id := "ces_kluk_pl_gen"
    lexeme := Lexemes.ces_kluk
    cell := gen_pl
    form := "kluků"
    morphs := ["kluk", "ů"]
    source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_kluk_pl_prep : Form Cell :=
  { id := "ces_kluk_pl_prep"
    lexeme := Lexemes.ces_kluk
    cell := prep_pl
    form := "klucích"
    morphs := ["kluc", "ích"]
    source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_kluk_pl_dat : Form Cell :=
  { id := "ces_kluk_pl_dat"
    lexeme := Lexemes.ces_kluk
    cell := dat_pl
    form := "klukům"
    morphs := ["kluk", "ům"]
    source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_kluk_pl_ins : Form Cell :=
  { id := "ces_kluk_pl_ins"
    lexeme := Lexemes.ces_kluk
    cell := ins_pl
    form := "kluky"
    morphs := ["kluk", "y"]
    source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_kluk_pl_colloquial_nom : Form Cell :=
  { id := "ces_kluk_pl_colloquial_nom"
    lexeme := Lexemes.ces_kluk
    cell := nom_pl
    form := "kluci"
    morphs := ["kluc", "i"]
    source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_kluk_pl_colloquial_acc : Form Cell :=
  { id := "ces_kluk_pl_colloquial_acc"
    lexeme := Lexemes.ces_kluk
    cell := acc_pl
    form := "kluky"
    morphs := ["kluk", "y"]
    source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_kluk_pl_colloquial_gen : Form Cell :=
  { id := "ces_kluk_pl_colloquial_gen"
    lexeme := Lexemes.ces_kluk
    cell := gen_pl
    form := "kluků"
    morphs := ["kluk", "ů"]
    source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_kluk_pl_colloquial_prep : Form Cell :=
  { id := "ces_kluk_pl_colloquial_prep"
    lexeme := Lexemes.ces_kluk
    cell := prep_pl
    form := "klukách"
    morphs := ["kluk", "ách"]
    source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_kluk_pl_colloquial_dat : Form Cell :=
  { id := "ces_kluk_pl_colloquial_dat"
    lexeme := Lexemes.ces_kluk
    cell := dat_pl
    form := "klukům"
    morphs := ["kluk", "ům"]
    source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_kluk_pl_colloquial_ins : Form Cell :=
  { id := "ces_kluk_pl_colloquial_ins"
    lexeme := Lexemes.ces_kluk
    cell := ins_pl
    form := "klukama"
    morphs := ["kluk", "ama"]
    source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_muz_pl_colloquial_nom : Form Cell :=
  { id := "ces_muz_pl_colloquial_nom"
    lexeme := Lexemes.ces_muz
    cell := nom_pl
    form := "muži"
    morphs := ["muž", "i"]
    source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_muz_pl_colloquial_acc : Form Cell :=
  { id := "ces_muz_pl_colloquial_acc"
    lexeme := Lexemes.ces_muz
    cell := acc_pl
    form := "muže"
    morphs := ["muž", "e"]
    source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_muz_pl_colloquial_gen : Form Cell :=
  { id := "ces_muz_pl_colloquial_gen"
    lexeme := Lexemes.ces_muz
    cell := gen_pl
    form := "mužů"
    morphs := ["muž", "ů"]
    source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_muz_pl_colloquial_prep : Form Cell :=
  { id := "ces_muz_pl_colloquial_prep"
    lexeme := Lexemes.ces_muz
    cell := prep_pl
    form := "mužích"
    morphs := ["muž", "ích"]
    source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_muz_pl_colloquial_dat : Form Cell :=
  { id := "ces_muz_pl_colloquial_dat"
    lexeme := Lexemes.ces_muz
    cell := dat_pl
    form := "mužům"
    morphs := ["muž", "ům"]
    source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_muz_pl_colloquial_ins : Form Cell :=
  { id := "ces_muz_pl_colloquial_ins"
    lexeme := Lexemes.ces_muz
    cell := ins_pl
    form := "mužema"
    morphs := ["muž", "ema"]
    source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_zena_pl_nom : Form Cell :=
  { id := "ces_zena_pl_nom"
    lexeme := Lexemes.ces_zena
    cell := nom_pl
    form := "ženy"
    morphs := ["žen", "y"]
    source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_zena_pl_acc : Form Cell :=
  { id := "ces_zena_pl_acc"
    lexeme := Lexemes.ces_zena
    cell := acc_pl
    form := "ženy"
    morphs := ["žen", "y"]
    source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_zena_pl_gen : Form Cell :=
  { id := "ces_zena_pl_gen"
    lexeme := Lexemes.ces_zena
    cell := gen_pl
    form := "žen"
    morphs := ["žen", "ø"]
    source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_zena_pl_prep : Form Cell :=
  { id := "ces_zena_pl_prep"
    lexeme := Lexemes.ces_zena
    cell := prep_pl
    form := "ženách"
    morphs := ["žen", "á", "ch"]
    source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_zena_pl_dat : Form Cell :=
  { id := "ces_zena_pl_dat"
    lexeme := Lexemes.ces_zena
    cell := dat_pl
    form := "ženám"
    morphs := ["žen", "á", "m"]
    source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_zena_pl_ins : Form Cell :=
  { id := "ces_zena_pl_ins"
    lexeme := Lexemes.ces_zena
    cell := ins_pl
    form := "ženami"
    morphs := ["žen", "a", "mi"]
    source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_pisen_pl_nom : Form Cell :=
  { id := "ces_pisen_pl_nom"
    lexeme := Lexemes.ces_pisen
    cell := nom_pl
    form := "písně"
    morphs := ["písn", "ě"]
    source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_pisen_pl_acc : Form Cell :=
  { id := "ces_pisen_pl_acc"
    lexeme := Lexemes.ces_pisen
    cell := acc_pl
    form := "písně"
    morphs := ["písn", "ě"]
    source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_pisen_pl_gen : Form Cell :=
  { id := "ces_pisen_pl_gen"
    lexeme := Lexemes.ces_pisen
    cell := gen_pl
    form := "písní"
    morphs := ["písn", "í"]
    source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_pisen_pl_prep : Form Cell :=
  { id := "ces_pisen_pl_prep"
    lexeme := Lexemes.ces_pisen
    cell := prep_pl
    form := "písních"
    morphs := ["písn", "í", "ch"]
    source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_pisen_pl_dat : Form Cell :=
  { id := "ces_pisen_pl_dat"
    lexeme := Lexemes.ces_pisen
    cell := dat_pl
    form := "písním"
    morphs := ["písn", "í", "m"]
    source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_pisen_pl_ins : Form Cell :=
  { id := "ces_pisen_pl_ins"
    lexeme := Lexemes.ces_pisen
    cell := ins_pl
    form := "písněmi"
    morphs := ["písn", "ě", "mi"]
    source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_dobry_mpl_nom : Form Cell :=
  { id := "ces_dobry_mpl_nom"
    lexeme := Lexemes.ces_dobry
    cell := nom_pl_m
    form := "dobré"
    morphs := ["dobr", "é"]
    source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_dobry_mpl_acc : Form Cell :=
  { id := "ces_dobry_mpl_acc"
    lexeme := Lexemes.ces_dobry
    cell := acc_pl_m
    form := "dobré"
    morphs := ["dobr", "é"]
    source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_dobry_mpl_gen : Form Cell :=
  { id := "ces_dobry_mpl_gen"
    lexeme := Lexemes.ces_dobry
    cell := gen_pl_m
    form := "dobrých"
    morphs := ["dobr", "ý", "ch"]
    source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_dobry_mpl_prep : Form Cell :=
  { id := "ces_dobry_mpl_prep"
    lexeme := Lexemes.ces_dobry
    cell := prep_pl_m
    form := "dobrých"
    morphs := ["dobr", "ý", "ch"]
    source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_dobry_mpl_dat : Form Cell :=
  { id := "ces_dobry_mpl_dat"
    lexeme := Lexemes.ces_dobry
    cell := dat_pl_m
    form := "dobrým"
    morphs := ["dobr", "ý", "m"]
    source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_dobry_mpl_ins : Form Cell :=
  { id := "ces_dobry_mpl_ins"
    lexeme := Lexemes.ces_dobry
    cell := ins_pl_m
    form := "dobrými"
    morphs := ["dobr", "ý", "mi"]
    source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_kost_sg_nom : Form Cell :=
  { id := "ces_kost_sg_nom"
    lexeme := Lexemes.ces_kost
    cell := nom_sg
    form := "kost"
    morphs := ["kost", "ø"]
    source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_kost_sg_acc : Form Cell :=
  { id := "ces_kost_sg_acc"
    lexeme := Lexemes.ces_kost
    cell := acc_sg
    form := "kost"
    morphs := ["kost", "ø"]
    source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_kost_sg_gen : Form Cell :=
  { id := "ces_kost_sg_gen"
    lexeme := Lexemes.ces_kost
    cell := gen_sg
    form := "kosti"
    morphs := ["kost", "i"]
    source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_kost_sg_prep : Form Cell :=
  { id := "ces_kost_sg_prep"
    lexeme := Lexemes.ces_kost
    cell := prep_sg
    form := "kosti"
    morphs := ["kost", "i"]
    source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_kost_sg_dat : Form Cell :=
  { id := "ces_kost_sg_dat"
    lexeme := Lexemes.ces_kost
    cell := dat_sg
    form := "kosti"
    morphs := ["kost", "i"]
    source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_kost_sg_ins : Form Cell :=
  { id := "ces_kost_sg_ins"
    lexeme := Lexemes.ces_kost
    cell := ins_sg
    form := "kostí"
    morphs := ["kost", "í"]
    source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_hrad_sg_nom : Form Cell :=
  { id := "ces_hrad_sg_nom"
    lexeme := Lexemes.ces_hrad
    cell := nom_sg
    form := "hrad"
    morphs := ["hrad", "ø"]
    source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_hrad_sg_acc : Form Cell :=
  { id := "ces_hrad_sg_acc"
    lexeme := Lexemes.ces_hrad
    cell := acc_sg
    form := "hrad"
    morphs := ["hrad", "ø"]
    source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_hrad_sg_gen : Form Cell :=
  { id := "ces_hrad_sg_gen"
    lexeme := Lexemes.ces_hrad
    cell := gen_sg
    form := "hradu"
    morphs := ["hrad", "u"]
    source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_hrad_sg_prep : Form Cell :=
  { id := "ces_hrad_sg_prep"
    lexeme := Lexemes.ces_hrad
    cell := prep_sg
    form := "hradu"
    morphs := ["hrad", "u"]
    source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_hrad_sg_dat : Form Cell :=
  { id := "ces_hrad_sg_dat"
    lexeme := Lexemes.ces_hrad
    cell := dat_sg
    form := "hradu"
    morphs := ["hrad", "u"]
    source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_hrad_sg_ins : Form Cell :=
  { id := "ces_hrad_sg_ins"
    lexeme := Lexemes.ces_hrad
    cell := ins_sg
    form := "hradem"
    morphs := ["hrad", "em"]
    source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_my_nom : Form Cell :=
  { id := "ces_my_nom"
    lexeme := Lexemes.ces_my
    cell := nom_pl
    form := "my"
    morphs := ["my"]
    source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_my_acc : Form Cell :=
  { id := "ces_my_acc"
    lexeme := Lexemes.ces_my
    cell := acc_pl
    form := "nás"
    morphs := ["ná", "s"]
    source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_my_gen : Form Cell :=
  { id := "ces_my_gen"
    lexeme := Lexemes.ces_my
    cell := gen_pl
    form := "nás"
    morphs := ["ná", "s"]
    source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_my_prep : Form Cell :=
  { id := "ces_my_prep"
    lexeme := Lexemes.ces_my
    cell := prep_pl
    form := "nás"
    morphs := ["ná", "s"]
    source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_my_dat : Form Cell :=
  { id := "ces_my_dat"
    lexeme := Lexemes.ces_my
    cell := dat_pl
    form := "nám"
    morphs := ["ná", "m"]
    source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_my_ins : Form Cell :=
  { id := "ces_my_ins"
    lexeme := Lexemes.ces_my
    cell := ins_pl
    form := "námi"
    morphs := ["ná", "mi"]
    source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_mesto_sg_nom : Form Cell :=
  { id := "ces_mesto_sg_nom"
    lexeme := Lexemes.ces_mesto
    cell := nom_sg
    form := "město"
    morphs := ["měst", "o"]
    source := [
      ⟨"caha-2009", "(56)"⟩
    ] }

def ces_mesto_sg_acc : Form Cell :=
  { id := "ces_mesto_sg_acc"
    lexeme := Lexemes.ces_mesto
    cell := acc_sg
    form := "město"
    morphs := ["měst", "o"]
    source := [
      ⟨"caha-2009", "(56)"⟩
    ] }

def ces_mesto_sg_gen : Form Cell :=
  { id := "ces_mesto_sg_gen"
    lexeme := Lexemes.ces_mesto
    cell := gen_sg
    form := "města"
    morphs := ["měst", "a"]
    source := [
      ⟨"caha-2009", "(56)"⟩
    ] }

def ces_mesto_sg_prep : Form Cell :=
  { id := "ces_mesto_sg_prep"
    lexeme := Lexemes.ces_mesto
    cell := prep_sg
    form := "městu"
    morphs := ["měst", "u"]
    source := [
      ⟨"caha-2009", "(56)"⟩
    ] }

def ces_mesto_sg_dat : Form Cell :=
  { id := "ces_mesto_sg_dat"
    lexeme := Lexemes.ces_mesto
    cell := dat_sg
    form := "městu"
    morphs := ["měst", "u"]
    source := [
      ⟨"caha-2009", "(56)"⟩
    ] }

def ces_mesto_sg_ins : Form Cell :=
  { id := "ces_mesto_sg_ins"
    lexeme := Lexemes.ces_mesto
    cell := ins_sg
    form := "městem"
    morphs := ["měst", "em"]
    source := [
      ⟨"caha-2009", "(56)"⟩
    ] }

def ces_vetsi_nsg_nom : Form Cell :=
  { id := "ces_vetsi_nsg_nom"
    lexeme := Lexemes.ces_vetsi
    cell := nom_sg_n
    form := "větší"
    morphs := ["větš", "í"]
    source := [
      ⟨"caha-2009", "(57)"⟩
    ] }

def ces_vetsi_nsg_acc : Form Cell :=
  { id := "ces_vetsi_nsg_acc"
    lexeme := Lexemes.ces_vetsi
    cell := acc_sg_n
    form := "větší"
    morphs := ["větš", "í"]
    source := [
      ⟨"caha-2009", "(57)"⟩
    ] }

def ces_vetsi_nsg_gen : Form Cell :=
  { id := "ces_vetsi_nsg_gen"
    lexeme := Lexemes.ces_vetsi
    cell := gen_sg_n
    form := "většího"
    morphs := ["větš", "ího"]
    source := [
      ⟨"caha-2009", "(57)"⟩
    ] }

def ces_vetsi_nsg_prep : Form Cell :=
  { id := "ces_vetsi_nsg_prep"
    lexeme := Lexemes.ces_vetsi
    cell := prep_sg_n
    form := "větším"
    morphs := ["větš", "ím"]
    source := [
      ⟨"caha-2009", "(57)"⟩
    ] }

def ces_vetsi_nsg_dat : Form Cell :=
  { id := "ces_vetsi_nsg_dat"
    lexeme := Lexemes.ces_vetsi
    cell := dat_sg_n
    form := "většímu"
    morphs := ["větš", "ímu"]
    source := [
      ⟨"caha-2009", "(57)"⟩
    ] }

def ces_vetsi_nsg_ins : Form Cell :=
  { id := "ces_vetsi_nsg_ins"
    lexeme := Lexemes.ces_vetsi
    cell := ins_sg_n
    form := "větším"
    morphs := ["větš", "ím"]
    source := [
      ⟨"caha-2009", "(57)"⟩
    ] }

def ces_ono_nom : Form Cell :=
  { id := "ces_ono_nom"
    lexeme := Lexemes.ces_ono
    cell := nom_sg
    form := "ono"
    morphs := ["ono"]
    source := [
      ⟨"caha-2009", "(58)"⟩
    ] }

def ces_ono_acc : Form Cell :=
  { id := "ces_ono_acc"
    lexeme := Lexemes.ces_ono
    cell := acc_sg
    form := "je"
    morphs := ["j", "e"]
    source := [
      ⟨"caha-2009", "(58)"⟩
    ] }

def ces_ono_gen : Form Cell :=
  { id := "ces_ono_gen"
    lexeme := Lexemes.ces_ono
    cell := gen_sg
    form := "jeho"
    morphs := ["j", "eho"]
    source := [
      ⟨"caha-2009", "(58)"⟩
    ] }

def ces_ono_prep : Form Cell :=
  { id := "ces_ono_prep"
    lexeme := Lexemes.ces_ono
    cell := prep_sg
    form := "jem"
    morphs := ["j", "em"]
    source := [
      ⟨"caha-2009", "(58)"⟩
    ] }

def ces_ono_dat : Form Cell :=
  { id := "ces_ono_dat"
    lexeme := Lexemes.ces_ono
    cell := dat_sg
    form := "jemu"
    morphs := ["j", "emu"]
    source := [
      ⟨"caha-2009", "(58)"⟩
    ] }

def ces_ono_ins : Form Cell :=
  { id := "ces_ono_ins"
    lexeme := Lexemes.ces_ono
    cell := ins_sg
    form := "jím"
    morphs := ["j", "ím"]
    source := [
      ⟨"caha-2009", "(58)"⟩
    ] }

def ces_nase_nsg_nom : Form Cell :=
  { id := "ces_nase_nsg_nom"
    lexeme := Lexemes.ces_nase
    cell := nom_sg_n
    form := "naše"
    morphs := ["naš", "e"]
    source := [
      ⟨"caha-2009", "(62)"⟩
    ] }

def ces_nase_nsg_acc : Form Cell :=
  { id := "ces_nase_nsg_acc"
    lexeme := Lexemes.ces_nase
    cell := acc_sg_n
    form := "naše"
    morphs := ["naš", "e"]
    source := [
      ⟨"caha-2009", "(62)"⟩
    ] }

def ces_nase_nsg_gen : Form Cell :=
  { id := "ces_nase_nsg_gen"
    lexeme := Lexemes.ces_nase
    cell := gen_sg_n
    form := "našeho"
    morphs := ["naš", "eho"]
    source := [
      ⟨"caha-2009", "(62)"⟩
    ] }

def ces_nase_nsg_prep : Form Cell :=
  { id := "ces_nase_nsg_prep"
    lexeme := Lexemes.ces_nase
    cell := prep_sg_n
    form := "našem"
    morphs := ["naš", "em"]
    source := [
      ⟨"caha-2009", "(62)"⟩
    ] }

def ces_nase_nsg_dat : Form Cell :=
  { id := "ces_nase_nsg_dat"
    lexeme := Lexemes.ces_nase
    cell := dat_sg_n
    form := "našemu"
    morphs := ["naš", "emu"]
    source := [
      ⟨"caha-2009", "(62)"⟩
    ] }

def ces_nase_nsg_ins : Form Cell :=
  { id := "ces_nase_nsg_ins"
    lexeme := Lexemes.ces_nase
    cell := ins_sg_n
    form := "naším"
    morphs := ["naš", "ím"]
    source := [
      ⟨"caha-2009", "(62)"⟩
    ] }

def ces_vetsi_fsg_nom : Form Cell :=
  { id := "ces_vetsi_fsg_nom"
    lexeme := Lexemes.ces_vetsi
    cell := nom_sg_f
    form := "větší"
    morphs := ["větš", "í"]
    source := [
      ⟨"caha-2009", "n. 25"⟩
    ] }

def ces_vetsi_fsg_acc : Form Cell :=
  { id := "ces_vetsi_fsg_acc"
    lexeme := Lexemes.ces_vetsi
    cell := acc_sg_f
    form := "větší"
    morphs := ["větš", "í"]
    source := [
      ⟨"caha-2009", "n. 25"⟩
    ] }

def ces_vetsi_fsg_gen : Form Cell :=
  { id := "ces_vetsi_fsg_gen"
    lexeme := Lexemes.ces_vetsi
    cell := gen_sg_f
    form := "větší"
    morphs := ["větš", "í"]
    source := [
      ⟨"caha-2009", "n. 25"⟩
    ] }

def ces_vetsi_fsg_prep : Form Cell :=
  { id := "ces_vetsi_fsg_prep"
    lexeme := Lexemes.ces_vetsi
    cell := prep_sg_f
    form := "větší"
    morphs := ["větš", "í"]
    source := [
      ⟨"caha-2009", "n. 25"⟩
    ] }

def ces_vetsi_fsg_dat : Form Cell :=
  { id := "ces_vetsi_fsg_dat"
    lexeme := Lexemes.ces_vetsi
    cell := dat_sg_f
    form := "větší"
    morphs := ["větš", "í"]
    source := [
      ⟨"caha-2009", "n. 25"⟩
    ] }

def ces_vetsi_fsg_ins : Form Cell :=
  { id := "ces_vetsi_fsg_ins"
    lexeme := Lexemes.ces_vetsi
    cell := ins_sg_f
    form := "větší"
    morphs := ["větš", "í"]
    source := [
      ⟨"caha-2009", "n. 25"⟩
    ] }

def ces_vetsi_npl_nom : Form Cell :=
  { id := "ces_vetsi_npl_nom"
    lexeme := Lexemes.ces_vetsi
    cell := nom_pl_n
    form := "větší"
    morphs := ["větš", "í"]
    source := [
      ⟨"caha-2009", "(63)"⟩
    ] }

def ces_vetsi_npl_acc : Form Cell :=
  { id := "ces_vetsi_npl_acc"
    lexeme := Lexemes.ces_vetsi
    cell := acc_pl_n
    form := "větší"
    morphs := ["větš", "í"]
    source := [
      ⟨"caha-2009", "(63)"⟩
    ] }

def ces_vetsi_npl_gen : Form Cell :=
  { id := "ces_vetsi_npl_gen"
    lexeme := Lexemes.ces_vetsi
    cell := gen_pl_n
    form := "větších"
    morphs := ["větš", "ích"]
    source := [
      ⟨"caha-2009", "(63)"⟩
    ] }

def ces_vetsi_npl_prep : Form Cell :=
  { id := "ces_vetsi_npl_prep"
    lexeme := Lexemes.ces_vetsi
    cell := prep_pl_n
    form := "větších"
    morphs := ["větš", "ích"]
    source := [
      ⟨"caha-2009", "(63)"⟩
    ] }

def ces_vetsi_npl_dat : Form Cell :=
  { id := "ces_vetsi_npl_dat"
    lexeme := Lexemes.ces_vetsi
    cell := dat_pl_n
    form := "větším"
    morphs := ["větš", "ím"]
    source := [
      ⟨"caha-2009", "(63)"⟩
    ] }

def ces_vetsi_npl_ins : Form Cell :=
  { id := "ces_vetsi_npl_ins"
    lexeme := Lexemes.ces_vetsi
    cell := ins_pl_n
    form := "většími"
    morphs := ["větš", "ími"]
    source := [
      ⟨"caha-2009", "(63)"⟩
    ] }

def ces_ona_npl_nom : Form Cell :=
  { id := "ces_ona_npl_nom"
    lexeme := Lexemes.ces_oni
    cell := nom_pl
    form := "ona"
    morphs := ["on", "a"]
    source := [
      ⟨"caha-2009", "(64)"⟩
    ] }

def ces_ona_npl_acc : Form Cell :=
  { id := "ces_ona_npl_acc"
    lexeme := Lexemes.ces_oni
    cell := acc_pl
    form := "je"
    morphs := ["j", "e"]
    source := [
      ⟨"caha-2009", "(64)"⟩
    ] }

def ces_ona_npl_gen : Form Cell :=
  { id := "ces_ona_npl_gen"
    lexeme := Lexemes.ces_oni
    cell := gen_pl
    form := "jich"
    morphs := ["j", "ich"]
    source := [
      ⟨"caha-2009", "(64)"⟩
    ] }

def ces_ona_npl_prep : Form Cell :=
  { id := "ces_ona_npl_prep"
    lexeme := Lexemes.ces_oni
    cell := prep_pl
    form := "jich"
    morphs := ["j", "ich"]
    source := [
      ⟨"caha-2009", "(64)"⟩
    ] }

def ces_ona_npl_dat : Form Cell :=
  { id := "ces_ona_npl_dat"
    lexeme := Lexemes.ces_oni
    cell := dat_pl
    form := "jim"
    morphs := ["j", "im"]
    source := [
      ⟨"caha-2009", "(64)"⟩
    ] }

def ces_ona_npl_ins : Form Cell :=
  { id := "ces_ona_npl_ins"
    lexeme := Lexemes.ces_oni
    cell := ins_pl
    form := "jimi"
    morphs := ["j", "imi"]
    source := [
      ⟨"caha-2009", "(64)"⟩
    ] }

def ces_ta_nom : Form Cell :=
  { id := "ces_ta_nom"
    lexeme := Lexemes.ces_ten
    cell := nom_sg_f
    form := "ta"
    morphs := ["t", "a"]
    source := [
      ⟨"caha-2009", "n. 26"⟩
    ] }

def ces_ta_acc : Form Cell :=
  { id := "ces_ta_acc"
    lexeme := Lexemes.ces_ten
    cell := acc_sg_f
    form := "tu"
    morphs := ["t", "u"]
    source := [
      ⟨"caha-2009", "n. 26"⟩
    ] }

def ces_ta_gen : Form Cell :=
  { id := "ces_ta_gen"
    lexeme := Lexemes.ces_ten
    cell := gen_sg_f
    form := "té"
    morphs := ["t", "é"]
    source := [
      ⟨"caha-2009", "n. 26"⟩
    ] }

def ces_ta_prep : Form Cell :=
  { id := "ces_ta_prep"
    lexeme := Lexemes.ces_ten
    cell := prep_sg_f
    form := "té"
    morphs := ["t", "é"]
    source := [
      ⟨"caha-2009", "n. 26"⟩
    ] }

def ces_ta_dat : Form Cell :=
  { id := "ces_ta_dat"
    lexeme := Lexemes.ces_ten
    cell := dat_sg_f
    form := "té"
    morphs := ["t", "é"]
    source := [
      ⟨"caha-2009", "n. 26"⟩
    ] }

def ces_ta_ins : Form Cell :=
  { id := "ces_ta_ins"
    lexeme := Lexemes.ces_ten
    cell := ins_sg_f
    form := "tou"
    morphs := ["t", "ou"]
    source := [
      ⟨"caha-2009", "n. 26"⟩
    ] }

def ces_dva_nom : Form Cell :=
  { id := "ces_dva_nom"
    lexeme := Lexemes.ces_dva
    cell := nom_du_m
    form := "dva"
    morphs := ["dv", "a"]
    source := [
      ⟨"caha-2009", "(65)"⟩
    ] }

def ces_dva_acc : Form Cell :=
  { id := "ces_dva_acc"
    lexeme := Lexemes.ces_dva
    cell := acc_du_m
    form := "dva"
    morphs := ["dv", "a"]
    source := [
      ⟨"caha-2009", "(65)"⟩
    ] }

def ces_dva_gen : Form Cell :=
  { id := "ces_dva_gen"
    lexeme := Lexemes.ces_dva
    cell := gen_du_m
    form := "dvou"
    morphs := ["dv", "ou"]
    source := [
      ⟨"caha-2009", "(65)"⟩
    ] }

def ces_dva_prep : Form Cell :=
  { id := "ces_dva_prep"
    lexeme := Lexemes.ces_dva
    cell := prep_du_m
    form := "dvou"
    morphs := ["dv", "ou"]
    source := [
      ⟨"caha-2009", "(65)"⟩
    ] }

def ces_dva_dat : Form Cell :=
  { id := "ces_dva_dat"
    lexeme := Lexemes.ces_dva
    cell := dat_du_m
    form := "dvěma"
    morphs := ["dv", "ěma"]
    source := [
      ⟨"caha-2009", "(65)"⟩
    ] }

def ces_dva_ins : Form Cell :=
  { id := "ces_dva_ins"
    lexeme := Lexemes.ces_dva
    cell := ins_du_m
    form := "dvěma"
    morphs := ["dv", "ěma"]
    source := [
      ⟨"caha-2009", "(65)"⟩
    ] }

def ces_pet_nom : Form Cell :=
  { id := "ces_pet_nom"
    lexeme := Lexemes.ces_pet
    cell := nom_pl
    form := "pět"
    morphs := ["pět"]
    source := [
      ⟨"caha-2009", "(66)"⟩
    ] }

def ces_pet_acc : Form Cell :=
  { id := "ces_pet_acc"
    lexeme := Lexemes.ces_pet
    cell := acc_pl
    form := "pět"
    morphs := ["pět"]
    source := [
      ⟨"caha-2009", "(66)"⟩
    ] }

def ces_pet_gen : Form Cell :=
  { id := "ces_pet_gen"
    lexeme := Lexemes.ces_pet
    cell := gen_pl
    form := "pěti"
    morphs := ["pět", "i"]
    source := [
      ⟨"caha-2009", "(66)"⟩
    ] }

def ces_pet_prep : Form Cell :=
  { id := "ces_pet_prep"
    lexeme := Lexemes.ces_pet
    cell := prep_pl
    form := "pěti"
    morphs := ["pět", "i"]
    source := [
      ⟨"caha-2009", "(66)"⟩
    ] }

def ces_pet_dat : Form Cell :=
  { id := "ces_pet_dat"
    lexeme := Lexemes.ces_pet
    cell := dat_pl
    form := "pěti"
    morphs := ["pět", "i"]
    source := [
      ⟨"caha-2009", "(66)"⟩
    ] }

def ces_pet_ins : Form Cell :=
  { id := "ces_pet_ins"
    lexeme := Lexemes.ces_pet
    cell := ins_pl
    form := "pěti"
    morphs := ["pět", "i"]
    source := [
      ⟨"caha-2009", "(66)"⟩
    ] }

def slk_ona_nom : Form Cell :=
  { id := "slk_ona_nom"
    lexeme := Lexemes.slk_ona
    cell := nom_sg
    form := "ona"
    morphs := ["ona"]
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_ona_acc : Form Cell :=
  { id := "slk_ona_acc"
    lexeme := Lexemes.slk_ona
    cell := acc_sg
    form := "ju"
    morphs := ["j", "u"]
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_ona_gen : Form Cell :=
  { id := "slk_ona_gen"
    lexeme := Lexemes.slk_ona
    cell := gen_sg
    form := "jej"
    morphs := ["j", "ej"]
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_ona_prep : Form Cell :=
  { id := "slk_ona_prep"
    lexeme := Lexemes.slk_ona
    cell := prep_sg
    form := "jej"
    morphs := ["j", "ej"]
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_ona_dat : Form Cell :=
  { id := "slk_ona_dat"
    lexeme := Lexemes.slk_ona
    cell := dat_sg
    form := "njej"
    morphs := ["nj", "ej"]
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_ona_ins : Form Cell :=
  { id := "slk_ona_ins"
    lexeme := Lexemes.slk_ona
    cell := ins_sg
    form := "njou"
    morphs := ["nj", "ou"]
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_nase_fsg_nom : Form Cell :=
  { id := "slk_nase_fsg_nom"
    lexeme := Lexemes.slk_nase
    cell := nom_sg_f
    form := "naša"
    morphs := ["naš", "a"]
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_nase_fsg_acc : Form Cell :=
  { id := "slk_nase_fsg_acc"
    lexeme := Lexemes.slk_nase
    cell := acc_sg_f
    form := "našu"
    morphs := ["naš", "u"]
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_nase_fsg_gen : Form Cell :=
  { id := "slk_nase_fsg_gen"
    lexeme := Lexemes.slk_nase
    cell := gen_sg_f
    form := "našej"
    morphs := ["naš", "ej"]
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_nase_fsg_prep : Form Cell :=
  { id := "slk_nase_fsg_prep"
    lexeme := Lexemes.slk_nase
    cell := prep_sg_f
    form := "našej"
    morphs := ["naš", "ej"]
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_nase_fsg_dat : Form Cell :=
  { id := "slk_nase_fsg_dat"
    lexeme := Lexemes.slk_nase
    cell := dat_sg_f
    form := "našej"
    morphs := ["naš", "ej"]
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_nase_fsg_ins : Form Cell :=
  { id := "slk_nase_fsg_ins"
    lexeme := Lexemes.slk_nase
    cell := ins_sg_f
    form := "našou"
    morphs := ["naš", "ou"]
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_ulica_sg_nom : Form Cell :=
  { id := "slk_ulica_sg_nom"
    lexeme := Lexemes.slk_ulica
    cell := nom_sg
    form := "ulica"
    morphs := ["ulic", "a"]
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_ulica_sg_acc : Form Cell :=
  { id := "slk_ulica_sg_acc"
    lexeme := Lexemes.slk_ulica
    cell := acc_sg
    form := "ulicu"
    morphs := ["ulic", "u"]
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_ulica_sg_gen : Form Cell :=
  { id := "slk_ulica_sg_gen"
    lexeme := Lexemes.slk_ulica
    cell := gen_sg
    form := "ulice"
    morphs := ["ulic", "e"]
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_ulica_sg_prep : Form Cell :=
  { id := "slk_ulica_sg_prep"
    lexeme := Lexemes.slk_ulica
    cell := prep_sg
    form := "ulici"
    morphs := ["ulic", "i"]
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_ulica_sg_dat : Form Cell :=
  { id := "slk_ulica_sg_dat"
    lexeme := Lexemes.slk_ulica
    cell := dat_sg
    form := "ulici"
    morphs := ["ulic", "i"]
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_ulica_sg_ins : Form Cell :=
  { id := "slk_ulica_sg_ins"
    lexeme := Lexemes.slk_ulica
    cell := ins_sg
    form := "ulicou"
    morphs := ["ulic", "ou"]
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_tlac_sg_nom : Form Cell :=
  { id := "slk_tlac_sg_nom"
    lexeme := Lexemes.slk_tlac
    cell := nom_sg
    form := "tlač"
    morphs := ["tlač", "ø"]
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_tlac_sg_acc : Form Cell :=
  { id := "slk_tlac_sg_acc"
    lexeme := Lexemes.slk_tlac
    cell := acc_sg
    form := "tlač"
    morphs := ["tlač", "ø"]
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_tlac_sg_gen : Form Cell :=
  { id := "slk_tlac_sg_gen"
    lexeme := Lexemes.slk_tlac
    cell := gen_sg
    form := "tlače"
    morphs := ["tlač", "e"]
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_tlac_sg_prep : Form Cell :=
  { id := "slk_tlac_sg_prep"
    lexeme := Lexemes.slk_tlac
    cell := prep_sg
    form := "tlači"
    morphs := ["tlač", "i"]
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_tlac_sg_dat : Form Cell :=
  { id := "slk_tlac_sg_dat"
    lexeme := Lexemes.slk_tlac
    cell := dat_sg
    form := "tlači"
    morphs := ["tlač", "i"]
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_tlac_sg_ins : Form Cell :=
  { id := "slk_tlac_sg_ins"
    lexeme := Lexemes.slk_tlac
    cell := ins_sg
    form := "tlačou"
    morphs := ["tlač", "ou"]
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def ukr_kraj_sg_nom : Form Cell :=
  { id := "ukr_kraj_sg_nom"
    lexeme := Lexemes.ukr_kraj
    cell := nom_sg
    form := "kraj"
    morphs := ["kraj", "ø"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kraj_sg_acc : Form Cell :=
  { id := "ukr_kraj_sg_acc"
    lexeme := Lexemes.ukr_kraj
    cell := acc_sg
    form := "kraj"
    morphs := ["kraj", "ø"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kraj_sg_gen : Form Cell :=
  { id := "ukr_kraj_sg_gen"
    lexeme := Lexemes.ukr_kraj
    cell := gen_sg
    form := "kráju"
    morphs := ["kráj", "u"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kraj_sg_prep : Form Cell :=
  { id := "ukr_kraj_sg_prep"
    lexeme := Lexemes.ukr_kraj
    cell := prep_sg
    form := "krajú"
    morphs := ["kraj", "ú"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kraj_sg_dat : Form Cell :=
  { id := "ukr_kraj_sg_dat"
    lexeme := Lexemes.ukr_kraj
    cell := dat_sg
    form := "krájevi"
    morphs := ["kráj", "evi"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kraj_sg_ins : Form Cell :=
  { id := "ukr_kraj_sg_ins"
    lexeme := Lexemes.ukr_kraj
    cell := ins_sg
    form := "krájem"
    morphs := ["kráj", "em"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_velykyj_pl_nom : Form Cell :=
  { id := "ukr_velykyj_pl_nom"
    lexeme := Lexemes.ukr_velykyj
    cell := nom_pl
    form := "velíki"
    morphs := ["velík", "i"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_velykyj_pl_acc : Form Cell :=
  { id := "ukr_velykyj_pl_acc"
    lexeme := Lexemes.ukr_velykyj
    cell := acc_pl
    form := "velíki"
    morphs := ["velík", "i"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_velykyj_pl_gen : Form Cell :=
  { id := "ukr_velykyj_pl_gen"
    lexeme := Lexemes.ukr_velykyj
    cell := gen_pl
    form := "velíkıch"
    morphs := ["velík", "ıch"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_velykyj_pl_prep : Form Cell :=
  { id := "ukr_velykyj_pl_prep"
    lexeme := Lexemes.ukr_velykyj
    cell := prep_pl
    form := "velíkıch"
    morphs := ["velík", "ıch"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_velykyj_pl_dat : Form Cell :=
  { id := "ukr_velykyj_pl_dat"
    lexeme := Lexemes.ukr_velykyj
    cell := dat_pl
    form := "velíkım"
    morphs := ["velík", "ım"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_velykyj_pl_ins : Form Cell :=
  { id := "ukr_velykyj_pl_ins"
    lexeme := Lexemes.ukr_velykyj
    cell := ins_pl
    form := "velíkımı"
    morphs := ["velík", "ımı"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_znannja_sg_nom : Form Cell :=
  { id := "ukr_znannja_sg_nom"
    lexeme := Lexemes.ukr_znannja
    cell := nom_sg
    form := "znannjá"
    morphs := ["znann", "já"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_znannja_sg_acc : Form Cell :=
  { id := "ukr_znannja_sg_acc"
    lexeme := Lexemes.ukr_znannja
    cell := acc_sg
    form := "znannjá"
    morphs := ["znann", "já"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_znannja_sg_gen : Form Cell :=
  { id := "ukr_znannja_sg_gen"
    lexeme := Lexemes.ukr_znannja
    cell := gen_sg
    form := "znannjá"
    morphs := ["znann", "já"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_znannja_sg_prep : Form Cell :=
  { id := "ukr_znannja_sg_prep"
    lexeme := Lexemes.ukr_znannja
    cell := prep_sg
    form := "znanni̇́"
    morphs := ["znann", "i̇́"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_znannja_sg_dat : Form Cell :=
  { id := "ukr_znannja_sg_dat"
    lexeme := Lexemes.ukr_znannja
    cell := dat_sg
    form := "znannjú"
    morphs := ["znann", "jú"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_znannja_sg_ins : Form Cell :=
  { id := "ukr_znannja_sg_ins"
    lexeme := Lexemes.ukr_znannja
    cell := ins_sg
    form := "znannjám"
    morphs := ["znann", "jám"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_my_nom : Form Cell :=
  { id := "ukr_my_nom"
    lexeme := Lexemes.ukr_my
    cell := nom_pl
    form := "mı"
    morphs := ["mı"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_my_acc : Form Cell :=
  { id := "ukr_my_acc"
    lexeme := Lexemes.ukr_my
    cell := acc_pl
    form := "nas"
    morphs := ["nas"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_my_gen : Form Cell :=
  { id := "ukr_my_gen"
    lexeme := Lexemes.ukr_my
    cell := gen_pl
    form := "nas"
    morphs := ["nas"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_my_prep : Form Cell :=
  { id := "ukr_my_prep"
    lexeme := Lexemes.ukr_my
    cell := prep_pl
    form := "nas"
    morphs := ["nas"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_my_dat : Form Cell :=
  { id := "ukr_my_dat"
    lexeme := Lexemes.ukr_my
    cell := dat_pl
    form := "nam"
    morphs := ["nam"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_my_ins : Form Cell :=
  { id := "ukr_my_ins"
    lexeme := Lexemes.ukr_my
    cell := ins_pl
    form := "námı"
    morphs := ["námı"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kasyr_sg_nom : Form Cell :=
  { id := "ukr_kasyr_sg_nom"
    lexeme := Lexemes.ukr_kasyr
    cell := nom_sg
    form := "kasír"
    morphs := ["kasír", "ø"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kasyr_sg_acc : Form Cell :=
  { id := "ukr_kasyr_sg_acc"
    lexeme := Lexemes.ukr_kasyr
    cell := acc_sg
    form := "kasíra"
    morphs := ["kasír", "a"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kasyr_sg_gen : Form Cell :=
  { id := "ukr_kasyr_sg_gen"
    lexeme := Lexemes.ukr_kasyr
    cell := gen_sg
    form := "kasíra"
    morphs := ["kasír", "a"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kasyr_sg_prep : Form Cell :=
  { id := "ukr_kasyr_sg_prep"
    lexeme := Lexemes.ukr_kasyr
    cell := prep_sg
    form := "kasírovi"
    morphs := ["kasír", "ovi"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kasyr_sg_dat : Form Cell :=
  { id := "ukr_kasyr_sg_dat"
    lexeme := Lexemes.ukr_kasyr
    cell := dat_sg
    form := "kasírovi"
    morphs := ["kasír", "ovi"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kasyr_sg_ins : Form Cell :=
  { id := "ukr_kasyr_sg_ins"
    lexeme := Lexemes.ukr_kasyr
    cell := ins_sg
    form := "kasírom"
    morphs := ["kasír", "om"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kasyr_pl_nom : Form Cell :=
  { id := "ukr_kasyr_pl_nom"
    lexeme := Lexemes.ukr_kasyr
    cell := nom_pl
    form := "kasírı"
    morphs := ["kasír", "ı"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kasyr_pl_acc : Form Cell :=
  { id := "ukr_kasyr_pl_acc"
    lexeme := Lexemes.ukr_kasyr
    cell := acc_pl
    form := "kasíriv"
    morphs := ["kasír", "iv"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kasyr_pl_gen : Form Cell :=
  { id := "ukr_kasyr_pl_gen"
    lexeme := Lexemes.ukr_kasyr
    cell := gen_pl
    form := "kasíriv"
    morphs := ["kasír", "iv"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kasyr_pl_prep : Form Cell :=
  { id := "ukr_kasyr_pl_prep"
    lexeme := Lexemes.ukr_kasyr
    cell := prep_pl
    form := "kasírach"
    morphs := ["kasír", "ach"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kasyr_pl_dat : Form Cell :=
  { id := "ukr_kasyr_pl_dat"
    lexeme := Lexemes.ukr_kasyr
    cell := dat_pl
    form := "kasíram"
    morphs := ["kasír", "am"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kasyr_pl_ins : Form Cell :=
  { id := "ukr_kasyr_pl_ins"
    lexeme := Lexemes.ukr_kasyr
    cell := ins_pl
    form := "kasíramı"
    morphs := ["kasír", "amı"]
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_maty_sg_nom : Form Cell :=
  { id := "ukr_maty_sg_nom"
    lexeme := Lexemes.ukr_maty
    cell := nom_sg
    form := "mátı"
    morphs := ["mát", "ı"]
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_maty_sg_acc : Form Cell :=
  { id := "ukr_maty_sg_acc"
    lexeme := Lexemes.ukr_maty
    cell := acc_sg
    form := "mátir"
    morphs := ["mát", "ir"]
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_maty_sg_gen : Form Cell :=
  { id := "ukr_maty_sg_gen"
    lexeme := Lexemes.ukr_maty
    cell := gen_sg
    form := "máteri"
    morphs := ["mát", "er", "i"]
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_maty_sg_prep : Form Cell :=
  { id := "ukr_maty_sg_prep"
    lexeme := Lexemes.ukr_maty
    cell := prep_sg
    form := "máteri"
    morphs := ["mát", "er", "i"]
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_maty_sg_dat : Form Cell :=
  { id := "ukr_maty_sg_dat"
    lexeme := Lexemes.ukr_maty
    cell := dat_sg
    form := "máteri"
    morphs := ["mát", "er", "i"]
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_maty_sg_ins : Form Cell :=
  { id := "ukr_maty_sg_ins"
    lexeme := Lexemes.ukr_maty
    cell := ins_sg
    form := "mátirju"
    morphs := ["mát", "ir", "ju"]
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_ruka_sg_nom : Form Cell :=
  { id := "ukr_ruka_sg_nom"
    lexeme := Lexemes.ukr_ruka
    cell := nom_sg
    form := "ruká"
    morphs := ["ruk", "á"]
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_ruka_sg_acc : Form Cell :=
  { id := "ukr_ruka_sg_acc"
    lexeme := Lexemes.ukr_ruka
    cell := acc_sg
    form := "rúku"
    morphs := ["rúk", "u"]
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_ruka_sg_gen : Form Cell :=
  { id := "ukr_ruka_sg_gen"
    lexeme := Lexemes.ukr_ruka
    cell := gen_sg
    form := "rukí"
    morphs := ["ruk", "í"]
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_ruka_sg_prep : Form Cell :=
  { id := "ukr_ruka_sg_prep"
    lexeme := Lexemes.ukr_ruka
    cell := prep_sg
    form := "ruci̇́"
    morphs := ["ruc", "i̇́"]
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_ruka_sg_dat : Form Cell :=
  { id := "ukr_ruka_sg_dat"
    lexeme := Lexemes.ukr_ruka
    cell := dat_sg
    form := "ruci̇́"
    morphs := ["ruc", "i̇́"]
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_ruka_sg_ins : Form Cell :=
  { id := "ukr_ruka_sg_ins"
    lexeme := Lexemes.ukr_ruka
    cell := ins_sg
    form := "rukóju"
    morphs := ["ruk", "óju"]
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_ja_nom : Form Cell :=
  { id := "ukr_ja_nom"
    lexeme := Lexemes.ukr_ja
    cell := nom_sg
    form := "ja"
    morphs := ["ja"]
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_ja_acc : Form Cell :=
  { id := "ukr_ja_acc"
    lexeme := Lexemes.ukr_ja
    cell := acc_sg
    form := "mené"
    morphs := ["mené"]
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_ja_gen : Form Cell :=
  { id := "ukr_ja_gen"
    lexeme := Lexemes.ukr_ja
    cell := gen_sg
    form := "mené"
    morphs := ["mené"]
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_ja_prep : Form Cell :=
  { id := "ukr_ja_prep"
    lexeme := Lexemes.ukr_ja
    cell := prep_sg
    form := "meni̇́"
    morphs := ["meni̇́"]
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_ja_dat : Form Cell :=
  { id := "ukr_ja_dat"
    lexeme := Lexemes.ukr_ja
    cell := dat_sg
    form := "meni̇́"
    morphs := ["meni̇́"]
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_ja_ins : Form Cell :=
  { id := "ukr_ja_ins"
    lexeme := Lexemes.ukr_ja
    cell := ins_sg
    form := "mnóju"
    morphs := ["mnóju"]
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_velykyj_msg_nom : Form Cell :=
  { id := "ukr_velykyj_msg_nom"
    lexeme := Lexemes.ukr_velykyj
    cell := nom_sg_m
    form := "velíkıj"
    morphs := ["velík", "ıj"]
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_velykyj_msg_acc : Form Cell :=
  { id := "ukr_velykyj_msg_acc"
    lexeme := Lexemes.ukr_velykyj
    cell := acc_sg_m
    form := "velíkıj"
    morphs := ["velík", "ıj"]
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_velykyj_msg_gen : Form Cell :=
  { id := "ukr_velykyj_msg_gen"
    lexeme := Lexemes.ukr_velykyj
    cell := gen_sg_m
    form := "velíkogo"
    morphs := ["velík", "ogo"]
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_velykyj_msg_prep : Form Cell :=
  { id := "ukr_velykyj_msg_prep"
    lexeme := Lexemes.ukr_velykyj
    cell := prep_sg_m
    form := "velíkomu"
    morphs := ["velík", "omu"]
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_velykyj_msg_dat : Form Cell :=
  { id := "ukr_velykyj_msg_dat"
    lexeme := Lexemes.ukr_velykyj
    cell := dat_sg_m
    form := "velíkomu"
    morphs := ["velík", "omu"]
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_velykyj_msg_ins : Form Cell :=
  { id := "ukr_velykyj_msg_ins"
    lexeme := Lexemes.ukr_velykyj
    cell := ins_sg_m
    form := "velíkım"
    morphs := ["velík", "ım"]
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_sto_nom : Form Cell :=
  { id := "ukr_sto_nom"
    lexeme := Lexemes.ukr_sto
    cell := nom_sg
    form := "sto"
    morphs := ["st", "o"]
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_sto_acc : Form Cell :=
  { id := "ukr_sto_acc"
    lexeme := Lexemes.ukr_sto
    cell := acc_sg
    form := "sto"
    morphs := ["st", "o"]
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_sto_gen : Form Cell :=
  { id := "ukr_sto_gen"
    lexeme := Lexemes.ukr_sto
    cell := gen_sg
    form := "sta"
    morphs := ["st", "a"]
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_sto_prep : Form Cell :=
  { id := "ukr_sto_prep"
    lexeme := Lexemes.ukr_sto
    cell := prep_sg
    form := "sta"
    morphs := ["st", "a"]
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_sto_dat : Form Cell :=
  { id := "ukr_sto_dat"
    lexeme := Lexemes.ukr_sto
    cell := dat_sg
    form := "sta"
    morphs := ["st", "a"]
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_sto_ins : Form Cell :=
  { id := "ukr_sto_ins"
    lexeme := Lexemes.ukr_sto
    cell := ins_sg
    form := "sta"
    morphs := ["st", "a"]
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_kraj_sg_2_nom : Form Cell :=
  { id := "ukr_kraj_sg_2_nom"
    lexeme := Lexemes.ukr_kraj
    cell := nom_sg
    form := "kraj"
    morphs := ["kraj", "ø"]
    source := [
      ⟨"caha-2009", "(70)"⟩
    ] }

def ukr_kraj_sg_2_acc : Form Cell :=
  { id := "ukr_kraj_sg_2_acc"
    lexeme := Lexemes.ukr_kraj
    cell := acc_sg
    form := "kraj"
    morphs := ["kraj", "ø"]
    source := [
      ⟨"caha-2009", "(70)"⟩
    ] }

def ukr_kraj_sg_2_gen : Form Cell :=
  { id := "ukr_kraj_sg_2_gen"
    lexeme := Lexemes.ukr_kraj
    cell := gen_sg
    form := "kráju"
    morphs := ["kráj", "u"]
    source := [
      ⟨"caha-2009", "(70)"⟩
    ] }

def ukr_kraj_sg_2_prep : Form Cell :=
  { id := "ukr_kraj_sg_2_prep"
    lexeme := Lexemes.ukr_kraj
    cell := prep_sg
    form := "kráji"
    morphs := ["kráj", "i"]
    source := [
      ⟨"caha-2009", "(70)"⟩
    ] }

def ukr_kraj_sg_2_dat : Form Cell :=
  { id := "ukr_kraj_sg_2_dat"
    lexeme := Lexemes.ukr_kraj
    cell := dat_sg
    form := "kráju"
    morphs := ["kráj", "u"]
    source := [
      ⟨"caha-2009", "(70)"⟩
    ] }

def ukr_kraj_sg_2_ins : Form Cell :=
  { id := "ukr_kraj_sg_2_ins"
    lexeme := Lexemes.ukr_kraj
    cell := ins_sg
    form := "krájem"
    morphs := ["kráj", "em"]
    source := [
      ⟨"caha-2009", "(70)"⟩
    ] }

def ukr_bezkrajij_msg_nom : Form Cell :=
  { id := "ukr_bezkrajij_msg_nom"
    lexeme := Lexemes.ukr_bezkrajij
    cell := nom_sg_m
    form := "bezkrajij"
    morphs := ["bezkraj", "ij"]
    source := [
      ⟨"caha-2009", "(71)"⟩
    ] }

def ukr_bezkrajij_msg_acc : Form Cell :=
  { id := "ukr_bezkrajij_msg_acc"
    lexeme := Lexemes.ukr_bezkrajij
    cell := acc_sg_m
    form := "bezkrajij"
    morphs := ["bezkraj", "ij"]
    source := [
      ⟨"caha-2009", "(71)"⟩
    ] }

def ukr_bezkrajij_msg_gen : Form Cell :=
  { id := "ukr_bezkrajij_msg_gen"
    lexeme := Lexemes.ukr_bezkrajij
    cell := gen_sg_m
    form := "bezkrajogo"
    morphs := ["bezkraj", "ogo"]
    source := [
      ⟨"caha-2009", "(71)"⟩
    ] }

def ukr_bezkrajij_msg_prep : Form Cell :=
  { id := "ukr_bezkrajij_msg_prep"
    lexeme := Lexemes.ukr_bezkrajij
    cell := prep_sg_m
    form := "bezkrajomu"
    morphs := ["bezkraj", "omu"]
    source := [
      ⟨"caha-2009", "(71)"⟩
    ] }

def ukr_bezkrajij_msg_dat : Form Cell :=
  { id := "ukr_bezkrajij_msg_dat"
    lexeme := Lexemes.ukr_bezkrajij
    cell := dat_sg_m
    form := "bezkrajomu"
    morphs := ["bezkraj", "omu"]
    source := [
      ⟨"caha-2009", "(71)"⟩
    ] }

def ukr_bezkrajij_msg_ins : Form Cell :=
  { id := "ukr_bezkrajij_msg_ins"
    lexeme := Lexemes.ukr_bezkrajij
    cell := ins_sg_m
    form := "bezkrajim"
    morphs := ["bezkraj", "im"]
    source := [
      ⟨"caha-2009", "(71)"⟩
    ] }

def ukr_bezkrajij_msg_2_nom : Form Cell :=
  { id := "ukr_bezkrajij_msg_2_nom"
    lexeme := Lexemes.ukr_bezkrajij
    cell := nom_sg_m
    form := "bezkrajij"
    morphs := ["bezkraj", "ij"]
    source := [
      ⟨"caha-2009", "(71)"⟩
    ] }

def ukr_bezkrajij_msg_2_acc : Form Cell :=
  { id := "ukr_bezkrajij_msg_2_acc"
    lexeme := Lexemes.ukr_bezkrajij
    cell := acc_sg_m
    form := "bezkrajij"
    morphs := ["bezkraj", "ij"]
    source := [
      ⟨"caha-2009", "(71)"⟩
    ] }

def ukr_bezkrajij_msg_2_gen : Form Cell :=
  { id := "ukr_bezkrajij_msg_2_gen"
    lexeme := Lexemes.ukr_bezkrajij
    cell := gen_sg_m
    form := "bezkrajogo"
    morphs := ["bezkraj", "ogo"]
    source := [
      ⟨"caha-2009", "(71)"⟩
    ] }

def ukr_bezkrajij_msg_2_prep : Form Cell :=
  { id := "ukr_bezkrajij_msg_2_prep"
    lexeme := Lexemes.ukr_bezkrajij
    cell := prep_sg_m
    form := "bezkrajim"
    morphs := ["bezkraj", "im"]
    source := [
      ⟨"caha-2009", "(71)"⟩
    ] }

def ukr_bezkrajij_msg_2_dat : Form Cell :=
  { id := "ukr_bezkrajij_msg_2_dat"
    lexeme := Lexemes.ukr_bezkrajij
    cell := dat_sg_m
    form := "bezkrajomu"
    morphs := ["bezkraj", "omu"]
    source := [
      ⟨"caha-2009", "(71)"⟩
    ] }

def ukr_bezkrajij_msg_2_ins : Form Cell :=
  { id := "ukr_bezkrajij_msg_2_ins"
    lexeme := Lexemes.ukr_bezkrajij
    cell := ins_sg_m
    form := "bezkrajim"
    morphs := ["bezkraj", "im"]
    source := [
      ⟨"caha-2009", "(71)"⟩
    ] }

def ukr_velykyj_msg_2_nom : Form Cell :=
  { id := "ukr_velykyj_msg_2_nom"
    lexeme := Lexemes.ukr_velykyj
    cell := nom_sg_m
    form := "velíkıj"
    morphs := ["velík", "ıj"]
    source := [
      ⟨"caha-2009", "(72)"⟩
    ] }

def ukr_velykyj_msg_2_acc : Form Cell :=
  { id := "ukr_velykyj_msg_2_acc"
    lexeme := Lexemes.ukr_velykyj
    cell := acc_sg_m
    form := "velíkıj"
    morphs := ["velík", "ıj"]
    source := [
      ⟨"caha-2009", "(72)"⟩
    ] }

def ukr_velykyj_msg_2_gen : Form Cell :=
  { id := "ukr_velykyj_msg_2_gen"
    lexeme := Lexemes.ukr_velykyj
    cell := gen_sg_m
    form := "velíkogo"
    morphs := ["velík", "ogo"]
    source := [
      ⟨"caha-2009", "(72)"⟩
    ] }

def ukr_velykyj_msg_2_prep : Form Cell :=
  { id := "ukr_velykyj_msg_2_prep"
    lexeme := Lexemes.ukr_velykyj
    cell := prep_sg_m
    form := "velíkim"
    morphs := ["velík", "im"]
    source := [
      ⟨"caha-2009", "(72)"⟩
    ] }

def ukr_velykyj_msg_2_dat : Form Cell :=
  { id := "ukr_velykyj_msg_2_dat"
    lexeme := Lexemes.ukr_velykyj
    cell := dat_sg_m
    form := "velíkomu"
    morphs := ["velík", "omu"]
    source := [
      ⟨"caha-2009", "(72)"⟩
    ] }

def ukr_velykyj_msg_2_ins : Form Cell :=
  { id := "ukr_velykyj_msg_2_ins"
    lexeme := Lexemes.ukr_velykyj
    cell := ins_sg_m
    form := "velíkım"
    morphs := ["velík", "ım"]
    source := [
      ⟨"caha-2009", "(72)"⟩
    ] }

def srp_sin_sg.paradigm : Paradigm Cell :=
  { id := "srp_sin_sg", lexeme := Lexemes.srp_sin,
    forms := [srp_sin_sg_nom, srp_sin_sg_acc, srp_sin_sg_gen, srp_sin_sg_prep, srp_sin_sg_dat,
      srp_sin_sg_ins],
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_grad_sg.paradigm : Paradigm Cell :=
  { id := "srp_grad_sg", lexeme := Lexemes.srp_grad,
    forms := [srp_grad_sg_nom, srp_grad_sg_acc, srp_grad_sg_gen, srp_grad_sg_prep, srp_grad_sg_dat,
      srp_grad_sg_ins],
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_muz_sg.paradigm : Paradigm Cell :=
  { id := "srp_muz_sg", lexeme := Lexemes.srp_muz,
    forms := [srp_muz_sg_nom, srp_muz_sg_acc, srp_muz_sg_gen, srp_muz_sg_prep, srp_muz_sg_dat,
      srp_muz_sg_ins],
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_selo_sg.paradigm : Paradigm Cell :=
  { id := "srp_selo_sg", lexeme := Lexemes.srp_selo,
    forms := [srp_selo_sg_nom, srp_selo_sg_acc, srp_selo_sg_gen, srp_selo_sg_prep, srp_selo_sg_dat,
      srp_selo_sg_ins],
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_srce_sg.paradigm : Paradigm Cell :=
  { id := "srp_srce_sg", lexeme := Lexemes.srp_srce,
    forms := [srp_srce_sg_nom, srp_srce_sg_acc, srp_srce_sg_gen, srp_srce_sg_prep, srp_srce_sg_dat,
      srp_srce_sg_ins],
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_ovca_sg.paradigm : Paradigm Cell :=
  { id := "srp_ovca_sg", lexeme := Lexemes.srp_ovca,
    forms := [srp_ovca_sg_nom, srp_ovca_sg_acc, srp_ovca_sg_gen, srp_ovca_sg_prep, srp_ovca_sg_dat,
      srp_ovca_sg_ins],
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_smrt_sg.paradigm : Paradigm Cell :=
  { id := "srp_smrt_sg", lexeme := Lexemes.srp_smrt,
    forms := [srp_smrt_sg_nom, srp_smrt_sg_acc, srp_smrt_sg_gen, srp_smrt_sg_prep, srp_smrt_sg_dat,
      srp_smrt_sg_ins],
    source := [
      ⟨"caha-2009", "(9)"⟩
    ] }

def srp_sin_pl.paradigm : Paradigm Cell :=
  { id := "srp_sin_pl", lexeme := Lexemes.srp_sin,
    forms := [srp_sin_pl_nom, srp_sin_pl_acc, srp_sin_pl_gen, srp_sin_pl_prep, srp_sin_pl_dat,
      srp_sin_pl_ins],
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_grad_pl.paradigm : Paradigm Cell :=
  { id := "srp_grad_pl", lexeme := Lexemes.srp_grad,
    forms := [srp_grad_pl_nom, srp_grad_pl_acc, srp_grad_pl_gen, srp_grad_pl_prep, srp_grad_pl_dat,
      srp_grad_pl_ins],
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_muz_pl.paradigm : Paradigm Cell :=
  { id := "srp_muz_pl", lexeme := Lexemes.srp_muz,
    forms := [srp_muz_pl_nom, srp_muz_pl_acc, srp_muz_pl_gen, srp_muz_pl_prep, srp_muz_pl_dat,
      srp_muz_pl_ins],
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_selo_pl.paradigm : Paradigm Cell :=
  { id := "srp_selo_pl", lexeme := Lexemes.srp_selo,
    forms := [srp_selo_pl_nom, srp_selo_pl_acc, srp_selo_pl_gen, srp_selo_pl_prep, srp_selo_pl_dat,
      srp_selo_pl_ins],
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_srce_pl.paradigm : Paradigm Cell :=
  { id := "srp_srce_pl", lexeme := Lexemes.srp_srce,
    forms := [srp_srce_pl_nom, srp_srce_pl_acc, srp_srce_pl_gen, srp_srce_pl_prep, srp_srce_pl_dat,
      srp_srce_pl_ins],
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_ovca_pl.paradigm : Paradigm Cell :=
  { id := "srp_ovca_pl", lexeme := Lexemes.srp_ovca,
    forms := [srp_ovca_pl_nom, srp_ovca_pl_acc, srp_ovca_pl_gen, srp_ovca_pl_prep, srp_ovca_pl_dat,
      srp_ovca_pl_ins],
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_smrt_pl.paradigm : Paradigm Cell :=
  { id := "srp_smrt_pl", lexeme := Lexemes.srp_smrt,
    forms := [srp_smrt_pl_nom, srp_smrt_pl_acc, srp_smrt_pl_gen, srp_smrt_pl_prep, srp_smrt_pl_dat,
      srp_smrt_pl_ins],
    source := [
      ⟨"caha-2009", "(10)"⟩
    ] }

def srp_ja.paradigm : Paradigm Cell :=
  { id := "srp_ja", lexeme := Lexemes.srp_ja,
    forms := [srp_ja_nom, srp_ja_acc, srp_ja_gen, srp_ja_prep, srp_ja_dat, srp_ja_ins],
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ti.paradigm : Paradigm Cell :=
  { id := "srp_ti", lexeme := Lexemes.srp_ti,
    forms := [srp_ti_nom, srp_ti_acc, srp_ti_gen, srp_ti_prep, srp_ti_dat, srp_ti_ins],
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_on.paradigm : Paradigm Cell :=
  { id := "srp_on", lexeme := Lexemes.srp_on,
    forms := [srp_on_nom, srp_on_acc, srp_on_gen, srp_on_prep, srp_on_dat, srp_on_ins],
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_ona.paradigm : Paradigm Cell :=
  { id := "srp_ona", lexeme := Lexemes.srp_ona,
    forms := [srp_ona_nom, srp_ona_acc, srp_ona_gen, srp_ona_prep, srp_ona_dat, srp_ona_ins],
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_mi.paradigm : Paradigm Cell :=
  { id := "srp_mi", lexeme := Lexemes.srp_mi,
    forms := [srp_mi_nom, srp_mi_acc, srp_mi_gen, srp_mi_prep, srp_mi_dat, srp_mi_ins],
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_vi.paradigm : Paradigm Cell :=
  { id := "srp_vi", lexeme := Lexemes.srp_vi,
    forms := [srp_vi_nom, srp_vi_acc, srp_vi_gen, srp_vi_prep, srp_vi_dat, srp_vi_ins],
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def srp_oni.paradigm : Paradigm Cell :=
  { id := "srp_oni", lexeme := Lexemes.srp_oni,
    forms := [srp_oni_nom, srp_oni_acc, srp_oni_gen, srp_oni_prep, srp_oni_dat, srp_oni_ins],
    source := [
      ⟨"caha-2009", "(12)"⟩
    ] }

def slv_miza_du.paradigm : Paradigm Cell :=
  { id := "slv_miza_du", lexeme := Lexemes.slv_miza,
    forms := [slv_miza_du_nom, slv_miza_du_acc, slv_miza_du_gen, slv_miza_du_prep, slv_miza_du_dat,
      slv_miza_du_ins],
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_breskev_sg.paradigm : Paradigm Cell :=
  { id := "slv_breskev_sg", lexeme := Lexemes.slv_breskev,
    forms := [slv_breskev_sg_nom, slv_breskev_sg_acc, slv_breskev_sg_gen, slv_breskev_sg_prep,
      slv_breskev_sg_dat, slv_breskev_sg_ins],
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_breskev_pl.paradigm : Paradigm Cell :=
  { id := "slv_breskev_pl", lexeme := Lexemes.slv_breskev,
    forms := [slv_breskev_pl_nom, slv_breskev_pl_acc, slv_breskev_pl_gen, slv_breskev_pl_prep,
      slv_breskev_pl_dat, slv_breskev_pl_ins],
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_jabolko_sg.paradigm : Paradigm Cell :=
  { id := "slv_jabolko_sg", lexeme := Lexemes.slv_jabolko,
    forms := [slv_jabolko_sg_nom, slv_jabolko_sg_acc, slv_jabolko_sg_gen, slv_jabolko_sg_prep,
      slv_jabolko_sg_dat, slv_jabolko_sg_ins],
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_kmet_du.paradigm : Paradigm Cell :=
  { id := "slv_kmet_du", lexeme := Lexemes.slv_kmet,
    forms := [slv_kmet_du_nom, slv_kmet_du_acc, slv_kmet_du_gen, slv_kmet_du_prep, slv_kmet_du_dat,
      slv_kmet_du_ins],
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_kmet_sg.paradigm : Paradigm Cell :=
  { id := "slv_kmet_sg", lexeme := Lexemes.slv_kmet,
    forms := [slv_kmet_sg_nom, slv_kmet_sg_acc, slv_kmet_sg_gen, slv_kmet_sg_prep, slv_kmet_sg_dat,
      slv_kmet_sg_ins],
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_jaz.paradigm : Paradigm Cell :=
  { id := "slv_jaz", lexeme := Lexemes.slv_jaz,
    forms := [slv_jaz_nom, slv_jaz_acc, slv_jaz_gen, slv_jaz_prep, slv_jaz_dat, slv_jaz_ins],
    source := [
      ⟨"caha-2009", "(14)"⟩
    ] }

def slv_moj_mpl.paradigm : Paradigm Cell :=
  { id := "slv_moj_mpl", lexeme := Lexemes.slv_moj,
    forms := [slv_moj_mpl_nom, slv_moj_mpl_acc, slv_moj_mpl_gen, slv_moj_mpl_prep, slv_moj_mpl_dat,
      slv_moj_mpl_ins],
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_dva.paradigm : Paradigm Cell :=
  { id := "slv_dva", lexeme := Lexemes.slv_dva,
    forms := [slv_dva_nom, slv_dva_acc, slv_dva_gen, slv_dva_prep, slv_dva_dat, slv_dva_ins],
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_mi.paradigm : Paradigm Cell :=
  { id := "slv_mi", lexeme := Lexemes.slv_mi,
    forms := [slv_mi_nom, slv_mi_acc, slv_mi_gen, slv_mi_prep, slv_mi_dat, slv_mi_ins],
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_midva.paradigm : Paradigm Cell :=
  { id := "slv_midva", lexeme := Lexemes.slv_midva,
    forms := [slv_midva_nom, slv_midva_acc, slv_midva_gen, slv_midva_prep, slv_midva_dat,
      slv_midva_ins],
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_nit_sg.paradigm : Paradigm Cell :=
  { id := "slv_nit_sg", lexeme := Lexemes.slv_nit,
    forms := [slv_nit_sg_nom, slv_nit_sg_acc, slv_nit_sg_gen, slv_nit_sg_prep, slv_nit_sg_dat,
      slv_nit_sg_ins],
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_gospa_sg.paradigm : Paradigm Cell :=
  { id := "slv_gospa_sg", lexeme := Lexemes.slv_gospa,
    forms := [slv_gospa_sg_nom, slv_gospa_sg_acc, slv_gospa_sg_gen, slv_gospa_sg_prep,
      slv_gospa_sg_dat, slv_gospa_sg_ins],
    source := [
      ⟨"caha-2009", "(16)"⟩
    ] }

def slv_dan_du.paradigm : Paradigm Cell :=
  { id := "slv_dan_du", lexeme := Lexemes.slv_dan,
    forms := [slv_dan_du_nom, slv_dan_du_acc, slv_dan_du_gen, slv_dan_du_prep, slv_dan_du_dat,
      slv_dan_du_ins],
    source := [
      ⟨"caha-2009", "(17)"⟩
    ] }

def slv_racunovodja_sg.paradigm : Paradigm Cell :=
  { id := "slv_racunovodja_sg", lexeme := Lexemes.slv_racunovodja,
    forms := [slv_racunovodja_sg_nom, slv_racunovodja_sg_acc, slv_racunovodja_sg_gen,
      slv_racunovodja_sg_prep, slv_racunovodja_sg_dat, slv_racunovodja_sg_ins],
    source := [
      ⟨"caha-2009", "(17)"⟩
    ] }

def slv_ta_n.paradigm : Paradigm Cell :=
  { id := "slv_ta_n", lexeme := Lexemes.slv_ta,
    forms := [slv_ta_n_nom, slv_ta_n_acc, slv_ta_n_gen, slv_ta_n_prep, slv_ta_n_dat, slv_ta_n_ins],
    source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_potnik_pl.paradigm : Paradigm Cell :=
  { id := "slv_potnik_pl", lexeme := Lexemes.slv_potnik,
    forms := [slv_potnik_pl_nom, slv_potnik_pl_acc, slv_potnik_pl_gen, slv_potnik_pl_prep,
      slv_potnik_pl_dat, slv_potnik_pl_ins],
    source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_ta_f.paradigm : Paradigm Cell :=
  { id := "slv_ta_f", lexeme := Lexemes.slv_ta,
    forms := [slv_ta_f_nom, slv_ta_f_acc, slv_ta_f_gen, slv_ta_f_prep, slv_ta_f_dat, slv_ta_f_ins],
    source := [
      ⟨"caha-2009", "(18)"⟩
    ] }

def slv_tisti_n.paradigm : Paradigm Cell :=
  { id := "slv_tisti_n", lexeme := Lexemes.slv_tisti,
    forms := [slv_tisti_n_nom, slv_tisti_n_acc, slv_tisti_n_gen, slv_tisti_n_prep, slv_tisti_n_dat,
      slv_tisti_n_ins],
    source := [
      ⟨"caha-2009", "(19)"⟩
    ] }

def slv_vas_n.paradigm : Paradigm Cell :=
  { id := "slv_vas_n", lexeme := Lexemes.slv_vas,
    forms := [slv_vas_n_nom, slv_vas_n_acc, slv_vas_n_gen, slv_vas_n_prep, slv_vas_n_dat,
      slv_vas_n_ins],
    source := [
      ⟨"caha-2009", "(20)"⟩
    ] }

def ces_okno_sg.paradigm : Paradigm Cell :=
  { id := "ces_okno_sg", lexeme := Lexemes.ces_okno,
    forms := [ces_okno_sg_nom, ces_okno_sg_acc, ces_okno_sg_gen, ces_okno_sg_prep, ces_okno_sg_dat,
      ces_okno_sg_ins],
    source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_ulice_sg.paradigm : Paradigm Cell :=
  { id := "ces_ulice_sg", lexeme := Lexemes.ces_ulice,
    forms := [ces_ulice_sg_nom, ces_ulice_sg_acc, ces_ulice_sg_gen, ces_ulice_sg_prep,
      ces_ulice_sg_dat, ces_ulice_sg_ins],
    source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_muz_pl.paradigm : Paradigm Cell :=
  { id := "ces_muz_pl", lexeme := Lexemes.ces_muz,
    forms := [ces_muz_pl_nom, ces_muz_pl_acc, ces_muz_pl_gen, ces_muz_pl_prep, ces_muz_pl_dat,
      ces_muz_pl_ins],
    source := [
      ⟨"caha-2009", "(22)"⟩
    ] }

def ces_muz_sg.paradigm : Paradigm Cell :=
  { id := "ces_muz_sg", lexeme := Lexemes.ces_muz,
    forms := [ces_muz_sg_nom, ces_muz_sg_acc, ces_muz_sg_gen, ces_muz_sg_prep, ces_muz_sg_dat,
      ces_muz_sg_ins],
    source := [
      ⟨"caha-2009", "(23)"⟩
    ] }

def ces_dobry_fsg.paradigm : Paradigm Cell :=
  { id := "ces_dobry_fsg", lexeme := Lexemes.ces_dobry,
    forms := [ces_dobry_fsg_nom, ces_dobry_fsg_acc, ces_dobry_fsg_gen, ces_dobry_fsg_prep,
      ces_dobry_fsg_dat, ces_dobry_fsg_ins],
    source := [
      ⟨"caha-2009", "(23)"⟩
    ] }

def ces_dobry_mpl_2.paradigm : Paradigm Cell :=
  { id := "ces_dobry_mpl_2", lexeme := Lexemes.ces_dobry,
    forms := [ces_dobry_mpl_2_nom, ces_dobry_mpl_2_acc, ces_dobry_mpl_2_gen, ces_dobry_mpl_2_prep,
      ces_dobry_mpl_2_dat, ces_dobry_mpl_2_ins],
    source := [
      ⟨"caha-2009", "(24)"⟩
    ] }

def ces_vetsi_msg.paradigm : Paradigm Cell :=
  { id := "ces_vetsi_msg", lexeme := Lexemes.ces_vetsi,
    forms := [ces_vetsi_msg_nom, ces_vetsi_msg_acc, ces_vetsi_msg_gen, ces_vetsi_msg_prep,
      ces_vetsi_msg_dat, ces_vetsi_msg_ins],
    source := [
      ⟨"caha-2009", "(25)"⟩
    ] }

def ces_oba.paradigm : Paradigm Cell :=
  { id := "ces_oba", lexeme := Lexemes.ces_oba,
    forms := [ces_oba_nom, ces_oba_acc, ces_oba_gen, ces_oba_prep, ces_oba_dat, ces_oba_ins],
    source := [
      ⟨"caha-2009", "(26)"⟩
    ] }

def ces_stroj_sg.paradigm : Paradigm Cell :=
  { id := "ces_stroj_sg", lexeme := Lexemes.ces_stroj,
    forms := [ces_stroj_sg_nom, ces_stroj_sg_acc, ces_stroj_sg_gen, ces_stroj_sg_prep,
      ces_stroj_sg_dat, ces_stroj_sg_ins],
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_stroj_pl.paradigm : Paradigm Cell :=
  { id := "ces_stroj_pl", lexeme := Lexemes.ces_stroj,
    forms := [ces_stroj_pl_nom, ces_stroj_pl_acc, ces_stroj_pl_gen, ces_stroj_pl_prep,
      ces_stroj_pl_dat, ces_stroj_pl_ins],
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_kost_pl.paradigm : Paradigm Cell :=
  { id := "ces_kost_pl", lexeme := Lexemes.ces_kost,
    forms := [ces_kost_pl_nom, ces_kost_pl_acc, ces_kost_pl_gen, ces_kost_pl_prep, ces_kost_pl_dat,
      ces_kost_pl_ins],
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_ty.paradigm : Paradigm Cell :=
  { id := "ces_ty", lexeme := Lexemes.ces_ten,
    forms := [ces_ty_nom, ces_ty_acc, ces_ty_gen, ces_ty_prep, ces_ty_dat, ces_ty_ins],
    source := [
      ⟨"caha-2009", "(30)"⟩
    ] }

def ces_vila_sg.paradigm : Paradigm Cell :=
  { id := "ces_vila_sg", lexeme := Lexemes.ces_vila,
    forms := [ces_vila_sg_nom, ces_vila_sg_acc, ces_vila_sg_gen, ces_vila_sg_prep, ces_vila_sg_dat,
      ces_vila_sg_ins],
    source := [
      ⟨"caha-2009", "(31)"⟩
    ] }

def ces_misa_sg.paradigm : Paradigm Cell :=
  { id := "ces_misa_sg", lexeme := Lexemes.ces_misa,
    forms := [ces_misa_sg_nom, ces_misa_sg_acc, ces_misa_sg_gen, ces_misa_sg_prep, ces_misa_sg_dat,
      ces_misa_sg_ins],
    source := [
      ⟨"caha-2009", "(31)"⟩
    ] }

def ces_vul_pl.paradigm : Paradigm Cell :=
  { id := "ces_vul_pl", lexeme := Lexemes.ces_vul,
    forms := [ces_vul_pl_nom, ces_vul_pl_acc, ces_vul_pl_gen, ces_vul_pl_prep, ces_vul_pl_dat,
      ces_vul_pl_ins],
    source := [
      ⟨"caha-2009", "(35)"⟩
    ] }

def ces_hoch_pl.paradigm : Paradigm Cell :=
  { id := "ces_hoch_pl", lexeme := Lexemes.ces_hoch,
    forms := [ces_hoch_pl_nom, ces_hoch_pl_acc, ces_hoch_pl_gen, ces_hoch_pl_prep, ces_hoch_pl_dat,
      ces_hoch_pl_ins],
    source := [
      ⟨"caha-2009", "(35)"⟩
    ] }

def ces_pan_sg.paradigm : Paradigm Cell :=
  { id := "ces_pan_sg", lexeme := Lexemes.ces_pan,
    forms := [ces_pan_sg_nom, ces_pan_sg_acc, ces_pan_sg_gen, ces_pan_sg_prep, ces_pan_sg_dat,
      ces_pan_sg_ins],
    source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_ten.paradigm : Paradigm Cell :=
  { id := "ces_ten", lexeme := Lexemes.ces_ten,
    forms := [ces_ten_nom, ces_ten_acc, ces_ten_gen, ces_ten_prep, ces_ten_dat, ces_ten_ins],
    source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_my_2.paradigm : Paradigm Cell :=
  { id := "ces_my_2", lexeme := Lexemes.ces_my,
    forms := [ces_my_2_nom, ces_my_2_acc, ces_my_2_gen, ces_my_2_prep, ces_my_2_dat, ces_my_2_ins],
    source := [
      ⟨"caha-2009", "(39)"⟩
    ] }

def ces_ona.paradigm : Paradigm Cell :=
  { id := "ces_ona", lexeme := Lexemes.ces_ona,
    forms := [ces_ona_nom, ces_ona_acc, ces_ona_gen, ces_ona_prep, ces_ona_dat, ces_ona_ins],
    source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_nase_fsg.paradigm : Paradigm Cell :=
  { id := "ces_nase_fsg", lexeme := Lexemes.ces_nase,
    forms := [ces_nase_fsg_nom, ces_nase_fsg_acc, ces_nase_fsg_gen, ces_nase_fsg_prep,
      ces_nase_fsg_dat, ces_nase_fsg_ins],
    source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_zatez_sg.paradigm : Paradigm Cell :=
  { id := "ces_zatez_sg", lexeme := Lexemes.ces_zatez,
    forms := [ces_zatez_sg_nom, ces_zatez_sg_acc, ces_zatez_sg_gen, ces_zatez_sg_prep,
      ces_zatez_sg_dat, ces_zatez_sg_ins],
    source := [
      ⟨"caha-2009", "(41)"⟩
    ] }

def ces_zena_sg.paradigm : Paradigm Cell :=
  { id := "ces_zena_sg", lexeme := Lexemes.ces_zena,
    forms := [ces_zena_sg_nom, ces_zena_sg_acc, ces_zena_sg_gen, ces_zena_sg_prep, ces_zena_sg_dat,
      ces_zena_sg_ins],
    source := [
      ⟨"caha-2009", "(44)"⟩
    ] }

def ces_kluk_pl.paradigm : Paradigm Cell :=
  { id := "ces_kluk_pl", lexeme := Lexemes.ces_kluk,
    forms := [ces_kluk_pl_nom, ces_kluk_pl_acc, ces_kluk_pl_gen, ces_kluk_pl_prep, ces_kluk_pl_dat,
      ces_kluk_pl_ins],
    source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_kluk_pl_colloquial.paradigm : Paradigm Cell :=
  { id := "ces_kluk_pl_colloquial", lexeme := Lexemes.ces_kluk,
    forms := [ces_kluk_pl_colloquial_nom, ces_kluk_pl_colloquial_acc, ces_kluk_pl_colloquial_gen,
      ces_kluk_pl_colloquial_prep, ces_kluk_pl_colloquial_dat, ces_kluk_pl_colloquial_ins],
    source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_muz_pl_colloquial.paradigm : Paradigm Cell :=
  { id := "ces_muz_pl_colloquial", lexeme := Lexemes.ces_muz,
    forms := [ces_muz_pl_colloquial_nom, ces_muz_pl_colloquial_acc, ces_muz_pl_colloquial_gen,
      ces_muz_pl_colloquial_prep, ces_muz_pl_colloquial_dat, ces_muz_pl_colloquial_ins],
    source := [
      ⟨"caha-2009", "(49)"⟩
    ] }

def ces_zena_pl.paradigm : Paradigm Cell :=
  { id := "ces_zena_pl", lexeme := Lexemes.ces_zena,
    forms := [ces_zena_pl_nom, ces_zena_pl_acc, ces_zena_pl_gen, ces_zena_pl_prep, ces_zena_pl_dat,
      ces_zena_pl_ins],
    source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_pisen_pl.paradigm : Paradigm Cell :=
  { id := "ces_pisen_pl", lexeme := Lexemes.ces_pisen,
    forms := [ces_pisen_pl_nom, ces_pisen_pl_acc, ces_pisen_pl_gen, ces_pisen_pl_prep,
      ces_pisen_pl_dat, ces_pisen_pl_ins],
    source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_dobry_mpl.paradigm : Paradigm Cell :=
  { id := "ces_dobry_mpl", lexeme := Lexemes.ces_dobry,
    forms := [ces_dobry_mpl_nom, ces_dobry_mpl_acc, ces_dobry_mpl_gen, ces_dobry_mpl_prep,
      ces_dobry_mpl_dat, ces_dobry_mpl_ins],
    source := [
      ⟨"caha-2009", "(51)"⟩
    ] }

def ces_kost_sg.paradigm : Paradigm Cell :=
  { id := "ces_kost_sg", lexeme := Lexemes.ces_kost,
    forms := [ces_kost_sg_nom, ces_kost_sg_acc, ces_kost_sg_gen, ces_kost_sg_prep, ces_kost_sg_dat,
      ces_kost_sg_ins],
    source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_hrad_sg.paradigm : Paradigm Cell :=
  { id := "ces_hrad_sg", lexeme := Lexemes.ces_hrad,
    forms := [ces_hrad_sg_nom, ces_hrad_sg_acc, ces_hrad_sg_gen, ces_hrad_sg_prep, ces_hrad_sg_dat,
      ces_hrad_sg_ins],
    source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_my.paradigm : Paradigm Cell :=
  { id := "ces_my", lexeme := Lexemes.ces_my,
    forms := [ces_my_nom, ces_my_acc, ces_my_gen, ces_my_prep, ces_my_dat, ces_my_ins],
    source := [
      ⟨"caha-2009", "(55)"⟩
    ] }

def ces_mesto_sg.paradigm : Paradigm Cell :=
  { id := "ces_mesto_sg", lexeme := Lexemes.ces_mesto,
    forms := [ces_mesto_sg_nom, ces_mesto_sg_acc, ces_mesto_sg_gen, ces_mesto_sg_prep,
      ces_mesto_sg_dat, ces_mesto_sg_ins],
    source := [
      ⟨"caha-2009", "(56)"⟩
    ] }

def ces_vetsi_nsg.paradigm : Paradigm Cell :=
  { id := "ces_vetsi_nsg", lexeme := Lexemes.ces_vetsi,
    forms := [ces_vetsi_nsg_nom, ces_vetsi_nsg_acc, ces_vetsi_nsg_gen, ces_vetsi_nsg_prep,
      ces_vetsi_nsg_dat, ces_vetsi_nsg_ins],
    source := [
      ⟨"caha-2009", "(57)"⟩
    ] }

def ces_ono.paradigm : Paradigm Cell :=
  { id := "ces_ono", lexeme := Lexemes.ces_ono,
    forms := [ces_ono_nom, ces_ono_acc, ces_ono_gen, ces_ono_prep, ces_ono_dat, ces_ono_ins],
    source := [
      ⟨"caha-2009", "(58)"⟩
    ] }

def ces_nase_nsg.paradigm : Paradigm Cell :=
  { id := "ces_nase_nsg", lexeme := Lexemes.ces_nase,
    forms := [ces_nase_nsg_nom, ces_nase_nsg_acc, ces_nase_nsg_gen, ces_nase_nsg_prep,
      ces_nase_nsg_dat, ces_nase_nsg_ins],
    source := [
      ⟨"caha-2009", "(62)"⟩
    ] }

def ces_vetsi_fsg.paradigm : Paradigm Cell :=
  { id := "ces_vetsi_fsg", lexeme := Lexemes.ces_vetsi,
    forms := [ces_vetsi_fsg_nom, ces_vetsi_fsg_acc, ces_vetsi_fsg_gen, ces_vetsi_fsg_prep,
      ces_vetsi_fsg_dat, ces_vetsi_fsg_ins],
    source := [
      ⟨"caha-2009", "n. 25"⟩
    ] }

def ces_vetsi_npl.paradigm : Paradigm Cell :=
  { id := "ces_vetsi_npl", lexeme := Lexemes.ces_vetsi,
    forms := [ces_vetsi_npl_nom, ces_vetsi_npl_acc, ces_vetsi_npl_gen, ces_vetsi_npl_prep,
      ces_vetsi_npl_dat, ces_vetsi_npl_ins],
    source := [
      ⟨"caha-2009", "(63)"⟩
    ] }

def ces_ona_npl.paradigm : Paradigm Cell :=
  { id := "ces_ona_npl", lexeme := Lexemes.ces_oni,
    forms := [ces_ona_npl_nom, ces_ona_npl_acc, ces_ona_npl_gen, ces_ona_npl_prep, ces_ona_npl_dat,
      ces_ona_npl_ins],
    source := [
      ⟨"caha-2009", "(64)"⟩
    ] }

def ces_ta.paradigm : Paradigm Cell :=
  { id := "ces_ta", lexeme := Lexemes.ces_ten,
    forms := [ces_ta_nom, ces_ta_acc, ces_ta_gen, ces_ta_prep, ces_ta_dat, ces_ta_ins],
    source := [
      ⟨"caha-2009", "n. 26"⟩
    ] }

def ces_dva.paradigm : Paradigm Cell :=
  { id := "ces_dva", lexeme := Lexemes.ces_dva,
    forms := [ces_dva_nom, ces_dva_acc, ces_dva_gen, ces_dva_prep, ces_dva_dat, ces_dva_ins],
    source := [
      ⟨"caha-2009", "(65)"⟩
    ] }

def ces_pet.paradigm : Paradigm Cell :=
  { id := "ces_pet", lexeme := Lexemes.ces_pet,
    forms := [ces_pet_nom, ces_pet_acc, ces_pet_gen, ces_pet_prep, ces_pet_dat, ces_pet_ins],
    source := [
      ⟨"caha-2009", "(66)"⟩
    ] }

def slk_ona.paradigm : Paradigm Cell :=
  { id := "slk_ona", lexeme := Lexemes.slk_ona,
    forms := [slk_ona_nom, slk_ona_acc, slk_ona_gen, slk_ona_prep, slk_ona_dat, slk_ona_ins],
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_nase_fsg.paradigm : Paradigm Cell :=
  { id := "slk_nase_fsg", lexeme := Lexemes.slk_nase,
    forms := [slk_nase_fsg_nom, slk_nase_fsg_acc, slk_nase_fsg_gen, slk_nase_fsg_prep,
      slk_nase_fsg_dat, slk_nase_fsg_ins],
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_ulica_sg.paradigm : Paradigm Cell :=
  { id := "slk_ulica_sg", lexeme := Lexemes.slk_ulica,
    forms := [slk_ulica_sg_nom, slk_ulica_sg_acc, slk_ulica_sg_gen, slk_ulica_sg_prep,
      slk_ulica_sg_dat, slk_ulica_sg_ins],
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def slk_tlac_sg.paradigm : Paradigm Cell :=
  { id := "slk_tlac_sg", lexeme := Lexemes.slk_tlac,
    forms := [slk_tlac_sg_nom, slk_tlac_sg_acc, slk_tlac_sg_gen, slk_tlac_sg_prep, slk_tlac_sg_dat,
      slk_tlac_sg_ins],
    source := [
      ⟨"caha-2009", "(42)"⟩
    ] }

def ukr_kraj_sg.paradigm : Paradigm Cell :=
  { id := "ukr_kraj_sg", lexeme := Lexemes.ukr_kraj,
    forms := [ukr_kraj_sg_nom, ukr_kraj_sg_acc, ukr_kraj_sg_gen, ukr_kraj_sg_prep, ukr_kraj_sg_dat,
      ukr_kraj_sg_ins],
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_velykyj_pl.paradigm : Paradigm Cell :=
  { id := "ukr_velykyj_pl", lexeme := Lexemes.ukr_velykyj,
    forms := [ukr_velykyj_pl_nom, ukr_velykyj_pl_acc, ukr_velykyj_pl_gen, ukr_velykyj_pl_prep,
      ukr_velykyj_pl_dat, ukr_velykyj_pl_ins],
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_znannja_sg.paradigm : Paradigm Cell :=
  { id := "ukr_znannja_sg", lexeme := Lexemes.ukr_znannja,
    forms := [ukr_znannja_sg_nom, ukr_znannja_sg_acc, ukr_znannja_sg_gen, ukr_znannja_sg_prep,
      ukr_znannja_sg_dat, ukr_znannja_sg_ins],
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_my.paradigm : Paradigm Cell :=
  { id := "ukr_my", lexeme := Lexemes.ukr_my,
    forms := [ukr_my_nom, ukr_my_acc, ukr_my_gen, ukr_my_prep, ukr_my_dat, ukr_my_ins],
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kasyr_sg.paradigm : Paradigm Cell :=
  { id := "ukr_kasyr_sg", lexeme := Lexemes.ukr_kasyr,
    forms := [ukr_kasyr_sg_nom, ukr_kasyr_sg_acc, ukr_kasyr_sg_gen, ukr_kasyr_sg_prep,
      ukr_kasyr_sg_dat, ukr_kasyr_sg_ins],
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_kasyr_pl.paradigm : Paradigm Cell :=
  { id := "ukr_kasyr_pl", lexeme := Lexemes.ukr_kasyr,
    forms := [ukr_kasyr_pl_nom, ukr_kasyr_pl_acc, ukr_kasyr_pl_gen, ukr_kasyr_pl_prep,
      ukr_kasyr_pl_dat, ukr_kasyr_pl_ins],
    source := [
      ⟨"caha-2009", "(68)"⟩
    ] }

def ukr_maty_sg.paradigm : Paradigm Cell :=
  { id := "ukr_maty_sg", lexeme := Lexemes.ukr_maty,
    forms := [ukr_maty_sg_nom, ukr_maty_sg_acc, ukr_maty_sg_gen, ukr_maty_sg_prep, ukr_maty_sg_dat,
      ukr_maty_sg_ins],
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_ruka_sg.paradigm : Paradigm Cell :=
  { id := "ukr_ruka_sg", lexeme := Lexemes.ukr_ruka,
    forms := [ukr_ruka_sg_nom, ukr_ruka_sg_acc, ukr_ruka_sg_gen, ukr_ruka_sg_prep, ukr_ruka_sg_dat,
      ukr_ruka_sg_ins],
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_ja.paradigm : Paradigm Cell :=
  { id := "ukr_ja", lexeme := Lexemes.ukr_ja,
    forms := [ukr_ja_nom, ukr_ja_acc, ukr_ja_gen, ukr_ja_prep, ukr_ja_dat, ukr_ja_ins],
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_velykyj_msg.paradigm : Paradigm Cell :=
  { id := "ukr_velykyj_msg", lexeme := Lexemes.ukr_velykyj,
    forms := [ukr_velykyj_msg_nom, ukr_velykyj_msg_acc, ukr_velykyj_msg_gen, ukr_velykyj_msg_prep,
      ukr_velykyj_msg_dat, ukr_velykyj_msg_ins],
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_sto.paradigm : Paradigm Cell :=
  { id := "ukr_sto", lexeme := Lexemes.ukr_sto,
    forms := [ukr_sto_nom, ukr_sto_acc, ukr_sto_gen, ukr_sto_prep, ukr_sto_dat, ukr_sto_ins],
    source := [
      ⟨"caha-2009", "(69)"⟩
    ] }

def ukr_kraj_sg_2.paradigm : Paradigm Cell :=
  { id := "ukr_kraj_sg_2", lexeme := Lexemes.ukr_kraj,
    forms := [ukr_kraj_sg_2_nom, ukr_kraj_sg_2_acc, ukr_kraj_sg_2_gen, ukr_kraj_sg_2_prep,
      ukr_kraj_sg_2_dat, ukr_kraj_sg_2_ins],
    source := [
      ⟨"caha-2009", "(70)"⟩
    ] }

def ukr_bezkrajij_msg.paradigm : Paradigm Cell :=
  { id := "ukr_bezkrajij_msg", lexeme := Lexemes.ukr_bezkrajij,
    forms := [ukr_bezkrajij_msg_nom, ukr_bezkrajij_msg_acc, ukr_bezkrajij_msg_gen,
      ukr_bezkrajij_msg_prep, ukr_bezkrajij_msg_dat, ukr_bezkrajij_msg_ins],
    source := [
      ⟨"caha-2009", "(71)"⟩
    ] }

def ukr_bezkrajij_msg_2.paradigm : Paradigm Cell :=
  { id := "ukr_bezkrajij_msg_2", lexeme := Lexemes.ukr_bezkrajij,
    forms := [ukr_bezkrajij_msg_2_nom, ukr_bezkrajij_msg_2_acc, ukr_bezkrajij_msg_2_gen,
      ukr_bezkrajij_msg_2_prep, ukr_bezkrajij_msg_2_dat, ukr_bezkrajij_msg_2_ins],
    source := [
      ⟨"caha-2009", "(71)"⟩
    ] }

def ukr_velykyj_msg_2.paradigm : Paradigm Cell :=
  { id := "ukr_velykyj_msg_2", lexeme := Lexemes.ukr_velykyj,
    forms := [ukr_velykyj_msg_2_nom, ukr_velykyj_msg_2_acc, ukr_velykyj_msg_2_gen,
      ukr_velykyj_msg_2_prep, ukr_velykyj_msg_2_dat, ukr_velykyj_msg_2_ins],
    source := [
      ⟨"caha-2009", "(72)"⟩
    ] }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.srp_sin, Lexemes.srp_grad, Lexemes.srp_muz, Lexemes.srp_selo,
  Lexemes.srp_srce, Lexemes.srp_ovca, Lexemes.srp_smrt, Lexemes.srp_ja, Lexemes.srp_ti,
  Lexemes.srp_on, Lexemes.srp_ona, Lexemes.srp_mi, Lexemes.srp_vi, Lexemes.srp_oni,
  Lexemes.slv_miza, Lexemes.slv_breskev, Lexemes.slv_jabolko, Lexemes.slv_kmet, Lexemes.slv_jaz,
  Lexemes.slv_moj, Lexemes.slv_dva, Lexemes.slv_mi, Lexemes.slv_midva, Lexemes.slv_nit,
  Lexemes.slv_gospa, Lexemes.slv_dan, Lexemes.slv_racunovodja, Lexemes.slv_ta, Lexemes.slv_potnik,
  Lexemes.slv_tisti, Lexemes.slv_vas, Lexemes.ces_okno, Lexemes.ces_ulice, Lexemes.ces_muz,
  Lexemes.ces_dobry, Lexemes.ces_vetsi, Lexemes.ces_oba, Lexemes.ces_stroj, Lexemes.ces_kost,
  Lexemes.ces_ten, Lexemes.ces_vila, Lexemes.ces_misa, Lexemes.ces_vul, Lexemes.ces_hoch,
  Lexemes.ces_pan, Lexemes.ces_my, Lexemes.ces_ona, Lexemes.ces_nase, Lexemes.ces_zatez,
  Lexemes.ces_zena, Lexemes.ces_kluk, Lexemes.ces_pisen, Lexemes.ces_hrad, Lexemes.ces_mesto,
  Lexemes.ces_ono, Lexemes.ces_oni, Lexemes.ces_dva, Lexemes.ces_pet, Lexemes.slk_ona,
  Lexemes.slk_nase, Lexemes.slk_ulica, Lexemes.slk_tlac, Lexemes.ukr_kraj, Lexemes.ukr_velykyj,
  Lexemes.ukr_znannja, Lexemes.ukr_my, Lexemes.ukr_kasyr, Lexemes.ukr_maty, Lexemes.ukr_ruka,
  Lexemes.ukr_ja, Lexemes.ukr_sto, Lexemes.ukr_bezkrajij]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [srp_sin_sg_nom, srp_sin_sg_acc, srp_sin_sg_gen, srp_sin_sg_prep,
  srp_sin_sg_dat, srp_sin_sg_ins, srp_grad_sg_nom, srp_grad_sg_acc, srp_grad_sg_gen,
  srp_grad_sg_prep, srp_grad_sg_dat, srp_grad_sg_ins, srp_muz_sg_nom, srp_muz_sg_acc,
  srp_muz_sg_gen, srp_muz_sg_prep, srp_muz_sg_dat, srp_muz_sg_ins, srp_selo_sg_nom, srp_selo_sg_acc,
  srp_selo_sg_gen, srp_selo_sg_prep, srp_selo_sg_dat, srp_selo_sg_ins, srp_srce_sg_nom,
  srp_srce_sg_acc, srp_srce_sg_gen, srp_srce_sg_prep, srp_srce_sg_dat, srp_srce_sg_ins,
  srp_ovca_sg_nom, srp_ovca_sg_acc, srp_ovca_sg_gen, srp_ovca_sg_prep, srp_ovca_sg_dat,
  srp_ovca_sg_ins, srp_smrt_sg_nom, srp_smrt_sg_acc, srp_smrt_sg_gen, srp_smrt_sg_prep,
  srp_smrt_sg_dat, srp_smrt_sg_ins, srp_sin_pl_nom, srp_sin_pl_acc, srp_sin_pl_gen, srp_sin_pl_prep,
  srp_sin_pl_dat, srp_sin_pl_ins, srp_grad_pl_nom, srp_grad_pl_acc, srp_grad_pl_gen,
  srp_grad_pl_prep, srp_grad_pl_dat, srp_grad_pl_ins, srp_muz_pl_nom, srp_muz_pl_acc,
  srp_muz_pl_gen, srp_muz_pl_prep, srp_muz_pl_dat, srp_muz_pl_ins, srp_selo_pl_nom, srp_selo_pl_acc,
  srp_selo_pl_gen, srp_selo_pl_prep, srp_selo_pl_dat, srp_selo_pl_ins, srp_srce_pl_nom,
  srp_srce_pl_acc, srp_srce_pl_gen, srp_srce_pl_prep, srp_srce_pl_dat, srp_srce_pl_ins,
  srp_ovca_pl_nom, srp_ovca_pl_acc, srp_ovca_pl_gen, srp_ovca_pl_prep, srp_ovca_pl_dat,
  srp_ovca_pl_ins, srp_smrt_pl_nom, srp_smrt_pl_acc, srp_smrt_pl_gen, srp_smrt_pl_prep,
  srp_smrt_pl_dat, srp_smrt_pl_ins, srp_ja_nom, srp_ja_acc, srp_ja_gen, srp_ja_prep, srp_ja_dat,
  srp_ja_ins, srp_ti_nom, srp_ti_acc, srp_ti_gen, srp_ti_prep, srp_ti_dat, srp_ti_ins, srp_on_nom,
  srp_on_acc, srp_on_gen, srp_on_prep, srp_on_dat, srp_on_ins, srp_ona_nom, srp_ona_acc,
  srp_ona_gen, srp_ona_prep, srp_ona_dat, srp_ona_ins, srp_mi_nom, srp_mi_acc, srp_mi_gen,
  srp_mi_prep, srp_mi_dat, srp_mi_ins, srp_vi_nom, srp_vi_acc, srp_vi_gen, srp_vi_prep, srp_vi_dat,
  srp_vi_ins, srp_oni_nom, srp_oni_acc, srp_oni_gen, srp_oni_prep, srp_oni_dat, srp_oni_ins,
  slv_miza_du_nom, slv_miza_du_acc, slv_miza_du_gen, slv_miza_du_prep, slv_miza_du_dat,
  slv_miza_du_ins, slv_breskev_sg_nom, slv_breskev_sg_acc, slv_breskev_sg_gen, slv_breskev_sg_prep,
  slv_breskev_sg_dat, slv_breskev_sg_ins, slv_breskev_pl_nom, slv_breskev_pl_acc,
  slv_breskev_pl_gen, slv_breskev_pl_prep, slv_breskev_pl_dat, slv_breskev_pl_ins,
  slv_jabolko_sg_nom, slv_jabolko_sg_acc, slv_jabolko_sg_gen, slv_jabolko_sg_prep,
  slv_jabolko_sg_dat, slv_jabolko_sg_ins, slv_kmet_du_nom, slv_kmet_du_acc, slv_kmet_du_gen,
  slv_kmet_du_prep, slv_kmet_du_dat, slv_kmet_du_ins, slv_kmet_sg_nom, slv_kmet_sg_acc,
  slv_kmet_sg_gen, slv_kmet_sg_prep, slv_kmet_sg_dat, slv_kmet_sg_ins, slv_jaz_nom, slv_jaz_acc,
  slv_jaz_gen, slv_jaz_prep, slv_jaz_dat, slv_jaz_ins, slv_moj_mpl_nom, slv_moj_mpl_acc,
  slv_moj_mpl_gen, slv_moj_mpl_prep, slv_moj_mpl_dat, slv_moj_mpl_ins, slv_dva_nom, slv_dva_acc,
  slv_dva_gen, slv_dva_prep, slv_dva_dat, slv_dva_ins, slv_mi_nom, slv_mi_acc, slv_mi_gen,
  slv_mi_prep, slv_mi_dat, slv_mi_ins, slv_midva_nom, slv_midva_acc, slv_midva_gen, slv_midva_prep,
  slv_midva_dat, slv_midva_ins, slv_nit_sg_nom, slv_nit_sg_acc, slv_nit_sg_gen, slv_nit_sg_prep,
  slv_nit_sg_dat, slv_nit_sg_ins, slv_gospa_sg_nom, slv_gospa_sg_acc, slv_gospa_sg_gen,
  slv_gospa_sg_prep, slv_gospa_sg_dat, slv_gospa_sg_ins, slv_dan_du_nom, slv_dan_du_acc,
  slv_dan_du_gen, slv_dan_du_prep, slv_dan_du_dat, slv_dan_du_ins, slv_racunovodja_sg_nom,
  slv_racunovodja_sg_acc, slv_racunovodja_sg_gen, slv_racunovodja_sg_prep, slv_racunovodja_sg_dat,
  slv_racunovodja_sg_ins, slv_ta_n_nom, slv_ta_n_acc, slv_ta_n_gen, slv_ta_n_prep, slv_ta_n_dat,
  slv_ta_n_ins, slv_potnik_pl_nom, slv_potnik_pl_acc, slv_potnik_pl_gen, slv_potnik_pl_prep,
  slv_potnik_pl_dat, slv_potnik_pl_ins, slv_ta_f_nom, slv_ta_f_acc, slv_ta_f_gen, slv_ta_f_prep,
  slv_ta_f_dat, slv_ta_f_ins, slv_tisti_n_nom, slv_tisti_n_acc, slv_tisti_n_gen, slv_tisti_n_prep,
  slv_tisti_n_dat, slv_tisti_n_ins, slv_vas_n_nom, slv_vas_n_acc, slv_vas_n_gen, slv_vas_n_prep,
  slv_vas_n_dat, slv_vas_n_ins, ces_okno_sg_nom, ces_okno_sg_acc, ces_okno_sg_gen, ces_okno_sg_prep,
  ces_okno_sg_dat, ces_okno_sg_ins, ces_ulice_sg_nom, ces_ulice_sg_acc, ces_ulice_sg_gen,
  ces_ulice_sg_prep, ces_ulice_sg_dat, ces_ulice_sg_ins, ces_muz_pl_nom, ces_muz_pl_acc,
  ces_muz_pl_gen, ces_muz_pl_prep, ces_muz_pl_dat, ces_muz_pl_ins, ces_muz_sg_nom, ces_muz_sg_acc,
  ces_muz_sg_gen, ces_muz_sg_prep, ces_muz_sg_dat, ces_muz_sg_ins, ces_dobry_fsg_nom,
  ces_dobry_fsg_acc, ces_dobry_fsg_gen, ces_dobry_fsg_prep, ces_dobry_fsg_dat, ces_dobry_fsg_ins,
  ces_dobry_mpl_2_nom, ces_dobry_mpl_2_acc, ces_dobry_mpl_2_gen, ces_dobry_mpl_2_prep,
  ces_dobry_mpl_2_dat, ces_dobry_mpl_2_ins, ces_vetsi_msg_nom, ces_vetsi_msg_acc, ces_vetsi_msg_gen,
  ces_vetsi_msg_prep, ces_vetsi_msg_dat, ces_vetsi_msg_ins, ces_oba_nom, ces_oba_acc, ces_oba_gen,
  ces_oba_prep, ces_oba_dat, ces_oba_ins, ces_stroj_sg_nom, ces_stroj_sg_acc, ces_stroj_sg_gen,
  ces_stroj_sg_prep, ces_stroj_sg_dat, ces_stroj_sg_ins, ces_stroj_pl_nom, ces_stroj_pl_acc,
  ces_stroj_pl_gen, ces_stroj_pl_prep, ces_stroj_pl_dat, ces_stroj_pl_ins, ces_kost_pl_nom,
  ces_kost_pl_acc, ces_kost_pl_gen, ces_kost_pl_prep, ces_kost_pl_dat, ces_kost_pl_ins, ces_ty_nom,
  ces_ty_acc, ces_ty_gen, ces_ty_prep, ces_ty_dat, ces_ty_ins, ces_vila_sg_nom, ces_vila_sg_acc,
  ces_vila_sg_gen, ces_vila_sg_prep, ces_vila_sg_dat, ces_vila_sg_ins, ces_misa_sg_nom,
  ces_misa_sg_acc, ces_misa_sg_gen, ces_misa_sg_prep, ces_misa_sg_dat, ces_misa_sg_ins,
  ces_vul_pl_nom, ces_vul_pl_acc, ces_vul_pl_gen, ces_vul_pl_prep, ces_vul_pl_dat, ces_vul_pl_ins,
  ces_hoch_pl_nom, ces_hoch_pl_acc, ces_hoch_pl_gen, ces_hoch_pl_prep, ces_hoch_pl_dat,
  ces_hoch_pl_ins, ces_pan_sg_nom, ces_pan_sg_acc, ces_pan_sg_gen, ces_pan_sg_prep, ces_pan_sg_dat,
  ces_pan_sg_ins, ces_ten_nom, ces_ten_acc, ces_ten_gen, ces_ten_prep, ces_ten_dat, ces_ten_ins,
  ces_my_2_nom, ces_my_2_acc, ces_my_2_gen, ces_my_2_prep, ces_my_2_dat, ces_my_2_ins, ces_ona_nom,
  ces_ona_acc, ces_ona_gen, ces_ona_prep, ces_ona_dat, ces_ona_ins, ces_nase_fsg_nom,
  ces_nase_fsg_acc, ces_nase_fsg_gen, ces_nase_fsg_prep, ces_nase_fsg_dat, ces_nase_fsg_ins,
  ces_zatez_sg_nom, ces_zatez_sg_acc, ces_zatez_sg_gen, ces_zatez_sg_prep, ces_zatez_sg_dat,
  ces_zatez_sg_ins, ces_zena_sg_nom, ces_zena_sg_acc, ces_zena_sg_gen, ces_zena_sg_prep,
  ces_zena_sg_dat, ces_zena_sg_ins, ces_kluk_pl_nom, ces_kluk_pl_acc, ces_kluk_pl_gen,
  ces_kluk_pl_prep, ces_kluk_pl_dat, ces_kluk_pl_ins, ces_kluk_pl_colloquial_nom,
  ces_kluk_pl_colloquial_acc, ces_kluk_pl_colloquial_gen, ces_kluk_pl_colloquial_prep,
  ces_kluk_pl_colloquial_dat, ces_kluk_pl_colloquial_ins, ces_muz_pl_colloquial_nom,
  ces_muz_pl_colloquial_acc, ces_muz_pl_colloquial_gen, ces_muz_pl_colloquial_prep,
  ces_muz_pl_colloquial_dat, ces_muz_pl_colloquial_ins, ces_zena_pl_nom, ces_zena_pl_acc,
  ces_zena_pl_gen, ces_zena_pl_prep, ces_zena_pl_dat, ces_zena_pl_ins, ces_pisen_pl_nom,
  ces_pisen_pl_acc, ces_pisen_pl_gen, ces_pisen_pl_prep, ces_pisen_pl_dat, ces_pisen_pl_ins,
  ces_dobry_mpl_nom, ces_dobry_mpl_acc, ces_dobry_mpl_gen, ces_dobry_mpl_prep, ces_dobry_mpl_dat,
  ces_dobry_mpl_ins, ces_kost_sg_nom, ces_kost_sg_acc, ces_kost_sg_gen, ces_kost_sg_prep,
  ces_kost_sg_dat, ces_kost_sg_ins, ces_hrad_sg_nom, ces_hrad_sg_acc, ces_hrad_sg_gen,
  ces_hrad_sg_prep, ces_hrad_sg_dat, ces_hrad_sg_ins, ces_my_nom, ces_my_acc, ces_my_gen,
  ces_my_prep, ces_my_dat, ces_my_ins, ces_mesto_sg_nom, ces_mesto_sg_acc, ces_mesto_sg_gen,
  ces_mesto_sg_prep, ces_mesto_sg_dat, ces_mesto_sg_ins, ces_vetsi_nsg_nom, ces_vetsi_nsg_acc,
  ces_vetsi_nsg_gen, ces_vetsi_nsg_prep, ces_vetsi_nsg_dat, ces_vetsi_nsg_ins, ces_ono_nom,
  ces_ono_acc, ces_ono_gen, ces_ono_prep, ces_ono_dat, ces_ono_ins, ces_nase_nsg_nom,
  ces_nase_nsg_acc, ces_nase_nsg_gen, ces_nase_nsg_prep, ces_nase_nsg_dat, ces_nase_nsg_ins,
  ces_vetsi_fsg_nom, ces_vetsi_fsg_acc, ces_vetsi_fsg_gen, ces_vetsi_fsg_prep, ces_vetsi_fsg_dat,
  ces_vetsi_fsg_ins, ces_vetsi_npl_nom, ces_vetsi_npl_acc, ces_vetsi_npl_gen, ces_vetsi_npl_prep,
  ces_vetsi_npl_dat, ces_vetsi_npl_ins, ces_ona_npl_nom, ces_ona_npl_acc, ces_ona_npl_gen,
  ces_ona_npl_prep, ces_ona_npl_dat, ces_ona_npl_ins, ces_ta_nom, ces_ta_acc, ces_ta_gen,
  ces_ta_prep, ces_ta_dat, ces_ta_ins, ces_dva_nom, ces_dva_acc, ces_dva_gen, ces_dva_prep,
  ces_dva_dat, ces_dva_ins, ces_pet_nom, ces_pet_acc, ces_pet_gen, ces_pet_prep, ces_pet_dat,
  ces_pet_ins, slk_ona_nom, slk_ona_acc, slk_ona_gen, slk_ona_prep, slk_ona_dat, slk_ona_ins,
  slk_nase_fsg_nom, slk_nase_fsg_acc, slk_nase_fsg_gen, slk_nase_fsg_prep, slk_nase_fsg_dat,
  slk_nase_fsg_ins, slk_ulica_sg_nom, slk_ulica_sg_acc, slk_ulica_sg_gen, slk_ulica_sg_prep,
  slk_ulica_sg_dat, slk_ulica_sg_ins, slk_tlac_sg_nom, slk_tlac_sg_acc, slk_tlac_sg_gen,
  slk_tlac_sg_prep, slk_tlac_sg_dat, slk_tlac_sg_ins, ukr_kraj_sg_nom, ukr_kraj_sg_acc,
  ukr_kraj_sg_gen, ukr_kraj_sg_prep, ukr_kraj_sg_dat, ukr_kraj_sg_ins, ukr_velykyj_pl_nom,
  ukr_velykyj_pl_acc, ukr_velykyj_pl_gen, ukr_velykyj_pl_prep, ukr_velykyj_pl_dat,
  ukr_velykyj_pl_ins, ukr_znannja_sg_nom, ukr_znannja_sg_acc, ukr_znannja_sg_gen,
  ukr_znannja_sg_prep, ukr_znannja_sg_dat, ukr_znannja_sg_ins, ukr_my_nom, ukr_my_acc, ukr_my_gen,
  ukr_my_prep, ukr_my_dat, ukr_my_ins, ukr_kasyr_sg_nom, ukr_kasyr_sg_acc, ukr_kasyr_sg_gen,
  ukr_kasyr_sg_prep, ukr_kasyr_sg_dat, ukr_kasyr_sg_ins, ukr_kasyr_pl_nom, ukr_kasyr_pl_acc,
  ukr_kasyr_pl_gen, ukr_kasyr_pl_prep, ukr_kasyr_pl_dat, ukr_kasyr_pl_ins, ukr_maty_sg_nom,
  ukr_maty_sg_acc, ukr_maty_sg_gen, ukr_maty_sg_prep, ukr_maty_sg_dat, ukr_maty_sg_ins,
  ukr_ruka_sg_nom, ukr_ruka_sg_acc, ukr_ruka_sg_gen, ukr_ruka_sg_prep, ukr_ruka_sg_dat,
  ukr_ruka_sg_ins, ukr_ja_nom, ukr_ja_acc, ukr_ja_gen, ukr_ja_prep, ukr_ja_dat, ukr_ja_ins,
  ukr_velykyj_msg_nom, ukr_velykyj_msg_acc, ukr_velykyj_msg_gen, ukr_velykyj_msg_prep,
  ukr_velykyj_msg_dat, ukr_velykyj_msg_ins, ukr_sto_nom, ukr_sto_acc, ukr_sto_gen, ukr_sto_prep,
  ukr_sto_dat, ukr_sto_ins, ukr_kraj_sg_2_nom, ukr_kraj_sg_2_acc, ukr_kraj_sg_2_gen,
  ukr_kraj_sg_2_prep, ukr_kraj_sg_2_dat, ukr_kraj_sg_2_ins, ukr_bezkrajij_msg_nom,
  ukr_bezkrajij_msg_acc, ukr_bezkrajij_msg_gen, ukr_bezkrajij_msg_prep, ukr_bezkrajij_msg_dat,
  ukr_bezkrajij_msg_ins, ukr_bezkrajij_msg_2_nom, ukr_bezkrajij_msg_2_acc, ukr_bezkrajij_msg_2_gen,
  ukr_bezkrajij_msg_2_prep, ukr_bezkrajij_msg_2_dat, ukr_bezkrajij_msg_2_ins, ukr_velykyj_msg_2_nom,
  ukr_velykyj_msg_2_acc, ukr_velykyj_msg_2_gen, ukr_velykyj_msg_2_prep, ukr_velykyj_msg_2_dat,
  ukr_velykyj_msg_2_ins]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := []

/-- Every paradigm of the data. -/
def paradigms : List (Paradigm Cell) := [srp_sin_sg.paradigm, srp_grad_sg.paradigm,
  srp_muz_sg.paradigm, srp_selo_sg.paradigm, srp_srce_sg.paradigm, srp_ovca_sg.paradigm,
  srp_smrt_sg.paradigm, srp_sin_pl.paradigm, srp_grad_pl.paradigm, srp_muz_pl.paradigm,
  srp_selo_pl.paradigm, srp_srce_pl.paradigm, srp_ovca_pl.paradigm, srp_smrt_pl.paradigm,
  srp_ja.paradigm, srp_ti.paradigm, srp_on.paradigm, srp_ona.paradigm, srp_mi.paradigm,
  srp_vi.paradigm, srp_oni.paradigm, slv_miza_du.paradigm, slv_breskev_sg.paradigm,
  slv_breskev_pl.paradigm, slv_jabolko_sg.paradigm, slv_kmet_du.paradigm, slv_kmet_sg.paradigm,
  slv_jaz.paradigm, slv_moj_mpl.paradigm, slv_dva.paradigm, slv_mi.paradigm, slv_midva.paradigm,
  slv_nit_sg.paradigm, slv_gospa_sg.paradigm, slv_dan_du.paradigm, slv_racunovodja_sg.paradigm,
  slv_ta_n.paradigm, slv_potnik_pl.paradigm, slv_ta_f.paradigm, slv_tisti_n.paradigm,
  slv_vas_n.paradigm, ces_okno_sg.paradigm, ces_ulice_sg.paradigm, ces_muz_pl.paradigm,
  ces_muz_sg.paradigm, ces_dobry_fsg.paradigm, ces_dobry_mpl_2.paradigm, ces_vetsi_msg.paradigm,
  ces_oba.paradigm, ces_stroj_sg.paradigm, ces_stroj_pl.paradigm, ces_kost_pl.paradigm,
  ces_ty.paradigm, ces_vila_sg.paradigm, ces_misa_sg.paradigm, ces_vul_pl.paradigm,
  ces_hoch_pl.paradigm, ces_pan_sg.paradigm, ces_ten.paradigm, ces_my_2.paradigm, ces_ona.paradigm,
  ces_nase_fsg.paradigm, ces_zatez_sg.paradigm, ces_zena_sg.paradigm, ces_kluk_pl.paradigm,
  ces_kluk_pl_colloquial.paradigm, ces_muz_pl_colloquial.paradigm, ces_zena_pl.paradigm,
  ces_pisen_pl.paradigm, ces_dobry_mpl.paradigm, ces_kost_sg.paradigm, ces_hrad_sg.paradigm,
  ces_my.paradigm, ces_mesto_sg.paradigm, ces_vetsi_nsg.paradigm, ces_ono.paradigm,
  ces_nase_nsg.paradigm, ces_vetsi_fsg.paradigm, ces_vetsi_npl.paradigm, ces_ona_npl.paradigm,
  ces_ta.paradigm, ces_dva.paradigm, ces_pet.paradigm, slk_ona.paradigm, slk_nase_fsg.paradigm,
  slk_ulica_sg.paradigm, slk_tlac_sg.paradigm, ukr_kraj_sg.paradigm, ukr_velykyj_pl.paradigm,
  ukr_znannja_sg.paradigm, ukr_my.paradigm, ukr_kasyr_sg.paradigm, ukr_kasyr_pl.paradigm,
  ukr_maty_sg.paradigm, ukr_ruka_sg.paradigm, ukr_ja.paradigm, ukr_velykyj_msg.paradigm,
  ukr_sto.paradigm, ukr_kraj_sg_2.paradigm, ukr_bezkrajij_msg.paradigm,
  ukr_bezkrajij_msg_2.paradigm, ukr_velykyj_msg_2.paradigm]

end Caha2009.Wordlist
