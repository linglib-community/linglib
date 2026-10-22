module

public import Linglib.Data.Wordlist.Schema

/-!
# `Stump2006`: word forms

Auto-generated from `Linglib/Data/Wordlist/Stump2006.json` by `scripts/gen_wordlist.py`. Do not edit
by hand; edit the JSON and re-run the generator. Declarations live in `namespace
Stump2006.Wordlist`.
-/

@[expose] public section

namespace Stump2006.Wordlist

open CLDF.Wordlist

/-- The values of `Grade` the source distinguishes. -/
inductive Grade where
  /-- The strong grade, `strong` in the source. -/
  | strong
  /-- The middle grade, `middle` in the source. -/
  | middle
  /-- The weakest grade, `weakest` in the source. -/
  | weakest
  deriving DecidableEq, Repr

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

/-- The nom sg cell, `Case=Nom|Number=Sing`. -/
def nom_sg : Cell := { case_ := ↑UD.Case.Nom, number := ↑UD.Number.Sing }

/-- The gen sg cell, `Case=Gen|Number=Sing`. -/
def gen_sg : Cell := { case_ := ↑UD.Case.Gen, number := ↑UD.Number.Sing }

/-- The dat sg cell, `Case=Dat|Number=Sing`. -/
def dat_sg : Cell := { case_ := ↑UD.Case.Dat, number := ↑UD.Number.Sing }

/-- The acc sg cell, `Case=Acc|Number=Sing`. -/
def acc_sg : Cell := { case_ := ↑UD.Case.Acc, number := ↑UD.Number.Sing }

/-- The voc sg cell, `Case=Voc|Number=Sing`. -/
def voc_sg : Cell := { case_ := ↑UD.Case.Voc, number := ↑UD.Number.Sing }

/-- The loc sg cell, `Case=Loc|Number=Sing`. -/
def loc_sg : Cell := { case_ := ↑UD.Case.Loc, number := ↑UD.Number.Sing }

/-- The ins sg cell, `Case=Ins|Number=Sing`. -/
def ins_sg : Cell := { case_ := ↑UD.Case.Ins, number := ↑UD.Number.Sing }

/-- The nom pl cell, `Case=Nom|Number=Plur`. -/
def nom_pl : Cell := { case_ := ↑UD.Case.Nom, number := ↑UD.Number.Plur }

/-- The gen pl cell, `Case=Gen|Number=Plur`. -/
def gen_pl : Cell := { case_ := ↑UD.Case.Gen, number := ↑UD.Number.Plur }

/-- The dat pl cell, `Case=Dat|Number=Plur`. -/
def dat_pl : Cell := { case_ := ↑UD.Case.Dat, number := ↑UD.Number.Plur }

/-- The acc pl cell, `Case=Acc|Number=Plur`. -/
def acc_pl : Cell := { case_ := ↑UD.Case.Acc, number := ↑UD.Number.Plur }

/-- The voc pl cell, `Case=Voc|Number=Plur`. -/
def voc_pl : Cell := { case_ := ↑UD.Case.Voc, number := ↑UD.Number.Plur }

/-- The loc pl cell, `Case=Loc|Number=Plur`. -/
def loc_pl : Cell := { case_ := ↑UD.Case.Loc, number := ↑UD.Number.Plur }

/-- The ins pl cell, `Case=Ins|Number=Plur`. -/
def ins_pl : Cell := { case_ := ↑UD.Case.Ins, number := ↑UD.Number.Plur }

/-- The nom sg masc cell, `Case=Nom|Number=Sing|Gender=Masc`. -/
def nom_sg_masc : Cell :=
  { case_ := ↑UD.Case.Nom, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Masc }

/-- The voc sg masc cell, `Case=Voc|Number=Sing|Gender=Masc`. -/
def voc_sg_masc : Cell :=
  { case_ := ↑UD.Case.Voc, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Masc }

/-- The acc sg masc cell, `Case=Acc|Number=Sing|Gender=Masc`. -/
def acc_sg_masc : Cell :=
  { case_ := ↑UD.Case.Acc, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Masc }

/-- The ins sg masc cell, `Case=Ins|Number=Sing|Gender=Masc`. -/
def ins_sg_masc : Cell :=
  { case_ := ↑UD.Case.Ins, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Masc }

/-- The dat sg masc cell, `Case=Dat|Number=Sing|Gender=Masc`. -/
def dat_sg_masc : Cell :=
  { case_ := ↑UD.Case.Dat, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Masc }

/-- The abl sg masc cell, `Case=Abl|Number=Sing|Gender=Masc`. -/
def abl_sg_masc : Cell :=
  { case_ := ↑UD.Case.Abl, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Masc }

/-- The gen sg masc cell, `Case=Gen|Number=Sing|Gender=Masc`. -/
def gen_sg_masc : Cell :=
  { case_ := ↑UD.Case.Gen, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Masc }

/-- The loc sg masc cell, `Case=Loc|Number=Sing|Gender=Masc`. -/
def loc_sg_masc : Cell :=
  { case_ := ↑UD.Case.Loc, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Masc }

/-- The nom du masc cell, `Case=Nom|Number=Dual|Gender=Masc`. -/
def nom_du_masc : Cell :=
  { case_ := ↑UD.Case.Nom, number := ↑UD.Number.Dual, gender := ↑UD.Gender.Masc }

/-- The voc du masc cell, `Case=Voc|Number=Dual|Gender=Masc`. -/
def voc_du_masc : Cell :=
  { case_ := ↑UD.Case.Voc, number := ↑UD.Number.Dual, gender := ↑UD.Gender.Masc }

/-- The acc du masc cell, `Case=Acc|Number=Dual|Gender=Masc`. -/
def acc_du_masc : Cell :=
  { case_ := ↑UD.Case.Acc, number := ↑UD.Number.Dual, gender := ↑UD.Gender.Masc }

/-- The ins du masc cell, `Case=Ins|Number=Dual|Gender=Masc`. -/
def ins_du_masc : Cell :=
  { case_ := ↑UD.Case.Ins, number := ↑UD.Number.Dual, gender := ↑UD.Gender.Masc }

/-- The dat du masc cell, `Case=Dat|Number=Dual|Gender=Masc`. -/
def dat_du_masc : Cell :=
  { case_ := ↑UD.Case.Dat, number := ↑UD.Number.Dual, gender := ↑UD.Gender.Masc }

/-- The abl du masc cell, `Case=Abl|Number=Dual|Gender=Masc`. -/
def abl_du_masc : Cell :=
  { case_ := ↑UD.Case.Abl, number := ↑UD.Number.Dual, gender := ↑UD.Gender.Masc }

/-- The gen du masc cell, `Case=Gen|Number=Dual|Gender=Masc`. -/
def gen_du_masc : Cell :=
  { case_ := ↑UD.Case.Gen, number := ↑UD.Number.Dual, gender := ↑UD.Gender.Masc }

/-- The loc du masc cell, `Case=Loc|Number=Dual|Gender=Masc`. -/
def loc_du_masc : Cell :=
  { case_ := ↑UD.Case.Loc, number := ↑UD.Number.Dual, gender := ↑UD.Gender.Masc }

/-- The nom pl masc cell, `Case=Nom|Number=Plur|Gender=Masc`. -/
def nom_pl_masc : Cell :=
  { case_ := ↑UD.Case.Nom, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Masc }

/-- The voc pl masc cell, `Case=Voc|Number=Plur|Gender=Masc`. -/
def voc_pl_masc : Cell :=
  { case_ := ↑UD.Case.Voc, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Masc }

/-- The acc pl masc cell, `Case=Acc|Number=Plur|Gender=Masc`. -/
def acc_pl_masc : Cell :=
  { case_ := ↑UD.Case.Acc, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Masc }

/-- The ins pl masc cell, `Case=Ins|Number=Plur|Gender=Masc`. -/
def ins_pl_masc : Cell :=
  { case_ := ↑UD.Case.Ins, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Masc }

/-- The dat pl masc cell, `Case=Dat|Number=Plur|Gender=Masc`. -/
def dat_pl_masc : Cell :=
  { case_ := ↑UD.Case.Dat, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Masc }

/-- The abl pl masc cell, `Case=Abl|Number=Plur|Gender=Masc`. -/
def abl_pl_masc : Cell :=
  { case_ := ↑UD.Case.Abl, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Masc }

/-- The gen pl masc cell, `Case=Gen|Number=Plur|Gender=Masc`. -/
def gen_pl_masc : Cell :=
  { case_ := ↑UD.Case.Gen, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Masc }

/-- The loc pl masc cell, `Case=Loc|Number=Plur|Gender=Masc`. -/
def loc_pl_masc : Cell :=
  { case_ := ↑UD.Case.Loc, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Masc }

/-- The nom sg neut cell, `Case=Nom|Number=Sing|Gender=Neut`. -/
def nom_sg_neut : Cell :=
  { case_ := ↑UD.Case.Nom, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Neut }

/-- The voc sg neut cell, `Case=Voc|Number=Sing|Gender=Neut`. -/
def voc_sg_neut : Cell :=
  { case_ := ↑UD.Case.Voc, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Neut }

/-- The acc sg neut cell, `Case=Acc|Number=Sing|Gender=Neut`. -/
def acc_sg_neut : Cell :=
  { case_ := ↑UD.Case.Acc, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Neut }

/-- The ins sg neut cell, `Case=Ins|Number=Sing|Gender=Neut`. -/
def ins_sg_neut : Cell :=
  { case_ := ↑UD.Case.Ins, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Neut }

/-- The dat sg neut cell, `Case=Dat|Number=Sing|Gender=Neut`. -/
def dat_sg_neut : Cell :=
  { case_ := ↑UD.Case.Dat, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Neut }

/-- The abl sg neut cell, `Case=Abl|Number=Sing|Gender=Neut`. -/
def abl_sg_neut : Cell :=
  { case_ := ↑UD.Case.Abl, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Neut }

/-- The gen sg neut cell, `Case=Gen|Number=Sing|Gender=Neut`. -/
def gen_sg_neut : Cell :=
  { case_ := ↑UD.Case.Gen, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Neut }

/-- The loc sg neut cell, `Case=Loc|Number=Sing|Gender=Neut`. -/
def loc_sg_neut : Cell :=
  { case_ := ↑UD.Case.Loc, number := ↑UD.Number.Sing, gender := ↑UD.Gender.Neut }

/-- The nom du neut cell, `Case=Nom|Number=Dual|Gender=Neut`. -/
def nom_du_neut : Cell :=
  { case_ := ↑UD.Case.Nom, number := ↑UD.Number.Dual, gender := ↑UD.Gender.Neut }

/-- The voc du neut cell, `Case=Voc|Number=Dual|Gender=Neut`. -/
def voc_du_neut : Cell :=
  { case_ := ↑UD.Case.Voc, number := ↑UD.Number.Dual, gender := ↑UD.Gender.Neut }

/-- The acc du neut cell, `Case=Acc|Number=Dual|Gender=Neut`. -/
def acc_du_neut : Cell :=
  { case_ := ↑UD.Case.Acc, number := ↑UD.Number.Dual, gender := ↑UD.Gender.Neut }

/-- The ins du neut cell, `Case=Ins|Number=Dual|Gender=Neut`. -/
def ins_du_neut : Cell :=
  { case_ := ↑UD.Case.Ins, number := ↑UD.Number.Dual, gender := ↑UD.Gender.Neut }

/-- The dat du neut cell, `Case=Dat|Number=Dual|Gender=Neut`. -/
def dat_du_neut : Cell :=
  { case_ := ↑UD.Case.Dat, number := ↑UD.Number.Dual, gender := ↑UD.Gender.Neut }

/-- The abl du neut cell, `Case=Abl|Number=Dual|Gender=Neut`. -/
def abl_du_neut : Cell :=
  { case_ := ↑UD.Case.Abl, number := ↑UD.Number.Dual, gender := ↑UD.Gender.Neut }

/-- The gen du neut cell, `Case=Gen|Number=Dual|Gender=Neut`. -/
def gen_du_neut : Cell :=
  { case_ := ↑UD.Case.Gen, number := ↑UD.Number.Dual, gender := ↑UD.Gender.Neut }

/-- The loc du neut cell, `Case=Loc|Number=Dual|Gender=Neut`. -/
def loc_du_neut : Cell :=
  { case_ := ↑UD.Case.Loc, number := ↑UD.Number.Dual, gender := ↑UD.Gender.Neut }

/-- The nom pl neut cell, `Case=Nom|Number=Plur|Gender=Neut`. -/
def nom_pl_neut : Cell :=
  { case_ := ↑UD.Case.Nom, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Neut }

/-- The voc pl neut cell, `Case=Voc|Number=Plur|Gender=Neut`. -/
def voc_pl_neut : Cell :=
  { case_ := ↑UD.Case.Voc, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Neut }

/-- The acc pl neut cell, `Case=Acc|Number=Plur|Gender=Neut`. -/
def acc_pl_neut : Cell :=
  { case_ := ↑UD.Case.Acc, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Neut }

/-- The ins pl neut cell, `Case=Ins|Number=Plur|Gender=Neut`. -/
def ins_pl_neut : Cell :=
  { case_ := ↑UD.Case.Ins, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Neut }

/-- The dat pl neut cell, `Case=Dat|Number=Plur|Gender=Neut`. -/
def dat_pl_neut : Cell :=
  { case_ := ↑UD.Case.Dat, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Neut }

/-- The abl pl neut cell, `Case=Abl|Number=Plur|Gender=Neut`. -/
def abl_pl_neut : Cell :=
  { case_ := ↑UD.Case.Abl, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Neut }

/-- The gen pl neut cell, `Case=Gen|Number=Plur|Gender=Neut`. -/
def gen_pl_neut : Cell :=
  { case_ := ↑UD.Case.Gen, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Neut }

/-- The loc pl neut cell, `Case=Loc|Number=Plur|Gender=Neut`. -/
def loc_pl_neut : Cell :=
  { case_ := ↑UD.Case.Loc, number := ↑UD.Number.Plur, gender := ↑UD.Gender.Neut }

def Lexemes.room : Lexeme :=
  { id := "room", languageId := "czec1258", parameterId := "room" }

def Lexemes.spring : Lexeme :=
  { id := "spring", languageId := "czec1258", parameterId := "spring" }

def Lexemes.bridge : Lexeme :=
  { id := "bridge", languageId := "czec1258", parameterId := "bridge" }

def Lexemes.woman : Lexeme :=
  { id := "woman", languageId := "czec1258", parameterId := "woman" }

def Lexemes.president : Lexeme :=
  { id := "president", languageId := "czec1258", parameterId := "president" }

def Lexemes.philosopher : Lexeme :=
  { id := "philosopher", languageId := "czec1258", parameterId := "philosopher" }

def Lexemes.servant : Lexeme :=
  { id := "servant", languageId := "czec1258", parameterId := "servant" }

def Lexemes.philologist : Lexeme :=
  { id := "philologist", languageId := "czec1258", parameterId := "philologist" }

def Lexemes.man : Lexeme :=
  { id := "man", languageId := "czec1258", parameterId := "man" }

def Lexemes.westerly : Lexeme :=
  { id := "westerly", languageId := "sans1269", parameterId := "westerly" }

def Lexemes.name : Lexeme :=
  { id := "name", languageId := "sans1269", parameterId := "name" }

def Lexemes.day : Lexeme :=
  { id := "day", languageId := "sans1269", parameterId := "day" }

def Lexemes.mind : Lexeme :=
  { id := "mind", languageId := "sans1269", parameterId := "mind" }

def room_nom_sg : Form Cell :=
  { id := "stump2006_room_nom_sg"
    lexeme := Lexemes.room
    cell := nom_sg
    form := "pokoj"
    segments := ["p", "o", "k", "o", "j"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def room_gen_sg : Form Cell :=
  { id := "stump2006_room_gen_sg"
    lexeme := Lexemes.room
    cell := gen_sg
    form := "pokoje"
    segments := ["p", "o", "k", "o", "j", "e"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def room_dat_sg : Form Cell :=
  { id := "stump2006_room_dat_sg"
    lexeme := Lexemes.room
    cell := dat_sg
    form := "pokoji"
    segments := ["p", "o", "k", "o", "j", "i"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def room_acc_sg : Form Cell :=
  { id := "stump2006_room_acc_sg"
    lexeme := Lexemes.room
    cell := acc_sg
    form := "pokoj"
    segments := ["p", "o", "k", "o", "j"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def room_voc_sg : Form Cell :=
  { id := "stump2006_room_voc_sg"
    lexeme := Lexemes.room
    cell := voc_sg
    form := "pokoji"
    segments := ["p", "o", "k", "o", "j", "i"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def room_loc_sg : Form Cell :=
  { id := "stump2006_room_loc_sg"
    lexeme := Lexemes.room
    cell := loc_sg
    form := "pokoji"
    segments := ["p", "o", "k", "o", "j", "i"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def room_ins_sg : Form Cell :=
  { id := "stump2006_room_ins_sg"
    lexeme := Lexemes.room
    cell := ins_sg
    form := "pokojem"
    segments := ["p", "o", "k", "o", "j", "e", "m"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def room_nom_pl : Form Cell :=
  { id := "stump2006_room_nom_pl"
    lexeme := Lexemes.room
    cell := nom_pl
    form := "pokoje"
    segments := ["p", "o", "k", "o", "j", "e"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def room_gen_pl : Form Cell :=
  { id := "stump2006_room_gen_pl"
    lexeme := Lexemes.room
    cell := gen_pl
    form := "pokojů"
    segments := ["p", "o", "k", "o", "j", "ů"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def room_dat_pl : Form Cell :=
  { id := "stump2006_room_dat_pl"
    lexeme := Lexemes.room
    cell := dat_pl
    form := "pokojům"
    segments := ["p", "o", "k", "o", "j", "ů", "m"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def room_acc_pl : Form Cell :=
  { id := "stump2006_room_acc_pl"
    lexeme := Lexemes.room
    cell := acc_pl
    form := "pokoje"
    segments := ["p", "o", "k", "o", "j", "e"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def room_voc_pl : Form Cell :=
  { id := "stump2006_room_voc_pl"
    lexeme := Lexemes.room
    cell := voc_pl
    form := "pokoje"
    segments := ["p", "o", "k", "o", "j", "e"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def room_loc_pl : Form Cell :=
  { id := "stump2006_room_loc_pl"
    lexeme := Lexemes.room
    cell := loc_pl
    form := "pokojích"
    segments := ["p", "o", "k", "o", "j", "í", "ch"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def room_ins_pl : Form Cell :=
  { id := "stump2006_room_ins_pl"
    lexeme := Lexemes.room
    cell := ins_pl
    form := "pokoji"
    segments := ["p", "o", "k", "o", "j", "i"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def spring_nom_sg : Form Cell :=
  { id := "stump2006_spring_nom_sg"
    lexeme := Lexemes.spring
    cell := nom_sg
    form := "pramen"
    segments := ["p", "r", "a", "m", "e", "n"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def spring_gen_sg : Form Cell :=
  { id := "stump2006_spring_gen_sg"
    lexeme := Lexemes.spring
    cell := gen_sg
    form := "pramene"
    segments := ["p", "r", "a", "m", "e", "n", "e"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def spring_dat_sg : Form Cell :=
  { id := "stump2006_spring_dat_sg"
    lexeme := Lexemes.spring
    cell := dat_sg
    form := "prameni"
    segments := ["p", "r", "a", "m", "e", "n", "i"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def spring_acc_sg : Form Cell :=
  { id := "stump2006_spring_acc_sg"
    lexeme := Lexemes.spring
    cell := acc_sg
    form := "pramen"
    segments := ["p", "r", "a", "m", "e", "n"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def spring_voc_sg : Form Cell :=
  { id := "stump2006_spring_voc_sg"
    lexeme := Lexemes.spring
    cell := voc_sg
    form := "prameni"
    segments := ["p", "r", "a", "m", "e", "n", "i"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def spring_loc_sg : Form Cell :=
  { id := "stump2006_spring_loc_sg"
    lexeme := Lexemes.spring
    cell := loc_sg
    form := "prameni"
    segments := ["p", "r", "a", "m", "e", "n", "i"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def spring_ins_sg : Form Cell :=
  { id := "stump2006_spring_ins_sg"
    lexeme := Lexemes.spring
    cell := ins_sg
    form := "pramenem"
    segments := ["p", "r", "a", "m", "e", "n", "e", "m"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def spring_nom_pl : Form Cell :=
  { id := "stump2006_spring_nom_pl"
    lexeme := Lexemes.spring
    cell := nom_pl
    form := "prameny"
    segments := ["p", "r", "a", "m", "e", "n", "y"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def spring_gen_pl : Form Cell :=
  { id := "stump2006_spring_gen_pl"
    lexeme := Lexemes.spring
    cell := gen_pl
    form := "pramenů"
    segments := ["p", "r", "a", "m", "e", "n", "ů"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def spring_dat_pl : Form Cell :=
  { id := "stump2006_spring_dat_pl"
    lexeme := Lexemes.spring
    cell := dat_pl
    form := "pramenům"
    segments := ["p", "r", "a", "m", "e", "n", "ů", "m"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def spring_acc_pl : Form Cell :=
  { id := "stump2006_spring_acc_pl"
    lexeme := Lexemes.spring
    cell := acc_pl
    form := "prameny"
    segments := ["p", "r", "a", "m", "e", "n", "y"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def spring_voc_pl : Form Cell :=
  { id := "stump2006_spring_voc_pl"
    lexeme := Lexemes.spring
    cell := voc_pl
    form := "prameny"
    segments := ["p", "r", "a", "m", "e", "n", "y"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def spring_loc_pl : Form Cell :=
  { id := "stump2006_spring_loc_pl"
    lexeme := Lexemes.spring
    cell := loc_pl
    form := "pramenech"
    segments := ["p", "r", "a", "m", "e", "n", "e", "ch"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def spring_ins_pl : Form Cell :=
  { id := "stump2006_spring_ins_pl"
    lexeme := Lexemes.spring
    cell := ins_pl
    form := "prameny"
    segments := ["p", "r", "a", "m", "e", "n", "y"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def bridge_nom_sg : Form Cell :=
  { id := "stump2006_bridge_nom_sg"
    lexeme := Lexemes.bridge
    cell := nom_sg
    form := "most"
    segments := ["m", "o", "s", "t"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def bridge_gen_sg : Form Cell :=
  { id := "stump2006_bridge_gen_sg"
    lexeme := Lexemes.bridge
    cell := gen_sg
    form := "mostu"
    segments := ["m", "o", "s", "t", "u"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def bridge_dat_sg : Form Cell :=
  { id := "stump2006_bridge_dat_sg"
    lexeme := Lexemes.bridge
    cell := dat_sg
    form := "mostu"
    segments := ["m", "o", "s", "t", "u"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def bridge_acc_sg : Form Cell :=
  { id := "stump2006_bridge_acc_sg"
    lexeme := Lexemes.bridge
    cell := acc_sg
    form := "most"
    segments := ["m", "o", "s", "t"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def bridge_voc_sg : Form Cell :=
  { id := "stump2006_bridge_voc_sg"
    lexeme := Lexemes.bridge
    cell := voc_sg
    form := "moste"
    segments := ["m", "o", "s", "t", "e"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def bridge_loc_sg : Form Cell :=
  { id := "stump2006_bridge_loc_sg"
    lexeme := Lexemes.bridge
    cell := loc_sg
    form := "mostě"
    segments := ["m", "o", "s", "t", "ě"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def bridge_ins_sg : Form Cell :=
  { id := "stump2006_bridge_ins_sg"
    lexeme := Lexemes.bridge
    cell := ins_sg
    form := "mostem"
    segments := ["m", "o", "s", "t", "e", "m"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def bridge_nom_pl : Form Cell :=
  { id := "stump2006_bridge_nom_pl"
    lexeme := Lexemes.bridge
    cell := nom_pl
    form := "mosty"
    segments := ["m", "o", "s", "t", "y"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def bridge_gen_pl : Form Cell :=
  { id := "stump2006_bridge_gen_pl"
    lexeme := Lexemes.bridge
    cell := gen_pl
    form := "mostů"
    segments := ["m", "o", "s", "t", "ů"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def bridge_dat_pl : Form Cell :=
  { id := "stump2006_bridge_dat_pl"
    lexeme := Lexemes.bridge
    cell := dat_pl
    form := "mostům"
    segments := ["m", "o", "s", "t", "ů", "m"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def bridge_acc_pl : Form Cell :=
  { id := "stump2006_bridge_acc_pl"
    lexeme := Lexemes.bridge
    cell := acc_pl
    form := "mosty"
    segments := ["m", "o", "s", "t", "y"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def bridge_voc_pl : Form Cell :=
  { id := "stump2006_bridge_voc_pl"
    lexeme := Lexemes.bridge
    cell := voc_pl
    form := "mosty"
    segments := ["m", "o", "s", "t", "y"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def bridge_loc_pl : Form Cell :=
  { id := "stump2006_bridge_loc_pl"
    lexeme := Lexemes.bridge
    cell := loc_pl
    form := "mostech"
    segments := ["m", "o", "s", "t", "e", "ch"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def bridge_ins_pl : Form Cell :=
  { id := "stump2006_bridge_ins_pl"
    lexeme := Lexemes.bridge
    cell := ins_pl
    form := "mosty"
    segments := ["m", "o", "s", "t", "y"]
    source := [
      ⟨"stump-2006", "Table 1"⟩
    ] }

def woman_nom_sg : Form Cell :=
  { id := "stump2006_woman_nom_sg"
    lexeme := Lexemes.woman
    cell := nom_sg
    form := "žena"
    segments := ["ž", "e", "n", "a"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def woman_gen_sg : Form Cell :=
  { id := "stump2006_woman_gen_sg"
    lexeme := Lexemes.woman
    cell := gen_sg
    form := "ženy"
    segments := ["ž", "e", "n", "y"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def woman_dat_sg : Form Cell :=
  { id := "stump2006_woman_dat_sg"
    lexeme := Lexemes.woman
    cell := dat_sg
    form := "ženě"
    segments := ["ž", "e", "n", "ě"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def woman_acc_sg : Form Cell :=
  { id := "stump2006_woman_acc_sg"
    lexeme := Lexemes.woman
    cell := acc_sg
    form := "ženu"
    segments := ["ž", "e", "n", "u"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def woman_voc_sg : Form Cell :=
  { id := "stump2006_woman_voc_sg"
    lexeme := Lexemes.woman
    cell := voc_sg
    form := "ženo"
    segments := ["ž", "e", "n", "o"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def woman_loc_sg : Form Cell :=
  { id := "stump2006_woman_loc_sg"
    lexeme := Lexemes.woman
    cell := loc_sg
    form := "ženě"
    segments := ["ž", "e", "n", "ě"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def woman_ins_sg : Form Cell :=
  { id := "stump2006_woman_ins_sg"
    lexeme := Lexemes.woman
    cell := ins_sg
    form := "ženou"
    segments := ["ž", "e", "n", "o", "u"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def woman_nom_pl : Form Cell :=
  { id := "stump2006_woman_nom_pl"
    lexeme := Lexemes.woman
    cell := nom_pl
    form := "ženy"
    segments := ["ž", "e", "n", "y"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def woman_gen_pl : Form Cell :=
  { id := "stump2006_woman_gen_pl"
    lexeme := Lexemes.woman
    cell := gen_pl
    form := "žen"
    segments := ["ž", "e", "n"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def woman_dat_pl : Form Cell :=
  { id := "stump2006_woman_dat_pl"
    lexeme := Lexemes.woman
    cell := dat_pl
    form := "ženám"
    segments := ["ž", "e", "n", "á", "m"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def woman_acc_pl : Form Cell :=
  { id := "stump2006_woman_acc_pl"
    lexeme := Lexemes.woman
    cell := acc_pl
    form := "ženy"
    segments := ["ž", "e", "n", "y"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def woman_voc_pl : Form Cell :=
  { id := "stump2006_woman_voc_pl"
    lexeme := Lexemes.woman
    cell := voc_pl
    form := "ženy"
    segments := ["ž", "e", "n", "y"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def woman_loc_pl : Form Cell :=
  { id := "stump2006_woman_loc_pl"
    lexeme := Lexemes.woman
    cell := loc_pl
    form := "ženách"
    segments := ["ž", "e", "n", "á", "ch"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def woman_ins_pl : Form Cell :=
  { id := "stump2006_woman_ins_pl"
    lexeme := Lexemes.woman
    cell := ins_pl
    form := "ženami"
    segments := ["ž", "e", "n", "a", "m", "i"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def president_nom_sg : Form Cell :=
  { id := "stump2006_president_nom_sg"
    lexeme := Lexemes.president
    cell := nom_sg
    form := "předseda"
    segments := ["p", "ř", "e", "d", "s", "e", "d", "a"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def president_gen_sg : Form Cell :=
  { id := "stump2006_president_gen_sg"
    lexeme := Lexemes.president
    cell := gen_sg
    form := "předsedy"
    segments := ["p", "ř", "e", "d", "s", "e", "d", "y"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def president_dat_sg : Form Cell :=
  { id := "stump2006_president_dat_sg"
    lexeme := Lexemes.president
    cell := dat_sg
    form := "předsedovi"
    segments := ["p", "ř", "e", "d", "s", "e", "d", "o", "v", "i"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def president_acc_sg : Form Cell :=
  { id := "stump2006_president_acc_sg"
    lexeme := Lexemes.president
    cell := acc_sg
    form := "předsedu"
    segments := ["p", "ř", "e", "d", "s", "e", "d", "u"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def president_voc_sg : Form Cell :=
  { id := "stump2006_president_voc_sg"
    lexeme := Lexemes.president
    cell := voc_sg
    form := "předsedo"
    segments := ["p", "ř", "e", "d", "s", "e", "d", "o"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def president_loc_sg : Form Cell :=
  { id := "stump2006_president_loc_sg"
    lexeme := Lexemes.president
    cell := loc_sg
    form := "předsedovi"
    segments := ["p", "ř", "e", "d", "s", "e", "d", "o", "v", "i"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def president_ins_sg : Form Cell :=
  { id := "stump2006_president_ins_sg"
    lexeme := Lexemes.president
    cell := ins_sg
    form := "předsedou"
    segments := ["p", "ř", "e", "d", "s", "e", "d", "o", "u"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def president_nom_pl : Form Cell :=
  { id := "stump2006_president_nom_pl"
    lexeme := Lexemes.president
    cell := nom_pl
    form := "předsedové"
    segments := ["p", "ř", "e", "d", "s", "e", "d", "o", "v", "é"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def president_gen_pl : Form Cell :=
  { id := "stump2006_president_gen_pl"
    lexeme := Lexemes.president
    cell := gen_pl
    form := "předsedů"
    segments := ["p", "ř", "e", "d", "s", "e", "d", "ů"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def president_dat_pl : Form Cell :=
  { id := "stump2006_president_dat_pl"
    lexeme := Lexemes.president
    cell := dat_pl
    form := "předsedům"
    segments := ["p", "ř", "e", "d", "s", "e", "d", "ů", "m"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def president_acc_pl : Form Cell :=
  { id := "stump2006_president_acc_pl"
    lexeme := Lexemes.president
    cell := acc_pl
    form := "předsedy"
    segments := ["p", "ř", "e", "d", "s", "e", "d", "y"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def president_voc_pl : Form Cell :=
  { id := "stump2006_president_voc_pl"
    lexeme := Lexemes.president
    cell := voc_pl
    form := "předsedové"
    segments := ["p", "ř", "e", "d", "s", "e", "d", "o", "v", "é"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def president_loc_pl : Form Cell :=
  { id := "stump2006_president_loc_pl"
    lexeme := Lexemes.president
    cell := loc_pl
    form := "předsedech"
    segments := ["p", "ř", "e", "d", "s", "e", "d", "e", "ch"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def president_ins_pl : Form Cell :=
  { id := "stump2006_president_ins_pl"
    lexeme := Lexemes.president
    cell := ins_pl
    form := "předsedy"
    segments := ["p", "ř", "e", "d", "s", "e", "d", "y"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def philosopher_nom_sg : Form Cell :=
  { id := "stump2006_philosopher_nom_sg"
    lexeme := Lexemes.philosopher
    cell := nom_sg
    form := "filosof"
    segments := ["f", "i", "l", "o", "s", "o", "f"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def philosopher_gen_sg : Form Cell :=
  { id := "stump2006_philosopher_gen_sg"
    lexeme := Lexemes.philosopher
    cell := gen_sg
    form := "filosofa"
    segments := ["f", "i", "l", "o", "s", "o", "f", "a"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def philosopher_dat_sg : Form Cell :=
  { id := "stump2006_philosopher_dat_sg"
    lexeme := Lexemes.philosopher
    cell := dat_sg
    form := "filosofovi"
    segments := ["f", "i", "l", "o", "s", "o", "f", "o", "v", "i"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def philosopher_dat_sg_u : Form Cell :=
  { id := "stump2006_philosopher_dat_sg_u"
    lexeme := Lexemes.philosopher
    cell := dat_sg
    form := "filosofu"
    segments := ["f", "i", "l", "o", "s", "o", "f", "u"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def philosopher_acc_sg : Form Cell :=
  { id := "stump2006_philosopher_acc_sg"
    lexeme := Lexemes.philosopher
    cell := acc_sg
    form := "filosofa"
    segments := ["f", "i", "l", "o", "s", "o", "f", "a"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def philosopher_voc_sg : Form Cell :=
  { id := "stump2006_philosopher_voc_sg"
    lexeme := Lexemes.philosopher
    cell := voc_sg
    form := "filosofe"
    segments := ["f", "i", "l", "o", "s", "o", "f", "e"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def philosopher_loc_sg : Form Cell :=
  { id := "stump2006_philosopher_loc_sg"
    lexeme := Lexemes.philosopher
    cell := loc_sg
    form := "filosofovi"
    segments := ["f", "i", "l", "o", "s", "o", "f", "o", "v", "i"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def philosopher_loc_sg_u : Form Cell :=
  { id := "stump2006_philosopher_loc_sg_u"
    lexeme := Lexemes.philosopher
    cell := loc_sg
    form := "filosofu"
    segments := ["f", "i", "l", "o", "s", "o", "f", "u"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def philosopher_ins_sg : Form Cell :=
  { id := "stump2006_philosopher_ins_sg"
    lexeme := Lexemes.philosopher
    cell := ins_sg
    form := "filosofem"
    segments := ["f", "i", "l", "o", "s", "o", "f", "e", "m"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def philosopher_nom_pl : Form Cell :=
  { id := "stump2006_philosopher_nom_pl"
    lexeme := Lexemes.philosopher
    cell := nom_pl
    form := "filosofové"
    segments := ["f", "i", "l", "o", "s", "o", "f", "o", "v", "é"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def philosopher_gen_pl : Form Cell :=
  { id := "stump2006_philosopher_gen_pl"
    lexeme := Lexemes.philosopher
    cell := gen_pl
    form := "filosofů"
    segments := ["f", "i", "l", "o", "s", "o", "f", "ů"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def philosopher_dat_pl : Form Cell :=
  { id := "stump2006_philosopher_dat_pl"
    lexeme := Lexemes.philosopher
    cell := dat_pl
    form := "filosofům"
    segments := ["f", "i", "l", "o", "s", "o", "f", "ů", "m"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def philosopher_acc_pl : Form Cell :=
  { id := "stump2006_philosopher_acc_pl"
    lexeme := Lexemes.philosopher
    cell := acc_pl
    form := "filosofy"
    segments := ["f", "i", "l", "o", "s", "o", "f", "y"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def philosopher_voc_pl : Form Cell :=
  { id := "stump2006_philosopher_voc_pl"
    lexeme := Lexemes.philosopher
    cell := voc_pl
    form := "filosofové"
    segments := ["f", "i", "l", "o", "s", "o", "f", "o", "v", "é"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def philosopher_loc_pl : Form Cell :=
  { id := "stump2006_philosopher_loc_pl"
    lexeme := Lexemes.philosopher
    cell := loc_pl
    form := "filosofech"
    segments := ["f", "i", "l", "o", "s", "o", "f", "e", "ch"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def philosopher_ins_pl : Form Cell :=
  { id := "stump2006_philosopher_ins_pl"
    lexeme := Lexemes.philosopher
    cell := ins_pl
    form := "filosofy"
    segments := ["f", "i", "l", "o", "s", "o", "f", "y"]
    source := [
      ⟨"stump-2006", "Table 6"⟩
    ] }

def servant_nom_sg : Form Cell :=
  { id := "stump2006_servant_nom_sg"
    lexeme := Lexemes.servant
    cell := nom_sg
    form := "sluha"
    segments := ["s", "l", "u", "h", "a"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def servant_gen_sg : Form Cell :=
  { id := "stump2006_servant_gen_sg"
    lexeme := Lexemes.servant
    cell := gen_sg
    form := "sluhy"
    segments := ["s", "l", "u", "h", "y"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def servant_dat_sg : Form Cell :=
  { id := "stump2006_servant_dat_sg"
    lexeme := Lexemes.servant
    cell := dat_sg
    form := "sluhovi"
    segments := ["s", "l", "u", "h", "o", "v", "i"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def servant_acc_sg : Form Cell :=
  { id := "stump2006_servant_acc_sg"
    lexeme := Lexemes.servant
    cell := acc_sg
    form := "sluhu"
    segments := ["s", "l", "u", "h", "u"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def servant_voc_sg : Form Cell :=
  { id := "stump2006_servant_voc_sg"
    lexeme := Lexemes.servant
    cell := voc_sg
    form := "sluho"
    segments := ["s", "l", "u", "h", "o"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def servant_loc_sg : Form Cell :=
  { id := "stump2006_servant_loc_sg"
    lexeme := Lexemes.servant
    cell := loc_sg
    form := "sluhovi"
    segments := ["s", "l", "u", "h", "o", "v", "i"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def servant_ins_sg : Form Cell :=
  { id := "stump2006_servant_ins_sg"
    lexeme := Lexemes.servant
    cell := ins_sg
    form := "sluhou"
    segments := ["s", "l", "u", "h", "o", "u"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def servant_nom_pl : Form Cell :=
  { id := "stump2006_servant_nom_pl"
    lexeme := Lexemes.servant
    cell := nom_pl
    form := "sluhové"
    segments := ["s", "l", "u", "h", "o", "v", "é"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def servant_gen_pl : Form Cell :=
  { id := "stump2006_servant_gen_pl"
    lexeme := Lexemes.servant
    cell := gen_pl
    form := "sluhů"
    segments := ["s", "l", "u", "h", "ů"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def servant_dat_pl : Form Cell :=
  { id := "stump2006_servant_dat_pl"
    lexeme := Lexemes.servant
    cell := dat_pl
    form := "sluhům"
    segments := ["s", "l", "u", "h", "ů", "m"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def servant_acc_pl : Form Cell :=
  { id := "stump2006_servant_acc_pl"
    lexeme := Lexemes.servant
    cell := acc_pl
    form := "sluhy"
    segments := ["s", "l", "u", "h", "y"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def servant_voc_pl : Form Cell :=
  { id := "stump2006_servant_voc_pl"
    lexeme := Lexemes.servant
    cell := voc_pl
    form := "sluhové"
    segments := ["s", "l", "u", "h", "o", "v", "é"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def servant_loc_pl : Form Cell :=
  { id := "stump2006_servant_loc_pl"
    lexeme := Lexemes.servant
    cell := loc_pl
    form := "sluzích"
    segments := ["s", "l", "u", "z", "í", "ch"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def servant_ins_pl : Form Cell :=
  { id := "stump2006_servant_ins_pl"
    lexeme := Lexemes.servant
    cell := ins_pl
    form := "sluhy"
    segments := ["s", "l", "u", "h", "y"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def philologist_nom_sg : Form Cell :=
  { id := "stump2006_philologist_nom_sg"
    lexeme := Lexemes.philologist
    cell := nom_sg
    form := "filolog"
    segments := ["f", "i", "l", "o", "l", "o", "g"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def philologist_gen_sg : Form Cell :=
  { id := "stump2006_philologist_gen_sg"
    lexeme := Lexemes.philologist
    cell := gen_sg
    form := "filologa"
    segments := ["f", "i", "l", "o", "l", "o", "g", "a"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def philologist_dat_sg : Form Cell :=
  { id := "stump2006_philologist_dat_sg"
    lexeme := Lexemes.philologist
    cell := dat_sg
    form := "filologovi"
    segments := ["f", "i", "l", "o", "l", "o", "g", "o", "v", "i"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def philologist_dat_sg_u : Form Cell :=
  { id := "stump2006_philologist_dat_sg_u"
    lexeme := Lexemes.philologist
    cell := dat_sg
    form := "filologu"
    segments := ["f", "i", "l", "o", "l", "o", "g", "u"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def philologist_acc_sg : Form Cell :=
  { id := "stump2006_philologist_acc_sg"
    lexeme := Lexemes.philologist
    cell := acc_sg
    form := "filologa"
    segments := ["f", "i", "l", "o", "l", "o", "g", "a"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def philologist_voc_sg : Form Cell :=
  { id := "stump2006_philologist_voc_sg"
    lexeme := Lexemes.philologist
    cell := voc_sg
    form := "filologu"
    segments := ["f", "i", "l", "o", "l", "o", "g", "u"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def philologist_loc_sg : Form Cell :=
  { id := "stump2006_philologist_loc_sg"
    lexeme := Lexemes.philologist
    cell := loc_sg
    form := "filologovi"
    segments := ["f", "i", "l", "o", "l", "o", "g", "o", "v", "i"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def philologist_loc_sg_u : Form Cell :=
  { id := "stump2006_philologist_loc_sg_u"
    lexeme := Lexemes.philologist
    cell := loc_sg
    form := "filologu"
    segments := ["f", "i", "l", "o", "l", "o", "g", "u"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def philologist_ins_sg : Form Cell :=
  { id := "stump2006_philologist_ins_sg"
    lexeme := Lexemes.philologist
    cell := ins_sg
    form := "filologem"
    segments := ["f", "i", "l", "o", "l", "o", "g", "e", "m"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def philologist_nom_pl : Form Cell :=
  { id := "stump2006_philologist_nom_pl"
    lexeme := Lexemes.philologist
    cell := nom_pl
    form := "filologové"
    segments := ["f", "i", "l", "o", "l", "o", "g", "o", "v", "é"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def philologist_gen_pl : Form Cell :=
  { id := "stump2006_philologist_gen_pl"
    lexeme := Lexemes.philologist
    cell := gen_pl
    form := "filologů"
    segments := ["f", "i", "l", "o", "l", "o", "g", "ů"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def philologist_dat_pl : Form Cell :=
  { id := "stump2006_philologist_dat_pl"
    lexeme := Lexemes.philologist
    cell := dat_pl
    form := "filologům"
    segments := ["f", "i", "l", "o", "l", "o", "g", "ů", "m"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def philologist_acc_pl : Form Cell :=
  { id := "stump2006_philologist_acc_pl"
    lexeme := Lexemes.philologist
    cell := acc_pl
    form := "filology"
    segments := ["f", "i", "l", "o", "l", "o", "g", "y"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def philologist_voc_pl : Form Cell :=
  { id := "stump2006_philologist_voc_pl"
    lexeme := Lexemes.philologist
    cell := voc_pl
    form := "filologové"
    segments := ["f", "i", "l", "o", "l", "o", "g", "o", "v", "é"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def philologist_loc_pl : Form Cell :=
  { id := "stump2006_philologist_loc_pl"
    lexeme := Lexemes.philologist
    cell := loc_pl
    form := "filolozích"
    segments := ["f", "i", "l", "o", "l", "o", "z", "í", "ch"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def philologist_ins_pl : Form Cell :=
  { id := "stump2006_philologist_ins_pl"
    lexeme := Lexemes.philologist
    cell := ins_pl
    form := "filology"
    segments := ["f", "i", "l", "o", "l", "o", "g", "y"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def man_nom_sg : Form Cell :=
  { id := "stump2006_man_nom_sg"
    lexeme := Lexemes.man
    cell := nom_sg
    form := "muž"
    segments := ["m", "u", "ž"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def man_gen_sg : Form Cell :=
  { id := "stump2006_man_gen_sg"
    lexeme := Lexemes.man
    cell := gen_sg
    form := "muže"
    segments := ["m", "u", "ž", "e"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def man_dat_sg : Form Cell :=
  { id := "stump2006_man_dat_sg"
    lexeme := Lexemes.man
    cell := dat_sg
    form := "mužovi"
    segments := ["m", "u", "ž", "o", "v", "i"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def man_dat_sg_i : Form Cell :=
  { id := "stump2006_man_dat_sg_i"
    lexeme := Lexemes.man
    cell := dat_sg
    form := "muži"
    segments := ["m", "u", "ž", "i"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def man_acc_sg : Form Cell :=
  { id := "stump2006_man_acc_sg"
    lexeme := Lexemes.man
    cell := acc_sg
    form := "muže"
    segments := ["m", "u", "ž", "e"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def man_voc_sg : Form Cell :=
  { id := "stump2006_man_voc_sg"
    lexeme := Lexemes.man
    cell := voc_sg
    form := "muži"
    segments := ["m", "u", "ž", "i"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def man_loc_sg : Form Cell :=
  { id := "stump2006_man_loc_sg"
    lexeme := Lexemes.man
    cell := loc_sg
    form := "mužovi"
    segments := ["m", "u", "ž", "o", "v", "i"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def man_loc_sg_i : Form Cell :=
  { id := "stump2006_man_loc_sg_i"
    lexeme := Lexemes.man
    cell := loc_sg
    form := "muži"
    segments := ["m", "u", "ž", "i"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def man_ins_sg : Form Cell :=
  { id := "stump2006_man_ins_sg"
    lexeme := Lexemes.man
    cell := ins_sg
    form := "mužem"
    segments := ["m", "u", "ž", "e", "m"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def man_nom_pl : Form Cell :=
  { id := "stump2006_man_nom_pl"
    lexeme := Lexemes.man
    cell := nom_pl
    form := "muži"
    segments := ["m", "u", "ž", "i"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def man_nom_pl_ove : Form Cell :=
  { id := "stump2006_man_nom_pl_ove"
    lexeme := Lexemes.man
    cell := nom_pl
    form := "mužové"
    segments := ["m", "u", "ž", "o", "v", "é"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def man_gen_pl : Form Cell :=
  { id := "stump2006_man_gen_pl"
    lexeme := Lexemes.man
    cell := gen_pl
    form := "mužů"
    segments := ["m", "u", "ž", "ů"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def man_dat_pl : Form Cell :=
  { id := "stump2006_man_dat_pl"
    lexeme := Lexemes.man
    cell := dat_pl
    form := "mužům"
    segments := ["m", "u", "ž", "ů", "m"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def man_acc_pl : Form Cell :=
  { id := "stump2006_man_acc_pl"
    lexeme := Lexemes.man
    cell := acc_pl
    form := "muže"
    segments := ["m", "u", "ž", "e"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def man_voc_pl : Form Cell :=
  { id := "stump2006_man_voc_pl"
    lexeme := Lexemes.man
    cell := voc_pl
    form := "muži"
    segments := ["m", "u", "ž", "i"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def man_voc_pl_ove : Form Cell :=
  { id := "stump2006_man_voc_pl_ove"
    lexeme := Lexemes.man
    cell := voc_pl
    form := "mužové"
    segments := ["m", "u", "ž", "o", "v", "é"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def man_loc_pl : Form Cell :=
  { id := "stump2006_man_loc_pl"
    lexeme := Lexemes.man
    cell := loc_pl
    form := "mužích"
    segments := ["m", "u", "ž", "í", "ch"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def man_ins_pl : Form Cell :=
  { id := "stump2006_man_ins_pl"
    lexeme := Lexemes.man
    cell := ins_pl
    form := "muži"
    segments := ["m", "u", "ž", "i"]
    source := [
      ⟨"stump-2006", "Table 8"⟩
    ] }

def westerly_masc_nom_sg : Form Cell :=
  { id := "stump2006_westerly_masc_nom_sg"
    lexeme := Lexemes.westerly
    cell := nom_sg_masc
    form := "pratyaṅ"
    segments := ["pratyaṅ"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_masc_voc_sg : Form Cell :=
  { id := "stump2006_westerly_masc_voc_sg"
    lexeme := Lexemes.westerly
    cell := voc_sg_masc
    form := "pratyaṅ"
    segments := ["pratyaṅ"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_masc_acc_sg : Form Cell :=
  { id := "stump2006_westerly_masc_acc_sg"
    lexeme := Lexemes.westerly
    cell := acc_sg_masc
    form := "pratyañcam"
    segments := ["pratyañc", "am"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_masc_ins_sg : Form Cell :=
  { id := "stump2006_westerly_masc_ins_sg"
    lexeme := Lexemes.westerly
    cell := ins_sg_masc
    form := "pratīcā"
    segments := ["pratīc", "ā"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_masc_dat_sg : Form Cell :=
  { id := "stump2006_westerly_masc_dat_sg"
    lexeme := Lexemes.westerly
    cell := dat_sg_masc
    form := "pratīce"
    segments := ["pratīc", "e"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_masc_abl_sg : Form Cell :=
  { id := "stump2006_westerly_masc_abl_sg"
    lexeme := Lexemes.westerly
    cell := abl_sg_masc
    form := "pratīcas"
    segments := ["pratīc", "as"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_masc_gen_sg : Form Cell :=
  { id := "stump2006_westerly_masc_gen_sg"
    lexeme := Lexemes.westerly
    cell := gen_sg_masc
    form := "pratīcas"
    segments := ["pratīc", "as"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_masc_loc_sg : Form Cell :=
  { id := "stump2006_westerly_masc_loc_sg"
    lexeme := Lexemes.westerly
    cell := loc_sg_masc
    form := "pratīci"
    segments := ["pratīc", "i"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_masc_nom_du : Form Cell :=
  { id := "stump2006_westerly_masc_nom_du"
    lexeme := Lexemes.westerly
    cell := nom_du_masc
    form := "pratyañcau"
    segments := ["pratyañc", "au"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_masc_voc_du : Form Cell :=
  { id := "stump2006_westerly_masc_voc_du"
    lexeme := Lexemes.westerly
    cell := voc_du_masc
    form := "pratyañcau"
    segments := ["pratyañc", "au"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_masc_acc_du : Form Cell :=
  { id := "stump2006_westerly_masc_acc_du"
    lexeme := Lexemes.westerly
    cell := acc_du_masc
    form := "pratyañcau"
    segments := ["pratyañc", "au"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_masc_ins_du : Form Cell :=
  { id := "stump2006_westerly_masc_ins_du"
    lexeme := Lexemes.westerly
    cell := ins_du_masc
    form := "pratyagbhyām"
    segments := ["pratyag", "bhyām"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_masc_dat_du : Form Cell :=
  { id := "stump2006_westerly_masc_dat_du"
    lexeme := Lexemes.westerly
    cell := dat_du_masc
    form := "pratyagbhyām"
    segments := ["pratyag", "bhyām"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_masc_abl_du : Form Cell :=
  { id := "stump2006_westerly_masc_abl_du"
    lexeme := Lexemes.westerly
    cell := abl_du_masc
    form := "pratyagbhyām"
    segments := ["pratyag", "bhyām"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_masc_gen_du : Form Cell :=
  { id := "stump2006_westerly_masc_gen_du"
    lexeme := Lexemes.westerly
    cell := gen_du_masc
    form := "pratīcos"
    segments := ["pratīc", "os"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_masc_loc_du : Form Cell :=
  { id := "stump2006_westerly_masc_loc_du"
    lexeme := Lexemes.westerly
    cell := loc_du_masc
    form := "pratīcos"
    segments := ["pratīc", "os"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_masc_nom_pl : Form Cell :=
  { id := "stump2006_westerly_masc_nom_pl"
    lexeme := Lexemes.westerly
    cell := nom_pl_masc
    form := "pratyañcas"
    segments := ["pratyañc", "as"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_masc_voc_pl : Form Cell :=
  { id := "stump2006_westerly_masc_voc_pl"
    lexeme := Lexemes.westerly
    cell := voc_pl_masc
    form := "pratyañcas"
    segments := ["pratyañc", "as"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_masc_acc_pl : Form Cell :=
  { id := "stump2006_westerly_masc_acc_pl"
    lexeme := Lexemes.westerly
    cell := acc_pl_masc
    form := "pratīcas"
    segments := ["pratīc", "as"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_masc_ins_pl : Form Cell :=
  { id := "stump2006_westerly_masc_ins_pl"
    lexeme := Lexemes.westerly
    cell := ins_pl_masc
    form := "pratyagbhis"
    segments := ["pratyag", "bhis"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_masc_dat_pl : Form Cell :=
  { id := "stump2006_westerly_masc_dat_pl"
    lexeme := Lexemes.westerly
    cell := dat_pl_masc
    form := "pratyagbhyas"
    segments := ["pratyag", "bhyas"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_masc_abl_pl : Form Cell :=
  { id := "stump2006_westerly_masc_abl_pl"
    lexeme := Lexemes.westerly
    cell := abl_pl_masc
    form := "pratyagbhyas"
    segments := ["pratyag", "bhyas"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_masc_gen_pl : Form Cell :=
  { id := "stump2006_westerly_masc_gen_pl"
    lexeme := Lexemes.westerly
    cell := gen_pl_masc
    form := "pratīcām"
    segments := ["pratīc", "ām"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_masc_loc_pl : Form Cell :=
  { id := "stump2006_westerly_masc_loc_pl"
    lexeme := Lexemes.westerly
    cell := loc_pl_masc
    form := "pratyakṣu"
    segments := ["pratyak", "ṣu"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_neut_nom_sg : Form Cell :=
  { id := "stump2006_westerly_neut_nom_sg"
    lexeme := Lexemes.westerly
    cell := nom_sg_neut
    form := "pratyak"
    segments := ["pratyak"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_neut_voc_sg : Form Cell :=
  { id := "stump2006_westerly_neut_voc_sg"
    lexeme := Lexemes.westerly
    cell := voc_sg_neut
    form := "pratyak"
    segments := ["pratyak"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_neut_acc_sg : Form Cell :=
  { id := "stump2006_westerly_neut_acc_sg"
    lexeme := Lexemes.westerly
    cell := acc_sg_neut
    form := "pratyak"
    segments := ["pratyak"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_neut_ins_sg : Form Cell :=
  { id := "stump2006_westerly_neut_ins_sg"
    lexeme := Lexemes.westerly
    cell := ins_sg_neut
    form := "pratīcā"
    segments := ["pratīc", "ā"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_neut_dat_sg : Form Cell :=
  { id := "stump2006_westerly_neut_dat_sg"
    lexeme := Lexemes.westerly
    cell := dat_sg_neut
    form := "pratīce"
    segments := ["pratīc", "e"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_neut_abl_sg : Form Cell :=
  { id := "stump2006_westerly_neut_abl_sg"
    lexeme := Lexemes.westerly
    cell := abl_sg_neut
    form := "pratīcas"
    segments := ["pratīc", "as"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_neut_gen_sg : Form Cell :=
  { id := "stump2006_westerly_neut_gen_sg"
    lexeme := Lexemes.westerly
    cell := gen_sg_neut
    form := "pratīcas"
    segments := ["pratīc", "as"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_neut_loc_sg : Form Cell :=
  { id := "stump2006_westerly_neut_loc_sg"
    lexeme := Lexemes.westerly
    cell := loc_sg_neut
    form := "pratīci"
    segments := ["pratīc", "i"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_neut_nom_du : Form Cell :=
  { id := "stump2006_westerly_neut_nom_du"
    lexeme := Lexemes.westerly
    cell := nom_du_neut
    form := "pratīcī"
    segments := ["pratīc", "ī"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_neut_voc_du : Form Cell :=
  { id := "stump2006_westerly_neut_voc_du"
    lexeme := Lexemes.westerly
    cell := voc_du_neut
    form := "pratīcī"
    segments := ["pratīc", "ī"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_neut_acc_du : Form Cell :=
  { id := "stump2006_westerly_neut_acc_du"
    lexeme := Lexemes.westerly
    cell := acc_du_neut
    form := "pratīcī"
    segments := ["pratīc", "ī"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_neut_ins_du : Form Cell :=
  { id := "stump2006_westerly_neut_ins_du"
    lexeme := Lexemes.westerly
    cell := ins_du_neut
    form := "pratyagbhyām"
    segments := ["pratyag", "bhyām"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_neut_dat_du : Form Cell :=
  { id := "stump2006_westerly_neut_dat_du"
    lexeme := Lexemes.westerly
    cell := dat_du_neut
    form := "pratyagbhyām"
    segments := ["pratyag", "bhyām"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_neut_abl_du : Form Cell :=
  { id := "stump2006_westerly_neut_abl_du"
    lexeme := Lexemes.westerly
    cell := abl_du_neut
    form := "pratyagbhyām"
    segments := ["pratyag", "bhyām"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_neut_gen_du : Form Cell :=
  { id := "stump2006_westerly_neut_gen_du"
    lexeme := Lexemes.westerly
    cell := gen_du_neut
    form := "pratīcos"
    segments := ["pratīc", "os"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_neut_loc_du : Form Cell :=
  { id := "stump2006_westerly_neut_loc_du"
    lexeme := Lexemes.westerly
    cell := loc_du_neut
    form := "pratīcos"
    segments := ["pratīc", "os"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_neut_nom_pl : Form Cell :=
  { id := "stump2006_westerly_neut_nom_pl"
    lexeme := Lexemes.westerly
    cell := nom_pl_neut
    form := "pratyañci"
    segments := ["pratyañc", "i"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_neut_voc_pl : Form Cell :=
  { id := "stump2006_westerly_neut_voc_pl"
    lexeme := Lexemes.westerly
    cell := voc_pl_neut
    form := "pratyañci"
    segments := ["pratyañc", "i"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_neut_acc_pl : Form Cell :=
  { id := "stump2006_westerly_neut_acc_pl"
    lexeme := Lexemes.westerly
    cell := acc_pl_neut
    form := "pratyañci"
    segments := ["pratyañc", "i"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_neut_ins_pl : Form Cell :=
  { id := "stump2006_westerly_neut_ins_pl"
    lexeme := Lexemes.westerly
    cell := ins_pl_neut
    form := "pratyagbhis"
    segments := ["pratyag", "bhis"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_neut_dat_pl : Form Cell :=
  { id := "stump2006_westerly_neut_dat_pl"
    lexeme := Lexemes.westerly
    cell := dat_pl_neut
    form := "pratyagbhyas"
    segments := ["pratyag", "bhyas"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_neut_abl_pl : Form Cell :=
  { id := "stump2006_westerly_neut_abl_pl"
    lexeme := Lexemes.westerly
    cell := abl_pl_neut
    form := "pratyagbhyas"
    segments := ["pratyag", "bhyas"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_neut_gen_pl : Form Cell :=
  { id := "stump2006_westerly_neut_gen_pl"
    lexeme := Lexemes.westerly
    cell := gen_pl_neut
    form := "pratīcām"
    segments := ["pratīc", "ām"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def westerly_neut_loc_pl : Form Cell :=
  { id := "stump2006_westerly_neut_loc_pl"
    lexeme := Lexemes.westerly
    cell := loc_pl_neut
    form := "pratyakṣu"
    segments := ["pratyak", "ṣu"]
    source := [
      ⟨"stump-2006", "Table 9"⟩
    ] }

def name_nom_sg : Form Cell :=
  { id := "stump2006_name_nom_sg"
    lexeme := Lexemes.name
    cell := nom_sg_neut
    form := "nāma"
    segments := ["nāma"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def name_voc_sg : Form Cell :=
  { id := "stump2006_name_voc_sg"
    lexeme := Lexemes.name
    cell := voc_sg_neut
    form := "nāma"
    segments := ["nāma"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def name_acc_sg : Form Cell :=
  { id := "stump2006_name_acc_sg"
    lexeme := Lexemes.name
    cell := acc_sg_neut
    form := "nāma"
    segments := ["nāma"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def name_ins_sg : Form Cell :=
  { id := "stump2006_name_ins_sg"
    lexeme := Lexemes.name
    cell := ins_sg_neut
    form := "nāmnā"
    segments := ["nāmn", "ā"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def name_dat_sg : Form Cell :=
  { id := "stump2006_name_dat_sg"
    lexeme := Lexemes.name
    cell := dat_sg_neut
    form := "nāmne"
    segments := ["nāmn", "e"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def name_abl_sg : Form Cell :=
  { id := "stump2006_name_abl_sg"
    lexeme := Lexemes.name
    cell := abl_sg_neut
    form := "nāmnas"
    segments := ["nāmn", "as"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def name_gen_sg : Form Cell :=
  { id := "stump2006_name_gen_sg"
    lexeme := Lexemes.name
    cell := gen_sg_neut
    form := "nāmnas"
    segments := ["nāmn", "as"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def name_loc_sg : Form Cell :=
  { id := "stump2006_name_loc_sg"
    lexeme := Lexemes.name
    cell := loc_sg_neut
    form := "nāmni"
    segments := ["nāmn", "i"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def name_nom_du : Form Cell :=
  { id := "stump2006_name_nom_du"
    lexeme := Lexemes.name
    cell := nom_du_neut
    form := "nāmnī"
    segments := ["nāmn", "ī"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def name_voc_du : Form Cell :=
  { id := "stump2006_name_voc_du"
    lexeme := Lexemes.name
    cell := voc_du_neut
    form := "nāmnī"
    segments := ["nāmn", "ī"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def name_acc_du : Form Cell :=
  { id := "stump2006_name_acc_du"
    lexeme := Lexemes.name
    cell := acc_du_neut
    form := "nāmnī"
    segments := ["nāmn", "ī"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def name_ins_du : Form Cell :=
  { id := "stump2006_name_ins_du"
    lexeme := Lexemes.name
    cell := ins_du_neut
    form := "nāmabhyām"
    segments := ["nāma", "bhyām"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def name_dat_du : Form Cell :=
  { id := "stump2006_name_dat_du"
    lexeme := Lexemes.name
    cell := dat_du_neut
    form := "nāmabhyām"
    segments := ["nāma", "bhyām"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def name_abl_du : Form Cell :=
  { id := "stump2006_name_abl_du"
    lexeme := Lexemes.name
    cell := abl_du_neut
    form := "nāmabhyām"
    segments := ["nāma", "bhyām"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def name_gen_du : Form Cell :=
  { id := "stump2006_name_gen_du"
    lexeme := Lexemes.name
    cell := gen_du_neut
    form := "nāmnos"
    segments := ["nāmn", "os"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def name_loc_du : Form Cell :=
  { id := "stump2006_name_loc_du"
    lexeme := Lexemes.name
    cell := loc_du_neut
    form := "nāmnos"
    segments := ["nāmn", "os"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def name_nom_pl : Form Cell :=
  { id := "stump2006_name_nom_pl"
    lexeme := Lexemes.name
    cell := nom_pl_neut
    form := "nāmāni"
    segments := ["nāmān", "i"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def name_voc_pl : Form Cell :=
  { id := "stump2006_name_voc_pl"
    lexeme := Lexemes.name
    cell := voc_pl_neut
    form := "nāmāni"
    segments := ["nāmān", "i"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def name_acc_pl : Form Cell :=
  { id := "stump2006_name_acc_pl"
    lexeme := Lexemes.name
    cell := acc_pl_neut
    form := "nāmāni"
    segments := ["nāmān", "i"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def name_ins_pl : Form Cell :=
  { id := "stump2006_name_ins_pl"
    lexeme := Lexemes.name
    cell := ins_pl_neut
    form := "nāmabhis"
    segments := ["nāma", "bhis"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def name_dat_pl : Form Cell :=
  { id := "stump2006_name_dat_pl"
    lexeme := Lexemes.name
    cell := dat_pl_neut
    form := "nāmabhyas"
    segments := ["nāma", "bhyas"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def name_abl_pl : Form Cell :=
  { id := "stump2006_name_abl_pl"
    lexeme := Lexemes.name
    cell := abl_pl_neut
    form := "nāmabhyas"
    segments := ["nāma", "bhyas"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def name_gen_pl : Form Cell :=
  { id := "stump2006_name_gen_pl"
    lexeme := Lexemes.name
    cell := gen_pl_neut
    form := "nāmnām"
    segments := ["nāmn", "ām"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def name_loc_pl : Form Cell :=
  { id := "stump2006_name_loc_pl"
    lexeme := Lexemes.name
    cell := loc_pl_neut
    form := "nāmasu"
    segments := ["nāma", "su"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def day_nom_sg : Form Cell :=
  { id := "stump2006_day_nom_sg"
    lexeme := Lexemes.day
    cell := nom_sg_neut
    form := "ahas"
    segments := ["ahas"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def day_voc_sg : Form Cell :=
  { id := "stump2006_day_voc_sg"
    lexeme := Lexemes.day
    cell := voc_sg_neut
    form := "ahas"
    segments := ["ahas"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def day_acc_sg : Form Cell :=
  { id := "stump2006_day_acc_sg"
    lexeme := Lexemes.day
    cell := acc_sg_neut
    form := "ahas"
    segments := ["ahas"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def day_ins_sg : Form Cell :=
  { id := "stump2006_day_ins_sg"
    lexeme := Lexemes.day
    cell := ins_sg_neut
    form := "ahnā"
    segments := ["ahn", "ā"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def day_dat_sg : Form Cell :=
  { id := "stump2006_day_dat_sg"
    lexeme := Lexemes.day
    cell := dat_sg_neut
    form := "ahne"
    segments := ["ahn", "e"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def day_abl_sg : Form Cell :=
  { id := "stump2006_day_abl_sg"
    lexeme := Lexemes.day
    cell := abl_sg_neut
    form := "ahnas"
    segments := ["ahn", "as"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def day_gen_sg : Form Cell :=
  { id := "stump2006_day_gen_sg"
    lexeme := Lexemes.day
    cell := gen_sg_neut
    form := "ahnas"
    segments := ["ahn", "as"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def day_loc_sg : Form Cell :=
  { id := "stump2006_day_loc_sg"
    lexeme := Lexemes.day
    cell := loc_sg_neut
    form := "ahni"
    segments := ["ahn", "i"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def day_nom_du : Form Cell :=
  { id := "stump2006_day_nom_du"
    lexeme := Lexemes.day
    cell := nom_du_neut
    form := "ahnī"
    segments := ["ahn", "ī"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def day_voc_du : Form Cell :=
  { id := "stump2006_day_voc_du"
    lexeme := Lexemes.day
    cell := voc_du_neut
    form := "ahnī"
    segments := ["ahn", "ī"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def day_acc_du : Form Cell :=
  { id := "stump2006_day_acc_du"
    lexeme := Lexemes.day
    cell := acc_du_neut
    form := "ahnī"
    segments := ["ahn", "ī"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def day_ins_du : Form Cell :=
  { id := "stump2006_day_ins_du"
    lexeme := Lexemes.day
    cell := ins_du_neut
    form := "ahobhyām"
    segments := ["aho", "bhyām"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def day_dat_du : Form Cell :=
  { id := "stump2006_day_dat_du"
    lexeme := Lexemes.day
    cell := dat_du_neut
    form := "ahobhyām"
    segments := ["aho", "bhyām"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def day_abl_du : Form Cell :=
  { id := "stump2006_day_abl_du"
    lexeme := Lexemes.day
    cell := abl_du_neut
    form := "ahobhyām"
    segments := ["aho", "bhyām"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def day_gen_du : Form Cell :=
  { id := "stump2006_day_gen_du"
    lexeme := Lexemes.day
    cell := gen_du_neut
    form := "ahnos"
    segments := ["ahn", "os"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def day_loc_du : Form Cell :=
  { id := "stump2006_day_loc_du"
    lexeme := Lexemes.day
    cell := loc_du_neut
    form := "ahnos"
    segments := ["ahn", "os"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def day_nom_pl : Form Cell :=
  { id := "stump2006_day_nom_pl"
    lexeme := Lexemes.day
    cell := nom_pl_neut
    form := "ahāni"
    segments := ["ahān", "i"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def day_voc_pl : Form Cell :=
  { id := "stump2006_day_voc_pl"
    lexeme := Lexemes.day
    cell := voc_pl_neut
    form := "ahāni"
    segments := ["ahān", "i"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def day_acc_pl : Form Cell :=
  { id := "stump2006_day_acc_pl"
    lexeme := Lexemes.day
    cell := acc_pl_neut
    form := "ahāni"
    segments := ["ahān", "i"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def day_ins_pl : Form Cell :=
  { id := "stump2006_day_ins_pl"
    lexeme := Lexemes.day
    cell := ins_pl_neut
    form := "ahobhis"
    segments := ["aho", "bhis"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def day_dat_pl : Form Cell :=
  { id := "stump2006_day_dat_pl"
    lexeme := Lexemes.day
    cell := dat_pl_neut
    form := "ahobhyas"
    segments := ["aho", "bhyas"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def day_abl_pl : Form Cell :=
  { id := "stump2006_day_abl_pl"
    lexeme := Lexemes.day
    cell := abl_pl_neut
    form := "ahobhyas"
    segments := ["aho", "bhyas"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def day_gen_pl : Form Cell :=
  { id := "stump2006_day_gen_pl"
    lexeme := Lexemes.day
    cell := gen_pl_neut
    form := "ahnām"
    segments := ["ahn", "ām"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def day_loc_pl : Form Cell :=
  { id := "stump2006_day_loc_pl"
    lexeme := Lexemes.day
    cell := loc_pl_neut
    form := "ahaḥsu"
    segments := ["ahaḥ", "su"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def mind_nom_sg : Form Cell :=
  { id := "stump2006_mind_nom_sg"
    lexeme := Lexemes.mind
    cell := nom_sg_neut
    form := "manas"
    segments := ["manas"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def mind_voc_sg : Form Cell :=
  { id := "stump2006_mind_voc_sg"
    lexeme := Lexemes.mind
    cell := voc_sg_neut
    form := "manas"
    segments := ["manas"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def mind_acc_sg : Form Cell :=
  { id := "stump2006_mind_acc_sg"
    lexeme := Lexemes.mind
    cell := acc_sg_neut
    form := "manas"
    segments := ["manas"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def mind_ins_sg : Form Cell :=
  { id := "stump2006_mind_ins_sg"
    lexeme := Lexemes.mind
    cell := ins_sg_neut
    form := "manasā"
    segments := ["manas", "ā"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def mind_dat_sg : Form Cell :=
  { id := "stump2006_mind_dat_sg"
    lexeme := Lexemes.mind
    cell := dat_sg_neut
    form := "manase"
    segments := ["manas", "e"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def mind_abl_sg : Form Cell :=
  { id := "stump2006_mind_abl_sg"
    lexeme := Lexemes.mind
    cell := abl_sg_neut
    form := "manasas"
    segments := ["manas", "as"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def mind_gen_sg : Form Cell :=
  { id := "stump2006_mind_gen_sg"
    lexeme := Lexemes.mind
    cell := gen_sg_neut
    form := "manasas"
    segments := ["manas", "as"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def mind_loc_sg : Form Cell :=
  { id := "stump2006_mind_loc_sg"
    lexeme := Lexemes.mind
    cell := loc_sg_neut
    form := "manasi"
    segments := ["manas", "i"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def mind_nom_du : Form Cell :=
  { id := "stump2006_mind_nom_du"
    lexeme := Lexemes.mind
    cell := nom_du_neut
    form := "manasī"
    segments := ["manas", "ī"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def mind_voc_du : Form Cell :=
  { id := "stump2006_mind_voc_du"
    lexeme := Lexemes.mind
    cell := voc_du_neut
    form := "manasī"
    segments := ["manas", "ī"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def mind_acc_du : Form Cell :=
  { id := "stump2006_mind_acc_du"
    lexeme := Lexemes.mind
    cell := acc_du_neut
    form := "manasī"
    segments := ["manas", "ī"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def mind_ins_du : Form Cell :=
  { id := "stump2006_mind_ins_du"
    lexeme := Lexemes.mind
    cell := ins_du_neut
    form := "manobhyām"
    segments := ["mano", "bhyām"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def mind_dat_du : Form Cell :=
  { id := "stump2006_mind_dat_du"
    lexeme := Lexemes.mind
    cell := dat_du_neut
    form := "manobhyām"
    segments := ["mano", "bhyām"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def mind_abl_du : Form Cell :=
  { id := "stump2006_mind_abl_du"
    lexeme := Lexemes.mind
    cell := abl_du_neut
    form := "manobhyām"
    segments := ["mano", "bhyām"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def mind_gen_du : Form Cell :=
  { id := "stump2006_mind_gen_du"
    lexeme := Lexemes.mind
    cell := gen_du_neut
    form := "manasos"
    segments := ["manas", "os"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def mind_loc_du : Form Cell :=
  { id := "stump2006_mind_loc_du"
    lexeme := Lexemes.mind
    cell := loc_du_neut
    form := "manasos"
    segments := ["manas", "os"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def mind_nom_pl : Form Cell :=
  { id := "stump2006_mind_nom_pl"
    lexeme := Lexemes.mind
    cell := nom_pl_neut
    form := "manāṃsi"
    segments := ["manāṃs", "i"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def mind_voc_pl : Form Cell :=
  { id := "stump2006_mind_voc_pl"
    lexeme := Lexemes.mind
    cell := voc_pl_neut
    form := "manāṃsi"
    segments := ["manāṃs", "i"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def mind_acc_pl : Form Cell :=
  { id := "stump2006_mind_acc_pl"
    lexeme := Lexemes.mind
    cell := acc_pl_neut
    form := "manāṃsi"
    segments := ["manāṃs", "i"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def mind_ins_pl : Form Cell :=
  { id := "stump2006_mind_ins_pl"
    lexeme := Lexemes.mind
    cell := ins_pl_neut
    form := "manobhis"
    segments := ["mano", "bhis"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def mind_dat_pl : Form Cell :=
  { id := "stump2006_mind_dat_pl"
    lexeme := Lexemes.mind
    cell := dat_pl_neut
    form := "manobhyas"
    segments := ["mano", "bhyas"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def mind_abl_pl : Form Cell :=
  { id := "stump2006_mind_abl_pl"
    lexeme := Lexemes.mind
    cell := abl_pl_neut
    form := "manobhyas"
    segments := ["mano", "bhyas"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def mind_gen_pl : Form Cell :=
  { id := "stump2006_mind_gen_pl"
    lexeme := Lexemes.mind
    cell := gen_pl_neut
    form := "manasām"
    segments := ["manas", "ām"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

def mind_loc_pl : Form Cell :=
  { id := "stump2006_mind_loc_pl"
    lexeme := Lexemes.mind
    cell := loc_pl_neut
    form := "manaḥsu"
    segments := ["manaḥ", "su"]
    source := [
      ⟨"stump-2006", "Table 10"⟩
    ] }

/-- The source's analysis of a form, its parse rather than data. -/
structure Analysis where
  /-- The form analysed. -/
  form : Form Cell
  /-- The `Grade` column, the stem grade the paper assigns. -/
  grade : Option Grade := none
  /-- The `Stem` column, the stem the paper assigns. -/
  stem : Option String := none
  deriving DecidableEq, Repr

def room_nom_sg.analysis : Analysis :=
  { form := room_nom_sg }

def room_gen_sg.analysis : Analysis :=
  { form := room_gen_sg }

def room_dat_sg.analysis : Analysis :=
  { form := room_dat_sg }

def room_acc_sg.analysis : Analysis :=
  { form := room_acc_sg }

def room_voc_sg.analysis : Analysis :=
  { form := room_voc_sg }

def room_loc_sg.analysis : Analysis :=
  { form := room_loc_sg }

def room_ins_sg.analysis : Analysis :=
  { form := room_ins_sg }

def room_nom_pl.analysis : Analysis :=
  { form := room_nom_pl }

def room_gen_pl.analysis : Analysis :=
  { form := room_gen_pl }

def room_dat_pl.analysis : Analysis :=
  { form := room_dat_pl }

def room_acc_pl.analysis : Analysis :=
  { form := room_acc_pl }

def room_voc_pl.analysis : Analysis :=
  { form := room_voc_pl }

def room_loc_pl.analysis : Analysis :=
  { form := room_loc_pl }

def room_ins_pl.analysis : Analysis :=
  { form := room_ins_pl }

def spring_nom_sg.analysis : Analysis :=
  { form := spring_nom_sg }

def spring_gen_sg.analysis : Analysis :=
  { form := spring_gen_sg }

def spring_dat_sg.analysis : Analysis :=
  { form := spring_dat_sg }

def spring_acc_sg.analysis : Analysis :=
  { form := spring_acc_sg }

def spring_voc_sg.analysis : Analysis :=
  { form := spring_voc_sg }

def spring_loc_sg.analysis : Analysis :=
  { form := spring_loc_sg }

def spring_ins_sg.analysis : Analysis :=
  { form := spring_ins_sg }

def spring_nom_pl.analysis : Analysis :=
  { form := spring_nom_pl }

def spring_gen_pl.analysis : Analysis :=
  { form := spring_gen_pl }

def spring_dat_pl.analysis : Analysis :=
  { form := spring_dat_pl }

def spring_acc_pl.analysis : Analysis :=
  { form := spring_acc_pl }

def spring_voc_pl.analysis : Analysis :=
  { form := spring_voc_pl }

def spring_loc_pl.analysis : Analysis :=
  { form := spring_loc_pl }

def spring_ins_pl.analysis : Analysis :=
  { form := spring_ins_pl }

def bridge_nom_sg.analysis : Analysis :=
  { form := bridge_nom_sg }

def bridge_gen_sg.analysis : Analysis :=
  { form := bridge_gen_sg }

def bridge_dat_sg.analysis : Analysis :=
  { form := bridge_dat_sg }

def bridge_acc_sg.analysis : Analysis :=
  { form := bridge_acc_sg }

def bridge_voc_sg.analysis : Analysis :=
  { form := bridge_voc_sg }

def bridge_loc_sg.analysis : Analysis :=
  { form := bridge_loc_sg }

def bridge_ins_sg.analysis : Analysis :=
  { form := bridge_ins_sg }

def bridge_nom_pl.analysis : Analysis :=
  { form := bridge_nom_pl }

def bridge_gen_pl.analysis : Analysis :=
  { form := bridge_gen_pl }

def bridge_dat_pl.analysis : Analysis :=
  { form := bridge_dat_pl }

def bridge_acc_pl.analysis : Analysis :=
  { form := bridge_acc_pl }

def bridge_voc_pl.analysis : Analysis :=
  { form := bridge_voc_pl }

def bridge_loc_pl.analysis : Analysis :=
  { form := bridge_loc_pl }

def bridge_ins_pl.analysis : Analysis :=
  { form := bridge_ins_pl }

def woman_nom_sg.analysis : Analysis :=
  { form := woman_nom_sg }

def woman_gen_sg.analysis : Analysis :=
  { form := woman_gen_sg }

def woman_dat_sg.analysis : Analysis :=
  { form := woman_dat_sg }

def woman_acc_sg.analysis : Analysis :=
  { form := woman_acc_sg }

def woman_voc_sg.analysis : Analysis :=
  { form := woman_voc_sg }

def woman_loc_sg.analysis : Analysis :=
  { form := woman_loc_sg }

def woman_ins_sg.analysis : Analysis :=
  { form := woman_ins_sg }

def woman_nom_pl.analysis : Analysis :=
  { form := woman_nom_pl }

def woman_gen_pl.analysis : Analysis :=
  { form := woman_gen_pl }

def woman_dat_pl.analysis : Analysis :=
  { form := woman_dat_pl }

def woman_acc_pl.analysis : Analysis :=
  { form := woman_acc_pl }

def woman_voc_pl.analysis : Analysis :=
  { form := woman_voc_pl }

def woman_loc_pl.analysis : Analysis :=
  { form := woman_loc_pl }

def woman_ins_pl.analysis : Analysis :=
  { form := woman_ins_pl }

def president_nom_sg.analysis : Analysis :=
  { form := president_nom_sg }

def president_gen_sg.analysis : Analysis :=
  { form := president_gen_sg }

def president_dat_sg.analysis : Analysis :=
  { form := president_dat_sg }

def president_acc_sg.analysis : Analysis :=
  { form := president_acc_sg }

def president_voc_sg.analysis : Analysis :=
  { form := president_voc_sg }

def president_loc_sg.analysis : Analysis :=
  { form := president_loc_sg }

def president_ins_sg.analysis : Analysis :=
  { form := president_ins_sg }

def president_nom_pl.analysis : Analysis :=
  { form := president_nom_pl }

def president_gen_pl.analysis : Analysis :=
  { form := president_gen_pl }

def president_dat_pl.analysis : Analysis :=
  { form := president_dat_pl }

def president_acc_pl.analysis : Analysis :=
  { form := president_acc_pl }

def president_voc_pl.analysis : Analysis :=
  { form := president_voc_pl }

def president_loc_pl.analysis : Analysis :=
  { form := president_loc_pl }

def president_ins_pl.analysis : Analysis :=
  { form := president_ins_pl }

def philosopher_nom_sg.analysis : Analysis :=
  { form := philosopher_nom_sg }

def philosopher_gen_sg.analysis : Analysis :=
  { form := philosopher_gen_sg }

def philosopher_dat_sg.analysis : Analysis :=
  { form := philosopher_dat_sg }

def philosopher_dat_sg_u.analysis : Analysis :=
  { form := philosopher_dat_sg_u }

def philosopher_acc_sg.analysis : Analysis :=
  { form := philosopher_acc_sg }

def philosopher_voc_sg.analysis : Analysis :=
  { form := philosopher_voc_sg }

def philosopher_loc_sg.analysis : Analysis :=
  { form := philosopher_loc_sg }

def philosopher_loc_sg_u.analysis : Analysis :=
  { form := philosopher_loc_sg_u }

def philosopher_ins_sg.analysis : Analysis :=
  { form := philosopher_ins_sg }

def philosopher_nom_pl.analysis : Analysis :=
  { form := philosopher_nom_pl }

def philosopher_gen_pl.analysis : Analysis :=
  { form := philosopher_gen_pl }

def philosopher_dat_pl.analysis : Analysis :=
  { form := philosopher_dat_pl }

def philosopher_acc_pl.analysis : Analysis :=
  { form := philosopher_acc_pl }

def philosopher_voc_pl.analysis : Analysis :=
  { form := philosopher_voc_pl }

def philosopher_loc_pl.analysis : Analysis :=
  { form := philosopher_loc_pl }

def philosopher_ins_pl.analysis : Analysis :=
  { form := philosopher_ins_pl }

def servant_nom_sg.analysis : Analysis :=
  { form := servant_nom_sg }

def servant_gen_sg.analysis : Analysis :=
  { form := servant_gen_sg }

def servant_dat_sg.analysis : Analysis :=
  { form := servant_dat_sg }

def servant_acc_sg.analysis : Analysis :=
  { form := servant_acc_sg }

def servant_voc_sg.analysis : Analysis :=
  { form := servant_voc_sg }

def servant_loc_sg.analysis : Analysis :=
  { form := servant_loc_sg }

def servant_ins_sg.analysis : Analysis :=
  { form := servant_ins_sg }

def servant_nom_pl.analysis : Analysis :=
  { form := servant_nom_pl }

def servant_gen_pl.analysis : Analysis :=
  { form := servant_gen_pl }

def servant_dat_pl.analysis : Analysis :=
  { form := servant_dat_pl }

def servant_acc_pl.analysis : Analysis :=
  { form := servant_acc_pl }

def servant_voc_pl.analysis : Analysis :=
  { form := servant_voc_pl }

def servant_loc_pl.analysis : Analysis :=
  { form := servant_loc_pl }

def servant_ins_pl.analysis : Analysis :=
  { form := servant_ins_pl }

def philologist_nom_sg.analysis : Analysis :=
  { form := philologist_nom_sg }

def philologist_gen_sg.analysis : Analysis :=
  { form := philologist_gen_sg }

def philologist_dat_sg.analysis : Analysis :=
  { form := philologist_dat_sg }

def philologist_dat_sg_u.analysis : Analysis :=
  { form := philologist_dat_sg_u }

def philologist_acc_sg.analysis : Analysis :=
  { form := philologist_acc_sg }

def philologist_voc_sg.analysis : Analysis :=
  { form := philologist_voc_sg }

def philologist_loc_sg.analysis : Analysis :=
  { form := philologist_loc_sg }

def philologist_loc_sg_u.analysis : Analysis :=
  { form := philologist_loc_sg_u }

def philologist_ins_sg.analysis : Analysis :=
  { form := philologist_ins_sg }

def philologist_nom_pl.analysis : Analysis :=
  { form := philologist_nom_pl }

def philologist_gen_pl.analysis : Analysis :=
  { form := philologist_gen_pl }

def philologist_dat_pl.analysis : Analysis :=
  { form := philologist_dat_pl }

def philologist_acc_pl.analysis : Analysis :=
  { form := philologist_acc_pl }

def philologist_voc_pl.analysis : Analysis :=
  { form := philologist_voc_pl }

def philologist_loc_pl.analysis : Analysis :=
  { form := philologist_loc_pl }

def philologist_ins_pl.analysis : Analysis :=
  { form := philologist_ins_pl }

def man_nom_sg.analysis : Analysis :=
  { form := man_nom_sg }

def man_gen_sg.analysis : Analysis :=
  { form := man_gen_sg }

def man_dat_sg.analysis : Analysis :=
  { form := man_dat_sg }

def man_dat_sg_i.analysis : Analysis :=
  { form := man_dat_sg_i }

def man_acc_sg.analysis : Analysis :=
  { form := man_acc_sg }

def man_voc_sg.analysis : Analysis :=
  { form := man_voc_sg }

def man_loc_sg.analysis : Analysis :=
  { form := man_loc_sg }

def man_loc_sg_i.analysis : Analysis :=
  { form := man_loc_sg_i }

def man_ins_sg.analysis : Analysis :=
  { form := man_ins_sg }

def man_nom_pl.analysis : Analysis :=
  { form := man_nom_pl }

def man_nom_pl_ove.analysis : Analysis :=
  { form := man_nom_pl_ove }

def man_gen_pl.analysis : Analysis :=
  { form := man_gen_pl }

def man_dat_pl.analysis : Analysis :=
  { form := man_dat_pl }

def man_acc_pl.analysis : Analysis :=
  { form := man_acc_pl }

def man_voc_pl.analysis : Analysis :=
  { form := man_voc_pl }

def man_voc_pl_ove.analysis : Analysis :=
  { form := man_voc_pl_ove }

def man_loc_pl.analysis : Analysis :=
  { form := man_loc_pl }

def man_ins_pl.analysis : Analysis :=
  { form := man_ins_pl }

def westerly_masc_nom_sg.analysis : Analysis :=
  { form := westerly_masc_nom_sg,
    grade := some Grade.strong }

def westerly_masc_voc_sg.analysis : Analysis :=
  { form := westerly_masc_voc_sg,
    grade := some Grade.strong }

def westerly_masc_acc_sg.analysis : Analysis :=
  { form := westerly_masc_acc_sg,
    grade := some Grade.strong }

def westerly_masc_ins_sg.analysis : Analysis :=
  { form := westerly_masc_ins_sg,
    grade := some Grade.weakest }

def westerly_masc_dat_sg.analysis : Analysis :=
  { form := westerly_masc_dat_sg,
    grade := some Grade.weakest }

def westerly_masc_abl_sg.analysis : Analysis :=
  { form := westerly_masc_abl_sg,
    grade := some Grade.weakest }

def westerly_masc_gen_sg.analysis : Analysis :=
  { form := westerly_masc_gen_sg,
    grade := some Grade.weakest }

def westerly_masc_loc_sg.analysis : Analysis :=
  { form := westerly_masc_loc_sg,
    grade := some Grade.weakest }

def westerly_masc_nom_du.analysis : Analysis :=
  { form := westerly_masc_nom_du,
    grade := some Grade.strong }

def westerly_masc_voc_du.analysis : Analysis :=
  { form := westerly_masc_voc_du,
    grade := some Grade.strong }

def westerly_masc_acc_du.analysis : Analysis :=
  { form := westerly_masc_acc_du,
    grade := some Grade.strong }

def westerly_masc_ins_du.analysis : Analysis :=
  { form := westerly_masc_ins_du,
    grade := some Grade.middle }

def westerly_masc_dat_du.analysis : Analysis :=
  { form := westerly_masc_dat_du,
    grade := some Grade.middle }

def westerly_masc_abl_du.analysis : Analysis :=
  { form := westerly_masc_abl_du,
    grade := some Grade.middle }

def westerly_masc_gen_du.analysis : Analysis :=
  { form := westerly_masc_gen_du,
    grade := some Grade.weakest }

def westerly_masc_loc_du.analysis : Analysis :=
  { form := westerly_masc_loc_du,
    grade := some Grade.weakest }

def westerly_masc_nom_pl.analysis : Analysis :=
  { form := westerly_masc_nom_pl,
    grade := some Grade.strong }

def westerly_masc_voc_pl.analysis : Analysis :=
  { form := westerly_masc_voc_pl,
    grade := some Grade.strong }

def westerly_masc_acc_pl.analysis : Analysis :=
  { form := westerly_masc_acc_pl,
    grade := some Grade.weakest }

def westerly_masc_ins_pl.analysis : Analysis :=
  { form := westerly_masc_ins_pl,
    grade := some Grade.middle }

def westerly_masc_dat_pl.analysis : Analysis :=
  { form := westerly_masc_dat_pl,
    grade := some Grade.middle }

def westerly_masc_abl_pl.analysis : Analysis :=
  { form := westerly_masc_abl_pl,
    grade := some Grade.middle }

def westerly_masc_gen_pl.analysis : Analysis :=
  { form := westerly_masc_gen_pl,
    grade := some Grade.weakest }

def westerly_masc_loc_pl.analysis : Analysis :=
  { form := westerly_masc_loc_pl,
    grade := some Grade.middle }

def westerly_neut_nom_sg.analysis : Analysis :=
  { form := westerly_neut_nom_sg,
    grade := some Grade.middle }

def westerly_neut_voc_sg.analysis : Analysis :=
  { form := westerly_neut_voc_sg,
    grade := some Grade.middle }

def westerly_neut_acc_sg.analysis : Analysis :=
  { form := westerly_neut_acc_sg,
    grade := some Grade.middle }

def westerly_neut_ins_sg.analysis : Analysis :=
  { form := westerly_neut_ins_sg,
    grade := some Grade.weakest }

def westerly_neut_dat_sg.analysis : Analysis :=
  { form := westerly_neut_dat_sg,
    grade := some Grade.weakest }

def westerly_neut_abl_sg.analysis : Analysis :=
  { form := westerly_neut_abl_sg,
    grade := some Grade.weakest }

def westerly_neut_gen_sg.analysis : Analysis :=
  { form := westerly_neut_gen_sg,
    grade := some Grade.weakest }

def westerly_neut_loc_sg.analysis : Analysis :=
  { form := westerly_neut_loc_sg,
    grade := some Grade.weakest }

def westerly_neut_nom_du.analysis : Analysis :=
  { form := westerly_neut_nom_du,
    grade := some Grade.weakest }

def westerly_neut_voc_du.analysis : Analysis :=
  { form := westerly_neut_voc_du,
    grade := some Grade.weakest }

def westerly_neut_acc_du.analysis : Analysis :=
  { form := westerly_neut_acc_du,
    grade := some Grade.weakest }

def westerly_neut_ins_du.analysis : Analysis :=
  { form := westerly_neut_ins_du,
    grade := some Grade.middle }

def westerly_neut_dat_du.analysis : Analysis :=
  { form := westerly_neut_dat_du,
    grade := some Grade.middle }

def westerly_neut_abl_du.analysis : Analysis :=
  { form := westerly_neut_abl_du,
    grade := some Grade.middle }

def westerly_neut_gen_du.analysis : Analysis :=
  { form := westerly_neut_gen_du,
    grade := some Grade.weakest }

def westerly_neut_loc_du.analysis : Analysis :=
  { form := westerly_neut_loc_du,
    grade := some Grade.weakest }

def westerly_neut_nom_pl.analysis : Analysis :=
  { form := westerly_neut_nom_pl,
    grade := some Grade.strong }

def westerly_neut_voc_pl.analysis : Analysis :=
  { form := westerly_neut_voc_pl,
    grade := some Grade.strong }

def westerly_neut_acc_pl.analysis : Analysis :=
  { form := westerly_neut_acc_pl,
    grade := some Grade.strong }

def westerly_neut_ins_pl.analysis : Analysis :=
  { form := westerly_neut_ins_pl,
    grade := some Grade.middle }

def westerly_neut_dat_pl.analysis : Analysis :=
  { form := westerly_neut_dat_pl,
    grade := some Grade.middle }

def westerly_neut_abl_pl.analysis : Analysis :=
  { form := westerly_neut_abl_pl,
    grade := some Grade.middle }

def westerly_neut_gen_pl.analysis : Analysis :=
  { form := westerly_neut_gen_pl,
    grade := some Grade.weakest }

def westerly_neut_loc_pl.analysis : Analysis :=
  { form := westerly_neut_loc_pl,
    grade := some Grade.middle }

def name_nom_sg.analysis : Analysis :=
  { form := name_nom_sg }

def name_voc_sg.analysis : Analysis :=
  { form := name_voc_sg }

def name_acc_sg.analysis : Analysis :=
  { form := name_acc_sg }

def name_ins_sg.analysis : Analysis :=
  { form := name_ins_sg }

def name_dat_sg.analysis : Analysis :=
  { form := name_dat_sg }

def name_abl_sg.analysis : Analysis :=
  { form := name_abl_sg }

def name_gen_sg.analysis : Analysis :=
  { form := name_gen_sg }

def name_loc_sg.analysis : Analysis :=
  { form := name_loc_sg }

def name_nom_du.analysis : Analysis :=
  { form := name_nom_du }

def name_voc_du.analysis : Analysis :=
  { form := name_voc_du }

def name_acc_du.analysis : Analysis :=
  { form := name_acc_du }

def name_ins_du.analysis : Analysis :=
  { form := name_ins_du }

def name_dat_du.analysis : Analysis :=
  { form := name_dat_du }

def name_abl_du.analysis : Analysis :=
  { form := name_abl_du }

def name_gen_du.analysis : Analysis :=
  { form := name_gen_du }

def name_loc_du.analysis : Analysis :=
  { form := name_loc_du }

def name_nom_pl.analysis : Analysis :=
  { form := name_nom_pl }

def name_voc_pl.analysis : Analysis :=
  { form := name_voc_pl }

def name_acc_pl.analysis : Analysis :=
  { form := name_acc_pl }

def name_ins_pl.analysis : Analysis :=
  { form := name_ins_pl }

def name_dat_pl.analysis : Analysis :=
  { form := name_dat_pl }

def name_abl_pl.analysis : Analysis :=
  { form := name_abl_pl }

def name_gen_pl.analysis : Analysis :=
  { form := name_gen_pl }

def name_loc_pl.analysis : Analysis :=
  { form := name_loc_pl }

def day_nom_sg.analysis : Analysis :=
  { form := day_nom_sg,
    stem := some "ahas" }

def day_voc_sg.analysis : Analysis :=
  { form := day_voc_sg,
    stem := some "ahas" }

def day_acc_sg.analysis : Analysis :=
  { form := day_acc_sg,
    stem := some "ahas" }

def day_ins_sg.analysis : Analysis :=
  { form := day_ins_sg,
    stem := some "ahn" }

def day_dat_sg.analysis : Analysis :=
  { form := day_dat_sg,
    stem := some "ahn" }

def day_abl_sg.analysis : Analysis :=
  { form := day_abl_sg,
    stem := some "ahn" }

def day_gen_sg.analysis : Analysis :=
  { form := day_gen_sg,
    stem := some "ahn" }

def day_loc_sg.analysis : Analysis :=
  { form := day_loc_sg,
    stem := some "ahn" }

def day_nom_du.analysis : Analysis :=
  { form := day_nom_du,
    stem := some "ahn" }

def day_voc_du.analysis : Analysis :=
  { form := day_voc_du,
    stem := some "ahn" }

def day_acc_du.analysis : Analysis :=
  { form := day_acc_du,
    stem := some "ahn" }

def day_ins_du.analysis : Analysis :=
  { form := day_ins_du,
    stem := some "ahas" }

def day_dat_du.analysis : Analysis :=
  { form := day_dat_du,
    stem := some "ahas" }

def day_abl_du.analysis : Analysis :=
  { form := day_abl_du,
    stem := some "ahas" }

def day_gen_du.analysis : Analysis :=
  { form := day_gen_du,
    stem := some "ahn" }

def day_loc_du.analysis : Analysis :=
  { form := day_loc_du,
    stem := some "ahn" }

def day_nom_pl.analysis : Analysis :=
  { form := day_nom_pl,
    stem := some "ahan" }

def day_voc_pl.analysis : Analysis :=
  { form := day_voc_pl,
    stem := some "ahan" }

def day_acc_pl.analysis : Analysis :=
  { form := day_acc_pl,
    stem := some "ahan" }

def day_ins_pl.analysis : Analysis :=
  { form := day_ins_pl,
    stem := some "ahas" }

def day_dat_pl.analysis : Analysis :=
  { form := day_dat_pl,
    stem := some "ahas" }

def day_abl_pl.analysis : Analysis :=
  { form := day_abl_pl,
    stem := some "ahas" }

def day_gen_pl.analysis : Analysis :=
  { form := day_gen_pl,
    stem := some "ahn" }

def day_loc_pl.analysis : Analysis :=
  { form := day_loc_pl,
    stem := some "ahas" }

def mind_nom_sg.analysis : Analysis :=
  { form := mind_nom_sg }

def mind_voc_sg.analysis : Analysis :=
  { form := mind_voc_sg }

def mind_acc_sg.analysis : Analysis :=
  { form := mind_acc_sg }

def mind_ins_sg.analysis : Analysis :=
  { form := mind_ins_sg }

def mind_dat_sg.analysis : Analysis :=
  { form := mind_dat_sg }

def mind_abl_sg.analysis : Analysis :=
  { form := mind_abl_sg }

def mind_gen_sg.analysis : Analysis :=
  { form := mind_gen_sg }

def mind_loc_sg.analysis : Analysis :=
  { form := mind_loc_sg }

def mind_nom_du.analysis : Analysis :=
  { form := mind_nom_du }

def mind_voc_du.analysis : Analysis :=
  { form := mind_voc_du }

def mind_acc_du.analysis : Analysis :=
  { form := mind_acc_du }

def mind_ins_du.analysis : Analysis :=
  { form := mind_ins_du }

def mind_dat_du.analysis : Analysis :=
  { form := mind_dat_du }

def mind_abl_du.analysis : Analysis :=
  { form := mind_abl_du }

def mind_gen_du.analysis : Analysis :=
  { form := mind_gen_du }

def mind_loc_du.analysis : Analysis :=
  { form := mind_loc_du }

def mind_nom_pl.analysis : Analysis :=
  { form := mind_nom_pl }

def mind_voc_pl.analysis : Analysis :=
  { form := mind_voc_pl }

def mind_acc_pl.analysis : Analysis :=
  { form := mind_acc_pl }

def mind_ins_pl.analysis : Analysis :=
  { form := mind_ins_pl }

def mind_dat_pl.analysis : Analysis :=
  { form := mind_dat_pl }

def mind_abl_pl.analysis : Analysis :=
  { form := mind_abl_pl }

def mind_gen_pl.analysis : Analysis :=
  { form := mind_gen_pl }

def mind_loc_pl.analysis : Analysis :=
  { form := mind_loc_pl }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.room, Lexemes.spring, Lexemes.bridge, Lexemes.woman,
  Lexemes.president, Lexemes.philosopher, Lexemes.servant, Lexemes.philologist, Lexemes.man,
  Lexemes.westerly, Lexemes.name, Lexemes.day, Lexemes.mind]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [room_nom_sg, room_gen_sg, room_dat_sg, room_acc_sg, room_voc_sg,
  room_loc_sg, room_ins_sg, room_nom_pl, room_gen_pl, room_dat_pl, room_acc_pl, room_voc_pl,
  room_loc_pl, room_ins_pl, spring_nom_sg, spring_gen_sg, spring_dat_sg, spring_acc_sg,
  spring_voc_sg, spring_loc_sg, spring_ins_sg, spring_nom_pl, spring_gen_pl, spring_dat_pl,
  spring_acc_pl, spring_voc_pl, spring_loc_pl, spring_ins_pl, bridge_nom_sg, bridge_gen_sg,
  bridge_dat_sg, bridge_acc_sg, bridge_voc_sg, bridge_loc_sg, bridge_ins_sg, bridge_nom_pl,
  bridge_gen_pl, bridge_dat_pl, bridge_acc_pl, bridge_voc_pl, bridge_loc_pl, bridge_ins_pl,
  woman_nom_sg, woman_gen_sg, woman_dat_sg, woman_acc_sg, woman_voc_sg, woman_loc_sg, woman_ins_sg,
  woman_nom_pl, woman_gen_pl, woman_dat_pl, woman_acc_pl, woman_voc_pl, woman_loc_pl, woman_ins_pl,
  president_nom_sg, president_gen_sg, president_dat_sg, president_acc_sg, president_voc_sg,
  president_loc_sg, president_ins_sg, president_nom_pl, president_gen_pl, president_dat_pl,
  president_acc_pl, president_voc_pl, president_loc_pl, president_ins_pl, philosopher_nom_sg,
  philosopher_gen_sg, philosopher_dat_sg, philosopher_dat_sg_u, philosopher_acc_sg,
  philosopher_voc_sg, philosopher_loc_sg, philosopher_loc_sg_u, philosopher_ins_sg,
  philosopher_nom_pl, philosopher_gen_pl, philosopher_dat_pl, philosopher_acc_pl,
  philosopher_voc_pl, philosopher_loc_pl, philosopher_ins_pl, servant_nom_sg, servant_gen_sg,
  servant_dat_sg, servant_acc_sg, servant_voc_sg, servant_loc_sg, servant_ins_sg, servant_nom_pl,
  servant_gen_pl, servant_dat_pl, servant_acc_pl, servant_voc_pl, servant_loc_pl, servant_ins_pl,
  philologist_nom_sg, philologist_gen_sg, philologist_dat_sg, philologist_dat_sg_u,
  philologist_acc_sg, philologist_voc_sg, philologist_loc_sg, philologist_loc_sg_u,
  philologist_ins_sg, philologist_nom_pl, philologist_gen_pl, philologist_dat_pl,
  philologist_acc_pl, philologist_voc_pl, philologist_loc_pl, philologist_ins_pl, man_nom_sg,
  man_gen_sg, man_dat_sg, man_dat_sg_i, man_acc_sg, man_voc_sg, man_loc_sg, man_loc_sg_i,
  man_ins_sg, man_nom_pl, man_nom_pl_ove, man_gen_pl, man_dat_pl, man_acc_pl, man_voc_pl,
  man_voc_pl_ove, man_loc_pl, man_ins_pl, westerly_masc_nom_sg, westerly_masc_voc_sg,
  westerly_masc_acc_sg, westerly_masc_ins_sg, westerly_masc_dat_sg, westerly_masc_abl_sg,
  westerly_masc_gen_sg, westerly_masc_loc_sg, westerly_masc_nom_du, westerly_masc_voc_du,
  westerly_masc_acc_du, westerly_masc_ins_du, westerly_masc_dat_du, westerly_masc_abl_du,
  westerly_masc_gen_du, westerly_masc_loc_du, westerly_masc_nom_pl, westerly_masc_voc_pl,
  westerly_masc_acc_pl, westerly_masc_ins_pl, westerly_masc_dat_pl, westerly_masc_abl_pl,
  westerly_masc_gen_pl, westerly_masc_loc_pl, westerly_neut_nom_sg, westerly_neut_voc_sg,
  westerly_neut_acc_sg, westerly_neut_ins_sg, westerly_neut_dat_sg, westerly_neut_abl_sg,
  westerly_neut_gen_sg, westerly_neut_loc_sg, westerly_neut_nom_du, westerly_neut_voc_du,
  westerly_neut_acc_du, westerly_neut_ins_du, westerly_neut_dat_du, westerly_neut_abl_du,
  westerly_neut_gen_du, westerly_neut_loc_du, westerly_neut_nom_pl, westerly_neut_voc_pl,
  westerly_neut_acc_pl, westerly_neut_ins_pl, westerly_neut_dat_pl, westerly_neut_abl_pl,
  westerly_neut_gen_pl, westerly_neut_loc_pl, name_nom_sg, name_voc_sg, name_acc_sg, name_ins_sg,
  name_dat_sg, name_abl_sg, name_gen_sg, name_loc_sg, name_nom_du, name_voc_du, name_acc_du,
  name_ins_du, name_dat_du, name_abl_du, name_gen_du, name_loc_du, name_nom_pl, name_voc_pl,
  name_acc_pl, name_ins_pl, name_dat_pl, name_abl_pl, name_gen_pl, name_loc_pl, day_nom_sg,
  day_voc_sg, day_acc_sg, day_ins_sg, day_dat_sg, day_abl_sg, day_gen_sg, day_loc_sg, day_nom_du,
  day_voc_du, day_acc_du, day_ins_du, day_dat_du, day_abl_du, day_gen_du, day_loc_du, day_nom_pl,
  day_voc_pl, day_acc_pl, day_ins_pl, day_dat_pl, day_abl_pl, day_gen_pl, day_loc_pl, mind_nom_sg,
  mind_voc_sg, mind_acc_sg, mind_ins_sg, mind_dat_sg, mind_abl_sg, mind_gen_sg, mind_loc_sg,
  mind_nom_du, mind_voc_du, mind_acc_du, mind_ins_du, mind_dat_du, mind_abl_du, mind_gen_du,
  mind_loc_du, mind_nom_pl, mind_voc_pl, mind_acc_pl, mind_ins_pl, mind_dat_pl, mind_abl_pl,
  mind_gen_pl, mind_loc_pl]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := []

/-- Every analysis of the data. -/
def analyses : List Analysis := [westerly_masc_nom_sg.analysis, westerly_masc_voc_sg.analysis,
  westerly_masc_acc_sg.analysis, westerly_masc_ins_sg.analysis, westerly_masc_dat_sg.analysis,
  westerly_masc_abl_sg.analysis, westerly_masc_gen_sg.analysis, westerly_masc_loc_sg.analysis,
  westerly_masc_nom_du.analysis, westerly_masc_voc_du.analysis, westerly_masc_acc_du.analysis,
  westerly_masc_ins_du.analysis, westerly_masc_dat_du.analysis, westerly_masc_abl_du.analysis,
  westerly_masc_gen_du.analysis, westerly_masc_loc_du.analysis, westerly_masc_nom_pl.analysis,
  westerly_masc_voc_pl.analysis, westerly_masc_acc_pl.analysis, westerly_masc_ins_pl.analysis,
  westerly_masc_dat_pl.analysis, westerly_masc_abl_pl.analysis, westerly_masc_gen_pl.analysis,
  westerly_masc_loc_pl.analysis, westerly_neut_nom_sg.analysis, westerly_neut_voc_sg.analysis,
  westerly_neut_acc_sg.analysis, westerly_neut_ins_sg.analysis, westerly_neut_dat_sg.analysis,
  westerly_neut_abl_sg.analysis, westerly_neut_gen_sg.analysis, westerly_neut_loc_sg.analysis,
  westerly_neut_nom_du.analysis, westerly_neut_voc_du.analysis, westerly_neut_acc_du.analysis,
  westerly_neut_ins_du.analysis, westerly_neut_dat_du.analysis, westerly_neut_abl_du.analysis,
  westerly_neut_gen_du.analysis, westerly_neut_loc_du.analysis, westerly_neut_nom_pl.analysis,
  westerly_neut_voc_pl.analysis, westerly_neut_acc_pl.analysis, westerly_neut_ins_pl.analysis,
  westerly_neut_dat_pl.analysis, westerly_neut_abl_pl.analysis, westerly_neut_gen_pl.analysis,
  westerly_neut_loc_pl.analysis, day_nom_sg.analysis, day_voc_sg.analysis, day_acc_sg.analysis,
  day_ins_sg.analysis, day_dat_sg.analysis, day_abl_sg.analysis, day_gen_sg.analysis,
  day_loc_sg.analysis, day_nom_du.analysis, day_voc_du.analysis, day_acc_du.analysis,
  day_ins_du.analysis, day_dat_du.analysis, day_abl_du.analysis, day_gen_du.analysis,
  day_loc_du.analysis, day_nom_pl.analysis, day_voc_pl.analysis, day_acc_pl.analysis,
  day_ins_pl.analysis, day_dat_pl.analysis, day_abl_pl.analysis, day_gen_pl.analysis,
  day_loc_pl.analysis]

end Stump2006.Wordlist
