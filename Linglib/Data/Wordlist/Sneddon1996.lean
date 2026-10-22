module

public import Linglib.Data.Wordlist.Schema

/-!
# `Sneddon1996`: word forms

Auto-generated from `Linglib/Data/Wordlist/Sneddon1996.json` by `scripts/gen_wordlist.py`. Do not
edit by hand; edit the JSON and re-run the generator. Declarations live in `namespace
Sneddon1996.Wordlist`.
-/

@[expose] public section

namespace Sneddon1996.Wordlist

open Data.Wordlist

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

def Lexemes.ajar : Lexeme :=
  { id := "ajar", languageId := "indo1316", parameterId := "ajar" }

def Lexemes.mengajar : Lexeme :=
  { id := "mengajar", languageId := "indo1316", parameterId := "mengajar" }

def Lexemes.pakai : Lexeme :=
  { id := "pakai", languageId := "indo1316", parameterId := "pakai" }

def Lexemes.memakai : Lexeme :=
  { id := "memakai", languageId := "indo1316", parameterId := "memakai" }

def Lexemes.beli : Lexeme :=
  { id := "beli", languageId := "indo1316", parameterId := "beli" }

def Lexemes.membeli : Lexeme :=
  { id := "membeli", languageId := "indo1316", parameterId := "membeli" }

def Lexemes.sewa : Lexeme :=
  { id := "sewa", languageId := "indo1316", parameterId := "sewa" }

def Lexemes.menyewa : Lexeme :=
  { id := "menyewa", languageId := "indo1316", parameterId := "menyewa" }

def Lexemes.lihat : Lexeme :=
  { id := "lihat", languageId := "indo1316", parameterId := "lihat" }

def Lexemes.melihat : Lexeme :=
  { id := "melihat", languageId := "indo1316", parameterId := "melihat" }

def Lexemes.tulis : Lexeme :=
  { id := "tulis", languageId := "indo1316", parameterId := "tulis" }

def Lexemes.penulis : Lexeme :=
  { id := "penulis", languageId := "indo1316", parameterId := "penulis" }

def Lexemes.besar : Lexeme :=
  { id := "besar", languageId := "indo1316", parameterId := "besar" }

def Lexemes.memperbesar : Lexeme :=
  { id := "memperbesar", languageId := "indo1316", parameterId := "memperbesar" }

def ajar : Form Cell :=
  { id := "sneddon1996_ajar"
    lexeme := Lexemes.ajar
    cell := {}
    form := "ajar"
    segments := ["a", "d̠ʒ", "a", "r"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def mengajar : Form Cell :=
  { id := "sneddon1996_mengajar"
    lexeme := Lexemes.mengajar
    cell := {}
    form := "mengajar"
    segments := ["m", "ə", "ŋ", "a", "d̠ʒ", "a", "r"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def pakai : Form Cell :=
  { id := "sneddon1996_pakai"
    lexeme := Lexemes.pakai
    cell := {}
    form := "pakai"
    segments := ["p", "a", "k", "a", "i"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def memakai : Form Cell :=
  { id := "sneddon1996_memakai"
    lexeme := Lexemes.memakai
    cell := {}
    form := "memakai"
    segments := ["m", "ə", "m", "a", "k", "a", "i"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def beli : Form Cell :=
  { id := "sneddon1996_beli"
    lexeme := Lexemes.beli
    cell := {}
    form := "beli"
    segments := ["b", "ə", "l", "i"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def membeli : Form Cell :=
  { id := "sneddon1996_membeli"
    lexeme := Lexemes.membeli
    cell := {}
    form := "membeli"
    segments := ["m", "ə", "m", "b", "ə", "l", "i"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def sewa : Form Cell :=
  { id := "sneddon1996_sewa"
    lexeme := Lexemes.sewa
    cell := {}
    form := "sewa"
    segments := ["s", "e", "w", "a"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def menyewa : Form Cell :=
  { id := "sneddon1996_menyewa"
    lexeme := Lexemes.menyewa
    cell := {}
    form := "menyewa"
    segments := ["m", "ə", "ɲ", "e", "w", "a"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def lihat : Form Cell :=
  { id := "sneddon1996_lihat"
    lexeme := Lexemes.lihat
    cell := {}
    form := "lihat"
    segments := ["l", "i", "h", "a", "t"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def melihat : Form Cell :=
  { id := "sneddon1996_melihat"
    lexeme := Lexemes.melihat
    cell := {}
    form := "melihat"
    segments := ["m", "ə", "l", "i", "h", "a", "t"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def tulis : Form Cell :=
  { id := "sneddon1996_tulis"
    lexeme := Lexemes.tulis
    cell := {}
    form := "tulis"
    segments := ["t", "u", "l", "i", "s"]
    source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] }

def penulis : Form Cell :=
  { id := "sneddon1996_penulis"
    lexeme := Lexemes.penulis
    cell := {}
    form := "penulis"
    segments := ["p", "ə", "n", "u", "l", "i", "s"]
    source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] }

def besar : Form Cell :=
  { id := "sneddon1996_besar"
    lexeme := Lexemes.besar
    cell := {}
    form := "besar"
    segments := ["b", "ə", "s", "a", "r"]
    source := [
      ⟨"sneddon-1996", "p. 26"⟩
    ] }

def memperbesar : Form Cell :=
  { id := "sneddon1996_memperbesar"
    lexeme := Lexemes.memperbesar
    cell := {}
    form := "memperbesar"
    segments := ["m", "ə", "m", "p", "ə", "r", "b", "ə", "s", "a", "r"]
    source := [
      ⟨"sneddon-1996", "p. 26"⟩
    ] }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.ajar, Lexemes.mengajar, Lexemes.pakai, Lexemes.memakai,
  Lexemes.beli, Lexemes.membeli, Lexemes.sewa, Lexemes.menyewa, Lexemes.lihat, Lexemes.melihat,
  Lexemes.tulis, Lexemes.penulis, Lexemes.besar, Lexemes.memperbesar]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [ajar, mengajar, pakai, memakai, beli, membeli, sewa, menyewa, lihat,
  melihat, tulis, penulis, besar, memperbesar]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := [
  { id := "sneddon1996_ajar_mengajar", form := ajar, target := mengajar, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_pakai_memakai", form := pakai, target := memakai, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_beli_membeli", form := beli, target := membeli, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_sewa_menyewa", form := sewa, target := menyewa, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_lihat_melihat", form := lihat, target := melihat, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_tulis_penulis", form := tulis, target := penulis, relation := "peN-",
    source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] },
  { id := "sneddon1996_besar_memperbesar", form := besar, target := memperbesar,
    relation := "meN- per-", source := [
      ⟨"sneddon-1996", "p. 26"⟩
    ] }]

end Sneddon1996.Wordlist
