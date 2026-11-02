module

public import Linglib.Data.Wordlist.Schema

/-!
# `Pater2001`: word forms

Auto-generated from `Linglib/Data/Wordlist/Pater2001.json` by `scripts/gen_wordlist.py`. Do not edit
by hand; edit the JSON and re-run the generator. Declarations live in `namespace
Pater2001.Wordlist`.
-/

@[expose] public section

namespace Pater2001.Wordlist

open CLDF.Wordlist

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

def Lexemes.paksa : Lexeme :=
  { id := "paksa", languageId := "indo1316", parameterId := "paksa" }

def Lexemes.memaksa : Lexeme :=
  { id := "memaksa", languageId := "indo1316", parameterId := "memaksa" }

def Lexemes.buat : Lexeme :=
  { id := "buat", languageId := "indo1316", parameterId := "buat" }

def Lexemes.membuat : Lexeme :=
  { id := "membuat", languageId := "indo1316", parameterId := "membuat" }

def Lexemes.empat : Lexeme :=
  { id := "empat", languageId := "indo1316", parameterId := "empat" }

def Lexemes.pilih : Lexeme :=
  { id := "pilih", languageId := "indo1316", parameterId := "pilih" }

def Lexemes.memilih : Lexeme :=
  { id := "memilih", languageId := "indo1316", parameterId := "memilih" }

def Lexemes.beli : Lexeme :=
  { id := "beli", languageId := "indo1316", parameterId := "beli" }

def Lexemes.membeli : Lexeme :=
  { id := "membeli", languageId := "indo1316", parameterId := "membeli" }

def Lexemes.besar : Lexeme :=
  { id := "besar", languageId := "indo1316", parameterId := "besar" }

def Lexemes.memperbesar : Lexeme :=
  { id := "memperbesar", languageId := "indo1316", parameterId := "memperbesar" }

def Lexemes.baru : Lexeme :=
  { id := "baru", languageId := "muna1247", parameterId := "baru" }

def Lexemes.baru_irr : Lexeme :=
  { id := "baru_irr", languageId := "muna1247", parameterId := "baru_irr" }

def Lexemes.bala : Lexeme :=
  { id := "bala", languageId := "muna1247", parameterId := "bala" }

def Lexemes.bala_irr : Lexeme :=
  { id := "bala_irr", languageId := "muna1247", parameterId := "bala_irr" }

def Lexemes.pili : Lexeme :=
  { id := "pili", languageId := "muna1247", parameterId := "pili" }

def Lexemes.mili : Lexeme :=
  { id := "mili", languageId := "muna1247", parameterId := "mili" }

def Lexemes.futaa : Lexeme :=
  { id := "futaa", languageId := "muna1247", parameterId := "futaa" }

def Lexemes.mutaa : Lexeme :=
  { id := "mutaa", languageId := "muna1247", parameterId := "mutaa" }

def Lexemes.waa : Lexeme :=
  { id := "waa", languageId := "muna1247", parameterId := "waa" }

def Lexemes.maa : Lexeme :=
  { id := "maa", languageId := "muna1247", parameterId := "maa" }

def Lexemes.wanu : Lexeme :=
  { id := "wanu", languageId := "muna1247", parameterId := "wanu" }

def Lexemes.wanu_irr : Lexeme :=
  { id := "wanu_irr", languageId := "muna1247", parameterId := "wanu_irr" }

def paksa : Form Cell :=
  { id := "pater2001_paksa"
    lexeme := Lexemes.paksa
    cell := {}
    form := "paksa"
    segments := ["p", "a", "k", "s", "a"]
    source := [
      ⟨"pater-2001", "(3)"⟩
    ] }

def memaksa : Form Cell :=
  { id := "pater2001_memaksa"
    lexeme := Lexemes.memaksa
    cell := {}
    form := "məmaksa"
    segments := ["m", "ə", "m", "a", "k", "s", "a"]
    source := [
      ⟨"pater-2001", "(3)"⟩
    ] }

def buat : Form Cell :=
  { id := "pater2001_buat"
    lexeme := Lexemes.buat
    cell := {}
    form := "buat"
    segments := ["b", "u", "a", "t"]
    source := [
      ⟨"pater-2001", "(3)"⟩
    ] }

def membuat : Form Cell :=
  { id := "pater2001_membuat"
    lexeme := Lexemes.membuat
    cell := {}
    form := "məmbuat"
    segments := ["m", "ə", "m", "b", "u", "a", "t"]
    source := [
      ⟨"pater-2001", "(3)"⟩
    ] }

def empat : Form Cell :=
  { id := "pater2001_empat"
    lexeme := Lexemes.empat
    cell := {}
    form := "əmpat"
    segments := ["ə", "m", "p", "a", "t"]
    source := [
      ⟨"pater-2001", "(4)"⟩
    ] }

def pilih : Form Cell :=
  { id := "pater2001_pilih"
    lexeme := Lexemes.pilih
    cell := {}
    form := "pilih"
    segments := ["p", "i", "l", "i", "h"]
    source := [
      ⟨"pater-2001", "(38)"⟩
    ] }

def memilih : Form Cell :=
  { id := "pater2001_memilih"
    lexeme := Lexemes.memilih
    cell := {}
    form := "məmilih"
    segments := ["m", "ə", "m", "i", "l", "i", "h"]
    source := [
      ⟨"pater-2001", "(38)"⟩
    ] }

def beli : Form Cell :=
  { id := "pater2001_beli"
    lexeme := Lexemes.beli
    cell := {}
    form := "bəli"
    segments := ["b", "ə", "l", "i"]
    source := [
      ⟨"pater-2001", "(37)"⟩
    ] }

def membeli : Form Cell :=
  { id := "pater2001_membeli"
    lexeme := Lexemes.membeli
    cell := {}
    form := "məmbəli"
    segments := ["m", "ə", "m", "b", "ə", "l", "i"]
    source := [
      ⟨"pater-2001", "(37)"⟩
    ] }

def besar : Form Cell :=
  { id := "pater2001_besar"
    lexeme := Lexemes.besar
    cell := {}
    form := "besar"
    segments := ["b", "ə", "s", "a", "r"]
    source := [
      ⟨"pater-2001", "(25a)"⟩
    ] }

def memperbesar : Form Cell :=
  { id := "pater2001_memperbesar"
    lexeme := Lexemes.memperbesar
    cell := {}
    form := "məmpərbesar"
    segments := ["m", "ə", "m", "p", "ə", "r", "b", "ə", "s", "a", "r"]
    source := [
      ⟨"pater-2001", "(25a)"⟩
    ] }

def baru : Form Cell :=
  { id := "pater2001_baru"
    lexeme := Lexemes.baru
    cell := {}
    form := "baru"
    segments := ["b", "a", "r", "u"]
    source := [
      ⟨"pater-2001", "(11a)"⟩
    ] }

def baru_irr : Form Cell :=
  { id := "pater2001_baru_irr"
    lexeme := Lexemes.baru_irr
    cell := {}
    form := "baru"
    segments := ["b", "a", "r", "u"]
    source := [
      ⟨"pater-2001", "(11a)"⟩
    ] }

def bala : Form Cell :=
  { id := "pater2001_bala"
    lexeme := Lexemes.bala
    cell := {}
    form := "ɓala"
    segments := ["ɓ", "a", "l", "a"]
    source := [
      ⟨"pater-2001", "(11b)"⟩
    ] }

def bala_irr : Form Cell :=
  { id := "pater2001_bala_irr"
    lexeme := Lexemes.bala_irr
    cell := {}
    form := "ɓala"
    segments := ["ɓ", "a", "l", "a"]
    source := [
      ⟨"pater-2001", "(11b)"⟩
    ] }

def pili : Form Cell :=
  { id := "pater2001_pili"
    lexeme := Lexemes.pili
    cell := {}
    form := "pili"
    segments := ["p", "i", "l", "i"]
    source := [
      ⟨"pater-2001", "(11c)"⟩
    ] }

def mili : Form Cell :=
  { id := "pater2001_mili"
    lexeme := Lexemes.mili
    cell := {}
    form := "mili"
    segments := ["m", "i", "l", "i"]
    source := [
      ⟨"pater-2001", "(11c)"⟩
    ] }

def futaa : Form Cell :=
  { id := "pater2001_futaa"
    lexeme := Lexemes.futaa
    cell := {}
    form := "futaa"
    segments := ["f", "u", "t", "a", "a"]
    source := [
      ⟨"pater-2001", "(11d)"⟩
    ] }

def mutaa : Form Cell :=
  { id := "pater2001_mutaa"
    lexeme := Lexemes.mutaa
    cell := {}
    form := "mutaa"
    segments := ["m", "u", "t", "a", "a"]
    source := [
      ⟨"pater-2001", "(11d)"⟩
    ] }

def waa : Form Cell :=
  { id := "pater2001_waa"
    lexeme := Lexemes.waa
    cell := {}
    form := "waa"
    segments := ["w", "a", "a"]
    source := [
      ⟨"pater-2001", "(11e)"⟩
    ] }

def maa : Form Cell :=
  { id := "pater2001_maa"
    lexeme := Lexemes.maa
    cell := {}
    form := "maa"
    segments := ["m", "a", "a"]
    source := [
      ⟨"pater-2001", "(11e)"⟩
    ] }

def wanu : Form Cell :=
  { id := "pater2001_wanu"
    lexeme := Lexemes.wanu
    cell := {}
    form := "wanu"
    segments := ["w", "a", "n", "u"]
    source := [
      ⟨"pater-2001", "(11f)"⟩
    ] }

def wanu_irr : Form Cell :=
  { id := "pater2001_wanu_irr"
    lexeme := Lexemes.wanu_irr
    cell := {}
    form := "wanu"
    segments := ["w", "a", "n", "u"]
    source := [
      ⟨"pater-2001", "(11f)"⟩
    ] }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.paksa, Lexemes.memaksa, Lexemes.buat, Lexemes.membuat,
  Lexemes.empat, Lexemes.pilih, Lexemes.memilih, Lexemes.beli, Lexemes.membeli, Lexemes.besar,
  Lexemes.memperbesar, Lexemes.baru, Lexemes.baru_irr, Lexemes.bala, Lexemes.bala_irr, Lexemes.pili,
  Lexemes.mili, Lexemes.futaa, Lexemes.mutaa, Lexemes.waa, Lexemes.maa, Lexemes.wanu,
  Lexemes.wanu_irr]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [paksa, memaksa, buat, membuat, empat, pilih, memilih, beli, membeli,
  besar, memperbesar, baru, baru_irr, bala, bala_irr, pili, mili, futaa, mutaa, waa, maa, wanu,
  wanu_irr]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := [
  { id := "pater2001_paksa_memaksa", form := paksa, target := memaksa, relation := "meN-",
    source := [
      ⟨"pater-2001", "(3)"⟩
    ] },
  { id := "pater2001_buat_membuat", form := buat, target := membuat, relation := "meN-", source := [
      ⟨"pater-2001", "(3)"⟩
    ] },
  { id := "pater2001_pilih_memilih", form := pilih, target := memilih, relation := "meN-",
    source := [
      ⟨"pater-2001", "(38)"⟩
    ] },
  { id := "pater2001_beli_membeli", form := beli, target := membeli, relation := "meN-", source := [
      ⟨"pater-2001", "(37)"⟩
    ] },
  { id := "pater2001_besar_memperbesar", form := besar, target := memperbesar,
    relation := "meN- per-", source := [
      ⟨"pater-2001", "(25a)"⟩
    ] },
  { id := "pater2001_baru_baru_irr", form := baru, target := baru_irr, relation := "-um-",
    source := [
      ⟨"pater-2001", "(11a)"⟩
    ] },
  { id := "pater2001_bala_bala_irr", form := bala, target := bala_irr, relation := "-um-",
    source := [
      ⟨"pater-2001", "(11b)"⟩
    ] },
  { id := "pater2001_pili_mili", form := pili, target := mili, relation := "-um-", source := [
      ⟨"pater-2001", "(11c)"⟩
    ] },
  { id := "pater2001_futaa_mutaa", form := futaa, target := mutaa, relation := "-um-", source := [
      ⟨"pater-2001", "(11d)"⟩
    ] },
  { id := "pater2001_waa_maa", form := waa, target := maa, relation := "-um-", source := [
      ⟨"pater-2001", "(11e)"⟩
    ] },
  { id := "pater2001_wanu_wanu_irr", form := wanu, target := wanu_irr, relation := "-um-",
    source := [
      ⟨"pater-2001", "(11f)"⟩
    ] }]

end Pater2001.Wordlist
