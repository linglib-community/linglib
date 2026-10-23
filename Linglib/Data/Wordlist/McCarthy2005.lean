module

public import Linglib.Data.Wordlist.Schema

/-!
# `McCarthy2005`: word forms

Auto-generated from `Linglib/Data/Wordlist/McCarthy2005.json` by `scripts/gen_wordlist.py`. Do not
edit by hand; edit the JSON and re-run the generator. Declarations live in `namespace
McCarthy2005.Wordlist`.
-/

@[expose] public section

namespace McCarthy2005.Wordlist

open CLDF.Wordlist

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

/-- The singular cell, `Number=Sing`. -/
def sg : Cell := { number := ↑UD.Number.Sing }

def Lexemes.dog : Lexeme :=
  { id := "dog", languageId := "moro1292", parameterId := "dog", pos := ↑UD.UPOS.NOUN }

def Lexemes.wind : Lexeme :=
  { id := "wind", languageId := "moro1292", parameterId := "wind", pos := ↑UD.UPOS.NOUN }

def Lexemes.sin : Lexeme :=
  { id := "sin", languageId := "moro1292", parameterId := "sin", pos := ↑UD.UPOS.NOUN }

def Lexemes.sun : Lexeme :=
  { id := "sun", languageId := "moro1292", parameterId := "sun", pos := ↑UD.UPOS.NOUN }

def Lexemes.game : Lexeme :=
  { id := "game", languageId := "moro1292", parameterId := "game", pos := ↑UD.UPOS.NOUN }

def Lexemes.brain : Lexeme :=
  { id := "brain", languageId := "moro1292", parameterId := "brain", pos := ↑UD.UPOS.NOUN }

def Lexemes.leg : Lexeme :=
  { id := "leg", languageId := "moro1292", parameterId := "leg", pos := ↑UD.UPOS.NOUN }

def Lexemes.shoulder : Lexeme :=
  { id := "shoulder", languageId := "moro1292", parameterId := "shoulder", pos := ↑UD.UPOS.NOUN }

def Lexemes.rope : Lexeme :=
  { id := "rope", languageId := "moro1292", parameterId := "rope", pos := ↑UD.UPOS.NOUN }

def Lexemes.mule : Lexeme :=
  { id := "mule", languageId := "moro1292", parameterId := "mule", pos := ↑UD.UPOS.NOUN }

def Lexemes.peg : Lexeme :=
  { id := "peg", languageId := "moro1292", parameterId := "peg", pos := ↑UD.UPOS.NOUN }

def Lexemes.shroud : Lexeme :=
  { id := "shroud", languageId := "moro1292", parameterId := "shroud", pos := ↑UD.UPOS.NOUN }

def dog_sg : Form Cell :=
  { id := "mccarthy2005_dog_sg"
    lexeme := Lexemes.dog
    cell := sg
    form := "kəlb"
    segments := ["k", "ə", "l", "b"]
    source := [
      ⟨"mccarthy-2005", "p. 202"⟩
    ] }

def wind_sg : Form Cell :=
  { id := "mccarthy2005_wind_sg"
    lexeme := Lexemes.wind
    cell := sg
    form := "bərd"
    segments := ["b", "ə", "r", "d"]
    source := [
      ⟨"mccarthy-2005", "p. 202"⟩
    ] }

def sin_sg : Form Cell :=
  { id := "mccarthy2005_sin_sg"
    lexeme := Lexemes.sin
    cell := sg
    form := "dənb"
    segments := ["d", "ə", "n", "b"]
    source := [
      ⟨"mccarthy-2005", "p. 202"⟩
    ] }

def sun_sg : Form Cell :=
  { id := "mccarthy2005_sun_sg"
    lexeme := Lexemes.sun
    cell := sg
    form := "ʃəmʃ"
    segments := ["ʃ", "ə", "m", "ʃ"]
    source := [
      ⟨"mccarthy-2005", "p. 202"⟩
    ] }

def game_sg : Form Cell :=
  { id := "mccarthy2005_game_sg"
    lexeme := Lexemes.game
    cell := sg
    form := "ləʕb"
    segments := ["l", "ə", "ʕ", "b"]
    source := [
      ⟨"mccarthy-2005", "p. 202"⟩
    ] }

def brain_sg : Form Cell :=
  { id := "mccarthy2005_brain_sg"
    lexeme := Lexemes.brain
    cell := sg
    form := "mʷəxx"
    segments := ["mʷ", "ə", "x", "x"]
    source := [
      ⟨"mccarthy-2005", "p. 202"⟩
    ] }

def leg_sg : Form Cell :=
  { id := "mccarthy2005_leg_sg"
    lexeme := Lexemes.leg
    cell := sg
    form := "rʒəl"
    segments := ["r", "ʒ", "ə", "l"]
    source := [
      ⟨"mccarthy-2005", "p. 202"⟩
    ] }

def shoulder_sg : Form Cell :=
  { id := "mccarthy2005_shoulder_sg"
    lexeme := Lexemes.shoulder
    cell := sg
    form := "ktəf"
    segments := ["k", "t", "ə", "f"]
    source := [
      ⟨"mccarthy-2005", "p. 202"⟩
    ] }

def rope_sg : Form Cell :=
  { id := "mccarthy2005_rope_sg"
    lexeme := Lexemes.rope
    cell := sg
    form := "ħbəl"
    segments := ["ħ", "b", "ə", "l"]
    source := [
      ⟨"mccarthy-2005", "p. 202"⟩
    ] }

def mule_sg : Form Cell :=
  { id := "mccarthy2005_mule_sg"
    lexeme := Lexemes.mule
    cell := sg
    form := "bɣəl"
    segments := ["b", "ɣ", "ə", "l"]
    source := [
      ⟨"mccarthy-2005", "p. 203"⟩
    ] }

def peg_sg : Form Cell :=
  { id := "mccarthy2005_peg_sg"
    lexeme := Lexemes.peg
    cell := sg
    form := "wtəd"
    segments := ["w", "t", "ə", "d"]
    source := [
      ⟨"mccarthy-2005", "p. 203"⟩
    ] }

def shroud_sg : Form Cell :=
  { id := "mccarthy2005_shroud_sg"
    lexeme := Lexemes.shroud
    cell := sg
    form := "kfən"
    segments := ["k", "f", "ə", "n"]
    source := [
      ⟨"mccarthy-2005", "p. 203"⟩
    ] }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.dog, Lexemes.wind, Lexemes.sin, Lexemes.sun, Lexemes.game,
  Lexemes.brain, Lexemes.leg, Lexemes.shoulder, Lexemes.rope, Lexemes.mule, Lexemes.peg,
  Lexemes.shroud]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [dog_sg, wind_sg, sin_sg, sun_sg, game_sg, brain_sg, leg_sg,
  shoulder_sg, rope_sg, mule_sg, peg_sg, shroud_sg]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := []

end McCarthy2005.Wordlist
