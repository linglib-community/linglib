module

public import Linglib.Data.Forms.Schema

/-!
# `Steriade1997`: word forms

Auto-generated from `Linglib/Data/Forms/Steriade1997.json` by `scripts/gen_forms.py`. Do not edit by
hand; edit the JSON and re-run the generator. Declarations live in `namespace Steriade1997.Forms`.
-/

@[expose] public section

namespace Steriade1997.Forms

open Data.Forms

/-- The values of `Sandhi` the source distinguishes. -/
inductive Sandhi where
  /-- The form a prenominal adjective takes before a vowel-initial noun (2), `liaison` in the
  source. -/
  | liaison
  deriving DecidableEq, Repr

/-- The values of `Category` the source distinguishes. -/
inductive Category where
  /-- The lexical category of a stem occurring in a verb ((17), p. 16), `verb` in the source. -/
  | verb
  /-- The lexical category of a stem occurring in an adjective ((17)), `adjective` in the source. -/
  | adjective
  deriving DecidableEq, Repr

/-- A cell of the source's tables, by its Universal Dependencies features and the features UD
lacks. -/
structure Cell extends UD.MorphFeatures where
  /-- The `Sandhi` feature. -/
  sandhi : Flat Sandhi := ⊥
  /-- The `Category` feature. -/
  category : Flat Category := ⊥
  deriving DecidableEq, Repr

/-- The masculine cell, `Gender=Masc`. -/
def masc : Cell := { gender := ↑UD.Gender.Masc }

/-- The feminine cell, `Gender=Fem`. -/
def fem : Cell := { gender := ↑UD.Gender.Fem }

/-- The masculine liaison cell, `Gender=Masc|Sandhi=liaison`. -/
def masc_liaison : Cell := { gender := ↑UD.Gender.Masc, sandhi := ↑Sandhi.liaison }

/-- The verbal stem cell, `Category=verb`. -/
def verb : Cell := { category := ↑Category.verb }

/-- The adjectival stem cell, `Category=adjective`. -/
def adj : Cell := { category := ↑Category.adjective }

def Lexemes.vain : Lexeme :=
  { id := "vain", languageId := "stan1290", parameterId := "vain", label := "vain",
    pos := ↑UD.UPOS.ADJ }

def Lexemes.joli : Lexeme :=
  { id := "joli", languageId := "stan1290", parameterId := "pretty", label := "joli",
    pos := ↑UD.UPOS.ADJ }

def Lexemes.remedy : Lexeme :=
  { id := "remedy", languageId := "stan1293", parameterId := "remedy", label := "remedy",
    pos := ↑UD.UPOS.VERB }

def Lexemes.parody : Lexeme :=
  { id := "parody", languageId := "stan1293", parameterId := "parody", label := "parody",
    pos := ↑UD.UPOS.VERB }

def Lexemes.remediable : Lexeme :=
  { id := "remediable", languageId := "stan1293", parameterId := "remediable",
    label := "remediable", pos := ↑UD.UPOS.ADJ }

def Lexemes.parodiable : Lexeme :=
  { id := "parodiable", languageId := "stan1293", parameterId := "parodiable",
    label := "parodiable", pos := ↑UD.UPOS.ADJ }

def vain_masc : Form Cell :=
  { id := "steriade1997_vain_masc"
    lexeme := Lexemes.vain
    cell := masc
    form := "vɛ̃"
    segments := ["v", "ɛ̃"]
    source := [
      ⟨"steriade-1997", "(3b)"⟩,
      ⟨"steriade-1997", "(8b)"⟩
    ] }

def vain_fem : Form Cell :=
  { id := "steriade1997_vain_fem"
    lexeme := Lexemes.vain
    cell := fem
    form := "vɛn"
    segments := ["v", "ɛ", "n"]
    source := [
      ⟨"steriade-1997", "(3b)"⟩,
      ⟨"steriade-1997", "(8b)"⟩
    ] }

def vain_espoir : Form Cell :=
  { id := "steriade1997_vain_espoir"
    lexeme := Lexemes.vain
    cell := masc_liaison
    form := "vɛ̃n ɛspwaʁ"
    segments := ["v", "ɛ̃", "n", "_", "ɛ", "s", "p", "w", "a", "ʁ"]
    source := [
      ⟨"steriade-1997", "(3b)"⟩,
      ⟨"steriade-1997", "(8b)"⟩,
      ⟨"steriade-1997", "(10)"⟩
    ] }

def vain_espoir_fem : Form Cell :=
  { id := "steriade1997_vain_espoir_fem"
    lexeme := Lexemes.vain
    cell := masc_liaison
    form := "vɛn ɛspwaʁ"
    segments := ["v", "ɛ", "n", "_", "ɛ", "s", "p", "w", "a", "ʁ"]
    source := [
      ⟨"steriade-1997", "(8b)"⟩,
      ⟨"steriade-1997", "(10)"⟩
    ] }

def joli_masc : Form Cell :=
  { id := "steriade1997_joli_masc"
    lexeme := Lexemes.joli
    cell := masc
    form := "ʒoli"
    segments := ["ʒ", "o", "l", "i"]
    source := [
      ⟨"steriade-1997", "(8a)"⟩
    ] }

def joli_fem : Form Cell :=
  { id := "steriade1997_joli_fem"
    lexeme := Lexemes.joli
    cell := fem
    form := "ʒoli"
    segments := ["ʒ", "o", "l", "i"]
    source := [
      ⟨"steriade-1997", "(8a)"⟩
    ] }

def joli_enfant : Form Cell :=
  { id := "steriade1997_joli_enfant"
    lexeme := Lexemes.joli
    cell := masc_liaison
    form := "ʒoli ɑ̃fɑ̃"
    segments := ["ʒ", "o", "l", "i", "_", "ɑ̃", "f", "ɑ̃"]
    source := [
      ⟨"steriade-1997", "(8a)"⟩
    ] }

def jolit_enfant : Form Cell :=
  { id := "steriade1997_jolit_enfant"
    lexeme := Lexemes.joli
    cell := masc_liaison
    form := "ʒolit ɑ̃fɑ̃"
    segments := ["ʒ", "o", "l", "i", "t", "_", "ɑ̃", "f", "ɑ̃"]
    judgment := .ungrammatical
    source := [
      ⟨"steriade-1997", "(8a)"⟩
    ] }

def remedy : Form Cell :=
  { id := "steriade1997_remedy"
    lexeme := Lexemes.remedy
    cell := verb
    form := "rɛ́məɾi"
    segments := ["r", "ɛ́", "m", "ə", "ɾ", "i"]
    source := [
      ⟨"steriade-1997", "(13)"⟩
    ] }

def remedial_stem : Form Cell :=
  { id := "steriade1997_remedial_stem"
    lexeme := Lexemes.remedy
    cell := adj
    form := "rəmídi-"
    segments := ["r", "ə", "m", "í", "d", "i"]
    source := [
      ⟨"steriade-1997", "(13)"⟩
    ] }

def parody : Form Cell :=
  { id := "steriade1997_parody"
    lexeme := Lexemes.parody
    cell := verb
    form := "pǽrəɾi"
    segments := ["p", "ǽ", "r", "ə", "ɾ", "i"]
    source := [
      ⟨"steriade-1997", "(13)"⟩
    ] }

def remediable : Form Cell :=
  { id := "steriade1997_remediable"
    lexeme := Lexemes.remediable
    cell := {}
    form := "rəmídiəbl̩"
    segments := ["r", "ə", "m", "í", "d", "i", "+", "ə", "b", "l̩"]
    morphs := ["rəmídi", "əbl̩"]
    source := [
      ⟨"steriade-1997", "(14)"⟩
    ] }

def parodiable : Form Cell :=
  { id := "steriade1997_parodiable"
    lexeme := Lexemes.parodiable
    cell := {}
    form := "pəródiəbl̩"
    segments := ["p", "ə", "r", "ó", "d", "i", "+", "ə", "b", "l̩"]
    morphs := ["pəródi", "əbl̩"]
    judgment := .ungrammatical
    source := [
      ⟨"steriade-1997", "(14)"⟩,
      ⟨"steriade-1997", "(16b)"⟩
    ] }

def vain_listed.paradigm : Paradigm Cell :=
  { id := "vain_listed", lexeme := Lexemes.vain,
    forms := [vain_masc, vain_fem],
    source := [
      ⟨"steriade-1997", "(8b)"⟩,
      ⟨"steriade-1997", "(10)"⟩
    ] }

def joli_listed.paradigm : Paradigm Cell :=
  { id := "joli_listed", lexeme := Lexemes.joli,
    forms := [joli_masc, joli_fem],
    source := [
      ⟨"steriade-1997", "(8a)"⟩
    ] }

def remedy_listed.paradigm : Paradigm Cell :=
  { id := "remedy_listed", lexeme := Lexemes.remedy,
    forms := [remedy, remedial_stem],
    source := [
      ⟨"steriade-1997", "(13)"⟩,
      ⟨"steriade-1997", "(16a)"⟩,
      ⟨"steriade-1997", "(17)"⟩
    ] }

def parody_listed.paradigm : Paradigm Cell :=
  { id := "parody_listed", lexeme := Lexemes.parody,
    forms := [parody],
    source := [
      ⟨"steriade-1997", "(13)"⟩,
      ⟨"steriade-1997", "(16b)"⟩
    ] }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.vain, Lexemes.joli, Lexemes.remedy, Lexemes.parody,
  Lexemes.remediable, Lexemes.parodiable]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [vain_masc, vain_fem, vain_espoir, vain_espoir_fem, joli_masc,
  joli_fem, joli_enfant, remedy, remedial_stem, parody, remediable]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := [jolit_enfant, parodiable]

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := [
  { id := "remedy_remediable", form := remedy, target := remediable, relation := "able", source := [
      ⟨"steriade-1997", "(14)"⟩
    ] },
  { id := "parody_parodiable", form := parody, target := parodiable, relation := "able", source := [
      ⟨"steriade-1997", "(14)"⟩,
      ⟨"steriade-1997", "(16b)"⟩
    ] }]

/-- Every paradigm of the data. -/
def paradigms : List (Paradigm Cell) := [vain_listed.paradigm, joli_listed.paradigm,
  remedy_listed.paradigm, parody_listed.paradigm]

end Steriade1997.Forms
