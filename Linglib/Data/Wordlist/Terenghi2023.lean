module

public import Linglib.Data.Wordlist.Schema

/-!
# `Terenghi2023`: word forms

Auto-generated from `Linglib/Data/Wordlist/Terenghi2023.json` by `scripts/gen_wordlist.py`. Do not
edit by hand; edit the JSON and re-run the generator. Declarations live in `namespace
Terenghi2023.Wordlist`.
-/

@[expose] public section

namespace Terenghi2023.Wordlist

open CLDF.Wordlist

/-- The values of `Term` the source distinguishes. -/
inductive Term where
  /-- The first term, speaker-related, `DEM.1` in the source. -/
  | dem1
  /-- The second term, hearer-related, `DEM.2` in the source. -/
  | dem2
  /-- The third term, `DEM.3` in the source. -/
  | dem3
  /-- The term of the area related to the discourse participants, `Local` in the source. -/
  | local
  /-- The term of the area not related to the discourse participants, `Non-local` in the source. -/
  | nonLocal
  deriving DecidableEq, Repr

/-- The values of `Subdivision` the source distinguishes. -/
inductive Subdivision where
  /-- The nearest degree of distance, `Nearest` in the source. -/
  | nearest
  /-- The nearer degree of distance, `Nearer` in the source. -/
  | nearer
  /-- The near degree of distance, `Near` in the source. -/
  | near
  /-- The term without a reinforcer, `Unmarked` in the source. -/
  | unmarked
  /-- Speaker-related, with the reinforcer aqui, `S-centred` in the source. -/
  | speakerCentred
  /-- Hearer-related, with the reinforcer aí, `A-centred` in the source. -/
  | addresseeCentred
  /-- Proximal, with the reinforcer ali, `Proximal` in the source. -/
  | proximal
  /-- Distal, with the reinforcer lá, `Distal` in the source. -/
  | distal
  /-- Contact with the participant, `+` in the source. -/
  | contact
  deriving DecidableEq, Repr

/-- A cell of the source's tables, by its Universal Dependencies features and the features UD
lacks. -/
structure Cell extends UD.MorphFeatures where
  /-- The `Term` feature. -/
  term : Flat Term := ⊥
  /-- The `Subdivision` feature. -/
  subdivision : Flat Subdivision := ⊥
  deriving DecidableEq, Repr

/-- The DEM.1, nearest cell, `PronType=Dem|Term=DEM.1|Subdivision=Nearest`. -/
def dem1_nearest : Cell :=
  { pronType := ↑UD.PronType.Dem, term := ↑Term.dem1, subdivision := ↑Subdivision.nearest }

/-- The DEM.2, nearest cell, `PronType=Dem|Term=DEM.2|Subdivision=Nearest`. -/
def dem2_nearest : Cell :=
  { pronType := ↑UD.PronType.Dem, term := ↑Term.dem2, subdivision := ↑Subdivision.nearest }

/-- The DEM.3, nearest cell, `PronType=Dem|Term=DEM.3|Subdivision=Nearest`. -/
def dem3_nearest : Cell :=
  { pronType := ↑UD.PronType.Dem, term := ↑Term.dem3, subdivision := ↑Subdivision.nearest }

/-- The DEM.1, nearer cell, `PronType=Dem|Term=DEM.1|Subdivision=Nearer`. -/
def dem1_nearer : Cell :=
  { pronType := ↑UD.PronType.Dem, term := ↑Term.dem1, subdivision := ↑Subdivision.nearer }

/-- The DEM.2, nearer cell, `PronType=Dem|Term=DEM.2|Subdivision=Nearer`. -/
def dem2_nearer : Cell :=
  { pronType := ↑UD.PronType.Dem, term := ↑Term.dem2, subdivision := ↑Subdivision.nearer }

/-- The DEM.3, nearer cell, `PronType=Dem|Term=DEM.3|Subdivision=Nearer`. -/
def dem3_nearer : Cell :=
  { pronType := ↑UD.PronType.Dem, term := ↑Term.dem3, subdivision := ↑Subdivision.nearer }

/-- The DEM.1, near cell, `PronType=Dem|Term=DEM.1|Subdivision=Near`. -/
def dem1_near : Cell :=
  { pronType := ↑UD.PronType.Dem, term := ↑Term.dem1, subdivision := ↑Subdivision.near }

/-- The DEM.2, near cell, `PronType=Dem|Term=DEM.2|Subdivision=Near`. -/
def dem2_near : Cell :=
  { pronType := ↑UD.PronType.Dem, term := ↑Term.dem2, subdivision := ↑Subdivision.near }

/-- The DEM.3, near cell, `PronType=Dem|Term=DEM.3|Subdivision=Near`. -/
def dem3_near : Cell :=
  { pronType := ↑UD.PronType.Dem, term := ↑Term.dem3, subdivision := ↑Subdivision.near }

/-- The Local, Unmarked cell, `PronType=Dem|Term=Local|Subdivision=Unmarked`. -/
def local_unmarked : Cell :=
  { pronType := ↑UD.PronType.Dem, term := ↑Term.local, subdivision := ↑Subdivision.unmarked }

/-- The Local, S-centred cell, `PronType=Dem|Term=Local|Subdivision=S-centred`. -/
def local_speakerCentred : Cell :=
  { pronType := ↑UD.PronType.Dem, term := ↑Term.local, subdivision := ↑Subdivision.speakerCentred }

/-- The Local, A-centred cell, `PronType=Dem|Term=Local|Subdivision=A-centred`. -/
def local_addresseeCentred : Cell :=
  { pronType := ↑UD.PronType.Dem, term := ↑Term.local,
    subdivision := ↑Subdivision.addresseeCentred }

/-- The Non-local, Unmarked cell, `PronType=Dem|Term=Non-local|Subdivision=Unmarked`. -/
def nonLocal_unmarked : Cell :=
  { pronType := ↑UD.PronType.Dem, term := ↑Term.nonLocal, subdivision := ↑Subdivision.unmarked }

/-- The Non-local, Proximal cell, `PronType=Dem|Term=Non-local|Subdivision=Proximal`. -/
def nonLocal_proximal : Cell :=
  { pronType := ↑UD.PronType.Dem, term := ↑Term.nonLocal, subdivision := ↑Subdivision.proximal }

/-- The Non-local, Distal cell, `PronType=Dem|Term=Non-local|Subdivision=Distal`. -/
def nonLocal_distal : Cell :=
  { pronType := ↑UD.PronType.Dem, term := ↑Term.nonLocal, subdivision := ↑Subdivision.distal }

/-- The DEM.1+ cell, `PronType=Dem|Term=DEM.1|Subdivision=+`. -/
def dem1_contact : Cell :=
  { pronType := ↑UD.PronType.Dem, term := ↑Term.dem1, subdivision := ↑Subdivision.contact }

/-- The DEM.1 cell, `PronType=Dem|Term=DEM.1`. -/
def dem1 : Cell := { pronType := ↑UD.PronType.Dem, term := ↑Term.dem1 }

/-- The DEM.2+ cell, `PronType=Dem|Term=DEM.2|Subdivision=+`. -/
def dem2_contact : Cell :=
  { pronType := ↑UD.PronType.Dem, term := ↑Term.dem2, subdivision := ↑Subdivision.contact }

/-- The DEM.2 cell, `PronType=Dem|Term=DEM.2`. -/
def dem2 : Cell := { pronType := ↑UD.PronType.Dem, term := ↑Term.dem2 }

/-- The DEM.3 cell, `PronType=Dem|Term=DEM.3`. -/
def dem3 : Cell := { pronType := ↑UD.PronType.Dem, term := ↑Term.dem3 }

def Lexemes.dem_mundari : Lexeme :=
  { id := "dem_mundari", languageId := "mund1320", parameterId := "demonstrative", label := "ni" }

def Lexemes.dem_portuguese : Lexeme :=
  { id := "dem_portuguese", languageId := "braz1246", parameterId := "demonstrative",
    label := "esse" }

def Lexemes.dem_satawal : Lexeme :=
  { id := "dem_satawal", languageId := "sata1237", parameterId := "demonstrative",
    label := "minne" }

def mundari_ni : Form Cell :=
  { id := "terenghi2023_mundari_ni"
    lexeme := Lexemes.dem_mundari
    cell := dem1_nearest
    form := "ni"
    source := [
      ⟨"terenghi-2023", "(19)"⟩
    ] }

def mundari_in : Form Cell :=
  { id := "terenghi2023_mundari_in"
    lexeme := Lexemes.dem_mundari
    cell := dem2_nearest
    form := "in"
    source := [
      ⟨"terenghi-2023", "(19)"⟩
    ] }

def mundari_hin : Form Cell :=
  { id := "terenghi2023_mundari_hin"
    lexeme := Lexemes.dem_mundari
    cell := dem3_nearest
    form := "hin"
    source := [
      ⟨"terenghi-2023", "(19)"⟩
    ] }

def mundari_ne : Form Cell :=
  { id := "terenghi2023_mundari_ne"
    lexeme := Lexemes.dem_mundari
    cell := dem1_nearer
    form := "ne"
    source := [
      ⟨"terenghi-2023", "(19)"⟩
    ] }

def mundari_en : Form Cell :=
  { id := "terenghi2023_mundari_en"
    lexeme := Lexemes.dem_mundari
    cell := dem2_nearer
    form := "en"
    source := [
      ⟨"terenghi-2023", "(19)"⟩
    ] }

def mundari_hen : Form Cell :=
  { id := "terenghi2023_mundari_hen"
    lexeme := Lexemes.dem_mundari
    cell := dem3_nearer
    form := "hen"
    source := [
      ⟨"terenghi-2023", "(19)"⟩
    ] }

def mundari_na : Form Cell :=
  { id := "terenghi2023_mundari_na"
    lexeme := Lexemes.dem_mundari
    cell := dem1_near
    form := "na"
    source := [
      ⟨"terenghi-2023", "(19)"⟩
    ] }

def mundari_an : Form Cell :=
  { id := "terenghi2023_mundari_an"
    lexeme := Lexemes.dem_mundari
    cell := dem2_near
    form := "an"
    source := [
      ⟨"terenghi-2023", "(19)"⟩
    ] }

def mundari_han : Form Cell :=
  { id := "terenghi2023_mundari_han"
    lexeme := Lexemes.dem_mundari
    cell := dem3_near
    form := "han"
    source := [
      ⟨"terenghi-2023", "(19)"⟩
    ] }

def portuguese_esse : Form Cell :=
  { id := "terenghi2023_portuguese_esse"
    lexeme := Lexemes.dem_portuguese
    cell := local_unmarked
    form := "esse"
    source := [
      ⟨"terenghi-2023", "(3)"⟩
    ] }

def portuguese_esse_aqui : Form Cell :=
  { id := "terenghi2023_portuguese_esse_aqui"
    lexeme := Lexemes.dem_portuguese
    cell := local_speakerCentred
    form := "esse aqui"
    source := [
      ⟨"terenghi-2023", "(3)"⟩
    ] }

def portuguese_esse_ai : Form Cell :=
  { id := "terenghi2023_portuguese_esse_ai"
    lexeme := Lexemes.dem_portuguese
    cell := local_addresseeCentred
    form := "esse aí"
    source := [
      ⟨"terenghi-2023", "(3)"⟩
    ] }

def portuguese_aquele : Form Cell :=
  { id := "terenghi2023_portuguese_aquele"
    lexeme := Lexemes.dem_portuguese
    cell := nonLocal_unmarked
    form := "aquele"
    source := [
      ⟨"terenghi-2023", "(3)"⟩
    ] }

def portuguese_aquele_ali : Form Cell :=
  { id := "terenghi2023_portuguese_aquele_ali"
    lexeme := Lexemes.dem_portuguese
    cell := nonLocal_proximal
    form := "aquele ali"
    source := [
      ⟨"terenghi-2023", "(3)"⟩
    ] }

def portuguese_aquele_la : Form Cell :=
  { id := "terenghi2023_portuguese_aquele_la"
    lexeme := Lexemes.dem_portuguese
    cell := nonLocal_distal
    form := "aquele lá"
    source := [
      ⟨"terenghi-2023", "(3)"⟩
    ] }

def satawal_minne : Form Cell :=
  { id := "terenghi2023_satawal_minne"
    lexeme := Lexemes.dem_satawal
    cell := dem1_contact
    form := "minne"
    source := [
      ⟨"terenghi-2023", "(7)"⟩
    ] }

def satawal_minnen : Form Cell :=
  { id := "terenghi2023_satawal_minnen"
    lexeme := Lexemes.dem_satawal
    cell := dem1
    form := "minnen"
    source := [
      ⟨"terenghi-2023", "(7)"⟩
    ] }

def satawal_minna : Form Cell :=
  { id := "terenghi2023_satawal_minna"
    lexeme := Lexemes.dem_satawal
    cell := dem2_contact
    form := "minna"
    source := [
      ⟨"terenghi-2023", "(7)"⟩
    ] }

def satawal_minimu : Form Cell :=
  { id := "terenghi2023_satawal_minimu"
    lexeme := Lexemes.dem_satawal
    cell := dem2
    form := "minimu"
    source := [
      ⟨"terenghi-2023", "(7)"⟩
    ] }

def satawal_minnan : Form Cell :=
  { id := "terenghi2023_satawal_minnan"
    lexeme := Lexemes.dem_satawal
    cell := dem3
    form := "minnan"
    source := [
      ⟨"terenghi-2023", "(7)"⟩
    ] }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.dem_mundari, Lexemes.dem_portuguese, Lexemes.dem_satawal]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [mundari_ni, mundari_in, mundari_hin, mundari_ne, mundari_en,
  mundari_hen, mundari_na, mundari_an, mundari_han, portuguese_esse, portuguese_esse_aqui,
  portuguese_esse_ai, portuguese_aquele, portuguese_aquele_ali, portuguese_aquele_la, satawal_minne,
  satawal_minnen, satawal_minna, satawal_minimu, satawal_minnan]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := []

end Terenghi2023.Wordlist
