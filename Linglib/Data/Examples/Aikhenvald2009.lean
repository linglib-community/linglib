module

public import Linglib.Data.Examples.Schema
public import Mathlib.Tactic.DeriveFintype

/-!
# `Aikhenvald2009` — typed example data

Auto-generated from `Linglib/Data/Examples/Aikhenvald2009.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Aikhenvald2009.Examples`.
-/

@[expose] public section

namespace Aikhenvald2009.Examples

def ex10 : Datum :=
  { id := "aikhenvald2009_ex10"
    source := ⟨"aikhenvald-2009", "(10)"⟩
    reportedIn := none
    language := "mana1298"
    primaryText := "ata wukǝ-ku gra-dian"
    glossedTokens := [("ata", "then"), ("wukǝ-ku", "worry-COMPL.SS"), ("gra-dian", "cry-1plBAS.PAST")]
    glossedWords := [⟨['a', 't', 'a'], ['t', 'h', 'e', 'n'], [⟨['a', 't', 'a'], ['t', 'h', 'e', 'n'], none⟩]⟩, ⟨['w', 'u', 'k', 'ǝ', '-', 'k', 'u'], ['w', 'o', 'r', 'r', 'y', '-', 'C', 'O', 'M', 'P', 'L', '.', 'S', 'S'], [⟨['w', 'u', 'k', 'ǝ'], ['w', 'o', 'r', 'r', 'y'], none⟩, ⟨['k', 'u'], ['C', 'O', 'M', 'P', 'L', '.', 'S', 'S'], some '-'⟩]⟩, ⟨['g', 'r', 'a', '-', 'd', 'i', 'a', 'n'], ['c', 'r', 'y', '-', '1', 'p', 'l', 'B', 'A', 'S', '.', 'P', 'A', 'S', 'T'], [⟨['g', 'r', 'a'], ['c', 'r', 'y'], none⟩, ⟨['d', 'i', 'a', 'n'], ['1', 'p', 'l', 'B', 'A', 'S', '.', 'P', 'A', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("after", .acceptable), ("because", .acceptable)]
    paperFeatures := [] }

def ex11 : Datum :=
  { id := "aikhenvald2009_ex11"
    source := ⟨"aikhenvald-2009", "(11)"⟩
    reportedIn := none
    language := "mana1298"
    primaryText := "amæywa nǝbi-ar vya-tuǝ-k kiya-k-na"
    glossedTokens := [("amæywa", "bow+COMIT"), ("nǝbi-ar", "arrow-LINK+INST"), ("vya-tuǝ-k", "hit-1sg-COMPL:DS"), ("kiya-k-na", "die-FUT-ACT.FOC+3fem.sgBAS.NPAST")]
    glossedWords := [⟨['a', 'm', 'æ', 'y', 'w', 'a'], ['b', 'o', 'w', '+', 'C', 'O', 'M', 'I', 'T'], [⟨['a', 'm', 'æ', 'y', 'w', 'a'], ['b', 'o', 'w', '+', 'C', 'O', 'M', 'I', 'T'], none⟩]⟩, ⟨['n', 'ǝ', 'b', 'i', '-', 'a', 'r'], ['a', 'r', 'r', 'o', 'w', '-', 'L', 'I', 'N', 'K', '+', 'I', 'N', 'S', 'T'], [⟨['n', 'ǝ', 'b', 'i'], ['a', 'r', 'r', 'o', 'w'], none⟩, ⟨['a', 'r'], ['L', 'I', 'N', 'K', '+', 'I', 'N', 'S', 'T'], some '-'⟩]⟩, ⟨['v', 'y', 'a', '-', 't', 'u', 'ǝ', '-', 'k'], ['h', 'i', 't', '-', '1', 's', 'g', '-', 'C', 'O', 'M', 'P', 'L', ':', 'D', 'S'], [⟨['v', 'y', 'a'], ['h', 'i', 't'], none⟩, ⟨['t', 'u', 'ǝ'], ['1', 's', 'g'], some '-'⟩, ⟨['k'], ['C', 'O', 'M', 'P', 'L', ':', 'D', 'S'], some '-'⟩]⟩, ⟨['k', 'i', 'y', 'a', '-', 'k', '-', 'n', 'a'], ['d', 'i', 'e', '-', 'F', 'U', 'T', '-', 'A', 'C', 'T', '.', 'F', 'O', 'C', '+', '3', 'f', 'e', 'm', '.', 's', 'g', 'B', 'A', 'S', '.', 'N', 'P', 'A', 'S', 'T'], [⟨['k', 'i', 'y', 'a'], ['d', 'i', 'e'], none⟩, ⟨['k'], ['F', 'U', 'T'], some '-'⟩, ⟨['n', 'a'], ['A', 'C', 'T', '.', 'F', 'O', 'C', '+', '3', 'f', 'e', 'm', '.', 's', 'g', 'B', 'A', 'S', '.', 'N', 'P', 'A', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("after", .acceptable), ("because", .acceptable), ("if", .acceptable)]
    paperFeatures := [] }

def ex12 : Datum :=
  { id := "aikhenvald2009_ex12"
    source := ⟨"aikhenvald-2009", "(12)"⟩
    reportedIn := none
    language := "mana1298"
    primaryText := "ata wukǝ-n napa-ku gra-dian"
    glossedTokens := [("ata", "then"), ("wukǝ-n", "worry-SIM"), ("napa-ku", "COMPL.VB-COMPL.SS"), ("gra-dian", "cry-1plBAS.PAST")]
    glossedWords := [⟨['a', 't', 'a'], ['t', 'h', 'e', 'n'], [⟨['a', 't', 'a'], ['t', 'h', 'e', 'n'], none⟩]⟩, ⟨['w', 'u', 'k', 'ǝ', '-', 'n'], ['w', 'o', 'r', 'r', 'y', '-', 'S', 'I', 'M'], [⟨['w', 'u', 'k', 'ǝ'], ['w', 'o', 'r', 'r', 'y'], none⟩, ⟨['n'], ['S', 'I', 'M'], some '-'⟩]⟩, ⟨['n', 'a', 'p', 'a', '-', 'k', 'u'], ['C', 'O', 'M', 'P', 'L', '.', 'V', 'B', '-', 'C', 'O', 'M', 'P', 'L', '.', 'S', 'S'], [⟨['n', 'a', 'p', 'a'], ['C', 'O', 'M', 'P', 'L', '.', 'V', 'B'], none⟩, ⟨['k', 'u'], ['C', 'O', 'M', 'P', 'L', '.', 'S', 'S'], some '-'⟩]⟩, ⟨['g', 'r', 'a', '-', 'd', 'i', 'a', 'n'], ['c', 'r', 'y', '-', '1', 'p', 'l', 'B', 'A', 'S', '.', 'P', 'A', 'S', 'T'], [⟨['g', 'r', 'a'], ['c', 'r', 'y'], none⟩, ⟨['d', 'i', 'a', 'n'], ['1', 'p', 'l', 'B', 'A', 'S', '.', 'P', 'A', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("after", .acceptable), ("because", .unacceptable)]
    paperFeatures := [] }

def all : List Datum := [ex10, ex11, ex12]

/-- The readings the chapter gives a completive medial clause. -/
inductive Reading where
  /-- after: relative time, the medial event over before the next -/
  | after
  /-- because: cause -/
  | because
  /-- if: real condition -/
  | condition
  deriving DecidableEq, Repr, Fintype

/-- The name the rows give the reading. -/
def Reading.label : Reading → String
  | .after => "after"
  | .because => "because"
  | .condition => "if"

/-- The judgment a row records for the reading, if it records one. -/
def reading (e : Datum) (r : Reading) : Option Judgment :=
  e.readings.lookup r.label

end Aikhenvald2009.Examples
