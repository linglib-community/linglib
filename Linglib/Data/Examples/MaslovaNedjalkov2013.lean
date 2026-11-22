module

public import Linglib.Data.Examples.Schema
public import Mathlib.Tactic.DeriveFintype

/-!
# `MaslovaNedjalkov2013` — typed example data

Auto-generated from `Linglib/Data/Examples/MaslovaNedjalkov2013.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace MaslovaNedjalkov2013.Examples`.
-/

@[expose] public section

namespace MaslovaNedjalkov2013.Examples

def ex_1 : Datum :=
  { id := "maslovanedjalkov2013_1"
    source := ⟨"maslova-nedjalkov-2013", "(1)"⟩
    reportedIn := none
    method := some .description
    language := "cant1236"
    primaryText := "Ngóh béi-min kéuih kéuih béi-min ngóh."
    glossedTokens := [("Ngóh", "I"), ("béi-min", "give-face"), ("kéuih", "him"), ("kéuih", "he"), ("béi-min", "give-face"), ("ngóh.", "me")]
    glossedWords := [⟨['N', 'g', 'ó', 'h'], ['I'], [⟨['N', 'g', 'ó', 'h'], ['I'], none⟩]⟩, ⟨['b', 'é', 'i', '-', 'm', 'i', 'n'], ['g', 'i', 'v', 'e', '-', 'f', 'a', 'c', 'e'], [⟨['b', 'é', 'i'], ['g', 'i', 'v', 'e'], none⟩, ⟨['m', 'i', 'n'], ['f', 'a', 'c', 'e'], some '-'⟩]⟩, ⟨['k', 'é', 'u', 'i', 'h'], ['h', 'i', 'm'], [⟨['k', 'é', 'u', 'i', 'h'], ['h', 'i', 'm'], none⟩]⟩, ⟨['k', 'é', 'u', 'i', 'h'], ['h', 'e'], [⟨['k', 'é', 'u', 'i', 'h'], ['h', 'e'], none⟩]⟩, ⟨['b', 'é', 'i', '-', 'm', 'i', 'n'], ['g', 'i', 'v', 'e', '-', 'f', 'a', 'c', 'e'], [⟨['b', 'é', 'i'], ['g', 'i', 'v', 'e'], none⟩, ⟨['m', 'i', 'n'], ['f', 'a', 'c', 'e'], some '-'⟩]⟩, ⟨['n', 'g', 'ó', 'h', '.'], ['m', 'e'], [⟨['n', 'g', 'ó', 'h'], ['m', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("reciprocal", .acceptable)]
    paperFeatures := [] }

def ex_2a : Datum :=
  { id := "maslovanedjalkov2013_2a"
    source := ⟨"maslova-nedjalkov-2013", "(2a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "sout2750"
    primaryText := "met tet-ul juo"
    glossedTokens := [("met", "I"), ("tet-ul", "you-ACC"), ("juo", "see(TR.1SG)")]
    glossedWords := [⟨['m', 'e', 't'], ['I'], [⟨['m', 'e', 't'], ['I'], none⟩]⟩, ⟨['t', 'e', 't', '-', 'u', 'l'], ['y', 'o', 'u', '-', 'A', 'C', 'C'], [⟨['t', 'e', 't'], ['y', 'o', 'u'], none⟩, ⟨['u', 'l'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['j', 'u', 'o'], ['s', 'e', 'e', '(', 'T', 'R', '.', '1', 'S', 'G', ')'], [⟨['j', 'u', 'o'], ['s', 'e', 'e', '(', 'T', 'R', '.', '1', 'S', 'G', ')'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_2b : Datum :=
  { id := "maslovanedjalkov2013_2b"
    source := ⟨"maslova-nedjalkov-2013", "(2b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "sout2750"
    primaryText := "mit n’e-juo-ji:l’i"
    glossedTokens := [("mit", "we"), ("n’e-juo-ji:l’i", "RECP-see-INTR.1PL")]
    glossedWords := [⟨['m', 'i', 't'], ['w', 'e'], [⟨['m', 'i', 't'], ['w', 'e'], none⟩]⟩, ⟨['n', '’', 'e', '-', 'j', 'u', 'o', '-', 'j', 'i', ':', 'l', '’', 'i'], ['R', 'E', 'C', 'P', '-', 's', 'e', 'e', '-', 'I', 'N', 'T', 'R', '.', '1', 'P', 'L'], [⟨['n', '’', 'e'], ['R', 'E', 'C', 'P'], none⟩, ⟨['j', 'u', 'o'], ['s', 'e', 'e'], some '-'⟩, ⟨['j', 'i', 'l', '’', 'i'], ['I', 'N', 'T', 'R', '.', '1', 'P', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("reciprocal", .acceptable)]
    paperFeatures := [] }

def ex_3a : Datum :=
  { id := "maslovanedjalkov2013_3a"
    source := ⟨"maslova-nedjalkov-2013", "(3a)"⟩
    reportedIn := none
    method := some .description
    language := "imba1240"
    primaryText := "wambra-kuna riku-ri-rka"
    glossedTokens := [("wambra-kuna", "child-PL"), ("riku-ri-rka", "see-REFL/RECP-PST(3)")]
    glossedWords := [⟨['w', 'a', 'm', 'b', 'r', 'a', '-', 'k', 'u', 'n', 'a'], ['c', 'h', 'i', 'l', 'd', '-', 'P', 'L'], [⟨['w', 'a', 'm', 'b', 'r', 'a'], ['c', 'h', 'i', 'l', 'd'], none⟩, ⟨['k', 'u', 'n', 'a'], ['P', 'L'], some '-'⟩]⟩, ⟨['r', 'i', 'k', 'u', '-', 'r', 'i', '-', 'r', 'k', 'a'], ['s', 'e', 'e', '-', 'R', 'E', 'F', 'L', '/', 'R', 'E', 'C', 'P', '-', 'P', 'S', 'T', '(', '3', ')'], [⟨['r', 'i', 'k', 'u'], ['s', 'e', 'e'], none⟩, ⟨['r', 'i'], ['R', 'E', 'F', 'L', '/', 'R', 'E', 'C', 'P'], some '-'⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '(', '3', ')'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("reciprocal", .acceptable), ("reflexive", .acceptable)]
    paperFeatures := [] }

def ex_3b : Datum :=
  { id := "maslovanedjalkov2013_3b"
    source := ⟨"maslova-nedjalkov-2013", "(3b)"⟩
    reportedIn := none
    method := some .description
    language := "imba1240"
    primaryText := "ñukanchi maka-naju-nchi"
    glossedTokens := [("ñukanchi", "we"), ("maka-naju-nchi", "hit-COLL/RECP-1PL")]
    glossedWords := [⟨['ñ', 'u', 'k', 'a', 'n', 'c', 'h', 'i'], ['w', 'e'], [⟨['ñ', 'u', 'k', 'a', 'n', 'c', 'h', 'i'], ['w', 'e'], none⟩]⟩, ⟨['m', 'a', 'k', 'a', '-', 'n', 'a', 'j', 'u', '-', 'n', 'c', 'h', 'i'], ['h', 'i', 't', '-', 'C', 'O', 'L', 'L', '/', 'R', 'E', 'C', 'P', '-', '1', 'P', 'L'], [⟨['m', 'a', 'k', 'a'], ['h', 'i', 't'], none⟩, ⟨['n', 'a', 'j', 'u'], ['C', 'O', 'L', 'L', '/', 'R', 'E', 'C', 'P'], some '-'⟩, ⟨['n', 'c', 'h', 'i'], ['1', 'P', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("collective", .acceptable), ("reciprocal", .acceptable)]
    paperFeatures := [] }

def ex_4 : Datum :=
  { id := "maslovanedjalkov2013_4"
    source := ⟨"maslova-nedjalkov-2013", "(4)"⟩
    reportedIn := none
    method := some .description
    language := "amel1241"
    primaryText := "Ele ew-udo-co-b ew-udo-co-b ow-a"
    glossedTokens := [("Ele", "1DU"), ("ew-udo-co-b", "despise-IO.3SG-DS-3SG"), ("ew-udo-co-b", "despise-IO.3SG-DS-3SG"), ("ow-a", "1DU.SUBJ-PST")]
    glossedWords := [⟨['E', 'l', 'e'], ['1', 'D', 'U'], [⟨['E', 'l', 'e'], ['1', 'D', 'U'], none⟩]⟩, ⟨['e', 'w', '-', 'u', 'd', 'o', '-', 'c', 'o', '-', 'b'], ['d', 'e', 's', 'p', 'i', 's', 'e', '-', 'I', 'O', '.', '3', 'S', 'G', '-', 'D', 'S', '-', '3', 'S', 'G'], [⟨['e', 'w'], ['d', 'e', 's', 'p', 'i', 's', 'e'], none⟩, ⟨['u', 'd', 'o'], ['I', 'O', '.', '3', 'S', 'G'], some '-'⟩, ⟨['c', 'o'], ['D', 'S'], some '-'⟩, ⟨['b'], ['3', 'S', 'G'], some '-'⟩]⟩, ⟨['e', 'w', '-', 'u', 'd', 'o', '-', 'c', 'o', '-', 'b'], ['d', 'e', 's', 'p', 'i', 's', 'e', '-', 'I', 'O', '.', '3', 'S', 'G', '-', 'D', 'S', '-', '3', 'S', 'G'], [⟨['e', 'w'], ['d', 'e', 's', 'p', 'i', 's', 'e'], none⟩, ⟨['u', 'd', 'o'], ['I', 'O', '.', '3', 'S', 'G'], some '-'⟩, ⟨['c', 'o'], ['D', 'S'], some '-'⟩, ⟨['b'], ['3', 'S', 'G'], some '-'⟩]⟩, ⟨['o', 'w', '-', 'a'], ['1', 'D', 'U', '.', 'S', 'U', 'B', 'J', '-', 'P', 'S', 'T'], [⟨['o', 'w'], ['1', 'D', 'U', '.', 'S', 'U', 'B', 'J'], none⟩, ⟨['a'], ['P', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("reciprocal", .acceptable)]
    paperFeatures := [] }

def ex_5 : Datum :=
  { id := "maslovanedjalkov2013_5"
    source := ⟨"maslova-nedjalkov-2013", "(5)"⟩
    reportedIn := none
    method := some .description
    language := "godi1239"
    primaryText := "wa wà-wà"
    glossedTokens := [("wa", "they"), ("wà-wà", "love-love")]
    glossedWords := [⟨['w', 'a'], ['t', 'h', 'e', 'y'], [⟨['w', 'a'], ['t', 'h', 'e', 'y'], none⟩]⟩, ⟨['w', 'à', '-', 'w', 'à'], ['l', 'o', 'v', 'e', '-', 'l', 'o', 'v', 'e'], [⟨['w', 'à'], ['l', 'o', 'v', 'e'], none⟩, ⟨['w', 'à'], ['l', 'o', 'v', 'e'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("reciprocal", .acceptable)]
    paperFeatures := [] }

def ex_6 : Datum :=
  { id := "maslovanedjalkov2013_6"
    source := ⟨"maslova-nedjalkov-2013", "(6)"⟩
    reportedIn := none
    method := some .description
    language := "kala1399"
    primaryText := "immi-ssin-nut tuqun-niar-pusi"
    glossedTokens := [("immi-ssin-nut", "REFL/RECP-2PL-ALL"), ("tuqun-niar-pusi", "kill-FUT-2PL.IND")]
    glossedWords := [⟨['i', 'm', 'm', 'i', '-', 's', 's', 'i', 'n', '-', 'n', 'u', 't'], ['R', 'E', 'F', 'L', '/', 'R', 'E', 'C', 'P', '-', '2', 'P', 'L', '-', 'A', 'L', 'L'], [⟨['i', 'm', 'm', 'i'], ['R', 'E', 'F', 'L', '/', 'R', 'E', 'C', 'P'], none⟩, ⟨['s', 's', 'i', 'n'], ['2', 'P', 'L'], some '-'⟩, ⟨['n', 'u', 't'], ['A', 'L', 'L'], some '-'⟩]⟩, ⟨['t', 'u', 'q', 'u', 'n', '-', 'n', 'i', 'a', 'r', '-', 'p', 'u', 's', 'i'], ['k', 'i', 'l', 'l', '-', 'F', 'U', 'T', '-', '2', 'P', 'L', '.', 'I', 'N', 'D'], [⟨['t', 'u', 'q', 'u', 'n'], ['k', 'i', 'l', 'l'], none⟩, ⟨['n', 'i', 'a', 'r'], ['F', 'U', 'T'], some '-'⟩, ⟨['p', 'u', 's', 'i'], ['2', 'P', 'L', '.', 'I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("reciprocal", .acceptable), ("reflexive", .acceptable)]
    paperFeatures := [] }

def ex_7 : Datum :=
  { id := "maslovanedjalkov2013_7"
    source := ⟨"maslova-nedjalkov-2013", "(7)"⟩
    reportedIn := none
    method := some .description
    language := "wang1291"
    primaryText := "miri gadha-la-nha"
    glossedTokens := [("miri", "dog(ABS)"), ("gadha-la-nha", "bite-RECP-PRES")]
    glossedWords := [⟨['m', 'i', 'r', 'i'], ['d', 'o', 'g', '(', 'A', 'B', 'S', ')'], [⟨['m', 'i', 'r', 'i'], ['d', 'o', 'g', '(', 'A', 'B', 'S', ')'], none⟩]⟩, ⟨['g', 'a', 'd', 'h', 'a', '-', 'l', 'a', '-', 'n', 'h', 'a'], ['b', 'i', 't', 'e', '-', 'R', 'E', 'C', 'P', '-', 'P', 'R', 'E', 'S'], [⟨['g', 'a', 'd', 'h', 'a'], ['b', 'i', 't', 'e'], none⟩, ⟨['l', 'a'], ['R', 'E', 'C', 'P'], some '-'⟩, ⟨['n', 'h', 'a'], ['P', 'R', 'E', 'S'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("reciprocal", .acceptable)]
    paperFeatures := [] }

def ex_8 : Datum :=
  { id := "maslovanedjalkov2013_8"
    source := ⟨"maslova-nedjalkov-2013", "(8)"⟩
    reportedIn := none
    method := some .description
    language := "wari1268"
    primaryText := "para mana’ xujuhu’"
    glossedTokens := [("para", "therefore"), ("mana’", "angry"), ("xujuhu’", "REFL/RECP.2PL")]
    glossedWords := [⟨['p', 'a', 'r', 'a'], ['t', 'h', 'e', 'r', 'e', 'f', 'o', 'r', 'e'], [⟨['p', 'a', 'r', 'a'], ['t', 'h', 'e', 'r', 'e', 'f', 'o', 'r', 'e'], none⟩]⟩, ⟨['m', 'a', 'n', 'a', '’'], ['a', 'n', 'g', 'r', 'y'], [⟨['m', 'a', 'n', 'a', '’'], ['a', 'n', 'g', 'r', 'y'], none⟩]⟩, ⟨['x', 'u', 'j', 'u', 'h', 'u', '’'], ['R', 'E', 'F', 'L', '/', 'R', 'E', 'C', 'P', '.', '2', 'P', 'L'], [⟨['x', 'u', 'j', 'u', 'h', 'u', '’'], ['R', 'E', 'F', 'L', '/', 'R', 'E', 'C', 'P', '.', '2', 'P', 'L'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("reciprocal", .acceptable), ("reflexive", .acceptable)]
    paperFeatures := [] }

def ex_9a : Datum :=
  { id := "maslovanedjalkov2013_9a"
    source := ⟨"maslova-nedjalkov-2013", "(9a)"⟩
    reportedIn := none
    method := some .description
    language := "lith1251"
    primaryText := "Petr-as ir On-a bučiuoja-si."
    glossedTokens := [("Petr-as", "Peter-NOM"), ("ir", "and"), ("On-a", "Ann-NOM"), ("bučiuoja-si.", "kiss-REFL/RECP")]
    glossedWords := [⟨['P', 'e', 't', 'r', '-', 'a', 's'], ['P', 'e', 't', 'e', 'r', '-', 'N', 'O', 'M'], [⟨['P', 'e', 't', 'r'], ['P', 'e', 't', 'e', 'r'], none⟩, ⟨['a', 's'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['i', 'r'], ['a', 'n', 'd'], [⟨['i', 'r'], ['a', 'n', 'd'], none⟩]⟩, ⟨['O', 'n', '-', 'a'], ['A', 'n', 'n', '-', 'N', 'O', 'M'], [⟨['O', 'n'], ['A', 'n', 'n'], none⟩, ⟨['a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['b', 'u', 'č', 'i', 'u', 'o', 'j', 'a', '-', 's', 'i', '.'], ['k', 'i', 's', 's', '-', 'R', 'E', 'F', 'L', '/', 'R', 'E', 'C', 'P'], [⟨['b', 'u', 'č', 'i', 'u', 'o', 'j', 'a'], ['k', 'i', 's', 's'], none⟩, ⟨['s', 'i'], ['R', 'E', 'F', 'L', '/', 'R', 'E', 'C', 'P'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("reciprocal", .acceptable), ("reflexive", .unacceptable)]
    paperFeatures := [] }

def ex_9b : Datum :=
  { id := "maslovanedjalkov2013_9b"
    source := ⟨"maslova-nedjalkov-2013", "(9b)"⟩
    reportedIn := none
    method := some .description
    language := "lith1251"
    primaryText := "Ona supa-si."
    glossedTokens := [("Ona", "Ann"), ("supa-si.", "rock-REFL/RECP")]
    glossedWords := [⟨['O', 'n', 'a'], ['A', 'n', 'n'], [⟨['O', 'n', 'a'], ['A', 'n', 'n'], none⟩]⟩, ⟨['s', 'u', 'p', 'a', '-', 's', 'i', '.'], ['r', 'o', 'c', 'k', '-', 'R', 'E', 'F', 'L', '/', 'R', 'E', 'C', 'P'], [⟨['s', 'u', 'p', 'a'], ['r', 'o', 'c', 'k'], none⟩, ⟨['s', 'i'], ['R', 'E', 'F', 'L', '/', 'R', 'E', 'C', 'P'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("reflexive", .acceptable), ("reciprocal", .unacceptable)]
    paperFeatures := [] }

def all : List Datum := [ex_1, ex_2a, ex_2b, ex_3a, ex_3b, ex_4, ex_5, ex_6, ex_7, ex_8, ex_9a, ex_9b]

/-- The meanings the chapter's translations give a clause. -/
inductive Reading where
  /-- reciprocal: the participants act on each other -/
  | reciprocal
  /-- reflexive: the participants act on themselves -/
  | reflexive
  /-- collective: the participants act jointly -/
  | collective
  deriving DecidableEq, Repr, Fintype

/-- The name the rows give the reading. -/
def Reading.label : Reading → String
  | .reciprocal => "reciprocal"
  | .reflexive => "reflexive"
  | .collective => "collective"

/-- The judgment a row records for the reading, if it records one. -/
def reading (e : Datum) (r : Reading) : Option Judgment :=
  e.readings.lookup r.label

end MaslovaNedjalkov2013.Examples
