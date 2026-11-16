module

public import Linglib.Data.Examples.Schema

/-!
# `Winter2018` — typed example data

Auto-generated from `Linglib/Data/Examples/Winter2018.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Winter2018.Examples`.
-/

@[expose] public section

namespace Winter2018.Examples

def ex_1 : Datum :=
  { id := "winter2018_1"
    source := ⟨"winter-2018", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue dated Dan."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Dan dated Sue.", .acceptable)]
    readings := []
    paperFeatures := [("predicate", "date"), ("property", "symmetric")] }

def ex_2 : Datum :=
  { id := "winter2018_2"
    source := ⟨"winter-2018", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue and Dan dated."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "date"), ("alternation", "plain")] }

def ex_3 : Datum :=
  { id := "winter2018_3"
    source := ⟨"winter-2018", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue and Dan hugged."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "hug"), ("alternation", "non-plain")] }

def ex_4 : Datum :=
  { id := "winter2018_4"
    source := ⟨"winter-2018", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue hugged Dan and Dan hugged Sue."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "hug"), ("inference", "does not entail Sue and Dan hugged")] }

def ex_5 : Datum :=
  { id := "winter2018_5"
    source := ⟨"winter-2018", "(25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A, B and C agreed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "agree"), ("inference", "one shared opinion")] }

def ex_6 : Datum :=
  { id := "winter2018_6"
    source := ⟨"winter-2018", "(25b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A agreed with B, and B agreed with C, and C agreed with A."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "agree"), ("inference", "possibly three opinions")] }

def ex_7 : Datum :=
  { id := "winter2018_7"
    source := ⟨"winter-2018", "(33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The drunk embraced the lamppost."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("The lamppost embraced the drunk.", .unacceptable)]
    readings := []
    paperFeatures := [("predicate", "embrace"), ("property", "non-symmetric")] }

def ex_8 : Datum :=
  { id := "winter2018_8"
    source := ⟨"winter-2018", "(37)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue and Dan hugged."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "hug"), ("scenario", "(39)"), ("truth", "does not follow")] }

def ex_9 : Datum :=
  { id := "winter2018_9"
    source := ⟨"winter-2018", "(38)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue hugged Dan and Dan hugged Sue."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "hug"), ("scenario", "(39)"), ("truth", "true")] }

def ex_10 : Datum :=
  { id := "winter2018_10"
    source := ⟨"winter-2018", "(44)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue hugged Dan and Dan hugged Sue simultaneously."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "hug"), ("inference", "entails Sue and Dan hugged")] }

def ex_11 : Datum :=
  { id := "winter2018_11"
    source := ⟨"winter-2018", "(45)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue and Dan broke up."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "break up"), ("inference", "does not entail Sue broke up with Dan")] }

def ex_12 : Datum :=
  { id := "winter2018_12"
    source := ⟨"winter-2018", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue broke up with Dan."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "break up"), ("inference", "entails Sue and Dan broke up")] }

def ex_13 : Datum :=
  { id := "winter2018_13"
    source := ⟨"winter-2018", "(47)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "morrissey makir et hod-ma'alata, ve-hi makira oto"
    glossedTokens := [("morrissey", "Morrissey"), ("makir", "know-MASC.SG"), ("et", "ACC"), ("hod-ma'alata", "her-majesty"), ("ve-hi", "and-she"), ("makira", "know-FEM.SG"), ("oto", "him")]
    glossedWords := [⟨['m', 'o', 'r', 'r', 'i', 's', 's', 'e', 'y'], ['M', 'o', 'r', 'r', 'i', 's', 's', 'e', 'y'], [⟨['m', 'o', 'r', 'r', 'i', 's', 's', 'e', 'y'], ['M', 'o', 'r', 'r', 'i', 's', 's', 'e', 'y'], none⟩]⟩, ⟨['m', 'a', 'k', 'i', 'r'], ['k', 'n', 'o', 'w', '-', 'M', 'A', 'S', 'C', '.', 'S', 'G'], []⟩, ⟨['e', 't'], ['A', 'C', 'C'], [⟨['e', 't'], ['A', 'C', 'C'], none⟩]⟩, ⟨['h', 'o', 'd', '-', 'm', 'a', '\'', 'a', 'l', 'a', 't', 'a'], ['h', 'e', 'r', '-', 'm', 'a', 'j', 'e', 's', 't', 'y'], [⟨['h', 'o', 'd'], ['h', 'e', 'r'], none⟩, ⟨['m', 'a', '\'', 'a', 'l', 'a', 't', 'a'], ['m', 'a', 'j', 'e', 's', 't', 'y'], some '-'⟩]⟩, ⟨['v', 'e', '-', 'h', 'i'], ['a', 'n', 'd', '-', 's', 'h', 'e'], [⟨['v', 'e'], ['a', 'n', 'd'], none⟩, ⟨['h', 'i'], ['s', 'h', 'e'], some '-'⟩]⟩, ⟨['m', 'a', 'k', 'i', 'r', 'a'], ['k', 'n', 'o', 'w', '-', 'F', 'E', 'M', '.', 'S', 'G'], []⟩, ⟨['o', 't', 'o'], ['h', 'i', 'm'], [⟨['o', 't', 'o'], ['h', 'i', 'm'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "makir"), ("inference", "does not entail (48)")] }

def ex_14 : Datum :=
  { id := "winter2018_14"
    source := ⟨"winter-2018", "(48)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "morrissey ve-hod-ma'alata makirim"
    glossedTokens := [("morrissey", "Morrissey"), ("ve-hod-ma'alata", "and-her-majesty"), ("makirim", "know-MASC.PL")]
    glossedWords := [⟨['m', 'o', 'r', 'r', 'i', 's', 's', 'e', 'y'], ['M', 'o', 'r', 'r', 'i', 's', 's', 'e', 'y'], [⟨['m', 'o', 'r', 'r', 'i', 's', 's', 'e', 'y'], ['M', 'o', 'r', 'r', 'i', 's', 's', 'e', 'y'], none⟩]⟩, ⟨['v', 'e', '-', 'h', 'o', 'd', '-', 'm', 'a', '\'', 'a', 'l', 'a', 't', 'a'], ['a', 'n', 'd', '-', 'h', 'e', 'r', '-', 'm', 'a', 'j', 'e', 's', 't', 'y'], [⟨['v', 'e'], ['a', 'n', 'd'], none⟩, ⟨['h', 'o', 'd'], ['h', 'e', 'r'], some '-'⟩, ⟨['m', 'a', '\'', 'a', 'l', 'a', 't', 'a'], ['m', 'a', 'j', 'e', 's', 't', 'y'], some '-'⟩]⟩, ⟨['m', 'a', 'k', 'i', 'r', 'i', 'm'], ['k', 'n', 'o', 'w', '-', 'M', 'A', 'S', 'C', '.', 'P', 'L'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "makir"), ("reading", "collective only")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, ex_10, ex_11, ex_12, ex_13, ex_14]

end Winter2018.Examples
