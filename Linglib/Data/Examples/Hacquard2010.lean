module

public import Linglib.Data.Examples.Schema

/-!
# `Hacquard2010` — typed example data

Auto-generated from `Linglib/Data/Examples/Hacquard2010.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Hacquard2010.Examples`.
-/

@[expose] public section

namespace Hacquard2010.Examples

def ex11 : Datum :=
  { id := "hacquard2010_ex11"
    source := ⟨"hacquard-2010", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary had to take the train to go to Paris."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("root: given Mary's circumstances then, a past necessity to take the train then", .acceptable), ("root evaluated now: given her circumstances now, a necessity to have taken the train then", .unacceptable)]
    paperFeatures := [("section", "3.1"), ("phenomenon", "tense")] }

def ex12 : Datum :=
  { id := "hacquard2010_ex12"
    source := ⟨"hacquard-2010", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary had to be home (at the time of the crime)."
    glossedTokens := []
    context := "Evidence gathered a week ago pointed to Mary being home at the time of the murder; yesterday Poirot debunked her alibi."
    judgment := .acceptable
    contrasts := []
    readings := [("epistemic over past: given what is known now, it is necessary that Mary was home", .acceptable), ("past over epistemic: given what was known then, it was necessary that Mary was home", .unacceptable)]
    paperFeatures := [("section", "3.1"), ("phenomenon", "tense")] }

def ex13a : Datum :=
  { id := "hacquard2010_ex13a"
    source := ⟨"hacquard-2010", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Two days ago, Poirot thought that Mary had to be home."
    glossedTokens := []
    context := "Evidence gathered a week ago pointed to Mary being home at the time of the murder; yesterday Poirot debunked her alibi."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("phenomenon", "tense")] }

def ex13b : Datum :=
  { id := "hacquard2010_ex13b"
    source := ⟨"hacquard-2010", "(13b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This didn't make sense, thought Poirot... Mary had to be home."
    glossedTokens := []
    context := "Evidence gathered a week ago pointed to Mary being home at the time of the murder; yesterday Poirot debunked her alibi."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("phenomenon", "tense")] }

def ex13c : Datum :=
  { id := "hacquard2010_ex13c"
    source := ⟨"hacquard-2010", "(13c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Given what Poirot knew then, Mary had to be home."
    glossedTokens := []
    context := "Evidence gathered a week ago pointed to Mary being home at the time of the murder; yesterday Poirot debunked her alibi."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("phenomenon", "tense")] }

def ex14a : Datum :=
  { id := "hacquard2010_ex14a"
    source := ⟨"hacquard-2010", "(14a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni può aver parlato a Maria."
    glossedTokens := [("Gianni", "Gianni"), ("può", "can"), ("aver", "have"), ("parlato", "talked"), ("a", "to"), ("Maria.", "Maria.")]
    glossedWords := [⟨['G', 'i', 'a', 'n', 'n', 'i'], ['G', 'i', 'a', 'n', 'n', 'i'], [⟨['G', 'i', 'a', 'n', 'n', 'i'], ['G', 'i', 'a', 'n', 'n', 'i'], none⟩]⟩, ⟨['p', 'u', 'ò'], ['c', 'a', 'n'], [⟨['p', 'u', 'ò'], ['c', 'a', 'n'], none⟩]⟩, ⟨['a', 'v', 'e', 'r'], ['h', 'a', 'v', 'e'], [⟨['a', 'v', 'e', 'r'], ['h', 'a', 'v', 'e'], none⟩]⟩, ⟨['p', 'a', 'r', 'l', 'a', 't', 'o'], ['t', 'a', 'l', 'k', 'e', 'd'], [⟨['p', 'a', 'r', 'l', 'a', 't', 'o'], ['t', 'a', 'l', 'k', 'e', 'd'], none⟩]⟩, ⟨['a'], ['t', 'o'], [⟨['a'], ['t', 'o'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a', '.'], ['M', 'a', 'r', 'i', 'a', '.'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a', '.'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("epistemic", .acceptable), ("deontic or ability", .unacceptable)]
    paperFeatures := [("section", "3.1"), ("phenomenon", "tense")] }

def ex14b : Datum :=
  { id := "hacquard2010_ex14b"
    source := ⟨"hacquard-2010", "(14b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni ha potuto parlare a Maria."
    glossedTokens := [("Gianni", "Gianni"), ("ha", "has"), ("potuto", "could"), ("parlare", "talk"), ("a", "to"), ("Maria.", "Maria.")]
    glossedWords := [⟨['G', 'i', 'a', 'n', 'n', 'i'], ['G', 'i', 'a', 'n', 'n', 'i'], [⟨['G', 'i', 'a', 'n', 'n', 'i'], ['G', 'i', 'a', 'n', 'n', 'i'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 's'], [⟨['h', 'a'], ['h', 'a', 's'], none⟩]⟩, ⟨['p', 'o', 't', 'u', 't', 'o'], ['c', 'o', 'u', 'l', 'd'], [⟨['p', 'o', 't', 'u', 't', 'o'], ['c', 'o', 'u', 'l', 'd'], none⟩]⟩, ⟨['p', 'a', 'r', 'l', 'a', 'r', 'e'], ['t', 'a', 'l', 'k'], [⟨['p', 'a', 'r', 'l', 'a', 'r', 'e'], ['t', 'a', 'l', 'k'], none⟩]⟩, ⟨['a'], ['t', 'o'], [⟨['a'], ['t', 'o'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a', '.'], ['M', 'a', 'r', 'i', 'a', '.'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a', '.'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("deontic or ability", .acceptable), ("epistemic", .unacceptable)]
    paperFeatures := [("section", "3.1"), ("phenomenon", "tense")] }

def ex16 : Datum :=
  { id := "hacquard2010_ex16"
    source := ⟨"hacquard-2010", "(16)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Mary put soulever cette table, mais elle ne la souleva pas."
    glossedTokens := [("Mary", "Mary"), ("put", "could-PFV"), ("soulever", "lift"), ("cette", "this"), ("table,", "table,"), ("mais", "but"), ("elle", "she"), ("ne", "NE"), ("la", "it"), ("souleva", "lifted"), ("pas.", "not.")]
    glossedWords := [⟨['M', 'a', 'r', 'y'], ['M', 'a', 'r', 'y'], [⟨['M', 'a', 'r', 'y'], ['M', 'a', 'r', 'y'], none⟩]⟩, ⟨['p', 'u', 't'], ['c', 'o', 'u', 'l', 'd', '-', 'P', 'F', 'V'], []⟩, ⟨['s', 'o', 'u', 'l', 'e', 'v', 'e', 'r'], ['l', 'i', 'f', 't'], [⟨['s', 'o', 'u', 'l', 'e', 'v', 'e', 'r'], ['l', 'i', 'f', 't'], none⟩]⟩, ⟨['c', 'e', 't', 't', 'e'], ['t', 'h', 'i', 's'], [⟨['c', 'e', 't', 't', 'e'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['t', 'a', 'b', 'l', 'e', ','], ['t', 'a', 'b', 'l', 'e', ','], [⟨['t', 'a', 'b', 'l', 'e'], ['t', 'a', 'b', 'l', 'e', ','], none⟩]⟩, ⟨['m', 'a', 'i', 's'], ['b', 'u', 't'], [⟨['m', 'a', 'i', 's'], ['b', 'u', 't'], none⟩]⟩, ⟨['e', 'l', 'l', 'e'], ['s', 'h', 'e'], [⟨['e', 'l', 'l', 'e'], ['s', 'h', 'e'], none⟩]⟩, ⟨['n', 'e'], ['N', 'E'], [⟨['n', 'e'], ['N', 'E'], none⟩]⟩, ⟨['l', 'a'], ['i', 't'], [⟨['l', 'a'], ['i', 't'], none⟩]⟩, ⟨['s', 'o', 'u', 'l', 'e', 'v', 'a'], ['l', 'i', 'f', 't', 'e', 'd'], [⟨['s', 'o', 'u', 'l', 'e', 'v', 'a'], ['l', 'i', 'f', 't', 'e', 'd'], none⟩]⟩, ⟨['p', 'a', 's', '.'], ['n', 'o', 't', '.'], [⟨['p', 'a', 's'], ['n', 'o', 't', '.'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("phenomenon", "actualityEntailment")] }

def ex17 : Datum :=
  { id := "hacquard2010_ex17"
    source := ⟨"hacquard-2010", "(17)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "John put prendre le train, bien qu'il soit possible qu'il ne l'ait pas pris."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("epistemic", .acceptable), ("root: John managed to take the train, but it is possible he didn't", .unacceptable)]
    paperFeatures := [("section", "3.2"), ("phenomenon", "actualityEntailment")] }

def ex18_19 : Datum :=
  { id := "hacquard2010_ex18_19"
    source := ⟨"hacquard-2010", "(18)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Mary put prendre le train."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("epistemic over aspect: some world compatible with what is known holds a past train-taking by Mary", .acceptable), ("aspect over root: an actual past event which in some circumstantial world is a train-taking by Mary", .acceptable)]
    paperFeatures := [("section", "3.2"), ("phenomenon", "actualityEntailment")] }

def ex22 : Datum :=
  { id := "hacquard2010_ex22"
    source := ⟨"hacquard-2010", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary had to take the train."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("given Mary's circumstances then, she had to take the train then", .acceptable), ("given Mary's circumstances now, she had to take the train", .unacceptable)]
    paperFeatures := [("section", "4.2"), ("phenomenon", "individualTimePair")] }

def ex23 : Datum :=
  { id := "hacquard2010_ex23"
    source := ⟨"hacquard-2010", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary had to be home."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("given what I know now, it must be the case that Mary was home then", .acceptable), ("given what I knew then, Mary had to be home", .unacceptable)]
    paperFeatures := [("section", "4.2"), ("phenomenon", "individualTimePair")] }

def ex24 : Datum :=
  { id := "hacquard2010_ex24"
    source := ⟨"hacquard-2010", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John thought that Mary might be home."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("given what John knew at his thinking time, it was possible Mary was home", .acceptable), ("given what John knows now, it was possible Mary was home", .unacceptable)]
    paperFeatures := [("section", "4.2"), ("phenomenon", "individualTimePair")] }

def ex25 : Datum :=
  { id := "hacquard2010_ex25"
    source := ⟨"hacquard-2010", "(25)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John thought yesterday that Mary had taken the train the day before."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.2"), ("phenomenon", "locality")] }

def ex26 : Datum :=
  { id := "hacquard2010_ex26"
    source := ⟨"hacquard-2010", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John might have thought yesterday that Mary had taken the train the day before."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("speech event: given what I know now, it is possible that John thought Mary had taken the train", .acceptable)]
    paperFeatures := [("section", "4.2"), ("phenomenon", "locality")] }

def ex27 : Datum :=
  { id := "hacquard2010_ex27"
    source := ⟨"hacquard-2010", "(27)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John thought yesterday that Mary might have taken the train the day before."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("attitude event: given what John thought yesterday, it was possible that Mary had taken the train", .acceptable), ("speech event: John thought yesterday that it was possible, given what I know, that Mary took the train", .unacceptable)]
    paperFeatures := [("section", "4.2"), ("phenomenon", "locality")] }

def ex28 : Datum :=
  { id := "hacquard2010_ex28"
    source := ⟨"hacquard-2010", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John thought yesterday that Mary had to take the train the day before."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("VP event: given Mary's circumstances the day before yesterday, it was necessary that she take the train", .acceptable), ("speech event: John thought that it was necessary given what I know that Mary took the train", .unacceptable)]
    paperFeatures := [("section", "4.2"), ("phenomenon", "locality")] }

def ex45a : Datum :=
  { id := "hacquard2010_ex45a"
    source := ⟨"hacquard-2010", "(45a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is the murderer."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.3.2"), ("phenomenon", "speechEvent")] }

def ex50 : Datum :=
  { id := "hacquard2010_ex50"
    source := ⟨"hacquard-2010", "(50)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John believes it might be raining."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("rain is compatible with what John believes", .acceptable)]
    paperFeatures := [("section", "6.1.1"), ("phenomenon", "embeddedEpistemic")] }

def ex55 : Datum :=
  { id := "hacquard2010_ex55"
    source := ⟨"hacquard-2010", "(55)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It must be raining."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.1.2"), ("phenomenon", "matrixEpistemic")] }

def ex58a : Datum :=
  { id := "hacquard2010_ex58a"
    source := ⟨"yalcin-2007", "(7)"⟩
    reportedIn := some ⟨"hacquard-2010", "(58a)"⟩
    language := "stan1293"
    primaryText := "Suppose that it is raining and that it might not be raining."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.1.3"), ("phenomenon", "yalcin")] }

def ex59 : Datum :=
  { id := "hacquard2010_ex59"
    source := ⟨"hacquard-2010", "(59)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Last night Mary had to take the train to go to Paris."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("epistemic for the subject: it was necessary, last night, given what Mary knew, that she took the train", .unacceptable)]
    paperFeatures := [("section", "6.1.4"), ("phenomenon", "contentLicensing")] }

def ex60a : Datum :=
  { id := "hacquard2010_ex60a"
    source := ⟨"hacquard-2010", "(60a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "John konnte sehen/merken, dass Mary nett war."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("epistemic for the subject: Mary being nice was compatible with what John came to know", .acceptable)]
    paperFeatures := [("section", "6.1.4"), ("phenomenon", "contentLicensing")] }

def ex60b : Datum :=
  { id := "hacquard2010_ex60b"
    source := ⟨"hacquard-2010", "(60b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "John a pu voir/remarquer que Mary était gentille."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("epistemic for the subject: Mary being nice was compatible with what John came to know", .acceptable)]
    paperFeatures := [("section", "6.1.4"), ("phenomenon", "contentLicensing")] }

def ex62 : Datum :=
  { id := "hacquard2010_ex62"
    source := ⟨"hacquard-2010", "(62)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "(Last night) Mary had to take the train (to go to Paris)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.2"), ("phenomenon", "circumstantial")] }

def ex63 : Datum :=
  { id := "hacquard2010_ex63"
    source := ⟨"hacquard-2010", "(63)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A lot of people can jump in this pool."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.2"), ("phenomenon", "circumstantial")] }

def all : List Datum := [ex11, ex12, ex13a, ex13b, ex13c, ex14a, ex14b, ex16, ex17, ex18_19, ex22, ex23, ex24, ex25, ex26, ex27, ex28, ex45a, ex50, ex55, ex58a, ex59, ex60a, ex60b, ex62, ex63]

end Hacquard2010.Examples
