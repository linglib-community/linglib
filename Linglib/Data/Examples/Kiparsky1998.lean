module

public import Linglib.Data.Examples.Schema

/-!
# `Kiparsky1998` — typed example data

Auto-generated from `Linglib/Data/Examples/Kiparsky1998.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Kiparsky1998.Examples`.
-/

@[expose] public section

namespace Kiparsky1998.Examples

def ex_1a_singular : Datum :=
  { id := "kiparsky1998_1a_singular"
    source := ⟨"kiparsky-1998", "(1a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Ammuin karhua"
    glossedTokens := [("Ammu-i-n", "shoot-Pst-1Sg"), ("karhu-a", "bear-Part")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "ampua"), ("object", "singular"), ("case", "part")] }

def ex_1a_numeral : Datum :=
  { id := "kiparsky1998_1a_numeral"
    source := ⟨"kiparsky-1998", "(1a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Ammuin kahta karhua"
    glossedTokens := [("Ammu-i-n", "shoot-Pst-1Sg"), ("kah-ta", "two-Part"), ("karhu-a", "bear-Part")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "ampua"), ("object", "numeral"), ("case", "part")] }

def ex_1a_plural : Datum :=
  { id := "kiparsky1998_1a_plural"
    source := ⟨"kiparsky-1998", "(1a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Ammuin karhuja"
    glossedTokens := [("Ammu-i-n", "shoot-Pst-1Sg"), ("karhu-j-a", "bear-Pl-Part")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "ampua"), ("object", "plural"), ("case", "part")] }

def ex_1b_singular : Datum :=
  { id := "kiparsky1998_1b_singular"
    source := ⟨"kiparsky-1998", "(1b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Ammuin karhun"
    glossedTokens := [("Ammu-i-n", "shoot-Pst-1Sg"), ("karhu-n", "bear-Acc")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "ampua"), ("object", "singular"), ("case", "acc")] }

def ex_1b_numeral : Datum :=
  { id := "kiparsky1998_1b_numeral"
    source := ⟨"kiparsky-1998", "(1b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Ammuin kaksi karhua"
    glossedTokens := [("Ammu-i-n", "shoot-Pst-1Sg"), ("kaksi", "two-Acc"), ("karhu-a", "bear-Part")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "ampua"), ("object", "numeral"), ("case", "acc")] }

def ex_1b_plural : Datum :=
  { id := "kiparsky1998_1b_plural"
    source := ⟨"kiparsky-1998", "(1b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Ammuin karhut"
    glossedTokens := [("Ammu-i-n", "shoot-Pst-1Sg"), ("karhu-t", "bear-PlAcc")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "ampua"), ("object", "plural"), ("case", "acc")] }

def ex_2a_singular : Datum :=
  { id := "kiparsky1998_2a_singular"
    source := ⟨"kiparsky-1998", "(2a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "saan karhua"
    glossedTokens := [("saa-n", "get-1Sg"), ("karhu-a", "bear-Part")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "saada"), ("object", "singular"), ("case", "part")] }

def ex_2a_numeral : Datum :=
  { id := "kiparsky1998_2a_numeral"
    source := ⟨"kiparsky-1998", "(2a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "saan kahta karhua"
    glossedTokens := [("saa-n", "get-1Sg"), ("kah-ta", "two-Part"), ("karhu-a", "bear-Part")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "saada"), ("object", "numeral"), ("case", "part")] }

def ex_2a_plural : Datum :=
  { id := "kiparsky1998_2a_plural"
    source := ⟨"kiparsky-1998", "(2a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "saan karhuja"
    glossedTokens := [("saa-n", "get-1Sg"), ("karhu-j-a", "bear-Pl-Part")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "saada"), ("object", "plural"), ("case", "part")] }

def ex_2b_singular : Datum :=
  { id := "kiparsky1998_2b_singular"
    source := ⟨"kiparsky-1998", "(2b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "saan karhun"
    glossedTokens := [("saa-n", "get-1Sg"), ("karhu-n", "bear-Acc")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "saada"), ("object", "singular"), ("case", "acc")] }

def ex_2b_numeral : Datum :=
  { id := "kiparsky1998_2b_numeral"
    source := ⟨"kiparsky-1998", "(2b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "saan kaksi karhua"
    glossedTokens := [("saa-n", "get-1Sg"), ("kaksi", "two-Acc"), ("karhu-a", "bear-Part")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "saada"), ("object", "numeral"), ("case", "acc")] }

def ex_2b_plural : Datum :=
  { id := "kiparsky1998_2b_plural"
    source := ⟨"kiparsky-1998", "(2b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "saan karhut"
    glossedTokens := [("saa-n", "get-1Sg"), ("karhu-t", "bear-PlAcc")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "saada"), ("object", "plural"), ("case", "acc")] }

def ex_3a_singular : Datum :=
  { id := "kiparsky1998_3a_singular"
    source := ⟨"kiparsky-1998", "(3a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "etsin karhua"
    glossedTokens := [("etsi-n", "seek-1Sg"), ("karhu-a", "bear-Part")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "etsiä"), ("object", "singular"), ("case", "part")] }

def ex_3a_numeral : Datum :=
  { id := "kiparsky1998_3a_numeral"
    source := ⟨"kiparsky-1998", "(3a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "etsin kahta karhua"
    glossedTokens := [("etsi-n", "seek-1Sg"), ("kah-ta", "two-Part"), ("karhu-a", "bear-Part")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "etsiä"), ("object", "numeral"), ("case", "part")] }

def ex_3a_plural : Datum :=
  { id := "kiparsky1998_3a_plural"
    source := ⟨"kiparsky-1998", "(3a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "etsin karhuja"
    glossedTokens := [("etsi-n", "seek-1Sg"), ("karhu-j-a", "bear-Pl-Part")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "etsiä"), ("object", "plural"), ("case", "part")] }

def ex_3b_singular : Datum :=
  { id := "kiparsky1998_3b_singular"
    source := ⟨"kiparsky-1998", "(3b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "etsin karhun"
    glossedTokens := [("etsi-n", "seek-1Sg"), ("karhu-n", "bear-Acc")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "etsiä"), ("object", "singular"), ("case", "acc")] }

def ex_3b_numeral : Datum :=
  { id := "kiparsky1998_3b_numeral"
    source := ⟨"kiparsky-1998", "(3b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "etsin kaksi karhua"
    glossedTokens := [("etsi-n", "seek-1Sg"), ("kaksi", "two-Acc"), ("karhu-a", "bear-Part")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "etsiä"), ("object", "numeral"), ("case", "acc")] }

def ex_3b_plural : Datum :=
  { id := "kiparsky1998_3b_plural"
    source := ⟨"kiparsky-1998", "(3b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "etsin karhut"
    glossedTokens := [("etsi-n", "seek-1Sg"), ("karhu-t", "bear-PlAcc")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "etsiä"), ("object", "plural"), ("case", "acc")] }

def ex_4a_singular : Datum :=
  { id := "kiparsky1998_4a_singular"
    source := ⟨"kiparsky-1998", "(4a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "omistan karhua"
    glossedTokens := [("omista-n", "own-1Sg"), ("karhu-a", "bear-Part")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "omistaa"), ("object", "singular"), ("case", "part")] }

def ex_4a_numeral : Datum :=
  { id := "kiparsky1998_4a_numeral"
    source := ⟨"kiparsky-1998", "(4a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "omistan kahta karhua"
    glossedTokens := [("omista-n", "own-1Sg"), ("kah-ta", "two-Part"), ("karhu-a", "bear-Part")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "omistaa"), ("object", "numeral"), ("case", "part")] }

def ex_4a_plural : Datum :=
  { id := "kiparsky1998_4a_plural"
    source := ⟨"kiparsky-1998", "(4a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "omistan karhuja"
    glossedTokens := [("omista-n", "own-1Sg"), ("karhu-j-a", "bear-Pl-Part")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "omistaa"), ("object", "plural"), ("case", "part")] }

def ex_4b_singular : Datum :=
  { id := "kiparsky1998_4b_singular"
    source := ⟨"kiparsky-1998", "(4b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "omistan karhun"
    glossedTokens := [("omista-n", "own-1Sg"), ("karhu-n", "bear-Acc")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "omistaa"), ("object", "singular"), ("case", "acc")] }

def ex_4b_numeral : Datum :=
  { id := "kiparsky1998_4b_numeral"
    source := ⟨"kiparsky-1998", "(4b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "omistan kaksi karhua"
    glossedTokens := [("omista-n", "own-1Sg"), ("kaksi", "two-Acc"), ("karhu-a", "bear-Part")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "omistaa"), ("object", "numeral"), ("case", "acc")] }

def ex_4b_plural : Datum :=
  { id := "kiparsky1998_4b_plural"
    source := ⟨"kiparsky-1998", "(4b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "omistan karhut"
    glossedTokens := [("omista-n", "own-1Sg"), ("karhu-t", "bear-PlAcc")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "omistaa"), ("object", "plural"), ("case", "acc")] }

def all : List Datum := [ex_1a_singular, ex_1a_numeral, ex_1a_plural, ex_1b_singular, ex_1b_numeral, ex_1b_plural, ex_2a_singular, ex_2a_numeral, ex_2a_plural, ex_2b_singular, ex_2b_numeral, ex_2b_plural, ex_3a_singular, ex_3a_numeral, ex_3a_plural, ex_3b_singular, ex_3b_numeral, ex_3b_plural, ex_4a_singular, ex_4a_numeral, ex_4a_plural, ex_4b_singular, ex_4b_numeral, ex_4b_plural]

end Kiparsky1998.Examples
