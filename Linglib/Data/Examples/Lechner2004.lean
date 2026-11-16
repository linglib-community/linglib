module

public import Linglib.Data.Examples.Schema

/-!
# `Lechner2004` — typed example data

Auto-generated from `Linglib/Data/Examples/Lechner2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Lechner2004.Examples`.
-/

@[expose] public section

namespace Lechner2004.Examples

def ch2_24 : Datum :=
  { id := "lechner2004_ch2_24"
    source := ⟨"lechner-2004", "(24) of chapter 2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is prouder of John_i than he_i is."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("coreference", "he = John"), ("deletion_site", "d-proud of John")] }

def ch2_25 : Datum :=
  { id := "lechner2004_ch2_25"
    source := ⟨"lechner-2004", "(25) of chapter 2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is prouder of John_i than he_i believes that I am."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("coreference", "he = John"), ("deletion_site", "d-proud of John")] }

def ch4_83a : Datum :=
  { id := "lechner2004_ch4_83a"
    source := ⟨"lechner-2004", "(83a) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sally introduced him_i to more friends than Peter_i's sister."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("coreference", "him = Peter"), ("remnant_case", "NOM")] }

def ch4_85a : Datum :=
  { id := "lechner2004_ch4_85a"
    source := ⟨"lechner-2004", "(85a) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He_i introduced Sally to more friends than Peter_i's sister."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("coreference", "he = Peter"), ("remnant_case", "ACC")] }

def ch4_87a : Datum :=
  { id := "lechner2004_ch4_87a"
    source := ⟨"lechner-2004", "(87a) of chapter 4"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Sie hat ihm_i mehr Leute vorgestellt als Peters_i Schwester."
    glossedTokens := [("Sie", "she"), ("hat", "has"), ("ihm", "him"), ("mehr", "more"), ("Leute", "people"), ("vorgestellt", "introduced"), ("als", "than"), ("Peters", "Peter's"), ("Schwester", "sister")]
    glossedWords := [⟨['S', 'i', 'e'], ['s', 'h', 'e'], [⟨['S', 'i', 'e'], ['s', 'h', 'e'], none⟩]⟩, ⟨['h', 'a', 't'], ['h', 'a', 's'], [⟨['h', 'a', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['i', 'h', 'm'], ['h', 'i', 'm'], [⟨['i', 'h', 'm'], ['h', 'i', 'm'], none⟩]⟩, ⟨['m', 'e', 'h', 'r'], ['m', 'o', 'r', 'e'], [⟨['m', 'e', 'h', 'r'], ['m', 'o', 'r', 'e'], none⟩]⟩, ⟨['L', 'e', 'u', 't', 'e'], ['p', 'e', 'o', 'p', 'l', 'e'], [⟨['L', 'e', 'u', 't', 'e'], ['p', 'e', 'o', 'p', 'l', 'e'], none⟩]⟩, ⟨['v', 'o', 'r', 'g', 'e', 's', 't', 'e', 'l', 'l', 't'], ['i', 'n', 't', 'r', 'o', 'd', 'u', 'c', 'e', 'd'], [⟨['v', 'o', 'r', 'g', 'e', 's', 't', 'e', 'l', 'l', 't'], ['i', 'n', 't', 'r', 'o', 'd', 'u', 'c', 'e', 'd'], none⟩]⟩, ⟨['a', 'l', 's'], ['t', 'h', 'a', 'n'], [⟨['a', 'l', 's'], ['t', 'h', 'a', 'n'], none⟩]⟩, ⟨['P', 'e', 't', 'e', 'r', 's'], ['P', 'e', 't', 'e', 'r', '\'', 's'], [⟨['P', 'e', 't', 'e', 'r', 's'], ['P', 'e', 't', 'e', 'r', '\'', 's'], none⟩]⟩, ⟨['S', 'c', 'h', 'w', 'e', 's', 't', 'e', 'r'], ['s', 'i', 's', 't', 'e', 'r'], [⟨['S', 'c', 'h', 'w', 'e', 's', 't', 'e', 'r'], ['s', 'i', 's', 't', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("coreference", "ihm = Peter"), ("remnant_case", "NOM")] }

def ch4_87b : Datum :=
  { id := "lechner2004_ch4_87b"
    source := ⟨"lechner-2004", "(87b) of chapter 4"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Er_i hat ihr mehr Leute vorgestellt als Peters_i Schwester."
    glossedTokens := [("Er", "he"), ("hat", "has"), ("ihr", "her"), ("mehr", "more"), ("Leute", "people"), ("vorgestellt", "introduced"), ("als", "than"), ("Peters", "Peter's"), ("Schwester", "sister")]
    glossedWords := [⟨['E', 'r'], ['h', 'e'], [⟨['E', 'r'], ['h', 'e'], none⟩]⟩, ⟨['h', 'a', 't'], ['h', 'a', 's'], [⟨['h', 'a', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['i', 'h', 'r'], ['h', 'e', 'r'], [⟨['i', 'h', 'r'], ['h', 'e', 'r'], none⟩]⟩, ⟨['m', 'e', 'h', 'r'], ['m', 'o', 'r', 'e'], [⟨['m', 'e', 'h', 'r'], ['m', 'o', 'r', 'e'], none⟩]⟩, ⟨['L', 'e', 'u', 't', 'e'], ['p', 'e', 'o', 'p', 'l', 'e'], [⟨['L', 'e', 'u', 't', 'e'], ['p', 'e', 'o', 'p', 'l', 'e'], none⟩]⟩, ⟨['v', 'o', 'r', 'g', 'e', 's', 't', 'e', 'l', 'l', 't'], ['i', 'n', 't', 'r', 'o', 'd', 'u', 'c', 'e', 'd'], [⟨['v', 'o', 'r', 'g', 'e', 's', 't', 'e', 'l', 'l', 't'], ['i', 'n', 't', 'r', 'o', 'd', 'u', 'c', 'e', 'd'], none⟩]⟩, ⟨['a', 'l', 's'], ['t', 'h', 'a', 'n'], [⟨['a', 'l', 's'], ['t', 'h', 'a', 'n'], none⟩]⟩, ⟨['P', 'e', 't', 'e', 'r', 's'], ['P', 'e', 't', 'e', 'r', '\'', 's'], [⟨['P', 'e', 't', 'e', 'r', 's'], ['P', 'e', 't', 'e', 'r', '\'', 's'], none⟩]⟩, ⟨['S', 'c', 'h', 'w', 'e', 's', 't', 'e', 'r'], ['s', 'i', 's', 't', 'e', 'r'], [⟨['S', 'c', 'h', 'w', 'e', 's', 't', 'e', 'r'], ['s', 'i', 's', 't', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("coreference", "er = Peter"), ("remnant_case", "DAT")] }

def ch4_90a : Datum :=
  { id := "lechner2004_ch4_90a"
    source := ⟨"lechner-2004", "(90a) of chapter 4"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Frau des Präsidenten_j schätzt die Öffentlichkeit mehr als ihn_j."
    glossedTokens := [("Die", "the"), ("Frau", "wife"), ("des", "of.the"), ("Präsidenten", "president"), ("schätzt", "appreciates"), ("die", "the"), ("Öffentlichkeit", "public"), ("mehr", "more"), ("als", "than"), ("ihn", "him")]
    glossedWords := [⟨['D', 'i', 'e'], ['t', 'h', 'e'], [⟨['D', 'i', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['F', 'r', 'a', 'u'], ['w', 'i', 'f', 'e'], [⟨['F', 'r', 'a', 'u'], ['w', 'i', 'f', 'e'], none⟩]⟩, ⟨['d', 'e', 's'], ['o', 'f', '.', 't', 'h', 'e'], [⟨['d', 'e', 's'], ['o', 'f', '.', 't', 'h', 'e'], none⟩]⟩, ⟨['P', 'r', 'ä', 's', 'i', 'd', 'e', 'n', 't', 'e', 'n'], ['p', 'r', 'e', 's', 'i', 'd', 'e', 'n', 't'], [⟨['P', 'r', 'ä', 's', 'i', 'd', 'e', 'n', 't', 'e', 'n'], ['p', 'r', 'e', 's', 'i', 'd', 'e', 'n', 't'], none⟩]⟩, ⟨['s', 'c', 'h', 'ä', 't', 'z', 't'], ['a', 'p', 'p', 'r', 'e', 'c', 'i', 'a', 't', 'e', 's'], [⟨['s', 'c', 'h', 'ä', 't', 'z', 't'], ['a', 'p', 'p', 'r', 'e', 'c', 'i', 'a', 't', 'e', 's'], none⟩]⟩, ⟨['d', 'i', 'e'], ['t', 'h', 'e'], [⟨['d', 'i', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['Ö', 'f', 'f', 'e', 'n', 't', 'l', 'i', 'c', 'h', 'k', 'e', 'i', 't'], ['p', 'u', 'b', 'l', 'i', 'c'], [⟨['Ö', 'f', 'f', 'e', 'n', 't', 'l', 'i', 'c', 'h', 'k', 'e', 'i', 't'], ['p', 'u', 'b', 'l', 'i', 'c'], none⟩]⟩, ⟨['m', 'e', 'h', 'r'], ['m', 'o', 'r', 'e'], [⟨['m', 'e', 'h', 'r'], ['m', 'o', 'r', 'e'], none⟩]⟩, ⟨['a', 'l', 's'], ['t', 'h', 'a', 'n'], [⟨['a', 'l', 's'], ['t', 'h', 'a', 'n'], none⟩]⟩, ⟨['i', 'h', 'n'], ['h', 'i', 'm'], [⟨['i', 'h', 'n'], ['h', 'i', 'm'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("coreference", "ihn = Präsident"), ("remnant_case", "ACC")] }

def ch4_91a : Datum :=
  { id := "lechner2004_ch4_91a"
    source := ⟨"lechner-2004", "(91a) of chapter 4"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Öffentlichkeit schätzt die Frau des Präsidenten_i mehr als er_i."
    glossedTokens := [("Die", "the"), ("Öffentlichkeit", "public"), ("schätzt", "appreciates"), ("die", "the"), ("Frau", "wife"), ("des", "of.the"), ("Präsidenten", "president"), ("mehr", "more"), ("als", "than"), ("er", "he")]
    glossedWords := [⟨['D', 'i', 'e'], ['t', 'h', 'e'], [⟨['D', 'i', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['Ö', 'f', 'f', 'e', 'n', 't', 'l', 'i', 'c', 'h', 'k', 'e', 'i', 't'], ['p', 'u', 'b', 'l', 'i', 'c'], [⟨['Ö', 'f', 'f', 'e', 'n', 't', 'l', 'i', 'c', 'h', 'k', 'e', 'i', 't'], ['p', 'u', 'b', 'l', 'i', 'c'], none⟩]⟩, ⟨['s', 'c', 'h', 'ä', 't', 'z', 't'], ['a', 'p', 'p', 'r', 'e', 'c', 'i', 'a', 't', 'e', 's'], [⟨['s', 'c', 'h', 'ä', 't', 'z', 't'], ['a', 'p', 'p', 'r', 'e', 'c', 'i', 'a', 't', 'e', 's'], none⟩]⟩, ⟨['d', 'i', 'e'], ['t', 'h', 'e'], [⟨['d', 'i', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['F', 'r', 'a', 'u'], ['w', 'i', 'f', 'e'], [⟨['F', 'r', 'a', 'u'], ['w', 'i', 'f', 'e'], none⟩]⟩, ⟨['d', 'e', 's'], ['o', 'f', '.', 't', 'h', 'e'], [⟨['d', 'e', 's'], ['o', 'f', '.', 't', 'h', 'e'], none⟩]⟩, ⟨['P', 'r', 'ä', 's', 'i', 'd', 'e', 'n', 't', 'e', 'n'], ['p', 'r', 'e', 's', 'i', 'd', 'e', 'n', 't'], [⟨['P', 'r', 'ä', 's', 'i', 'd', 'e', 'n', 't', 'e', 'n'], ['p', 'r', 'e', 's', 'i', 'd', 'e', 'n', 't'], none⟩]⟩, ⟨['m', 'e', 'h', 'r'], ['m', 'o', 'r', 'e'], [⟨['m', 'e', 'h', 'r'], ['m', 'o', 'r', 'e'], none⟩]⟩, ⟨['a', 'l', 's'], ['t', 'h', 'a', 'n'], [⟨['a', 'l', 's'], ['t', 'h', 'a', 'n'], none⟩]⟩, ⟨['e', 'r'], ['h', 'e'], [⟨['e', 'r'], ['h', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("coreference", "er = Präsident"), ("remnant_case", "NOM")] }

def all : List Datum := [ch2_24, ch2_25, ch4_83a, ch4_85a, ch4_87a, ch4_87b, ch4_90a, ch4_91a]

end Lechner2004.Examples
