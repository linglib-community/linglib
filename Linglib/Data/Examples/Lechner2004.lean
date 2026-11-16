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
    glossedWords := [⟨[['S', 'i', 'e']], [['s', 'h', 'e']]⟩, ⟨[['h', 'a', 't']], [['h', 'a', 's']]⟩, ⟨[['i', 'h', 'm']], [['h', 'i', 'm']]⟩, ⟨[['m', 'e', 'h', 'r']], [['m', 'o', 'r', 'e']]⟩, ⟨[['L', 'e', 'u', 't', 'e']], [['p', 'e', 'o', 'p', 'l', 'e']]⟩, ⟨[['v', 'o', 'r', 'g', 'e', 's', 't', 'e', 'l', 'l', 't']], [['i', 'n', 't', 'r', 'o', 'd', 'u', 'c', 'e', 'd']]⟩, ⟨[['a', 'l', 's']], [['t', 'h', 'a', 'n']]⟩, ⟨[['P', 'e', 't', 'e', 'r', 's']], [['P', 'e', 't', 'e', 'r', '\'', 's']]⟩, ⟨[['S', 'c', 'h', 'w', 'e', 's', 't', 'e', 'r']], [['s', 'i', 's', 't', 'e', 'r']]⟩]
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
    glossedWords := [⟨[['E', 'r']], [['h', 'e']]⟩, ⟨[['h', 'a', 't']], [['h', 'a', 's']]⟩, ⟨[['i', 'h', 'r']], [['h', 'e', 'r']]⟩, ⟨[['m', 'e', 'h', 'r']], [['m', 'o', 'r', 'e']]⟩, ⟨[['L', 'e', 'u', 't', 'e']], [['p', 'e', 'o', 'p', 'l', 'e']]⟩, ⟨[['v', 'o', 'r', 'g', 'e', 's', 't', 'e', 'l', 'l', 't']], [['i', 'n', 't', 'r', 'o', 'd', 'u', 'c', 'e', 'd']]⟩, ⟨[['a', 'l', 's']], [['t', 'h', 'a', 'n']]⟩, ⟨[['P', 'e', 't', 'e', 'r', 's']], [['P', 'e', 't', 'e', 'r', '\'', 's']]⟩, ⟨[['S', 'c', 'h', 'w', 'e', 's', 't', 'e', 'r']], [['s', 'i', 's', 't', 'e', 'r']]⟩]
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
    glossedWords := [⟨[['D', 'i', 'e']], [['t', 'h', 'e']]⟩, ⟨[['F', 'r', 'a', 'u']], [['w', 'i', 'f', 'e']]⟩, ⟨[['d', 'e', 's']], [['o', 'f', '.', 't', 'h', 'e']]⟩, ⟨[['P', 'r', 'ä', 's', 'i', 'd', 'e', 'n', 't', 'e', 'n']], [['p', 'r', 'e', 's', 'i', 'd', 'e', 'n', 't']]⟩, ⟨[['s', 'c', 'h', 'ä', 't', 'z', 't']], [['a', 'p', 'p', 'r', 'e', 'c', 'i', 'a', 't', 'e', 's']]⟩, ⟨[['d', 'i', 'e']], [['t', 'h', 'e']]⟩, ⟨[['Ö', 'f', 'f', 'e', 'n', 't', 'l', 'i', 'c', 'h', 'k', 'e', 'i', 't']], [['p', 'u', 'b', 'l', 'i', 'c']]⟩, ⟨[['m', 'e', 'h', 'r']], [['m', 'o', 'r', 'e']]⟩, ⟨[['a', 'l', 's']], [['t', 'h', 'a', 'n']]⟩, ⟨[['i', 'h', 'n']], [['h', 'i', 'm']]⟩]
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
    glossedWords := [⟨[['D', 'i', 'e']], [['t', 'h', 'e']]⟩, ⟨[['Ö', 'f', 'f', 'e', 'n', 't', 'l', 'i', 'c', 'h', 'k', 'e', 'i', 't']], [['p', 'u', 'b', 'l', 'i', 'c']]⟩, ⟨[['s', 'c', 'h', 'ä', 't', 'z', 't']], [['a', 'p', 'p', 'r', 'e', 'c', 'i', 'a', 't', 'e', 's']]⟩, ⟨[['d', 'i', 'e']], [['t', 'h', 'e']]⟩, ⟨[['F', 'r', 'a', 'u']], [['w', 'i', 'f', 'e']]⟩, ⟨[['d', 'e', 's']], [['o', 'f', '.', 't', 'h', 'e']]⟩, ⟨[['P', 'r', 'ä', 's', 'i', 'd', 'e', 'n', 't', 'e', 'n']], [['p', 'r', 'e', 's', 'i', 'd', 'e', 'n', 't']]⟩, ⟨[['m', 'e', 'h', 'r']], [['m', 'o', 'r', 'e']]⟩, ⟨[['a', 'l', 's']], [['t', 'h', 'a', 'n']]⟩, ⟨[['e', 'r']], [['h', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("coreference", "er = Präsident"), ("remnant_case", "NOM")] }

def all : List Datum := [ch2_24, ch2_25, ch4_83a, ch4_85a, ch4_87a, ch4_87b, ch4_90a, ch4_91a]

end Lechner2004.Examples
