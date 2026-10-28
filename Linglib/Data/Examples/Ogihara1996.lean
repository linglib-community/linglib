module

public import Linglib.Data.Examples.Schema

/-!
# `Ogihara1996` — typed example data

Auto-generated from `Linglib/Data/Examples/Ogihara1996.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Ogihara1996.Examples`.
-/

@[expose] public section

namespace Ogihara1996.Examples

def ex2a : Datum :=
  { id := "ogihara1996_ex2a"
    source := ⟨"ogihara-1996", "ch. 3, (2a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-wa Hanako-ga byooki-da-to it-ta."
    glossedTokens := [("Taroo-wa", "Taro-TOP"), ("Hanako-ga", "Hanako-NOM"), ("byooki-da", "be-sick-PRES"), ("-to", "that"), ("it-ta", "say-PAST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .acceptable), ("shifted", .unacceptable)]
    paperFeatures := [("tense", "ta"), ("tense", "ru")] }

def ex2b : Datum :=
  { id := "ogihara1996_ex2b"
    source := ⟨"ogihara-1996", "ch. 3, (2b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-wa Hanako-ga byookidat-ta-to it-ta."
    glossedTokens := [("Taroo-wa", "Taro-TOP"), ("Hanako-ga", "Hanako-NOM"), ("byookidat-ta", "be-sick-PAST"), ("-to", "that"), ("it-ta", "say-PAST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .unacceptable), ("shifted", .acceptable)]
    paperFeatures := [("tense", "ta"), ("tense", "ta")] }

def ex19d : Datum :=
  { id := "ogihara1996_ex19d"
    source := ⟨"ogihara-1996", "ch. 1, (19d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He said that Mary had been reading books yesterday."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("shifted", .acceptable)]
    paperFeatures := [("tense", "ed"), ("tense", "ed"), ("tense", "perfect")] }

def ex10a : Datum :=
  { id := "ogihara1996_ex10a"
    source := ⟨"ogihara-1996", "ch. 1, (10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John said that Mary was in Seattle."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .acceptable), ("shifted", .acceptable)]
    paperFeatures := [("tense", "ed"), ("tense", "ed")] }

def ex10b : Datum :=
  { id := "ogihara1996_ex10b"
    source := ⟨"ogihara-1996", "ch. 1, (10b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-wa Hanako-ga Siatoru-ni i-ru to it-ta."
    glossedTokens := [("Taroo-wa", "Taro-TOP"), ("Hanako-ga", "Hanako-NOM"), ("Siatoru-ni", "Seattle-in"), ("i-ru", "be-PRES"), ("to", "that"), ("it-ta", "say-PAST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .acceptable), ("shifted", .unacceptable)]
    paperFeatures := [("tense", "ta"), ("tense", "ru")] }

def ex4_9a : Datum :=
  { id := "ogihara1996_ex4_9a"
    source := ⟨"ogihara-1996", "ch. 4, (9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John said that Mary will claim that she was sick."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .unacceptable), ("shifted", .acceptable)]
    paperFeatures := [("tense", "woll"), ("tense", "ed")] }

def all : List Datum := [ex2a, ex2b, ex19d, ex10a, ex10b, ex4_9a]

end Ogihara1996.Examples
