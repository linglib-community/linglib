module

public import Linglib.Data.Examples.Schema

/-!
# `KnickSharf2026` — typed example data

Auto-generated from `Linglib/Data/Examples/KnickSharf2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace KnickSharf2026.Examples`.
-/

@[expose] public section

namespace KnickSharf2026.Examples

def ex_5 : Datum :=
  { id := "knicksharf2026_5"
    source := ⟨"knick-sharf-2026", "(5)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "How is Ursula? Ursula has been happy ever since Monday, but she's not anymore."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("reading", "universal"), ("adverbial", "ever since Monday")] }

def ex_6 : Datum :=
  { id := "knicksharf2026_6"
    source := ⟨"knick-sharf-2026", "(6)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "How is Ursula? Ursula has been happy, but she's not anymore."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("reading", "experiential")] }

def ex_8a : Datum :=
  { id := "knicksharf2026_8a"
    source := ⟨"knick-sharf-2026", "(8a)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "Louis has been crying, but he's not anymore."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("reading", "experiential")] }

def ex_8b : Datum :=
  { id := "knicksharf2026_8b"
    source := ⟨"knick-sharf-2026", "(8b)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "Louis has been crying ever since this morning, but he's not anymore."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("reading", "universal"), ("adverbial", "ever since this morning")] }

def ex_10 : Datum :=
  { id := "knicksharf2026_10"
    source := ⟨"knick-sharf-2026", "(10)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "Sadie is sick right now. Sadie has been sick, but she's not anymore."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("reading", "universal"), ("focus", "been")] }

def ex_12 : Datum :=
  { id := "knicksharf2026_12"
    source := ⟨"knick-sharf-2026", "(12)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "How is Sadie? Well, she has been sick, but she isn't anymore."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("reading", "experiential")] }

def all : List Datum := [ex_5, ex_6, ex_8a, ex_8b, ex_10, ex_12]

end KnickSharf2026.Examples
