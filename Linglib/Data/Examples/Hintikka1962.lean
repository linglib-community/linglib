module

public import Linglib.Data.Examples.Schema

/-!
# `Hintikka1962` — typed example data

Auto-generated from `Linglib/Data/Examples/Hintikka1962.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Hintikka1962.Examples`.
-/

@[expose] public section

namespace Hintikka1962.Examples

def s8 : Datum :=
  { id := "hintikka1962_s8"
    source := ⟨"hintikka-1962", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "p but I do not believe that p."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.5")] }

def s9 : Datum :=
  { id := "hintikka1962_s9"
    source := ⟨"hintikka-1962", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "p but I do not know whether p."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.11")] }

def s28 : Datum :=
  { id := "hintikka1962_s28"
    source := ⟨"hintikka-1962", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "p but he does not believe that p."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.5")] }

def s29 : Datum :=
  { id := "hintikka1962_s29"
    source := ⟨"hintikka-1962", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He was at home but I did not believe it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.5")] }

def s30 : Datum :=
  { id := "hintikka1962_s30"
    source := ⟨"hintikka-1962", "(30)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I believe that the case is as follows: p but I do not believe that p."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.6")] }

def s30a : Datum :=
  { id := "hintikka1962_s30a"
    source := ⟨"hintikka-1962", "(30)(a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I believe that the case is as follows: p but a does not believe that p."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.6")] }

def s40 : Datum :=
  { id := "hintikka1962_s40"
    source := ⟨"hintikka-1962", "(40)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I know that the case is as follows: p but I do not know whether p."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.11")] }

def s42 : Datum :=
  { id := "hintikka1962_s42"
    source := ⟨"hintikka-1962", "(42)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He knows that p but I don't know it."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.13")] }

def s43 : Datum :=
  { id := "hintikka1962_s43"
    source := ⟨"hintikka-1962", "(43)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He knows whether p although I don't."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.13")] }

def s46 : Datum :=
  { id := "hintikka1962_s46"
    source := ⟨"hintikka-1962", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I believe that p but that I do not know whether p."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.14")] }

def s47 : Datum :=
  { id := "hintikka1962_s47"
    source := ⟨"hintikka-1962", "(47)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I believe that p but I do not know it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.14")] }

def s49 : Datum :=
  { id := "hintikka1962_s49"
    source := ⟨"hintikka-1962", "(49)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I believe that p but I do not know that I believe it."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.15")] }

def s51 : Datum :=
  { id := "hintikka1962_s51"
    source := ⟨"hintikka-1962", "(51)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I believe that p but I may be mistaken."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.16")] }

def s52 : Datum :=
  { id := "hintikka1962_s52"
    source := ⟨"hintikka-1962", "(52)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "p but you do not know that p."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.17")] }

def prize : Datum :=
  { id := "hintikka1962_prize"
    source := ⟨"hintikka-1962", "Section 4.17"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You don't know it but your essay has won the prize."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.17")] }

def s55 : Datum :=
  { id := "hintikka1962_s55"
    source := ⟨"hintikka-1962", "(55)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "God is almighty although I don't know that He is."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.21")] }

def s56 : Datum :=
  { id := "hintikka1962_s56"
    source := ⟨"hintikka-1962", "(56)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Phosphorus melts at 44°C. but I do not know that it does."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.21")] }

def s57 : Datum :=
  { id := "hintikka1962_s57"
    source := ⟨"hintikka-1962", "(57)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "p but I don't KNOW that p."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.21")] }

def s58 : Datum :=
  { id := "hintikka1962_s58"
    source := ⟨"hintikka-1962", "(58)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "p but I cannot believe that p."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.21")] }

def s59 : Datum :=
  { id := "hintikka1962_s59"
    source := ⟨"hintikka-1962", "(59)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "September is here already. I cannot believe it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.21")] }

def s60 : Datum :=
  { id := "hintikka1962_s60"
    source := ⟨"hintikka-1962", "(60)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I know that I know that p."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1")] }

def s61 : Datum :=
  { id := "hintikka1962_s61"
    source := ⟨"hintikka-1962", "(61)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He knows that I know that p."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1")] }

def s62 : Datum :=
  { id := "hintikka1962_s62"
    source := ⟨"hintikka-1962", "(62)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I know that p."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.2")] }

def s70 : Datum :=
  { id := "hintikka1962_s70"
    source := ⟨"hintikka-1962", "(70)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "a knows that p but he does not know that he knows."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.5")] }

def s71 : Datum :=
  { id := "hintikka1962_s71"
    source := ⟨"hintikka-1962", "(71)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I know that p but I do not know that I know."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.5")] }

def all : List Datum := [s8, s9, s28, s29, s30, s30a, s40, s42, s43, s46, s47, s49, s51, s52, prize, s55, s56, s57, s58, s59, s60, s61, s62, s70, s71]

end Hintikka1962.Examples
