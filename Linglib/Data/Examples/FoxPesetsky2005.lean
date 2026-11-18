module

public import Linglib.Data.Examples.Schema

/-!
# `FoxPesetsky2005` — typed example data

Auto-generated from `Linglib/Data/Examples/FoxPesetsky2005.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace FoxPesetsky2005.Examples`.
-/

@[expose] public section

namespace FoxPesetsky2005.Examples

def ex19a : Datum :=
  { id := "foxpesetsky2005_ex19a"
    source := ⟨"fox-pesetsky-2005", "(19a)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Jag kysste henne inte"
    glossedTokens := [("Jag", "I"), ("kysste", "kissed"), ("henne", "her"), ("inte", "not")]
    glossedWords := [⟨['J', 'a', 'g'], ['I'], [⟨['J', 'a', 'g'], ['I'], none⟩]⟩, ⟨['k', 'y', 's', 's', 't', 'e'], ['k', 'i', 's', 's', 'e', 'd'], [⟨['k', 'y', 's', 's', 't', 'e'], ['k', 'i', 's', 's', 'e', 'd'], none⟩]⟩, ⟨['h', 'e', 'n', 'n', 'e'], ['h', 'e', 'r'], [⟨['h', 'e', 'n', 'n', 'e'], ['h', 'e', 'r'], none⟩]⟩, ⟨['i', 'n', 't', 'e'], ['n', 'o', 't'], [⟨['i', 'n', 't', 'e'], ['n', 'o', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("sketch", "verbToC"), ("intervener", "none")] }

def ex19b : Datum :=
  { id := "foxpesetsky2005_ex19b"
    source := ⟨"fox-pesetsky-2005", "(19b)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "att jag henne inte kysste"
    glossedTokens := [("att", "that"), ("jag", "I"), ("henne", "her"), ("inte", "not"), ("kysste", "kissed")]
    glossedWords := [⟨['a', 't', 't'], ['t', 'h', 'a', 't'], [⟨['a', 't', 't'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['j', 'a', 'g'], ['I'], [⟨['j', 'a', 'g'], ['I'], none⟩]⟩, ⟨['h', 'e', 'n', 'n', 'e'], ['h', 'e', 'r'], [⟨['h', 'e', 'n', 'n', 'e'], ['h', 'e', 'r'], none⟩]⟩, ⟨['i', 'n', 't', 'e'], ['n', 'o', 't'], [⟨['i', 'n', 't', 'e'], ['n', 'o', 't'], none⟩]⟩, ⟨['k', 'y', 's', 's', 't', 'e'], ['k', 'i', 's', 's', 'e', 'd'], [⟨['k', 'y', 's', 's', 't', 'e'], ['k', 'i', 's', 's', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("sketch", "embedded"), ("intervener", "none")] }

def ex19c : Datum :=
  { id := "foxpesetsky2005_ex19c"
    source := ⟨"fox-pesetsky-2005", "(19c)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Jag har henne inte kysst"
    glossedTokens := [("Jag", "I"), ("har", "have"), ("henne", "her"), ("inte", "not"), ("kysst", "kissed")]
    glossedWords := [⟨['J', 'a', 'g'], ['I'], [⟨['J', 'a', 'g'], ['I'], none⟩]⟩, ⟨['h', 'a', 'r'], ['h', 'a', 'v', 'e'], [⟨['h', 'a', 'r'], ['h', 'a', 'v', 'e'], none⟩]⟩, ⟨['h', 'e', 'n', 'n', 'e'], ['h', 'e', 'r'], [⟨['h', 'e', 'n', 'n', 'e'], ['h', 'e', 'r'], none⟩]⟩, ⟨['i', 'n', 't', 'e'], ['n', 'o', 't'], [⟨['i', 'n', 't', 'e'], ['n', 'o', 't'], none⟩]⟩, ⟨['k', 'y', 's', 's', 't'], ['k', 'i', 's', 's', 'e', 'd'], [⟨['k', 'y', 's', 's', 't'], ['k', 'i', 's', 's', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("sketch", "auxiliary"), ("intervener", "none")] }

def ex23a : Datum :=
  { id := "foxpesetsky2005_ex23a"
    source := ⟨"fox-pesetsky-2005", "(23a)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Jag gav den inte Elsa"
    glossedTokens := [("Jag", "I"), ("gav", "gave"), ("den", "it"), ("inte", "not"), ("Elsa", "Elsa")]
    glossedWords := [⟨['J', 'a', 'g'], ['I'], [⟨['J', 'a', 'g'], ['I'], none⟩]⟩, ⟨['g', 'a', 'v'], ['g', 'a', 'v', 'e'], [⟨['g', 'a', 'v'], ['g', 'a', 'v', 'e'], none⟩]⟩, ⟨['d', 'e', 'n'], ['i', 't'], [⟨['d', 'e', 'n'], ['i', 't'], none⟩]⟩, ⟨['i', 'n', 't', 'e'], ['n', 'o', 't'], [⟨['i', 'n', 't', 'e'], ['n', 'o', 't'], none⟩]⟩, ⟨['E', 'l', 's', 'a'], ['E', 'l', 's', 'a'], [⟨['E', 'l', 's', 'a'], ['E', 'l', 's', 'a'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("sketch", "intervener"), ("intervener", "firstObject")] }

def ex23b : Datum :=
  { id := "foxpesetsky2005_ex23b"
    source := ⟨"fox-pesetsky-2005", "(23b)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Dom kastade mej inte ut"
    glossedTokens := [("Dom", "they"), ("kastade", "threw"), ("mej", "me"), ("inte", "not"), ("ut", "out")]
    glossedWords := [⟨['D', 'o', 'm'], ['t', 'h', 'e', 'y'], [⟨['D', 'o', 'm'], ['t', 'h', 'e', 'y'], none⟩]⟩, ⟨['k', 'a', 's', 't', 'a', 'd', 'e'], ['t', 'h', 'r', 'e', 'w'], [⟨['k', 'a', 's', 't', 'a', 'd', 'e'], ['t', 'h', 'r', 'e', 'w'], none⟩]⟩, ⟨['m', 'e', 'j'], ['m', 'e'], [⟨['m', 'e', 'j'], ['m', 'e'], none⟩]⟩, ⟨['i', 'n', 't', 'e'], ['n', 'o', 't'], [⟨['i', 'n', 't', 'e'], ['n', 'o', 't'], none⟩]⟩, ⟨['u', 't'], ['o', 'u', 't'], [⟨['u', 't'], ['o', 'u', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("sketch", "intervener"), ("intervener", "particle")] }

def ex25a : Datum :=
  { id := "foxpesetsky2005_ex25a"
    source := ⟨"fox-pesetsky-2005", "(25a)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Vem gav du den inte"
    glossedTokens := [("Vem", "who"), ("gav", "gave"), ("du", "you"), ("den", "it"), ("inte", "not")]
    glossedWords := [⟨['V', 'e', 'm'], ['w', 'h', 'o'], [⟨['V', 'e', 'm'], ['w', 'h', 'o'], none⟩]⟩, ⟨['g', 'a', 'v'], ['g', 'a', 'v', 'e'], [⟨['g', 'a', 'v'], ['g', 'a', 'v', 'e'], none⟩]⟩, ⟨['d', 'u'], ['y', 'o', 'u'], [⟨['d', 'u'], ['y', 'o', 'u'], none⟩]⟩, ⟨['d', 'e', 'n'], ['i', 't'], [⟨['d', 'e', 'n'], ['i', 't'], none⟩]⟩, ⟨['i', 'n', 't', 'e'], ['n', 'o', 't'], [⟨['i', 'n', 't', 'e'], ['n', 'o', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("sketch", "intervenerFronted"), ("intervener", "firstObject")] }

def ex25b : Datum :=
  { id := "foxpesetsky2005_ex25b"
    source := ⟨"fox-pesetsky-2005", "(25b)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Ut kastade dom mej inte"
    glossedTokens := [("Ut", "out"), ("kastade", "threw"), ("dom", "they"), ("mej", "me"), ("inte", "not")]
    glossedWords := [⟨['U', 't'], ['o', 'u', 't'], [⟨['U', 't'], ['o', 'u', 't'], none⟩]⟩, ⟨['k', 'a', 's', 't', 'a', 'd', 'e'], ['t', 'h', 'r', 'e', 'w'], [⟨['k', 'a', 's', 't', 'a', 'd', 'e'], ['t', 'h', 'r', 'e', 'w'], none⟩]⟩, ⟨['d', 'o', 'm'], ['t', 'h', 'e', 'y'], [⟨['d', 'o', 'm'], ['t', 'h', 'e', 'y'], none⟩]⟩, ⟨['m', 'e', 'j'], ['m', 'e'], [⟨['m', 'e', 'j'], ['m', 'e'], none⟩]⟩, ⟨['i', 'n', 't', 'e'], ['n', 'o', 't'], [⟨['i', 'n', 't', 'e'], ['n', 'o', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("sketch", "intervenerFronted"), ("intervener", "particle")] }

def all : List Datum := [ex19a, ex19b, ex19c, ex23a, ex23b, ex25a, ex25b]

end FoxPesetsky2005.Examples
