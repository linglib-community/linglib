module

public import Linglib.Data.Examples.Schema

/-!
# `BroekhuisCorver2026` — typed example data

Auto-generated from `Linglib/Data/Examples/BroekhuisCorver2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BroekhuisCorver2026.Examples`.
-/

@[expose] public section

namespace BroekhuisCorver2026.Examples

def ex_26c : Datum :=
  { id := "broekhuiscorver2026_26c"
    source := ⟨"broekhuis-corver-2026a", "(26c), p. 9"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "De wandeling er op duurde 10 uur."
    glossedTokens := [("De", "the"), ("wandeling", "hike"), ("er", "there"), ("op", "on"), ("duurde", "lasted"), ("10", "10"), ("uur", "hour")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("on it", .acceptable), ("up it", .unacceptable)]
    paperFeatures := [] }

def ex_56b : Datum :=
  { id := "broekhuiscorver2026_56b"
    source := ⟨"broekhuis-corver-2026a", "(56b), p. 20"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Het café staat daar vaak pal naast."
    glossedTokens := [("Het", "the"), ("café", "café"), ("staat", "stands"), ("daar", "there"), ("vaak", "often"), ("pal", "right"), ("naast", "next.to")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_57b : Datum :=
  { id := "broekhuiscorver2026_57b"
    source := ⟨"broekhuis-corver-2026a", "(57b), p. 20"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "De luchtballon hangt er nu hoog boven."
    glossedTokens := [("De", "the"), ("luchtballon", "balloon"), ("hangt", "hangs"), ("er", "there"), ("nu", "now"), ("hoog", "high"), ("boven", "above")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_58b : Datum :=
  { id := "broekhuiscorver2026_58b"
    source := ⟨"broekhuis-corver-2026a", "(58b), p. 20"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Marie gaat het bos nooit alleen in."
    glossedTokens := [("Marie", "Marie"), ("gaat", "goes"), ("het", "the"), ("bos", "woods"), ("nooit", "never"), ("alleen", "alone"), ("in", "into")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_58c : Datum :=
  { id := "broekhuiscorver2026_58c"
    source := ⟨"broekhuis-corver-2026a", "(58c), p. 20"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "het bos dat Marie nooit alleen in gaat"
    glossedTokens := [("het", "the"), ("bos", "forest"), ("dat", "that"), ("Marie", "Marie"), ("nooit", "never"), ("alleen", "alone"), ("in", "into"), ("gaat", "goes")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_59b_daar : Datum :=
  { id := "broekhuiscorver2026_59b_daar"
    source := ⟨"broekhuis-corver-2026a", "(59b), p. 21"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Jan is daar gisteren van af gesprongen."
    glossedTokens := [("Jan", "Jan"), ("is", "is"), ("daar", "there"), ("gisteren", "yesterday"), ("van", "from"), ("af", "AF"), ("gesprongen", "jumped")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_59b_dak : Datum :=
  { id := "broekhuiscorver2026_59b_dak"
    source := ⟨"broekhuis-corver-2026a", "(59b), p. 21"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Jan is het dak gisteren van af gesprongen."
    glossedTokens := [("Jan", "Jan"), ("is", "is"), ("het", "the"), ("dak", "roof"), ("gisteren", "yesterday"), ("van", "from"), ("af", "AF"), ("gesprongen", "jumped")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_59c_waar : Datum :=
  { id := "broekhuiscorver2026_59c_waar"
    source := ⟨"broekhuis-corver-2026a", "(59c), p. 21"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Waar is Jan van af gesprongen?"
    glossedTokens := [("Waar", "where"), ("is", "is"), ("Jan", "Jan"), ("van", "from"), ("af", "AF"), ("gesprongen", "jumped")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_59c_dak : Datum :=
  { id := "broekhuiscorver2026_59c_dak"
    source := ⟨"broekhuis-corver-2026a", "(59c), p. 21"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Welk dak is Jan van af gesprongen?"
    glossedTokens := [("Welk", "which"), ("dak", "roof"), ("is", "is"), ("Jan", "Jan"), ("van", "from"), ("af", "AF"), ("gesprongen", "jumped")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex_26c, ex_56b, ex_57b, ex_58b, ex_58c, ex_59b_daar, ex_59b_dak, ex_59c_waar, ex_59c_dak]

end BroekhuisCorver2026.Examples
