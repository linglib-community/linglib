module

public import Linglib.Data.Examples.Schema

/-!
# `Elbourne2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Elbourne2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Elbourne2026.Examples`.
-/

@[expose] public section

namespace Elbourne2026.Examples

def ex_14 : Datum :=
  { id := "elbourne2026_14"
    source := ⟨"elbourne-2026", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every woman inspected some donkey."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("surface scope", .acceptable), ("inverse scope", .acceptable)]
    paperFeatures := [("section", "2.3")] }

def ex_28 : Datum :=
  { id := "elbourne2026_28"
    source := ⟨"elbourne-2026", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fido was cute."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2")] }

def ex_31 : Datum :=
  { id := "elbourne2026_31"
    source := ⟨"elbourne-2026", "(31)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fido is a dog."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2")] }

def ex_36 : Datum :=
  { id := "elbourne2026_36"
    source := ⟨"elbourne-2026", "(36)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Joe is a former."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2")] }

def ex_37 : Datum :=
  { id := "elbourne2026_37"
    source := ⟨"elbourne-2026", "(37)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every red is attractive."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2")] }

def ex_42 : Datum :=
  { id := "elbourne2026_42"
    source := ⟨"elbourne-2026", "(42)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The president is former."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2")] }

def ex_43 : Datum :=
  { id := "elbourne2026_43"
    source := ⟨"beesley-1982", "p. 202"⟩
    reportedIn := some ⟨"elbourne-2026", "(43)"⟩
    language := "stan1293"
    primaryText := "Q: Which of the men over there is Quang? A: Quang is the short Vietnamese."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("short by the standard of men", .acceptable)]
    paperFeatures := [("section", "3.3")] }

def ex_45 : Datum :=
  { id := "elbourne2026_45"
    source := ⟨"elbourne-2026", "(45)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John was a former judge."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4")] }

def ex_47 : Datum :=
  { id := "elbourne2026_47"
    source := ⟨"elbourne-2026", "(47)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John visited a local bar."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("local to John", .acceptable)]
    paperFeatures := [("section", "3.5")] }

def ex_48 : Datum :=
  { id := "elbourne2026_48"
    source := ⟨"elbourne-2026", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every sports fan in the country was at a local bar watching the playoffs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("local to each fan", .acceptable)]
    paperFeatures := [("section", "3.5")] }

def ex_49 : Datum :=
  { id := "elbourne2026_49"
    source := ⟨"elbourne-2026", "(49)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I need to find a plumber local to Westchester."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.5")] }

def ex_55 : Datum :=
  { id := "elbourne2026_55"
    source := ⟨"elbourne-2026", "(55)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone entered a local bar."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("local to each person", .acceptable)]
    paperFeatures := [("section", "3.5")] }

def ex_64_long : Datum :=
  { id := "elbourne2026_64_long"
    source := ⟨"morzycki-2015", "ch. 2, (48)"⟩
    reportedIn := some ⟨"elbourne-2026", "(64)"⟩
    method := some .description
    language := "russ1263"
    primaryText := "Zimnie noči budut dolgimi."
    glossedTokens := [("Zimnie", "winter"), ("noči", "nights"), ("budut", "will.be"), ("dolgimi", "long-LONG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2")] }

def ex_64_short : Datum :=
  { id := "elbourne2026_64_short"
    source := ⟨"morzycki-2015", "ch. 2, (48)"⟩
    reportedIn := some ⟨"elbourne-2026", "(64)"⟩
    method := some .description
    language := "russ1263"
    primaryText := "Zimnie noči budut dolgi."
    glossedTokens := [("Zimnie", "winter"), ("noči", "nights"), ("budut", "will.be"), ("dolgi", "long-SHORT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2")] }

def ex_65a : Datum :=
  { id := "elbourne2026_65a"
    source := ⟨"morzycki-2015", "ch. 2, (46a)"⟩
    reportedIn := some ⟨"elbourne-2026", "(65a)"⟩
    method := some .description
    language := "russ1263"
    primaryText := "xorošaja teorija"
    glossedTokens := [("xorošaja", "good-LONG"), ("teorija", "theory")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2")] }

def ex_65b : Datum :=
  { id := "elbourne2026_65b"
    source := ⟨"morzycki-2015", "ch. 2, (46b)"⟩
    reportedIn := some ⟨"elbourne-2026", "(65b)"⟩
    method := some .description
    language := "russ1263"
    primaryText := "xoroša teorija"
    glossedTokens := [("xoroša", "good-SHORT"), ("teorija", "theory")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2")] }

def ex_82 : Datum :=
  { id := "elbourne2026_82"
    source := ⟨"mcnally-boleda-2004", "p. 180"⟩
    reportedIn := some ⟨"elbourne-2026", "(82)"⟩
    language := "stan1293"
    primaryText := "Olga is a beautiful dancer."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("dances beautifully", .acceptable), ("Olga is beautiful", .acceptable)]
    paperFeatures := [("section", "4.4")] }

def ex_83 : Datum :=
  { id := "elbourne2026_83"
    source := ⟨"mcnally-boleda-2004", "p. 180"⟩
    reportedIn := some ⟨"elbourne-2026", "(83)"⟩
    language := "stan1293"
    primaryText := "Look at Olga dance—she's beautiful!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("Olga is beautiful", .acceptable)]
    paperFeatures := [("section", "4.4")] }

def ex_92a : Datum :=
  { id := "elbourne2026_92a"
    source := ⟨"mcnally-boleda-2004", "p. 186"⟩
    reportedIn := some ⟨"elbourne-2026", "(92a)"⟩
    language := "stan1289"
    primaryText := "jove presumpte assassí"
    glossedTokens := [("jove", "young"), ("presumpte", "alleged"), ("assassí", "murderer")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("speaker committed to the person's youth", .acceptable)]
    paperFeatures := [("section", "4.4")] }

def ex_92b : Datum :=
  { id := "elbourne2026_92b"
    source := ⟨"mcnally-boleda-2004", "p. 186"⟩
    reportedIn := some ⟨"elbourne-2026", "(92b)"⟩
    language := "stan1289"
    primaryText := "presumpte jove assassí"
    glossedTokens := [("presumpte", "alleged"), ("jove", "young"), ("assassí", "murderer")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("youth part of the allegation", .acceptable)]
    paperFeatures := [("section", "4.4")] }

def ex_93 : Datum :=
  { id := "elbourne2026_93"
    source := ⟨"bolinger-1967", "p. 4"⟩
    reportedIn := some ⟨"elbourne-2026", "(93)"⟩
    language := "stan1293"
    primaryText := "The visible stars were Aldebaran and Sirius."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inherently visible", .acceptable), ("visible on the occasion", .acceptable)]
    paperFeatures := [("section", "4.5")] }

def ex_94 : Datum :=
  { id := "elbourne2026_94"
    source := ⟨"bolinger-1967", "p. 4"⟩
    reportedIn := some ⟨"elbourne-2026", "(94)"⟩
    language := "stan1293"
    primaryText := "The stars visible were Aldebaran and Sirius."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inherently visible", .unacceptable), ("visible on the occasion", .acceptable)]
    paperFeatures := [("section", "4.5")] }

def ex_101 : Datum :=
  { id := "elbourne2026_101"
    source := ⟨"elbourne-2026", "(101)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is very dead."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.6")] }

def ex_105 : Datum :=
  { id := "elbourne2026_105"
    source := ⟨"elbourne-2026", "(105)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "excellent small brown cardboard box"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("cardboard brown small excellent box", .questionable)]
    readings := []
    paperFeatures := [("section", "5")] }

def all : List Datum := [ex_14, ex_28, ex_31, ex_36, ex_37, ex_42, ex_43, ex_45, ex_47, ex_48, ex_49, ex_55, ex_64_long, ex_64_short, ex_65a, ex_65b, ex_82, ex_83, ex_92a, ex_92b, ex_93, ex_94, ex_101, ex_105]

end Elbourne2026.Examples
