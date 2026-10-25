module

public import Linglib.Data.Examples.Schema

/-!
# `HoleFraser2026` — typed example data

Auto-generated from `Linglib/Data/Examples/HoleFraser2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HoleFraser2026.Examples`.
-/

@[expose] public section

namespace HoleFraser2026.Examples

def ex_17 : Datum :=
  { id := "holefraser2026_17"
    source := ⟨"hole-fraser-2026", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The pool is swimming with turtles. No, that's not true. There are just a few turtles."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("content", "abundance"), ("response", "denial")] }

def ex_18 : Datum :=
  { id := "holefraser2026_18"
    source := ⟨"hole-fraser-2026", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The metro is crawling with rats. No, that's not true. There are just a few rats."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("content", "abundance"), ("response", "denial")] }

def ex_19 : Datum :=
  { id := "holefraser2026_19"
    source := ⟨"hole-fraser-2026", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The sky is glittering with stars. No, that's not true. There are just a few stars."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("content", "abundance"), ("response", "denial")] }

def ex_30b : Datum :=
  { id := "holefraser2026_30b"
    source := ⟨"hole-fraser-2026", "(30b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Teich schwamm heute vor Fischen!"
    glossedTokens := []
    context := "There are normally a few fish swimming in the pond."
    judgment := .acceptable
    alternatives := [("Der Teich schwamm heute nur so vor Fischen!", .acceptable)]
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("diagnostic", "nur so")] }

def ex_31b : Datum :=
  { id := "holefraser2026_31b"
    source := ⟨"hole-fraser-2026", "(31b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Das Gleisbett krabbelte heute vor Kakerlaken!"
    glossedTokens := []
    context := "There are normally a few cockroaches crawling on the underground tracks."
    judgment := .acceptable
    alternatives := [("Das Gleisbett krabbelte heute nur so vor Kakerlaken!", .acceptable)]
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("diagnostic", "nur so")] }

def ex_32b : Datum :=
  { id := "holefraser2026_32b"
    source := ⟨"hole-fraser-2026", "(32b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Werkshalle hat heute vor Maschinen gesummt!"
    glossedTokens := []
    context := "There's usually a subdued sound of industriousness in the factory."
    judgment := .acceptable
    alternatives := [("Die Werkshalle hat heute vor Maschinen nur so gesummt!", .acceptable)]
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("diagnostic", "nur so")] }

def ex_38a : Datum :=
  { id := "holefraser2026_38a"
    source := ⟨"hole-fraser-2026", "(38a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Turtles aren't even swimming in the pool, let alone diving in it!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternant", "base"), ("diagnostic", "not even")] }

def ex_38b : Datum :=
  { id := "holefraser2026_38b"
    source := ⟨"hole-fraser-2026", "(38b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The pool isn't even swimming with turtles, let alone infested by them."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := [("The pool isn't swimming with turtles, let alone infested by them.", .acceptable)]
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("diagnostic", "not even")] }

def ex_39a : Datum :=
  { id := "holefraser2026_39a"
    source := ⟨"hole-fraser-2026", "(39a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Rats aren't even crawling in the metro, let alone eating scraps of half-rotten food!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternant", "base"), ("diagnostic", "not even")] }

def ex_39b : Datum :=
  { id := "holefraser2026_39b"
    source := ⟨"hole-fraser-2026", "(39b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The metro isn't even crawling with rats, let alone infested by them."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := [("The metro isn't crawling with rats, let alone infested by them.", .acceptable)]
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("diagnostic", "not even")] }

def ex_40a : Datum :=
  { id := "holefraser2026_40a"
    source := ⟨"hole-fraser-2026", "(40a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Steaks aren't even simmering in the pan, let alone sizzling!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternant", "base"), ("diagnostic", "not even")] }

def ex_40b : Datum :=
  { id := "holefraser2026_40b"
    source := ⟨"hole-fraser-2026", "(40b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The pan isn't even simmering with steaks, let alone sizzling."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := [("The pan isn't simmering with steaks, let alone sizzling.", .acceptable)]
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("diagnostic", "not even")] }

def ex_45B_mirativity : Datum :=
  { id := "holefraser2026_45B_mirativity"
    source := ⟨"hole-fraser-2026", "(45)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The pool is swimming with turtles. No, that's not true. This is not remarkable for me."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("content", "mirativity"), ("response", "denial")] }

def ex_45Bprime_mirativity : Datum :=
  { id := "holefraser2026_45Bprime_mirativity"
    source := ⟨"hole-fraser-2026", "(45)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The pool is swimming with turtles. Hey, wait a minute! This is not remarkable for me."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("content", "mirativity"), ("response", "wait a minute")] }

def ex_45B_scalarity : Datum :=
  { id := "holefraser2026_45B_scalarity"
    source := ⟨"hole-fraser-2026", "(45)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The pool is swimming with turtles. No, that's not true. This is not a lot for me."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("content", "scalarity"), ("response", "denial")] }

def ex_45Bprime_scalarity : Datum :=
  { id := "holefraser2026_45Bprime_scalarity"
    source := ⟨"hole-fraser-2026", "(45)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The pool is swimming with turtles. Hey, wait a minute! This is not a lot for me."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("content", "scalarity"), ("response", "wait a minute")] }

def ex_46B_mirativity : Datum :=
  { id := "holefraser2026_46B_mirativity"
    source := ⟨"hole-fraser-2026", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The metro is crawling with rats. No, that's not true. This is not remarkable for me."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("content", "mirativity"), ("response", "denial")] }

def ex_46Bprime_mirativity : Datum :=
  { id := "holefraser2026_46Bprime_mirativity"
    source := ⟨"hole-fraser-2026", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The metro is crawling with rats. Hey, wait a minute! This is not remarkable for me."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("content", "mirativity"), ("response", "wait a minute")] }

def ex_46B_scalarity : Datum :=
  { id := "holefraser2026_46B_scalarity"
    source := ⟨"hole-fraser-2026", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The metro is crawling with rats. No, that's not true. This is not a lot for me."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("content", "scalarity"), ("response", "denial")] }

def ex_46Bprime_scalarity : Datum :=
  { id := "holefraser2026_46Bprime_scalarity"
    source := ⟨"hole-fraser-2026", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The metro is crawling with rats. Hey, wait a minute! This is not a lot for me."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("content", "scalarity"), ("response", "wait a minute")] }

def ex_47B_mirativity : Datum :=
  { id := "holefraser2026_47B_mirativity"
    source := ⟨"hole-fraser-2026", "(47)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The pan is sizzling with steaks. No, that's not true. This is not remarkable for me."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("content", "mirativity"), ("response", "denial")] }

def ex_47Bprime_mirativity : Datum :=
  { id := "holefraser2026_47Bprime_mirativity"
    source := ⟨"hole-fraser-2026", "(47)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The pan is sizzling with steaks. Hey, wait a minute! This is not remarkable for me."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("content", "mirativity"), ("response", "wait a minute")] }

def ex_47B_scalarity : Datum :=
  { id := "holefraser2026_47B_scalarity"
    source := ⟨"hole-fraser-2026", "(47)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The pan is sizzling with steaks. No, that's not true. This is not a lot for me."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("content", "scalarity"), ("response", "denial")] }

def ex_47Bprime_scalarity : Datum :=
  { id := "holefraser2026_47Bprime_scalarity"
    source := ⟨"hole-fraser-2026", "(47)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The pan is sizzling with steaks. Hey, wait a minute! This is not a lot for me."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("content", "scalarity"), ("response", "wait a minute")] }

def ex_49a : Datum :=
  { id := "holefraser2026_49a"
    source := ⟨"hole-fraser-2026", "(49a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Josie believes that turtles are swimming in the pool and that it isn't a big deal that there is an extremely large amount of turtles swimming in the pool."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternant", "base"), ("content", "scalarity"), ("diagnostic", "obligatory local effect"), ("holder", "negative")] }

def ex_49b : Datum :=
  { id := "holefraser2026_49b"
    source := ⟨"hole-fraser-2026", "(49b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Josie believes that turtles are swimming in the pool. That turtles are swimming in the pool isn't remarkable for her."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternant", "base"), ("content", "mirativity"), ("diagnostic", "obligatory local effect"), ("holder", "negative")] }

def ex_50a : Datum :=
  { id := "holefraser2026_50a"
    source := ⟨"hole-fraser-2026", "(50a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Josie believes that the pool is swimming with turtles and that it isn't a big deal."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("content", "scalarity"), ("diagnostic", "obligatory local effect"), ("holder", "negative")] }

def ex_50b : Datum :=
  { id := "holefraser2026_50b"
    source := ⟨"hole-fraser-2026", "(50b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Josie believes that the pool is swimming with turtles. That the pool is swimming with turtles isn't remarkable for her."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("content", "mirativity"), ("diagnostic", "obligatory local effect"), ("holder", "negative")] }

def ex_51a : Datum :=
  { id := "holefraser2026_51a"
    source := ⟨"hole-fraser-2026", "(51a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I remember ants frankly crawling on the sidewalk."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("I remember ants crawling on the sidewalk.", .acceptable)]
    readings := []
    paperFeatures := [("alternant", "base"), ("projection", "speech-act")] }

def ex_51b : Datum :=
  { id := "holefraser2026_51b"
    source := ⟨"hole-fraser-2026", "(51b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I remember the sidewalk frankly crawling with ants."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("I remember the sidewalk crawling with ants.", .acceptable)]
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("projection", "speech-act")] }

def ex_52a : Datum :=
  { id := "holefraser2026_52a"
    source := ⟨"hole-fraser-2026", "(52a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I remember ants fortunately crawling on the sidewalk."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("I remember ants crawling on the sidewalk.", .acceptable)]
    readings := []
    paperFeatures := [("alternant", "base"), ("projection", "evaluation")] }

def ex_52b : Datum :=
  { id := "holefraser2026_52b"
    source := ⟨"hole-fraser-2026", "(52b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I remember the sidewalk fortunately crawling with ants."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("I remember the sidewalk crawling with ants.", .acceptable)]
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("projection", "evaluation")] }

def ex_53a : Datum :=
  { id := "holefraser2026_53a"
    source := ⟨"hole-fraser-2026", "(53a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I remember ants surprisingly crawling on the sidewalk."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("I remember ants crawling on the sidewalk.", .acceptable)]
    readings := []
    paperFeatures := [("alternant", "base"), ("projection", "mirativity")] }

def ex_53b : Datum :=
  { id := "holefraser2026_53b"
    source := ⟨"hole-fraser-2026", "(53b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I remember the sidewalk surprisingly crawling with ants."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("I remember the sidewalk crawling with ants.", .acceptable)]
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("projection", "mirativity")] }

def ex_54a : Datum :=
  { id := "holefraser2026_54a"
    source := ⟨"hole-fraser-2026", "(54a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I remember ants certainly crawling on the sidewalk."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("I remember ants crawling on the sidewalk.", .acceptable)]
    readings := []
    paperFeatures := [("alternant", "base"), ("projection", "epistemic modality")] }

def ex_54b : Datum :=
  { id := "holefraser2026_54b"
    source := ⟨"hole-fraser-2026", "(54b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I remember the sidewalk certainly crawling with ants."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("I remember the sidewalk crawling with ants.", .acceptable)]
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("projection", "epistemic modality")] }

def ex_55a : Datum :=
  { id := "holefraser2026_55a"
    source := ⟨"hole-fraser-2026", "(55a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I remember ants just crawling on the sidewalk."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("I remember ants crawling on the sidewalk.", .acceptable)]
    readings := []
    paperFeatures := [("alternant", "base"), ("projection", "scalar evaluation")] }

def ex_55b : Datum :=
  { id := "holefraser2026_55b"
    source := ⟨"hole-fraser-2026", "(55b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I remember the sidewalk just crawling with ants."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("I remember the sidewalk crawling with ants.", .acceptable)]
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("projection", "scalar evaluation")] }

def ex_56a : Datum :=
  { id := "holefraser2026_56a"
    source := ⟨"hole-fraser-2026", "(56a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I remember ants once crawling on the sidewalk."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("I remember ants crawling on the sidewalk.", .acceptable)]
    readings := []
    paperFeatures := [("alternant", "base"), ("projection", "deictic tense")] }

def ex_56b : Datum :=
  { id := "holefraser2026_56b"
    source := ⟨"hole-fraser-2026", "(56b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I remember the sidewalk once crawling with ants."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("I remember the sidewalk crawling with ants.", .acceptable)]
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("projection", "deictic tense")] }

def ex_57a : Datum :=
  { id := "holefraser2026_57a"
    source := ⟨"hole-fraser-2026", "(57a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I remember ants habitually crawling on the sidewalk."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("I remember ants crawling on the sidewalk.", .acceptable)]
    readings := []
    paperFeatures := [("alternant", "base"), ("projection", "habitual aspect")] }

def ex_57b : Datum :=
  { id := "holefraser2026_57b"
    source := ⟨"hole-fraser-2026", "(57b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I remember the sidewalk habitually crawling with ants."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("I remember the sidewalk crawling with ants.", .acceptable)]
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("projection", "habitual aspect")] }

def ex_58a : Datum :=
  { id := "holefraser2026_58a"
    source := ⟨"hole-fraser-2026", "(58a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I remember ants still crawling on the sidewalk."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("I remember ants crawling on the sidewalk.", .acceptable)]
    readings := []
    paperFeatures := [("alternant", "base"), ("projection", "continuative aspect I")] }

def ex_58b : Datum :=
  { id := "holefraser2026_58b"
    source := ⟨"hole-fraser-2026", "(58b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I remember the sidewalk still crawling with ants."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("I remember the sidewalk crawling with ants.", .acceptable)]
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("projection", "continuative aspect I")] }

def ex_59a : Datum :=
  { id := "holefraser2026_59a"
    source := ⟨"hole-fraser-2026", "(59a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I remember ants briefly crawling on the sidewalk."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("I remember ants crawling on the sidewalk.", .acceptable)]
    readings := []
    paperFeatures := [("alternant", "base"), ("projection", "durative aspect")] }

def ex_59b : Datum :=
  { id := "holefraser2026_59b"
    source := ⟨"hole-fraser-2026", "(59b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I remember the sidewalk briefly crawling with ants."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("I remember the sidewalk crawling with ants.", .acceptable)]
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("projection", "durative aspect")] }

def ex_60a : Datum :=
  { id := "holefraser2026_60a"
    source := ⟨"hole-fraser-2026", "(60a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I remember ants almost crawling on the sidewalk."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("I remember ants crawling on the sidewalk.", .acceptable)]
    readings := []
    paperFeatures := [("alternant", "base"), ("projection", "prospective aspect")] }

def ex_60b : Datum :=
  { id := "holefraser2026_60b"
    source := ⟨"hole-fraser-2026", "(60b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I remember the sidewalk almost crawling with ants."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("I remember the sidewalk crawling with ants.", .acceptable)]
    readings := []
    paperFeatures := [("alternant", "nonBase"), ("projection", "prospective aspect")] }

def all : List Datum := [ex_17, ex_18, ex_19, ex_30b, ex_31b, ex_32b, ex_38a, ex_38b, ex_39a, ex_39b, ex_40a, ex_40b, ex_45B_mirativity, ex_45Bprime_mirativity, ex_45B_scalarity, ex_45Bprime_scalarity, ex_46B_mirativity, ex_46Bprime_mirativity, ex_46B_scalarity, ex_46Bprime_scalarity, ex_47B_mirativity, ex_47Bprime_mirativity, ex_47B_scalarity, ex_47Bprime_scalarity, ex_49a, ex_49b, ex_50a, ex_50b, ex_51a, ex_51b, ex_52a, ex_52b, ex_53a, ex_53b, ex_54a, ex_54b, ex_55a, ex_55b, ex_56a, ex_56b, ex_57a, ex_57b, ex_58a, ex_58b, ex_59a, ex_59b, ex_60a, ex_60b]

end HoleFraser2026.Examples
