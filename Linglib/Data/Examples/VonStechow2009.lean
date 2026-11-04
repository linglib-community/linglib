module

public import Linglib.Data.Examples.Schema

/-!
# `VonStechow2009` — typed example data

Auto-generated from `Linglib/Data/Examples/VonStechow2009.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace VonStechow2009.Examples`.
-/

@[expose] public section

namespace VonStechow2009.Examples

def ex_21a : Datum :=
  { id := "vonstechow2009_21a"
    source := ⟨"von-stechow-2009", "(21a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John called."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("there is a time before the speech time at which John calls", .acceptable)]
    paperFeatures := [("tense", "past"), ("lf", "[P N] λ1 John called t1")] }

def ex_27 : Datum :=
  { id := "vonstechow2009_27"
    source := ⟨"von-stechow-2009", "(27)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John had called."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("a past time before a past time", .acceptable)]
    paperFeatures := [("tense", "pluperfect"), ("auxiliary", "had")] }

def ex_30 : Datum :=
  { id := "vonstechow2009_30"
    source := ⟨"von-stechow-2009", "(30)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John will call."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("tense", "future"), ("auxiliary", "will")] }

def ex_37 : Datum :=
  { id := "vonstechow2009_37"
    source := ⟨"von-stechow-2009", "(37)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary called on my birthday."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adverbial", "frame"), ("composition", "predicate modification")] }

def ex_42 : Datum :=
  { id := "vonstechow2009_42"
    source := ⟨"von-stechow-2009", "(42)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John has called yesterday."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "present perfect puzzle"), ("auxiliary", "extended now")] }

def ex_43 : Datum :=
  { id := "vonstechow2009_43"
    source := ⟨"von-stechow-2009", "(43)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary had left at six."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("reference-time modification: the leaving is before six", .acceptable), ("event-time modification: the leaving is at six", .acceptable)]
    paperFeatures := [("adverbial", "at"), ("scope", "perfect auxiliary")] }

def ex_44 : Datum :=
  { id := "vonstechow2009_44"
    source := ⟨"von-stechow-2009", "(44)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John worked on every Sunday."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("quantifier under the Past: a past time on every Sunday", .unacceptable), ("quantifier over the Past: every Sunday contains a past time", .unacceptable), ("every past Sunday contains a working time", .acceptable)]
    paperFeatures := [("adverbial", "quantified"), ("restriction", "domain variable")] }

def ex_46 : Datum :=
  { id := "vonstechow2009_46"
    source := ⟨"partee-1973", ""⟩
    reportedIn := some ⟨"von-stechow-2009", "(46)"⟩
    language := "stan1293"
    primaryText := "I didn't turn off the stove."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("some past time at which I do not turn off the stove", .unacceptable), ("no past time at which I turn off the stove", .unacceptable), ("no time in the contextually given past interval at which I turn off the stove", .acceptable)]
    paperFeatures := [("tense", "referential vs indefinite"), ("scope", "negation")] }

def ex_55 : Datum :=
  { id := "vonstechow2009_55"
    source := ⟨"von-stechow-2009", "(55)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John will have left at six."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("the leaving is after the speech time", .acceptable)]
    paperFeatures := [("tense", "future perfect"), ("restriction", "superordinate tense")] }

def ex_58 : Datum :=
  { id := "vonstechow2009_58"
    source := ⟨"von-stechow-2009", "(58)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It didn't rain today."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("no past time in today at which it rains", .acceptable)]
    paperFeatures := [("scope", "negation over tense")] }

def ex_60 : Datum :=
  { id := "vonstechow2009_60"
    source := ⟨"von-stechow-2009", "(60)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John polished every boot."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("for every boot a past polishing time", .acceptable)]
    paperFeatures := [("scope", "quantifier over tense")] }

def ex_62 : Datum :=
  { id := "vonstechow2009_62"
    source := ⟨"von-stechow-2009", "(62)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary will buy a fish that is alive."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous: alive at the buying time", .acceptable), ("deictic: alive at the speech time", .acceptable)]
    paperFeatures := [("clause", "relative"), ("tense", "present under future")] }

def ex_63 : Datum :=
  { id := "vonstechow2009_63"
    source := ⟨"von-stechow-2009", "(63)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary will buy a fish that has been alive."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("shifted: alive before the buying time", .acceptable), ("deictic perfect: alive before the speech time", .acceptable)]
    paperFeatures := [("clause", "relative"), ("tense", "perfect under future")] }

def ex_64 : Datum :=
  { id := "vonstechow2009_64"
    source := ⟨"von-stechow-2009", "(64)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary will buy a fish that was alive."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("deictic: alive before the speech time", .acceptable), ("shifted: alive before the buying time", .marginal)]
    paperFeatures := [("clause", "relative"), ("tense", "past under future")] }

def ex_68 : Datum :=
  { id := "vonstechow2009_68"
    source := ⟨"von-stechow-2009", "(68)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary talked to a boy who is crying."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("deictic", .acceptable), ("simultaneous", .ungrammatical)]
    paperFeatures := [("clause", "relative"), ("feature", "uN")] }

def ex_69 : Datum :=
  { id := "vonstechow2009_69"
    source := ⟨"von-stechow-2009", "(69)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary talked to a boy who was crying."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .acceptable), ("backward shifted", .acceptable), ("independent, forward shifted", .acceptable)]
    paperFeatures := [("clause", "relative"), ("tense", "past under past")] }

def ex_70 : Datum :=
  { id := "vonstechow2009_70"
    source := ⟨"von-stechow-2009", "(70)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Hillary married a man who became the president."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("forward shifted", .acceptable)]
    paperFeatures := [("clause", "relative"), ("tense", "past under past")] }

def ex_71 : Datum :=
  { id := "vonstechow2009_71"
    source := ⟨"von-stechow-2009", "(71)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John thought that he would buy a fish that was still alive."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("the fish is alive at the future buying time", .acceptable)]
    paperFeatures := [("clause", "relative under attitude"), ("tense", "bound")] }

def ex_76 : Datum :=
  { id := "vonstechow2009_76"
    source := ⟨"von-stechow-2009", "(76)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John believed it was raining."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("a belief John would word as it is raining", .acceptable)]
    paperFeatures := [("clause", "attitude complement"), ("tense", "subjective now")] }

def ex_77 : Datum :=
  { id := "vonstechow2009_77"
    source := ⟨"von-stechow-2009", "(77)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "At 5 o'clock Mary thought it was 6 o'clock."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("anaphoric: Mary believes that 5 o'clock is 6 o'clock", .unacceptable), ("Mary locates her time at 6 o'clock", .acceptable)]
    paperFeatures := [("clause", "attitude complement"), ("complement", "property of times")] }

def ex_80 : Datum :=
  { id := "vonstechow2009_80"
    source := ⟨"von-stechow-2009", "(80)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary thought Bill left."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("shifted: the leaving before Mary's subjective now", .acceptable)]
    paperFeatures := [("clause", "attitude complement"), ("tense", "past over PRO")] }

def ex_84a : Datum :=
  { id := "vonstechow2009_84a"
    source := ⟨"stump-1985", ""⟩
    reportedIn := some ⟨"von-stechow-2009", "(84a)"⟩
    language := "stan1293"
    primaryText := "John will enter the room before Mary leaves."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("John will enter the room after Mary has left.", .acceptable), ("John will enter the room after Mary leaves.", .acceptable)]
    readings := [("before the earliest future time at which Mary leaves", .acceptable)]
    paperFeatures := [("clause", "before/after"), ("tense", "present under future")] }

def ex_84d : Datum :=
  { id := "vonstechow2009_84d"
    source := ⟨"stump-1985", ""⟩
    reportedIn := some ⟨"von-stechow-2009", "(84d)"⟩
    language := "stan1293"
    primaryText := "John will enter the room after Mary will leave."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("John will enter the room before Mary will leave.", .ungrammatical)]
    readings := []
    paperFeatures := [("clause", "before/after"), ("tense", "future under future")] }

def ex_85 : Datum :=
  { id := "vonstechow2009_85"
    source := ⟨"von-stechow-2009", "(85)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary left before John arrived."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Mary left after John arrived.", .acceptable)]
    readings := [("before the earliest past time at which John arrives", .acceptable)]
    paperFeatures := [("clause", "before/after"), ("tense", "past under past")] }

def ex_86 : Datum :=
  { id := "vonstechow2009_86"
    source := ⟨"von-stechow-2009", "(86)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary arrived after 6."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Mary arrived before 6.", .acceptable)]
    readings := []
    paperFeatures := [("preposition", "temporal"), ("meaning", "precedence")] }

def all : List Datum := [ex_21a, ex_27, ex_30, ex_37, ex_42, ex_43, ex_44, ex_46, ex_55, ex_58, ex_60, ex_62, ex_63, ex_64, ex_68, ex_69, ex_70, ex_71, ex_76, ex_77, ex_80, ex_84a, ex_84d, ex_85, ex_86]

end VonStechow2009.Examples
