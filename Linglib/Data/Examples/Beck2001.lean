module

public import Linglib.Data.Examples.Schema

/-!
# `Beck2001` — typed example data

Auto-generated from `Linglib/Data/Examples/Beck2001.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Beck2001.Examples`.
-/

@[expose] public section

namespace Beck2001.Examples

def ex14_15 : Datum :=
  { id := "beck2001_ex14_15"
    source := ⟨"dalrymple-et-al-1998", "(4)"⟩
    reportedIn := some ⟨"beck-2001", "(14)"⟩
    method := some .corpus
    language := "stan1293"
    primaryText := "Five Boston pitchers sat alongside each other."
    glossedTokens := []
    context := "The pitchers sit in a line, each alongside the next, as depicted in (15)."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex83b : Datum :=
  { id := "beck2001_ex83b"
    source := ⟨"dalrymple-et-al-1998", "(75)"⟩
    reportedIn := some ⟨"beck-2001", "(83b)"⟩
    language := "stan1293"
    primaryText := "The forks are propped against each other."
    glossedTokens := []
    context := "Three forks. Each one is jointly supported by the other two, but not by any single other fork."
    judgment := .acceptable
    alternatives := []
    readings := [("collective", .acceptable)]
    paperFeatures := [] }

def ex99 : Datum :=
  { id := "beck2001_ex99"
    source := ⟨"beck-2001", "(99b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They like each other."
    glossedTokens := []
    context := "Susanne proposes taking Amy, Bertha, Celia and Dave backpacking and says this of them. Ed replies: You're kidding! Bertha can't stand Dave!"
    judgment := .acceptable
    alternatives := []
    readings := [("Strong Reciprocity", .acceptable)]
    paperFeatures := [] }

def ex105a : Datum :=
  { id := "beck2001_ex105a"
    source := ⟨"beck-2001", "(105a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The four professors introduced exactly two students to each other."
    glossedTokens := []
    context := "The professors are a, b, c and d. a introduced exactly one student to b and vice versa; c introduced exactly one student to d and vice versa."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex119 : Datum :=
  { id := "beck2001_ex119"
    source := ⟨"beck-2001", "(119)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "These pants do not resemble each other (because there is only one of them)."
    glossedTokens := []
    context := "There is only one pair of pants."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex128a : Datum :=
  { id := "beck2001_ex128a"
    source := ⟨"beck-2001", "(128a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue and Amy hate the other ones in their two girl scout groups."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("(128b)", .acceptable)]
    paperFeatures := [] }

def ex135_136 : Datum :=
  { id := "beck2001_ex135_136"
    source := ⟨"dalrymple-et-al-1998", "(6)"⟩
    reportedIn := some ⟨"beck-2001", "(135)"⟩
    language := "stan1293"
    primaryText := "The pirates stared at each other."
    glossedTokens := []
    context := "Pirate 1 stares at 2, 2 at 3, 3 at 4, 4 at 5, 5 at 1, and 6 at 1, as depicted in (136)."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex135_141 : Datum :=
  { id := "beck2001_ex135_141"
    source := ⟨"beck-2001", "(135)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The pirates stared at each other."
    glossedTokens := []
    context := "Pirate 1 stares at 2, 2 at 3, 3 at 4, 4 at 5 and 5 at 1; pirate 6 is completely uninvolved, as depicted in (141)."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex135_142 : Datum :=
  { id := "beck2001_ex135_142"
    source := ⟨"beck-2001", "(135)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The pirates stared at each other."
    glossedTokens := []
    context := "Pirates 2, 3, 4, 5 and 6 stare at 1, and 1 stares at 6, as depicted in (142)."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex143_141 : Datum :=
  { id := "beck2001_ex143_141"
    source := ⟨"beck-2001", "(143)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The pirates all stared at each other."
    glossedTokens := []
    context := "Pirate 1 stares at 2, 2 at 3, 3 at 4, 4 at 5 and 5 at 1; pirate 6 is completely uninvolved, as depicted in (141)."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex153 : Datum :=
  { id := "beck2001_ex153"
    source := ⟨"beck-2001", "(153b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The girls can all just touch each other."
    glossedTokens := []
    context := "The girls are standing in a circle. There is one gap between the girls that is too large."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex188a : Datum :=
  { id := "beck2001_ex188a"
    source := ⟨"beck-2001", "(188a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My colleagues often recycle the others' class notes. They (all) respect each other."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("(188d)", .unacceptable)]
    paperFeatures := [] }

def ex220 : Datum :=
  { id := "beck2001_ex220"
    source := ⟨"beck-2001", "(220)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "None of them knew each other."
    glossedTokens := []
    context := "Four out of the five members of the group know the fifth, a semanticist famous from TV, who doesn't know the other four; those four are complete strangers to each other."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def fn16i : Datum :=
  { id := "beck2001_fn16i"
    source := ⟨"beck-2001", "fn. 16 (i)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "(Let's make a bunch of teams such that) none of them outnumber each other."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def fn16ii : Datum :=
  { id := "beck2001_fn16ii"
    source := ⟨"beck-2001", "fn. 16 (ii)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "None of them procreated each other."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def fn16iii : Datum :=
  { id := "beck2001_fn16iii"
    source := ⟨"beck-2001", "fn. 16 (iii)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "(Line up these glasses on the shelf in such a way that) none of them are behind each other."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex14_15, ex83b, ex99, ex105a, ex119, ex128a, ex135_136, ex135_141, ex135_142, ex143_141, ex153, ex188a, ex220, fn16i, fn16ii, fn16iii]

end Beck2001.Examples
