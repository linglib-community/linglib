module

public import Linglib.Data.Examples.Schema

/-!
# `Icard2012` — typed example data

Auto-generated from `Linglib/Data/Examples/Icard2012.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Icard2012.Examples`.
-/

@[expose] public section

namespace Icard2012.Examples

def squid_t : Datum :=
  { id := "icard2012_squid_t"
    source := ⟨"icard-2012", "Section 3.2, t"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every job that involves a giant squid is dangerous."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("relation", "⊑ t'"), ("derivation", "three substitutions and two compositions")] }

def squid_t2 : Datum :=
  { id := "icard2012_squid_t2"
    source := ⟨"icard-2012", "Section 3.2, t'"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not every job that involves a cephalopod is safe."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("relation", "⊒ t")] }

def mono : Datum :=
  { id := "icard2012_mono"
    source := ⟨"icard-2012", "Section 3.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "every cephalopod ⊑ every giant squid"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("relation", "a monotonicity inference from giant squid ⊑ cephalopod under ◇")] }

def no_notevery : Datum :=
  { id := "icard2012_no_notevery"
    source := ⟨"icard-2012", "Section 3.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "no ⊑ not every"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("relation", "derived from no | every and every ^ not every, | ⋈ ^ = ⊑")] }

def confluence : Datum :=
  { id := "icard2012_confluence"
    source := ⟨"icard-2012", "Section 3.3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "some squid ⊑ some cephalopod"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3"), ("relation", "derivable in one substitution; lost after substituting octopus for squid, which yields #")] }

def s4_1 : Datum :=
  { id := "icard2012_s4_1"
    source := ⟨"icard-2012", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not everyone is here yet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4"), ("npi", "yet, weak"), ("context", "not every, antitone")] }

def s4_2 : Datum :=
  { id := "icard2012_s4_2"
    source := ⟨"icard-2012", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Few students are here yet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4"), ("npi", "yet, weak"), ("context", "few, antitone")] }

def s4_3 : Datum :=
  { id := "icard2012_s4_3"
    source := ⟨"icard-2012", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Few scholars have written about it in years."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4"), ("npi", "in years, strong"), ("context", "few, not anti-additive")] }

def s4_4 : Datum :=
  { id := "icard2012_s4_4"
    source := ⟨"icard-2012", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No scholar has written about it in years."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4"), ("npi", "in years, strong"), ("context", "no, anti-additive in its second argument")] }

def s4_5 : Datum :=
  { id := "icard2012_s4_5"
    source := ⟨"icard-2012", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No customer was a tad bit happy."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4"), ("npi", "a tad bit, superstrong"), ("context", "no, not anti-multiplicative")] }

def s4_6 : Datum :=
  { id := "icard2012_s4_6"
    source := ⟨"icard-2012", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The manager was not a tad bit happy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4"), ("npi", "a tad bit, superstrong"), ("context", "not, anti-additive and anti-multiplicative")] }

def all : List Datum := [squid_t, squid_t2, mono, no_notevery, confluence, s4_1, s4_2, s4_3, s4_4, s4_5, s4_6]

end Icard2012.Examples
