module

public import Linglib.Data.Examples.Schema

/-!
# `DechaineWiltschko2002` — typed example data

Auto-generated from `Linglib/Data/Examples/DechaineWiltschko2002.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace DechaineWiltschko2002.Examples`.
-/

@[expose] public section

namespace DechaineWiltschko2002.Examples

def ex32a_1 : Datum :=
  { id := "dechainewiltschko2002_ex32a_1"
    source := ⟨"dechaine-wiltschko-2002", "(32a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "we linguists"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("test", "precedesNoun"), ("pronoun", "we"), ("dialect", "A")] }

def ex32a_2 : Datum :=
  { id := "dechainewiltschko2002_ex32a_2"
    source := ⟨"dechaine-wiltschko-2002", "(32a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "us linguists"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("test", "precedesNoun"), ("pronoun", "us"), ("dialect", "A")] }

def ex32b : Datum :=
  { id := "dechainewiltschko2002_ex32b"
    source := ⟨"dechaine-wiltschko-2002", "(32b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "you linguists"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("test", "precedesNoun"), ("pronoun", "you"), ("dialect", "A")] }

def ex32c_1 : Datum :=
  { id := "dechainewiltschko2002_ex32c_1"
    source := ⟨"dechaine-wiltschko-2002", "(32c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "they linguists"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("test", "precedesNoun"), ("pronoun", "they"), ("dialect", "A")] }

def ex32c_2 : Datum :=
  { id := "dechainewiltschko2002_ex32c_2"
    source := ⟨"dechaine-wiltschko-2002", "(32c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "them linguists"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("test", "precedesNoun"), ("pronoun", "them"), ("dialect", "A")] }

def ex34c_1 : Datum :=
  { id := "dechainewiltschko2002_ex34c_1"
    source := ⟨"dechaine-wiltschko-2002", "(34c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "they linguists"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("test", "precedesNoun"), ("pronoun", "they"), ("dialect", "B")] }

def ex34c_2 : Datum :=
  { id := "dechainewiltschko2002_ex34c_2"
    source := ⟨"dechaine-wiltschko-2002", "(34c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "them linguists"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("test", "precedesNoun"), ("pronoun", "them"), ("dialect", "B")] }

def ex38 : Datum :=
  { id := "dechainewiltschko2002_ex38"
    source := ⟨"dechaine-wiltschko-2002", "(38)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every candidate thinks that he will win."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("test", "boundVariable"), ("pronoun", "he")] }

def ex40 : Datum :=
  { id := "dechainewiltschko2002_ex40"
    source := ⟨"dechaine-wiltschko-2002", "(40)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I know that John saw me, and Mary does too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("strict", .acceptable), ("sloppy", .unacceptable)]
    paperFeatures := [("test", "boundVariable"), ("pronoun", "me")] }

def ex30a : Datum :=
  { id := "dechainewiltschko2002_ex30a"
    source := ⟨"dechaine-wiltschko-2002", "(30a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everybody thinks one is a genius."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("test", "boundVariable"), ("pronoun", "one")] }

def ex30b : Datum :=
  { id := "dechainewiltschko2002_ex30b"
    source := ⟨"dechaine-wiltschko-2002", "(30b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everybody loves one's mother."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("test", "boundVariable"), ("pronoun", "one")] }

def ex22a : Datum :=
  { id := "dechainewiltschko2002_ex22a"
    source := ⟨"dechaine-wiltschko-2002", "(22a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Daremo-ga kare-no hahaoya-o aisite-iru."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("test", "boundVariable"), ("pronoun", "kare")] }

def all : List Datum := [ex32a_1, ex32a_2, ex32b, ex32c_1, ex32c_2, ex34c_1, ex34c_2, ex38, ex40, ex30a, ex30b, ex22a]

end DechaineWiltschko2002.Examples
