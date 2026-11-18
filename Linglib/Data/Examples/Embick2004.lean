module

public import Linglib.Data.Examples.Schema

/-!
# `Embick2004` — typed example data

Auto-generated from `Linglib/Data/Examples/Embick2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Embick2004.Examples`.
-/

@[expose] public section

namespace Embick2004.Examples

def ex_33 : Datum :=
  { id := "embick2004_33"
    source := ⟨"embick-2004", "(33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John hammered the metal flat."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("spec", "theMetal"), ("merged", "hammer"), ("comp", "aP"), ("compRoot", "flat"), ("innerSpec", "none"), ("means", "argument")] }

def ex_34 : Datum :=
  { id := "embick2004_34"
    source := ⟨"embick-2004", "(34)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The metal is hammered flat."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("spec", "theMetal"), ("merged", "hammer"), ("comp", "aP"), ("compRoot", "flat"), ("innerSpec", "none"), ("means", "argument")] }

def ex_44 : Datum :=
  { id := "embick2004_44"
    source := ⟨"embick-2004", "(44)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The metal is hammered."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("spec", "theMetal"), ("merged", "none"), ("comp", "root"), ("compRoot", "hammer"), ("innerSpec", "none"), ("means", "none")] }

def flattened : Datum :=
  { id := "embick2004_flattened"
    source := ⟨"embick-2004", "p. 373"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The metal is flattened."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("spec", "theMetal"), ("merged", "none"), ("comp", "root"), ("compRoot", "flat"), ("innerSpec", "none"), ("means", "none")] }

def ex_45b : Datum :=
  { id := "embick2004_45b"
    source := ⟨"embick-2004", "(45b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is laughed."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("spec", "john"), ("merged", "none"), ("comp", "root"), ("compRoot", "laugh"), ("innerSpec", "none"), ("means", "none")] }

def laughed_hoarse : Datum :=
  { id := "embick2004_laughed_hoarse"
    source := ⟨"embick-2004", "p. 369"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John laughed hoarse."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("spec", "none"), ("merged", "laugh"), ("comp", "aP"), ("compRoot", "hoarse"), ("innerSpec", "none"), ("means", "noArgument")] }

def laughed_himself_hoarse : Datum :=
  { id := "embick2004_laughed_himself_hoarse"
    source := ⟨"embick-2004", "p. 369"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John laughed himself hoarse."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("spec", "himself"), ("merged", "laugh"), ("comp", "aP"), ("compRoot", "hoarse"), ("innerSpec", "none"), ("means", "noArgument")] }

def froze_solid : Datum :=
  { id := "embick2004_froze_solid"
    source := ⟨"embick-2004", "p. 369"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The river froze solid."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("spec", "theRiver"), ("merged", "freeze"), ("comp", "aP"), ("compRoot", "solid"), ("innerSpec", "none"), ("means", "argument")] }

def ex_51 : Datum :=
  { id := "embick2004_51"
    source := ⟨"embick-2004", "(51)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John smoked himself thin."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("spec", "himself"), ("merged", "smoke"), ("comp", "aP"), ("compRoot", "thin"), ("innerSpec", "none"), ("means", "noArgument")] }

def ex_53 : Datum :=
  { id := "embick2004_53"
    source := ⟨"embick-2004", "(53)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John hammered himself thin."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("spec", "himself"), ("merged", "hammer"), ("comp", "aP"), ("compRoot", "thin"), ("innerSpec", "none"), ("means", "noArgument")] }

def ex_57a : Datum :=
  { id := "embick2004_57a"
    source := ⟨"embick-2004", "(57a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John kicked the door open."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("spec", "theDoor"), ("merged", "kick"), ("comp", "aP"), ("compRoot", "open"), ("innerSpec", "none"), ("means", "argument")] }

def ex_57b : Datum :=
  { id := "embick2004_57b"
    source := ⟨"embick-2004", "(57b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John kicked the door opened."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("spec", "theDoor"), ("merged", "kick"), ("comp", "participle"), ("compRoot", "open"), ("innerSpec", "none"), ("means", "argument")] }

def all : List Datum := [ex_33, ex_34, ex_44, flattened, ex_45b, laughed_hoarse, laughed_himself_hoarse, froze_solid, ex_51, ex_53, ex_57a, ex_57b]

end Embick2004.Examples
