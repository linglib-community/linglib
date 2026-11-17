module

public import Linglib.Data.Examples.Schema

/-!
# `Reinhart1976` — typed example data

Auto-generated from `Linglib/Data/Examples/Reinhart1976.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Reinhart1976.Examples`.
-/

@[expose] public section

namespace Reinhart1976.Examples

def ex_11a : Datum :=
  { id := "reinhart1976_11a"
    source := ⟨"reinhart-1976", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Rosa denied that Rosa has met the Shah."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("coreference", .unacceptable)]
    paperFeatures := [("structure", "denied"), ("np1", "0"), ("np2", "110"), ("pronouns", "none")] }

def ex_11b : Datum :=
  { id := "reinhart1976_11b"
    source := ⟨"reinhart-1976", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She denied that Rosa has met the Shah."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("coreference", .unacceptable)]
    paperFeatures := [("structure", "denied"), ("np1", "0"), ("np2", "110"), ("pronouns", "np1")] }

def ex_11c : Datum :=
  { id := "reinhart1976_11c"
    source := ⟨"reinhart-1976", "(11c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Rosa denied that she has met the Shah."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("structure", "denied"), ("np1", "0"), ("np2", "110"), ("pronouns", "np2")] }

def ex_11d : Datum :=
  { id := "reinhart1976_11d"
    source := ⟨"reinhart-1976", "(11d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She denied that she has met the Shah."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("structure", "denied"), ("np1", "0"), ("np2", "110"), ("pronouns", "both")] }

def IIa : Datum :=
  { id := "reinhart1976_IIa"
    source := ⟨"reinhart-1976", "(IIa)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The man who traveled with Rosa denied that she met the Shah."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("structure", "relative"), ("np1", "02111"), ("np2", "110"), ("pronouns", "np2")] }

def IIb : Datum :=
  { id := "reinhart1976_IIb"
    source := ⟨"reinhart-1976", "(IIb)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The man who traveled with her denied that Rosa met the Shah."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("structure", "relative"), ("np1", "02111"), ("np2", "110"), ("pronouns", "np1")] }

def ex_12a : Datum :=
  { id := "reinhart1976_12a"
    source := ⟨"reinhart-1976", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "People who know Nixon hate him."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("structure", "relativeObject"), ("np1", "0111"), ("np2", "11"), ("pronouns", "np2")] }

def ex_12b : Datum :=
  { id := "reinhart1976_12b"
    source := ⟨"reinhart-1976", "(12b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "People who know him hate Nixon."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("structure", "relativeObject"), ("np1", "0111"), ("np2", "11"), ("pronouns", "np1")] }

def ex_12c : Datum :=
  { id := "reinhart1976_12c"
    source := ⟨"reinhart-1976", "(12c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "People who know Nixon hate Nixon."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("structure", "relativeObject"), ("np1", "0111"), ("np2", "11"), ("pronouns", "none")] }

def ex_43a : Datum :=
  { id := "reinhart1976_43a"
    source := ⟨"reinhart-1976", "(43a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Near Dan, he saw a snake."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("structure", "preposedPP"), ("np1", "01"), ("np2", "1"), ("pronouns", "np2")] }

def ex_43b : Datum :=
  { id := "reinhart1976_43b"
    source := ⟨"reinhart-1976", "(43b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Near Dan, Dan saw a snake."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("structure", "preposedPP"), ("np1", "01"), ("np2", "1"), ("pronouns", "none")] }

def ex_45 : Datum :=
  { id := "reinhart1976_45"
    source := ⟨"reinhart-1976", "(45)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Near him, Dan saw a snake."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("structure", "preposedPP"), ("np1", "01"), ("np2", "1"), ("pronouns", "np1")] }

def ex_47 : Datum :=
  { id := "reinhart1976_47"
    source := ⟨"reinhart-1976", "(47)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In Dan's apartment, Rosa showed him her new tricks."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("structure", "preposedPP"), ("np1", "010"), ("np2", "21"), ("pronouns", "np2")] }

def ex_44a : Datum :=
  { id := "reinhart1976_44a"
    source := ⟨"reinhart-1976", "(44a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He was fired since McIntosh's weird habits had finally reached an intolerable stage."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("structure", "sententialPP"), ("np1", "0"), ("np2", "2100"), ("pronouns", "np1")] }

def ex_44b : Datum :=
  { id := "reinhart1976_44b"
    source := ⟨"reinhart-1976", "(44b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "McIntosh was fired since McIntosh's weird habits had finally reached an intolerable stage."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("structure", "sententialPP"), ("np1", "0"), ("np2", "2100"), ("pronouns", "none")] }

def ex_46 : Datum :=
  { id := "reinhart1976_46"
    source := ⟨"reinhart-1976", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We had to fire him since McIntosh's weird habits had reached an intolerable stage."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("structure", "sententialPP"), ("np1", "11"), ("np2", "2100"), ("pronouns", "np1")] }

def ex_48a : Datum :=
  { id := "reinhart1976_48a"
    source := ⟨"reinhart-1976", "(48a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I'm willing to give him 2 grand for Ben's car."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("structure", "verbalPP"), ("np1", "111"), ("np2", "11310"), ("pronouns", "np1")] }

def ex_51a : Datum :=
  { id := "reinhart1976_51a"
    source := ⟨"reinhart-1976", "(51a)"⟩
    reportedIn := none
    language := "plat1254"
    primaryText := "namono azy ny anadahin-dRakoto"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("structure", "vos"), ("np1", "01"), ("np2", "11"), ("pronouns", "np1")] }

def ex_51b : Datum :=
  { id := "reinhart1976_51b"
    source := ⟨"reinhart-1976", "(51b)"⟩
    reportedIn := none
    language := "plat1254"
    primaryText := "namono ny anadahin-dRakoto izy"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("structure", "vos"), ("np1", "011"), ("np2", "1"), ("pronouns", "np2")] }

def all : List Datum := [ex_11a, ex_11b, ex_11c, ex_11d, IIa, IIb, ex_12a, ex_12b, ex_12c, ex_43a, ex_43b, ex_45, ex_47, ex_44a, ex_44b, ex_46, ex_48a, ex_51a, ex_51b]

end Reinhart1976.Examples
