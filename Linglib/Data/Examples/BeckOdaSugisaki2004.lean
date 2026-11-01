module

public import Linglib.Data.Examples.Schema

/-!
# `BeckOdaSugisaki2004` — typed example data

Auto-generated from `Linglib/Data/Examples/BeckOdaSugisaki2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BeckOdaSugisaki2004.Examples`.
-/

@[expose] public section

namespace BeckOdaSugisaki2004.Examples

def amount_yori : Datum :=
  { id := "beckodasugisaki2004_amount_yori"
    source := ⟨"beck-oda-sugisaki-2004", "(3-a), p. 290"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-wa [Hanako-ga katta yori (mo)] takusan(-no) kasa-o katta"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "amount_comparative")] }

def degree_yori : Datum :=
  { id := "beckodasugisaki2004_degree_yori"
    source := ⟨"beck-oda-sugisaki-2004", "(4-a), p. 290"⟩
    reportedIn := none
    method := some .elicitation
    language := "nucl1643"
    primaryText := "Taroo-wa [Hanako-ga katta yori (mo)] nagai kasa-o katta"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "degree_comparative")] }

def subcomp_ja : Datum :=
  { id := "beckodasugisaki2004_subcomp_ja"
    source := ⟨"beck-oda-sugisaki-2004", "(5-a), p. 290"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Kono tana-wa [ano doa-ga hiroi yori (mo)] (motto) takai"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "subcomparative")] }

def subcomp_en : Datum :=
  { id := "beckodasugisaki2004_subcomp_en"
    source := ⟨"beck-oda-sugisaki-2004", "(5-b), p. 290"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This shelf is taller than that door is wide"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "subcomparative")] }

def negisland_ja : Datum :=
  { id := "beckodasugisaki2004_negisland_ja"
    source := ⟨"beck-oda-sugisaki-2004", "(6-a), p. 290"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "John-wa [dare-mo kawa-naka-tta no yori] takai hon-o katta"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "negative_island")] }

def negisland_en : Datum :=
  { id := "beckodasugisaki2004_negisland_en"
    source := ⟨"beck-oda-sugisaki-2004", "(6-b), p. 290"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John bought a more expensive book than nobody did"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "negative_island")] }

def all : List Datum := [amount_yori, degree_yori, subcomp_ja, subcomp_en, negisland_ja, negisland_en]

end BeckOdaSugisaki2004.Examples
