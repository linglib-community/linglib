module

public import Linglib.Data.Examples.Schema

/-!
# `GinzburgCooper2004` — typed example data

Auto-generated from `Linglib/Data/Examples/GinzburgCooper2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace GinzburgCooper2004.Examples`.
-/

@[expose] public section

namespace GinzburgCooper2004.Examples

def ex_4a_bo : Datum :=
  { id := "ginzburgcooper2004_4a_bo"
    source := ⟨"ginzburg-cooper-2004", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Did Bo finagle a raise? B: Bo?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("clausal", .acceptable), ("constituent", .acceptable)]
    paperFeatures := [("antecedent", "Bo"), ("antecedentCat", "NP"), ("fragment", "Bo"), ("fragmentCat", "NP"), ("access", "shared")] }

def ex_4a_finagle : Datum :=
  { id := "ginzburgcooper2004_4a_finagle"
    source := ⟨"ginzburg-cooper-2004", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Did Bo finagle a raise? B: Finagle?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("clausal", .acceptable), ("constituent", .acceptable)]
    paperFeatures := [("antecedent", "finagle"), ("antecedentCat", "V[bse]"), ("fragment", "Finagle"), ("fragmentCat", "V[bse]"), ("access", "shared")] }

def ex_6a : Datum :=
  { id := "ginzburgcooper2004_6a"
    source := ⟨"ginzburg-cooper-2004", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "George: … you always had er er say every foot he had with a piece of spunyarn in the wire. Anon1: Spunyarn? George: Spunyarn, yes. Anon1: What's spunyarn? George: Well that's like er tarred rope."
    glossedTokens := []
    context := "British National Corpus, file H5G, sentences 193–196."
    judgment := .acceptable
    contrasts := []
    readings := [("clausal", .acceptable), ("constituent", .acceptable)]
    paperFeatures := [("antecedent", "spunyarn"), ("antecedentCat", "N"), ("fragment", "Spunyarn"), ("fragmentCat", "N"), ("access", "shared")] }

def ex_8a : Datum :=
  { id := "ginzburgcooper2004_8a"
    source := ⟨"ginzburg-cooper-2004", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Did Bo leave? B: My cousin?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("clausal", .acceptable), ("constituent", .acceptable)]
    paperFeatures := [("antecedent", "Bo"), ("antecedentCat", "NP"), ("fragment", "My cousin"), ("fragmentCat", "NP"), ("access", "shared")] }

def ex_8b : Datum :=
  { id := "ginzburgcooper2004_8b"
    source := ⟨"ginzburg-cooper-2004", "(8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Did she annoy Bo? B: Sue?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("clausal", .acceptable), ("constituent", .acceptable)]
    paperFeatures := [("antecedent", "she"), ("antecedentCat", "NP"), ("fragment", "Sue"), ("fragmentCat", "NP"), ("access", "shared")] }

def ex_8c : Datum :=
  { id := "ginzburgcooper2004_8c"
    source := ⟨"ginzburg-cooper-2004", "(8c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Did you bike to work yesterday? B: Cycle?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("clausal", .acceptable), ("constituent", .acceptable)]
    paperFeatures := [("antecedent", "bike"), ("antecedentCat", "V[bse]"), ("fragment", "Cycle"), ("fragmentCat", "V[bse]"), ("access", "shared")] }

def ex_9a : Datum :=
  { id := "ginzburgcooper2004_9a"
    source := ⟨"ginzburg-cooper-2004", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Did Bo leave? B: Who?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("clausal", .acceptable), ("constituent", .acceptable)]
    paperFeatures := [("antecedent", "Bo"), ("antecedentCat", "NP"), ("fragment", "Who"), ("fragmentCat", "NP"), ("access", "shared")] }

def ex_10a_him : Datum :=
  { id := "ginzburgcooper2004_10a_him"
    source := ⟨"ginzburg-cooper-2004", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: I phoned him. B: Him?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("antecedent", "him"), ("antecedentCat", "NP[acc]"), ("fragment", "Him"), ("fragmentCat", "NP[acc]"), ("access", "shared")] }

def ex_10a_he : Datum :=
  { id := "ginzburgcooper2004_10a_he"
    source := ⟨"ginzburg-cooper-2004", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: I phoned him. B: He?"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("antecedent", "him"), ("antecedentCat", "NP[acc]"), ("fragment", "He"), ("fragmentCat", "NP[nom]"), ("access", "shared")] }

def ex_10b_he : Datum :=
  { id := "ginzburgcooper2004_10b_he"
    source := ⟨"ginzburg-cooper-2004", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Did he phone you? B: He?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("antecedent", "he"), ("antecedentCat", "NP[nom]"), ("fragment", "He"), ("fragmentCat", "NP[nom]"), ("access", "shared")] }

def ex_10b_him : Datum :=
  { id := "ginzburgcooper2004_10b_him"
    source := ⟨"ginzburg-cooper-2004", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Did he phone you? B: Him?"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("antecedent", "he"), ("antecedentCat", "NP[nom]"), ("fragment", "Him"), ("fragmentCat", "NP[acc]"), ("access", "shared")] }

def ex_10c_adore : Datum :=
  { id := "ginzburgcooper2004_10c_adore"
    source := ⟨"ginzburg-cooper-2004", "(10c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Did he adore the book? B: Adore?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("antecedent", "adore"), ("antecedentCat", "V[bse]"), ("fragment", "Adore"), ("fragmentCat", "V[bse]"), ("access", "shared")] }

def ex_10c_adored : Datum :=
  { id := "ginzburgcooper2004_10c_adored"
    source := ⟨"ginzburg-cooper-2004", "(10c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Did he adore the book? B: Adored?"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("antecedent", "adore"), ("antecedentCat", "V[bse]"), ("fragment", "Adored"), ("fragmentCat", "V[fin]"), ("access", "shared")] }

def ex_10d_cycling : Datum :=
  { id := "ginzburgcooper2004_10d_cycling"
    source := ⟨"ginzburg-cooper-2004", "(10d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Were you cycling yesterday? B: Cycling?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("antecedent", "cycling"), ("antecedentCat", "V[prp]"), ("fragment", "Cycling"), ("fragmentCat", "V[prp]"), ("access", "shared")] }

def ex_10d_biking : Datum :=
  { id := "ginzburgcooper2004_10d_biking"
    source := ⟨"ginzburg-cooper-2004", "(10d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Were you cycling yesterday? B: Biking?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("antecedent", "cycling"), ("antecedentCat", "V[prp]"), ("fragment", "Biking"), ("fragmentCat", "V[prp]"), ("access", "shared")] }

def ex_10d_biked : Datum :=
  { id := "ginzburgcooper2004_10d_biked"
    source := ⟨"ginzburg-cooper-2004", "(10d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Were you cycling yesterday? B: Biked?"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("antecedent", "cycling"), ("antecedentCat", "V[prp]"), ("fragment", "Biked"), ("fragmentCat", "V[psp]"), ("access", "shared")] }

def ex_11 : Datum :=
  { id := "ginzburgcooper2004_11"
    source := ⟨"ginzburg-cooper-2004", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Let's hold the conference here. B: Here?"
    glossedTokens := []
    context := "A is located in Gothenburg, B in Hyderabad."
    judgment := .acceptable
    contrasts := []
    readings := [("clausal", .unacceptable), ("constituent", .acceptable)]
    paperFeatures := [("antecedent", "here"), ("antecedentCat", "AdvP"), ("fragment", "Here"), ("fragmentCat", "AdvP"), ("access", "distinct")] }

def ex_12 : Datum :=
  { id := "ginzburgcooper2004_12"
    source := ⟨"ginzburg-cooper-2004", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Let's hold the conference here. B: Here?"
    glossedTokens := []
    context := "A and B are both located in Gothenburg."
    judgment := .acceptable
    contrasts := []
    readings := [("clausal", .acceptable), ("constituent", .acceptable)]
    paperFeatures := [("antecedent", "here"), ("antecedentCat", "AdvP"), ("fragment", "Here"), ("fragmentCat", "AdvP"), ("access", "shared")] }

def ex_13a : Datum :=
  { id := "ginzburgcooper2004_13a"
    source := ⟨"ginzburg-cooper-2004", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Can I come in? B: I?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("clausal", .unacceptable), ("constituent", .acceptable)]
    paperFeatures := [("antecedent", "I"), ("antecedentCat", "NP[nom]"), ("fragment", "I"), ("fragmentCat", "NP[nom]"), ("access", "distinct")] }

def all : List Datum := [ex_4a_bo, ex_4a_finagle, ex_6a, ex_8a, ex_8b, ex_8c, ex_9a, ex_10a_him, ex_10a_he, ex_10b_he, ex_10b_him, ex_10c_adore, ex_10c_adored, ex_10d_cycling, ex_10d_biking, ex_10d_biked, ex_11, ex_12, ex_13a]

end GinzburgCooper2004.Examples
