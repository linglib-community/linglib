module

public import Linglib.Data.Examples.Schema

/-!
# `AnandHardtMcCloskey2025` — typed example data

Auto-generated from `Linglib/Data/Examples/AnandHardtMcCloskey2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AnandHardtMcCloskey2025.Examples`.
-/

@[expose] public section

namespace AnandHardtMcCloskey2025.Examples

def ex_13a : Datum :=
  { id := "anandhardtmccloskey2025_13a"
    source := ⟨"anand-hardt-mccloskey-2025", "(13a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "\"The board believes that a 'one-size-fits-all' approach to financial market regulation is inappropriate,\" Phillips said. \"A particular market's characteristics determine whether government regulation is necessary, and if so, what form [government regulation is necessary IN].\""
    glossedTokens := []
    context := "Corpus-attested sluice with a stranded nonargument preposition in the ellipsis site that has no antecedent source. The bracketed capitalized material is the elided clause, not pronounced."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "sluicing"), ("ppType", "nonargument")] }

def ex_13b : Datum :=
  { id := "anandhardtmccloskey2025_13b"
    source := ⟨"anand-hardt-mccloskey-2025", "(13b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "When the officer asked me about her, I remembered meeting her but I couldn't say what date [I MET her ON]."
    glossedTokens := []
    context := "Corpus-attested sluice with a stranded nonargument PP 'on' in the ellipsis site that has no antecedent source. The bracketed capitalized material is the elided clause, not pronounced."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "sluicing"), ("ppType", "nonargument")] }

def ex_12c : Datum :=
  { id := "anandhardtmccloskey2025_12c"
    source := ⟨"anand-hardt-mccloskey-2025", "(12c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They're furious but it's unclear who."
    glossedTokens := []
    context := "The argument/nonargument PP contrast: (12a) 'at who(m)', with the sprouted PP moved out of the ellipsis site, is fine, (12b) pied-piped 'who at' is fine, but the bare sluice fails because the possibly semantically vacuous preposition 'at' is within the argument domain of the elided clause, has no counterpart in the antecedent, and fails the Isomorphism Condition."
    judgment := .ungrammatical
    alternatives := [("They're furious but it's unclear who at.", .acceptable)]
    readings := []
    paperFeatures := [("phenomenon", "sluicing"), ("ppType", "argument")] }

def ex_15a : Datum :=
  { id := "anandhardtmccloskey2025_15a"
    source := ⟨"anand-hardt-mccloskey-2025", "(15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He is very loyal, but I don't know who."
    glossedTokens := []
    context := "Sluicing fails completely when the argument domain itself has no match: no vP in the antecedent whose argument domain matches 'who [he is loyal to]'."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "sluicing"), ("ppType", "argument")] }

def all : List Datum := [ex_13a, ex_13b, ex_12c, ex_15a]

end AnandHardtMcCloskey2025.Examples
