module

public import Linglib.Data.Examples.Schema

/-!
# `Beavers2010` — typed example data

Auto-generated from `Linglib/Data/Examples/Beavers2010.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Beavers2010.Examples`.
-/

@[expose] public section

namespace Beavers2010.Examples

def ex_9a : Datum :=
  { id := "beavers2010_9a"
    source := ⟨"beavers-2010", "(9a)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "John loaded the hay onto the wagon."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "locative"), ("direct", "theme")] }

def ex_9b : Datum :=
  { id := "beavers2010_9b"
    source := ⟨"beavers-2010", "(9b)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "John loaded the wagon with the hay."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "locative"), ("direct", "location")] }

def ex_10a : Datum :=
  { id := "beavers2010_10a"
    source := ⟨"beavers-2010", "(10a)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "Kim loaded the hay onto the wagon, but still needed a truck for the rest."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "locative"), ("diagnostic", "holistic effect")] }

def ex_18a : Datum :=
  { id := "beavers2010_18a"
    source := ⟨"beavers-2010", "(18a)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "John cut the diamond on the glass."
    glossedTokens := []
    context := "John moves a sharp-edged diamond forcefully into contact with a piece of glass."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "locative"), ("verb class", "cut/slice")] }

def ex_18b : Datum :=
  { id := "beavers2010_18b"
    source := ⟨"beavers-2010", "(18b)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "John cut the glass with the diamond."
    glossedTokens := []
    context := "Same scenario; the glass is damaged rather than the diamond."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "locative"), ("verb class", "cut/slice")] }

def ex_20a : Datum :=
  { id := "beavers2010_20a"
    source := ⟨"beavers-2010", "(20a)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "Marie cut the rope."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "conative"), ("verb class", "cut")] }

def ex_20b : Datum :=
  { id := "beavers2010_20b"
    source := ⟨"beavers-2010", "(20b)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "Marie cut at the rope."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "conative"), ("verb class", "cut")] }

def ex_21a : Datum :=
  { id := "beavers2010_21a"
    source := ⟨"beavers-2010", "(21a)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "Marie ate her cake."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "conative"), ("verb class", "consumption")] }

def ex_21b : Datum :=
  { id := "beavers2010_21b"
    source := ⟨"beavers-2010", "(21b)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "Marie ate at her cake."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "conative"), ("verb class", "consumption")] }

def ex_22a : Datum :=
  { id := "beavers2010_22a"
    source := ⟨"beavers-2010", "(22a)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "Marie hit Defarge."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "conative"), ("verb class", "impact")] }

def ex_22b : Datum :=
  { id := "beavers2010_22b"
    source := ⟨"beavers-2010", "(22b)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "Marie hit at Defarge."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "conative"), ("verb class", "impact")] }

def ex_24a : Datum :=
  { id := "beavers2010_24a"
    source := ⟨"beavers-2010", "(24a)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "John hit the fence with the stick."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "locative"), ("contrast", "none")] }

def ex_24b : Datum :=
  { id := "beavers2010_24b"
    source := ⟨"beavers-2010", "(24b)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "John hit the stick against the fence."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "locative"), ("contrast", "none")] }

def ex_25a : Datum :=
  { id := "beavers2010_25a"
    source := ⟨"beavers-2010", "(25a)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "John cleared the table of the dishes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "locative"), ("contrast", "none")] }

def ex_25b : Datum :=
  { id := "beavers2010_25b"
    source := ⟨"beavers-2010", "(25b)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "John cleared the dishes off the table."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "locative"), ("contrast", "none")] }

def ex_29 : Datum :=
  { id := "beavers2010_29"
    source := ⟨"beavers-2010", "(29)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "The tailor lengthened the jeans to 32ins."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("degree", "quantized"), ("diagnostic", "telicity")] }

def ex_30 : Datum :=
  { id := "beavers2010_30"
    source := ⟨"beavers-2010", "(30)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "The tailor lengthened the jeans."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("degree", "nonquantized"), ("diagnostic", "telicity")] }

def ex_43a : Datum :=
  { id := "beavers2010_43a"
    source := ⟨"beavers-2010", "(43a)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "John ate the pizza, but nothing is different about it."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("variant", "eat"), ("diagnostic", "nothing different")] }

def ex_43b : Datum :=
  { id := "beavers2010_43b"
    source := ⟨"beavers-2010", "(43b)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "John ate at the pizza, but nothing is different about it."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("variant", "eat at"), ("diagnostic", "nothing different")] }

def ex_43c : Datum :=
  { id := "beavers2010_43c"
    source := ⟨"beavers-2010", "(43c)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "What happened to the pizza is John ate it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("variant", "eat"), ("diagnostic", "what happened")] }

def ex_43d : Datum :=
  { id := "beavers2010_43d"
    source := ⟨"beavers-2010", "(43d)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "What happened to the pizza is John ate at it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("variant", "eat at"), ("diagnostic", "what happened")] }

def ex_45a : Datum :=
  { id := "beavers2010_45a"
    source := ⟨"beavers-2010", "(45a)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "John cut the rope, but nothing is different about it."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("variant", "cut"), ("diagnostic", "nothing different")] }

def ex_45b : Datum :=
  { id := "beavers2010_45b"
    source := ⟨"beavers-2010", "(45b)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "John cut at the rope, but nothing is different about it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("variant", "cut at"), ("diagnostic", "nothing different")] }

def ex_45c : Datum :=
  { id := "beavers2010_45c"
    source := ⟨"beavers-2010", "(45c)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "What happened to the rope is that John cut it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("variant", "cut"), ("diagnostic", "what happened")] }

def ex_45d : Datum :=
  { id := "beavers2010_45d"
    source := ⟨"beavers-2010", "(45d)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "What happened to the rope is that John cut at it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("variant", "cut at"), ("diagnostic", "what happened")] }

def ex_47a_hit : Datum :=
  { id := "beavers2010_47a_hit"
    source := ⟨"beavers-2010", "(47a)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "John hit the rope, but nothing is different about it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("variant", "hit"), ("diagnostic", "nothing different")] }

def ex_47a_hitat : Datum :=
  { id := "beavers2010_47a_hitat"
    source := ⟨"beavers-2010", "(47a)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "John hit at the rope, but nothing is different about it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("variant", "hit at"), ("diagnostic", "nothing different")] }

def ex_48a : Datum :=
  { id := "beavers2010_48a"
    source := ⟨"beavers-2010", "(48a)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "What happened to the rope is John hit it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("variant", "hit"), ("diagnostic", "what happened")] }

def ex_48b : Datum :=
  { id := "beavers2010_48b"
    source := ⟨"beavers-2010", "(48b)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "What happened to the rope is John hit at it."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("variant", "hit at"), ("diagnostic", "what happened")] }

def ex_81a : Datum :=
  { id := "beavers2010_81a"
    source := ⟨"beavers-2010", "(81a)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "John climbed the stairs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "traversal"), ("degree", "totally traversed")] }

def ex_81b : Datum :=
  { id := "beavers2010_81b"
    source := ⟨"beavers-2010", "(81b)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "John climbed up the stairs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "traversal"), ("degree", "traversed")] }

def ex_88a : Datum :=
  { id := "beavers2010_88a"
    source := ⟨"beavers-2010", "(88a)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "Kim mailed London a ball."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := [("London as an agency (Scotland Yard reading)", .acceptable)]
    paperFeatures := [("alternation", "dative"), ("direct", "recipient")] }

def ex_88b : Datum :=
  { id := "beavers2010_88b"
    source := ⟨"beavers-2010", "(88b)"⟩
    reportedIn := none
    method := some .introspection
    language := "stan1293"
    primaryText := "Kim mailed a ball to London."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("alternation", "dative"), ("oblique", "goal")] }

def all : List Datum := [ex_9a, ex_9b, ex_10a, ex_18a, ex_18b, ex_20a, ex_20b, ex_21a, ex_21b, ex_22a, ex_22b, ex_24a, ex_24b, ex_25a, ex_25b, ex_29, ex_30, ex_43a, ex_43b, ex_43c, ex_43d, ex_45a, ex_45b, ex_45c, ex_45d, ex_47a_hit, ex_47a_hitat, ex_48a, ex_48b, ex_81a, ex_81b, ex_88a, ex_88b]

end Beavers2010.Examples
