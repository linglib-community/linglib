module

public import Linglib.Data.Examples.Schema

/-!
# `Homer2021` — typed example data

Auto-generated from `Linglib/Data/Examples/Homer2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Homer2021.Examples`.
-/

@[expose] public section

namespace Homer2021.Examples

def ex18 : Datum :=
  { id := "homer2021_ex18"
    source := ⟨"homer-2021", "(18)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Il n'est pas impossible que Jean ait fait quoi que ce soit pour aider la Mafia."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("item", "quoi que ce soit"), ("clause", "none"), ("superordinate", "not impossible")] }

def ex19 : Datum :=
  { id := "homer2021_ex19"
    source := ⟨"homer-2021", "(19)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Il est impossible que Jean n'ait pas fait quoi que ce soit pour aider…"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "quoi que ce soit"), ("clause", "negation"), ("superordinate", "impossible")] }

def ex24 : Datum :=
  { id := "homer2021_ex24"
    source := ⟨"homer-2021", "(24)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "S'il est impossible que Jean ait fait quoi que ce soit pour aider la Mafia, je lui présenterai mes excuses."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "quoi que ce soit"), ("clause", "none"), ("superordinate", "if impossible")] }

def ex32 : Datum :=
  { id := "homer2021_ex32"
    source := ⟨"homer-2021", "(32)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Il n'est pas impossible que Jean n'ait pas fait quoi que ce soit pour aider la Mafia."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "quoi que ce soit"), ("clause", "negation"), ("superordinate", "not impossible")] }

def ex41a : Datum :=
  { id := "homer2021_ex41a"
    source := ⟨"homer-2021", "(41a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "When Fred speaks French, Jean-Paul doesn't understand something."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("narrowest scope of some", .ungrammatical)]
    paperFeatures := [("item", "some"), ("clause", "negation")] }

def ex42a : Datum :=
  { id := "homer2021_ex42a"
    source := ⟨"homer-2021", "(42a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't claim that Jean-Paul understands something."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("narrowest scope of some", .acceptable)]
    paperFeatures := [("item", "some"), ("clause", "none"), ("superordinate", "not claim")] }

def ex42b : Datum :=
  { id := "homer2021_ex42b"
    source := ⟨"homer-2021", "(42b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is impossible that Jean-Paul understands something."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("narrowest scope of some", .acceptable)]
    paperFeatures := [("item", "some"), ("clause", "none"), ("superordinate", "impossible")] }

def ex46a : Datum :=
  { id := "homer2021_ex46a"
    source := ⟨"homer-2021", "(46a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I'm not sure that Jean-Paul doesn't understand something."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("narrowest scope of some", .acceptable)]
    paperFeatures := [("item", "some"), ("clause", "negation"), ("superordinate", "not sure")] }

def ex46b : Datum :=
  { id := "homer2021_ex46b"
    source := ⟨"homer-2021", "(46b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Jean-Paul doesn't understand something, he has no notion of French at all."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("narrowest scope of some", .acceptable)]
    paperFeatures := [("item", "some"), ("clause", "negation"), ("superordinate", "if")] }

def ex48a : Datum :=
  { id := "homer2021_ex48a"
    source := ⟨"homer-2021", "(48a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is impossible that John doesn't understand something."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("narrowest scope of some", .acceptable)]
    paperFeatures := [("item", "some"), ("clause", "negation"), ("superordinate", "impossible")] }

def ex48b : Datum :=
  { id := "homer2021_ex48b"
    source := ⟨"homer-2021", "(48b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is not impossible that John doesn't understand something."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("narrowest scope of some", .ungrammatical)]
    paperFeatures := [("item", "some"), ("clause", "negation"), ("superordinate", "not impossible")] }

def ex48c : Datum :=
  { id := "homer2021_ex48c"
    source := ⟨"homer-2021", "(48c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not that it is impossible that John doesn't understand something."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("narrowest scope of some", .acceptable)]
    paperFeatures := [("item", "some"), ("clause", "negation"), ("superordinate", "not that impossible")] }

def ex50e : Datum :=
  { id := "homer2021_ex50e"
    source := ⟨"homer-2021", "(50e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't drink wine and any coffee."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("item", "any"), ("clause", "negation"), ("connective", "and")] }

def ex51b : Datum :=
  { id := "homer2021_ex51b"
    source := ⟨"homer-2021", "(51b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't drink wine or any coffee."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "any"), ("clause", "negation"), ("connective", "or")] }

def ex56d : Datum :=
  { id := "homer2021_ex56d"
    source := ⟨"homer-2021", "(56d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't drink wine and some coffee."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("narrowest scope of some", .acceptable)]
    paperFeatures := [("item", "some"), ("clause", "negation"), ("connective", "and")] }

def ex56e : Datum :=
  { id := "homer2021_ex56e"
    source := ⟨"homer-2021", "(56e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't drink wine or some coffee."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("narrowest scope of some", .ungrammatical)]
    paperFeatures := [("item", "some"), ("clause", "negation"), ("connective", "or")] }

def ex92b : Datum :=
  { id := "homer2021_ex92b"
    source := ⟨"homer-2021", "(92b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is impossible that someone stole anything."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("IMPOS.≫SOME", .ungrammatical)]
    paperFeatures := [("subject", "someone"), ("object", "anything"), ("superordinate", "impossible"), ("clause", "none")] }

def ex98 : Datum :=
  { id := "homer2021_ex98"
    source := ⟨"homer-2021", "(98)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's impossible that someone isn't eating anything."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("IMPOS.≫NEG≫SOME≫ANY", .ungrammatical), ("IMPOS.≫SOME≫NEG≫ANY", .acceptable)]
    paperFeatures := [("subject", "someone"), ("object", "anything"), ("superordinate", "impossible"), ("clause", "negation")] }

def ex103b : Datum :=
  { id := "homer2021_ex103b"
    source := ⟨"homer-2021", "(103b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is impossible that anyone stole something."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("IMPOS.≫SOME", .acceptable)]
    paperFeatures := [("subject", "anyone"), ("object", "something"), ("superordinate", "impossible"), ("clause", "none")] }

def ex122b : Datum :=
  { id := "homer2021_ex122b"
    source := ⟨"homer-2021", "(122b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I'm not sure that someone understood anything."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("NEG≫SOME", .ungrammatical)]
    paperFeatures := [("subject", "someone"), ("object", "anything"), ("superordinate", "not sure"), ("clause", "none")] }

def all : List Datum := [ex18, ex19, ex24, ex32, ex41a, ex42a, ex42b, ex46a, ex46b, ex48a, ex48b, ex48c, ex50e, ex51b, ex56d, ex56e, ex92b, ex98, ex103b, ex122b]

end Homer2021.Examples
