module

public import Linglib.Data.Examples.Schema

/-!
# `Landau2024b` — typed example data

Auto-generated from `Linglib/Data/Examples/Landau2024b.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Landau2024b.Examples`.
-/

@[expose] public section

namespace Landau2024b.Examples

def ex_15a : Datum :=
  { id := "landau2024b_15a"
    source := ⟨"landau-2024b", "(15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I persuaded John for Bill to come."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "persuade"), ("embeddedSubject", "for")] }

def ex_15b : Datum :=
  { id := "landau2024b_15b"
    source := ⟨"landau-2024b", "(15b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I persuaded John for him to come."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "persuade"), ("embeddedSubject", "for")] }

def ex_48a : Datum :=
  { id := "landau2024b_48a"
    source := ⟨"landau-2024b", "(48a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John arranged to meet at noon."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "arrange"), ("embeddedSubject", "PRO")] }

def ex_48b : Datum :=
  { id := "landau2024b_48b"
    source := ⟨"landau-2024b", "(48b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John managed to meet at noon."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "manage"), ("embeddedSubject", "PRO")] }

def ex_49a : Datum :=
  { id := "landau2024b_49a"
    source := ⟨"landau-2024b", "(49a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John arranged for us/them to meet at noon."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "arrange"), ("embeddedSubject", "for")] }

def ex_49b : Datum :=
  { id := "landau2024b_49b"
    source := ⟨"landau-2024b", "(49b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John managed for us/them to meet at noon"
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "manage"), ("embeddedSubject", "for")] }

def ex_52c : Datum :=
  { id := "landau2024b_52c"
    source := ⟨"landau-2024b", "(52c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Suzan could not attend, so she persuaded the chair to meet without her."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "persuade"), ("embeddedSubject", "PRO")] }

def ex_56a : Datum :=
  { id := "landau2024b_56a"
    source := ⟨"landau-2024b", "(56a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John wanted for us to meet without him."
    glossedTokens := []
    context := "Mary and I had a fight and we stopped talking. John, a good friend of both of us, is keen on getting us to be friends again. He insists that we meet but he feels it would be best if the meeting would be just between Mary and myself, without him."
    judgment := .acceptable
    alternatives := []
    readings := [("free", .acceptable)]
    paperFeatures := [("verb", "want"), ("embeddedSubject", "for"), ("diagnostic", "conditionB")] }

def ex_56b : Datum :=
  { id := "landau2024b_56b"
    source := ⟨"landau-2024b", "(56b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John wanted to meet without him."
    glossedTokens := []
    context := "Mary and I had a fight and we stopped talking. John, a good friend of both of us, is keen on getting us to be friends again. He insists that we meet but he feels it would be best if the meeting would be just between Mary and myself, without him."
    judgment := .acceptable
    alternatives := []
    readings := [("free", .ungrammatical)]
    paperFeatures := [("verb", "want"), ("embeddedSubject", "PRO"), ("diagnostic", "conditionB")] }

def ex_57c : Datum :=
  { id := "landau2024b_57c"
    source := ⟨"landau-2024b", "(57c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I advised John for his team to meet without him."
    glossedTokens := []
    context := "John annoyed a number of people on his team at work, right before an important deadline. He asks for my advice on what they should do."
    judgment := .acceptable
    alternatives := []
    readings := [("free", .acceptable)]
    paperFeatures := [("verb", "advise"), ("embeddedSubject", "for"), ("diagnostic", "conditionB")] }

def ex_57d : Datum :=
  { id := "landau2024b_57d"
    source := ⟨"landau-2024b", "(57d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I advised John to meet without him."
    glossedTokens := []
    context := "John annoyed a number of people on his team at work, right before an important deadline. He asks for my advice on what they should do."
    judgment := .acceptable
    alternatives := []
    readings := [("free", .ungrammatical)]
    paperFeatures := [("verb", "advise"), ("embeddedSubject", "PRO"), ("diagnostic", "conditionB")] }

def ex_58a : Datum :=
  { id := "landau2024b_58a"
    source := ⟨"landau-2024b", "(58a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Only Peter arranged for his family/them to meet."
    glossedTokens := []
    context := "Peter, Jane and Adam are each making arrangements to have a meeting with their respective families."
    judgment := .acceptable
    alternatives := []
    readings := [("strict", .acceptable), ("sloppy", .acceptable)]
    paperFeatures := [("verb", "arrange"), ("embeddedSubject", "for"), ("diagnostic", "only")] }

def ex_58b : Datum :=
  { id := "landau2024b_58b"
    source := ⟨"landau-2024b", "(58b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Only Peter arranged to meet."
    glossedTokens := []
    context := "Peter, Jane and Adam are each making arrangements to have a meeting with their respective families."
    judgment := .acceptable
    alternatives := []
    readings := [("strict", .unacceptable), ("sloppy", .acceptable)]
    paperFeatures := [("verb", "arrange"), ("embeddedSubject", "PRO"), ("diagnostic", "only")] }

def ex_59a : Datum :=
  { id := "landau2024b_59a"
    source := ⟨"landau-2024b", "(59a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Only Peter arranged for his family/them to meet."
    glossedTokens := []
    context := "Peter, Jane and Adam are each making arrangements for Peter's family to meet."
    judgment := .acceptable
    alternatives := []
    readings := [("strict", .acceptable), ("sloppy", .acceptable)]
    paperFeatures := [("verb", "arrange"), ("embeddedSubject", "for"), ("diagnostic", "only")] }

def ex_59b : Datum :=
  { id := "landau2024b_59b"
    source := ⟨"landau-2024b", "(59b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Only Peter arranged to meet."
    glossedTokens := []
    context := "Peter, Jane and Adam are each making arrangements for Peter's family to meet."
    judgment := .acceptable
    alternatives := []
    readings := [("strict", .unacceptable), ("sloppy", .acceptable)]
    paperFeatures := [("verb", "arrange"), ("embeddedSubject", "PRO"), ("diagnostic", "only")] }

def all : List Datum := [ex_15a, ex_15b, ex_48a, ex_48b, ex_49a, ex_49b, ex_52c, ex_56a, ex_56b, ex_57c, ex_57d, ex_58a, ex_58b, ex_59a, ex_59b]

end Landau2024b.Examples
