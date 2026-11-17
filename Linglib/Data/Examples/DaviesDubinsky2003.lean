module

public import Linglib.Data.Examples.Schema

/-!
# `DaviesDubinsky2003` — typed example data

Auto-generated from `Linglib/Data/Examples/DaviesDubinsky2003.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace DaviesDubinsky2003.Examples`.
-/

@[expose] public section

namespace DaviesDubinsky2003.Examples

def ex52a_write : Datum :=
  { id := "daviesdubinsky2003_ex52a_write"
    source := ⟨"davies-dubinsky-2003", "(52a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did you write those essays about?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("wh", "fronted"), ("verb", "write"), ("creation", "yes"), ("object", "definite")] }

def ex52a_read : Datum :=
  { id := "daviesdubinsky2003_ex52a_read"
    source := ⟨"davies-dubinsky-2003", "(52a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did you read those essays about?"
    glossedTokens := []
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    paperFeatures := [("wh", "fronted"), ("verb", "read"), ("creation", "no"), ("object", "definite")] }

def ex52b_write : Datum :=
  { id := "daviesdubinsky2003_ex52b_write"
    source := ⟨"davies-dubinsky-2003", "(52b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did you write essays about?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("wh", "fronted"), ("verb", "write"), ("creation", "yes"), ("object", "indefinite")] }

def ex52b_read : Datum :=
  { id := "daviesdubinsky2003_ex52b_read"
    source := ⟨"davies-dubinsky-2003", "(52b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did you read essays about?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("wh", "fronted"), ("verb", "read"), ("creation", "no"), ("object", "indefinite")] }

def ex53a_tell : Datum :=
  { id := "daviesdubinsky2003_ex53a_tell"
    source := ⟨"davies-dubinsky-2003", "(53a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did you tell those jokes about?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("wh", "fronted"), ("verb", "tell"), ("creation", "yes"), ("object", "definite")] }

def ex53a_hear : Datum :=
  { id := "daviesdubinsky2003_ex53a_hear"
    source := ⟨"davies-dubinsky-2003", "(53a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did you hear those jokes about?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("wh", "fronted"), ("verb", "hear"), ("creation", "no"), ("object", "definite")] }

def ex53b_tell : Datum :=
  { id := "daviesdubinsky2003_ex53b_tell"
    source := ⟨"davies-dubinsky-2003", "(53b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did you tell jokes about?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("wh", "fronted"), ("verb", "tell"), ("creation", "yes"), ("object", "indefinite")] }

def ex53b_hear : Datum :=
  { id := "daviesdubinsky2003_ex53b_hear"
    source := ⟨"davies-dubinsky-2003", "(53b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did you hear jokes about?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("wh", "fronted"), ("verb", "hear"), ("creation", "no"), ("object", "indefinite")] }

def ex54a_paint : Datum :=
  { id := "daviesdubinsky2003_ex54a_paint"
    source := ⟨"davies-dubinsky-2003", "(54a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did you paint that portrait of?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("wh", "fronted"), ("verb", "paint"), ("creation", "yes"), ("object", "definite")] }

def ex54a_see : Datum :=
  { id := "daviesdubinsky2003_ex54a_see"
    source := ⟨"davies-dubinsky-2003", "(54a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did you see that portrait of?"
    glossedTokens := []
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    paperFeatures := [("wh", "fronted"), ("verb", "see"), ("creation", "no"), ("object", "definite")] }

def ex54b_paint : Datum :=
  { id := "daviesdubinsky2003_ex54b_paint"
    source := ⟨"davies-dubinsky-2003", "(54b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did you paint a portrait of?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("wh", "fronted"), ("verb", "paint"), ("creation", "yes"), ("object", "indefinite")] }

def ex54b_see : Datum :=
  { id := "daviesdubinsky2003_ex54b_see"
    source := ⟨"davies-dubinsky-2003", "(54b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did you see a portrait of?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("wh", "fronted"), ("verb", "see"), ("creation", "no"), ("object", "indefinite")] }

def all : List Datum := [ex52a_write, ex52a_read, ex52b_write, ex52b_read, ex53a_tell, ex53a_hear, ex53b_tell, ex53b_hear, ex54a_paint, ex54a_see, ex54b_paint, ex54b_see]

end DaviesDubinsky2003.Examples
