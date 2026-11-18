module

public import Linglib.Data.Examples.Schema

/-!
# `Thomas2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Thomas2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Thomas2026.Examples`.
-/

@[expose] public section

namespace Thomas2026.Examples

def ex_2 : Datum :=
  { id := "thomas2026_2"
    source := ⟨"thomas-2026", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Avery invited Bailey. She invited Cameron, too."
    glossedTokens := []
    context := "Q: Who did Avery invite?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "satisfied")] }

def ex_3 : Datum :=
  { id := "thomas2026_3"
    source := ⟨"thomas-2026", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Tonight [Sam]F is having dinner in New York, too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "antecedent_violation"), ("felicity", "infelicitous")] }

def ex_5a : Datum :=
  { id := "thomas2026_5a"
    source := ⟨"thomas-2026", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I like [pizza]F, and I like [spaghetti]F, too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "satisfied")] }

def ex_5b : Datum :=
  { id := "thomas2026_5b"
    source := ⟨"thomas-2026", "(5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't like [pizza]F, and I don't like [spaghetti]F, either."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "either"), ("use_type", "standard")] }

def ex_11 : Datum :=
  { id := "thomas2026_11"
    source := ⟨"thomas-2026", "(11), (29a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sam is happy. He's ecstatic, too."
    glossedTokens := []
    context := "RQ: What is Sam's emotional state?"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "prejacent_violation_i")] }

def ex_12 : Datum :=
  { id := "thomas2026_12"
    source := ⟨"thomas-2026", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: I love you. B: I love you, too."
    glossedTokens := []
    context := "Q: Who loves whom?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "satisfied")] }

def ex_13 : Datum :=
  { id := "thomas2026_13"
    source := ⟨"thomas-2026", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John ate pizza. Mary ate spaghetti, too."
    glossedTokens := []
    context := "Q: Who ate what?"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard")] }

def ex_18c : Datum :=
  { id := "thomas2026_18c"
    source := ⟨"thomas-2026", "(18c), (65)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A room just opened up at this hotel. It looks like a fancy one, too."
    glossedTokens := []
    context := "A and some traveling companions are looking for a place to stay during their upcoming vacation. A is searching for a hotel room on the internet. Q: What would be a good hotel to stay at?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "argumentBuilding"), ("def64_status", "satisfied")] }

def ex_19c : Datum :=
  { id := "thomas2026_19c"
    source := ⟨"thomas-2026", "(19c), (66)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A room just opened up at this hotel. It looks like a dingy one, (#too)."
    glossedTokens := []
    context := "A and companions are looking for a nice hotel room to stay in."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "argumentBuilding"), ("def64_status", "conjunction_violation")] }

def ex_20b : Datum :=
  { id := "thomas2026_20b"
    source := ⟨"thomas-2026", "(20b), (67)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A room just opened up at this hotel. It looks like a dingy one, too."
    glossedTokens := []
    context := "A's band is looking for a dingy hotel room in which to shoot a music video. Q: Where would be a good place to shoot our music video?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "argumentBuilding"), ("def64_status", "satisfied")] }

def ex_24 : Datum :=
  { id := "thomas2026_24"
    source := ⟨"thomas-2026", "(24), (69)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I eat a lot of pizza. I like spaghetti, too."
    glossedTokens := []
    context := "RQ: What foods do you like?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "satisfied")] }

def ex_25 : Datum :=
  { id := "thomas2026_25"
    source := ⟨"thomas-2026", "(25)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dogs are mammals. I had pancakes for breakfast, too."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "conjunction_violation")] }

def ex_29bA : Datum :=
  { id := "thomas2026_29bA"
    source := ⟨"thomas-2026", "(29b A)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sam's fingerprints were found on the cookie jar. He stole the cookies, too."
    glossedTokens := []
    context := "RQ: Who stole the cookies?"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "prejacent_violation_i")] }

def ex_29bA2 : Datum :=
  { id := "thomas2026_29bA2"
    source := ⟨"thomas-2026", "(29b A′)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sam's fingerprints were found on the cookie jar. He has crumbs on his shirt, too."
    glossedTokens := []
    context := "RQ: Who stole the cookies?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "argumentBuilding"), ("def64_status", "satisfied")] }

def ex_30A : Datum :=
  { id := "thomas2026_30A"
    source := ⟨"thomas-2026", "(30 A)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Avery plays an instrument. Bailey plays the cello, (#too)."
    glossedTokens := []
    context := "RQ: Who plays an instrument?"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "prejacent_violation_ii")] }

def ex_30A2 : Datum :=
  { id := "thomas2026_30A2"
    source := ⟨"thomas-2026", "(30 A′)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Avery plays the cello. Bailey plays an instrument, too."
    glossedTokens := []
    context := "RQ: Who plays an instrument?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "satisfied")] }

def ex_68 : Datum :=
  { id := "thomas2026_68"
    source := ⟨"thomas-2026", "(68)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: She invited Bailey and Cameron. B: She invited Dana, too."
    glossedTokens := []
    context := "Q: Who are some people Avery invited?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "satisfied")] }

def ex_70 : Datum :=
  { id := "thomas2026_70"
    source := ⟨"thomas-2026", "(70)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: She invited Bailey, Cameron, and Dana. B: She invited Ellis, too."
    glossedTokens := []
    context := "Q: Who all did Avery invite?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "satisfied")] }

def ex_71 : Datum :=
  { id := "thomas2026_71"
    source := ⟨"thomas-2026", "(71)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "(Well,) she invited Bailey.↑ ... She invited Cameron, too."
    glossedTokens := []
    context := "Q: Who are some people Avery invited?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "satisfied")] }

def ex_72 : Datum :=
  { id := "thomas2026_72"
    source := ⟨"thomas-2026", "(72)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: She invited Bailey and Cameron. B: Dogs are mammals, too."
    glossedTokens := []
    context := "Q: Who are some people Avery invited?"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "conjunction_violation")] }

def all : List Datum := [ex_2, ex_3, ex_5a, ex_5b, ex_11, ex_12, ex_13, ex_18c, ex_19c, ex_20b, ex_24, ex_25, ex_29bA, ex_29bA2, ex_30A, ex_30A2, ex_68, ex_70, ex_71, ex_72]

end Thomas2026.Examples
