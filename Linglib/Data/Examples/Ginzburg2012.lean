module

public import Linglib.Data.Examples.Schema

/-!
# `Ginzburg2012` — typed example data

Auto-generated from `Linglib/Data/Examples/Ginzburg2012.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Ginzburg2012.Examples`.
-/

@[expose] public section

namespace Ginzburg2012.Examples

def ex_22a : Datum :=
  { id := "ginzburg2012_22a"
    source := ⟨"ginzburg-2012", "Ch. 2 (22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Who does Bo admire? B: Bo?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("short answer: Does Bo admire Bo?", .acceptable), ("clausal confirmation: Are you asking who Bo (of all people) admires?", .acceptable), ("intended content: Who do you mean 'Bo'?", .acceptable)]
    paperFeatures := [("speaker", "addressee")] }

def ex_22b : Datum :=
  { id := "ginzburg2012_22b"
    source := ⟨"ginzburg-2012", "Ch. 2 (22b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Who does Bo admire? Bo?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("short answer: Does Bo admire Bo?", .acceptable), ("self-correction: Did I say 'Bo'?", .acceptable)]
    paperFeatures := [("speaker", "original speaker")] }

def ex_23a : Datum :=
  { id := "ginzburg2012_23a"
    source := ⟨"ginzburg-2012", "Ch. 2 (23a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Which members of this audience own a parakeet? Why?"
    glossedTokens := []
    context := "A keeps the turn."
    judgment := .acceptable
    contrasts := []
    readings := [("Why own a parakeet?", .acceptable), ("Why are you asking which members of this audience own a parakeet?", .unacceptable)]
    paperFeatures := [("turn", "kept")] }

def ex_23b : Datum :=
  { id := "ginzburg2012_23b"
    source := ⟨"ginzburg-2012", "Ch. 2 (23b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Which members of this audience own a parakeet? B: Why?"
    glossedTokens := []
    context := "B takes the turn."
    judgment := .acceptable
    contrasts := []
    readings := [("Why are you asking which members of this audience own a parakeet?", .acceptable), ("Why own a parakeet?", .unacceptable)]
    paperFeatures := [("turn", "taken")] }

def ex_23c : Datum :=
  { id := "ginzburg2012_23c"
    source := ⟨"ginzburg-2012", "Ch. 2 (23c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Which members of this audience own a parakeet? Why am I asking this question?"
    glossedTokens := []
    context := "A keeps the turn."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("turn", "kept")] }

def ex_54 : Datum :=
  { id := "ginzburg2012_54"
    source := ⟨"ginzburg-2012", "Ch. 4 (54)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Hi. B: Hi. A: Who's coming tomorrow? B: Several colleagues of mine (are coming). A: I see. B: Mike (is coming) too."
    glossedTokens := []
    context := "Taking place conversation-initially."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_65 : Datum :=
  { id := "ginzburg2012_65"
    source := ⟨"ginzburg-2012", "Ch. 4 (65)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Who should we invite for tomorrow? B: Who will agree to come? A: Helen and Jelle and Fran and maybe Sunil. B: (a) I see. (b) So, Jelle I think. A: OK."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_67 : Datum :=
  { id := "ginzburg2012_67"
    source := ⟨"ginzburg-2012", "Ch. 4 (67)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: (a) Bo is now in Essen, (b) is he? B: Yes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_78 : Datum :=
  { id := "ginzburg2012_78"
    source := ⟨"ginzburg-2012", "Ch. 4 (78)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: (1a) Who will Max be inviting? (1b) When will these guests be arriving? B: Mary and Bill. A: Aha. B: Tomorrow or the day after most likely."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_95 : Datum :=
  { id := "ginzburg2012_95"
    source := ⟨"ginzburg-2012", "Ch. 4 (95)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Hi. B: I'm off. A: OK. B: Bye."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("genre", "CasualChat")] }

def ch6_90 : Datum :=
  { id := "ginzburg2012_ch6_90"
    source := ⟨"ginzburg-2012", "Ch. 6 (90)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Is George here? B: Is WHO here? A: George Sand. B: Ah, no."
    glossedTokens := []
    context := "B is unsure about the intended reference of 'George'."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("ccur", "Parameter Focussing")] }

def ex_24a : Datum :=
  { id := "ginzburg2012_24a"
    source := ⟨"ginzburg-2012", "Ch. 8 (24a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Did Bo leave? B: Bo? A: Your cousin."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("repair", "other-initiated")] }

def ex_24b : Datum :=
  { id := "ginzburg2012_24b"
    source := ⟨"ginzburg-2012", "Ch. 8 (24b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: [Did Bo + {I mean} my cousin] leave?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("repair", "self-initiated")] }

def all : List Datum := [ex_22a, ex_22b, ex_23a, ex_23b, ex_23c, ex_54, ex_65, ex_67, ex_78, ex_95, ch6_90, ex_24a, ex_24b]

end Ginzburg2012.Examples
