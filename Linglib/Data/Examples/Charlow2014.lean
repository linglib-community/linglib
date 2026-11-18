module

public import Linglib.Data.Examples.Schema

/-!
# `Charlow2014` — typed example data

Auto-generated from `Linglib/Data/Examples/Charlow2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Charlow2014.Examples`.
-/

@[expose] public section

namespace Charlow2014.Examples

def ex4_1a : Datum :=
  { id := "charlow2014_ex4_1a"
    source := ⟨"charlow-2014", "(4.1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If a relative of mine dies, I'll inherit a house."
    glossedTokens := []
    context := "A single rich relative has put the speaker in her will, though the speaker may not know who."
    judgment := .acceptable
    contrasts := []
    readings := [("∃ > if", .acceptable)]
    paperFeatures := [] }

def ex4_1b : Datum :=
  { id := "charlow2014_ex4_1b"
    source := ⟨"charlow-2014", "(4.1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If every relative of mine dies, I'll inherit a house."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("∀ > if", .unacceptable)]
    paperFeatures := [] }

def ex4_1c : Datum :=
  { id := "charlow2014_ex4_1c"
    source := ⟨"charlow-2014", "(4.1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If no relative of mine dies, I'll inherit a house."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("¬∃ > if", .unacceptable)]
    paperFeatures := [] }

def ex4_2a : Datum :=
  { id := "charlow2014_ex4_2a"
    source := ⟨"charlow-2014", "(4.2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No student read every book that a teacher of his recommended."
    glossedTokens := []
    context := "Teachers vary with students but not with books."
    judgment := .acceptable
    contrasts := []
    readings := [("no > ∃ > every (intermediate)", .acceptable)]
    paperFeatures := [] }

def ex4_4 : Datum :=
  { id := "charlow2014_ex4_4"
    source := ⟨"schwarz-2001", "(25)"⟩
    reportedIn := some ⟨"charlow-2014", "(4.4)"⟩
    language := "stan1293"
    primaryText := "No candidate submitted a paper he had written."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("∃ > no (pronoun bound)", .unacceptable)]
    paperFeatures := [] }

def ex4_6 : Datum :=
  { id := "charlow2014_ex4_6"
    source := ⟨"charlow-2014", "(4.6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I didn't read a book by a famous linguist."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("a book > not > a famous linguist", .unacceptable)]
    paperFeatures := [] }

def ex4_18b : Datum :=
  { id := "charlow2014_ex4_18b"
    source := ⟨"charlow-2014", "(4.18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If a persuasive lawyer visits a relative of mine, I'll inherit a house."
    glossedTokens := []
    context := "For some relative of mine, if some persuasive lawyer or other visits them, I'll inherit a house; continue with 'she lives in Highland Park'."
    judgment := .acceptable
    contrasts := []
    readings := [("a relative > if > a lawyer", .acceptable)]
    paperFeatures := [] }

def ex4_23a : Datum :=
  { id := "charlow2014_ex4_23a"
    source := ⟨"rooth-partee-1982", "(21c)"⟩
    reportedIn := some ⟨"charlow-2014", "(4.23a)"⟩
    language := "stan1293"
    primaryText := "Bill hopes that someone will hire a maid or a cook."
    glossedTokens := []
    context := "Bill either hopes de dicto that someone hires a maid, or hopes de dicto that someone hires a cook."
    judgment := .acceptable
    contrasts := []
    readings := [("or > hopes, indefinites de dicto", .acceptable)]
    paperFeatures := [] }

def ex4_23b : Datum :=
  { id := "charlow2014_ex4_23b"
    source := ⟨"rooth-partee-1982", "(21a)"⟩
    reportedIn := some ⟨"charlow-2014", "(4.23b)"⟩
    language := "stan1293"
    primaryText := "Bill hopes that someone will hire a maid and a cook."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("and > hopes", .unacceptable)]
    paperFeatures := [] }

def ex4_24b : Datum :=
  { id := "charlow2014_ex4_24b"
    source := ⟨"charlow-2014", "(4.24b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either everyone ate a steak or a hamburger. (I've forgotten which.)"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("either everyone ate a steak, or everyone ate a hamburger (or > every > a)", .acceptable)]
    paperFeatures := [] }

def ex4_25b : Datum :=
  { id := "charlow2014_ex4_25b"
    source := ⟨"charlow-2014", "(4.25b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If a farmer owns a donkey or a horse, he beats it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("every farmer beats every donkey or horse he owns", .acceptable)]
    paperFeatures := [] }

def ex5_7a : Datum :=
  { id := "charlow2014_ex5_7a"
    source := ⟨"charlow-2014", "(5.7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If everyone thinks John will come, we'll have to invite him. If everyone thinks BILL will come, we WON'T have to invite him."
    glossedTokens := []
    context := "Sloppy reading of the elided pronoun: we won't have to invite Bill."
    judgment := .acceptable
    contrasts := []
    readings := [("sloppy (him = Bill)", .acceptable)]
    paperFeatures := [] }

def ex5_22 : Datum :=
  { id := "charlow2014_ex5_22"
    source := ⟨"charlow-2014", "(5.22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone heard the rumor that at least six senators supported Cruz's filibuster. It turned out to be erroneous: they numbered at most three."
    glossedTokens := []
    context := "'they' refers to the senators who supported the filibuster."
    judgment := .acceptable
    contrasts := []
    readings := [("they = maximal refset", .acceptable)]
    paperFeatures := [] }

def ex5_23 : Datum :=
  { id := "charlow2014_ex5_23"
    source := ⟨"charlow-2014", "(5.23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's absolutely false that no senators admire Cruz. But even so, they're all very junior."
    glossedTokens := []
    context := "'they' refers to the senators who admire Cruz."
    judgment := .acceptable
    contrasts := []
    readings := [("they = maximal refset", .acceptable)]
    paperFeatures := [] }

def ex5_27b : Datum :=
  { id := "charlow2014_ex5_27b"
    source := ⟨"charlow-2014", "(5.27b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He also only introduced BILL to SUE."
    glossedTokens := []
    context := "Reply to 'John only introduced BILL to Mary' at a party where Mary met only Bill and Sue also met only Bill."
    judgment := .acceptable
    contrasts := []
    readings := [("also > SUE > only > BILL", .acceptable)]
    paperFeatures := [] }

def all : List Datum := [ex4_1a, ex4_1b, ex4_1c, ex4_2a, ex4_4, ex4_6, ex4_18b, ex4_23a, ex4_23b, ex4_24b, ex4_25b, ex5_7a, ex5_22, ex5_23, ex5_27b]

end Charlow2014.Examples
