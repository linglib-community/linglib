module

public import Linglib.Data.Examples.Schema

/-!
# `Barker2002` — typed example data

Auto-generated from `Linglib/Data/Examples/Barker2002.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Barker2002.Examples`.
-/

@[expose] public section

namespace Barker2002.Examples

def ex_4a : Datum :=
  { id := "barker2002_4a"
    source := ⟨"barker-2002", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John left."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("translation", "left j")] }

def ex_4b : Datum :=
  { id := "barker2002_4b"
    source := ⟨"barker-2002", "(4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John saw Mary."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("translation", "saw m j")] }

def ex_14 : Datum :=
  { id := "barker2002_14"
    source := ⟨"barker-2002", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John saw everyone."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("translation", "∀x.saw x j"), ("quantifiers", "everyone")] }

def ex_17a : Datum :=
  { id := "barker2002_17a"
    source := ⟨"barker-2002", "(17a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John saw every man."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("translation", "∀x.man x → saw x j"), ("quantifiers", "every")] }

def ex_17b : Datum :=
  { id := "barker2002_17b"
    source := ⟨"barker-2002", "(17b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John saw most men."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("translation", "most(man)(λx.saw x j)"), ("quantifiers", "most")] }

def ex_17c : Datum :=
  { id := "barker2002_17c"
    source := ⟨"barker-2002", "(17c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every man saw a woman."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("a > every", .acceptable), ("every > a", .acceptable)]
    paperFeatures := [("quantifiers", "every a"), ("derivation", "every man saw a woman")] }

def ex_19a : Datum :=
  { id := "barker2002_19a"
    source := ⟨"barker-2002", "(19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A raindrop fell on every car."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifiers", "a every"), ("natural_reading", "every > a")] }

def ex_19b : Datum :=
  { id := "barker2002_19b"
    source := ⟨"barker-2002", "(19b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A raindrop fell on the hood of every car."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifiers", "a every"), ("natural_reading", "every > a")] }

def ex_19c : Datum :=
  { id := "barker2002_19c"
    source := ⟨"barker-2002", "(19c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A raindrop fell on the top of the hood of every car."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifiers", "a every"), ("natural_reading", "every > a")] }

def ex_21a : Datum :=
  { id := "barker2002_21a"
    source := ⟨"barker-2002", "(21a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A man thought everyone saw Mary."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifiers", "a everyone"), ("translation", "∃y.man y ∧ thought(∀x.saw m x) y"), ("island", "tensed S")] }

def ex_22a : Datum :=
  { id := "barker2002_22a"
    source := ⟨"barker-2002", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No man from a foreign country was admitted."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("no > a", .acceptable), ("a > no", .acceptable)]
    paperFeatures := [("quantifiers", "no a")] }

def ex_23a : Datum :=
  { id := "barker2002_23a"
    source := ⟨"barker-2002", "(23a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Two politicians spy on someone from every city."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("every > two > someone", .ungrammatical)]
    paperFeatures := [("quantifiers", "two someone every"), ("constituent", "someone every")] }

def ex_26a : Datum :=
  { id := "barker2002_26a"
    source := ⟨"barker-2002", "(26a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most subjects put an object in every box."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("every > most > an", .ungrammatical)]
    paperFeatures := [("quantifiers", "most an every"), ("constituent", "an every")] }

def ex_27a : Datum :=
  { id := "barker2002_27a"
    source := ⟨"barker-2002", "(27a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John left and John slept."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("coordination", "S"), ("translation", "and(left j)(slept j)")] }

def ex_27b : Datum :=
  { id := "barker2002_27b"
    source := ⟨"barker-2002", "(27b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John left and slept."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("coordination", "VP"), ("translation", "and(left j)(slept j)")] }

def ex_27c : Datum :=
  { id := "barker2002_27c"
    source := ⟨"barker-2002", "(27c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John saw and liked Mary."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("coordination", "Vt"), ("translation", "and(saw m j)(liked m j)")] }

def ex_27d : Datum :=
  { id := "barker2002_27d"
    source := ⟨"barker-2002", "(27d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John and Mary left."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("coordination", "NP"), ("translation", "and(left j)(left m)")] }

def ex_42a : Datum :=
  { id := "barker2002_42a"
    source := ⟨"barker-2002", "(42a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Someone saw the friend of the friend of everyone."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("someone > everyone", .acceptable), ("everyone > someone", .acceptable)]
    paperFeatures := [("quantifiers", "someone everyone"), ("derivation", "someone saw the friend of the friend of everyone")] }

def ex_43 : Datum :=
  { id := "barker2002_43"
    source := ⟨"barker-2002", "(43)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Someone saw a friend of everyone."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("someone > a > everyone", .acceptable), ("someone > everyone > a", .acceptable), ("a > everyone > someone", .acceptable), ("everyone > a > someone", .acceptable), ("everyone > someone > a", .unacceptable), ("a > someone > everyone", .unacceptable)]
    paperFeatures := [("quantifiers", "someone a everyone"), ("constituent", "a everyone"), ("derivation", "someone saw a friend of everyone")] }

def all : List Datum := [ex_4a, ex_4b, ex_14, ex_17a, ex_17b, ex_17c, ex_19a, ex_19b, ex_19c, ex_21a, ex_22a, ex_23a, ex_26a, ex_27a, ex_27b, ex_27c, ex_27d, ex_42a, ex_43]

end Barker2002.Examples
