module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `GuerriniWehbe2025` — typed example data

Auto-generated from `Linglib/Data/Examples/GuerriniWehbe2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace GuerriniWehbe2025.Examples`.
-/

@[expose] public section

namespace GuerriniWehbe2025.Examples

def ex_9a : Datum :=
  { id := "guerriniwehbe2025_9a"
    source := ⟨"guerrini-wehbe-2025", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I knew that all of John's kids are adopted but today I discovered something amazing. All 10 of John's kids are adopted!"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("presupposition", "John has 10 kids")] }

def ex_9b : Datum :=
  { id := "guerriniwehbe2025_9b"
    source := ⟨"guerrini-wehbe-2025", "(9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I knew that all of John's kids are adopted but today I discovered something amazing. John has 10 adopted kids!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_10a : Datum :=
  { id := "guerriniwehbe2025_10a"
    source := ⟨"guerrini-wehbe-2025", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I knew that Mary read at least some of the books, but today I learned something interesting. She read the books."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("nominal", "definite plural"), ("known", "some"), ("predicate", "base")] }

def ex_10b : Datum :=
  { id := "guerriniwehbe2025_10b"
    source := ⟨"guerrini-wehbe-2025", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I knew that Mary didn't read all of the books, but today I learned something interesting. She didn't read the books."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("nominal", "definite plural"), ("known", "not all"), ("predicate", "base")] }

def ex_12a : Datum :=
  { id := "guerriniwehbe2025_12a"
    source := ⟨"guerrini-wehbe-2025", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John isn't married to any of his teammates."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("nominal", "quantifier"), ("known", "not all"), ("predicate", "base")] }

def ex_12b : Datum :=
  { id := "guerriniwehbe2025_12b"
    source := ⟨"guerrini-wehbe-2025", "(12b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John isn't married to his teammates."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("nominal", "definite plural"), ("known", "not all"), ("predicate", "base")] }

def ex_13a : Datum :=
  { id := "guerriniwehbe2025_13a"
    source := ⟨"guerrini-wehbe-2025", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "None of the candidates won."
    glossedTokens := []
    context := "The rules for this year's election are that the person with the most votes wins, but if there is a tie for most votes, all of the candidates lose. This year.."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("nominal", "quantifier"), ("known", "at most one"), ("predicate", "base")] }

def ex_13b : Datum :=
  { id := "guerriniwehbe2025_13b"
    source := ⟨"guerrini-wehbe-2025", "(13b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All of the candidates lost."
    glossedTokens := []
    context := "The rules for this year's election are that the person with the most votes wins, but if there is a tie for most votes, all of the candidates lose. This year.."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("nominal", "quantifier"), ("known", "at most one"), ("predicate", "antonym")] }

def ex_13c : Datum :=
  { id := "guerriniwehbe2025_13c"
    source := ⟨"guerrini-wehbe-2025", "(13c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The candidates didn't win."
    glossedTokens := []
    context := "The rules for this year's election are that the person with the most votes wins, but if there is a tie for most votes, all of the candidates lose. This year.."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("nominal", "definite plural"), ("known", "at most one"), ("predicate", "base")] }

def ex_13d : Datum :=
  { id := "guerriniwehbe2025_13d"
    source := ⟨"guerrini-wehbe-2025", "(13d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The candidates lost."
    glossedTokens := []
    context := "The rules for this year's election are that the person with the most votes wins, but if there is a tie for most votes, all of the candidates lose. This year.."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("nominal", "definite plural"), ("known", "at most one"), ("predicate", "antonym")] }

def ex_23 : Datum :=
  { id := "guerriniwehbe2025_23"
    source := ⟨"guerrini-wehbe-2025", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I knew that not all of the students smiled, but today I learned something interesting. The students didn't smile."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("nominal", "definite plural"), ("known", "not all"), ("predicate", "base")] }

def fn3_ia : Datum :=
  { id := "guerriniwehbe2025_fn3_ia"
    source := ⟨"guerrini-wehbe-2025", "fn. 3 (i-a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's crazy, I didn't realize this was possible. Somehow.. John married his teammates."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def fn3_ib : Datum :=
  { id := "guerriniwehbe2025_fn3_ib"
    source := ⟨"guerrini-wehbe-2025", "fn. 3 (i-b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's crazy, I didn't realize this was possible. Somehow.. John married all of his teammates."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_42 : Datum :=
  { id := "guerriniwehbe2025_42"
    source := ⟨"guerrini-wehbe-2025", "(42)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I knew that Mary can eat cake, but today I learned something interesting. She can eat cake or candy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "free choice")] }

def ex_43a : Datum :=
  { id := "guerriniwehbe2025_43a"
    source := ⟨"guerrini-wehbe-2025", "(43a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is not the case that Mary can read any book. She can only read War and Peace."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "free choice")] }

def ex_43b : Datum :=
  { id := "guerriniwehbe2025_43b"
    source := ⟨"guerrini-wehbe-2025", "(43b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is not the case that Mary read the books. She only read War and Peace."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_44a : Datum :=
  { id := "guerriniwehbe2025_44a"
    source := ⟨"guerrini-wehbe-2025", "(44a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I already knew that Mary sometimes goes to the gym on Tuesdays, but today I learned something interesting. Mary goes to the gym on Tuesdays."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "habitual")] }

def ex_44b : Datum :=
  { id := "guerriniwehbe2025_44b"
    source := ⟨"guerrini-wehbe-2025", "(44b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I knew that lions sometimes hunt, but today I learned something interesting. Lions hunt."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "generic")] }

def ex_44c : Datum :=
  { id := "guerriniwehbe2025_44c"
    source := ⟨"guerrini-wehbe-2025", "(44c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I already knew that some birds are migrating right now, but today I learned something interesting. Birds are migrating right now."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "episodic universal bare plural")] }

def ex_44d : Datum :=
  { id := "guerriniwehbe2025_44d"
    source := ⟨"guerrini-wehbe-2025", "(44d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I already knew that the wall was partly red, but today I learned something interesting. The wall is red."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "predicate homogeneity")] }

def ex_44e : Datum :=
  { id := "guerriniwehbe2025_44e"
    source := ⟨"guerrini-wehbe-2025", "(44e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I already knew that sometimes, if you hit the brakes, the car stops, but today I learned something interesting. If you hit the brakes, the car stops."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "conditional")] }

def ex_47a : Datum :=
  { id := "guerriniwehbe2025_47a"
    source := ⟨"guerrini-wehbe-2025", "(47a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I knew that Mary is allowed to read this book, but today I learned something interesting. She should read this book."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "neg-raising")] }

def ex_47b : Datum :=
  { id := "guerriniwehbe2025_47b"
    source := ⟨"guerrini-wehbe-2025", "(47b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I knew that Mary is allowed not to read this book, but today I learned something interesting. She shouldn't read this book."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "neg-raising")] }

def fn20_i : Datum :=
  { id := "guerriniwehbe2025_fn20_i"
    source := ⟨"guerrini-wehbe-2025", "fn. 20 (i)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is not the case that Mary should read this book. She is allowed to, but it's also fine if she doesn't read it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "neg-raising")] }

def all : List Datum := [ex_9a, ex_9b, ex_10a, ex_10b, ex_12a, ex_12b, ex_13a, ex_13b, ex_13c, ex_13d, ex_23, fn3_ia, fn3_ib, ex_42, ex_43a, ex_43b, ex_44a, ex_44b, ex_44c, ex_44d, ex_44e, ex_47a, ex_47b, fn20_i]

/-- The noun phrase the predicate applies to. -/
inductive Nominal where
  /-- definite plural: a plural definite, *the books* -/
  | definitePlural
  /-- quantifier: its counterpart with an overt quantifier, *all of*, *none of*, *any of* -/
  | quantifier
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `nominal`. -/
def nominal (e : Datum) : Option Nominal :=
  e.parse? "nominal" [("definite plural", .definitePlural), ("quantifier", .quantifier)]

/-- Whether the sentence is negated. -/
inductive Polarity where
  /-- positive: an affirmative sentence -/
  | positive
  /-- negative: a sentence with negation or a negative quantifier -/
  | negative
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `polarity`. -/
def polarity (e : Datum) : Option Polarity :=
  e.parse? "polarity" [("positive", .positive), ("negative", .negative)]

/-- The predicate, as against the one the context is stated with. -/
inductive Predicate where
  /-- base: the predicate of the context, *read*, *win* -/
  | base
  /-- antonym: its antonym, *lose* for *win* -/
  | antonym
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `predicate`. -/
def predicate (e : Datum) : Option Predicate :=
  e.parse? "predicate" [("base", .base), ("antonym", .antonym)]

/-- What the context establishes about how many of the plurality satisfy the predicate. -/
inductive Known where
  /-- some: at least one does -/
  | some
  /-- not all: not all do -/
  | notAll
  /-- at most one: at most one can -/
  | atMostOne
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `known`. -/
def known (e : Datum) : Option Known :=
  e.parse? "known" [("some", .some), ("not all", .notAll), ("at most one", .atMostOne)]

end GuerriniWehbe2025.Examples
