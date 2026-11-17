module

public import Linglib.Data.Examples.Schema

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
    source := ⟨"guerrini-wehbe-2025", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All 10 of John's kids are adopted!"
    glossedTokens := []
    context := "I knew that all of John's kids are adopted but today I discovered something amazing."
    judgment := .unacceptable
    contrasts := [("John has 10 adopted kids!", .acceptable)]
    readings := []
    paperFeatures := [("presupposition", "John has 10 kids")] }

def ex_10a : Datum :=
  { id := "guerriniwehbe2025_10a"
    source := ⟨"guerrini-wehbe-2025", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She read the books."
    glossedTokens := []
    context := "I knew that Mary read at least some of the books, but today I learned something interesting."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_10b : Datum :=
  { id := "guerriniwehbe2025_10b"
    source := ⟨"guerrini-wehbe-2025", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She didn't read the books."
    glossedTokens := []
    context := "I knew that Mary didn't read all of the books, but today I learned something interesting."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_12b : Datum :=
  { id := "guerriniwehbe2025_12b"
    source := ⟨"guerrini-wehbe-2025", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John isn't married to his teammates."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := [("John isn't married to any of his teammates.", .acceptable)]
    readings := []
    paperFeatures := [] }

def ex_13c : Datum :=
  { id := "guerriniwehbe2025_13c"
    source := ⟨"guerrini-wehbe-2025", "(13a), (13c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The candidates didn't win."
    glossedTokens := []
    context := "The rules for this year's election are that the person with the most votes wins, but if there is a tie for most votes, all of the candidates lose. This year.."
    judgment := .unacceptable
    contrasts := [("None of the candidates won.", .acceptable)]
    readings := []
    paperFeatures := [] }

def ex_13d : Datum :=
  { id := "guerriniwehbe2025_13d"
    source := ⟨"guerrini-wehbe-2025", "(13b), (13d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The candidates lost."
    glossedTokens := []
    context := "The rules for this year's election are that the person with the most votes wins, but if there is a tie for most votes, all of the candidates lose. This year.."
    judgment := .unacceptable
    contrasts := [("All of the candidates lost.", .acceptable)]
    readings := []
    paperFeatures := [] }

def ex_23 : Datum :=
  { id := "guerriniwehbe2025_23"
    source := ⟨"guerrini-wehbe-2025", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The students didn't smile."
    glossedTokens := []
    context := "I knew that not all of the students smiled, but today I learned something interesting."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def fn3_ia : Datum :=
  { id := "guerriniwehbe2025_fn3_ia"
    source := ⟨"guerrini-wehbe-2025", "fn. 3 (i)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John married his teammates."
    glossedTokens := []
    context := "It's crazy, I didn't realize this was possible. Somehow.."
    judgment := .unacceptable
    contrasts := [("John married all of his teammates.", .acceptable)]
    readings := []
    paperFeatures := [] }

def ex_42 : Datum :=
  { id := "guerriniwehbe2025_42"
    source := ⟨"guerrini-wehbe-2025", "(42)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She can eat cake or candy."
    glossedTokens := []
    context := "I knew that Mary can eat cake, but today I learned something interesting."
    judgment := .acceptable
    contrasts := []
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
    contrasts := []
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
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_44a : Datum :=
  { id := "guerriniwehbe2025_44a"
    source := ⟨"guerrini-wehbe-2025", "(44a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary goes to the gym on Tuesdays."
    glossedTokens := []
    context := "I already knew that Mary sometimes goes to the gym on Tuesdays, but today I learned something interesting."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "habitual")] }

def ex_44b : Datum :=
  { id := "guerriniwehbe2025_44b"
    source := ⟨"guerrini-wehbe-2025", "(44b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lions hunt."
    glossedTokens := []
    context := "I knew that lions sometimes hunt, but today I learned something interesting."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "generic")] }

def ex_44c : Datum :=
  { id := "guerriniwehbe2025_44c"
    source := ⟨"guerrini-wehbe-2025", "(44c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Birds are migrating right now."
    glossedTokens := []
    context := "I already knew that some birds are migrating right now, but today I learned something interesting."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "episodic universal bare plural")] }

def ex_44d : Datum :=
  { id := "guerriniwehbe2025_44d"
    source := ⟨"guerrini-wehbe-2025", "(44d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The wall is red."
    glossedTokens := []
    context := "I already knew that the wall was partly red, but today I learned something interesting."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "predicate homogeneity")] }

def ex_44e : Datum :=
  { id := "guerriniwehbe2025_44e"
    source := ⟨"guerrini-wehbe-2025", "(44e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you hit the brakes, the car stops."
    glossedTokens := []
    context := "I already knew that sometimes, if you hit the brakes, the car stops, but today I learned something interesting."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "conditional")] }

def ex_47a : Datum :=
  { id := "guerriniwehbe2025_47a"
    source := ⟨"guerrini-wehbe-2025", "(47a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She should read this book."
    glossedTokens := []
    context := "I knew that Mary is allowed to read this book, but today I learned something interesting."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "neg-raising")] }

def ex_47b : Datum :=
  { id := "guerriniwehbe2025_47b"
    source := ⟨"guerrini-wehbe-2025", "(47b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She shouldn't read this book."
    glossedTokens := []
    context := "I knew that Mary is allowed not to read this book, but today I learned something interesting."
    judgment := .acceptable
    contrasts := []
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
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "neg-raising")] }

def all : List Datum := [ex_9a, ex_10a, ex_10b, ex_12b, ex_13c, ex_13d, ex_23, fn3_ia, ex_42, ex_43a, ex_43b, ex_44a, ex_44b, ex_44c, ex_44d, ex_44e, ex_47a, ex_47b, fn20_i]

end GuerriniWehbe2025.Examples
