module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Eckardt2006` — typed example data

Auto-generated from `Linglib/Data/Examples/Eckardt2006.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Eckardt2006.Examples`.
-/

@[expose] public section

namespace Eckardt2006.Examples

def ex_4_6 : Datum :=
  { id := "eckardt2006_4_6"
    source := ⟨"eckardt-2006", "(4.6)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "when you are going to lay a tax upon the people . . ."
    glossedTokens := []
    context := "1657, Burton, entry of 12 January."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "go"), ("form", "going to"), ("movement", "excluded")] }

def ex_4_20 : Datum :=
  { id := "eckardt2006_4_20"
    source := ⟨"eckardt-2006", "(4.20)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Sir, I am going to visit a friend, that's sicke"
    glossedTokens := []
    context := "1601, B. Jonson, Poetaster II.i; spoken by Horatio."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "go"), ("form", "going to"), ("movement", "possible")] }

def ex_4_49 : Datum :=
  { id := "eckardt2006_4_49"
    source := ⟨"eckardt-2006", "(4.49)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Horatio is going to visit a friend"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "go"), ("form", "going to"), ("movement", "possible")] }

def ex_4_60a : Datum :=
  { id := "eckardt2006_4_60a"
    source := ⟨"eckardt-2006", "(4.60)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Horatio was going to visit a friend"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "go"), ("form", "going to"), ("movement", "possible")] }

def ex_4_60b : Datum :=
  { id := "eckardt2006_4_60b"
    source := ⟨"eckardt-2006", "(4.60)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Horatio had been going to visit a friend"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "go"), ("form", "going to"), ("movement", "possible")] }

def ex_4_60c : Datum :=
  { id := "eckardt2006_4_60c"
    source := ⟨"eckardt-2006", "(4.60)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Horatio will be going to visit a friend"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "go"), ("form", "going to"), ("movement", "possible")] }

def ex_4_62a : Datum :=
  { id := "eckardt2006_4_62a"
    source := ⟨"eckardt-2006", "(4.62)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Horatio went to finish his talk at 5 o'clock."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "go"), ("form", "simple"), ("movement", "excluded")] }

def ex_4_62b : Datum :=
  { id := "eckardt2006_4_62b"
    source := ⟨"eckardt-2006", "(4.62)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Horatio had gone to like Paris."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "go"), ("form", "simple"), ("movement", "excluded")] }

def ex_4_62c : Datum :=
  { id := "eckardt2006_4_62c"
    source := ⟨"eckardt-2006", "(4.62)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The house will go to break down."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "go"), ("form", "simple"), ("movement", "excluded")] }

def ex_4_64a : Datum :=
  { id := "eckardt2006_4_64a"
    source := ⟨"eckardt-2006", "(4.64)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Horatio went to stop talking in five minutes."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "go"), ("form", "simple"), ("movement", "excluded")] }

def ex_4_64b : Datum :=
  { id := "eckardt2006_4_64b"
    source := ⟨"eckardt-2006", "(4.64)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Horatio went to avoid any allusions to the scandal."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "go"), ("form", "simple"), ("movement", "excluded")] }

def ex_4_10 : Datum :=
  { id := "eckardt2006_4_10"
    source := ⟨"eckardt-2006", "(4.10)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Emil geht ein Bier holen"
    glossedTokens := [("Emil", "Emil"), ("geht", "goes"), ("ein", "a"), ("Bier", "beer"), ("holen", "to-fetch")]
    glossedWords := [⟨['E', 'm', 'i', 'l'], ['E', 'm', 'i', 'l'], [⟨['E', 'm', 'i', 'l'], ['E', 'm', 'i', 'l'], none⟩]⟩, ⟨['g', 'e', 'h', 't'], ['g', 'o', 'e', 's'], [⟨['g', 'e', 'h', 't'], ['g', 'o', 'e', 's'], none⟩]⟩, ⟨['e', 'i', 'n'], ['a'], [⟨['e', 'i', 'n'], ['a'], none⟩]⟩, ⟨['B', 'i', 'e', 'r'], ['b', 'e', 'e', 'r'], [⟨['B', 'i', 'e', 'r'], ['b', 'e', 'e', 'r'], none⟩]⟩, ⟨['h', 'o', 'l', 'e', 'n'], ['t', 'o', '-', 'f', 'e', 't', 'c', 'h'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "gehen"), ("form", "simple"), ("movement", "possible")] }

def ex_4_12 : Datum :=
  { id := "eckardt2006_4_12"
    source := ⟨"eckardt-2006", "(4.12)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Emil geht die Arbeit um fünf Uhr niederlegen"
    glossedTokens := [("Emil", "Emil"), ("geht", "goes"), ("die", "the"), ("Arbeit", "work"), ("um", "at"), ("fünf", "5"), ("Uhr", "o'clock"), ("niederlegen", "stop")]
    glossedWords := [⟨['E', 'm', 'i', 'l'], ['E', 'm', 'i', 'l'], [⟨['E', 'm', 'i', 'l'], ['E', 'm', 'i', 'l'], none⟩]⟩, ⟨['g', 'e', 'h', 't'], ['g', 'o', 'e', 's'], [⟨['g', 'e', 'h', 't'], ['g', 'o', 'e', 's'], none⟩]⟩, ⟨['d', 'i', 'e'], ['t', 'h', 'e'], [⟨['d', 'i', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['A', 'r', 'b', 'e', 'i', 't'], ['w', 'o', 'r', 'k'], [⟨['A', 'r', 'b', 'e', 'i', 't'], ['w', 'o', 'r', 'k'], none⟩]⟩, ⟨['u', 'm'], ['a', 't'], [⟨['u', 'm'], ['a', 't'], none⟩]⟩, ⟨['f', 'ü', 'n', 'f'], ['5'], [⟨['f', 'ü', 'n', 'f'], ['5'], none⟩]⟩, ⟨['U', 'h', 'r'], ['o', '\'', 'c', 'l', 'o', 'c', 'k'], [⟨['U', 'h', 'r'], ['o', '\'', 'c', 'l', 'o', 'c', 'k'], none⟩]⟩, ⟨['n', 'i', 'e', 'd', 'e', 'r', 'l', 'e', 'g', 'e', 'n'], ['s', 't', 'o', 'p'], [⟨['n', 'i', 'e', 'd', 'e', 'r', 'l', 'e', 'g', 'e', 'n'], ['s', 't', 'o', 'p'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "gehen"), ("form", "simple"), ("movement", "excluded")] }

def all : List Datum := [ex_4_6, ex_4_20, ex_4_49, ex_4_60a, ex_4_60b, ex_4_60c, ex_4_62a, ex_4_62b, ex_4_62c, ex_4_64a, ex_4_64b, ex_4_10, ex_4_12]

/-- The verb of movement of the example. -/
inductive Verb where
  /-- go: English *go* -/
  | go
  /-- gehen: German *gehen* -/
  | gehen
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `verb`. -/
def verb (e : Datum) : Option Verb :=
  e.parse? "verb" [("go", .go), ("gehen", .gehen)]

/-- The form of the verb of movement. -/
inductive Form where
  /-- going to: a form of *be going to* -/
  | goingTo
  /-- simple: a form without the progressive -/
  | simple
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `form`. -/
def form (e : Datum) : Option Form :=
  e.parse? "form" [("going to", .goingTo), ("simple", .simple)]

/-- Whether the embedded clause allows the movement interpretation. -/
inductive Movement where
  /-- possible: the going can be a preparation for what the clause describes -/
  | possible
  /-- excluded: the clause disallows a movement interpretation -/
  | excluded
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `movement`. -/
def movement (e : Datum) : Option Movement :=
  e.parse? "movement" [("possible", .possible), ("excluded", .excluded)]

/-- The examples of chapter 4. -/
inductive Example where
  | ex_4_6
  | ex_4_20
  | ex_4_49
  | ex_4_60a
  | ex_4_60b
  | ex_4_60c
  | ex_4_62a
  | ex_4_62b
  | ex_4_62c
  | ex_4_64a
  | ex_4_64b
  | ex_4_10
  | ex_4_12
  deriving DecidableEq, Repr, Fintype

/-- Every example of the file, in its order. -/
def Example.all : List Example :=
  [.ex_4_6, .ex_4_20, .ex_4_49, .ex_4_60a, .ex_4_60b, .ex_4_60c, .ex_4_62a, .ex_4_62b, .ex_4_62c,
    .ex_4_64a, .ex_4_64b, .ex_4_10, .ex_4_12]

/-- The row of an example. -/
def Example.datum : Example → Datum
  | .ex_4_6 => _root_.Eckardt2006.Examples.ex_4_6
  | .ex_4_20 => _root_.Eckardt2006.Examples.ex_4_20
  | .ex_4_49 => _root_.Eckardt2006.Examples.ex_4_49
  | .ex_4_60a => _root_.Eckardt2006.Examples.ex_4_60a
  | .ex_4_60b => _root_.Eckardt2006.Examples.ex_4_60b
  | .ex_4_60c => _root_.Eckardt2006.Examples.ex_4_60c
  | .ex_4_62a => _root_.Eckardt2006.Examples.ex_4_62a
  | .ex_4_62b => _root_.Eckardt2006.Examples.ex_4_62b
  | .ex_4_62c => _root_.Eckardt2006.Examples.ex_4_62c
  | .ex_4_64a => _root_.Eckardt2006.Examples.ex_4_64a
  | .ex_4_64b => _root_.Eckardt2006.Examples.ex_4_64b
  | .ex_4_10 => _root_.Eckardt2006.Examples.ex_4_10
  | .ex_4_12 => _root_.Eckardt2006.Examples.ex_4_12

theorem Example.map_datum_all :
    Example.all.map Example.datum = _root_.Eckardt2006.Examples.all := rfl

/-- The value the example records under `verb`. -/
def Example.verb : Example → Option Verb
  | .ex_4_6 => some .go
  | .ex_4_20 => some .go
  | .ex_4_49 => some .go
  | .ex_4_60a => some .go
  | .ex_4_60b => some .go
  | .ex_4_60c => some .go
  | .ex_4_62a => some .go
  | .ex_4_62b => some .go
  | .ex_4_62c => some .go
  | .ex_4_64a => some .go
  | .ex_4_64b => some .go
  | .ex_4_10 => some .gehen
  | .ex_4_12 => some .gehen

theorem Example.verb_datum :
    ∀ x : Example, _root_.Eckardt2006.Examples.verb x.datum = x.verb := by
  decide +kernel

/-- The value the example records under `form`. -/
def Example.form : Example → Option Form
  | .ex_4_6 => some .goingTo
  | .ex_4_20 => some .goingTo
  | .ex_4_49 => some .goingTo
  | .ex_4_60a => some .goingTo
  | .ex_4_60b => some .goingTo
  | .ex_4_60c => some .goingTo
  | .ex_4_62a => some .simple
  | .ex_4_62b => some .simple
  | .ex_4_62c => some .simple
  | .ex_4_64a => some .simple
  | .ex_4_64b => some .simple
  | .ex_4_10 => some .simple
  | .ex_4_12 => some .simple

theorem Example.form_datum :
    ∀ x : Example, _root_.Eckardt2006.Examples.form x.datum = x.form := by
  decide +kernel

/-- The value the example records under `movement`. -/
def Example.movement : Example → Option Movement
  | .ex_4_6 => some .excluded
  | .ex_4_20 => some .possible
  | .ex_4_49 => some .possible
  | .ex_4_60a => some .possible
  | .ex_4_60b => some .possible
  | .ex_4_60c => some .possible
  | .ex_4_62a => some .excluded
  | .ex_4_62b => some .excluded
  | .ex_4_62c => some .excluded
  | .ex_4_64a => some .excluded
  | .ex_4_64b => some .excluded
  | .ex_4_10 => some .possible
  | .ex_4_12 => some .excluded

theorem Example.movement_datum :
    ∀ x : Example, _root_.Eckardt2006.Examples.movement x.datum = x.movement := by
  decide +kernel

end Eckardt2006.Examples
