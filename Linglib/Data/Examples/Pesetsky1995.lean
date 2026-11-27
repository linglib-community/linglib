module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Pesetsky1995` — typed example data

Auto-generated from `Linglib/Data/Examples/Pesetsky1995.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Pesetsky1995.Examples`.
-/

@[expose] public section

namespace Pesetsky1995.Examples

def ex_171a : Datum :=
  { id := "pesetsky1995_171a"
    source := ⟨"pesetsky-1995", "(171a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The article in the Times angered Bill at the government."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "causer"), ("frame", "atPhrase"), ("predicate", "anger")] }

def ex_171c : Datum :=
  { id := "pesetsky1995_171c"
    source := ⟨"pesetsky-1995", "(171c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The television set worried John about the veracity of Bill's alibi."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "causer"), ("frame", "aboutPhrase"), ("predicate", "worry")] }

def ex_181b : Datum :=
  { id := "pesetsky1995_181b"
    source := ⟨"pesetsky-1995", "(181b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill was angry (at the government)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "experiencer"), ("frame", "atPhrase"), ("predicate", "angry")] }

def ex_494a : Datum :=
  { id := "pesetsky1995_494a"
    source := ⟨"pesetsky-1995", "(494a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The war years gave Mailer his first big success."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "causer"), ("frame", "doubleObject"), ("predicate", "give")] }

def ex_494b : Datum :=
  { id := "pesetsky1995_494b"
    source := ⟨"pesetsky-1995", "(494b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The war years gave his first big success to Mailer."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "causer"), ("frame", "toPhrase"), ("predicate", "give")] }

def ex_497a : Datum :=
  { id := "pesetsky1995_497a"
    source := ⟨"pesetsky-1995", "(497a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Katya taught me Russian."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "agent"), ("frame", "doubleObject"), ("predicate", "teach")] }

def ex_497b : Datum :=
  { id := "pesetsky1995_497b"
    source := ⟨"pesetsky-1995", "(497b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Katya taught Russian to me."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "agent"), ("frame", "toPhrase"), ("predicate", "teach")] }

def ex_497c : Datum :=
  { id := "pesetsky1995_497c"
    source := ⟨"pesetsky-1995", "(497c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lipson's textbook taught me Russian."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "causer"), ("frame", "doubleObject"), ("predicate", "teach")] }

def ex_497d : Datum :=
  { id := "pesetsky1995_497d"
    source := ⟨"pesetsky-1995", "(497d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lipson's textbook taught Russian to me."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "causer"), ("frame", "toPhrase"), ("predicate", "teach")] }

def ex_502a : Datum :=
  { id := "pesetsky1995_502a"
    source := ⟨"pesetsky-1995", "(502a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill got Mary the prize."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "agent"), ("frame", "doubleObject"), ("predicate", "get")] }

def ex_502b : Datum :=
  { id := "pesetsky1995_502b"
    source := ⟨"pesetsky-1995", "(502b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill got the prize for Mary."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "agent"), ("frame", "forPhrase"), ("predicate", "get")] }

def ex_502c : Datum :=
  { id := "pesetsky1995_502c"
    source := ⟨"pesetsky-1995", "(502c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Hard work got Mary the prize."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "causer"), ("frame", "doubleObject"), ("predicate", "get")] }

def ex_502d : Datum :=
  { id := "pesetsky1995_502d"
    source := ⟨"pesetsky-1995", "(502d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Hard work got the prize for Mary."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "causer"), ("frame", "forPhrase"), ("predicate", "get")] }

def ex_503c : Datum :=
  { id := "pesetsky1995_503c"
    source := ⟨"pesetsky-1995", "(503c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The conversation with Sue handed Bill a golden opportunity."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "causer"), ("frame", "doubleObject"), ("predicate", "hand")] }

def ex_503d : Datum :=
  { id := "pesetsky1995_503d"
    source := ⟨"pesetsky-1995", "(503d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The conversation with Sue handed a golden opportunity to Bill."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "causer"), ("frame", "toPhrase"), ("predicate", "hand")] }

def ex_518 : Datum :=
  { id := "pesetsky1995_518"
    source := ⟨"pesetsky-1995", "(518)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Pictures of each other annoyed the kids."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "causer"), ("frame", "bare"), ("predicate", "annoy")] }

def ex_534 : Datum :=
  { id := "pesetsky1995_534"
    source := ⟨"pesetsky-1995", "(534)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "His manner was angry."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "suggestor"), ("frame", "bare"), ("predicate", "angry")] }

def ex_535 : Datum :=
  { id := "pesetsky1995_535"
    source := ⟨"pesetsky-1995", "(535)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "His manner was angry at Mary."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "suggestor"), ("frame", "atPhrase"), ("predicate", "angry")] }

def all : List Datum := [ex_171a, ex_171c, ex_181b, ex_494a, ex_494b, ex_497a, ex_497b, ex_497c, ex_497d, ex_502a, ex_502b, ex_502c, ex_502d, ex_503c, ex_503d, ex_518, ex_534, ex_535]

/-- The role of the subject. -/
inductive Subject where
  /-- agent: an Agent -/
  | agent
  /-- experiencer: an Experiencer -/
  | experiencer
  /-- causer: a Causer, which performs no action -/
  | causer
  /-- suggestor: a Suggestor, the manner or remarks that suggest an emotion -/
  | suggestor
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `subject`. -/
def subject (e : Datum) : Option Subject :=
  e.parse? "subject" [("agent", .agent), ("experiencer", .experiencer), ("causer", .causer),
    ("suggestor", .suggestor)]

/-- What introduces the argument of the predicate that follows its first object. -/
inductive Frame where
  /-- bare: no such argument -/
  | bare
  /-- doubleObject: a second object with no overt preposition -/
  | doubleObject
  /-- toPhrase: the preposition to -/
  | toPhrase
  /-- forPhrase: the preposition for -/
  | forPhrase
  /-- atPhrase: the preposition at -/
  | atPhrase
  /-- aboutPhrase: the preposition about -/
  | aboutPhrase
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `frame`. -/
def frame (e : Datum) : Option Frame :=
  e.parse? "frame" [("bare", .bare), ("doubleObject", .doubleObject), ("toPhrase", .toPhrase),
    ("forPhrase", .forPhrase), ("atPhrase", .atPhrase), ("aboutPhrase", .aboutPhrase)]

/-- The examples of the book. -/
inductive Example where
  | ex_171a
  | ex_171c
  | ex_181b
  | ex_494a
  | ex_494b
  | ex_497a
  | ex_497b
  | ex_497c
  | ex_497d
  | ex_502a
  | ex_502b
  | ex_502c
  | ex_502d
  | ex_503c
  | ex_503d
  | ex_518
  | ex_534
  | ex_535
  deriving DecidableEq, Repr, Fintype

/-- Every example of the file, in its order. -/
def Example.all : List Example :=
  [.ex_171a, .ex_171c, .ex_181b, .ex_494a, .ex_494b, .ex_497a, .ex_497b, .ex_497c, .ex_497d,
    .ex_502a, .ex_502b, .ex_502c, .ex_502d, .ex_503c, .ex_503d, .ex_518, .ex_534, .ex_535]

/-- The row of an example. -/
def Example.datum : Example → Datum
  | .ex_171a => _root_.Pesetsky1995.Examples.ex_171a
  | .ex_171c => _root_.Pesetsky1995.Examples.ex_171c
  | .ex_181b => _root_.Pesetsky1995.Examples.ex_181b
  | .ex_494a => _root_.Pesetsky1995.Examples.ex_494a
  | .ex_494b => _root_.Pesetsky1995.Examples.ex_494b
  | .ex_497a => _root_.Pesetsky1995.Examples.ex_497a
  | .ex_497b => _root_.Pesetsky1995.Examples.ex_497b
  | .ex_497c => _root_.Pesetsky1995.Examples.ex_497c
  | .ex_497d => _root_.Pesetsky1995.Examples.ex_497d
  | .ex_502a => _root_.Pesetsky1995.Examples.ex_502a
  | .ex_502b => _root_.Pesetsky1995.Examples.ex_502b
  | .ex_502c => _root_.Pesetsky1995.Examples.ex_502c
  | .ex_502d => _root_.Pesetsky1995.Examples.ex_502d
  | .ex_503c => _root_.Pesetsky1995.Examples.ex_503c
  | .ex_503d => _root_.Pesetsky1995.Examples.ex_503d
  | .ex_518 => _root_.Pesetsky1995.Examples.ex_518
  | .ex_534 => _root_.Pesetsky1995.Examples.ex_534
  | .ex_535 => _root_.Pesetsky1995.Examples.ex_535

theorem Example.map_datum_all :
    Example.all.map Example.datum = _root_.Pesetsky1995.Examples.all := rfl

/-- The value the example records under `subject`. -/
def Example.subject : Example → Option Subject
  | .ex_171a => some .causer
  | .ex_171c => some .causer
  | .ex_181b => some .experiencer
  | .ex_494a => some .causer
  | .ex_494b => some .causer
  | .ex_497a => some .agent
  | .ex_497b => some .agent
  | .ex_497c => some .causer
  | .ex_497d => some .causer
  | .ex_502a => some .agent
  | .ex_502b => some .agent
  | .ex_502c => some .causer
  | .ex_502d => some .causer
  | .ex_503c => some .causer
  | .ex_503d => some .causer
  | .ex_518 => some .causer
  | .ex_534 => some .suggestor
  | .ex_535 => some .suggestor

theorem Example.subject_datum :
    ∀ x : Example, _root_.Pesetsky1995.Examples.subject x.datum = x.subject := by
  decide +kernel

/-- The value the example records under `frame`. -/
def Example.frame : Example → Option Frame
  | .ex_171a => some .atPhrase
  | .ex_171c => some .aboutPhrase
  | .ex_181b => some .atPhrase
  | .ex_494a => some .doubleObject
  | .ex_494b => some .toPhrase
  | .ex_497a => some .doubleObject
  | .ex_497b => some .toPhrase
  | .ex_497c => some .doubleObject
  | .ex_497d => some .toPhrase
  | .ex_502a => some .doubleObject
  | .ex_502b => some .forPhrase
  | .ex_502c => some .doubleObject
  | .ex_502d => some .forPhrase
  | .ex_503c => some .doubleObject
  | .ex_503d => some .toPhrase
  | .ex_518 => some .bare
  | .ex_534 => some .bare
  | .ex_535 => some .atPhrase

theorem Example.frame_datum :
    ∀ x : Example, _root_.Pesetsky1995.Examples.frame x.datum = x.frame := by
  decide +kernel

end Pesetsky1995.Examples
