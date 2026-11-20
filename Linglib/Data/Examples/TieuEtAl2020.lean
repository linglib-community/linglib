module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `TieuEtAl2020` — typed example data

Auto-generated from `Linglib/Data/Examples/TieuEtAl2020.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace TieuEtAl2020.Examples`.
-/

@[expose] public section

namespace TieuEtAl2020.Examples

def ex_1a : Datum :=
  { id := "tieuetal2020_1a"
    source := ⟨"tieu-etal-2020", "(1a), (13), (21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily fed giraffes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("more than one giraffe", .acceptable)]
    paperFeatures := [("polarity", "positive"), ("inference", "multiplicity")] }

def ex_2a : Datum :=
  { id := "tieuetal2020_2a"
    source := ⟨"tieu-etal-2020", "(2a), (16), (23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily didn't feed giraffes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("not more than one giraffe", .unacceptable), ("not a single giraffe", .acceptable)]
    paperFeatures := [("polarity", "negative"), ("inference", "multiplicity")] }

def ex_3a : Datum :=
  { id := "tieuetal2020_3a"
    source := ⟨"tieu-etal-2020", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If there are books on Stephen's desk, Robin should lock the door."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "downward"), ("inference", "multiplicity")] }

def ex_4a : Datum :=
  { id := "tieuetal2020_4a"
    source := ⟨"tieu-etal-2020", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Are there books on Stephen's desk?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "downward"), ("inference", "multiplicity")] }

def ex_8 : Datum :=
  { id := "tieuetal2020_8"
    source := ⟨"tieu-etal-2020", "(8), (18), (26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily didn't feed giraffes, because she fed only one!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("inference", "multiplicity")] }

def ex_14 : Datum :=
  { id := "tieuetal2020_14"
    source := ⟨"tieu-etal-2020", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily fed exactly one giraffe."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "positive")] }

def ex_17 : Datum :=
  { id := "tieuetal2020_17"
    source := ⟨"tieu-etal-2020", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily didn't feed exactly one giraffe."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "negative")] }

def ex_27a : Datum :=
  { id := "tieuetal2020_27a"
    source := ⟨"tieu-etal-2020", "(27a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily fed giraffes."
    glossedTokens := []
    context := "Emily fed exactly one giraffe."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("n_acted_on", "1"), ("inference", "multiplicity")] }

def ex_27b : Datum :=
  { id := "tieuetal2020_27b"
    source := ⟨"tieu-etal-2020", "(27b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily didn't feed giraffes."
    glossedTokens := []
    context := "Emily fed exactly one giraffe."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("n_acted_on", "1"), ("inference", "multiplicity")] }

def ex_29a : Datum :=
  { id := "tieuetal2020_29a"
    source := ⟨"tieu-etal-2020", "(29a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily fed some of the giraffes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("not all of the giraffes", .acceptable)]
    paperFeatures := [("polarity", "positive"), ("inference", "scalar")] }

def exp1_positive : Datum :=
  { id := "tieuetal2020_exp1_positive"
    source := ⟨"tieu-etal-2020", "(34a), Experiment 1"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Emily fed pigs!"
    glossedTokens := []
    context := "Emily is visiting the pig farm and feeds exactly one pig."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "1"), ("polarity", "positive"), ("n_acted_on", "1"), ("inference", "multiplicity")] }

def exp1_negative : Datum :=
  { id := "tieuetal2020_exp1_negative"
    source := ⟨"tieu-etal-2020", "(35a), Experiment 1"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Emily didn't feed giraffes!"
    glossedTokens := []
    context := "Emily feeds exactly one giraffe."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "1"), ("polarity", "negative"), ("n_acted_on", "1"), ("inference", "multiplicity")] }

def exp2_si : Datum :=
  { id := "tieuetal2020_exp2_si"
    source := ⟨"tieu-etal-2020", "(48), Experiment 2"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Lion carried some of the apples!"
    glossedTokens := []
    context := "Lion carried all of the apples."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "2"), ("polarity", "positive"), ("inference", "scalar")] }

def exp3_positive_plural : Datum :=
  { id := "tieuetal2020_exp3_positive_plural"
    source := ⟨"tieu-etal-2020", "(55a), Experiment 3"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Koala bought pears."
    glossedTokens := []
    context := "Koala bought exactly one pear."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "3"), ("polarity", "positive"), ("n_acted_on", "1"), ("task", "ternary_reward"), ("reward", "intermediate"), ("inference", "multiplicity")] }

def exp3_negative_plural : Datum :=
  { id := "tieuetal2020_exp3_negative_plural"
    source := ⟨"tieu-etal-2020", "(55b), Experiment 3"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Koala didn't buy pears."
    glossedTokens := []
    context := "Koala bought exactly one pear."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "3"), ("polarity", "negative"), ("n_acted_on", "1"), ("task", "ternary_reward"), ("reward", "minimal"), ("inference", "multiplicity")] }

def all : List Datum := [ex_1a, ex_2a, ex_3a, ex_4a, ex_8, ex_14, ex_17, ex_27a, ex_27b, ex_29a, exp1_positive, exp1_negative, exp2_si, exp3_positive_plural, exp3_negative_plural]

/-- The environment of the plural or scalar item. -/
inductive Polarity where
  /-- positive: an unembedded positive sentence -/
  | positive
  /-- negative: under sentential negation -/
  | negative
  /-- downward: in the antecedent of a conditional or in a question -/
  | downward
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `polarity`. -/
def polarity (e : Datum) : Option Polarity :=
  e.parse? "polarity" [("positive", .positive), ("negative", .negative), ("downward", .downward)]

/-- The inference the sentence is tested for. -/
inductive Inference where
  /-- multiplicity: the more-than-one inference of a bare plural -/
  | multiplicity
  /-- scalar: the not-all inference of *some* -/
  | scalar
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `inference`. -/
def inference (e : Datum) : Option Inference :=
  e.parse? "inference" [("multiplicity", .multiplicity), ("scalar", .scalar)]

/-- The reward adults most often gave in the ternary judgment task of Experiment 3. -/
inductive Reward where
  /-- minimal: one strawberry -/
  | minimal
  /-- intermediate: two strawberries -/
  | intermediate
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `reward`. -/
def reward (e : Datum) : Option Reward :=
  e.parse? "reward" [("minimal", .minimal), ("intermediate", .intermediate)]

/-- The paraphrases the paper judges a sentence against. -/
inductive Reading where
  /-- more than one giraffe: Emily fed more than one giraffe -/
  | moreThanOne
  /-- not more than one giraffe: Emily didn't feed more than one giraffe -/
  | notMoreThanOne
  /-- not a single giraffe: Emily didn't feed a single giraffe -/
  | notASingle
  /-- not all of the giraffes: Emily fed some and not all of the giraffes -/
  | notAll
  deriving DecidableEq, Repr, Fintype

/-- The name the rows give the reading. -/
def Reading.label : Reading → String
  | .moreThanOne => "more than one giraffe"
  | .notMoreThanOne => "not more than one giraffe"
  | .notASingle => "not a single giraffe"
  | .notAll => "not all of the giraffes"

/-- The judgment a row records for the reading, if it records one. -/
def reading (e : Datum) (r : Reading) : Option Judgment :=
  e.readings.lookup r.label

end TieuEtAl2020.Examples
