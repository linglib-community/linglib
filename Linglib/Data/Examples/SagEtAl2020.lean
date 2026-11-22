module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `SagEtAl2020` — typed example data

Auto-generated from `Linglib/Data/Examples/SagEtAl2020.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace SagEtAl2020.Examples`.
-/

@[expose] public section

namespace SagEtAl2020.Examples

def ex_9a_could : Datum :=
  { id := "sagetal2020_9a_could"
    source := ⟨"sag-etal-2020", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sandy could finish the job."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "can"), ("clause", "subjPred")] }

def ex_9a_helped : Datum :=
  { id := "sagetal2020_9a_helped"
    source := ⟨"sag-etal-2020", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sandy helped finish the job."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "help"), ("clause", "subjPred")] }

def ex_10a : Datum :=
  { id := "sagetal2020_10a"
    source := ⟨"sag-etal-2020", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kim dĭd leave."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "do"), ("clause", "subjPred")] }

def ex_10b : Datum :=
  { id := "sagetal2020_10b"
    source := ⟨"sag-etal-2020", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kim wĭll leave."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "will"), ("clause", "subjPred")] }

def p94_seems : Datum :=
  { id := "sagetal2020_p94_seems"
    source := ⟨"sag-etal-2020", "p. 94"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Seems Pat ever dishonest"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "seem"), ("clause", "polarInt")] }

def ex_11a : Datum :=
  { id := "sagetal2020_11a"
    source := ⟨"sag-etal-2020", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We shall dance."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("futurate", .acceptable)]
    paperFeatures := [("verb", "shall"), ("clause", "subjPred")] }

def ex_11b : Datum :=
  { id := "sagetal2020_11b"
    source := ⟨"sag-etal-2020", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Shall we dance?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("deontic", .acceptable)]
    paperFeatures := [("verb", "shall"), ("clause", "polarInt")] }

def ex_14a : Datum :=
  { id := "sagetal2020_14a"
    source := ⟨"sag-etal-2020", "(14a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We better be careful."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "better"), ("clause", "subjPred")] }

def ex_14b : Datum :=
  { id := "sagetal2020_14b"
    source := ⟨"sag-etal-2020", "(14b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Better we be careful?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "better"), ("clause", "polarInt")] }

def fig11 : Datum :=
  { id := "sagetal2020_fig11"
    source := ⟨"sag-etal-2020", "Figure 11"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Did Kim get the job?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "do"), ("clause", "polarInt")] }

def ex_42a : Datum :=
  { id := "sagetal2020_42a"
    source := ⟨"chomsky-1981", "p. 209"⟩
    reportedIn := some ⟨"sag-etal-2020", "(42a)"⟩
    language := "stan1293"
    primaryText := "I shall go downtown."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("futurate", .acceptable), ("deontic", .unacceptable)]
    paperFeatures := [("verb", "shall"), ("clause", "subjPred")] }

def ex_42b : Datum :=
  { id := "sagetal2020_42b"
    source := ⟨"chomsky-1981", "p. 209"⟩
    reportedIn := some ⟨"sag-etal-2020", "(42b)"⟩
    language := "stan1293"
    primaryText := "Shall I go downtown?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("deontic", .acceptable)]
    paperFeatures := [("verb", "shall"), ("clause", "polarInt")] }

def ex_44 : Datum :=
  { id := "sagetal2020_44"
    source := ⟨"sag-etal-2020", "(44)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Shall we be home in time for tea, do you think?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("futurate", .acceptable)]
    paperFeatures := [("verb", "shall"), ("clause", "polarInt")] }

def ex_48a : Datum :=
  { id := "sagetal2020_48a"
    source := ⟨"sag-etal-2020", "(48a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I better get out of here!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "better"), ("clause", "subjPred")] }

def ex_48b : Datum :=
  { id := "sagetal2020_48b"
    source := ⟨"sag-etal-2020", "(48b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Better I get out of here?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "better"), ("clause", "polarInt")] }

def ex_112a : Datum :=
  { id := "sagetal2020_112a"
    source := ⟨"sag-etal-2020", "(112a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Aren’t I on the list?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "arent"), ("clause", "polarInt")] }

def ex_112b : Datum :=
  { id := "sagetal2020_112b"
    source := ⟨"sag-etal-2020", "(112b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Aren’t I clever!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "arent"), ("clause", "auxInitialExcl")] }

def ex_113a : Datum :=
  { id := "sagetal2020_113a"
    source := ⟨"sag-etal-2020", "(113a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I aren’t an idiot."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "arent"), ("clause", "subjPred")] }

def all : List Datum := [ex_9a_could, ex_9a_helped, ex_10a, ex_10b, p94_seems, ex_11a, ex_11b, ex_14a, ex_14b, fig11, ex_42a, ex_42b, ex_44, ex_48a, ex_48b, ex_112a, ex_112b, ex_113a]

/-- The finite verb of the example. -/
inductive Verb where
  /-- can: the modal *can*, in its present or its preterite -/
  | can
  /-- will: the modal *will* -/
  | will
  /-- shall: the modal *shall* -/
  | shall
  /-- better: the modal *better* -/
  | better
  /-- do: unstressed auxiliary *do* -/
  | doAux
  /-- arent: *aren't* with a first person singular subject -/
  | arent
  /-- help: the lexical verb *help* -/
  | help
  /-- seem: the lexical verb *seem* -/
  | seem
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `verb`. -/
def verb (e : Datum) : Option Verb :=
  e.parse? "verb" [("can", .can), ("will", .will), ("shall", .shall), ("better", .better), ("do", .doAux),
    ("arent", .arent), ("help", .help), ("seem", .seem)]

/-- The clause type of the example. -/
inductive Clause where
  /-- subjPred: a subject-predicate clause, the subject before the finite verb -/
  | subjPred
  /-- polarInt: a polar interrogative, the finite verb before the subject -/
  | polarInt
  /-- auxInitialExcl: an inverted exclamative, the finite verb before the subject -/
  | auxInitialExcl
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `clause`. -/
def clause (e : Datum) : Option Clause :=
  e.parse? "clause" [("subjPred", .subjPred), ("polarInt", .polarInt), ("auxInitialExcl", .auxInitialExcl)]

/-- The senses of *shall* that the paper judges. -/
inductive Reading where
  /-- futurate: simple futurity -/
  | futurate
  /-- deontic: the deontic sense -/
  | deontic
  deriving DecidableEq, Repr, Fintype

/-- The name the rows give the reading. -/
def Reading.label : Reading → String
  | .futurate => "futurate"
  | .deontic => "deontic"

/-- The judgment a row records for the reading, if it records one. -/
def reading (e : Datum) (r : Reading) : Option Judgment :=
  e.readings.lookup r.label

/-- The examples. -/
inductive Example where
  | ex_9a_could
  | ex_9a_helped
  | ex_10a
  | ex_10b
  | p94_seems
  | ex_11a
  | ex_11b
  | ex_14a
  | ex_14b
  | fig11
  | ex_42a
  | ex_42b
  | ex_44
  | ex_48a
  | ex_48b
  | ex_112a
  | ex_112b
  | ex_113a
  deriving DecidableEq, Repr, Fintype

/-- Every example of the file, in its order. -/
def Example.all : List Example :=
  [.ex_9a_could, .ex_9a_helped, .ex_10a, .ex_10b, .p94_seems, .ex_11a, .ex_11b, .ex_14a, .ex_14b,
    .fig11, .ex_42a, .ex_42b, .ex_44, .ex_48a, .ex_48b, .ex_112a, .ex_112b, .ex_113a]

/-- The row of an example. -/
def Example.datum : Example → Datum
  | .ex_9a_could => _root_.SagEtAl2020.Examples.ex_9a_could
  | .ex_9a_helped => _root_.SagEtAl2020.Examples.ex_9a_helped
  | .ex_10a => _root_.SagEtAl2020.Examples.ex_10a
  | .ex_10b => _root_.SagEtAl2020.Examples.ex_10b
  | .p94_seems => _root_.SagEtAl2020.Examples.p94_seems
  | .ex_11a => _root_.SagEtAl2020.Examples.ex_11a
  | .ex_11b => _root_.SagEtAl2020.Examples.ex_11b
  | .ex_14a => _root_.SagEtAl2020.Examples.ex_14a
  | .ex_14b => _root_.SagEtAl2020.Examples.ex_14b
  | .fig11 => _root_.SagEtAl2020.Examples.fig11
  | .ex_42a => _root_.SagEtAl2020.Examples.ex_42a
  | .ex_42b => _root_.SagEtAl2020.Examples.ex_42b
  | .ex_44 => _root_.SagEtAl2020.Examples.ex_44
  | .ex_48a => _root_.SagEtAl2020.Examples.ex_48a
  | .ex_48b => _root_.SagEtAl2020.Examples.ex_48b
  | .ex_112a => _root_.SagEtAl2020.Examples.ex_112a
  | .ex_112b => _root_.SagEtAl2020.Examples.ex_112b
  | .ex_113a => _root_.SagEtAl2020.Examples.ex_113a

theorem Example.map_datum_all :
    Example.all.map Example.datum = _root_.SagEtAl2020.Examples.all := rfl

/-- The value the example records under `verb`. -/
def Example.verb : Example → Option Verb
  | .ex_9a_could => some .can
  | .ex_9a_helped => some .help
  | .ex_10a => some .doAux
  | .ex_10b => some .will
  | .p94_seems => some .seem
  | .ex_11a => some .shall
  | .ex_11b => some .shall
  | .ex_14a => some .better
  | .ex_14b => some .better
  | .fig11 => some .doAux
  | .ex_42a => some .shall
  | .ex_42b => some .shall
  | .ex_44 => some .shall
  | .ex_48a => some .better
  | .ex_48b => some .better
  | .ex_112a => some .arent
  | .ex_112b => some .arent
  | .ex_113a => some .arent

theorem Example.verb_datum :
    ∀ x : Example, _root_.SagEtAl2020.Examples.verb x.datum = x.verb := by
  decide +kernel

/-- The value the example records under `clause`. -/
def Example.clause : Example → Option Clause
  | .ex_9a_could => some .subjPred
  | .ex_9a_helped => some .subjPred
  | .ex_10a => some .subjPred
  | .ex_10b => some .subjPred
  | .p94_seems => some .polarInt
  | .ex_11a => some .subjPred
  | .ex_11b => some .polarInt
  | .ex_14a => some .subjPred
  | .ex_14b => some .polarInt
  | .fig11 => some .polarInt
  | .ex_42a => some .subjPred
  | .ex_42b => some .polarInt
  | .ex_44 => some .polarInt
  | .ex_48a => some .subjPred
  | .ex_48b => some .polarInt
  | .ex_112a => some .polarInt
  | .ex_112b => some .auxInitialExcl
  | .ex_113a => some .subjPred

theorem Example.clause_datum :
    ∀ x : Example, _root_.SagEtAl2020.Examples.clause x.datum = x.clause := by
  decide +kernel

/-- The readings the example judges, each with its judgment. -/
def Example.readings : Example → List (Reading × Judgment)
  | .ex_9a_could => []
  | .ex_9a_helped => []
  | .ex_10a => []
  | .ex_10b => []
  | .p94_seems => []
  | .ex_11a => [(.futurate, .acceptable)]
  | .ex_11b => [(.deontic, .acceptable)]
  | .ex_14a => []
  | .ex_14b => []
  | .fig11 => []
  | .ex_42a => [(.futurate, .acceptable), (.deontic, .unacceptable)]
  | .ex_42b => [(.deontic, .acceptable)]
  | .ex_44 => [(.futurate, .acceptable)]
  | .ex_48a => []
  | .ex_48b => []
  | .ex_112a => []
  | .ex_112b => []
  | .ex_113a => []

/-- The judgment the example records for the reading, if it records one. -/
def Example.reading (x : Example) (r : Reading) : Option Judgment :=
  (x.readings.lookup r)

theorem Example.reading_datum : ∀ (x : Example) (r : Reading),
    _root_.SagEtAl2020.Examples.reading x.datum r = x.reading r := by
  decide +kernel

end SagEtAl2020.Examples
