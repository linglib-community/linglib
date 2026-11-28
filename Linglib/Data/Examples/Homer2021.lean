module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Homer2021` — typed example data

Auto-generated from `Linglib/Data/Examples/Homer2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Homer2021.Examples`.
-/

@[expose] public section

namespace Homer2021.Examples

def ex18 : Datum :=
  { id := "homer2021_ex18"
    source := ⟨"homer-2021", "(18)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Il n'est pas impossible que Jean ait fait quoi que ce soit pour aider la Mafia."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("item", "quoi que ce soit"), ("clause", "positive"), ("superordinate", "not impossible")] }

def ex19 : Datum :=
  { id := "homer2021_ex19"
    source := ⟨"homer-2021", "(19)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Il est impossible que Jean n'ait pas fait quoi que ce soit pour aider…"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "quoi que ce soit"), ("clause", "negative"), ("superordinate", "impossible")] }

def ex24 : Datum :=
  { id := "homer2021_ex24"
    source := ⟨"homer-2021", "(24)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "S'il est impossible que Jean ait fait quoi que ce soit pour aider la Mafia, je lui présenterai mes excuses."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "quoi que ce soit"), ("clause", "positive"), ("superordinate", "if impossible")] }

def ex32 : Datum :=
  { id := "homer2021_ex32"
    source := ⟨"homer-2021", "(32)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Il n'est pas impossible que Jean n'ait pas fait quoi que ce soit pour aider la Mafia."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "quoi que ce soit"), ("clause", "negative"), ("superordinate", "not impossible")] }

def ex41a : Datum :=
  { id := "homer2021_ex41a"
    source := ⟨"homer-2021", "(41a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "When Fred speaks French, Jean-Paul doesn't understand something."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("narrowest scope of some", .ungrammatical)]
    paperFeatures := [("item", "some"), ("clause", "negative")] }

def ex42a : Datum :=
  { id := "homer2021_ex42a"
    source := ⟨"homer-2021", "(42a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "I don't claim that Jean-Paul understands something."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("narrowest scope of some", .acceptable)]
    paperFeatures := [("item", "some"), ("clause", "positive"), ("superordinate", "not claim")] }

def ex42b : Datum :=
  { id := "homer2021_ex42b"
    source := ⟨"homer-2021", "(42b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "It is impossible that Jean-Paul understands something."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("narrowest scope of some", .acceptable)]
    paperFeatures := [("item", "some"), ("clause", "positive"), ("superordinate", "impossible")] }

def ex46a : Datum :=
  { id := "homer2021_ex46a"
    source := ⟨"homer-2021", "(46a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "I'm not sure that Jean-Paul doesn't understand something."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("narrowest scope of some", .acceptable)]
    paperFeatures := [("item", "some"), ("clause", "negative"), ("superordinate", "not sure")] }

def ex46b : Datum :=
  { id := "homer2021_ex46b"
    source := ⟨"homer-2021", "(46b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "If Jean-Paul doesn't understand something, he has no notion of French at all."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("narrowest scope of some", .acceptable)]
    paperFeatures := [("item", "some"), ("clause", "negative"), ("superordinate", "if")] }

def ex48a : Datum :=
  { id := "homer2021_ex48a"
    source := ⟨"homer-2021", "(48a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "It is impossible that John doesn't understand something."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("narrowest scope of some", .acceptable)]
    paperFeatures := [("item", "some"), ("clause", "negative"), ("superordinate", "impossible")] }

def ex48b : Datum :=
  { id := "homer2021_ex48b"
    source := ⟨"homer-2021", "(48b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "It is not impossible that John doesn't understand something."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("narrowest scope of some", .ungrammatical)]
    paperFeatures := [("item", "some"), ("clause", "negative"), ("superordinate", "not impossible")] }

def ex48c : Datum :=
  { id := "homer2021_ex48c"
    source := ⟨"homer-2021", "(48c)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "Not that it is impossible that John doesn't understand something."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("narrowest scope of some", .acceptable)]
    paperFeatures := [("item", "some"), ("clause", "negative"), ("superordinate", "not that impossible")] }

def ex50e : Datum :=
  { id := "homer2021_ex50e"
    source := ⟨"homer-2021", "(50e)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John didn't drink wine and any coffee."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("item", "any"), ("clause", "negative"), ("connective", "and")] }

def ex51b : Datum :=
  { id := "homer2021_ex51b"
    source := ⟨"homer-2021", "(51b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John didn't drink wine or any coffee."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "any"), ("clause", "negative"), ("connective", "or")] }

def ex56d : Datum :=
  { id := "homer2021_ex56d"
    source := ⟨"homer-2021", "(56d)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John didn't drink wine and some coffee."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("narrowest scope of some", .acceptable)]
    paperFeatures := [("item", "some"), ("clause", "negative"), ("connective", "and")] }

def ex56e : Datum :=
  { id := "homer2021_ex56e"
    source := ⟨"homer-2021", "(56e)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John didn't drink wine or some coffee."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("narrowest scope of some", .ungrammatical)]
    paperFeatures := [("item", "some"), ("clause", "negative"), ("connective", "or")] }

def ex92b : Datum :=
  { id := "homer2021_ex92b"
    source := ⟨"homer-2021", "(92b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "It is impossible that someone stole anything."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("IMPOS.≫SOME", .ungrammatical)]
    paperFeatures := [("subject", "someone"), ("object", "anything"), ("superordinate", "impossible"), ("clause", "positive")] }

def ex98 : Datum :=
  { id := "homer2021_ex98"
    source := ⟨"homer-2021", "(98)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "It's impossible that someone isn't eating anything."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("IMPOS.≫NEG≫SOME≫ANY", .ungrammatical), ("IMPOS.≫SOME≫NEG≫ANY", .acceptable)]
    paperFeatures := [("subject", "someone"), ("object", "anything"), ("superordinate", "impossible"), ("clause", "negative")] }

def ex103b : Datum :=
  { id := "homer2021_ex103b"
    source := ⟨"homer-2021", "(103b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "It is impossible that anyone stole something."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("IMPOS.≫SOME", .acceptable)]
    paperFeatures := [("subject", "anyone"), ("object", "something"), ("superordinate", "impossible"), ("clause", "positive")] }

def ex122b : Datum :=
  { id := "homer2021_ex122b"
    source := ⟨"homer-2021", "(122b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "I'm not sure that someone understood anything."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("NEG≫SOME", .ungrammatical)]
    paperFeatures := [("subject", "someone"), ("object", "anything"), ("superordinate", "not sure"), ("clause", "positive")] }

def all : List Datum := [ex18, ex19, ex24, ex32, ex41a, ex42a, ex42b, ex46a, ex46b, ex48a, ex48b, ex48c, ex50e, ex51b, ex56d, ex56e, ex92b, ex98, ex103b, ex122b]

/-- The polarity item a sentence with one item is judged for. -/
inductive Item where
  /-- quoi que ce soit: French *quoi que ce soit* -/
  | quoiQueCeSoit
  /-- any: English *any* -/
  | any
  /-- some: English *some* -/
  | some
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `item`. -/
def item (e : Datum) : Option Item :=
  e.parse? "item" [("quoi que ce soit", .quoiQueCeSoit), ("any", .any), ("some", .some)]

/-- The polarity of the clause that contains the item. -/
inductive ClausePolarity where
  /-- positive: no negation in the clause of the item -/
  | positive
  /-- negative: sentential negation in the clause of the item -/
  | negative
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `clause`. -/
def clause (e : Datum) : Option ClausePolarity :=
  e.parse? "clause" [("positive", .positive), ("negative", .negative)]

/-- The expressions above the clause of the item. -/
inductive Superordinate where
  /-- impossible: *it is impossible that* -/
  | impossible
  /-- not impossible: *it is not impossible that* -/
  | notImpossible
  /-- if impossible: the item below *impossible* in a conditional clause -/
  | ifImpossible
  /-- not claim: *I don't claim that* -/
  | notClaim
  /-- not sure: *I'm not sure that* -/
  | notSure
  /-- if: the item in a conditional clause -/
  | conditional
  /-- not that impossible: *not that it is impossible that* -/
  | notThatImpossible
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `superordinate`. -/
def superordinate (e : Datum) : Option Superordinate :=
  e.parse? "superordinate" [("impossible", .impossible), ("not impossible", .notImpossible),
    ("if impossible", .ifImpossible), ("not claim", .notClaim), ("not sure", .notSure),
    ("if", .conditional), ("not that impossible", .notThatImpossible)]

/-- The connective that joins the item's noun phrase to another below negation. -/
inductive Connective where
  /-- and: conjunction -/
  | and
  /-- or: disjunction -/
  | or
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `connective`. -/
def connective (e : Datum) : Option Connective :=
  e.parse? "connective" [("and", .and), ("or", .or)]

/-- The subject of a sentence with two polarity items. -/
inductive Subject where
  /-- someone: *someone* -/
  | someone
  /-- anyone: *anyone* -/
  | anyone
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `subject`. -/
def subject (e : Datum) : Option Subject :=
  e.parse? "subject" [("someone", .someone), ("anyone", .anyone)]

/-- The object of a sentence with two polarity items. -/
inductive Object where
  /-- anything: *anything* -/
  | anything
  /-- something: *something* -/
  | something
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `object`. -/
def object (e : Datum) : Option Object :=
  e.parse? "object" [("anything", .anything), ("something", .something)]

/-- The scope readings the sentences are judged on. -/
inductive Reading where
  /-- narrowest scope of some: *some* takes scope below every other operator -/
  | narrowestScope
  /-- IMPOS.≫SOME: *some* takes scope below *impossible* -/
  | imposSome
  /-- IMPOS.≫NEG≫SOME≫ANY: the subject *someone* is reconstructed below the negation -/
  | imposNegSomeAny
  /-- IMPOS.≫SOME≫NEG≫ANY: the subject *someone* takes scope above the negation -/
  | imposSomeNegAny
  /-- NEG≫SOME: *some* takes scope below the negation -/
  | negSome
  deriving DecidableEq, Repr, Fintype

/-- The name the rows give the reading. -/
def Reading.label : Reading → String
  | .narrowestScope => "narrowest scope of some"
  | .imposSome => "IMPOS.≫SOME"
  | .imposNegSomeAny => "IMPOS.≫NEG≫SOME≫ANY"
  | .imposSomeNegAny => "IMPOS.≫SOME≫NEG≫ANY"
  | .negSome => "NEG≫SOME"

/-- The judgment a row records for the reading, if it records one. -/
def reading (e : Datum) (r : Reading) : Option Judgment :=
  e.readings.lookup r.label

end Homer2021.Examples
