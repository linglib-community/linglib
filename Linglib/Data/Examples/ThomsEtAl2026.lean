module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `ThomsEtAl2026` — typed example data

Auto-generated from `Linglib/Data/Examples/ThomsEtAl2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ThomsEtAl2026.Examples`.
-/

@[expose] public section

namespace ThomsEtAl2026.Examples

def ex_5a_A : Datum :=
  { id := "thomsetal2026_5a_A"
    source := ⟨"thoms-etal-2026", "(5a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "I haven't any money with me."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("group", "A"), ("frame", "raisedNegation"), ("determiner", "any"), ("relation", "alienable")] }

def ex_5a_B : Datum :=
  { id := "thomsetal2026_5a_B"
    source := ⟨"thoms-etal-2026", "(5a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "I haven't any money with me."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("group", "B"), ("frame", "raisedNegation"), ("determiner", "any"), ("relation", "alienable")] }

def ex_5b_A : Datum :=
  { id := "thomsetal2026_5b_A"
    source := ⟨"thoms-etal-2026", "(5b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "I haven't that charger with me."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("group", "A"), ("frame", "raisedNegation"), ("determiner", "that"), ("relation", "alienable")] }

def ex_5b_B : Datum :=
  { id := "thomsetal2026_5b_B"
    source := ⟨"thoms-etal-2026", "(5b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "I haven't that charger with me."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("group", "B"), ("frame", "raisedNegation"), ("determiner", "that"), ("relation", "alienable")] }

def ex_7a_A : Datum :=
  { id := "thomsetal2026_7a_A"
    source := ⟨"thoms-etal-2026", "(7a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "I haven't any cousins."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("group", "A"), ("frame", "raisedNegation"), ("determiner", "any"), ("relation", "kinship")] }

def ex_7b_A : Datum :=
  { id := "thomsetal2026_7b_A"
    source := ⟨"thoms-etal-2026", "(7b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "I haven't much hair left."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("group", "A"), ("frame", "raisedNegation"), ("determiner", "much"), ("relation", "bodyPart")] }

def ex_8a_A : Datum :=
  { id := "thomsetal2026_8a_A"
    source := ⟨"thoms-etal-2026", "(8a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "I haven't the money they lent me."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("group", "A"), ("frame", "raisedNegation"), ("determiner", "the"), ("relation", "alienable")] }

def ex_8b_A : Datum :=
  { id := "thomsetal2026_8b_A"
    source := ⟨"thoms-etal-2026", "(8b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "I haven't the money to buy what we need."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("group", "A"), ("frame", "raisedNegation"), ("determiner", "amountThe"), ("relation", "alienable")] }

def ex_9a : Datum :=
  { id := "thomsetal2026_9a"
    source := ⟨"thoms-etal-2026", "(9a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "There isn't the money they lent me."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("frame", "thereBe"), ("determiner", "the")] }

def ex_9b : Datum :=
  { id := "thomsetal2026_9b"
    source := ⟨"thoms-etal-2026", "(9b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "There isn't the money to buy what we need."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "thereBe"), ("determiner", "amountThe")] }

def ex_10a_A : Datum :=
  { id := "thomsetal2026_10a_A"
    source := ⟨"thoms-etal-2026", "(10a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "I haven't every Perec novel in paperback."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("group", "A"), ("frame", "raisedNegation"), ("determiner", "every"), ("relation", "alienable")] }

def ex_10b_A : Datum :=
  { id := "thomsetal2026_10b_A"
    source := ⟨"thoms-etal-2026", "(10b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "I haven't most Perec novels in paperback."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("group", "A"), ("frame", "raisedNegation"), ("determiner", "most"), ("relation", "alienable")] }

def ex_11a_A : Datum :=
  { id := "thomsetal2026_11a_A"
    source := ⟨"thoms-etal-2026", "(11a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "Have you every Perec novel in paperback?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("group", "A"), ("frame", "raisedQuestion"), ("determiner", "every"), ("relation", "alienable")] }

def ex_11b_A : Datum :=
  { id := "thomsetal2026_11b_A"
    source := ⟨"thoms-etal-2026", "(11b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "Have you most Perec novels in paperback?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("group", "A"), ("frame", "raisedQuestion"), ("determiner", "most"), ("relation", "alienable")] }

def ex_12a : Datum :=
  { id := "thomsetal2026_12a"
    source := ⟨"thoms-etal-2026", "(12a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "I have every Perec novel in paperback."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "plain"), ("determiner", "every"), ("relation", "alienable")] }

def ex_12b : Datum :=
  { id := "thomsetal2026_12b"
    source := ⟨"thoms-etal-2026", "(12b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "I have most Perec novels in paperback."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "plain"), ("determiner", "most"), ("relation", "alienable")] }

def ex_12c : Datum :=
  { id := "thomsetal2026_12c"
    source := ⟨"thoms-etal-2026", "(12c)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "I have the money they lent me."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "plain"), ("determiner", "the"), ("relation", "alienable")] }

def ex_13a : Datum :=
  { id := "thomsetal2026_13a"
    source := ⟨"thoms-etal-2026", "(13a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "I have got every Perec novel in paperback."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "haveGot"), ("determiner", "every"), ("relation", "alienable")] }

def ex_13b : Datum :=
  { id := "thomsetal2026_13b"
    source := ⟨"thoms-etal-2026", "(13b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "I have got most Perec novels in paperback."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "haveGot"), ("determiner", "most"), ("relation", "alienable")] }

def ex_13c : Datum :=
  { id := "thomsetal2026_13c"
    source := ⟨"thoms-etal-2026", "(13c)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "I have got the money they lent me."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "haveGot"), ("determiner", "the"), ("relation", "alienable")] }

def ex_14a : Datum :=
  { id := "thomsetal2026_14a"
    source := ⟨"thoms-etal-2026", "(14a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "I don't have every Perec novel in paperback."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "doSupport"), ("determiner", "every"), ("relation", "alienable")] }

def ex_14b : Datum :=
  { id := "thomsetal2026_14b"
    source := ⟨"thoms-etal-2026", "(14b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "I don't have most Perec novels in paperback."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "doSupport"), ("determiner", "most"), ("relation", "alienable")] }

def ex_14c : Datum :=
  { id := "thomsetal2026_14c"
    source := ⟨"thoms-etal-2026", "(14c)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "I don't have the money they lent me."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "doSupport"), ("determiner", "the"), ("relation", "alienable")] }

def ex_15a : Datum :=
  { id := "thomsetal2026_15a"
    source := ⟨"thoms-etal-2026", "(15a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "There is every Perec novel on that shelf."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("frame", "thereBe"), ("determiner", "every")] }

def ex_15b : Datum :=
  { id := "thomsetal2026_15b"
    source := ⟨"thoms-etal-2026", "(15b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "There are most Perec novels on that shelf."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("frame", "thereBe"), ("determiner", "most")] }

def ex_43a : Datum :=
  { id := "thomsetal2026_43a"
    source := ⟨"thoms-etal-2026", "(43a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "I have the keys."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "plain"), ("determiner", "the"), ("relation", "alienable")] }

def ex_43b : Datum :=
  { id := "thomsetal2026_43b"
    source := ⟨"thoms-etal-2026", "(43b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John has your typewriter."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "plain"), ("determiner", "your"), ("relation", "alienable")] }

def ex_48a : Datum :=
  { id := "thomsetal2026_48a"
    source := ⟨"thoms-etal-2026", "(48a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "I have that sister."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("frame", "plain"), ("determiner", "that"), ("relation", "kinship")] }

def ex_48b : Datum :=
  { id := "thomsetal2026_48b"
    source := ⟨"thoms-etal-2026", "(48b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "I have your mother."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("frame", "plain"), ("determiner", "your"), ("relation", "kinship")] }

def ex_48c : Datum :=
  { id := "thomsetal2026_48c"
    source := ⟨"thoms-etal-2026", "(48c)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "I have the blue eyes."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("frame", "plain"), ("determiner", "the"), ("relation", "bodyPart")] }

def all : List Datum := [ex_5a_A, ex_5a_B, ex_5b_A, ex_5b_B, ex_7a_A, ex_7b_A, ex_8a_A, ex_8b_A, ex_9a, ex_9b, ex_10a_A, ex_10b_A, ex_11a_A, ex_11b_A, ex_12a, ex_12b, ex_12c, ex_13a, ex_13b, ex_13c, ex_14a, ex_14b, ex_14c, ex_15a, ex_15b, ex_43a, ex_43b, ex_48a, ex_48b, ex_48c]

/-- The group of speakers a judgment is attributed to; absent for English generally. -/
inductive Group where
  /-- A: Group A, who accept HAVE-raising with indefinite possessees only -/
  | a
  /-- B: Group B, who accept HAVE-raising with definite possessees too -/
  | b
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `group`. -/
def group (e : Datum) : Option Group :=
  e.parse? "group" [("A", .a), ("B", .b)]

/-- The clause type, which shows or hides the position of the verb. -/
inductive Frame where
  /-- raisedNegation: HAVE before negation -/
  | raisedNegation
  /-- raisedQuestion: HAVE inverted with the subject -/
  | raisedQuestion
  /-- plain: HAVE in a clause with no positional diagnostic -/
  | plain
  /-- haveGot: HAVE GOT -/
  | haveGot
  /-- doSupport: HAVE under *do*-support -/
  | doSupport
  /-- thereBe: a *there*-existential -/
  | thereBe
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `frame`. -/
def frame (e : Datum) : Option Frame :=
  e.parse? "frame" [("raisedNegation", .raisedNegation), ("raisedQuestion", .raisedQuestion), ("plain", .plain),
    ("haveGot", .haveGot), ("doSupport", .doSupport), ("thereBe", .thereBe)]

/-- The determiner of the possessee, or of the pivot of an existential. -/
inductive Determiner where
  /-- any: *any* -/
  | any
  /-- much: *much* -/
  | much
  /-- amountThe: *the* in an amount phrase, semantically indefinite -/
  | amountThe
  /-- the: the definite article -/
  | the
  /-- that: the demonstrative *that* -/
  | that
  /-- your: a possessive -/
  | your
  /-- every: *every* -/
  | every
  /-- most: *most* -/
  | most
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `determiner`. -/
def determiner (e : Datum) : Option Determiner :=
  e.parse? "determiner" [("any", .any), ("much", .much), ("amountThe", .amountThe), ("the", .the), ("that", .that),
    ("your", .your), ("every", .every), ("most", .most)]

/-- The relation of the possessor to the possessee. -/
inductive Relation where
  /-- alienable: alienable possession, including temporary possession -/
  | alienable
  /-- kinship: a kinship relation -/
  | kinship
  /-- bodyPart: a body part -/
  | bodyPart
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `relation`. -/
def relation (e : Datum) : Option Relation :=
  e.parse? "relation" [("alienable", .alienable), ("kinship", .kinship), ("bodyPart", .bodyPart)]

end ThomsEtAl2026.Examples
