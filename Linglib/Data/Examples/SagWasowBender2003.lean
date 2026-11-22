module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `SagWasowBender2003` — typed example data

Auto-generated from `Linglib/Data/Examples/SagWasowBender2003.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace SagWasowBender2003.Examples`.
-/

@[expose] public section

namespace SagWasowBender2003.Examples

def ex2a : Datum :=
  { id := "sagwasowbender2003_ex2a"
    source := ⟨"sag-wasow-bender-2003", "ch. 7, (2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Susan likes herself."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("topic", "binding"), ("sort", "anaphor"), ("frame", "transitive")] }

def ex2b : Datum :=
  { id := "sagwasowbender2003_ex2b"
    source := ⟨"sag-wasow-bender-2003", "ch. 7, (2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Susan likes her."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("topic", "binding"), ("sort", "pronoun"), ("frame", "transitive")] }

def ex3a : Datum :=
  { id := "sagwasowbender2003_ex3a"
    source := ⟨"sag-wasow-bender-2003", "ch. 7, (3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Susan told herself a story."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("topic", "binding"), ("sort", "anaphor"), ("frame", "double object")] }

def ex3b : Datum :=
  { id := "sagwasowbender2003_ex3b"
    source := ⟨"sag-wasow-bender-2003", "ch. 7, (3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Susan told her a story."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("topic", "binding"), ("sort", "pronoun"), ("frame", "double object")] }

def ex4a : Datum :=
  { id := "sagwasowbender2003_ex4a"
    source := ⟨"sag-wasow-bender-2003", "ch. 7, (4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Susan told a story to herself."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("topic", "binding"), ("sort", "anaphor"), ("frame", "to-PP")] }

def ex4b : Datum :=
  { id := "sagwasowbender2003_ex4b"
    source := ⟨"sag-wasow-bender-2003", "ch. 7, (4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Susan told a story to her."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("topic", "binding"), ("sort", "pronoun"), ("frame", "to-PP")] }

def ex5a : Datum :=
  { id := "sagwasowbender2003_ex5a"
    source := ⟨"sag-wasow-bender-2003", "ch. 7, (5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Susan devoted herself to linguistics."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("topic", "binding"), ("sort", "anaphor"), ("frame", "object and PP")] }

def ex5b : Datum :=
  { id := "sagwasowbender2003_ex5b"
    source := ⟨"sag-wasow-bender-2003", "ch. 7, (5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Susan devoted her to linguistics."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("topic", "binding"), ("sort", "pronoun"), ("frame", "object and PP")] }

def ex6a : Datum :=
  { id := "sagwasowbender2003_ex6a"
    source := ⟨"sag-wasow-bender-2003", "ch. 7, (6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Nobody told Susan about herself."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("topic", "binding"), ("sort", "anaphor"), ("frame", "object antecedent")] }

def ex6b : Datum :=
  { id := "sagwasowbender2003_ex6b"
    source := ⟨"sag-wasow-bender-2003", "ch. 7, (6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Nobody told Susan about her."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("topic", "binding"), ("sort", "pronoun"), ("frame", "object antecedent")] }

def ex7a : Datum :=
  { id := "sagwasowbender2003_ex7a"
    source := ⟨"sag-wasow-bender-2003", "ch. 7, (7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Susan thinks that nobody likes herself."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("topic", "binding"), ("sort", "anaphor"), ("frame", "embedded clause")] }

def ex7b : Datum :=
  { id := "sagwasowbender2003_ex7b"
    source := ⟨"sag-wasow-bender-2003", "ch. 7, (7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Susan thinks that nobody likes her."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("topic", "binding"), ("sort", "pronoun"), ("frame", "embedded clause")] }

def ex8a : Datum :=
  { id := "sagwasowbender2003_ex8a"
    source := ⟨"sag-wasow-bender-2003", "ch. 7, (8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Susan's friends like herself."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("topic", "binding"), ("sort", "anaphor"), ("frame", "possessor")] }

def ex8b : Datum :=
  { id := "sagwasowbender2003_ex8b"
    source := ⟨"sag-wasow-bender-2003", "ch. 7, (8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Susan's friends like her."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("topic", "binding"), ("sort", "pronoun"), ("frame", "possessor")] }

def ex9a : Datum :=
  { id := "sagwasowbender2003_ex9a"
    source := ⟨"sag-wasow-bender-2003", "ch. 7, (9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That picture of Susan offended herself."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("topic", "binding"), ("sort", "anaphor"), ("frame", "picture noun")] }

def ex9b : Datum :=
  { id := "sagwasowbender2003_ex9b"
    source := ⟨"sag-wasow-bender-2003", "ch. 7, (9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That picture of Susan offended her."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("topic", "binding"), ("sort", "pronoun"), ("frame", "picture noun")] }

def ex17a : Datum :=
  { id := "sagwasowbender2003_ex17a"
    source := ⟨"sag-wasow-bender-2003", "ch. 7, (17a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I enjoy yourself."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("topic", "pronominal agreement"), ("antecedent", "I"), ("reflexive", "yourself")] }

def ex17b : Datum :=
  { id := "sagwasowbender2003_ex17b"
    source := ⟨"sag-wasow-bender-2003", "ch. 7, (17b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He enjoys themselves."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("topic", "pronominal agreement"), ("antecedent", "he"), ("reflexive", "themselves")] }

def ex17c : Datum :=
  { id := "sagwasowbender2003_ex17c"
    source := ⟨"sag-wasow-bender-2003", "ch. 7, (17c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She enjoys himself."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("topic", "pronominal agreement"), ("antecedent", "she"), ("reflexive", "himself")] }

def ex37a : Datum :=
  { id := "sagwasowbender2003_ex37a"
    source := ⟨"sag-wasow-bender-2003", "ch. 15, (37a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Here is the student that the principal suspended and Sandy defended him."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("topic", "coordination"), ("gapInFirst", "true"), ("gapInSecond", "false")] }

def ex37b : Datum :=
  { id := "sagwasowbender2003_ex37b"
    source := ⟨"sag-wasow-bender-2003", "ch. 15, (37b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Here is the student that the student council passed new rules and the principal suspended."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("topic", "coordination"), ("gapInFirst", "false"), ("gapInSecond", "true")] }

def ex38a : Datum :=
  { id := "sagwasowbender2003_ex38a"
    source := ⟨"sag-wasow-bender-2003", "ch. 15, (38a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Apple bagels, I can assure you that Leslie likes and Sandy hates cream cheese."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("topic", "coordination"), ("gapInFirst", "true"), ("gapInSecond", "false")] }

def ex38b : Datum :=
  { id := "sagwasowbender2003_ex38b"
    source := ⟨"sag-wasow-bender-2003", "ch. 15, (38b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Apple bagels, I can assure you that Leslie likes cream cheese and Sandy hates."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("topic", "coordination"), ("gapInFirst", "false"), ("gapInSecond", "true")] }

def ex40a : Datum :=
  { id := "sagwasowbender2003_ex40a"
    source := ⟨"sag-wasow-bender-2003", "ch. 15, (40a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This is the dancer that we bought a portrait of and two photos of."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("topic", "coordination"), ("gapInFirst", "true"), ("gapInSecond", "true")] }

def ex40b : Datum :=
  { id := "sagwasowbender2003_ex40b"
    source := ⟨"sag-wasow-bender-2003", "ch. 15, (40b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Here is the student that the principal suspended and the teacher defended."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("topic", "coordination"), ("gapInFirst", "true"), ("gapInSecond", "true")] }

def ex40c : Datum :=
  { id := "sagwasowbender2003_ex40c"
    source := ⟨"sag-wasow-bender-2003", "ch. 15, (40c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Apple bagels, I can assure you that Leslie likes and Sandy hates."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("topic", "coordination"), ("gapInFirst", "true"), ("gapInSecond", "true")] }

def ex36a : Datum :=
  { id := "sagwasowbender2003_ex36a"
    source := ⟨"sag-wasow-bender-2003", "ch. 15, (36a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Here is the student that the principal suspended and Sandy."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("topic", "conjunctGap")] }

def ex36b : Datum :=
  { id := "sagwasowbender2003_ex36b"
    source := ⟨"sag-wasow-bender-2003", "ch. 15, (36b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Here is the student that the principal suspended Sandy and."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("topic", "conjunctGap")] }

def ex44 : Datum :=
  { id := "sagwasowbender2003_ex44"
    source := ⟨"sag-wasow-bender-2003", "ch. 15, (44)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which rock legend would it be ridiculous to compare and?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("topic", "conjunctGap")] }

def all : List Datum := [ex2a, ex2b, ex3a, ex3b, ex4a, ex4b, ex5a, ex5b, ex6a, ex6b, ex7a, ex7b, ex8a, ex8b, ex9a, ex9b, ex17a, ex17b, ex17c, ex37a, ex37b, ex38a, ex38b, ex40a, ex40b, ex40c, ex36a, ex36b, ex44]

/-- The part of the textbook a row illustrates. -/
inductive Topic where
  /-- binding: the binding principles of Chapter 7 -/
  | binding
  /-- pronominal agreement: the agreement of a reflexive with its antecedent (§7.3.2.1) -/
  | pronominalAgreement
  /-- coordination: extraction from coordinate structures (Chapter 15) -/
  | coordination
  /-- conjunctGap: a conjunct that is itself a gap (Chapter 15) -/
  | conjunctGap
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `topic`. -/
def topic (e : Datum) : Option Topic :=
  e.parse? "topic" [("binding", .binding), ("pronominal agreement", .pronominalAgreement),
    ("coordination", .coordination), ("conjunctGap", .conjunctGap)]

/-- Whether a row's pronoun is a reflexive or a personal pronoun. -/
inductive PronounSort where
  /-- anaphor: a reflexive pronoun -/
  | anaphor
  /-- pronoun: a nonreflexive personal pronoun -/
  | pronoun
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `sort`. -/
def sort (e : Datum) : Option PronounSort :=
  e.parse? "sort" [("anaphor", .anaphor), ("pronoun", .pronoun)]

/-- The argument structures of a row's sentence, with the places of *Susan* and of the pronoun on them. -/
inductive Frame where
  /-- transitive: a transitive verb with *Susan* as subject and the pronoun as object -/
  | transitive
  /-- double object: a verb with *Susan* as subject, the pronoun as first object and a second object -/
  | doubleObject
  /-- to-PP: a verb with *Susan* as subject, an object, and the pronoun as object of an argument-marking preposition -/
  | toDative
  /-- object and PP: a verb with *Susan* as subject, the pronoun as object, and a prepositional complement -/
  | objectAndPP
  /-- object antecedent: a verb with another subject, *Susan* as object, and the pronoun as object of an argument-marking preposition -/
  | objectAntecedent
  /-- embedded clause: *Susan* as subject of a verb taking a clause, in which the pronoun is the object of a verb with another subject -/
  | embedded
  /-- possessor: the pronoun as object of a verb whose subject is a noun phrase with *Susan* as possessor -/
  | possessor
  /-- picture noun: the pronoun as object of a verb whose subject is a noun phrase with *Susan* as complement of its noun -/
  | pictureNoun
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `frame`. -/
def frame (e : Datum) : Option Frame :=
  e.parse? "frame" [("transitive", .transitive), ("double object", .doubleObject), ("to-PP", .toDative),
    ("object and PP", .objectAndPP), ("object antecedent", .objectAntecedent),
    ("embedded clause", .embedded), ("possessor", .possessor), ("picture noun", .pictureNoun)]

end SagWasowBender2003.Examples
