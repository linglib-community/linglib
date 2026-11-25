module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `GoldbergJackendoff2004` — typed example data

Auto-generated from `Linglib/Data/Examples/GoldbergJackendoff2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace GoldbergJackendoff2004.Examples`.
-/

@[expose] public section

namespace GoldbergJackendoff2004.Examples

def gj2004_5a : Datum :=
  { id := "gj2004_5a"
    source := ⟨"goldberg-jackendoff-2004", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Herman hammered the metal flat."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "hammer"), ("subconstruction", "causative property"), ("rpCat", "AP"), ("selection", "selected")] }

def gj2004_5b : Datum :=
  { id := "gj2004_5b"
    source := ⟨"goldberg-jackendoff-2004", "(5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The critics laughed the play off the stage."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "laugh"), ("subconstruction", "causative path"), ("rpCat", "PP"), ("selection", "unselected")] }

def gj2004_6a : Datum :=
  { id := "gj2004_6a"
    source := ⟨"goldberg-jackendoff-2004", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The pond froze solid."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "freeze"), ("subconstruction", "noncausative property"), ("rpCat", "AP")] }

def gj2004_6b : Datum :=
  { id := "gj2004_6b"
    source := ⟨"goldberg-jackendoff-2004", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill rolled out of the room."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "roll"), ("subconstruction", "noncausative path"), ("rpCat", "PP")] }

def gj2004_7a : Datum :=
  { id := "gj2004_7a"
    source := ⟨"goldberg-jackendoff-2004", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The gardener watered the flowers flat."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "water"), ("subconstruction", "causative property"), ("rpCat", "AP"), ("selection", "selected")] }

def gj2004_7b : Datum :=
  { id := "gj2004_7b"
    source := ⟨"goldberg-jackendoff-2004", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill broke the bathtub into pieces."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "break"), ("subconstruction", "causative property"), ("rpCat", "PP"), ("selection", "selected")] }

def gj2004_8a : Datum :=
  { id := "gj2004_8a"
    source := ⟨"goldberg-jackendoff-2004", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They drank the pub dry."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("They drank the pub.", .ungrammatical)]
    readings := []
    paperFeatures := [("verb", "drink"), ("subconstruction", "causative property"), ("rpCat", "AP"), ("selection", "unselected")] }

def gj2004_8b : Datum :=
  { id := "gj2004_8b"
    source := ⟨"goldberg-jackendoff-2004", "(8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The professor talked us into a stupor."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("The professor talked us.", .ungrammatical)]
    readings := []
    paperFeatures := [("verb", "talk"), ("subconstruction", "causative property"), ("rpCat", "PP"), ("selection", "unselected")] }

def gj2004_9a : Datum :=
  { id := "gj2004_9a"
    source := ⟨"goldberg-jackendoff-2004", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We yelled ourselves hoarse."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("We yelled ourselves.", .ungrammatical), ("We yelled Harry hoarse.", .ungrammatical)]
    readings := []
    paperFeatures := [("verb", "yell"), ("subconstruction", "causative property"), ("rpCat", "AP"), ("selection", "fake reflexive")] }

def gj2004_23a : Datum :=
  { id := "gj2004_23a"
    source := ⟨"goldberg-jackendoff-2004", "(23a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "For hours, Bill heated the mixture hotter and hotter."
    glossedTokens := []
    context := "Nonrepetitive reading."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "heat"), ("subconstruction", "causative property"), ("rpCat", "AP"), ("endBounded", "false")] }

def gj2004_23b : Datum :=
  { id := "gj2004_23b"
    source := ⟨"goldberg-jackendoff-2004", "(23b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "For hours, Bill hammered the metal ever flatter."
    glossedTokens := []
    context := "Nonrepetitive reading."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "hammer"), ("subconstruction", "causative property"), ("rpCat", "AP"), ("endBounded", "false")] }

def gj2004_23c : Datum :=
  { id := "gj2004_23c"
    source := ⟨"goldberg-jackendoff-2004", "(23c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "For years, Penelope wove the shawl longer and longer."
    glossedTokens := []
    context := "Nonrepetitive reading."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "weave"), ("subconstruction", "causative property"), ("rpCat", "AP"), ("endBounded", "false")] }

def gj2004_24a : Datum :=
  { id := "gj2004_24a"
    source := ⟨"goldberg-jackendoff-2004", "(24a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill floated into the cave for hours."
    glossedTokens := []
    context := "Nonrepetitive reading."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "float"), ("subconstruction", "noncausative path"), ("rpCat", "PP"), ("endBounded", "true")] }

def gj2004_24b : Datum :=
  { id := "gj2004_24b"
    source := ⟨"goldberg-jackendoff-2004", "(24b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill pushed Harry off the sofa for hours."
    glossedTokens := []
    context := "Nonrepetitive reading."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "push"), ("subconstruction", "causative path"), ("rpCat", "PP"), ("endBounded", "true")] }

def gj2004_24c : Datum :=
  { id := "gj2004_24c"
    source := ⟨"goldberg-jackendoff-2004", "(24c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill floated down the river for hours."
    glossedTokens := []
    context := "Nonrepetitive reading."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "float"), ("subconstruction", "noncausative path"), ("rpCat", "PP"), ("endBounded", "false")] }

def gj2004_24d : Datum :=
  { id := "gj2004_24d"
    source := ⟨"goldberg-jackendoff-2004", "(24d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill pushed Harry along the trail for hours."
    glossedTokens := []
    context := "Nonrepetitive reading."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "push"), ("subconstruction", "causative path"), ("rpCat", "PP"), ("endBounded", "false")] }

def gj2004_45a : Datum :=
  { id := "gj2004_45a"
    source := ⟨"goldberg-jackendoff-2004", "(45a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She yelled hoarse."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "yell"), ("subconstruction", "noncausative property"), ("rpCat", "AP"), ("subjectRole", "agent")] }

def gj2004_45b : Datum :=
  { id := "gj2004_45b"
    source := ⟨"goldberg-jackendoff-2004", "(45b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ted cried to sleep."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "cry"), ("subconstruction", "noncausative property"), ("rpCat", "PP"), ("subjectRole", "agent")] }

def gj2004_45c : Datum :=
  { id := "gj2004_45c"
    source := ⟨"goldberg-jackendoff-2004", "(45c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The tiger bled to death."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "bleed"), ("subconstruction", "noncausative property"), ("rpCat", "PP"), ("subjectRole", "patient")] }

def gj2004_46a : Datum :=
  { id := "gj2004_46a"
    source := ⟨"goldberg-jackendoff-2004", "(46a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He coughed awake and we were all overjoyed, especially Sierra."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "cough"), ("subconstruction", "noncausative property"), ("rpCat", "AP"), ("subjectRole", "agent or patient")] }

def gj2004_47a : Datum :=
  { id := "gj2004_47a"
    source := ⟨"goldberg-jackendoff-2004", "(47a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Patamon coughed himself awake on the bank of the lake where he and Gomammon had their play."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "cough"), ("subconstruction", "causative property"), ("rpCat", "AP"), ("selection", "fake reflexive"), ("subjectRole", "agent or patient")] }

def gj2004_48a : Datum :=
  { id := "gj2004_48a"
    source := ⟨"goldberg-jackendoff-2004", "(48a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The worm wriggled onto the carpet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "wriggle"), ("subconstruction", "noncausative path"), ("rpCat", "PP"), ("subjectRole", "agent")] }

def gj2004_48b : Datum :=
  { id := "gj2004_48b"
    source := ⟨"goldberg-jackendoff-2004", "(48b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The chocolate melted onto the carpet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "melt"), ("subconstruction", "noncausative path"), ("rpCat", "PP"), ("subjectRole", "patient")] }

def gj2004_49a : Datum :=
  { id := "gj2004_49a"
    source := ⟨"goldberg-jackendoff-2004", "(49a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill wiggled himself loose."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "wiggle"), ("subconstruction", "causative path"), ("rpCat", "AP"), ("subjectRole", "agent")] }

def gj2004_49b : Datum :=
  { id := "gj2004_49b"
    source := ⟨"goldberg-jackendoff-2004", "(49b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Aliza wiggled her tooth loose."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "wiggle"), ("subconstruction", "causative path"), ("rpCat", "AP"), ("subjectRole", "agent")] }

def gj2004_49c : Datum :=
  { id := "gj2004_49c"
    source := ⟨"goldberg-jackendoff-2004", "(49c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The mechanical doll wiggled itself loose."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "wiggle"), ("subconstruction", "causative path"), ("rpCat", "AP"), ("subjectRole", "agent")] }

def gj2004_49e : Datum :=
  { id := "gj2004_49e"
    source := ⟨"goldberg-jackendoff-2004", "(49e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The ball wiggled itself loose."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "wiggle"), ("subconstruction", "causative path"), ("rpCat", "AP"), ("subjectRole", "patient")] }

def gj2004_wipe : Datum :=
  { id := "gj2004_wipe"
    source := ⟨"goldberg-jackendoff-2004", "§6.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She wiped the table clean."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "wipe"), ("subconstruction", "causative property"), ("rpCat", "AP"), ("selection", "selected"), ("objectRole", "patient")] }

def gj2004_97c : Datum :=
  { id := "gj2004_97c"
    source := ⟨"goldberg-jackendoff-2004", "(97c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The truck rumbled into the station."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "rumble"), ("subconstruction", "noncausative path"), ("rpCat", "PP"), ("subeventRelation", "result")] }

def all : List Datum := [gj2004_5a, gj2004_5b, gj2004_6a, gj2004_6b, gj2004_7a, gj2004_7b, gj2004_8a, gj2004_8b, gj2004_9a, gj2004_23a, gj2004_23b, gj2004_23c, gj2004_24a, gj2004_24b, gj2004_24c, gj2004_24d, gj2004_45a, gj2004_45b, gj2004_45c, gj2004_46a, gj2004_47a, gj2004_48a, gj2004_48b, gj2004_49a, gj2004_49b, gj2004_49c, gj2004_49e, gj2004_wipe, gj2004_97c]

/-- How the object of a transitive resultative is selected (§2). By §5 the fake reflexive is not grammatically special: another object is excluded because it is implausible to make someone else fall asleep by crying. -/
inductive ObjectSelection where
  /-- selected: the verb selects the object: *The gardener watered the flowers flat*, (7a) -/
  | selected
  /-- unselected: only the construction licenses the object: *They drank the pub dry*, (8a) -/
  | unselected
  /-- fake reflexive: an unselected reflexive that alternates with no other object, as in *We yelled ourselves hoarse*, (9a) -/
  | fakeReflexive
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `selection`. -/
def selection (e : Datum) : Option ObjectSelection :=
  e.parse? "selection" [("selected", .selected), ("unselected", .unselected), ("fake reflexive", .fakeReflexive)]

end GoldbergJackendoff2004.Examples
