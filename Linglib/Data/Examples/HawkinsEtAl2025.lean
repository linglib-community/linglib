module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `HawkinsEtAl2025` — typed example data

Auto-generated from `Linglib/Data/Examples/HawkinsEtAl2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HawkinsEtAl2025.Examples`.
-/

@[expose] public section

namespace HawkinsEtAl2025.Examples

def ex1 : Datum :=
  { id := "hawkinsetal2025_ex1"
    source := ⟨"hawkins-etal-2025", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Quinn: Do you take Visa or Mastercard? Rickie: Yes, we take Visa. Quinn: Yeah, sure I already knew that!"
    glossedTokens := []
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2a"), ("mentioned", "visa")] }

def ex2 : Datum :=
  { id := "hawkinsetal2025_ex2"
    source := ⟨"hawkins-etal-2025", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Quinn: Do you take Visa or Mastercard? Rickie: No, but we take American Express. Quinn: Yeah, sure I already knew that!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2a"), ("mentioned", "american express")] }

def ex3 : Datum :=
  { id := "hawkinsetal2025_ex3"
    source := ⟨"hawkins-etal-2025", "(3)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Quinn: Do you accept American Express? Rickie: Yes, we accept American Express and … [exhaustive list]."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3a"), ("question", "specific"), ("target", "available")] }

def ex4 : Datum :=
  { id := "hawkinsetal2025_ex4"
    source := ⟨"hawkins-etal-2025", "(4)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Quinn: Do you accept American Express? Rickie: No, we accept … [exhaustive list]."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3a"), ("question", "specific"), ("target", "unavailable")] }

def ex5 : Datum :=
  { id := "hawkinsetal2025_ex5"
    source := ⟨"hawkins-etal-2025", "(5)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Quinn: Do you accept credit cards? Rickie: Yes, we accept … [exhaustive list]."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3a"), ("question", "general")] }

def ex6 : Datum :=
  { id := "hawkinsetal2025_ex6"
    source := ⟨"hawkins-etal-2025", "(6)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "You are a bartender in a hotel bar. The bar serves only soda, iced coffee and Chardonnay. A woman walks in. She says: Do you have iced tea?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3b"), ("competitor", "iced coffee"), ("sameCategory", "soda"), ("otherCategory", "Chardonnay")] }

def ex7 : Datum :=
  { id := "hawkinsetal2025_ex7"
    source := ⟨"hawkins-etal-2025", "(7)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Context 1 (sleepover): Your friend is having a sleepover with some friends on the weekend. They are preparing everything for the guests since they don't host many guests very often. You have the following items at home that you could spare for some time: some bubble wrap, a pillow, a sleeping bag and a carpet. Your friend asks: Do you have a blanket?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3c"), ("competitor", "sleeping bag"), ("mostSimilar", "pillow"), ("otherCategory", "carpet")] }

def ex8 : Datum :=
  { id := "hawkinsetal2025_ex8"
    source := ⟨"hawkins-etal-2025", "(8)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Context 2 (transportation): Your roommate is moving to another apartment and is packing her things. She has a large mirror that she needs to pack for transportation. You have the following items at home that you could spare for some time: some bubble wrap, a pillow, a sleeping bag and a carpet. She asks: Do you have a blanket?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3c"), ("competitor", "bubble wrap"), ("mostSimilar", "pillow"), ("otherCategory", "carpet")] }

def icedtea : Datum :=
  { id := "hawkinsetal2025_icedtea"
    source := ⟨"hawkins-etal-2025", "§1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Customer: Do you have iced tea? Barista: No, I'm afraid we're out of iced tea but we do have iced coffee."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1")] }

def bbq : Datum :=
  { id := "hawkinsetal2025_bbq"
    source := ⟨"hawkins-etal-2025", "§4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Q: Will we have BBQ in the park? A: Chances of rain are 90%."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4")] }

def all : List Datum := [ex1, ex2, ex3, ex4, ex5, ex6, ex7, ex8, icedtea, bbq]

/-- The card a response mentions beyond its polar answer. -/
inductive Card where
  /-- visa: Visa -/
  | visa
  /-- mastercard: Mastercard -/
  | mastercard
  /-- american express: American Express -/
  | americanExpress
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `mentioned`. -/
def mentioned (e : Datum) : Option Card :=
  e.parse? "mentioned" [("visa", .visa), ("mastercard", .mastercard), ("american express", .americanExpress)]

/-- The questions of case study 1. -/
inductive Question where
  /-- specific: a polar question about one option -/
  | specific
  /-- general: a polar question about the category -/
  | general
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `question`. -/
def question (e : Datum) : Option Question :=
  e.parse? "question" [("specific", .specific), ("general", .general)]

/-- Whether the option asked about is available. -/
inductive Target where
  /-- available: the option asked about is available -/
  | available
  /-- unavailable: the option asked about is not available -/
  | unavailable
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `target`. -/
def target (e : Datum) : Option Target :=
  e.parse? "target" [("available", .available), ("unavailable", .unavailable)]

end HawkinsEtAl2025.Examples
