module

public import Linglib.Data.Examples.Schema

/-!
# `Heim1982` — typed example data

Auto-generated from `Linglib/Data/Examples/Heim1982.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Heim1982.Examples`.
-/

@[expose] public section

namespace Heim1982.Examples

def indefinite_persists : Datum :=
  { id := "heim1982_indefinite_persists"
    source := ⟨"heim-1982", "Ch. I §1 (9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A dog came in. It lay down under the table."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("antecedent_type", "indefinite"), ("context", "none")] }

def universal_blocks : Datum :=
  { id := "heim1982_universal_blocks"
    source := ⟨"heim-1982", "Ch. I §1 (16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every dog came in. It lay down under the table."
    glossedTokens := []
    context := "No referent for 'it' fixed independently of the preceding sentence."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("antecedent_type", "universal"), ("context", "none"), ("felicity", "infelicitous")] }

def negative_blocks : Datum :=
  { id := "heim1982_negative_blocks"
    source := ⟨"heim-1982", "Ch. I §1 (17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No dog came in. It lay down under the table."
    glossedTokens := []
    context := "No referent for 'it' fixed independently of the preceding sentence."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("antecedent_type", "negative_quant"), ("context", "none"), ("felicity", "infelicitous")] }

def definite_reference : Datum :=
  { id := "heim1982_definite_reference"
    source := ⟨"heim-1982", "Ch. III §5.1 (2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is a cat behind you. The cat is hungry."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("antecedent_type", "indefinite"), ("context", "none")] }

def conditional_donkey : Datum :=
  { id := "heim1982_conditional_donkey"
    source := ⟨"heim-1982", "Ch. I §2 (2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If a man owns a donkey, he beats it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("donkey_configuration", "conditional")] }

def relative_donkey : Datum :=
  { id := "heim1982_relative_donkey"
    source := ⟨"heim-1982", "Ch. I §2 (3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every man who owns a donkey beats it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("donkey_configuration", "relative_clause")] }

def soldier_gun : Datum :=
  { id := "heim1982_soldier_gun"
    source := ⟨"heim-1982", "Ch. II §5.2 (6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every soldier has a gun. He will shoot."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Someone has a gun. He will shoot.", .acceptable)]
    readings := []
    paperFeatures := [("antecedent_type", "universal"), ("context", "none"), ("felicity", "infelicitous")] }

def cat_door : Datum :=
  { id := "heim1982_cat_door"
    source := ⟨"heim-1982", "Ch. II §3.3 (3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A cat was at the door. It wanted to be fed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("antecedent_type", "indefinite"), ("context", "none")] }

def woman_dog : Datum :=
  { id := "heim1982_woman_dog"
    source := ⟨"heim-1982", "Ch. III §2.4 (5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A woman was bitten by a dog. She hit him."
    glossedTokens := []
    context := "Uttered against a file in whose domain neither 1 nor 2 occurs."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("antecedent_type", "indefinite"), ("context", "none")] }

def woman_dog_definite : Datum :=
  { id := "heim1982_woman_dog_definite"
    source := ⟨"heim-1982", "Ch. III §3.2 (4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She is a woman. He is a dog. She was bitten by him."
    glossedTokens := []
    context := "Uttered against a true file in whose domain both 1 and 2 occur."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("antecedent_type", "definite"), ("context", "none")] }

def pretzel : Datum :=
  { id := "heim1982_pretzel"
    source := ⟨"heim-1982", "Ch. III §4.1 (2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone bought a pretzel and ate it."
    glossedTokens := []
    context := "Uttered when an empty file obtains."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("antecedent_type", "indefinite"), ("context", "nuclear_scope")] }

def flea_collar : Datum :=
  { id := "heim1982_flea_collar"
    source := ⟨"heim-1982", "Ch. III §4.3 (7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If a cat is well cared for, it always has a flea collar."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("antecedent_type", "indefinite"), ("context", "nuclear_scope")] }

def dog_bite : Datum :=
  { id := "heim1982_dog_bite"
    source := ⟨"heim-1982", "Ch. III §5.2 (3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Watch out, the dog will bite you."
    glossedTokens := []
    context := "Said to the addressee walking up a driveway: no previous discourse, no dog in sight, no reason to believe a dog lives there."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("antecedent_type", "definite"), ("context", "accommodation")] }

def king_of_france : Datum :=
  { id := "heim1982_king_of_france"
    source := ⟨"heim-1982", "Ch. III §5.2 (10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary didn't have lunch with the king of France (because France doesn't have a king)."
    glossedTokens := []
    context := "The because-clause denies that France has a king."
    judgment := .acceptable
    contrasts := []
    readings := [("narrow scope (local accommodation)", .acceptable), ("existence implied (global accommodation)", .acceptable)]
    paperFeatures := [("antecedent_type", "definite"), ("context", "negation")] }

def all : List Datum := [indefinite_persists, universal_blocks, negative_blocks, definite_reference, conditional_donkey, relative_donkey, soldier_gun, cat_door, woman_dog, woman_dog_definite, pretzel, flea_collar, dog_bite, king_of_france]

end Heim1982.Examples
