module

public import Linglib.Data.Examples.Schema

/-!
# `Gunlogson2001` — typed example data

Auto-generated from `Linglib/Data/Examples/Gunlogson2001.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Gunlogson2001.Examples`.
-/

@[expose] public section

namespace Gunlogson2001.Examples

def ex_13 : Datum :=
  { id := "gunlogson2001_13"
    source := ⟨"gunlogson-2001", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "During the tax year, did you receive a distribution from a foreign trust?"
    glossedTokens := []
    context := "On a tax form."
    judgment := .acceptable
    contrasts := [("During the tax year, you received a distribution from a foreign trust?", .unacceptable), ("During the tax year, you received a distribution from a foreign trust.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "neutrality"), ("locutions", "interrogative;risingDeclarative;fallingDeclarative")] }

def ex_14 : Datum :=
  { id := "gunlogson2001_14"
    source := ⟨"gunlogson-2001", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Is it bigger than a breadbox?"
    glossedTokens := []
    context := "In a guessing game."
    judgment := .acceptable
    contrasts := [("It's bigger than a breadbox?", .unacceptable), ("It's bigger than a breadbox.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "neutrality"), ("locutions", "interrogative;risingDeclarative;fallingDeclarative")] }

def ex_16 : Datum :=
  { id := "gunlogson2001_16"
    source := ⟨"gunlogson-2001", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Did she lie to the grand jury?"
    glossedTokens := []
    context := "It's an open question."
    judgment := .acceptable
    contrasts := [("She lied to the grand jury?", .unacceptable), ("She lied to the grand jury.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "neutrality"), ("locutions", "interrogative;risingDeclarative;fallingDeclarative")] }

def ex_27 : Datum :=
  { id := "gunlogson2001_27"
    source := ⟨"gunlogson-2001", "(27)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Can you (please) pass the salt?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("You can (please) pass the salt?", .unacceptable), ("You can (please) pass the salt.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "neutrality"), ("locutions", "interrogative;risingDeclarative;fallingDeclarative")] }

def ex_31 : Datum :=
  { id := "gunlogson2001_31"
    source := ⟨"gunlogson-2001", "(31)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Am I from Skokie?"
    glossedTokens := []
    context := "Radio station DJ: Good morning Susan. Where are you calling from? The caller answers."
    judgment := .unacceptable
    contrasts := [("I'm from Skokie?", .acceptable), ("I'm from Skokie.", .acceptable)]
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "informativeRising"), ("locutions", "interrogative;risingDeclarative;fallingDeclarative")] }

def ex_33 : Datum :=
  { id := "gunlogson2001_33"
    source := ⟨"gunlogson-2001", "(33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Has the manager of course been informed?"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := [("The manager has of course been informed?", .acceptable), ("The manager has of course been informed.", .acceptable)]
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "biasMarker"), ("locutions", "interrogative;risingDeclarative;fallingDeclarative")] }

def ex_44 : Datum :=
  { id := "gunlogson2001_44"
    source := ⟨"gunlogson-2001", "(44)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Has it? I don't see much evidence of that."
    glossedTokens := []
    context := "A and B are looking at a co-worker's much-dented car. A: His driving has gotten a lot better. B responds."
    judgment := .acceptable
    contrasts := [("It has? I don't see much evidence of that.", .acceptable), ("It has. I don't see much evidence of that.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "2.3"), ("phenomenon", "speakerCommitment"), ("locutions", "interrogative;risingDeclarative;fallingDeclarative")] }

def ex_45 : Datum :=
  { id := "gunlogson2001_45"
    source := ⟨"gunlogson-2001", "(45)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Is it? Thanks, I'll use a different one."
    glossedTokens := []
    context := "A: That copier is broken. B responds."
    judgment := .acceptable
    contrasts := [("It is? Thanks, I'll use a different one.", .acceptable), ("(Oh), it is. Thanks, I'll use a different one.", .acceptable)]
    readings := []
    paperFeatures := [("section", "2.3"), ("phenomenon", "speakerCommitment"), ("locutions", "interrogative;risingDeclarative;fallingDeclarative")] }

def ex_46 : Datum :=
  { id := "gunlogson2001_46"
    source := ⟨"gunlogson-2001", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Is Jake here? Then let's get started."
    glossedTokens := []
    context := "A: Jake's here. B responds."
    judgment := .acceptable
    contrasts := [("Jake's here? Then let's get started.", .acceptable), ("(Oh), Jake's here. Then let's get started.", .acceptable)]
    readings := []
    paperFeatures := [("section", "2.3"), ("phenomenon", "speakerCommitment"), ("locutions", "interrogative;risingDeclarative;fallingDeclarative")] }

def ex_47 : Datum :=
  { id := "gunlogson2001_47"
    source := ⟨"gunlogson-2001", "(47)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Is France a monarchy?"
    glossedTokens := []
    context := "A: The king of France is bald. B responds."
    judgment := .acceptable
    contrasts := [("France is a monarchy?", .acceptable), ("France is a monarchy.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "2.3"), ("phenomenon", "speakerCommitment"), ("locutions", "interrogative;risingDeclarative;fallingDeclarative")] }

def ex_48 : Datum :=
  { id := "gunlogson2001_48"
    source := ⟨"gunlogson-2001", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Is shoplifting fun?"
    glossedTokens := []
    context := "Uttered to insinuate that the addressee has shoplifted."
    judgment := .acceptable
    contrasts := [("Shoplifting's fun?", .acceptable), ("Shoplifting's fun.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "2.3"), ("phenomenon", "speakerCommitment"), ("locutions", "interrogative;risingDeclarative;fallingDeclarative")] }

def ex_100 : Datum :=
  { id := "gunlogson2001_100"
    source := ⟨"gunlogson-2001", "(100)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: That was a kingfisher. B: Are you sure? It looked like a seagull to me. A: I'm positive. It was a kingfisher."
    glossedTokens := []
    context := "A is watching a bird fly away; neither A nor B has a prior commitment about its identity."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.5"), ("phenomenon", "entailedButInformative")] }

def ex_102 : Datum :=
  { id := "gunlogson2001_102"
    source := ⟨"gunlogson-2001", "(102)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Are we out of beer?"
    glossedTokens := []
    context := "A: I've just searched the refrigerator and there's absolutely nothing cold to drink. B responds."
    judgment := .acceptable
    contrasts := [("We're out of beer?", .acceptable), ("(So) we're out of beer.", .acceptable)]
    readings := []
    paperFeatures := [("section", "3.5"), ("phenomenon", "vacuousness"), ("locutions", "interrogative;risingDeclarative;fallingDeclarative")] }

def ex_103 : Datum :=
  { id := "gunlogson2001_103"
    source := ⟨"gunlogson-2001", "(103)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Are we out of beer?"
    glossedTokens := []
    context := "B: I've just searched the refrigerator and there's absolutely nothing cold to drink. A: Yeah, I know. We're out of just about everything. B responds."
    judgment := .unacceptable
    contrasts := [("We're out of beer?", .unacceptable), ("(So) we're out of beer.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "3.5"), ("phenomenon", "vacuousness"), ("locutions", "interrogative;risingDeclarative;fallingDeclarative")] }

def ex_118 : Datum :=
  { id := "gunlogson2001_118"
    source := ⟨"gunlogson-2001", "(118)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Is Maria married?"
    glossedTokens := []
    context := "A: Maria's husband was at the party. B responds."
    judgment := .acceptable
    contrasts := [("Maria's married?", .acceptable), ("Maria's married.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.3"), ("phenomenon", "fallingDeclarativeQuestion"), ("locutions", "interrogative;risingDeclarative;fallingDeclarative")] }

def ex_128 : Datum :=
  { id := "gunlogson2001_128"
    source := ⟨"gunlogson-2001", "(128)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Is it raining?"
    glossedTokens := []
    context := "Robin is sitting, as before, in a windowless computer room when another person enters. The newcomer is wearing a wet raincoat and boots. Robin says:"
    judgment := .acceptable
    contrasts := [("It's raining?", .acceptable), ("(I see that/So) It's raining.", .acceptable)]
    readings := []
    paperFeatures := [("section", "4.3"), ("phenomenon", "fallingDeclarativeQuestion"), ("locutions", "interrogative;risingDeclarative;fallingDeclarative")] }

def all : List Datum := [ex_13, ex_14, ex_16, ex_27, ex_31, ex_33, ex_44, ex_45, ex_46, ex_47, ex_48, ex_100, ex_102, ex_103, ex_118, ex_128]

end Gunlogson2001.Examples
