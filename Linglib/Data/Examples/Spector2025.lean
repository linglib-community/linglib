module

public import Linglib.Data.Examples.Schema

/-!
# `Spector2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Spector2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Spector2025.Examples`.
-/

@[expose] public section

namespace Spector2025.Examples

def ex_11a : Datum :=
  { id := "spector2025_11a"
    source := ⟨"spector-2025", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "(Something surprising happened.) Some of the marbles sank!"
    glossedTokens := []
    context := "Gloria is a scientist. She's investigating a new substance, whose density she does not know. She will perform an experiment by throwing ten marbles, believed to have the same density, into the substance. She of course expects the marbles to behave uniformly, i.e. that they will all float or all sink. She's also interested in how the marbles might collide with each other. She will report to her friend Alfred, who knows all of this but does not witness the experiment. To her surprise, the marbles did not behave uniformly; some sank and others floated. She hasn't reported this to Alfred yet. Then Alfred asks her: 'So what happened?'"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("message", "some")] }

def ex_11b : Datum :=
  { id := "spector2025_11b"
    source := ⟨"spector-2025", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "(Something surprising happened.) Some but not all of the marbles sank."
    glossedTokens := []
    context := "Gloria is a scientist. She's investigating a new substance, whose density she does not know. She will perform an experiment by throwing ten marbles, believed to have the same density, into the substance. She of course expects the marbles to behave uniformly, i.e. that they will all float or all sink. She's also interested in how the marbles might collide with each other. She will report to her friend Alfred, who knows all of this but does not witness the experiment. To her surprise, the marbles did not behave uniformly; some sank and others floated. She hasn't reported this to Alfred yet. Then Alfred asks her: 'So what happened?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("message", "some but not all")] }

def ex_14a : Datum :=
  { id := "spector2025_14a"
    source := ⟨"spector-2025", "(14a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You know what, Gloria saw some Hitchcock movies."
    glossedTokens := []
    context := "To get admission to this group of Hitchcock movie fans, one has to prove that they have watched at least one Hitchcock movie. Sue, Peter and Gloria all belong to the club, and know this. Sue talks with Gloria, and then tells Peter:"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("message", "some")] }

def ex_14b : Datum :=
  { id := "spector2025_14b"
    source := ⟨"spector-2025", "(14b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You know what, Gloria did not see all Hitchcock movies."
    glossedTokens := []
    context := "To get admission to this group of Hitchcock movie fans, one has to prove that they have watched at least one Hitchcock movie. Sue, Peter and Gloria all belong to the club, and know this. Sue talks with Gloria, and then tells Peter:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("message", "not all")] }

def ex_15a : Datum :=
  { id := "spector2025_15a"
    source := ⟨"spector-2025", "(15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some talks were in English."
    glossedTokens := []
    context := "At an international conference, one expects talks to be in English. Gloria reports:"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("message", "some")] }

def ex_15c : Datum :=
  { id := "spector2025_15c"
    source := ⟨"spector-2025", "(15c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not all talks were in English."
    glossedTokens := []
    context := "At an international conference, one expects talks to be in English. Gloria reports:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("message", "not all")] }

def ex_19b : Datum :=
  { id := "spector2025_19b"
    source := ⟨"spector-2025", "(19b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The blue marble sank."
    glossedTokens := []
    context := "Gloria is experimenting with just two marbles, a blue one and a red one. She throws them both into an unknown substance, and it is expected that they will either both sink or both float. She then reports the results of this experiment to her friend Alfred: Alfred: What happened?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex_11a, ex_11b, ex_14a, ex_14b, ex_15a, ex_15c, ex_19b]

end Spector2025.Examples
