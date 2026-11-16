module

public import Linglib.Data.Examples.Schema

/-!
# `Condoravdi2002` — typed example data

Auto-generated from `Linglib/Data/Examples/Condoravdi2002.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Condoravdi2002.Examples`.
-/

@[expose] public section

namespace Condoravdi2002.Examples

def ex1a_tomorrow : Datum :=
  { id := "condoravdi2002_ex1a_tomorrow"
    source := ⟨"condoravdi-2002", "[1a]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He might get sick tomorrow."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "adverb"), ("scope", "modal"), ("sort", "eventive"), ("adverb", "future")] }

def ex1a_now : Datum :=
  { id := "condoravdi2002_ex1a_now"
    source := ⟨"condoravdi-2002", "[1a]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He might get sick now."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "adverb"), ("scope", "modal"), ("sort", "eventive"), ("adverb", "present")] }

def ex1a_yesterday : Datum :=
  { id := "condoravdi2002_ex1a_yesterday"
    source := ⟨"condoravdi-2002", "[1a]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He might get sick yesterday."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "adverb"), ("scope", "modal"), ("sort", "eventive"), ("adverb", "past")] }

def ex1b_now : Datum :=
  { id := "condoravdi2002_ex1b_now"
    source := ⟨"condoravdi-2002", "[1b]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He might be getting sick now."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "adverb"), ("scope", "modal"), ("sort", "stative"), ("adverb", "present")] }

def ex1b_yesterday : Datum :=
  { id := "condoravdi2002_ex1b_yesterday"
    source := ⟨"condoravdi-2002", "[1b]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He might be getting sick yesterday."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "adverb"), ("scope", "modal"), ("sort", "stative"), ("adverb", "past")] }

def ex1c_now : Datum :=
  { id := "condoravdi2002_ex1c_now"
    source := ⟨"condoravdi-2002", "[1c]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He might be sick now."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "adverb"), ("scope", "modal"), ("sort", "stative"), ("adverb", "present")] }

def ex1c_tomorrow : Datum :=
  { id := "condoravdi2002_ex1c_tomorrow"
    source := ⟨"condoravdi-2002", "[1c]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He might be sick tomorrow."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "adverb"), ("scope", "modal"), ("sort", "stative"), ("adverb", "future")] }

def ex1c_yesterday : Datum :=
  { id := "condoravdi2002_ex1c_yesterday"
    source := ⟨"condoravdi-2002", "[1c]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He might be sick yesterday."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "adverb"), ("scope", "modal"), ("sort", "stative"), ("adverb", "past")] }

def ex2a_yesterday : Datum :=
  { id := "condoravdi2002_ex2a_yesterday"
    source := ⟨"condoravdi-2002", "[2a]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He must have gotten sick yesterday."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "adverb"), ("scope", "modalPerf"), ("sort", "eventive"), ("adverb", "past")] }

def ex2a_tomorrow : Datum :=
  { id := "condoravdi2002_ex2a_tomorrow"
    source := ⟨"condoravdi-2002", "[2a]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He must have gotten sick tomorrow."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "adverb"), ("scope", "modalPerf"), ("sort", "eventive"), ("adverb", "future")] }

def ex2b_yesterday : Datum :=
  { id := "condoravdi2002_ex2b_yesterday"
    source := ⟨"condoravdi-2002", "[2b]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He must have been sick yesterday."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "adverb"), ("scope", "modalPerf"), ("sort", "stative"), ("adverb", "past")] }

def ex2b_tomorrow : Datum :=
  { id := "condoravdi2002_ex2b_tomorrow"
    source := ⟨"condoravdi-2002", "[2b]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He must have been sick tomorrow."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "adverb"), ("scope", "modalPerf"), ("sort", "stative"), ("adverb", "future")] }

def ex29a : Datum :=
  { id := "condoravdi2002_ex29a"
    source := ⟨"condoravdi-2002", "[29a]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He may have won yesterday."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "adverb"), ("scope", "modalPerf"), ("sort", "eventive"), ("adverb", "past")] }

def ex29b : Datum :=
  { id := "condoravdi2002_ex29b"
    source := ⟨"condoravdi-2002", "[29b]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He may win yesterday."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "adverb"), ("scope", "modal"), ("sort", "eventive"), ("adverb", "past")] }

def ex34a_yesterday : Datum :=
  { id := "condoravdi2002_ex34a_yesterday"
    source := ⟨"condoravdi-2002", "[34a]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He might have been available yesterday."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "adverb"), ("scope", "perfModal"), ("sort", "stative"), ("adverb", "past")] }

def ex34a_nextMonth : Datum :=
  { id := "condoravdi2002_ex34a_nextMonth"
    source := ⟨"condoravdi-2002", "[34a]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He might have been available next month."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "adverb"), ("scope", "perfModal"), ("sort", "stative"), ("adverb", "future")] }

def ex34b_yesterday : Datum :=
  { id := "condoravdi2002_ex34b_yesterday"
    source := ⟨"condoravdi-2002", "[34b]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It might have been raining yesterday."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "adverb"), ("scope", "perfModal"), ("sort", "stative"), ("adverb", "past")] }

def ex34b_now : Datum :=
  { id := "condoravdi2002_ex34b_now"
    source := ⟨"condoravdi-2002", "[34b]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It might have been raining now."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "adverb"), ("scope", "perfModal"), ("sort", "stative"), ("adverb", "present")] }

def ex35a_yesterday : Datum :=
  { id := "condoravdi2002_ex35a_yesterday"
    source := ⟨"condoravdi-2002", "[35a]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He must have been available yesterday."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "adverb"), ("scope", "modalPerf"), ("sort", "stative"), ("adverb", "past")] }

def ex35a_nextMonth : Datum :=
  { id := "condoravdi2002_ex35a_nextMonth"
    source := ⟨"condoravdi-2002", "[35a]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He must have been available next month."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "adverb"), ("scope", "modalPerf"), ("sort", "stative"), ("adverb", "future")] }

def ex35b_yesterday : Datum :=
  { id := "condoravdi2002_ex35b_yesterday"
    source := ⟨"condoravdi-2002", "[35b]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It must have been raining yesterday."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "adverb"), ("scope", "modalPerf"), ("sort", "stative"), ("adverb", "past")] }

def ex35b_now : Datum :=
  { id := "condoravdi2002_ex35b_now"
    source := ⟨"condoravdi-2002", "[35b]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It must have been raining now."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "adverb"), ("scope", "modalPerf"), ("sort", "stative"), ("adverb", "present")] }

def ex6a : Datum :=
  { id := "condoravdi2002_ex6a"
    source := ⟨"condoravdi-2002", "[6a]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He may/might win the game."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "reading"), ("scope", "modal"), ("sort", "eventive"), ("reference", "future"), ("context", "none"), ("metaphysical", "available")] }

def ex7a : Datum :=
  { id := "condoravdi2002_ex7a"
    source := ⟨"condoravdi-2002", "[7a]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He may/might have (already) won the game (# but he didn't)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "reading"), ("scope", "modalPerf"), ("sort", "eventive"), ("reference", "past"), ("context", "none"), ("metaphysical", "unavailable")] }

def ex7b : Datum :=
  { id := "condoravdi2002_ex7b"
    source := ⟨"condoravdi-2002", "[7b]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "At that point he might (still) have won the game but he didn't in the end."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "reading"), ("scope", "perfModal"), ("sort", "eventive"), ("reference", "future"), ("context", "none"), ("metaphysical", "available")] }

def ex41a : Datum :=
  { id := "condoravdi2002_ex41a"
    source := ⟨"condoravdi-2002", "[41a]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He may/might have the flu (now)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "reading"), ("scope", "modal"), ("sort", "stative"), ("reference", "present"), ("context", "none"), ("metaphysical", "unavailable")] }

def ex41b : Datum :=
  { id := "condoravdi2002_ex41b"
    source := ⟨"condoravdi-2002", "[41b]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He may/might get the flu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "reading"), ("scope", "modal"), ("sort", "eventive"), ("reference", "future"), ("context", "none"), ("metaphysical", "available")] }

def ex42b : Datum :=
  { id := "condoravdi2002_ex42b"
    source := ⟨"condoravdi-2002", "[42b]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It hasn't been decided yet who he will meet with. He may see the dean. He may see the provost."
    glossedTokens := []
    context := "He will meet with one senior administrator."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "reading"), ("scope", "modal"), ("sort", "eventive"), ("reference", "future"), ("context", "open"), ("metaphysical", "available")] }

def ex42c : Datum :=
  { id := "condoravdi2002_ex42c"
    source := ⟨"condoravdi-2002", "[42c]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It has been decided who he will meet with but I don't know who it is. He may see the dean. He may see the provost."
    glossedTokens := []
    context := "He will meet with one senior administrator."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "reading"), ("scope", "modal"), ("sort", "eventive"), ("reference", "future"), ("context", "settled"), ("metaphysical", "unavailable")] }

def ex14a : Datum :=
  { id := "condoravdi2002_ex14a"
    source := ⟨"condoravdi-2002", "[14a]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He already returned."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "sortal"), ("adverb", "already"), ("complement", "eventive")] }

def ex14b : Datum :=
  { id := "condoravdi2002_ex14b"
    source := ⟨"condoravdi-2002", "[14b]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He did not write us yet."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "sortal"), ("adverb", "yet"), ("complement", "eventive")] }

def ex14c : Datum :=
  { id := "condoravdi2002_ex14c"
    source := ⟨"condoravdi-2002", "[14c]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He has already returned."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "sortal"), ("adverb", "already"), ("complement", "perfect")] }

def ex14d : Datum :=
  { id := "condoravdi2002_ex14d"
    source := ⟨"condoravdi-2002", "[14d]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He has not written us yet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "sortal"), ("adverb", "yet"), ("complement", "perfect")] }

def ex15a : Datum :=
  { id := "condoravdi2002_ex15a"
    source := ⟨"condoravdi-2002", "[15a]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He might have already returned."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "sortal"), ("adverb", "already"), ("complement", "perfect")] }

def ex15b : Datum :=
  { id := "condoravdi2002_ex15b"
    source := ⟨"condoravdi-2002", "[15b]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He might not have written us yet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "sortal"), ("adverb", "yet"), ("complement", "perfect")] }

def ex15c : Datum :=
  { id := "condoravdi2002_ex15c"
    source := ⟨"condoravdi-2002", "[15c]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He might already return."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "sortal"), ("adverb", "already"), ("complement", "eventive")] }

def ex15d : Datum :=
  { id := "condoravdi2002_ex15d"
    source := ⟨"condoravdi-2002", "[15d]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He might not write us yet."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "sortal"), ("adverb", "yet"), ("complement", "eventive")] }

def ex36a : Datum :=
  { id := "condoravdi2002_ex36a"
    source := ⟨"condoravdi-2002", "[36a]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He might still win."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "phase"), ("adverb", "still"), ("scope", "modal")] }

def ex37a : Datum :=
  { id := "condoravdi2002_ex37a"
    source := ⟨"condoravdi-2002", "[37a]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "At that point he might still have won."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "phase"), ("adverb", "still"), ("scope", "perfModal")] }

def ex40a : Datum :=
  { id := "condoravdi2002_ex40a"
    source := ⟨"condoravdi-2002", "[40a]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He may still win."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "phase"), ("adverb", "still"), ("scope", "modal")] }

def ex40b : Datum :=
  { id := "condoravdi2002_ex40b"
    source := ⟨"condoravdi-2002", "[40b]"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He may already win."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "phase"), ("adverb", "already"), ("scope", "modal")] }

def ex38a : Datum :=
  { id := "condoravdi2002_ex38a"
    source := ⟨"condoravdi-2002", "[38a]"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Er könnte (schon) gewonnen haben."
    glossedTokens := [("Er", "he"), ("könnte", "could"), ("(schon)", "already"), ("gewonnen", "won"), ("haben", "have")]
    glossedWords := [⟨[['E', 'r']], [['h', 'e']]⟩, ⟨[['k', 'ö', 'n', 'n', 't', 'e']], [['c', 'o', 'u', 'l', 'd']]⟩, ⟨[['s', 'c', 'h', 'o', 'n']], [['a', 'l', 'r', 'e', 'a', 'd', 'y']]⟩, ⟨[['g', 'e', 'w', 'o', 'n', 'n', 'e', 'n']], [['w', 'o', 'n']]⟩, ⟨[['h', 'a', 'b', 'e', 'n']], [['h', 'a', 'v', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "german"), ("order", "modalHave"), ("adverb", "schon")] }

def ex38b : Datum :=
  { id := "condoravdi2002_ex38b"
    source := ⟨"condoravdi-2002", "[38b]"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Er hätte schon gewinnen können."
    glossedTokens := [("Er", "he"), ("hätte", "had"), ("schon", "already"), ("gewinnen", "won"), ("können", "could")]
    glossedWords := [⟨[['E', 'r']], [['h', 'e']]⟩, ⟨[['h', 'ä', 't', 't', 'e']], [['h', 'a', 'd']]⟩, ⟨[['s', 'c', 'h', 'o', 'n']], [['a', 'l', 'r', 'e', 'a', 'd', 'y']]⟩, ⟨[['g', 'e', 'w', 'i', 'n', 'n', 'e', 'n']], [['w', 'o', 'n']]⟩, ⟨[['k', 'ö', 'n', 'n', 'e', 'n']], [['c', 'o', 'u', 'l', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "german"), ("order", "hadModal"), ("adverb", "schon")] }

def ex38c : Datum :=
  { id := "condoravdi2002_ex38c"
    source := ⟨"condoravdi-2002", "[38c]"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Er hätte (noch) gewinnen können."
    glossedTokens := [("Er", "he"), ("hätte", "had"), ("(noch)", "still"), ("gewinnen", "won"), ("können", "could")]
    glossedWords := [⟨[['E', 'r']], [['h', 'e']]⟩, ⟨[['h', 'ä', 't', 't', 'e']], [['h', 'a', 'd']]⟩, ⟨[['n', 'o', 'c', 'h']], [['s', 't', 'i', 'l', 'l']]⟩, ⟨[['g', 'e', 'w', 'i', 'n', 'n', 'e', 'n']], [['w', 'o', 'n']]⟩, ⟨[['k', 'ö', 'n', 'n', 'e', 'n']], [['c', 'o', 'u', 'l', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "german"), ("order", "hadModal"), ("adverb", "noch")] }

def ex38d : Datum :=
  { id := "condoravdi2002_ex38d"
    source := ⟨"condoravdi-2002", "[38d]"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Er könnte noch gewonnen haben."
    glossedTokens := [("Er", "he"), ("könnte", "could"), ("noch", "still"), ("gewonnen", "won"), ("haben", "have")]
    glossedWords := [⟨[['E', 'r']], [['h', 'e']]⟩, ⟨[['k', 'ö', 'n', 'n', 't', 'e']], [['c', 'o', 'u', 'l', 'd']]⟩, ⟨[['n', 'o', 'c', 'h']], [['s', 't', 'i', 'l', 'l']]⟩, ⟨[['g', 'e', 'w', 'o', 'n', 'n', 'e', 'n']], [['w', 'o', 'n']]⟩, ⟨[['h', 'a', 'b', 'e', 'n']], [['h', 'a', 'v', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "german"), ("order", "modalHave"), ("adverb", "noch")] }

def all : List Datum := [ex1a_tomorrow, ex1a_now, ex1a_yesterday, ex1b_now, ex1b_yesterday, ex1c_now, ex1c_tomorrow, ex1c_yesterday, ex2a_yesterday, ex2a_tomorrow, ex2b_yesterday, ex2b_tomorrow, ex29a, ex29b, ex34a_yesterday, ex34a_nextMonth, ex34b_yesterday, ex34b_now, ex35a_yesterday, ex35a_nextMonth, ex35b_yesterday, ex35b_now, ex6a, ex7a, ex7b, ex41a, ex41b, ex42b, ex42c, ex14a, ex14b, ex14c, ex14d, ex15a, ex15b, ex15c, ex15d, ex36a, ex37a, ex40a, ex40b, ex38a, ex38b, ex38c, ex38d]

end Condoravdi2002.Examples
