module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Simik2024` — typed example data

Auto-generated from `Linglib/Data/Examples/Simik2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Simik2024.Examples`.
-/

@[expose] public section

namespace Simik2024.Examples

def ex11a : Datum :=
  { id := "simik2024_ex11a"
    source := ⟨"simik-2024", "ex. 11a"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Uklidil Marek třetí patro?"
    glossedTokens := [("Uklidil", "cleaned"), ("Marek", "Marek"), ("třetí", "third"), ("patro", "floor")]
    glossedWords := [⟨['U', 'k', 'l', 'i', 'd', 'i', 'l'], ['c', 'l', 'e', 'a', 'n', 'e', 'd'], [⟨['U', 'k', 'l', 'i', 'd', 'i', 'l'], ['c', 'l', 'e', 'a', 'n', 'e', 'd'], none⟩]⟩, ⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], [⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], none⟩]⟩, ⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], [⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], none⟩]⟩, ⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], [⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "On a busy day, two hotel cleaning service coordinators (A and B), sitting in their office, are taking note of the progress made thus far. A is about to make a tick for the whole third floor, which Marek was responsible for. B is informed about the progress. A asks:"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "11"), ("strategy", "verbMovement"), ("polarity", "positive")] }

def ex11b : Datum :=
  { id := "simik2024_ex11b"
    source := ⟨"simik-2024", "ex. 11b"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Neuklidil Marek třetí patro?"
    glossedTokens := [("Neuklidil", "NEG.cleaned"), ("Marek", "Marek"), ("třetí", "third"), ("patro", "floor")]
    glossedWords := [⟨['N', 'e', 'u', 'k', 'l', 'i', 'd', 'i', 'l'], ['N', 'E', 'G', '.', 'c', 'l', 'e', 'a', 'n', 'e', 'd'], [⟨['N', 'e', 'u', 'k', 'l', 'i', 'd', 'i', 'l'], ['N', 'E', 'G', '.', 'c', 'l', 'e', 'a', 'n', 'e', 'd'], none⟩]⟩, ⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], [⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], none⟩]⟩, ⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], [⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], none⟩]⟩, ⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], [⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "On a busy day, two hotel cleaning service coordinators (A and B), sitting in their office, are taking note of the progress made thus far. A is about to make a tick for the whole third floor, which Marek was responsible for. B is informed about the progress. A asks:"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "11"), ("strategy", "verbMovement"), ("polarity", "negative")] }

def ex11c : Datum :=
  { id := "simik2024_ex11c"
    source := ⟨"simik-2024", "ex. 11c"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Marek uklidil třetí patro?"
    glossedTokens := [("Marek", "Marek"), ("uklidil", "cleaned"), ("třetí", "third"), ("patro", "floor")]
    glossedWords := [⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], [⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], none⟩]⟩, ⟨['u', 'k', 'l', 'i', 'd', 'i', 'l'], ['c', 'l', 'e', 'a', 'n', 'e', 'd'], [⟨['u', 'k', 'l', 'i', 'd', 'i', 'l'], ['c', 'l', 'e', 'a', 'n', 'e', 'd'], none⟩]⟩, ⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], [⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], none⟩]⟩, ⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], [⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "On a busy day, two hotel cleaning service coordinators (A and B), sitting in their office, are taking note of the progress made thus far. A is about to make a tick for the whole third floor, which Marek was responsible for. B is informed about the progress. A asks:"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "11"), ("strategy", "declarative"), ("polarity", "positive")] }

def ex11c_neg : Datum :=
  { id := "simik2024_ex11c_neg"
    source := ⟨"simik-2024", "ex. 11c_neg"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Marek neuklidil třetí patro?"
    glossedTokens := [("Marek", "Marek"), ("neuklidil", "NEG.cleaned"), ("třetí", "third"), ("patro", "floor")]
    glossedWords := [⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], [⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], none⟩]⟩, ⟨['n', 'e', 'u', 'k', 'l', 'i', 'd', 'i', 'l'], ['N', 'E', 'G', '.', 'c', 'l', 'e', 'a', 'n', 'e', 'd'], [⟨['n', 'e', 'u', 'k', 'l', 'i', 'd', 'i', 'l'], ['N', 'E', 'G', '.', 'c', 'l', 'e', 'a', 'n', 'e', 'd'], none⟩]⟩, ⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], [⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], none⟩]⟩, ⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], [⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "On a busy day, two hotel cleaning service coordinators (A and B), sitting in their office, are taking note of the progress made thus far. A is about to make a tick for the whole third floor, which Marek was responsible for. B is informed about the progress. A asks:"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "11"), ("strategy", "declarative"), ("polarity", "negative")] }

def ex12a : Datum :=
  { id := "simik2024_ex12a"
    source := ⟨"simik-2024", "ex. 12a"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Uklízel Marek i třetí patro?"
    glossedTokens := [("Uklízel", "cleaned"), ("Marek", "Marek"), ("i", "also"), ("třetí", "third"), ("patro", "floor")]
    glossedWords := [⟨['U', 'k', 'l', 'í', 'z', 'e', 'l'], ['c', 'l', 'e', 'a', 'n', 'e', 'd'], [⟨['U', 'k', 'l', 'í', 'z', 'e', 'l'], ['c', 'l', 'e', 'a', 'n', 'e', 'd'], none⟩]⟩, ⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], [⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], none⟩]⟩, ⟨['i'], ['a', 'l', 's', 'o'], [⟨['i'], ['a', 'l', 's', 'o'], none⟩]⟩, ⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], [⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], none⟩]⟩, ⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], [⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "On a busy day, two hotel cleaning service coordinators (A and B), sitting in their office, are taking note of the progress made thus far. A is about to make a tick for the whole third floor. Marek was responsible for the second floor (and he cleaned that), but earlier that day A asked Marek if he could also exceptionally take care of the third floor. B was not informed about A's request to Marek. B is informed about the progress. A asks:"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "12"), ("strategy", "verbMovement"), ("polarity", "positive")] }

def ex12b : Datum :=
  { id := "simik2024_ex12b"
    source := ⟨"simik-2024", "ex. 12b"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Neuklízel Marek i třetí patro?"
    glossedTokens := [("Neuklízel", "NEG.cleaned"), ("Marek", "Marek"), ("i", "also"), ("třetí", "third"), ("patro", "floor")]
    glossedWords := [⟨['N', 'e', 'u', 'k', 'l', 'í', 'z', 'e', 'l'], ['N', 'E', 'G', '.', 'c', 'l', 'e', 'a', 'n', 'e', 'd'], [⟨['N', 'e', 'u', 'k', 'l', 'í', 'z', 'e', 'l'], ['N', 'E', 'G', '.', 'c', 'l', 'e', 'a', 'n', 'e', 'd'], none⟩]⟩, ⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], [⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], none⟩]⟩, ⟨['i'], ['a', 'l', 's', 'o'], [⟨['i'], ['a', 'l', 's', 'o'], none⟩]⟩, ⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], [⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], none⟩]⟩, ⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], [⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "On a busy day, two hotel cleaning service coordinators (A and B), sitting in their office, are taking note of the progress made thus far. A is about to make a tick for the whole third floor. Marek was responsible for the second floor (and he cleaned that), but earlier that day A asked Marek if he could also exceptionally take care of the third floor. B was not informed about A's request to Marek. B is informed about the progress. A asks:"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "12"), ("strategy", "verbMovement"), ("polarity", "negative")] }

def ex12c : Datum :=
  { id := "simik2024_ex12c"
    source := ⟨"simik-2024", "ex. 12c"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Marek uklízel i třetí patro?"
    glossedTokens := [("Marek", "Marek"), ("uklízel", "cleaned"), ("i", "also"), ("třetí", "third"), ("patro", "floor")]
    glossedWords := [⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], [⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], none⟩]⟩, ⟨['u', 'k', 'l', 'í', 'z', 'e', 'l'], ['c', 'l', 'e', 'a', 'n', 'e', 'd'], [⟨['u', 'k', 'l', 'í', 'z', 'e', 'l'], ['c', 'l', 'e', 'a', 'n', 'e', 'd'], none⟩]⟩, ⟨['i'], ['a', 'l', 's', 'o'], [⟨['i'], ['a', 'l', 's', 'o'], none⟩]⟩, ⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], [⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], none⟩]⟩, ⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], [⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "On a busy day, two hotel cleaning service coordinators (A and B), sitting in their office, are taking note of the progress made thus far. A is about to make a tick for the whole third floor. Marek was responsible for the second floor (and he cleaned that), but earlier that day A asked Marek if he could also exceptionally take care of the third floor. B was not informed about A's request to Marek. B is informed about the progress. A asks:"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "12"), ("strategy", "declarative"), ("polarity", "positive")] }

def ex12c_neg : Datum :=
  { id := "simik2024_ex12c_neg"
    source := ⟨"simik-2024", "ex. 12c_neg"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Marek neuklízel i třetí patro?"
    glossedTokens := [("Marek", "Marek"), ("neuklízel", "NEG.cleaned"), ("i", "also"), ("třetí", "third"), ("patro", "floor")]
    glossedWords := [⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], [⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], none⟩]⟩, ⟨['n', 'e', 'u', 'k', 'l', 'í', 'z', 'e', 'l'], ['N', 'E', 'G', '.', 'c', 'l', 'e', 'a', 'n', 'e', 'd'], [⟨['n', 'e', 'u', 'k', 'l', 'í', 'z', 'e', 'l'], ['N', 'E', 'G', '.', 'c', 'l', 'e', 'a', 'n', 'e', 'd'], none⟩]⟩, ⟨['i'], ['a', 'l', 's', 'o'], [⟨['i'], ['a', 'l', 's', 'o'], none⟩]⟩, ⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], [⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], none⟩]⟩, ⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], [⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "On a busy day, two hotel cleaning service coordinators (A and B), sitting in their office, are taking note of the progress made thus far. A is about to make a tick for the whole third floor. Marek was responsible for the second floor (and he cleaned that), but earlier that day A asked Marek if he could also exceptionally take care of the third floor. B was not informed about A's request to Marek. B is informed about the progress. A asks:"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "12"), ("strategy", "declarative"), ("polarity", "negative")] }

def ex16a : Datum :=
  { id := "simik2024_ex16a"
    source := ⟨"simik-2024", "ex. 16a"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Uklízel Marek třetí patro?"
    glossedTokens := [("Uklízel", "cleaned"), ("Marek", "Marek"), ("třetí", "third"), ("patro", "floor")]
    glossedWords := [⟨['U', 'k', 'l', 'í', 'z', 'e', 'l'], ['c', 'l', 'e', 'a', 'n', 'e', 'd'], [⟨['U', 'k', 'l', 'í', 'z', 'e', 'l'], ['c', 'l', 'e', 'a', 'n', 'e', 'd'], none⟩]⟩, ⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], [⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], none⟩]⟩, ⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], [⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], none⟩]⟩, ⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], [⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "On a busy day two hotel cleaning service coordinators (A and B), sitting in their office, are taking note of the progress made. B informs A that Marek has finished cleaning the second floor. A is slightly surprised as he believed that Marek was responsible for the third floor and it's common for one person to take care of a single floor. A asks:"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "16"), ("strategy", "verbMovement"), ("polarity", "positive")] }

def ex16b : Datum :=
  { id := "simik2024_ex16b"
    source := ⟨"simik-2024", "ex. 16b"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Neuklízel Marek třetí patro?"
    glossedTokens := [("Neuklízel", "NEG.cleaned"), ("Marek", "Marek"), ("třetí", "third"), ("patro", "floor")]
    glossedWords := [⟨['N', 'e', 'u', 'k', 'l', 'í', 'z', 'e', 'l'], ['N', 'E', 'G', '.', 'c', 'l', 'e', 'a', 'n', 'e', 'd'], [⟨['N', 'e', 'u', 'k', 'l', 'í', 'z', 'e', 'l'], ['N', 'E', 'G', '.', 'c', 'l', 'e', 'a', 'n', 'e', 'd'], none⟩]⟩, ⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], [⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], none⟩]⟩, ⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], [⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], none⟩]⟩, ⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], [⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "On a busy day two hotel cleaning service coordinators (A and B), sitting in their office, are taking note of the progress made. B informs A that Marek has finished cleaning the second floor. A is slightly surprised as he believed that Marek was responsible for the third floor and it's common for one person to take care of a single floor. A asks:"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "16"), ("strategy", "verbMovement"), ("polarity", "negative")] }

def ex16c : Datum :=
  { id := "simik2024_ex16c"
    source := ⟨"simik-2024", "ex. 16c"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Marek uklízel třetí patro?"
    glossedTokens := [("Marek", "Marek"), ("uklízel", "cleaned"), ("třetí", "third"), ("patro", "floor")]
    glossedWords := [⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], [⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], none⟩]⟩, ⟨['u', 'k', 'l', 'í', 'z', 'e', 'l'], ['c', 'l', 'e', 'a', 'n', 'e', 'd'], [⟨['u', 'k', 'l', 'í', 'z', 'e', 'l'], ['c', 'l', 'e', 'a', 'n', 'e', 'd'], none⟩]⟩, ⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], [⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], none⟩]⟩, ⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], [⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "On a busy day two hotel cleaning service coordinators (A and B), sitting in their office, are taking note of the progress made. B informs A that Marek has finished cleaning the second floor. A is slightly surprised as he believed that Marek was responsible for the third floor and it's common for one person to take care of a single floor. A asks:"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "16"), ("strategy", "declarative"), ("polarity", "positive")] }

def ex16d : Datum :=
  { id := "simik2024_ex16d"
    source := ⟨"simik-2024", "ex. 16d"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Marek neuklízel třetí patro?"
    glossedTokens := [("Marek", "Marek"), ("neuklízel", "NEG.cleaned"), ("třetí", "third"), ("patro", "floor")]
    glossedWords := [⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], [⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], none⟩]⟩, ⟨['n', 'e', 'u', 'k', 'l', 'í', 'z', 'e', 'l'], ['N', 'E', 'G', '.', 'c', 'l', 'e', 'a', 'n', 'e', 'd'], [⟨['n', 'e', 'u', 'k', 'l', 'í', 'z', 'e', 'l'], ['N', 'E', 'G', '.', 'c', 'l', 'e', 'a', 'n', 'e', 'd'], none⟩]⟩, ⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], [⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], none⟩]⟩, ⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], [⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "On a busy day two hotel cleaning service coordinators (A and B), sitting in their office, are taking note of the progress made. B informs A that Marek has finished cleaning the second floor. A is slightly surprised as he believed that Marek was responsible for the third floor and it's common for one person to take care of a single floor. A asks:"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "16"), ("strategy", "declarative"), ("polarity", "negative")] }

def ex17a : Datum :=
  { id := "simik2024_ex17a"
    source := ⟨"simik-2024", "ex. 17a"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Uklízel Marek třetí patro?"
    glossedTokens := [("Uklízel", "cleaned"), ("Marek", "Marek"), ("třetí", "third"), ("patro", "floor")]
    glossedWords := [⟨['U', 'k', 'l', 'í', 'z', 'e', 'l'], ['c', 'l', 'e', 'a', 'n', 'e', 'd'], [⟨['U', 'k', 'l', 'í', 'z', 'e', 'l'], ['c', 'l', 'e', 'a', 'n', 'e', 'd'], none⟩]⟩, ⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], [⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], none⟩]⟩, ⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], [⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], none⟩]⟩, ⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], [⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Two hotel cleaning service coordinators (A and B) are walking around the hotel and inspecting the progress made. A has no idea about the cleaning plan for today (esp. who is responsible for what), only B does. When on the third floor, A and B find an earbud that A suspects belongs to Marek, one of the cleaners. A asks:"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "17"), ("strategy", "verbMovement"), ("polarity", "positive")] }

def ex17b : Datum :=
  { id := "simik2024_ex17b"
    source := ⟨"simik-2024", "ex. 17b"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Neuklízel Marek třetí patro?"
    glossedTokens := [("Neuklízel", "NEG.cleaned"), ("Marek", "Marek"), ("třetí", "third"), ("patro", "floor")]
    glossedWords := [⟨['N', 'e', 'u', 'k', 'l', 'í', 'z', 'e', 'l'], ['N', 'E', 'G', '.', 'c', 'l', 'e', 'a', 'n', 'e', 'd'], [⟨['N', 'e', 'u', 'k', 'l', 'í', 'z', 'e', 'l'], ['N', 'E', 'G', '.', 'c', 'l', 'e', 'a', 'n', 'e', 'd'], none⟩]⟩, ⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], [⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], none⟩]⟩, ⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], [⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], none⟩]⟩, ⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], [⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Two hotel cleaning service coordinators (A and B) are walking around the hotel and inspecting the progress made. A has no idea about the cleaning plan for today (esp. who is responsible for what), only B does. When on the third floor, A and B find an earbud that A suspects belongs to Marek, one of the cleaners. A asks:"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "17"), ("strategy", "verbMovement"), ("polarity", "negative")] }

def ex17c : Datum :=
  { id := "simik2024_ex17c"
    source := ⟨"simik-2024", "ex. 17c"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Marek uklízel třetí patro?"
    glossedTokens := [("Marek", "Marek"), ("uklízel", "cleaned"), ("třetí", "third"), ("patro", "floor")]
    glossedWords := [⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], [⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], none⟩]⟩, ⟨['u', 'k', 'l', 'í', 'z', 'e', 'l'], ['c', 'l', 'e', 'a', 'n', 'e', 'd'], [⟨['u', 'k', 'l', 'í', 'z', 'e', 'l'], ['c', 'l', 'e', 'a', 'n', 'e', 'd'], none⟩]⟩, ⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], [⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], none⟩]⟩, ⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], [⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Two hotel cleaning service coordinators (A and B) are walking around the hotel and inspecting the progress made. A has no idea about the cleaning plan for today (esp. who is responsible for what), only B does. When on the third floor, A and B find an earbud that A suspects belongs to Marek, one of the cleaners. A asks:"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "17"), ("strategy", "declarative"), ("polarity", "positive")] }

def ex17d : Datum :=
  { id := "simik2024_ex17d"
    source := ⟨"simik-2024", "ex. 17d"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Marek neuklízel třetí patro?"
    glossedTokens := [("Marek", "Marek"), ("neuklízel", "NEG.cleaned"), ("třetí", "third"), ("patro", "floor")]
    glossedWords := [⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], [⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], none⟩]⟩, ⟨['n', 'e', 'u', 'k', 'l', 'í', 'z', 'e', 'l'], ['N', 'E', 'G', '.', 'c', 'l', 'e', 'a', 'n', 'e', 'd'], [⟨['n', 'e', 'u', 'k', 'l', 'í', 'z', 'e', 'l'], ['N', 'E', 'G', '.', 'c', 'l', 'e', 'a', 'n', 'e', 'd'], none⟩]⟩, ⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], [⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], none⟩]⟩, ⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], [⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Two hotel cleaning service coordinators (A and B) are walking around the hotel and inspecting the progress made. A has no idea about the cleaning plan for today (esp. who is responsible for what), only B does. When on the third floor, A and B find an earbud that A suspects belongs to Marek, one of the cleaners. A asks:"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "17"), ("strategy", "declarative"), ("polarity", "negative")] }

def ex18a : Datum :=
  { id := "simik2024_ex18a"
    source := ⟨"simik-2024", "ex. 18a"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Uklidil Marek třetí patro?"
    glossedTokens := [("Uklidil", "cleaned"), ("Marek", "Marek"), ("třetí", "third"), ("patro", "floor")]
    glossedWords := [⟨['U', 'k', 'l', 'i', 'd', 'i', 'l'], ['c', 'l', 'e', 'a', 'n', 'e', 'd'], [⟨['U', 'k', 'l', 'i', 'd', 'i', 'l'], ['c', 'l', 'e', 'a', 'n', 'e', 'd'], none⟩]⟩, ⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], [⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], none⟩]⟩, ⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], [⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], none⟩]⟩, ⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], [⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "On a busy day, two hotel cleaning service coordinators (A and B), sitting in their office, are taking note of the progress made thus far. B is informed about the progress. After a brief chat about two new cleaners who have just joined the team, Lucie and Marek, A wants to take note of the final two floors and wonders who (Lucie or Marek) cleaned which floor (second or third). A starts by asking:"
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "18"), ("strategy", "verbMovement"), ("polarity", "positive")] }

def ex18b : Datum :=
  { id := "simik2024_ex18b"
    source := ⟨"simik-2024", "ex. 18b"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Neuklidil Marek třetí patro?"
    glossedTokens := [("Neuklidil", "NEG.cleaned"), ("Marek", "Marek"), ("třetí", "third"), ("patro", "floor")]
    glossedWords := [⟨['N', 'e', 'u', 'k', 'l', 'i', 'd', 'i', 'l'], ['N', 'E', 'G', '.', 'c', 'l', 'e', 'a', 'n', 'e', 'd'], [⟨['N', 'e', 'u', 'k', 'l', 'i', 'd', 'i', 'l'], ['N', 'E', 'G', '.', 'c', 'l', 'e', 'a', 'n', 'e', 'd'], none⟩]⟩, ⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], [⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], none⟩]⟩, ⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], [⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], none⟩]⟩, ⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], [⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "On a busy day, two hotel cleaning service coordinators (A and B), sitting in their office, are taking note of the progress made thus far. B is informed about the progress. After a brief chat about two new cleaners who have just joined the team, Lucie and Marek, A wants to take note of the final two floors and wonders who (Lucie or Marek) cleaned which floor (second or third). A starts by asking:"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "18"), ("strategy", "verbMovement"), ("polarity", "negative")] }

def ex18c : Datum :=
  { id := "simik2024_ex18c"
    source := ⟨"simik-2024", "ex. 18c"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Marek uklidil třetí patro?"
    glossedTokens := [("Marek", "Marek"), ("uklidil", "cleaned"), ("třetí", "third"), ("patro", "floor")]
    glossedWords := [⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], [⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], none⟩]⟩, ⟨['u', 'k', 'l', 'i', 'd', 'i', 'l'], ['c', 'l', 'e', 'a', 'n', 'e', 'd'], [⟨['u', 'k', 'l', 'i', 'd', 'i', 'l'], ['c', 'l', 'e', 'a', 'n', 'e', 'd'], none⟩]⟩, ⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], [⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], none⟩]⟩, ⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], [⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "On a busy day, two hotel cleaning service coordinators (A and B), sitting in their office, are taking note of the progress made thus far. B is informed about the progress. After a brief chat about two new cleaners who have just joined the team, Lucie and Marek, A wants to take note of the final two floors and wonders who (Lucie or Marek) cleaned which floor (second or third). A starts by asking:"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "18"), ("strategy", "declarative"), ("polarity", "positive")] }

def ex18d : Datum :=
  { id := "simik2024_ex18d"
    source := ⟨"simik-2024", "ex. 18d"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Marek neuklidil třetí patro?"
    glossedTokens := [("Marek", "Marek"), ("neuklidil", "NEG.cleaned"), ("třetí", "third"), ("patro", "floor")]
    glossedWords := [⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], [⟨['M', 'a', 'r', 'e', 'k'], ['M', 'a', 'r', 'e', 'k'], none⟩]⟩, ⟨['n', 'e', 'u', 'k', 'l', 'i', 'd', 'i', 'l'], ['N', 'E', 'G', '.', 'c', 'l', 'e', 'a', 'n', 'e', 'd'], [⟨['n', 'e', 'u', 'k', 'l', 'i', 'd', 'i', 'l'], ['N', 'E', 'G', '.', 'c', 'l', 'e', 'a', 'n', 'e', 'd'], none⟩]⟩, ⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], [⟨['t', 'ř', 'e', 't', 'í'], ['t', 'h', 'i', 'r', 'd'], none⟩]⟩, ⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], [⟨['p', 'a', 't', 'r', 'o'], ['f', 'l', 'o', 'o', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "On a busy day, two hotel cleaning service coordinators (A and B), sitting in their office, are taking note of the progress made thus far. B is informed about the progress. After a brief chat about two new cleaners who have just joined the team, Lucie and Marek, A wants to take note of the final two floors and wonders who (Lucie or Marek) cleaned which floor (second or third). A starts by asking:"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "18"), ("strategy", "declarative"), ("polarity", "negative")] }

def ex25a : Datum :=
  { id := "simik2024_ex25a"
    source := ⟨"simik-2024", "ex. 25a"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Dožil se císař Justinián I. 80 let?"
    glossedTokens := [("Dožil", "lived.to"), ("se", "REFL"), ("císař", "emperor"), ("Justinián", "Justinian"), ("I.", "I"), ("80", "80"), ("let", "years")]
    glossedWords := [⟨['D', 'o', 'ž', 'i', 'l'], ['l', 'i', 'v', 'e', 'd', '.', 't', 'o'], [⟨['D', 'o', 'ž', 'i', 'l'], ['l', 'i', 'v', 'e', 'd', '.', 't', 'o'], none⟩]⟩, ⟨['s', 'e'], ['R', 'E', 'F', 'L'], [⟨['s', 'e'], ['R', 'E', 'F', 'L'], none⟩]⟩, ⟨['c', 'í', 's', 'a', 'ř'], ['e', 'm', 'p', 'e', 'r', 'o', 'r'], [⟨['c', 'í', 's', 'a', 'ř'], ['e', 'm', 'p', 'e', 'r', 'o', 'r'], none⟩]⟩, ⟨['J', 'u', 's', 't', 'i', 'n', 'i', 'á', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], [⟨['J', 'u', 's', 't', 'i', 'n', 'i', 'á', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], none⟩]⟩, ⟨['I', '.'], ['I'], [⟨['I'], ['I'], none⟩]⟩, ⟨['8', '0'], ['8', '0'], [⟨['8', '0'], ['8', '0'], none⟩]⟩, ⟨['l', 'e', 't'], ['y', 'e', 'a', 'r', 's'], [⟨['l', 'e', 't'], ['y', 'e', 'a', 'r', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "verbMovement"), ("polarity", "positive"), ("label", "InterPPQ")] }

def ex25b : Datum :=
  { id := "simik2024_ex25b"
    source := ⟨"simik-2024", "ex. 25b"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Nedožil se císař Justinián I. 80 let?"
    glossedTokens := []
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "verbMovement"), ("polarity", "negative"), ("label", "InterNPQ")] }

def ex25c : Datum :=
  { id := "simik2024_ex25c"
    source := ⟨"simik-2024", "ex. 25c"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Císař Justinián I. se dožil 80 let?"
    glossedTokens := []
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "declarative"), ("polarity", "positive"), ("label", "DeclPQ")] }

def ex25c_neg : Datum :=
  { id := "simik2024_ex25c_neg"
    source := ⟨"simik-2024", "ex. 25c_neg"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Císař Justinián I. se nedožil 80 let?"
    glossedTokens := []
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "declarative"), ("polarity", "negative"), ("label", "DeclPQ")] }

def ex26a : Datum :=
  { id := "simik2024_ex26a"
    source := ⟨"simik-2024", "ex. 26a"⟩
    reportedIn := none
    method := some .elicitation
    language := "slov1269"
    primaryText := "Dožil sa cisár Justinián 80 rokov?"
    glossedTokens := [("Dožil", "live.to"), ("sa", "REFL"), ("cisár", "emperor"), ("Justinián", "Justinian"), ("80", "80"), ("rokov", "years")]
    glossedWords := [⟨['D', 'o', 'ž', 'i', 'l'], ['l', 'i', 'v', 'e', '.', 't', 'o'], [⟨['D', 'o', 'ž', 'i', 'l'], ['l', 'i', 'v', 'e', '.', 't', 'o'], none⟩]⟩, ⟨['s', 'a'], ['R', 'E', 'F', 'L'], [⟨['s', 'a'], ['R', 'E', 'F', 'L'], none⟩]⟩, ⟨['c', 'i', 's', 'á', 'r'], ['e', 'm', 'p', 'e', 'r', 'o', 'r'], [⟨['c', 'i', 's', 'á', 'r'], ['e', 'm', 'p', 'e', 'r', 'o', 'r'], none⟩]⟩, ⟨['J', 'u', 's', 't', 'i', 'n', 'i', 'á', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], [⟨['J', 'u', 's', 't', 'i', 'n', 'i', 'á', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], none⟩]⟩, ⟨['8', '0'], ['8', '0'], [⟨['8', '0'], ['8', '0'], none⟩]⟩, ⟨['r', 'o', 'k', 'o', 'v'], ['y', 'e', 'a', 'r', 's'], [⟨['r', 'o', 'k', 'o', 'v'], ['y', 'e', 'a', 'r', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "verbMovement"), ("polarity", "positive"), ("label", "InterPPQ")] }

def ex26b : Datum :=
  { id := "simik2024_ex26b"
    source := ⟨"simik-2024", "ex. 26b"⟩
    reportedIn := none
    method := some .elicitation
    language := "slov1269"
    primaryText := "Nedožil sa cisár Justinián 80 rokov?"
    glossedTokens := []
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "verbMovement"), ("polarity", "negative"), ("label", "InterNPQ")] }

def ex26c : Datum :=
  { id := "simik2024_ex26c"
    source := ⟨"simik-2024", "ex. 26c"⟩
    reportedIn := none
    method := some .elicitation
    language := "slov1269"
    primaryText := "Cisár Justinián sa dožil 80 rokov?"
    glossedTokens := []
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "declarative"), ("polarity", "positive"), ("label", "DeclPQ")] }

def ex26c_neg : Datum :=
  { id := "simik2024_ex26c_neg"
    source := ⟨"simik-2024", "ex. 26c_neg"⟩
    reportedIn := none
    method := some .elicitation
    language := "slov1269"
    primaryText := "Cisár Justinián sa nedožil 80 rokov?"
    glossedTokens := []
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "declarative"), ("polarity", "negative"), ("label", "DeclPQ")] }

def ex27a : Datum :=
  { id := "simik2024_ex27a"
    source := ⟨"simik-2024", "ex. 27a"⟩
    reportedIn := none
    method := some .elicitation
    language := "uppe1395"
    primaryText := "Je kejžor Justinian Wulki 80 lět wordował?"
    glossedTokens := [("Je", "is.AUX"), ("kejžor", "emperor"), ("Justinian", "Justinian"), ("Wulki", "Great"), ("80", "80"), ("lět", "years"), ("wordował", "become")]
    glossedWords := [⟨['J', 'e'], ['i', 's', '.', 'A', 'U', 'X'], [⟨['J', 'e'], ['i', 's', '.', 'A', 'U', 'X'], none⟩]⟩, ⟨['k', 'e', 'j', 'ž', 'o', 'r'], ['e', 'm', 'p', 'e', 'r', 'o', 'r'], [⟨['k', 'e', 'j', 'ž', 'o', 'r'], ['e', 'm', 'p', 'e', 'r', 'o', 'r'], none⟩]⟩, ⟨['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], [⟨['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], none⟩]⟩, ⟨['W', 'u', 'l', 'k', 'i'], ['G', 'r', 'e', 'a', 't'], [⟨['W', 'u', 'l', 'k', 'i'], ['G', 'r', 'e', 'a', 't'], none⟩]⟩, ⟨['8', '0'], ['8', '0'], [⟨['8', '0'], ['8', '0'], none⟩]⟩, ⟨['l', 'ě', 't'], ['y', 'e', 'a', 'r', 's'], [⟨['l', 'ě', 't'], ['y', 'e', 'a', 'r', 's'], none⟩]⟩, ⟨['w', 'o', 'r', 'd', 'o', 'w', 'a', 'ł'], ['b', 'e', 'c', 'o', 'm', 'e'], [⟨['w', 'o', 'r', 'd', 'o', 'w', 'a', 'ł'], ['b', 'e', 'c', 'o', 'm', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "verbMovement"), ("polarity", "positive"), ("label", "InterPPQ")] }

def ex27b : Datum :=
  { id := "simik2024_ex27b"
    source := ⟨"simik-2024", "ex. 27b"⟩
    reportedIn := none
    method := some .elicitation
    language := "uppe1395"
    primaryText := "Njeje kejžor Justinian Wulki 80 lět wordował?"
    glossedTokens := []
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "verbMovement"), ("polarity", "negative"), ("label", "InterNPQ")] }

def ex27c : Datum :=
  { id := "simik2024_ex27c"
    source := ⟨"simik-2024", "ex. 27c"⟩
    reportedIn := none
    method := some .elicitation
    language := "uppe1395"
    primaryText := "Kejžor Justinian Wulki je 80 lět wordował?"
    glossedTokens := []
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "declarative"), ("polarity", "positive"), ("label", "DeclPQ")] }

def ex27c_neg : Datum :=
  { id := "simik2024_ex27c_neg"
    source := ⟨"simik-2024", "ex. 27c_neg"⟩
    reportedIn := none
    method := some .elicitation
    language := "uppe1395"
    primaryText := "Kejžor Justinian Wulki njeje 80 lět wordował?"
    glossedTokens := []
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "declarative"), ("polarity", "negative"), ("label", "DeclPQ")] }

def ex28a : Datum :=
  { id := "simik2024_ex28a"
    source := ⟨"simik-2024", "ex. 28a"⟩
    reportedIn := none
    method := some .elicitation
    language := "slov1268"
    primaryText := "(Ali) Je cesar Justinijan doživel 80 let?"
    glossedTokens := [("(Ali)", "ALI"), ("Je", "is.AUX"), ("cesar", "emperor"), ("Justinijan", "Justinian"), ("doživel", "lived.to"), ("80", "80"), ("let", "years")]
    glossedWords := [⟨['(', 'A', 'l', 'i', ')'], ['A', 'L', 'I'], [⟨['A', 'l', 'i'], ['A', 'L', 'I'], none⟩]⟩, ⟨['J', 'e'], ['i', 's', '.', 'A', 'U', 'X'], [⟨['J', 'e'], ['i', 's', '.', 'A', 'U', 'X'], none⟩]⟩, ⟨['c', 'e', 's', 'a', 'r'], ['e', 'm', 'p', 'e', 'r', 'o', 'r'], [⟨['c', 'e', 's', 'a', 'r'], ['e', 'm', 'p', 'e', 'r', 'o', 'r'], none⟩]⟩, ⟨['J', 'u', 's', 't', 'i', 'n', 'i', 'j', 'a', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], [⟨['J', 'u', 's', 't', 'i', 'n', 'i', 'j', 'a', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], none⟩]⟩, ⟨['d', 'o', 'ž', 'i', 'v', 'e', 'l'], ['l', 'i', 'v', 'e', 'd', '.', 't', 'o'], [⟨['d', 'o', 'ž', 'i', 'v', 'e', 'l'], ['l', 'i', 'v', 'e', 'd', '.', 't', 'o'], none⟩]⟩, ⟨['8', '0'], ['8', '0'], [⟨['8', '0'], ['8', '0'], none⟩]⟩, ⟨['l', 'e', 't'], ['y', 'e', 'a', 'r', 's'], [⟨['l', 'e', 't'], ['y', 'e', 'a', 'r', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "verbMovement"), ("strategy", "clauseInitialParticle"), ("polarity", "positive"), ("label", "InterPPQ"), ("particle", "ali")] }

def ex28b : Datum :=
  { id := "simik2024_ex28b"
    source := ⟨"simik-2024", "ex. 28b"⟩
    reportedIn := none
    method := some .elicitation
    language := "slov1268"
    primaryText := "(Ali) Ni cesar Justinijan doživel 80 let?"
    glossedTokens := [("(Ali)", "ALI"), ("Ni", "NEG.is.AUX"), ("cesar", "emperor"), ("Justinijan", "Justinian"), ("doživel", "lived.to"), ("80", "80"), ("let", "years")]
    glossedWords := [⟨['(', 'A', 'l', 'i', ')'], ['A', 'L', 'I'], [⟨['A', 'l', 'i'], ['A', 'L', 'I'], none⟩]⟩, ⟨['N', 'i'], ['N', 'E', 'G', '.', 'i', 's', '.', 'A', 'U', 'X'], [⟨['N', 'i'], ['N', 'E', 'G', '.', 'i', 's', '.', 'A', 'U', 'X'], none⟩]⟩, ⟨['c', 'e', 's', 'a', 'r'], ['e', 'm', 'p', 'e', 'r', 'o', 'r'], [⟨['c', 'e', 's', 'a', 'r'], ['e', 'm', 'p', 'e', 'r', 'o', 'r'], none⟩]⟩, ⟨['J', 'u', 's', 't', 'i', 'n', 'i', 'j', 'a', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], [⟨['J', 'u', 's', 't', 'i', 'n', 'i', 'j', 'a', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], none⟩]⟩, ⟨['d', 'o', 'ž', 'i', 'v', 'e', 'l'], ['l', 'i', 'v', 'e', 'd', '.', 't', 'o'], [⟨['d', 'o', 'ž', 'i', 'v', 'e', 'l'], ['l', 'i', 'v', 'e', 'd', '.', 't', 'o'], none⟩]⟩, ⟨['8', '0'], ['8', '0'], [⟨['8', '0'], ['8', '0'], none⟩]⟩, ⟨['l', 'e', 't'], ['y', 'e', 'a', 'r', 's'], [⟨['l', 'e', 't'], ['y', 'e', 'a', 'r', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "verbMovement"), ("strategy", "clauseInitialParticle"), ("polarity", "negative"), ("label", "InterNPQ"), ("particle", "ali")] }

def ex28c : Datum :=
  { id := "simik2024_ex28c"
    source := ⟨"simik-2024", "ex. 28c"⟩
    reportedIn := none
    method := some .elicitation
    language := "slov1268"
    primaryText := "Cesar Justinijan je doživel 80 let?"
    glossedTokens := []
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "declarative"), ("polarity", "positive"), ("label", "DeclPQ")] }

def ex28c_neg : Datum :=
  { id := "simik2024_ex28c_neg"
    source := ⟨"simik-2024", "ex. 28c_neg"⟩
    reportedIn := none
    method := some .elicitation
    language := "slov1268"
    primaryText := "Cesar Justinijan ni doživel 80 let?"
    glossedTokens := []
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "declarative"), ("polarity", "negative"), ("label", "DeclPQ")] }

def ex29a : Datum :=
  { id := "simik2024_ex29a"
    source := ⟨"simik-2024", "ex. 29a"⟩
    reportedIn := none
    method := some .elicitation
    language := "ukra1253"
    primaryText := "Čy dožyv imperator Justynian Velykyj do 80 rokiv?"
    glossedTokens := [("Čy", "CY"), ("dožyv", "lived"), ("imperator", "emperor"), ("Justynian", "Justinian"), ("Velykyj", "Great"), ("do", "to"), ("80", "80"), ("rokiv", "years")]
    glossedWords := [⟨['Č', 'y'], ['C', 'Y'], [⟨['Č', 'y'], ['C', 'Y'], none⟩]⟩, ⟨['d', 'o', 'ž', 'y', 'v'], ['l', 'i', 'v', 'e', 'd'], [⟨['d', 'o', 'ž', 'y', 'v'], ['l', 'i', 'v', 'e', 'd'], none⟩]⟩, ⟨['i', 'm', 'p', 'e', 'r', 'a', 't', 'o', 'r'], ['e', 'm', 'p', 'e', 'r', 'o', 'r'], [⟨['i', 'm', 'p', 'e', 'r', 'a', 't', 'o', 'r'], ['e', 'm', 'p', 'e', 'r', 'o', 'r'], none⟩]⟩, ⟨['J', 'u', 's', 't', 'y', 'n', 'i', 'a', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], [⟨['J', 'u', 's', 't', 'y', 'n', 'i', 'a', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], none⟩]⟩, ⟨['V', 'e', 'l', 'y', 'k', 'y', 'j'], ['G', 'r', 'e', 'a', 't'], [⟨['V', 'e', 'l', 'y', 'k', 'y', 'j'], ['G', 'r', 'e', 'a', 't'], none⟩]⟩, ⟨['d', 'o'], ['t', 'o'], [⟨['d', 'o'], ['t', 'o'], none⟩]⟩, ⟨['8', '0'], ['8', '0'], [⟨['8', '0'], ['8', '0'], none⟩]⟩, ⟨['r', 'o', 'k', 'i', 'v'], ['y', 'e', 'a', 'r', 's'], [⟨['r', 'o', 'k', 'i', 'v'], ['y', 'e', 'a', 'r', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "clauseInitialParticle"), ("polarity", "positive"), ("label", "cyPPQ"), ("particle", "čy")] }

def ex29b : Datum :=
  { id := "simik2024_ex29b"
    source := ⟨"simik-2024", "ex. 29b"⟩
    reportedIn := none
    method := some .elicitation
    language := "ukra1253"
    primaryText := "Čy imperator Justynian Velykyj dožyv do 80 rokiv?"
    glossedTokens := []
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "clauseInitialParticle"), ("polarity", "positive"), ("label", "cyPPQ"), ("particle", "čy")] }

def ex29c : Datum :=
  { id := "simik2024_ex29c"
    source := ⟨"simik-2024", "ex. 29c"⟩
    reportedIn := none
    method := some .elicitation
    language := "ukra1253"
    primaryText := "Čy ne dožyv imperator Justynian Velykyj do 80 rokiv?"
    glossedTokens := []
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "clauseInitialParticle"), ("polarity", "negative"), ("label", "cyNPQ"), ("particle", "čy")] }

def ex29d : Datum :=
  { id := "simik2024_ex29d"
    source := ⟨"simik-2024", "ex. 29d"⟩
    reportedIn := none
    method := some .elicitation
    language := "ukra1253"
    primaryText := "Čy imperator Justynian Velykyj ne dožyv do 80 rokiv?"
    glossedTokens := []
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "clauseInitialParticle"), ("polarity", "negative"), ("label", "cyNPQ"), ("particle", "čy")] }

def ex29e : Datum :=
  { id := "simik2024_ex29e"
    source := ⟨"simik-2024", "ex. 29e"⟩
    reportedIn := none
    method := some .elicitation
    language := "ukra1253"
    primaryText := "Imperator Justynian Velykyj dožyv do 80 rokiv?"
    glossedTokens := []
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "declarative"), ("polarity", "positive"), ("label", "DeclPQ")] }

def ex29e_neg : Datum :=
  { id := "simik2024_ex29e_neg"
    source := ⟨"simik-2024", "ex. 29e_neg"⟩
    reportedIn := none
    method := some .elicitation
    language := "ukra1253"
    primaryText := "Imperator Justynian Velykyj ne dožyv do 80 rokiv?"
    glossedTokens := []
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "declarative"), ("polarity", "negative"), ("label", "DeclPQ")] }

def ex30a : Datum :=
  { id := "simik2024_ex30a"
    source := ⟨"simik-2024", "ex. 30a"⟩
    reportedIn := none
    method := some .elicitation
    language := "poli1260"
    primaryText := "Czy Justynian I Wielki dożył wieku 80 lat?"
    glossedTokens := [("Czy", "CZY"), ("Justynian", "Justinian"), ("I", "I"), ("Wielki", "Great"), ("dożył", "live.to"), ("wieku", "age"), ("80", "80"), ("lat", "years")]
    glossedWords := [⟨['C', 'z', 'y'], ['C', 'Z', 'Y'], [⟨['C', 'z', 'y'], ['C', 'Z', 'Y'], none⟩]⟩, ⟨['J', 'u', 's', 't', 'y', 'n', 'i', 'a', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], [⟨['J', 'u', 's', 't', 'y', 'n', 'i', 'a', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], none⟩]⟩, ⟨['I'], ['I'], [⟨['I'], ['I'], none⟩]⟩, ⟨['W', 'i', 'e', 'l', 'k', 'i'], ['G', 'r', 'e', 'a', 't'], [⟨['W', 'i', 'e', 'l', 'k', 'i'], ['G', 'r', 'e', 'a', 't'], none⟩]⟩, ⟨['d', 'o', 'ż', 'y', 'ł'], ['l', 'i', 'v', 'e', '.', 't', 'o'], [⟨['d', 'o', 'ż', 'y', 'ł'], ['l', 'i', 'v', 'e', '.', 't', 'o'], none⟩]⟩, ⟨['w', 'i', 'e', 'k', 'u'], ['a', 'g', 'e'], [⟨['w', 'i', 'e', 'k', 'u'], ['a', 'g', 'e'], none⟩]⟩, ⟨['8', '0'], ['8', '0'], [⟨['8', '0'], ['8', '0'], none⟩]⟩, ⟨['l', 'a', 't'], ['y', 'e', 'a', 'r', 's'], [⟨['l', 'a', 't'], ['y', 'e', 'a', 'r', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "clauseInitialParticle"), ("polarity", "positive"), ("label", "czyPPQ"), ("particle", "czy")] }

def ex30b : Datum :=
  { id := "simik2024_ex30b"
    source := ⟨"simik-2024", "ex. 30b"⟩
    reportedIn := none
    method := some .elicitation
    language := "poli1260"
    primaryText := "Czy Justynian I Wielki nie dożył wieku 80 lat?"
    glossedTokens := [("Czy", "CZY"), ("Justynian", "Justinian"), ("I", "I"), ("Wielki", "Great"), ("nie", "NEG"), ("dożył", "live.to"), ("wieku", "age"), ("80", "80"), ("lat", "years")]
    glossedWords := [⟨['C', 'z', 'y'], ['C', 'Z', 'Y'], [⟨['C', 'z', 'y'], ['C', 'Z', 'Y'], none⟩]⟩, ⟨['J', 'u', 's', 't', 'y', 'n', 'i', 'a', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], [⟨['J', 'u', 's', 't', 'y', 'n', 'i', 'a', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], none⟩]⟩, ⟨['I'], ['I'], [⟨['I'], ['I'], none⟩]⟩, ⟨['W', 'i', 'e', 'l', 'k', 'i'], ['G', 'r', 'e', 'a', 't'], [⟨['W', 'i', 'e', 'l', 'k', 'i'], ['G', 'r', 'e', 'a', 't'], none⟩]⟩, ⟨['n', 'i', 'e'], ['N', 'E', 'G'], [⟨['n', 'i', 'e'], ['N', 'E', 'G'], none⟩]⟩, ⟨['d', 'o', 'ż', 'y', 'ł'], ['l', 'i', 'v', 'e', '.', 't', 'o'], [⟨['d', 'o', 'ż', 'y', 'ł'], ['l', 'i', 'v', 'e', '.', 't', 'o'], none⟩]⟩, ⟨['w', 'i', 'e', 'k', 'u'], ['a', 'g', 'e'], [⟨['w', 'i', 'e', 'k', 'u'], ['a', 'g', 'e'], none⟩]⟩, ⟨['8', '0'], ['8', '0'], [⟨['8', '0'], ['8', '0'], none⟩]⟩, ⟨['l', 'a', 't'], ['y', 'e', 'a', 'r', 's'], [⟨['l', 'a', 't'], ['y', 'e', 'a', 'r', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "clauseInitialParticle"), ("polarity", "negative"), ("label", "czyNPQ"), ("particle", "czy")] }

def ex30c : Datum :=
  { id := "simik2024_ex30c"
    source := ⟨"simik-2024", "ex. 30c"⟩
    reportedIn := none
    method := some .elicitation
    language := "poli1260"
    primaryText := "Justynian I Wielki dożył wieku 80 lat?"
    glossedTokens := []
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "declarative"), ("polarity", "positive"), ("label", "DeclPQ")] }

def ex30c_neg : Datum :=
  { id := "simik2024_ex30c_neg"
    source := ⟨"simik-2024", "ex. 30c_neg"⟩
    reportedIn := none
    method := some .elicitation
    language := "poli1260"
    primaryText := "Justynian I Wielki nie dożył wieku 80 lat?"
    glossedTokens := []
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "declarative"), ("polarity", "negative"), ("label", "DeclPQ")] }

def ex30d : Datum :=
  { id := "simik2024_ex30d"
    source := ⟨"simik-2024", "ex. 30d"⟩
    reportedIn := none
    method := some .elicitation
    language := "poli1260"
    primaryText := "Dożył Justynian I Wielki wieku 80 lat?"
    glossedTokens := []
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "verbMovement"), ("polarity", "positive"), ("label", "V1PQ")] }

def ex30d_neg : Datum :=
  { id := "simik2024_ex30d_neg"
    source := ⟨"simik-2024", "ex. 30d_neg"⟩
    reportedIn := none
    method := some .elicitation
    language := "poli1260"
    primaryText := "Nie dożył Justynian I Wielki wieku 80 lat?"
    glossedTokens := []
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "verbMovement"), ("polarity", "negative"), ("label", "V1PQ")] }

def ex31a : Datum :=
  { id := "simik2024_ex31a"
    source := ⟨"simik-2024", "ex. 31a"⟩
    reportedIn := none
    method := some .elicitation
    language := "serb1264"
    primaryText := "Da li je Justinijan I/Veliki doživeo 80 godinu?"
    glossedTokens := [("Da", "DA"), ("li", "LI"), ("je", "is.AUX"), ("Justinijan", "Justinian"), ("I/Veliki", "I/Great"), ("doživeo", "lived.to"), ("80", "80"), ("godinu", "years")]
    glossedWords := [⟨['D', 'a'], ['D', 'A'], [⟨['D', 'a'], ['D', 'A'], none⟩]⟩, ⟨['l', 'i'], ['L', 'I'], [⟨['l', 'i'], ['L', 'I'], none⟩]⟩, ⟨['j', 'e'], ['i', 's', '.', 'A', 'U', 'X'], [⟨['j', 'e'], ['i', 's', '.', 'A', 'U', 'X'], none⟩]⟩, ⟨['J', 'u', 's', 't', 'i', 'n', 'i', 'j', 'a', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], [⟨['J', 'u', 's', 't', 'i', 'n', 'i', 'j', 'a', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], none⟩]⟩, ⟨['I', '/', 'V', 'e', 'l', 'i', 'k', 'i'], ['I', '/', 'G', 'r', 'e', 'a', 't'], [⟨['I', '/', 'V', 'e', 'l', 'i', 'k', 'i'], ['I', '/', 'G', 'r', 'e', 'a', 't'], none⟩]⟩, ⟨['d', 'o', 'ž', 'i', 'v', 'e', 'o'], ['l', 'i', 'v', 'e', 'd', '.', 't', 'o'], [⟨['d', 'o', 'ž', 'i', 'v', 'e', 'o'], ['l', 'i', 'v', 'e', 'd', '.', 't', 'o'], none⟩]⟩, ⟨['8', '0'], ['8', '0'], [⟨['8', '0'], ['8', '0'], none⟩]⟩, ⟨['g', 'o', 'd', 'i', 'n', 'u'], ['y', 'e', 'a', 'r', 's'], [⟨['g', 'o', 'd', 'i', 'n', 'u'], ['y', 'e', 'a', 'r', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "clauseInitialParticle"), ("polarity", "positive"), ("label", "da+liPPQ"), ("particle", "da li")] }

def ex31b : Datum :=
  { id := "simik2024_ex31b"
    source := ⟨"simik-2024", "ex. 31b"⟩
    reportedIn := none
    method := some .elicitation
    language := "serb1264"
    primaryText := "Je l' (je) Justinijan I/Veliki doživeo 80 godinu?"
    glossedTokens := [("Je", "JE"), ("l'", "LI"), ("(je)", "is.AUX"), ("Justinijan", "Justinian"), ("I/Veliki", "I/Great"), ("doživeo", "lived.to"), ("80", "80"), ("godinu", "years")]
    glossedWords := [⟨['J', 'e'], ['J', 'E'], [⟨['J', 'e'], ['J', 'E'], none⟩]⟩, ⟨['l', '\''], ['L', 'I'], [⟨['l', '\''], ['L', 'I'], none⟩]⟩, ⟨['(', 'j', 'e', ')'], ['i', 's', '.', 'A', 'U', 'X'], [⟨['j', 'e'], ['i', 's', '.', 'A', 'U', 'X'], none⟩]⟩, ⟨['J', 'u', 's', 't', 'i', 'n', 'i', 'j', 'a', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], [⟨['J', 'u', 's', 't', 'i', 'n', 'i', 'j', 'a', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], none⟩]⟩, ⟨['I', '/', 'V', 'e', 'l', 'i', 'k', 'i'], ['I', '/', 'G', 'r', 'e', 'a', 't'], [⟨['I', '/', 'V', 'e', 'l', 'i', 'k', 'i'], ['I', '/', 'G', 'r', 'e', 'a', 't'], none⟩]⟩, ⟨['d', 'o', 'ž', 'i', 'v', 'e', 'o'], ['l', 'i', 'v', 'e', 'd', '.', 't', 'o'], [⟨['d', 'o', 'ž', 'i', 'v', 'e', 'o'], ['l', 'i', 'v', 'e', 'd', '.', 't', 'o'], none⟩]⟩, ⟨['8', '0'], ['8', '0'], [⟨['8', '0'], ['8', '0'], none⟩]⟩, ⟨['g', 'o', 'd', 'i', 'n', 'u'], ['y', 'e', 'a', 'r', 's'], [⟨['g', 'o', 'd', 'i', 'n', 'u'], ['y', 'e', 'a', 'r', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "clauseInitialParticle"), ("polarity", "positive"), ("label", "je+liPPQ"), ("particle", "je li")] }

def ex31c : Datum :=
  { id := "simik2024_ex31c"
    source := ⟨"simik-2024", "ex. 31c"⟩
    reportedIn := none
    method := some .elicitation
    language := "serb1264"
    primaryText := "Nije li Justinijan I/Veliki doživeo 80 godinu?"
    glossedTokens := [("Nije", "NEG.is.AUX"), ("li", "LI"), ("Justinijan", "Justinian"), ("I/Veliki", "I/Great"), ("doživeo", "lived.to"), ("80", "80"), ("godinu", "years")]
    glossedWords := [⟨['N', 'i', 'j', 'e'], ['N', 'E', 'G', '.', 'i', 's', '.', 'A', 'U', 'X'], [⟨['N', 'i', 'j', 'e'], ['N', 'E', 'G', '.', 'i', 's', '.', 'A', 'U', 'X'], none⟩]⟩, ⟨['l', 'i'], ['L', 'I'], [⟨['l', 'i'], ['L', 'I'], none⟩]⟩, ⟨['J', 'u', 's', 't', 'i', 'n', 'i', 'j', 'a', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], [⟨['J', 'u', 's', 't', 'i', 'n', 'i', 'j', 'a', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], none⟩]⟩, ⟨['I', '/', 'V', 'e', 'l', 'i', 'k', 'i'], ['I', '/', 'G', 'r', 'e', 'a', 't'], [⟨['I', '/', 'V', 'e', 'l', 'i', 'k', 'i'], ['I', '/', 'G', 'r', 'e', 'a', 't'], none⟩]⟩, ⟨['d', 'o', 'ž', 'i', 'v', 'e', 'o'], ['l', 'i', 'v', 'e', 'd', '.', 't', 'o'], [⟨['d', 'o', 'ž', 'i', 'v', 'e', 'o'], ['l', 'i', 'v', 'e', 'd', '.', 't', 'o'], none⟩]⟩, ⟨['8', '0'], ['8', '0'], [⟨['8', '0'], ['8', '0'], none⟩]⟩, ⟨['g', 'o', 'd', 'i', 'n', 'u'], ['y', 'e', 'a', 'r', 's'], [⟨['g', 'o', 'd', 'i', 'n', 'u'], ['y', 'e', 'a', 'r', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "verbAttachedParticle"), ("strategy", "verbMovement"), ("polarity", "negative"), ("label", "HighNPQ"), ("particle", "li")] }

def ex31d : Datum :=
  { id := "simik2024_ex31d"
    source := ⟨"simik-2024", "ex. 31d"⟩
    reportedIn := none
    method := some .elicitation
    language := "serb1264"
    primaryText := "Je l' Justinijan I/Veliki nije doživeo 80 godinu?"
    glossedTokens := []
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "clauseInitialParticle"), ("polarity", "negative"), ("label", "LowNPQ"), ("particle", "je li")] }

def ex31e : Datum :=
  { id := "simik2024_ex31e"
    source := ⟨"simik-2024", "ex. 31e"⟩
    reportedIn := none
    method := some .elicitation
    language := "serb1264"
    primaryText := "Justinijan I/Veliki je doživeo 80 godinu?"
    glossedTokens := []
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "declarative"), ("polarity", "positive"), ("label", "DeclPQ")] }

def ex31e_neg : Datum :=
  { id := "simik2024_ex31e_neg"
    source := ⟨"simik-2024", "ex. 31e_neg"⟩
    reportedIn := none
    method := some .elicitation
    language := "serb1264"
    primaryText := "Justinijan I/Veliki nije doživeo 80 godinu?"
    glossedTokens := []
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "declarative"), ("polarity", "negative"), ("label", "DeclPQ")] }

def ex32a : Datum :=
  { id := "simik2024_ex32a"
    source := ⟨"simik-2024", "ex. 32a"⟩
    reportedIn := none
    method := some .elicitation
    language := "mace1250"
    primaryText := "Dali Justinijan Veliki doživeal 80-godišna vozrast?"
    glossedTokens := [("Dali", "DALI"), ("Justinijan", "Justinian"), ("Veliki", "Great"), ("doživeal", "lived.to"), ("80-godišna", "80-yearly"), ("vozrast", "age")]
    glossedWords := [⟨['D', 'a', 'l', 'i'], ['D', 'A', 'L', 'I'], [⟨['D', 'a', 'l', 'i'], ['D', 'A', 'L', 'I'], none⟩]⟩, ⟨['J', 'u', 's', 't', 'i', 'n', 'i', 'j', 'a', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], [⟨['J', 'u', 's', 't', 'i', 'n', 'i', 'j', 'a', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], none⟩]⟩, ⟨['V', 'e', 'l', 'i', 'k', 'i'], ['G', 'r', 'e', 'a', 't'], [⟨['V', 'e', 'l', 'i', 'k', 'i'], ['G', 'r', 'e', 'a', 't'], none⟩]⟩, ⟨['d', 'o', 'ž', 'i', 'v', 'e', 'a', 'l'], ['l', 'i', 'v', 'e', 'd', '.', 't', 'o'], [⟨['d', 'o', 'ž', 'i', 'v', 'e', 'a', 'l'], ['l', 'i', 'v', 'e', 'd', '.', 't', 'o'], none⟩]⟩, ⟨['8', '0', '-', 'g', 'o', 'd', 'i', 'š', 'n', 'a'], ['8', '0', '-', 'y', 'e', 'a', 'r', 'l', 'y'], [⟨['8', '0'], ['8', '0'], none⟩, ⟨['g', 'o', 'd', 'i', 'š', 'n', 'a'], ['y', 'e', 'a', 'r', 'l', 'y'], some '-'⟩]⟩, ⟨['v', 'o', 'z', 'r', 'a', 's', 't'], ['a', 'g', 'e'], [⟨['v', 'o', 'z', 'r', 'a', 's', 't'], ['a', 'g', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "clauseInitialParticle"), ("polarity", "positive"), ("label", "daliPQ"), ("particle", "dali")] }

def ex32a_neg : Datum :=
  { id := "simik2024_ex32a_neg"
    source := ⟨"simik-2024", "ex. 32a_neg"⟩
    reportedIn := none
    method := some .elicitation
    language := "mace1250"
    primaryText := "Dali Justinijan Veliki ne doživeal 80-godišna vozrast?"
    glossedTokens := [("Dali", "DALI"), ("Justinijan", "Justinian"), ("Veliki", "Great"), ("ne", "NEG"), ("doživeal", "lived.to"), ("80-godišna", "80-yearly"), ("vozrast", "age")]
    glossedWords := [⟨['D', 'a', 'l', 'i'], ['D', 'A', 'L', 'I'], [⟨['D', 'a', 'l', 'i'], ['D', 'A', 'L', 'I'], none⟩]⟩, ⟨['J', 'u', 's', 't', 'i', 'n', 'i', 'j', 'a', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], [⟨['J', 'u', 's', 't', 'i', 'n', 'i', 'j', 'a', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], none⟩]⟩, ⟨['V', 'e', 'l', 'i', 'k', 'i'], ['G', 'r', 'e', 'a', 't'], [⟨['V', 'e', 'l', 'i', 'k', 'i'], ['G', 'r', 'e', 'a', 't'], none⟩]⟩, ⟨['n', 'e'], ['N', 'E', 'G'], [⟨['n', 'e'], ['N', 'E', 'G'], none⟩]⟩, ⟨['d', 'o', 'ž', 'i', 'v', 'e', 'a', 'l'], ['l', 'i', 'v', 'e', 'd', '.', 't', 'o'], [⟨['d', 'o', 'ž', 'i', 'v', 'e', 'a', 'l'], ['l', 'i', 'v', 'e', 'd', '.', 't', 'o'], none⟩]⟩, ⟨['8', '0', '-', 'g', 'o', 'd', 'i', 'š', 'n', 'a'], ['8', '0', '-', 'y', 'e', 'a', 'r', 'l', 'y'], [⟨['8', '0'], ['8', '0'], none⟩, ⟨['g', 'o', 'd', 'i', 'š', 'n', 'a'], ['y', 'e', 'a', 'r', 'l', 'y'], some '-'⟩]⟩, ⟨['v', 'o', 'z', 'r', 'a', 's', 't'], ['a', 'g', 'e'], [⟨['v', 'o', 'z', 'r', 'a', 's', 't'], ['a', 'g', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "clauseInitialParticle"), ("polarity", "negative"), ("label", "daliPQ"), ("particle", "dali")] }

def ex32b : Datum :=
  { id := "simik2024_ex32b"
    source := ⟨"simik-2024", "ex. 32b"⟩
    reportedIn := none
    method := some .elicitation
    language := "mace1250"
    primaryText := "Doživeal li Justinijan Veliki 80-godišna vozrast?"
    glossedTokens := [("Doživeal", "lived.to"), ("li", "LI"), ("Justinijan", "Justinian"), ("Veliki", "Great"), ("80-godišna", "80-yearly"), ("vozrast", "age")]
    glossedWords := [⟨['D', 'o', 'ž', 'i', 'v', 'e', 'a', 'l'], ['l', 'i', 'v', 'e', 'd', '.', 't', 'o'], [⟨['D', 'o', 'ž', 'i', 'v', 'e', 'a', 'l'], ['l', 'i', 'v', 'e', 'd', '.', 't', 'o'], none⟩]⟩, ⟨['l', 'i'], ['L', 'I'], [⟨['l', 'i'], ['L', 'I'], none⟩]⟩, ⟨['J', 'u', 's', 't', 'i', 'n', 'i', 'j', 'a', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], [⟨['J', 'u', 's', 't', 'i', 'n', 'i', 'j', 'a', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], none⟩]⟩, ⟨['V', 'e', 'l', 'i', 'k', 'i'], ['G', 'r', 'e', 'a', 't'], [⟨['V', 'e', 'l', 'i', 'k', 'i'], ['G', 'r', 'e', 'a', 't'], none⟩]⟩, ⟨['8', '0', '-', 'g', 'o', 'd', 'i', 'š', 'n', 'a'], ['8', '0', '-', 'y', 'e', 'a', 'r', 'l', 'y'], [⟨['8', '0'], ['8', '0'], none⟩, ⟨['g', 'o', 'd', 'i', 'š', 'n', 'a'], ['y', 'e', 'a', 'r', 'l', 'y'], some '-'⟩]⟩, ⟨['v', 'o', 'z', 'r', 'a', 's', 't'], ['a', 'g', 'e'], [⟨['v', 'o', 'z', 'r', 'a', 's', 't'], ['a', 'g', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "verbAttachedParticle"), ("strategy", "verbMovement"), ("polarity", "positive"), ("label", "liPQ"), ("particle", "li")] }

def ex32b_neg : Datum :=
  { id := "simik2024_ex32b_neg"
    source := ⟨"simik-2024", "ex. 32b_neg"⟩
    reportedIn := none
    method := some .elicitation
    language := "mace1250"
    primaryText := "Ne doživeal li Justinijan Veliki 80-godišna vozrast?"
    glossedTokens := []
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "verbAttachedParticle"), ("strategy", "verbMovement"), ("polarity", "negative"), ("label", "liPQ"), ("particle", "li")] }

def ex32c : Datum :=
  { id := "simik2024_ex32c"
    source := ⟨"simik-2024", "ex. 32c"⟩
    reportedIn := none
    method := some .elicitation
    language := "mace1250"
    primaryText := "Doživeal Justinijan Veliki 80-godišna vozrast?"
    glossedTokens := []
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "verbMovement"), ("polarity", "positive"), ("label", "v1PQ")] }

def ex32c_neg : Datum :=
  { id := "simik2024_ex32c_neg"
    source := ⟨"simik-2024", "ex. 32c_neg"⟩
    reportedIn := none
    method := some .elicitation
    language := "mace1250"
    primaryText := "Ne doživeal Justinijan Veliki 80-godišna vozrast?"
    glossedTokens := []
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "verbMovement"), ("polarity", "negative"), ("label", "v1PQ")] }

def ex33a : Datum :=
  { id := "simik2024_ex33a"
    source := ⟨"simik-2024", "ex. 33a"⟩
    reportedIn := none
    method := some .elicitation
    language := "bulg1262"
    primaryText := "Justinian doživjava li do 80-godišna vŭzrast?"
    glossedTokens := [("Justinian", "Justinian"), ("doživjava", "lives"), ("li", "LI"), ("do", "to"), ("80-godišna", "80-yearly"), ("vŭzrast", "age")]
    glossedWords := [⟨['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], [⟨['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], none⟩]⟩, ⟨['d', 'o', 'ž', 'i', 'v', 'j', 'a', 'v', 'a'], ['l', 'i', 'v', 'e', 's'], [⟨['d', 'o', 'ž', 'i', 'v', 'j', 'a', 'v', 'a'], ['l', 'i', 'v', 'e', 's'], none⟩]⟩, ⟨['l', 'i'], ['L', 'I'], [⟨['l', 'i'], ['L', 'I'], none⟩]⟩, ⟨['d', 'o'], ['t', 'o'], [⟨['d', 'o'], ['t', 'o'], none⟩]⟩, ⟨['8', '0', '-', 'g', 'o', 'd', 'i', 'š', 'n', 'a'], ['8', '0', '-', 'y', 'e', 'a', 'r', 'l', 'y'], [⟨['8', '0'], ['8', '0'], none⟩, ⟨['g', 'o', 'd', 'i', 'š', 'n', 'a'], ['y', 'e', 'a', 'r', 'l', 'y'], some '-'⟩]⟩, ⟨['v', 'ŭ', 'z', 'r', 'a', 's', 't'], ['a', 'g', 'e'], [⟨['v', 'ŭ', 'z', 'r', 'a', 's', 't'], ['a', 'g', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "verbAttachedParticle"), ("polarity", "positive"), ("label", "liPPQ"), ("particle", "li")] }

def ex33b : Datum :=
  { id := "simik2024_ex33b"
    source := ⟨"simik-2024", "ex. 33b"⟩
    reportedIn := none
    method := some .elicitation
    language := "bulg1262"
    primaryText := "Justinian ne doživjava li do 80-godišna vŭzrast?"
    glossedTokens := []
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "verbAttachedParticle"), ("polarity", "negative"), ("label", "liNPQ"), ("particle", "li")] }

def ex33c : Datum :=
  { id := "simik2024_ex33c"
    source := ⟨"simik-2024", "ex. 33c"⟩
    reportedIn := none
    method := some .elicitation
    language := "bulg1262"
    primaryText := "Justinian doživjava do 80-godišna vŭzrast?"
    glossedTokens := []
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "declarative"), ("polarity", "positive"), ("label", "DeclPQ")] }

def ex33c_neg : Datum :=
  { id := "simik2024_ex33c_neg"
    source := ⟨"simik-2024", "ex. 33c_neg"⟩
    reportedIn := none
    method := some .elicitation
    language := "bulg1262"
    primaryText := "Justinian ne doživjava do 80-godišna vŭzrast?"
    glossedTokens := []
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "declarative"), ("polarity", "negative"), ("label", "DeclPQ")] }

def ex34a : Datum :=
  { id := "simik2024_ex34a"
    source := ⟨"simik-2024", "ex. 34a"⟩
    reportedIn := none
    method := some .elicitation
    language := "russ1263"
    primaryText := "Dožil li Justinian Velikij do 80 let?"
    glossedTokens := [("Dožil", "lived.to"), ("li", "LI"), ("Justinian", "Justinian"), ("Velikij", "Great"), ("do", "to"), ("80", "80"), ("let", "years")]
    glossedWords := [⟨['D', 'o', 'ž', 'i', 'l'], ['l', 'i', 'v', 'e', 'd', '.', 't', 'o'], [⟨['D', 'o', 'ž', 'i', 'l'], ['l', 'i', 'v', 'e', 'd', '.', 't', 'o'], none⟩]⟩, ⟨['l', 'i'], ['L', 'I'], [⟨['l', 'i'], ['L', 'I'], none⟩]⟩, ⟨['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], [⟨['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], ['J', 'u', 's', 't', 'i', 'n', 'i', 'a', 'n'], none⟩]⟩, ⟨['V', 'e', 'l', 'i', 'k', 'i', 'j'], ['G', 'r', 'e', 'a', 't'], [⟨['V', 'e', 'l', 'i', 'k', 'i', 'j'], ['G', 'r', 'e', 'a', 't'], none⟩]⟩, ⟨['d', 'o'], ['t', 'o'], [⟨['d', 'o'], ['t', 'o'], none⟩]⟩, ⟨['8', '0'], ['8', '0'], [⟨['8', '0'], ['8', '0'], none⟩]⟩, ⟨['l', 'e', 't'], ['y', 'e', 'a', 'r', 's'], [⟨['l', 'e', 't'], ['y', 'e', 'a', 'r', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "verbAttachedParticle"), ("polarity", "positive"), ("label", "liPPQ"), ("particle", "li")] }

def ex34b : Datum :=
  { id := "simik2024_ex34b"
    source := ⟨"simik-2024", "ex. 34b"⟩
    reportedIn := none
    method := some .elicitation
    language := "russ1263"
    primaryText := "Ne dožil li Justinian Velikij do 80 let?"
    glossedTokens := []
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "verbAttachedParticle"), ("polarity", "negative"), ("label", "liNPQ"), ("particle", "li")] }

def ex34c : Datum :=
  { id := "simik2024_ex34c"
    source := ⟨"simik-2024", "ex. 34c"⟩
    reportedIn := none
    method := some .elicitation
    language := "russ1263"
    primaryText := "Justinian Velikij dožil do 80 let?"
    glossedTokens := []
    context := "Scenario (24): a TV quiz moderator asks the following polar question, expecting a simple 'yes' or 'no' answer."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("scenario", "24"), ("strategy", "intonation"), ("polarity", "positive"), ("label", "IntonPQ")] }

def ex43c_ppi : Datum :=
  { id := "simik2024_ex43c_ppi"
    source := ⟨"simik-2024", "ex. 43c"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Nemá Max nějaké námitky?"
    glossedTokens := [("Nemá", "NEG.has"), ("Max", "Max"), ("nějaké", "DET.PPI"), ("námitky", "objections")]
    glossedWords := [⟨['N', 'e', 'm', 'á'], ['N', 'E', 'G', '.', 'h', 'a', 's'], [⟨['N', 'e', 'm', 'á'], ['N', 'E', 'G', '.', 'h', 'a', 's'], none⟩]⟩, ⟨['M', 'a', 'x'], ['M', 'a', 'x'], [⟨['M', 'a', 'x'], ['M', 'a', 'x'], none⟩]⟩, ⟨['n', 'ě', 'j', 'a', 'k', 'é'], ['D', 'E', 'T', '.', 'P', 'P', 'I'], [⟨['n', 'ě', 'j', 'a', 'k', 'é'], ['D', 'E', 'T', '.', 'P', 'P', 'I'], none⟩]⟩, ⟨['n', 'á', 'm', 'i', 't', 'k', 'y'], ['o', 'b', 'j', 'e', 'c', 't', 'i', 'o', 'n', 's'], [⟨['n', 'á', 'm', 'i', 't', 'k', 'y'], ['o', 'b', 'j', 'e', 'c', 't', 'i', 'o', 'n', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("indefinite", "ppi")] }

def ex43c_nci : Datum :=
  { id := "simik2024_ex43c_nci"
    source := ⟨"simik-2024", "ex. 43c"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Nemá Max žádné námitky?"
    glossedTokens := [("Nemá", "NEG.has"), ("Max", "Max"), ("žádné", "NEG.NCI"), ("námitky", "objections")]
    glossedWords := [⟨['N', 'e', 'm', 'á'], ['N', 'E', 'G', '.', 'h', 'a', 's'], [⟨['N', 'e', 'm', 'á'], ['N', 'E', 'G', '.', 'h', 'a', 's'], none⟩]⟩, ⟨['M', 'a', 'x'], ['M', 'a', 'x'], [⟨['M', 'a', 'x'], ['M', 'a', 'x'], none⟩]⟩, ⟨['ž', 'á', 'd', 'n', 'é'], ['N', 'E', 'G', '.', 'N', 'C', 'I'], [⟨['ž', 'á', 'd', 'n', 'é'], ['N', 'E', 'G', '.', 'N', 'C', 'I'], none⟩]⟩, ⟨['n', 'á', 'm', 'i', 't', 'k', 'y'], ['o', 'b', 'j', 'e', 'c', 't', 'i', 'o', 'n', 's'], [⟨['n', 'á', 'm', 'i', 't', 'k', 'y'], ['o', 'b', 'j', 'e', 'c', 't', 'i', 'o', 'n', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("indefinite", "nci")] }

def ex43d_ppi : Datum :=
  { id := "simik2024_ex43d_ppi"
    source := ⟨"simik-2024", "ex. 43d"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Nemá Max náhodou nějaké námitky?"
    glossedTokens := [("Nemá", "NEG.has"), ("Max", "Max"), ("náhodou", "by.chance"), ("nějaké", "DET.PPI"), ("námitky", "objections")]
    glossedWords := [⟨['N', 'e', 'm', 'á'], ['N', 'E', 'G', '.', 'h', 'a', 's'], [⟨['N', 'e', 'm', 'á'], ['N', 'E', 'G', '.', 'h', 'a', 's'], none⟩]⟩, ⟨['M', 'a', 'x'], ['M', 'a', 'x'], [⟨['M', 'a', 'x'], ['M', 'a', 'x'], none⟩]⟩, ⟨['n', 'á', 'h', 'o', 'd', 'o', 'u'], ['b', 'y', '.', 'c', 'h', 'a', 'n', 'c', 'e'], [⟨['n', 'á', 'h', 'o', 'd', 'o', 'u'], ['b', 'y', '.', 'c', 'h', 'a', 'n', 'c', 'e'], none⟩]⟩, ⟨['n', 'ě', 'j', 'a', 'k', 'é'], ['D', 'E', 'T', '.', 'P', 'P', 'I'], [⟨['n', 'ě', 'j', 'a', 'k', 'é'], ['D', 'E', 'T', '.', 'P', 'P', 'I'], none⟩]⟩, ⟨['n', 'á', 'm', 'i', 't', 'k', 'y'], ['o', 'b', 'j', 'e', 'c', 't', 'i', 'o', 'n', 's'], [⟨['n', 'á', 'm', 'i', 't', 'k', 'y'], ['o', 'b', 'j', 'e', 'c', 't', 'i', 'o', 'n', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("particle", "náhodou"), ("indefinite", "ppi")] }

def ex43d_nci : Datum :=
  { id := "simik2024_ex43d_nci"
    source := ⟨"simik-2024", "ex. 43d"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Nemá Max náhodou žádné námitky?"
    glossedTokens := [("Nemá", "NEG.has"), ("Max", "Max"), ("náhodou", "by.chance"), ("žádné", "NEG.NCI"), ("námitky", "objections")]
    glossedWords := [⟨['N', 'e', 'm', 'á'], ['N', 'E', 'G', '.', 'h', 'a', 's'], [⟨['N', 'e', 'm', 'á'], ['N', 'E', 'G', '.', 'h', 'a', 's'], none⟩]⟩, ⟨['M', 'a', 'x'], ['M', 'a', 'x'], [⟨['M', 'a', 'x'], ['M', 'a', 'x'], none⟩]⟩, ⟨['n', 'á', 'h', 'o', 'd', 'o', 'u'], ['b', 'y', '.', 'c', 'h', 'a', 'n', 'c', 'e'], [⟨['n', 'á', 'h', 'o', 'd', 'o', 'u'], ['b', 'y', '.', 'c', 'h', 'a', 'n', 'c', 'e'], none⟩]⟩, ⟨['ž', 'á', 'd', 'n', 'é'], ['N', 'E', 'G', '.', 'N', 'C', 'I'], [⟨['ž', 'á', 'd', 'n', 'é'], ['N', 'E', 'G', '.', 'N', 'C', 'I'], none⟩]⟩, ⟨['n', 'á', 'm', 'i', 't', 'k', 'y'], ['o', 'b', 'j', 'e', 'c', 't', 'i', 'o', 'n', 's'], [⟨['n', 'á', 'm', 'i', 't', 'k', 'y'], ['o', 'b', 'j', 'e', 'c', 't', 'i', 'o', 'n', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("particle", "náhodou"), ("indefinite", "nci")] }

def ex43e : Datum :=
  { id := "simik2024_ex43e"
    source := ⟨"simik-2024", "ex. 43e"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Má Max náhodou nějaké námitky?"
    glossedTokens := [("Má", "has"), ("Max", "Max"), ("náhodou", "by.chance"), ("nějaké", "DET.PPI"), ("námitky", "objections")]
    glossedWords := [⟨['M', 'á'], ['h', 'a', 's'], [⟨['M', 'á'], ['h', 'a', 's'], none⟩]⟩, ⟨['M', 'a', 'x'], ['M', 'a', 'x'], [⟨['M', 'a', 'x'], ['M', 'a', 'x'], none⟩]⟩, ⟨['n', 'á', 'h', 'o', 'd', 'o', 'u'], ['b', 'y', '.', 'c', 'h', 'a', 'n', 'c', 'e'], [⟨['n', 'á', 'h', 'o', 'd', 'o', 'u'], ['b', 'y', '.', 'c', 'h', 'a', 'n', 'c', 'e'], none⟩]⟩, ⟨['n', 'ě', 'j', 'a', 'k', 'é'], ['D', 'E', 'T', '.', 'P', 'P', 'I'], [⟨['n', 'ě', 'j', 'a', 'k', 'é'], ['D', 'E', 'T', '.', 'P', 'P', 'I'], none⟩]⟩, ⟨['n', 'á', 'm', 'i', 't', 'k', 'y'], ['o', 'b', 'j', 'e', 'c', 't', 'i', 'o', 'n', 's'], [⟨['n', 'á', 'm', 'i', 't', 'k', 'y'], ['o', 'b', 'j', 'e', 'c', 't', 'i', 'o', 'n', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("particle", "náhodou"), ("indefinite", "ppi")] }

def all : List Datum := [ex11a, ex11b, ex11c, ex11c_neg, ex12a, ex12b, ex12c, ex12c_neg, ex16a, ex16b, ex16c, ex16d, ex17a, ex17b, ex17c, ex17d, ex18a, ex18b, ex18c, ex18d, ex25a, ex25b, ex25c, ex25c_neg, ex26a, ex26b, ex26c, ex26c_neg, ex27a, ex27b, ex27c, ex27c_neg, ex28a, ex28b, ex28c, ex28c_neg, ex29a, ex29b, ex29c, ex29d, ex29e, ex29e_neg, ex30a, ex30b, ex30c, ex30c_neg, ex30d, ex30d_neg, ex31a, ex31b, ex31c, ex31d, ex31e, ex31e_neg, ex32a, ex32a_neg, ex32b, ex32b_neg, ex32c, ex32c_neg, ex33a, ex33b, ex33c, ex33c_neg, ex34a, ex34b, ex34c, ex43c_ppi, ex43c_nci, ex43d_ppi, ex43d_nci, ex43e]

/-- The scenario a question is judged in. -/
inductive Scenario where
  /-- 11: (11): A ticks off the floor Marek was responsible for -/
  | plan
  /-- 12: (12): A had privately asked Marek to clean the third floor as well -/
  | request
  /-- 16: (16): B reports that Marek cleaned the second floor, and A believed he was responsible for the third -/
  | report
  /-- 17: (17): A, who does not know the cleaning plan, finds an earbud like Marek's on the third floor -/
  | earbud
  /-- 18: (18): after a chat about Lucie and Marek, A asks who cleaned which floor, with Marek a contrastive topic -/
  | newCleaners
  /-- 24: (24): a television quiz moderator asks the question, expecting 'yes' or 'no' -/
  | quiz
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `scenario`. -/
def scenario (e : Datum) : Option Scenario :=
  e.parse? "scenario" [("11", .plan), ("12", .request), ("16", .report), ("17", .earbud), ("18", .newCleaners),
    ("24", .quiz)]

/-- The formal means that mark a polar question. -/
inductive Strategy where
  /-- verbMovement: the finite verb or auxiliary precedes the subject -/
  | verbMovement
  /-- clauseInitialParticle: an utterance-initial question particle -/
  | clauseInitialParticle
  /-- verbAttachedParticle: the particle *li* after the verb or the focused constituent -/
  | verbAttachedParticle
  /-- declarative: declarative word order with no particle -/
  | declarative
  /-- intonation: declarative word order with the pitch accent of a Russian polar question -/
  | intonation
  deriving DecidableEq, Repr, Fintype

/-- The values a row records under `strategy`. -/
def strategy (e : Datum) : List Strategy :=
  (e.features "strategy").filterMap (List.lookup · [("verbMovement", .verbMovement), ("clauseInitialParticle", .clauseInitialParticle),
    ("verbAttachedParticle", .verbAttachedParticle), ("declarative", .declarative),
    ("intonation", .intonation)])

/-- Whether the finite verb of the question is negated. -/
inductive QuestionPolarity where
  /-- positive: an affirmative finite verb -/
  | positive
  /-- negative: a finite verb with the negative prefix or proclitic -/
  | negative
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `polarity`. -/
def polarity (e : Datum) : Option QuestionPolarity :=
  e.parse? "polarity" [("positive", .positive), ("negative", .negative)]

/-- The indefinite determiner of the object in (43). -/
inductive Indefinite where
  /-- ppi: the positive polarity item *nějaký* 'some' -/
  | ppi
  /-- nci: the negative concord item *žádný* 'no' -/
  | nci
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `indefinite`. -/
def indefinite (e : Datum) : Option Indefinite :=
  e.parse? "indefinite" [("ppi", .ppi), ("nci", .nci)]

/-- The examples of the file. -/
inductive Example where
  | ex11a
  | ex11b
  | ex11c
  | ex11c_neg
  | ex12a
  | ex12b
  | ex12c
  | ex12c_neg
  | ex16a
  | ex16b
  | ex16c
  | ex16d
  | ex17a
  | ex17b
  | ex17c
  | ex17d
  | ex18a
  | ex18b
  | ex18c
  | ex18d
  | ex25a
  | ex25b
  | ex25c
  | ex25c_neg
  | ex26a
  | ex26b
  | ex26c
  | ex26c_neg
  | ex27a
  | ex27b
  | ex27c
  | ex27c_neg
  | ex28a
  | ex28b
  | ex28c
  | ex28c_neg
  | ex29a
  | ex29b
  | ex29c
  | ex29d
  | ex29e
  | ex29e_neg
  | ex30a
  | ex30b
  | ex30c
  | ex30c_neg
  | ex30d
  | ex30d_neg
  | ex31a
  | ex31b
  | ex31c
  | ex31d
  | ex31e
  | ex31e_neg
  | ex32a
  | ex32a_neg
  | ex32b
  | ex32b_neg
  | ex32c
  | ex32c_neg
  | ex33a
  | ex33b
  | ex33c
  | ex33c_neg
  | ex34a
  | ex34b
  | ex34c
  | ex43c_ppi
  | ex43c_nci
  | ex43d_ppi
  | ex43d_nci
  | ex43e
  deriving DecidableEq, Repr, Fintype

/-- Every example of the file, in its order. -/
def Example.all : List Example :=
  [.ex11a, .ex11b, .ex11c, .ex11c_neg, .ex12a, .ex12b, .ex12c, .ex12c_neg, .ex16a, .ex16b,
    .ex16c, .ex16d, .ex17a, .ex17b, .ex17c, .ex17d, .ex18a, .ex18b, .ex18c, .ex18d, .ex25a,
    .ex25b, .ex25c, .ex25c_neg, .ex26a, .ex26b, .ex26c, .ex26c_neg, .ex27a, .ex27b, .ex27c,
    .ex27c_neg, .ex28a, .ex28b, .ex28c, .ex28c_neg, .ex29a, .ex29b, .ex29c, .ex29d, .ex29e,
    .ex29e_neg, .ex30a, .ex30b, .ex30c, .ex30c_neg, .ex30d, .ex30d_neg, .ex31a, .ex31b, .ex31c,
    .ex31d, .ex31e, .ex31e_neg, .ex32a, .ex32a_neg, .ex32b, .ex32b_neg, .ex32c, .ex32c_neg,
    .ex33a, .ex33b, .ex33c, .ex33c_neg, .ex34a, .ex34b, .ex34c, .ex43c_ppi, .ex43c_nci,
    .ex43d_ppi, .ex43d_nci, .ex43e]

/-- The row of an example. -/
def Example.datum : Example → Datum
  | .ex11a => _root_.Simik2024.Examples.ex11a
  | .ex11b => _root_.Simik2024.Examples.ex11b
  | .ex11c => _root_.Simik2024.Examples.ex11c
  | .ex11c_neg => _root_.Simik2024.Examples.ex11c_neg
  | .ex12a => _root_.Simik2024.Examples.ex12a
  | .ex12b => _root_.Simik2024.Examples.ex12b
  | .ex12c => _root_.Simik2024.Examples.ex12c
  | .ex12c_neg => _root_.Simik2024.Examples.ex12c_neg
  | .ex16a => _root_.Simik2024.Examples.ex16a
  | .ex16b => _root_.Simik2024.Examples.ex16b
  | .ex16c => _root_.Simik2024.Examples.ex16c
  | .ex16d => _root_.Simik2024.Examples.ex16d
  | .ex17a => _root_.Simik2024.Examples.ex17a
  | .ex17b => _root_.Simik2024.Examples.ex17b
  | .ex17c => _root_.Simik2024.Examples.ex17c
  | .ex17d => _root_.Simik2024.Examples.ex17d
  | .ex18a => _root_.Simik2024.Examples.ex18a
  | .ex18b => _root_.Simik2024.Examples.ex18b
  | .ex18c => _root_.Simik2024.Examples.ex18c
  | .ex18d => _root_.Simik2024.Examples.ex18d
  | .ex25a => _root_.Simik2024.Examples.ex25a
  | .ex25b => _root_.Simik2024.Examples.ex25b
  | .ex25c => _root_.Simik2024.Examples.ex25c
  | .ex25c_neg => _root_.Simik2024.Examples.ex25c_neg
  | .ex26a => _root_.Simik2024.Examples.ex26a
  | .ex26b => _root_.Simik2024.Examples.ex26b
  | .ex26c => _root_.Simik2024.Examples.ex26c
  | .ex26c_neg => _root_.Simik2024.Examples.ex26c_neg
  | .ex27a => _root_.Simik2024.Examples.ex27a
  | .ex27b => _root_.Simik2024.Examples.ex27b
  | .ex27c => _root_.Simik2024.Examples.ex27c
  | .ex27c_neg => _root_.Simik2024.Examples.ex27c_neg
  | .ex28a => _root_.Simik2024.Examples.ex28a
  | .ex28b => _root_.Simik2024.Examples.ex28b
  | .ex28c => _root_.Simik2024.Examples.ex28c
  | .ex28c_neg => _root_.Simik2024.Examples.ex28c_neg
  | .ex29a => _root_.Simik2024.Examples.ex29a
  | .ex29b => _root_.Simik2024.Examples.ex29b
  | .ex29c => _root_.Simik2024.Examples.ex29c
  | .ex29d => _root_.Simik2024.Examples.ex29d
  | .ex29e => _root_.Simik2024.Examples.ex29e
  | .ex29e_neg => _root_.Simik2024.Examples.ex29e_neg
  | .ex30a => _root_.Simik2024.Examples.ex30a
  | .ex30b => _root_.Simik2024.Examples.ex30b
  | .ex30c => _root_.Simik2024.Examples.ex30c
  | .ex30c_neg => _root_.Simik2024.Examples.ex30c_neg
  | .ex30d => _root_.Simik2024.Examples.ex30d
  | .ex30d_neg => _root_.Simik2024.Examples.ex30d_neg
  | .ex31a => _root_.Simik2024.Examples.ex31a
  | .ex31b => _root_.Simik2024.Examples.ex31b
  | .ex31c => _root_.Simik2024.Examples.ex31c
  | .ex31d => _root_.Simik2024.Examples.ex31d
  | .ex31e => _root_.Simik2024.Examples.ex31e
  | .ex31e_neg => _root_.Simik2024.Examples.ex31e_neg
  | .ex32a => _root_.Simik2024.Examples.ex32a
  | .ex32a_neg => _root_.Simik2024.Examples.ex32a_neg
  | .ex32b => _root_.Simik2024.Examples.ex32b
  | .ex32b_neg => _root_.Simik2024.Examples.ex32b_neg
  | .ex32c => _root_.Simik2024.Examples.ex32c
  | .ex32c_neg => _root_.Simik2024.Examples.ex32c_neg
  | .ex33a => _root_.Simik2024.Examples.ex33a
  | .ex33b => _root_.Simik2024.Examples.ex33b
  | .ex33c => _root_.Simik2024.Examples.ex33c
  | .ex33c_neg => _root_.Simik2024.Examples.ex33c_neg
  | .ex34a => _root_.Simik2024.Examples.ex34a
  | .ex34b => _root_.Simik2024.Examples.ex34b
  | .ex34c => _root_.Simik2024.Examples.ex34c
  | .ex43c_ppi => _root_.Simik2024.Examples.ex43c_ppi
  | .ex43c_nci => _root_.Simik2024.Examples.ex43c_nci
  | .ex43d_ppi => _root_.Simik2024.Examples.ex43d_ppi
  | .ex43d_nci => _root_.Simik2024.Examples.ex43d_nci
  | .ex43e => _root_.Simik2024.Examples.ex43e

theorem Example.map_datum_all :
    Example.all.map Example.datum = _root_.Simik2024.Examples.all := rfl

/-- The value the example records under `scenario`. -/
def Example.scenario : Example → Option Scenario
  | .ex11a => some .plan
  | .ex11b => some .plan
  | .ex11c => some .plan
  | .ex11c_neg => some .plan
  | .ex12a => some .request
  | .ex12b => some .request
  | .ex12c => some .request
  | .ex12c_neg => some .request
  | .ex16a => some .report
  | .ex16b => some .report
  | .ex16c => some .report
  | .ex16d => some .report
  | .ex17a => some .earbud
  | .ex17b => some .earbud
  | .ex17c => some .earbud
  | .ex17d => some .earbud
  | .ex18a => some .newCleaners
  | .ex18b => some .newCleaners
  | .ex18c => some .newCleaners
  | .ex18d => some .newCleaners
  | .ex25a => some .quiz
  | .ex25b => some .quiz
  | .ex25c => some .quiz
  | .ex25c_neg => some .quiz
  | .ex26a => some .quiz
  | .ex26b => some .quiz
  | .ex26c => some .quiz
  | .ex26c_neg => some .quiz
  | .ex27a => some .quiz
  | .ex27b => some .quiz
  | .ex27c => some .quiz
  | .ex27c_neg => some .quiz
  | .ex28a => some .quiz
  | .ex28b => some .quiz
  | .ex28c => some .quiz
  | .ex28c_neg => some .quiz
  | .ex29a => some .quiz
  | .ex29b => some .quiz
  | .ex29c => some .quiz
  | .ex29d => some .quiz
  | .ex29e => some .quiz
  | .ex29e_neg => some .quiz
  | .ex30a => some .quiz
  | .ex30b => some .quiz
  | .ex30c => some .quiz
  | .ex30c_neg => some .quiz
  | .ex30d => some .quiz
  | .ex30d_neg => some .quiz
  | .ex31a => some .quiz
  | .ex31b => some .quiz
  | .ex31c => some .quiz
  | .ex31d => some .quiz
  | .ex31e => some .quiz
  | .ex31e_neg => some .quiz
  | .ex32a => some .quiz
  | .ex32a_neg => some .quiz
  | .ex32b => some .quiz
  | .ex32b_neg => some .quiz
  | .ex32c => some .quiz
  | .ex32c_neg => some .quiz
  | .ex33a => some .quiz
  | .ex33b => some .quiz
  | .ex33c => some .quiz
  | .ex33c_neg => some .quiz
  | .ex34a => some .quiz
  | .ex34b => some .quiz
  | .ex34c => some .quiz
  | .ex43c_ppi => none
  | .ex43c_nci => none
  | .ex43d_ppi => none
  | .ex43d_nci => none
  | .ex43e => none

theorem Example.scenario_datum :
    ∀ x : Example, _root_.Simik2024.Examples.scenario x.datum = x.scenario := by
  decide +kernel

/-- The values the example records under `strategy`. -/
def Example.strategy : Example → List Strategy
  | .ex11a => [.verbMovement]
  | .ex11b => [.verbMovement]
  | .ex11c => [.declarative]
  | .ex11c_neg => [.declarative]
  | .ex12a => [.verbMovement]
  | .ex12b => [.verbMovement]
  | .ex12c => [.declarative]
  | .ex12c_neg => [.declarative]
  | .ex16a => [.verbMovement]
  | .ex16b => [.verbMovement]
  | .ex16c => [.declarative]
  | .ex16d => [.declarative]
  | .ex17a => [.verbMovement]
  | .ex17b => [.verbMovement]
  | .ex17c => [.declarative]
  | .ex17d => [.declarative]
  | .ex18a => [.verbMovement]
  | .ex18b => [.verbMovement]
  | .ex18c => [.declarative]
  | .ex18d => [.declarative]
  | .ex25a => [.verbMovement]
  | .ex25b => [.verbMovement]
  | .ex25c => [.declarative]
  | .ex25c_neg => [.declarative]
  | .ex26a => [.verbMovement]
  | .ex26b => [.verbMovement]
  | .ex26c => [.declarative]
  | .ex26c_neg => [.declarative]
  | .ex27a => [.verbMovement]
  | .ex27b => [.verbMovement]
  | .ex27c => [.declarative]
  | .ex27c_neg => [.declarative]
  | .ex28a => [.verbMovement, .clauseInitialParticle]
  | .ex28b => [.verbMovement, .clauseInitialParticle]
  | .ex28c => [.declarative]
  | .ex28c_neg => [.declarative]
  | .ex29a => [.clauseInitialParticle]
  | .ex29b => [.clauseInitialParticle]
  | .ex29c => [.clauseInitialParticle]
  | .ex29d => [.clauseInitialParticle]
  | .ex29e => [.declarative]
  | .ex29e_neg => [.declarative]
  | .ex30a => [.clauseInitialParticle]
  | .ex30b => [.clauseInitialParticle]
  | .ex30c => [.declarative]
  | .ex30c_neg => [.declarative]
  | .ex30d => [.verbMovement]
  | .ex30d_neg => [.verbMovement]
  | .ex31a => [.clauseInitialParticle]
  | .ex31b => [.clauseInitialParticle]
  | .ex31c => [.verbAttachedParticle, .verbMovement]
  | .ex31d => [.clauseInitialParticle]
  | .ex31e => [.declarative]
  | .ex31e_neg => [.declarative]
  | .ex32a => [.clauseInitialParticle]
  | .ex32a_neg => [.clauseInitialParticle]
  | .ex32b => [.verbAttachedParticle, .verbMovement]
  | .ex32b_neg => [.verbAttachedParticle, .verbMovement]
  | .ex32c => [.verbMovement]
  | .ex32c_neg => [.verbMovement]
  | .ex33a => [.verbAttachedParticle]
  | .ex33b => [.verbAttachedParticle]
  | .ex33c => [.declarative]
  | .ex33c_neg => [.declarative]
  | .ex34a => [.verbAttachedParticle]
  | .ex34b => [.verbAttachedParticle]
  | .ex34c => [.intonation]
  | .ex43c_ppi => []
  | .ex43c_nci => []
  | .ex43d_ppi => []
  | .ex43d_nci => []
  | .ex43e => []

theorem Example.strategy_datum :
    ∀ x : Example, _root_.Simik2024.Examples.strategy x.datum = x.strategy := by
  decide +kernel

/-- The value the example records under `polarity`. -/
def Example.polarity : Example → Option QuestionPolarity
  | .ex11a => some .positive
  | .ex11b => some .negative
  | .ex11c => some .positive
  | .ex11c_neg => some .negative
  | .ex12a => some .positive
  | .ex12b => some .negative
  | .ex12c => some .positive
  | .ex12c_neg => some .negative
  | .ex16a => some .positive
  | .ex16b => some .negative
  | .ex16c => some .positive
  | .ex16d => some .negative
  | .ex17a => some .positive
  | .ex17b => some .negative
  | .ex17c => some .positive
  | .ex17d => some .negative
  | .ex18a => some .positive
  | .ex18b => some .negative
  | .ex18c => some .positive
  | .ex18d => some .negative
  | .ex25a => some .positive
  | .ex25b => some .negative
  | .ex25c => some .positive
  | .ex25c_neg => some .negative
  | .ex26a => some .positive
  | .ex26b => some .negative
  | .ex26c => some .positive
  | .ex26c_neg => some .negative
  | .ex27a => some .positive
  | .ex27b => some .negative
  | .ex27c => some .positive
  | .ex27c_neg => some .negative
  | .ex28a => some .positive
  | .ex28b => some .negative
  | .ex28c => some .positive
  | .ex28c_neg => some .negative
  | .ex29a => some .positive
  | .ex29b => some .positive
  | .ex29c => some .negative
  | .ex29d => some .negative
  | .ex29e => some .positive
  | .ex29e_neg => some .negative
  | .ex30a => some .positive
  | .ex30b => some .negative
  | .ex30c => some .positive
  | .ex30c_neg => some .negative
  | .ex30d => some .positive
  | .ex30d_neg => some .negative
  | .ex31a => some .positive
  | .ex31b => some .positive
  | .ex31c => some .negative
  | .ex31d => some .negative
  | .ex31e => some .positive
  | .ex31e_neg => some .negative
  | .ex32a => some .positive
  | .ex32a_neg => some .negative
  | .ex32b => some .positive
  | .ex32b_neg => some .negative
  | .ex32c => some .positive
  | .ex32c_neg => some .negative
  | .ex33a => some .positive
  | .ex33b => some .negative
  | .ex33c => some .positive
  | .ex33c_neg => some .negative
  | .ex34a => some .positive
  | .ex34b => some .negative
  | .ex34c => some .positive
  | .ex43c_ppi => some .negative
  | .ex43c_nci => some .negative
  | .ex43d_ppi => some .negative
  | .ex43d_nci => some .negative
  | .ex43e => some .positive

theorem Example.polarity_datum :
    ∀ x : Example, _root_.Simik2024.Examples.polarity x.datum = x.polarity := by
  decide +kernel

/-- The value the example records under `indefinite`. -/
def Example.indefinite : Example → Option Indefinite
  | .ex11a => none
  | .ex11b => none
  | .ex11c => none
  | .ex11c_neg => none
  | .ex12a => none
  | .ex12b => none
  | .ex12c => none
  | .ex12c_neg => none
  | .ex16a => none
  | .ex16b => none
  | .ex16c => none
  | .ex16d => none
  | .ex17a => none
  | .ex17b => none
  | .ex17c => none
  | .ex17d => none
  | .ex18a => none
  | .ex18b => none
  | .ex18c => none
  | .ex18d => none
  | .ex25a => none
  | .ex25b => none
  | .ex25c => none
  | .ex25c_neg => none
  | .ex26a => none
  | .ex26b => none
  | .ex26c => none
  | .ex26c_neg => none
  | .ex27a => none
  | .ex27b => none
  | .ex27c => none
  | .ex27c_neg => none
  | .ex28a => none
  | .ex28b => none
  | .ex28c => none
  | .ex28c_neg => none
  | .ex29a => none
  | .ex29b => none
  | .ex29c => none
  | .ex29d => none
  | .ex29e => none
  | .ex29e_neg => none
  | .ex30a => none
  | .ex30b => none
  | .ex30c => none
  | .ex30c_neg => none
  | .ex30d => none
  | .ex30d_neg => none
  | .ex31a => none
  | .ex31b => none
  | .ex31c => none
  | .ex31d => none
  | .ex31e => none
  | .ex31e_neg => none
  | .ex32a => none
  | .ex32a_neg => none
  | .ex32b => none
  | .ex32b_neg => none
  | .ex32c => none
  | .ex32c_neg => none
  | .ex33a => none
  | .ex33b => none
  | .ex33c => none
  | .ex33c_neg => none
  | .ex34a => none
  | .ex34b => none
  | .ex34c => none
  | .ex43c_ppi => some .ppi
  | .ex43c_nci => some .nci
  | .ex43d_ppi => some .ppi
  | .ex43d_nci => some .nci
  | .ex43e => some .ppi

theorem Example.indefinite_datum :
    ∀ x : Example, _root_.Simik2024.Examples.indefinite x.datum = x.indefinite := by
  decide +kernel

end Simik2024.Examples
