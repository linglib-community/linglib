module

public import Linglib.Data.Examples.Schema

/-!
# `Westergaard2009` — typed example data

Auto-generated from `Linglib/Data/Examples/Westergaard2009.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Westergaard2009.Examples`.
-/

@[expose] public section

namespace Westergaard2009.Examples

def ex_1 : Datum :=
  { id := "westergaard2009_1"
    source := ⟨"westergaard-2009", "ch. 1 (1)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Hvilket språk snakker dere?"
    glossedTokens := [("Hvilket", "which"), ("språk", "language"), ("snakker", "speak"), ("dere", "you.PL")]
    glossedWords := [⟨['H', 'v', 'i', 'l', 'k', 'e', 't'], ['w', 'h', 'i', 'c', 'h'], [⟨['H', 'v', 'i', 'l', 'k', 'e', 't'], ['w', 'h', 'i', 'c', 'h'], none⟩]⟩, ⟨['s', 'p', 'r', 'å', 'k'], ['l', 'a', 'n', 'g', 'u', 'a', 'g', 'e'], [⟨['s', 'p', 'r', 'å', 'k'], ['l', 'a', 'n', 'g', 'u', 'a', 'g', 'e'], none⟩]⟩, ⟨['s', 'n', 'a', 'k', 'k', 'e', 'r'], ['s', 'p', 'e', 'a', 'k'], [⟨['s', 'n', 'a', 'k', 'k', 'e', 'r'], ['s', 'p', 'e', 'a', 'k'], none⟩]⟩, ⟨['d', 'e', 'r', 'e'], ['y', 'o', 'u', '.', 'P', 'L'], [⟨['d', 'e', 'r', 'e'], ['y', 'o', 'u', '.', 'P', 'L'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "wh-question"), ("order", "V2")] }

def ex_2 : Datum :=
  { id := "westergaard2009_2"
    source := ⟨"westergaard-2009", "ch. 1 (2)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Av og til snakker vi tysk."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "non-subject-initial declarative"), ("order", "V2")] }

def ex_3 : Datum :=
  { id := "westergaard2009_3"
    source := ⟨"westergaard-2009", "ch. 2 (20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What will you bring to the party?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "wh-question"), ("order", "V2")] }

def ex_4 : Datum :=
  { id := "westergaard2009_4"
    source := ⟨"westergaard-2009", "ch. 2 (21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Have you seen her today?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "yes/no-question"), ("order", "V1")] }

def ex_5 : Datum :=
  { id := "westergaard2009_5"
    source := ⟨"westergaard-2009", "ch. 2 (23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They asked me was I going to the party."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("variety", "Belfast English"), ("clause", "embedded question"), ("complementizer", "none"), ("order", "V2")] }

def ex_6 : Datum :=
  { id := "westergaard2009_6"
    source := ⟨"westergaard-2009", "ch. 2 (24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bring you that with you!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("variety", "Belfast English"), ("clause", "imperative"), ("order", "V2")] }

def ex_7 : Datum :=
  { id := "westergaard2009_7"
    source := ⟨"westergaard-2009", "ch. 2 (36)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Han sa at han ikke kommer."
    glossedTokens := [("Han", "he"), ("sa", "said"), ("at", "that"), ("han", "he"), ("ikke", "not"), ("kommer", "comes")]
    glossedWords := [⟨['H', 'a', 'n'], ['h', 'e'], [⟨['H', 'a', 'n'], ['h', 'e'], none⟩]⟩, ⟨['s', 'a'], ['s', 'a', 'i', 'd'], [⟨['s', 'a'], ['s', 'a', 'i', 'd'], none⟩]⟩, ⟨['a', 't'], ['t', 'h', 'a', 't'], [⟨['a', 't'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['h', 'a', 'n'], ['h', 'e'], [⟨['h', 'a', 'n'], ['h', 'e'], none⟩]⟩, ⟨['i', 'k', 'k', 'e'], ['n', 'o', 't'], [⟨['i', 'k', 'k', 'e'], ['n', 'o', 't'], none⟩]⟩, ⟨['k', 'o', 'm', 'm', 'e', 'r'], ['c', 'o', 'm', 'e', 's'], [⟨['k', 'o', 'm', 'm', 'e', 'r'], ['c', 'o', 'm', 'e', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Han sa at han kommer ikke.", .acceptable)]
    readings := []
    paperFeatures := [("clause", "embedded declarative"), ("embedding", "bridge verb"), ("order", "non-V2 or V2")] }

def ex_27 : Datum :=
  { id := "westergaard2009_27"
    source := ⟨"westergaard-2009", "ch. 2 (36)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Han sa han ikke kommer."
    glossedTokens := [("Han", "he"), ("sa", "said"), ("han", "he"), ("ikke", "not"), ("kommer", "comes")]
    glossedWords := [⟨['H', 'a', 'n'], ['h', 'e'], [⟨['H', 'a', 'n'], ['h', 'e'], none⟩]⟩, ⟨['s', 'a'], ['s', 'a', 'i', 'd'], [⟨['s', 'a'], ['s', 'a', 'i', 'd'], none⟩]⟩, ⟨['h', 'a', 'n'], ['h', 'e'], [⟨['h', 'a', 'n'], ['h', 'e'], none⟩]⟩, ⟨['i', 'k', 'k', 'e'], ['n', 'o', 't'], [⟨['i', 'k', 'k', 'e'], ['n', 'o', 't'], none⟩]⟩, ⟨['k', 'o', 'm', 'm', 'e', 'r'], ['c', 'o', 'm', 'e', 's'], [⟨['k', 'o', 'm', 'm', 'e', 'r'], ['c', 'o', 'm', 'e', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Han sa han kommer ikke.", .acceptable)]
    readings := []
    paperFeatures := [("clause", "embedded declarative"), ("embedding", "bridge verb"), ("complementizer", "none"), ("order", "non-V2 or V2")] }

def ex_8 : Datum :=
  { id := "westergaard2009_8"
    source := ⟨"westergaard-2009", "ch. 2 (39)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Ka slags bil kjøpte du?"
    glossedTokens := [("Ka slags", "which"), ("bil", "car"), ("kjøpte", "bought"), ("du", "you")]
    glossedWords := [⟨['K', 'a', ' ', 's', 'l', 'a', 'g', 's'], ['w', 'h', 'i', 'c', 'h'], [⟨['K', 'a', ' ', 's', 'l', 'a', 'g', 's'], ['w', 'h', 'i', 'c', 'h'], none⟩]⟩, ⟨['b', 'i', 'l'], ['c', 'a', 'r'], [⟨['b', 'i', 'l'], ['c', 'a', 'r'], none⟩]⟩, ⟨['k', 'j', 'ø', 'p', 't', 'e'], ['b', 'o', 'u', 'g', 'h', 't'], [⟨['k', 'j', 'ø', 'p', 't', 'e'], ['b', 'o', 'u', 'g', 'h', 't'], none⟩]⟩, ⟨['d', 'u'], ['y', 'o', 'u'], [⟨['d', 'u'], ['y', 'o', 'u'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Ka slags bil du kjøpte?", .ungrammatical)]
    readings := []
    paperFeatures := [("variety", "Tromsø"), ("wh", "phrase"), ("order", "V2")] }

def ex_9 : Datum :=
  { id := "westergaard2009_9"
    source := ⟨"westergaard-2009", "ch. 2 (40)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Korfor gikk ho?"
    glossedTokens := [("Korfor", "why"), ("gikk", "went"), ("ho", "she")]
    glossedWords := [⟨['K', 'o', 'r', 'f', 'o', 'r'], ['w', 'h', 'y'], [⟨['K', 'o', 'r', 'f', 'o', 'r'], ['w', 'h', 'y'], none⟩]⟩, ⟨['g', 'i', 'k', 'k'], ['w', 'e', 'n', 't'], [⟨['g', 'i', 'k', 'k'], ['w', 'e', 'n', 't'], none⟩]⟩, ⟨['h', 'o'], ['s', 'h', 'e'], [⟨['h', 'o'], ['s', 'h', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Korfor ho gikk?", .ungrammatical)]
    readings := []
    paperFeatures := [("variety", "Tromsø"), ("wh", "disyllabic"), ("order", "V2")] }

def ex_10 : Datum :=
  { id := "westergaard2009_10"
    source := ⟨"westergaard-2009", "ch. 2 (41)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Korsen har ungan det?"
    glossedTokens := [("Korsen", "how"), ("har", "have"), ("ungan", "kid.DEF/PL"), ("det", "it")]
    glossedWords := [⟨['K', 'o', 'r', 's', 'e', 'n'], ['h', 'o', 'w'], [⟨['K', 'o', 'r', 's', 'e', 'n'], ['h', 'o', 'w'], none⟩]⟩, ⟨['h', 'a', 'r'], ['h', 'a', 'v', 'e'], [⟨['h', 'a', 'r'], ['h', 'a', 'v', 'e'], none⟩]⟩, ⟨['u', 'n', 'g', 'a', 'n'], ['k', 'i', 'd', '.', 'D', 'E', 'F', '/', 'P', 'L'], [⟨['u', 'n', 'g', 'a', 'n'], ['k', 'i', 'd', '.', 'D', 'E', 'F', '/', 'P', 'L'], none⟩]⟩, ⟨['d', 'e', 't'], ['i', 't'], [⟨['d', 'e', 't'], ['i', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Korsen ungan har det?", .ungrammatical)]
    readings := []
    paperFeatures := [("variety", "Tromsø"), ("wh", "disyllabic"), ("order", "V2")] }

def ex_11 : Datum :=
  { id := "westergaard2009_11"
    source := ⟨"westergaard-2009", "ch. 3 (12)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Har du vært i byen?"
    glossedTokens := [("Har", "have"), ("du", "you"), ("vært", "been"), ("i", "in"), ("byen", "town")]
    glossedWords := [⟨['H', 'a', 'r'], ['h', 'a', 'v', 'e'], [⟨['H', 'a', 'r'], ['h', 'a', 'v', 'e'], none⟩]⟩, ⟨['d', 'u'], ['y', 'o', 'u'], [⟨['d', 'u'], ['y', 'o', 'u'], none⟩]⟩, ⟨['v', 'æ', 'r', 't'], ['b', 'e', 'e', 'n'], [⟨['v', 'æ', 'r', 't'], ['b', 'e', 'e', 'n'], none⟩]⟩, ⟨['i'], ['i', 'n'], [⟨['i'], ['i', 'n'], none⟩]⟩, ⟨['b', 'y', 'e', 'n'], ['t', 'o', 'w', 'n'], [⟨['b', 'y', 'e', 'n'], ['t', 'o', 'w', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "yes/no-question"), ("order", "V1")] }

def ex_12 : Datum :=
  { id := "westergaard2009_12"
    source := ⟨"westergaard-2009", "ch. 3 (17)"⟩
    reportedIn := none
    language := "dani1285"
    primaryText := "Hvor er han sød!"
    glossedTokens := [("Hvor", "where/how"), ("er", "is"), ("han", "he"), ("sød", "sweet")]
    glossedWords := [⟨['H', 'v', 'o', 'r'], ['w', 'h', 'e', 'r', 'e', '/', 'h', 'o', 'w'], [⟨['H', 'v', 'o', 'r'], ['w', 'h', 'e', 'r', 'e', '/', 'h', 'o', 'w'], none⟩]⟩, ⟨['e', 'r'], ['i', 's'], [⟨['e', 'r'], ['i', 's'], none⟩]⟩, ⟨['h', 'a', 'n'], ['h', 'e'], [⟨['h', 'a', 'n'], ['h', 'e'], none⟩]⟩, ⟨['s', 'ø', 'd'], ['s', 'w', 'e', 'e', 't'], [⟨['s', 'ø', 'd'], ['s', 'w', 'e', 'e', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "exclamative"), ("order", "V2")] }

def ex_13 : Datum :=
  { id := "westergaard2009_13"
    source := ⟨"westergaard-2009", "ch. 3 (21)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Kanskje kongen kommer."
    glossedTokens := [("Kanskje", "maybe"), ("kongen", "king.DEF"), ("kommer", "come.PRES")]
    glossedWords := [⟨['K', 'a', 'n', 's', 'k', 'j', 'e'], ['m', 'a', 'y', 'b', 'e'], [⟨['K', 'a', 'n', 's', 'k', 'j', 'e'], ['m', 'a', 'y', 'b', 'e'], none⟩]⟩, ⟨['k', 'o', 'n', 'g', 'e', 'n'], ['k', 'i', 'n', 'g', '.', 'D', 'E', 'F'], [⟨['k', 'o', 'n', 'g', 'e', 'n'], ['k', 'i', 'n', 'g', '.', 'D', 'E', 'F'], none⟩]⟩, ⟨['k', 'o', 'm', 'm', 'e', 'r'], ['c', 'o', 'm', 'e', '.', 'P', 'R', 'E', 'S'], [⟨['k', 'o', 'm', 'm', 'e', 'r'], ['c', 'o', 'm', 'e', '.', 'P', 'R', 'E', 'S'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Kanskje kommer kongen.", .acceptable)]
    readings := []
    paperFeatures := [("clause", "declarative"), ("adverb", "kanskje"), ("order", "non-V2 or V2")] }

def ex_14 : Datum :=
  { id := "westergaard2009_14"
    source := ⟨"westergaard-2009", "ch. 3 (22a)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Hvem liker du best?"
    glossedTokens := [("Hvem", "who"), ("liker", "like"), ("du", "you"), ("best", "best")]
    glossedWords := [⟨['H', 'v', 'e', 'm'], ['w', 'h', 'o'], [⟨['H', 'v', 'e', 'm'], ['w', 'h', 'o'], none⟩]⟩, ⟨['l', 'i', 'k', 'e', 'r'], ['l', 'i', 'k', 'e'], [⟨['l', 'i', 'k', 'e', 'r'], ['l', 'i', 'k', 'e'], none⟩]⟩, ⟨['d', 'u'], ['y', 'o', 'u'], [⟨['d', 'u'], ['y', 'o', 'u'], none⟩]⟩, ⟨['b', 'e', 's', 't'], ['b', 'e', 's', 't'], [⟨['b', 'e', 's', 't'], ['b', 'e', 's', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Hvem du liker best?", .ungrammatical)]
    readings := []
    paperFeatures := [("variety", "Standard Norwegian"), ("wh", "monosyllabic"), ("order", "V2")] }

def ex_15 : Datum :=
  { id := "westergaard2009_15"
    source := ⟨"westergaard-2009", "ch. 3 (22b)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Hvilken bil kjøpte du?"
    glossedTokens := [("Hvilken", "which"), ("bil", "car"), ("kjøpte", "bought"), ("du", "you")]
    glossedWords := [⟨['H', 'v', 'i', 'l', 'k', 'e', 'n'], ['w', 'h', 'i', 'c', 'h'], [⟨['H', 'v', 'i', 'l', 'k', 'e', 'n'], ['w', 'h', 'i', 'c', 'h'], none⟩]⟩, ⟨['b', 'i', 'l'], ['c', 'a', 'r'], [⟨['b', 'i', 'l'], ['c', 'a', 'r'], none⟩]⟩, ⟨['k', 'j', 'ø', 'p', 't', 'e'], ['b', 'o', 'u', 'g', 'h', 't'], [⟨['k', 'j', 'ø', 'p', 't', 'e'], ['b', 'o', 'u', 'g', 'h', 't'], none⟩]⟩, ⟨['d', 'u'], ['y', 'o', 'u'], [⟨['d', 'u'], ['y', 'o', 'u'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Hvilken bil du kjøpte?", .ungrammatical)]
    readings := []
    paperFeatures := [("variety", "Standard Norwegian"), ("wh", "phrase"), ("order", "V2")] }

def ex_16 : Datum :=
  { id := "westergaard2009_16"
    source := ⟨"westergaard-2009", "ch. 3 (23a)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Kem like du best?"
    glossedTokens := [("Kem", "who"), ("like", "like"), ("du", "you"), ("best", "best")]
    glossedWords := [⟨['K', 'e', 'm'], ['w', 'h', 'o'], [⟨['K', 'e', 'm'], ['w', 'h', 'o'], none⟩]⟩, ⟨['l', 'i', 'k', 'e'], ['l', 'i', 'k', 'e'], [⟨['l', 'i', 'k', 'e'], ['l', 'i', 'k', 'e'], none⟩]⟩, ⟨['d', 'u'], ['y', 'o', 'u'], [⟨['d', 'u'], ['y', 'o', 'u'], none⟩]⟩, ⟨['b', 'e', 's', 't'], ['b', 'e', 's', 't'], [⟨['b', 'e', 's', 't'], ['b', 'e', 's', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Kem du like best?", .acceptable)]
    readings := []
    paperFeatures := [("variety", "Tromsø"), ("wh", "monosyllabic"), ("order", "V2 or non-V2")] }

def ex_17 : Datum :=
  { id := "westergaard2009_17"
    source := ⟨"westergaard-2009", "ch. 3 (23b)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Korsen bil kjøpte du?"
    glossedTokens := [("Korsen", "how/which"), ("bil", "car"), ("kjøpte", "bought"), ("du", "you")]
    glossedWords := [⟨['K', 'o', 'r', 's', 'e', 'n'], ['h', 'o', 'w', '/', 'w', 'h', 'i', 'c', 'h'], [⟨['K', 'o', 'r', 's', 'e', 'n'], ['h', 'o', 'w', '/', 'w', 'h', 'i', 'c', 'h'], none⟩]⟩, ⟨['b', 'i', 'l'], ['c', 'a', 'r'], [⟨['b', 'i', 'l'], ['c', 'a', 'r'], none⟩]⟩, ⟨['k', 'j', 'ø', 'p', 't', 'e'], ['b', 'o', 'u', 'g', 'h', 't'], [⟨['k', 'j', 'ø', 'p', 't', 'e'], ['b', 'o', 'u', 'g', 'h', 't'], none⟩]⟩, ⟨['d', 'u'], ['y', 'o', 'u'], [⟨['d', 'u'], ['y', 'o', 'u'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Korsen bil du kjøpte?", .ungrammatical)]
    readings := []
    paperFeatures := [("variety", "Tromsø"), ("wh", "phrase"), ("order", "V2")] }

def ex_18 : Datum :=
  { id := "westergaard2009_18"
    source := ⟨"westergaard-2009", "ch. 3 (24a)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Kåin du lika best?"
    glossedTokens := [("Kåin", "who"), ("du", "you"), ("lika", "like"), ("best", "best")]
    glossedWords := [⟨['K', 'å', 'i', 'n'], ['w', 'h', 'o'], [⟨['K', 'å', 'i', 'n'], ['w', 'h', 'o'], none⟩]⟩, ⟨['d', 'u'], ['y', 'o', 'u'], [⟨['d', 'u'], ['y', 'o', 'u'], none⟩]⟩, ⟨['l', 'i', 'k', 'a'], ['l', 'i', 'k', 'e'], [⟨['l', 'i', 'k', 'a'], ['l', 'i', 'k', 'e'], none⟩]⟩, ⟨['b', 'e', 's', 't'], ['b', 'e', 's', 't'], [⟨['b', 'e', 's', 't'], ['b', 'e', 's', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Kåin lika du best?", .acceptable)]
    readings := []
    paperFeatures := [("variety", "Nordmøre"), ("wh", "monosyllabic"), ("order", "non-V2 or V2")] }

def ex_19 : Datum :=
  { id := "westergaard2009_19"
    source := ⟨"westergaard-2009", "ch. 3 (24b)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Kåles bil du kjøpte?"
    glossedTokens := [("Kåles", "which"), ("bil", "car"), ("du", "you"), ("kjøpte", "bought")]
    glossedWords := [⟨['K', 'å', 'l', 'e', 's'], ['w', 'h', 'i', 'c', 'h'], [⟨['K', 'å', 'l', 'e', 's'], ['w', 'h', 'i', 'c', 'h'], none⟩]⟩, ⟨['b', 'i', 'l'], ['c', 'a', 'r'], [⟨['b', 'i', 'l'], ['c', 'a', 'r'], none⟩]⟩, ⟨['d', 'u'], ['y', 'o', 'u'], [⟨['d', 'u'], ['y', 'o', 'u'], none⟩]⟩, ⟨['k', 'j', 'ø', 'p', 't', 'e'], ['b', 'o', 'u', 'g', 'h', 't'], [⟨['k', 'j', 'ø', 'p', 't', 'e'], ['b', 'o', 'u', 'g', 'h', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Kåles bil kjøpte du?", .acceptable)]
    readings := []
    paperFeatures := [("variety", "Nordmøre"), ("wh", "phrase"), ("order", "non-V2 or V2")] }

def ex_20 : Datum :=
  { id := "westergaard2009_20"
    source := ⟨"westergaard-2009", "ch. 3 (29)"⟩
    reportedIn := none
    method := some .corpus
    language := "norw1258"
    primaryText := "kor er mitt fly?"
    glossedTokens := [("kor", "where"), ("er", "is"), ("mitt", "my"), ("fly", "plane")]
    glossedWords := [⟨['k', 'o', 'r'], ['w', 'h', 'e', 'r', 'e'], [⟨['k', 'o', 'r'], ['w', 'h', 'e', 'r', 'e'], none⟩]⟩, ⟨['e', 'r'], ['i', 's'], [⟨['e', 'r'], ['i', 's'], none⟩]⟩, ⟨['m', 'i', 't', 't'], ['m', 'y'], [⟨['m', 'i', 't', 't'], ['m', 'y'], none⟩]⟩, ⟨['f', 'l', 'y'], ['p', 'l', 'a', 'n', 'e'], [⟨['f', 'l', 'y'], ['p', 'l', 'a', 'n', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("variety", "Tromsø"), ("subject", "new"), ("order", "V2")] }

def ex_21 : Datum :=
  { id := "westergaard2009_21"
    source := ⟨"westergaard-2009", "ch. 3 (30)"⟩
    reportedIn := none
    method := some .corpus
    language := "norw1258"
    primaryText := "kor vi lande henne?"
    glossedTokens := [("kor", "where"), ("vi", "we"), ("lande", "land"), ("henne", "LOC")]
    glossedWords := [⟨['k', 'o', 'r'], ['w', 'h', 'e', 'r', 'e'], [⟨['k', 'o', 'r'], ['w', 'h', 'e', 'r', 'e'], none⟩]⟩, ⟨['v', 'i'], ['w', 'e'], [⟨['v', 'i'], ['w', 'e'], none⟩]⟩, ⟨['l', 'a', 'n', 'd', 'e'], ['l', 'a', 'n', 'd'], [⟨['l', 'a', 'n', 'd', 'e'], ['l', 'a', 'n', 'd'], none⟩]⟩, ⟨['h', 'e', 'n', 'n', 'e'], ['L', 'O', 'C'], [⟨['h', 'e', 'n', 'n', 'e'], ['L', 'O', 'C'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("variety", "Tromsø"), ("subject", "given"), ("order", "non-V2")] }

def ex_22 : Datum :=
  { id := "westergaard2009_22"
    source := ⟨"westergaard-2009", "ch. 3 (33)"⟩
    reportedIn := none
    method := some .corpus
    language := "norw1258"
    primaryText := "kem som ikkje får kjøre?"
    glossedTokens := [("kem", "who"), ("som", "that"), ("ikkje", "not"), ("får", "gets"), ("kjøre", "drive")]
    glossedWords := [⟨['k', 'e', 'm'], ['w', 'h', 'o'], [⟨['k', 'e', 'm'], ['w', 'h', 'o'], none⟩]⟩, ⟨['s', 'o', 'm'], ['t', 'h', 'a', 't'], [⟨['s', 'o', 'm'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['i', 'k', 'k', 'j', 'e'], ['n', 'o', 't'], [⟨['i', 'k', 'k', 'j', 'e'], ['n', 'o', 't'], none⟩]⟩, ⟨['f', 'å', 'r'], ['g', 'e', 't', 's'], [⟨['f', 'å', 'r'], ['g', 'e', 't', 's'], none⟩]⟩, ⟨['k', 'j', 'ø', 'r', 'e'], ['d', 'r', 'i', 'v', 'e'], [⟨['k', 'j', 'ø', 'r', 'e'], ['d', 'r', 'i', 'v', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("variety", "Tromsø"), ("clause", "subject question"), ("order", "non-V2")] }

def ex_23 : Datum :=
  { id := "westergaard2009_23"
    source := ⟨"westergaard-2009", "ch. 3 (38)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Han bare svarte ikke."
    glossedTokens := [("Han", "he"), ("bare", "just"), ("svarte", "answered"), ("ikke", "not")]
    glossedWords := [⟨['H', 'a', 'n'], ['h', 'e'], [⟨['H', 'a', 'n'], ['h', 'e'], none⟩]⟩, ⟨['b', 'a', 'r', 'e'], ['j', 'u', 's', 't'], [⟨['b', 'a', 'r', 'e'], ['j', 'u', 's', 't'], none⟩]⟩, ⟨['s', 'v', 'a', 'r', 't', 'e'], ['a', 'n', 's', 'w', 'e', 'r', 'e', 'd'], [⟨['s', 'v', 'a', 'r', 't', 'e'], ['a', 'n', 's', 'w', 'e', 'r', 'e', 'd'], none⟩]⟩, ⟨['i', 'k', 'k', 'e'], ['n', 'o', 't'], [⟨['i', 'k', 'k', 'e'], ['n', 'o', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "subject-initial declarative"), ("adverb", "focus-sensitive")] }

def ex_24 : Datum :=
  { id := "westergaard2009_24"
    source := ⟨"westergaard-2009", "ch. 3 (47)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Hvilken bok liker du best?"
    glossedTokens := [("Hvilken", "which"), ("bok", "book.DEF"), ("liker", "like"), ("du", "you"), ("best", "best")]
    glossedWords := [⟨['H', 'v', 'i', 'l', 'k', 'e', 'n'], ['w', 'h', 'i', 'c', 'h'], [⟨['H', 'v', 'i', 'l', 'k', 'e', 'n'], ['w', 'h', 'i', 'c', 'h'], none⟩]⟩, ⟨['b', 'o', 'k'], ['b', 'o', 'o', 'k', '.', 'D', 'E', 'F'], [⟨['b', 'o', 'k'], ['b', 'o', 'o', 'k', '.', 'D', 'E', 'F'], none⟩]⟩, ⟨['l', 'i', 'k', 'e', 'r'], ['l', 'i', 'k', 'e'], [⟨['l', 'i', 'k', 'e', 'r'], ['l', 'i', 'k', 'e'], none⟩]⟩, ⟨['d', 'u'], ['y', 'o', 'u'], [⟨['d', 'u'], ['y', 'o', 'u'], none⟩]⟩, ⟨['b', 'e', 's', 't'], ['b', 'e', 's', 't'], [⟨['b', 'e', 's', 't'], ['b', 'e', 's', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("variety", "Standard Norwegian"), ("clause", "wh-question"), ("order", "V2")] }

def ex_25 : Datum :=
  { id := "westergaard2009_25"
    source := ⟨"westergaard-2009", "ch. 3 (48)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Denne boka liker jeg ikke."
    glossedTokens := [("Denne", "this"), ("boka", "book.DEF"), ("liker", "like"), ("jeg", "I"), ("ikke", "not")]
    glossedWords := [⟨['D', 'e', 'n', 'n', 'e'], ['t', 'h', 'i', 's'], [⟨['D', 'e', 'n', 'n', 'e'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['b', 'o', 'k', 'a'], ['b', 'o', 'o', 'k', '.', 'D', 'E', 'F'], [⟨['b', 'o', 'k', 'a'], ['b', 'o', 'o', 'k', '.', 'D', 'E', 'F'], none⟩]⟩, ⟨['l', 'i', 'k', 'e', 'r'], ['l', 'i', 'k', 'e'], [⟨['l', 'i', 'k', 'e', 'r'], ['l', 'i', 'k', 'e'], none⟩]⟩, ⟨['j', 'e', 'g'], ['I'], [⟨['j', 'e', 'g'], ['I'], none⟩]⟩, ⟨['i', 'k', 'k', 'e'], ['n', 'o', 't'], [⟨['i', 'k', 'k', 'e'], ['n', 'o', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("variety", "Standard Norwegian"), ("clause", "non-subject-initial declarative"), ("order", "V2")] }

def ex_26 : Datum :=
  { id := "westergaard2009_26"
    source := ⟨"westergaard-2009", "ch. 3 (66)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Kem som ikkje kommer til festen?"
    glossedTokens := [("Kem", "who"), ("som", "SOM"), ("ikkje", "not"), ("kommer", "comes"), ("til", "to"), ("festen", "party.DEF")]
    glossedWords := [⟨['K', 'e', 'm'], ['w', 'h', 'o'], [⟨['K', 'e', 'm'], ['w', 'h', 'o'], none⟩]⟩, ⟨['s', 'o', 'm'], ['S', 'O', 'M'], [⟨['s', 'o', 'm'], ['S', 'O', 'M'], none⟩]⟩, ⟨['i', 'k', 'k', 'j', 'e'], ['n', 'o', 't'], [⟨['i', 'k', 'k', 'j', 'e'], ['n', 'o', 't'], none⟩]⟩, ⟨['k', 'o', 'm', 'm', 'e', 'r'], ['c', 'o', 'm', 'e', 's'], [⟨['k', 'o', 'm', 'm', 'e', 'r'], ['c', 'o', 'm', 'e', 's'], none⟩]⟩, ⟨['t', 'i', 'l'], ['t', 'o'], [⟨['t', 'i', 'l'], ['t', 'o'], none⟩]⟩, ⟨['f', 'e', 's', 't', 'e', 'n'], ['p', 'a', 'r', 't', 'y', '.', 'D', 'E', 'F'], [⟨['f', 'e', 's', 't', 'e', 'n'], ['p', 'a', 'r', 't', 'y', '.', 'D', 'E', 'F'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Kem kommer ikkje til festen?", .ungrammatical)]
    readings := []
    paperFeatures := [("variety", "Tromsø"), ("clause", "subject question"), ("som", "inserted")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_27, ex_8, ex_9, ex_10, ex_11, ex_12, ex_13, ex_14, ex_15, ex_16, ex_17, ex_18, ex_19, ex_20, ex_21, ex_22, ex_23, ex_24, ex_25, ex_26]

end Westergaard2009.Examples
