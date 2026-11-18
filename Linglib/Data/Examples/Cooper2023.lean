module

public import Linglib.Data.Examples.Schema

/-!
# `Cooper2023` — typed example data

Auto-generated from `Linglib/Data/Examples/Cooper2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Cooper2023.Examples`.
-/

@[expose] public section

namespace Cooper2023.Examples

def ex_3_89 : Datum :=
  { id := "cooper2023_3_89"
    source := ⟨"cooper-2023", "Ch. 3, (89)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A conductor is Dudamel"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("chapter", "3"), ("phenomenon", "predication")] }

def ex_6_25 : Datum :=
  { id := "cooper2023_6_25"
    source := ⟨"portner-2009", "p. 49"⟩
    reportedIn := some ⟨"cooper-2023", "Ch. 6, (25)"⟩
    language := "stan1293"
    primaryText := "Mary should eat her broccoli"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("deontic", .acceptable), ("bouletic", .acceptable)]
    paperFeatures := [("chapter", "6"), ("phenomenon", "modality")] }

def ex_7_27 : Datum :=
  { id := "cooper2023_7_27"
    source := ⟨"cooper-2023", "Ch. 7, (27)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every dog ran into the field. They had seen the rabbits."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("maxset", .acceptable)]
    paperFeatures := [("chapter", "7"), ("quantifier", "every")] }

def ex_7_64 : Datum :=
  { id := "cooper2023_7_64"
    source := ⟨"cooper-2023", "Ch. 7, (64)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A dog is barking. It is right outside my window"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("refset", .acceptable)]
    paperFeatures := [("chapter", "7"), ("quantifier", "a")] }

def ex_7_66 : Datum :=
  { id := "cooper2023_7_66"
    source := ⟨"cooper-2023", "Ch. 7, (66)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some dogs are barking. They are right outside my window."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("refset", .acceptable)]
    paperFeatures := [("chapter", "7"), ("quantifier", "some")] }

def ex_7_71 : Datum :=
  { id := "cooper2023_7_71"
    source := ⟨"cooper-2023", "Ch. 7, (71)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No dog barked. They were all busy gnawing on a bone."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("compset", .acceptable)]
    paperFeatures := [("chapter", "7"), ("quantifier", "no")] }

def ex_7_73 : Datum :=
  { id := "cooper2023_7_73"
    source := ⟨"cooper-2023", "Ch. 7, (73)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every dog barked. They had been disturbed by the intruder."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("maxset", .acceptable)]
    paperFeatures := [("chapter", "7"), ("quantifier", "every")] }

def ex_7_75 : Datum :=
  { id := "cooper2023_7_75"
    source := ⟨"cooper-2023", "Ch. 7, (75)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most dogs bark when somebody unknown comes into their territory. They are disturbed by an intruder."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("refset", .acceptable), ("maxset", .acceptable)]
    paperFeatures := [("chapter", "7"), ("quantifier", "most")] }

def ex_7_76 : Datum :=
  { id := "cooper2023_7_76"
    source := ⟨"cooper-2023", "Ch. 7, (76)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most dogs bark when somebody unknown comes into their territory. They never feel threatened whatever happens."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := [("compset", .unacceptable)]
    paperFeatures := [("chapter", "7"), ("quantifier", "most")] }

def ex_7_87 : Datum :=
  { id := "cooper2023_7_87"
    source := ⟨"cooper-2023", "Ch. 7, (87)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Few dogs in the kennels barked. They didn't hear the intruder."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("compset", .acceptable)]
    paperFeatures := [("chapter", "7"), ("quantifier", "few")] }

def ex_7_88 : Datum :=
  { id := "cooper2023_7_88"
    source := ⟨"evans-1980", ""⟩
    reportedIn := some ⟨"cooper-2023", "Ch. 7, (88)"⟩
    language := "stan1293"
    primaryText := "Few congressmen admire Kennedy, and they are very junior."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("refset", .acceptable)]
    paperFeatures := [("chapter", "7"), ("quantifier", "few")] }

def ex_7_91 : Datum :=
  { id := "cooper2023_7_91"
    source := ⟨"cooper-2023", "Ch. 7, (91)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A few dogs barked. They had heard the intruder."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("refset", .acceptable)]
    paperFeatures := [("chapter", "7"), ("quantifier", "a few")] }

def ex_7_92 : Datum :=
  { id := "cooper2023_7_92"
    source := ⟨"cooper-2023", "Ch. 7, (92)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A few dogs barked. They hadn't heard the intruder"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := [("compset", .unacceptable)]
    paperFeatures := [("chapter", "7"), ("quantifier", "a few")] }

def ex_7_103a : Datum :=
  { id := "cooper2023_7_103a"
    source := ⟨"cooper-2023", "Ch. 7, (103a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A dog barked. They do when they notice an intruder."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("maxset", .acceptable)]
    paperFeatures := [("chapter", "7"), ("quantifier", "a")] }

def ex_7_103d : Datum :=
  { id := "cooper2023_7_103d"
    source := ⟨"cooper-2023", "Ch. 7, (103d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A dog barked. It heard an intruder."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("refset", .acceptable)]
    paperFeatures := [("chapter", "7"), ("quantifier", "a")] }

def ex_7_108a : Datum :=
  { id := "cooper2023_7_108a"
    source := ⟨"cooper-2023", "Ch. 7, (108a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No dog barked. They normally do when they notice an intruder."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("maxset", .acceptable)]
    paperFeatures := [("chapter", "7"), ("quantifier", "no")] }

def ex_7_108d : Datum :=
  { id := "cooper2023_7_108d"
    source := ⟨"cooper-2023", "Ch. 7, (108d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No dog barked. They did not hear the intruder."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("compset", .acceptable)]
    paperFeatures := [("chapter", "7"), ("quantifier", "no")] }

def ex_7_113a : Datum :=
  { id := "cooper2023_7_113a"
    source := ⟨"cooper-2023", "Ch. 7, (113a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Few dogs barked. They normally do when they notice an intruder."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("maxset", .acceptable)]
    paperFeatures := [("chapter", "7"), ("quantifier", "few")] }

def ex_7_113d : Datum :=
  { id := "cooper2023_7_113d"
    source := ⟨"cooper-2023", "Ch. 7, (113d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Few dogs barked. They did not hear the intruder."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("compset", .acceptable)]
    paperFeatures := [("chapter", "7"), ("quantifier", "few")] }

def ex_8_1 : Datum :=
  { id := "cooper2023_8_1"
    source := ⟨"cooper-2023", "Ch. 8, (1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "every boy hugged a dog"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("every > a", .acceptable), ("a > every", .acceptable)]
    paperFeatures := [("chapter", "8"), ("phenomenon", "scope")] }

def ex_8_2a : Datum :=
  { id := "cooper2023_8_2a"
    source := ⟨"cooper-2023", "Ch. 8, (2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "a boy hugged every dog"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("a > every", .acceptable), ("every > a", .acceptable)]
    paperFeatures := [("chapter", "8"), ("phenomenon", "scope")] }

def ex_8_46a : Datum :=
  { id := "cooper2023_8_46a"
    source := ⟨"cooper-2023", "Ch. 8, (46a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No dog which chases a cat catches it"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("it = a cat", .acceptable)]
    paperFeatures := [("chapter", "8"), ("phenomenon", "donkey anaphora")] }

def ex_8_46b : Datum :=
  { id := "cooper2023_8_46b"
    source := ⟨"cooper-2023", "Ch. 8, (46b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No dog which chases every cat catches it"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("it = every cat", .questionable)]
    paperFeatures := [("chapter", "8"), ("phenomenon", "donkey anaphora")] }

def ex_8_46c : Datum :=
  { id := "cooper2023_8_46c"
    source := ⟨"cooper-2023", "Ch. 8, (46c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No dog which chases every cat catches them"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("them = every cat", .acceptable)]
    paperFeatures := [("chapter", "8"), ("phenomenon", "donkey anaphora")] }

def ex_8_46d : Datum :=
  { id := "cooper2023_8_46d"
    source := ⟨"cooper-2023", "Ch. 8, (46d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every cat miaowed. It wanted milk."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("it = every cat", .questionable)]
    paperFeatures := [("chapter", "8"), ("phenomenon", "discourse anaphora")] }

def ex_8_46e : Datum :=
  { id := "cooper2023_8_46e"
    source := ⟨"cooper-2023", "Ch. 8, (46e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every cat miaowed. They wanted milk."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("maxset", .acceptable)]
    paperFeatures := [("chapter", "8"), ("quantifier", "every")] }

def ex_8_56a : Datum :=
  { id := "cooper2023_8_56a"
    source := ⟨"schubert-pelletier-1989", ""⟩
    reportedIn := some ⟨"cooper-2023", "Ch. 8, (56a)"⟩
    language := "stan1293"
    primaryText := "Every person who had a dime put it in the parking meter"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("weak", .acceptable), ("strong", .unacceptable)]
    paperFeatures := [("chapter", "8"), ("phenomenon", "donkey anaphora")] }

def ex_8_56b : Datum :=
  { id := "cooper2023_8_56b"
    source := ⟨"cooper-1979", ""⟩
    reportedIn := some ⟨"cooper-2023", "Ch. 8, (56b)"⟩
    language := "stan1293"
    primaryText := "Every man who has a daughter thinks she is the most beautiful girl in the world"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("weak", .acceptable), ("strong", .unacceptable)]
    paperFeatures := [("chapter", "8"), ("phenomenon", "donkey anaphora")] }

def ex_8_57 : Datum :=
  { id := "cooper2023_8_57"
    source := ⟨"chierchia-1995b", ""⟩
    reportedIn := some ⟨"cooper-2023", "Ch. 8, (57)"⟩
    language := "stan1293"
    primaryText := "Every man who owned a slave owned his offspring"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("strong", .acceptable), ("weak", .questionable)]
    paperFeatures := [("chapter", "8"), ("phenomenon", "donkey anaphora")] }

def ex_8_67 : Datum :=
  { id := "cooper2023_8_67"
    source := ⟨"cooper-2023", "Ch. 8, (67)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sam likes him"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("him = Sam", .unacceptable)]
    paperFeatures := [("chapter", "8"), ("phenomenon", "binding")] }

def ex_8_man_walked : Datum :=
  { id := "cooper2023_8_man_walked"
    source := ⟨"cooper-2023", "Ch. 8, §8.3, (37)–(44)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A man walked. He whistled."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("refset", .acceptable)]
    paperFeatures := [("chapter", "8"), ("quantifier", "a")] }

def ex_8_no_girl : Datum :=
  { id := "cooper2023_8_no_girl"
    source := ⟨"cooper-2023", "Ch. 8, §8.3, (30)–(36)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No girl thinks she failed"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("she bound by no girl", .acceptable)]
    paperFeatures := [("chapter", "8"), ("phenomenon", "binding")] }

def all : List Datum := [ex_3_89, ex_6_25, ex_7_27, ex_7_64, ex_7_66, ex_7_71, ex_7_73, ex_7_75, ex_7_76, ex_7_87, ex_7_88, ex_7_91, ex_7_92, ex_7_103a, ex_7_103d, ex_7_108a, ex_7_108d, ex_7_113a, ex_7_113d, ex_8_1, ex_8_2a, ex_8_46a, ex_8_46b, ex_8_46c, ex_8_46d, ex_8_46e, ex_8_56a, ex_8_56b, ex_8_57, ex_8_67, ex_8_man_walked, ex_8_no_girl]

end Cooper2023.Examples
