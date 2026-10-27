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
    context := ""
    judgment := .acceptable
    alternatives := []
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
    alternatives := []
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
    alternatives := []
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
    alternatives := []
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
    alternatives := []
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
    alternatives := []
    readings := []
    paperFeatures := [("variety", "Belfast English"), ("clause", "imperative"), ("order", "V2")] }

def ex_7 : Datum :=
  { id := "westergaard2009_7"
    source := ⟨"westergaard-2009", "ch. 2 (36)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Han sa at han ikke kommer."
    glossedTokens := [("Han", "he"), ("sa", "said"), ("at", "that"), ("han", "he"), ("ikke", "not"), ("kommer", "comes")]
    context := ""
    judgment := .acceptable
    alternatives := [("Han sa at han kommer ikke.", .acceptable)]
    readings := []
    paperFeatures := [("clause", "embedded declarative"), ("embedding", "bridge verb"), ("order", "non-V2 or V2")] }

def ex_27 : Datum :=
  { id := "westergaard2009_27"
    source := ⟨"westergaard-2009", "ch. 2 (36)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Han sa han ikke kommer."
    glossedTokens := [("Han", "he"), ("sa", "said"), ("han", "he"), ("ikke", "not"), ("kommer", "comes")]
    context := ""
    judgment := .acceptable
    alternatives := [("Han sa han kommer ikke.", .acceptable)]
    readings := []
    paperFeatures := [("clause", "embedded declarative"), ("embedding", "bridge verb"), ("complementizer", "none"), ("order", "non-V2 or V2")] }

def ex_8 : Datum :=
  { id := "westergaard2009_8"
    source := ⟨"westergaard-2009", "ch. 2 (39)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Ka slags bil kjøpte du?"
    glossedTokens := [("Ka slags", "which"), ("bil", "car"), ("kjøpte", "bought"), ("du", "you")]
    context := ""
    judgment := .acceptable
    alternatives := [("Ka slags bil du kjøpte?", .ungrammatical)]
    readings := []
    paperFeatures := [("variety", "Tromsø"), ("wh", "phrase"), ("order", "V2")] }

def ex_9 : Datum :=
  { id := "westergaard2009_9"
    source := ⟨"westergaard-2009", "ch. 2 (40)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Korfor gikk ho?"
    glossedTokens := [("Korfor", "why"), ("gikk", "went"), ("ho", "she")]
    context := ""
    judgment := .acceptable
    alternatives := [("Korfor ho gikk?", .ungrammatical)]
    readings := []
    paperFeatures := [("variety", "Tromsø"), ("wh", "disyllabic"), ("order", "V2")] }

def ex_10 : Datum :=
  { id := "westergaard2009_10"
    source := ⟨"westergaard-2009", "ch. 2 (41)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Korsen har ungan det?"
    glossedTokens := [("Korsen", "how"), ("har", "have"), ("ungan", "kid.DEF/PL"), ("det", "it")]
    context := ""
    judgment := .acceptable
    alternatives := [("Korsen ungan har det?", .ungrammatical)]
    readings := []
    paperFeatures := [("variety", "Tromsø"), ("wh", "disyllabic"), ("order", "V2")] }

def ex_11 : Datum :=
  { id := "westergaard2009_11"
    source := ⟨"westergaard-2009", "ch. 3 (12)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Har du vært i byen?"
    glossedTokens := [("Har", "have"), ("du", "you"), ("vært", "been"), ("i", "in"), ("byen", "town")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "yes/no-question"), ("order", "V1")] }

def ex_12 : Datum :=
  { id := "westergaard2009_12"
    source := ⟨"westergaard-2009", "ch. 3 (17)"⟩
    reportedIn := none
    language := "dani1285"
    primaryText := "Hvor er han sød!"
    glossedTokens := [("Hvor", "where/how"), ("er", "is"), ("han", "he"), ("sød", "sweet")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "exclamative"), ("order", "V2")] }

def ex_13 : Datum :=
  { id := "westergaard2009_13"
    source := ⟨"westergaard-2009", "ch. 3 (21)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Kanskje kongen kommer."
    glossedTokens := [("Kanskje", "maybe"), ("kongen", "king.DEF"), ("kommer", "come.PRES")]
    context := ""
    judgment := .acceptable
    alternatives := [("Kanskje kommer kongen.", .acceptable)]
    readings := []
    paperFeatures := [("clause", "declarative"), ("adverb", "kanskje"), ("order", "non-V2 or V2")] }

def ex_14 : Datum :=
  { id := "westergaard2009_14"
    source := ⟨"westergaard-2009", "ch. 3 (22a)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Hvem liker du best?"
    glossedTokens := [("Hvem", "who"), ("liker", "like"), ("du", "you"), ("best", "best")]
    context := ""
    judgment := .acceptable
    alternatives := [("Hvem du liker best?", .ungrammatical)]
    readings := []
    paperFeatures := [("variety", "Standard Norwegian"), ("wh", "monosyllabic"), ("order", "V2")] }

def ex_15 : Datum :=
  { id := "westergaard2009_15"
    source := ⟨"westergaard-2009", "ch. 3 (22b)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Hvilken bil kjøpte du?"
    glossedTokens := [("Hvilken", "which"), ("bil", "car"), ("kjøpte", "bought"), ("du", "you")]
    context := ""
    judgment := .acceptable
    alternatives := [("Hvilken bil du kjøpte?", .ungrammatical)]
    readings := []
    paperFeatures := [("variety", "Standard Norwegian"), ("wh", "phrase"), ("order", "V2")] }

def ex_16 : Datum :=
  { id := "westergaard2009_16"
    source := ⟨"westergaard-2009", "ch. 3 (23a)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Kem like du best?"
    glossedTokens := [("Kem", "who"), ("like", "like"), ("du", "you"), ("best", "best")]
    context := ""
    judgment := .acceptable
    alternatives := [("Kem du like best?", .acceptable)]
    readings := []
    paperFeatures := [("variety", "Tromsø"), ("wh", "monosyllabic"), ("order", "V2 or non-V2")] }

def ex_17 : Datum :=
  { id := "westergaard2009_17"
    source := ⟨"westergaard-2009", "ch. 3 (23b)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Korsen bil kjøpte du?"
    glossedTokens := [("Korsen", "how/which"), ("bil", "car"), ("kjøpte", "bought"), ("du", "you")]
    context := ""
    judgment := .acceptable
    alternatives := [("Korsen bil du kjøpte?", .ungrammatical)]
    readings := []
    paperFeatures := [("variety", "Tromsø"), ("wh", "phrase"), ("order", "V2")] }

def ex_18 : Datum :=
  { id := "westergaard2009_18"
    source := ⟨"westergaard-2009", "ch. 3 (24a)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Kåin du lika best?"
    glossedTokens := [("Kåin", "who"), ("du", "you"), ("lika", "like"), ("best", "best")]
    context := ""
    judgment := .acceptable
    alternatives := [("Kåin lika du best?", .acceptable)]
    readings := []
    paperFeatures := [("variety", "Nordmøre"), ("wh", "monosyllabic"), ("order", "non-V2 or V2")] }

def ex_19 : Datum :=
  { id := "westergaard2009_19"
    source := ⟨"westergaard-2009", "ch. 3 (24b)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Kåles bil du kjøpte?"
    glossedTokens := [("Kåles", "which"), ("bil", "car"), ("du", "you"), ("kjøpte", "bought")]
    context := ""
    judgment := .acceptable
    alternatives := [("Kåles bil kjøpte du?", .acceptable)]
    readings := []
    paperFeatures := [("variety", "Nordmøre"), ("wh", "phrase"), ("order", "non-V2 or V2")] }

def ex_20 : Datum :=
  { id := "westergaard2009_20"
    source := ⟨"westergaard-2009", "ch. 3 (29)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "kor er mitt fly?"
    glossedTokens := [("kor", "where"), ("er", "is"), ("mitt", "my"), ("fly", "plane")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("variety", "Tromsø"), ("subject", "new"), ("order", "V2")] }

def ex_21 : Datum :=
  { id := "westergaard2009_21"
    source := ⟨"westergaard-2009", "ch. 3 (30)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "kor vi lande henne?"
    glossedTokens := [("kor", "where"), ("vi", "we"), ("lande", "land"), ("henne", "LOC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("variety", "Tromsø"), ("subject", "given"), ("order", "non-V2")] }

def ex_22 : Datum :=
  { id := "westergaard2009_22"
    source := ⟨"westergaard-2009", "ch. 3 (33)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "kem som ikkje får kjøre?"
    glossedTokens := [("kem", "who"), ("som", "that"), ("ikkje", "not"), ("får", "gets"), ("kjøre", "drive")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("variety", "Tromsø"), ("clause", "subject question"), ("order", "non-V2")] }

def ex_23 : Datum :=
  { id := "westergaard2009_23"
    source := ⟨"westergaard-2009", "ch. 3 (38)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Han bare svarte ikke."
    glossedTokens := [("Han", "he"), ("bare", "just"), ("svarte", "answered"), ("ikke", "not")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "subject-initial declarative"), ("adverb", "focus-sensitive")] }

def ex_24 : Datum :=
  { id := "westergaard2009_24"
    source := ⟨"westergaard-2009", "ch. 3 (47)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Hvilken bok liker du best?"
    glossedTokens := [("Hvilken", "which"), ("bok", "book.DEF"), ("liker", "like"), ("du", "you"), ("best", "best")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("variety", "Standard Norwegian"), ("clause", "wh-question"), ("order", "V2")] }

def ex_25 : Datum :=
  { id := "westergaard2009_25"
    source := ⟨"westergaard-2009", "ch. 3 (48)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Denne boka liker jeg ikke."
    glossedTokens := [("Denne", "this"), ("boka", "book.DEF"), ("liker", "like"), ("jeg", "I"), ("ikke", "not")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("variety", "Standard Norwegian"), ("clause", "non-subject-initial declarative"), ("order", "V2")] }

def ex_26 : Datum :=
  { id := "westergaard2009_26"
    source := ⟨"westergaard-2009", "ch. 3 (66)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Kem som ikkje kommer til festen?"
    glossedTokens := [("Kem", "who"), ("som", "SOM"), ("ikkje", "not"), ("kommer", "comes"), ("til", "to"), ("festen", "party.DEF")]
    context := ""
    judgment := .acceptable
    alternatives := [("Kem kommer ikkje til festen?", .ungrammatical)]
    readings := []
    paperFeatures := [("variety", "Tromsø"), ("clause", "subject question"), ("som", "inserted")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_27, ex_8, ex_9, ex_10, ex_11, ex_12, ex_13, ex_14, ex_15, ex_16, ex_17, ex_18, ex_19, ex_20, ex_21, ex_22, ex_23, ex_24, ex_25, ex_26]

end Westergaard2009.Examples
