module

public import Linglib.Data.Examples.Schema

/-!
# `Spector2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Spector2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Spector2026.Examples`.
-/

@[expose] public section

namespace Spector2026.Examples

def ex_1a : Datum :=
  { id := "spector2026_1a"
    source := ⟨"spector-2026", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A woman is in the room and she is smiling."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1")] }

def ex_3a : Datum :=
  { id := "spector2026_3a"
    source := ⟨"spector-2026", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary owns a violin, and it is expensive."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1.1")] }

def ex_3b : Datum :=
  { id := "spector2026_3b"
    source := ⟨"spector-2026", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary owns a violin, and Peter knows that Mary owns a musical instrument."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1.1")] }

def ex_4 : Datum :=
  { id := "spector2026_4"
    source := ⟨"spector-2026", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A woman was in the room. She smiled."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1.2")] }

def ex_5 : Datum :=
  { id := "spector2026_5"
    source := ⟨"spector-2026", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A woman was in the room. She smiled. Another woman was in the room."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1.2")] }

def s2_2_singing : Datum :=
  { id := "spector2026_s2_2_singing"
    source := ⟨"spector-2026", "§2.2 singing"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Someone is singing and someone is standing."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("one person singing and standing", .unacceptable)]
    paperFeatures := [("section", "2.2")] }

def s3_1_purple : Datum :=
  { id := "spector2026_s3_1_purple"
    source := ⟨"spector-2026", "§3.1 purple"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is purple."
    glossedTokens := []
    context := "out of the blue"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1")] }

def s3_1_table : Datum :=
  { id := "spector2026_s3_1_table"
    source := ⟨"spector-2026", "§3.1 table"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A table is in the room. It is purple."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1")] }

def s3_3_bathroom : Datum :=
  { id := "spector2026_s3_3_bathroom"
    source := ⟨"spector-2026", "§3.3 bathroom"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is no bathroom in this house, or it is hidden."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3")] }

def ex_13 : Datum :=
  { id := "spector2026_13"
    source := ⟨"spector-2026", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either Matt does not live in Japan, or he has a female yoga teacher. True! He lives in Tokyo, and she is an excellent instructor."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.4")] }

def fn15_i : Datum :=
  { id := "spector2026_fn15_i"
    source := ⟨"spector-2026", "fn. 15 (i)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Matt bought a train ticket or an airplane ticket. It was expensive."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.4")] }

def s4_smokes : Datum :=
  { id := "spector2026_s4_smokes"
    source := ⟨"spector-2026", "§4 smokes"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Someone smokes. Someone drinks."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("one person smokes and drinks", .unacceptable)]
    paperFeatures := [("section", "4")] }

def ex_16a : Datum :=
  { id := "spector2026_16a"
    source := ⟨"spector-2026", "(16a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either the room is locked, or a female guitarist is playing. A woman is singing."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("a woman is singing, and the room is locked or one of the singing women is a guitarist playing", .unacceptable)]
    paperFeatures := [("section", "4")] }

def ex_17a : Datum :=
  { id := "spector2026_17a"
    source := ⟨"spector-2026", "(17a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There isn't anyone who didn't speak to someone."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("everyone spoke to someone (narrow scope)", .acceptable)]
    paperFeatures := [("section", "5")] }

def ex_17b : Datum :=
  { id := "spector2026_17b"
    source := ⟨"spector-2026", "(17b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not a single person failed to speak to someone."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("everyone spoke to someone (narrow scope)", .acceptable)]
    paperFeatures := [("section", "5")] }

def fn19_he : Datum :=
  { id := "spector2026_fn19_he"
    source := ⟨"spector-2026", "§6.2 he"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not every male student came. He stayed home."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := [("he = a male student who did not come", .unacceptable)]
    paperFeatures := [("section", "6.2")] }

def fn19_they : Datum :=
  { id := "spector2026_fn19_they"
    source := ⟨"spector-2026", "fn. 19 they"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not every student came. They all stayed home."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("they = all the students", .acceptable), ("they = the students who did not come", .unacceptable)]
    paperFeatures := [("section", "6.2")] }

def ex_35 : Datum :=
  { id := "spector2026_35"
    source := ⟨"spector-2026", "(35)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every student read a book. A student liked it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.6")] }

def ex_39 : Datum :=
  { id := "spector2026_39"
    source := ⟨"spector-2026", "(39)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is not true that Sue has a donkey and that she beats it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("Sue has no donkey or a donkey she does not beat (weak)", .unacceptable), ("Sue beats no donkey she has", .acceptable)]
    paperFeatures := [("section", "7")] }

def ex_41 : Datum :=
  { id := "spector2026_41"
    source := ⟨"spector-2026", "(41)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is not true that Sue has an umbrella and that she left it home."
    glossedTokens := []
    context := "Sue has two umbrellas, and she took one with her and left the other one at home."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7")] }

def ex_43 : Datum :=
  { id := "spector2026_43"
    source := ⟨"spector-2026", "(43)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No farmer who owns a donkey beats it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("no farmer who owns a donkey beats any donkey they have", .acceptable)]
    paperFeatures := [("section", "7")] }

def ex_45 : Datum :=
  { id := "spector2026_45"
    source := ⟨"spector-2026", "(45)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No student who has an umbrella left it home."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("no student who has an umbrella left every umbrella they have at home", .acceptable)]
    paperFeatures := [("section", "7")] }

def ex_47a : Datum :=
  { id := "spector2026_47a"
    source := ⟨"spector-2026", "(47a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is a bathroom and it is upstairs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7")] }

def ex_47b : Datum :=
  { id := "spector2026_47b"
    source := ⟨"spector-2026", "(47b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either there isn't a bathroom, or it is upstairs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7")] }

def ex_47c : Datum :=
  { id := "spector2026_47c"
    source := ⟨"spector-2026", "(47c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is not true that there is a bathroom and that it is upstairs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7")] }

def ex_47d : Datum :=
  { id := "spector2026_47d"
    source := ⟨"spector-2026", "(47d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every farmer who owns a donkey beats it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7")] }

def ex_47e : Datum :=
  { id := "spector2026_47e"
    source := ⟨"spector-2026", "(47e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some farmer who owns a donkey beats it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7")] }

def ex_48 : Datum :=
  { id := "spector2026_48"
    source := ⟨"spector-2026", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue has an umbrella but she left it home."
    glossedTokens := []
    context := "It is raining."
    judgment := .acceptable
    contrasts := []
    readings := [("Sue left every umbrella she has home", .acceptable)]
    paperFeatures := [("section", "7")] }

def ex_49 : Datum :=
  { id := "spector2026_49"
    source := ⟨"spector-2026", "(49)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some students who have an umbrella left it home."
    glossedTokens := []
    context := "It is raining."
    judgment := .acceptable
    contrasts := []
    readings := [("some students left all their umbrellas home", .acceptable)]
    paperFeatures := [("section", "7")] }

def ex_50 : Datum :=
  { id := "spector2026_50"
    source := ⟨"spector-2026", "(50)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue has at least one umbrella, but she left it home."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7")] }

def ex_51 : Datum :=
  { id := "spector2026_51"
    source := ⟨"spector-2026", "(51)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some students who have at least one umbrella left it home."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7")] }

def ex_52 : Datum :=
  { id := "spector2026_52"
    source := ⟨"spector-2026", "(52)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Gloria has a credit card but did not pay with it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("every credit card she has is one she did not pay with (strong)", .acceptable)]
    paperFeatures := [("section", "7")] }

def ex_53 : Datum :=
  { id := "spector2026_53"
    source := ⟨"spector-2026", "(53)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Gloria has a credit card (and probably more than one), but she did not pay with it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7")] }

def ex_54 : Datum :=
  { id := "spector2026_54"
    source := ⟨"spector-2026", "(54)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either it's not the case that Sue has a credit card and bought a cake with it, or she also used it to buy a book."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("either Sue has no card she bought a cake with, or she has one she bought a cake and a book with", .acceptable)]
    paperFeatures := [("section", "7")] }

def ex_58a : Datum :=
  { id := "spector2026_58a"
    source := ⟨"spector-2026", "(58a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue has an umbrella and she left it home."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7")] }

def ex_61 : Datum :=
  { id := "spector2026_61"
    source := ⟨"spector-2026", "(61)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every student read a book, and a student liked it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("one student liked the book they read", .acceptable)]
    paperFeatures := [("section", "App.")] }

def all : List Datum := [ex_1a, ex_3a, ex_3b, ex_4, ex_5, s2_2_singing, s3_1_purple, s3_1_table, s3_3_bathroom, ex_13, fn15_i, s4_smokes, ex_16a, ex_17a, ex_17b, fn19_he, fn19_they, ex_35, ex_39, ex_41, ex_43, ex_45, ex_47a, ex_47b, ex_47c, ex_47d, ex_47e, ex_48, ex_49, ex_50, ex_51, ex_52, ex_53, ex_54, ex_58a, ex_61]

end Spector2026.Examples
