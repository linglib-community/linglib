module

public import Linglib.Data.Examples.Schema

/-!
# `ColeHermon2008` — typed example data

Auto-generated from `Linglib/Data/Examples/ColeHermon2008.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ColeHermon2008.Examples`.
-/

@[expose] public section

namespace ColeHermon2008.Examples

def ex3a : Datum :=
  { id := "colehermon2008_ex3a"
    source := ⟨"cole-hermon-2008", "(3a)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Dakdanak-an mang-atuk biang-i."
    glossedTokens := [("Dakdanak-an", "child-that"), ("mang-atuk", "ACT-hit"), ("biang-i", "dog-DEF")]
    context := "Active clause in SVO order."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("agent", "dakdanak-an"), ("patient", "biang-i")] }

def ex3b : Datum :=
  { id := "colehermon2008_ex3b"
    source := ⟨"cole-hermon-2008", "(3b)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Mang-atuk biang-i dakdanak-an."
    glossedTokens := [("Mang-atuk", "ACT-hit"), ("biang-i", "dog-DEF"), ("dakdanak-an", "child-that")]
    context := "Active clause in VOS order."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("agent", "dakdanak-an"), ("patient", "biang-i")] }

def ex4a : Datum :=
  { id := "colehermon2008_ex4a"
    source := ⟨"cole-hermon-2008", "(4a)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Biang-i di-atuk si-John."
    glossedTokens := [("Biang-i", "dog-DEF"), ("di-atuk", "PASS-hit"), ("si-John", "HON-John")]
    context := "Passive clause in SVO order."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("agent", "si-John"), ("patient", "biang-i")] }

def ex4b : Datum :=
  { id := "colehermon2008_ex4b"
    source := ⟨"cole-hermon-2008", "(4b)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Di-atuk si-John biang-i."
    glossedTokens := [("Di-atuk", "PASS-hit"), ("si-John", "HON-John"), ("biang-i", "dog-DEF")]
    context := "Passive clause in VOS order."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("agent", "si-John"), ("patient", "biang-i")] }

def ex7a : Datum :=
  { id := "colehermon2008_ex7a"
    source := ⟨"cole-hermon-2008", "(7a)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Aha si-John mang-alean tu si-Mary?"
    glossedTokens := [("Aha", "what"), ("si-John", "HON-John"), ("mang-alean", "ACT-give"), ("tu", "to"), ("si-Mary", "HON-Mary")]
    context := "The wh-object of an active ditransitive fronted; the subject precedes the verb."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("agent", "si-John"), ("patient", "aha"), ("goal", "tu si-Mary")] }

def ex7b : Datum :=
  { id := "colehermon2008_ex7b"
    source := ⟨"cole-hermon-2008", "(7b)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Mang-allang aha do dakdanak-i?"
    glossedTokens := [("Mang-allang", "ACT-eat"), ("aha", "what"), ("do", "FOC"), ("dakdanak-i", "child-DEF")]
    context := "The wh-object of an active clause in situ, immediately after the verb."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("agent", "dakdanak-i"), ("patient", "aha")] }

def ex8a : Datum :=
  { id := "colehermon2008_ex8a"
    source := ⟨"cole-hermon-2008", "(8a)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Ise di-lean buku tu si-Mary?"
    glossedTokens := [("Ise", "who"), ("di-lean", "PASS-give"), ("buku", "book"), ("tu", "to"), ("si-Mary", "HON-Mary")]
    context := "The wh-agent of a passive ditransitive fronted."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("agent", "ise"), ("patient", "buku"), ("goal", "tu si-Mary")] }

def ex8b : Datum :=
  { id := "colehermon2008_ex8b"
    source := ⟨"cole-hermon-2008", "(8b)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Di-lean ise do tu si-Mary sada bunga?"
    glossedTokens := [("Di-lean", "PASS-give"), ("ise", "who"), ("do", "FOC"), ("tu", "to"), ("si-Mary", "HON-Mary"), ("sada", "some"), ("bunga", "flower")]
    context := "The wh-agent of a passive ditransitive in situ, immediately after the verb."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("agent", "ise"), ("patient", "sada bunga"), ("goal", "tu si-Mary")] }

def ex9 : Datum :=
  { id := "colehermon2008_ex9"
    source := ⟨"cole-hermon-2008", "(9)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Tu ise mang-alean buku si-John?"
    glossedTokens := [("Tu", "to"), ("ise", "who"), ("mang-alean", "ACT-give"), ("buku", "book"), ("si-John", "HON-John")]
    context := "The wh-goal PP of an active ditransitive fronted."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("agent", "si-John"), ("patient", "buku"), ("goal", "tu ise")] }

def ex10 : Datum :=
  { id := "colehermon2008_ex10"
    source := ⟨"cole-hermon-2008", "(10)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Tu ise do di-lean si-John buku?"
    glossedTokens := [("Tu", "to"), ("ise", "who"), ("do", "FOC"), ("di-lean", "PASS-give"), ("si-John", "HON-John"), ("buku", "book")]
    context := "The wh-goal PP of a passive ditransitive fronted."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("agent", "si-John"), ("patient", "buku"), ("goal", "tu ise")] }

def ex13 : Datum :=
  { id := "colehermon2008_ex13"
    source := ⟨"cole-hermon-2008", "(13)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Di-lean si-John sada buku tu si-Mary."
    glossedTokens := [("Di-lean", "PASS-give"), ("si-John", "HON-John"), ("sada", "one"), ("buku", "book"), ("tu", "to"), ("si-Mary", "HON-Mary")]
    context := "Passive ditransitive with the indirect object after the subject."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("agent", "si-John"), ("patient", "sada buku"), ("goal", "tu si-Mary")] }

def ex14 : Datum :=
  { id := "colehermon2008_ex14"
    source := ⟨"cole-hermon-2008", "(14)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Di-lean si-John tu si-Mary buku."
    glossedTokens := [("Di-lean", "PASS-give"), ("si-John", "HON-John"), ("tu", "to"), ("si-Mary", "HON-Mary"), ("buku", "book")]
    context := "Passive ditransitive with the indirect object before the subject."
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("agent", "si-John"), ("patient", "buku"), ("goal", "tu si-Mary")] }

def ex17 : Datum :=
  { id := "colehermon2008_ex17"
    source := ⟨"cole-hermon-2008", "(17)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Si-Bunga mang-ida dirina sandiri."
    glossedTokens := [("Si-Bunga", "HON-Bunga"), ("mang-ida", "ACT-see"), ("dirina sandiri", "herself")]
    context := "Active clause in SVO order; the subject antecedes a reflexive direct object."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("agent", "si-Bunga"), ("patient", "dirina sandiri"), ("antecedent", "agent"), ("tableOne", "A")] }

def ex21 : Datum :=
  { id := "colehermon2008_ex21"
    source := ⟨"cole-hermon-2008", "(21)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Dirina sandiri pa-ias-hon dakdanak-i."
    glossedTokens := [("Dirina sandiri", "self"), ("pa-ias-hon", "make-clean-CAUS"), ("dakdanak-i", "child-DEF")]
    context := "Active clause in SVO order; the direct object would antecede a reflexive subject."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("agent", "dirina sandiri"), ("patient", "dakdanak-i"), ("antecedent", "patient"), ("tableOne", "C")] }

def ex37 : Datum :=
  { id := "colehermon2008_ex37"
    source := ⟨"cole-hermon-2008", "(37)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Si-Bunga di-ida dirina sandiri."
    glossedTokens := [("Si-Bunga", "HON-Bunga"), ("di-ida", "PASS-see"), ("dirina sandiri", "self")]
    context := "Passive clause in SVO order; the passive subject antecedes a reflexive passive agent."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("agent", "dirina sandiri"), ("patient", "si-Bunga"), ("antecedent", "patient"), ("tableOne", "B")] }

def ex43 : Datum :=
  { id := "colehermon2008_ex43"
    source := ⟨"cole-hermon-2008", "(43)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Aha mang-atuk si-John?"
    glossedTokens := [("Aha", "what"), ("mang-atuk", "ACT-hit"), ("si-John", "HON-John")]
    context := "The wh-object of an active monotransitive fronted."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("agent", "si-John"), ("patient", "aha")] }

def ex44 : Datum :=
  { id := "colehermon2008_ex44"
    source := ⟨"cole-hermon-2008", "(44)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Mang-atuk aha si-John?"
    glossedTokens := [("Mang-atuk", "ACT-hit"), ("aha", "what"), ("si-John", "HON-John")]
    context := "The wh-object of an active monotransitive in situ."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("agent", "si-John"), ("patient", "aha")] }

def ex49 : Datum :=
  { id := "colehermon2008_ex49"
    source := ⟨"cole-hermon-2008", "(49)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Mang-ida si-Mary si-John."
    glossedTokens := [("Mang-ida", "ACT-see"), ("si-Mary", "HON-Mary"), ("si-John", "HON-John")]
    context := "Active monotransitive clause in VOS order."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("agent", "si-John"), ("patient", "si-Mary")] }

def ex56 : Datum :=
  { id := "colehermon2008_ex56"
    source := ⟨"cole-hermon-2008", "(56)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Mang-alean buku si-John tu si-Mary."
    glossedTokens := [("Mang-alean", "ACT-give"), ("buku", "book"), ("si-John", "HON-John"), ("tu", "to"), ("si-Mary", "HON-Mary")]
    context := "Active ditransitive clause in VOS order."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("agent", "si-John"), ("patient", "buku"), ("goal", "tu si-Mary")] }

def ex62 : Datum :=
  { id := "colehermon2008_ex62"
    source := ⟨"cole-hermon-2008", "(62)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Mang-ida dirina sandiri si-Bunga."
    glossedTokens := [("Mang-ida", "ACT-see"), ("dirina sandiri", "herself"), ("si-Bunga", "HON-Bunga")]
    context := "Active clause in VOS order; the subject antecedes a reflexive direct object."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("agent", "si-Bunga"), ("patient", "dirina sandiri"), ("antecedent", "agent"), ("tableOne", "A")] }

def ex66 : Datum :=
  { id := "colehermon2008_ex66"
    source := ⟨"cole-hermon-2008", "(66)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Dirina sandiri mang-ida si-Bunga."
    glossedTokens := [("Dirina sandiri", "herself"), ("mang-ida", "ACT-see"), ("si-Bunga", "HON-Bunga")]
    context := "Active clause in SVO order; the direct object would antecede a reflexive subject."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("agent", "dirina sandiri"), ("patient", "si-Bunga"), ("antecedent", "patient"), ("tableOne", "C")] }

def ex67 : Datum :=
  { id := "colehermon2008_ex67"
    source := ⟨"cole-hermon-2008", "(67)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Di-ida si-Torus dirina sandiri."
    glossedTokens := [("Di-ida", "PASS-see"), ("si-Torus", "HON-Torus"), ("dirina sandiri", "himself")]
    context := "Passive clause in VOS order; the passive agent antecedes a reflexive passive subject."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("agent", "si-Torus"), ("patient", "dirina sandiri"), ("antecedent", "agent"), ("tableOne", "A")] }

def ex68 : Datum :=
  { id := "colehermon2008_ex68"
    source := ⟨"cole-hermon-2008", "(68)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Di-ida dirina sandiri si-John."
    glossedTokens := [("Di-ida", "PASS-see"), ("dirina sandiri", "self"), ("si-John", "HON-John")]
    context := "Passive clause in VOS order; the passive subject antecedes a reflexive passive agent."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("agent", "dirina sandiri"), ("patient", "si-John"), ("antecedent", "patient"), ("tableOne", "B")] }

def ex81 : Datum :=
  { id := "colehermon2008_ex81"
    source := ⟨"cole-hermon-2008", "(81)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Dakdanak-on mang-atuk biang-i."
    glossedTokens := [("Dakdanak-on", "child-this"), ("mang-atuk", "ACT-hit"), ("biang-i", "dog-DEF")]
    context := "Active clause in SVO order."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("agent", "dakdanak-on"), ("patient", "biang-i")] }

def ex85 : Datum :=
  { id := "colehermon2008_ex85"
    source := ⟨"cole-hermon-2008", "(85)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Si-John mang-alean aha tu si-Mary?"
    glossedTokens := [("Si-John", "HON-John"), ("mang-alean", "ACT-give"), ("aha", "what"), ("tu", "to"), ("si-Mary", "HON-Mary")]
    context := "The wh-object of an active ditransitive in SVO order in situ."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("agent", "si-John"), ("patient", "aha"), ("goal", "tu si-Mary")] }

def ex87 : Datum :=
  { id := "colehermon2008_ex87"
    source := ⟨"cole-hermon-2008", "(87)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Biang-i di-atuk ise?"
    glossedTokens := [("Biang-i", "dog-DEF"), ("di-atuk", "PASS-hit"), ("ise", "who")]
    context := "The wh-agent of a passive clause in SVO order in situ."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("agent", "ise"), ("patient", "biang-i")] }

def ex88 : Datum :=
  { id := "colehermon2008_ex88"
    source := ⟨"cole-hermon-2008", "(88)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Ise biang-i di-atuk?"
    glossedTokens := [("Ise", "who"), ("biang-i", "dog-DEF"), ("di-atuk", "PASS-hit")]
    context := "The wh-agent of a passive clause in SVO order fronted."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("agent", "ise"), ("patient", "biang-i")] }

def ex95 : Datum :=
  { id := "colehermon2008_ex95"
    source := ⟨"cole-hermon-2008", "(95)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The findings of the court were that the boy was injured by himself, and not by someone else."
    glossedTokens := []
    context := "English passive; the passive subject antecedes a reflexive in the by-phrase."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "patient")] }

def ex96 : Datum :=
  { id := "colehermon2008_ex96"
    source := ⟨"cole-hermon-2008", "(96)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The findings of the court were that himself was injured by the boy, and not by someone else."
    glossedTokens := []
    context := "English passive; the by-phrase agent would antecede a reflexive passive subject."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "agent")] }

def all : List Datum := [ex3a, ex3b, ex4a, ex4b, ex7a, ex7b, ex8a, ex8b, ex9, ex10, ex13, ex14, ex17, ex21, ex37, ex43, ex44, ex49, ex56, ex62, ex66, ex67, ex68, ex81, ex85, ex87, ex88, ex95, ex96]

end ColeHermon2008.Examples
