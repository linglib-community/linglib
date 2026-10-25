module

public import Linglib.Data.Examples.Schema

/-!
# `TsiliaZhao2026` — typed example data

Auto-generated from `Linglib/Data/Examples/TsiliaZhao2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace TsiliaZhao2026.Examples`.
-/

@[expose] public section

namespace TsiliaZhao2026.Examples

def ex_6 : Datum :=
  { id := "tsiliazhao2026_6"
    source := ⟨"tsilia-zhao-2026", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is feeling sick then."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("matrix", "present"), ("environment", "root"), ("then", "incompatible")] }

def ex_7a : Datum :=
  { id := "tsiliazhao2026_7a"
    source := ⟨"tsilia-zhao-2026", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary was feeling sick then."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("matrix", "past"), ("environment", "root"), ("then", "compatible")] }

def ex_7b : Datum :=
  { id := "tsiliazhao2026_7b"
    source := ⟨"tsilia-zhao-2026", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary will be feeling sick then."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("matrix", "future"), ("environment", "root"), ("then", "compatible")] }

def ex_8 : Datum :=
  { id := "tsiliazhao2026_8"
    source := ⟨"tsilia-zhao-2026", "(8)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "To 2000, o Yanis iksere oti i Maria ine egkios."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("shifted present: the pregnancy overlaps the knowledge in 2000", .acceptable)]
    paperFeatures := [("matrix", "past"), ("environment", "attitude report"), ("embedded", "present"), ("shifted", "yes")] }

def ex_11 : Datum :=
  { id := "tsiliazhao2026_11"
    source := ⟨"tsilia-zhao-2026", "(11)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "To 2000, o Yanis iksere oti i Maria ine egkios tote."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("matrix", "past"), ("environment", "attitude report"), ("embedded", "present"), ("shifted", "yes"), ("then", "incompatible")] }

def ex_9 : Datum :=
  { id := "tsiliazhao2026_9"
    source := ⟨"tsilia-zhao-2026", "(9)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "Lifney alpayim šana, Yosef xašav še Miriam ohevet oto az."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("matrix", "past"), ("environment", "attitude report"), ("embedded", "present"), ("shifted", "yes"), ("then", "incompatible")] }

def ex_10 : Datum :=
  { id := "tsiliazhao2026_10"
    source := ⟨"tsilia-zhao-2026", "(10)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "V 2016 godu Tanja skazala, čto Putin togda ∅ prezident Rossii."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("matrix", "past"), ("environment", "attitude report"), ("embedded", "present"), ("shifted", "yes"), ("then", "incompatible")] }

def ex_18 : Datum :=
  { id := "tsiliazhao2026_18"
    source := ⟨"tsilia-zhao-2026", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A month ago, John found out that Mary loves him."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("double access: Mary loves John at the utterance time and at the finding out", .acceptable)]
    paperFeatures := [("matrix", "past"), ("environment", "attitude report"), ("embedded", "present"), ("shifted", "no")] }

def ex_20 : Datum :=
  { id := "tsiliazhao2026_20"
    source := ⟨"tsilia-zhao-2026", "(20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A month ago, John found out that Mary loves him then."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("matrix", "past"), ("environment", "attitude report"), ("embedded", "present"), ("shifted", "no"), ("then", "incompatible")] }

def ex_21 : Datum :=
  { id := "tsiliazhao2026_21"
    source := ⟨"tsilia-zhao-2026", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In his childhood, Joseph met a woman who loves traveling then."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("matrix", "past"), ("environment", "relative clause"), ("embedded", "present"), ("shifted", "no"), ("then", "incompatible")] }

def ex_25 : Datum :=
  { id := "tsiliazhao2026_25"
    source := ⟨"tsilia-zhao-2026", "(25)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Prin 20 chronia o Pavlos sinerghastike me enan andra pu ine proedros tote."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("matrix", "past"), ("environment", "relative clause"), ("embedded", "present"), ("shifted", "no"), ("then", "incompatible")] }

def ex_28 : Datum :=
  { id := "tsiliazhao2026_28"
    source := ⟨"tsilia-zhao-2026", "(28)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "ninenn mae, Yusuke-wa Yukiko-ga tooji ninnshinn shite-iru to shitteita."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("matrix", "past"), ("environment", "attitude report"), ("embedded", "present"), ("shifted", "yes"), ("then", "incompatible")] }

def ex_29 : Datum :=
  { id := "tsiliazhao2026_29"
    source := ⟨"tsilia-zhao-2026", "(29)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "ninenn mae, Yusuke-wa tooji seifu de hatarai-te-iru hito to renkei o hakat-te-ita."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("matrix", "past"), ("environment", "relative clause"), ("embedded", "present"), ("shifted", "yes"), ("then", "incompatible")] }

def ex_30a : Datum :=
  { id := "tsiliazhao2026_30a"
    source := ⟨"tsilia-zhao-2026", "(30a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "To 2030, i Maria tha pi oti ine sti filaki tote."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("matrix", "future"), ("environment", "attitude report"), ("embedded", "present"), ("shifted", "yes"), ("then", "incompatible")] }

def ex_30d : Datum :=
  { id := "tsiliazhao2026_30d"
    source := ⟨"tsilia-zhao-2026", "(30d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In 2030, John will say that he is in jail then."
    glossedTokens := []
    context := ""
    judgment := .variable
    alternatives := []
    readings := []
    paperFeatures := [("matrix", "future"), ("environment", "attitude report"), ("embedded", "present"), ("shifted", "deleted"), ("then", "variation")] }

def ex_31a : Datum :=
  { id := "tsiliazhao2026_31a"
    source := ⟨"tsilia-zhao-2026", "(31a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "To 2030, i Zoi tha ine pantremeni me kapion pu ine tote sti filaki."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("matrix", "future"), ("environment", "relative clause"), ("embedded", "present"), ("shifted", "yes"), ("then", "incompatible")] }

def ex_31d : Datum :=
  { id := "tsiliazhao2026_31d"
    source := ⟨"tsilia-zhao-2026", "(31d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In 2030, John will be married to someone who is in jail then."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("matrix", "future"), ("environment", "relative clause"), ("embedded", "present"), ("shifted", "deleted"), ("then", "compatible")] }

def ex_32 : Datum :=
  { id := "tsiliazhao2026_32"
    source := ⟨"tsilia-zhao-2026", "(32)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Tooji ai-mashou."
    glossedTokens := []
    context := "Two friends are making plans to go to the movies on Saturday; one says this before they leave."
    judgment := .ungrammatical
    alternatives := [("Sonotoki ai-mashou.", .acceptable)]
    readings := []
    paperFeatures := [("matrix", "future"), ("then", "past-oriented only")] }

def ex_38 : Datum :=
  { id := "tsiliazhao2026_38"
    source := ⟨"tsilia-zhao-2026", "(38)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "lifney alpayim šana, Yosef xašav še Miriam ahava oto az."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous: the love overlaps the belief", .acceptable)]
    paperFeatures := [("matrix", "past"), ("environment", "attitude report"), ("embedded", "past"), ("then", "compatible")] }

def ex_48 : Datum :=
  { id := "tsiliazhao2026_48"
    source := ⟨"tsilia-zhao-2026", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A week ago, John said that in ten days he would say to his girlfriend that they were meeting then for the last time."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("the meeting is at the time of the future saying, three days from now", .acceptable)]
    paperFeatures := [("matrix", "past"), ("environment", "attitude report"), ("embedded", "deleted past"), ("then", "compatible")] }

def ex_99 : Datum :=
  { id := "tsiliazhao2026_99"
    source := ⟨"tsilia-zhao-2026", "(99)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "To 1960, o Yanis iksere oti i Maria ine omorfi tora."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("matrix", "past"), ("environment", "attitude report"), ("embedded", "present"), ("shifted", "yes"), ("indexical", "unshifted")] }

def all : List Datum := [ex_6, ex_7a, ex_7b, ex_8, ex_11, ex_9, ex_10, ex_18, ex_20, ex_21, ex_25, ex_28, ex_29, ex_30a, ex_30d, ex_31a, ex_31d, ex_32, ex_38, ex_48, ex_99]

end TsiliaZhao2026.Examples
