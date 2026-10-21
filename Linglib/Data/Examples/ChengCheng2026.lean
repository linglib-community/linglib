module

public import Linglib.Data.Examples.Schema

/-!
# `ChengCheng2026` — typed example data

Auto-generated from `Linglib/Data/Examples/ChengCheng2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ChengCheng2026.Examples`.
-/

@[expose] public section

namespace ChengCheng2026.Examples

def ex_44a : Datum :=
  { id := "chengcheng2026_44a"
    source := ⟨"cheng-cheng-2026", "(44a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Tā yǐjīng dǎ le diànhuà."
    glossedTokens := [("Tā", "3SG"), ("yǐjīng", "already"), ("dǎ", "hit"), ("le", "PFV"), ("diànhuà", "telephone")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("test", "aspect"), ("combination", "N"), ("separated", "yes")] }

def ex_44b : Datum :=
  { id := "chengcheng2026_44b"
    source := ⟨"cheng-cheng-2026", "(44b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Tā yǐjīng dǎ le sǎo jiàoshì."
    glossedTokens := [("Tā", "3SG"), ("yǐjīng", "already"), ("dǎ", "hit"), ("le", "PFV"), ("sǎo", "sweep"), ("jiàoshì", "classroom")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("test", "aspect"), ("combination", "R"), ("separated", "yes")] }

def ex_44c : Datum :=
  { id := "chengcheng2026_44c"
    source := ⟨"cheng-cheng-2026", "(44c)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Tā yǐjīng dǎ-sǎo le jiàoshì."
    glossedTokens := [("Tā", "3SG"), ("yǐjīng", "already"), ("dǎ-sǎo", "hit-sweep"), ("le", "PFV"), ("jiàoshì", "classroom")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("test", "aspect"), ("combination", "R"), ("separated", "no")] }

def ex_46a : Datum :=
  { id := "chengcheng2026_46a"
    source := ⟨"cheng-cheng-2026", "(46a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Diànhuà tā dǎ shì dǎ le, dànshì méi zhǎodào rén."
    glossedTokens := [("Diànhuà", "telephone"), ("tā", "3SG"), ("dǎ", "hit"), ("shì", "COP"), ("dǎ", "hit"), ("le", "PFV"), ("dànshì", "but"), ("méi", "NEG"), ("zhǎodào", "find"), ("rén", "people")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("test", "cleft"), ("combination", "N"), ("separated", "yes")] }

def ex_46b : Datum :=
  { id := "chengcheng2026_46b"
    source := ⟨"cheng-cheng-2026", "(46b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Jiàoshì tā dǎ shì dǎ-sǎo le, dànshì méi dǎ-sǎo hǎo."
    glossedTokens := [("Jiàoshì", "classroom"), ("tā", "3SG"), ("dǎ", "hit"), ("shì", "COP"), ("dǎ-sǎo", "hit-sweep"), ("le", "PFV"), ("dànshì", "but"), ("méi", "NEG"), ("dǎ-sǎo", "hit-sweep"), ("hǎo", "good")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("test", "cleft"), ("combination", "R"), ("separated", "yes")] }

def ex_46c : Datum :=
  { id := "chengcheng2026_46c"
    source := ⟨"cheng-cheng-2026", "(46c)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Jiàoshì tā dǎ-sǎo shì dǎ-sǎo le, dànshì méi dǎ-sǎo hǎo."
    glossedTokens := [("Jiàoshì", "classroom"), ("tā", "3SG"), ("dǎ-sǎo", "hit-sweep"), ("shì", "COP"), ("dǎ-sǎo", "hit-sweep"), ("le", "PFV"), ("dànshì", "but"), ("méi", "NEG"), ("dǎ-sǎo", "hit-sweep"), ("hǎo", "good")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("test", "cleft"), ("combination", "R"), ("separated", "no")] }

def ex_48a : Datum :=
  { id := "chengcheng2026_48a"
    source := ⟨"cheng-cheng-2026", "(48a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Tā dǎ diànhuà le ma? Dǎ le."
    glossedTokens := [("Tā", "3SG"), ("dǎ", "hit"), ("diànhuà", "telephone"), ("le", "PFV"), ("ma", "Q"), ("Dǎ", "hit"), ("le", "PFV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("test", "fragment"), ("combination", "N"), ("separated", "yes")] }

def ex_48b_da : Datum :=
  { id := "chengcheng2026_48b_da"
    source := ⟨"cheng-cheng-2026", "(48b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Tā dǎ-sǎo jiàoshì le ma? Dǎ le."
    glossedTokens := [("Tā", "3SG"), ("dǎ-sǎo", "hit-sweep"), ("jiàoshì", "classroom"), ("le", "PFV"), ("ma", "Q"), ("Dǎ", "hit"), ("le", "PFV")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("test", "fragment"), ("combination", "R"), ("separated", "yes")] }

def ex_48b_dasao : Datum :=
  { id := "chengcheng2026_48b_dasao"
    source := ⟨"cheng-cheng-2026", "(48b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Tā dǎ-sǎo jiàoshì le ma? Dǎ-sǎo le."
    glossedTokens := [("Tā", "3SG"), ("dǎ-sǎo", "hit-sweep"), ("jiàoshì", "classroom"), ("le", "PFV"), ("ma", "Q"), ("Dǎ-sǎo", "hit-sweep"), ("le", "PFV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("test", "fragment"), ("combination", "R"), ("separated", "no")] }

def ex_49a : Datum :=
  { id := "chengcheng2026_49a"
    source := ⟨"cheng-cheng-2026", "(49a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Tā gěi māma dǎ le diànhuà, wǒ yě dǎ le."
    glossedTokens := [("Tā", "3SG"), ("gěi", "APPL"), ("māma", "mother"), ("dǎ", "hit"), ("le", "PFV"), ("diànhuà", "telephone"), ("wǒ", "1SG"), ("yě", "also"), ("dǎ", "hit"), ("le", "PFV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("test", "ellipsis"), ("combination", "N"), ("separated", "yes")] }

def ex_49b_da : Datum :=
  { id := "chengcheng2026_49b_da"
    source := ⟨"cheng-cheng-2026", "(49b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Tā dǎ-sǎo le tā de fángjiān, wǒ yě dǎ le."
    glossedTokens := [("Tā", "3SG"), ("dǎ-sǎo", "hit-sweep"), ("le", "PFV"), ("tā", "3SG"), ("de", "POSS"), ("fángjiān", "room"), ("wǒ", "1SG"), ("yě", "also"), ("dǎ", "hit"), ("le", "PFV")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("test", "ellipsis"), ("combination", "R"), ("separated", "yes")] }

def ex_49b_dasao : Datum :=
  { id := "chengcheng2026_49b_dasao"
    source := ⟨"cheng-cheng-2026", "(49b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Tā dǎ-sǎo le tā de fángjiān, wǒ yě dǎ-sǎo le."
    glossedTokens := [("Tā", "3SG"), ("dǎ-sǎo", "hit-sweep"), ("le", "PFV"), ("tā", "3SG"), ("de", "POSS"), ("fángjiān", "room"), ("wǒ", "1SG"), ("yě", "also"), ("dǎ-sǎo", "hit-sweep"), ("le", "PFV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("test", "ellipsis"), ("combination", "R"), ("separated", "no")] }

def ex_30a : Datum :=
  { id := "chengcheng2026_30a"
    source := ⟨"cheng-cheng-2026", "(30a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhāngsān bǎ fángjiān gěi dǎ-sǎo gānjìng le."
    glossedTokens := [("Zhāngsān", "Zhangsan"), ("bǎ", "BA"), ("fángjiān", "room"), ("gěi", "GIVE"), ("dǎ-sǎo", "hit-sweep"), ("gānjìng", "clean"), ("le", "PFV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("exponent", "bǎ"), ("exponent", "gěi"), ("exponent", "dǎ")] }

def ex_30b : Datum :=
  { id := "chengcheng2026_30b"
    source := ⟨"cheng-cheng-2026", "(30b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Nǐ bǎ diànhuà gěi dǎ le ba!"
    glossedTokens := [("Nǐ", "you"), ("bǎ", "BA"), ("diànhuà", "telephone"), ("gěi", "GIVE"), ("dǎ", "hit"), ("le", "PFV"), ("ba", "SFP")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("exponent", "bǎ"), ("exponent", "gěi"), ("exponent", "dǎ")] }

def all : List Datum := [ex_44a, ex_44b, ex_44c, ex_46a, ex_46b, ex_46c, ex_48a, ex_48b_da, ex_48b_dasao, ex_49a, ex_49b_da, ex_49b_dasao, ex_30a, ex_30b]

end ChengCheng2026.Examples
