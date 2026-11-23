module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `FaustLampitelli2026` — typed example data

Auto-generated from `Linglib/Data/Examples/FaustLampitelli2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace FaustLampitelli2026.Examples`.
-/

@[expose] public section

namespace FaustLampitelli2026.Examples

def ex_4a_depPrf : Datum :=
  { id := "faustlampitelli2026_4a_depPrf"
    source := ⟨"faust-lampitelli-2026", "(4a)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "gʌrʌf-"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "whip"), ("template", "depPrf")] }

def ex_4a_prf : Datum :=
  { id := "faustlampitelli2026_4a_prf"
    source := ⟨"faust-lampitelli-2026", "(4a)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "gʌrif-"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "whip"), ("template", "prf")] }

def ex_4a_imprf : Datum :=
  { id := "faustlampitelli2026_4a_imprf"
    source := ⟨"faust-lampitelli-2026", "(4a)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "-gʌrrɨf"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "whip"), ("template", "imprf")] }

def ex_4b_depPrf : Datum :=
  { id := "faustlampitelli2026_4b_depPrf"
    source := ⟨"faust-lampitelli-2026", "(4b)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "sʌmaʕ-"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "hear"), ("template", "depPrf")] }

def ex_4b_prf : Datum :=
  { id := "faustlampitelli2026_4b_prf"
    source := ⟨"faust-lampitelli-2026", "(4b)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "sʌmiʕ-"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "hear"), ("template", "prf")] }

def ex_4b_imprf : Datum :=
  { id := "faustlampitelli2026_4b_imprf"
    source := ⟨"faust-lampitelli-2026", "(4b)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "-sʌmmɨʕ"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "hear"), ("template", "imprf")] }

def ex_4c_depPrf : Datum :=
  { id := "faustlampitelli2026_4c_depPrf"
    source := ⟨"faust-lampitelli-2026", "(4c)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "ʔasʌr-"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "arrest"), ("template", "depPrf")] }

def ex_4c_prf : Datum :=
  { id := "faustlampitelli2026_4c_prf"
    source := ⟨"faust-lampitelli-2026", "(4c)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "ʔasir-"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "arrest"), ("template", "prf")] }

def ex_4c_imprf : Datum :=
  { id := "faustlampitelli2026_4c_imprf"
    source := ⟨"faust-lampitelli-2026", "(4c)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "-ʔassɨr"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "arrest"), ("template", "imprf")] }

def ex_4d_depPrf : Datum :=
  { id := "faustlampitelli2026_4d_depPrf"
    source := ⟨"faust-lampitelli-2026", "(4d)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "saħab-"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("sɨħab-", .acceptable)]
    readings := []
    paperFeatures := [("root", "pull"), ("template", "depPrf")] }

def ex_4d_prf : Datum :=
  { id := "faustlampitelli2026_4d_prf"
    source := ⟨"faust-lampitelli-2026", "(4d)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "siħib-"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "pull"), ("template", "prf")] }

def ex_4d_imprf : Datum :=
  { id := "faustlampitelli2026_4d_imprf"
    source := ⟨"faust-lampitelli-2026", "(4d)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "-sɨħɨb"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "pull"), ("template", "imprf")] }

def ex_5a_juss : Datum :=
  { id := "faustlampitelli2026_5a_juss"
    source := ⟨"faust-lampitelli-2026", "(5a)"⟩
    reportedIn := none
    language := "tigr1270"
    primaryText := "tɨ-mazzɨn"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "weigh"), ("template", "jussGem2")] }

def ex_5a_imp : Datum :=
  { id := "faustlampitelli2026_5a_imp"
    source := ⟨"faust-lampitelli-2026", "(5a)"⟩
    reportedIn := none
    language := "tigr1270"
    primaryText := "mazzɨn"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "weigh"), ("template", "impGem")] }

def ex_5b_juss : Datum :=
  { id := "faustlampitelli2026_5b_juss"
    source := ⟨"faust-lampitelli-2026", "(5b)"⟩
    reportedIn := none
    language := "tigr1270"
    primaryText := "tɨ-fgʌr"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "leave"), ("template", "juss2")] }

def ex_5b_imp : Datum :=
  { id := "faustlampitelli2026_5b_imp"
    source := ⟨"faust-lampitelli-2026", "(5b)"⟩
    reportedIn := none
    language := "tigr1270"
    primaryText := "fɨgʌr"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "leave"), ("template", "imp")] }

def ex_5c_juss : Datum :=
  { id := "faustlampitelli2026_5c_juss"
    source := ⟨"faust-lampitelli-2026", "(5c)"⟩
    reportedIn := none
    language := "tigr1270"
    primaryText := "tɨ-kˀnʌsˁ"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "getUp"), ("template", "juss2")] }

def ex_5c_imp : Datum :=
  { id := "faustlampitelli2026_5c_imp"
    source := ⟨"faust-lampitelli-2026", "(5c)"⟩
    reportedIn := none
    language := "tigr1270"
    primaryText := "kˀɨnʌsˁ"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "getUp"), ("template", "imp")] }

def ex_6a_prf : Datum :=
  { id := "faustlampitelli2026_6a_prf"
    source := ⟨"faust-lampitelli-2026", "(6a)"⟩
    reportedIn := none
    language := "tigr1270"
    primaryText := "fagr-a"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "leave"), ("template", "prf3"), ("suffix", "a")] }

def ex_6b_prf : Datum :=
  { id := "faustlampitelli2026_6b_prf"
    source := ⟨"faust-lampitelli-2026", "(6b)"⟩
    reportedIn := none
    language := "tigr1270"
    primaryText := "ħatˁb-a"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "wash"), ("template", "prf3"), ("suffix", "a")] }

def ex_6b_juss : Datum :=
  { id := "faustlampitelli2026_6b_juss"
    source := ⟨"faust-lampitelli-2026", "(6b)"⟩
    reportedIn := none
    language := "tigr1270"
    primaryText := "tɨ-ħɨtˁʌb"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "wash"), ("template", "juss2")] }

def ex_6c_prf : Datum :=
  { id := "faustlampitelli2026_6c_prf"
    source := ⟨"faust-lampitelli-2026", "(6c)"⟩
    reportedIn := none
    language := "tigr1270"
    primaryText := "harb-a"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "flee"), ("template", "prf3"), ("suffix", "a")] }

def ex_7a : Datum :=
  { id := "faustlampitelli2026_7a"
    source := ⟨"faust-lampitelli-2026", "(7a)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "tɨ-gʌrrɨf"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "whip"), ("template", "imprf2")] }

def ex_7b : Datum :=
  { id := "faustlampitelli2026_7b"
    source := ⟨"faust-lampitelli-2026", "(7b)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "ta-ħarrɨd"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "slaughter"), ("template", "imprf2")] }

def ex_7c : Datum :=
  { id := "faustlampitelli2026_7c"
    source := ⟨"faust-lampitelli-2026", "(7c)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "ta-ħadɨm"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "escape"), ("template", "imprf2NoGem")] }

def ex_7d : Datum :=
  { id := "faustlampitelli2026_7d"
    source := ⟨"faust-lampitelli-2026", "(7d)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "gɨrʌf"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "whip"), ("template", "imp")] }

def ex_7e : Datum :=
  { id := "faustlampitelli2026_7e"
    source := ⟨"faust-lampitelli-2026", "(7e)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "mahar"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "teach"), ("template", "imp")] }

def ex_7f : Datum :=
  { id := "faustlampitelli2026_7f"
    source := ⟨"faust-lampitelli-2026", "(7f)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "saʔal"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "ask"), ("template", "imp")] }

def ex_10a_f : Datum :=
  { id := "faustlampitelli2026_10a_f"
    source := ⟨"faust-lampitelli-2026", "(10a)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "gɨrʌf-i"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "whip"), ("template", "imp"), ("suffix", "i")] }

def ex_10b_m : Datum :=
  { id := "faustlampitelli2026_10b_m"
    source := ⟨"faust-lampitelli-2026", "(10b)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "nɨβaħ"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "bark"), ("template", "imp")] }

def ex_10b_f : Datum :=
  { id := "faustlampitelli2026_10b_f"
    source := ⟨"faust-lampitelli-2026", "(10b)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "nɨbħ-i"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "bark"), ("template", "imp"), ("suffix", "i")] }

def ex_10c_m : Datum :=
  { id := "faustlampitelli2026_10c_m"
    source := ⟨"faust-lampitelli-2026", "(10c)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "sɨmaʕ"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "hear"), ("template", "imp")] }

def ex_10c_f : Datum :=
  { id := "faustlampitelli2026_10c_f"
    source := ⟨"faust-lampitelli-2026", "(10c)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "sɨmʕ-i"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "hear"), ("template", "imp"), ("suffix", "i")] }

def ex_10d_m : Datum :=
  { id := "faustlampitelli2026_10d_m"
    source := ⟨"faust-lampitelli-2026", "(10d)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "gɨlah"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "uncover"), ("template", "imp")] }

def ex_10d_f : Datum :=
  { id := "faustlampitelli2026_10d_f"
    source := ⟨"faust-lampitelli-2026", "(10d)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "gɨlh-i"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "uncover"), ("template", "imp"), ("suffix", "i")] }

def ex_36b : Datum :=
  { id := "faustlampitelli2026_36b"
    source := ⟨"faust-lampitelli-2026", "(36b)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "sɨmʕa"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "hear"), ("template", "imp"), ("suffix", "a")] }

def ex_12a : Datum :=
  { id := "faustlampitelli2026_12a"
    source := ⟨"faust-lampitelli-2026", "(12a)"⟩
    reportedIn := none
    language := "tigr1270"
    primaryText := "tɨ-fʌggɨr"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "whip (Tigre)"), ("template", "imprf2")] }

def ex_12b : Datum :=
  { id := "faustlampitelli2026_12b"
    source := ⟨"faust-lampitelli-2026", "(12b)"⟩
    reportedIn := none
    language := "tigr1270"
    primaryText := "tɨ-sʔɨl"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "ask (Tigre)"), ("template", "imprf2")] }

def ex_12c : Datum :=
  { id := "faustlampitelli2026_12c"
    source := ⟨"faust-lampitelli-2026", "(12c)"⟩
    reportedIn := none
    language := "tigr1270"
    primaryText := "tɨ-tˀʕɨn"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "load"), ("template", "imprf2")] }

def ex_12d : Datum :=
  { id := "faustlampitelli2026_12d"
    source := ⟨"faust-lampitelli-2026", "(12d)"⟩
    reportedIn := none
    language := "tigr1270"
    primaryText := "tɨ-sħɨk"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "uncover (Tigre)"), ("template", "imprf2")] }

def ex_26d : Datum :=
  { id := "faustlampitelli2026_26d"
    source := ⟨"faust-lampitelli-2026", "(26d)"⟩
    reportedIn := none
    language := "tigr1270"
    primaryText := "tɨ-sħɨb"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "pull (Tigre)"), ("template", "imprf2")] }

def ex_13a_ger : Datum :=
  { id := "faustlampitelli2026_13a_ger"
    source := ⟨"faust-lampitelli-2026", "(13a)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "mɨ-graf"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "whip"), ("template", "gerA")] }

def ex_13a_poss : Datum :=
  { id := "faustlampitelli2026_13a_poss"
    source := ⟨"faust-lampitelli-2026", "(13a)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "mɨ-graf-u"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "whip"), ("template", "gerA"), ("suffix", "u")] }

def ex_13b_ger : Datum :=
  { id := "faustlampitelli2026_13b_ger"
    source := ⟨"faust-lampitelli-2026", "(13b)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "mɨ-nbaħ"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "bark"), ("template", "gerA")] }

def ex_13b_poss : Datum :=
  { id := "faustlampitelli2026_13b_poss"
    source := ⟨"faust-lampitelli-2026", "(13b)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "mɨ-nbuħ-u"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("mɨ-nbɨħ-u", .acceptable)]
    readings := []
    paperFeatures := [("root", "bark"), ("template", "gerA"), ("suffix", "u")] }

def ex_13c_ger : Datum :=
  { id := "faustlampitelli2026_13c_ger"
    source := ⟨"faust-lampitelli-2026", "(13c)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "mɨ-smaʕ"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "hear"), ("template", "gerA")] }

def ex_13c_poss : Datum :=
  { id := "faustlampitelli2026_13c_poss"
    source := ⟨"faust-lampitelli-2026", "(13c)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "mɨ-smeʕ-ej"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("mɨ-smɨʕ-ej", .acceptable)]
    readings := []
    paperFeatures := [("root", "hear"), ("template", "gerA"), ("suffix", "ej")] }

def ex_13d_ger : Datum :=
  { id := "faustlampitelli2026_13d_ger"
    source := ⟨"faust-lampitelli-2026", "(13d)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "mɨ-glah"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "uncover"), ("template", "gerA")] }

def ex_13d_poss : Datum :=
  { id := "faustlampitelli2026_13d_poss"
    source := ⟨"faust-lampitelli-2026", "(13d)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "mɨ-gloh-om"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("mɨ-glɨh-om", .acceptable)]
    readings := []
    paperFeatures := [("root", "uncover"), ("template", "gerA"), ("suffix", "om")] }

def ex_37a : Datum :=
  { id := "faustlampitelli2026_37a"
    source := ⟨"faust-lampitelli-2026", "(37a)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "mɨsmuʕu"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("mɨsmɨʕu", .acceptable)]
    readings := []
    paperFeatures := [("root", "hear"), ("template", "gerA"), ("suffix", "u")] }

def ex_17a_pass : Datum :=
  { id := "faustlampitelli2026_17a_pass"
    source := ⟨"faust-lampitelli-2026", "(17a)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "tɨ-gʌrif"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "whip"), ("template", "passPrf")] }

def ex_17b_imprf : Datum :=
  { id := "faustlampitelli2026_17b_imprf"
    source := ⟨"faust-lampitelli-2026", "(17b)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "tɨ-sɨħɨb"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "pull"), ("template", "imprf2")] }

def ex_17b_pass : Datum :=
  { id := "faustlampitelli2026_17b_pass"
    source := ⟨"faust-lampitelli-2026", "(17b)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "tɨ-siħib"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("tɨ-sɨħib", .acceptable)]
    readings := []
    paperFeatures := [("root", "pull"), ("template", "passPrf")] }

def ex_17c_imprf : Datum :=
  { id := "faustlampitelli2026_17c_imprf"
    source := ⟨"faust-lampitelli-2026", "(17c)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "tɨ-mɨhɨr"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "teach"), ("template", "imprf2")] }

def ex_17c_pass : Datum :=
  { id := "faustlampitelli2026_17c_pass"
    source := ⟨"faust-lampitelli-2026", "(17c)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "tɨ-mihir"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("tɨ-mɨhir", .acceptable)]
    readings := []
    paperFeatures := [("root", "teach"), ("template", "passPrf")] }

def ex_17d_imprf : Datum :=
  { id := "faustlampitelli2026_17d_imprf"
    source := ⟨"faust-lampitelli-2026", "(17d)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "tɨ-sɨʔɨl"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "ask"), ("template", "imprf2")] }

def ex_17d_pass : Datum :=
  { id := "faustlampitelli2026_17d_pass"
    source := ⟨"faust-lampitelli-2026", "(17d)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "tɨsiʔil"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("tɨ-sɨʔil", .acceptable)]
    readings := []
    paperFeatures := [("root", "ask"), ("template", "passPrf")] }

def ex_18a_dep : Datum :=
  { id := "faustlampitelli2026_18a_dep"
    source := ⟨"faust-lampitelli-2026", "(18a)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "gʌrʌf-ʌ"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "whip"), ("template", "depPrf"), ("suffix", "ʌ")] }

def ex_18b_dep : Datum :=
  { id := "faustlampitelli2026_18b_dep"
    source := ⟨"faust-lampitelli-2026", "(18b)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "bʌddʌl-ʌ"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "hurt"), ("template", "depPrfB"), ("suffix", "ʌ")] }

def ex_18b_ger : Datum :=
  { id := "faustlampitelli2026_18b_ger"
    source := ⟨"faust-lampitelli-2026", "(18b)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "mɨ-bɨddal"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "hurt"), ("template", "gerB")] }

def ex_18c_dep : Datum :=
  { id := "faustlampitelli2026_18c_dep"
    source := ⟨"faust-lampitelli-2026", "(18c)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "barʌk-ʌ"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "bless"), ("template", "depPrfC"), ("suffix", "ʌ")] }

def ex_18c_ger : Datum :=
  { id := "faustlampitelli2026_18c_ger"
    source := ⟨"faust-lampitelli-2026", "(18c)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "mɨ-bɨrak"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "bless"), ("template", "gerC")] }

def ex_19b_arifu : Datum :=
  { id := "faustlampitelli2026_19b_arifu"
    source := ⟨"faust-lampitelli-2026", "(19b)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "ʕarifu"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "arf"), ("template", "prf"), ("suffix", "u")] }

def ex_19b_tismaa : Datum :=
  { id := "faustlampitelli2026_19b_tismaa"
    source := ⟨"faust-lampitelli-2026", "(19b)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "tɨsmaʕ"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "hear"), ("template", "juss2")] }

def ex_19c : Datum :=
  { id := "faustlampitelli2026_19c"
    source := ⟨"faust-lampitelli-2026", "(19c)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "ʔasmiʕika"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "hear"), ("template", "caus"), ("suffix", "ka")] }

def ex_31a : Datum :=
  { id := "faustlampitelli2026_31a"
    source := ⟨"faust-lampitelli-2026", "(31a)"⟩
    reportedIn := none
    language := "tigr1270"
    primaryText := "tɨfgʌr"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "leave"), ("template", "juss2")] }

def ex_32b : Datum :=
  { id := "faustlampitelli2026_32b"
    source := ⟨"faust-lampitelli-2026", "(32b)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "tɨsħab"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "pull"), ("template", "juss2")] }

def ex_32c : Datum :=
  { id := "faustlampitelli2026_32c"
    source := ⟨"faust-lampitelli-2026", "(32c)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "tɨsħabi"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "pull"), ("template", "juss2"), ("suffix", "i")] }

def ex_33a : Datum :=
  { id := "faustlampitelli2026_33a"
    source := ⟨"faust-lampitelli-2026", "(33a)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "ʕɨrʌf"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "arf"), ("template", "imp")] }

def ex_33b : Datum :=
  { id := "faustlampitelli2026_33b"
    source := ⟨"faust-lampitelli-2026", "(33b)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "ʕarʌf"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "arf"), ("template", "depPrf")] }

def ex_37b : Datum :=
  { id := "faustlampitelli2026_37b"
    source := ⟨"faust-lampitelli-2026", "(37b)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "saħab"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("sɨħab", .acceptable)]
    readings := []
    paperFeatures := [("root", "pull"), ("template", "imp")] }

def ex_37d : Datum :=
  { id := "faustlampitelli2026_37d"
    source := ⟨"faust-lampitelli-2026", "(37d)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "sʌmaʕaku"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("sʌmaʕɨku", .acceptable)]
    readings := []
    paperFeatures := [("root", "hear"), ("template", "depPrf"), ("suffix", "ku")] }

def ex_38 : Datum :=
  { id := "faustlampitelli2026_38"
    source := ⟨"faust-lampitelli-2026", "(38)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "tɨsʌmiʕu"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "hear"), ("template", "passPrf"), ("suffix", "u")] }

def all : List Datum := [ex_4a_depPrf, ex_4a_prf, ex_4a_imprf, ex_4b_depPrf, ex_4b_prf, ex_4b_imprf, ex_4c_depPrf, ex_4c_prf, ex_4c_imprf, ex_4d_depPrf, ex_4d_prf, ex_4d_imprf, ex_5a_juss, ex_5a_imp, ex_5b_juss, ex_5b_imp, ex_5c_juss, ex_5c_imp, ex_6a_prf, ex_6b_prf, ex_6b_juss, ex_6c_prf, ex_7a, ex_7b, ex_7c, ex_7d, ex_7e, ex_7f, ex_10a_f, ex_10b_m, ex_10b_f, ex_10c_m, ex_10c_f, ex_10d_m, ex_10d_f, ex_36b, ex_12a, ex_12b, ex_12c, ex_12d, ex_26d, ex_13a_ger, ex_13a_poss, ex_13b_ger, ex_13b_poss, ex_13c_ger, ex_13c_poss, ex_13d_ger, ex_13d_poss, ex_37a, ex_17a_pass, ex_17b_imprf, ex_17b_pass, ex_17c_imprf, ex_17c_pass, ex_17d_imprf, ex_17d_pass, ex_18a_dep, ex_18b_dep, ex_18b_ger, ex_18c_dep, ex_18c_ger, ex_19b_arifu, ex_19b_tismaa, ex_19c, ex_31a, ex_32b, ex_32c, ex_33a, ex_33b, ex_37b, ex_37d, ex_38]

/-- The roots of the paper's forms, named by their glosses; a Tigre root whose gloss a Tigrinya root shares is marked. -/
inductive Root where
  /-- whip: √grf 'whip' -/
  | whip
  /-- hear: √smʕ 'hear' -/
  | hear
  /-- arrest: √ʔsr 'arrest' -/
  | arrest
  /-- pull: √sħb 'pull' -/
  | pull
  /-- teach: √mhr 'teach' -/
  | teach
  /-- slaughter: √ħrd 'slaughter' -/
  | slaughter
  /-- escape: √ħdm 'escape' -/
  | escape
  /-- ask: √sʔl 'ask' -/
  | ask
  /-- uncover: √glh 'uncover' -/
  | uncover
  /-- bark: √nbħ 'bark' -/
  | bark
  /-- hurt: √bdl 'hurt', of type B -/
  | hurt
  /-- bless: √brk 'bless', of type C -/
  | bless
  /-- arf: √ʕrf, which the paper does not gloss -/
  | arf
  /-- weigh: Tigre √mzn 'weigh' -/
  | weigh
  /-- leave: Tigre √fgr 'leave' -/
  | leave
  /-- wash: Tigre √ħtˁb 'wash' -/
  | wash
  /-- flee: Tigre √hrb 'flee' -/
  | flee
  /-- getUp: Tigre √kˀnsˁ 'get up' -/
  | getUp
  /-- whip (Tigre): Tigre √fgr 'whip' -/
  | whipTigre
  /-- ask (Tigre): Tigre √sʔl 'ask' -/
  | askTigre
  /-- load: Tigre √tˀʕn 'load' -/
  | load
  /-- uncover (Tigre): Tigre √sħk 'uncover' -/
  | uncoverTigre
  /-- pull (Tigre): Tigre √sħb 'pull' -/
  | pullTigre
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `root`. -/
def root (e : Datum) : Option Root :=
  e.parse? "root" [("whip", .whip), ("hear", .hear), ("arrest", .arrest), ("pull", .pull), ("teach", .teach),
    ("slaughter", .slaughter), ("escape", .escape), ("ask", .ask), ("uncover", .uncover),
    ("bark", .bark), ("hurt", .hurt), ("bless", .bless), ("arf", .arf), ("weigh", .weigh),
    ("leave", .leave), ("wash", .wash), ("flee", .flee), ("getUp", .getUp),
    ("whip (Tigre)", .whipTigre), ("ask (Tigre)", .askTigre), ("load", .load),
    ("uncover (Tigre)", .uncoverTigre), ("pull (Tigre)", .pullTigre)]

/-- The verbal and nominal templates of the paper's paradigms, Q, T, L standing for the radicals. -/
inductive Template where
  /-- depPrf: DEP.PRF QʌTʌL (4) -/
  | depPrf
  /-- depPrfB: the type B DEP.PRF QʌTTʌL, with medial gemination (18b) -/
  | depPrfB
  /-- depPrfC: the type C DEP.PRF QaTʌL, with [a] after the first radical (18c) -/
  | depPrfC
  /-- prf: PRF QʌTiL (4) -/
  | prf
  /-- imprf: IMPRF QʌTTɨL (4) -/
  | imprf
  /-- imprf2: 2-IMPRF tɨ-QʌTTɨL ((7), (12), (17)) -/
  | imprf2
  /-- imprf2NoGem: the 2-IMPRF without gemination, tɨ-QʌTɨL, of (7c) -/
  | imprf2NoGem
  /-- passPrf: PASS-PRF tɨ-QʌTiL (17) -/
  | passPrf
  /-- imp: IMP QɨTʌL ((5), (10)) -/
  | imp
  /-- juss2: 2-JUSS tɨ-QTʌL ((5), (6), (31), (32)) -/
  | juss2
  /-- impGem: the Tigre IMP QaTTɨL of (5a) -/
  | impGem
  /-- jussGem2: the Tigre 2-JUSS tɨ-QaTTɨL of (5a) -/
  | jussGem2
  /-- gerA: the type A gerund mɨQTaL (13) -/
  | gerA
  /-- gerB: the type B gerund mɨQɨTTaL (18b) -/
  | gerB
  /-- gerC: the type C gerund mɨQaTaL ((18c), (39b)) -/
  | gerC
  /-- caus: the causative PRF ʔʌQTiL (19c) -/
  | caus
  /-- prf3: the Tigre PRF-3MSG stem QaTL- (6) -/
  | prf3
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `template`. -/
def template (e : Datum) : Option Template :=
  e.parse? "template" [("depPrf", .depPrf), ("depPrfB", .depPrfB), ("depPrfC", .depPrfC), ("prf", .prf),
    ("imprf", .imprf), ("imprf2", .imprf2), ("imprf2NoGem", .imprf2NoGem),
    ("passPrf", .passPrf), ("imp", .imp), ("juss2", .juss2), ("impGem", .impGem),
    ("jussGem2", .jussGem2), ("gerA", .gerA), ("gerB", .gerB), ("gerC", .gerC), ("caus", .caus),
    ("prf3", .prf3)]

/-- The suffixes of the paper's suffixed forms. -/
inductive Suffix where
  /-- a: -a, as in Tigre PRF-3MSG [fagr-a] (6) and [sɨmʕa] (36b) -/
  | a
  /-- i: -i, the feminine of the imperative (10) -/
  | i
  /-- u: -u, as in [ʕarifu] (19b) and the possessed gerund [mɨ-graf-u] (13) -/
  | u
  /-- ʌ: -ʌ, as in DEP.PRF [gʌrʌf-ʌ] (18) -/
  | aBare
  /-- ej: -ej, the 1SG possessor of (13c) -/
  | ej
  /-- om: -om, the 3PL possessor of (13d) -/
  | om
  /-- ku: -ku, the 1SG of (37d) -/
  | ku
  /-- ka: -ka, the 2MSG of (19c) -/
  | ka
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `suffix`. -/
def suffix (e : Datum) : Option Suffix :=
  e.parse? "suffix" [("a", .a), ("i", .i), ("u", .u), ("ʌ", .aBare), ("ej", .ej), ("om", .om), ("ku", .ku),
    ("ka", .ka)]

/-- The forms of the paper's paradigms (4)-(19) and derivations (26)-(38). -/
inductive Example where
  | ex_4a_depPrf
  | ex_4a_prf
  | ex_4a_imprf
  | ex_4b_depPrf
  | ex_4b_prf
  | ex_4b_imprf
  | ex_4c_depPrf
  | ex_4c_prf
  | ex_4c_imprf
  | ex_4d_depPrf
  | ex_4d_prf
  | ex_4d_imprf
  | ex_5a_juss
  | ex_5a_imp
  | ex_5b_juss
  | ex_5b_imp
  | ex_5c_juss
  | ex_5c_imp
  | ex_6a_prf
  | ex_6b_prf
  | ex_6b_juss
  | ex_6c_prf
  | ex_7a
  | ex_7b
  | ex_7c
  | ex_7d
  | ex_7e
  | ex_7f
  | ex_10a_f
  | ex_10b_m
  | ex_10b_f
  | ex_10c_m
  | ex_10c_f
  | ex_10d_m
  | ex_10d_f
  | ex_36b
  | ex_12a
  | ex_12b
  | ex_12c
  | ex_12d
  | ex_26d
  | ex_13a_ger
  | ex_13a_poss
  | ex_13b_ger
  | ex_13b_poss
  | ex_13c_ger
  | ex_13c_poss
  | ex_13d_ger
  | ex_13d_poss
  | ex_37a
  | ex_17a_pass
  | ex_17b_imprf
  | ex_17b_pass
  | ex_17c_imprf
  | ex_17c_pass
  | ex_17d_imprf
  | ex_17d_pass
  | ex_18a_dep
  | ex_18b_dep
  | ex_18b_ger
  | ex_18c_dep
  | ex_18c_ger
  | ex_19b_arifu
  | ex_19b_tismaa
  | ex_19c
  | ex_31a
  | ex_32b
  | ex_32c
  | ex_33a
  | ex_33b
  | ex_37b
  | ex_37d
  | ex_38
  deriving DecidableEq, Repr, Fintype

/-- Every example of the file, in its order. -/
def Example.all : List Example :=
  [.ex_4a_depPrf, .ex_4a_prf, .ex_4a_imprf, .ex_4b_depPrf, .ex_4b_prf, .ex_4b_imprf,
    .ex_4c_depPrf, .ex_4c_prf, .ex_4c_imprf, .ex_4d_depPrf, .ex_4d_prf, .ex_4d_imprf, .ex_5a_juss,
    .ex_5a_imp, .ex_5b_juss, .ex_5b_imp, .ex_5c_juss, .ex_5c_imp, .ex_6a_prf, .ex_6b_prf,
    .ex_6b_juss, .ex_6c_prf, .ex_7a, .ex_7b, .ex_7c, .ex_7d, .ex_7e, .ex_7f, .ex_10a_f, .ex_10b_m,
    .ex_10b_f, .ex_10c_m, .ex_10c_f, .ex_10d_m, .ex_10d_f, .ex_36b, .ex_12a, .ex_12b, .ex_12c,
    .ex_12d, .ex_26d, .ex_13a_ger, .ex_13a_poss, .ex_13b_ger, .ex_13b_poss, .ex_13c_ger,
    .ex_13c_poss, .ex_13d_ger, .ex_13d_poss, .ex_37a, .ex_17a_pass, .ex_17b_imprf, .ex_17b_pass,
    .ex_17c_imprf, .ex_17c_pass, .ex_17d_imprf, .ex_17d_pass, .ex_18a_dep, .ex_18b_dep,
    .ex_18b_ger, .ex_18c_dep, .ex_18c_ger, .ex_19b_arifu, .ex_19b_tismaa, .ex_19c, .ex_31a,
    .ex_32b, .ex_32c, .ex_33a, .ex_33b, .ex_37b, .ex_37d, .ex_38]

/-- The row of an example. -/
def Example.datum : Example → Datum
  | .ex_4a_depPrf => _root_.FaustLampitelli2026.Examples.ex_4a_depPrf
  | .ex_4a_prf => _root_.FaustLampitelli2026.Examples.ex_4a_prf
  | .ex_4a_imprf => _root_.FaustLampitelli2026.Examples.ex_4a_imprf
  | .ex_4b_depPrf => _root_.FaustLampitelli2026.Examples.ex_4b_depPrf
  | .ex_4b_prf => _root_.FaustLampitelli2026.Examples.ex_4b_prf
  | .ex_4b_imprf => _root_.FaustLampitelli2026.Examples.ex_4b_imprf
  | .ex_4c_depPrf => _root_.FaustLampitelli2026.Examples.ex_4c_depPrf
  | .ex_4c_prf => _root_.FaustLampitelli2026.Examples.ex_4c_prf
  | .ex_4c_imprf => _root_.FaustLampitelli2026.Examples.ex_4c_imprf
  | .ex_4d_depPrf => _root_.FaustLampitelli2026.Examples.ex_4d_depPrf
  | .ex_4d_prf => _root_.FaustLampitelli2026.Examples.ex_4d_prf
  | .ex_4d_imprf => _root_.FaustLampitelli2026.Examples.ex_4d_imprf
  | .ex_5a_juss => _root_.FaustLampitelli2026.Examples.ex_5a_juss
  | .ex_5a_imp => _root_.FaustLampitelli2026.Examples.ex_5a_imp
  | .ex_5b_juss => _root_.FaustLampitelli2026.Examples.ex_5b_juss
  | .ex_5b_imp => _root_.FaustLampitelli2026.Examples.ex_5b_imp
  | .ex_5c_juss => _root_.FaustLampitelli2026.Examples.ex_5c_juss
  | .ex_5c_imp => _root_.FaustLampitelli2026.Examples.ex_5c_imp
  | .ex_6a_prf => _root_.FaustLampitelli2026.Examples.ex_6a_prf
  | .ex_6b_prf => _root_.FaustLampitelli2026.Examples.ex_6b_prf
  | .ex_6b_juss => _root_.FaustLampitelli2026.Examples.ex_6b_juss
  | .ex_6c_prf => _root_.FaustLampitelli2026.Examples.ex_6c_prf
  | .ex_7a => _root_.FaustLampitelli2026.Examples.ex_7a
  | .ex_7b => _root_.FaustLampitelli2026.Examples.ex_7b
  | .ex_7c => _root_.FaustLampitelli2026.Examples.ex_7c
  | .ex_7d => _root_.FaustLampitelli2026.Examples.ex_7d
  | .ex_7e => _root_.FaustLampitelli2026.Examples.ex_7e
  | .ex_7f => _root_.FaustLampitelli2026.Examples.ex_7f
  | .ex_10a_f => _root_.FaustLampitelli2026.Examples.ex_10a_f
  | .ex_10b_m => _root_.FaustLampitelli2026.Examples.ex_10b_m
  | .ex_10b_f => _root_.FaustLampitelli2026.Examples.ex_10b_f
  | .ex_10c_m => _root_.FaustLampitelli2026.Examples.ex_10c_m
  | .ex_10c_f => _root_.FaustLampitelli2026.Examples.ex_10c_f
  | .ex_10d_m => _root_.FaustLampitelli2026.Examples.ex_10d_m
  | .ex_10d_f => _root_.FaustLampitelli2026.Examples.ex_10d_f
  | .ex_36b => _root_.FaustLampitelli2026.Examples.ex_36b
  | .ex_12a => _root_.FaustLampitelli2026.Examples.ex_12a
  | .ex_12b => _root_.FaustLampitelli2026.Examples.ex_12b
  | .ex_12c => _root_.FaustLampitelli2026.Examples.ex_12c
  | .ex_12d => _root_.FaustLampitelli2026.Examples.ex_12d
  | .ex_26d => _root_.FaustLampitelli2026.Examples.ex_26d
  | .ex_13a_ger => _root_.FaustLampitelli2026.Examples.ex_13a_ger
  | .ex_13a_poss => _root_.FaustLampitelli2026.Examples.ex_13a_poss
  | .ex_13b_ger => _root_.FaustLampitelli2026.Examples.ex_13b_ger
  | .ex_13b_poss => _root_.FaustLampitelli2026.Examples.ex_13b_poss
  | .ex_13c_ger => _root_.FaustLampitelli2026.Examples.ex_13c_ger
  | .ex_13c_poss => _root_.FaustLampitelli2026.Examples.ex_13c_poss
  | .ex_13d_ger => _root_.FaustLampitelli2026.Examples.ex_13d_ger
  | .ex_13d_poss => _root_.FaustLampitelli2026.Examples.ex_13d_poss
  | .ex_37a => _root_.FaustLampitelli2026.Examples.ex_37a
  | .ex_17a_pass => _root_.FaustLampitelli2026.Examples.ex_17a_pass
  | .ex_17b_imprf => _root_.FaustLampitelli2026.Examples.ex_17b_imprf
  | .ex_17b_pass => _root_.FaustLampitelli2026.Examples.ex_17b_pass
  | .ex_17c_imprf => _root_.FaustLampitelli2026.Examples.ex_17c_imprf
  | .ex_17c_pass => _root_.FaustLampitelli2026.Examples.ex_17c_pass
  | .ex_17d_imprf => _root_.FaustLampitelli2026.Examples.ex_17d_imprf
  | .ex_17d_pass => _root_.FaustLampitelli2026.Examples.ex_17d_pass
  | .ex_18a_dep => _root_.FaustLampitelli2026.Examples.ex_18a_dep
  | .ex_18b_dep => _root_.FaustLampitelli2026.Examples.ex_18b_dep
  | .ex_18b_ger => _root_.FaustLampitelli2026.Examples.ex_18b_ger
  | .ex_18c_dep => _root_.FaustLampitelli2026.Examples.ex_18c_dep
  | .ex_18c_ger => _root_.FaustLampitelli2026.Examples.ex_18c_ger
  | .ex_19b_arifu => _root_.FaustLampitelli2026.Examples.ex_19b_arifu
  | .ex_19b_tismaa => _root_.FaustLampitelli2026.Examples.ex_19b_tismaa
  | .ex_19c => _root_.FaustLampitelli2026.Examples.ex_19c
  | .ex_31a => _root_.FaustLampitelli2026.Examples.ex_31a
  | .ex_32b => _root_.FaustLampitelli2026.Examples.ex_32b
  | .ex_32c => _root_.FaustLampitelli2026.Examples.ex_32c
  | .ex_33a => _root_.FaustLampitelli2026.Examples.ex_33a
  | .ex_33b => _root_.FaustLampitelli2026.Examples.ex_33b
  | .ex_37b => _root_.FaustLampitelli2026.Examples.ex_37b
  | .ex_37d => _root_.FaustLampitelli2026.Examples.ex_37d
  | .ex_38 => _root_.FaustLampitelli2026.Examples.ex_38

theorem Example.map_datum_all :
    Example.all.map Example.datum = _root_.FaustLampitelli2026.Examples.all := rfl

/-- The value the example records under `root`. -/
def Example.root : Example → Option Root
  | .ex_4a_depPrf => some .whip
  | .ex_4a_prf => some .whip
  | .ex_4a_imprf => some .whip
  | .ex_4b_depPrf => some .hear
  | .ex_4b_prf => some .hear
  | .ex_4b_imprf => some .hear
  | .ex_4c_depPrf => some .arrest
  | .ex_4c_prf => some .arrest
  | .ex_4c_imprf => some .arrest
  | .ex_4d_depPrf => some .pull
  | .ex_4d_prf => some .pull
  | .ex_4d_imprf => some .pull
  | .ex_5a_juss => some .weigh
  | .ex_5a_imp => some .weigh
  | .ex_5b_juss => some .leave
  | .ex_5b_imp => some .leave
  | .ex_5c_juss => some .getUp
  | .ex_5c_imp => some .getUp
  | .ex_6a_prf => some .leave
  | .ex_6b_prf => some .wash
  | .ex_6b_juss => some .wash
  | .ex_6c_prf => some .flee
  | .ex_7a => some .whip
  | .ex_7b => some .slaughter
  | .ex_7c => some .escape
  | .ex_7d => some .whip
  | .ex_7e => some .teach
  | .ex_7f => some .ask
  | .ex_10a_f => some .whip
  | .ex_10b_m => some .bark
  | .ex_10b_f => some .bark
  | .ex_10c_m => some .hear
  | .ex_10c_f => some .hear
  | .ex_10d_m => some .uncover
  | .ex_10d_f => some .uncover
  | .ex_36b => some .hear
  | .ex_12a => some .whipTigre
  | .ex_12b => some .askTigre
  | .ex_12c => some .load
  | .ex_12d => some .uncoverTigre
  | .ex_26d => some .pullTigre
  | .ex_13a_ger => some .whip
  | .ex_13a_poss => some .whip
  | .ex_13b_ger => some .bark
  | .ex_13b_poss => some .bark
  | .ex_13c_ger => some .hear
  | .ex_13c_poss => some .hear
  | .ex_13d_ger => some .uncover
  | .ex_13d_poss => some .uncover
  | .ex_37a => some .hear
  | .ex_17a_pass => some .whip
  | .ex_17b_imprf => some .pull
  | .ex_17b_pass => some .pull
  | .ex_17c_imprf => some .teach
  | .ex_17c_pass => some .teach
  | .ex_17d_imprf => some .ask
  | .ex_17d_pass => some .ask
  | .ex_18a_dep => some .whip
  | .ex_18b_dep => some .hurt
  | .ex_18b_ger => some .hurt
  | .ex_18c_dep => some .bless
  | .ex_18c_ger => some .bless
  | .ex_19b_arifu => some .arf
  | .ex_19b_tismaa => some .hear
  | .ex_19c => some .hear
  | .ex_31a => some .leave
  | .ex_32b => some .pull
  | .ex_32c => some .pull
  | .ex_33a => some .arf
  | .ex_33b => some .arf
  | .ex_37b => some .pull
  | .ex_37d => some .hear
  | .ex_38 => some .hear

theorem Example.root_datum :
    ∀ x : Example, _root_.FaustLampitelli2026.Examples.root x.datum = x.root := by
  decide +kernel

/-- The value the example records under `template`. -/
def Example.template : Example → Option Template
  | .ex_4a_depPrf => some .depPrf
  | .ex_4a_prf => some .prf
  | .ex_4a_imprf => some .imprf
  | .ex_4b_depPrf => some .depPrf
  | .ex_4b_prf => some .prf
  | .ex_4b_imprf => some .imprf
  | .ex_4c_depPrf => some .depPrf
  | .ex_4c_prf => some .prf
  | .ex_4c_imprf => some .imprf
  | .ex_4d_depPrf => some .depPrf
  | .ex_4d_prf => some .prf
  | .ex_4d_imprf => some .imprf
  | .ex_5a_juss => some .jussGem2
  | .ex_5a_imp => some .impGem
  | .ex_5b_juss => some .juss2
  | .ex_5b_imp => some .imp
  | .ex_5c_juss => some .juss2
  | .ex_5c_imp => some .imp
  | .ex_6a_prf => some .prf3
  | .ex_6b_prf => some .prf3
  | .ex_6b_juss => some .juss2
  | .ex_6c_prf => some .prf3
  | .ex_7a => some .imprf2
  | .ex_7b => some .imprf2
  | .ex_7c => some .imprf2NoGem
  | .ex_7d => some .imp
  | .ex_7e => some .imp
  | .ex_7f => some .imp
  | .ex_10a_f => some .imp
  | .ex_10b_m => some .imp
  | .ex_10b_f => some .imp
  | .ex_10c_m => some .imp
  | .ex_10c_f => some .imp
  | .ex_10d_m => some .imp
  | .ex_10d_f => some .imp
  | .ex_36b => some .imp
  | .ex_12a => some .imprf2
  | .ex_12b => some .imprf2
  | .ex_12c => some .imprf2
  | .ex_12d => some .imprf2
  | .ex_26d => some .imprf2
  | .ex_13a_ger => some .gerA
  | .ex_13a_poss => some .gerA
  | .ex_13b_ger => some .gerA
  | .ex_13b_poss => some .gerA
  | .ex_13c_ger => some .gerA
  | .ex_13c_poss => some .gerA
  | .ex_13d_ger => some .gerA
  | .ex_13d_poss => some .gerA
  | .ex_37a => some .gerA
  | .ex_17a_pass => some .passPrf
  | .ex_17b_imprf => some .imprf2
  | .ex_17b_pass => some .passPrf
  | .ex_17c_imprf => some .imprf2
  | .ex_17c_pass => some .passPrf
  | .ex_17d_imprf => some .imprf2
  | .ex_17d_pass => some .passPrf
  | .ex_18a_dep => some .depPrf
  | .ex_18b_dep => some .depPrfB
  | .ex_18b_ger => some .gerB
  | .ex_18c_dep => some .depPrfC
  | .ex_18c_ger => some .gerC
  | .ex_19b_arifu => some .prf
  | .ex_19b_tismaa => some .juss2
  | .ex_19c => some .caus
  | .ex_31a => some .juss2
  | .ex_32b => some .juss2
  | .ex_32c => some .juss2
  | .ex_33a => some .imp
  | .ex_33b => some .depPrf
  | .ex_37b => some .imp
  | .ex_37d => some .depPrf
  | .ex_38 => some .passPrf

theorem Example.template_datum :
    ∀ x : Example, _root_.FaustLampitelli2026.Examples.template x.datum = x.template := by
  decide +kernel

/-- The value the example records under `suffix`. -/
def Example.suffix : Example → Option Suffix
  | .ex_4a_depPrf => none
  | .ex_4a_prf => none
  | .ex_4a_imprf => none
  | .ex_4b_depPrf => none
  | .ex_4b_prf => none
  | .ex_4b_imprf => none
  | .ex_4c_depPrf => none
  | .ex_4c_prf => none
  | .ex_4c_imprf => none
  | .ex_4d_depPrf => none
  | .ex_4d_prf => none
  | .ex_4d_imprf => none
  | .ex_5a_juss => none
  | .ex_5a_imp => none
  | .ex_5b_juss => none
  | .ex_5b_imp => none
  | .ex_5c_juss => none
  | .ex_5c_imp => none
  | .ex_6a_prf => some .a
  | .ex_6b_prf => some .a
  | .ex_6b_juss => none
  | .ex_6c_prf => some .a
  | .ex_7a => none
  | .ex_7b => none
  | .ex_7c => none
  | .ex_7d => none
  | .ex_7e => none
  | .ex_7f => none
  | .ex_10a_f => some .i
  | .ex_10b_m => none
  | .ex_10b_f => some .i
  | .ex_10c_m => none
  | .ex_10c_f => some .i
  | .ex_10d_m => none
  | .ex_10d_f => some .i
  | .ex_36b => some .a
  | .ex_12a => none
  | .ex_12b => none
  | .ex_12c => none
  | .ex_12d => none
  | .ex_26d => none
  | .ex_13a_ger => none
  | .ex_13a_poss => some .u
  | .ex_13b_ger => none
  | .ex_13b_poss => some .u
  | .ex_13c_ger => none
  | .ex_13c_poss => some .ej
  | .ex_13d_ger => none
  | .ex_13d_poss => some .om
  | .ex_37a => some .u
  | .ex_17a_pass => none
  | .ex_17b_imprf => none
  | .ex_17b_pass => none
  | .ex_17c_imprf => none
  | .ex_17c_pass => none
  | .ex_17d_imprf => none
  | .ex_17d_pass => none
  | .ex_18a_dep => some .aBare
  | .ex_18b_dep => some .aBare
  | .ex_18b_ger => none
  | .ex_18c_dep => some .aBare
  | .ex_18c_ger => none
  | .ex_19b_arifu => some .u
  | .ex_19b_tismaa => none
  | .ex_19c => some .ka
  | .ex_31a => none
  | .ex_32b => none
  | .ex_32c => some .i
  | .ex_33a => none
  | .ex_33b => none
  | .ex_37b => none
  | .ex_37d => some .ku
  | .ex_38 => some .u

theorem Example.suffix_datum :
    ∀ x : Example, _root_.FaustLampitelli2026.Examples.suffix x.datum = x.suffix := by
  decide +kernel

end FaustLampitelli2026.Examples
