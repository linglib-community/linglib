module

public import Linglib.Data.Examples.Schema

/-!
# `Ferreira2023` — typed example data

Auto-generated from `Linglib/Data/Examples/Ferreira2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Ferreira2023.Examples`.
-/

@[expose] public section

namespace Ferreira2023.Examples

def ex_16 : Datum :=
  { id := "ferreira2023_16"
    source := ⟨"ferreira-2023", "(16)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "Este homem tem que ter sido assassinado, mas ele pode não ter sido."
    glossedTokens := []
    context := "A criminal investigator announces his findings about a man's body found in a dark alley."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("first", "sn_p"), ("second", "pos_notp")] }

def ex_17 : Datum :=
  { id := "ferreira2023_17"
    source := ⟨"ferreira-2023", "(17)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "Este homem deve ter sido assassinado, mas ele pode não ter sido."
    glossedTokens := []
    context := "A criminal investigator announces his findings about a man's body found in a dark alley."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("first", "wn_p"), ("second", "pos_notp")] }

def ex_18 : Datum :=
  { id := "ferreira2023_18"
    source := ⟨"ferreira-2023", "(18)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "Este homem pode ter sido assassinado, mas ele pode não ter sido."
    glossedTokens := []
    context := "A criminal investigator announces his findings about a man's body found in a dark alley."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("first", "pos_p"), ("second", "pos_notp")] }

def ex_19 : Datum :=
  { id := "ferreira2023_19"
    source := ⟨"ferreira-2023", "(19)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "Este homem tem que ter sido assassinado, mas ele não deve ter sido."
    glossedTokens := []
    context := "A criminal investigator announces his findings about a man's body found in a dark alley."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("first", "sn_p"), ("second", "not_wn_p")] }

def ex_20 : Datum :=
  { id := "ferreira2023_20"
    source := ⟨"ferreira-2023", "(20)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "Este homem deve ter sido assassinado, mas ele não tem que ter sido."
    glossedTokens := []
    context := "A criminal investigator announces his findings about a man's body found in a dark alley."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("first", "wn_p"), ("second", "not_sn_p")] }

def ex_21 : Datum :=
  { id := "ferreira2023_21"
    source := ⟨"ferreira-2023", "(21)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "Este homem deve ter sido assassinado, mas ele não pode ter sido."
    glossedTokens := []
    context := "A criminal investigator announces his findings about a man's body found in a dark alley."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("first", "wn_p"), ("second", "not_pos_p")] }

def ex_22 : Datum :=
  { id := "ferreira2023_22"
    source := ⟨"ferreira-2023", "(22)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "Este homem pode ter sido assassinado, mas não deve ter sido."
    glossedTokens := []
    context := "A criminal investigator announces his findings about a man's body found in a dark alley."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("first", "pos_p"), ("second", "not_wn_p")] }

def ex_24 : Datum :=
  { id := "ferreira2023_24"
    source := ⟨"ferreira-2023", "(24)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "Este homem deve ter sido assassinado, mas ele deve não ter sido."
    glossedTokens := []
    context := "A criminal investigator announces his findings about a man's body found in a dark alley."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("first", "wn_p"), ("second", "wn_notp")] }

def ex_25 : Datum :=
  { id := "ferreira2023_25"
    source := ⟨"ferreira-2023", "(25)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "Este homem tem que ter sido assassinado, mas ele tem que não ter sido."
    glossedTokens := []
    context := "A criminal investigator announces his findings about a man's body found in a dark alley."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("first", "sn_p"), ("second", "sn_notp")] }

def ex_30a : Datum :=
  { id := "ferreira2023_30a"
    source := ⟨"ferreira-2023", "(30a)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "Clientes devem usar máscara, mas eles não têm que."
    glossedTokens := []
    context := "Concerning the COVID-19 protocol of this establishment."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("first", "wn_p"), ("second", "not_sn_p")] }

def ex_30b : Datum :=
  { id := "ferreira2023_30b"
    source := ⟨"ferreira-2023", "(30b)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "Clientes devem usar máscara. Na verdade, eles têm que."
    glossedTokens := []
    context := "Concerning the COVID-19 protocol of this establishment."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("first", "wn_p"), ("second", "sn_p")] }

def ex_32a : Datum :=
  { id := "ferreira2023_32a"
    source := ⟨"ferreira-2023", "(32a)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "Tenho que limpar os pratos, mas não estou obrigado."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("first", "sn_p"), ("second", "not_sn_p")] }

def ex_32b : Datum :=
  { id := "ferreira2023_32b"
    source := ⟨"ferreira-2023", "(32b)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "Devo limpar os pratos, mas não estou obrigado."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("first", "wn_p"), ("second", "not_sn_p")] }

def ex_80 : Datum :=
  { id := "ferreira2023_80"
    source := ⟨"ferreira-2023", "(80)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "(É por isso que) ele devia estar lá."
    glossedTokens := []
    context := "A: Where is Peter? B: Probably in his office. A: But today is a holiday! B: Oh, I didn't know it was …"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("base", "holiday")] }

def ex_81 : Datum :=
  { id := "ferreira2023_81"
    source := ⟨"ferreira-2023", "(81)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "Estranho! Ele devia estar lá."
    glossedTokens := []
    context := "A: Where is Peter? B: Probably in his office. A: I have just checked and he isn't there."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("base", "checked")] }

def all : List Datum := [ex_16, ex_17, ex_18, ex_19, ex_20, ex_21, ex_22, ex_24, ex_25, ex_30a, ex_30b, ex_32a, ex_32b, ex_80, ex_81]

end Ferreira2023.Examples
