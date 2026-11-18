module

public import Linglib.Data.Examples.Schema

/-!
# `ElliottSudo2025` — typed example data

Auto-generated from `Linglib/Data/Examples/ElliottSudo2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ElliottSudo2025.Examples`.
-/

@[expose] public section

namespace ElliottSudo2025.Examples

def ex_1 : Datum :=
  { id := "elliottsudo2025_1"
    source := ⟨"kamp-1973", "permission sentences"⟩
    reportedIn := some ⟨"elliott-sudo-2025", "(1)"⟩
    language := "stan1293"
    primaryText := "You may have tea or coffee."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("implies: you may have coffee and you may have tea", .acceptable)]
    paperFeatures := [("section", "1")] }

def ex_2 : Datum :=
  { id := "elliottsudo2025_2"
    source := ⟨"zimmermann-2000", "epistemic free choice"⟩
    reportedIn := some ⟨"elliott-sudo-2025", "(2)"⟩
    language := "stan1293"
    primaryText := "It might be here or there."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("implies: it might be here and it might be there", .acceptable)]
    paperFeatures := [("section", "1")] }

def ex_6 : Datum :=
  { id := "elliottsudo2025_6"
    source := ⟨"elliott-sudo-2025", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either there isn't a bathroom in this house, or it's in a funny place."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("existential: either no bathroom, or a bathroom in a funny place", .acceptable)]
    paperFeatures := [("section", "2.1")] }

def ex_10a : Datum :=
  { id := "elliottsudo2025_10a"
    source := ⟨"elliott-sudo-2025", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ethan has a husband. He's standing outside."
    glossedTokens := []
    context := "It is known that if Ethan is married, he is married to a man."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.1")] }

def ex_10b : Datum :=
  { id := "elliottsudo2025_10b"
    source := ⟨"elliott-sudo-2025", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ethan is married. He's standing outside."
    glossedTokens := []
    context := "It is known that if Ethan is married, he is married to a man."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.1")] }

def ex_11a : Datum :=
  { id := "elliottsudo2025_11a"
    source := ⟨"elliott-sudo-2025", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either John has no husband, or he's standing outside."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.1")] }

def ex_11b : Datum :=
  { id := "elliottsudo2025_11b"
    source := ⟨"elliott-sudo-2025", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either John isn't married, or he's standing outside."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.1")] }

def ex_14 : Datum :=
  { id := "elliottsudo2025_14"
    source := ⟨"elliott-sudo-2025", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either Sue didn't buy a sage plant, or she bought eight others along with it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.1")] }

def ex_16a : Datum :=
  { id := "elliottsudo2025_16a"
    source := ⟨"elliott-sudo-2025", "(16a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either John doesn't own a shirt, or it's in the wardrobe."
    glossedTokens := []
    context := ""
    judgment := .questionable
    contrasts := [("John owns a shirt, and it's in the wardrobe.", .questionable)]
    readings := []
    paperFeatures := [("section", "2.1")] }

def ex_18 : Datum :=
  { id := "elliottsudo2025_18"
    source := ⟨"elliott-sudo-2025", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either Gennaro doesn't have a credit card, or he paid with it."
    glossedTokens := []
    context := "Wondering how Gennaro paid for dinner."
    judgment := .acceptable
    contrasts := []
    readings := [("existential: consistent with a credit card he did not pay with", .acceptable), ("universal: every credit card was used to pay", .unacceptable)]
    paperFeatures := [("section", "2.1")] }

def ex_22 : Datum :=
  { id := "elliottsudo2025_22"
    source := ⟨"elliott-sudo-2025", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's possible that either there's no bathroom in this house or it's in a surprising place."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("entails: it's possible that there's no bathroom in this house", .acceptable), ("entails: it's possible that there's a bathroom in this house in a surprising place", .acceptable)]
    paperFeatures := [("section", "2.2")] }

def ex_23 : Datum :=
  { id := "elliottsudo2025_23"
    source := ⟨"elliott-sudo-2025", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may include no appendix, or keep it to a single page."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("entails: you may include no appendix", .acceptable), ("entails: you may include an appendix kept to a single page", .acceptable), ("entails: you may keep it to a single page", .unacceptable)]
    paperFeatures := [("section", "2.2")] }

def ex_42 : Datum :=
  { id := "elliottsudo2025_42"
    source := ⟨"elliott-sudo-2025", "(42)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Gabor didn't write a paper about free choice, but it was interesting."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3")] }

def ex_51 : Datum :=
  { id := "elliottsudo2025_51"
    source := ⟨"elliott-sudo-2025", "(51)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not true that Sue didn't buy a sage plant — she bought eight others along with it!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3")] }

def ex_52b : Datum :=
  { id := "elliottsudo2025_52b"
    source := ⟨"elliott-sudo-2025", "(52b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No, Kafuku doesn't own no car — he drives it every day."
    glossedTokens := []
    context := "Answering: Does Kafuku own no car?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3")] }

def ex_63 : Datum :=
  { id := "elliottsudo2025_63"
    source := ⟨"elliott-sudo-2025", "(63)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either it's upstairs, or there is no bathroom."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.4.2")] }

def ex_71 : Datum :=
  { id := "elliottsudo2025_71"
    source := ⟨"elliott-sudo-2025", "(71)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either Gennaro doesn't have a credit card, or he paid with it."
    glossedTokens := []
    context := "Gennaro has a credit card that he paid with and another that he did not."
    judgment := .acceptable
    contrasts := []
    readings := [("true in the context", .acceptable)]
    paperFeatures := [("section", "3.4.2")] }

def ex_74 : Datum :=
  { id := "elliottsudo2025_74"
    source := ⟨"elliott-sudo-2025", "(74)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Maybe there isn't a bathroom."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.5")] }

def ex_78 : Datum :=
  { id := "elliottsudo2025_78"
    source := ⟨"elliott-sudo-2025", "(78)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There might be a bathroom and it might be upstairs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.5")] }

def ex_82 : Datum :=
  { id := "elliottsudo2025_82"
    source := ⟨"elliott-sudo-2025", "(82)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There might be coffee or tea."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("entails: there might be coffee and there might be tea", .acceptable)]
    paperFeatures := [("section", "3.6")] }

def ex_85 : Datum :=
  { id := "elliottsudo2025_85"
    source := ⟨"elliott-sudo-2025", "(85)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's impossible that there's coffee or tea."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("entails: no coffee is possible and no tea is possible", .acceptable)]
    paperFeatures := [("section", "3.6")] }

def ex_110 : Datum :=
  { id := "elliottsudo2025_110"
    source := ⟨"elliott-sudo-2025", "(110)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either it's possible there's no bathroom, or it's possible it's upstairs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("entails: it's possible there's no bathroom, and it's possible there's a bathroom upstairs", .acceptable)]
    paperFeatures := [("section", "5.1")] }

def ex_114 : Datum :=
  { id := "elliottsudo2025_114"
    source := ⟨"elliott-sudo-2025", "(114)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every student read The Master and Margarita or The White Guard."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("entails: some student read The Master and Margarita", .acceptable), ("entails: some student read The White Guard", .acceptable)]
    paperFeatures := [("section", "5.2")] }

def ex_116 : Datum :=
  { id := "elliottsudo2025_116"
    source := ⟨"elliott-sudo-2025", "(116)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every student either didn't read a novel, or wrote a report on it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("entails: some student didn't read a novel", .acceptable), ("entails: some student read a novel and wrote a report on it", .acceptable)]
    paperFeatures := [("section", "5.2")] }

def ex_118 : Datum :=
  { id := "elliottsudo2025_118"
    source := ⟨"elliott-sudo-2025", "(118)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not every linguist is attending the plenary talk. She's smoking outside."
    glossedTokens := []
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.2")] }

def ex_126 : Datum :=
  { id := "elliottsudo2025_126"
    source := ⟨"elliott-sudo-2025", "(126)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If either there's no bathroom or it's upstairs, this house needs to be renovated."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("entails: if there's no bathroom, this house needs to be renovated", .acceptable), ("entails: if there's a bathroom upstairs, this house needs to be renovated", .acceptable)]
    paperFeatures := [("section", "5.3")] }

def ex_129 : Datum :=
  { id := "elliottsudo2025_129"
    source := ⟨"elliott-sudo-2025", "(129)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not required that you include an appendix and keep it to a single page."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("negative free choice with anaphora", .acceptable)]
    paperFeatures := [("section", "5.4")] }

def all : List Datum := [ex_1, ex_2, ex_6, ex_10a, ex_10b, ex_11a, ex_11b, ex_14, ex_16a, ex_18, ex_22, ex_23, ex_42, ex_51, ex_52b, ex_63, ex_71, ex_74, ex_78, ex_82, ex_85, ex_110, ex_114, ex_116, ex_118, ex_126, ex_129]

end ElliottSudo2025.Examples
