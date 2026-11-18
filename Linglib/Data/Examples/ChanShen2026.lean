module

public import Linglib.Data.Examples.Schema

/-!
# `ChanShen2026` — typed example data

Auto-generated from `Linglib/Data/Examples/ChanShen2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ChanShen2026.Examples`.
-/

@[expose] public section

namespace ChanShen2026.Examples

def ex1a : Datum :=
  { id := "chanshen2026_ex1a"
    source := ⟨"chan-shen-2026", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who loves what the hell?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("modifier", "theHell"), ("strategy", "inSitu"), ("question", "multiple")] }

def ex1b : Datum :=
  { id := "chanshen2026_ex1b"
    source := ⟨"chan-shen-2026", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who the hell loves what?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modifier", "theHell"), ("strategy", "full"), ("question", "multiple")] }

def ex4a : Datum :=
  { id := "chanshen2026_ex4a"
    source := ⟨"chan-shen-2026", "(4a)"⟩
    reportedIn := none
    language := "sing1272"
    primaryText := "What you think Natalie is baking at 3am ah?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("condition", "Wh-Long"), ("strategy", "full")] }

def ex4b : Datum :=
  { id := "chanshen2026_ex4b"
    source := ⟨"chan-shen-2026", "(4b)"⟩
    reportedIn := none
    method := some .corpus
    language := "sing1272"
    primaryText := "What the hell you think Natalie is baking at 3am ah?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("condition", "WhHell-Long"), ("modifier", "theHell"), ("strategy", "full")] }

def ex4c : Datum :=
  { id := "chanshen2026_ex4c"
    source := ⟨"chan-shen-2026", "(4c)"⟩
    reportedIn := none
    language := "sing1272"
    primaryText := "You think Natalie is baking what at 3am ah?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("condition", "Wh-Situ"), ("strategy", "inSitu")] }

def ex4d : Datum :=
  { id := "chanshen2026_ex4d"
    source := ⟨"chan-shen-2026", "(4d)"⟩
    reportedIn := none
    language := "sing1272"
    primaryText := "You think Natalie is baking what the hell at 3am ah?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("condition", "WhHell-Situ"), ("modifier", "theHell"), ("strategy", "inSitu")] }

def ex6c : Datum :=
  { id := "chanshen2026_ex6c"
    source := ⟨"chan-shen-2026", "(6c)"⟩
    reportedIn := none
    language := "sing1272"
    primaryText := "You think what Natalie is baking at 3am ah?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("condition", "Wh-Partial"), ("strategy", "partial")] }

def ex6d : Datum :=
  { id := "chanshen2026_ex6d"
    source := ⟨"chan-shen-2026", "(6d)"⟩
    reportedIn := none
    language := "sing1272"
    primaryText := "You think what the hell Natalie is baking at 3am ah?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("condition", "WhHell-Partial"), ("modifier", "theHell"), ("strategy", "partial")] }

def ex11a : Datum :=
  { id := "chanshen2026_ex11a"
    source := ⟨"sato-ngui-2017", "(21a)"⟩
    reportedIn := some ⟨"chan-shen-2026", "(11a)"⟩
    language := "sing1272"
    primaryText := "What John like the man that think Mary eat?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("strategy", "full"), ("island", "complexNP")] }

def ex11b : Datum :=
  { id := "chanshen2026_ex11b"
    source := ⟨"sato-ngui-2017", "(21c)"⟩
    reportedIn := some ⟨"chan-shen-2026", "(11b)"⟩
    language := "sing1272"
    primaryText := "John like the man that think Mary eat what?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("strategy", "inSitu"), ("island", "complexNP")] }

def ex15 : Datum :=
  { id := "chanshen2026_ex15"
    source := ⟨"sato-ngui-2017", "(21b)"⟩
    reportedIn := some ⟨"chan-shen-2026", "(15)"⟩
    language := "sing1272"
    primaryText := "John like the man that think what Mary eat?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("strategy", "partial"), ("island", "complexNP")] }

def ex17a : Datum :=
  { id := "chanshen2026_ex17a"
    source := ⟨"chan-shen-2026", "(17a)"⟩
    reportedIn := none
    language := "stan1306"
    primaryText := "Kamu sayang perempuan yang Ali fikir yang telah makan apa?"
    glossedTokens := [("Kamu", "you"), ("sayang", "love"), ("perempuan", "woman"), ("yang", "that"), ("Ali", "Ali"), ("fikir", "thinks"), ("yang", "that"), ("telah", "already"), ("makan", "eat"), ("apa", "what")]
    glossedWords := [⟨['K', 'a', 'm', 'u'], ['y', 'o', 'u'], [⟨['K', 'a', 'm', 'u'], ['y', 'o', 'u'], none⟩]⟩, ⟨['s', 'a', 'y', 'a', 'n', 'g'], ['l', 'o', 'v', 'e'], [⟨['s', 'a', 'y', 'a', 'n', 'g'], ['l', 'o', 'v', 'e'], none⟩]⟩, ⟨['p', 'e', 'r', 'e', 'm', 'p', 'u', 'a', 'n'], ['w', 'o', 'm', 'a', 'n'], [⟨['p', 'e', 'r', 'e', 'm', 'p', 'u', 'a', 'n'], ['w', 'o', 'm', 'a', 'n'], none⟩]⟩, ⟨['y', 'a', 'n', 'g'], ['t', 'h', 'a', 't'], [⟨['y', 'a', 'n', 'g'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['A', 'l', 'i'], ['A', 'l', 'i'], [⟨['A', 'l', 'i'], ['A', 'l', 'i'], none⟩]⟩, ⟨['f', 'i', 'k', 'i', 'r'], ['t', 'h', 'i', 'n', 'k', 's'], [⟨['f', 'i', 'k', 'i', 'r'], ['t', 'h', 'i', 'n', 'k', 's'], none⟩]⟩, ⟨['y', 'a', 'n', 'g'], ['t', 'h', 'a', 't'], [⟨['y', 'a', 'n', 'g'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['t', 'e', 'l', 'a', 'h'], ['a', 'l', 'r', 'e', 'a', 'd', 'y'], [⟨['t', 'e', 'l', 'a', 'h'], ['a', 'l', 'r', 'e', 'a', 'd', 'y'], none⟩]⟩, ⟨['m', 'a', 'k', 'a', 'n'], ['e', 'a', 't'], [⟨['m', 'a', 'k', 'a', 'n'], ['e', 'a', 't'], none⟩]⟩, ⟨['a', 'p', 'a'], ['w', 'h', 'a', 't'], [⟨['a', 'p', 'a'], ['w', 'h', 'a', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("strategy", "inSitu"), ("island", "complexNP")] }

def ex17b : Datum :=
  { id := "chanshen2026_ex17b"
    source := ⟨"chan-shen-2026", "(17b)"⟩
    reportedIn := none
    language := "stan1306"
    primaryText := "Kamu sayang perempuan yang Ali fikir apa yang telah makan?"
    glossedTokens := [("Kamu", "you"), ("sayang", "love"), ("perempuan", "woman"), ("yang", "that"), ("Ali", "Ali"), ("fikir", "thinks"), ("apa", "what"), ("yang", "that"), ("telah", "already"), ("makan", "eat")]
    glossedWords := [⟨['K', 'a', 'm', 'u'], ['y', 'o', 'u'], [⟨['K', 'a', 'm', 'u'], ['y', 'o', 'u'], none⟩]⟩, ⟨['s', 'a', 'y', 'a', 'n', 'g'], ['l', 'o', 'v', 'e'], [⟨['s', 'a', 'y', 'a', 'n', 'g'], ['l', 'o', 'v', 'e'], none⟩]⟩, ⟨['p', 'e', 'r', 'e', 'm', 'p', 'u', 'a', 'n'], ['w', 'o', 'm', 'a', 'n'], [⟨['p', 'e', 'r', 'e', 'm', 'p', 'u', 'a', 'n'], ['w', 'o', 'm', 'a', 'n'], none⟩]⟩, ⟨['y', 'a', 'n', 'g'], ['t', 'h', 'a', 't'], [⟨['y', 'a', 'n', 'g'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['A', 'l', 'i'], ['A', 'l', 'i'], [⟨['A', 'l', 'i'], ['A', 'l', 'i'], none⟩]⟩, ⟨['f', 'i', 'k', 'i', 'r'], ['t', 'h', 'i', 'n', 'k', 's'], [⟨['f', 'i', 'k', 'i', 'r'], ['t', 'h', 'i', 'n', 'k', 's'], none⟩]⟩, ⟨['a', 'p', 'a'], ['w', 'h', 'a', 't'], [⟨['a', 'p', 'a'], ['w', 'h', 'a', 't'], none⟩]⟩, ⟨['y', 'a', 'n', 'g'], ['t', 'h', 'a', 't'], [⟨['y', 'a', 'n', 'g'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['t', 'e', 'l', 'a', 'h'], ['a', 'l', 'r', 'e', 'a', 'd', 'y'], [⟨['t', 'e', 'l', 'a', 'h'], ['a', 'l', 'r', 'e', 'a', 'd', 'y'], none⟩]⟩, ⟨['m', 'a', 'k', 'a', 'n'], ['e', 'a', 't'], [⟨['m', 'a', 'k', 'a', 'n'], ['e', 'a', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("strategy", "partial"), ("island", "complexNP")] }

def ex19 : Datum :=
  { id := "chanshen2026_ex19"
    source := ⟨"chou-2012", "(31)"⟩
    reportedIn := some ⟨"chan-shen-2026", "(19)"⟩
    language := "mand1415"
    primaryText := "Ni renwei Lisi daodi xihuan shenme?"
    glossedTokens := [("Ni", "you"), ("renwei", "think"), ("Lisi", "Lisi"), ("daodi", "THE-HELL"), ("xihuan", "like"), ("shenme", "what")]
    glossedWords := [⟨['N', 'i'], ['y', 'o', 'u'], [⟨['N', 'i'], ['y', 'o', 'u'], none⟩]⟩, ⟨['r', 'e', 'n', 'w', 'e', 'i'], ['t', 'h', 'i', 'n', 'k'], [⟨['r', 'e', 'n', 'w', 'e', 'i'], ['t', 'h', 'i', 'n', 'k'], none⟩]⟩, ⟨['L', 'i', 's', 'i'], ['L', 'i', 's', 'i'], [⟨['L', 'i', 's', 'i'], ['L', 'i', 's', 'i'], none⟩]⟩, ⟨['d', 'a', 'o', 'd', 'i'], ['T', 'H', 'E', '-', 'H', 'E', 'L', 'L'], []⟩, ⟨['x', 'i', 'h', 'u', 'a', 'n'], ['l', 'i', 'k', 'e'], [⟨['x', 'i', 'h', 'u', 'a', 'n'], ['l', 'i', 'k', 'e'], none⟩]⟩, ⟨['s', 'h', 'e', 'n', 'm', 'e'], ['w', 'h', 'a', 't'], [⟨['s', 'h', 'e', 'n', 'm', 'e'], ['w', 'h', 'a', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modifier", "daodi"), ("strategy", "inSitu")] }

def ex22a : Datum :=
  { id := "chanshen2026_ex22a"
    source := ⟨"chan-shen-2026", "(22a)"⟩
    reportedIn := none
    language := "sing1272"
    primaryText := "You that time heard that who went hospital for surgery ah?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("strategy", "inSitu"), ("role", "subject")] }

def ex22b : Datum :=
  { id := "chanshen2026_ex22b"
    source := ⟨"chan-shen-2026", "(22b)"⟩
    reportedIn := none
    language := "sing1272"
    primaryText := "You that time heard that who the hell went hospital for surgery ah?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("modifier", "theHell"), ("strategy", "inSitu"), ("role", "subject")] }

def ex25a : Datum :=
  { id := "chanshen2026_ex25a"
    source := ⟨"chan-shen-2026", "(25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who the hell is in love with who?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modifier", "theHell"), ("strategy", "full"), ("question", "multiple")] }

def ex26a : Datum :=
  { id := "chanshen2026_ex26a"
    source := ⟨"den-dikken-giannakidou-2002", "(71a)"⟩
    reportedIn := some ⟨"chan-shen-2026", "(26a)"⟩
    language := "stan1293"
    primaryText := "Who is in love with who the hell?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("modifier", "theHell"), ("strategy", "inSitu"), ("question", "multiple")] }

def all : List Datum := [ex1a, ex1b, ex4a, ex4b, ex4c, ex4d, ex6c, ex6d, ex11a, ex11b, ex15, ex17a, ex17b, ex19, ex22a, ex22b, ex25a, ex26a]

end ChanShen2026.Examples
