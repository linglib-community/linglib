module

public import Linglib.Data.Examples.Schema

/-!
# `Arka2013` — typed example data

Auto-generated from `Linglib/Data/Examples/Arka2013.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Arka2013.Examples`.
-/

@[expose] public section

namespace Arka2013.Examples

def ex_3 : Datum :=
  { id := "arka2013_3"
    source := ⟨"arka-2013", "(3)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia datang."
    glossedTokens := [("Dia", "3s"), ("datang", "come")]
    glossedWords := [⟨['D', 'i', 'a'], ['3', 's'], [⟨['D', 'i', 'a'], ['3', 's'], none⟩]⟩, ⟨['d', 'a', 't', 'a', 'n', 'g'], ['c', 'o', 'm', 'e'], [⟨['d', 'a', 't', 'a', 'n', 'g'], ['c', 'o', 'm', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("past", .acceptable), ("present", .acceptable), ("future", .acceptable)]
    paperFeatures := [] }

def ex_4a : Datum :=
  { id := "arka2013_4a"
    source := ⟨"arka-2013", "(4a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia datang (besok)."
    glossedTokens := [("Dia", "3s"), ("datang", "come"), ("besok", "tomorrow")]
    glossedWords := [⟨['D', 'i', 'a'], ['3', 's'], [⟨['D', 'i', 'a'], ['3', 's'], none⟩]⟩, ⟨['d', 'a', 't', 'a', 'n', 'g'], ['c', 'o', 'm', 'e'], [⟨['d', 'a', 't', 'a', 'n', 'g'], ['c', 'o', 'm', 'e'], none⟩]⟩, ⟨['b', 'e', 's', 'o', 'k'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['b', 'e', 's', 'o', 'k'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "S<E-R")] }

def ex_4b : Datum :=
  { id := "arka2013_4b"
    source := ⟨"arka-2013", "(4b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia datang (kemarin)."
    glossedTokens := [("Dia", "3s"), ("datang", "come"), ("kemarin", "yesterday")]
    glossedWords := [⟨['D', 'i', 'a'], ['3', 's'], [⟨['D', 'i', 'a'], ['3', 's'], none⟩]⟩, ⟨['d', 'a', 't', 'a', 'n', 'g'], ['c', 'o', 'm', 'e'], [⟨['d', 'a', 't', 'a', 'n', 'g'], ['c', 'o', 'm', 'e'], none⟩]⟩, ⟨['k', 'e', 'm', 'a', 'r', 'i', 'n'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['k', 'e', 'm', 'a', 'r', 'i', 'n'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "E-R<S")] }

def ex_4c : Datum :=
  { id := "arka2013_4c"
    source := ⟨"arka-2013", "(4c)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia datang (sekarang)."
    glossedTokens := [("Dia", "3s"), ("datang", "come"), ("sekarang", "now")]
    glossedWords := [⟨['D', 'i', 'a'], ['3', 's'], [⟨['D', 'i', 'a'], ['3', 's'], none⟩]⟩, ⟨['d', 'a', 't', 'a', 'n', 'g'], ['c', 'o', 'm', 'e'], [⟨['d', 'a', 't', 'a', 'n', 'g'], ['c', 'o', 'm', 'e'], none⟩]⟩, ⟨['s', 'e', 'k', 'a', 'r', 'a', 'n', 'g'], ['n', 'o', 'w'], [⟨['s', 'e', 'k', 'a', 'r', 'a', 'n', 'g'], ['n', 'o', 'w'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "E-R-S")] }

def ex_5a : Datum :=
  { id := "arka2013_5a"
    source := ⟨"arka-2013", "(5a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia sudah pergi (sekarang)."
    glossedTokens := [("Dia", "3s"), ("sudah", "PERF"), ("pergi", "go"), ("sekarang", "now")]
    glossedWords := [⟨['D', 'i', 'a'], ['3', 's'], [⟨['D', 'i', 'a'], ['3', 's'], none⟩]⟩, ⟨['s', 'u', 'd', 'a', 'h'], ['P', 'E', 'R', 'F'], [⟨['s', 'u', 'd', 'a', 'h'], ['P', 'E', 'R', 'F'], none⟩]⟩, ⟨['p', 'e', 'r', 'g', 'i'], ['g', 'o'], [⟨['p', 'e', 'r', 'g', 'i'], ['g', 'o'], none⟩]⟩, ⟨['s', 'e', 'k', 'a', 'r', 'a', 'n', 'g'], ['n', 'o', 'w'], [⟨['s', 'e', 'k', 'a', 'r', 'a', 'n', 'g'], ['n', 'o', 'w'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "E<S,R")] }

def ex_5b : Datum :=
  { id := "arka2013_5b"
    source := ⟨"arka-2013", "(5b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia sudah pergi kemarin."
    glossedTokens := [("Dia", "3s"), ("sudah", "PERF"), ("pergi", "go"), ("kemarin", "yesterday")]
    glossedWords := [⟨['D', 'i', 'a'], ['3', 's'], [⟨['D', 'i', 'a'], ['3', 's'], none⟩]⟩, ⟨['s', 'u', 'd', 'a', 'h'], ['P', 'E', 'R', 'F'], [⟨['s', 'u', 'd', 'a', 'h'], ['P', 'E', 'R', 'F'], none⟩]⟩, ⟨['p', 'e', 'r', 'g', 'i'], ['g', 'o'], [⟨['p', 'e', 'r', 'g', 'i'], ['g', 'o'], none⟩]⟩, ⟨['k', 'e', 'm', 'a', 'r', 'i', 'n'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['k', 'e', 'm', 'a', 'r', 'i', 'n'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "E<R<S")] }

def ex_6a : Datum :=
  { id := "arka2013_6a"
    source := ⟨"arka-2013", "(6a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Ali (sedang) me-mukul-i kepala=nya sendiri."
    glossedTokens := [("Ali", "A."), ("sedang", "PROG"), ("me-mukul-i", "AV.hit-I"), ("kepala=nya", "head=3sg.poss"), ("sendiri", "self")]
    glossedWords := [⟨['A', 'l', 'i'], ['A', '.'], [⟨['A', 'l', 'i'], ['A', '.'], none⟩]⟩, ⟨['s', 'e', 'd', 'a', 'n', 'g'], ['P', 'R', 'O', 'G'], [⟨['s', 'e', 'd', 'a', 'n', 'g'], ['P', 'R', 'O', 'G'], none⟩]⟩, ⟨['m', 'e', '-', 'm', 'u', 'k', 'u', 'l', '-', 'i'], ['A', 'V', '.', 'h', 'i', 't', '-', 'I'], []⟩, ⟨['k', 'e', 'p', 'a', 'l', 'a', '=', 'n', 'y', 'a'], ['h', 'e', 'a', 'd', '=', '3', 's', 'g', '.', 'p', 'o', 's', 's'], [⟨['k', 'e', 'p', 'a', 'l', 'a'], ['h', 'e', 'a', 'd'], none⟩, ⟨['n', 'y', 'a'], ['3', 's', 'g', '.', 'p', 'o', 's', 's'], some '='⟩]⟩, ⟨['s', 'e', 'n', 'd', 'i', 'r', 'i'], ['s', 'e', 'l', 'f'], [⟨['s', 'e', 'n', 'd', 'i', 'r', 'i'], ['s', 'e', 'l', 'f'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_6b : Datum :=
  { id := "arka2013_6b"
    source := ⟨"arka-2013", "(6b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Ali (sedang) me-mukul-mukul kepala=nya sendiri."
    glossedTokens := [("Ali", "Ali"), ("sedang", "PROG"), ("me-mukul-mukul", "AV.hit-RED"), ("kepala=nya", "head=3sg.poss"), ("sendiri", "self")]
    glossedWords := [⟨['A', 'l', 'i'], ['A', 'l', 'i'], [⟨['A', 'l', 'i'], ['A', 'l', 'i'], none⟩]⟩, ⟨['s', 'e', 'd', 'a', 'n', 'g'], ['P', 'R', 'O', 'G'], [⟨['s', 'e', 'd', 'a', 'n', 'g'], ['P', 'R', 'O', 'G'], none⟩]⟩, ⟨['m', 'e', '-', 'm', 'u', 'k', 'u', 'l', '-', 'm', 'u', 'k', 'u', 'l'], ['A', 'V', '.', 'h', 'i', 't', '-', 'R', 'E', 'D'], []⟩, ⟨['k', 'e', 'p', 'a', 'l', 'a', '=', 'n', 'y', 'a'], ['h', 'e', 'a', 'd', '=', '3', 's', 'g', '.', 'p', 'o', 's', 's'], [⟨['k', 'e', 'p', 'a', 'l', 'a'], ['h', 'e', 'a', 'd'], none⟩, ⟨['n', 'y', 'a'], ['3', 's', 'g', '.', 'p', 'o', 's', 's'], some '='⟩]⟩, ⟨['s', 'e', 'n', 'd', 'i', 'r', 'i'], ['s', 'e', 'l', 'f'], [⟨['s', 'e', 'n', 'd', 'i', 'r', 'i'], ['s', 'e', 'l', 'f'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_7 : Datum :=
  { id := "arka2013_7"
    source := ⟨"arka-2013", "(7)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Ali tidak masuk-masuk ke rumah."
    glossedTokens := [("Ali", "Ali"), ("tidak", "NEG"), ("masuk-masuk", "enter-RED"), ("ke", "to"), ("rumah", "house")]
    glossedWords := [⟨['A', 'l', 'i'], ['A', 'l', 'i'], [⟨['A', 'l', 'i'], ['A', 'l', 'i'], none⟩]⟩, ⟨['t', 'i', 'd', 'a', 'k'], ['N', 'E', 'G'], [⟨['t', 'i', 'd', 'a', 'k'], ['N', 'E', 'G'], none⟩]⟩, ⟨['m', 'a', 's', 'u', 'k', '-', 'm', 'a', 's', 'u', 'k'], ['e', 'n', 't', 'e', 'r', '-', 'R', 'E', 'D'], [⟨['m', 'a', 's', 'u', 'k'], ['e', 'n', 't', 'e', 'r'], none⟩, ⟨['m', 'a', 's', 'u', 'k'], ['R', 'E', 'D'], some '-'⟩]⟩, ⟨['k', 'e'], ['t', 'o'], [⟨['k', 'e'], ['t', 'o'], none⟩]⟩, ⟨['r', 'u', 'm', 'a', 'h'], ['h', 'o', 'u', 's', 'e'], [⟨['r', 'u', 'm', 'a', 'h'], ['h', 'o', 'u', 's', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_8 : Datum :=
  { id := "arka2013_8"
    source := ⟨"arka-2013", "(8)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia makan sambil menonton TV."
    glossedTokens := [("Dia", "3s"), ("makan", "eat"), ("sambil", "while"), ("menonton", "AV.watch"), ("TV", "TV")]
    glossedWords := [⟨['D', 'i', 'a'], ['3', 's'], [⟨['D', 'i', 'a'], ['3', 's'], none⟩]⟩, ⟨['m', 'a', 'k', 'a', 'n'], ['e', 'a', 't'], [⟨['m', 'a', 'k', 'a', 'n'], ['e', 'a', 't'], none⟩]⟩, ⟨['s', 'a', 'm', 'b', 'i', 'l'], ['w', 'h', 'i', 'l', 'e'], [⟨['s', 'a', 'm', 'b', 'i', 'l'], ['w', 'h', 'i', 'l', 'e'], none⟩]⟩, ⟨['m', 'e', 'n', 'o', 'n', 't', 'o', 'n'], ['A', 'V', '.', 'w', 'a', 't', 'c', 'h'], [⟨['m', 'e', 'n', 'o', 'n', 't', 'o', 'n'], ['A', 'V', '.', 'w', 'a', 't', 'c', 'h'], none⟩]⟩, ⟨['T', 'V'], ['T', 'V'], [⟨['T', 'V'], ['T', 'V'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_10 : Datum :=
  { id := "arka2013_10"
    source := ⟨"arka-2013", "(10)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Mereka (akan) datang."
    glossedTokens := [("Mereka", "3p"), ("akan", "FUT"), ("datang", "come")]
    glossedWords := [⟨['M', 'e', 'r', 'e', 'k', 'a'], ['3', 'p'], [⟨['M', 'e', 'r', 'e', 'k', 'a'], ['3', 'p'], none⟩]⟩, ⟨['a', 'k', 'a', 'n'], ['F', 'U', 'T'], [⟨['a', 'k', 'a', 'n'], ['F', 'U', 'T'], none⟩]⟩, ⟨['d', 'a', 't', 'a', 'n', 'g'], ['c', 'o', 'm', 'e'], [⟨['d', 'a', 't', 'a', 'n', 'g'], ['c', 'o', 'm', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "S<E-R")] }

def ex_11a : Datum :=
  { id := "arka2013_11a"
    source := ⟨"arka-2013", "(11a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Mereka ingin [datang besok]."
    glossedTokens := [("Mereka", "3p"), ("ingin", "want"), ("datang", "come"), ("besok", "tomorrow")]
    glossedWords := [⟨['M', 'e', 'r', 'e', 'k', 'a'], ['3', 'p'], [⟨['M', 'e', 'r', 'e', 'k', 'a'], ['3', 'p'], none⟩]⟩, ⟨['i', 'n', 'g', 'i', 'n'], ['w', 'a', 'n', 't'], [⟨['i', 'n', 'g', 'i', 'n'], ['w', 'a', 'n', 't'], none⟩]⟩, ⟨['d', 'a', 't', 'a', 'n', 'g'], ['c', 'o', 'm', 'e'], [⟨['d', 'a', 't', 'a', 'n', 'g'], ['c', 'o', 'm', 'e'], none⟩]⟩, ⟨['b', 'e', 's', 'o', 'k'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['b', 'e', 's', 'o', 'k'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Mereka ingin [akan datang besok].", .ungrammatical)]
    readings := []
    paperFeatures := [] }

def ex_11c : Datum :=
  { id := "arka2013_11c"
    source := ⟨"arka-2013", "(11c)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Saya tahu [bahwa mereka akan datang]."
    glossedTokens := [("Saya", "1s"), ("tahu", "know"), ("bahwa", "that"), ("mereka", "3p"), ("akan", "FUT"), ("datang", "come")]
    glossedWords := [⟨['S', 'a', 'y', 'a'], ['1', 's'], [⟨['S', 'a', 'y', 'a'], ['1', 's'], none⟩]⟩, ⟨['t', 'a', 'h', 'u'], ['k', 'n', 'o', 'w'], [⟨['t', 'a', 'h', 'u'], ['k', 'n', 'o', 'w'], none⟩]⟩, ⟨['b', 'a', 'h', 'w', 'a'], ['t', 'h', 'a', 't'], [⟨['b', 'a', 'h', 'w', 'a'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['m', 'e', 'r', 'e', 'k', 'a'], ['3', 'p'], [⟨['m', 'e', 'r', 'e', 'k', 'a'], ['3', 'p'], none⟩]⟩, ⟨['a', 'k', 'a', 'n'], ['F', 'U', 'T'], [⟨['a', 'k', 'a', 'n'], ['F', 'U', 'T'], none⟩]⟩, ⟨['d', 'a', 't', 'a', 'n', 'g'], ['c', 'o', 'm', 'e'], [⟨['d', 'a', 't', 'a', 'n', 'g'], ['c', 'o', 'm', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_12a : Datum :=
  { id := "arka2013_12a"
    source := ⟨"arka-2013", "(12a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia akan makan."
    glossedTokens := [("Dia", "3s"), ("akan", "FUT"), ("makan", "eat")]
    glossedWords := [⟨['D', 'i', 'a'], ['3', 's'], [⟨['D', 'i', 'a'], ['3', 's'], none⟩]⟩, ⟨['a', 'k', 'a', 'n'], ['F', 'U', 'T'], [⟨['a', 'k', 'a', 'n'], ['F', 'U', 'T'], none⟩]⟩, ⟨['m', 'a', 'k', 'a', 'n'], ['e', 'a', 't'], [⟨['m', 'a', 'k', 'a', 'n'], ['e', 'a', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Dia sudah makan.", .acceptable), ("Dia sedang makan.", .acceptable)]
    readings := []
    paperFeatures := [] }

def ex_12b : Datum :=
  { id := "arka2013_12b"
    source := ⟨"arka-2013", "(12b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Saya menyuruh dia [makan]."
    glossedTokens := [("Saya", "1s"), ("menyuruh", "AV.ask"), ("dia", "3s"), ("makan", "eat")]
    glossedWords := [⟨['S', 'a', 'y', 'a'], ['1', 's'], [⟨['S', 'a', 'y', 'a'], ['1', 's'], none⟩]⟩, ⟨['m', 'e', 'n', 'y', 'u', 'r', 'u', 'h'], ['A', 'V', '.', 'a', 's', 'k'], [⟨['m', 'e', 'n', 'y', 'u', 'r', 'u', 'h'], ['A', 'V', '.', 'a', 's', 'k'], none⟩]⟩, ⟨['d', 'i', 'a'], ['3', 's'], [⟨['d', 'i', 'a'], ['3', 's'], none⟩]⟩, ⟨['m', 'a', 'k', 'a', 'n'], ['e', 'a', 't'], [⟨['m', 'a', 'k', 'a', 'n'], ['e', 'a', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Saya menyuruh dia [akan makan].", .ungrammatical), ("Saya menyuruh dia [sudah makan].", .ungrammatical), ("Saya menyuruh dia [sedang makan].", .ungrammatical)]
    readings := []
    paperFeatures := [] }

def ex_13a : Datum :=
  { id := "arka2013_13a"
    source := ⟨"arka-2013", "(13a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Orang itu mendorong saya [ _ jatuh]."
    glossedTokens := [("Orang", "person"), ("itu", "that"), ("mendorong", "AV.push"), ("saya", "1s"), ("jatuh", "fall")]
    glossedWords := [⟨['O', 'r', 'a', 'n', 'g'], ['p', 'e', 'r', 's', 'o', 'n'], [⟨['O', 'r', 'a', 'n', 'g'], ['p', 'e', 'r', 's', 'o', 'n'], none⟩]⟩, ⟨['i', 't', 'u'], ['t', 'h', 'a', 't'], [⟨['i', 't', 'u'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['m', 'e', 'n', 'd', 'o', 'r', 'o', 'n', 'g'], ['A', 'V', '.', 'p', 'u', 's', 'h'], [⟨['m', 'e', 'n', 'd', 'o', 'r', 'o', 'n', 'g'], ['A', 'V', '.', 'p', 'u', 's', 'h'], none⟩]⟩, ⟨['s', 'a', 'y', 'a'], ['1', 's'], [⟨['s', 'a', 'y', 'a'], ['1', 's'], none⟩]⟩, ⟨['j', 'a', 't', 'u', 'h'], ['f', 'a', 'l', 'l'], [⟨['j', 'a', 't', 'u', 'h'], ['f', 'a', 'l', 'l'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Orang itu mendorong saya [ _ akan jatuh].", .ungrammatical), ("Orang itu mendorong saya [ _ sedang jatuh].", .ungrammatical), ("Orang itu mendorong saya [ _ sudah jatuh].", .ungrammatical)]
    readings := []
    paperFeatures := [] }

def ex_14a : Datum :=
  { id := "arka2013_14a"
    source := ⟨"arka-2013", "(14a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia datang (sambil) menangis."
    glossedTokens := [("Dia", "3s"), ("datang", "come"), ("sambil", "while"), ("menangis", "AV.cry")]
    glossedWords := [⟨['D', 'i', 'a'], ['3', 's'], [⟨['D', 'i', 'a'], ['3', 's'], none⟩]⟩, ⟨['d', 'a', 't', 'a', 'n', 'g'], ['c', 'o', 'm', 'e'], [⟨['d', 'a', 't', 'a', 'n', 'g'], ['c', 'o', 'm', 'e'], none⟩]⟩, ⟨['s', 'a', 'm', 'b', 'i', 'l'], ['w', 'h', 'i', 'l', 'e'], [⟨['s', 'a', 'm', 'b', 'i', 'l'], ['w', 'h', 'i', 'l', 'e'], none⟩]⟩, ⟨['m', 'e', 'n', 'a', 'n', 'g', 'i', 's'], ['A', 'V', '.', 'c', 'r', 'y'], [⟨['m', 'e', 'n', 'a', 'n', 'g', 'i', 's'], ['A', 'V', '.', 'c', 'r', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Dia datang [(sambil) sedang menangis].", .ungrammatical)]
    readings := []
    paperFeatures := [] }

def ex_15a : Datum :=
  { id := "arka2013_15a"
    source := ⟨"arka-2013", "(15a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Saya belajar [menembak]."
    glossedTokens := [("Saya", "1s"), ("belajar", "study"), ("menembak", "AV.shoot")]
    glossedWords := [⟨['S', 'a', 'y', 'a'], ['1', 's'], [⟨['S', 'a', 'y', 'a'], ['1', 's'], none⟩]⟩, ⟨['b', 'e', 'l', 'a', 'j', 'a', 'r'], ['s', 't', 'u', 'd', 'y'], [⟨['b', 'e', 'l', 'a', 'j', 'a', 'r'], ['s', 't', 'u', 'd', 'y'], none⟩]⟩, ⟨['m', 'e', 'n', 'e', 'm', 'b', 'a', 'k'], ['A', 'V', '.', 's', 'h', 'o', 'o', 't'], [⟨['m', 'e', 'n', 'e', 'm', 'b', 'a', 'k'], ['A', 'V', '.', 's', 'h', 'o', 'o', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Saya belajar bisa [menembak].", .ungrammatical)]
    readings := []
    paperFeatures := [] }

def ex_15c : Datum :=
  { id := "arka2013_15c"
    source := ⟨"arka-2013", "(15c)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Saya belajar agar (bisa) menembak."
    glossedTokens := [("Saya", "1s"), ("belajar", "study"), ("agar", "so.that"), ("bisa", "able"), ("menembak", "AV.shoot")]
    glossedWords := [⟨['S', 'a', 'y', 'a'], ['1', 's'], [⟨['S', 'a', 'y', 'a'], ['1', 's'], none⟩]⟩, ⟨['b', 'e', 'l', 'a', 'j', 'a', 'r'], ['s', 't', 'u', 'd', 'y'], [⟨['b', 'e', 'l', 'a', 'j', 'a', 'r'], ['s', 't', 'u', 'd', 'y'], none⟩]⟩, ⟨['a', 'g', 'a', 'r'], ['s', 'o', '.', 't', 'h', 'a', 't'], [⟨['a', 'g', 'a', 'r'], ['s', 'o', '.', 't', 'h', 'a', 't'], none⟩]⟩, ⟨['b', 'i', 's', 'a'], ['a', 'b', 'l', 'e'], [⟨['b', 'i', 's', 'a'], ['a', 'b', 'l', 'e'], none⟩]⟩, ⟨['m', 'e', 'n', 'e', 'm', 'b', 'a', 'k'], ['A', 'V', '.', 's', 'h', 'o', 'o', 't'], [⟨['m', 'e', 'n', 'e', 'm', 'b', 'a', 'k'], ['A', 'V', '.', 's', 'h', 'o', 'o', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_18a : Datum :=
  { id := "arka2013_18a"
    source := ⟨"arka-2013", "(18a)"⟩
    reportedIn := none
    method := some .corpus
    language := "indo1316"
    primaryText := "...di jalan banyak sapi yang sedang memakan rumput."
    glossedTokens := [("di", "at"), ("jalan", "road"), ("banyak", "plenty"), ("sapi", "cow"), ("yang", "REL"), ("sedang", "PROG"), ("memakan", "AV.eat"), ("rumput", "grass")]
    glossedWords := [⟨['d', 'i'], ['a', 't'], [⟨['d', 'i'], ['a', 't'], none⟩]⟩, ⟨['j', 'a', 'l', 'a', 'n'], ['r', 'o', 'a', 'd'], [⟨['j', 'a', 'l', 'a', 'n'], ['r', 'o', 'a', 'd'], none⟩]⟩, ⟨['b', 'a', 'n', 'y', 'a', 'k'], ['p', 'l', 'e', 'n', 't', 'y'], [⟨['b', 'a', 'n', 'y', 'a', 'k'], ['p', 'l', 'e', 'n', 't', 'y'], none⟩]⟩, ⟨['s', 'a', 'p', 'i'], ['c', 'o', 'w'], [⟨['s', 'a', 'p', 'i'], ['c', 'o', 'w'], none⟩]⟩, ⟨['y', 'a', 'n', 'g'], ['R', 'E', 'L'], [⟨['y', 'a', 'n', 'g'], ['R', 'E', 'L'], none⟩]⟩, ⟨['s', 'e', 'd', 'a', 'n', 'g'], ['P', 'R', 'O', 'G'], [⟨['s', 'e', 'd', 'a', 'n', 'g'], ['P', 'R', 'O', 'G'], none⟩]⟩, ⟨['m', 'e', 'm', 'a', 'k', 'a', 'n'], ['A', 'V', '.', 'e', 'a', 't'], [⟨['m', 'e', 'm', 'a', 'k', 'a', 'n'], ['A', 'V', '.', 'e', 'a', 't'], none⟩]⟩, ⟨['r', 'u', 'm', 'p', 'u', 't'], ['g', 'r', 'a', 's', 's'], [⟨['r', 'u', 'm', 'p', 'u', 't'], ['g', 'r', 'a', 's', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_18b : Datum :=
  { id := "arka2013_18b"
    source := ⟨"arka-2013", "(18b)"⟩
    reportedIn := none
    method := some .corpus
    language := "indo1316"
    primaryText := "Dari salah satu swalayan, petugas menemukan makanan jenis roti yang kemasan dan isi=nya telah rusak dan diduga sudah dimakan tikus."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_34a : Datum :=
  { id := "arka2013_34a"
    source := ⟨"arka-2013", "(34a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "'Siapa itu?', tanya=nya."
    glossedTokens := [("Siapa", "who"), ("itu", "that"), ("tanya=nya", "ask=NYA")]
    glossedWords := [⟨['S', 'i', 'a', 'p', 'a'], ['w', 'h', 'o'], [⟨['S', 'i', 'a', 'p', 'a'], ['w', 'h', 'o'], none⟩]⟩, ⟨['i', 't', 'u'], ['t', 'h', 'a', 't'], [⟨['i', 't', 'u'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['t', 'a', 'n', 'y', 'a', '=', 'n', 'y', 'a'], ['a', 's', 'k', '=', 'N', 'Y', 'A'], [⟨['t', 'a', 'n', 'y', 'a'], ['a', 's', 'k'], none⟩, ⟨['n', 'y', 'a'], ['N', 'Y', 'A'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("'Siapa itu?' akan tanyanya (nanti).", .ungrammatical)]
    readings := [("past", .acceptable), ("future", .unacceptable)]
    paperFeatures := [] }

def ex_34b : Datum :=
  { id := "arka2013_34b"
    source := ⟨"arka-2013", "(34b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "'Siapa itu?', tanya=nya nanti."
    glossedTokens := [("Siapa", "who"), ("itu", "that"), ("tanya=nya", "ask=NYA"), ("nanti", "later")]
    glossedWords := [⟨['S', 'i', 'a', 'p', 'a'], ['w', 'h', 'o'], [⟨['S', 'i', 'a', 'p', 'a'], ['w', 'h', 'o'], none⟩]⟩, ⟨['i', 't', 'u'], ['t', 'h', 'a', 't'], [⟨['i', 't', 'u'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['t', 'a', 'n', 'y', 'a', '=', 'n', 'y', 'a'], ['a', 's', 'k', '=', 'N', 'Y', 'A'], [⟨['t', 'a', 'n', 'y', 'a'], ['a', 's', 'k'], none⟩, ⟨['n', 'y', 'a'], ['N', 'Y', 'A'], some '='⟩]⟩, ⟨['n', 'a', 'n', 't', 'i'], ['l', 'a', 't', 'e', 'r'], [⟨['n', 'a', 'n', 't', 'i'], ['l', 'a', 't', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("future", .acceptable)]
    paperFeatures := [] }

def ex_34d : Datum :=
  { id := "arka2013_34d"
    source := ⟨"arka-2013", "(34d)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "'Siapa itu?', dia akan (ber)tanya (nanti)."
    glossedTokens := [("Siapa", "who"), ("itu", "that"), ("dia", "3"), ("akan", "FUT"), ("(ber)tanya", "BER-ask"), ("nanti", "later")]
    glossedWords := [⟨['S', 'i', 'a', 'p', 'a'], ['w', 'h', 'o'], [⟨['S', 'i', 'a', 'p', 'a'], ['w', 'h', 'o'], none⟩]⟩, ⟨['i', 't', 'u'], ['t', 'h', 'a', 't'], [⟨['i', 't', 'u'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['d', 'i', 'a'], ['3'], [⟨['d', 'i', 'a'], ['3'], none⟩]⟩, ⟨['a', 'k', 'a', 'n'], ['F', 'U', 'T'], [⟨['a', 'k', 'a', 'n'], ['F', 'U', 'T'], none⟩]⟩, ⟨['(', 'b', 'e', 'r', ')', 't', 'a', 'n', 'y', 'a'], ['B', 'E', 'R', '-', 'a', 's', 'k'], []⟩, ⟨['n', 'a', 'n', 't', 'i'], ['l', 'a', 't', 'e', 'r'], [⟨['n', 'a', 'n', 't', 'i'], ['l', 'a', 't', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_35a : Datum :=
  { id := "arka2013_35a"
    source := ⟨"arka-2013", "(35a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Kapan beli=nya?"
    glossedTokens := [("Kapan", "when"), ("beli=nya", "buy=NYA")]
    glossedWords := [⟨['K', 'a', 'p', 'a', 'n'], ['w', 'h', 'e', 'n'], [⟨['K', 'a', 'p', 'a', 'n'], ['w', 'h', 'e', 'n'], none⟩]⟩, ⟨['b', 'e', 'l', 'i', '=', 'n', 'y', 'a'], ['b', 'u', 'y', '=', 'N', 'Y', 'A'], [⟨['b', 'e', 'l', 'i'], ['b', 'u', 'y'], none⟩, ⟨['n', 'y', 'a'], ['N', 'Y', 'A'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("kapan akan beli=nya?", .ungrammatical)]
    readings := [("past", .acceptable), ("future", .unacceptable)]
    paperFeatures := [] }

def ex_35c : Datum :=
  { id := "arka2013_35c"
    source := ⟨"arka-2013", "(35c)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Kapan kamu akan beli?"
    glossedTokens := [("Kapan", "when"), ("kamu", "2s"), ("akan", "FUT"), ("beli", "buy")]
    glossedWords := [⟨['K', 'a', 'p', 'a', 'n'], ['w', 'h', 'e', 'n'], [⟨['K', 'a', 'p', 'a', 'n'], ['w', 'h', 'e', 'n'], none⟩]⟩, ⟨['k', 'a', 'm', 'u'], ['2', 's'], [⟨['k', 'a', 'm', 'u'], ['2', 's'], none⟩]⟩, ⟨['a', 'k', 'a', 'n'], ['F', 'U', 'T'], [⟨['a', 'k', 'a', 'n'], ['F', 'U', 'T'], none⟩]⟩, ⟨['b', 'e', 'l', 'i'], ['b', 'u', 'y'], [⟨['b', 'e', 'l', 'i'], ['b', 'u', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_36a : Datum :=
  { id := "arka2013_36a"
    source := ⟨"arka-2013", "(36a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Kapan lahirnya?"
    glossedTokens := [("Kapan", "when"), ("lahirnya", "birth=3s")]
    glossedWords := [⟨['K', 'a', 'p', 'a', 'n'], ['w', 'h', 'e', 'n'], [⟨['K', 'a', 'p', 'a', 'n'], ['w', 'h', 'e', 'n'], none⟩]⟩, ⟨['l', 'a', 'h', 'i', 'r', 'n', 'y', 'a'], ['b', 'i', 'r', 't', 'h', '=', '3', 's'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Kapan akan lahirnya?", .ungrammatical)]
    readings := [("past", .acceptable), ("future", .unacceptable)]
    paperFeatures := [] }

def ex_36c : Datum :=
  { id := "arka2013_36c"
    source := ⟨"arka-2013", "(36c)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Kapan ia akan lahir?"
    glossedTokens := [("Kapan", "when"), ("ia", "3s"), ("akan", "FUT"), ("lahir", "birth")]
    glossedWords := [⟨['K', 'a', 'p', 'a', 'n'], ['w', 'h', 'e', 'n'], [⟨['K', 'a', 'p', 'a', 'n'], ['w', 'h', 'e', 'n'], none⟩]⟩, ⟨['i', 'a'], ['3', 's'], [⟨['i', 'a'], ['3', 's'], none⟩]⟩, ⟨['a', 'k', 'a', 'n'], ['F', 'U', 'T'], [⟨['a', 'k', 'a', 'n'], ['F', 'U', 'T'], none⟩]⟩, ⟨['l', 'a', 'h', 'i', 'r'], ['b', 'i', 'r', 't', 'h'], [⟨['l', 'a', 'h', 'i', 'r'], ['b', 'i', 'r', 't', 'h'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_37a : Datum :=
  { id := "arka2013_37a"
    source := ⟨"arka-2013", "(37a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "kamu harus datang."
    glossedTokens := [("kamu", "2"), ("harus", "must"), ("datang", "come")]
    glossedWords := [⟨['k', 'a', 'm', 'u'], ['2'], [⟨['k', 'a', 'm', 'u'], ['2'], none⟩]⟩, ⟨['h', 'a', 'r', 'u', 's'], ['m', 'u', 's', 't'], [⟨['h', 'a', 'r', 'u', 's'], ['m', 'u', 's', 't'], none⟩]⟩, ⟨['d', 'a', 't', 'a', 'n', 'g'], ['c', 'o', 'm', 'e'], [⟨['d', 'a', 't', 'a', 'n', 'g'], ['c', 'o', 'm', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("soa", "future"), ("evaluation", "deontic")] }

def ex_37b : Datum :=
  { id := "arka2013_37b"
    source := ⟨"arka-2013", "(37b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "harus=nya kamu datang."
    glossedTokens := [("harus=nya", "must=NYA"), ("kamu", "2"), ("datang", "come")]
    glossedWords := [⟨['h', 'a', 'r', 'u', 's', '=', 'n', 'y', 'a'], ['m', 'u', 's', 't', '=', 'N', 'Y', 'A'], [⟨['h', 'a', 'r', 'u', 's'], ['m', 'u', 's', 't'], none⟩, ⟨['n', 'y', 'a'], ['N', 'Y', 'A'], some '='⟩]⟩, ⟨['k', 'a', 'm', 'u'], ['2'], [⟨['k', 'a', 'm', 'u'], ['2'], none⟩]⟩, ⟨['d', 'a', 't', 'a', 'n', 'g'], ['c', 'o', 'm', 'e'], [⟨['d', 'a', 't', 'a', 'n', 'g'], ['c', 'o', 'm', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("soa", "past"), ("evaluation", "counterfactual")] }

def ex_38a : Datum :=
  { id := "arka2013_38a"
    source := ⟨"arka-2013", "(38a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Ia bisa menangis"
    glossedTokens := [("Ia", "she"), ("bisa", "can"), ("menangis", "cry")]
    glossedWords := [⟨['I', 'a'], ['s', 'h', 'e'], [⟨['I', 'a'], ['s', 'h', 'e'], none⟩]⟩, ⟨['b', 'i', 's', 'a'], ['c', 'a', 'n'], [⟨['b', 'i', 's', 'a'], ['c', 'a', 'n'], none⟩]⟩, ⟨['m', 'e', 'n', 'a', 'n', 'g', 'i', 's'], ['c', 'r', 'y'], [⟨['m', 'e', 'n', 'a', 'n', 'g', 'i', 's'], ['c', 'r', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("soa", "future"), ("evaluation", "epistemic")] }

def ex_38b : Datum :=
  { id := "arka2013_38b"
    source := ⟨"arka-2013", "(38b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "bisa=nya menangis"
    glossedTokens := [("bisa=nya", "can=3s"), ("menangis", "cry")]
    glossedWords := [⟨['b', 'i', 's', 'a', '=', 'n', 'y', 'a'], ['c', 'a', 'n', '=', '3', 's'], [⟨['b', 'i', 's', 'a'], ['c', 'a', 'n'], none⟩, ⟨['n', 'y', 'a'], ['3', 's'], some '='⟩]⟩, ⟨['m', 'e', 'n', 'a', 'n', 'g', 'i', 's'], ['c', 'r', 'y'], [⟨['m', 'e', 'n', 'a', 'n', 'g', 'i', 's'], ['c', 'r', 'y'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("soa", "past"), ("evaluation", "past ability")] }

def ex_39a : Datum :=
  { id := "arka2013_39a"
    source := ⟨"arka-2013", "(39a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Ia mau pulang."
    glossedTokens := [("Ia", "3s"), ("mau", "wish"), ("pulang", "go.home")]
    glossedWords := [⟨['I', 'a'], ['3', 's'], [⟨['I', 'a'], ['3', 's'], none⟩]⟩, ⟨['m', 'a', 'u'], ['w', 'i', 's', 'h'], [⟨['m', 'a', 'u'], ['w', 'i', 's', 'h'], none⟩]⟩, ⟨['p', 'u', 'l', 'a', 'n', 'g'], ['g', 'o', '.', 'h', 'o', 'm', 'e'], [⟨['p', 'u', 'l', 'a', 'n', 'g'], ['g', 'o', '.', 'h', 'o', 'm', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("soa", "future")] }

def ex_39b : Datum :=
  { id := "arka2013_39b"
    source := ⟨"arka-2013", "(39b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "mau=nya pulang."
    glossedTokens := [("mau=nya", "wish=DEF"), ("pulang", "go.home")]
    glossedWords := [⟨['m', 'a', 'u', '=', 'n', 'y', 'a'], ['w', 'i', 's', 'h', '=', 'D', 'E', 'F'], [⟨['m', 'a', 'u'], ['w', 'i', 's', 'h'], none⟩, ⟨['n', 'y', 'a'], ['D', 'E', 'F'], some '='⟩]⟩, ⟨['p', 'u', 'l', 'a', 'n', 'g'], ['g', 'o', '.', 'h', 'o', 'm', 'e'], [⟨['p', 'u', 'l', 'a', 'n', 'g'], ['g', 'o', '.', 'h', 'o', 'm', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("evaluation", "counterfactual"), ("soa", "present"), ("soa", "past")] }

def ex_40a : Datum :=
  { id := "arka2013_40a"
    source := ⟨"arka-2013", "(40a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "tampak=nya [ada orang datang]"
    glossedTokens := [("tampak=nya", "appear=DEF"), ("ada", "exist"), ("orang", "person"), ("datang", "come")]
    glossedWords := [⟨['t', 'a', 'm', 'p', 'a', 'k', '=', 'n', 'y', 'a'], ['a', 'p', 'p', 'e', 'a', 'r', '=', 'D', 'E', 'F'], [⟨['t', 'a', 'm', 'p', 'a', 'k'], ['a', 'p', 'p', 'e', 'a', 'r'], none⟩, ⟨['n', 'y', 'a'], ['D', 'E', 'F'], some '='⟩]⟩, ⟨['a', 'd', 'a'], ['e', 'x', 'i', 's', 't'], [⟨['a', 'd', 'a'], ['e', 'x', 'i', 's', 't'], none⟩]⟩, ⟨['o', 'r', 'a', 'n', 'g'], ['p', 'e', 'r', 's', 'o', 'n'], [⟨['o', 'r', 'a', 'n', 'g'], ['p', 'e', 'r', 's', 'o', 'n'], none⟩]⟩, ⟨['d', 'a', 't', 'a', 'n', 'g'], ['c', 'o', 'm', 'e'], [⟨['d', 'a', 't', 'a', 'n', 'g'], ['c', 'o', 'm', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("sedang tampak=nya [ada orang datang].", .ungrammatical)]
    readings := []
    paperFeatures := [] }

def ex_41 : Datum :=
  { id := "arka2013_41"
    source := ⟨"arka-2013", "(41)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Tampak ada orang datang"
    glossedTokens := [("Tampak", "appear"), ("ada", "exist"), ("orang", "people"), ("datang", "come")]
    glossedWords := [⟨['T', 'a', 'm', 'p', 'a', 'k'], ['a', 'p', 'p', 'e', 'a', 'r'], [⟨['T', 'a', 'm', 'p', 'a', 'k'], ['a', 'p', 'p', 'e', 'a', 'r'], none⟩]⟩, ⟨['a', 'd', 'a'], ['e', 'x', 'i', 's', 't'], [⟨['a', 'd', 'a'], ['e', 'x', 'i', 's', 't'], none⟩]⟩, ⟨['o', 'r', 'a', 'n', 'g'], ['p', 'e', 'o', 'p', 'l', 'e'], [⟨['o', 'r', 'a', 'n', 'g'], ['p', 'e', 'o', 'p', 'l', 'e'], none⟩]⟩, ⟨['d', 'a', 't', 'a', 'n', 'g'], ['c', 'o', 'm', 'e'], [⟨['d', 'a', 't', 'a', 'n', 'g'], ['c', 'o', 'm', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_42a : Datum :=
  { id := "arka2013_42a"
    source := ⟨"arka-2013", "(42a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia sakit."
    glossedTokens := [("Dia", "3s"), ("sakit", "ill")]
    glossedWords := [⟨['D', 'i', 'a'], ['3', 's'], [⟨['D', 'i', 'a'], ['3', 's'], none⟩]⟩, ⟨['s', 'a', 'k', 'i', 't'], ['i', 'l', 'l'], [⟨['s', 'a', 'k', 'i', 't'], ['i', 'l', 'l'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_42b : Datum :=
  { id := "arka2013_42b"
    source := ⟨"arka-2013", "(42b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia sakit kata=nya."
    glossedTokens := [("Dia", "3s"), ("sakit", "ill"), ("kata=nya", "word=DEF")]
    glossedWords := [⟨['D', 'i', 'a'], ['3', 's'], [⟨['D', 'i', 'a'], ['3', 's'], none⟩]⟩, ⟨['s', 'a', 'k', 'i', 't'], ['i', 'l', 'l'], [⟨['s', 'a', 'k', 'i', 't'], ['i', 'l', 'l'], none⟩]⟩, ⟨['k', 'a', 't', 'a', '=', 'n', 'y', 'a'], ['w', 'o', 'r', 'd', '=', 'D', 'E', 'F'], [⟨['k', 'a', 't', 'a'], ['w', 'o', 'r', 'd'], none⟩, ⟨['n', 'y', 'a'], ['D', 'E', 'F'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_43a : Datum :=
  { id := "arka2013_43a"
    source := ⟨"arka-2013", "(43a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Kamu pembohong kata=nya"
    glossedTokens := [("Kamu", "2"), ("pembohong", "PEN.lie"), ("kata=nya", "word=DEF")]
    glossedWords := [⟨['K', 'a', 'm', 'u'], ['2'], [⟨['K', 'a', 'm', 'u'], ['2'], none⟩]⟩, ⟨['p', 'e', 'm', 'b', 'o', 'h', 'o', 'n', 'g'], ['P', 'E', 'N', '.', 'l', 'i', 'e'], [⟨['p', 'e', 'm', 'b', 'o', 'h', 'o', 'n', 'g'], ['P', 'E', 'N', '.', 'l', 'i', 'e'], none⟩]⟩, ⟨['k', 'a', 't', 'a', '=', 'n', 'y', 'a'], ['w', 'o', 'r', 'd', '=', 'D', 'E', 'F'], [⟨['k', 'a', 't', 'a'], ['w', 'o', 'r', 'd'], none⟩, ⟨['n', 'y', 'a'], ['D', 'E', 'F'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_43b : Datum :=
  { id := "arka2013_43b"
    source := ⟨"arka-2013", "(43b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Kamu pembohong keluh=nya"
    glossedTokens := [("Kamu", "2"), ("pembohong", "PEN.lie"), ("keluh=nya", "word=3POSS")]
    glossedWords := [⟨['K', 'a', 'm', 'u'], ['2'], [⟨['K', 'a', 'm', 'u'], ['2'], none⟩]⟩, ⟨['p', 'e', 'm', 'b', 'o', 'h', 'o', 'n', 'g'], ['P', 'E', 'N', '.', 'l', 'i', 'e'], [⟨['p', 'e', 'm', 'b', 'o', 'h', 'o', 'n', 'g'], ['P', 'E', 'N', '.', 'l', 'i', 'e'], none⟩]⟩, ⟨['k', 'e', 'l', 'u', 'h', '=', 'n', 'y', 'a'], ['w', 'o', 'r', 'd', '=', '3', 'P', 'O', 'S', 'S'], [⟨['k', 'e', 'l', 'u', 'h'], ['w', 'o', 'r', 'd'], none⟩, ⟨['n', 'y', 'a'], ['3', 'P', 'O', 'S', 'S'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_44a : Datum :=
  { id := "arka2013_44a"
    source := ⟨"arka-2013", "(44a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia tidur."
    glossedTokens := [("Dia", "3s"), ("tidur", "sleep")]
    glossedWords := [⟨['D', 'i', 'a'], ['3', 's'], [⟨['D', 'i', 'a'], ['3', 's'], none⟩]⟩, ⟨['t', 'i', 'd', 'u', 'r'], ['s', 'l', 'e', 'e', 'p'], [⟨['t', 'i', 'd', 'u', 'r'], ['s', 'l', 'e', 'e', 'p'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Dia adalah tidur.", .ungrammatical)]
    readings := []
    paperFeatures := [] }

def ex_45a : Datum :=
  { id := "arka2013_45a"
    source := ⟨"arka-2013", "(45a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Ali (adalah) guru itu."
    glossedTokens := [("Ali", "Ali"), ("adalah", "be"), ("guru", "teacher"), ("itu", "the")]
    glossedWords := [⟨['A', 'l', 'i'], ['A', 'l', 'i'], [⟨['A', 'l', 'i'], ['A', 'l', 'i'], none⟩]⟩, ⟨['a', 'd', 'a', 'l', 'a', 'h'], ['b', 'e'], [⟨['a', 'd', 'a', 'l', 'a', 'h'], ['b', 'e'], none⟩]⟩, ⟨['g', 'u', 'r', 'u'], ['t', 'e', 'a', 'c', 'h', 'e', 'r'], [⟨['g', 'u', 'r', 'u'], ['t', 'e', 'a', 'c', 'h', 'e', 'r'], none⟩]⟩, ⟨['i', 't', 'u'], ['t', 'h', 'e'], [⟨['i', 't', 'u'], ['t', 'h', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_45b : Datum :=
  { id := "arka2013_45b"
    source := ⟨"arka-2013", "(45b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Guru itu (adalah) Ali."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_46a : Datum :=
  { id := "arka2013_46a"
    source := ⟨"arka-2013", "(46a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "[ _ tidur] (adalah) mau=nya"
    glossedTokens := [("tidur", "sleep"), ("adalah", "be"), ("mau=nya", "want=DEF")]
    glossedWords := [⟨['t', 'i', 'd', 'u', 'r'], ['s', 'l', 'e', 'e', 'p'], [⟨['t', 'i', 'd', 'u', 'r'], ['s', 'l', 'e', 'e', 'p'], none⟩]⟩, ⟨['a', 'd', 'a', 'l', 'a', 'h'], ['b', 'e'], [⟨['a', 'd', 'a', 'l', 'a', 'h'], ['b', 'e'], none⟩]⟩, ⟨['m', 'a', 'u', '=', 'n', 'y', 'a'], ['w', 'a', 'n', 't', '=', 'D', 'E', 'F'], [⟨['m', 'a', 'u'], ['w', 'a', 'n', 't'], none⟩, ⟨['n', 'y', 'a'], ['D', 'E', 'F'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_46b : Datum :=
  { id := "arka2013_46b"
    source := ⟨"arka-2013", "(46b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Mau=nya (adalah) [ _ tidur]"
    glossedTokens := [("Mau=nya", "want=DEF"), ("adalah", "be"), ("tidur", "sleep")]
    glossedWords := [⟨['M', 'a', 'u', '=', 'n', 'y', 'a'], ['w', 'a', 'n', 't', '=', 'D', 'E', 'F'], [⟨['M', 'a', 'u'], ['w', 'a', 'n', 't'], none⟩, ⟨['n', 'y', 'a'], ['D', 'E', 'F'], some '='⟩]⟩, ⟨['a', 'd', 'a', 'l', 'a', 'h'], ['b', 'e'], [⟨['a', 'd', 'a', 'l', 'a', 'h'], ['b', 'e'], none⟩]⟩, ⟨['t', 'i', 'd', 'u', 'r'], ['s', 'l', 'e', 'e', 'p'], [⟨['t', 'i', 'd', 'u', 'r'], ['s', 'l', 'e', 'e', 'p'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_47a : Datum :=
  { id := "arka2013_47a"
    source := ⟨"arka-2013", "(47a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Ali bukan guru itu."
    glossedTokens := [("Ali", "Ali"), ("bukan", "NEG"), ("guru", "teacher"), ("itu", "that")]
    glossedWords := [⟨['A', 'l', 'i'], ['A', 'l', 'i'], [⟨['A', 'l', 'i'], ['A', 'l', 'i'], none⟩]⟩, ⟨['b', 'u', 'k', 'a', 'n'], ['N', 'E', 'G'], [⟨['b', 'u', 'k', 'a', 'n'], ['N', 'E', 'G'], none⟩]⟩, ⟨['g', 'u', 'r', 'u'], ['t', 'e', 'a', 'c', 'h', 'e', 'r'], [⟨['g', 'u', 'r', 'u'], ['t', 'e', 'a', 'c', 'h', 'e', 'r'], none⟩]⟩, ⟨['i', 't', 'u'], ['t', 'h', 'a', 't'], [⟨['i', 't', 'u'], ['t', 'h', 'a', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Ali tidak guru itu.", .ungrammatical)]
    readings := []
    paperFeatures := [] }

def ex_47b : Datum :=
  { id := "arka2013_47b"
    source := ⟨"arka-2013", "(47b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Guru itu bukan Ali."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Guru itu tidak Ali.", .ungrammatical)]
    readings := []
    paperFeatures := [] }

def ex_48a : Datum :=
  { id := "arka2013_48a"
    source := ⟨"arka-2013", "(48a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "[_ tidur] bukan mau=nya"
    glossedTokens := [("tidur", "sleep"), ("bukan", "NEG"), ("mau=nya", "want=DEF")]
    glossedWords := [⟨['t', 'i', 'd', 'u', 'r'], ['s', 'l', 'e', 'e', 'p'], [⟨['t', 'i', 'd', 'u', 'r'], ['s', 'l', 'e', 'e', 'p'], none⟩]⟩, ⟨['b', 'u', 'k', 'a', 'n'], ['N', 'E', 'G'], [⟨['b', 'u', 'k', 'a', 'n'], ['N', 'E', 'G'], none⟩]⟩, ⟨['m', 'a', 'u', '=', 'n', 'y', 'a'], ['w', 'a', 'n', 't', '=', 'D', 'E', 'F'], [⟨['m', 'a', 'u'], ['w', 'a', 'n', 't'], none⟩, ⟨['n', 'y', 'a'], ['D', 'E', 'F'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("[_ tidur] tidak mau=nya", .ungrammatical)]
    readings := []
    paperFeatures := [] }

def ex_48b : Datum :=
  { id := "arka2013_48b"
    source := ⟨"arka-2013", "(48b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Mau=nya bukan tidur"
    glossedTokens := [("Mau=nya", "want=DEF"), ("bukan", "NEG"), ("tidur", "sleep")]
    glossedWords := [⟨['M', 'a', 'u', '=', 'n', 'y', 'a'], ['w', 'a', 'n', 't', '=', 'D', 'E', 'F'], [⟨['M', 'a', 'u'], ['w', 'a', 'n', 't'], none⟩, ⟨['n', 'y', 'a'], ['D', 'E', 'F'], some '='⟩]⟩, ⟨['b', 'u', 'k', 'a', 'n'], ['N', 'E', 'G'], [⟨['b', 'u', 'k', 'a', 'n'], ['N', 'E', 'G'], none⟩]⟩, ⟨['t', 'i', 'd', 'u', 'r'], ['s', 'l', 'e', 'e', 'p'], [⟨['t', 'i', 'd', 'u', 'r'], ['s', 'l', 'e', 'e', 'p'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Mau=nya tidak tidur", .acceptable)]
    readings := [("The/his/her/my wish was not to sleep.", .acceptable), ("It is the/her/his/your wish that (I/you/(s)he) would not sleep (but I did sleep).", .acceptable)]
    paperFeatures := [] }

def ex_52a : Datum :=
  { id := "arka2013_52a"
    source := ⟨"arka-2013", "(52a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "[Kamu pembohong] kata=nya"
    glossedTokens := [("Kamu", "2"), ("pembohong", "peN.lie"), ("kata=nya", "word=DEF")]
    glossedWords := [⟨['K', 'a', 'm', 'u'], ['2'], [⟨['K', 'a', 'm', 'u'], ['2'], none⟩]⟩, ⟨['p', 'e', 'm', 'b', 'o', 'h', 'o', 'n', 'g'], ['p', 'e', 'N', '.', 'l', 'i', 'e'], [⟨['p', 'e', 'm', 'b', 'o', 'h', 'o', 'n', 'g'], ['p', 'e', 'N', '.', 'l', 'i', 'e'], none⟩]⟩, ⟨['k', 'a', 't', 'a', '=', 'n', 'y', 'a'], ['w', 'o', 'r', 'd', '=', 'D', 'E', 'F'], [⟨['k', 'a', 't', 'a'], ['w', 'o', 'r', 'd'], none⟩, ⟨['n', 'y', 'a'], ['D', 'E', 'F'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("[Kamu pembohong] adalah katanya.", .ungrammatical)]
    readings := []
    paperFeatures := [] }

def ex_52b : Datum :=
  { id := "arka2013_52b"
    source := ⟨"arka-2013", "(52b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Katanya [kamu pembohong]"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("katanya adalah [kamu pembohong].", .ungrammatical)]
    readings := []
    paperFeatures := [] }

def ex_53 : Datum :=
  { id := "arka2013_53"
    source := ⟨"arka-2013", "(53)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "[Kamu] katanya [pembohong]"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex_3, ex_4a, ex_4b, ex_4c, ex_5a, ex_5b, ex_6a, ex_6b, ex_7, ex_8, ex_10, ex_11a, ex_11c, ex_12a, ex_12b, ex_13a, ex_14a, ex_15a, ex_15c, ex_18a, ex_18b, ex_34a, ex_34b, ex_34d, ex_35a, ex_35c, ex_36a, ex_36c, ex_37a, ex_37b, ex_38a, ex_38b, ex_39a, ex_39b, ex_40a, ex_41, ex_42a, ex_42b, ex_43a, ex_43b, ex_44a, ex_45a, ex_45b, ex_46a, ex_46b, ex_47a, ex_47b, ex_48a, ex_48b, ex_52a, ex_52b, ex_53]

end Arka2013.Examples
