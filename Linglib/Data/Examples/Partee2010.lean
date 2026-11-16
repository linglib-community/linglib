module

public import Linglib.Data.Examples.Schema

/-!
# `Partee2010` — typed example data

Auto-generated from `Linglib/Data/Examples/Partee2010.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Partee2010.Examples`.
-/

@[expose] public section

namespace Partee2010.Examples

def ex_10a : Datum :=
  { id := "partee2010_10a"
    source := ⟨"partee-2010", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A fake gun is not a gun."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_10b : Datum :=
  { id := "partee2010_10b"
    source := ⟨"partee-2010", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Is that gun real or fake?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_11a : Datum :=
  { id := "partee2010_11a"
    source := ⟨"nowak-2000", ""⟩
    reportedIn := some ⟨"partee-2010", "(11a)"⟩
    language := "poli1260"
    primaryText := "Kelnerki rozmawiały o przystojnym chłopcu."
    glossedTokens := [("Kelnerki", "waitresses"), ("rozmawiały", "talked"), ("o", "about"), ("przystojnym", "handsome-LOC"), ("chłopcu", "boy-LOC")]
    glossedWords := [⟨['K', 'e', 'l', 'n', 'e', 'r', 'k', 'i'], ['w', 'a', 'i', 't', 'r', 'e', 's', 's', 'e', 's'], [⟨['K', 'e', 'l', 'n', 'e', 'r', 'k', 'i'], ['w', 'a', 'i', 't', 'r', 'e', 's', 's', 'e', 's'], none⟩]⟩, ⟨['r', 'o', 'z', 'm', 'a', 'w', 'i', 'a', 'ł', 'y'], ['t', 'a', 'l', 'k', 'e', 'd'], [⟨['r', 'o', 'z', 'm', 'a', 'w', 'i', 'a', 'ł', 'y'], ['t', 'a', 'l', 'k', 'e', 'd'], none⟩]⟩, ⟨['o'], ['a', 'b', 'o', 'u', 't'], [⟨['o'], ['a', 'b', 'o', 'u', 't'], none⟩]⟩, ⟨['p', 'r', 'z', 'y', 's', 't', 'o', 'j', 'n', 'y', 'm'], ['h', 'a', 'n', 'd', 's', 'o', 'm', 'e', '-', 'L', 'O', 'C'], []⟩, ⟨['c', 'h', 'ł', 'o', 'p', 'c', 'u'], ['b', 'o', 'y', '-', 'L', 'O', 'C'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "handsome"), ("construction", "unsplit")] }

def ex_11b : Datum :=
  { id := "partee2010_11b"
    source := ⟨"nowak-2000", ""⟩
    reportedIn := some ⟨"partee-2010", "(11b)"⟩
    language := "poli1260"
    primaryText := "O przystojnym kelnerki rozmawiały chłopcu."
    glossedTokens := [("O", "about"), ("przystojnym", "handsome-LOC"), ("kelnerki", "waitresses"), ("rozmawiały", "talked"), ("chłopcu", "boy-LOC")]
    glossedWords := [⟨['O'], ['a', 'b', 'o', 'u', 't'], [⟨['O'], ['a', 'b', 'o', 'u', 't'], none⟩]⟩, ⟨['p', 'r', 'z', 'y', 's', 't', 'o', 'j', 'n', 'y', 'm'], ['h', 'a', 'n', 'd', 's', 'o', 'm', 'e', '-', 'L', 'O', 'C'], []⟩, ⟨['k', 'e', 'l', 'n', 'e', 'r', 'k', 'i'], ['w', 'a', 'i', 't', 'r', 'e', 's', 's', 'e', 's'], [⟨['k', 'e', 'l', 'n', 'e', 'r', 'k', 'i'], ['w', 'a', 'i', 't', 'r', 'e', 's', 's', 'e', 's'], none⟩]⟩, ⟨['r', 'o', 'z', 'm', 'a', 'w', 'i', 'a', 'ł', 'y'], ['t', 'a', 'l', 'k', 'e', 'd'], [⟨['r', 'o', 'z', 'm', 'a', 'w', 'i', 'a', 'ł', 'y'], ['t', 'a', 'l', 'k', 'e', 'd'], none⟩]⟩, ⟨['c', 'h', 'ł', 'o', 'p', 'c', 'u'], ['b', 'o', 'y', '-', 'L', 'O', 'C'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "handsome"), ("construction", "NP-split")] }

def ex_13b : Datum :=
  { id := "partee2010_13b"
    source := ⟨"nowak-2000", ""⟩
    reportedIn := some ⟨"partee-2010", "(13b)"⟩
    language := "poli1260"
    primaryText := "Do doliny weszliśmy rozległej."
    glossedTokens := [("Do", "to"), ("doliny", "valley-GEN"), ("weszliśmy", "enter-PST.1ST.PL"), ("rozległej", "large-GEN")]
    glossedWords := [⟨['D', 'o'], ['t', 'o'], [⟨['D', 'o'], ['t', 'o'], none⟩]⟩, ⟨['d', 'o', 'l', 'i', 'n', 'y'], ['v', 'a', 'l', 'l', 'e', 'y', '-', 'G', 'E', 'N'], []⟩, ⟨['w', 'e', 's', 'z', 'l', 'i', 'ś', 'm', 'y'], ['e', 'n', 't', 'e', 'r', '-', 'P', 'S', 'T', '.', '1', 'S', 'T', '.', 'P', 'L'], []⟩, ⟨['r', 'o', 'z', 'l', 'e', 'g', 'ł', 'e', 'j'], ['l', 'a', 'r', 'g', 'e', '-', 'G', 'E', 'N'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "large"), ("construction", "NP-split")] }

def ex_14b : Datum :=
  { id := "partee2010_14b"
    source := ⟨"nowak-2000", ""⟩
    reportedIn := some ⟨"partee-2010", "(14b)"⟩
    language := "poli1260"
    primaryText := "Z prezydentem rozmawiała byłym."
    glossedTokens := [("Z", "with"), ("prezydentem", "president-INSTR"), ("rozmawiała", "talk-PST.3RD.F.SG"), ("byłym", "former-INSTR")]
    glossedWords := [⟨['Z'], ['w', 'i', 't', 'h'], [⟨['Z'], ['w', 'i', 't', 'h'], none⟩]⟩, ⟨['p', 'r', 'e', 'z', 'y', 'd', 'e', 'n', 't', 'e', 'm'], ['p', 'r', 'e', 's', 'i', 'd', 'e', 'n', 't', '-', 'I', 'N', 'S', 'T', 'R'], []⟩, ⟨['r', 'o', 'z', 'm', 'a', 'w', 'i', 'a', 'ł', 'a'], ['t', 'a', 'l', 'k', '-', 'P', 'S', 'T', '.', '3', 'R', 'D', '.', 'F', '.', 'S', 'G'], []⟩, ⟨['b', 'y', 'ł', 'y', 'm'], ['f', 'o', 'r', 'm', 'e', 'r', '-', 'I', 'N', 'S', 'T', 'R'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "former"), ("class", "privative"), ("construction", "NP-split")] }

def ex_15b : Datum :=
  { id := "partee2010_15b"
    source := ⟨"nowak-2000", ""⟩
    reportedIn := some ⟨"partee-2010", "(15b)"⟩
    language := "poli1260"
    primaryText := "biedny"
    glossedTokens := [("biedny", "poor")]
    glossedWords := [⟨['b', 'i', 'e', 'd', 'n', 'y'], ['p', 'o', 'o', 'r'], [⟨['b', 'i', 'e', 'd', 'n', 'y'], ['p', 'o', 'o', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "poor"), ("sense", "not rich"), ("construction", "NP-split")] }

def ex_16a : Datum :=
  { id := "partee2010_16a"
    source := ⟨"nowak-2000", ""⟩
    reportedIn := some ⟨"partee-2010", "(16a)"⟩
    language := "poli1260"
    primaryText := "biedny"
    glossedTokens := [("biedny", "poor")]
    glossedWords := [⟨['b', 'i', 'e', 'd', 'n', 'y'], ['p', 'o', 'o', 'r'], [⟨['b', 'i', 'e', 'd', 'n', 'y'], ['p', 'o', 'o', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "poor"), ("sense", "pitiful"), ("construction", "NP-split")] }

def ex_17b : Datum :=
  { id := "partee2010_17b"
    source := ⟨"partee-2010", "(17b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't care whether that fur is fake or real."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_19b : Datum :=
  { id := "partee2010_19b"
    source := ⟨"kamp-partee-1995", "(29c)"⟩
    reportedIn := some ⟨"partee-2010", "(19b)"⟩
    language := "stan1293"
    primaryText := "midget giant"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("a giant, but an exceptionally small one", .acceptable)]
    paperFeatures := [] }

def ex_21b : Datum :=
  { id := "partee2010_21b"
    source := ⟨"kamp-partee-1995", "(31)"⟩
    reportedIn := some ⟨"partee-2010", "(21b)"⟩
    language := "stan1293"
    primaryText := "Knives are sharp."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_22b : Datum :=
  { id := "partee2010_22b"
    source := ⟨"partee-2010", "(22b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How many poets are buried in Amherst?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_12a : Datum :=
  { id := "partee2010_12a"
    source := ⟨"nowak-2000", ""⟩
    reportedIn := some ⟨"partee-2010", "(12a)"⟩
    language := "poli1260"
    primaryText := "Włamano się do nowego sklepu."
    glossedTokens := [("Włamano", "broke-in-NEUT.SG"), ("się", "REFL"), ("do", "to"), ("nowego", "new-GEN"), ("sklepu", "store-GEN")]
    glossedWords := [⟨['W', 'ł', 'a', 'm', 'a', 'n', 'o'], ['b', 'r', 'o', 'k', 'e', '-', 'i', 'n', '-', 'N', 'E', 'U', 'T', '.', 'S', 'G'], []⟩, ⟨['s', 'i', 'ę'], ['R', 'E', 'F', 'L'], [⟨['s', 'i', 'ę'], ['R', 'E', 'F', 'L'], none⟩]⟩, ⟨['d', 'o'], ['t', 'o'], [⟨['d', 'o'], ['t', 'o'], none⟩]⟩, ⟨['n', 'o', 'w', 'e', 'g', 'o'], ['n', 'e', 'w', '-', 'G', 'E', 'N'], []⟩, ⟨['s', 'k', 'l', 'e', 'p', 'u'], ['s', 't', 'o', 'r', 'e', '-', 'G', 'E', 'N'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "new"), ("construction", "unsplit")] }

def ex_12b : Datum :=
  { id := "partee2010_12b"
    source := ⟨"nowak-2000", ""⟩
    reportedIn := some ⟨"partee-2010", "(12b)"⟩
    language := "poli1260"
    primaryText := "Do sklepu włamano się nowego."
    glossedTokens := [("Do", "to"), ("sklepu", "store-GEN"), ("włamano", "broke-in-NEUT.SG"), ("się", "REFL"), ("nowego", "new-GEN")]
    glossedWords := [⟨['D', 'o'], ['t', 'o'], [⟨['D', 'o'], ['t', 'o'], none⟩]⟩, ⟨['s', 'k', 'l', 'e', 'p', 'u'], ['s', 't', 'o', 'r', 'e', '-', 'G', 'E', 'N'], []⟩, ⟨['w', 'ł', 'a', 'm', 'a', 'n', 'o'], ['b', 'r', 'o', 'k', 'e', '-', 'i', 'n', '-', 'N', 'E', 'U', 'T', '.', 'S', 'G'], []⟩, ⟨['s', 'i', 'ę'], ['R', 'E', 'F', 'L'], [⟨['s', 'i', 'ę'], ['R', 'E', 'F', 'L'], none⟩]⟩, ⟨['n', 'o', 'w', 'e', 'g', 'o'], ['n', 'e', 'w', '-', 'G', 'E', 'N'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "new"), ("construction", "NP-split")] }

def ex_13a : Datum :=
  { id := "partee2010_13a"
    source := ⟨"nowak-2000", ""⟩
    reportedIn := some ⟨"partee-2010", "(13a)"⟩
    language := "poli1260"
    primaryText := "Do rozległej weszliśmy doliny."
    glossedTokens := [("Do", "to"), ("rozległej", "large-GEN"), ("weszliśmy", "enter-PST.1ST.PL"), ("doliny", "valley-GEN")]
    glossedWords := [⟨['D', 'o'], ['t', 'o'], [⟨['D', 'o'], ['t', 'o'], none⟩]⟩, ⟨['r', 'o', 'z', 'l', 'e', 'g', 'ł', 'e', 'j'], ['l', 'a', 'r', 'g', 'e', '-', 'G', 'E', 'N'], []⟩, ⟨['w', 'e', 's', 'z', 'l', 'i', 'ś', 'm', 'y'], ['e', 'n', 't', 'e', 'r', '-', 'P', 'S', 'T', '.', '1', 'S', 'T', '.', 'P', 'L'], []⟩, ⟨['d', 'o', 'l', 'i', 'n', 'y'], ['v', 'a', 'l', 'l', 'e', 'y', '-', 'G', 'E', 'N'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "large"), ("construction", "NP-split")] }

def ex_14a : Datum :=
  { id := "partee2010_14a"
    source := ⟨"nowak-2000", ""⟩
    reportedIn := some ⟨"partee-2010", "(14a)"⟩
    language := "poli1260"
    primaryText := "Z byłym rozmawiała prezydentem."
    glossedTokens := [("Z", "with"), ("byłym", "former-INSTR"), ("rozmawiała", "talk-PST.3RD.F.SG"), ("prezydentem", "president-INSTR")]
    glossedWords := [⟨['Z'], ['w', 'i', 't', 'h'], [⟨['Z'], ['w', 'i', 't', 'h'], none⟩]⟩, ⟨['b', 'y', 'ł', 'y', 'm'], ['f', 'o', 'r', 'm', 'e', 'r', '-', 'I', 'N', 'S', 'T', 'R'], []⟩, ⟨['r', 'o', 'z', 'm', 'a', 'w', 'i', 'a', 'ł', 'a'], ['t', 'a', 'l', 'k', '-', 'P', 'S', 'T', '.', '3', 'R', 'D', '.', 'F', '.', 'S', 'G'], []⟩, ⟨['p', 'r', 'e', 'z', 'y', 'd', 'e', 'n', 't', 'e', 'm'], ['p', 'r', 'e', 's', 'i', 'd', 'e', 'n', 't', '-', 'I', 'N', 'S', 'T', 'R'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "former"), ("class", "privative"), ("construction", "NP-split")] }

def ex_17a : Datum :=
  { id := "partee2010_17a"
    source := ⟨"partee-2010", "(17a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't care whether that fur is fake fur or real fur."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_19a : Datum :=
  { id := "partee2010_19a"
    source := ⟨"kamp-partee-1995", "(29b)"⟩
    reportedIn := some ⟨"partee-2010", "(19a)"⟩
    language := "stan1293"
    primaryText := "giant midget"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("a midget, but an exceptionally large one", .acceptable)]
    paperFeatures := [] }

def ex_21a : Datum :=
  { id := "partee2010_21a"
    source := ⟨"kamp-partee-1995", "(30)"⟩
    reportedIn := some ⟨"partee-2010", "(21a)"⟩
    language := "stan1293"
    primaryText := "This is a sharp knife."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_22a : Datum :=
  { id := "partee2010_22a"
    source := ⟨"partee-2010", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How many poets are there in Amherst?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_15c_generous : Datum :=
  { id := "partee2010_15c_generous"
    source := ⟨"nowak-2000", ""⟩
    reportedIn := some ⟨"partee-2010", "(15c)"⟩
    language := "poli1260"
    primaryText := "generous"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "generous"), ("class", "intersective"), ("construction", "NP-split")] }

def ex_15c_pretty : Datum :=
  { id := "partee2010_15c_pretty"
    source := ⟨"nowak-2000", ""⟩
    reportedIn := some ⟨"partee-2010", "(15c)"⟩
    language := "poli1260"
    primaryText := "pretty"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "pretty"), ("class", "intersective"), ("construction", "NP-split")] }

def ex_15c_healthy : Datum :=
  { id := "partee2010_15c_healthy"
    source := ⟨"nowak-2000", ""⟩
    reportedIn := some ⟨"partee-2010", "(15c)"⟩
    language := "poli1260"
    primaryText := "healthy"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "healthy"), ("class", "intersective"), ("construction", "NP-split")] }

def ex_15c_Chinese : Datum :=
  { id := "partee2010_15c_Chinese"
    source := ⟨"nowak-2000", ""⟩
    reportedIn := some ⟨"partee-2010", "(15c)"⟩
    language := "poli1260"
    primaryText := "Chinese"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "Chinese"), ("class", "intersective"), ("construction", "NP-split")] }

def ex_15c_talkative : Datum :=
  { id := "partee2010_15c_talkative"
    source := ⟨"nowak-2000", ""⟩
    reportedIn := some ⟨"partee-2010", "(15c)"⟩
    language := "poli1260"
    primaryText := "talkative"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "talkative"), ("class", "intersective"), ("construction", "NP-split")] }

def ex_15d_skillful : Datum :=
  { id := "partee2010_15d_skillful"
    source := ⟨"nowak-2000", ""⟩
    reportedIn := some ⟨"partee-2010", "(15d)"⟩
    language := "poli1260"
    primaryText := "skillful"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "skillful"), ("class", "subsective"), ("construction", "NP-split")] }

def ex_15d_recent : Datum :=
  { id := "partee2010_15d_recent"
    source := ⟨"nowak-2000", ""⟩
    reportedIn := some ⟨"partee-2010", "(15d)"⟩
    language := "poli1260"
    primaryText := "recent"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "recent"), ("class", "subsective"), ("construction", "NP-split")] }

def ex_15d_good : Datum :=
  { id := "partee2010_15d_good"
    source := ⟨"nowak-2000", ""⟩
    reportedIn := some ⟨"partee-2010", "(15d)"⟩
    language := "poli1260"
    primaryText := "good"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "good"), ("class", "subsective"), ("construction", "NP-split")] }

def ex_15d_typical : Datum :=
  { id := "partee2010_15d_typical"
    source := ⟨"nowak-2000", ""⟩
    reportedIn := some ⟨"partee-2010", "(15d)"⟩
    language := "poli1260"
    primaryText := "typical"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "typical"), ("class", "subsective"), ("construction", "NP-split")] }

def ex_15e_counterfeit : Datum :=
  { id := "partee2010_15e_counterfeit"
    source := ⟨"nowak-2000", ""⟩
    reportedIn := some ⟨"partee-2010", "(15e)"⟩
    language := "poli1260"
    primaryText := "counterfeit"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "counterfeit"), ("class", "privative"), ("construction", "NP-split")] }

def ex_15e_past : Datum :=
  { id := "partee2010_15e_past"
    source := ⟨"nowak-2000", ""⟩
    reportedIn := some ⟨"partee-2010", "(15e)"⟩
    language := "poli1260"
    primaryText := "past"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "past"), ("class", "privative"), ("construction", "NP-split")] }

def ex_15e_spurious : Datum :=
  { id := "partee2010_15e_spurious"
    source := ⟨"nowak-2000", ""⟩
    reportedIn := some ⟨"partee-2010", "(15e)"⟩
    language := "poli1260"
    primaryText := "spurious"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "spurious"), ("class", "privative"), ("construction", "NP-split")] }

def ex_15e_imaginary : Datum :=
  { id := "partee2010_15e_imaginary"
    source := ⟨"nowak-2000", ""⟩
    reportedIn := some ⟨"partee-2010", "(15e)"⟩
    language := "poli1260"
    primaryText := "imaginary"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "imaginary"), ("class", "privative"), ("construction", "NP-split")] }

def ex_15e_fictitious : Datum :=
  { id := "partee2010_15e_fictitious"
    source := ⟨"nowak-2000", ""⟩
    reportedIn := some ⟨"partee-2010", "(15e)"⟩
    language := "poli1260"
    primaryText := "fictitious"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "fictitious"), ("class", "privative"), ("construction", "NP-split")] }

def ex_16b_alleged : Datum :=
  { id := "partee2010_16b_alleged"
    source := ⟨"nowak-2000", ""⟩
    reportedIn := some ⟨"partee-2010", "(16b)"⟩
    language := "poli1260"
    primaryText := "alleged"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "alleged"), ("class", "modal"), ("construction", "NP-split")] }

def ex_16b_potential : Datum :=
  { id := "partee2010_16b_potential"
    source := ⟨"nowak-2000", ""⟩
    reportedIn := some ⟨"partee-2010", "(16b)"⟩
    language := "poli1260"
    primaryText := "potential"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "potential"), ("class", "modal"), ("construction", "NP-split")] }

def ex_16b_predicted : Datum :=
  { id := "partee2010_16b_predicted"
    source := ⟨"nowak-2000", ""⟩
    reportedIn := some ⟨"partee-2010", "(16b)"⟩
    language := "poli1260"
    primaryText := "predicted"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "predicted"), ("class", "modal"), ("construction", "NP-split")] }

def ex_16b_disputed : Datum :=
  { id := "partee2010_16b_disputed"
    source := ⟨"nowak-2000", ""⟩
    reportedIn := some ⟨"partee-2010", "(16b)"⟩
    language := "poli1260"
    primaryText := "disputed"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "disputed"), ("class", "modal"), ("construction", "NP-split")] }

def all : List Datum := [ex_10a, ex_10b, ex_11a, ex_11b, ex_13b, ex_14b, ex_15b, ex_16a, ex_17b, ex_19b, ex_21b, ex_22b, ex_12a, ex_12b, ex_13a, ex_14a, ex_17a, ex_19a, ex_21a, ex_22a, ex_15c_generous, ex_15c_pretty, ex_15c_healthy, ex_15c_Chinese, ex_15c_talkative, ex_15d_skillful, ex_15d_recent, ex_15d_good, ex_15d_typical, ex_15e_counterfeit, ex_15e_past, ex_15e_spurious, ex_15e_imaginary, ex_15e_fictitious, ex_16b_alleged, ex_16b_potential, ex_16b_predicted, ex_16b_disputed]

end Partee2010.Examples
