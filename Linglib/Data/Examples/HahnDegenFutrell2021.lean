module

public import Linglib.Data.Examples.Schema

/-!
# `HahnDegenFutrell2021` — typed example data

Auto-generated from `Linglib/Data/Examples/HahnDegenFutrell2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HahnDegenFutrell2021.Examples`.
-/

@[expose] public section

namespace HahnDegenFutrell2021.Examples

def ex2a : Datum :=
  { id := "hahndegenfutrell2021_ex2a"
    source := ⟨"hahn-degen-futrell-2021", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lucy ate the broccoli with a fork."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "heavyNPShift")] }

def ex2b : Datum :=
  { id := "hahndegenfutrell2021_ex2b"
    source := ⟨"hahn-degen-futrell-2021", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lucy ate with a fork the broccoli."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "heavyNPShift")] }

def ex2c : Datum :=
  { id := "hahndegenfutrell2021_ex2c"
    source := ⟨"hahn-degen-futrell-2021", "(2c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lucy ate the extremely delicious, bright green broccoli with a fork."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "heavyNPShift")] }

def ex2d : Datum :=
  { id := "hahndegenfutrell2021_ex2d"
    source := ⟨"hahn-degen-futrell-2021", "(2d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lucy ate with a fork the extremely delicious, bright green broccoli."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "heavyNPShift")] }

def si1 : Datum :=
  { id := "hahndegenfutrell2021_si1"
    source := ⟨"hahn-degen-futrell-2021", "SI, Japanese, ordering table row 1"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "mi-naka-tta"
    glossedTokens := [("mi", "see"), ("naka", "NEG"), ("tta", "PST")]
    glossedWords := [⟨[['m', 'i']], [['s', 'e', 'e']]⟩, ⟨[['n', 'a', 'k', 'a']], [['N', 'E', 'G']]⟩, ⟨[['t', 't', 'a']], [['P', 'S', 'T']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "SI Japanese"), ("phenomenon", "morphemeOrder")] }

def si2 : Datum :=
  { id := "hahndegenfutrell2021_si2"
    source := ⟨"hahn-degen-futrell-2021", "SI, Japanese, ordering table row 2"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "mi-taku-nai"
    glossedTokens := [("mi", "see"), ("taku", "DESID"), ("nai", "NEG")]
    glossedWords := [⟨[['m', 'i']], [['s', 'e', 'e']]⟩, ⟨[['t', 'a', 'k', 'u']], [['D', 'E', 'S', 'I', 'D']]⟩, ⟨[['n', 'a', 'i']], [['N', 'E', 'G']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "SI Japanese"), ("phenomenon", "morphemeOrder")] }

def si3 : Datum :=
  { id := "hahndegenfutrell2021_si3"
    source := ⟨"hahn-degen-futrell-2021", "SI, Japanese, ordering table row 3"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "mi-taku-naka-tta"
    glossedTokens := [("mi", "see"), ("taku", "DESID"), ("naka", "NEG"), ("tta", "PST")]
    glossedWords := [⟨[['m', 'i']], [['s', 'e', 'e']]⟩, ⟨[['t', 'a', 'k', 'u']], [['D', 'E', 'S', 'I', 'D']]⟩, ⟨[['n', 'a', 'k', 'a']], [['N', 'E', 'G']]⟩, ⟨[['t', 't', 'a']], [['P', 'S', 'T']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "SI Japanese"), ("phenomenon", "morphemeOrder")] }

def si4 : Datum :=
  { id := "hahndegenfutrell2021_si4"
    source := ⟨"hahn-degen-futrell-2021", "SI, Japanese, ordering table row 4"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "tat-ase-rare-ta"
    glossedTokens := [("tat", "stand"), ("ase", "CAUS"), ("rare", "PASS"), ("ta", "PST")]
    glossedWords := [⟨[['t', 'a', 't']], [['s', 't', 'a', 'n', 'd']]⟩, ⟨[['a', 's', 'e']], [['C', 'A', 'U', 'S']]⟩, ⟨[['r', 'a', 'r', 'e']], [['P', 'A', 'S', 'S']]⟩, ⟨[['t', 'a']], [['P', 'S', 'T']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "SI Japanese"), ("phenomenon", "morphemeOrder")] }

def si5 : Datum :=
  { id := "hahndegenfutrell2021_si5"
    source := ⟨"hahn-degen-futrell-2021", "SI, Japanese, ordering table row 5"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "waraw-are-ta"
    glossedTokens := [("waraw", "laugh"), ("are", "PASS"), ("ta", "PST")]
    glossedWords := [⟨[['w', 'a', 'r', 'a', 'w']], [['l', 'a', 'u', 'g', 'h']]⟩, ⟨[['a', 'r', 'e']], [['P', 'A', 'S', 'S']]⟩, ⟨[['t', 'a']], [['P', 'S', 'T']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "SI Japanese"), ("phenomenon", "morphemeOrder")] }

def si6 : Datum :=
  { id := "hahndegenfutrell2021_si6"
    source := ⟨"hahn-degen-futrell-2021", "SI, Japanese, ordering table row 6"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "mi-rare-mase-n"
    glossedTokens := [("mi", "see"), ("rare", "PASS"), ("mase", "POL"), ("n", "NEG")]
    glossedWords := [⟨[['m', 'i']], [['s', 'e', 'e']]⟩, ⟨[['r', 'a', 'r', 'e']], [['P', 'A', 'S', 'S']]⟩, ⟨[['m', 'a', 's', 'e']], [['P', 'O', 'L']]⟩, ⟨[['n']], [['N', 'E', 'G']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "SI Japanese"), ("phenomenon", "morphemeOrder")] }

def si7 : Datum :=
  { id := "hahndegenfutrell2021_si7"
    source := ⟨"hahn-degen-futrell-2021", "SI, Japanese, ordering table row 7"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "mi-rare-mash-yoo"
    glossedTokens := [("mi", "see"), ("rare", "PASS"), ("mash", "POL"), ("yoo", "HORT")]
    glossedWords := [⟨[['m', 'i']], [['s', 'e', 'e']]⟩, ⟨[['r', 'a', 'r', 'e']], [['P', 'A', 'S', 'S']]⟩, ⟨[['m', 'a', 's', 'h']], [['P', 'O', 'L']]⟩, ⟨[['y', 'o', 'o']], [['H', 'O', 'R', 'T']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "SI Japanese"), ("phenomenon", "morphemeOrder")] }

def si8 : Datum :=
  { id := "hahndegenfutrell2021_si8"
    source := ⟨"hahn-degen-futrell-2021", "SI, Japanese, ordering table row 8"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "de-naka-roo"
    glossedTokens := [("de", "go.out"), ("naka", "NEG"), ("roo", "HORT")]
    glossedWords := [⟨[['d', 'e']], [['g', 'o', '.', 'o', 'u', 't']]⟩, ⟨[['n', 'a', 'k', 'a']], [['N', 'E', 'G']]⟩, ⟨[['r', 'o', 'o']], [['H', 'O', 'R', 'T']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "SI Japanese"), ("phenomenon", "morphemeOrder")] }

def si9 : Datum :=
  { id := "hahndegenfutrell2021_si9"
    source := ⟨"hahn-degen-futrell-2021", "SI, Japanese, ordering table row 9"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "mi-e-mase-n"
    glossedTokens := [("mi", "see"), ("e", "POT"), ("mase", "POL"), ("n", "NEG")]
    glossedWords := [⟨[['m', 'i']], [['s', 'e', 'e']]⟩, ⟨[['e']], [['P', 'O', 'T']]⟩, ⟨[['m', 'a', 's', 'e']], [['P', 'O', 'L']]⟩, ⟨[['n']], [['N', 'E', 'G']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "SI Japanese"), ("phenomenon", "morphemeOrder")] }

def so1 : Datum :=
  { id := "hahndegenfutrell2021_so1"
    source := ⟨"demuth-1992", "(13)"⟩
    reportedIn := some ⟨"hahn-degen-futrell-2021", "(2a)"⟩
    language := "sout2807"
    primaryText := "oa-di-rek-a"
    glossedTokens := [("oa", "SM"), ("di", "OBJ"), ("rek", "buy"), ("a", "M")]
    glossedWords := [⟨[['o', 'a']], [['S', 'M']]⟩, ⟨[['d', 'i']], [['O', 'B', 'J']]⟩, ⟨[['r', 'e', 'k']], [['b', 'u', 'y']]⟩, ⟨[['a']], [['M']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.2"), ("phenomenon", "morphemeOrder")] }

def so2 : Datum :=
  { id := "hahndegenfutrell2021_so2"
    source := ⟨"demuth-1992", "(41)"⟩
    reportedIn := some ⟨"hahn-degen-futrell-2021", "(2b)"⟩
    language := "sout2807"
    primaryText := "o-pheh-el-a"
    glossedTokens := [("o", "SM"), ("pheh", "cook"), ("el", "APL"), ("a", "M")]
    glossedWords := [⟨[['o']], [['S', 'M']]⟩, ⟨[['p', 'h', 'e', 'h']], [['c', 'o', 'o', 'k']]⟩, ⟨[['e', 'l']], [['A', 'P', 'L']]⟩, ⟨[['a']], [['M']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.2"), ("phenomenon", "morphemeOrder")] }

def so3 : Datum :=
  { id := "hahndegenfutrell2021_so3"
    source := ⟨"demuth-1992", "(15)"⟩
    reportedIn := some ⟨"hahn-degen-futrell-2021", "SI, Sesotho, examples table"⟩
    language := "sout2807"
    primaryText := "o-pheh-il-e"
    glossedTokens := [("o", "SM"), ("pheh", "cook"), ("il", "PERF"), ("e", "M")]
    glossedWords := [⟨[['o']], [['S', 'M']]⟩, ⟨[['p', 'h', 'e', 'h']], [['c', 'o', 'o', 'k']]⟩, ⟨[['i', 'l']], [['P', 'E', 'R', 'F']]⟩, ⟨[['e']], [['M']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "SI Sesotho"), ("phenomenon", "morphemeOrder")] }

def so4 : Datum :=
  { id := "hahndegenfutrell2021_so4"
    source := ⟨"demuth-1992", "(26c)"⟩
    reportedIn := some ⟨"hahn-degen-futrell-2021", "SI, Sesotho, examples table"⟩
    language := "sout2807"
    primaryText := "ke-e-f-uw-e"
    glossedTokens := [("ke", "SM"), ("e", "OBJ"), ("f", "give"), ("uw", "PASS"), ("e", "M")]
    glossedWords := [⟨[['k', 'e']], [['S', 'M']]⟩, ⟨[['e']], [['O', 'B', 'J']]⟩, ⟨[['f']], [['g', 'i', 'v', 'e']]⟩, ⟨[['u', 'w']], [['P', 'A', 'S', 'S']]⟩, ⟨[['e']], [['M']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "SI Sesotho"), ("phenomenon", "morphemeOrder")] }

def so5 : Datum :=
  { id := "hahndegenfutrell2021_so5"
    source := ⟨"demuth-1992", "(43)"⟩
    reportedIn := some ⟨"hahn-degen-futrell-2021", "SI, Sesotho, examples table"⟩
    language := "sout2807"
    primaryText := "o-pheh-el-w-a"
    glossedTokens := [("o", "SM"), ("pheh", "cook"), ("el", "APL"), ("w", "PASS"), ("a", "M")]
    glossedWords := [⟨[['o']], [['S', 'M']]⟩, ⟨[['p', 'h', 'e', 'h']], [['c', 'o', 'o', 'k']]⟩, ⟨[['e', 'l']], [['A', 'P', 'L']]⟩, ⟨[['w']], [['P', 'A', 'S', 'S']]⟩, ⟨[['a']], [['M']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "SI Sesotho"), ("phenomenon", "morphemeOrder")] }

def so6 : Datum :=
  { id := "hahndegenfutrell2021_so6"
    source := ⟨"demuth-1992", "(44)"⟩
    reportedIn := none
    language := "sout2807"
    primaryText := "o-pheh-ets-w-e"
    glossedTokens := [("o", "SM"), ("pheh", "cook"), ("ets", "APL:PERF"), ("w", "PASS"), ("e", "M")]
    glossedWords := [⟨[['o']], [['S', 'M']]⟩, ⟨[['p', 'h', 'e', 'h']], [['c', 'o', 'o', 'k']]⟩, ⟨[['e', 't', 's']], [['A', 'P', 'L', ':', 'P', 'E', 'R', 'F']]⟩, ⟨[['w']], [['P', 'A', 'S', 'S']]⟩, ⟨[['e']], [['M']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "SI Sesotho"), ("phenomenon", "morphemeOrder")] }

def so7 : Datum :=
  { id := "hahndegenfutrell2021_so7"
    source := ⟨"demuth-1992", "(45)"⟩
    reportedIn := none
    language := "sout2807"
    primaryText := "o-hod-is-ets-a"
    glossedTokens := [("o", "SM"), ("hod", "grow"), ("is", "CAUS"), ("ets", "APL"), ("a", "M")]
    glossedWords := [⟨[['o']], [['S', 'M']]⟩, ⟨[['h', 'o', 'd']], [['g', 'r', 'o', 'w']]⟩, ⟨[['i', 's']], [['C', 'A', 'U', 'S']]⟩, ⟨[['e', 't', 's']], [['A', 'P', 'L']]⟩, ⟨[['a']], [['M']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "SI Sesotho"), ("phenomenon", "morphemeOrder")] }

def so8 : Datum :=
  { id := "hahndegenfutrell2021_so8"
    source := ⟨"demuth-1992", "(29)"⟩
    reportedIn := none
    language := "sout2807"
    primaryText := "pheh-il-e-ng"
    glossedTokens := [("pheh", "cook"), ("il", "PERF"), ("e", "M"), ("ng", "RL")]
    glossedWords := [⟨[['p', 'h', 'e', 'h']], [['c', 'o', 'o', 'k']]⟩, ⟨[['i', 'l']], [['P', 'E', 'R', 'F']]⟩, ⟨[['e']], [['M']]⟩, ⟨[['n', 'g']], [['R', 'L']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "SI Sesotho"), ("phenomenon", "morphemeOrder")] }

def so9 : Datum :=
  { id := "hahndegenfutrell2021_so9"
    source := ⟨"hahn-degen-futrell-2021", "SI, Sesotho, completive footnote"⟩
    reportedIn := none
    method := some .corpus
    language := "sout2807"
    primaryText := "u-neh-el-ets-w-a-ng"
    glossedTokens := [("u", "OBJ"), ("neh", "give"), ("el", "APL"), ("ets", "CL"), ("w", "PASS"), ("a", "M"), ("ng", "WH")]
    glossedWords := [⟨[['u']], [['O', 'B', 'J']]⟩, ⟨[['n', 'e', 'h']], [['g', 'i', 'v', 'e']]⟩, ⟨[['e', 'l']], [['A', 'P', 'L']]⟩, ⟨[['e', 't', 's']], [['C', 'L']]⟩, ⟨[['w']], [['P', 'A', 'S', 'S']]⟩, ⟨[['a']], [['M']]⟩, ⟨[['n', 'g']], [['W', 'H']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "SI Sesotho"), ("phenomenon", "morphemeOrder")] }

def so10 : Datum :=
  { id := "hahndegenfutrell2021_so10"
    source := ⟨"hahn-degen-futrell-2021", "SI, Sesotho, stacking footnote"⟩
    reportedIn := none
    method := some .corpus
    language := "sout2807"
    primaryText := "ba-arol-el-an-a"
    glossedTokens := [("ba", "SM"), ("arol", "divide"), ("el", "APL"), ("an", "RC"), ("a", "M")]
    glossedWords := [⟨[['b', 'a']], [['S', 'M']]⟩, ⟨[['a', 'r', 'o', 'l']], [['d', 'i', 'v', 'i', 'd', 'e']]⟩, ⟨[['e', 'l']], [['A', 'P', 'L']]⟩, ⟨[['a', 'n']], [['R', 'C']]⟩, ⟨[['a']], [['M']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "SI Sesotho"), ("phenomenon", "morphemeOrder")] }

def all : List Datum := [ex2a, ex2b, ex2c, ex2d, si1, si2, si3, si4, si5, si6, si7, si8, si9, so1, so2, so3, so4, so5, so6, so7, so8, so9, so10]

end HahnDegenFutrell2021.Examples
