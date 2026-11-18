module

public import Linglib.Data.Examples.Schema

/-!
# `Kramer2015` — typed example data

Auto-generated from `Linglib/Data/Examples/Kramer2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Kramer2015.Examples`.
-/

@[expose] public section

namespace Kramer2015.Examples

def ex_10_2 : Datum :=
  { id := "kramer2015_10_2"
    source := ⟨"kramer-2015", "ch. 10 (2)"⟩
    reportedIn := none
    method := some .description
    language := "soma1255"
    primaryText := "inammó"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "i[-fem]"), ("head", "u[+fem]"), ("gender", "feminine")] }

def ex_10_3a : Datum :=
  { id := "kramer2015_10_3a"
    source := ⟨"kramer-2015", "ch. 10 (3a)"⟩
    reportedIn := none
    method := some .description
    language := "sout1528"
    primaryText := "ova pametna devojka"
    glossedTokens := [("ova", "this.F.SG"), ("pametna", "smart.F.SG"), ("devojka", "girl")]
    glossedWords := [⟨['o', 'v', 'a'], ['t', 'h', 'i', 's', '.', 'F', '.', 'S', 'G'], [⟨['o', 'v', 'a'], ['t', 'h', 'i', 's', '.', 'F', '.', 'S', 'G'], none⟩]⟩, ⟨['p', 'a', 'm', 'e', 't', 'n', 'a'], ['s', 'm', 'a', 'r', 't', '.', 'F', '.', 'S', 'G'], [⟨['p', 'a', 'm', 'e', 't', 'n', 'a'], ['s', 'm', 'a', 'r', 't', '.', 'F', '.', 'S', 'G'], none⟩]⟩, ⟨['d', 'e', 'v', 'o', 'j', 'k', 'a'], ['g', 'i', 'r', 'l'], [⟨['d', 'e', 'v', 'o', 'j', 'k', 'a'], ['g', 'i', 'r', 'l'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "i[+fem]"), ("gender", "feminine")] }

def ex_10_3b : Datum :=
  { id := "kramer2015_10_3b"
    source := ⟨"kramer-2015", "ch. 10 (3b)"⟩
    reportedIn := none
    method := some .description
    language := "sout1528"
    primaryText := "ovaj pametni devojčurak"
    glossedTokens := [("ovaj", "this.M.SG"), ("pametni", "smart.M.SG"), ("devojčurak", "girl.DIM")]
    glossedWords := [⟨['o', 'v', 'a', 'j'], ['t', 'h', 'i', 's', '.', 'M', '.', 'S', 'G'], [⟨['o', 'v', 'a', 'j'], ['t', 'h', 'i', 's', '.', 'M', '.', 'S', 'G'], none⟩]⟩, ⟨['p', 'a', 'm', 'e', 't', 'n', 'i'], ['s', 'm', 'a', 'r', 't', '.', 'M', '.', 'S', 'G'], [⟨['p', 'a', 'm', 'e', 't', 'n', 'i'], ['s', 'm', 'a', 'r', 't', '.', 'M', '.', 'S', 'G'], none⟩]⟩, ⟨['d', 'e', 'v', 'o', 'j', 'č', 'u', 'r', 'a', 'k'], ['g', 'i', 'r', 'l', '.', 'D', 'I', 'M'], [⟨['d', 'e', 'v', 'o', 'j', 'č', 'u', 'r', 'a', 'k'], ['g', 'i', 'r', 'l', '.', 'D', 'I', 'M'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "i[+fem]"), ("head", "u[-fem]"), ("gender", "masculine")] }

def ex_10_5c : Datum :=
  { id := "kramer2015_10_5c"
    source := ⟨"kramer-2015", "ch. 10 (5c)"⟩
    reportedIn := none
    method := some .description
    language := "stan1295"
    primaryText := "die Lehrer-schaft"
    glossedTokens := [("die", "the.F.SG"), ("Lehrer-schaft", "faculty")]
    glossedWords := [⟨['d', 'i', 'e'], ['t', 'h', 'e', '.', 'F', '.', 'S', 'G'], [⟨['d', 'i', 'e'], ['t', 'h', 'e', '.', 'F', '.', 'S', 'G'], none⟩]⟩, ⟨['L', 'e', 'h', 'r', 'e', 'r', '-', 's', 'c', 'h', 'a', 'f', 't'], ['f', 'a', 'c', 'u', 'l', 't', 'y'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "u[-fem]"), ("head", "u[+fem]"), ("gender", "feminine")] }

def ex_10_8a : Datum :=
  { id := "kramer2015_10_8a"
    source := ⟨"kramer-2015", "ch. 10 (8a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "amha1245"
    primaryText := "bet-u"
    glossedTokens := [("bet-u", "house-DEF.M")]
    glossedWords := [⟨['b', 'e', 't', '-', 'u'], ['h', 'o', 'u', 's', 'e', '-', 'D', 'E', 'F', '.', 'M'], [⟨['b', 'e', 't'], ['h', 'o', 'u', 's', 'e'], none⟩, ⟨['u'], ['D', 'E', 'F', '.', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "plain"), ("gender", "masculine")] }

def ex_10_8b : Datum :=
  { id := "kramer2015_10_8b"
    source := ⟨"kramer-2015", "ch. 10 (8b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "amha1245"
    primaryText := "bet-wa t-amɨr-all-ätʃtʃ"
    glossedTokens := [("bet-wa", "house-DEF.F"), ("t-amɨr-all-ätʃtʃ", "3F.SG-be.cute-AUX-3F.SG")]
    glossedWords := [⟨['b', 'e', 't', '-', 'w', 'a'], ['h', 'o', 'u', 's', 'e', '-', 'D', 'E', 'F', '.', 'F'], [⟨['b', 'e', 't'], ['h', 'o', 'u', 's', 'e'], none⟩, ⟨['w', 'a'], ['D', 'E', 'F', '.', 'F'], some '-'⟩]⟩, ⟨['t', '-', 'a', 'm', 'ɨ', 'r', '-', 'a', 'l', 'l', '-', 'ä', 't', 'ʃ', 't', 'ʃ'], ['3', 'F', '.', 'S', 'G', '-', 'b', 'e', '.', 'c', 'u', 't', 'e', '-', 'A', 'U', 'X', '-', '3', 'F', '.', 'S', 'G'], [⟨['t'], ['3', 'F', '.', 'S', 'G'], none⟩, ⟨['a', 'm', 'ɨ', 'r'], ['b', 'e', '.', 'c', 'u', 't', 'e'], some '-'⟩, ⟨['a', 'l', 'l'], ['A', 'U', 'X'], some '-'⟩, ⟨['ä', 't', 'ʃ', 't', 'ʃ'], ['3', 'F', '.', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "plain"), ("head", "u[+fem]"), ("gender", "feminine")] }

def ex_10_10a : Datum :=
  { id := "kramer2015_10_10a"
    source := ⟨"kramer-2015", "ch. 10 (10a)"⟩
    reportedIn := none
    method := some .description
    language := "amha1245"
    primaryText := "yɨh bäre"
    glossedTokens := [("yɨh", "this.M"), ("bäre", "ox")]
    glossedWords := [⟨['y', 'ɨ', 'h'], ['t', 'h', 'i', 's', '.', 'M'], [⟨['y', 'ɨ', 'h'], ['t', 'h', 'i', 's', '.', 'M'], none⟩]⟩, ⟨['b', 'ä', 'r', 'e'], ['o', 'x'], [⟨['b', 'ä', 'r', 'e'], ['o', 'x'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "i[-fem]"), ("gender", "masculine")] }

def ex_10_10b : Datum :=
  { id := "kramer2015_10_10b"
    source := ⟨"kramer-2015", "ch. 10 (10b)"⟩
    reportedIn := none
    method := some .description
    language := "amha1245"
    primaryText := "yɨtʃtʃ bäre"
    glossedTokens := [("yɨtʃtʃ", "this.F"), ("bäre", "ox")]
    glossedWords := [⟨['y', 'ɨ', 't', 'ʃ', 't', 'ʃ'], ['t', 'h', 'i', 's', '.', 'F'], [⟨['y', 'ɨ', 't', 'ʃ', 't', 'ʃ'], ['t', 'h', 'i', 's', '.', 'F'], none⟩]⟩, ⟨['b', 'ä', 'r', 'e'], ['o', 'x'], [⟨['b', 'ä', 'r', 'e'], ['o', 'x'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "i[-fem]"), ("head", "u[+fem]"), ("gender", "feminine")] }

def ex_10_14a : Datum :=
  { id := "kramer2015_10_14a"
    source := ⟨"kramer-2015", "ch. 10 (14a)"⟩
    reportedIn := none
    method := some .description
    language := "stan1295"
    primaryText := "die Lehr-er-in"
    glossedTokens := [("die", "the.F.SG"), ("Lehr-er-in", "teach-er-FEM")]
    glossedWords := [⟨['d', 'i', 'e'], ['t', 'h', 'e', '.', 'F', '.', 'S', 'G'], [⟨['d', 'i', 'e'], ['t', 'h', 'e', '.', 'F', '.', 'S', 'G'], none⟩]⟩, ⟨['L', 'e', 'h', 'r', '-', 'e', 'r', '-', 'i', 'n'], ['t', 'e', 'a', 'c', 'h', '-', 'e', 'r', '-', 'F', 'E', 'M'], [⟨['L', 'e', 'h', 'r'], ['t', 'e', 'a', 'c', 'h'], none⟩, ⟨['e', 'r'], ['e', 'r'], some '-'⟩, ⟨['i', 'n'], ['F', 'E', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "u[-fem]"), ("head", "i[+fem]"), ("gender", "feminine")] }

def ex_10_21 : Datum :=
  { id := "kramer2015_10_21"
    source := ⟨"kramer-2015", "ch. 10 (21)"⟩
    reportedIn := none
    method := some .description
    language := "amha1245"
    primaryText := "dägg-ɨnnät hulgize t'ɨru näw"
    glossedTokens := [("dägg-ɨnnät", "kind-NMLZ"), ("hulgize", "always"), ("t'ɨru", "good"), ("näw", "be.3M.SG")]
    glossedWords := [⟨['d', 'ä', 'g', 'g', '-', 'ɨ', 'n', 'n', 'ä', 't'], ['k', 'i', 'n', 'd', '-', 'N', 'M', 'L', 'Z'], [⟨['d', 'ä', 'g', 'g'], ['k', 'i', 'n', 'd'], none⟩, ⟨['ɨ', 'n', 'n', 'ä', 't'], ['N', 'M', 'L', 'Z'], some '-'⟩]⟩, ⟨['h', 'u', 'l', 'g', 'i', 'z', 'e'], ['a', 'l', 'w', 'a', 'y', 's'], [⟨['h', 'u', 'l', 'g', 'i', 'z', 'e'], ['a', 'l', 'w', 'a', 'y', 's'], none⟩]⟩, ⟨['t', '\'', 'ɨ', 'r', 'u'], ['g', 'o', 'o', 'd'], [⟨['t', '\'', 'ɨ', 'r', 'u'], ['g', 'o', 'o', 'd'], none⟩]⟩, ⟨['n', 'ä', 'w'], ['b', 'e', '.', '3', 'M', '.', 'S', 'G'], [⟨['n', 'ä', 'w'], ['b', 'e', '.', '3', 'M', '.', 'S', 'G'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "a"), ("head", "plain"), ("gender", "masculine")] }

def ex_10_24 : Datum :=
  { id := "kramer2015_10_24"
    source := ⟨"kramer-2015", "ch. 10 (24)"⟩
    reportedIn := none
    method := some .elicitation
    language := "amha1245"
    primaryText := "ɨnnat-ɨnnät käbbad näw"
    glossedTokens := [("ɨnnat-ɨnnät", "mother-NMLZ"), ("käbbad", "difficult"), ("näw", "be.3M.SG")]
    glossedWords := [⟨['ɨ', 'n', 'n', 'a', 't', '-', 'ɨ', 'n', 'n', 'ä', 't'], ['m', 'o', 't', 'h', 'e', 'r', '-', 'N', 'M', 'L', 'Z'], [⟨['ɨ', 'n', 'n', 'a', 't'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['ɨ', 'n', 'n', 'ä', 't'], ['N', 'M', 'L', 'Z'], some '-'⟩]⟩, ⟨['k', 'ä', 'b', 'b', 'a', 'd'], ['d', 'i', 'f', 'f', 'i', 'c', 'u', 'l', 't'], [⟨['k', 'ä', 'b', 'b', 'a', 'd'], ['d', 'i', 'f', 'f', 'i', 'c', 'u', 'l', 't'], none⟩]⟩, ⟨['n', 'ä', 'w'], ['b', 'e', '.', '3', 'M', '.', 'S', 'G'], [⟨['n', 'ä', 'w'], ['b', 'e', '.', '3', 'M', '.', 'S', 'G'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "i[+fem]"), ("head", "plain"), ("gender", "masculine")] }

def ex_10_25 : Datum :=
  { id := "kramer2015_10_25"
    source := ⟨"kramer-2015", "ch. 10 (25)"⟩
    reportedIn := none
    method := some .elicitation
    language := "amha1245"
    primaryText := "mist-ɨnnät käbbad näw"
    glossedTokens := [("mist-ɨnnät", "wife-NMLZ"), ("käbbad", "difficult"), ("näw", "be.3M.SG")]
    glossedWords := [⟨['m', 'i', 's', 't', '-', 'ɨ', 'n', 'n', 'ä', 't'], ['w', 'i', 'f', 'e', '-', 'N', 'M', 'L', 'Z'], [⟨['m', 'i', 's', 't'], ['w', 'i', 'f', 'e'], none⟩, ⟨['ɨ', 'n', 'n', 'ä', 't'], ['N', 'M', 'L', 'Z'], some '-'⟩]⟩, ⟨['k', 'ä', 'b', 'b', 'a', 'd'], ['d', 'i', 'f', 'f', 'i', 'c', 'u', 'l', 't'], [⟨['k', 'ä', 'b', 'b', 'a', 'd'], ['d', 'i', 'f', 'f', 'i', 'c', 'u', 'l', 't'], none⟩]⟩, ⟨['n', 'ä', 'w'], ['b', 'e', '.', '3', 'M', '.', 'S', 'G'], [⟨['n', 'ä', 'w'], ['b', 'e', '.', '3', 'M', '.', 'S', 'G'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "i[+fem]"), ("head", "plain"), ("gender", "masculine")] }

def ex_10_26 : Datum :=
  { id := "kramer2015_10_26"
    source := ⟨"kramer-2015", "ch. 10 (26)"⟩
    reportedIn := none
    method := some .elicitation
    language := "amha1245"
    primaryText := "lam-ɨnnät käbbad näw"
    glossedTokens := [("lam-ɨnnät", "cow-NMLZ"), ("käbbad", "difficult"), ("näw", "be.3M.SG")]
    glossedWords := [⟨['l', 'a', 'm', '-', 'ɨ', 'n', 'n', 'ä', 't'], ['c', 'o', 'w', '-', 'N', 'M', 'L', 'Z'], [⟨['l', 'a', 'm'], ['c', 'o', 'w'], none⟩, ⟨['ɨ', 'n', 'n', 'ä', 't'], ['N', 'M', 'L', 'Z'], some '-'⟩]⟩, ⟨['k', 'ä', 'b', 'b', 'a', 'd'], ['d', 'i', 'f', 'f', 'i', 'c', 'u', 'l', 't'], [⟨['k', 'ä', 'b', 'b', 'a', 'd'], ['d', 'i', 'f', 'f', 'i', 'c', 'u', 'l', 't'], none⟩]⟩, ⟨['n', 'ä', 'w'], ['b', 'e', '.', '3', 'M', '.', 'S', 'G'], [⟨['n', 'ä', 'w'], ['b', 'e', '.', '3', 'M', '.', 'S', 'G'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "i[+fem]"), ("head", "plain"), ("gender", "masculine")] }

def ex_10_27a : Datum :=
  { id := "kramer2015_10_27a"
    source := ⟨"kramer-2015", "ch. 10 (27a)"⟩
    reportedIn := none
    method := some .description
    language := "soma1255"
    primaryText := "náág-ta"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "i[+fem]"), ("gender", "feminine")] }

def ex_10_27c : Datum :=
  { id := "kramer2015_10_27c"
    source := ⟨"kramer-2015", "ch. 10 (27c)"⟩
    reportedIn := none
    method := some .description
    language := "soma1255"
    primaryText := "naag-á-ha"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "i[+fem]"), ("head", "plain"), ("gender", "masculine")] }

def ex_10_29a : Datum :=
  { id := "kramer2015_10_29a"
    source := ⟨"kramer-2015", "ch. 10 (29a)"⟩
    reportedIn := none
    method := some .description
    language := "stan1295"
    primaryText := "die Karte"
    glossedTokens := [("die", "the.F.SG"), ("Karte", "card")]
    glossedWords := [⟨['d', 'i', 'e'], ['t', 'h', 'e', '.', 'F', '.', 'S', 'G'], [⟨['d', 'i', 'e'], ['t', 'h', 'e', '.', 'F', '.', 'S', 'G'], none⟩]⟩, ⟨['K', 'a', 'r', 't', 'e'], ['c', 'a', 'r', 'd'], [⟨['K', 'a', 'r', 't', 'e'], ['c', 'a', 'r', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "u[+fem]"), ("gender", "feminine")] }

def ex_10_29b : Datum :=
  { id := "kramer2015_10_29b"
    source := ⟨"kramer-2015", "ch. 10 (29b)"⟩
    reportedIn := none
    method := some .description
    language := "stan1295"
    primaryText := "die Stadt"
    glossedTokens := [("die", "the.F.SG"), ("Stadt", "town")]
    glossedWords := [⟨['d', 'i', 'e'], ['t', 'h', 'e', '.', 'F', '.', 'S', 'G'], [⟨['d', 'i', 'e'], ['t', 'h', 'e', '.', 'F', '.', 'S', 'G'], none⟩]⟩, ⟨['S', 't', 'a', 'd', 't'], ['t', 'o', 'w', 'n'], [⟨['S', 't', 'a', 'd', 't'], ['t', 'o', 'w', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "u[+fem]"), ("gender", "feminine")] }

def ex_10_29c : Datum :=
  { id := "kramer2015_10_29c"
    source := ⟨"kramer-2015", "ch. 10 (29c)"⟩
    reportedIn := none
    method := some .description
    language := "stan1295"
    primaryText := "die Flasche"
    glossedTokens := [("die", "the.F.SG"), ("Flasche", "bottle")]
    glossedWords := [⟨['d', 'i', 'e'], ['t', 'h', 'e', '.', 'F', '.', 'S', 'G'], [⟨['d', 'i', 'e'], ['t', 'h', 'e', '.', 'F', '.', 'S', 'G'], none⟩]⟩, ⟨['F', 'l', 'a', 's', 'c', 'h', 'e'], ['b', 'o', 't', 't', 'l', 'e'], [⟨['F', 'l', 'a', 's', 'c', 'h', 'e'], ['b', 'o', 't', 't', 'l', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "u[+fem]"), ("gender", "feminine")] }

def ex_10_29d : Datum :=
  { id := "kramer2015_10_29d"
    source := ⟨"kramer-2015", "ch. 10 (29d)"⟩
    reportedIn := none
    method := some .description
    language := "stan1295"
    primaryText := "das Kärt-chen"
    glossedTokens := [("das", "the.N.SG"), ("Kärt-chen", "card-DIM")]
    glossedWords := [⟨['d', 'a', 's'], ['t', 'h', 'e', '.', 'N', '.', 'S', 'G'], [⟨['d', 'a', 's'], ['t', 'h', 'e', '.', 'N', '.', 'S', 'G'], none⟩]⟩, ⟨['K', 'ä', 'r', 't', '-', 'c', 'h', 'e', 'n'], ['c', 'a', 'r', 'd', '-', 'D', 'I', 'M'], [⟨['K', 'ä', 'r', 't'], ['c', 'a', 'r', 'd'], none⟩, ⟨['c', 'h', 'e', 'n'], ['D', 'I', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "u[+fem]"), ("head", "plain"), ("gender", "neuter")] }

def ex_10_29e : Datum :=
  { id := "kramer2015_10_29e"
    source := ⟨"kramer-2015", "ch. 10 (29e)"⟩
    reportedIn := none
    method := some .description
    language := "stan1295"
    primaryText := "das Städt-chen"
    glossedTokens := [("das", "the.N.SG"), ("Städt-chen", "town-DIM")]
    glossedWords := [⟨['d', 'a', 's'], ['t', 'h', 'e', '.', 'N', '.', 'S', 'G'], [⟨['d', 'a', 's'], ['t', 'h', 'e', '.', 'N', '.', 'S', 'G'], none⟩]⟩, ⟨['S', 't', 'ä', 'd', 't', '-', 'c', 'h', 'e', 'n'], ['t', 'o', 'w', 'n', '-', 'D', 'I', 'M'], [⟨['S', 't', 'ä', 'd', 't'], ['t', 'o', 'w', 'n'], none⟩, ⟨['c', 'h', 'e', 'n'], ['D', 'I', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "u[+fem]"), ("head", "plain"), ("gender", "neuter")] }

def ex_10_29f : Datum :=
  { id := "kramer2015_10_29f"
    source := ⟨"kramer-2015", "ch. 10 (29f)"⟩
    reportedIn := none
    method := some .description
    language := "stan1295"
    primaryText := "das Fläsch-chen"
    glossedTokens := [("das", "the.N.SG"), ("Fläsch-chen", "bottle-DIM")]
    glossedWords := [⟨['d', 'a', 's'], ['t', 'h', 'e', '.', 'N', '.', 'S', 'G'], [⟨['d', 'a', 's'], ['t', 'h', 'e', '.', 'N', '.', 'S', 'G'], none⟩]⟩, ⟨['F', 'l', 'ä', 's', 'c', 'h', '-', 'c', 'h', 'e', 'n'], ['b', 'o', 't', 't', 'l', 'e', '-', 'D', 'I', 'M'], [⟨['F', 'l', 'ä', 's', 'c', 'h'], ['b', 'o', 't', 't', 'l', 'e'], none⟩, ⟨['c', 'h', 'e', 'n'], ['D', 'I', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "u[+fem]"), ("head", "plain"), ("gender", "neuter")] }

def ex_10_30b : Datum :=
  { id := "kramer2015_10_30b"
    source := ⟨"kramer-2015", "ch. 10 (30b)"⟩
    reportedIn := none
    method := some .description
    language := "sout1528"
    primaryText := "ovo pametno devojče"
    glossedTokens := [("ovo", "this.N.SG"), ("pametno", "smart.N.SG"), ("devojče", "girl.DIM")]
    glossedWords := [⟨['o', 'v', 'o'], ['t', 'h', 'i', 's', '.', 'N', '.', 'S', 'G'], [⟨['o', 'v', 'o'], ['t', 'h', 'i', 's', '.', 'N', '.', 'S', 'G'], none⟩]⟩, ⟨['p', 'a', 'm', 'e', 't', 'n', 'o'], ['s', 'm', 'a', 'r', 't', '.', 'N', '.', 'S', 'G'], [⟨['p', 'a', 'm', 'e', 't', 'n', 'o'], ['s', 'm', 'a', 'r', 't', '.', 'N', '.', 'S', 'G'], none⟩]⟩, ⟨['d', 'e', 'v', 'o', 'j', 'č', 'e'], ['g', 'i', 'r', 'l', '.', 'D', 'I', 'M'], [⟨['d', 'e', 'v', 'o', 'j', 'č', 'e'], ['g', 'i', 'r', 'l', '.', 'D', 'I', 'M'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "i[+fem]"), ("head", "plain"), ("gender", "neuter")] }

def ex_10_35a : Datum :=
  { id := "kramer2015_10_35a"
    source := ⟨"kramer-2015", "ch. 10 (35a)"⟩
    reportedIn := none
    method := some .description
    language := "stan1288"
    primaryText := "la madre"
    glossedTokens := [("la", "the.F.SG"), ("madre", "mother")]
    glossedWords := [⟨['l', 'a'], ['t', 'h', 'e', '.', 'F', '.', 'S', 'G'], [⟨['l', 'a'], ['t', 'h', 'e', '.', 'F', '.', 'S', 'G'], none⟩]⟩, ⟨['m', 'a', 'd', 'r', 'e'], ['m', 'o', 't', 'h', 'e', 'r'], [⟨['m', 'a', 'd', 'r', 'e'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "i[+fem]"), ("gender", "feminine")] }

def ex_10_35b : Datum :=
  { id := "kramer2015_10_35b"
    source := ⟨"kramer-2015", "ch. 10 (35b)"⟩
    reportedIn := none
    method := some .description
    language := "stan1288"
    primaryText := "la piedra"
    glossedTokens := [("la", "the.F.SG"), ("piedra", "stone")]
    glossedWords := [⟨['l', 'a'], ['t', 'h', 'e', '.', 'F', '.', 'S', 'G'], [⟨['l', 'a'], ['t', 'h', 'e', '.', 'F', '.', 'S', 'G'], none⟩]⟩, ⟨['p', 'i', 'e', 'd', 'r', 'a'], ['s', 't', 'o', 'n', 'e'], [⟨['p', 'i', 'e', 'd', 'r', 'a'], ['s', 't', 'o', 'n', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "u[+fem]"), ("gender", "feminine")] }

def ex_10_35c : Datum :=
  { id := "kramer2015_10_35c"
    source := ⟨"kramer-2015", "ch. 10 (35c)"⟩
    reportedIn := none
    method := some .description
    language := "stan1288"
    primaryText := "el padre"
    glossedTokens := [("el", "the.M.SG"), ("padre", "father")]
    glossedWords := [⟨['e', 'l'], ['t', 'h', 'e', '.', 'M', '.', 'S', 'G'], [⟨['e', 'l'], ['t', 'h', 'e', '.', 'M', '.', 'S', 'G'], none⟩]⟩, ⟨['p', 'a', 'd', 'r', 'e'], ['f', 'a', 't', 'h', 'e', 'r'], [⟨['p', 'a', 'd', 'r', 'e'], ['f', 'a', 't', 'h', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "i[-fem]"), ("gender", "masculine")] }

def ex_10_35d : Datum :=
  { id := "kramer2015_10_35d"
    source := ⟨"kramer-2015", "ch. 10 (35d)"⟩
    reportedIn := none
    method := some .description
    language := "stan1288"
    primaryText := "el armario"
    glossedTokens := [("el", "the.M.SG"), ("armario", "wardrobe")]
    glossedWords := [⟨['e', 'l'], ['t', 'h', 'e', '.', 'M', '.', 'S', 'G'], [⟨['e', 'l'], ['t', 'h', 'e', '.', 'M', '.', 'S', 'G'], none⟩]⟩, ⟨['a', 'r', 'm', 'a', 'r', 'i', 'o'], ['w', 'a', 'r', 'd', 'r', 'o', 'b', 'e'], [⟨['a', 'r', 'm', 'a', 'r', 'i', 'o'], ['w', 'a', 'r', 'd', 'r', 'o', 'b', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "plain"), ("gender", "masculine")] }

def ex_10_35e : Datum :=
  { id := "kramer2015_10_35e"
    source := ⟨"kramer-2015", "ch. 10 (35e)"⟩
    reportedIn := none
    method := some .description
    language := "stan1288"
    primaryText := "la madre-cita"
    glossedTokens := [("la", "the.F.SG"), ("madre-cita", "mother-DIM")]
    glossedWords := [⟨['l', 'a'], ['t', 'h', 'e', '.', 'F', '.', 'S', 'G'], [⟨['l', 'a'], ['t', 'h', 'e', '.', 'F', '.', 'S', 'G'], none⟩]⟩, ⟨['m', 'a', 'd', 'r', 'e', '-', 'c', 'i', 't', 'a'], ['m', 'o', 't', 'h', 'e', 'r', '-', 'D', 'I', 'M'], [⟨['m', 'a', 'd', 'r', 'e'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['c', 'i', 't', 'a'], ['D', 'I', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "i[+fem]"), ("head", "dim"), ("gender", "feminine")] }

def ex_10_35f : Datum :=
  { id := "kramer2015_10_35f"
    source := ⟨"kramer-2015", "ch. 10 (35f)"⟩
    reportedIn := none
    method := some .description
    language := "stan1288"
    primaryText := "la piedre-cita"
    glossedTokens := [("la", "the.F.SG"), ("piedre-cita", "stone-DIM")]
    glossedWords := [⟨['l', 'a'], ['t', 'h', 'e', '.', 'F', '.', 'S', 'G'], [⟨['l', 'a'], ['t', 'h', 'e', '.', 'F', '.', 'S', 'G'], none⟩]⟩, ⟨['p', 'i', 'e', 'd', 'r', 'e', '-', 'c', 'i', 't', 'a'], ['s', 't', 'o', 'n', 'e', '-', 'D', 'I', 'M'], [⟨['p', 'i', 'e', 'd', 'r', 'e'], ['s', 't', 'o', 'n', 'e'], none⟩, ⟨['c', 'i', 't', 'a'], ['D', 'I', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "u[+fem]"), ("head", "dim"), ("gender", "feminine")] }

def ex_10_35g : Datum :=
  { id := "kramer2015_10_35g"
    source := ⟨"kramer-2015", "ch. 10 (35g)"⟩
    reportedIn := none
    method := some .description
    language := "stan1288"
    primaryText := "el padre-cito"
    glossedTokens := [("el", "the.M.SG"), ("padre-cito", "father-DIM")]
    glossedWords := [⟨['e', 'l'], ['t', 'h', 'e', '.', 'M', '.', 'S', 'G'], [⟨['e', 'l'], ['t', 'h', 'e', '.', 'M', '.', 'S', 'G'], none⟩]⟩, ⟨['p', 'a', 'd', 'r', 'e', '-', 'c', 'i', 't', 'o'], ['f', 'a', 't', 'h', 'e', 'r', '-', 'D', 'I', 'M'], [⟨['p', 'a', 'd', 'r', 'e'], ['f', 'a', 't', 'h', 'e', 'r'], none⟩, ⟨['c', 'i', 't', 'o'], ['D', 'I', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "i[-fem]"), ("head", "dim"), ("gender", "masculine")] }

def ex_10_35h : Datum :=
  { id := "kramer2015_10_35h"
    source := ⟨"kramer-2015", "ch. 10 (35h)"⟩
    reportedIn := none
    method := some .description
    language := "stan1288"
    primaryText := "el armar-ito"
    glossedTokens := [("el", "the.M.SG"), ("armar-ito", "wardrobe-DIM")]
    glossedWords := [⟨['e', 'l'], ['t', 'h', 'e', '.', 'M', '.', 'S', 'G'], [⟨['e', 'l'], ['t', 'h', 'e', '.', 'M', '.', 'S', 'G'], none⟩]⟩, ⟨['a', 'r', 'm', 'a', 'r', '-', 'i', 't', 'o'], ['w', 'a', 'r', 'd', 'r', 'o', 'b', 'e', '-', 'D', 'I', 'M'], [⟨['a', 'r', 'm', 'a', 'r'], ['w', 'a', 'r', 'd', 'r', 'o', 'b', 'e'], none⟩, ⟨['i', 't', 'o'], ['D', 'I', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "plain"), ("head", "dim"), ("gender", "masculine")] }

def all : List Datum := [ex_10_2, ex_10_3a, ex_10_3b, ex_10_5c, ex_10_8a, ex_10_8b, ex_10_10a, ex_10_10b, ex_10_14a, ex_10_21, ex_10_24, ex_10_25, ex_10_26, ex_10_27a, ex_10_27c, ex_10_29a, ex_10_29b, ex_10_29c, ex_10_29d, ex_10_29e, ex_10_29f, ex_10_30b, ex_10_35a, ex_10_35b, ex_10_35c, ex_10_35d, ex_10_35e, ex_10_35f, ex_10_35g, ex_10_35h]

end Kramer2015.Examples
