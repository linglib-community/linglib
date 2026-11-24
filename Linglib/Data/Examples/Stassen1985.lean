module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Stassen1985` — typed example data

Auto-generated from `Linglib/Data/Examples/Stassen1985.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Stassen1985.Examples`.
-/

@[expose] public section

namespace Stassen1985.Examples

def ex_6_15 : Datum :=
  { id := "stassen1985_6_15"
    source := ⟨"stassen-1985", "ch. 6 (15)"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "Sen gul-den güzel-sin"
    glossedTokens := [("Sen", "you"), ("gul-den", "rose-from"), ("güzel-sin", "beautiful-be-2SG")]
    glossedWords := [⟨['S', 'e', 'n'], ['y', 'o', 'u'], [⟨['S', 'e', 'n'], ['y', 'o', 'u'], none⟩]⟩, ⟨['g', 'u', 'l', '-', 'd', 'e', 'n'], ['r', 'o', 's', 'e', '-', 'f', 'r', 'o', 'm'], [⟨['g', 'u', 'l'], ['r', 'o', 's', 'e'], none⟩, ⟨['d', 'e', 'n'], ['f', 'r', 'o', 'm'], some '-'⟩]⟩, ⟨['g', 'ü', 'z', 'e', 'l', '-', 's', 'i', 'n'], ['b', 'e', 'a', 'u', 't', 'i', 'f', 'u', 'l', '-', 'b', 'e', '-', '2', 'S', 'G'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "standard", some "dan"⟩]
    paperFeatures := [("comparativeClass", "separative")] }

def ex_6_24a : Datum :=
  { id := "stassen1985_6_24a"
    source := ⟨"stassen-1985", "ch. 6 (24a)"⟩
    reportedIn := none
    method := some .description
    language := "hind1269"
    primaryText := "Ap us-se bare haim"
    glossedTokens := [("Ap", "you"), ("us-se", "him-from"), ("bare", "big"), ("haim", "be-PRES.2SG")]
    glossedWords := [⟨['A', 'p'], ['y', 'o', 'u'], [⟨['A', 'p'], ['y', 'o', 'u'], none⟩]⟩, ⟨['u', 's', '-', 's', 'e'], ['h', 'i', 'm', '-', 'f', 'r', 'o', 'm'], [⟨['u', 's'], ['h', 'i', 'm'], none⟩, ⟨['s', 'e'], ['f', 'r', 'o', 'm'], some '-'⟩]⟩, ⟨['b', 'a', 'r', 'e'], ['b', 'i', 'g'], [⟨['b', 'a', 'r', 'e'], ['b', 'i', 'g'], none⟩]⟩, ⟨['h', 'a', 'i', 'm'], ['b', 'e', '-', 'P', 'R', 'E', 'S', '.', '2', 'S', 'G'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "standard", some "se"⟩]
    paperFeatures := [("comparativeClass", "separative")] }

def ex_6_26a : Datum :=
  { id := "stassen1985_6_26a"
    source := ⟨"stassen-1985", "ch. 6 (26a)"⟩
    reportedIn := none
    method := some .description
    language := "nucl1643"
    primaryText := "Nihon-go wa doits-go yori muzukashi"
    glossedTokens := [("Nihon-go", "Japanese"), ("wa", "TOP"), ("doits-go", "German"), ("yori", "from"), ("muzukashi", "difficult")]
    glossedWords := [⟨['N', 'i', 'h', 'o', 'n', '-', 'g', 'o'], ['J', 'a', 'p', 'a', 'n', 'e', 's', 'e'], []⟩, ⟨['w', 'a'], ['T', 'O', 'P'], [⟨['w', 'a'], ['T', 'O', 'P'], none⟩]⟩, ⟨['d', 'o', 'i', 't', 's', '-', 'g', 'o'], ['G', 'e', 'r', 'm', 'a', 'n'], []⟩, ⟨['y', 'o', 'r', 'i'], ['f', 'r', 'o', 'm'], [⟨['y', 'o', 'r', 'i'], ['f', 'r', 'o', 'm'], none⟩]⟩, ⟨['m', 'u', 'z', 'u', 'k', 'a', 's', 'h', 'i'], ['d', 'i', 'f', 'f', 'i', 'c', 'u', 'l', 't'], [⟨['m', 'u', 'z', 'u', 'k', 'a', 's', 'h', 'i'], ['d', 'i', 'f', 'f', 'i', 'c', 'u', 'l', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "standard", some "yori"⟩]
    paperFeatures := [("comparativeClass", "separative")] }

def ex_6_32 : Datum :=
  { id := "stassen1985_6_32"
    source := ⟨"stassen-1985", "ch. 6 (32)"⟩
    reportedIn := none
    method := some .description
    language := "kore1280"
    primaryText := "Na-eso to kheda"
    glossedTokens := [("Na-eso", "I-from"), ("to", "he"), ("kheda", "big-PRES")]
    glossedWords := [⟨['N', 'a', '-', 'e', 's', 'o'], ['I', '-', 'f', 'r', 'o', 'm'], [⟨['N', 'a'], ['I'], none⟩, ⟨['e', 's', 'o'], ['f', 'r', 'o', 'm'], some '-'⟩]⟩, ⟨['t', 'o'], ['h', 'e'], [⟨['t', 'o'], ['h', 'e'], none⟩]⟩, ⟨['k', 'h', 'e', 'd', 'a'], ['b', 'i', 'g', '-', 'P', 'R', 'E', 'S'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "standard", none⟩]
    paperFeatures := [("comparativeClass", "separative")] }

def ex_6_42 : Datum :=
  { id := "stassen1985_6_42"
    source := ⟨"stassen-1985", "ch. 6 (42)"⟩
    reportedIn := none
    method := some .description
    language := "stan1318"
    primaryText := "Laysat al-nisa 'adcafa min al-rijali"
    glossedTokens := [("Laysat", "not"), ("al-nisa", "the-women"), ("'adcafa", "weaker"), ("min", "from"), ("al-rijali", "the-men")]
    glossedWords := [⟨['L', 'a', 'y', 's', 'a', 't'], ['n', 'o', 't'], [⟨['L', 'a', 'y', 's', 'a', 't'], ['n', 'o', 't'], none⟩]⟩, ⟨['a', 'l', '-', 'n', 'i', 's', 'a'], ['t', 'h', 'e', '-', 'w', 'o', 'm', 'e', 'n'], [⟨['a', 'l'], ['t', 'h', 'e'], none⟩, ⟨['n', 'i', 's', 'a'], ['w', 'o', 'm', 'e', 'n'], some '-'⟩]⟩, ⟨['\'', 'a', 'd', 'c', 'a', 'f', 'a'], ['w', 'e', 'a', 'k', 'e', 'r'], [⟨['\'', 'a', 'd', 'c', 'a', 'f', 'a'], ['w', 'e', 'a', 'k', 'e', 'r'], none⟩]⟩, ⟨['m', 'i', 'n'], ['f', 'r', 'o', 'm'], [⟨['m', 'i', 'n'], ['f', 'r', 'o', 'm'], none⟩]⟩, ⟨['a', 'l', '-', 'r', 'i', 'j', 'a', 'l', 'i'], ['t', 'h', 'e', '-', 'm', 'e', 'n'], [⟨['a', 'l'], ['t', 'h', 'e'], none⟩, ⟨['r', 'i', 'j', 'a', 'l', 'i'], ['m', 'e', 'n'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "standard", some "min"⟩]
    paperFeatures := [("comparativeClass", "separative")] }

def ex_8_12b : Datum :=
  { id := "stassen1985_8_12b"
    source := ⟨"stassen-1985", "ch. 8 (12b)"⟩
    reportedIn := none
    method := some .description
    language := "mand1415"
    primaryText := "Wo na p'i ma pi ni na p'i ma kwai"
    glossedTokens := [("Wo", "I"), ("na", "this"), ("p'i", "CLASS"), ("ma", "horse"), ("pi", "exceed"), ("ni", "you"), ("na", "this"), ("p'i", "CLASS"), ("ma", "horse"), ("kwai", "is-big")]
    glossedWords := [⟨['W', 'o'], ['I'], [⟨['W', 'o'], ['I'], none⟩]⟩, ⟨['n', 'a'], ['t', 'h', 'i', 's'], [⟨['n', 'a'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['p', '\'', 'i'], ['C', 'L', 'A', 'S', 'S'], [⟨['p', '\'', 'i'], ['C', 'L', 'A', 'S', 'S'], none⟩]⟩, ⟨['m', 'a'], ['h', 'o', 'r', 's', 'e'], [⟨['m', 'a'], ['h', 'o', 'r', 's', 'e'], none⟩]⟩, ⟨['p', 'i'], ['e', 'x', 'c', 'e', 'e', 'd'], [⟨['p', 'i'], ['e', 'x', 'c', 'e', 'e', 'd'], none⟩]⟩, ⟨['n', 'i'], ['y', 'o', 'u'], [⟨['n', 'i'], ['y', 'o', 'u'], none⟩]⟩, ⟨['n', 'a'], ['t', 'h', 'i', 's'], [⟨['n', 'a'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['p', '\'', 'i'], ['C', 'L', 'A', 'S', 'S'], [⟨['p', '\'', 'i'], ['C', 'L', 'A', 'S', 'S'], none⟩]⟩, ⟨['m', 'a'], ['h', 'o', 'r', 's', 'e'], [⟨['m', 'a'], ['h', 'o', 'r', 's', 'e'], none⟩]⟩, ⟨['k', 'w', 'a', 'i'], ['i', 's', '-', 'b', 'i', 'g'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "standard", some "bi"⟩]
    paperFeatures := [("comparativeClass", "exceed")] }

def ex_8_16b : Datum :=
  { id := "stassen1985_8_16b"
    source := ⟨"stassen-1985", "ch. 8 (16b)"⟩
    reportedIn := none
    method := some .description
    language := "yoru1245"
    primaryText := "Ile mi kere ju tiwon"
    glossedTokens := [("Ile", "house"), ("mi", "my"), ("kere", "small"), ("ju", "exceed"), ("tiwon", "theirs")]
    glossedWords := [⟨['I', 'l', 'e'], ['h', 'o', 'u', 's', 'e'], [⟨['I', 'l', 'e'], ['h', 'o', 'u', 's', 'e'], none⟩]⟩, ⟨['m', 'i'], ['m', 'y'], [⟨['m', 'i'], ['m', 'y'], none⟩]⟩, ⟨['k', 'e', 'r', 'e'], ['s', 'm', 'a', 'l', 'l'], [⟨['k', 'e', 'r', 'e'], ['s', 'm', 'a', 'l', 'l'], none⟩]⟩, ⟨['j', 'u'], ['e', 'x', 'c', 'e', 'e', 'd'], [⟨['j', 'u'], ['e', 'x', 'c', 'e', 'e', 'd'], none⟩]⟩, ⟨['t', 'i', 'w', 'o', 'n'], ['t', 'h', 'e', 'i', 'r', 's'], [⟨['t', 'i', 'w', 'o', 'n'], ['t', 'h', 'e', 'i', 'r', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "standard", some "ju"⟩]
    paperFeatures := [("comparativeClass", "exceed")] }

def ex_8_24 : Datum :=
  { id := "stassen1985_8_24"
    source := ⟨"stassen-1985", "ch. 8 (24)"⟩
    reportedIn := none
    method := some .description
    language := "swah1253"
    primaryText := "Mti huu ni mrefu ku-shinda ule"
    glossedTokens := [("Mti", "tree"), ("huu", "this"), ("ni", "is"), ("mrefu", "big"), ("ku-shinda", "INF-exceed"), ("ule", "that")]
    glossedWords := [⟨['M', 't', 'i'], ['t', 'r', 'e', 'e'], [⟨['M', 't', 'i'], ['t', 'r', 'e', 'e'], none⟩]⟩, ⟨['h', 'u', 'u'], ['t', 'h', 'i', 's'], [⟨['h', 'u', 'u'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['n', 'i'], ['i', 's'], [⟨['n', 'i'], ['i', 's'], none⟩]⟩, ⟨['m', 'r', 'e', 'f', 'u'], ['b', 'i', 'g'], [⟨['m', 'r', 'e', 'f', 'u'], ['b', 'i', 'g'], none⟩]⟩, ⟨['k', 'u', '-', 's', 'h', 'i', 'n', 'd', 'a'], ['I', 'N', 'F', '-', 'e', 'x', 'c', 'e', 'e', 'd'], [⟨['k', 'u'], ['I', 'N', 'F'], none⟩, ⟨['s', 'h', 'i', 'n', 'd', 'a'], ['e', 'x', 'c', 'e', 'e', 'd'], some '-'⟩]⟩, ⟨['u', 'l', 'e'], ['t', 'h', 'a', 't'], [⟨['u', 'l', 'e'], ['t', 'h', 'a', 't'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "standard", some "kushinda"⟩]
    paperFeatures := [("comparativeClass", "exceed")] }

def ex_8_26 : Datum :=
  { id := "stassen1985_8_26"
    source := ⟨"stassen-1985", "ch. 8 (26)"⟩
    reportedIn := none
    method := some .description
    language := "swah1253"
    primaryText := "Nyumba nyake nzuri sana ku-liko nyumba yangu"
    glossedTokens := [("Nyumba", "house"), ("nyake", "his"), ("nzuri", "it-is"), ("sana", "good"), ("ku-liko", "PRT"), ("nyumba", "house"), ("yangu", "my")]
    glossedWords := [⟨['N', 'y', 'u', 'm', 'b', 'a'], ['h', 'o', 'u', 's', 'e'], [⟨['N', 'y', 'u', 'm', 'b', 'a'], ['h', 'o', 'u', 's', 'e'], none⟩]⟩, ⟨['n', 'y', 'a', 'k', 'e'], ['h', 'i', 's'], [⟨['n', 'y', 'a', 'k', 'e'], ['h', 'i', 's'], none⟩]⟩, ⟨['n', 'z', 'u', 'r', 'i'], ['i', 't', '-', 'i', 's'], []⟩, ⟨['s', 'a', 'n', 'a'], ['g', 'o', 'o', 'd'], [⟨['s', 'a', 'n', 'a'], ['g', 'o', 'o', 'd'], none⟩]⟩, ⟨['k', 'u', '-', 'l', 'i', 'k', 'o'], ['P', 'R', 'T'], []⟩, ⟨['n', 'y', 'u', 'm', 'b', 'a'], ['h', 'o', 'u', 's', 'e'], [⟨['n', 'y', 'u', 'm', 'b', 'a'], ['h', 'o', 'u', 's', 'e'], none⟩]⟩, ⟨['y', 'a', 'n', 'g', 'u'], ['m', 'y'], [⟨['y', 'a', 'n', 'g', 'u'], ['m', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "standard", some "kuliko"⟩]
    paperFeatures := [] }

def ex_9_35 : Datum :=
  { id := "stassen1985_9_35"
    source := ⟨"stassen-1985", "ch. 9 (35)"⟩
    reportedIn := none
    method := some .description
    language := "russ1263"
    primaryText := "On umnjee cem ja"
    glossedTokens := [("On", "he"), ("umnjee", "clever-er"), ("cem", "PRT"), ("ja", "I")]
    glossedWords := [⟨['O', 'n'], ['h', 'e'], [⟨['O', 'n'], ['h', 'e'], none⟩]⟩, ⟨['u', 'm', 'n', 'j', 'e', 'e'], ['c', 'l', 'e', 'v', 'e', 'r', '-', 'e', 'r'], []⟩, ⟨['c', 'e', 'm'], ['P', 'R', 'T'], [⟨['c', 'e', 'm'], ['P', 'R', 'T'], none⟩]⟩, ⟨['j', 'a'], ['I'], [⟨['j', 'a'], ['I'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "standard", some "chem"⟩]
    paperFeatures := [("comparativeClass", "particle")] }

def ex_9_36 : Datum :=
  { id := "stassen1985_9_36"
    source := ⟨"stassen-1985", "ch. 9 (36)"⟩
    reportedIn := none
    method := some .description
    language := "stan1290"
    primaryText := "Angélique est plus charmante que Marie"
    glossedTokens := [("Angélique", "A."), ("est", "is"), ("plus", "more"), ("charmante", "charming-FEM"), ("que", "PRT"), ("Marie", "M.")]
    glossedWords := [⟨['A', 'n', 'g', 'é', 'l', 'i', 'q', 'u', 'e'], ['A', '.'], [⟨['A', 'n', 'g', 'é', 'l', 'i', 'q', 'u', 'e'], ['A', '.'], none⟩]⟩, ⟨['e', 's', 't'], ['i', 's'], [⟨['e', 's', 't'], ['i', 's'], none⟩]⟩, ⟨['p', 'l', 'u', 's'], ['m', 'o', 'r', 'e'], [⟨['p', 'l', 'u', 's'], ['m', 'o', 'r', 'e'], none⟩]⟩, ⟨['c', 'h', 'a', 'r', 'm', 'a', 'n', 't', 'e'], ['c', 'h', 'a', 'r', 'm', 'i', 'n', 'g', '-', 'F', 'E', 'M'], []⟩, ⟨['q', 'u', 'e'], ['P', 'R', 'T'], [⟨['q', 'u', 'e'], ['P', 'R', 'T'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'e'], ['M', '.'], [⟨['M', 'a', 'r', 'i', 'e'], ['M', '.'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "standard", some "que"⟩]
    paperFeatures := [("comparativeClass", "particle")] }

def ex_9_37 : Datum :=
  { id := "stassen1985_9_37"
    source := ⟨"stassen-1985", "ch. 9 (37)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Hän on pite-mpi kuin sina"
    glossedTokens := [("Hän", "he"), ("on", "is"), ("pite-mpi", "big-PRT"), ("kuin", "PRT"), ("sina", "you")]
    glossedWords := [⟨['H', 'ä', 'n'], ['h', 'e'], [⟨['H', 'ä', 'n'], ['h', 'e'], none⟩]⟩, ⟨['o', 'n'], ['i', 's'], [⟨['o', 'n'], ['i', 's'], none⟩]⟩, ⟨['p', 'i', 't', 'e', '-', 'm', 'p', 'i'], ['b', 'i', 'g', '-', 'P', 'R', 'T'], [⟨['p', 'i', 't', 'e'], ['b', 'i', 'g'], none⟩, ⟨['m', 'p', 'i'], ['P', 'R', 'T'], some '-'⟩]⟩, ⟨['k', 'u', 'i', 'n'], ['P', 'R', 'T'], [⟨['k', 'u', 'i', 'n'], ['P', 'R', 'T'], none⟩]⟩, ⟨['s', 'i', 'n', 'a'], ['y', 'o', 'u'], [⟨['s', 'i', 'n', 'a'], ['y', 'o', 'u'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "standard", some "kuin"⟩]
    paperFeatures := [("comparativeClass", "particle")] }

def ex_10_5a : Datum :=
  { id := "stassen1985_10_5a"
    source := ⟨"stassen-1985", "ch. 10 (5a)"⟩
    reportedIn := none
    method := some .description
    language := "swah1253"
    primaryText := "Joogoo wa Ali hodari, yule wa Juma dhaifu"
    glossedTokens := [("Joogoo", "rooster"), ("wa", "of"), ("Ali", "A."), ("hodari,", "strong"), ("yule", "that"), ("wa", "of"), ("Juma", "J."), ("dhaifu", "weak")]
    glossedWords := [⟨['J', 'o', 'o', 'g', 'o', 'o'], ['r', 'o', 'o', 's', 't', 'e', 'r'], [⟨['J', 'o', 'o', 'g', 'o', 'o'], ['r', 'o', 'o', 's', 't', 'e', 'r'], none⟩]⟩, ⟨['w', 'a'], ['o', 'f'], [⟨['w', 'a'], ['o', 'f'], none⟩]⟩, ⟨['A', 'l', 'i'], ['A', '.'], [⟨['A', 'l', 'i'], ['A', '.'], none⟩]⟩, ⟨['h', 'o', 'd', 'a', 'r', 'i', ','], ['s', 't', 'r', 'o', 'n', 'g'], [⟨['h', 'o', 'd', 'a', 'r', 'i'], ['s', 't', 'r', 'o', 'n', 'g'], none⟩]⟩, ⟨['y', 'u', 'l', 'e'], ['t', 'h', 'a', 't'], [⟨['y', 'u', 'l', 'e'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['w', 'a'], ['o', 'f'], [⟨['w', 'a'], ['o', 'f'], none⟩]⟩, ⟨['J', 'u', 'm', 'a'], ['J', '.'], [⟨['J', 'u', 'm', 'a'], ['J', '.'], none⟩]⟩, ⟨['d', 'h', 'a', 'i', 'f', 'u'], ['w', 'e', 'a', 'k'], [⟨['d', 'h', 'a', 'i', 'f', 'u'], ['w', 'e', 'a', 'k'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨4, 0, "standard", some "juxtaposition"⟩]
    paperFeatures := [("comparativeClass", "conjoined")] }

def ex_10_54a : Datum :=
  { id := "stassen1985_10_54a"
    source := ⟨"stassen-1985", "ch. 10 (54a)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Nykyinen professori on edellis-a heiko-mpi"
    glossedTokens := [("Nykyinen", "current"), ("professori", "professor"), ("on", "is"), ("edellis-a", "former-PART"), ("heiko-mpi", "weak-er")]
    glossedWords := [⟨['N', 'y', 'k', 'y', 'i', 'n', 'e', 'n'], ['c', 'u', 'r', 'r', 'e', 'n', 't'], [⟨['N', 'y', 'k', 'y', 'i', 'n', 'e', 'n'], ['c', 'u', 'r', 'r', 'e', 'n', 't'], none⟩]⟩, ⟨['p', 'r', 'o', 'f', 'e', 's', 's', 'o', 'r', 'i'], ['p', 'r', 'o', 'f', 'e', 's', 's', 'o', 'r'], [⟨['p', 'r', 'o', 'f', 'e', 's', 's', 'o', 'r', 'i'], ['p', 'r', 'o', 'f', 'e', 's', 's', 'o', 'r'], none⟩]⟩, ⟨['o', 'n'], ['i', 's'], [⟨['o', 'n'], ['i', 's'], none⟩]⟩, ⟨['e', 'd', 'e', 'l', 'l', 'i', 's', '-', 'a'], ['f', 'o', 'r', 'm', 'e', 'r', '-', 'P', 'A', 'R', 'T'], [⟨['e', 'd', 'e', 'l', 'l', 'i', 's'], ['f', 'o', 'r', 'm', 'e', 'r'], none⟩, ⟨['a'], ['P', 'A', 'R', 'T'], some '-'⟩]⟩, ⟨['h', 'e', 'i', 'k', 'o', '-', 'm', 'p', 'i'], ['w', 'e', 'a', 'k', '-', 'e', 'r'], [⟨['h', 'e', 'i', 'k', 'o'], ['w', 'e', 'a', 'k'], none⟩, ⟨['m', 'p', 'i'], ['e', 'r'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "standard", some "partitive"⟩]
    paperFeatures := [("comparativeClass", "separative")] }

def all : List Datum := [ex_6_15, ex_6_24a, ex_6_26a, ex_6_32, ex_6_42, ex_8_12b, ex_8_16b, ex_8_24, ex_8_26, ex_9_35, ex_9_36, ex_9_37, ex_10_5a, ex_10_54a]

/-- The class of comparative construction the book lists the example under. -/
inductive ComparativeClass where
  /-- separative: the standard is in a source phrase -/
  | separative
  /-- allative: the standard is in a goal phrase -/
  | allative
  /-- locative: the standard is in a phrase of location or contact -/
  | locative
  /-- exceed: the standard is the direct object of a verb of exceeding -/
  | exceed
  /-- conjoined: two independent clauses, one for the comparee and one for the standard -/
  | conjoined
  /-- particle: a derived-case standard with a comparative particle -/
  | particle
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `comparativeClass`. -/
def comparativeClass (e : Datum) : Option ComparativeClass :=
  e.parse? "comparativeClass" [("separative", .separative), ("allative", .allative), ("locative", .locative),
    ("exceed", .exceed), ("conjoined", .conjoined), ("particle", .particle)]

/-- The labels of the spans the rows mark. -/
inductive SpanLabel where
  /-- standard: the word that carries the marker of the standard, or the place of the standard clause where there is no marker -/
  | standard
  deriving DecidableEq, Repr, Fintype

/-- The label of a span, where it is a declared one. -/
def label? (p : Datum.Span) : Option SpanLabel :=
  List.lookup p.label [("standard", .standard)]

/-- The comparative constructions of the rows, by the marker of the standard. -/
inductive Lexeme where
  /-- dan: the Turkish ablative suffix -DAn -/
  | dan
  /-- se: the Hindi-Urdu postposition se -/
  | se
  /-- yori: the Japanese postposition yori -/
  | yori
  /-- min: the Arabic preposition min -/
  | min
  /-- bi: the Mandarin verb bǐ -/
  | bi
  /-- ju: the Yoruba verb ju -/
  | ju
  /-- kushinda: the Swahili infinitive ku-shinda -/
  | kushinda
  /-- kuliko: the Swahili infinitive ku-liko -/
  | kuliko
  /-- chem: the Russian particle chem -/
  | chem
  /-- que: the French particle que -/
  | que
  /-- kuin: the Finnish particle kuin -/
  | kuin
  /-- juxtaposition: the Swahili juxtaposition of two clauses, with no marker -/
  | juxtaposition
  /-- partitive: the Finnish partitive standard -/
  | partitive
  deriving DecidableEq, Repr, Fintype

/-- The lexeme a span is a form of, where it names a declared one. -/
def lexeme? (p : Datum.Span) : Option Lexeme :=
  p.lexeme.bind (List.lookup · [("dan", .dan), ("se", .se), ("yori", .yori), ("min", .min), ("bi", .bi), ("ju", .ju), ("kushinda", .kushinda), ("kuliko", .kuliko), ("chem", .chem), ("que", .que), ("kuin", .kuin), ("juxtaposition", .juxtaposition), ("partitive", .partitive)])

/-- The examples of the book that are recorded. -/
inductive Example where
  | ex_6_15
  | ex_6_24a
  | ex_6_26a
  | ex_6_32
  | ex_6_42
  | ex_8_12b
  | ex_8_16b
  | ex_8_24
  | ex_8_26
  | ex_9_35
  | ex_9_36
  | ex_9_37
  | ex_10_5a
  | ex_10_54a
  deriving DecidableEq, Repr, Fintype

/-- Every example of the file, in its order. -/
def Example.all : List Example :=
  [.ex_6_15, .ex_6_24a, .ex_6_26a, .ex_6_32, .ex_6_42, .ex_8_12b, .ex_8_16b, .ex_8_24, .ex_8_26,
    .ex_9_35, .ex_9_36, .ex_9_37, .ex_10_5a, .ex_10_54a]

/-- The row of an example. -/
def Example.datum : Example → Datum
  | .ex_6_15 => _root_.Stassen1985.Examples.ex_6_15
  | .ex_6_24a => _root_.Stassen1985.Examples.ex_6_24a
  | .ex_6_26a => _root_.Stassen1985.Examples.ex_6_26a
  | .ex_6_32 => _root_.Stassen1985.Examples.ex_6_32
  | .ex_6_42 => _root_.Stassen1985.Examples.ex_6_42
  | .ex_8_12b => _root_.Stassen1985.Examples.ex_8_12b
  | .ex_8_16b => _root_.Stassen1985.Examples.ex_8_16b
  | .ex_8_24 => _root_.Stassen1985.Examples.ex_8_24
  | .ex_8_26 => _root_.Stassen1985.Examples.ex_8_26
  | .ex_9_35 => _root_.Stassen1985.Examples.ex_9_35
  | .ex_9_36 => _root_.Stassen1985.Examples.ex_9_36
  | .ex_9_37 => _root_.Stassen1985.Examples.ex_9_37
  | .ex_10_5a => _root_.Stassen1985.Examples.ex_10_5a
  | .ex_10_54a => _root_.Stassen1985.Examples.ex_10_54a

theorem Example.map_datum_all :
    Example.all.map Example.datum = _root_.Stassen1985.Examples.all := rfl

/-- The value the example records under `comparativeClass`. -/
def Example.comparativeClass : Example → Option ComparativeClass
  | .ex_6_15 => some .separative
  | .ex_6_24a => some .separative
  | .ex_6_26a => some .separative
  | .ex_6_32 => some .separative
  | .ex_6_42 => some .separative
  | .ex_8_12b => some .exceed
  | .ex_8_16b => some .exceed
  | .ex_8_24 => some .exceed
  | .ex_8_26 => none
  | .ex_9_35 => some .particle
  | .ex_9_36 => some .particle
  | .ex_9_37 => some .particle
  | .ex_10_5a => some .conjoined
  | .ex_10_54a => some .separative

theorem Example.comparativeClass_datum :
    ∀ x : Example, _root_.Stassen1985.Examples.comparativeClass x.datum = x.comparativeClass := by
  decide +kernel

/-- The lexemes the spans of the example name, each with the span's label, in order. -/
def Example.labelledLexemes : Example → List (SpanLabel × Lexeme)
  | .ex_6_15 => [(.standard, .dan)]
  | .ex_6_24a => [(.standard, .se)]
  | .ex_6_26a => [(.standard, .yori)]
  | .ex_6_32 => []
  | .ex_6_42 => [(.standard, .min)]
  | .ex_8_12b => [(.standard, .bi)]
  | .ex_8_16b => [(.standard, .ju)]
  | .ex_8_24 => [(.standard, .kushinda)]
  | .ex_8_26 => [(.standard, .kuliko)]
  | .ex_9_35 => [(.standard, .chem)]
  | .ex_9_36 => [(.standard, .que)]
  | .ex_9_37 => [(.standard, .kuin)]
  | .ex_10_5a => [(.standard, .juxtaposition)]
  | .ex_10_54a => [(.standard, .partitive)]

/-- The lexemes the spans of the example labelled `l` name, in order. -/
def Example.lexemes (x : Example) (l : SpanLabel) : List Lexeme :=
  (x.labelledLexemes.filter (·.1 = l)).map (·.2)

theorem Example.lexemes_datum : ∀ (x : Example) (l : SpanLabel),
    (x.datum.spans.filter (_root_.Stassen1985.Examples.label? · = some l)).filterMap _root_.Stassen1985.Examples.lexeme? =
      x.lexemes l := by
  decide +kernel

end Stassen1985.Examples
