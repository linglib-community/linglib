module

public import Linglib.Data.Examples.Schema

/-!
# `Baker2015` — typed example data

Auto-generated from `Linglib/Data/Examples/Baker2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Baker2015.Examples`.
-/

@[expose] public section

namespace Baker2015.Examples

def ex_1a : Datum :=
  { id := "baker2015_1a"
    source := ⟨"baker-2015", "ch. 1 (1a)"⟩
    reportedIn := none
    language := "yaku1245"
    primaryText := "Min kellim."
    glossedTokens := [("Min", "I.NOM"), ("kel-li-m", "come-PST-1SG.SBJ")]
    glossedWords := [⟨['M', 'i', 'n'], ['I', '.', 'N', 'O', 'M'], [⟨['M', 'i', 'n'], ['I', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['k', 'e', 'l', '-', 'l', 'i', '-', 'm'], ['c', 'o', 'm', 'e', '-', 'P', 'S', 'T', '-', '1', 'S', 'G', '.', 'S', 'B', 'J'], [⟨['k', 'e', 'l'], ['c', 'o', 'm', 'e'], none⟩, ⟨['l', 'i'], ['P', 'S', 'T'], some '-'⟩, ⟨['m'], ['1', 'S', 'G', '.', 'S', 'B', 'J'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "no"), ("subjectCase", "NOM")] }

def ex_1b : Datum :=
  { id := "baker2015_1b"
    source := ⟨"baker-2015", "ch. 1 (1b)"⟩
    reportedIn := none
    language := "yaku1245"
    primaryText := "Min oloppohu aldjattym."
    glossedTokens := [("Min", "I.NOM"), ("oloppoh-u", "chair-ACC"), ("aldjat-ty-m", "break-PST-1SG.SBJ")]
    glossedWords := [⟨['M', 'i', 'n'], ['I', '.', 'N', 'O', 'M'], [⟨['M', 'i', 'n'], ['I', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['o', 'l', 'o', 'p', 'p', 'o', 'h', '-', 'u'], ['c', 'h', 'a', 'i', 'r', '-', 'A', 'C', 'C'], [⟨['o', 'l', 'o', 'p', 'p', 'o', 'h'], ['c', 'h', 'a', 'i', 'r'], none⟩, ⟨['u'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['a', 'l', 'd', 'j', 'a', 't', '-', 't', 'y', '-', 'm'], ['b', 'r', 'e', 'a', 'k', '-', 'P', 'S', 'T', '-', '1', 'S', 'G', '.', 'S', 'B', 'J'], [⟨['a', 'l', 'd', 'j', 'a', 't'], ['b', 'r', 'e', 'a', 'k'], none⟩, ⟨['t', 'y'], ['P', 'S', 'T'], some '-'⟩, ⟨['m'], ['1', 'S', 'G', '.', 'S', 'B', 'J'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "yes"), ("subjectCase", "NOM"), ("objectCase", "ACC")] }

def ex_1c : Datum :=
  { id := "baker2015_1c"
    source := ⟨"baker-2015", "ch. 1 (1c)"⟩
    reportedIn := none
    language := "yaku1245"
    primaryText := "Erel kinigeni atyylasta."
    glossedTokens := [("Erel", "Erel.NOM"), ("kinige-ni", "book-ACC"), ("atyylas-ta", "buy-PST.3SG.SBJ")]
    glossedWords := [⟨['E', 'r', 'e', 'l'], ['E', 'r', 'e', 'l', '.', 'N', 'O', 'M'], [⟨['E', 'r', 'e', 'l'], ['E', 'r', 'e', 'l', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['k', 'i', 'n', 'i', 'g', 'e', '-', 'n', 'i'], ['b', 'o', 'o', 'k', '-', 'A', 'C', 'C'], [⟨['k', 'i', 'n', 'i', 'g', 'e'], ['b', 'o', 'o', 'k'], none⟩, ⟨['n', 'i'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['a', 't', 'y', 'y', 'l', 'a', 's', '-', 't', 'a'], ['b', 'u', 'y', '-', 'P', 'S', 'T', '.', '3', 'S', 'G', '.', 'S', 'B', 'J'], [⟨['a', 't', 'y', 'y', 'l', 'a', 's'], ['b', 'u', 'y'], none⟩, ⟨['t', 'a'], ['P', 'S', 'T', '.', '3', 'S', 'G', '.', 'S', 'B', 'J'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "yes"), ("subjectCase", "NOM"), ("objectCase", "ACC")] }

def ex_12a : Datum :=
  { id := "baker2015_12a"
    source := ⟨"baker-2015", "ch. 1 (12a)"⟩
    reportedIn := none
    language := "ship1254"
    primaryText := "Maria-nin-ra ochiti nokoke."
    glossedTokens := [("Maria-nin-ra", "Maria-ERG-PRT"), ("ochiti", "dog"), ("noko-ke", "find-PRF")]
    glossedWords := [⟨['M', 'a', 'r', 'i', 'a', '-', 'n', 'i', 'n', '-', 'r', 'a'], ['M', 'a', 'r', 'i', 'a', '-', 'E', 'R', 'G', '-', 'P', 'R', 'T'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩, ⟨['n', 'i', 'n'], ['E', 'R', 'G'], some '-'⟩, ⟨['r', 'a'], ['P', 'R', 'T'], some '-'⟩]⟩, ⟨['o', 'c', 'h', 'i', 't', 'i'], ['d', 'o', 'g'], [⟨['o', 'c', 'h', 'i', 't', 'i'], ['d', 'o', 'g'], none⟩]⟩, ⟨['n', 'o', 'k', 'o', '-', 'k', 'e'], ['f', 'i', 'n', 'd', '-', 'P', 'R', 'F'], [⟨['n', 'o', 'k', 'o'], ['f', 'i', 'n', 'd'], none⟩, ⟨['k', 'e'], ['P', 'R', 'F'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "yes"), ("subjectCase", "ERG"), ("objectCase", "unmarked")] }

def ex_12b : Datum :=
  { id := "baker2015_12b"
    source := ⟨"baker-2015", "ch. 1 (12b)"⟩
    reportedIn := none
    language := "ship1254"
    primaryText := "Maria-ra kake."
    glossedTokens := [("Maria-ra", "Maria-PRT"), ("ka-ke", "go-PRF")]
    glossedWords := [⟨['M', 'a', 'r', 'i', 'a', '-', 'r', 'a'], ['M', 'a', 'r', 'i', 'a', '-', 'P', 'R', 'T'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩, ⟨['r', 'a'], ['P', 'R', 'T'], some '-'⟩]⟩, ⟨['k', 'a', '-', 'k', 'e'], ['g', 'o', '-', 'P', 'R', 'F'], [⟨['k', 'a'], ['g', 'o'], none⟩, ⟨['k', 'e'], ['P', 'R', 'F'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "no"), ("subjectCase", "unmarked")] }

def ex_28a : Datum :=
  { id := "baker2015_28a"
    source := ⟨"baker-2015", "ch. 1 (28a)"⟩
    reportedIn := none
    language := "ship1254"
    primaryText := "Jose-kan ochiti benai."
    glossedTokens := [("Jose-kan", "Jose-ERG"), ("ochiti", "dog"), ("ben-ai", "seek-IPFV")]
    glossedWords := [⟨['J', 'o', 's', 'e', '-', 'k', 'a', 'n'], ['J', 'o', 's', 'e', '-', 'E', 'R', 'G'], [⟨['J', 'o', 's', 'e'], ['J', 'o', 's', 'e'], none⟩, ⟨['k', 'a', 'n'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['o', 'c', 'h', 'i', 't', 'i'], ['d', 'o', 'g'], [⟨['o', 'c', 'h', 'i', 't', 'i'], ['d', 'o', 'g'], none⟩]⟩, ⟨['b', 'e', 'n', '-', 'a', 'i'], ['s', 'e', 'e', 'k', '-', 'I', 'P', 'F', 'V'], [⟨['b', 'e', 'n'], ['s', 'e', 'e', 'k'], none⟩, ⟨['a', 'i'], ['I', 'P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "yes"), ("subjectCase", "ERG"), ("objectCase", "unmarked"), ("genitiveForm", "Jose-kan")] }

def ex_28b : Datum :=
  { id := "baker2015_28b"
    source := ⟨"baker-2015", "ch. 1 (28b)"⟩
    reportedIn := none
    language := "ship1254"
    primaryText := "E-n ochiti benai."
    glossedTokens := [("E-n", "I-ERG"), ("ochiti", "dog"), ("ben-ai", "seek-IPFV")]
    glossedWords := [⟨['E', '-', 'n'], ['I', '-', 'E', 'R', 'G'], [⟨['E'], ['I'], none⟩, ⟨['n'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['o', 'c', 'h', 'i', 't', 'i'], ['d', 'o', 'g'], [⟨['o', 'c', 'h', 'i', 't', 'i'], ['d', 'o', 'g'], none⟩]⟩, ⟨['b', 'e', 'n', '-', 'a', 'i'], ['s', 'e', 'e', 'k', '-', 'I', 'P', 'F', 'V'], [⟨['b', 'e', 'n'], ['s', 'e', 'e', 'k'], none⟩, ⟨['a', 'i'], ['I', 'P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "yes"), ("subjectCase", "ERG"), ("objectCase", "unmarked"), ("genitiveForm", "nokon")] }

def ex_30a : Datum :=
  { id := "baker2015_30a"
    source := ⟨"baker-2015", "ch. 1 (30a)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "Hipáayna háama."
    glossedTokens := [("Hi-páay-na", "3SG.SBJ-arrive-ASP"), ("háama", "man.NOM")]
    glossedWords := [⟨['H', 'i', '-', 'p', 'á', 'a', 'y', '-', 'n', 'a'], ['3', 'S', 'G', '.', 'S', 'B', 'J', '-', 'a', 'r', 'r', 'i', 'v', 'e', '-', 'A', 'S', 'P'], [⟨['H', 'i'], ['3', 'S', 'G', '.', 'S', 'B', 'J'], none⟩, ⟨['p', 'á', 'a', 'y'], ['a', 'r', 'r', 'i', 'v', 'e'], some '-'⟩, ⟨['n', 'a'], ['A', 'S', 'P'], some '-'⟩]⟩, ⟨['h', 'á', 'a', 'm', 'a'], ['m', 'a', 'n', '.', 'N', 'O', 'M'], [⟨['h', 'á', 'a', 'm', 'a'], ['m', 'a', 'n', '.', 'N', 'O', 'M'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "no"), ("subjectCase", "NOM")] }

def ex_30b : Datum :=
  { id := "baker2015_30b"
    source := ⟨"baker-2015", "ch. 1 (30b)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "Háamanm hinéec'wiye wewúkiyene."
    glossedTokens := [("Háama-nm", "man-ERG"), ("hi-néec-'wi-ye", "3SG.SBJ-PL.OBJ-shoot-ASP"), ("wewúkiye-ne", "elk-ACC")]
    glossedWords := [⟨['H', 'á', 'a', 'm', 'a', '-', 'n', 'm'], ['m', 'a', 'n', '-', 'E', 'R', 'G'], [⟨['H', 'á', 'a', 'm', 'a'], ['m', 'a', 'n'], none⟩, ⟨['n', 'm'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['h', 'i', '-', 'n', 'é', 'e', 'c', '-', '\'', 'w', 'i', '-', 'y', 'e'], ['3', 'S', 'G', '.', 'S', 'B', 'J', '-', 'P', 'L', '.', 'O', 'B', 'J', '-', 's', 'h', 'o', 'o', 't', '-', 'A', 'S', 'P'], [⟨['h', 'i'], ['3', 'S', 'G', '.', 'S', 'B', 'J'], none⟩, ⟨['n', 'é', 'e', 'c'], ['P', 'L', '.', 'O', 'B', 'J'], some '-'⟩, ⟨['\'', 'w', 'i'], ['s', 'h', 'o', 'o', 't'], some '-'⟩, ⟨['y', 'e'], ['A', 'S', 'P'], some '-'⟩]⟩, ⟨['w', 'e', 'w', 'ú', 'k', 'i', 'y', 'e', '-', 'n', 'e'], ['e', 'l', 'k', '-', 'A', 'C', 'C'], [⟨['w', 'e', 'w', 'ú', 'k', 'i', 'y', 'e'], ['e', 'l', 'k'], none⟩, ⟨['n', 'e'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "yes"), ("subjectCase", "ERG"), ("objectCase", "ACC")] }

def ex_21a : Datum :=
  { id := "baker2015_21a"
    source := ⟨"baker-2015", "ch. 2 (21a)"⟩
    reportedIn := none
    language := "lezg1247"
    primaryText := "Farid atanani?"
    glossedTokens := [("Farid", "Farid.ABS"), ("ata-na-ni", "come-AOR-Q")]
    glossedWords := [⟨['F', 'a', 'r', 'i', 'd'], ['F', 'a', 'r', 'i', 'd', '.', 'A', 'B', 'S'], [⟨['F', 'a', 'r', 'i', 'd'], ['F', 'a', 'r', 'i', 'd', '.', 'A', 'B', 'S'], none⟩]⟩, ⟨['a', 't', 'a', '-', 'n', 'a', '-', 'n', 'i'], ['c', 'o', 'm', 'e', '-', 'A', 'O', 'R', '-', 'Q'], [⟨['a', 't', 'a'], ['c', 'o', 'm', 'e'], none⟩, ⟨['n', 'a'], ['A', 'O', 'R'], some '-'⟩, ⟨['n', 'i'], ['Q'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "no"), ("subjectCase", "ABS")] }

def ex_21b : Datum :=
  { id := "baker2015_21b"
    source := ⟨"baker-2015", "ch. 2 (21b)"⟩
    reportedIn := none
    language := "lezg1247"
    primaryText := "Sadiq'a jad qhwana."
    glossedTokens := [("Sadiq'-a", "Sadiq'-ERG"), ("jad", "water.ABS"), ("qhwa-na", "drink-AOR")]
    glossedWords := [⟨['S', 'a', 'd', 'i', 'q', '\'', '-', 'a'], ['S', 'a', 'd', 'i', 'q', '\'', '-', 'E', 'R', 'G'], [⟨['S', 'a', 'd', 'i', 'q', '\''], ['S', 'a', 'd', 'i', 'q', '\''], none⟩, ⟨['a'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['j', 'a', 'd'], ['w', 'a', 't', 'e', 'r', '.', 'A', 'B', 'S'], [⟨['j', 'a', 'd'], ['w', 'a', 't', 'e', 'r', '.', 'A', 'B', 'S'], none⟩]⟩, ⟨['q', 'h', 'w', 'a', '-', 'n', 'a'], ['d', 'r', 'i', 'n', 'k', '-', 'A', 'O', 'R'], [⟨['q', 'h', 'w', 'a'], ['d', 'r', 'i', 'n', 'k'], none⟩, ⟨['n', 'a'], ['A', 'O', 'R'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "yes"), ("subjectCase", "ERG"), ("objectCase", "ABS")] }

def ex_22a : Datum :=
  { id := "baker2015_22a"
    source := ⟨"baker-2015", "ch. 2 (22a)"⟩
    reportedIn := none
    language := "west2599"
    primaryText := "Ní adapara pírawa."
    glossedTokens := [("Ní", "I"), ("ada-para", "house-in"), ("píra-wa", "sit-1SG.SBJ")]
    glossedWords := [⟨['N', 'í'], ['I'], [⟨['N', 'í'], ['I'], none⟩]⟩, ⟨['a', 'd', 'a', '-', 'p', 'a', 'r', 'a'], ['h', 'o', 'u', 's', 'e', '-', 'i', 'n'], [⟨['a', 'd', 'a'], ['h', 'o', 'u', 's', 'e'], none⟩, ⟨['p', 'a', 'r', 'a'], ['i', 'n'], some '-'⟩]⟩, ⟨['p', 'í', 'r', 'a', '-', 'w', 'a'], ['s', 'i', 't', '-', '1', 'S', 'G', '.', 'S', 'B', 'J'], [⟨['p', 'í', 'r', 'a'], ['s', 'i', 't'], none⟩, ⟨['w', 'a'], ['1', 'S', 'G', '.', 'S', 'B', 'J'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "no"), ("subjectCase", "unmarked"), ("subjectAgreement", "yes")] }

def ex_22b : Datum :=
  { id := "baker2015_22b"
    source := ⟨"baker-2015", "ch. 2 (22b)"⟩
    reportedIn := none
    language := "west2599"
    primaryText := "Némé irikai táwa."
    glossedTokens := [("Né-mé", "I-ERG"), ("irikai", "dog"), ("tá-wa", "hit-1SG.SBJ")]
    glossedWords := [⟨['N', 'é', '-', 'm', 'é'], ['I', '-', 'E', 'R', 'G'], [⟨['N', 'é'], ['I'], none⟩, ⟨['m', 'é'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['i', 'r', 'i', 'k', 'a', 'i'], ['d', 'o', 'g'], [⟨['i', 'r', 'i', 'k', 'a', 'i'], ['d', 'o', 'g'], none⟩]⟩, ⟨['t', 'á', '-', 'w', 'a'], ['h', 'i', 't', '-', '1', 'S', 'G', '.', 'S', 'B', 'J'], [⟨['t', 'á'], ['h', 'i', 't'], none⟩, ⟨['w', 'a'], ['1', 'S', 'G', '.', 'S', 'B', 'J'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "yes"), ("subjectCase", "ERG"), ("objectCase", "unmarked"), ("subjectAgreement", "yes")] }

def ex_23a : Datum :=
  { id := "baker2015_23a"
    source := ⟨"baker-2015", "ch. 2 (23a)"⟩
    reportedIn := none
    language := "buru1296"
    primaryText := "Dasín háe le hurútumo."
    glossedTokens := [("Dasín", "girl.ABS"), ("há-e", "house-OBL"), ("le", "in"), ("hurút-umo", "sit-PST.3SG.F.SBJ")]
    glossedWords := [⟨['D', 'a', 's', 'í', 'n'], ['g', 'i', 'r', 'l', '.', 'A', 'B', 'S'], [⟨['D', 'a', 's', 'í', 'n'], ['g', 'i', 'r', 'l', '.', 'A', 'B', 'S'], none⟩]⟩, ⟨['h', 'á', '-', 'e'], ['h', 'o', 'u', 's', 'e', '-', 'O', 'B', 'L'], [⟨['h', 'á'], ['h', 'o', 'u', 's', 'e'], none⟩, ⟨['e'], ['O', 'B', 'L'], some '-'⟩]⟩, ⟨['l', 'e'], ['i', 'n'], [⟨['l', 'e'], ['i', 'n'], none⟩]⟩, ⟨['h', 'u', 'r', 'ú', 't', '-', 'u', 'm', 'o'], ['s', 'i', 't', '-', 'P', 'S', 'T', '.', '3', 'S', 'G', '.', 'F', '.', 'S', 'B', 'J'], [⟨['h', 'u', 'r', 'ú', 't'], ['s', 'i', 't'], none⟩, ⟨['u', 'm', 'o'], ['P', 'S', 'T', '.', '3', 'S', 'G', '.', 'F', '.', 'S', 'B', 'J'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "no"), ("subjectCase", "ABS"), ("subjectAgreement", "yes")] }

def ex_23b : Datum :=
  { id := "baker2015_23b"
    source := ⟨"baker-2015", "ch. 2 (23b)"⟩
    reportedIn := none
    language := "buru1296"
    primaryText := "Hilése dasin muyeétsimi."
    glossedTokens := [("Hilés-e", "boy-ERG"), ("dasin", "girl.ABS"), ("mu-yeéts-imi", "3SG.F.OBJ-see-PST.3SG.M.SBJ")]
    glossedWords := [⟨['H', 'i', 'l', 'é', 's', '-', 'e'], ['b', 'o', 'y', '-', 'E', 'R', 'G'], [⟨['H', 'i', 'l', 'é', 's'], ['b', 'o', 'y'], none⟩, ⟨['e'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['d', 'a', 's', 'i', 'n'], ['g', 'i', 'r', 'l', '.', 'A', 'B', 'S'], [⟨['d', 'a', 's', 'i', 'n'], ['g', 'i', 'r', 'l', '.', 'A', 'B', 'S'], none⟩]⟩, ⟨['m', 'u', '-', 'y', 'e', 'é', 't', 's', '-', 'i', 'm', 'i'], ['3', 'S', 'G', '.', 'F', '.', 'O', 'B', 'J', '-', 's', 'e', 'e', '-', 'P', 'S', 'T', '.', '3', 'S', 'G', '.', 'M', '.', 'S', 'B', 'J'], [⟨['m', 'u'], ['3', 'S', 'G', '.', 'F', '.', 'O', 'B', 'J'], none⟩, ⟨['y', 'e', 'é', 't', 's'], ['s', 'e', 'e'], some '-'⟩, ⟨['i', 'm', 'i'], ['P', 'S', 'T', '.', '3', 'S', 'G', '.', 'M', '.', 'S', 'B', 'J'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "yes"), ("subjectCase", "ERG"), ("objectCase", "ABS"), ("subjectAgreement", "yes"), ("objectAgreement", "yes")] }

def ex_25a : Datum :=
  { id := "baker2015_25a"
    source := ⟨"baker-2015", "ch. 2 (25a)"⟩
    reportedIn := none
    language := "urdu1245"
    primaryText := "Nadya nahayi."
    glossedTokens := [("Nadya", "Nadya.F.NOM"), ("naha-yi", "bathe-PRF.F.SG")]
    glossedWords := [⟨['N', 'a', 'd', 'y', 'a'], ['N', 'a', 'd', 'y', 'a', '.', 'F', '.', 'N', 'O', 'M'], [⟨['N', 'a', 'd', 'y', 'a'], ['N', 'a', 'd', 'y', 'a', '.', 'F', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['n', 'a', 'h', 'a', '-', 'y', 'i'], ['b', 'a', 't', 'h', 'e', '-', 'P', 'R', 'F', '.', 'F', '.', 'S', 'G'], [⟨['n', 'a', 'h', 'a'], ['b', 'a', 't', 'h', 'e'], none⟩, ⟨['y', 'i'], ['P', 'R', 'F', '.', 'F', '.', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "no"), ("subjectCase", "NOM"), ("subjectAgreement", "yes")] }

def ex_25b : Datum :=
  { id := "baker2015_25b"
    source := ⟨"baker-2015", "ch. 2 (25b)"⟩
    reportedIn := none
    language := "urdu1245"
    primaryText := "Ram=ne gaRi calayi hE."
    glossedTokens := [("Ram=ne", "Ram.M=ERG"), ("gaRi", "car.F.SG.NOM"), ("cala-yi", "drive-PRF.F.SG"), ("hE", "be.PRS.3SG")]
    glossedWords := [⟨['R', 'a', 'm', '=', 'n', 'e'], ['R', 'a', 'm', '.', 'M', '=', 'E', 'R', 'G'], [⟨['R', 'a', 'm'], ['R', 'a', 'm', '.', 'M'], none⟩, ⟨['n', 'e'], ['E', 'R', 'G'], some '='⟩]⟩, ⟨['g', 'a', 'R', 'i'], ['c', 'a', 'r', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M'], [⟨['g', 'a', 'R', 'i'], ['c', 'a', 'r', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['c', 'a', 'l', 'a', '-', 'y', 'i'], ['d', 'r', 'i', 'v', 'e', '-', 'P', 'R', 'F', '.', 'F', '.', 'S', 'G'], [⟨['c', 'a', 'l', 'a'], ['d', 'r', 'i', 'v', 'e'], none⟩, ⟨['y', 'i'], ['P', 'R', 'F', '.', 'F', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['h', 'E'], ['b', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], [⟨['h', 'E'], ['b', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "yes"), ("subjectCase", "ERG"), ("objectCase", "NOM"), ("subjectAgreement", "no"), ("objectAgreement", "yes")] }

def all : List Datum := [ex_1a, ex_1b, ex_1c, ex_12a, ex_12b, ex_28a, ex_28b, ex_30a, ex_30b, ex_21a, ex_21b, ex_22a, ex_22b, ex_23a, ex_23b, ex_25a, ex_25b]

end Baker2015.Examples
