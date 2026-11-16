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
    glossedWords := [⟨[['M', 'i', 'n']], [['I', '.', 'N', 'O', 'M']]⟩, ⟨[['k', 'e', 'l'], ['l', 'i'], ['m']], [['c', 'o', 'm', 'e'], ['P', 'S', 'T'], ['1', 'S', 'G', '.', 'S', 'B', 'J']]⟩]
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
    glossedWords := [⟨[['M', 'i', 'n']], [['I', '.', 'N', 'O', 'M']]⟩, ⟨[['o', 'l', 'o', 'p', 'p', 'o', 'h'], ['u']], [['c', 'h', 'a', 'i', 'r'], ['A', 'C', 'C']]⟩, ⟨[['a', 'l', 'd', 'j', 'a', 't'], ['t', 'y'], ['m']], [['b', 'r', 'e', 'a', 'k'], ['P', 'S', 'T'], ['1', 'S', 'G', '.', 'S', 'B', 'J']]⟩]
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
    glossedWords := [⟨[['E', 'r', 'e', 'l']], [['E', 'r', 'e', 'l', '.', 'N', 'O', 'M']]⟩, ⟨[['k', 'i', 'n', 'i', 'g', 'e'], ['n', 'i']], [['b', 'o', 'o', 'k'], ['A', 'C', 'C']]⟩, ⟨[['a', 't', 'y', 'y', 'l', 'a', 's'], ['t', 'a']], [['b', 'u', 'y'], ['P', 'S', 'T', '.', '3', 'S', 'G', '.', 'S', 'B', 'J']]⟩]
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
    glossedWords := [⟨[['M', 'a', 'r', 'i', 'a'], ['n', 'i', 'n'], ['r', 'a']], [['M', 'a', 'r', 'i', 'a'], ['E', 'R', 'G'], ['P', 'R', 'T']]⟩, ⟨[['o', 'c', 'h', 'i', 't', 'i']], [['d', 'o', 'g']]⟩, ⟨[['n', 'o', 'k', 'o'], ['k', 'e']], [['f', 'i', 'n', 'd'], ['P', 'R', 'F']]⟩]
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
    glossedWords := [⟨[['M', 'a', 'r', 'i', 'a'], ['r', 'a']], [['M', 'a', 'r', 'i', 'a'], ['P', 'R', 'T']]⟩, ⟨[['k', 'a'], ['k', 'e']], [['g', 'o'], ['P', 'R', 'F']]⟩]
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
    glossedWords := [⟨[['J', 'o', 's', 'e'], ['k', 'a', 'n']], [['J', 'o', 's', 'e'], ['E', 'R', 'G']]⟩, ⟨[['o', 'c', 'h', 'i', 't', 'i']], [['d', 'o', 'g']]⟩, ⟨[['b', 'e', 'n'], ['a', 'i']], [['s', 'e', 'e', 'k'], ['I', 'P', 'F', 'V']]⟩]
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
    glossedWords := [⟨[['E'], ['n']], [['I'], ['E', 'R', 'G']]⟩, ⟨[['o', 'c', 'h', 'i', 't', 'i']], [['d', 'o', 'g']]⟩, ⟨[['b', 'e', 'n'], ['a', 'i']], [['s', 'e', 'e', 'k'], ['I', 'P', 'F', 'V']]⟩]
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
    glossedWords := [⟨[['H', 'i'], ['p', 'á', 'a', 'y'], ['n', 'a']], [['3', 'S', 'G', '.', 'S', 'B', 'J'], ['a', 'r', 'r', 'i', 'v', 'e'], ['A', 'S', 'P']]⟩, ⟨[['h', 'á', 'a', 'm', 'a']], [['m', 'a', 'n', '.', 'N', 'O', 'M']]⟩]
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
    glossedWords := [⟨[['H', 'á', 'a', 'm', 'a'], ['n', 'm']], [['m', 'a', 'n'], ['E', 'R', 'G']]⟩, ⟨[['h', 'i'], ['n', 'é', 'e', 'c'], ['\'', 'w', 'i'], ['y', 'e']], [['3', 'S', 'G', '.', 'S', 'B', 'J'], ['P', 'L', '.', 'O', 'B', 'J'], ['s', 'h', 'o', 'o', 't'], ['A', 'S', 'P']]⟩, ⟨[['w', 'e', 'w', 'ú', 'k', 'i', 'y', 'e'], ['n', 'e']], [['e', 'l', 'k'], ['A', 'C', 'C']]⟩]
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
    glossedWords := [⟨[['F', 'a', 'r', 'i', 'd']], [['F', 'a', 'r', 'i', 'd', '.', 'A', 'B', 'S']]⟩, ⟨[['a', 't', 'a'], ['n', 'a'], ['n', 'i']], [['c', 'o', 'm', 'e'], ['A', 'O', 'R'], ['Q']]⟩]
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
    glossedWords := [⟨[['S', 'a', 'd', 'i', 'q', '\''], ['a']], [['S', 'a', 'd', 'i', 'q', '\''], ['E', 'R', 'G']]⟩, ⟨[['j', 'a', 'd']], [['w', 'a', 't', 'e', 'r', '.', 'A', 'B', 'S']]⟩, ⟨[['q', 'h', 'w', 'a'], ['n', 'a']], [['d', 'r', 'i', 'n', 'k'], ['A', 'O', 'R']]⟩]
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
    glossedWords := [⟨[['N', 'í']], [['I']]⟩, ⟨[['a', 'd', 'a'], ['p', 'a', 'r', 'a']], [['h', 'o', 'u', 's', 'e'], ['i', 'n']]⟩, ⟨[['p', 'í', 'r', 'a'], ['w', 'a']], [['s', 'i', 't'], ['1', 'S', 'G', '.', 'S', 'B', 'J']]⟩]
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
    glossedWords := [⟨[['N', 'é'], ['m', 'é']], [['I'], ['E', 'R', 'G']]⟩, ⟨[['i', 'r', 'i', 'k', 'a', 'i']], [['d', 'o', 'g']]⟩, ⟨[['t', 'á'], ['w', 'a']], [['h', 'i', 't'], ['1', 'S', 'G', '.', 'S', 'B', 'J']]⟩]
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
    glossedWords := [⟨[['D', 'a', 's', 'í', 'n']], [['g', 'i', 'r', 'l', '.', 'A', 'B', 'S']]⟩, ⟨[['h', 'á'], ['e']], [['h', 'o', 'u', 's', 'e'], ['O', 'B', 'L']]⟩, ⟨[['l', 'e']], [['i', 'n']]⟩, ⟨[['h', 'u', 'r', 'ú', 't'], ['u', 'm', 'o']], [['s', 'i', 't'], ['P', 'S', 'T', '.', '3', 'S', 'G', '.', 'F', '.', 'S', 'B', 'J']]⟩]
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
    glossedWords := [⟨[['H', 'i', 'l', 'é', 's'], ['e']], [['b', 'o', 'y'], ['E', 'R', 'G']]⟩, ⟨[['d', 'a', 's', 'i', 'n']], [['g', 'i', 'r', 'l', '.', 'A', 'B', 'S']]⟩, ⟨[['m', 'u'], ['y', 'e', 'é', 't', 's'], ['i', 'm', 'i']], [['3', 'S', 'G', '.', 'F', '.', 'O', 'B', 'J'], ['s', 'e', 'e'], ['P', 'S', 'T', '.', '3', 'S', 'G', '.', 'M', '.', 'S', 'B', 'J']]⟩]
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
    glossedWords := [⟨[['N', 'a', 'd', 'y', 'a']], [['N', 'a', 'd', 'y', 'a', '.', 'F', '.', 'N', 'O', 'M']]⟩, ⟨[['n', 'a', 'h', 'a'], ['y', 'i']], [['b', 'a', 't', 'h', 'e'], ['P', 'R', 'F', '.', 'F', '.', 'S', 'G']]⟩]
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
    glossedWords := [⟨[['R', 'a', 'm'], ['n', 'e']], [['R', 'a', 'm', '.', 'M'], ['E', 'R', 'G']]⟩, ⟨[['g', 'a', 'R', 'i']], [['c', 'a', 'r', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['c', 'a', 'l', 'a'], ['y', 'i']], [['d', 'r', 'i', 'v', 'e'], ['P', 'R', 'F', '.', 'F', '.', 'S', 'G']]⟩, ⟨[['h', 'E']], [['b', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("transitive", "yes"), ("subjectCase", "ERG"), ("objectCase", "NOM"), ("subjectAgreement", "no"), ("objectAgreement", "yes")] }

def all : List Datum := [ex_1a, ex_1b, ex_1c, ex_12a, ex_12b, ex_28a, ex_28b, ex_30a, ex_30b, ex_21a, ex_21b, ex_22a, ex_22b, ex_23a, ex_23b, ex_25a, ex_25b]

end Baker2015.Examples
