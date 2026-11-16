module

public import Linglib.Data.Examples.Schema

/-!
# `Corbett1998` — typed example data

Auto-generated from `Linglib/Data/Examples/Corbett1998.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Corbett1998.Examples`.
-/

@[expose] public section

namespace Corbett1998.Examples

def s1 : Datum :=
  { id := "corbett1998_s1"
    source := ⟨"corbett-1998", "§1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I'm parked on the hill"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("I is parked on the hill", .ungrammatical)]
    readings := []
    paperFeatures := [] }

def ex_1 : Datum :=
  { id := "corbett1998_1"
    source := ⟨"corbett-1998", "(1)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "nov-yj avtomobil'"
    glossedTokens := [("nov-yj", "new-SG.MASC"), ("avtomobil'", "car")]
    glossedWords := [⟨[['n', 'o', 'v'], ['y', 'j']], [['n', 'e', 'w'], ['S', 'G', '.', 'M', 'A', 'S', 'C']]⟩, ⟨[['a', 'v', 't', 'o', 'm', 'o', 'b', 'i', 'l', '\'']], [['c', 'a', 'r']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("gender", "masc"), ("number", "sg"), ("ending", "yj"), ("case", "nom")] }

def ex_2 : Datum :=
  { id := "corbett1998_2"
    source := ⟨"corbett-1998", "(2)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "nov-aja mašina"
    glossedTokens := [("nov-aja", "new-SG.FEM"), ("mašina", "car")]
    glossedWords := [⟨[['n', 'o', 'v'], ['a', 'j', 'a']], [['n', 'e', 'w'], ['S', 'G', '.', 'F', 'E', 'M']]⟩, ⟨[['m', 'a', 'š', 'i', 'n', 'a']], [['c', 'a', 'r']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("gender", "fem"), ("number", "sg"), ("ending", "aja"), ("case", "nom")] }

def ex_3 : Datum :=
  { id := "corbett1998_3"
    source := ⟨"corbett-1998", "(3)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "nov-oe taksi"
    glossedTokens := [("nov-oe", "new-SG.NEUT"), ("taksi", "taxi")]
    glossedWords := [⟨[['n', 'o', 'v'], ['o', 'e']], [['n', 'e', 'w'], ['S', 'G', '.', 'N', 'E', 'U', 'T']]⟩, ⟨[['t', 'a', 'k', 's', 'i']], [['t', 'a', 'x', 'i']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("gender", "neut"), ("number", "sg"), ("ending", "oe"), ("case", "nom")] }

def ex_4 : Datum :=
  { id := "corbett1998_4"
    source := ⟨"corbett-1998", "(4)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "nov-ye avtomobil-i"
    glossedTokens := [("nov-ye", "new-PL"), ("avtomobil-i", "car-PL")]
    glossedWords := [⟨[['n', 'o', 'v'], ['y', 'e']], [['n', 'e', 'w'], ['P', 'L']]⟩, ⟨[['a', 'v', 't', 'o', 'm', 'o', 'b', 'i', 'l'], ['i']], [['c', 'a', 'r'], ['P', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("gender", "masc"), ("number", "pl"), ("ending", "ye"), ("case", "nom")] }

def ex_5 : Datum :=
  { id := "corbett1998_5"
    source := ⟨"corbett-1998", "(5)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "v nov-om avtomobil-e"
    glossedTokens := [("v", "in"), ("nov-om", "new-SG.LOC.MASC"), ("avtomobil-e", "car-SG.LOC")]
    glossedWords := [⟨[['v']], [['i', 'n']]⟩, ⟨[['n', 'o', 'v'], ['o', 'm']], [['n', 'e', 'w'], ['S', 'G', '.', 'L', 'O', 'C', '.', 'M', 'A', 'S', 'C']]⟩, ⟨[['a', 'v', 't', 'o', 'm', 'o', 'b', 'i', 'l'], ['e']], [['c', 'a', 'r'], ['S', 'G', '.', 'L', 'O', 'C']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("gender", "masc"), ("number", "sg"), ("case", "loc"), ("ending", "om")] }

def s2_3a : Datum :=
  { id := "corbett1998_s2_3a"
    source := ⟨"corbett-1998", "§2.3"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "ja beru"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("person", "1"), ("number", "sg"), ("ending", "u")] }

def s2_3b : Datum :=
  { id := "corbett1998_s2_3b"
    source := ⟨"corbett-1998", "§2.3"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "ty bereš'"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("person", "2"), ("number", "sg"), ("ending", "eš'")] }

def s2_3c : Datum :=
  { id := "corbett1998_s2_3c"
    source := ⟨"corbett-1998", "§2.3"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "on beret"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("person", "3"), ("number", "sg"), ("ending", "et")] }

def ex_6 : Datum :=
  { id := "corbett1998_6"
    source := ⟨"corbett-1998", "(6)"⟩
    reportedIn := none
    language := "nucl1622"
    primaryText := "e-pe anem e-pe akek ka"
    glossedTokens := [("e-pe", "I-the"), ("anem", "man"), ("e-pe", "I-the"), ("akek", "light.I"), ("ka", "is")]
    glossedWords := [⟨[['e'], ['p', 'e']], [['I'], ['t', 'h', 'e']]⟩, ⟨[['a', 'n', 'e', 'm']], [['m', 'a', 'n']]⟩, ⟨[['e'], ['p', 'e']], [['I'], ['t', 'h', 'e']]⟩, ⟨[['a', 'k', 'e', 'k']], [['l', 'i', 'g', 'h', 't', '.', 'I']]⟩, ⟨[['k', 'a']], [['i', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("gender", "I"), ("adjective", "akek"), ("demonstrative", "e-pe")] }

def ex_7 : Datum :=
  { id := "corbett1998_7"
    source := ⟨"corbett-1998", "(7)"⟩
    reportedIn := none
    language := "nucl1622"
    primaryText := "u-pe anum u-pe akuk ka"
    glossedTokens := [("u-pe", "II-the"), ("anum", "woman"), ("u-pe", "II-the"), ("akuk", "light.II"), ("ka", "is")]
    glossedWords := [⟨[['u'], ['p', 'e']], [['I', 'I'], ['t', 'h', 'e']]⟩, ⟨[['a', 'n', 'u', 'm']], [['w', 'o', 'm', 'a', 'n']]⟩, ⟨[['u'], ['p', 'e']], [['I', 'I'], ['t', 'h', 'e']]⟩, ⟨[['a', 'k', 'u', 'k']], [['l', 'i', 'g', 'h', 't', '.', 'I', 'I']]⟩, ⟨[['k', 'a']], [['i', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("gender", "II"), ("adjective", "akuk"), ("demonstrative", "u-pe")] }

def ex_8 : Datum :=
  { id := "corbett1998_8"
    source := ⟨"corbett-1998", "(8)"⟩
    reportedIn := none
    language := "nucl1622"
    primaryText := "e-pe de e-pe akak ka"
    glossedTokens := [("e-pe", "III-the"), ("de", "wood"), ("e-pe", "III-the"), ("akak", "light.III"), ("ka", "is")]
    glossedWords := [⟨[['e'], ['p', 'e']], [['I', 'I', 'I'], ['t', 'h', 'e']]⟩, ⟨[['d', 'e']], [['w', 'o', 'o', 'd']]⟩, ⟨[['e'], ['p', 'e']], [['I', 'I', 'I'], ['t', 'h', 'e']]⟩, ⟨[['a', 'k', 'a', 'k']], [['l', 'i', 'g', 'h', 't', '.', 'I', 'I', 'I']]⟩, ⟨[['k', 'a']], [['i', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("gender", "III"), ("adjective", "akak"), ("demonstrative", "e-pe")] }

def ex_9 : Datum :=
  { id := "corbett1998_9"
    source := ⟨"corbett-1998", "(9)"⟩
    reportedIn := none
    language := "nucl1622"
    primaryText := "i-pe behaw i-pe akik ka"
    glossedTokens := [("i-pe", "IV-the"), ("behaw", "pole"), ("i-pe", "IV-the"), ("akik", "light.IV"), ("ka", "is")]
    glossedWords := [⟨[['i'], ['p', 'e']], [['I', 'V'], ['t', 'h', 'e']]⟩, ⟨[['b', 'e', 'h', 'a', 'w']], [['p', 'o', 'l', 'e']]⟩, ⟨[['i'], ['p', 'e']], [['I', 'V'], ['t', 'h', 'e']]⟩, ⟨[['a', 'k', 'i', 'k']], [['l', 'i', 'g', 'h', 't', '.', 'I', 'V']]⟩, ⟨[['k', 'a']], [['i', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("gender", "IV"), ("adjective", "akik"), ("demonstrative", "i-pe")] }

def ex_10 : Datum :=
  { id := "corbett1998_10"
    source := ⟨"corbett-1998", "(10)"⟩
    reportedIn := none
    language := "arch1244"
    primaryText := "d-as̄-a-r-ej-r-u-t̄u-r x̌̄anna"
    glossedTokens := [("d-as̄-a-r-ej-r-u-t̄u-r", "II-of.me-SELF-II-SUFFIX-II-SUFFIX-ADJ-II"), ("x̌̄anna", "wife")]
    glossedWords := [⟨[['d'], ['a', 's', '̄'], ['a'], ['r'], ['e', 'j'], ['r'], ['u'], ['t', '̄', 'u'], ['r']], [['I', 'I'], ['o', 'f', '.', 'm', 'e'], ['S', 'E', 'L', 'F'], ['I', 'I'], ['S', 'U', 'F', 'F', 'I', 'X'], ['I', 'I'], ['S', 'U', 'F', 'F', 'I', 'X'], ['A', 'D', 'J'], ['I', 'I']]⟩, ⟨[['x', '̌', '̄', 'a', 'n', 'n', 'a']], [['w', 'i', 'f', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("gender", "II"), ("slots", "4")] }

def ex_11 : Datum :=
  { id := "corbett1998_11"
    source := ⟨"corbett-1998", "(11)"⟩
    reportedIn := none
    language := "soma1255"
    primaryText := "ìnan-kii baa y-imid"
    glossedTokens := [("ìnan-kii", "boy-the.SG.MASC"), ("baa", "FOCUS.MARKER"), ("y-imid", "SG.MASC-came")]
    glossedWords := [⟨[['ì', 'n', 'a', 'n'], ['k', 'i', 'i']], [['b', 'o', 'y'], ['t', 'h', 'e', '.', 'S', 'G', '.', 'M', 'A', 'S', 'C']]⟩, ⟨[['b', 'a', 'a']], [['F', 'O', 'C', 'U', 'S', '.', 'M', 'A', 'R', 'K', 'E', 'R']]⟩, ⟨[['y'], ['i', 'm', 'i', 'd']], [['S', 'G', '.', 'M', 'A', 'S', 'C'], ['c', 'a', 'm', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "ìnan"), ("number", "sg"), ("article", "kii"), ("verb", "y")] }

def ex_12 : Datum :=
  { id := "corbett1998_12"
    source := ⟨"corbett-1998", "(12)"⟩
    reportedIn := none
    language := "soma1255"
    primaryText := "inán-tii baa t-imid"
    glossedTokens := [("inán-tii", "girl-the.SG.FEM"), ("baa", "FOCUS.MARKER"), ("t-imid", "SG.FEM-came")]
    glossedWords := [⟨[['i', 'n', 'á', 'n'], ['t', 'i', 'i']], [['g', 'i', 'r', 'l'], ['t', 'h', 'e', '.', 'S', 'G', '.', 'F', 'E', 'M']]⟩, ⟨[['b', 'a', 'a']], [['F', 'O', 'C', 'U', 'S', '.', 'M', 'A', 'R', 'K', 'E', 'R']]⟩, ⟨[['t'], ['i', 'm', 'i', 'd']], [['S', 'G', '.', 'F', 'E', 'M'], ['c', 'a', 'm', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "inán"), ("number", "sg"), ("article", "tii"), ("verb", "t")] }

def ex_13 : Datum :=
  { id := "corbett1998_13"
    source := ⟨"corbett-1998", "(13)"⟩
    reportedIn := none
    language := "soma1255"
    primaryText := "inammá-dii baa y-imid"
    glossedTokens := [("inammá-dii", "boys-the.PL.MASC"), ("baa", "FOCUS.MARKER"), ("y-imid", "PL-came")]
    glossedWords := [⟨[['i', 'n', 'a', 'm', 'm', 'á'], ['d', 'i', 'i']], [['b', 'o', 'y', 's'], ['t', 'h', 'e', '.', 'P', 'L', '.', 'M', 'A', 'S', 'C']]⟩, ⟨[['b', 'a', 'a']], [['F', 'O', 'C', 'U', 'S', '.', 'M', 'A', 'R', 'K', 'E', 'R']]⟩, ⟨[['y'], ['i', 'm', 'i', 'd']], [['P', 'L'], ['c', 'a', 'm', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "ìnan"), ("number", "pl"), ("article", "tii"), ("verb", "y")] }

def ex_14 : Datum :=
  { id := "corbett1998_14"
    source := ⟨"corbett-1998", "(14)"⟩
    reportedIn := none
    language := "soma1255"
    primaryText := "ináma-hii baa y-imid"
    glossedTokens := [("ináma-hii", "girls-the.PL.FEM"), ("baa", "FOCUS.MARKER"), ("y-imid", "PL-came")]
    glossedWords := [⟨[['i', 'n', 'á', 'm', 'a'], ['h', 'i', 'i']], [['g', 'i', 'r', 'l', 's'], ['t', 'h', 'e', '.', 'P', 'L', '.', 'F', 'E', 'M']]⟩, ⟨[['b', 'a', 'a']], [['F', 'O', 'C', 'U', 'S', '.', 'M', 'A', 'R', 'K', 'E', 'R']]⟩, ⟨[['y'], ['i', 'm', 'i', 'd']], [['P', 'L'], ['c', 'a', 'm', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "inán"), ("number", "pl"), ("article", "kii"), ("verb", "y")] }

def s3_2a : Datum :=
  { id := "corbett1998_s3_2a"
    source := ⟨"corbett-1998", "§3.2"⟩
    reportedIn := none
    language := "soma1255"
    primaryText := "nin-kii"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "nin"), ("number", "sg"), ("article", "kii")] }

def s3_2b : Datum :=
  { id := "corbett1998_s3_2b"
    source := ⟨"corbett-1998", "§3.2"⟩
    reportedIn := none
    language := "soma1255"
    primaryText := "niman-kii"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "nin"), ("number", "pl"), ("article", "kii")] }

def s4a : Datum :=
  { id := "corbett1998_s4a"
    source := ⟨"corbett-1998", "§4"⟩
    reportedIn := none
    language := "lakk1252"
    primaryText := "q̄at-lu-wu-n-m-aj"
    glossedTokens := [("q̄at-lu-wu-n-m-aj", "house-OBLIQUE-IN-LATIVE-III-ALLATIVE")]
    glossedWords := [⟨[['q', '̄', 'a', 't'], ['l', 'u'], ['w', 'u'], ['n'], ['m'], ['a', 'j']], [['h', 'o', 'u', 's', 'e'], ['O', 'B', 'L', 'I', 'Q', 'U', 'E'], ['I', 'N'], ['L', 'A', 'T', 'I', 'V', 'E'], ['I', 'I', 'I'], ['A', 'L', 'L', 'A', 'T', 'I', 'V', 'E']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "caseMarkedNoun"), ("gender", "III")] }

def s4b : Datum :=
  { id := "corbett1998_s4b"
    source := ⟨"corbett-1998", "§4"⟩
    reportedIn := none
    language := "darg1241"
    primaryText := "bidra-li-če-b"
    glossedTokens := [("bidra-li-če-b", "bucket-OBLIQUE-SUPER-III")]
    glossedWords := [⟨[['b', 'i', 'd', 'r', 'a'], ['l', 'i'], ['č', 'e'], ['b']], [['b', 'u', 'c', 'k', 'e', 't'], ['O', 'B', 'L', 'I', 'Q', 'U', 'E'], ['S', 'U', 'P', 'E', 'R'], ['I', 'I', 'I']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "caseMarkedNoun"), ("gender", "III")] }

def ex_15 : Datum :=
  { id := "corbett1998_15"
    source := ⟨"corbett-1998", "(15)"⟩
    reportedIn := none
    language := "arch1244"
    primaryText := "d-ez buwa ǩ'anši d-i"
    glossedTokens := [("d-ez", "II-me.DAT"), ("buwa", "mother"), ("ǩ'anši", "like"), ("d-i", "II-is")]
    glossedWords := [⟨[['d'], ['e', 'z']], [['I', 'I'], ['m', 'e', '.', 'D', 'A', 'T']]⟩, ⟨[['b', 'u', 'w', 'a']], [['m', 'o', 't', 'h', 'e', 'r']]⟩, ⟨[['ǩ', '\'', 'a', 'n', 'š', 'i']], [['l', 'i', 'k', 'e']]⟩, ⟨[['d'], ['i']], [['I', 'I'], ['i', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "pronoun"), ("gender", "II")] }

def ex_16 : Datum :=
  { id := "corbett1998_16"
    source := ⟨"corbett-1998", "(16)"⟩
    reportedIn := none
    language := "arch1244"
    primaryText := "b-ez dogi ǩ'anši b-i"
    glossedTokens := [("b-ez", "III-me"), ("dogi", "donkey"), ("ǩ'anši", "like"), ("b-i", "III-is")]
    glossedWords := [⟨[['b'], ['e', 'z']], [['I', 'I', 'I'], ['m', 'e']]⟩, ⟨[['d', 'o', 'g', 'i']], [['d', 'o', 'n', 'k', 'e', 'y']]⟩, ⟨[['ǩ', '\'', 'a', 'n', 'š', 'i']], [['l', 'i', 'k', 'e']]⟩, ⟨[['b'], ['i']], [['I', 'I', 'I'], ['i', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "pronoun"), ("gender", "III")] }

def ex_17 : Datum :=
  { id := "corbett1998_17"
    source := ⟨"corbett-1998", "(17)"⟩
    reportedIn := none
    language := "uppe1395"
    primaryText := "wón je pisał"
    glossedTokens := [("wón", "he"), ("je", "is.3SG"), ("pisał", "written.SG.MASC")]
    glossedWords := [⟨[['w', 'ó', 'n']], [['h', 'e']]⟩, ⟨[['j', 'e']], [['i', 's', '.', '3', 'S', 'G']]⟩, ⟨[['p', 'i', 's', 'a', 'ł']], [['w', 'r', 'i', 't', 't', 'e', 'n', '.', 'S', 'G', '.', 'M', 'A', 'S', 'C']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("finiteVerb", "number,person"), ("participle", "number,gender")] }

def ex_18 : Datum :=
  { id := "corbett1998_18"
    source := ⟨"corbett-1998", "(18)"⟩
    reportedIn := none
    language := "nyan1308"
    primaryText := "ma-lalanje ndi ma-samba a-kubvunda"
    glossedTokens := [("ma-lalanje", "6-orange"), ("ndi", "and"), ("ma-samba", "6-leaf"), ("a-kubvunda", "6-be.rotting")]
    glossedWords := [⟨[['m', 'a'], ['l', 'a', 'l', 'a', 'n', 'j', 'e']], [['6'], ['o', 'r', 'a', 'n', 'g', 'e']]⟩, ⟨[['n', 'd', 'i']], [['a', 'n', 'd']]⟩, ⟨[['m', 'a'], ['s', 'a', 'm', 'b', 'a']], [['6'], ['l', 'e', 'a', 'f']]⟩, ⟨[['a'], ['k', 'u', 'b', 'v', 'u', 'n', 'd', 'a']], [['6'], ['b', 'e', '.', 'r', 'o', 't', 't', 'i', 'n', 'g']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "ma-lalanje"), ("conjunct2", "ma-samba"), ("prefix", "a")] }

def ex_19 : Datum :=
  { id := "corbett1998_19"
    source := ⟨"corbett-1998", "(19)"⟩
    reportedIn := none
    language := "nyan1308"
    primaryText := "a-mphaka ndi ma-lalanje a-li uko"
    glossedTokens := [("a-mphaka", "2-cat"), ("ndi", "and"), ("ma-lalanje", "6-orange"), ("a-li", "GN-be"), ("uko", "there")]
    glossedWords := [⟨[['a'], ['m', 'p', 'h', 'a', 'k', 'a']], [['2'], ['c', 'a', 't']]⟩, ⟨[['n', 'd', 'i']], [['a', 'n', 'd']]⟩, ⟨[['m', 'a'], ['l', 'a', 'l', 'a', 'n', 'j', 'e']], [['6'], ['o', 'r', 'a', 'n', 'g', 'e']]⟩, ⟨[['a'], ['l', 'i']], [['G', 'N'], ['b', 'e']]⟩, ⟨[['u', 'k', 'o']], [['t', 'h', 'e', 'r', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "a-mphaka"), ("conjunct2", "ma-lalanje"), ("prefix", "a")] }

def all : List Datum := [s1, ex_1, ex_2, ex_3, ex_4, ex_5, s2_3a, s2_3b, s2_3c, ex_6, ex_7, ex_8, ex_9, ex_10, ex_11, ex_12, ex_13, ex_14, s3_2a, s3_2b, s4a, s4b, ex_15, ex_16, ex_17, ex_18, ex_19]

end Corbett1998.Examples
