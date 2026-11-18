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
    contrasts := [("I is parked on the hill", .ungrammatical)]
    readings := []
    paperFeatures := [] }

def ex_1 : Datum :=
  { id := "corbett1998_1"
    source := ⟨"corbett-1998", "(1)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "nov-yj avtomobil'"
    glossedTokens := [("nov-yj", "new-SG.MASC"), ("avtomobil'", "car")]
    glossedWords := [⟨['n', 'o', 'v', '-', 'y', 'j'], ['n', 'e', 'w', '-', 'S', 'G', '.', 'M', 'A', 'S', 'C'], [⟨['n', 'o', 'v'], ['n', 'e', 'w'], none⟩, ⟨['y', 'j'], ['S', 'G', '.', 'M', 'A', 'S', 'C'], some '-'⟩]⟩, ⟨['a', 'v', 't', 'o', 'm', 'o', 'b', 'i', 'l', '\''], ['c', 'a', 'r'], [⟨['a', 'v', 't', 'o', 'm', 'o', 'b', 'i', 'l', '\''], ['c', 'a', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("gender", "masc"), ("number", "sg"), ("ending", "yj"), ("case", "nom")] }

def ex_2 : Datum :=
  { id := "corbett1998_2"
    source := ⟨"corbett-1998", "(2)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "nov-aja mašina"
    glossedTokens := [("nov-aja", "new-SG.FEM"), ("mašina", "car")]
    glossedWords := [⟨['n', 'o', 'v', '-', 'a', 'j', 'a'], ['n', 'e', 'w', '-', 'S', 'G', '.', 'F', 'E', 'M'], [⟨['n', 'o', 'v'], ['n', 'e', 'w'], none⟩, ⟨['a', 'j', 'a'], ['S', 'G', '.', 'F', 'E', 'M'], some '-'⟩]⟩, ⟨['m', 'a', 'š', 'i', 'n', 'a'], ['c', 'a', 'r'], [⟨['m', 'a', 'š', 'i', 'n', 'a'], ['c', 'a', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("gender", "fem"), ("number", "sg"), ("ending", "aja"), ("case", "nom")] }

def ex_3 : Datum :=
  { id := "corbett1998_3"
    source := ⟨"corbett-1998", "(3)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "nov-oe taksi"
    glossedTokens := [("nov-oe", "new-SG.NEUT"), ("taksi", "taxi")]
    glossedWords := [⟨['n', 'o', 'v', '-', 'o', 'e'], ['n', 'e', 'w', '-', 'S', 'G', '.', 'N', 'E', 'U', 'T'], [⟨['n', 'o', 'v'], ['n', 'e', 'w'], none⟩, ⟨['o', 'e'], ['S', 'G', '.', 'N', 'E', 'U', 'T'], some '-'⟩]⟩, ⟨['t', 'a', 'k', 's', 'i'], ['t', 'a', 'x', 'i'], [⟨['t', 'a', 'k', 's', 'i'], ['t', 'a', 'x', 'i'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("gender", "neut"), ("number", "sg"), ("ending", "oe"), ("case", "nom")] }

def ex_4 : Datum :=
  { id := "corbett1998_4"
    source := ⟨"corbett-1998", "(4)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "nov-ye avtomobil-i"
    glossedTokens := [("nov-ye", "new-PL"), ("avtomobil-i", "car-PL")]
    glossedWords := [⟨['n', 'o', 'v', '-', 'y', 'e'], ['n', 'e', 'w', '-', 'P', 'L'], [⟨['n', 'o', 'v'], ['n', 'e', 'w'], none⟩, ⟨['y', 'e'], ['P', 'L'], some '-'⟩]⟩, ⟨['a', 'v', 't', 'o', 'm', 'o', 'b', 'i', 'l', '-', 'i'], ['c', 'a', 'r', '-', 'P', 'L'], [⟨['a', 'v', 't', 'o', 'm', 'o', 'b', 'i', 'l'], ['c', 'a', 'r'], none⟩, ⟨['i'], ['P', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("gender", "masc"), ("number", "pl"), ("ending", "ye"), ("case", "nom")] }

def ex_5 : Datum :=
  { id := "corbett1998_5"
    source := ⟨"corbett-1998", "(5)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "v nov-om avtomobil-e"
    glossedTokens := [("v", "in"), ("nov-om", "new-SG.LOC.MASC"), ("avtomobil-e", "car-SG.LOC")]
    glossedWords := [⟨['v'], ['i', 'n'], [⟨['v'], ['i', 'n'], none⟩]⟩, ⟨['n', 'o', 'v', '-', 'o', 'm'], ['n', 'e', 'w', '-', 'S', 'G', '.', 'L', 'O', 'C', '.', 'M', 'A', 'S', 'C'], [⟨['n', 'o', 'v'], ['n', 'e', 'w'], none⟩, ⟨['o', 'm'], ['S', 'G', '.', 'L', 'O', 'C', '.', 'M', 'A', 'S', 'C'], some '-'⟩]⟩, ⟨['a', 'v', 't', 'o', 'm', 'o', 'b', 'i', 'l', '-', 'e'], ['c', 'a', 'r', '-', 'S', 'G', '.', 'L', 'O', 'C'], [⟨['a', 'v', 't', 'o', 'm', 'o', 'b', 'i', 'l'], ['c', 'a', 'r'], none⟩, ⟨['e'], ['S', 'G', '.', 'L', 'O', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
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
    contrasts := []
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
    contrasts := []
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
    contrasts := []
    readings := []
    paperFeatures := [("person", "3"), ("number", "sg"), ("ending", "et")] }

def ex_6 : Datum :=
  { id := "corbett1998_6"
    source := ⟨"corbett-1998", "(6)"⟩
    reportedIn := none
    language := "nucl1622"
    primaryText := "e-pe anem e-pe akek ka"
    glossedTokens := [("e-pe", "I-the"), ("anem", "man"), ("e-pe", "I-the"), ("akek", "light.I"), ("ka", "is")]
    glossedWords := [⟨['e', '-', 'p', 'e'], ['I', '-', 't', 'h', 'e'], [⟨['e'], ['I'], none⟩, ⟨['p', 'e'], ['t', 'h', 'e'], some '-'⟩]⟩, ⟨['a', 'n', 'e', 'm'], ['m', 'a', 'n'], [⟨['a', 'n', 'e', 'm'], ['m', 'a', 'n'], none⟩]⟩, ⟨['e', '-', 'p', 'e'], ['I', '-', 't', 'h', 'e'], [⟨['e'], ['I'], none⟩, ⟨['p', 'e'], ['t', 'h', 'e'], some '-'⟩]⟩, ⟨['a', 'k', 'e', 'k'], ['l', 'i', 'g', 'h', 't', '.', 'I'], [⟨['a', 'k', 'e', 'k'], ['l', 'i', 'g', 'h', 't', '.', 'I'], none⟩]⟩, ⟨['k', 'a'], ['i', 's'], [⟨['k', 'a'], ['i', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("gender", "I"), ("adjective", "akek"), ("demonstrative", "e-pe")] }

def ex_7 : Datum :=
  { id := "corbett1998_7"
    source := ⟨"corbett-1998", "(7)"⟩
    reportedIn := none
    language := "nucl1622"
    primaryText := "u-pe anum u-pe akuk ka"
    glossedTokens := [("u-pe", "II-the"), ("anum", "woman"), ("u-pe", "II-the"), ("akuk", "light.II"), ("ka", "is")]
    glossedWords := [⟨['u', '-', 'p', 'e'], ['I', 'I', '-', 't', 'h', 'e'], [⟨['u'], ['I', 'I'], none⟩, ⟨['p', 'e'], ['t', 'h', 'e'], some '-'⟩]⟩, ⟨['a', 'n', 'u', 'm'], ['w', 'o', 'm', 'a', 'n'], [⟨['a', 'n', 'u', 'm'], ['w', 'o', 'm', 'a', 'n'], none⟩]⟩, ⟨['u', '-', 'p', 'e'], ['I', 'I', '-', 't', 'h', 'e'], [⟨['u'], ['I', 'I'], none⟩, ⟨['p', 'e'], ['t', 'h', 'e'], some '-'⟩]⟩, ⟨['a', 'k', 'u', 'k'], ['l', 'i', 'g', 'h', 't', '.', 'I', 'I'], [⟨['a', 'k', 'u', 'k'], ['l', 'i', 'g', 'h', 't', '.', 'I', 'I'], none⟩]⟩, ⟨['k', 'a'], ['i', 's'], [⟨['k', 'a'], ['i', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("gender", "II"), ("adjective", "akuk"), ("demonstrative", "u-pe")] }

def ex_8 : Datum :=
  { id := "corbett1998_8"
    source := ⟨"corbett-1998", "(8)"⟩
    reportedIn := none
    language := "nucl1622"
    primaryText := "e-pe de e-pe akak ka"
    glossedTokens := [("e-pe", "III-the"), ("de", "wood"), ("e-pe", "III-the"), ("akak", "light.III"), ("ka", "is")]
    glossedWords := [⟨['e', '-', 'p', 'e'], ['I', 'I', 'I', '-', 't', 'h', 'e'], [⟨['e'], ['I', 'I', 'I'], none⟩, ⟨['p', 'e'], ['t', 'h', 'e'], some '-'⟩]⟩, ⟨['d', 'e'], ['w', 'o', 'o', 'd'], [⟨['d', 'e'], ['w', 'o', 'o', 'd'], none⟩]⟩, ⟨['e', '-', 'p', 'e'], ['I', 'I', 'I', '-', 't', 'h', 'e'], [⟨['e'], ['I', 'I', 'I'], none⟩, ⟨['p', 'e'], ['t', 'h', 'e'], some '-'⟩]⟩, ⟨['a', 'k', 'a', 'k'], ['l', 'i', 'g', 'h', 't', '.', 'I', 'I', 'I'], [⟨['a', 'k', 'a', 'k'], ['l', 'i', 'g', 'h', 't', '.', 'I', 'I', 'I'], none⟩]⟩, ⟨['k', 'a'], ['i', 's'], [⟨['k', 'a'], ['i', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("gender", "III"), ("adjective", "akak"), ("demonstrative", "e-pe")] }

def ex_9 : Datum :=
  { id := "corbett1998_9"
    source := ⟨"corbett-1998", "(9)"⟩
    reportedIn := none
    language := "nucl1622"
    primaryText := "i-pe behaw i-pe akik ka"
    glossedTokens := [("i-pe", "IV-the"), ("behaw", "pole"), ("i-pe", "IV-the"), ("akik", "light.IV"), ("ka", "is")]
    glossedWords := [⟨['i', '-', 'p', 'e'], ['I', 'V', '-', 't', 'h', 'e'], [⟨['i'], ['I', 'V'], none⟩, ⟨['p', 'e'], ['t', 'h', 'e'], some '-'⟩]⟩, ⟨['b', 'e', 'h', 'a', 'w'], ['p', 'o', 'l', 'e'], [⟨['b', 'e', 'h', 'a', 'w'], ['p', 'o', 'l', 'e'], none⟩]⟩, ⟨['i', '-', 'p', 'e'], ['I', 'V', '-', 't', 'h', 'e'], [⟨['i'], ['I', 'V'], none⟩, ⟨['p', 'e'], ['t', 'h', 'e'], some '-'⟩]⟩, ⟨['a', 'k', 'i', 'k'], ['l', 'i', 'g', 'h', 't', '.', 'I', 'V'], [⟨['a', 'k', 'i', 'k'], ['l', 'i', 'g', 'h', 't', '.', 'I', 'V'], none⟩]⟩, ⟨['k', 'a'], ['i', 's'], [⟨['k', 'a'], ['i', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("gender", "IV"), ("adjective", "akik"), ("demonstrative", "i-pe")] }

def ex_10 : Datum :=
  { id := "corbett1998_10"
    source := ⟨"corbett-1998", "(10)"⟩
    reportedIn := none
    language := "arch1244"
    primaryText := "d-as̄-a-r-ej-r-u-t̄u-r x̌̄anna"
    glossedTokens := [("d-as̄-a-r-ej-r-u-t̄u-r", "II-of.me-SELF-II-SUFFIX-II-SUFFIX-ADJ-II"), ("x̌̄anna", "wife")]
    glossedWords := [⟨['d', '-', 'a', 's', '̄', '-', 'a', '-', 'r', '-', 'e', 'j', '-', 'r', '-', 'u', '-', 't', '̄', 'u', '-', 'r'], ['I', 'I', '-', 'o', 'f', '.', 'm', 'e', '-', 'S', 'E', 'L', 'F', '-', 'I', 'I', '-', 'S', 'U', 'F', 'F', 'I', 'X', '-', 'I', 'I', '-', 'S', 'U', 'F', 'F', 'I', 'X', '-', 'A', 'D', 'J', '-', 'I', 'I'], [⟨['d'], ['I', 'I'], none⟩, ⟨['a', 's', '̄'], ['o', 'f', '.', 'm', 'e'], some '-'⟩, ⟨['a'], ['S', 'E', 'L', 'F'], some '-'⟩, ⟨['r'], ['I', 'I'], some '-'⟩, ⟨['e', 'j'], ['S', 'U', 'F', 'F', 'I', 'X'], some '-'⟩, ⟨['r'], ['I', 'I'], some '-'⟩, ⟨['u'], ['S', 'U', 'F', 'F', 'I', 'X'], some '-'⟩, ⟨['t', '̄', 'u'], ['A', 'D', 'J'], some '-'⟩, ⟨['r'], ['I', 'I'], some '-'⟩]⟩, ⟨['x', '̌', '̄', 'a', 'n', 'n', 'a'], ['w', 'i', 'f', 'e'], [⟨['x', '̌', '̄', 'a', 'n', 'n', 'a'], ['w', 'i', 'f', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("gender", "II"), ("slots", "4")] }

def ex_11 : Datum :=
  { id := "corbett1998_11"
    source := ⟨"corbett-1998", "(11)"⟩
    reportedIn := none
    language := "soma1255"
    primaryText := "ìnan-kii baa y-imid"
    glossedTokens := [("ìnan-kii", "boy-the.SG.MASC"), ("baa", "FOCUS.MARKER"), ("y-imid", "SG.MASC-came")]
    glossedWords := [⟨['ì', 'n', 'a', 'n', '-', 'k', 'i', 'i'], ['b', 'o', 'y', '-', 't', 'h', 'e', '.', 'S', 'G', '.', 'M', 'A', 'S', 'C'], [⟨['ì', 'n', 'a', 'n'], ['b', 'o', 'y'], none⟩, ⟨['k', 'i', 'i'], ['t', 'h', 'e', '.', 'S', 'G', '.', 'M', 'A', 'S', 'C'], some '-'⟩]⟩, ⟨['b', 'a', 'a'], ['F', 'O', 'C', 'U', 'S', '.', 'M', 'A', 'R', 'K', 'E', 'R'], [⟨['b', 'a', 'a'], ['F', 'O', 'C', 'U', 'S', '.', 'M', 'A', 'R', 'K', 'E', 'R'], none⟩]⟩, ⟨['y', '-', 'i', 'm', 'i', 'd'], ['S', 'G', '.', 'M', 'A', 'S', 'C', '-', 'c', 'a', 'm', 'e'], [⟨['y'], ['S', 'G', '.', 'M', 'A', 'S', 'C'], none⟩, ⟨['i', 'm', 'i', 'd'], ['c', 'a', 'm', 'e'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("noun", "ìnan"), ("number", "sg"), ("article", "kii"), ("verb", "y")] }

def ex_12 : Datum :=
  { id := "corbett1998_12"
    source := ⟨"corbett-1998", "(12)"⟩
    reportedIn := none
    language := "soma1255"
    primaryText := "inán-tii baa t-imid"
    glossedTokens := [("inán-tii", "girl-the.SG.FEM"), ("baa", "FOCUS.MARKER"), ("t-imid", "SG.FEM-came")]
    glossedWords := [⟨['i', 'n', 'á', 'n', '-', 't', 'i', 'i'], ['g', 'i', 'r', 'l', '-', 't', 'h', 'e', '.', 'S', 'G', '.', 'F', 'E', 'M'], [⟨['i', 'n', 'á', 'n'], ['g', 'i', 'r', 'l'], none⟩, ⟨['t', 'i', 'i'], ['t', 'h', 'e', '.', 'S', 'G', '.', 'F', 'E', 'M'], some '-'⟩]⟩, ⟨['b', 'a', 'a'], ['F', 'O', 'C', 'U', 'S', '.', 'M', 'A', 'R', 'K', 'E', 'R'], [⟨['b', 'a', 'a'], ['F', 'O', 'C', 'U', 'S', '.', 'M', 'A', 'R', 'K', 'E', 'R'], none⟩]⟩, ⟨['t', '-', 'i', 'm', 'i', 'd'], ['S', 'G', '.', 'F', 'E', 'M', '-', 'c', 'a', 'm', 'e'], [⟨['t'], ['S', 'G', '.', 'F', 'E', 'M'], none⟩, ⟨['i', 'm', 'i', 'd'], ['c', 'a', 'm', 'e'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("noun", "inán"), ("number", "sg"), ("article", "tii"), ("verb", "t")] }

def ex_13 : Datum :=
  { id := "corbett1998_13"
    source := ⟨"corbett-1998", "(13)"⟩
    reportedIn := none
    language := "soma1255"
    primaryText := "inammá-dii baa y-imid"
    glossedTokens := [("inammá-dii", "boys-the.PL.MASC"), ("baa", "FOCUS.MARKER"), ("y-imid", "PL-came")]
    glossedWords := [⟨['i', 'n', 'a', 'm', 'm', 'á', '-', 'd', 'i', 'i'], ['b', 'o', 'y', 's', '-', 't', 'h', 'e', '.', 'P', 'L', '.', 'M', 'A', 'S', 'C'], [⟨['i', 'n', 'a', 'm', 'm', 'á'], ['b', 'o', 'y', 's'], none⟩, ⟨['d', 'i', 'i'], ['t', 'h', 'e', '.', 'P', 'L', '.', 'M', 'A', 'S', 'C'], some '-'⟩]⟩, ⟨['b', 'a', 'a'], ['F', 'O', 'C', 'U', 'S', '.', 'M', 'A', 'R', 'K', 'E', 'R'], [⟨['b', 'a', 'a'], ['F', 'O', 'C', 'U', 'S', '.', 'M', 'A', 'R', 'K', 'E', 'R'], none⟩]⟩, ⟨['y', '-', 'i', 'm', 'i', 'd'], ['P', 'L', '-', 'c', 'a', 'm', 'e'], [⟨['y'], ['P', 'L'], none⟩, ⟨['i', 'm', 'i', 'd'], ['c', 'a', 'm', 'e'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("noun", "ìnan"), ("number", "pl"), ("article", "tii"), ("verb", "y")] }

def ex_14 : Datum :=
  { id := "corbett1998_14"
    source := ⟨"corbett-1998", "(14)"⟩
    reportedIn := none
    language := "soma1255"
    primaryText := "ináma-hii baa y-imid"
    glossedTokens := [("ináma-hii", "girls-the.PL.FEM"), ("baa", "FOCUS.MARKER"), ("y-imid", "PL-came")]
    glossedWords := [⟨['i', 'n', 'á', 'm', 'a', '-', 'h', 'i', 'i'], ['g', 'i', 'r', 'l', 's', '-', 't', 'h', 'e', '.', 'P', 'L', '.', 'F', 'E', 'M'], [⟨['i', 'n', 'á', 'm', 'a'], ['g', 'i', 'r', 'l', 's'], none⟩, ⟨['h', 'i', 'i'], ['t', 'h', 'e', '.', 'P', 'L', '.', 'F', 'E', 'M'], some '-'⟩]⟩, ⟨['b', 'a', 'a'], ['F', 'O', 'C', 'U', 'S', '.', 'M', 'A', 'R', 'K', 'E', 'R'], [⟨['b', 'a', 'a'], ['F', 'O', 'C', 'U', 'S', '.', 'M', 'A', 'R', 'K', 'E', 'R'], none⟩]⟩, ⟨['y', '-', 'i', 'm', 'i', 'd'], ['P', 'L', '-', 'c', 'a', 'm', 'e'], [⟨['y'], ['P', 'L'], none⟩, ⟨['i', 'm', 'i', 'd'], ['c', 'a', 'm', 'e'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
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
    contrasts := []
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
    contrasts := []
    readings := []
    paperFeatures := [("noun", "nin"), ("number", "pl"), ("article", "kii")] }

def s4a : Datum :=
  { id := "corbett1998_s4a"
    source := ⟨"corbett-1998", "§4"⟩
    reportedIn := none
    language := "lakk1252"
    primaryText := "q̄at-lu-wu-n-m-aj"
    glossedTokens := [("q̄at-lu-wu-n-m-aj", "house-OBLIQUE-IN-LATIVE-III-ALLATIVE")]
    glossedWords := [⟨['q', '̄', 'a', 't', '-', 'l', 'u', '-', 'w', 'u', '-', 'n', '-', 'm', '-', 'a', 'j'], ['h', 'o', 'u', 's', 'e', '-', 'O', 'B', 'L', 'I', 'Q', 'U', 'E', '-', 'I', 'N', '-', 'L', 'A', 'T', 'I', 'V', 'E', '-', 'I', 'I', 'I', '-', 'A', 'L', 'L', 'A', 'T', 'I', 'V', 'E'], [⟨['q', '̄', 'a', 't'], ['h', 'o', 'u', 's', 'e'], none⟩, ⟨['l', 'u'], ['O', 'B', 'L', 'I', 'Q', 'U', 'E'], some '-'⟩, ⟨['w', 'u'], ['I', 'N'], some '-'⟩, ⟨['n'], ['L', 'A', 'T', 'I', 'V', 'E'], some '-'⟩, ⟨['m'], ['I', 'I', 'I'], some '-'⟩, ⟨['a', 'j'], ['A', 'L', 'L', 'A', 'T', 'I', 'V', 'E'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "caseMarkedNoun"), ("gender", "III")] }

def s4b : Datum :=
  { id := "corbett1998_s4b"
    source := ⟨"corbett-1998", "§4"⟩
    reportedIn := none
    language := "darg1241"
    primaryText := "bidra-li-če-b"
    glossedTokens := [("bidra-li-če-b", "bucket-OBLIQUE-SUPER-III")]
    glossedWords := [⟨['b', 'i', 'd', 'r', 'a', '-', 'l', 'i', '-', 'č', 'e', '-', 'b'], ['b', 'u', 'c', 'k', 'e', 't', '-', 'O', 'B', 'L', 'I', 'Q', 'U', 'E', '-', 'S', 'U', 'P', 'E', 'R', '-', 'I', 'I', 'I'], [⟨['b', 'i', 'd', 'r', 'a'], ['b', 'u', 'c', 'k', 'e', 't'], none⟩, ⟨['l', 'i'], ['O', 'B', 'L', 'I', 'Q', 'U', 'E'], some '-'⟩, ⟨['č', 'e'], ['S', 'U', 'P', 'E', 'R'], some '-'⟩, ⟨['b'], ['I', 'I', 'I'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "caseMarkedNoun"), ("gender", "III")] }

def ex_15 : Datum :=
  { id := "corbett1998_15"
    source := ⟨"corbett-1998", "(15)"⟩
    reportedIn := none
    language := "arch1244"
    primaryText := "d-ez buwa ǩ'anši d-i"
    glossedTokens := [("d-ez", "II-me.DAT"), ("buwa", "mother"), ("ǩ'anši", "like"), ("d-i", "II-is")]
    glossedWords := [⟨['d', '-', 'e', 'z'], ['I', 'I', '-', 'm', 'e', '.', 'D', 'A', 'T'], [⟨['d'], ['I', 'I'], none⟩, ⟨['e', 'z'], ['m', 'e', '.', 'D', 'A', 'T'], some '-'⟩]⟩, ⟨['b', 'u', 'w', 'a'], ['m', 'o', 't', 'h', 'e', 'r'], [⟨['b', 'u', 'w', 'a'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩]⟩, ⟨['ǩ', '\'', 'a', 'n', 'š', 'i'], ['l', 'i', 'k', 'e'], [⟨['ǩ', '\'', 'a', 'n', 'š', 'i'], ['l', 'i', 'k', 'e'], none⟩]⟩, ⟨['d', '-', 'i'], ['I', 'I', '-', 'i', 's'], [⟨['d'], ['I', 'I'], none⟩, ⟨['i'], ['i', 's'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "pronoun"), ("gender", "II")] }

def ex_16 : Datum :=
  { id := "corbett1998_16"
    source := ⟨"corbett-1998", "(16)"⟩
    reportedIn := none
    language := "arch1244"
    primaryText := "b-ez dogi ǩ'anši b-i"
    glossedTokens := [("b-ez", "III-me"), ("dogi", "donkey"), ("ǩ'anši", "like"), ("b-i", "III-is")]
    glossedWords := [⟨['b', '-', 'e', 'z'], ['I', 'I', 'I', '-', 'm', 'e'], [⟨['b'], ['I', 'I', 'I'], none⟩, ⟨['e', 'z'], ['m', 'e'], some '-'⟩]⟩, ⟨['d', 'o', 'g', 'i'], ['d', 'o', 'n', 'k', 'e', 'y'], [⟨['d', 'o', 'g', 'i'], ['d', 'o', 'n', 'k', 'e', 'y'], none⟩]⟩, ⟨['ǩ', '\'', 'a', 'n', 'š', 'i'], ['l', 'i', 'k', 'e'], [⟨['ǩ', '\'', 'a', 'n', 'š', 'i'], ['l', 'i', 'k', 'e'], none⟩]⟩, ⟨['b', '-', 'i'], ['I', 'I', 'I', '-', 'i', 's'], [⟨['b'], ['I', 'I', 'I'], none⟩, ⟨['i'], ['i', 's'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "pronoun"), ("gender", "III")] }

def ex_17 : Datum :=
  { id := "corbett1998_17"
    source := ⟨"corbett-1998", "(17)"⟩
    reportedIn := none
    language := "uppe1395"
    primaryText := "wón je pisał"
    glossedTokens := [("wón", "he"), ("je", "is.3SG"), ("pisał", "written.SG.MASC")]
    glossedWords := [⟨['w', 'ó', 'n'], ['h', 'e'], [⟨['w', 'ó', 'n'], ['h', 'e'], none⟩]⟩, ⟨['j', 'e'], ['i', 's', '.', '3', 'S', 'G'], [⟨['j', 'e'], ['i', 's', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['p', 'i', 's', 'a', 'ł'], ['w', 'r', 'i', 't', 't', 'e', 'n', '.', 'S', 'G', '.', 'M', 'A', 'S', 'C'], [⟨['p', 'i', 's', 'a', 'ł'], ['w', 'r', 'i', 't', 't', 'e', 'n', '.', 'S', 'G', '.', 'M', 'A', 'S', 'C'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("finiteVerb", "number,person"), ("participle", "number,gender")] }

def ex_18 : Datum :=
  { id := "corbett1998_18"
    source := ⟨"corbett-1998", "(18)"⟩
    reportedIn := none
    language := "nyan1308"
    primaryText := "ma-lalanje ndi ma-samba a-kubvunda"
    glossedTokens := [("ma-lalanje", "6-orange"), ("ndi", "and"), ("ma-samba", "6-leaf"), ("a-kubvunda", "6-be.rotting")]
    glossedWords := [⟨['m', 'a', '-', 'l', 'a', 'l', 'a', 'n', 'j', 'e'], ['6', '-', 'o', 'r', 'a', 'n', 'g', 'e'], [⟨['m', 'a'], ['6'], none⟩, ⟨['l', 'a', 'l', 'a', 'n', 'j', 'e'], ['o', 'r', 'a', 'n', 'g', 'e'], some '-'⟩]⟩, ⟨['n', 'd', 'i'], ['a', 'n', 'd'], [⟨['n', 'd', 'i'], ['a', 'n', 'd'], none⟩]⟩, ⟨['m', 'a', '-', 's', 'a', 'm', 'b', 'a'], ['6', '-', 'l', 'e', 'a', 'f'], [⟨['m', 'a'], ['6'], none⟩, ⟨['s', 'a', 'm', 'b', 'a'], ['l', 'e', 'a', 'f'], some '-'⟩]⟩, ⟨['a', '-', 'k', 'u', 'b', 'v', 'u', 'n', 'd', 'a'], ['6', '-', 'b', 'e', '.', 'r', 'o', 't', 't', 'i', 'n', 'g'], [⟨['a'], ['6'], none⟩, ⟨['k', 'u', 'b', 'v', 'u', 'n', 'd', 'a'], ['b', 'e', '.', 'r', 'o', 't', 't', 'i', 'n', 'g'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("conjunct1", "ma-lalanje"), ("conjunct2", "ma-samba"), ("prefix", "a")] }

def ex_19 : Datum :=
  { id := "corbett1998_19"
    source := ⟨"corbett-1998", "(19)"⟩
    reportedIn := none
    language := "nyan1308"
    primaryText := "a-mphaka ndi ma-lalanje a-li uko"
    glossedTokens := [("a-mphaka", "2-cat"), ("ndi", "and"), ("ma-lalanje", "6-orange"), ("a-li", "GN-be"), ("uko", "there")]
    glossedWords := [⟨['a', '-', 'm', 'p', 'h', 'a', 'k', 'a'], ['2', '-', 'c', 'a', 't'], [⟨['a'], ['2'], none⟩, ⟨['m', 'p', 'h', 'a', 'k', 'a'], ['c', 'a', 't'], some '-'⟩]⟩, ⟨['n', 'd', 'i'], ['a', 'n', 'd'], [⟨['n', 'd', 'i'], ['a', 'n', 'd'], none⟩]⟩, ⟨['m', 'a', '-', 'l', 'a', 'l', 'a', 'n', 'j', 'e'], ['6', '-', 'o', 'r', 'a', 'n', 'g', 'e'], [⟨['m', 'a'], ['6'], none⟩, ⟨['l', 'a', 'l', 'a', 'n', 'j', 'e'], ['o', 'r', 'a', 'n', 'g', 'e'], some '-'⟩]⟩, ⟨['a', '-', 'l', 'i'], ['G', 'N', '-', 'b', 'e'], [⟨['a'], ['G', 'N'], none⟩, ⟨['l', 'i'], ['b', 'e'], some '-'⟩]⟩, ⟨['u', 'k', 'o'], ['t', 'h', 'e', 'r', 'e'], [⟨['u', 'k', 'o'], ['t', 'h', 'e', 'r', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("conjunct1", "a-mphaka"), ("conjunct2", "ma-lalanje"), ("prefix", "a")] }

def all : List Datum := [s1, ex_1, ex_2, ex_3, ex_4, ex_5, s2_3a, s2_3b, s2_3c, ex_6, ex_7, ex_8, ex_9, ex_10, ex_11, ex_12, ex_13, ex_14, s3_2a, s3_2b, s4a, s4b, ex_15, ex_16, ex_17, ex_18, ex_19]

end Corbett1998.Examples
