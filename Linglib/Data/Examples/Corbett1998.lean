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
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "a-mphaka"), ("conjunct2", "ma-lalanje"), ("prefix", "a")] }

def all : List Datum := [s1, ex_1, ex_2, ex_3, ex_4, ex_5, s2_3a, s2_3b, s2_3c, ex_6, ex_7, ex_8, ex_9, ex_10, ex_11, ex_12, ex_13, ex_14, s3_2a, s3_2b, s4a, s4b, ex_15, ex_16, ex_17, ex_18, ex_19]

end Corbett1998.Examples
