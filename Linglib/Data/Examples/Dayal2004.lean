module

public import Linglib.Data.Examples.Schema

/-!
# `Dayal2004` — typed example data

Auto-generated from `Linglib/Data/Examples/Dayal2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Dayal2004.Examples`.
-/

@[expose] public section

namespace Dayal2004.Examples

def ex_6a_bare : Datum :=
  { id := "dayal2004_6a_bare"
    source := ⟨"dayal-2004", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dogs are widespread."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("number", "plural"), ("form", "bare")] }

def ex_6a_def : Datum :=
  { id := "dayal2004_6a_def"
    source := ⟨"dayal-2004", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The dogs are widespread."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("number", "plural"), ("form", "definite")] }

def ex_14a : Datum :=
  { id := "dayal2004_14a"
    source := ⟨"dayal-2004", "(14a)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "kutta aam janvar hai"
    glossedTokens := [("kutta", "dog"), ("aam", "common"), ("janvar", "animal"), ("hai", "is")]
    glossedWords := [⟨['k', 'u', 't', 't', 'a'], ['d', 'o', 'g'], [⟨['k', 'u', 't', 't', 'a'], ['d', 'o', 'g'], none⟩]⟩, ⟨['a', 'a', 'm'], ['c', 'o', 'm', 'm', 'o', 'n'], [⟨['a', 'a', 'm'], ['c', 'o', 'm', 'm', 'o', 'n'], none⟩]⟩, ⟨['j', 'a', 'n', 'v', 'a', 'r'], ['a', 'n', 'i', 'm', 'a', 'l'], [⟨['j', 'a', 'n', 'v', 'a', 'r'], ['a', 'n', 'i', 'm', 'a', 'l'], none⟩]⟩, ⟨['h', 'a', 'i'], ['i', 's'], [⟨['h', 'a', 'i'], ['i', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.2"), ("number", "singular"), ("form", "bare")] }

def ex_14b : Datum :=
  { id := "dayal2004_14b"
    source := ⟨"dayal-2004", "(14b)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "kutte yehaaN aam haiN"
    glossedTokens := [("kutte", "dogs"), ("yehaaN", "here"), ("aam", "common"), ("haiN", "are")]
    glossedWords := [⟨['k', 'u', 't', 't', 'e'], ['d', 'o', 'g', 's'], [⟨['k', 'u', 't', 't', 'e'], ['d', 'o', 'g', 's'], none⟩]⟩, ⟨['y', 'e', 'h', 'a', 'a', 'N'], ['h', 'e', 'r', 'e'], [⟨['y', 'e', 'h', 'a', 'a', 'N'], ['h', 'e', 'r', 'e'], none⟩]⟩, ⟨['a', 'a', 'm'], ['c', 'o', 'm', 'm', 'o', 'n'], [⟨['a', 'a', 'm'], ['c', 'o', 'm', 'm', 'o', 'n'], none⟩]⟩, ⟨['h', 'a', 'i', 'N'], ['a', 'r', 'e'], [⟨['h', 'a', 'i', 'N'], ['a', 'r', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.2"), ("number", "plural"), ("form", "bare")] }

def ex_15a : Datum :=
  { id := "dayal2004_15a"
    source := ⟨"dayal-2004", "(15a)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "chelovek proizoshel ot obez’jani"
    glossedTokens := [("chelovek", "man"), ("proizoshel", "evolved"), ("ot", "from"), ("obez’jani", "ape")]
    glossedWords := [⟨['c', 'h', 'e', 'l', 'o', 'v', 'e', 'k'], ['m', 'a', 'n'], [⟨['c', 'h', 'e', 'l', 'o', 'v', 'e', 'k'], ['m', 'a', 'n'], none⟩]⟩, ⟨['p', 'r', 'o', 'i', 'z', 'o', 's', 'h', 'e', 'l'], ['e', 'v', 'o', 'l', 'v', 'e', 'd'], [⟨['p', 'r', 'o', 'i', 'z', 'o', 's', 'h', 'e', 'l'], ['e', 'v', 'o', 'l', 'v', 'e', 'd'], none⟩]⟩, ⟨['o', 't'], ['f', 'r', 'o', 'm'], [⟨['o', 't'], ['f', 'r', 'o', 'm'], none⟩]⟩, ⟨['o', 'b', 'e', 'z', '’', 'j', 'a', 'n', 'i'], ['a', 'p', 'e'], [⟨['o', 'b', 'e', 'z', '’', 'j', 'a', 'n', 'i'], ['a', 'p', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.2"), ("number", "singular"), ("form", "bare")] }

def ex_15b : Datum :=
  { id := "dayal2004_15b"
    source := ⟨"dayal-2004", "(15b)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Ljudi proizoshli ot obez’jan"
    glossedTokens := [("Ljudi", "men"), ("proizoshli", "evolved"), ("ot", "from"), ("obez’jan", "apes")]
    glossedWords := [⟨['L', 'j', 'u', 'd', 'i'], ['m', 'e', 'n'], [⟨['L', 'j', 'u', 'd', 'i'], ['m', 'e', 'n'], none⟩]⟩, ⟨['p', 'r', 'o', 'i', 'z', 'o', 's', 'h', 'l', 'i'], ['e', 'v', 'o', 'l', 'v', 'e', 'd'], [⟨['p', 'r', 'o', 'i', 'z', 'o', 's', 'h', 'l', 'i'], ['e', 'v', 'o', 'l', 'v', 'e', 'd'], none⟩]⟩, ⟨['o', 't'], ['f', 'r', 'o', 'm'], [⟨['o', 't'], ['f', 'r', 'o', 'm'], none⟩]⟩, ⟨['o', 'b', 'e', 'z', '’', 'j', 'a', 'n'], ['a', 'p', 'e', 's'], [⟨['o', 'b', 'e', 'z', '’', 'j', 'a', 'n'], ['a', 'p', 'e', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.2"), ("number", "plural"), ("form", "bare")] }

def ex_16 : Datum :=
  { id := "dayal2004_16"
    source := ⟨"dayal-2004", "(16)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Gou juezhong le"
    glossedTokens := [("Gou", "dog"), ("juezhong", "extinct"), ("le", "Asp")]
    glossedWords := [⟨['G', 'o', 'u'], ['d', 'o', 'g'], [⟨['G', 'o', 'u'], ['d', 'o', 'g'], none⟩]⟩, ⟨['j', 'u', 'e', 'z', 'h', 'o', 'n', 'g'], ['e', 'x', 't', 'i', 'n', 'c', 't'], [⟨['j', 'u', 'e', 'z', 'h', 'o', 'n', 'g'], ['e', 'x', 't', 'i', 'n', 'c', 't'], none⟩]⟩, ⟨['l', 'e'], ['A', 's', 'p'], [⟨['l', 'e'], ['A', 's', 'p'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.2"), ("number", "general"), ("form", "bare")] }

def ex_46a_def : Datum :=
  { id := "dayal2004_46a_def"
    source := ⟨"dayal-2004", "(46a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The dinosaur is extinct."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("number", "singular"), ("form", "definite")] }

def ex_46a_bare : Datum :=
  { id := "dayal2004_46a_bare"
    source := ⟨"dayal-2004", "(46a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dinosaur is extinct."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("number", "singular"), ("form", "bare")] }

def ex_46b_def : Datum :=
  { id := "dayal2004_46b_def"
    source := ⟨"dayal-2004", "(46b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Babbage invented the computer."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("number", "singular"), ("form", "definite")] }

def ex_46b_bare : Datum :=
  { id := "dayal2004_46b_bare"
    source := ⟨"dayal-2004", "(46b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Babbage invented computer."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("number", "singular"), ("form", "bare")] }

def ex_46c_bare : Datum :=
  { id := "dayal2004_46c_bare"
    source := ⟨"dayal-2004", "(46c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Water is becoming scarce."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("number", "mass"), ("form", "bare")] }

def ex_46c_def : Datum :=
  { id := "dayal2004_46c_def"
    source := ⟨"dayal-2004", "(46c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The water is becoming scarce."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("number", "mass"), ("form", "definite")] }

def ex_46d_bare : Datum :=
  { id := "dayal2004_46d_bare"
    source := ⟨"dayal-2004", "(46d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Gold is rare."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("number", "mass"), ("form", "bare")] }

def ex_46d_def : Datum :=
  { id := "dayal2004_46d_def"
    source := ⟨"dayal-2004", "(46d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The gold is rare."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("number", "mass"), ("form", "definite")] }

def ex_78a_def : Datum :=
  { id := "dayal2004_78a_def"
    source := ⟨"dayal-2004", "(78a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Il cane é diffuso"
    glossedTokens := [("Il", "the"), ("cane", "dog"), ("é", "is"), ("diffuso", "widespread")]
    glossedWords := [⟨['I', 'l'], ['t', 'h', 'e'], [⟨['I', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['c', 'a', 'n', 'e'], ['d', 'o', 'g'], [⟨['c', 'a', 'n', 'e'], ['d', 'o', 'g'], none⟩]⟩, ⟨['é'], ['i', 's'], [⟨['é'], ['i', 's'], none⟩]⟩, ⟨['d', 'i', 'f', 'f', 'u', 's', 'o'], ['w', 'i', 'd', 'e', 's', 'p', 'r', 'e', 'a', 'd'], [⟨['d', 'i', 'f', 'f', 'u', 's', 'o'], ['w', 'i', 'd', 'e', 's', 'p', 'r', 'e', 'a', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.2"), ("number", "singular"), ("form", "definite")] }

def ex_78a_bare : Datum :=
  { id := "dayal2004_78a_bare"
    source := ⟨"dayal-2004", "(78a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "cane é diffuso"
    glossedTokens := [("cane", "dog"), ("é", "is"), ("diffuso", "widespread")]
    glossedWords := [⟨['c', 'a', 'n', 'e'], ['d', 'o', 'g'], [⟨['c', 'a', 'n', 'e'], ['d', 'o', 'g'], none⟩]⟩, ⟨['é'], ['i', 's'], [⟨['é'], ['i', 's'], none⟩]⟩, ⟨['d', 'i', 'f', 'f', 'u', 's', 'o'], ['w', 'i', 'd', 'e', 's', 'p', 'r', 'e', 'a', 'd'], [⟨['d', 'i', 'f', 'f', 'u', 's', 'o'], ['w', 'i', 'd', 'e', 's', 'p', 'r', 'e', 'a', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.2"), ("number", "singular"), ("form", "bare")] }

def ex_78b_def : Datum :=
  { id := "dayal2004_78b_def"
    source := ⟨"dayal-2004", "(78b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "I cani sono diffusi"
    glossedTokens := [("I", "the"), ("cani", "dogs"), ("sono", "are"), ("diffusi", "widespread")]
    glossedWords := [⟨['I'], ['t', 'h', 'e'], [⟨['I'], ['t', 'h', 'e'], none⟩]⟩, ⟨['c', 'a', 'n', 'i'], ['d', 'o', 'g', 's'], [⟨['c', 'a', 'n', 'i'], ['d', 'o', 'g', 's'], none⟩]⟩, ⟨['s', 'o', 'n', 'o'], ['a', 'r', 'e'], [⟨['s', 'o', 'n', 'o'], ['a', 'r', 'e'], none⟩]⟩, ⟨['d', 'i', 'f', 'f', 'u', 's', 'i'], ['w', 'i', 'd', 'e', 's', 'p', 'r', 'e', 'a', 'd'], [⟨['d', 'i', 'f', 'f', 'u', 's', 'i'], ['w', 'i', 'd', 'e', 's', 'p', 'r', 'e', 'a', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.2"), ("number", "plural"), ("form", "definite")] }

def ex_78b_bare : Datum :=
  { id := "dayal2004_78b_bare"
    source := ⟨"dayal-2004", "(78b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "cani sono diffusi"
    glossedTokens := [("cani", "dogs"), ("sono", "are"), ("diffusi", "widespread")]
    glossedWords := [⟨['c', 'a', 'n', 'i'], ['d', 'o', 'g', 's'], [⟨['c', 'a', 'n', 'i'], ['d', 'o', 'g', 's'], none⟩]⟩, ⟨['s', 'o', 'n', 'o'], ['a', 'r', 'e'], [⟨['s', 'o', 'n', 'o'], ['a', 'r', 'e'], none⟩]⟩, ⟨['d', 'i', 'f', 'f', 'u', 's', 'i'], ['w', 'i', 'd', 'e', 's', 'p', 'r', 'e', 'a', 'd'], [⟨['d', 'i', 'f', 'f', 'u', 's', 'i'], ['w', 'i', 'd', 'e', 's', 'p', 'r', 'e', 'a', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.2"), ("number", "plural"), ("form", "bare")] }

def ex_86a_def : Datum :=
  { id := "dayal2004_86a_def"
    source := ⟨"dayal-2004", "(86a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Pandabären sind vom Aussterben bedroht."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.3"), ("number", "plural"), ("form", "definite")] }

def ex_86a_bare : Datum :=
  { id := "dayal2004_86a_bare"
    source := ⟨"dayal-2004", "(86a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Pandabären sind vom Aussterben bedroht."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.3"), ("number", "plural"), ("form", "bare")] }

def ex_86b_def : Datum :=
  { id := "dayal2004_86b_def"
    source := ⟨"dayal-2004", "(86b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Das Gold steigt im Preis."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.3"), ("number", "mass"), ("form", "definite")] }

def ex_86b_bare : Datum :=
  { id := "dayal2004_86b_bare"
    source := ⟨"dayal-2004", "(86b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Gold steigt im Preis."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.3"), ("number", "mass"), ("form", "bare")] }

def ex_87a_def : Datum :=
  { id := "dayal2004_87a_def"
    source := ⟨"dayal-2004", "(87a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Pandabär ist vom Aussterben bedroht."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.3"), ("number", "singular"), ("form", "definite")] }

def ex_87a_bare : Datum :=
  { id := "dayal2004_87a_bare"
    source := ⟨"dayal-2004", "(87a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Pandabär ist vom Aussterben bedroht."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.3"), ("number", "singular"), ("form", "bare")] }

def all : List Datum := [ex_6a_bare, ex_6a_def, ex_14a, ex_14b, ex_15a, ex_15b, ex_16, ex_46a_def, ex_46a_bare, ex_46b_def, ex_46b_bare, ex_46c_bare, ex_46c_def, ex_46d_bare, ex_46d_def, ex_78a_def, ex_78a_bare, ex_78b_def, ex_78b_bare, ex_86a_def, ex_86a_bare, ex_86b_def, ex_86b_bare, ex_87a_def, ex_87a_bare]

end Dayal2004.Examples
