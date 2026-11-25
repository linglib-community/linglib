module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `QingEtAl2025` — typed example data

Auto-generated from `Linglib/Data/Examples/QingEtAl2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace QingEtAl2025.Examples`.
-/

@[expose] public section

namespace QingEtAl2025.Examples

def en_6 : Datum :=
  { id := "qingetal2025_en_6"
    source := ⟨"qing-uegaki-2025", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John hopes which student will sing."
    glossedTokens := [("John", ""), ("hopes", ""), ("which", ""), ("student", ""), ("will", ""), ("sing", "")]
    glossedWords := [⟨['J', 'o', 'h', 'n'], [], [⟨['J', 'o', 'h', 'n'], [], none⟩]⟩, ⟨['h', 'o', 'p', 'e', 's'], [], [⟨['h', 'o', 'p', 'e', 's'], [], none⟩]⟩, ⟨['w', 'h', 'i', 'c', 'h'], [], [⟨['w', 'h', 'i', 'c', 'h'], [], none⟩]⟩, ⟨['s', 't', 'u', 'd', 'e', 'n', 't'], [], [⟨['s', 't', 'u', 'd', 'e', 'n', 't'], [], none⟩]⟩, ⟨['w', 'i', 'l', 'l'], [], [⟨['w', 'i', 'l', 'l'], [], none⟩]⟩, ⟨['s', 'i', 'n', 'g'], [], [⟨['s', 'i', 'n', 'g'], [], none⟩]⟩]
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨1, 1, "predicate", some "hope"⟩]
    paperFeatures := [("clause", "constituent")] }

def en_26 : Datum :=
  { id := "qingetal2025_en_26"
    source := ⟨"qing-uegaki-2025", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary worries that John didn't go to school yesterday."
    glossedTokens := [("Mary", ""), ("worries", ""), ("that", ""), ("John", ""), ("didn't", ""), ("go", ""), ("to", ""), ("school", ""), ("yesterday", "")]
    glossedWords := [⟨['M', 'a', 'r', 'y'], [], [⟨['M', 'a', 'r', 'y'], [], none⟩]⟩, ⟨['w', 'o', 'r', 'r', 'i', 'e', 's'], [], [⟨['w', 'o', 'r', 'r', 'i', 'e', 's'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['J', 'o', 'h', 'n'], [], [⟨['J', 'o', 'h', 'n'], [], none⟩]⟩, ⟨['d', 'i', 'd', 'n', '\'', 't'], [], [⟨['d', 'i', 'd', 'n', '\'', 't'], [], none⟩]⟩, ⟨['g', 'o'], [], [⟨['g', 'o'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['s', 'c', 'h', 'o', 'o', 'l'], [], [⟨['s', 'c', 'h', 'o', 'o', 'l'], [], none⟩]⟩, ⟨['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [], [⟨['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "predicate", some "worry"⟩]
    paperFeatures := [("clause", "declarative")] }

def en_28 : Datum :=
  { id := "qingetal2025_en_28"
    source := ⟨"qing-uegaki-2025", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Al's father worries where he can dock his boat."
    glossedTokens := [("Al's", ""), ("father", ""), ("worries", ""), ("where", ""), ("he", ""), ("can", ""), ("dock", ""), ("his", ""), ("boat", "")]
    glossedWords := [⟨['A', 'l', '\'', 's'], [], [⟨['A', 'l', '\'', 's'], [], none⟩]⟩, ⟨['f', 'a', 't', 'h', 'e', 'r'], [], [⟨['f', 'a', 't', 'h', 'e', 'r'], [], none⟩]⟩, ⟨['w', 'o', 'r', 'r', 'i', 'e', 's'], [], [⟨['w', 'o', 'r', 'r', 'i', 'e', 's'], [], none⟩]⟩, ⟨['w', 'h', 'e', 'r', 'e'], [], [⟨['w', 'h', 'e', 'r', 'e'], [], none⟩]⟩, ⟨['h', 'e'], [], [⟨['h', 'e'], [], none⟩]⟩, ⟨['c', 'a', 'n'], [], [⟨['c', 'a', 'n'], [], none⟩]⟩, ⟨['d', 'o', 'c', 'k'], [], [⟨['d', 'o', 'c', 'k'], [], none⟩]⟩, ⟨['h', 'i', 's'], [], [⟨['h', 'i', 's'], [], none⟩]⟩, ⟨['b', 'o', 'a', 't'], [], [⟨['b', 'o', 'a', 't'], [], none⟩]⟩]
    context := "Al's father recently bought a new boat and is visiting Amsterdam with it. He is sure that there must be a place in Amsterdam where he can dock his boat, and he would be happy to dock his boat anywhere. However, for any specific place, he does not know whether it still has spots available, and he is anxiously trying to find out where exactly he can dock his boat."
    judgment := .acceptable
    verdict := some true
    contrasts := []
    readings := []
    spans := [⟨2, 1, "predicate", some "worry"⟩]
    paperFeatures := [("clause", "constituent")] }

def en_29 : Datum :=
  { id := "qingetal2025_en_29"
    source := ⟨"qing-uegaki-2025", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Al's father worries that he can dock his boat at Y."
    glossedTokens := [("Al's", ""), ("father", ""), ("worries", ""), ("that", ""), ("he", ""), ("can", ""), ("dock", ""), ("his", ""), ("boat", ""), ("at", ""), ("Y", "")]
    glossedWords := [⟨['A', 'l', '\'', 's'], [], [⟨['A', 'l', '\'', 's'], [], none⟩]⟩, ⟨['f', 'a', 't', 'h', 'e', 'r'], [], [⟨['f', 'a', 't', 'h', 'e', 'r'], [], none⟩]⟩, ⟨['w', 'o', 'r', 'r', 'i', 'e', 's'], [], [⟨['w', 'o', 'r', 'r', 'i', 'e', 's'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['h', 'e'], [], [⟨['h', 'e'], [], none⟩]⟩, ⟨['c', 'a', 'n'], [], [⟨['c', 'a', 'n'], [], none⟩]⟩, ⟨['d', 'o', 'c', 'k'], [], [⟨['d', 'o', 'c', 'k'], [], none⟩]⟩, ⟨['h', 'i', 's'], [], [⟨['h', 'i', 's'], [], none⟩]⟩, ⟨['b', 'o', 'a', 't'], [], [⟨['b', 'o', 'a', 't'], [], none⟩]⟩, ⟨['a', 't'], [], [⟨['a', 't'], [], none⟩]⟩, ⟨['Y'], [], [⟨['Y'], [], none⟩]⟩]
    context := "Al's father recently bought a new boat and is visiting Amsterdam with it. He is sure that there must be a place in Amsterdam where he can dock his boat, and he would be happy to dock his boat anywhere. However, for any specific place, he does not know whether it still has spots available, and he is anxiously trying to find out where exactly he can dock his boat."
    judgment := .acceptable
    verdict := some false
    contrasts := []
    readings := []
    spans := [⟨2, 1, "predicate", some "worry"⟩]
    paperFeatures := [("clause", "declarative")] }

def en_30a : Datum :=
  { id := "qingetal2025_en_30a"
    source := ⟨"qing-uegaki-2025", "(30a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Mr. Nelson denies he is “a real collector – the kind of person who buys first and then worries where he can find room for his purchases.”"
    glossedTokens := [("Mr", ""), ("Nelson", ""), ("denies", ""), ("he", ""), ("is", ""), ("a", ""), ("real", ""), ("collector", ""), ("the", ""), ("kind", ""), ("of", ""), ("person", ""), ("who", ""), ("buys", ""), ("first", ""), ("and", ""), ("then", ""), ("worries", ""), ("where", ""), ("he", ""), ("can", ""), ("find", ""), ("room", ""), ("for", ""), ("his", ""), ("purchases", "")]
    glossedWords := [⟨['M', 'r'], [], [⟨['M', 'r'], [], none⟩]⟩, ⟨['N', 'e', 'l', 's', 'o', 'n'], [], [⟨['N', 'e', 'l', 's', 'o', 'n'], [], none⟩]⟩, ⟨['d', 'e', 'n', 'i', 'e', 's'], [], [⟨['d', 'e', 'n', 'i', 'e', 's'], [], none⟩]⟩, ⟨['h', 'e'], [], [⟨['h', 'e'], [], none⟩]⟩, ⟨['i', 's'], [], [⟨['i', 's'], [], none⟩]⟩, ⟨['a'], [], [⟨['a'], [], none⟩]⟩, ⟨['r', 'e', 'a', 'l'], [], [⟨['r', 'e', 'a', 'l'], [], none⟩]⟩, ⟨['c', 'o', 'l', 'l', 'e', 'c', 't', 'o', 'r'], [], [⟨['c', 'o', 'l', 'l', 'e', 'c', 't', 'o', 'r'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['k', 'i', 'n', 'd'], [], [⟨['k', 'i', 'n', 'd'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['p', 'e', 'r', 's', 'o', 'n'], [], [⟨['p', 'e', 'r', 's', 'o', 'n'], [], none⟩]⟩, ⟨['w', 'h', 'o'], [], [⟨['w', 'h', 'o'], [], none⟩]⟩, ⟨['b', 'u', 'y', 's'], [], [⟨['b', 'u', 'y', 's'], [], none⟩]⟩, ⟨['f', 'i', 'r', 's', 't'], [], [⟨['f', 'i', 'r', 's', 't'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e', 'n'], [], [⟨['t', 'h', 'e', 'n'], [], none⟩]⟩, ⟨['w', 'o', 'r', 'r', 'i', 'e', 's'], [], [⟨['w', 'o', 'r', 'r', 'i', 'e', 's'], [], none⟩]⟩, ⟨['w', 'h', 'e', 'r', 'e'], [], [⟨['w', 'h', 'e', 'r', 'e'], [], none⟩]⟩, ⟨['h', 'e'], [], [⟨['h', 'e'], [], none⟩]⟩, ⟨['c', 'a', 'n'], [], [⟨['c', 'a', 'n'], [], none⟩]⟩, ⟨['f', 'i', 'n', 'd'], [], [⟨['f', 'i', 'n', 'd'], [], none⟩]⟩, ⟨['r', 'o', 'o', 'm'], [], [⟨['r', 'o', 'o', 'm'], [], none⟩]⟩, ⟨['f', 'o', 'r'], [], [⟨['f', 'o', 'r'], [], none⟩]⟩, ⟨['h', 'i', 's'], [], [⟨['h', 'i', 's'], [], none⟩]⟩, ⟨['p', 'u', 'r', 'c', 'h', 'a', 's', 'e', 's'], [], [⟨['p', 'u', 'r', 'c', 'h', 'a', 's', 'e', 's'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨17, 1, "predicate", some "worry"⟩]
    paperFeatures := [("clause", "constituent")] }

def en_30b : Datum :=
  { id := "qingetal2025_en_30b"
    source := ⟨"qing-uegaki-2025", "(30b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "As Ashley hands his church keys back he worries where he can spend the night."
    glossedTokens := [("As", ""), ("Ashley", ""), ("hands", ""), ("his", ""), ("church", ""), ("keys", ""), ("back", ""), ("he", ""), ("worries", ""), ("where", ""), ("he", ""), ("can", ""), ("spend", ""), ("the", ""), ("night", "")]
    glossedWords := [⟨['A', 's'], [], [⟨['A', 's'], [], none⟩]⟩, ⟨['A', 's', 'h', 'l', 'e', 'y'], [], [⟨['A', 's', 'h', 'l', 'e', 'y'], [], none⟩]⟩, ⟨['h', 'a', 'n', 'd', 's'], [], [⟨['h', 'a', 'n', 'd', 's'], [], none⟩]⟩, ⟨['h', 'i', 's'], [], [⟨['h', 'i', 's'], [], none⟩]⟩, ⟨['c', 'h', 'u', 'r', 'c', 'h'], [], [⟨['c', 'h', 'u', 'r', 'c', 'h'], [], none⟩]⟩, ⟨['k', 'e', 'y', 's'], [], [⟨['k', 'e', 'y', 's'], [], none⟩]⟩, ⟨['b', 'a', 'c', 'k'], [], [⟨['b', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['h', 'e'], [], [⟨['h', 'e'], [], none⟩]⟩, ⟨['w', 'o', 'r', 'r', 'i', 'e', 's'], [], [⟨['w', 'o', 'r', 'r', 'i', 'e', 's'], [], none⟩]⟩, ⟨['w', 'h', 'e', 'r', 'e'], [], [⟨['w', 'h', 'e', 'r', 'e'], [], none⟩]⟩, ⟨['h', 'e'], [], [⟨['h', 'e'], [], none⟩]⟩, ⟨['c', 'a', 'n'], [], [⟨['c', 'a', 'n'], [], none⟩]⟩, ⟨['s', 'p', 'e', 'n', 'd'], [], [⟨['s', 'p', 'e', 'n', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['n', 'i', 'g', 'h', 't'], [], [⟨['n', 'i', 'g', 'h', 't'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨8, 1, "predicate", some "worry"⟩]
    paperFeatures := [("clause", "constituent")] }

def en_30c : Datum :=
  { id := "qingetal2025_en_30c"
    source := ⟨"qing-uegaki-2025", "(30c)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "I have a sister in California that worries where she can live because she is white and her kids are mixed race."
    glossedTokens := [("I", ""), ("have", ""), ("a", ""), ("sister", ""), ("in", ""), ("California", ""), ("that", ""), ("worries", ""), ("where", ""), ("she", ""), ("can", ""), ("live", ""), ("because", ""), ("she", ""), ("is", ""), ("white", ""), ("and", ""), ("her", ""), ("kids", ""), ("are", ""), ("mixed", ""), ("race", "")]
    glossedWords := [⟨['I'], [], [⟨['I'], [], none⟩]⟩, ⟨['h', 'a', 'v', 'e'], [], [⟨['h', 'a', 'v', 'e'], [], none⟩]⟩, ⟨['a'], [], [⟨['a'], [], none⟩]⟩, ⟨['s', 'i', 's', 't', 'e', 'r'], [], [⟨['s', 'i', 's', 't', 'e', 'r'], [], none⟩]⟩, ⟨['i', 'n'], [], [⟨['i', 'n'], [], none⟩]⟩, ⟨['C', 'a', 'l', 'i', 'f', 'o', 'r', 'n', 'i', 'a'], [], [⟨['C', 'a', 'l', 'i', 'f', 'o', 'r', 'n', 'i', 'a'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['w', 'o', 'r', 'r', 'i', 'e', 's'], [], [⟨['w', 'o', 'r', 'r', 'i', 'e', 's'], [], none⟩]⟩, ⟨['w', 'h', 'e', 'r', 'e'], [], [⟨['w', 'h', 'e', 'r', 'e'], [], none⟩]⟩, ⟨['s', 'h', 'e'], [], [⟨['s', 'h', 'e'], [], none⟩]⟩, ⟨['c', 'a', 'n'], [], [⟨['c', 'a', 'n'], [], none⟩]⟩, ⟨['l', 'i', 'v', 'e'], [], [⟨['l', 'i', 'v', 'e'], [], none⟩]⟩, ⟨['b', 'e', 'c', 'a', 'u', 's', 'e'], [], [⟨['b', 'e', 'c', 'a', 'u', 's', 'e'], [], none⟩]⟩, ⟨['s', 'h', 'e'], [], [⟨['s', 'h', 'e'], [], none⟩]⟩, ⟨['i', 's'], [], [⟨['i', 's'], [], none⟩]⟩, ⟨['w', 'h', 'i', 't', 'e'], [], [⟨['w', 'h', 'i', 't', 'e'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['h', 'e', 'r'], [], [⟨['h', 'e', 'r'], [], none⟩]⟩, ⟨['k', 'i', 'd', 's'], [], [⟨['k', 'i', 'd', 's'], [], none⟩]⟩, ⟨['a', 'r', 'e'], [], [⟨['a', 'r', 'e'], [], none⟩]⟩, ⟨['m', 'i', 'x', 'e', 'd'], [], [⟨['m', 'i', 'x', 'e', 'd'], [], none⟩]⟩, ⟨['r', 'a', 'c', 'e'], [], [⟨['r', 'a', 'c', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨7, 1, "predicate", some "worry"⟩]
    paperFeatures := [("clause", "constituent")] }

def en_30d : Datum :=
  { id := "qingetal2025_en_30d"
    source := ⟨"qing-uegaki-2025", "(30d)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Lucas tells Sami that he loves her and Sami tells him that she loves him too. Sami worries what she can do since she loves them both."
    glossedTokens := [("Lucas", ""), ("tells", ""), ("Sami", ""), ("that", ""), ("he", ""), ("loves", ""), ("her", ""), ("and", ""), ("Sami", ""), ("tells", ""), ("him", ""), ("that", ""), ("she", ""), ("loves", ""), ("him", ""), ("too", ""), ("Sami", ""), ("worries", ""), ("what", ""), ("she", ""), ("can", ""), ("do", ""), ("since", ""), ("she", ""), ("loves", ""), ("them", ""), ("both", "")]
    glossedWords := [⟨['L', 'u', 'c', 'a', 's'], [], [⟨['L', 'u', 'c', 'a', 's'], [], none⟩]⟩, ⟨['t', 'e', 'l', 'l', 's'], [], [⟨['t', 'e', 'l', 'l', 's'], [], none⟩]⟩, ⟨['S', 'a', 'm', 'i'], [], [⟨['S', 'a', 'm', 'i'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['h', 'e'], [], [⟨['h', 'e'], [], none⟩]⟩, ⟨['l', 'o', 'v', 'e', 's'], [], [⟨['l', 'o', 'v', 'e', 's'], [], none⟩]⟩, ⟨['h', 'e', 'r'], [], [⟨['h', 'e', 'r'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['S', 'a', 'm', 'i'], [], [⟨['S', 'a', 'm', 'i'], [], none⟩]⟩, ⟨['t', 'e', 'l', 'l', 's'], [], [⟨['t', 'e', 'l', 'l', 's'], [], none⟩]⟩, ⟨['h', 'i', 'm'], [], [⟨['h', 'i', 'm'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['s', 'h', 'e'], [], [⟨['s', 'h', 'e'], [], none⟩]⟩, ⟨['l', 'o', 'v', 'e', 's'], [], [⟨['l', 'o', 'v', 'e', 's'], [], none⟩]⟩, ⟨['h', 'i', 'm'], [], [⟨['h', 'i', 'm'], [], none⟩]⟩, ⟨['t', 'o', 'o'], [], [⟨['t', 'o', 'o'], [], none⟩]⟩, ⟨['S', 'a', 'm', 'i'], [], [⟨['S', 'a', 'm', 'i'], [], none⟩]⟩, ⟨['w', 'o', 'r', 'r', 'i', 'e', 's'], [], [⟨['w', 'o', 'r', 'r', 'i', 'e', 's'], [], none⟩]⟩, ⟨['w', 'h', 'a', 't'], [], [⟨['w', 'h', 'a', 't'], [], none⟩]⟩, ⟨['s', 'h', 'e'], [], [⟨['s', 'h', 'e'], [], none⟩]⟩, ⟨['c', 'a', 'n'], [], [⟨['c', 'a', 'n'], [], none⟩]⟩, ⟨['d', 'o'], [], [⟨['d', 'o'], [], none⟩]⟩, ⟨['s', 'i', 'n', 'c', 'e'], [], [⟨['s', 'i', 'n', 'c', 'e'], [], none⟩]⟩, ⟨['s', 'h', 'e'], [], [⟨['s', 'h', 'e'], [], none⟩]⟩, ⟨['l', 'o', 'v', 'e', 's'], [], [⟨['l', 'o', 'v', 'e', 's'], [], none⟩]⟩, ⟨['t', 'h', 'e', 'm'], [], [⟨['t', 'h', 'e', 'm'], [], none⟩]⟩, ⟨['b', 'o', 't', 'h'], [], [⟨['b', 'o', 't', 'h'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨17, 1, "predicate", some "worry"⟩]
    paperFeatures := [("clause", "constituent")] }

def en_36a : Datum :=
  { id := "qingetal2025_en_36a"
    source := ⟨"qing-uegaki-2025", "(36a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sam worries what they should wear."
    glossedTokens := [("Sam", ""), ("worries", ""), ("what", ""), ("they", ""), ("should", ""), ("wear", "")]
    glossedWords := [⟨['S', 'a', 'm'], [], [⟨['S', 'a', 'm'], [], none⟩]⟩, ⟨['w', 'o', 'r', 'r', 'i', 'e', 's'], [], [⟨['w', 'o', 'r', 'r', 'i', 'e', 's'], [], none⟩]⟩, ⟨['w', 'h', 'a', 't'], [], [⟨['w', 'h', 'a', 't'], [], none⟩]⟩, ⟨['t', 'h', 'e', 'y'], [], [⟨['t', 'h', 'e', 'y'], [], none⟩]⟩, ⟨['s', 'h', 'o', 'u', 'l', 'd'], [], [⟨['s', 'h', 'o', 'u', 'l', 'd'], [], none⟩]⟩, ⟨['w', 'e', 'a', 'r'], [], [⟨['w', 'e', 'a', 'r'], [], none⟩]⟩]
    context := "Sam is invited to an event. Not knowing much about it, they do not know what type of clothes would be appropriate: Casual, business casual, formal? They possess all relevant types of clothes and are happy to wear anything as long as it is appropriate for the occasion."
    judgment := .acceptable
    verdict := some true
    contrasts := []
    readings := []
    spans := [⟨1, 1, "predicate", some "worry"⟩]
    paperFeatures := [("clause", "constituent")] }

def en_36b : Datum :=
  { id := "qingetal2025_en_36b"
    source := ⟨"qing-uegaki-2025", "(36b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sam worries that they should wear casual/business casual/formal."
    glossedTokens := [("Sam", ""), ("worries", ""), ("that", ""), ("they", ""), ("should", ""), ("wear", ""), ("casual/business", ""), ("casual/formal", "")]
    glossedWords := [⟨['S', 'a', 'm'], [], [⟨['S', 'a', 'm'], [], none⟩]⟩, ⟨['w', 'o', 'r', 'r', 'i', 'e', 's'], [], [⟨['w', 'o', 'r', 'r', 'i', 'e', 's'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['t', 'h', 'e', 'y'], [], [⟨['t', 'h', 'e', 'y'], [], none⟩]⟩, ⟨['s', 'h', 'o', 'u', 'l', 'd'], [], [⟨['s', 'h', 'o', 'u', 'l', 'd'], [], none⟩]⟩, ⟨['w', 'e', 'a', 'r'], [], [⟨['w', 'e', 'a', 'r'], [], none⟩]⟩, ⟨['c', 'a', 's', 'u', 'a', 'l', '/', 'b', 'u', 's', 'i', 'n', 'e', 's', 's'], [], [⟨['c', 'a', 's', 'u', 'a', 'l', '/', 'b', 'u', 's', 'i', 'n', 'e', 's', 's'], [], none⟩]⟩, ⟨['c', 'a', 's', 'u', 'a', 'l', '/', 'f', 'o', 'r', 'm', 'a', 'l'], [], [⟨['c', 'a', 's', 'u', 'a', 'l', '/', 'f', 'o', 'r', 'm', 'a', 'l'], [], none⟩]⟩]
    context := "Sam is invited to an event. Not knowing much about it, they do not know what type of clothes would be appropriate: Casual, business casual, formal? They possess all relevant types of clothes and are happy to wear anything as long as it is appropriate for the occasion."
    judgment := .acceptable
    verdict := some false
    contrasts := []
    readings := []
    spans := [⟨1, 1, "predicate", some "worry"⟩]
    paperFeatures := [("clause", "declarative")] }

def en_42a : Datum :=
  { id := "qingetal2025_en_42a"
    source := ⟨"qing-uegaki-2025", "(42a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John doesn't like which student will sing."
    glossedTokens := [("John", ""), ("doesn't", ""), ("like", ""), ("which", ""), ("student", ""), ("will", ""), ("sing", "")]
    glossedWords := [⟨['J', 'o', 'h', 'n'], [], [⟨['J', 'o', 'h', 'n'], [], none⟩]⟩, ⟨['d', 'o', 'e', 's', 'n', '\'', 't'], [], [⟨['d', 'o', 'e', 's', 'n', '\'', 't'], [], none⟩]⟩, ⟨['l', 'i', 'k', 'e'], [], [⟨['l', 'i', 'k', 'e'], [], none⟩]⟩, ⟨['w', 'h', 'i', 'c', 'h'], [], [⟨['w', 'h', 'i', 'c', 'h'], [], none⟩]⟩, ⟨['s', 't', 'u', 'd', 'e', 'n', 't'], [], [⟨['s', 't', 'u', 'd', 'e', 'n', 't'], [], none⟩]⟩, ⟨['w', 'i', 'l', 'l'], [], [⟨['w', 'i', 'l', 'l'], [], none⟩]⟩, ⟨['s', 'i', 'n', 'g'], [], [⟨['s', 'i', 'n', 'g'], [], none⟩]⟩]
    context := "It is common knowledge that John knows which student will sing. Al knows that there is no particular student John wants to sing (i.e., John is indifferent about which student will sing). Bo asks Al: “How does John feel about which student will sing?”"
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "predicate", none⟩]
    paperFeatures := [("clause", "constituent"), ("polarity", "negated"), ("valence", "positive")] }

def en_42b : Datum :=
  { id := "qingetal2025_en_42b"
    source := ⟨"qing-uegaki-2025", "(42b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John isn't happy about which student will sing."
    glossedTokens := [("John", ""), ("isn't", ""), ("happy", ""), ("about", ""), ("which", ""), ("student", ""), ("will", ""), ("sing", "")]
    glossedWords := [⟨['J', 'o', 'h', 'n'], [], [⟨['J', 'o', 'h', 'n'], [], none⟩]⟩, ⟨['i', 's', 'n', '\'', 't'], [], [⟨['i', 's', 'n', '\'', 't'], [], none⟩]⟩, ⟨['h', 'a', 'p', 'p', 'y'], [], [⟨['h', 'a', 'p', 'p', 'y'], [], none⟩]⟩, ⟨['a', 'b', 'o', 'u', 't'], [], [⟨['a', 'b', 'o', 'u', 't'], [], none⟩]⟩, ⟨['w', 'h', 'i', 'c', 'h'], [], [⟨['w', 'h', 'i', 'c', 'h'], [], none⟩]⟩, ⟨['s', 't', 'u', 'd', 'e', 'n', 't'], [], [⟨['s', 't', 'u', 'd', 'e', 'n', 't'], [], none⟩]⟩, ⟨['w', 'i', 'l', 'l'], [], [⟨['w', 'i', 'l', 'l'], [], none⟩]⟩, ⟨['s', 'i', 'n', 'g'], [], [⟨['s', 'i', 'n', 'g'], [], none⟩]⟩]
    context := "It is common knowledge that John knows which student will sing. Al knows that there is no particular student John wants to sing (i.e., John is indifferent about which student will sing). Bo asks Al: “How does John feel about which student will sing?”"
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "predicate", none⟩]
    paperFeatures := [("clause", "constituent"), ("polarity", "negated"), ("valence", "positive")] }

def en_44a : Datum :=
  { id := "qingetal2025_en_44a"
    source := ⟨"qing-uegaki-2025", "(44a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John doesn't hate which student will sing."
    glossedTokens := [("John", ""), ("doesn't", ""), ("hate", ""), ("which", ""), ("student", ""), ("will", ""), ("sing", "")]
    glossedWords := [⟨['J', 'o', 'h', 'n'], [], [⟨['J', 'o', 'h', 'n'], [], none⟩]⟩, ⟨['d', 'o', 'e', 's', 'n', '\'', 't'], [], [⟨['d', 'o', 'e', 's', 'n', '\'', 't'], [], none⟩]⟩, ⟨['h', 'a', 't', 'e'], [], [⟨['h', 'a', 't', 'e'], [], none⟩]⟩, ⟨['w', 'h', 'i', 'c', 'h'], [], [⟨['w', 'h', 'i', 'c', 'h'], [], none⟩]⟩, ⟨['s', 't', 'u', 'd', 'e', 'n', 't'], [], [⟨['s', 't', 'u', 'd', 'e', 'n', 't'], [], none⟩]⟩, ⟨['w', 'i', 'l', 'l'], [], [⟨['w', 'i', 'l', 'l'], [], none⟩]⟩, ⟨['s', 'i', 'n', 'g'], [], [⟨['s', 'i', 'n', 'g'], [], none⟩]⟩]
    context := "It is common knowledge that John knows which student will sing. Al knows that there is no student such that John will hate it or be upset if they will sing. Bo asks Al: “How does John feel about which student will sing?”"
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "predicate", none⟩]
    paperFeatures := [("clause", "constituent"), ("polarity", "negated"), ("valence", "negative")] }

def en_44b : Datum :=
  { id := "qingetal2025_en_44b"
    source := ⟨"qing-uegaki-2025", "(44b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John isn't upset about which student will sing."
    glossedTokens := [("John", ""), ("isn't", ""), ("upset", ""), ("about", ""), ("which", ""), ("student", ""), ("will", ""), ("sing", "")]
    glossedWords := [⟨['J', 'o', 'h', 'n'], [], [⟨['J', 'o', 'h', 'n'], [], none⟩]⟩, ⟨['i', 's', 'n', '\'', 't'], [], [⟨['i', 's', 'n', '\'', 't'], [], none⟩]⟩, ⟨['u', 'p', 's', 'e', 't'], [], [⟨['u', 'p', 's', 'e', 't'], [], none⟩]⟩, ⟨['a', 'b', 'o', 'u', 't'], [], [⟨['a', 'b', 'o', 'u', 't'], [], none⟩]⟩, ⟨['w', 'h', 'i', 'c', 'h'], [], [⟨['w', 'h', 'i', 'c', 'h'], [], none⟩]⟩, ⟨['s', 't', 'u', 'd', 'e', 'n', 't'], [], [⟨['s', 't', 'u', 'd', 'e', 'n', 't'], [], none⟩]⟩, ⟨['w', 'i', 'l', 'l'], [], [⟨['w', 'i', 'l', 'l'], [], none⟩]⟩, ⟨['s', 'i', 'n', 'g'], [], [⟨['s', 'i', 'n', 'g'], [], none⟩]⟩]
    context := "It is common knowledge that John knows which student will sing. Al knows that there is no student such that John will hate it or be upset if they will sing. Bo asks Al: “How does John feel about which student will sing?”"
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "predicate", none⟩]
    paperFeatures := [("clause", "constituent"), ("polarity", "negated"), ("valence", "negative")] }

def en_46a : Datum :=
  { id := "qingetal2025_en_46a"
    source := ⟨"white-2021", "(25a)"⟩
    reportedIn := some ⟨"qing-uegaki-2025", "(46a)"⟩
    method := some .corpus
    language := "stan1293"
    primaryText := "Interstellar space is so vast that there is no need to fear whether stars in the Andromeda galaxy will accidentally slam into the Sun."
    glossedTokens := [("Interstellar", ""), ("space", ""), ("is", ""), ("so", ""), ("vast", ""), ("that", ""), ("there", ""), ("is", ""), ("no", ""), ("need", ""), ("to", ""), ("fear", ""), ("whether", ""), ("stars", ""), ("in", ""), ("the", ""), ("Andromeda", ""), ("galaxy", ""), ("will", ""), ("accidentally", ""), ("slam", ""), ("into", ""), ("the", ""), ("Sun", "")]
    glossedWords := [⟨['I', 'n', 't', 'e', 'r', 's', 't', 'e', 'l', 'l', 'a', 'r'], [], [⟨['I', 'n', 't', 'e', 'r', 's', 't', 'e', 'l', 'l', 'a', 'r'], [], none⟩]⟩, ⟨['s', 'p', 'a', 'c', 'e'], [], [⟨['s', 'p', 'a', 'c', 'e'], [], none⟩]⟩, ⟨['i', 's'], [], [⟨['i', 's'], [], none⟩]⟩, ⟨['s', 'o'], [], [⟨['s', 'o'], [], none⟩]⟩, ⟨['v', 'a', 's', 't'], [], [⟨['v', 'a', 's', 't'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['t', 'h', 'e', 'r', 'e'], [], [⟨['t', 'h', 'e', 'r', 'e'], [], none⟩]⟩, ⟨['i', 's'], [], [⟨['i', 's'], [], none⟩]⟩, ⟨['n', 'o'], [], [⟨['n', 'o'], [], none⟩]⟩, ⟨['n', 'e', 'e', 'd'], [], [⟨['n', 'e', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['f', 'e', 'a', 'r'], [], [⟨['f', 'e', 'a', 'r'], [], none⟩]⟩, ⟨['w', 'h', 'e', 't', 'h', 'e', 'r'], [], [⟨['w', 'h', 'e', 't', 'h', 'e', 'r'], [], none⟩]⟩, ⟨['s', 't', 'a', 'r', 's'], [], [⟨['s', 't', 'a', 'r', 's'], [], none⟩]⟩, ⟨['i', 'n'], [], [⟨['i', 'n'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['A', 'n', 'd', 'r', 'o', 'm', 'e', 'd', 'a'], [], [⟨['A', 'n', 'd', 'r', 'o', 'm', 'e', 'd', 'a'], [], none⟩]⟩, ⟨['g', 'a', 'l', 'a', 'x', 'y'], [], [⟨['g', 'a', 'l', 'a', 'x', 'y'], [], none⟩]⟩, ⟨['w', 'i', 'l', 'l'], [], [⟨['w', 'i', 'l', 'l'], [], none⟩]⟩, ⟨['a', 'c', 'c', 'i', 'd', 'e', 'n', 't', 'a', 'l', 'l', 'y'], [], [⟨['a', 'c', 'c', 'i', 'd', 'e', 'n', 't', 'a', 'l', 'l', 'y'], [], none⟩]⟩, ⟨['s', 'l', 'a', 'm'], [], [⟨['s', 'l', 'a', 'm'], [], none⟩]⟩, ⟨['i', 'n', 't', 'o'], [], [⟨['i', 'n', 't', 'o'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['S', 'u', 'n'], [], [⟨['S', 'u', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨11, 1, "predicate", some "fear"⟩]
    paperFeatures := [("clause", "polar"), ("answer", "radical")] }

def en_46b : Datum :=
  { id := "qingetal2025_en_46b"
    source := ⟨"white-2021", "(25b)"⟩
    reportedIn := some ⟨"qing-uegaki-2025", "(46b)"⟩
    method := some .corpus
    language := "stan1293"
    primaryText := "I fear whether this test would run safely on the oxygen sensor as it has a lot of drawback when compared with the others."
    glossedTokens := [("I", ""), ("fear", ""), ("whether", ""), ("this", ""), ("test", ""), ("would", ""), ("run", ""), ("safely", ""), ("on", ""), ("the", ""), ("oxygen", ""), ("sensor", ""), ("as", ""), ("it", ""), ("has", ""), ("a", ""), ("lot", ""), ("of", ""), ("drawback", ""), ("when", ""), ("compared", ""), ("with", ""), ("the", ""), ("others", "")]
    glossedWords := [⟨['I'], [], [⟨['I'], [], none⟩]⟩, ⟨['f', 'e', 'a', 'r'], [], [⟨['f', 'e', 'a', 'r'], [], none⟩]⟩, ⟨['w', 'h', 'e', 't', 'h', 'e', 'r'], [], [⟨['w', 'h', 'e', 't', 'h', 'e', 'r'], [], none⟩]⟩, ⟨['t', 'h', 'i', 's'], [], [⟨['t', 'h', 'i', 's'], [], none⟩]⟩, ⟨['t', 'e', 's', 't'], [], [⟨['t', 'e', 's', 't'], [], none⟩]⟩, ⟨['w', 'o', 'u', 'l', 'd'], [], [⟨['w', 'o', 'u', 'l', 'd'], [], none⟩]⟩, ⟨['r', 'u', 'n'], [], [⟨['r', 'u', 'n'], [], none⟩]⟩, ⟨['s', 'a', 'f', 'e', 'l', 'y'], [], [⟨['s', 'a', 'f', 'e', 'l', 'y'], [], none⟩]⟩, ⟨['o', 'n'], [], [⟨['o', 'n'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['o', 'x', 'y', 'g', 'e', 'n'], [], [⟨['o', 'x', 'y', 'g', 'e', 'n'], [], none⟩]⟩, ⟨['s', 'e', 'n', 's', 'o', 'r'], [], [⟨['s', 'e', 'n', 's', 'o', 'r'], [], none⟩]⟩, ⟨['a', 's'], [], [⟨['a', 's'], [], none⟩]⟩, ⟨['i', 't'], [], [⟨['i', 't'], [], none⟩]⟩, ⟨['h', 'a', 's'], [], [⟨['h', 'a', 's'], [], none⟩]⟩, ⟨['a'], [], [⟨['a'], [], none⟩]⟩, ⟨['l', 'o', 't'], [], [⟨['l', 'o', 't'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['d', 'r', 'a', 'w', 'b', 'a', 'c', 'k'], [], [⟨['d', 'r', 'a', 'w', 'b', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['w', 'h', 'e', 'n'], [], [⟨['w', 'h', 'e', 'n'], [], none⟩]⟩, ⟨['c', 'o', 'm', 'p', 'a', 'r', 'e', 'd'], [], [⟨['c', 'o', 'm', 'p', 'a', 'r', 'e', 'd'], [], none⟩]⟩, ⟨['w', 'i', 't', 'h'], [], [⟨['w', 'i', 't', 'h'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['o', 't', 'h', 'e', 'r', 's'], [], [⟨['o', 't', 'h', 'e', 'r', 's'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "predicate", some "fear"⟩]
    paperFeatures := [("clause", "polar"), ("answer", "negation")] }

def en_46c : Datum :=
  { id := "qingetal2025_en_46c"
    source := ⟨"white-2021", "(25c)"⟩
    reportedIn := some ⟨"qing-uegaki-2025", "(46c)"⟩
    method := some .corpus
    language := "stan1293"
    primaryText := "[...] I fear whether I'll have use of my arms/hands by age 55 or 60."
    glossedTokens := [("I", ""), ("fear", ""), ("whether", ""), ("I'll", ""), ("have", ""), ("use", ""), ("of", ""), ("my", ""), ("arms/hands", ""), ("by", ""), ("age", ""), ("55", ""), ("or", ""), ("60", "")]
    glossedWords := [⟨['I'], [], [⟨['I'], [], none⟩]⟩, ⟨['f', 'e', 'a', 'r'], [], [⟨['f', 'e', 'a', 'r'], [], none⟩]⟩, ⟨['w', 'h', 'e', 't', 'h', 'e', 'r'], [], [⟨['w', 'h', 'e', 't', 'h', 'e', 'r'], [], none⟩]⟩, ⟨['I', '\'', 'l', 'l'], [], [⟨['I', '\'', 'l', 'l'], [], none⟩]⟩, ⟨['h', 'a', 'v', 'e'], [], [⟨['h', 'a', 'v', 'e'], [], none⟩]⟩, ⟨['u', 's', 'e'], [], [⟨['u', 's', 'e'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['m', 'y'], [], [⟨['m', 'y'], [], none⟩]⟩, ⟨['a', 'r', 'm', 's', '/', 'h', 'a', 'n', 'd', 's'], [], [⟨['a', 'r', 'm', 's', '/', 'h', 'a', 'n', 'd', 's'], [], none⟩]⟩, ⟨['b', 'y'], [], [⟨['b', 'y'], [], none⟩]⟩, ⟨['a', 'g', 'e'], [], [⟨['a', 'g', 'e'], [], none⟩]⟩, ⟨['5', '5'], [], [⟨['5', '5'], [], none⟩]⟩, ⟨['o', 'r'], [], [⟨['o', 'r'], [], none⟩]⟩, ⟨['6', '0'], [], [⟨['6', '0'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "predicate", some "fear"⟩]
    paperFeatures := [("clause", "polar"), ("answer", "negation")] }

def en_46d : Datum :=
  { id := "qingetal2025_en_46d"
    source := ⟨"white-2021", "(25d)"⟩
    reportedIn := some ⟨"qing-uegaki-2025", "(46d)"⟩
    method := some .corpus
    language := "stan1293"
    primaryText := "I know parents who seriously fear whether their children will ever hold a meaningful job."
    glossedTokens := [("I", ""), ("know", ""), ("parents", ""), ("who", ""), ("seriously", ""), ("fear", ""), ("whether", ""), ("their", ""), ("children", ""), ("will", ""), ("ever", ""), ("hold", ""), ("a", ""), ("meaningful", ""), ("job", "")]
    glossedWords := [⟨['I'], [], [⟨['I'], [], none⟩]⟩, ⟨['k', 'n', 'o', 'w'], [], [⟨['k', 'n', 'o', 'w'], [], none⟩]⟩, ⟨['p', 'a', 'r', 'e', 'n', 't', 's'], [], [⟨['p', 'a', 'r', 'e', 'n', 't', 's'], [], none⟩]⟩, ⟨['w', 'h', 'o'], [], [⟨['w', 'h', 'o'], [], none⟩]⟩, ⟨['s', 'e', 'r', 'i', 'o', 'u', 's', 'l', 'y'], [], [⟨['s', 'e', 'r', 'i', 'o', 'u', 's', 'l', 'y'], [], none⟩]⟩, ⟨['f', 'e', 'a', 'r'], [], [⟨['f', 'e', 'a', 'r'], [], none⟩]⟩, ⟨['w', 'h', 'e', 't', 'h', 'e', 'r'], [], [⟨['w', 'h', 'e', 't', 'h', 'e', 'r'], [], none⟩]⟩, ⟨['t', 'h', 'e', 'i', 'r'], [], [⟨['t', 'h', 'e', 'i', 'r'], [], none⟩]⟩, ⟨['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n'], [], [⟨['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n'], [], none⟩]⟩, ⟨['w', 'i', 'l', 'l'], [], [⟨['w', 'i', 'l', 'l'], [], none⟩]⟩, ⟨['e', 'v', 'e', 'r'], [], [⟨['e', 'v', 'e', 'r'], [], none⟩]⟩, ⟨['h', 'o', 'l', 'd'], [], [⟨['h', 'o', 'l', 'd'], [], none⟩]⟩, ⟨['a'], [], [⟨['a'], [], none⟩]⟩, ⟨['m', 'e', 'a', 'n', 'i', 'n', 'g', 'f', 'u', 'l'], [], [⟨['m', 'e', 'a', 'n', 'i', 'n', 'g', 'f', 'u', 'l'], [], none⟩]⟩, ⟨['j', 'o', 'b'], [], [⟨['j', 'o', 'b'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨5, 1, "predicate", some "fear"⟩]
    paperFeatures := [("clause", "polar"), ("answer", "negation")] }

def en_47a : Datum :=
  { id := "qingetal2025_en_47a"
    source := ⟨"qing-uegaki-2025", "(47a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Both women initially worried about taking the bus, fearing who else might be riding the bus. Both have been pleasantly surprised. Express bus seats recline, and have individual reading lights and air-conditioning vents."
    glossedTokens := [("Both", ""), ("women", ""), ("initially", ""), ("worried", ""), ("about", ""), ("taking", ""), ("the", ""), ("bus", ""), ("fearing", ""), ("who", ""), ("else", ""), ("might", ""), ("be", ""), ("riding", ""), ("the", ""), ("bus", ""), ("Both", ""), ("have", ""), ("been", ""), ("pleasantly", ""), ("surprised", ""), ("Express", ""), ("bus", ""), ("seats", ""), ("recline", ""), ("and", ""), ("have", ""), ("individual", ""), ("reading", ""), ("lights", ""), ("and", ""), ("air-conditioning", ""), ("vents", "")]
    glossedWords := [⟨['B', 'o', 't', 'h'], [], [⟨['B', 'o', 't', 'h'], [], none⟩]⟩, ⟨['w', 'o', 'm', 'e', 'n'], [], [⟨['w', 'o', 'm', 'e', 'n'], [], none⟩]⟩, ⟨['i', 'n', 'i', 't', 'i', 'a', 'l', 'l', 'y'], [], [⟨['i', 'n', 'i', 't', 'i', 'a', 'l', 'l', 'y'], [], none⟩]⟩, ⟨['w', 'o', 'r', 'r', 'i', 'e', 'd'], [], [⟨['w', 'o', 'r', 'r', 'i', 'e', 'd'], [], none⟩]⟩, ⟨['a', 'b', 'o', 'u', 't'], [], [⟨['a', 'b', 'o', 'u', 't'], [], none⟩]⟩, ⟨['t', 'a', 'k', 'i', 'n', 'g'], [], [⟨['t', 'a', 'k', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['b', 'u', 's'], [], [⟨['b', 'u', 's'], [], none⟩]⟩, ⟨['f', 'e', 'a', 'r', 'i', 'n', 'g'], [], [⟨['f', 'e', 'a', 'r', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['w', 'h', 'o'], [], [⟨['w', 'h', 'o'], [], none⟩]⟩, ⟨['e', 'l', 's', 'e'], [], [⟨['e', 'l', 's', 'e'], [], none⟩]⟩, ⟨['m', 'i', 'g', 'h', 't'], [], [⟨['m', 'i', 'g', 'h', 't'], [], none⟩]⟩, ⟨['b', 'e'], [], [⟨['b', 'e'], [], none⟩]⟩, ⟨['r', 'i', 'd', 'i', 'n', 'g'], [], [⟨['r', 'i', 'd', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['b', 'u', 's'], [], [⟨['b', 'u', 's'], [], none⟩]⟩, ⟨['B', 'o', 't', 'h'], [], [⟨['B', 'o', 't', 'h'], [], none⟩]⟩, ⟨['h', 'a', 'v', 'e'], [], [⟨['h', 'a', 'v', 'e'], [], none⟩]⟩, ⟨['b', 'e', 'e', 'n'], [], [⟨['b', 'e', 'e', 'n'], [], none⟩]⟩, ⟨['p', 'l', 'e', 'a', 's', 'a', 'n', 't', 'l', 'y'], [], [⟨['p', 'l', 'e', 'a', 's', 'a', 'n', 't', 'l', 'y'], [], none⟩]⟩, ⟨['s', 'u', 'r', 'p', 'r', 'i', 's', 'e', 'd'], [], [⟨['s', 'u', 'r', 'p', 'r', 'i', 's', 'e', 'd'], [], none⟩]⟩, ⟨['E', 'x', 'p', 'r', 'e', 's', 's'], [], [⟨['E', 'x', 'p', 'r', 'e', 's', 's'], [], none⟩]⟩, ⟨['b', 'u', 's'], [], [⟨['b', 'u', 's'], [], none⟩]⟩, ⟨['s', 'e', 'a', 't', 's'], [], [⟨['s', 'e', 'a', 't', 's'], [], none⟩]⟩, ⟨['r', 'e', 'c', 'l', 'i', 'n', 'e'], [], [⟨['r', 'e', 'c', 'l', 'i', 'n', 'e'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['h', 'a', 'v', 'e'], [], [⟨['h', 'a', 'v', 'e'], [], none⟩]⟩, ⟨['i', 'n', 'd', 'i', 'v', 'i', 'd', 'u', 'a', 'l'], [], [⟨['i', 'n', 'd', 'i', 'v', 'i', 'd', 'u', 'a', 'l'], [], none⟩]⟩, ⟨['r', 'e', 'a', 'd', 'i', 'n', 'g'], [], [⟨['r', 'e', 'a', 'd', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['l', 'i', 'g', 'h', 't', 's'], [], [⟨['l', 'i', 'g', 'h', 't', 's'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['a', 'i', 'r', '-', 'c', 'o', 'n', 'd', 'i', 't', 'i', 'o', 'n', 'i', 'n', 'g'], [], [⟨['a', 'i', 'r'], [], none⟩, ⟨['c', 'o', 'n', 'd', 'i', 't', 'i', 'o', 'n', 'i', 'n', 'g'], [], some '-'⟩]⟩, ⟨['v', 'e', 'n', 't', 's'], [], [⟨['v', 'e', 'n', 't', 's'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨8, 1, "predicate", some "fear"⟩]
    paperFeatures := [("clause", "constituent")] }

def en_47b : Datum :=
  { id := "qingetal2025_en_47b"
    source := ⟨"qing-uegaki-2025", "(47b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "But if my party doesn't enter this city, I fear who else will."
    glossedTokens := [("But", ""), ("if", ""), ("my", ""), ("party", ""), ("doesn't", ""), ("enter", ""), ("this", ""), ("city", ""), ("I", ""), ("fear", ""), ("who", ""), ("else", ""), ("will", "")]
    glossedWords := [⟨['B', 'u', 't'], [], [⟨['B', 'u', 't'], [], none⟩]⟩, ⟨['i', 'f'], [], [⟨['i', 'f'], [], none⟩]⟩, ⟨['m', 'y'], [], [⟨['m', 'y'], [], none⟩]⟩, ⟨['p', 'a', 'r', 't', 'y'], [], [⟨['p', 'a', 'r', 't', 'y'], [], none⟩]⟩, ⟨['d', 'o', 'e', 's', 'n', '\'', 't'], [], [⟨['d', 'o', 'e', 's', 'n', '\'', 't'], [], none⟩]⟩, ⟨['e', 'n', 't', 'e', 'r'], [], [⟨['e', 'n', 't', 'e', 'r'], [], none⟩]⟩, ⟨['t', 'h', 'i', 's'], [], [⟨['t', 'h', 'i', 's'], [], none⟩]⟩, ⟨['c', 'i', 't', 'y'], [], [⟨['c', 'i', 't', 'y'], [], none⟩]⟩, ⟨['I'], [], [⟨['I'], [], none⟩]⟩, ⟨['f', 'e', 'a', 'r'], [], [⟨['f', 'e', 'a', 'r'], [], none⟩]⟩, ⟨['w', 'h', 'o'], [], [⟨['w', 'h', 'o'], [], none⟩]⟩, ⟨['e', 'l', 's', 'e'], [], [⟨['e', 'l', 's', 'e'], [], none⟩]⟩, ⟨['w', 'i', 'l', 'l'], [], [⟨['w', 'i', 'l', 'l'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨9, 1, "predicate", some "fear"⟩]
    paperFeatures := [("clause", "constituent")] }

def en_48 : Datum :=
  { id := "qingetal2025_en_48"
    source := ⟨"qing-uegaki-2025", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The women do not fear who else might be riding the bus."
    glossedTokens := [("The", ""), ("women", ""), ("do", ""), ("not", ""), ("fear", ""), ("who", ""), ("else", ""), ("might", ""), ("be", ""), ("riding", ""), ("the", ""), ("bus", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['w', 'o', 'm', 'e', 'n'], [], [⟨['w', 'o', 'm', 'e', 'n'], [], none⟩]⟩, ⟨['d', 'o'], [], [⟨['d', 'o'], [], none⟩]⟩, ⟨['n', 'o', 't'], [], [⟨['n', 'o', 't'], [], none⟩]⟩, ⟨['f', 'e', 'a', 'r'], [], [⟨['f', 'e', 'a', 'r'], [], none⟩]⟩, ⟨['w', 'h', 'o'], [], [⟨['w', 'h', 'o'], [], none⟩]⟩, ⟨['e', 'l', 's', 'e'], [], [⟨['e', 'l', 's', 'e'], [], none⟩]⟩, ⟨['m', 'i', 'g', 'h', 't'], [], [⟨['m', 'i', 'g', 'h', 't'], [], none⟩]⟩, ⟨['b', 'e'], [], [⟨['b', 'e'], [], none⟩]⟩, ⟨['r', 'i', 'd', 'i', 'n', 'g'], [], [⟨['r', 'i', 'd', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['b', 'u', 's'], [], [⟨['b', 'u', 's'], [], none⟩]⟩]
    context := "There exists no person x such that the women fear that x might be riding the bus."
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "predicate", some "fear"⟩]
    paperFeatures := [("clause", "constituent"), ("polarity", "negated")] }

def zh_22 : Datum :=
  { id := "qingetal2025_zh_22"
    source := ⟨"qing-uegaki-2025", "(22)"⟩
    reportedIn := none
    method := some .corpus
    language := "mand1415"
    primaryText := "Hen qidai ta hui zenyang quanshi zhege xinde juese."
    glossedTokens := [("Hen", "very"), ("qidai", "qidai"), ("ta", "he"), ("hui", "will"), ("zenyang", "how"), ("quanshi", "interpret"), ("zhege", "this"), ("xinde", "new"), ("juese", "character")]
    glossedWords := [⟨['H', 'e', 'n'], ['v', 'e', 'r', 'y'], [⟨['H', 'e', 'n'], ['v', 'e', 'r', 'y'], none⟩]⟩, ⟨['q', 'i', 'd', 'a', 'i'], ['q', 'i', 'd', 'a', 'i'], [⟨['q', 'i', 'd', 'a', 'i'], ['q', 'i', 'd', 'a', 'i'], none⟩]⟩, ⟨['t', 'a'], ['h', 'e'], [⟨['t', 'a'], ['h', 'e'], none⟩]⟩, ⟨['h', 'u', 'i'], ['w', 'i', 'l', 'l'], [⟨['h', 'u', 'i'], ['w', 'i', 'l', 'l'], none⟩]⟩, ⟨['z', 'e', 'n', 'y', 'a', 'n', 'g'], ['h', 'o', 'w'], [⟨['z', 'e', 'n', 'y', 'a', 'n', 'g'], ['h', 'o', 'w'], none⟩]⟩, ⟨['q', 'u', 'a', 'n', 's', 'h', 'i'], ['i', 'n', 't', 'e', 'r', 'p', 'r', 'e', 't'], [⟨['q', 'u', 'a', 'n', 's', 'h', 'i'], ['i', 'n', 't', 'e', 'r', 'p', 'r', 'e', 't'], none⟩]⟩, ⟨['z', 'h', 'e', 'g', 'e'], ['t', 'h', 'i', 's'], [⟨['z', 'h', 'e', 'g', 'e'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['x', 'i', 'n', 'd', 'e'], ['n', 'e', 'w'], [⟨['x', 'i', 'n', 'd', 'e'], ['n', 'e', 'w'], none⟩]⟩, ⟨['j', 'u', 'e', 's', 'e'], ['c', 'h', 'a', 'r', 'a', 'c', 't', 'e', 'r'], [⟨['j', 'u', 'e', 's', 'e'], ['c', 'h', 'a', 'r', 'a', 'c', 't', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "predicate", some "qidai"⟩]
    paperFeatures := [("clause", "constituent")] }

def zh_23 : Datum :=
  { id := "qingetal2025_zh_23"
    source := ⟨"qing-uegaki-2025", "(23)"⟩
    reportedIn := none
    method := some .corpus
    language := "mand1415"
    primaryText := "Ye qidai ta neng tongguo zhege zuopin rang gengduode ren shuzhi ta."
    glossedTokens := [("Ye", "also"), ("qidai", "qidai"), ("ta", "he"), ("neng", "can"), ("tongguo", "through"), ("zhege", "this.CLF"), ("zuopin", "work.of.art"), ("rang", "let"), ("gengduode", "more"), ("ren", "people"), ("shuzhi", "know.well"), ("ta", "him")]
    glossedWords := [⟨['Y', 'e'], ['a', 'l', 's', 'o'], [⟨['Y', 'e'], ['a', 'l', 's', 'o'], none⟩]⟩, ⟨['q', 'i', 'd', 'a', 'i'], ['q', 'i', 'd', 'a', 'i'], [⟨['q', 'i', 'd', 'a', 'i'], ['q', 'i', 'd', 'a', 'i'], none⟩]⟩, ⟨['t', 'a'], ['h', 'e'], [⟨['t', 'a'], ['h', 'e'], none⟩]⟩, ⟨['n', 'e', 'n', 'g'], ['c', 'a', 'n'], [⟨['n', 'e', 'n', 'g'], ['c', 'a', 'n'], none⟩]⟩, ⟨['t', 'o', 'n', 'g', 'g', 'u', 'o'], ['t', 'h', 'r', 'o', 'u', 'g', 'h'], [⟨['t', 'o', 'n', 'g', 'g', 'u', 'o'], ['t', 'h', 'r', 'o', 'u', 'g', 'h'], none⟩]⟩, ⟨['z', 'h', 'e', 'g', 'e'], ['t', 'h', 'i', 's', '.', 'C', 'L', 'F'], [⟨['z', 'h', 'e', 'g', 'e'], ['t', 'h', 'i', 's', '.', 'C', 'L', 'F'], none⟩]⟩, ⟨['z', 'u', 'o', 'p', 'i', 'n'], ['w', 'o', 'r', 'k', '.', 'o', 'f', '.', 'a', 'r', 't'], [⟨['z', 'u', 'o', 'p', 'i', 'n'], ['w', 'o', 'r', 'k', '.', 'o', 'f', '.', 'a', 'r', 't'], none⟩]⟩, ⟨['r', 'a', 'n', 'g'], ['l', 'e', 't'], [⟨['r', 'a', 'n', 'g'], ['l', 'e', 't'], none⟩]⟩, ⟨['g', 'e', 'n', 'g', 'd', 'u', 'o', 'd', 'e'], ['m', 'o', 'r', 'e'], [⟨['g', 'e', 'n', 'g', 'd', 'u', 'o', 'd', 'e'], ['m', 'o', 'r', 'e'], none⟩]⟩, ⟨['r', 'e', 'n'], ['p', 'e', 'o', 'p', 'l', 'e'], [⟨['r', 'e', 'n'], ['p', 'e', 'o', 'p', 'l', 'e'], none⟩]⟩, ⟨['s', 'h', 'u', 'z', 'h', 'i'], ['k', 'n', 'o', 'w', '.', 'w', 'e', 'l', 'l'], [⟨['s', 'h', 'u', 'z', 'h', 'i'], ['k', 'n', 'o', 'w', '.', 'w', 'e', 'l', 'l'], none⟩]⟩, ⟨['t', 'a'], ['h', 'i', 'm'], [⟨['t', 'a'], ['h', 'i', 'm'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "predicate", some "qidai"⟩]
    paperFeatures := [("clause", "declarative")] }

def zh_31a : Datum :=
  { id := "qingetal2025_zh_31a"
    source := ⟨"qing-uegaki-2025", "(31a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Wode baba hen danxin ta neng zai nali ting tade chuan."
    glossedTokens := [("Wode", "my"), ("baba", "father"), ("hen", "very"), ("danxin", "worry"), ("ta", "he"), ("neng", "can"), ("zai", "at"), ("nali", "where"), ("ting", "dock"), ("tade", "his"), ("chuan", "boat")]
    glossedWords := [⟨['W', 'o', 'd', 'e'], ['m', 'y'], [⟨['W', 'o', 'd', 'e'], ['m', 'y'], none⟩]⟩, ⟨['b', 'a', 'b', 'a'], ['f', 'a', 't', 'h', 'e', 'r'], [⟨['b', 'a', 'b', 'a'], ['f', 'a', 't', 'h', 'e', 'r'], none⟩]⟩, ⟨['h', 'e', 'n'], ['v', 'e', 'r', 'y'], [⟨['h', 'e', 'n'], ['v', 'e', 'r', 'y'], none⟩]⟩, ⟨['d', 'a', 'n', 'x', 'i', 'n'], ['w', 'o', 'r', 'r', 'y'], [⟨['d', 'a', 'n', 'x', 'i', 'n'], ['w', 'o', 'r', 'r', 'y'], none⟩]⟩, ⟨['t', 'a'], ['h', 'e'], [⟨['t', 'a'], ['h', 'e'], none⟩]⟩, ⟨['n', 'e', 'n', 'g'], ['c', 'a', 'n'], [⟨['n', 'e', 'n', 'g'], ['c', 'a', 'n'], none⟩]⟩, ⟨['z', 'a', 'i'], ['a', 't'], [⟨['z', 'a', 'i'], ['a', 't'], none⟩]⟩, ⟨['n', 'a', 'l', 'i'], ['w', 'h', 'e', 'r', 'e'], [⟨['n', 'a', 'l', 'i'], ['w', 'h', 'e', 'r', 'e'], none⟩]⟩, ⟨['t', 'i', 'n', 'g'], ['d', 'o', 'c', 'k'], [⟨['t', 'i', 'n', 'g'], ['d', 'o', 'c', 'k'], none⟩]⟩, ⟨['t', 'a', 'd', 'e'], ['h', 'i', 's'], [⟨['t', 'a', 'd', 'e'], ['h', 'i', 's'], none⟩]⟩, ⟨['c', 'h', 'u', 'a', 'n'], ['b', 'o', 'a', 't'], [⟨['c', 'h', 'u', 'a', 'n'], ['b', 'o', 'a', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Al's father recently bought a new boat and is visiting Amsterdam with it. He is sure that there must be a place in Amsterdam where he can dock his boat, and he would be happy to dock his boat anywhere. However, for any specific place, he does not know whether it still has spots available, and he is anxiously trying to find out where exactly he can dock his boat."
    judgment := .acceptable
    verdict := some true
    contrasts := []
    readings := []
    spans := [⟨3, 1, "predicate", some "danxin"⟩]
    paperFeatures := [("clause", "constituent")] }

def zh_31b : Datum :=
  { id := "qingetal2025_zh_31b"
    source := ⟨"qing-uegaki-2025", "(31b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Wode baba hen danxin ta neng zai Y (nali) ting tade chuan."
    glossedTokens := [("Wode", "my"), ("baba", "father"), ("hen", "very"), ("danxin", "worry"), ("ta", "he"), ("neng", "can"), ("zai", "at"), ("Y", "Y"), ("(nali)", "there"), ("ting", "dock"), ("tade", "his"), ("chuan", "boat")]
    glossedWords := [⟨['W', 'o', 'd', 'e'], ['m', 'y'], [⟨['W', 'o', 'd', 'e'], ['m', 'y'], none⟩]⟩, ⟨['b', 'a', 'b', 'a'], ['f', 'a', 't', 'h', 'e', 'r'], [⟨['b', 'a', 'b', 'a'], ['f', 'a', 't', 'h', 'e', 'r'], none⟩]⟩, ⟨['h', 'e', 'n'], ['v', 'e', 'r', 'y'], [⟨['h', 'e', 'n'], ['v', 'e', 'r', 'y'], none⟩]⟩, ⟨['d', 'a', 'n', 'x', 'i', 'n'], ['w', 'o', 'r', 'r', 'y'], [⟨['d', 'a', 'n', 'x', 'i', 'n'], ['w', 'o', 'r', 'r', 'y'], none⟩]⟩, ⟨['t', 'a'], ['h', 'e'], [⟨['t', 'a'], ['h', 'e'], none⟩]⟩, ⟨['n', 'e', 'n', 'g'], ['c', 'a', 'n'], [⟨['n', 'e', 'n', 'g'], ['c', 'a', 'n'], none⟩]⟩, ⟨['z', 'a', 'i'], ['a', 't'], [⟨['z', 'a', 'i'], ['a', 't'], none⟩]⟩, ⟨['Y'], ['Y'], [⟨['Y'], ['Y'], none⟩]⟩, ⟨['(', 'n', 'a', 'l', 'i', ')'], ['t', 'h', 'e', 'r', 'e'], [⟨['n', 'a', 'l', 'i'], ['t', 'h', 'e', 'r', 'e'], none⟩]⟩, ⟨['t', 'i', 'n', 'g'], ['d', 'o', 'c', 'k'], [⟨['t', 'i', 'n', 'g'], ['d', 'o', 'c', 'k'], none⟩]⟩, ⟨['t', 'a', 'd', 'e'], ['h', 'i', 's'], [⟨['t', 'a', 'd', 'e'], ['h', 'i', 's'], none⟩]⟩, ⟨['c', 'h', 'u', 'a', 'n'], ['b', 'o', 'a', 't'], [⟨['c', 'h', 'u', 'a', 'n'], ['b', 'o', 'a', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Al's father recently bought a new boat and is visiting Amsterdam with it. He is sure that there must be a place in Amsterdam where he can dock his boat, and he would be happy to dock his boat anywhere. However, for any specific place, he does not know whether it still has spots available, and he is anxiously trying to find out where exactly he can dock his boat."
    judgment := .acceptable
    verdict := some false
    contrasts := []
    readings := []
    spans := [⟨3, 1, "predicate", some "danxin"⟩]
    paperFeatures := [("clause", "declarative")] }

def zh_37 : Datum :=
  { id := "qingetal2025_zh_37"
    source := ⟨"qing-uegaki-2025", "(37)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Yuehan hen danxin ta yao chuan shenme."
    glossedTokens := [("Yuehan", "John"), ("hen", "very"), ("danxin", "worry"), ("ta", "he"), ("yao", "should"), ("chuan", "wear"), ("shenme", "what")]
    glossedWords := [⟨['Y', 'u', 'e', 'h', 'a', 'n'], ['J', 'o', 'h', 'n'], [⟨['Y', 'u', 'e', 'h', 'a', 'n'], ['J', 'o', 'h', 'n'], none⟩]⟩, ⟨['h', 'e', 'n'], ['v', 'e', 'r', 'y'], [⟨['h', 'e', 'n'], ['v', 'e', 'r', 'y'], none⟩]⟩, ⟨['d', 'a', 'n', 'x', 'i', 'n'], ['w', 'o', 'r', 'r', 'y'], [⟨['d', 'a', 'n', 'x', 'i', 'n'], ['w', 'o', 'r', 'r', 'y'], none⟩]⟩, ⟨['t', 'a'], ['h', 'e'], [⟨['t', 'a'], ['h', 'e'], none⟩]⟩, ⟨['y', 'a', 'o'], ['s', 'h', 'o', 'u', 'l', 'd'], [⟨['y', 'a', 'o'], ['s', 'h', 'o', 'u', 'l', 'd'], none⟩]⟩, ⟨['c', 'h', 'u', 'a', 'n'], ['w', 'e', 'a', 'r'], [⟨['c', 'h', 'u', 'a', 'n'], ['w', 'e', 'a', 'r'], none⟩]⟩, ⟨['s', 'h', 'e', 'n', 'm', 'e'], ['w', 'h', 'a', 't'], [⟨['s', 'h', 'e', 'n', 'm', 'e'], ['w', 'h', 'a', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Sam is invited to an event. Not knowing much about it, they do not know what type of clothes would be appropriate: Casual, business casual, formal? They possess all relevant types of clothes and are happy to wear anything as long as it is appropriate for the occasion."
    judgment := .acceptable
    verdict := some true
    contrasts := []
    readings := []
    spans := [⟨2, 1, "predicate", some "danxin"⟩]
    paperFeatures := [("clause", "constituent")] }

def zh_59 : Datum :=
  { id := "qingetal2025_zh_59"
    source := ⟨"qing-uegaki-2025", "(59)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Yuehan (hen) haipa tade linju huibuhui zaijia."
    glossedTokens := [("Yuehan", "John"), ("(hen)", "very"), ("haipa", "fears"), ("tade", "his"), ("linju", "neighbor"), ("huibuhui", "will.not.will"), ("zaijia", "at.home")]
    glossedWords := [⟨['Y', 'u', 'e', 'h', 'a', 'n'], ['J', 'o', 'h', 'n'], [⟨['Y', 'u', 'e', 'h', 'a', 'n'], ['J', 'o', 'h', 'n'], none⟩]⟩, ⟨['(', 'h', 'e', 'n', ')'], ['v', 'e', 'r', 'y'], [⟨['h', 'e', 'n'], ['v', 'e', 'r', 'y'], none⟩]⟩, ⟨['h', 'a', 'i', 'p', 'a'], ['f', 'e', 'a', 'r', 's'], [⟨['h', 'a', 'i', 'p', 'a'], ['f', 'e', 'a', 'r', 's'], none⟩]⟩, ⟨['t', 'a', 'd', 'e'], ['h', 'i', 's'], [⟨['t', 'a', 'd', 'e'], ['h', 'i', 's'], none⟩]⟩, ⟨['l', 'i', 'n', 'j', 'u'], ['n', 'e', 'i', 'g', 'h', 'b', 'o', 'r'], [⟨['l', 'i', 'n', 'j', 'u'], ['n', 'e', 'i', 'g', 'h', 'b', 'o', 'r'], none⟩]⟩, ⟨['h', 'u', 'i', 'b', 'u', 'h', 'u', 'i'], ['w', 'i', 'l', 'l', '.', 'n', 'o', 't', '.', 'w', 'i', 'l', 'l'], [⟨['h', 'u', 'i', 'b', 'u', 'h', 'u', 'i'], ['w', 'i', 'l', 'l', '.', 'n', 'o', 't', '.', 'w', 'i', 'l', 'l'], none⟩]⟩, ⟨['z', 'a', 'i', 'j', 'i', 'a'], ['a', 't', '.', 'h', 'o', 'm', 'e'], [⟨['z', 'a', 'i', 'j', 'i', 'a'], ['a', 't', '.', 'h', 'o', 'm', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "predicate", some "haipa"⟩]
    paperFeatures := [("clause", "polar")] }

def zh_60 : Datum :=
  { id := "qingetal2025_zh_60"
    source := ⟨"qing-uegaki-2025", "(60)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Yuehan (hen) haipa naming xuanshou hui yingde bisai."
    glossedTokens := [("Yuehan", "John"), ("(hen)", "very"), ("haipa", "fears"), ("naming", "which.CLF"), ("xuanshou", "player"), ("hui", "will"), ("yingde", "win"), ("bisai", "match")]
    glossedWords := [⟨['Y', 'u', 'e', 'h', 'a', 'n'], ['J', 'o', 'h', 'n'], [⟨['Y', 'u', 'e', 'h', 'a', 'n'], ['J', 'o', 'h', 'n'], none⟩]⟩, ⟨['(', 'h', 'e', 'n', ')'], ['v', 'e', 'r', 'y'], [⟨['h', 'e', 'n'], ['v', 'e', 'r', 'y'], none⟩]⟩, ⟨['h', 'a', 'i', 'p', 'a'], ['f', 'e', 'a', 'r', 's'], [⟨['h', 'a', 'i', 'p', 'a'], ['f', 'e', 'a', 'r', 's'], none⟩]⟩, ⟨['n', 'a', 'm', 'i', 'n', 'g'], ['w', 'h', 'i', 'c', 'h', '.', 'C', 'L', 'F'], [⟨['n', 'a', 'm', 'i', 'n', 'g'], ['w', 'h', 'i', 'c', 'h', '.', 'C', 'L', 'F'], none⟩]⟩, ⟨['x', 'u', 'a', 'n', 's', 'h', 'o', 'u'], ['p', 'l', 'a', 'y', 'e', 'r'], [⟨['x', 'u', 'a', 'n', 's', 'h', 'o', 'u'], ['p', 'l', 'a', 'y', 'e', 'r'], none⟩]⟩, ⟨['h', 'u', 'i'], ['w', 'i', 'l', 'l'], [⟨['h', 'u', 'i'], ['w', 'i', 'l', 'l'], none⟩]⟩, ⟨['y', 'i', 'n', 'g', 'd', 'e'], ['w', 'i', 'n'], [⟨['y', 'i', 'n', 'g', 'd', 'e'], ['w', 'i', 'n'], none⟩]⟩, ⟨['b', 'i', 's', 'a', 'i'], ['m', 'a', 't', 'c', 'h'], [⟨['b', 'i', 's', 'a', 'i'], ['m', 'a', 't', 'c', 'h'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("question", .unacceptable), ("indefinite", .acceptable)]
    spans := [⟨2, 1, "predicate", some "haipa"⟩]
    paperFeatures := [("clause", "constituent")] }

def zh_fn10_i : Datum :=
  { id := "qingetal2025_zh_fn10_i"
    source := ⟨"qing-uegaki-2025", "fn. 10 (i)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Yuehan haipa tamen tigong na xie yinliao."
    glossedTokens := [("Yuehan", "John"), ("haipa", "fears"), ("tamen", "they"), ("tigong", "serve"), ("na", "which"), ("xie", "CL.PL"), ("yinliao", "beverage")]
    glossedWords := [⟨['Y', 'u', 'e', 'h', 'a', 'n'], ['J', 'o', 'h', 'n'], [⟨['Y', 'u', 'e', 'h', 'a', 'n'], ['J', 'o', 'h', 'n'], none⟩]⟩, ⟨['h', 'a', 'i', 'p', 'a'], ['f', 'e', 'a', 'r', 's'], [⟨['h', 'a', 'i', 'p', 'a'], ['f', 'e', 'a', 'r', 's'], none⟩]⟩, ⟨['t', 'a', 'm', 'e', 'n'], ['t', 'h', 'e', 'y'], [⟨['t', 'a', 'm', 'e', 'n'], ['t', 'h', 'e', 'y'], none⟩]⟩, ⟨['t', 'i', 'g', 'o', 'n', 'g'], ['s', 'e', 'r', 'v', 'e'], [⟨['t', 'i', 'g', 'o', 'n', 'g'], ['s', 'e', 'r', 'v', 'e'], none⟩]⟩, ⟨['n', 'a'], ['w', 'h', 'i', 'c', 'h'], [⟨['n', 'a'], ['w', 'h', 'i', 'c', 'h'], none⟩]⟩, ⟨['x', 'i', 'e'], ['C', 'L', '.', 'P', 'L'], [⟨['x', 'i', 'e'], ['C', 'L', '.', 'P', 'L'], none⟩]⟩, ⟨['y', 'i', 'n', 'l', 'i', 'a', 'o'], ['b', 'e', 'v', 'e', 'r', 'a', 'g', 'e'], [⟨['y', 'i', 'n', 'l', 'i', 'a', 'o'], ['b', 'e', 'v', 'e', 'r', 'a', 'g', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨1, 1, "predicate", some "haipa"⟩]
    paperFeatures := [("clause", "constituent")] }

def ja_24a : Datum :=
  { id := "qingetal2025_ja_24a"
    source := ⟨"qing-uegaki-2025", "(24a)"⟩
    reportedIn := none
    method := some .corpus
    language := "nucl1643"
    primaryText := "Kotosi-wa dare-ga MVP-o toru-no-ka tanosimi-desu-wa."
    glossedTokens := [("Kotosi-wa", "this.year-TOP"), ("dare-ga", "who-NOM"), ("MVP-o", "MVP-ACC"), ("toru-no-ka", "win-NMZ-Q"), ("tanosimi-desu-wa", "fun-COP.POL-PARTICLE")]
    glossedWords := [⟨['K', 'o', 't', 'o', 's', 'i', '-', 'w', 'a'], ['t', 'h', 'i', 's', '.', 'y', 'e', 'a', 'r', '-', 'T', 'O', 'P'], [⟨['K', 'o', 't', 'o', 's', 'i'], ['t', 'h', 'i', 's', '.', 'y', 'e', 'a', 'r'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['d', 'a', 'r', 'e', '-', 'g', 'a'], ['w', 'h', 'o', '-', 'N', 'O', 'M'], [⟨['d', 'a', 'r', 'e'], ['w', 'h', 'o'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['M', 'V', 'P', '-', 'o'], ['M', 'V', 'P', '-', 'A', 'C', 'C'], [⟨['M', 'V', 'P'], ['M', 'V', 'P'], none⟩, ⟨['o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['t', 'o', 'r', 'u', '-', 'n', 'o', '-', 'k', 'a'], ['w', 'i', 'n', '-', 'N', 'M', 'Z', '-', 'Q'], [⟨['t', 'o', 'r', 'u'], ['w', 'i', 'n'], none⟩, ⟨['n', 'o'], ['N', 'M', 'Z'], some '-'⟩, ⟨['k', 'a'], ['Q'], some '-'⟩]⟩, ⟨['t', 'a', 'n', 'o', 's', 'i', 'm', 'i', '-', 'd', 'e', 's', 'u', '-', 'w', 'a'], ['f', 'u', 'n', '-', 'C', 'O', 'P', '.', 'P', 'O', 'L', '-', 'P', 'A', 'R', 'T', 'I', 'C', 'L', 'E'], [⟨['t', 'a', 'n', 'o', 's', 'i', 'm', 'i'], ['f', 'u', 'n'], none⟩, ⟨['d', 'e', 's', 'u'], ['C', 'O', 'P', '.', 'P', 'O', 'L'], some '-'⟩, ⟨['w', 'a'], ['P', 'A', 'R', 'T', 'I', 'C', 'L', 'E'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "predicate", some "tanosimi"⟩]
    paperFeatures := [("clause", "constituent")] }

def ja_25a : Datum :=
  { id := "qingetal2025_ja_25a"
    source := ⟨"qing-uegaki-2025", "(25a)"⟩
    reportedIn := none
    method := some .corpus
    language := "nucl1643"
    primaryText := "Watasi-wa Pattinson-ga Batman-de nani-o suru-no-ka tanosimi-desu."
    glossedTokens := [("Watasi-wa", "I-TOP"), ("Pattinson-ga", "Pattinson-NOM"), ("Batman-de", "Batman-LOC"), ("nani-o", "what-ACC"), ("suru-no-ka", "do-NMZ-Q"), ("tanosimi-desu", "fun-COP.POL")]
    glossedWords := [⟨['W', 'a', 't', 'a', 's', 'i', '-', 'w', 'a'], ['I', '-', 'T', 'O', 'P'], [⟨['W', 'a', 't', 'a', 's', 'i'], ['I'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['P', 'a', 't', 't', 'i', 'n', 's', 'o', 'n', '-', 'g', 'a'], ['P', 'a', 't', 't', 'i', 'n', 's', 'o', 'n', '-', 'N', 'O', 'M'], [⟨['P', 'a', 't', 't', 'i', 'n', 's', 'o', 'n'], ['P', 'a', 't', 't', 'i', 'n', 's', 'o', 'n'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['B', 'a', 't', 'm', 'a', 'n', '-', 'd', 'e'], ['B', 'a', 't', 'm', 'a', 'n', '-', 'L', 'O', 'C'], [⟨['B', 'a', 't', 'm', 'a', 'n'], ['B', 'a', 't', 'm', 'a', 'n'], none⟩, ⟨['d', 'e'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['n', 'a', 'n', 'i', '-', 'o'], ['w', 'h', 'a', 't', '-', 'A', 'C', 'C'], [⟨['n', 'a', 'n', 'i'], ['w', 'h', 'a', 't'], none⟩, ⟨['o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['s', 'u', 'r', 'u', '-', 'n', 'o', '-', 'k', 'a'], ['d', 'o', '-', 'N', 'M', 'Z', '-', 'Q'], [⟨['s', 'u', 'r', 'u'], ['d', 'o'], none⟩, ⟨['n', 'o'], ['N', 'M', 'Z'], some '-'⟩, ⟨['k', 'a'], ['Q'], some '-'⟩]⟩, ⟨['t', 'a', 'n', 'o', 's', 'i', 'm', 'i', '-', 'd', 'e', 's', 'u'], ['f', 'u', 'n', '-', 'C', 'O', 'P', '.', 'P', 'O', 'L'], [⟨['t', 'a', 'n', 'o', 's', 'i', 'm', 'i'], ['f', 'u', 'n'], none⟩, ⟨['d', 'e', 's', 'u'], ['C', 'O', 'P', '.', 'P', 'O', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨5, 1, "predicate", some "tanosimi"⟩]
    paperFeatures := [("clause", "constituent")] }

def ja_32a : Datum :=
  { id := "qingetal2025_ja_32a"
    source := ⟨"qing-uegaki-2025", "(32a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nucl1643"
    primaryText := "Kare-wa doko-ni hune-o tome-rareru-ka-o sinpai-siteiru."
    glossedTokens := [("Kare-wa", "he-TOP"), ("doko-ni", "where-LOC"), ("hune-o", "boat-ACC"), ("tome-rareru-ka-o", "park-can-Q-ACC"), ("sinpai-siteiru", "worry-do.ASP")]
    glossedWords := [⟨['K', 'a', 'r', 'e', '-', 'w', 'a'], ['h', 'e', '-', 'T', 'O', 'P'], [⟨['K', 'a', 'r', 'e'], ['h', 'e'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['d', 'o', 'k', 'o', '-', 'n', 'i'], ['w', 'h', 'e', 'r', 'e', '-', 'L', 'O', 'C'], [⟨['d', 'o', 'k', 'o'], ['w', 'h', 'e', 'r', 'e'], none⟩, ⟨['n', 'i'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['h', 'u', 'n', 'e', '-', 'o'], ['b', 'o', 'a', 't', '-', 'A', 'C', 'C'], [⟨['h', 'u', 'n', 'e'], ['b', 'o', 'a', 't'], none⟩, ⟨['o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['t', 'o', 'm', 'e', '-', 'r', 'a', 'r', 'e', 'r', 'u', '-', 'k', 'a', '-', 'o'], ['p', 'a', 'r', 'k', '-', 'c', 'a', 'n', '-', 'Q', '-', 'A', 'C', 'C'], [⟨['t', 'o', 'm', 'e'], ['p', 'a', 'r', 'k'], none⟩, ⟨['r', 'a', 'r', 'e', 'r', 'u'], ['c', 'a', 'n'], some '-'⟩, ⟨['k', 'a'], ['Q'], some '-'⟩, ⟨['o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['s', 'i', 'n', 'p', 'a', 'i', '-', 's', 'i', 't', 'e', 'i', 'r', 'u'], ['w', 'o', 'r', 'r', 'y', '-', 'd', 'o', '.', 'A', 'S', 'P'], [⟨['s', 'i', 'n', 'p', 'a', 'i'], ['w', 'o', 'r', 'r', 'y'], none⟩, ⟨['s', 'i', 't', 'e', 'i', 'r', 'u'], ['d', 'o', '.', 'A', 'S', 'P'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Al's father recently bought a new boat and is visiting Amsterdam with it. He is sure that there must be a place in Amsterdam where he can dock his boat, and he would be happy to dock his boat anywhere. However, for any specific place, he does not know whether it still has spots available, and he is anxiously trying to find out where exactly he can dock his boat."
    judgment := .acceptable
    verdict := some true
    contrasts := []
    readings := []
    spans := [⟨4, 1, "predicate", some "sinpai"⟩]
    paperFeatures := [("clause", "constituent")] }

def ja_32b : Datum :=
  { id := "qingetal2025_ja_32b"
    source := ⟨"qing-uegaki-2025", "(32b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nucl1643"
    primaryText := "Kare-wa Y-ni hune-o tome-rareru-no-o sinpai-siteiru."
    glossedTokens := [("Kare-wa", "he-TOP"), ("Y-ni", "Y-LOC"), ("hune-o", "boat-ACC"), ("tome-rareru-no-o", "park-can-NMZ-ACC"), ("sinpai-siteiru", "worry-do.ASP")]
    glossedWords := [⟨['K', 'a', 'r', 'e', '-', 'w', 'a'], ['h', 'e', '-', 'T', 'O', 'P'], [⟨['K', 'a', 'r', 'e'], ['h', 'e'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['Y', '-', 'n', 'i'], ['Y', '-', 'L', 'O', 'C'], [⟨['Y'], ['Y'], none⟩, ⟨['n', 'i'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['h', 'u', 'n', 'e', '-', 'o'], ['b', 'o', 'a', 't', '-', 'A', 'C', 'C'], [⟨['h', 'u', 'n', 'e'], ['b', 'o', 'a', 't'], none⟩, ⟨['o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['t', 'o', 'm', 'e', '-', 'r', 'a', 'r', 'e', 'r', 'u', '-', 'n', 'o', '-', 'o'], ['p', 'a', 'r', 'k', '-', 'c', 'a', 'n', '-', 'N', 'M', 'Z', '-', 'A', 'C', 'C'], [⟨['t', 'o', 'm', 'e'], ['p', 'a', 'r', 'k'], none⟩, ⟨['r', 'a', 'r', 'e', 'r', 'u'], ['c', 'a', 'n'], some '-'⟩, ⟨['n', 'o'], ['N', 'M', 'Z'], some '-'⟩, ⟨['o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['s', 'i', 'n', 'p', 'a', 'i', '-', 's', 'i', 't', 'e', 'i', 'r', 'u'], ['w', 'o', 'r', 'r', 'y', '-', 'd', 'o', '.', 'A', 'S', 'P'], [⟨['s', 'i', 'n', 'p', 'a', 'i'], ['w', 'o', 'r', 'r', 'y'], none⟩, ⟨['s', 'i', 't', 'e', 'i', 'r', 'u'], ['d', 'o', '.', 'A', 'S', 'P'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Al's father recently bought a new boat and is visiting Amsterdam with it. He is sure that there must be a place in Amsterdam where he can dock his boat, and he would be happy to dock his boat anywhere. However, for any specific place, he does not know whether it still has spots available, and he is anxiously trying to find out where exactly he can dock his boat."
    judgment := .acceptable
    verdict := some false
    contrasts := []
    readings := []
    spans := [⟨4, 1, "predicate", some "sinpai"⟩]
    paperFeatures := [("clause", "declarative")] }

def ja_38 : Datum :=
  { id := "qingetal2025_ja_38"
    source := ⟨"qing-uegaki-2025", "(38)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nucl1643"
    primaryText := "John-wa nani-o kiru-beki-ka-o sinpai-siteiru."
    glossedTokens := [("John-wa", "John-TOP"), ("nani-o", "what-ACC"), ("kiru-beki-ka-o", "wear-should-Q-ACC"), ("sinpai-siteiru", "worry-ASP")]
    glossedWords := [⟨['J', 'o', 'h', 'n', '-', 'w', 'a'], ['J', 'o', 'h', 'n', '-', 'T', 'O', 'P'], [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['n', 'a', 'n', 'i', '-', 'o'], ['w', 'h', 'a', 't', '-', 'A', 'C', 'C'], [⟨['n', 'a', 'n', 'i'], ['w', 'h', 'a', 't'], none⟩, ⟨['o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['k', 'i', 'r', 'u', '-', 'b', 'e', 'k', 'i', '-', 'k', 'a', '-', 'o'], ['w', 'e', 'a', 'r', '-', 's', 'h', 'o', 'u', 'l', 'd', '-', 'Q', '-', 'A', 'C', 'C'], [⟨['k', 'i', 'r', 'u'], ['w', 'e', 'a', 'r'], none⟩, ⟨['b', 'e', 'k', 'i'], ['s', 'h', 'o', 'u', 'l', 'd'], some '-'⟩, ⟨['k', 'a'], ['Q'], some '-'⟩, ⟨['o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['s', 'i', 'n', 'p', 'a', 'i', '-', 's', 'i', 't', 'e', 'i', 'r', 'u'], ['w', 'o', 'r', 'r', 'y', '-', 'A', 'S', 'P'], [⟨['s', 'i', 'n', 'p', 'a', 'i'], ['w', 'o', 'r', 'r', 'y'], none⟩, ⟨['s', 'i', 't', 'e', 'i', 'r', 'u'], ['A', 'S', 'P'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Sam is invited to an event. Not knowing much about it, they do not know what type of clothes would be appropriate: Casual, business casual, formal? They possess all relevant types of clothes and are happy to wear anything as long as it is appropriate for the occasion."
    judgment := .acceptable
    verdict := some true
    contrasts := []
    readings := []
    spans := [⟨3, 1, "predicate", some "sinpai"⟩]
    paperFeatures := [("clause", "constituent")] }

def ja_54_goodfriend : Datum :=
  { id := "qingetal2025_ja_54_goodfriend"
    source := ⟨"qing-uegaki-2025", "(54)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nucl1643"
    primaryText := "John-wa rinzin-ga konsyuumatu ie-ni iru ka-o osore-teiru."
    glossedTokens := [("John-wa", "John-TOP"), ("rinzin-ga", "neighbor-NOM"), ("konsyuumatu", "this.weekend"), ("ie-ni", "home-LOC"), ("iru", "be"), ("ka-o", "Q-ACC"), ("osore-teiru", "fear-ASP")]
    glossedWords := [⟨['J', 'o', 'h', 'n', '-', 'w', 'a'], ['J', 'o', 'h', 'n', '-', 'T', 'O', 'P'], [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['r', 'i', 'n', 'z', 'i', 'n', '-', 'g', 'a'], ['n', 'e', 'i', 'g', 'h', 'b', 'o', 'r', '-', 'N', 'O', 'M'], [⟨['r', 'i', 'n', 'z', 'i', 'n'], ['n', 'e', 'i', 'g', 'h', 'b', 'o', 'r'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['k', 'o', 'n', 's', 'y', 'u', 'u', 'm', 'a', 't', 'u'], ['t', 'h', 'i', 's', '.', 'w', 'e', 'e', 'k', 'e', 'n', 'd'], [⟨['k', 'o', 'n', 's', 'y', 'u', 'u', 'm', 'a', 't', 'u'], ['t', 'h', 'i', 's', '.', 'w', 'e', 'e', 'k', 'e', 'n', 'd'], none⟩]⟩, ⟨['i', 'e', '-', 'n', 'i'], ['h', 'o', 'm', 'e', '-', 'L', 'O', 'C'], [⟨['i', 'e'], ['h', 'o', 'm', 'e'], none⟩, ⟨['n', 'i'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['i', 'r', 'u'], ['b', 'e'], [⟨['i', 'r', 'u'], ['b', 'e'], none⟩]⟩, ⟨['k', 'a', '-', 'o'], ['Q', '-', 'A', 'C', 'C'], [⟨['k', 'a'], ['Q'], none⟩, ⟨['o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['o', 's', 'o', 'r', 'e', '-', 't', 'e', 'i', 'r', 'u'], ['f', 'e', 'a', 'r', '-', 'A', 'S', 'P'], [⟨['o', 's', 'o', 'r', 'e'], ['f', 'e', 'a', 'r'], none⟩, ⟨['t', 'e', 'i', 'r', 'u'], ['A', 'S', 'P'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "John and his neighbor are good friends. His neighbor is away on a business trip, which may be long or short. John wants to throw a party this weekend."
    judgment := .acceptable
    verdict := some true
    contrasts := []
    readings := []
    spans := [⟨6, 1, "predicate", some "osore"⟩]
    paperFeatures := [("clause", "polar"), ("answer", "negation")] }

def ja_54_noisehater : Datum :=
  { id := "qingetal2025_ja_54_noisehater"
    source := ⟨"qing-uegaki-2025", "(54)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nucl1643"
    primaryText := "John-wa rinzin-ga konsyuumatu ie-ni iru ka-o osore-teiru."
    glossedTokens := [("John-wa", "John-TOP"), ("rinzin-ga", "neighbor-NOM"), ("konsyuumatu", "this.weekend"), ("ie-ni", "home-LOC"), ("iru", "be"), ("ka-o", "Q-ACC"), ("osore-teiru", "fear-ASP")]
    glossedWords := [⟨['J', 'o', 'h', 'n', '-', 'w', 'a'], ['J', 'o', 'h', 'n', '-', 'T', 'O', 'P'], [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['r', 'i', 'n', 'z', 'i', 'n', '-', 'g', 'a'], ['n', 'e', 'i', 'g', 'h', 'b', 'o', 'r', '-', 'N', 'O', 'M'], [⟨['r', 'i', 'n', 'z', 'i', 'n'], ['n', 'e', 'i', 'g', 'h', 'b', 'o', 'r'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['k', 'o', 'n', 's', 'y', 'u', 'u', 'm', 'a', 't', 'u'], ['t', 'h', 'i', 's', '.', 'w', 'e', 'e', 'k', 'e', 'n', 'd'], [⟨['k', 'o', 'n', 's', 'y', 'u', 'u', 'm', 'a', 't', 'u'], ['t', 'h', 'i', 's', '.', 'w', 'e', 'e', 'k', 'e', 'n', 'd'], none⟩]⟩, ⟨['i', 'e', '-', 'n', 'i'], ['h', 'o', 'm', 'e', '-', 'L', 'O', 'C'], [⟨['i', 'e'], ['h', 'o', 'm', 'e'], none⟩, ⟨['n', 'i'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['i', 'r', 'u'], ['b', 'e'], [⟨['i', 'r', 'u'], ['b', 'e'], none⟩]⟩, ⟨['k', 'a', '-', 'o'], ['Q', '-', 'A', 'C', 'C'], [⟨['k', 'a'], ['Q'], none⟩, ⟨['o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['o', 's', 'o', 'r', 'e', '-', 't', 'e', 'i', 'r', 'u'], ['f', 'e', 'a', 'r', '-', 'A', 'S', 'P'], [⟨['o', 's', 'o', 'r', 'e'], ['f', 'e', 'a', 'r'], none⟩, ⟨['t', 'e', 'i', 'r', 'u'], ['A', 'S', 'P'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "John likes to invite his friends over to party, but his neighbor hates noise and they have had several heated quarrels. His neighbor is away on a business trip, which may be long or short. John wants to throw a party this weekend."
    judgment := .acceptable
    verdict := some true
    contrasts := []
    readings := []
    spans := [⟨6, 1, "predicate", some "osore"⟩]
    paperFeatures := [("clause", "polar"), ("answer", "radical")] }

def ja_55 : Datum :=
  { id := "qingetal2025_ja_55"
    source := ⟨"qing-uegaki-2025", "(55)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nucl1643"
    primaryText := "John-wa dono sensyu-ga sono siai-de katu-ka osore-teiru."
    glossedTokens := [("John-wa", "John-TOP"), ("dono", "which"), ("sensyu-ga", "player-NOM"), ("sono", "the"), ("siai-de", "match-LOC"), ("katu-ka", "win-Q"), ("osore-teiru", "fear-ASP")]
    glossedWords := [⟨['J', 'o', 'h', 'n', '-', 'w', 'a'], ['J', 'o', 'h', 'n', '-', 'T', 'O', 'P'], [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['d', 'o', 'n', 'o'], ['w', 'h', 'i', 'c', 'h'], [⟨['d', 'o', 'n', 'o'], ['w', 'h', 'i', 'c', 'h'], none⟩]⟩, ⟨['s', 'e', 'n', 's', 'y', 'u', '-', 'g', 'a'], ['p', 'l', 'a', 'y', 'e', 'r', '-', 'N', 'O', 'M'], [⟨['s', 'e', 'n', 's', 'y', 'u'], ['p', 'l', 'a', 'y', 'e', 'r'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['s', 'o', 'n', 'o'], ['t', 'h', 'e'], [⟨['s', 'o', 'n', 'o'], ['t', 'h', 'e'], none⟩]⟩, ⟨['s', 'i', 'a', 'i', '-', 'd', 'e'], ['m', 'a', 't', 'c', 'h', '-', 'L', 'O', 'C'], [⟨['s', 'i', 'a', 'i'], ['m', 'a', 't', 'c', 'h'], none⟩, ⟨['d', 'e'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['k', 'a', 't', 'u', '-', 'k', 'a'], ['w', 'i', 'n', '-', 'Q'], [⟨['k', 'a', 't', 'u'], ['w', 'i', 'n'], none⟩, ⟨['k', 'a'], ['Q'], some '-'⟩]⟩, ⟨['o', 's', 'o', 'r', 'e', '-', 't', 'e', 'i', 'r', 'u'], ['f', 'e', 'a', 'r', '-', 'A', 'S', 'P'], [⟨['o', 's', 'o', 'r', 'e'], ['f', 'e', 'a', 'r'], none⟩, ⟨['t', 'e', 'i', 'r', 'u'], ['A', 'S', 'P'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨6, 1, "predicate", some "osore"⟩]
    paperFeatures := [("clause", "constituent")] }

def ja_56 : Datum :=
  { id := "qingetal2025_ja_56"
    source := ⟨"qing-uegaki-2025", "(56)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nucl1643"
    primaryText := "John-wa dono sensyu-ga sono siai-de katu-ka osore-teinai."
    glossedTokens := [("John-wa", "John-TOP"), ("dono", "which"), ("sensyu-ga", "player-NOM"), ("sono", "the"), ("siai-de", "match-LOC"), ("katu-ka", "win-Q"), ("osore-teinai", "fear-ASP.NEG")]
    glossedWords := [⟨['J', 'o', 'h', 'n', '-', 'w', 'a'], ['J', 'o', 'h', 'n', '-', 'T', 'O', 'P'], [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['d', 'o', 'n', 'o'], ['w', 'h', 'i', 'c', 'h'], [⟨['d', 'o', 'n', 'o'], ['w', 'h', 'i', 'c', 'h'], none⟩]⟩, ⟨['s', 'e', 'n', 's', 'y', 'u', '-', 'g', 'a'], ['p', 'l', 'a', 'y', 'e', 'r', '-', 'N', 'O', 'M'], [⟨['s', 'e', 'n', 's', 'y', 'u'], ['p', 'l', 'a', 'y', 'e', 'r'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['s', 'o', 'n', 'o'], ['t', 'h', 'e'], [⟨['s', 'o', 'n', 'o'], ['t', 'h', 'e'], none⟩]⟩, ⟨['s', 'i', 'a', 'i', '-', 'd', 'e'], ['m', 'a', 't', 'c', 'h', '-', 'L', 'O', 'C'], [⟨['s', 'i', 'a', 'i'], ['m', 'a', 't', 'c', 'h'], none⟩, ⟨['d', 'e'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['k', 'a', 't', 'u', '-', 'k', 'a'], ['w', 'i', 'n', '-', 'Q'], [⟨['k', 'a', 't', 'u'], ['w', 'i', 'n'], none⟩, ⟨['k', 'a'], ['Q'], some '-'⟩]⟩, ⟨['o', 's', 'o', 'r', 'e', '-', 't', 'e', 'i', 'n', 'a', 'i'], ['f', 'e', 'a', 'r', '-', 'A', 'S', 'P', '.', 'N', 'E', 'G'], [⟨['o', 's', 'o', 'r', 'e'], ['f', 'e', 'a', 'r'], none⟩, ⟨['t', 'e', 'i', 'n', 'a', 'i'], ['A', 'S', 'P', '.', 'N', 'E', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "There exists no player x such that John fears that x will win the match."
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨6, 1, "predicate", some "osore"⟩]
    paperFeatures := [("clause", "constituent"), ("polarity", "negated")] }

def es_33a : Datum :=
  { id := "qingetal2025_es_33a"
    source := ⟨"qing-uegaki-2025", "(33a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1288"
    primaryText := "A mi padre le preocupa dónde puede atracar Antonio el barco."
    glossedTokens := [("A", "to"), ("mi", "my"), ("padre", "father"), ("le", "CL"), ("preocupa", "worries"), ("dónde", "where"), ("puede", "could.IND"), ("atracar", "dock"), ("Antonio", "Antonio"), ("el", "the"), ("barco", "boat")]
    glossedWords := [⟨['A'], ['t', 'o'], [⟨['A'], ['t', 'o'], none⟩]⟩, ⟨['m', 'i'], ['m', 'y'], [⟨['m', 'i'], ['m', 'y'], none⟩]⟩, ⟨['p', 'a', 'd', 'r', 'e'], ['f', 'a', 't', 'h', 'e', 'r'], [⟨['p', 'a', 'd', 'r', 'e'], ['f', 'a', 't', 'h', 'e', 'r'], none⟩]⟩, ⟨['l', 'e'], ['C', 'L'], [⟨['l', 'e'], ['C', 'L'], none⟩]⟩, ⟨['p', 'r', 'e', 'o', 'c', 'u', 'p', 'a'], ['w', 'o', 'r', 'r', 'i', 'e', 's'], [⟨['p', 'r', 'e', 'o', 'c', 'u', 'p', 'a'], ['w', 'o', 'r', 'r', 'i', 'e', 's'], none⟩]⟩, ⟨['d', 'ó', 'n', 'd', 'e'], ['w', 'h', 'e', 'r', 'e'], [⟨['d', 'ó', 'n', 'd', 'e'], ['w', 'h', 'e', 'r', 'e'], none⟩]⟩, ⟨['p', 'u', 'e', 'd', 'e'], ['c', 'o', 'u', 'l', 'd', '.', 'I', 'N', 'D'], [⟨['p', 'u', 'e', 'd', 'e'], ['c', 'o', 'u', 'l', 'd', '.', 'I', 'N', 'D'], none⟩]⟩, ⟨['a', 't', 'r', 'a', 'c', 'a', 'r'], ['d', 'o', 'c', 'k'], [⟨['a', 't', 'r', 'a', 'c', 'a', 'r'], ['d', 'o', 'c', 'k'], none⟩]⟩, ⟨['A', 'n', 't', 'o', 'n', 'i', 'o'], ['A', 'n', 't', 'o', 'n', 'i', 'o'], [⟨['A', 'n', 't', 'o', 'n', 'i', 'o'], ['A', 'n', 't', 'o', 'n', 'i', 'o'], none⟩]⟩, ⟨['e', 'l'], ['t', 'h', 'e'], [⟨['e', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['b', 'a', 'r', 'c', 'o'], ['b', 'o', 'a', 't'], [⟨['b', 'a', 'r', 'c', 'o'], ['b', 'o', 'a', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Al's father recently bought a new boat and is visiting Amsterdam with it. He is sure that there must be a place in Amsterdam where he can dock his boat, and he would be happy to dock his boat anywhere. However, for any specific place, he does not know whether it still has spots available, and he is anxiously trying to find out where exactly he can dock his boat."
    judgment := .acceptable
    verdict := some true
    contrasts := []
    readings := []
    spans := [⟨4, 1, "predicate", some "preocupar"⟩]
    paperFeatures := [("clause", "constituent")] }

def es_33b : Datum :=
  { id := "qingetal2025_es_33b"
    source := ⟨"qing-uegaki-2025", "(33b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1288"
    primaryText := "A mi padre le preocupa que Antonio pueda atracar el barco en Y."
    glossedTokens := [("A", "to"), ("mi", "my"), ("padre", "father"), ("le", "CL"), ("preocupa", "worries"), ("que", "that"), ("Antonio", "Antonio"), ("pueda", "can.SUBJ"), ("atracar", "dock"), ("el", "the"), ("barco", "boat"), ("en", "at"), ("Y", "Y")]
    glossedWords := [⟨['A'], ['t', 'o'], [⟨['A'], ['t', 'o'], none⟩]⟩, ⟨['m', 'i'], ['m', 'y'], [⟨['m', 'i'], ['m', 'y'], none⟩]⟩, ⟨['p', 'a', 'd', 'r', 'e'], ['f', 'a', 't', 'h', 'e', 'r'], [⟨['p', 'a', 'd', 'r', 'e'], ['f', 'a', 't', 'h', 'e', 'r'], none⟩]⟩, ⟨['l', 'e'], ['C', 'L'], [⟨['l', 'e'], ['C', 'L'], none⟩]⟩, ⟨['p', 'r', 'e', 'o', 'c', 'u', 'p', 'a'], ['w', 'o', 'r', 'r', 'i', 'e', 's'], [⟨['p', 'r', 'e', 'o', 'c', 'u', 'p', 'a'], ['w', 'o', 'r', 'r', 'i', 'e', 's'], none⟩]⟩, ⟨['q', 'u', 'e'], ['t', 'h', 'a', 't'], [⟨['q', 'u', 'e'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['A', 'n', 't', 'o', 'n', 'i', 'o'], ['A', 'n', 't', 'o', 'n', 'i', 'o'], [⟨['A', 'n', 't', 'o', 'n', 'i', 'o'], ['A', 'n', 't', 'o', 'n', 'i', 'o'], none⟩]⟩, ⟨['p', 'u', 'e', 'd', 'a'], ['c', 'a', 'n', '.', 'S', 'U', 'B', 'J'], [⟨['p', 'u', 'e', 'd', 'a'], ['c', 'a', 'n', '.', 'S', 'U', 'B', 'J'], none⟩]⟩, ⟨['a', 't', 'r', 'a', 'c', 'a', 'r'], ['d', 'o', 'c', 'k'], [⟨['a', 't', 'r', 'a', 'c', 'a', 'r'], ['d', 'o', 'c', 'k'], none⟩]⟩, ⟨['e', 'l'], ['t', 'h', 'e'], [⟨['e', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['b', 'a', 'r', 'c', 'o'], ['b', 'o', 'a', 't'], [⟨['b', 'a', 'r', 'c', 'o'], ['b', 'o', 'a', 't'], none⟩]⟩, ⟨['e', 'n'], ['a', 't'], [⟨['e', 'n'], ['a', 't'], none⟩]⟩, ⟨['Y'], ['Y'], [⟨['Y'], ['Y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Al's father recently bought a new boat and is visiting Amsterdam with it. He is sure that there must be a place in Amsterdam where he can dock his boat, and he would be happy to dock his boat anywhere. However, for any specific place, he does not know whether it still has spots available, and he is anxiously trying to find out where exactly he can dock his boat."
    judgment := .acceptable
    verdict := some false
    contrasts := []
    readings := []
    spans := [⟨4, 1, "predicate", some "preocupar"⟩]
    paperFeatures := [("clause", "declarative")] }

def es_39 : Datum :=
  { id := "qingetal2025_es_39"
    source := ⟨"qing-uegaki-2025", "(39)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1288"
    primaryText := "A Juan le preocupa qué debería ponerse."
    glossedTokens := [("A", "to"), ("Juan", "Juan"), ("le", "CL"), ("preocupa", "worries"), ("qué", "what"), ("debería", "should.3SG"), ("ponerse", "wear")]
    glossedWords := [⟨['A'], ['t', 'o'], [⟨['A'], ['t', 'o'], none⟩]⟩, ⟨['J', 'u', 'a', 'n'], ['J', 'u', 'a', 'n'], [⟨['J', 'u', 'a', 'n'], ['J', 'u', 'a', 'n'], none⟩]⟩, ⟨['l', 'e'], ['C', 'L'], [⟨['l', 'e'], ['C', 'L'], none⟩]⟩, ⟨['p', 'r', 'e', 'o', 'c', 'u', 'p', 'a'], ['w', 'o', 'r', 'r', 'i', 'e', 's'], [⟨['p', 'r', 'e', 'o', 'c', 'u', 'p', 'a'], ['w', 'o', 'r', 'r', 'i', 'e', 's'], none⟩]⟩, ⟨['q', 'u', 'é'], ['w', 'h', 'a', 't'], [⟨['q', 'u', 'é'], ['w', 'h', 'a', 't'], none⟩]⟩, ⟨['d', 'e', 'b', 'e', 'r', 'í', 'a'], ['s', 'h', 'o', 'u', 'l', 'd', '.', '3', 'S', 'G'], [⟨['d', 'e', 'b', 'e', 'r', 'í', 'a'], ['s', 'h', 'o', 'u', 'l', 'd', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['p', 'o', 'n', 'e', 'r', 's', 'e'], ['w', 'e', 'a', 'r'], [⟨['p', 'o', 'n', 'e', 'r', 's', 'e'], ['w', 'e', 'a', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Sam is invited to an event. Not knowing much about it, they do not know what type of clothes would be appropriate: Casual, business casual, formal? They possess all relevant types of clothes and are happy to wear anything as long as it is appropriate for the occasion."
    judgment := .acceptable
    verdict := some true
    contrasts := []
    readings := []
    spans := [⟨3, 1, "predicate", some "preocupar"⟩]
    paperFeatures := [("clause", "constituent")] }

def es_57 : Datum :=
  { id := "qingetal2025_es_57"
    source := ⟨"qing-uegaki-2025", "(57)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1288"
    primaryText := "Juan teme qué puede pasar si su vecino está en casa."
    glossedTokens := [("Juan", "Juan"), ("teme", "fears"), ("qué", "what"), ("puede", "can.IND"), ("pasar", "happen"), ("si", "if"), ("su", "his"), ("vecino", "neighbor"), ("está", "is"), ("en", "at"), ("casa", "home")]
    glossedWords := [⟨['J', 'u', 'a', 'n'], ['J', 'u', 'a', 'n'], [⟨['J', 'u', 'a', 'n'], ['J', 'u', 'a', 'n'], none⟩]⟩, ⟨['t', 'e', 'm', 'e'], ['f', 'e', 'a', 'r', 's'], [⟨['t', 'e', 'm', 'e'], ['f', 'e', 'a', 'r', 's'], none⟩]⟩, ⟨['q', 'u', 'é'], ['w', 'h', 'a', 't'], [⟨['q', 'u', 'é'], ['w', 'h', 'a', 't'], none⟩]⟩, ⟨['p', 'u', 'e', 'd', 'e'], ['c', 'a', 'n', '.', 'I', 'N', 'D'], [⟨['p', 'u', 'e', 'd', 'e'], ['c', 'a', 'n', '.', 'I', 'N', 'D'], none⟩]⟩, ⟨['p', 'a', 's', 'a', 'r'], ['h', 'a', 'p', 'p', 'e', 'n'], [⟨['p', 'a', 's', 'a', 'r'], ['h', 'a', 'p', 'p', 'e', 'n'], none⟩]⟩, ⟨['s', 'i'], ['i', 'f'], [⟨['s', 'i'], ['i', 'f'], none⟩]⟩, ⟨['s', 'u'], ['h', 'i', 's'], [⟨['s', 'u'], ['h', 'i', 's'], none⟩]⟩, ⟨['v', 'e', 'c', 'i', 'n', 'o'], ['n', 'e', 'i', 'g', 'h', 'b', 'o', 'r'], [⟨['v', 'e', 'c', 'i', 'n', 'o'], ['n', 'e', 'i', 'g', 'h', 'b', 'o', 'r'], none⟩]⟩, ⟨['e', 's', 't', 'á'], ['i', 's'], [⟨['e', 's', 't', 'á'], ['i', 's'], none⟩]⟩, ⟨['e', 'n'], ['a', 't'], [⟨['e', 'n'], ['a', 't'], none⟩]⟩, ⟨['c', 'a', 's', 'a'], ['h', 'o', 'm', 'e'], [⟨['c', 'a', 's', 'a'], ['h', 'o', 'm', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "predicate", some "temer"⟩]
    paperFeatures := [("clause", "constituent")] }

def es_58 : Datum :=
  { id := "qingetal2025_es_58"
    source := ⟨"qing-uegaki-2025", "(58)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1288"
    primaryText := "Juan teme si su vecino estará en casa."
    glossedTokens := [("Juan", "Juan"), ("teme", "fears"), ("si", "whether"), ("su", "his"), ("vecino", "neighbor"), ("estará", "will.be"), ("en", "at"), ("casa", "home")]
    glossedWords := [⟨['J', 'u', 'a', 'n'], ['J', 'u', 'a', 'n'], [⟨['J', 'u', 'a', 'n'], ['J', 'u', 'a', 'n'], none⟩]⟩, ⟨['t', 'e', 'm', 'e'], ['f', 'e', 'a', 'r', 's'], [⟨['t', 'e', 'm', 'e'], ['f', 'e', 'a', 'r', 's'], none⟩]⟩, ⟨['s', 'i'], ['w', 'h', 'e', 't', 'h', 'e', 'r'], [⟨['s', 'i'], ['w', 'h', 'e', 't', 'h', 'e', 'r'], none⟩]⟩, ⟨['s', 'u'], ['h', 'i', 's'], [⟨['s', 'u'], ['h', 'i', 's'], none⟩]⟩, ⟨['v', 'e', 'c', 'i', 'n', 'o'], ['n', 'e', 'i', 'g', 'h', 'b', 'o', 'r'], [⟨['v', 'e', 'c', 'i', 'n', 'o'], ['n', 'e', 'i', 'g', 'h', 'b', 'o', 'r'], none⟩]⟩, ⟨['e', 's', 't', 'a', 'r', 'á'], ['w', 'i', 'l', 'l', '.', 'b', 'e'], [⟨['e', 's', 't', 'a', 'r', 'á'], ['w', 'i', 'l', 'l', '.', 'b', 'e'], none⟩]⟩, ⟨['e', 'n'], ['a', 't'], [⟨['e', 'n'], ['a', 't'], none⟩]⟩, ⟨['c', 'a', 's', 'a'], ['h', 'o', 'm', 'e'], [⟨['c', 'a', 's', 'a'], ['h', 'o', 'm', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "predicate", some "temer"⟩]
    paperFeatures := [("clause", "polar")] }

def tr_34a : Datum :=
  { id := "qingetal2025_tr_34a"
    source := ⟨"qing-uegaki-2025", "(34a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nucl1301"
    primaryText := "Baba-m gemi-sin-i nereye demirle-yeceğ-in-den endişelen-iyor."
    glossedTokens := [("Baba-m", "dad-my"), ("gemi-sin-i", "boat-his-ACC"), ("nereye", "where"), ("demirle-yeceğ-in-den", "anchor.V-NMZ.FUT-3S.POSS-ABL"), ("endişelen-iyor", "worry-IPFV.PRES")]
    glossedWords := [⟨['B', 'a', 'b', 'a', '-', 'm'], ['d', 'a', 'd', '-', 'm', 'y'], [⟨['B', 'a', 'b', 'a'], ['d', 'a', 'd'], none⟩, ⟨['m'], ['m', 'y'], some '-'⟩]⟩, ⟨['g', 'e', 'm', 'i', '-', 's', 'i', 'n', '-', 'i'], ['b', 'o', 'a', 't', '-', 'h', 'i', 's', '-', 'A', 'C', 'C'], [⟨['g', 'e', 'm', 'i'], ['b', 'o', 'a', 't'], none⟩, ⟨['s', 'i', 'n'], ['h', 'i', 's'], some '-'⟩, ⟨['i'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['n', 'e', 'r', 'e', 'y', 'e'], ['w', 'h', 'e', 'r', 'e'], [⟨['n', 'e', 'r', 'e', 'y', 'e'], ['w', 'h', 'e', 'r', 'e'], none⟩]⟩, ⟨['d', 'e', 'm', 'i', 'r', 'l', 'e', '-', 'y', 'e', 'c', 'e', 'ğ', '-', 'i', 'n', '-', 'd', 'e', 'n'], ['a', 'n', 'c', 'h', 'o', 'r', '.', 'V', '-', 'N', 'M', 'Z', '.', 'F', 'U', 'T', '-', '3', 'S', '.', 'P', 'O', 'S', 'S', '-', 'A', 'B', 'L'], [⟨['d', 'e', 'm', 'i', 'r', 'l', 'e'], ['a', 'n', 'c', 'h', 'o', 'r', '.', 'V'], none⟩, ⟨['y', 'e', 'c', 'e', 'ğ'], ['N', 'M', 'Z', '.', 'F', 'U', 'T'], some '-'⟩, ⟨['i', 'n'], ['3', 'S', '.', 'P', 'O', 'S', 'S'], some '-'⟩, ⟨['d', 'e', 'n'], ['A', 'B', 'L'], some '-'⟩]⟩, ⟨['e', 'n', 'd', 'i', 'ş', 'e', 'l', 'e', 'n', '-', 'i', 'y', 'o', 'r'], ['w', 'o', 'r', 'r', 'y', '-', 'I', 'P', 'F', 'V', '.', 'P', 'R', 'E', 'S'], [⟨['e', 'n', 'd', 'i', 'ş', 'e', 'l', 'e', 'n'], ['w', 'o', 'r', 'r', 'y'], none⟩, ⟨['i', 'y', 'o', 'r'], ['I', 'P', 'F', 'V', '.', 'P', 'R', 'E', 'S'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Al's father recently bought a new boat and is visiting Amsterdam with it. He is sure that there must be a place in Amsterdam where he can dock his boat, and he would be happy to dock his boat anywhere. However, for any specific place, he does not know whether it still has spots available, and he is anxiously trying to find out where exactly he can dock his boat."
    judgment := .acceptable
    verdict := some true
    contrasts := []
    readings := []
    spans := [⟨4, 1, "predicate", some "endiselen"⟩]
    paperFeatures := [("clause", "constituent")] }

def tr_34b : Datum :=
  { id := "qingetal2025_tr_34b"
    source := ⟨"qing-uegaki-2025", "(34b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nucl1301"
    primaryText := "Baba-m gemi-sin-i Y-ye demirle-yeceğ-in-den endişelen-iyor."
    glossedTokens := [("Baba-m", "dad-my"), ("gemi-sin-i", "boat-his-ACC"), ("Y-ye", "Y-LOC"), ("demirle-yeceğ-in-den", "anchor.V-NMZ.FUT-3S.POSS-ABL"), ("endişelen-iyor", "worry-IPFV.PRES")]
    glossedWords := [⟨['B', 'a', 'b', 'a', '-', 'm'], ['d', 'a', 'd', '-', 'm', 'y'], [⟨['B', 'a', 'b', 'a'], ['d', 'a', 'd'], none⟩, ⟨['m'], ['m', 'y'], some '-'⟩]⟩, ⟨['g', 'e', 'm', 'i', '-', 's', 'i', 'n', '-', 'i'], ['b', 'o', 'a', 't', '-', 'h', 'i', 's', '-', 'A', 'C', 'C'], [⟨['g', 'e', 'm', 'i'], ['b', 'o', 'a', 't'], none⟩, ⟨['s', 'i', 'n'], ['h', 'i', 's'], some '-'⟩, ⟨['i'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['Y', '-', 'y', 'e'], ['Y', '-', 'L', 'O', 'C'], [⟨['Y'], ['Y'], none⟩, ⟨['y', 'e'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['d', 'e', 'm', 'i', 'r', 'l', 'e', '-', 'y', 'e', 'c', 'e', 'ğ', '-', 'i', 'n', '-', 'd', 'e', 'n'], ['a', 'n', 'c', 'h', 'o', 'r', '.', 'V', '-', 'N', 'M', 'Z', '.', 'F', 'U', 'T', '-', '3', 'S', '.', 'P', 'O', 'S', 'S', '-', 'A', 'B', 'L'], [⟨['d', 'e', 'm', 'i', 'r', 'l', 'e'], ['a', 'n', 'c', 'h', 'o', 'r', '.', 'V'], none⟩, ⟨['y', 'e', 'c', 'e', 'ğ'], ['N', 'M', 'Z', '.', 'F', 'U', 'T'], some '-'⟩, ⟨['i', 'n'], ['3', 'S', '.', 'P', 'O', 'S', 'S'], some '-'⟩, ⟨['d', 'e', 'n'], ['A', 'B', 'L'], some '-'⟩]⟩, ⟨['e', 'n', 'd', 'i', 'ş', 'e', 'l', 'e', 'n', '-', 'i', 'y', 'o', 'r'], ['w', 'o', 'r', 'r', 'y', '-', 'I', 'P', 'F', 'V', '.', 'P', 'R', 'E', 'S'], [⟨['e', 'n', 'd', 'i', 'ş', 'e', 'l', 'e', 'n'], ['w', 'o', 'r', 'r', 'y'], none⟩, ⟨['i', 'y', 'o', 'r'], ['I', 'P', 'F', 'V', '.', 'P', 'R', 'E', 'S'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Al's father recently bought a new boat and is visiting Amsterdam with it. He is sure that there must be a place in Amsterdam where he can dock his boat, and he would be happy to dock his boat anywhere. However, for any specific place, he does not know whether it still has spots available, and he is anxiously trying to find out where exactly he can dock his boat."
    judgment := .acceptable
    verdict := some false
    contrasts := []
    readings := []
    spans := [⟨4, 1, "predicate", some "endiselen"⟩]
    paperFeatures := [("clause", "declarative")] }

def tr_40 : Datum :=
  { id := "qingetal2025_tr_40"
    source := ⟨"qing-uegaki-2025", "(40)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nucl1301"
    primaryText := "John ne giy-me-si gerek-tiğ-in-den endişelen-iyor."
    glossedTokens := [("John", "John"), ("ne", "what"), ("giy-me-si", "wear-NMZ-3S.POSS"), ("gerek-tiğ-in-den", "MOD-NMZ-3S.POSS-ABL"), ("endişelen-iyor", "worry-IPFV.PRES")]
    glossedWords := [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], none⟩]⟩, ⟨['n', 'e'], ['w', 'h', 'a', 't'], [⟨['n', 'e'], ['w', 'h', 'a', 't'], none⟩]⟩, ⟨['g', 'i', 'y', '-', 'm', 'e', '-', 's', 'i'], ['w', 'e', 'a', 'r', '-', 'N', 'M', 'Z', '-', '3', 'S', '.', 'P', 'O', 'S', 'S'], [⟨['g', 'i', 'y'], ['w', 'e', 'a', 'r'], none⟩, ⟨['m', 'e'], ['N', 'M', 'Z'], some '-'⟩, ⟨['s', 'i'], ['3', 'S', '.', 'P', 'O', 'S', 'S'], some '-'⟩]⟩, ⟨['g', 'e', 'r', 'e', 'k', '-', 't', 'i', 'ğ', '-', 'i', 'n', '-', 'd', 'e', 'n'], ['M', 'O', 'D', '-', 'N', 'M', 'Z', '-', '3', 'S', '.', 'P', 'O', 'S', 'S', '-', 'A', 'B', 'L'], [⟨['g', 'e', 'r', 'e', 'k'], ['M', 'O', 'D'], none⟩, ⟨['t', 'i', 'ğ'], ['N', 'M', 'Z'], some '-'⟩, ⟨['i', 'n'], ['3', 'S', '.', 'P', 'O', 'S', 'S'], some '-'⟩, ⟨['d', 'e', 'n'], ['A', 'B', 'L'], some '-'⟩]⟩, ⟨['e', 'n', 'd', 'i', 'ş', 'e', 'l', 'e', 'n', '-', 'i', 'y', 'o', 'r'], ['w', 'o', 'r', 'r', 'y', '-', 'I', 'P', 'F', 'V', '.', 'P', 'R', 'E', 'S'], [⟨['e', 'n', 'd', 'i', 'ş', 'e', 'l', 'e', 'n'], ['w', 'o', 'r', 'r', 'y'], none⟩, ⟨['i', 'y', 'o', 'r'], ['I', 'P', 'F', 'V', '.', 'P', 'R', 'E', 'S'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Sam is invited to an event. Not knowing much about it, they do not know what type of clothes would be appropriate: Casual, business casual, formal? They possess all relevant types of clothes and are happy to wear anything as long as it is appropriate for the occasion."
    judgment := .acceptable
    verdict := some true
    contrasts := []
    readings := []
    spans := [⟨4, 1, "predicate", some "endiselen"⟩]
    paperFeatures := [("clause", "constituent")] }

def tr_49_goodfriend : Datum :=
  { id := "qingetal2025_tr_49_goodfriend"
    source := ⟨"qing-uegaki-2025", "(49)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nucl1301"
    primaryText := "John komşu-sun-un haftasonu ev-de ol-up ol-ma-yacağ-ın-dan korkuyor."
    glossedTokens := [("John", "John"), ("komşu-sun-un", "neighbor-his-GEN"), ("haftasonu", "weekend"), ("ev-de", "home-LOC"), ("ol-up", "be-CONJ"), ("ol-ma-yacağ-ın-dan", "be-NEG-NMZ.FUT-3S.POSS-ABL"), ("korkuyor", "fear")]
    glossedWords := [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], none⟩]⟩, ⟨['k', 'o', 'm', 'ş', 'u', '-', 's', 'u', 'n', '-', 'u', 'n'], ['n', 'e', 'i', 'g', 'h', 'b', 'o', 'r', '-', 'h', 'i', 's', '-', 'G', 'E', 'N'], [⟨['k', 'o', 'm', 'ş', 'u'], ['n', 'e', 'i', 'g', 'h', 'b', 'o', 'r'], none⟩, ⟨['s', 'u', 'n'], ['h', 'i', 's'], some '-'⟩, ⟨['u', 'n'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['h', 'a', 'f', 't', 'a', 's', 'o', 'n', 'u'], ['w', 'e', 'e', 'k', 'e', 'n', 'd'], [⟨['h', 'a', 'f', 't', 'a', 's', 'o', 'n', 'u'], ['w', 'e', 'e', 'k', 'e', 'n', 'd'], none⟩]⟩, ⟨['e', 'v', '-', 'd', 'e'], ['h', 'o', 'm', 'e', '-', 'L', 'O', 'C'], [⟨['e', 'v'], ['h', 'o', 'm', 'e'], none⟩, ⟨['d', 'e'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['o', 'l', '-', 'u', 'p'], ['b', 'e', '-', 'C', 'O', 'N', 'J'], [⟨['o', 'l'], ['b', 'e'], none⟩, ⟨['u', 'p'], ['C', 'O', 'N', 'J'], some '-'⟩]⟩, ⟨['o', 'l', '-', 'm', 'a', '-', 'y', 'a', 'c', 'a', 'ğ', '-', 'ı', 'n', '-', 'd', 'a', 'n'], ['b', 'e', '-', 'N', 'E', 'G', '-', 'N', 'M', 'Z', '.', 'F', 'U', 'T', '-', '3', 'S', '.', 'P', 'O', 'S', 'S', '-', 'A', 'B', 'L'], [⟨['o', 'l'], ['b', 'e'], none⟩, ⟨['m', 'a'], ['N', 'E', 'G'], some '-'⟩, ⟨['y', 'a', 'c', 'a', 'ğ'], ['N', 'M', 'Z', '.', 'F', 'U', 'T'], some '-'⟩, ⟨['ı', 'n'], ['3', 'S', '.', 'P', 'O', 'S', 'S'], some '-'⟩, ⟨['d', 'a', 'n'], ['A', 'B', 'L'], some '-'⟩]⟩, ⟨['k', 'o', 'r', 'k', 'u', 'y', 'o', 'r'], ['f', 'e', 'a', 'r'], [⟨['k', 'o', 'r', 'k', 'u', 'y', 'o', 'r'], ['f', 'e', 'a', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "John and his neighbor are good friends. His neighbor is away on a business trip, which may be long or short. John wants to throw a party this weekend."
    judgment := .acceptable
    verdict := some true
    contrasts := []
    readings := []
    spans := [⟨6, 1, "predicate", some "kork"⟩]
    paperFeatures := [("clause", "polar"), ("answer", "negation")] }

def tr_49_noisehater : Datum :=
  { id := "qingetal2025_tr_49_noisehater"
    source := ⟨"qing-uegaki-2025", "(49)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nucl1301"
    primaryText := "John komşu-sun-un haftasonu ev-de ol-up ol-ma-yacağ-ın-dan korkuyor."
    glossedTokens := [("John", "John"), ("komşu-sun-un", "neighbor-his-GEN"), ("haftasonu", "weekend"), ("ev-de", "home-LOC"), ("ol-up", "be-CONJ"), ("ol-ma-yacağ-ın-dan", "be-NEG-NMZ.FUT-3S.POSS-ABL"), ("korkuyor", "fear")]
    glossedWords := [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], none⟩]⟩, ⟨['k', 'o', 'm', 'ş', 'u', '-', 's', 'u', 'n', '-', 'u', 'n'], ['n', 'e', 'i', 'g', 'h', 'b', 'o', 'r', '-', 'h', 'i', 's', '-', 'G', 'E', 'N'], [⟨['k', 'o', 'm', 'ş', 'u'], ['n', 'e', 'i', 'g', 'h', 'b', 'o', 'r'], none⟩, ⟨['s', 'u', 'n'], ['h', 'i', 's'], some '-'⟩, ⟨['u', 'n'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['h', 'a', 'f', 't', 'a', 's', 'o', 'n', 'u'], ['w', 'e', 'e', 'k', 'e', 'n', 'd'], [⟨['h', 'a', 'f', 't', 'a', 's', 'o', 'n', 'u'], ['w', 'e', 'e', 'k', 'e', 'n', 'd'], none⟩]⟩, ⟨['e', 'v', '-', 'd', 'e'], ['h', 'o', 'm', 'e', '-', 'L', 'O', 'C'], [⟨['e', 'v'], ['h', 'o', 'm', 'e'], none⟩, ⟨['d', 'e'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['o', 'l', '-', 'u', 'p'], ['b', 'e', '-', 'C', 'O', 'N', 'J'], [⟨['o', 'l'], ['b', 'e'], none⟩, ⟨['u', 'p'], ['C', 'O', 'N', 'J'], some '-'⟩]⟩, ⟨['o', 'l', '-', 'm', 'a', '-', 'y', 'a', 'c', 'a', 'ğ', '-', 'ı', 'n', '-', 'd', 'a', 'n'], ['b', 'e', '-', 'N', 'E', 'G', '-', 'N', 'M', 'Z', '.', 'F', 'U', 'T', '-', '3', 'S', '.', 'P', 'O', 'S', 'S', '-', 'A', 'B', 'L'], [⟨['o', 'l'], ['b', 'e'], none⟩, ⟨['m', 'a'], ['N', 'E', 'G'], some '-'⟩, ⟨['y', 'a', 'c', 'a', 'ğ'], ['N', 'M', 'Z', '.', 'F', 'U', 'T'], some '-'⟩, ⟨['ı', 'n'], ['3', 'S', '.', 'P', 'O', 'S', 'S'], some '-'⟩, ⟨['d', 'a', 'n'], ['A', 'B', 'L'], some '-'⟩]⟩, ⟨['k', 'o', 'r', 'k', 'u', 'y', 'o', 'r'], ['f', 'e', 'a', 'r'], [⟨['k', 'o', 'r', 'k', 'u', 'y', 'o', 'r'], ['f', 'e', 'a', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "John likes to invite his friends over to party, but his neighbor hates noise and they have had several heated quarrels. His neighbor is away on a business trip, which may be long or short. John wants to throw a party this weekend."
    judgment := .acceptable
    verdict := some true
    contrasts := []
    readings := []
    spans := [⟨6, 1, "predicate", some "kork"⟩]
    paperFeatures := [("clause", "polar"), ("answer", "radical")] }

def tr_52 : Datum :=
  { id := "qingetal2025_tr_52"
    source := ⟨"qing-uegaki-2025", "(52)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nucl1301"
    primaryText := "John maç-ı hangi oyuncu-nun kazan-acağ-ın-dan kork-uyor."
    glossedTokens := [("John", "John"), ("maç-ı", "match-ACC"), ("hangi", "which"), ("oyuncu-nun", "player-GEN"), ("kazan-acağ-ın-dan", "win-NMZ.FUT-3S.POSS-ABL"), ("kork-uyor", "fear-IPFV.PRES")]
    glossedWords := [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], none⟩]⟩, ⟨['m', 'a', 'ç', '-', 'ı'], ['m', 'a', 't', 'c', 'h', '-', 'A', 'C', 'C'], [⟨['m', 'a', 'ç'], ['m', 'a', 't', 'c', 'h'], none⟩, ⟨['ı'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['h', 'a', 'n', 'g', 'i'], ['w', 'h', 'i', 'c', 'h'], [⟨['h', 'a', 'n', 'g', 'i'], ['w', 'h', 'i', 'c', 'h'], none⟩]⟩, ⟨['o', 'y', 'u', 'n', 'c', 'u', '-', 'n', 'u', 'n'], ['p', 'l', 'a', 'y', 'e', 'r', '-', 'G', 'E', 'N'], [⟨['o', 'y', 'u', 'n', 'c', 'u'], ['p', 'l', 'a', 'y', 'e', 'r'], none⟩, ⟨['n', 'u', 'n'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['k', 'a', 'z', 'a', 'n', '-', 'a', 'c', 'a', 'ğ', '-', 'ı', 'n', '-', 'd', 'a', 'n'], ['w', 'i', 'n', '-', 'N', 'M', 'Z', '.', 'F', 'U', 'T', '-', '3', 'S', '.', 'P', 'O', 'S', 'S', '-', 'A', 'B', 'L'], [⟨['k', 'a', 'z', 'a', 'n'], ['w', 'i', 'n'], none⟩, ⟨['a', 'c', 'a', 'ğ'], ['N', 'M', 'Z', '.', 'F', 'U', 'T'], some '-'⟩, ⟨['ı', 'n'], ['3', 'S', '.', 'P', 'O', 'S', 'S'], some '-'⟩, ⟨['d', 'a', 'n'], ['A', 'B', 'L'], some '-'⟩]⟩, ⟨['k', 'o', 'r', 'k', '-', 'u', 'y', 'o', 'r'], ['f', 'e', 'a', 'r', '-', 'I', 'P', 'F', 'V', '.', 'P', 'R', 'E', 'S'], [⟨['k', 'o', 'r', 'k'], ['f', 'e', 'a', 'r'], none⟩, ⟨['u', 'y', 'o', 'r'], ['I', 'P', 'F', 'V', '.', 'P', 'R', 'E', 'S'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨5, 1, "predicate", some "kork"⟩]
    paperFeatures := [("clause", "constituent")] }

def tr_53 : Datum :=
  { id := "qingetal2025_tr_53"
    source := ⟨"qing-uegaki-2025", "(53)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nucl1301"
    primaryText := "John maç-ı hangi oyuncu-nun kazan-acağ-ın-dan kork-m-uyor."
    glossedTokens := [("John", "John"), ("maç-ı", "match-ACC"), ("hangi", "which"), ("oyuncu-nun", "player-GEN"), ("kazan-acağ-ın-dan", "win-NMZ.FUT-3S.POSS-ABL"), ("kork-m-uyor", "fear-NEG-IPFV.PRES")]
    glossedWords := [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], none⟩]⟩, ⟨['m', 'a', 'ç', '-', 'ı'], ['m', 'a', 't', 'c', 'h', '-', 'A', 'C', 'C'], [⟨['m', 'a', 'ç'], ['m', 'a', 't', 'c', 'h'], none⟩, ⟨['ı'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['h', 'a', 'n', 'g', 'i'], ['w', 'h', 'i', 'c', 'h'], [⟨['h', 'a', 'n', 'g', 'i'], ['w', 'h', 'i', 'c', 'h'], none⟩]⟩, ⟨['o', 'y', 'u', 'n', 'c', 'u', '-', 'n', 'u', 'n'], ['p', 'l', 'a', 'y', 'e', 'r', '-', 'G', 'E', 'N'], [⟨['o', 'y', 'u', 'n', 'c', 'u'], ['p', 'l', 'a', 'y', 'e', 'r'], none⟩, ⟨['n', 'u', 'n'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['k', 'a', 'z', 'a', 'n', '-', 'a', 'c', 'a', 'ğ', '-', 'ı', 'n', '-', 'd', 'a', 'n'], ['w', 'i', 'n', '-', 'N', 'M', 'Z', '.', 'F', 'U', 'T', '-', '3', 'S', '.', 'P', 'O', 'S', 'S', '-', 'A', 'B', 'L'], [⟨['k', 'a', 'z', 'a', 'n'], ['w', 'i', 'n'], none⟩, ⟨['a', 'c', 'a', 'ğ'], ['N', 'M', 'Z', '.', 'F', 'U', 'T'], some '-'⟩, ⟨['ı', 'n'], ['3', 'S', '.', 'P', 'O', 'S', 'S'], some '-'⟩, ⟨['d', 'a', 'n'], ['A', 'B', 'L'], some '-'⟩]⟩, ⟨['k', 'o', 'r', 'k', '-', 'm', '-', 'u', 'y', 'o', 'r'], ['f', 'e', 'a', 'r', '-', 'N', 'E', 'G', '-', 'I', 'P', 'F', 'V', '.', 'P', 'R', 'E', 'S'], [⟨['k', 'o', 'r', 'k'], ['f', 'e', 'a', 'r'], none⟩, ⟨['m'], ['N', 'E', 'G'], some '-'⟩, ⟨['u', 'y', 'o', 'r'], ['I', 'P', 'F', 'V', '.', 'P', 'R', 'E', 'S'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "There exists no player x such that John fears that x will win the match."
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨5, 1, "predicate", some "kork"⟩]
    paperFeatures := [("clause", "constituent"), ("polarity", "negated")] }

def all : List Datum := [en_6, en_26, en_28, en_29, en_30a, en_30b, en_30c, en_30d, en_36a, en_36b, en_42a, en_42b, en_44a, en_44b, en_46a, en_46b, en_46c, en_46d, en_47a, en_47b, en_48, zh_22, zh_23, zh_31a, zh_31b, zh_37, zh_59, zh_60, zh_fn10_i, ja_24a, ja_25a, ja_32a, ja_32b, ja_38, ja_54_goodfriend, ja_54_noisehater, ja_55, ja_56, es_33a, es_33b, es_39, es_57, es_58, tr_34a, tr_34b, tr_40, tr_49_goodfriend, tr_49_noisehater, tr_52, tr_53]

/-- The type of the complement clause. -/
inductive Clause where
  /-- declarative: a declarative clause -/
  | declarative
  /-- polar: a polar interrogative -/
  | polar
  /-- constituent: a constituent interrogative -/
  | constituent
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `clause`. -/
def clause (e : Datum) : Option Clause :=
  e.parse? "clause" [("declarative", .declarative), ("polar", .polar), ("constituent", .constituent)]

/-- The polarity of the matrix clause, where it is negated. -/
inductive MatrixPolarity where
  /-- negated: the matrix predicate is negated -/
  | negated
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `polarity`. -/
def polarity (e : Datum) : Option MatrixPolarity :=
  e.parse? "polarity" [("negated", .negated)]

/-- The valence the paper gives the veridical preferential under test. -/
inductive Valence where
  /-- positive: evaluatively positive, as *like* and *be happy* -/
  | positive
  /-- negative: evaluatively negative, as *hate* and *be upset* -/
  | negative
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `valence`. -/
def valence (e : Datum) : Option Valence :=
  e.parse? "valence" [("positive", .positive), ("negative", .negative)]

/-- The answer to the embedded polar question that the holder fears. -/
inductive Answer where
  /-- radical: the holder fears that the radical of the question holds -/
  | radical
  /-- negation: the holder fears that the radical does not hold -/
  | negation
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `answer`. -/
def answer (e : Datum) : Option Answer :=
  e.parse? "answer" [("radical", .radical), ("negation", .negation)]

/-- The parses of a clause with a wh-phrase. -/
inductive Reading where
  /-- question: the clause is a constituent question -/
  | question
  /-- indefinite: the wh-phrase is an indefinite and the clause a declarative -/
  | indefinite
  deriving DecidableEq, Repr, Fintype

/-- The name the rows give the reading. -/
def Reading.label : Reading → String
  | .question => "question"
  | .indefinite => "indefinite"

/-- The judgment a row records for the reading, if it records one. -/
def reading (e : Datum) (r : Reading) : Option Judgment :=
  e.readings.lookup r.label

/-- The labels of the spans the rows mark. -/
inductive SpanLabel where
  /-- predicate: the preferential predicate under test -/
  | predicate
  deriving DecidableEq, Repr, Fintype

/-- The label of a span, where it is a declared one. -/
def label? (p : Datum.Span) : Option SpanLabel :=
  List.lookup p.label [("predicate", .predicate)]

/-- The nonveridical preferential predicates under test. -/
inductive Lexeme where
  /-- hope: English *hope* -/
  | hope
  /-- fear: English *fear* -/
  | fear
  /-- worry: English *worry*, with an experiencer subject -/
  | worry
  /-- qidai: Mandarin *qidai* 'look forward to' -/
  | qidai
  /-- danxin: Mandarin *danxin* 'worry' -/
  | danxin
  /-- haipa: Mandarin *haipa* 'fear' -/
  | haipa
  /-- tanosimi: Japanese *tanosimi* 'look forward to' -/
  | tanosimi
  /-- sinpai: Japanese *sinpai-suru* 'worry' -/
  | sinpai
  /-- osore: Japanese *osore(ru)* 'fear' -/
  | osore
  /-- preocupar: Spanish *preocupar* 'worry' -/
  | preocupar
  /-- temer: Spanish *temer* 'fear' -/
  | temer
  /-- endiselen: Turkish *endişelen-* 'worry' -/
  | endiselen
  /-- kork: Turkish *kork-* 'fear' -/
  | kork
  deriving DecidableEq, Repr, Fintype

/-- The lexeme a span is a form of, where it names a declared one. -/
def lexeme? (p : Datum.Span) : Option Lexeme :=
  p.lexeme.bind (List.lookup · [("hope", .hope), ("fear", .fear), ("worry", .worry), ("qidai", .qidai), ("danxin", .danxin), ("haipa", .haipa), ("tanosimi", .tanosimi), ("sinpai", .sinpai), ("osore", .osore), ("preocupar", .preocupar), ("temer", .temer), ("endiselen", .endiselen), ("kork", .kork)])

/-- The examples of the article with a preferential predicate under test. -/
inductive Example where
  | en_6
  | en_26
  | en_28
  | en_29
  | en_30a
  | en_30b
  | en_30c
  | en_30d
  | en_36a
  | en_36b
  | en_42a
  | en_42b
  | en_44a
  | en_44b
  | en_46a
  | en_46b
  | en_46c
  | en_46d
  | en_47a
  | en_47b
  | en_48
  | zh_22
  | zh_23
  | zh_31a
  | zh_31b
  | zh_37
  | zh_59
  | zh_60
  | zh_fn10_i
  | ja_24a
  | ja_25a
  | ja_32a
  | ja_32b
  | ja_38
  | ja_54_goodfriend
  | ja_54_noisehater
  | ja_55
  | ja_56
  | es_33a
  | es_33b
  | es_39
  | es_57
  | es_58
  | tr_34a
  | tr_34b
  | tr_40
  | tr_49_goodfriend
  | tr_49_noisehater
  | tr_52
  | tr_53
  deriving DecidableEq, Repr, Fintype

/-- Every example of the file, in its order. -/
def Example.all : List Example :=
  [.en_6, .en_26, .en_28, .en_29, .en_30a, .en_30b, .en_30c, .en_30d, .en_36a, .en_36b, .en_42a,
    .en_42b, .en_44a, .en_44b, .en_46a, .en_46b, .en_46c, .en_46d, .en_47a, .en_47b, .en_48,
    .zh_22, .zh_23, .zh_31a, .zh_31b, .zh_37, .zh_59, .zh_60, .zh_fn10_i, .ja_24a, .ja_25a,
    .ja_32a, .ja_32b, .ja_38, .ja_54_goodfriend, .ja_54_noisehater, .ja_55, .ja_56, .es_33a,
    .es_33b, .es_39, .es_57, .es_58, .tr_34a, .tr_34b, .tr_40, .tr_49_goodfriend,
    .tr_49_noisehater, .tr_52, .tr_53]

/-- The row of an example. -/
def Example.datum : Example → Datum
  | .en_6 => _root_.QingEtAl2025.Examples.en_6
  | .en_26 => _root_.QingEtAl2025.Examples.en_26
  | .en_28 => _root_.QingEtAl2025.Examples.en_28
  | .en_29 => _root_.QingEtAl2025.Examples.en_29
  | .en_30a => _root_.QingEtAl2025.Examples.en_30a
  | .en_30b => _root_.QingEtAl2025.Examples.en_30b
  | .en_30c => _root_.QingEtAl2025.Examples.en_30c
  | .en_30d => _root_.QingEtAl2025.Examples.en_30d
  | .en_36a => _root_.QingEtAl2025.Examples.en_36a
  | .en_36b => _root_.QingEtAl2025.Examples.en_36b
  | .en_42a => _root_.QingEtAl2025.Examples.en_42a
  | .en_42b => _root_.QingEtAl2025.Examples.en_42b
  | .en_44a => _root_.QingEtAl2025.Examples.en_44a
  | .en_44b => _root_.QingEtAl2025.Examples.en_44b
  | .en_46a => _root_.QingEtAl2025.Examples.en_46a
  | .en_46b => _root_.QingEtAl2025.Examples.en_46b
  | .en_46c => _root_.QingEtAl2025.Examples.en_46c
  | .en_46d => _root_.QingEtAl2025.Examples.en_46d
  | .en_47a => _root_.QingEtAl2025.Examples.en_47a
  | .en_47b => _root_.QingEtAl2025.Examples.en_47b
  | .en_48 => _root_.QingEtAl2025.Examples.en_48
  | .zh_22 => _root_.QingEtAl2025.Examples.zh_22
  | .zh_23 => _root_.QingEtAl2025.Examples.zh_23
  | .zh_31a => _root_.QingEtAl2025.Examples.zh_31a
  | .zh_31b => _root_.QingEtAl2025.Examples.zh_31b
  | .zh_37 => _root_.QingEtAl2025.Examples.zh_37
  | .zh_59 => _root_.QingEtAl2025.Examples.zh_59
  | .zh_60 => _root_.QingEtAl2025.Examples.zh_60
  | .zh_fn10_i => _root_.QingEtAl2025.Examples.zh_fn10_i
  | .ja_24a => _root_.QingEtAl2025.Examples.ja_24a
  | .ja_25a => _root_.QingEtAl2025.Examples.ja_25a
  | .ja_32a => _root_.QingEtAl2025.Examples.ja_32a
  | .ja_32b => _root_.QingEtAl2025.Examples.ja_32b
  | .ja_38 => _root_.QingEtAl2025.Examples.ja_38
  | .ja_54_goodfriend => _root_.QingEtAl2025.Examples.ja_54_goodfriend
  | .ja_54_noisehater => _root_.QingEtAl2025.Examples.ja_54_noisehater
  | .ja_55 => _root_.QingEtAl2025.Examples.ja_55
  | .ja_56 => _root_.QingEtAl2025.Examples.ja_56
  | .es_33a => _root_.QingEtAl2025.Examples.es_33a
  | .es_33b => _root_.QingEtAl2025.Examples.es_33b
  | .es_39 => _root_.QingEtAl2025.Examples.es_39
  | .es_57 => _root_.QingEtAl2025.Examples.es_57
  | .es_58 => _root_.QingEtAl2025.Examples.es_58
  | .tr_34a => _root_.QingEtAl2025.Examples.tr_34a
  | .tr_34b => _root_.QingEtAl2025.Examples.tr_34b
  | .tr_40 => _root_.QingEtAl2025.Examples.tr_40
  | .tr_49_goodfriend => _root_.QingEtAl2025.Examples.tr_49_goodfriend
  | .tr_49_noisehater => _root_.QingEtAl2025.Examples.tr_49_noisehater
  | .tr_52 => _root_.QingEtAl2025.Examples.tr_52
  | .tr_53 => _root_.QingEtAl2025.Examples.tr_53

theorem Example.map_datum_all :
    Example.all.map Example.datum = _root_.QingEtAl2025.Examples.all := rfl

/-- The value the example records under `clause`. -/
def Example.clause : Example → Option Clause
  | .en_6 => some .constituent
  | .en_26 => some .declarative
  | .en_28 => some .constituent
  | .en_29 => some .declarative
  | .en_30a => some .constituent
  | .en_30b => some .constituent
  | .en_30c => some .constituent
  | .en_30d => some .constituent
  | .en_36a => some .constituent
  | .en_36b => some .declarative
  | .en_42a => some .constituent
  | .en_42b => some .constituent
  | .en_44a => some .constituent
  | .en_44b => some .constituent
  | .en_46a => some .polar
  | .en_46b => some .polar
  | .en_46c => some .polar
  | .en_46d => some .polar
  | .en_47a => some .constituent
  | .en_47b => some .constituent
  | .en_48 => some .constituent
  | .zh_22 => some .constituent
  | .zh_23 => some .declarative
  | .zh_31a => some .constituent
  | .zh_31b => some .declarative
  | .zh_37 => some .constituent
  | .zh_59 => some .polar
  | .zh_60 => some .constituent
  | .zh_fn10_i => some .constituent
  | .ja_24a => some .constituent
  | .ja_25a => some .constituent
  | .ja_32a => some .constituent
  | .ja_32b => some .declarative
  | .ja_38 => some .constituent
  | .ja_54_goodfriend => some .polar
  | .ja_54_noisehater => some .polar
  | .ja_55 => some .constituent
  | .ja_56 => some .constituent
  | .es_33a => some .constituent
  | .es_33b => some .declarative
  | .es_39 => some .constituent
  | .es_57 => some .constituent
  | .es_58 => some .polar
  | .tr_34a => some .constituent
  | .tr_34b => some .declarative
  | .tr_40 => some .constituent
  | .tr_49_goodfriend => some .polar
  | .tr_49_noisehater => some .polar
  | .tr_52 => some .constituent
  | .tr_53 => some .constituent

theorem Example.clause_datum :
    ∀ x : Example, _root_.QingEtAl2025.Examples.clause x.datum = x.clause := by
  decide +kernel

/-- The value the example records under `polarity`. -/
def Example.polarity : Example → Option MatrixPolarity
  | .en_6 => none
  | .en_26 => none
  | .en_28 => none
  | .en_29 => none
  | .en_30a => none
  | .en_30b => none
  | .en_30c => none
  | .en_30d => none
  | .en_36a => none
  | .en_36b => none
  | .en_42a => some .negated
  | .en_42b => some .negated
  | .en_44a => some .negated
  | .en_44b => some .negated
  | .en_46a => none
  | .en_46b => none
  | .en_46c => none
  | .en_46d => none
  | .en_47a => none
  | .en_47b => none
  | .en_48 => some .negated
  | .zh_22 => none
  | .zh_23 => none
  | .zh_31a => none
  | .zh_31b => none
  | .zh_37 => none
  | .zh_59 => none
  | .zh_60 => none
  | .zh_fn10_i => none
  | .ja_24a => none
  | .ja_25a => none
  | .ja_32a => none
  | .ja_32b => none
  | .ja_38 => none
  | .ja_54_goodfriend => none
  | .ja_54_noisehater => none
  | .ja_55 => none
  | .ja_56 => some .negated
  | .es_33a => none
  | .es_33b => none
  | .es_39 => none
  | .es_57 => none
  | .es_58 => none
  | .tr_34a => none
  | .tr_34b => none
  | .tr_40 => none
  | .tr_49_goodfriend => none
  | .tr_49_noisehater => none
  | .tr_52 => none
  | .tr_53 => some .negated

theorem Example.polarity_datum :
    ∀ x : Example, _root_.QingEtAl2025.Examples.polarity x.datum = x.polarity := by
  decide +kernel

/-- The value the example records under `valence`. -/
def Example.valence : Example → Option Valence
  | .en_6 => none
  | .en_26 => none
  | .en_28 => none
  | .en_29 => none
  | .en_30a => none
  | .en_30b => none
  | .en_30c => none
  | .en_30d => none
  | .en_36a => none
  | .en_36b => none
  | .en_42a => some .positive
  | .en_42b => some .positive
  | .en_44a => some .negative
  | .en_44b => some .negative
  | .en_46a => none
  | .en_46b => none
  | .en_46c => none
  | .en_46d => none
  | .en_47a => none
  | .en_47b => none
  | .en_48 => none
  | .zh_22 => none
  | .zh_23 => none
  | .zh_31a => none
  | .zh_31b => none
  | .zh_37 => none
  | .zh_59 => none
  | .zh_60 => none
  | .zh_fn10_i => none
  | .ja_24a => none
  | .ja_25a => none
  | .ja_32a => none
  | .ja_32b => none
  | .ja_38 => none
  | .ja_54_goodfriend => none
  | .ja_54_noisehater => none
  | .ja_55 => none
  | .ja_56 => none
  | .es_33a => none
  | .es_33b => none
  | .es_39 => none
  | .es_57 => none
  | .es_58 => none
  | .tr_34a => none
  | .tr_34b => none
  | .tr_40 => none
  | .tr_49_goodfriend => none
  | .tr_49_noisehater => none
  | .tr_52 => none
  | .tr_53 => none

theorem Example.valence_datum :
    ∀ x : Example, _root_.QingEtAl2025.Examples.valence x.datum = x.valence := by
  decide +kernel

/-- The value the example records under `answer`. -/
def Example.answer : Example → Option Answer
  | .en_6 => none
  | .en_26 => none
  | .en_28 => none
  | .en_29 => none
  | .en_30a => none
  | .en_30b => none
  | .en_30c => none
  | .en_30d => none
  | .en_36a => none
  | .en_36b => none
  | .en_42a => none
  | .en_42b => none
  | .en_44a => none
  | .en_44b => none
  | .en_46a => some .radical
  | .en_46b => some .negation
  | .en_46c => some .negation
  | .en_46d => some .negation
  | .en_47a => none
  | .en_47b => none
  | .en_48 => none
  | .zh_22 => none
  | .zh_23 => none
  | .zh_31a => none
  | .zh_31b => none
  | .zh_37 => none
  | .zh_59 => none
  | .zh_60 => none
  | .zh_fn10_i => none
  | .ja_24a => none
  | .ja_25a => none
  | .ja_32a => none
  | .ja_32b => none
  | .ja_38 => none
  | .ja_54_goodfriend => some .negation
  | .ja_54_noisehater => some .radical
  | .ja_55 => none
  | .ja_56 => none
  | .es_33a => none
  | .es_33b => none
  | .es_39 => none
  | .es_57 => none
  | .es_58 => none
  | .tr_34a => none
  | .tr_34b => none
  | .tr_40 => none
  | .tr_49_goodfriend => some .negation
  | .tr_49_noisehater => some .radical
  | .tr_52 => none
  | .tr_53 => none

theorem Example.answer_datum :
    ∀ x : Example, _root_.QingEtAl2025.Examples.answer x.datum = x.answer := by
  decide +kernel

/-- The lexemes the spans of the example name, each with the span's label, in order. -/
def Example.labelledLexemes : Example → List (SpanLabel × Lexeme)
  | .en_6 => [(.predicate, .hope)]
  | .en_26 => [(.predicate, .worry)]
  | .en_28 => [(.predicate, .worry)]
  | .en_29 => [(.predicate, .worry)]
  | .en_30a => [(.predicate, .worry)]
  | .en_30b => [(.predicate, .worry)]
  | .en_30c => [(.predicate, .worry)]
  | .en_30d => [(.predicate, .worry)]
  | .en_36a => [(.predicate, .worry)]
  | .en_36b => [(.predicate, .worry)]
  | .en_42a => []
  | .en_42b => []
  | .en_44a => []
  | .en_44b => []
  | .en_46a => [(.predicate, .fear)]
  | .en_46b => [(.predicate, .fear)]
  | .en_46c => [(.predicate, .fear)]
  | .en_46d => [(.predicate, .fear)]
  | .en_47a => [(.predicate, .fear)]
  | .en_47b => [(.predicate, .fear)]
  | .en_48 => [(.predicate, .fear)]
  | .zh_22 => [(.predicate, .qidai)]
  | .zh_23 => [(.predicate, .qidai)]
  | .zh_31a => [(.predicate, .danxin)]
  | .zh_31b => [(.predicate, .danxin)]
  | .zh_37 => [(.predicate, .danxin)]
  | .zh_59 => [(.predicate, .haipa)]
  | .zh_60 => [(.predicate, .haipa)]
  | .zh_fn10_i => [(.predicate, .haipa)]
  | .ja_24a => [(.predicate, .tanosimi)]
  | .ja_25a => [(.predicate, .tanosimi)]
  | .ja_32a => [(.predicate, .sinpai)]
  | .ja_32b => [(.predicate, .sinpai)]
  | .ja_38 => [(.predicate, .sinpai)]
  | .ja_54_goodfriend => [(.predicate, .osore)]
  | .ja_54_noisehater => [(.predicate, .osore)]
  | .ja_55 => [(.predicate, .osore)]
  | .ja_56 => [(.predicate, .osore)]
  | .es_33a => [(.predicate, .preocupar)]
  | .es_33b => [(.predicate, .preocupar)]
  | .es_39 => [(.predicate, .preocupar)]
  | .es_57 => [(.predicate, .temer)]
  | .es_58 => [(.predicate, .temer)]
  | .tr_34a => [(.predicate, .endiselen)]
  | .tr_34b => [(.predicate, .endiselen)]
  | .tr_40 => [(.predicate, .endiselen)]
  | .tr_49_goodfriend => [(.predicate, .kork)]
  | .tr_49_noisehater => [(.predicate, .kork)]
  | .tr_52 => [(.predicate, .kork)]
  | .tr_53 => [(.predicate, .kork)]

/-- The lexemes the spans of the example labelled `l` name, in order. -/
def Example.lexemes (x : Example) (l : SpanLabel) : List Lexeme :=
  (x.labelledLexemes.filter (·.1 = l)).map (·.2)

theorem Example.lexemes_datum : ∀ (x : Example) (l : SpanLabel),
    (x.datum.spans.filter (_root_.QingEtAl2025.Examples.label? · = some l)).filterMap _root_.QingEtAl2025.Examples.lexeme? =
      x.lexemes l := by
  decide +kernel

/-- The readings the example judges, each with its judgment. -/
def Example.readings : Example → List (Reading × Judgment)
  | .en_6 => []
  | .en_26 => []
  | .en_28 => []
  | .en_29 => []
  | .en_30a => []
  | .en_30b => []
  | .en_30c => []
  | .en_30d => []
  | .en_36a => []
  | .en_36b => []
  | .en_42a => []
  | .en_42b => []
  | .en_44a => []
  | .en_44b => []
  | .en_46a => []
  | .en_46b => []
  | .en_46c => []
  | .en_46d => []
  | .en_47a => []
  | .en_47b => []
  | .en_48 => []
  | .zh_22 => []
  | .zh_23 => []
  | .zh_31a => []
  | .zh_31b => []
  | .zh_37 => []
  | .zh_59 => []
  | .zh_60 => [(.question, .unacceptable), (.indefinite, .acceptable)]
  | .zh_fn10_i => []
  | .ja_24a => []
  | .ja_25a => []
  | .ja_32a => []
  | .ja_32b => []
  | .ja_38 => []
  | .ja_54_goodfriend => []
  | .ja_54_noisehater => []
  | .ja_55 => []
  | .ja_56 => []
  | .es_33a => []
  | .es_33b => []
  | .es_39 => []
  | .es_57 => []
  | .es_58 => []
  | .tr_34a => []
  | .tr_34b => []
  | .tr_40 => []
  | .tr_49_goodfriend => []
  | .tr_49_noisehater => []
  | .tr_52 => []
  | .tr_53 => []

/-- The judgment the example records for the reading, if it records one. -/
def Example.reading (x : Example) (r : Reading) : Option Judgment :=
  (x.readings.lookup r)

theorem Example.reading_datum : ∀ (x : Example) (r : Reading),
    _root_.QingEtAl2025.Examples.reading x.datum r = x.reading r := by
  decide +kernel

end QingEtAl2025.Examples
