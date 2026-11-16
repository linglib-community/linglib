module

public import Linglib.Data.Examples.Schema

/-!
# `Heine1997` — typed example data

Auto-generated from `Linglib/Data/Examples/Heine1997.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Heine1997.Examples`.
-/

@[expose] public section

namespace Heine1997.Examples

def ex_2_pt : Datum :=
  { id := "heine1997_2_pt"
    source := ⟨"heine-1997", "ch. 2, (2)"⟩
    reportedIn := none
    language := "port1283"
    primaryText := "O menino tem fome."
    glossedTokens := [("O", "the"), ("menino", "child"), ("tem", "takes/has"), ("fome", "hunger")]
    glossedWords := [⟨[['O']], [['t', 'h', 'e']]⟩, ⟨[['m', 'e', 'n', 'i', 'n', 'o']], [['c', 'h', 'i', 'l', 'd']]⟩, ⟨[['t', 'e', 'm']], [['t', 'a', 'k', 'e', 's', '/', 'h', 'a', 's']]⟩, ⟨[['f', 'o', 'm', 'e']], [['h', 'u', 'n', 'g', 'e', 'r']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("schema", "action")] }

def ex_73a : Datum :=
  { id := "heine1997_73a"
    source := ⟨"heine-1997", "ch. 2, (73a)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Lámpa stoít u okná."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("location", .acceptable)]
    paperFeatures := [("schema", "location"), ("source", "true"), ("target", "false")] }

def ex_73b : Datum :=
  { id := "heine1997_73b"
    source := ⟨"heine-1997", "ch. 2, (73b)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Mašina u Péti."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("location", .acceptable)]
    paperFeatures := [("schema", "location"), ("source", "true"), ("target", "false")] }

def ex_73c : Datum :=
  { id := "heine1997_73c"
    source := ⟨"heine-1997", "ch. 2, (73c)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Sejčás u Márkovyx gripp."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("There is flu at the Markovs.", .acceptable), ("The Markovs have the flu now.", .acceptable)]
    paperFeatures := [("schema", "location"), ("source", "true"), ("target", "true")] }

def ex_73d : Datum :=
  { id := "heine1997_73d"
    source := ⟨"heine-1997", "ch. 2, (73d)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "U Péti est' mašina."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possession", .acceptable)]
    paperFeatures := [("schema", "location"), ("source", "false"), ("target", "true")] }

def ex_84a : Datum :=
  { id := "heine1997_84a"
    source := ⟨"heine-1997", "ch. 2, (84a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The car is mine."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("schema", "equation"), ("notion", "permanent")] }

def ex_84b : Datum :=
  { id := "heine1997_84b"
    source := ⟨"heine-1997", "ch. 2, (84b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Two sisters are mine."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("schema", "equation"), ("notion", "inalienable")] }

def ex_84c : Datum :=
  { id := "heine1997_84c"
    source := ⟨"heine-1997", "ch. 2, (84c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The cold is mine."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("schema", "equation"), ("notion", "abstract")] }

def ex_84d : Datum :=
  { id := "heine1997_84d"
    source := ⟨"heine-1997", "ch. 2, (84d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Two bedrooms are my house's."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("schema", "equation"), ("notion", "inanimateInalienable")] }

def ex_85a : Datum :=
  { id := "heine1997_85a"
    source := ⟨"heine-1997", "ch. 2, (85a)"⟩
    reportedIn := none
    language := "telu1262"
    primaryText := "pennu vaːḍi-daggara undi"
    glossedTokens := [("pennu", "pen"), ("vaːḍi-daggara", "him-at"), ("undi", "is")]
    glossedWords := [⟨[['p', 'e', 'n', 'n', 'u']], [['p', 'e', 'n']]⟩, ⟨[['v', 'a', 'ː', 'ḍ', 'i'], ['d', 'a', 'g', 'g', 'a', 'r', 'a']], [['h', 'i', 'm'], ['a', 't']]⟩, ⟨[['u', 'n', 'd', 'i']], [['i', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("schema", "location"), ("notion", "physical")] }

def ex_85b : Datum :=
  { id := "heine1997_85b"
    source := ⟨"heine-1997", "ch. 2, (85b)"⟩
    reportedIn := none
    language := "telu1262"
    primaryText := "pennu vaːḍi-ki undi"
    glossedTokens := [("pennu", "pen"), ("vaːḍi-ki", "him-to"), ("undi", "is")]
    glossedWords := [⟨[['p', 'e', 'n', 'n', 'u']], [['p', 'e', 'n']]⟩, ⟨[['v', 'a', 'ː', 'ḍ', 'i'], ['k', 'i']], [['h', 'i', 'm'], ['t', 'o']]⟩, ⟨[['u', 'n', 'd', 'i']], [['i', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("schema", "goal"), ("notion", "permanent")] }

def ex_85c : Datum :=
  { id := "heine1997_85c"
    source := ⟨"heine-1997", "ch. 2, (85c)"⟩
    reportedIn := none
    language := "telu1262"
    primaryText := "reṇḍu kaḷḷu naː-ku unnaːy"
    glossedTokens := [("reṇḍu", "two"), ("kaḷḷu", "eyes"), ("naː-ku", "me-to"), ("unnaːy", "are")]
    glossedWords := [⟨[['r', 'e', 'ṇ', 'ḍ', 'u']], [['t', 'w', 'o']]⟩, ⟨[['k', 'a', 'ḷ', 'ḷ', 'u']], [['e', 'y', 'e', 's']]⟩, ⟨[['n', 'a', 'ː'], ['k', 'u']], [['m', 'e'], ['t', 'o']]⟩, ⟨[['u', 'n', 'n', 'a', 'ː', 'y']], [['a', 'r', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("schema", "goal"), ("notion", "inalienable")] }

def ex_85d : Datum :=
  { id := "heine1997_85d"
    source := ⟨"heine-1997", "ch. 2, (85d)"⟩
    reportedIn := none
    language := "telu1262"
    primaryText := "iddaru pillalu naː-ku unnaːru"
    glossedTokens := [("iddaru", "two"), ("pillalu", "children"), ("naː-ku", "me-to"), ("unnaːru", "are")]
    glossedWords := [⟨[['i', 'd', 'd', 'a', 'r', 'u']], [['t', 'w', 'o']]⟩, ⟨[['p', 'i', 'l', 'l', 'a', 'l', 'u']], [['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n']]⟩, ⟨[['n', 'a', 'ː'], ['k', 'u']], [['m', 'e'], ['t', 'o']]⟩, ⟨[['u', 'n', 'n', 'a', 'ː', 'r', 'u']], [['a', 'r', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("schema", "goal"), ("notion", "inalienable")] }

def ex_85e : Datum :=
  { id := "heine1997_85e"
    source := ⟨"heine-1997", "ch. 2, (85e)"⟩
    reportedIn := none
    language := "telu1262"
    primaryText := "kommalu ceṭṭu-ki unnaːy"
    glossedTokens := [("kommalu", "branches"), ("ceṭṭu-ki", "tree-to"), ("unnaːy", "are")]
    glossedWords := [⟨[['k', 'o', 'm', 'm', 'a', 'l', 'u']], [['b', 'r', 'a', 'n', 'c', 'h', 'e', 's']]⟩, ⟨[['c', 'e', 'ṭ', 'ṭ', 'u'], ['k', 'i']], [['t', 'r', 'e', 'e'], ['t', 'o']]⟩, ⟨[['u', 'n', 'n', 'a', 'ː', 'y']], [['a', 'r', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("schema", "goal"), ("notion", "inanimateInalienable")] }

def ex_86a : Datum :=
  { id := "heine1997_86a"
    source := ⟨"heine-1997", "ch. 2, (86a)"⟩
    reportedIn := none
    language := "ewee1241"
    primaryText := "dɔ lii ná Kofí"
    glossedTokens := [("dɔ", "work"), ("lii", "exist"), ("ná", "to"), ("Kofí", "Kofi")]
    glossedWords := [⟨[['d', 'ɔ']], [['w', 'o', 'r', 'k']]⟩, ⟨[['l', 'i', 'i']], [['e', 'x', 'i', 's', 't']]⟩, ⟨[['n', 'á']], [['t', 'o']]⟩, ⟨[['K', 'o', 'f', 'í']], [['K', 'o', 'f', 'i']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("schema", "goal"), ("possessee", "indefinite"), ("notion", "permanent")] }

def ex_86b : Datum :=
  { id := "heine1997_86b"
    source := ⟨"heine-1997", "ch. 2, (86b)"⟩
    reportedIn := none
    language := "ewee1241"
    primaryText := "dɔ lá lii ná Kofí"
    glossedTokens := [("dɔ", "work"), ("lá", "the"), ("lii", "exist"), ("ná", "to"), ("Kofí", "Kofi")]
    glossedWords := [⟨[['d', 'ɔ']], [['w', 'o', 'r', 'k']]⟩, ⟨[['l', 'á']], [['t', 'h', 'e']]⟩, ⟨[['l', 'i', 'i']], [['e', 'x', 'i', 's', 't']]⟩, ⟨[['n', 'á']], [['t', 'o']]⟩, ⟨[['K', 'o', 'f', 'í']], [['K', 'o', 'f', 'i']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("schema", "goal"), ("possessee", "definite"), ("notion", "physical")] }

def ex_87a : Datum :=
  { id := "heine1997_87a"
    source := ⟨"heine-1997", "ch. 2, (87a)"⟩
    reportedIn := none
    language := "ewee1241"
    primaryText := "ga le Kofí sí"
    glossedTokens := [("ga", "money"), ("le", "be.at"), ("Kofí", "Kofi"), ("sí", "hand")]
    glossedWords := [⟨[['g', 'a']], [['m', 'o', 'n', 'e', 'y']]⟩, ⟨[['l', 'e']], [['b', 'e', '.', 'a', 't']]⟩, ⟨[['K', 'o', 'f', 'í']], [['K', 'o', 'f', 'i']]⟩, ⟨[['s', 'í']], [['h', 'a', 'n', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("schema", "location"), ("possessee", "indefinite"), ("notion", "permanent")] }

def ex_87b : Datum :=
  { id := "heine1997_87b"
    source := ⟨"heine-1997", "ch. 2, (87b)"⟩
    reportedIn := none
    language := "ewee1241"
    primaryText := "ga lá le Kofí sí"
    glossedTokens := [("ga", "money"), ("lá", "the"), ("le", "be.at"), ("Kofí", "Kofi"), ("sí", "hand")]
    glossedWords := [⟨[['g', 'a']], [['m', 'o', 'n', 'e', 'y']]⟩, ⟨[['l', 'á']], [['t', 'h', 'e']]⟩, ⟨[['l', 'e']], [['b', 'e', '.', 'a', 't']]⟩, ⟨[['K', 'o', 'f', 'í']], [['K', 'o', 'f', 'i']]⟩, ⟨[['s', 'í']], [['h', 'a', 'n', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("schema", "location"), ("possessee", "definite"), ("notion", "physical")] }

def all : List Datum := [ex_2_pt, ex_73a, ex_73b, ex_73c, ex_73d, ex_84a, ex_84b, ex_84c, ex_84d, ex_85a, ex_85b, ex_85c, ex_85d, ex_85e, ex_86a, ex_86b, ex_87a, ex_87b]

end Heine1997.Examples
