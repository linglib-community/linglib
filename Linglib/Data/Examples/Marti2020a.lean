module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Marti2020a` — typed example data

Auto-generated from `Linglib/Data/Examples/Marti2020a.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Marti2020a.Examples`.
-/

@[expose] public section

namespace Marti2020a.Examples

def ex_19 : Datum :=
  { id := "marti2020a_19"
    source := ⟨"sauerland-2003", "(38a)"⟩
    reportedIn := some ⟨"marti-2020a", "(1), (19), (55), (67)"⟩
    language := "stan1293"
    primaryText := "Lina harvested tomatoes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("exclusive", .acceptable), ("inclusive", .unacceptable)]
    paperFeatures := [("environment", "upward"), ("form", "plural"), ("at_least", "2")] }

def ex_20 : Datum :=
  { id := "marti2020a_20"
    source := ⟨"sauerland-2003", "(41b)"⟩
    reportedIn := some ⟨"marti-2020a", "(2), (20), (56), (70)"⟩
    language := "stan1293"
    primaryText := "Lina didn't harvest tomatoes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("inclusive", .acceptable), ("exclusive", .unacceptable)]
    paperFeatures := [("environment", "negation"), ("form", "plural")] }

def ex_21a : Datum :=
  { id := "marti2020a_21a"
    source := ⟨"marti-2020a", "(21a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't have children."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("inclusive", .acceptable)]
    paperFeatures := [("environment", "negation"), ("form", "plural")] }

def ex_21b : Datum :=
  { id := "marti2020a_21b"
    source := ⟨"marti-2020a", "(21b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dogs are not barking at me."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("inclusive", .acceptable)]
    paperFeatures := [("environment", "negation"), ("form", "plural")] }

def ex_22 : Datum :=
  { id := "marti2020a_22"
    source := ⟨"marti-2020a", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Few/No students came to the party."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("inclusive", .acceptable)]
    paperFeatures := [("environment", "restrictor"), ("form", "plural")] }

def ex_23 : Datum :=
  { id := "marti2020a_23"
    source := ⟨"marti-2020a", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you spot horses in this picture, you will get a prize."
    glossedTokens := []
    context := "Directed at one person."
    judgment := .acceptable
    contrasts := []
    readings := [("inclusive", .acceptable)]
    paperFeatures := [("environment", "conditional"), ("form", "plural")] }

def ex_24 : Datum :=
  { id := "marti2020a_24"
    source := ⟨"marti-2020a", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every house with windows overlooking the ocean is overpriced."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("inclusive", .acceptable)]
    paperFeatures := [("environment", "restrictor"), ("form", "plural")] }

def ex_25a : Datum :=
  { id := "marti2020a_25a"
    source := ⟨"marti-2020a", "(25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Have you ever seen horses in this meadow?"
    glossedTokens := []
    context := "Directed at one person."
    judgment := .acceptable
    contrasts := []
    readings := [("inclusive", .acceptable)]
    paperFeatures := [("environment", "question"), ("form", "plural")] }

def ex_25b : Datum :=
  { id := "marti2020a_25b"
    source := ⟨"marti-2020a", "(25b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Did you eat apples today?"
    glossedTokens := []
    context := "Directed at one person."
    judgment := .acceptable
    contrasts := []
    readings := [("inclusive", .acceptable)]
    paperFeatures := [("environment", "question"), ("form", "plural")] }

def ex_26a : Datum :=
  { id := "marti2020a_26a"
    source := ⟨"marti-2020a", "(26a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have children."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("exclusive", .acceptable)]
    paperFeatures := [("environment", "upward"), ("form", "plural")] }

def ex_26b : Datum :=
  { id := "marti2020a_26b"
    source := ⟨"marti-2020a", "(26b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dogs are barking at me."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("exclusive", .acceptable)]
    paperFeatures := [("environment", "upward"), ("form", "plural")] }

def ex_32 : Datum :=
  { id := "marti2020a_32"
    source := ⟨"marti-2020a", "(32)"⟩
    reportedIn := none
    method := some .elicitation
    language := "slov1268"
    primaryText := "Kdor prvi zagleda konje na tem travniku, dobi nagrado."
    glossedTokens := [("Kdor", "who"), ("prvi", "first"), ("zagleda", "see"), ("konje", "horse.ACC.MASC.PL"), ("na", "on"), ("tem", "this"), ("travniku,", "meadow"), ("dobi", "win"), ("nagrado.", "prize")]
    glossedWords := [⟨['K', 'd', 'o', 'r'], ['w', 'h', 'o'], [⟨['K', 'd', 'o', 'r'], ['w', 'h', 'o'], none⟩]⟩, ⟨['p', 'r', 'v', 'i'], ['f', 'i', 'r', 's', 't'], [⟨['p', 'r', 'v', 'i'], ['f', 'i', 'r', 's', 't'], none⟩]⟩, ⟨['z', 'a', 'g', 'l', 'e', 'd', 'a'], ['s', 'e', 'e'], [⟨['z', 'a', 'g', 'l', 'e', 'd', 'a'], ['s', 'e', 'e'], none⟩]⟩, ⟨['k', 'o', 'n', 'j', 'e'], ['h', 'o', 'r', 's', 'e', '.', 'A', 'C', 'C', '.', 'M', 'A', 'S', 'C', '.', 'P', 'L'], [⟨['k', 'o', 'n', 'j', 'e'], ['h', 'o', 'r', 's', 'e', '.', 'A', 'C', 'C', '.', 'M', 'A', 'S', 'C', '.', 'P', 'L'], none⟩]⟩, ⟨['n', 'a'], ['o', 'n'], [⟨['n', 'a'], ['o', 'n'], none⟩]⟩, ⟨['t', 'e', 'm'], ['t', 'h', 'i', 's'], [⟨['t', 'e', 'm'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['t', 'r', 'a', 'v', 'n', 'i', 'k', 'u', ','], ['m', 'e', 'a', 'd', 'o', 'w'], [⟨['t', 'r', 'a', 'v', 'n', 'i', 'k', 'u'], ['m', 'e', 'a', 'd', 'o', 'w'], none⟩]⟩, ⟨['d', 'o', 'b', 'i'], ['w', 'i', 'n'], [⟨['d', 'o', 'b', 'i'], ['w', 'i', 'n'], none⟩]⟩, ⟨['n', 'a', 'g', 'r', 'a', 'd', 'o', '.'], ['p', 'r', 'i', 'z', 'e'], [⟨['n', 'a', 'g', 'r', 'a', 'd', 'o'], ['p', 'r', 'i', 'z', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("inclusive", .acceptable)]
    paperFeatures := [("environment", "restrictor"), ("form", "plural")] }

def ex_33 : Datum :=
  { id := "marti2020a_33"
    source := ⟨"marti-2020a", "(33)"⟩
    reportedIn := none
    method := some .elicitation
    language := "slov1268"
    primaryText := "Ali ima Peter otroke? Ja. Ima enega."
    glossedTokens := [("Ali", "Q"), ("ima", "have"), ("Peter", "Peter"), ("otroke?", "child.ACC.MASC.PL"), ("Ja.", "yes"), ("Ima", "has"), ("enega.", "one")]
    glossedWords := [⟨['A', 'l', 'i'], ['Q'], [⟨['A', 'l', 'i'], ['Q'], none⟩]⟩, ⟨['i', 'm', 'a'], ['h', 'a', 'v', 'e'], [⟨['i', 'm', 'a'], ['h', 'a', 'v', 'e'], none⟩]⟩, ⟨['P', 'e', 't', 'e', 'r'], ['P', 'e', 't', 'e', 'r'], [⟨['P', 'e', 't', 'e', 'r'], ['P', 'e', 't', 'e', 'r'], none⟩]⟩, ⟨['o', 't', 'r', 'o', 'k', 'e', '?'], ['c', 'h', 'i', 'l', 'd', '.', 'A', 'C', 'C', '.', 'M', 'A', 'S', 'C', '.', 'P', 'L'], [⟨['o', 't', 'r', 'o', 'k', 'e'], ['c', 'h', 'i', 'l', 'd', '.', 'A', 'C', 'C', '.', 'M', 'A', 'S', 'C', '.', 'P', 'L'], none⟩]⟩, ⟨['J', 'a', '.'], ['y', 'e', 's'], [⟨['J', 'a'], ['y', 'e', 's'], none⟩]⟩, ⟨['I', 'm', 'a'], ['h', 'a', 's'], [⟨['I', 'm', 'a'], ['h', 'a', 's'], none⟩]⟩, ⟨['e', 'n', 'e', 'g', 'a', '.'], ['o', 'n', 'e'], [⟨['e', 'n', 'e', 'g', 'a'], ['o', 'n', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("inclusive", .acceptable)]
    paperFeatures := [("environment", "question"), ("form", "plural")] }

def ex_34 : Datum :=
  { id := "marti2020a_34"
    source := ⟨"marti-2020a", "(34)"⟩
    reportedIn := none
    method := some .elicitation
    language := "slov1268"
    primaryText := "Do danes fantom (še) nisem pomagal."
    glossedTokens := [("Do", "until"), ("danes", "today"), ("fantom", "boy.DAT.MASC.DU/PL"), ("(še)", "yet"), ("nisem", "NEG.AUX.1SG"), ("pomagal.", "help.PTC.SG")]
    glossedWords := [⟨['D', 'o'], ['u', 'n', 't', 'i', 'l'], [⟨['D', 'o'], ['u', 'n', 't', 'i', 'l'], none⟩]⟩, ⟨['d', 'a', 'n', 'e', 's'], ['t', 'o', 'd', 'a', 'y'], [⟨['d', 'a', 'n', 'e', 's'], ['t', 'o', 'd', 'a', 'y'], none⟩]⟩, ⟨['f', 'a', 'n', 't', 'o', 'm'], ['b', 'o', 'y', '.', 'D', 'A', 'T', '.', 'M', 'A', 'S', 'C', '.', 'D', 'U', '/', 'P', 'L'], [⟨['f', 'a', 'n', 't', 'o', 'm'], ['b', 'o', 'y', '.', 'D', 'A', 'T', '.', 'M', 'A', 'S', 'C', '.', 'D', 'U', '/', 'P', 'L'], none⟩]⟩, ⟨['(', 'š', 'e', ')'], ['y', 'e', 't'], [⟨['š', 'e'], ['y', 'e', 't'], none⟩]⟩, ⟨['n', 'i', 's', 'e', 'm'], ['N', 'E', 'G', '.', 'A', 'U', 'X', '.', '1', 'S', 'G'], [⟨['n', 'i', 's', 'e', 'm'], ['N', 'E', 'G', '.', 'A', 'U', 'X', '.', '1', 'S', 'G'], none⟩]⟩, ⟨['p', 'o', 'm', 'a', 'g', 'a', 'l', '.'], ['h', 'e', 'l', 'p', '.', 'P', 'T', 'C', '.', 'S', 'G'], [⟨['p', 'o', 'm', 'a', 'g', 'a', 'l'], ['h', 'e', 'l', 'p', '.', 'P', 'T', 'C', '.', 'S', 'G'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("inclusive", .acceptable), ("negated dual", .unacceptable)]
    paperFeatures := [("environment", "negation"), ("form", "dual or plural")] }

def ex_35 : Datum :=
  { id := "marti2020a_35"
    source := ⟨"marti-2020a", "(35)"⟩
    reportedIn := none
    method := some .elicitation
    language := "slov1268"
    primaryText := "Do danes fantoma nisem pomagal."
    glossedTokens := [("Do", "until"), ("danes", "today"), ("fantoma", "boy.DAT.MASC.DU"), ("nisem", "NEG.AUX.1SG"), ("pomagal.", "help.PTC.SG")]
    glossedWords := [⟨['D', 'o'], ['u', 'n', 't', 'i', 'l'], [⟨['D', 'o'], ['u', 'n', 't', 'i', 'l'], none⟩]⟩, ⟨['d', 'a', 'n', 'e', 's'], ['t', 'o', 'd', 'a', 'y'], [⟨['d', 'a', 'n', 'e', 's'], ['t', 'o', 'd', 'a', 'y'], none⟩]⟩, ⟨['f', 'a', 'n', 't', 'o', 'm', 'a'], ['b', 'o', 'y', '.', 'D', 'A', 'T', '.', 'M', 'A', 'S', 'C', '.', 'D', 'U'], [⟨['f', 'a', 'n', 't', 'o', 'm', 'a'], ['b', 'o', 'y', '.', 'D', 'A', 'T', '.', 'M', 'A', 'S', 'C', '.', 'D', 'U'], none⟩]⟩, ⟨['n', 'i', 's', 'e', 'm'], ['N', 'E', 'G', '.', 'A', 'U', 'X', '.', '1', 'S', 'G'], [⟨['n', 'i', 's', 'e', 'm'], ['N', 'E', 'G', '.', 'A', 'U', 'X', '.', '1', 'S', 'G'], none⟩]⟩, ⟨['p', 'o', 'm', 'a', 'g', 'a', 'l', '.'], ['h', 'e', 'l', 'p', '.', 'P', 'T', 'C', '.', 'S', 'G'], [⟨['p', 'o', 'm', 'a', 'g', 'a', 'l'], ['h', 'e', 'l', 'p', '.', 'P', 'T', 'C', '.', 'S', 'G'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("negated dual", .acceptable)]
    paperFeatures := [("environment", "negation"), ("form", "dual")] }

def ex_36 : Datum :=
  { id := "marti2020a_36"
    source := ⟨"marti-2020a", "(36)"⟩
    reportedIn := none
    method := some .elicitation
    language := "slov1268"
    primaryText := "Rože ne cvetijo."
    glossedTokens := [("Rože", "flower.NOM.FEM.PL"), ("ne", "NEG"), ("cvetijo.", "blossom.3PL")]
    glossedWords := [⟨['R', 'o', 'ž', 'e'], ['f', 'l', 'o', 'w', 'e', 'r', '.', 'N', 'O', 'M', '.', 'F', 'E', 'M', '.', 'P', 'L'], [⟨['R', 'o', 'ž', 'e'], ['f', 'l', 'o', 'w', 'e', 'r', '.', 'N', 'O', 'M', '.', 'F', 'E', 'M', '.', 'P', 'L'], none⟩]⟩, ⟨['n', 'e'], ['N', 'E', 'G'], [⟨['n', 'e'], ['N', 'E', 'G'], none⟩]⟩, ⟨['c', 'v', 'e', 't', 'i', 'j', 'o', '.'], ['b', 'l', 'o', 's', 's', 'o', 'm', '.', '3', 'P', 'L'], [⟨['c', 'v', 'e', 't', 'i', 'j', 'o'], ['b', 'l', 'o', 's', 's', 'o', 'm', '.', '3', 'P', 'L'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("inclusive", .acceptable)]
    paperFeatures := [("environment", "negation"), ("form", "plural")] }

def ex_37 : Datum :=
  { id := "marti2020a_37"
    source := ⟨"marti-2020a", "(37)"⟩
    reportedIn := none
    method := some .elicitation
    language := "slov1268"
    primaryText := "Nimam otrok."
    glossedTokens := [("Nimam", "NEG.have.1SG"), ("otrok.", "child.GEN.MASC.DU/PL")]
    glossedWords := [⟨['N', 'i', 'm', 'a', 'm'], ['N', 'E', 'G', '.', 'h', 'a', 'v', 'e', '.', '1', 'S', 'G'], [⟨['N', 'i', 'm', 'a', 'm'], ['N', 'E', 'G', '.', 'h', 'a', 'v', 'e', '.', '1', 'S', 'G'], none⟩]⟩, ⟨['o', 't', 'r', 'o', 'k', '.'], ['c', 'h', 'i', 'l', 'd', '.', 'G', 'E', 'N', '.', 'M', 'A', 'S', 'C', '.', 'D', 'U', '/', 'P', 'L'], [⟨['o', 't', 'r', 'o', 'k'], ['c', 'h', 'i', 'l', 'd', '.', 'G', 'E', 'N', '.', 'M', 'A', 'S', 'C', '.', 'D', 'U', '/', 'P', 'L'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("inclusive", .acceptable), ("negated dual", .unacceptable)]
    paperFeatures := [("environment", "negation"), ("form", "dual or plural")] }

def ex_38 : Datum :=
  { id := "marti2020a_38"
    source := ⟨"marti-2020a", "(38)"⟩
    reportedIn := none
    method := some .elicitation
    language := "slov1268"
    primaryText := "Ne vidim konjev na travniku."
    glossedTokens := [("Ne", "NEG"), ("vidim", "see"), ("konjev", "horse.GEN.MASC.DU/PL"), ("na", "on"), ("travniku.", "meadow")]
    glossedWords := [⟨['N', 'e'], ['N', 'E', 'G'], [⟨['N', 'e'], ['N', 'E', 'G'], none⟩]⟩, ⟨['v', 'i', 'd', 'i', 'm'], ['s', 'e', 'e'], [⟨['v', 'i', 'd', 'i', 'm'], ['s', 'e', 'e'], none⟩]⟩, ⟨['k', 'o', 'n', 'j', 'e', 'v'], ['h', 'o', 'r', 's', 'e', '.', 'G', 'E', 'N', '.', 'M', 'A', 'S', 'C', '.', 'D', 'U', '/', 'P', 'L'], [⟨['k', 'o', 'n', 'j', 'e', 'v'], ['h', 'o', 'r', 's', 'e', '.', 'G', 'E', 'N', '.', 'M', 'A', 'S', 'C', '.', 'D', 'U', '/', 'P', 'L'], none⟩]⟩, ⟨['n', 'a'], ['o', 'n'], [⟨['n', 'a'], ['o', 'n'], none⟩]⟩, ⟨['t', 'r', 'a', 'v', 'n', 'i', 'k', 'u', '.'], ['m', 'e', 'a', 'd', 'o', 'w'], [⟨['t', 'r', 'a', 'v', 'n', 'i', 'k', 'u'], ['m', 'e', 'a', 'd', 'o', 'w'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("inclusive", .acceptable), ("negated dual", .unacceptable)]
    paperFeatures := [("environment", "negation"), ("form", "dual or plural")] }

def ex_39 : Datum :=
  { id := "marti2020a_39"
    source := ⟨"marti-2020a", "(39)"⟩
    reportedIn := none
    method := some .elicitation
    language := "slov1268"
    primaryText := "Nimam dveh otrok."
    glossedTokens := [("Nimam", "NEG.have.1SG"), ("dveh", "two.GEN.MASC.DU"), ("otrok.", "child.GEN.MASC.DU")]
    glossedWords := [⟨['N', 'i', 'm', 'a', 'm'], ['N', 'E', 'G', '.', 'h', 'a', 'v', 'e', '.', '1', 'S', 'G'], [⟨['N', 'i', 'm', 'a', 'm'], ['N', 'E', 'G', '.', 'h', 'a', 'v', 'e', '.', '1', 'S', 'G'], none⟩]⟩, ⟨['d', 'v', 'e', 'h'], ['t', 'w', 'o', '.', 'G', 'E', 'N', '.', 'M', 'A', 'S', 'C', '.', 'D', 'U'], [⟨['d', 'v', 'e', 'h'], ['t', 'w', 'o', '.', 'G', 'E', 'N', '.', 'M', 'A', 'S', 'C', '.', 'D', 'U'], none⟩]⟩, ⟨['o', 't', 'r', 'o', 'k', '.'], ['c', 'h', 'i', 'l', 'd', '.', 'G', 'E', 'N', '.', 'M', 'A', 'S', 'C', '.', 'D', 'U'], [⟨['o', 't', 'r', 'o', 'k'], ['c', 'h', 'i', 'l', 'd', '.', 'G', 'E', 'N', '.', 'M', 'A', 'S', 'C', '.', 'D', 'U'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("negated dual", .acceptable)]
    paperFeatures := [("environment", "negation"), ("form", "dual")] }

def ex_40 : Datum :=
  { id := "marti2020a_40"
    source := ⟨"marti-2020a", "(40)"⟩
    reportedIn := none
    method := some .elicitation
    language := "slov1268"
    primaryText := "Ne vidim dveh konjev na travniku."
    glossedTokens := [("Ne", "NEG"), ("vidim", "see"), ("dveh", "two.GEN.MASC.DU"), ("konjev", "horse.GEN.MASC.DU"), ("na", "on"), ("travniku.", "meadow")]
    glossedWords := [⟨['N', 'e'], ['N', 'E', 'G'], [⟨['N', 'e'], ['N', 'E', 'G'], none⟩]⟩, ⟨['v', 'i', 'd', 'i', 'm'], ['s', 'e', 'e'], [⟨['v', 'i', 'd', 'i', 'm'], ['s', 'e', 'e'], none⟩]⟩, ⟨['d', 'v', 'e', 'h'], ['t', 'w', 'o', '.', 'G', 'E', 'N', '.', 'M', 'A', 'S', 'C', '.', 'D', 'U'], [⟨['d', 'v', 'e', 'h'], ['t', 'w', 'o', '.', 'G', 'E', 'N', '.', 'M', 'A', 'S', 'C', '.', 'D', 'U'], none⟩]⟩, ⟨['k', 'o', 'n', 'j', 'e', 'v'], ['h', 'o', 'r', 's', 'e', '.', 'G', 'E', 'N', '.', 'M', 'A', 'S', 'C', '.', 'D', 'U'], [⟨['k', 'o', 'n', 'j', 'e', 'v'], ['h', 'o', 'r', 's', 'e', '.', 'G', 'E', 'N', '.', 'M', 'A', 'S', 'C', '.', 'D', 'U'], none⟩]⟩, ⟨['n', 'a'], ['o', 'n'], [⟨['n', 'a'], ['o', 'n'], none⟩]⟩, ⟨['t', 'r', 'a', 'v', 'n', 'i', 'k', 'u', '.'], ['m', 'e', 'a', 'd', 'o', 'w'], [⟨['t', 'r', 'a', 'v', 'n', 'i', 'k', 'u'], ['m', 'e', 'a', 'd', 'o', 'w'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("negated dual", .acceptable)]
    paperFeatures := [("environment", "negation"), ("form", "dual")] }

def ex_41 : Datum :=
  { id := "marti2020a_41"
    source := ⟨"marti-2020a", "(41)"⟩
    reportedIn := none
    method := some .elicitation
    language := "slov1268"
    primaryText := "Vsaka hiša ki ima okna s pogledom na morje je precenjena."
    glossedTokens := [("Vsaka", "every"), ("hiša", "house.NOM.FEM.SG"), ("ki", "which"), ("ima", "has"), ("okna", "window.ACC.NEUT.DU/PL"), ("s", "with"), ("pogledom", "view"), ("na", "on"), ("morje", "sea"), ("je", "is"), ("precenjena.", "overpriced")]
    glossedWords := [⟨['V', 's', 'a', 'k', 'a'], ['e', 'v', 'e', 'r', 'y'], [⟨['V', 's', 'a', 'k', 'a'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['h', 'i', 'š', 'a'], ['h', 'o', 'u', 's', 'e', '.', 'N', 'O', 'M', '.', 'F', 'E', 'M', '.', 'S', 'G'], [⟨['h', 'i', 'š', 'a'], ['h', 'o', 'u', 's', 'e', '.', 'N', 'O', 'M', '.', 'F', 'E', 'M', '.', 'S', 'G'], none⟩]⟩, ⟨['k', 'i'], ['w', 'h', 'i', 'c', 'h'], [⟨['k', 'i'], ['w', 'h', 'i', 'c', 'h'], none⟩]⟩, ⟨['i', 'm', 'a'], ['h', 'a', 's'], [⟨['i', 'm', 'a'], ['h', 'a', 's'], none⟩]⟩, ⟨['o', 'k', 'n', 'a'], ['w', 'i', 'n', 'd', 'o', 'w', '.', 'A', 'C', 'C', '.', 'N', 'E', 'U', 'T', '.', 'D', 'U', '/', 'P', 'L'], [⟨['o', 'k', 'n', 'a'], ['w', 'i', 'n', 'd', 'o', 'w', '.', 'A', 'C', 'C', '.', 'N', 'E', 'U', 'T', '.', 'D', 'U', '/', 'P', 'L'], none⟩]⟩, ⟨['s'], ['w', 'i', 't', 'h'], [⟨['s'], ['w', 'i', 't', 'h'], none⟩]⟩, ⟨['p', 'o', 'g', 'l', 'e', 'd', 'o', 'm'], ['v', 'i', 'e', 'w'], [⟨['p', 'o', 'g', 'l', 'e', 'd', 'o', 'm'], ['v', 'i', 'e', 'w'], none⟩]⟩, ⟨['n', 'a'], ['o', 'n'], [⟨['n', 'a'], ['o', 'n'], none⟩]⟩, ⟨['m', 'o', 'r', 'j', 'e'], ['s', 'e', 'a'], [⟨['m', 'o', 'r', 'j', 'e'], ['s', 'e', 'a'], none⟩]⟩, ⟨['j', 'e'], ['i', 's'], [⟨['j', 'e'], ['i', 's'], none⟩]⟩, ⟨['p', 'r', 'e', 'c', 'e', 'n', 'j', 'e', 'n', 'a', '.'], ['o', 'v', 'e', 'r', 'p', 'r', 'i', 'c', 'e', 'd'], [⟨['p', 'r', 'e', 'c', 'e', 'n', 'j', 'e', 'n', 'a'], ['o', 'v', 'e', 'r', 'p', 'r', 'i', 'c', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("inclusive", .acceptable)]
    paperFeatures := [("environment", "restrictor"), ("form", "dual or plural")] }

def ex_42 : Datum :=
  { id := "marti2020a_42"
    source := ⟨"marti-2020a", "(42)"⟩
    reportedIn := none
    method := some .elicitation
    language := "slov1268"
    primaryText := "En avtomobil je povozil študente."
    glossedTokens := [("En", "one.NOM.MASC.SG"), ("avtomobil", "car.NOM.MASC.SG"), ("je", "AUX.SG"), ("povozil", "run.over.PTC.MASC.SG"), ("študente.", "student.ACC.MASC.PL")]
    glossedWords := [⟨['E', 'n'], ['o', 'n', 'e', '.', 'N', 'O', 'M', '.', 'M', 'A', 'S', 'C', '.', 'S', 'G'], [⟨['E', 'n'], ['o', 'n', 'e', '.', 'N', 'O', 'M', '.', 'M', 'A', 'S', 'C', '.', 'S', 'G'], none⟩]⟩, ⟨['a', 'v', 't', 'o', 'm', 'o', 'b', 'i', 'l'], ['c', 'a', 'r', '.', 'N', 'O', 'M', '.', 'M', 'A', 'S', 'C', '.', 'S', 'G'], [⟨['a', 'v', 't', 'o', 'm', 'o', 'b', 'i', 'l'], ['c', 'a', 'r', '.', 'N', 'O', 'M', '.', 'M', 'A', 'S', 'C', '.', 'S', 'G'], none⟩]⟩, ⟨['j', 'e'], ['A', 'U', 'X', '.', 'S', 'G'], [⟨['j', 'e'], ['A', 'U', 'X', '.', 'S', 'G'], none⟩]⟩, ⟨['p', 'o', 'v', 'o', 'z', 'i', 'l'], ['r', 'u', 'n', '.', 'o', 'v', 'e', 'r', '.', 'P', 'T', 'C', '.', 'M', 'A', 'S', 'C', '.', 'S', 'G'], [⟨['p', 'o', 'v', 'o', 'z', 'i', 'l'], ['r', 'u', 'n', '.', 'o', 'v', 'e', 'r', '.', 'P', 'T', 'C', '.', 'M', 'A', 'S', 'C', '.', 'S', 'G'], none⟩]⟩, ⟨['š', 't', 'u', 'd', 'e', 'n', 't', 'e', '.'], ['s', 't', 'u', 'd', 'e', 'n', 't', '.', 'A', 'C', 'C', '.', 'M', 'A', 'S', 'C', '.', 'P', 'L'], [⟨['š', 't', 'u', 'd', 'e', 'n', 't', 'e'], ['s', 't', 'u', 'd', 'e', 'n', 't', '.', 'A', 'C', 'C', '.', 'M', 'A', 'S', 'C', '.', 'P', 'L'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("exclusive", .acceptable)]
    paperFeatures := [("environment", "upward"), ("form", "plural"), ("at_least", "3")] }

def ex_43 : Datum :=
  { id := "marti2020a_43"
    source := ⟨"marti-2020a", "(43)"⟩
    reportedIn := none
    method := some .elicitation
    language := "slov1268"
    primaryText := "Ena hiša ki ima okna s pogledom na morje je precenjena."
    glossedTokens := [("Ena", "one.NOM.FEM.SG"), ("hiša", "house.NOM.FEM.SG"), ("ki", "which"), ("ima", "has"), ("okna", "window.ACC.NEUT.DU/PL"), ("s", "with"), ("pogledom", "view"), ("na", "on"), ("morje", "sea"), ("je", "is"), ("precenjena.", "overpriced")]
    glossedWords := [⟨['E', 'n', 'a'], ['o', 'n', 'e', '.', 'N', 'O', 'M', '.', 'F', 'E', 'M', '.', 'S', 'G'], [⟨['E', 'n', 'a'], ['o', 'n', 'e', '.', 'N', 'O', 'M', '.', 'F', 'E', 'M', '.', 'S', 'G'], none⟩]⟩, ⟨['h', 'i', 'š', 'a'], ['h', 'o', 'u', 's', 'e', '.', 'N', 'O', 'M', '.', 'F', 'E', 'M', '.', 'S', 'G'], [⟨['h', 'i', 'š', 'a'], ['h', 'o', 'u', 's', 'e', '.', 'N', 'O', 'M', '.', 'F', 'E', 'M', '.', 'S', 'G'], none⟩]⟩, ⟨['k', 'i'], ['w', 'h', 'i', 'c', 'h'], [⟨['k', 'i'], ['w', 'h', 'i', 'c', 'h'], none⟩]⟩, ⟨['i', 'm', 'a'], ['h', 'a', 's'], [⟨['i', 'm', 'a'], ['h', 'a', 's'], none⟩]⟩, ⟨['o', 'k', 'n', 'a'], ['w', 'i', 'n', 'd', 'o', 'w', '.', 'A', 'C', 'C', '.', 'N', 'E', 'U', 'T', '.', 'D', 'U', '/', 'P', 'L'], [⟨['o', 'k', 'n', 'a'], ['w', 'i', 'n', 'd', 'o', 'w', '.', 'A', 'C', 'C', '.', 'N', 'E', 'U', 'T', '.', 'D', 'U', '/', 'P', 'L'], none⟩]⟩, ⟨['s'], ['w', 'i', 't', 'h'], [⟨['s'], ['w', 'i', 't', 'h'], none⟩]⟩, ⟨['p', 'o', 'g', 'l', 'e', 'd', 'o', 'm'], ['v', 'i', 'e', 'w'], [⟨['p', 'o', 'g', 'l', 'e', 'd', 'o', 'm'], ['v', 'i', 'e', 'w'], none⟩]⟩, ⟨['n', 'a'], ['o', 'n'], [⟨['n', 'a'], ['o', 'n'], none⟩]⟩, ⟨['m', 'o', 'r', 'j', 'e'], ['s', 'e', 'a'], [⟨['m', 'o', 'r', 'j', 'e'], ['s', 'e', 'a'], none⟩]⟩, ⟨['j', 'e'], ['i', 's'], [⟨['j', 'e'], ['i', 's'], none⟩]⟩, ⟨['p', 'r', 'e', 'c', 'e', 'n', 'j', 'e', 'n', 'a', '.'], ['o', 'v', 'e', 'r', 'p', 'r', 'i', 'c', 'e', 'd'], [⟨['p', 'r', 'e', 'c', 'e', 'n', 'j', 'e', 'n', 'a'], ['o', 'v', 'e', 'r', 'p', 'r', 'i', 'c', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("exclusive", .acceptable)]
    paperFeatures := [("environment", "upward"), ("form", "dual or plural"), ("at_least", "3")] }

def all : List Datum := [ex_19, ex_20, ex_21a, ex_21b, ex_22, ex_23, ex_24, ex_25a, ex_25b, ex_26a, ex_26b, ex_32, ex_33, ex_34, ex_35, ex_36, ex_37, ex_38, ex_39, ex_40, ex_41, ex_42, ex_43]

/-- The environment of the noun phrase. -/
inductive Environment where
  /-- upward: an upward-entailing environment -/
  | upward
  /-- negation: under sentential negation -/
  | negation
  /-- restrictor: in the restriction of a universal or negative quantifier -/
  | restrictor
  /-- conditional: in the antecedent of a conditional -/
  | conditional
  /-- question: in a question -/
  | question
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `environment`. -/
def environment (e : Datum) : Option Environment :=
  e.parse? "environment" [("upward", .upward), ("negation", .negation), ("restrictor", .restrictor),
    ("conditional", .conditional), ("question", .question)]

/-- The number the noun's form marks. -/
inductive Form where
  /-- plural: a plural form -/
  | plural
  /-- dual: an unambiguously dual form -/
  | dual
  /-- dual or plural: a form syncretic between dual and plural -/
  | dualOrPlural
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `form`. -/
def form (e : Datum) : Option Form :=
  e.parse? "form" [("plural", .plural), ("dual", .dual), ("dual or plural", .dualOrPlural)]

/-- The interpretations the paper judges a noun phrase for. -/
inductive Reading where
  /-- inclusive: one or more -/
  | inclusive
  /-- exclusive: only as many as the plural of the language requires -/
  | exclusive
  /-- negated dual: two, under the negation of the sentence -/
  | negatedDual
  deriving DecidableEq, Repr, Fintype

/-- The name the rows give the reading. -/
def Reading.label : Reading → String
  | .inclusive => "inclusive"
  | .exclusive => "exclusive"
  | .negatedDual => "negated dual"

/-- The judgment a row records for the reading, if it records one. -/
def reading (e : Datum) (r : Reading) : Option Judgment :=
  e.readings.lookup r.label

end Marti2020a.Examples
