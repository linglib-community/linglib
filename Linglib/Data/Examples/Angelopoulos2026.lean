module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Angelopoulos2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Angelopoulos2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Angelopoulos2026.Examples`.
-/

@[expose] public section

namespace Angelopoulos2026.Examples

def ex_1a : Datum :=
  { id := "angelopoulos2026_1a"
    source := ⟨"angelopoulos-2026", "ex. (1a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I Elena ipe oti eçi episkefti tin Vrazilia."
    glossedTokens := [("I", "the.F.SG.NOM"), ("Elena", "Elena.F.SG.NOM"), ("ipe", "said.3SG"), ("oti", "OTI"), ("eçi", "have.3SG"), ("episkefti", "visited"), ("tin", "the.F.SG.ACC"), ("Vrazilia", "Brazil.F.SG.ACC")]
    glossedWords := [⟨[['I']], [['t', 'h', 'e', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['E', 'l', 'e', 'n', 'a']], [['E', 'l', 'e', 'n', 'a', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['i', 'p', 'e']], [['s', 'a', 'i', 'd', '.', '3', 'S', 'G']]⟩, ⟨[['o', 't', 'i']], [['O', 'T', 'I']]⟩, ⟨[['e', 'ç', 'i']], [['h', 'a', 'v', 'e', '.', '3', 'S', 'G']]⟩, ⟨[['e', 'p', 'i', 's', 'k', 'e', 'f', 't', 'i']], [['v', 'i', 's', 'i', 't', 'e', 'd']]⟩, ⟨[['t', 'i', 'n']], [['t', 'h', 'e', '.', 'F', '.', 'S', 'G', '.', 'A', 'C', 'C']]⟩, ⟨[['V', 'r', 'a', 'z', 'i', 'l', 'i', 'a']], [['B', 'r', 'a', 'z', 'i', 'l', '.', 'F', '.', 'S', 'G', '.', 'A', 'C', 'C']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("I Elena ipe pu eçi episkefti tin Vrazilia.", .ungrammatical)]
    readings := []
    paperFeatures := [("complementizer", "oti"), ("verbClass", "saying"), ("verb", "leo"), ("position", "internal_argument")] }

def ex_1b : Datum :=
  { id := "angelopoulos2026_1b"
    source := ⟨"angelopoulos-2026", "ex. (1b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I Elena metanjose pu paretiθike."
    glossedTokens := [("I", "the.F.SG.NOM"), ("Elena", "Elena.F.SG.NOM"), ("metanjose", "regretted.3SG"), ("pu", "PU"), ("paretiθike", "quit.3SG")]
    glossedWords := [⟨[['I']], [['t', 'h', 'e', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['E', 'l', 'e', 'n', 'a']], [['E', 'l', 'e', 'n', 'a', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['m', 'e', 't', 'a', 'n', 'j', 'o', 's', 'e']], [['r', 'e', 'g', 'r', 'e', 't', 't', 'e', 'd', '.', '3', 'S', 'G']]⟩, ⟨[['p', 'u']], [['P', 'U']]⟩, ⟨[['p', 'a', 'r', 'e', 't', 'i', 'θ', 'i', 'k', 'e']], [['q', 'u', 'i', 't', '.', '3', 'S', 'G']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("I Elena metanjose oti paretiθike.", .ungrammatical)]
    readings := []
    paperFeatures := [("complementizer", "pu"), ("verbClass", "emotive-factive"), ("verb", "metaniono"), ("position", "internal_argument")] }

def ex_31a : Datum :=
  { id := "angelopoulos2026_31a"
    source := ⟨"angelopoulos-2026", "ex. (31a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "δjafono me kati."
    glossedTokens := [("δjafono", "disagree.1SG"), ("me", "with"), ("kati", "something.N.SG.ACC")]
    glossedWords := [⟨[['δ', 'j', 'a', 'f', 'o', 'n', 'o']], [['d', 'i', 's', 'a', 'g', 'r', 'e', 'e', '.', '1', 'S', 'G']]⟩, ⟨[['m', 'e']], [['w', 'i', 't', 'h']]⟩, ⟨[['k', 'a', 't', 'i']], [['s', 'o', 'm', 'e', 't', 'h', 'i', 'n', 'g', '.', 'N', '.', 'S', 'G', '.', 'A', 'C', 'C']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "P-ban"), ("verb", "δjafono 'disagree'")] }

def ex_31b : Datum :=
  { id := "angelopoulos2026_31b"
    source := ⟨"angelopoulos-2026", "ex. (31b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "δjafono oti prepi na kanume epenδisis."
    glossedTokens := [("δjafono", "disagree.1SG"), ("oti", "OTI"), ("prepi", "must.3SG"), ("na", "na"), ("kanume", "do.1PL"), ("epenδisis", "investments.F.PL.ACC")]
    glossedWords := [⟨[['δ', 'j', 'a', 'f', 'o', 'n', 'o']], [['d', 'i', 's', 'a', 'g', 'r', 'e', 'e', '.', '1', 'S', 'G']]⟩, ⟨[['o', 't', 'i']], [['O', 'T', 'I']]⟩, ⟨[['p', 'r', 'e', 'p', 'i']], [['m', 'u', 's', 't', '.', '3', 'S', 'G']]⟩, ⟨[['n', 'a']], [['n', 'a']]⟩, ⟨[['k', 'a', 'n', 'u', 'm', 'e']], [['d', 'o', '.', '1', 'P', 'L']]⟩, ⟨[['e', 'p', 'e', 'n', 'δ', 'i', 's', 'i', 's']], [['i', 'n', 'v', 'e', 's', 't', 'm', 'e', 'n', 't', 's', '.', 'F', '.', 'P', 'L', '.', 'A', 'C', 'C']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "P-ban"), ("verb", "δjafono 'disagree'"), ("complementizer", "oti"), ("position", "internal_argument")] }

def ex_31c : Datum :=
  { id := "angelopoulos2026_31c"
    source := ⟨"angelopoulos-2026", "ex. (31c)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "δjafono me oti prepi na kanume epenδisis."
    glossedTokens := [("δjafono", "disagree.1SG"), ("me", "with"), ("oti", "OTI"), ("prepi", "must.3SG"), ("na", "na"), ("kanume", "do.1PL"), ("epenδisis", "investments.F.PL.ACC")]
    glossedWords := [⟨[['δ', 'j', 'a', 'f', 'o', 'n', 'o']], [['d', 'i', 's', 'a', 'g', 'r', 'e', 'e', '.', '1', 'S', 'G']]⟩, ⟨[['m', 'e']], [['w', 'i', 't', 'h']]⟩, ⟨[['o', 't', 'i']], [['O', 'T', 'I']]⟩, ⟨[['p', 'r', 'e', 'p', 'i']], [['m', 'u', 's', 't', '.', '3', 'S', 'G']]⟩, ⟨[['n', 'a']], [['n', 'a']]⟩, ⟨[['k', 'a', 'n', 'u', 'm', 'e']], [['d', 'o', '.', '1', 'P', 'L']]⟩, ⟨[['e', 'p', 'e', 'n', 'δ', 'i', 's', 'i', 's']], [['i', 'n', 'v', 'e', 's', 't', 'm', 'e', 'n', 't', 's', '.', 'F', '.', 'P', 'L', '.', 'A', 'C', 'C']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "P-ban"), ("verb", "δjafono 'disagree'"), ("complementizer", "oti"), ("position", "p_complement")] }

def ex_32a : Datum :=
  { id := "angelopoulos2026_32a"
    source := ⟨"angelopoulos-2026", "ex. (32a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Metanjono ja kati."
    glossedTokens := [("Metanjono", "regret.1SG"), ("ja", "for"), ("kati", "something.N.SG.ACC")]
    glossedWords := [⟨[['M', 'e', 't', 'a', 'n', 'j', 'o', 'n', 'o']], [['r', 'e', 'g', 'r', 'e', 't', '.', '1', 'S', 'G']]⟩, ⟨[['j', 'a']], [['f', 'o', 'r']]⟩, ⟨[['k', 'a', 't', 'i']], [['s', 'o', 'm', 'e', 't', 'h', 'i', 'n', 'g', '.', 'N', '.', 'S', 'G', '.', 'A', 'C', 'C']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "P-ban"), ("verb", "metaniono")] }

def ex_32b : Datum :=
  { id := "angelopoulos2026_32b"
    source := ⟨"angelopoulos-2026", "ex. (32b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Metanjono pu paremina."
    glossedTokens := [("Metanjono", "regret.1SG"), ("pu", "PU"), ("paremina", "stayed.1SG")]
    glossedWords := [⟨[['M', 'e', 't', 'a', 'n', 'j', 'o', 'n', 'o']], [['r', 'e', 'g', 'r', 'e', 't', '.', '1', 'S', 'G']]⟩, ⟨[['p', 'u']], [['P', 'U']]⟩, ⟨[['p', 'a', 'r', 'e', 'm', 'i', 'n', 'a']], [['s', 't', 'a', 'y', 'e', 'd', '.', '1', 'S', 'G']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "P-ban"), ("complementizer", "pu"), ("verb", "metaniono"), ("position", "internal_argument")] }

def ex_32c : Datum :=
  { id := "angelopoulos2026_32c"
    source := ⟨"angelopoulos-2026", "ex. (32c)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Metanjono ja pu paremina."
    glossedTokens := [("Metanjono", "regret.1SG"), ("ja", "for"), ("pu", "PU"), ("paremina", "stayed.1SG")]
    glossedWords := [⟨[['M', 'e', 't', 'a', 'n', 'j', 'o', 'n', 'o']], [['r', 'e', 'g', 'r', 'e', 't', '.', '1', 'S', 'G']]⟩, ⟨[['j', 'a']], [['f', 'o', 'r']]⟩, ⟨[['p', 'u']], [['P', 'U']]⟩, ⟨[['p', 'a', 'r', 'e', 'm', 'i', 'n', 'a']], [['s', 't', 'a', 'y', 'e', 'd', '.', '1', 'S', 'G']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "P-ban"), ("verb", "metaniono"), ("complementizer", "pu"), ("position", "p_complement"), ("confound", "p_ban")] }

def ex_33a : Datum :=
  { id := "angelopoulos2026_33a"
    source := ⟨"angelopoulos-2026", "ex. (33a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Afti i fimi ine aliθis."
    glossedTokens := [("Afti", "this.F.SG.NOM"), ("i", "the.F.SG.NOM"), ("fimi", "rumor.F.SG.NOM"), ("ine", "be.3SG"), ("aliθis", "true.F.SG.NOM")]
    glossedWords := [⟨[['A', 'f', 't', 'i']], [['t', 'h', 'i', 's', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['i']], [['t', 'h', 'e', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['f', 'i', 'm', 'i']], [['r', 'u', 'm', 'o', 'r', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['i', 'n', 'e']], [['b', 'e', '.', '3', 'S', 'G']]⟩, ⟨[['a', 'l', 'i', 'θ', 'i', 's']], [['t', 'r', 'u', 'e', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Afti i fimi ine lanθasmeni.", .acceptable)]
    readings := []
    paperFeatures := [("diagnostic", "truth-predicates"), ("nounSort", "content")] }

def ex_33b : Datum :=
  { id := "angelopoulos2026_33b"
    source := ⟨"angelopoulos-2026", "ex. (33b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Afti i katastasi ine aliθis."
    glossedTokens := [("Afti", "this.F.SG.NOM"), ("i", "the.F.SG.NOM"), ("katastasi", "situation.F.SG.NOM"), ("ine", "be.3SG"), ("aliθis", "true.F.SG.NOM")]
    glossedWords := [⟨[['A', 'f', 't', 'i']], [['t', 'h', 'i', 's', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['i']], [['t', 'h', 'e', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['k', 'a', 't', 'a', 's', 't', 'a', 's', 'i']], [['s', 'i', 't', 'u', 'a', 't', 'i', 'o', 'n', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['i', 'n', 'e']], [['b', 'e', '.', '3', 'S', 'G']]⟩, ⟨[['a', 'l', 'i', 'θ', 'i', 's']], [['t', 'r', 'u', 'e', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    alternatives := [("Afti i katastasi ine lanθasmeni.", .unacceptable)]
    readings := []
    paperFeatures := [("diagnostic", "truth-predicates"), ("nounSort", "situation")] }

def ex_34a : Datum :=
  { id := "angelopoulos2026_34a"
    source := ⟨"angelopoulos-2026", "ex. (34a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Tetjes fimes δen simvenun sixna."
    glossedTokens := [("Tetjes", "such.F.PL.NOM"), ("fimes", "rumors.F.PL.NOM"), ("δen", "not"), ("simvenun", "occur.3PL"), ("sixna", "often")]
    glossedWords := [⟨[['T', 'e', 't', 'j', 'e', 's']], [['s', 'u', 'c', 'h', '.', 'F', '.', 'P', 'L', '.', 'N', 'O', 'M']]⟩, ⟨[['f', 'i', 'm', 'e', 's']], [['r', 'u', 'm', 'o', 'r', 's', '.', 'F', '.', 'P', 'L', '.', 'N', 'O', 'M']]⟩, ⟨[['δ', 'e', 'n']], [['n', 'o', 't']]⟩, ⟨[['s', 'i', 'm', 'v', 'e', 'n', 'u', 'n']], [['o', 'c', 'c', 'u', 'r', '.', '3', 'P', 'L']]⟩, ⟨[['s', 'i', 'x', 'n', 'a']], [['o', 'f', 't', 'e', 'n']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    alternatives := [("Tetjes iδees δen simvenun sixna.", .unacceptable), ("Tetjes proiδopiisis δen simvenun sixna.", .unacceptable), ("Tetjes pepiθisis δen simvenun sixna.", .unacceptable), ("Tetjes ipoθesis δen simvenun sixna.", .unacceptable), ("Tetjes θeories δen simvenun sixna.", .unacceptable)]
    readings := []
    paperFeatures := [("diagnostic", "occurrence-predicates"), ("nounSort", "content")] }

def ex_34b : Datum :=
  { id := "angelopoulos2026_34b"
    source := ⟨"angelopoulos-2026", "ex. (34b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Tetjes periptosis δen simvenun sixna."
    glossedTokens := [("Tetjes", "such.F.PL.NOM"), ("periptosis", "situations.F.PL.NOM"), ("δen", "not"), ("simvenun", "occur.3PL"), ("sixna", "often")]
    glossedWords := [⟨[['T', 'e', 't', 'j', 'e', 's']], [['s', 'u', 'c', 'h', '.', 'F', '.', 'P', 'L', '.', 'N', 'O', 'M']]⟩, ⟨[['p', 'e', 'r', 'i', 'p', 't', 'o', 's', 'i', 's']], [['s', 'i', 't', 'u', 'a', 't', 'i', 'o', 'n', 's', '.', 'F', '.', 'P', 'L', '.', 'N', 'O', 'M']]⟩, ⟨[['δ', 'e', 'n']], [['n', 'o', 't']]⟩, ⟨[['s', 'i', 'm', 'v', 'e', 'n', 'u', 'n']], [['o', 'c', 'c', 'u', 'r', '.', '3', 'P', 'L']]⟩, ⟨[['s', 'i', 'x', 'n', 'a']], [['o', 'f', 't', 'e', 'n']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Tetjes katastasis δen simvenun sixna.", .acceptable)]
    readings := []
    paperFeatures := [("diagnostic", "occurrence-predicates"), ("nounSort", "situation")] }

def ex_3a : Datum :=
  { id := "angelopoulos2026_3a"
    source := ⟨"angelopoulos-2026", "ex. (3a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "To pistevi oti katalaveni tin katastasi."
    glossedTokens := [("To", "3SG.N.ACC"), ("pistevi", "believe.3SG"), ("oti", "OTI"), ("katalaveni", "understand.3SG"), ("tin", "the.F.SG.ACC"), ("katastasi", "situation.F.SG.ACC")]
    glossedWords := [⟨[['T', 'o']], [['3', 'S', 'G', '.', 'N', '.', 'A', 'C', 'C']]⟩, ⟨[['p', 'i', 's', 't', 'e', 'v', 'i']], [['b', 'e', 'l', 'i', 'e', 'v', 'e', '.', '3', 'S', 'G']]⟩, ⟨[['o', 't', 'i']], [['O', 'T', 'I']]⟩, ⟨[['k', 'a', 't', 'a', 'l', 'a', 'v', 'e', 'n', 'i']], [['u', 'n', 'd', 'e', 'r', 's', 't', 'a', 'n', 'd', '.', '3', 'S', 'G']]⟩, ⟨[['t', 'i', 'n']], [['t', 'h', 'e', '.', 'F', '.', 'S', 'G', '.', 'A', 'C', 'C']]⟩, ⟨[['k', 'a', 't', 'a', 's', 't', 'a', 's', 'i']], [['s', 'i', 't', 'u', 'a', 't', 'i', 'o', 'n', '.', 'F', '.', 'S', 'G', '.', 'A', 'C', 'C']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("To pistevi pu katalaveni tin katastasi.", .ungrammatical)]
    readings := []
    paperFeatures := [("verb", "pistevo"), ("complementizer", "oti"), ("position", "internal_argument"), ("diagnostic", "clitic-doubling")] }

def ex_3b : Datum :=
  { id := "angelopoulos2026_3b"
    source := ⟨"angelopoulos-2026", "ex. (3b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "To metanjose pu δen θa ksanavlepodan pote."
    glossedTokens := [("To", "3SG.N.ACC"), ("metanjose", "regret.3SG"), ("pu", "PU"), ("δen", "not"), ("θa", "would"), ("ksanavlepodan", "see.3PL"), ("pote", "never")]
    glossedWords := [⟨[['T', 'o']], [['3', 'S', 'G', '.', 'N', '.', 'A', 'C', 'C']]⟩, ⟨[['m', 'e', 't', 'a', 'n', 'j', 'o', 's', 'e']], [['r', 'e', 'g', 'r', 'e', 't', '.', '3', 'S', 'G']]⟩, ⟨[['p', 'u']], [['P', 'U']]⟩, ⟨[['δ', 'e', 'n']], [['n', 'o', 't']]⟩, ⟨[['θ', 'a']], [['w', 'o', 'u', 'l', 'd']]⟩, ⟨[['k', 's', 'a', 'n', 'a', 'v', 'l', 'e', 'p', 'o', 'd', 'a', 'n']], [['s', 'e', 'e', '.', '3', 'P', 'L']]⟩, ⟨[['p', 'o', 't', 'e']], [['n', 'e', 'v', 'e', 'r']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("To metanjose oti δen θa ksanavlepodan pote.", .ungrammatical)]
    readings := []
    paperFeatures := [("verb", "metaniono"), ("complementizer", "pu"), ("position", "internal_argument"), ("diagnostic", "clitic-doubling")] }

def ex_4a : Datum :=
  { id := "angelopoulos2026_4a"
    source := ⟨"angelopoulos-2026", "ex. (4a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I Maria mas eksijise kala oti i Ji ine stroɟili."
    glossedTokens := [("I", "the.F.SG.NOM"), ("Maria", "Maria.F.SG.NOM"), ("mas", "us.1PL.DAT"), ("eksijise", "explained.3SG"), ("kala", "well"), ("oti", "OTI"), ("i", "the.F.SG.NOM"), ("Ji", "Earth.F.SG.NOM"), ("ine", "be.3SG"), ("stroɟili", "round.F.SG.NOM")]
    glossedWords := [⟨[['I']], [['t', 'h', 'e', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['M', 'a', 'r', 'i', 'a']], [['M', 'a', 'r', 'i', 'a', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['m', 'a', 's']], [['u', 's', '.', '1', 'P', 'L', '.', 'D', 'A', 'T']]⟩, ⟨[['e', 'k', 's', 'i', 'j', 'i', 's', 'e']], [['e', 'x', 'p', 'l', 'a', 'i', 'n', 'e', 'd', '.', '3', 'S', 'G']]⟩, ⟨[['k', 'a', 'l', 'a']], [['w', 'e', 'l', 'l']]⟩, ⟨[['o', 't', 'i']], [['O', 'T', 'I']]⟩, ⟨[['i']], [['t', 'h', 'e', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['J', 'i']], [['E', 'a', 'r', 't', 'h', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['i', 'n', 'e']], [['b', 'e', '.', '3', 'S', 'G']]⟩, ⟨[['s', 't', 'r', 'o', 'ɟ', 'i', 'l', 'i']], [['r', 'o', 'u', 'n', 'd', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("explanans", .acceptable)]
    paperFeatures := [("verb", "eksigo"), ("complementizer", "oti"), ("position", "internal_argument"), ("composition", "predicate_modification")] }

def ex_4b : Datum :=
  { id := "angelopoulos2026_4b"
    source := ⟨"angelopoulos-2026", "ex. (4b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I Maria mas eksijise kala to oti i Ji ine stroɟili."
    glossedTokens := [("I", "the.F.SG.NOM"), ("Maria", "Maria.F.SG.NOM"), ("mas", "us.1PL.DAT"), ("eksijise", "explained.3SG"), ("kala", "well"), ("to", "the.N.SG.ACC"), ("oti", "OTI"), ("i", "the.F.SG.NOM"), ("Ji", "Earth.F.SG.NOM"), ("ine", "be.3SG"), ("stroɟili", "round.F.SG.NOM")]
    glossedWords := [⟨[['I']], [['t', 'h', 'e', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['M', 'a', 'r', 'i', 'a']], [['M', 'a', 'r', 'i', 'a', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['m', 'a', 's']], [['u', 's', '.', '1', 'P', 'L', '.', 'D', 'A', 'T']]⟩, ⟨[['e', 'k', 's', 'i', 'j', 'i', 's', 'e']], [['e', 'x', 'p', 'l', 'a', 'i', 'n', 'e', 'd', '.', '3', 'S', 'G']]⟩, ⟨[['k', 'a', 'l', 'a']], [['w', 'e', 'l', 'l']]⟩, ⟨[['t', 'o']], [['t', 'h', 'e', '.', 'N', '.', 'S', 'G', '.', 'A', 'C', 'C']]⟩, ⟨[['o', 't', 'i']], [['O', 'T', 'I']]⟩, ⟨[['i']], [['t', 'h', 'e', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['J', 'i']], [['E', 'a', 'r', 't', 'h', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['i', 'n', 'e']], [['b', 'e', '.', '3', 'S', 'G']]⟩, ⟨[['s', 't', 'r', 'o', 'ɟ', 'i', 'l', 'i']], [['r', 'o', 'u', 'n', 'd', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("explanandum", .acceptable)]
    paperFeatures := [("verb", "eksigo"), ("complementizer", "oti"), ("nominalized", "yes"), ("composition", "functional_application")] }

def ex_4c : Datum :=
  { id := "angelopoulos2026_4c"
    source := ⟨"angelopoulos-2026", "ex. (4c)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I Maria mas to eksijise kala oti i Ji ine stroɟili."
    glossedTokens := [("I", "the.F.SG.NOM"), ("Maria", "Maria.F.SG.NOM"), ("mas", "us.1PL.DAT"), ("to", "3SG.N.ACC"), ("eksijise", "explained.3SG"), ("kala", "well"), ("oti", "OTI"), ("i", "the.F.SG.NOM"), ("Ji", "Earth.F.SG.NOM"), ("ine", "be.3SG"), ("stroɟili", "round.F.SG.NOM")]
    glossedWords := [⟨[['I']], [['t', 'h', 'e', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['M', 'a', 'r', 'i', 'a']], [['M', 'a', 'r', 'i', 'a', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['m', 'a', 's']], [['u', 's', '.', '1', 'P', 'L', '.', 'D', 'A', 'T']]⟩, ⟨[['t', 'o']], [['3', 'S', 'G', '.', 'N', '.', 'A', 'C', 'C']]⟩, ⟨[['e', 'k', 's', 'i', 'j', 'i', 's', 'e']], [['e', 'x', 'p', 'l', 'a', 'i', 'n', 'e', 'd', '.', '3', 'S', 'G']]⟩, ⟨[['k', 'a', 'l', 'a']], [['w', 'e', 'l', 'l']]⟩, ⟨[['o', 't', 'i']], [['O', 'T', 'I']]⟩, ⟨[['i']], [['t', 'h', 'e', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['J', 'i']], [['E', 'a', 'r', 't', 'h', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['i', 'n', 'e']], [['b', 'e', '.', '3', 'S', 'G']]⟩, ⟨[['s', 't', 'r', 'o', 'ɟ', 'i', 'l', 'i']], [['r', 'o', 'u', 'n', 'd', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("explanans", .acceptable)]
    paperFeatures := [("verb", "eksigo"), ("complementizer", "oti"), ("position", "internal_argument"), ("diagnostic", "clitic-doubling"), ("composition", "predicate_modification")] }

def ex_6a : Datum :=
  { id := "angelopoulos2026_6a"
    source := ⟨"angelopoulos-2026", "ex. (6a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Oti i Ji ine stroɟili tis eksijiθike tis δonatas."
    glossedTokens := [("Oti", "OTI"), ("i", "the.F.SG.NOM"), ("Ji", "Earth.F.SG.NOM"), ("ine", "be.3SG"), ("stroɟili", "round.F.SG.NOM"), ("tis", "3SG.F.DAT"), ("eksijiθike", "was.explained.3SG"), ("tis", "the.F.SG.DAT"), ("δonatas", "δonata.F.SG.DAT")]
    glossedWords := [⟨[['O', 't', 'i']], [['O', 'T', 'I']]⟩, ⟨[['i']], [['t', 'h', 'e', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['J', 'i']], [['E', 'a', 'r', 't', 'h', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['i', 'n', 'e']], [['b', 'e', '.', '3', 'S', 'G']]⟩, ⟨[['s', 't', 'r', 'o', 'ɟ', 'i', 'l', 'i']], [['r', 'o', 'u', 'n', 'd', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['t', 'i', 's']], [['3', 'S', 'G', '.', 'F', '.', 'D', 'A', 'T']]⟩, ⟨[['e', 'k', 's', 'i', 'j', 'i', 'θ', 'i', 'k', 'e']], [['w', 'a', 's', '.', 'e', 'x', 'p', 'l', 'a', 'i', 'n', 'e', 'd', '.', '3', 'S', 'G']]⟩, ⟨[['t', 'i', 's']], [['t', 'h', 'e', '.', 'F', '.', 'S', 'G', '.', 'D', 'A', 'T']]⟩, ⟨[['δ', 'o', 'n', 'a', 't', 'a', 's']], [['δ', 'o', 'n', 'a', 't', 'a', '.', 'F', '.', 'S', 'G', '.', 'D', 'A', 'T']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Oti i Ji ine stroɟili eksijiθike tis δonatas.", .ungrammatical)]
    readings := [("explanans", .acceptable)]
    paperFeatures := [("verb", "eksigo"), ("complementizer", "oti"), ("position", "derived_subject"), ("diagnostic", "passivization")] }

def ex_11a : Datum :=
  { id := "angelopoulos2026_11a"
    source := ⟨"angelopoulos-2026", "ex. (11a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Oti eçis filus δixni pola ja sena."
    glossedTokens := [("Oti", "OTI"), ("eçis", "have.2SG"), ("filus", "friends.M.PL.ACC"), ("δixni", "show.3SG"), ("pola", "a lot"), ("ja", "for"), ("sena", "you.2SG.ACC")]
    glossedWords := [⟨[['O', 't', 'i']], [['O', 'T', 'I']]⟩, ⟨[['e', 'ç', 'i', 's']], [['h', 'a', 'v', 'e', '.', '2', 'S', 'G']]⟩, ⟨[['f', 'i', 'l', 'u', 's']], [['f', 'r', 'i', 'e', 'n', 'd', 's', '.', 'M', '.', 'P', 'L', '.', 'A', 'C', 'C']]⟩, ⟨[['δ', 'i', 'x', 'n', 'i']], [['s', 'h', 'o', 'w', '.', '3', 'S', 'G']]⟩, ⟨[['p', 'o', 'l', 'a']], [['a', ' ', 'l', 'o', 't']]⟩, ⟨[['j', 'a']], [['f', 'o', 'r']]⟩, ⟨[['s', 'e', 'n', 'a']], [['y', 'o', 'u', '.', '2', 'S', 'G', '.', 'A', 'C', 'C']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("complementizer", "oti"), ("position", "external_argument")] }

def ex_12a : Datum :=
  { id := "angelopoulos2026_12a"
    source := ⟨"angelopoulos-2026", "ex. (12a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Pu eçis filus δixni pola ja sena."
    glossedTokens := [("Pu", "PU"), ("eçis", "have.2SG"), ("filus", "friends.M.PL.ACC"), ("δixni", "show.3SG"), ("pola", "a lot"), ("ja", "for"), ("sena", "you.2SG.ACC")]
    glossedWords := [⟨[['P', 'u']], [['P', 'U']]⟩, ⟨[['e', 'ç', 'i', 's']], [['h', 'a', 'v', 'e', '.', '2', 'S', 'G']]⟩, ⟨[['f', 'i', 'l', 'u', 's']], [['f', 'r', 'i', 'e', 'n', 'd', 's', '.', 'M', '.', 'P', 'L', '.', 'A', 'C', 'C']]⟩, ⟨[['δ', 'i', 'x', 'n', 'i']], [['s', 'h', 'o', 'w', '.', '3', 'S', 'G']]⟩, ⟨[['p', 'o', 'l', 'a']], [['a', ' ', 'l', 'o', 't']]⟩, ⟨[['j', 'a']], [['f', 'o', 'r']]⟩, ⟨[['s', 'e', 'n', 'a']], [['y', 'o', 'u', '.', '2', 'S', 'G', '.', 'A', 'C', 'C']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("complementizer", "pu"), ("position", "external_argument")] }

def ex_14a : Datum :=
  { id := "angelopoulos2026_14a"
    source := ⟨"angelopoulos-2026", "ex. (14a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "δen tus arese pu efiɣan xoris enimerosi."
    glossedTokens := [("δen", "not"), ("tus", "3PL.DAT"), ("arese", "like.3SG"), ("pu", "PU"), ("efiɣan", "left.3PL"), ("xoris", "without"), ("enimerosi", "update")]
    glossedWords := [⟨[['δ', 'e', 'n']], [['n', 'o', 't']]⟩, ⟨[['t', 'u', 's']], [['3', 'P', 'L', '.', 'D', 'A', 'T']]⟩, ⟨[['a', 'r', 'e', 's', 'e']], [['l', 'i', 'k', 'e', '.', '3', 'S', 'G']]⟩, ⟨[['p', 'u']], [['P', 'U']]⟩, ⟨[['e', 'f', 'i', 'ɣ', 'a', 'n']], [['l', 'e', 'f', 't', '.', '3', 'P', 'L']]⟩, ⟨[['x', 'o', 'r', 'i', 's']], [['w', 'i', 't', 'h', 'o', 'u', 't']]⟩, ⟨[['e', 'n', 'i', 'm', 'e', 'r', 'o', 's', 'i']], [['u', 'p', 'd', 'a', 't', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "areso"), ("complementizer", "pu"), ("position", "internal_argument")] }

def ex_14b : Datum :=
  { id := "angelopoulos2026_14b"
    source := ⟨"angelopoulos-2026", "ex. (14b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Pu efiɣan xoris enimerosi δen tus arese."
    glossedTokens := [("Pu", "PU"), ("efiɣan", "left.3PL"), ("xoris", "without"), ("enimerosi", "update"), ("δen", "not"), ("tus", "3PL.DAT"), ("arese", "like.3SG")]
    glossedWords := [⟨[['P', 'u']], [['P', 'U']]⟩, ⟨[['e', 'f', 'i', 'ɣ', 'a', 'n']], [['l', 'e', 'f', 't', '.', '3', 'P', 'L']]⟩, ⟨[['x', 'o', 'r', 'i', 's']], [['w', 'i', 't', 'h', 'o', 'u', 't']]⟩, ⟨[['e', 'n', 'i', 'm', 'e', 'r', 'o', 's', 'i']], [['u', 'p', 'd', 'a', 't', 'e']]⟩, ⟨[['δ', 'e', 'n']], [['n', 'o', 't']]⟩, ⟨[['t', 'u', 's']], [['3', 'P', 'L', '.', 'D', 'A', 'T']]⟩, ⟨[['a', 'r', 'e', 's', 'e']], [['l', 'i', 'k', 'e', '.', '3', 'S', 'G']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "areso"), ("complementizer", "pu"), ("position", "derived_subject")] }

def ex_19c : Datum :=
  { id := "angelopoulos2026_19c"
    source := ⟨"angelopoulos-2026", "ex. (19c)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "θimose pu apoliun prosopiko."
    glossedTokens := [("θimose", "was.angry.3SG"), ("pu", "PU"), ("apoliun", "fired.3PL"), ("prosopiko", "personnel.N.SG.ACC")]
    glossedWords := [⟨[['θ', 'i', 'm', 'o', 's', 'e']], [['w', 'a', 's', '.', 'a', 'n', 'g', 'r', 'y', '.', '3', 'S', 'G']]⟩, ⟨[['p', 'u']], [['P', 'U']]⟩, ⟨[['a', 'p', 'o', 'l', 'i', 'u', 'n']], [['f', 'i', 'r', 'e', 'd', '.', '3', 'P', 'L']]⟩, ⟨[['p', 'r', 'o', 's', 'o', 'p', 'i', 'k', 'o']], [['p', 'e', 'r', 's', 'o', 'n', 'n', 'e', 'l', '.', 'N', '.', 'S', 'G', '.', 'A', 'C', 'C']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("θimose apotoma pu apoliun prosopiko.", .ungrammatical)]
    readings := []
    paperFeatures := [("verb", "thimono_stative"), ("complementizer", "pu"), ("position", "internal_argument"), ("diagnostic", "manner-adverb")] }

def ex_20c : Datum :=
  { id := "angelopoulos2026_20c"
    source := ⟨"angelopoulos-2026", "ex. (20c)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Metanjose pu aɣorase mavro pukamiso."
    glossedTokens := [("Metanjose", "regretted.3SG"), ("pu", "PU"), ("aɣorase", "bought.3SG"), ("mavro", "black.N.SG.ACC"), ("pukamiso", "shirt.N.SG.ACC")]
    glossedWords := [⟨[['M', 'e', 't', 'a', 'n', 'j', 'o', 's', 'e']], [['r', 'e', 'g', 'r', 'e', 't', 't', 'e', 'd', '.', '3', 'S', 'G']]⟩, ⟨[['p', 'u']], [['P', 'U']]⟩, ⟨[['a', 'ɣ', 'o', 'r', 'a', 's', 'e']], [['b', 'o', 'u', 'g', 'h', 't', '.', '3', 'S', 'G']]⟩, ⟨[['m', 'a', 'v', 'r', 'o']], [['b', 'l', 'a', 'c', 'k', '.', 'N', '.', 'S', 'G', '.', 'A', 'C', 'C']]⟩, ⟨[['p', 'u', 'k', 'a', 'm', 'i', 's', 'o']], [['s', 'h', 'i', 'r', 't', '.', 'N', '.', 'S', 'G', '.', 'A', 'C', 'C']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Metanjose efkola pu aɣorase mavro pukamiso.", .ungrammatical)]
    readings := []
    paperFeatures := [("verb", "metaniono"), ("complementizer", "pu"), ("position", "internal_argument"), ("diagnostic", "manner-adverb")] }

def ex_21a : Datum :=
  { id := "angelopoulos2026_21a"
    source := ⟨"angelopoulos-2026", "ex. (21a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Iksere oti prepi na alaksi stratijiki."
    glossedTokens := [("Iksere", "knew.3SG"), ("oti", "OTI"), ("prepi", "must.3SG"), ("na", "na"), ("alaksi", "change.3SG"), ("stratijiki", "strategy.F.SG.ACC")]
    glossedWords := [⟨[['I', 'k', 's', 'e', 'r', 'e']], [['k', 'n', 'e', 'w', '.', '3', 'S', 'G']]⟩, ⟨[['o', 't', 'i']], [['O', 'T', 'I']]⟩, ⟨[['p', 'r', 'e', 'p', 'i']], [['m', 'u', 's', 't', '.', '3', 'S', 'G']]⟩, ⟨[['n', 'a']], [['n', 'a']]⟩, ⟨[['a', 'l', 'a', 'k', 's', 'i']], [['c', 'h', 'a', 'n', 'g', 'e', '.', '3', 'S', 'G']]⟩, ⟨[['s', 't', 'r', 'a', 't', 'i', 'j', 'i', 'k', 'i']], [['s', 't', 'r', 'a', 't', 'e', 'g', 'y', '.', 'F', '.', 'S', 'G', '.', 'A', 'C', 'C']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Iksere efkola oti prepi na alaksi stratijiki.", .ungrammatical)]
    readings := []
    paperFeatures := [("verb", "ksero"), ("complementizer", "oti"), ("position", "internal_argument"), ("diagnostic", "manner-adverb")] }

def ex_21b : Datum :=
  { id := "angelopoulos2026_21b"
    source := ⟨"angelopoulos-2026", "ex. (21b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Arketos kosmos δen siniδitopii (efkola) oti i periɣrafiki kanones ine δjaforetiki apo tus riθmistikus."
    glossedTokens := [("Arketos", "many.M.SG.NOM"), ("kosmos", "people.M.SG.NOM"), ("δen", "not"), ("siniδitopii", "realize.3SG"), ("(efkola)", "easily"), ("oti", "OTI"), ("i", "the.M.PL.NOM"), ("periɣrafiki", "descriptive.M.PL.NOM"), ("kanones", "rules.M.PL.NOM"), ("ine", "be.3PL"), ("δjaforetiki", "different.M.PL.NOM"), ("apo", "from"), ("tus", "the.M.PL.ACC"), ("riθmistikus", "prescriptive.M.PL.ACC")]
    glossedWords := [⟨[['A', 'r', 'k', 'e', 't', 'o', 's']], [['m', 'a', 'n', 'y', '.', 'M', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['k', 'o', 's', 'm', 'o', 's']], [['p', 'e', 'o', 'p', 'l', 'e', '.', 'M', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['δ', 'e', 'n']], [['n', 'o', 't']]⟩, ⟨[['s', 'i', 'n', 'i', 'δ', 'i', 't', 'o', 'p', 'i', 'i']], [['r', 'e', 'a', 'l', 'i', 'z', 'e', '.', '3', 'S', 'G']]⟩, ⟨[['e', 'f', 'k', 'o', 'l', 'a']], [['e', 'a', 's', 'i', 'l', 'y']]⟩, ⟨[['o', 't', 'i']], [['O', 'T', 'I']]⟩, ⟨[['i']], [['t', 'h', 'e', '.', 'M', '.', 'P', 'L', '.', 'N', 'O', 'M']]⟩, ⟨[['p', 'e', 'r', 'i', 'ɣ', 'r', 'a', 'f', 'i', 'k', 'i']], [['d', 'e', 's', 'c', 'r', 'i', 'p', 't', 'i', 'v', 'e', '.', 'M', '.', 'P', 'L', '.', 'N', 'O', 'M']]⟩, ⟨[['k', 'a', 'n', 'o', 'n', 'e', 's']], [['r', 'u', 'l', 'e', 's', '.', 'M', '.', 'P', 'L', '.', 'N', 'O', 'M']]⟩, ⟨[['i', 'n', 'e']], [['b', 'e', '.', '3', 'P', 'L']]⟩, ⟨[['δ', 'j', 'a', 'f', 'o', 'r', 'e', 't', 'i', 'k', 'i']], [['d', 'i', 'f', 'f', 'e', 'r', 'e', 'n', 't', '.', 'M', '.', 'P', 'L', '.', 'N', 'O', 'M']]⟩, ⟨[['a', 'p', 'o']], [['f', 'r', 'o', 'm']]⟩, ⟨[['t', 'u', 's']], [['t', 'h', 'e', '.', 'M', '.', 'P', 'L', '.', 'A', 'C', 'C']]⟩, ⟨[['r', 'i', 'θ', 'm', 'i', 's', 't', 'i', 'k', 'u', 's']], [['p', 'r', 'e', 's', 'c', 'r', 'i', 'p', 't', 'i', 'v', 'e', '.', 'M', '.', 'P', 'L', '.', 'A', 'C', 'C']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Arketos kosmos δen katalaveni (efkola) oti i periɣrafiki kanones ine δjaforetiki apo tus riθmistikus.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "sinidhitopio"), ("complementizer", "oti"), ("position", "internal_argument"), ("diagnostic", "manner-adverb"), ("confound", "manner_adverb")] }

def ex_22a : Datum :=
  { id := "angelopoulos2026_22a"
    source := ⟨"angelopoulos-2026", "ex. (22a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "θimame me δiskolia oti milises s-ti Maria."
    glossedTokens := [("θimame", "remember.1SG"), ("me", "with"), ("δiskolia", "difficulty"), ("oti", "OTI"), ("milises", "talk.2SG"), ("s-ti", "to-the.F.SG.ACC"), ("Maria", "Maria.F.SG.ACC")]
    glossedWords := [⟨[['θ', 'i', 'm', 'a', 'm', 'e']], [['r', 'e', 'm', 'e', 'm', 'b', 'e', 'r', '.', '1', 'S', 'G']]⟩, ⟨[['m', 'e']], [['w', 'i', 't', 'h']]⟩, ⟨[['δ', 'i', 's', 'k', 'o', 'l', 'i', 'a']], [['d', 'i', 'f', 'f', 'i', 'c', 'u', 'l', 't', 'y']]⟩, ⟨[['o', 't', 'i']], [['O', 'T', 'I']]⟩, ⟨[['m', 'i', 'l', 'i', 's', 'e', 's']], [['t', 'a', 'l', 'k', '.', '2', 'S', 'G']]⟩, ⟨[['s'], ['t', 'i']], [['t', 'o'], ['t', 'h', 'e', '.', 'F', '.', 'S', 'G', '.', 'A', 'C', 'C']]⟩, ⟨[['M', 'a', 'r', 'i', 'a']], [['M', 'a', 'r', 'i', 'a', '.', 'F', '.', 'S', 'G', '.', 'A', 'C', 'C']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "thimame"), ("complementizer", "oti"), ("diagnostic", "manner-adverb"), ("confound", "manner_adverb")] }

def ex_22b : Datum :=
  { id := "angelopoulos2026_22b"
    source := ⟨"angelopoulos-2026", "ex. (22b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "θimame me δiskolia pu milises s-ti Maria."
    glossedTokens := [("θimame", "remember.1SG"), ("me", "with"), ("δiskolia", "difficulty"), ("pu", "PU"), ("milises", "talk.2SG"), ("s-ti", "to-the.F.SG.ACC"), ("Maria", "Maria.F.SG.ACC")]
    glossedWords := [⟨[['θ', 'i', 'm', 'a', 'm', 'e']], [['r', 'e', 'm', 'e', 'm', 'b', 'e', 'r', '.', '1', 'S', 'G']]⟩, ⟨[['m', 'e']], [['w', 'i', 't', 'h']]⟩, ⟨[['δ', 'i', 's', 'k', 'o', 'l', 'i', 'a']], [['d', 'i', 'f', 'f', 'i', 'c', 'u', 'l', 't', 'y']]⟩, ⟨[['p', 'u']], [['P', 'U']]⟩, ⟨[['m', 'i', 'l', 'i', 's', 'e', 's']], [['t', 'a', 'l', 'k', '.', '2', 'S', 'G']]⟩, ⟨[['s'], ['t', 'i']], [['t', 'o'], ['t', 'h', 'e', '.', 'F', '.', 'S', 'G', '.', 'A', 'C', 'C']]⟩, ⟨[['M', 'a', 'r', 'i', 'a']], [['M', 'a', 'r', 'i', 'a', '.', 'F', '.', 'S', 'G', '.', 'A', 'C', 'C']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "thimame_perception"), ("complementizer", "pu"), ("diagnostic", "manner-adverb"), ("confound", "manner_adverb")] }

def ex_23c : Datum :=
  { id := "angelopoulos2026_23c"
    source := ⟨"angelopoulos-2026", "ex. (23c)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "θimose pu psifistike o nomos."
    glossedTokens := [("θimose", "got.angry.3SG"), ("pu", "PU"), ("psifistike", "was.voted.3SG"), ("o", "the.M.SG.NOM"), ("nomos", "law.M.SG.NOM")]
    glossedWords := [⟨[['θ', 'i', 'm', 'o', 's', 'e']], [['g', 'o', 't', '.', 'a', 'n', 'g', 'r', 'y', '.', '3', 'S', 'G']]⟩, ⟨[['p', 'u']], [['P', 'U']]⟩, ⟨[['p', 's', 'i', 'f', 'i', 's', 't', 'i', 'k', 'e']], [['w', 'a', 's', '.', 'v', 'o', 't', 'e', 'd', '.', '3', 'S', 'G']]⟩, ⟨[['o']], [['t', 'h', 'e', '.', 'M', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['n', 'o', 'm', 'o', 's']], [['l', 'a', 'w', '.', 'M', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("θimose mesa se pede lepta pu psifistike o nomos.", .ungrammatical)]
    readings := []
    paperFeatures := [("verb", "thimono_stative"), ("complementizer", "pu"), ("position", "internal_argument"), ("diagnostic", "in-adverbial")] }

def ex_35a : Datum :=
  { id := "angelopoulos2026_35a"
    source := ⟨"angelopoulos-2026", "ex. (35a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Akuse ti fimi oti i Ji ine stroɟili."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Akuse ti fimi pu i Ji ine stroɟili.", .ungrammatical)]
    readings := []
    paperFeatures := [("complementizer", "oti"), ("nounSort", "content"), ("diagnostic", "noun-complement")] }

def ex_35b : Datum :=
  { id := "angelopoulos2026_35b"
    source := ⟨"angelopoulos-2026", "ex. (35b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Afora tin periptosi pu o pateras ine apon."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Afora tin periptosi oti o pateras ine apon.", .ungrammatical)]
    readings := []
    paperFeatures := [("complementizer", "pu"), ("nounSort", "situation"), ("diagnostic", "noun-complement")] }

def ex_36a : Datum :=
  { id := "angelopoulos2026_36a"
    source := ⟨"angelopoulos-2026", "ex. (36a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I pisti oti i maskes ine pali ipoxreotikes ine aliθis."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("complementizer", "oti"), ("nounSort", "content"), ("diagnostic", "truth-predicates")] }

def ex_37a : Datum :=
  { id := "angelopoulos2026_37a"
    source := ⟨"angelopoulos-2026", "ex. (37a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I stenaxorja tus pu efije i Maria ine aliθis."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("complementizer", "pu"), ("nounSort", "situation"), ("diagnostic", "truth-predicates")] }

def ex_38a : Datum :=
  { id := "angelopoulos2026_38a"
    source := ⟨"angelopoulos-2026", "ex. (38a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "θimude oti i ɣata efaje to psari, ala i ɣata δen to içe fai s-tin praɣmatikotita."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "thimame"), ("complementizer", "oti"), ("diagnostic", "factivity"), ("confound", "factivity_continuation")] }

def ex_38b : Datum :=
  { id := "angelopoulos2026_38b"
    source := ⟨"angelopoulos-2026", "ex. (38b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "θimude pu i ɣata efaje to psari, ala i ɣata δen to içe fai s-tin praɣmatikotita."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "thimame_perception"), ("complementizer", "pu"), ("diagnostic", "factivity"), ("confound", "factivity_continuation")] }

def fn14_i : Datum :=
  { id := "angelopoulos2026_fn14_i"
    source := ⟨"angelopoulos-2026", "fn. 14 (i)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Içe simvi oti kanume lathos."
    glossedTokens := [("Içe", "had.3SG"), ("simvi", "happened.3SG"), ("oti", "OTI"), ("kanume", "make.1PL"), ("lathos", "mistake.N.SG.ACC")]
    glossedWords := [⟨[['I', 'ç', 'e']], [['h', 'a', 'd', '.', '3', 'S', 'G']]⟩, ⟨[['s', 'i', 'm', 'v', 'i']], [['h', 'a', 'p', 'p', 'e', 'n', 'e', 'd', '.', '3', 'S', 'G']]⟩, ⟨[['o', 't', 'i']], [['O', 'T', 'I']]⟩, ⟨[['k', 'a', 'n', 'u', 'm', 'e']], [['m', 'a', 'k', 'e', '.', '1', 'P', 'L']]⟩, ⟨[['l', 'a', 't', 'h', 'o', 's']], [['m', 'i', 's', 't', 'a', 'k', 'e', '.', 'N', '.', 'S', 'G', '.', 'A', 'C', 'C']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := [("Içe simvi pu kanume laθos.", .ungrammatical)]
    readings := []
    paperFeatures := [("verb", "simveni"), ("complementizer", "oti")] }

def ex_43a : Datum :=
  { id := "angelopoulos2026_43a"
    source := ⟨"angelopoulos-2026", "ex. (43a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "To oti eçis filus δixni pola ja sena."
    glossedTokens := [("To", "the"), ("oti", "OTI"), ("eçis", "have.2SG"), ("filus", "friends.M.PL.ACC"), ("δixni", "show.3SG"), ("pola", "a lot"), ("ja", "for"), ("sena", "you.2SG.ACC")]
    glossedWords := [⟨[['T', 'o']], [['t', 'h', 'e']]⟩, ⟨[['o', 't', 'i']], [['O', 'T', 'I']]⟩, ⟨[['e', 'ç', 'i', 's']], [['h', 'a', 'v', 'e', '.', '2', 'S', 'G']]⟩, ⟨[['f', 'i', 'l', 'u', 's']], [['f', 'r', 'i', 'e', 'n', 'd', 's', '.', 'M', '.', 'P', 'L', '.', 'A', 'C', 'C']]⟩, ⟨[['δ', 'i', 'x', 'n', 'i']], [['s', 'h', 'o', 'w', '.', '3', 'S', 'G']]⟩, ⟨[['p', 'o', 'l', 'a']], [['a', ' ', 'l', 'o', 't']]⟩, ⟨[['j', 'a']], [['f', 'o', 'r']]⟩, ⟨[['s', 'e', 'n', 'a']], [['y', 'o', 'u', '.', '2', 'S', 'G', '.', 'A', 'C', 'C']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("complementizer", "oti"), ("position", "external_argument"), ("nominalized", "yes")] }

def ex_44a : Datum :=
  { id := "angelopoulos2026_44a"
    source := ⟨"angelopoulos-2026", "ex. (44a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "To pu eçis filus δixni pola ja sena."
    glossedTokens := [("To", "the"), ("pu", "PU"), ("eçis", "have.2SG"), ("filus", "friends.M.PL.ACC"), ("δixni", "show.3SG"), ("pola", "a lot"), ("ja", "for"), ("sena", "you.2SG.ACC")]
    glossedWords := [⟨[['T', 'o']], [['t', 'h', 'e']]⟩, ⟨[['p', 'u']], [['P', 'U']]⟩, ⟨[['e', 'ç', 'i', 's']], [['h', 'a', 'v', 'e', '.', '2', 'S', 'G']]⟩, ⟨[['f', 'i', 'l', 'u', 's']], [['f', 'r', 'i', 'e', 'n', 'd', 's', '.', 'M', '.', 'P', 'L', '.', 'A', 'C', 'C']]⟩, ⟨[['δ', 'i', 'x', 'n', 'i']], [['s', 'h', 'o', 'w', '.', '3', 'S', 'G']]⟩, ⟨[['p', 'o', 'l', 'a']], [['a', ' ', 'l', 'o', 't']]⟩, ⟨[['j', 'a']], [['f', 'o', 'r']]⟩, ⟨[['s', 'e', 'n', 'a']], [['y', 'o', 'u', '.', '2', 'S', 'G', '.', 'A', 'C', 'C']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("complementizer", "pu"), ("position", "external_argument"), ("nominalized", "yes")] }

def all : List Datum := [ex_1a, ex_1b, ex_31a, ex_31b, ex_31c, ex_32a, ex_32b, ex_32c, ex_33a, ex_33b, ex_34a, ex_34b, ex_3a, ex_3b, ex_4a, ex_4b, ex_4c, ex_6a, ex_11a, ex_12a, ex_14a, ex_14b, ex_19c, ex_20c, ex_21a, ex_21b, ex_22a, ex_22b, ex_23c, ex_35a, ex_35b, ex_36a, ex_37a, ex_38a, ex_38b, fn14_i, ex_43a, ex_44a]

/-- The complementizer of the embedded clause. -/
inductive Complementizer where
  /-- oti: *oti* 'that' -/
  | oti
  /-- pu: *pu* 'that' -/
  | pu
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `complementizer`. -/
def complementizer (e : Datum) : Option Complementizer :=
  e.parse? "complementizer" [("oti", .oti), ("pu", .pu)]

/-- The embedding verb. -/
inductive Verb where
  /-- leo: *leo* 'say' -/
  | leo
  /-- metaniono: *metaniono* 'regret' -/
  | metaniono
  /-- δjafono 'disagree': *δjafono* 'disagree' -/
  | djafono
  /-- pistevo: *pistevo* 'believe' -/
  | pistevo
  /-- eksigo: *eksigo* 'explain' -/
  | eksigo
  /-- areso: *areso* 'like' -/
  | areso
  /-- thimono_stative: *thimono* 'be angry', stative -/
  | thimonoStative
  /-- ksero: *ksero* 'know' -/
  | ksero
  /-- sinidhitopio: *sinidhitopio* 'realize' -/
  | sinidhitopio
  /-- thimame: *thimame* 'remember', attitude -/
  | thimame
  /-- thimame_perception: *thimame* 'remember', perception -/
  | thimamePerception
  /-- simveni: *simveni* 'happen' -/
  | simveni
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `verb`. -/
def verb (e : Datum) : Option Verb :=
  e.parse? "verb" [("leo", .leo), ("metaniono", .metaniono), ("δjafono 'disagree'", .djafono),
    ("pistevo", .pistevo), ("eksigo", .eksigo), ("areso", .areso),
    ("thimono_stative", .thimonoStative), ("ksero", .ksero), ("sinidhitopio", .sinidhitopio),
    ("thimame", .thimame), ("thimame_perception", .thimamePerception), ("simveni", .simveni)]

/-- The position the clause is merged in. -/
inductive Position where
  /-- internal_argument: the internal argument -/
  | internalArgument
  /-- derived_subject: a derived subject -/
  | derivedSubject
  /-- external_argument: the external argument -/
  | externalArgument
  /-- p_complement: the complement of a preposition -/
  | pComplement
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `position`. -/
def position (e : Datum) : Option Position :=
  e.parse? "position" [("internal_argument", .internalArgument), ("derived_subject", .derivedSubject),
    ("external_argument", .externalArgument), ("p_complement", .pComplement)]

/-- The sort of the noun the clause pairs with. -/
inductive NounSort where
  /-- content: content-denoting -/
  | content
  /-- situation: situation-denoting -/
  | situation
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `nounSort`. -/
def nounSort (e : Datum) : Option NounSort :=
  e.parse? "nounSort" [("content", .content), ("situation", .situation)]

/-- The diagnostic the example applies. -/
inductive Diagnostic where
  /-- P-ban: the ban on prepositions -/
  | pBan
  /-- truth-predicates: truth predicates -/
  | truthPredicates
  /-- occurrence-predicates: occurrence predicates -/
  | occurrencePredicates
  /-- clitic-doubling: clitic doubling -/
  | cliticDoubling
  /-- passivization: passivization -/
  | passivization
  /-- manner-adverb: manner adverbs -/
  | mannerAdverb
  /-- in-adverbial: in-adverbials -/
  | inAdverbial
  /-- noun-complement: noun complements -/
  | nounComplement
  /-- factivity: factivity -/
  | factivity
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `diagnostic`. -/
def diagnostic (e : Datum) : Option Diagnostic :=
  e.parse? "diagnostic" [("P-ban", .pBan), ("truth-predicates", .truthPredicates),
    ("occurrence-predicates", .occurrencePredicates), ("clitic-doubling", .cliticDoubling),
    ("passivization", .passivization), ("manner-adverb", .mannerAdverb),
    ("in-adverbial", .inAdverbial), ("noun-complement", .nounComplement),
    ("factivity", .factivity)]

/-- A confound the example controls for. -/
inductive Confound where
  /-- p_ban: the ban on prepositions -/
  | pBan
  /-- manner_adverb: a manner adverb -/
  | mannerAdverb
  /-- factivity_continuation: a factive continuation -/
  | factivityContinuation
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `confound`. -/
def confound (e : Datum) : Option Confound :=
  e.parse? "confound" [("p_ban", .pBan), ("manner_adverb", .mannerAdverb),
    ("factivity_continuation", .factivityContinuation)]

/-- Whether the clause is nominalized. -/
inductive Nominalized where
  /-- yes: nominalized -/
  | yes
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `nominalized`. -/
def nominalized (e : Datum) : Option Nominalized :=
  e.parse? "nominalized" [("yes", .yes)]

end Angelopoulos2026.Examples
