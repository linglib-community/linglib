module

public import Linglib.Data.Examples.Schema

/-!
# `Hanink2021` — typed example data

Auto-generated from `Linglib/Data/Examples/Hanink2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Hanink2021.Examples`.
-/

@[expose] public section

namespace Hanink2021.Examples

def ex1 : Datum :=
  { id := "hanink2021_ex1"
    source := ⟨"hanink-2021", "(1)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "gí: pélew ʔ-íʔiw-i"
    glossedTokens := [("gí:", "GI"), ("pélew", "jackrabbit"), ("ʔ-íʔiw-i", "3/3-eat-IND")]
    glossedWords := [⟨['g', 'í', ':'], ['G', 'I'], [⟨['g', 'í'], ['G', 'I'], none⟩]⟩, ⟨['p', 'é', 'l', 'e', 'w'], ['j', 'a', 'c', 'k', 'r', 'a', 'b', 'b', 'i', 't'], [⟨['p', 'é', 'l', 'e', 'w'], ['j', 'a', 'c', 'k', 'r', 'a', 'b', 'b', 'i', 't'], none⟩]⟩, ⟨['ʔ', '-', 'í', 'ʔ', 'i', 'w', '-', 'i'], ['3', '/', '3', '-', 'e', 'a', 't', '-', 'I', 'N', 'D'], [⟨['ʔ'], ['3', '/', '3'], none⟩, ⟨['í', 'ʔ', 'i', 'w'], ['e', 'a', 't'], some '-'⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("phenomenon", "pronoun"), ("idxForm", "gi"), ("case", "nominative")] }

def ex2 : Datum :=
  { id := "hanink2021_ex2"
    source := ⟨"hanink-2021", "(2)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "hádi-gi pélew Mú:biʔ-i"
    glossedTokens := [("hádi-gi", "DIST-GI"), ("pélew", "jackrabbit"), ("Mú:biʔ-i", "3.run-IND")]
    glossedWords := [⟨['h', 'á', 'd', 'i', '-', 'g', 'i'], ['D', 'I', 'S', 'T', '-', 'G', 'I'], [⟨['h', 'á', 'd', 'i'], ['D', 'I', 'S', 'T'], none⟩, ⟨['g', 'i'], ['G', 'I'], some '-'⟩]⟩, ⟨['p', 'é', 'l', 'e', 'w'], ['j', 'a', 'c', 'k', 'r', 'a', 'b', 'b', 'i', 't'], [⟨['p', 'é', 'l', 'e', 'w'], ['j', 'a', 'c', 'k', 'r', 'a', 'b', 'b', 'i', 't'], none⟩]⟩, ⟨['M', 'ú', ':', 'b', 'i', 'ʔ', '-', 'i'], ['3', '.', 'r', 'u', 'n', '-', 'I', 'N', 'D'], [⟨['M', 'ú', 'b', 'i', 'ʔ'], ['3', '.', 'r', 'u', 'n'], none⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("phenomenon", "demonstrative"), ("idxForm", "gi")] }

def ex3 : Datum :=
  { id := "hanink2021_ex3"
    source := ⟨"hanink-2021", "(3)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "t'é:liwhu šáwlamhu ʔló:t ʔ-í:gi-yi-š-gi ʔwáʔ ʔ-éʔ-i"
    glossedTokens := [("t'é:liwhu", "man"), ("šáwlamhu", "girl"), ("ʔló:t", "yesterday"), ("ʔ-í:gi-yi-š-gi", "3-see-IND-DS-GI"), ("ʔwáʔ", "here"), ("ʔ-éʔ-i", "3-be-IND")]
    glossedWords := [⟨['t', '\'', 'é', ':', 'l', 'i', 'w', 'h', 'u'], ['m', 'a', 'n'], [⟨['t', '\'', 'é', 'l', 'i', 'w', 'h', 'u'], ['m', 'a', 'n'], none⟩]⟩, ⟨['š', 'á', 'w', 'l', 'a', 'm', 'h', 'u'], ['g', 'i', 'r', 'l'], [⟨['š', 'á', 'w', 'l', 'a', 'm', 'h', 'u'], ['g', 'i', 'r', 'l'], none⟩]⟩, ⟨['ʔ', 'l', 'ó', ':', 't'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['ʔ', 'l', 'ó', 't'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩, ⟨['ʔ', '-', 'í', ':', 'g', 'i', '-', 'y', 'i', '-', 'š', '-', 'g', 'i'], ['3', '-', 's', 'e', 'e', '-', 'I', 'N', 'D', '-', 'D', 'S', '-', 'G', 'I'], [⟨['ʔ'], ['3'], none⟩, ⟨['í', 'g', 'i'], ['s', 'e', 'e'], some '-'⟩, ⟨['y', 'i'], ['I', 'N', 'D'], some '-'⟩, ⟨['š'], ['D', 'S'], some '-'⟩, ⟨['g', 'i'], ['G', 'I'], some '-'⟩]⟩, ⟨['ʔ', 'w', 'á', 'ʔ'], ['h', 'e', 'r', 'e'], [⟨['ʔ', 'w', 'á', 'ʔ'], ['h', 'e', 'r', 'e'], none⟩]⟩, ⟨['ʔ', '-', 'é', 'ʔ', '-', 'i'], ['3', '-', 'b', 'e', '-', 'I', 'N', 'D'], [⟨['ʔ'], ['3'], none⟩, ⟨['é', 'ʔ'], ['b', 'e'], some '-'⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("phenomenon", "internallyHeadedRelative"), ("idxForm", "gi"), ("case", "nominative")] }

def ex19 : Datum :=
  { id := "hanink2021_ex19"
    source := ⟨"hanink-2021", "(19)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "mušé:gew ʔ-lémiʔ-giš-uwaʔ-ášaʔ-aʔ"
    glossedTokens := [("mušé:gew", "bear"), ("ʔ-lémiʔ-giš-uwaʔ-ášaʔ-aʔ", "3-gather.food-DUR-hence-PROSP-DEP")]
    glossedWords := [⟨['m', 'u', 'š', 'é', ':', 'g', 'e', 'w'], ['b', 'e', 'a', 'r'], [⟨['m', 'u', 'š', 'é', 'g', 'e', 'w'], ['b', 'e', 'a', 'r'], none⟩]⟩, ⟨['ʔ', '-', 'l', 'é', 'm', 'i', 'ʔ', '-', 'g', 'i', 'š', '-', 'u', 'w', 'a', 'ʔ', '-', 'á', 'š', 'a', 'ʔ', '-', 'a', 'ʔ'], ['3', '-', 'g', 'a', 't', 'h', 'e', 'r', '.', 'f', 'o', 'o', 'd', '-', 'D', 'U', 'R', '-', 'h', 'e', 'n', 'c', 'e', '-', 'P', 'R', 'O', 'S', 'P', '-', 'D', 'E', 'P'], [⟨['ʔ'], ['3'], none⟩, ⟨['l', 'é', 'm', 'i', 'ʔ'], ['g', 'a', 't', 'h', 'e', 'r', '.', 'f', 'o', 'o', 'd'], some '-'⟩, ⟨['g', 'i', 'š'], ['D', 'U', 'R'], some '-'⟩, ⟨['u', 'w', 'a', 'ʔ'], ['h', 'e', 'n', 'c', 'e'], some '-'⟩, ⟨['á', 'š', 'a', 'ʔ'], ['P', 'R', 'O', 'S', 'P'], some '-'⟩, ⟨['a', 'ʔ'], ['D', 'E', 'P'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "First line of the story, setting the scene."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "bareNoun"), ("reading", "indefinite")] }

def ex20 : Datum :=
  { id := "hanink2021_ex20"
    source := ⟨"hanink-2021", "(20)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "dí:be wa-dášiw-i"
    glossedTokens := [("dí:be", "sun"), ("wa-dášiw-i", "STAT-shine-IND")]
    glossedWords := [⟨['d', 'í', ':', 'b', 'e'], ['s', 'u', 'n'], [⟨['d', 'í', 'b', 'e'], ['s', 'u', 'n'], none⟩]⟩, ⟨['w', 'a', '-', 'd', 'á', 'š', 'i', 'w', '-', 'i'], ['S', 'T', 'A', 'T', '-', 's', 'h', 'i', 'n', 'e', '-', 'I', 'N', 'D'], [⟨['w', 'a'], ['S', 'T', 'A', 'T'], none⟩, ⟨['d', 'á', 'š', 'i', 'w'], ['s', 'h', 'i', 'n', 'e'], some '-'⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "bareNoun"), ("reading", "unique")] }

def ex21 : Datum :=
  { id := "hanink2021_ex21"
    source := ⟨"hanink-2021", "(21)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "lák'aʔ t'é:liwhu ʔwáʔ ʔ-éʔ-i t'é:liwhu ʔ-émlu-yé:biʔ-i"
    glossedTokens := [("lák'aʔ", "one"), ("t'é:liwhu", "man"), ("ʔwáʔ", "here"), ("ʔ-éʔ-i", "3-be-IND"), ("t'é:liwhu", "man"), ("ʔ-émlu-yé:biʔ-i", "3-eat-come-IND")]
    glossedWords := [⟨['l', 'á', 'k', '\'', 'a', 'ʔ'], ['o', 'n', 'e'], [⟨['l', 'á', 'k', '\'', 'a', 'ʔ'], ['o', 'n', 'e'], none⟩]⟩, ⟨['t', '\'', 'é', ':', 'l', 'i', 'w', 'h', 'u'], ['m', 'a', 'n'], [⟨['t', '\'', 'é', 'l', 'i', 'w', 'h', 'u'], ['m', 'a', 'n'], none⟩]⟩, ⟨['ʔ', 'w', 'á', 'ʔ'], ['h', 'e', 'r', 'e'], [⟨['ʔ', 'w', 'á', 'ʔ'], ['h', 'e', 'r', 'e'], none⟩]⟩, ⟨['ʔ', '-', 'é', 'ʔ', '-', 'i'], ['3', '-', 'b', 'e', '-', 'I', 'N', 'D'], [⟨['ʔ'], ['3'], none⟩, ⟨['é', 'ʔ'], ['b', 'e'], some '-'⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩]⟩, ⟨['t', '\'', 'é', ':', 'l', 'i', 'w', 'h', 'u'], ['m', 'a', 'n'], [⟨['t', '\'', 'é', 'l', 'i', 'w', 'h', 'u'], ['m', 'a', 'n'], none⟩]⟩, ⟨['ʔ', '-', 'é', 'm', 'l', 'u', '-', 'y', 'é', ':', 'b', 'i', 'ʔ', '-', 'i'], ['3', '-', 'e', 'a', 't', '-', 'c', 'o', 'm', 'e', '-', 'I', 'N', 'D'], [⟨['ʔ'], ['3'], none⟩, ⟨['é', 'm', 'l', 'u'], ['e', 'a', 't'], some '-'⟩, ⟨['y', 'é', 'b', 'i', 'ʔ'], ['c', 'o', 'm', 'e'], some '-'⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "bareNoun"), ("reading", "anaphoric"), ("idxForm", "null")] }

def ex22 : Datum :=
  { id := "hanink2021_ex22"
    source := ⟨"hanink-2021", "(22)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "ʔlót súkuʔ l-í:gi-yi Adele gí:-saʔ súkuʔ ʔ-í:gi-yi"
    glossedTokens := [("ʔlót", "yesterday"), ("súkuʔ", "dog"), ("l-í:gi-yi", "1/3-see-IND"), ("Adele", "Adele"), ("gí:-saʔ", "3.PRO-also"), ("súkuʔ", "dog"), ("ʔ-í:gi-yi", "3/3-see-IND")]
    glossedWords := [⟨['ʔ', 'l', 'ó', 't'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['ʔ', 'l', 'ó', 't'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩, ⟨['s', 'ú', 'k', 'u', 'ʔ'], ['d', 'o', 'g'], [⟨['s', 'ú', 'k', 'u', 'ʔ'], ['d', 'o', 'g'], none⟩]⟩, ⟨['l', '-', 'í', ':', 'g', 'i', '-', 'y', 'i'], ['1', '/', '3', '-', 's', 'e', 'e', '-', 'I', 'N', 'D'], [⟨['l'], ['1', '/', '3'], none⟩, ⟨['í', 'g', 'i'], ['s', 'e', 'e'], some '-'⟩, ⟨['y', 'i'], ['I', 'N', 'D'], some '-'⟩]⟩, ⟨['A', 'd', 'e', 'l', 'e'], ['A', 'd', 'e', 'l', 'e'], [⟨['A', 'd', 'e', 'l', 'e'], ['A', 'd', 'e', 'l', 'e'], none⟩]⟩, ⟨['g', 'í', ':', '-', 's', 'a', 'ʔ'], ['3', '.', 'P', 'R', 'O', '-', 'a', 'l', 's', 'o'], [⟨['g', 'í'], ['3', '.', 'P', 'R', 'O'], none⟩, ⟨['s', 'a', 'ʔ'], ['a', 'l', 's', 'o'], some '-'⟩]⟩, ⟨['s', 'ú', 'k', 'u', 'ʔ'], ['d', 'o', 'g'], [⟨['s', 'ú', 'k', 'u', 'ʔ'], ['d', 'o', 'g'], none⟩]⟩, ⟨['ʔ', '-', 'í', ':', 'g', 'i', '-', 'y', 'i'], ['3', '/', '3', '-', 's', 'e', 'e', '-', 'I', 'N', 'D'], [⟨['ʔ'], ['3', '/', '3'], none⟩, ⟨['í', 'g', 'i'], ['s', 'e', 'e'], some '-'⟩, ⟨['y', 'i'], ['I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "bareNoun"), ("reading", "anaphoric"), ("idxForm", "null"), ("case", "accusative")] }

def ex23 : Datum :=
  { id := "hanink2021_ex23"
    source := ⟨"hanink-2021", "(23)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "hádigi daláʔak behéziŋ k'-éʔ-i"
    glossedTokens := [("hádigi", "that"), ("daláʔak", "mountain"), ("behéziŋ", "small"), ("k'-éʔ-i", "3-be-IND")]
    glossedWords := [⟨['h', 'á', 'd', 'i', 'g', 'i'], ['t', 'h', 'a', 't'], [⟨['h', 'á', 'd', 'i', 'g', 'i'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['d', 'a', 'l', 'á', 'ʔ', 'a', 'k'], ['m', 'o', 'u', 'n', 't', 'a', 'i', 'n'], [⟨['d', 'a', 'l', 'á', 'ʔ', 'a', 'k'], ['m', 'o', 'u', 'n', 't', 'a', 'i', 'n'], none⟩]⟩, ⟨['b', 'e', 'h', 'é', 'z', 'i', 'ŋ'], ['s', 'm', 'a', 'l', 'l'], [⟨['b', 'e', 'h', 'é', 'z', 'i', 'ŋ'], ['s', 'm', 'a', 'l', 'l'], none⟩]⟩, ⟨['k', '\'', '-', 'é', 'ʔ', '-', 'i'], ['3', '-', 'b', 'e', '-', 'I', 'N', 'D'], [⟨['k', '\''], ['3'], none⟩, ⟨['é', 'ʔ'], ['b', 'e'], some '-'⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Pointing at the mountain."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "demonstrative")] }

def ex25a : Datum :=
  { id := "hanink2021_ex25a"
    source := ⟨"hanink-2021", "(25a)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "hádi-gi pélew Mú:biʔ-i"
    glossedTokens := [("hádi-gi", "DIST-GI"), ("pélew", "jackrabbit"), ("Mú:biʔ-i", "3.come.running-IND")]
    glossedWords := [⟨['h', 'á', 'd', 'i', '-', 'g', 'i'], ['D', 'I', 'S', 'T', '-', 'G', 'I'], [⟨['h', 'á', 'd', 'i'], ['D', 'I', 'S', 'T'], none⟩, ⟨['g', 'i'], ['G', 'I'], some '-'⟩]⟩, ⟨['p', 'é', 'l', 'e', 'w'], ['j', 'a', 'c', 'k', 'r', 'a', 'b', 'b', 'i', 't'], [⟨['p', 'é', 'l', 'e', 'w'], ['j', 'a', 'c', 'k', 'r', 'a', 'b', 'b', 'i', 't'], none⟩]⟩, ⟨['M', 'ú', ':', 'b', 'i', 'ʔ', '-', 'i'], ['3', '.', 'c', 'o', 'm', 'e', '.', 'r', 'u', 'n', 'n', 'i', 'n', 'g', '-', 'I', 'N', 'D'], [⟨['M', 'ú', 'b', 'i', 'ʔ'], ['3', '.', 'c', 'o', 'm', 'e', '.', 'r', 'u', 'n', 'n', 'i', 'n', 'g'], none⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "demonstrative"), ("deixis", "distal")] }

def ex25b : Datum :=
  { id := "hanink2021_ex25b"
    source := ⟨"hanink-2021", "(25b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "wídi-gi pélew Mú:biʔ-i"
    glossedTokens := [("wídi-gi", "PROX-GI"), ("pélew", "jackrabbit"), ("Mú:biʔ-i", "3.come.running-IND")]
    glossedWords := [⟨['w', 'í', 'd', 'i', '-', 'g', 'i'], ['P', 'R', 'O', 'X', '-', 'G', 'I'], [⟨['w', 'í', 'd', 'i'], ['P', 'R', 'O', 'X'], none⟩, ⟨['g', 'i'], ['G', 'I'], some '-'⟩]⟩, ⟨['p', 'é', 'l', 'e', 'w'], ['j', 'a', 'c', 'k', 'r', 'a', 'b', 'b', 'i', 't'], [⟨['p', 'é', 'l', 'e', 'w'], ['j', 'a', 'c', 'k', 'r', 'a', 'b', 'b', 'i', 't'], none⟩]⟩, ⟨['M', 'ú', ':', 'b', 'i', 'ʔ', '-', 'i'], ['3', '.', 'c', 'o', 'm', 'e', '.', 'r', 'u', 'n', 'n', 'i', 'n', 'g', '-', 'I', 'N', 'D'], [⟨['M', 'ú', 'b', 'i', 'ʔ'], ['3', '.', 'c', 'o', 'm', 'e', '.', 'r', 'u', 'n', 'n', 'i', 'n', 'g'], none⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "demonstrative"), ("deixis", "proximal")] }

def ex27 : Datum :=
  { id := "hanink2021_ex27"
    source := ⟨"hanink-2021", "(27)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "Eddy ʔwáʔ ʔ-éʔ-é:s-i ʔi-š-ŋa gé: l-í:gi k'-éʔ-i"
    glossedTokens := [("Eddy", "Eddy"), ("ʔwáʔ", "here"), ("ʔ-éʔ-é:s-i", "3-be-NEG-IND"), ("ʔi-š-ŋa", "IND-DS-but"), ("gé:", "3.ACC"), ("l-í:gi", "1/3-see"), ("k'-éʔ-i", "3-be-IND")]
    glossedWords := [⟨['E', 'd', 'd', 'y'], ['E', 'd', 'd', 'y'], [⟨['E', 'd', 'd', 'y'], ['E', 'd', 'd', 'y'], none⟩]⟩, ⟨['ʔ', 'w', 'á', 'ʔ'], ['h', 'e', 'r', 'e'], [⟨['ʔ', 'w', 'á', 'ʔ'], ['h', 'e', 'r', 'e'], none⟩]⟩, ⟨['ʔ', '-', 'é', 'ʔ', '-', 'é', ':', 's', '-', 'i'], ['3', '-', 'b', 'e', '-', 'N', 'E', 'G', '-', 'I', 'N', 'D'], [⟨['ʔ'], ['3'], none⟩, ⟨['é', 'ʔ'], ['b', 'e'], some '-'⟩, ⟨['é', 's'], ['N', 'E', 'G'], some '-'⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩]⟩, ⟨['ʔ', 'i', '-', 'š', '-', 'ŋ', 'a'], ['I', 'N', 'D', '-', 'D', 'S', '-', 'b', 'u', 't'], [⟨['ʔ', 'i'], ['I', 'N', 'D'], none⟩, ⟨['š'], ['D', 'S'], some '-'⟩, ⟨['ŋ', 'a'], ['b', 'u', 't'], some '-'⟩]⟩, ⟨['g', 'é', ':'], ['3', '.', 'A', 'C', 'C'], [⟨['g', 'é'], ['3', '.', 'A', 'C', 'C'], none⟩]⟩, ⟨['l', '-', 'í', ':', 'g', 'i'], ['1', '/', '3', '-', 's', 'e', 'e'], [⟨['l'], ['1', '/', '3'], none⟩, ⟨['í', 'g', 'i'], ['s', 'e', 'e'], some '-'⟩]⟩, ⟨['k', '\'', '-', 'é', 'ʔ', '-', 'i'], ['3', '-', 'b', 'e', '-', 'I', 'N', 'D'], [⟨['k', '\''], ['3'], none⟩, ⟨['é', 'ʔ'], ['b', 'e'], some '-'⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "pronoun"), ("idxForm", "ge"), ("case", "accusative")] }

def ex41 : Datum :=
  { id := "hanink2021_ex41"
    source := ⟨"hanink-2021", "(41)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "dáwligaŋa m-í:gi-aʔy-i-š-ge lé:-saʔ l-í:gi-yi"
    glossedTokens := [("dáwligaŋa", "movie"), ("m-í:gi-aʔy-i-š-ge", "2/3-see-INT.PST-IND-DS-IDX.ACC"), ("lé:-saʔ", "1.PRO-also"), ("l-í:gi-yi", "1/3-see-IND")]
    glossedWords := [⟨['d', 'á', 'w', 'l', 'i', 'g', 'a', 'ŋ', 'a'], ['m', 'o', 'v', 'i', 'e'], [⟨['d', 'á', 'w', 'l', 'i', 'g', 'a', 'ŋ', 'a'], ['m', 'o', 'v', 'i', 'e'], none⟩]⟩, ⟨['m', '-', 'í', ':', 'g', 'i', '-', 'a', 'ʔ', 'y', '-', 'i', '-', 'š', '-', 'g', 'e'], ['2', '/', '3', '-', 's', 'e', 'e', '-', 'I', 'N', 'T', '.', 'P', 'S', 'T', '-', 'I', 'N', 'D', '-', 'D', 'S', '-', 'I', 'D', 'X', '.', 'A', 'C', 'C'], [⟨['m'], ['2', '/', '3'], none⟩, ⟨['í', 'g', 'i'], ['s', 'e', 'e'], some '-'⟩, ⟨['a', 'ʔ', 'y'], ['I', 'N', 'T', '.', 'P', 'S', 'T'], some '-'⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩, ⟨['š'], ['D', 'S'], some '-'⟩, ⟨['g', 'e'], ['I', 'D', 'X', '.', 'A', 'C', 'C'], some '-'⟩]⟩, ⟨['l', 'é', ':', '-', 's', 'a', 'ʔ'], ['1', '.', 'P', 'R', 'O', '-', 'a', 'l', 's', 'o'], [⟨['l', 'é'], ['1', '.', 'P', 'R', 'O'], none⟩, ⟨['s', 'a', 'ʔ'], ['a', 'l', 's', 'o'], some '-'⟩]⟩, ⟨['l', '-', 'í', ':', 'g', 'i', '-', 'y', 'i'], ['1', '/', '3', '-', 's', 'e', 'e', '-', 'I', 'N', 'D'], [⟨['l'], ['1', '/', '3'], none⟩, ⟨['í', 'g', 'i'], ['s', 'e', 'e'], some '-'⟩, ⟨['y', 'i'], ['I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("phenomenon", "internallyHeadedRelative"), ("idxForm", "ge"), ("case", "accusative")] }

def ex45 : Datum :=
  { id := "hanink2021_ex45"
    source := ⟨"hanink-2021", "(45)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "mé:hu géwe ʔ-í:gi-yi-š-ge lé:-saʔ l-í:gi-yi"
    glossedTokens := [("mé:hu", "boy"), ("géwe", "coyote"), ("ʔ-í:gi-yi-š-ge", "3-see-IND-DS-IDX.ACC"), ("lé:-saʔ", "1.PRO-also"), ("l-í:gi-yi", "1-see-IND")]
    glossedWords := [⟨['m', 'é', ':', 'h', 'u'], ['b', 'o', 'y'], [⟨['m', 'é', 'h', 'u'], ['b', 'o', 'y'], none⟩]⟩, ⟨['g', 'é', 'w', 'e'], ['c', 'o', 'y', 'o', 't', 'e'], [⟨['g', 'é', 'w', 'e'], ['c', 'o', 'y', 'o', 't', 'e'], none⟩]⟩, ⟨['ʔ', '-', 'í', ':', 'g', 'i', '-', 'y', 'i', '-', 'š', '-', 'g', 'e'], ['3', '-', 's', 'e', 'e', '-', 'I', 'N', 'D', '-', 'D', 'S', '-', 'I', 'D', 'X', '.', 'A', 'C', 'C'], [⟨['ʔ'], ['3'], none⟩, ⟨['í', 'g', 'i'], ['s', 'e', 'e'], some '-'⟩, ⟨['y', 'i'], ['I', 'N', 'D'], some '-'⟩, ⟨['š'], ['D', 'S'], some '-'⟩, ⟨['g', 'e'], ['I', 'D', 'X', '.', 'A', 'C', 'C'], some '-'⟩]⟩, ⟨['l', 'é', ':', '-', 's', 'a', 'ʔ'], ['1', '.', 'P', 'R', 'O', '-', 'a', 'l', 's', 'o'], [⟨['l', 'é'], ['1', '.', 'P', 'R', 'O'], none⟩, ⟨['s', 'a', 'ʔ'], ['a', 'l', 's', 'o'], some '-'⟩]⟩, ⟨['l', '-', 'í', ':', 'g', 'i', '-', 'y', 'i'], ['1', '-', 's', 'e', 'e', '-', 'I', 'N', 'D'], [⟨['l'], ['1'], none⟩, ⟨['í', 'g', 'i'], ['s', 'e', 'e'], some '-'⟩, ⟨['y', 'i'], ['I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("phenomenon", "internallyHeadedRelative"), ("idxForm", "ge"), ("case", "accusative")] }

def ex46 : Datum :=
  { id := "hanink2021_ex46"
    source := ⟨"hanink-2021", "(46)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "di-tulíc'ik-lu di-gum-c'í:ge-yi"
    glossedTokens := [("di-tulíc'ik-lu", "1-finger-INST"), ("di-gum-c'í:ge-yi", "1-REFL-scratch-IND")]
    glossedWords := [⟨['d', 'i', '-', 't', 'u', 'l', 'í', 'c', '\'', 'i', 'k', '-', 'l', 'u'], ['1', '-', 'f', 'i', 'n', 'g', 'e', 'r', '-', 'I', 'N', 'S', 'T'], [⟨['d', 'i'], ['1'], none⟩, ⟨['t', 'u', 'l', 'í', 'c', '\'', 'i', 'k'], ['f', 'i', 'n', 'g', 'e', 'r'], some '-'⟩, ⟨['l', 'u'], ['I', 'N', 'S', 'T'], some '-'⟩]⟩, ⟨['d', 'i', '-', 'g', 'u', 'm', '-', 'c', '\'', 'í', ':', 'g', 'e', '-', 'y', 'i'], ['1', '-', 'R', 'E', 'F', 'L', '-', 's', 'c', 'r', 'a', 't', 'c', 'h', '-', 'I', 'N', 'D'], [⟨['d', 'i'], ['1'], none⟩, ⟨['g', 'u', 'm'], ['R', 'E', 'F', 'L'], some '-'⟩, ⟨['c', '\'', 'í', 'g', 'e'], ['s', 'c', 'r', 'a', 't', 'c', 'h'], some '-'⟩, ⟨['y', 'i'], ['I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("phenomenon", "postposition")] }

def ex47 : Datum :=
  { id := "hanink2021_ex47"
    source := ⟨"hanink-2021", "(47)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "gó:beʔ l-émeʔ-áŋaw-i-∅-ge-lu di-p'ím-eweʔ-giš-i"
    glossedTokens := [("gó:beʔ", "coffee"), ("l-émeʔ-áŋaw-i-∅-ge-lu", "1-drink-well-IND-SS-IDX.ACC-INST"), ("di-p'ím-eweʔ-giš-i", "1-go.out-hence-DUR-IND")]
    glossedWords := [⟨['g', 'ó', ':', 'b', 'e', 'ʔ'], ['c', 'o', 'f', 'f', 'e', 'e'], [⟨['g', 'ó', 'b', 'e', 'ʔ'], ['c', 'o', 'f', 'f', 'e', 'e'], none⟩]⟩, ⟨['l', '-', 'é', 'm', 'e', 'ʔ', '-', 'á', 'ŋ', 'a', 'w', '-', 'i', '-', '∅', '-', 'g', 'e', '-', 'l', 'u'], ['1', '-', 'd', 'r', 'i', 'n', 'k', '-', 'w', 'e', 'l', 'l', '-', 'I', 'N', 'D', '-', 'S', 'S', '-', 'I', 'D', 'X', '.', 'A', 'C', 'C', '-', 'I', 'N', 'S', 'T'], [⟨['l'], ['1'], none⟩, ⟨['é', 'm', 'e', 'ʔ'], ['d', 'r', 'i', 'n', 'k'], some '-'⟩, ⟨['á', 'ŋ', 'a', 'w'], ['w', 'e', 'l', 'l'], some '-'⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩, ⟨['∅'], ['S', 'S'], some '-'⟩, ⟨['g', 'e'], ['I', 'D', 'X', '.', 'A', 'C', 'C'], some '-'⟩, ⟨['l', 'u'], ['I', 'N', 'S', 'T'], some '-'⟩]⟩, ⟨['d', 'i', '-', 'p', '\'', 'í', 'm', '-', 'e', 'w', 'e', 'ʔ', '-', 'g', 'i', 'š', '-', 'i'], ['1', '-', 'g', 'o', '.', 'o', 'u', 't', '-', 'h', 'e', 'n', 'c', 'e', '-', 'D', 'U', 'R', '-', 'I', 'N', 'D'], [⟨['d', 'i'], ['1'], none⟩, ⟨['p', '\'', 'í', 'm'], ['g', 'o', '.', 'o', 'u', 't'], some '-'⟩, ⟨['e', 'w', 'e', 'ʔ'], ['h', 'e', 'n', 'c', 'e'], some '-'⟩, ⟨['g', 'i', 'š'], ['D', 'U', 'R'], some '-'⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("phenomenon", "postposition"), ("idxForm", "ge")] }

def ex50 : Datum :=
  { id := "hanink2021_ex50"
    source := ⟨"hanink-2021", "(50)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "t'ánu démlu sú:biʔ-i-š-ge di-sú:dɨm-i-š-gi wayúʔuš-áŋaw-i"
    glossedTokens := [("t'ánu", "people"), ("démlu", "food"), ("sú:biʔ-i-š-ge", "3/3.bring-IND-DS-IDX.ACC"), ("di-sú:dɨm-i-š-gi", "1/3-look.at-IND-DS-IDX.NOM"), ("wayúʔuš-áŋaw-i", "3.smell-good-IND")]
    glossedWords := [⟨['t', '\'', 'á', 'n', 'u'], ['p', 'e', 'o', 'p', 'l', 'e'], [⟨['t', '\'', 'á', 'n', 'u'], ['p', 'e', 'o', 'p', 'l', 'e'], none⟩]⟩, ⟨['d', 'é', 'm', 'l', 'u'], ['f', 'o', 'o', 'd'], [⟨['d', 'é', 'm', 'l', 'u'], ['f', 'o', 'o', 'd'], none⟩]⟩, ⟨['s', 'ú', ':', 'b', 'i', 'ʔ', '-', 'i', '-', 'š', '-', 'g', 'e'], ['3', '/', '3', '.', 'b', 'r', 'i', 'n', 'g', '-', 'I', 'N', 'D', '-', 'D', 'S', '-', 'I', 'D', 'X', '.', 'A', 'C', 'C'], [⟨['s', 'ú', 'b', 'i', 'ʔ'], ['3', '/', '3', '.', 'b', 'r', 'i', 'n', 'g'], none⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩, ⟨['š'], ['D', 'S'], some '-'⟩, ⟨['g', 'e'], ['I', 'D', 'X', '.', 'A', 'C', 'C'], some '-'⟩]⟩, ⟨['d', 'i', '-', 's', 'ú', ':', 'd', 'ɨ', 'm', '-', 'i', '-', 'š', '-', 'g', 'i'], ['1', '/', '3', '-', 'l', 'o', 'o', 'k', '.', 'a', 't', '-', 'I', 'N', 'D', '-', 'D', 'S', '-', 'I', 'D', 'X', '.', 'N', 'O', 'M'], [⟨['d', 'i'], ['1', '/', '3'], none⟩, ⟨['s', 'ú', 'd', 'ɨ', 'm'], ['l', 'o', 'o', 'k', '.', 'a', 't'], some '-'⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩, ⟨['š'], ['D', 'S'], some '-'⟩, ⟨['g', 'i'], ['I', 'D', 'X', '.', 'N', 'O', 'M'], some '-'⟩]⟩, ⟨['w', 'a', 'y', 'ú', 'ʔ', 'u', 'š', '-', 'á', 'ŋ', 'a', 'w', '-', 'i'], ['3', '.', 's', 'm', 'e', 'l', 'l', '-', 'g', 'o', 'o', 'd', '-', 'I', 'N', 'D'], [⟨['w', 'a', 'y', 'ú', 'ʔ', 'u', 'š'], ['3', '.', 's', 'm', 'e', 'l', 'l'], none⟩, ⟨['á', 'ŋ', 'a', 'w'], ['g', 'o', 'o', 'd'], some '-'⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("phenomenon", "islandInsensitivity")] }

def ex51 : Datum :=
  { id := "hanink2021_ex51"
    source := ⟨"hanink-2021", "(51)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "daʔmóʔmoʔ gó:beʔ ʔ-ímeʔ-i-š-ge l-í:gi-yi-∅-ge lé:-saʔ l-émeʔ-ašaʔ-i"
    glossedTokens := [("daʔmóʔmoʔ", "woman"), ("gó:beʔ", "coffee"), ("ʔ-ímeʔ-i-š-ge", "drink-IND-DS-IDX.ACC"), ("l-í:gi-yi-∅-ge", "1/3-see-IND-SS-IDX.ACC"), ("lé:-saʔ", "1.PRO-also"), ("l-émeʔ-ašaʔ-i", "1/3-drink-PROSP-IND")]
    glossedWords := [⟨['d', 'a', 'ʔ', 'm', 'ó', 'ʔ', 'm', 'o', 'ʔ'], ['w', 'o', 'm', 'a', 'n'], [⟨['d', 'a', 'ʔ', 'm', 'ó', 'ʔ', 'm', 'o', 'ʔ'], ['w', 'o', 'm', 'a', 'n'], none⟩]⟩, ⟨['g', 'ó', ':', 'b', 'e', 'ʔ'], ['c', 'o', 'f', 'f', 'e', 'e'], [⟨['g', 'ó', 'b', 'e', 'ʔ'], ['c', 'o', 'f', 'f', 'e', 'e'], none⟩]⟩, ⟨['ʔ', '-', 'í', 'm', 'e', 'ʔ', '-', 'i', '-', 'š', '-', 'g', 'e'], ['d', 'r', 'i', 'n', 'k', '-', 'I', 'N', 'D', '-', 'D', 'S', '-', 'I', 'D', 'X', '.', 'A', 'C', 'C'], []⟩, ⟨['l', '-', 'í', ':', 'g', 'i', '-', 'y', 'i', '-', '∅', '-', 'g', 'e'], ['1', '/', '3', '-', 's', 'e', 'e', '-', 'I', 'N', 'D', '-', 'S', 'S', '-', 'I', 'D', 'X', '.', 'A', 'C', 'C'], [⟨['l'], ['1', '/', '3'], none⟩, ⟨['í', 'g', 'i'], ['s', 'e', 'e'], some '-'⟩, ⟨['y', 'i'], ['I', 'N', 'D'], some '-'⟩, ⟨['∅'], ['S', 'S'], some '-'⟩, ⟨['g', 'e'], ['I', 'D', 'X', '.', 'A', 'C', 'C'], some '-'⟩]⟩, ⟨['l', 'é', ':', '-', 's', 'a', 'ʔ'], ['1', '.', 'P', 'R', 'O', '-', 'a', 'l', 's', 'o'], [⟨['l', 'é'], ['1', '.', 'P', 'R', 'O'], none⟩, ⟨['s', 'a', 'ʔ'], ['a', 'l', 's', 'o'], some '-'⟩]⟩, ⟨['l', '-', 'é', 'm', 'e', 'ʔ', '-', 'a', 'š', 'a', 'ʔ', '-', 'i'], ['1', '/', '3', '-', 'd', 'r', 'i', 'n', 'k', '-', 'P', 'R', 'O', 'S', 'P', '-', 'I', 'N', 'D'], [⟨['l'], ['1', '/', '3'], none⟩, ⟨['é', 'm', 'e', 'ʔ'], ['d', 'r', 'i', 'n', 'k'], some '-'⟩, ⟨['a', 'š', 'a', 'ʔ'], ['P', 'R', 'O', 'S', 'P'], some '-'⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("phenomenon", "islandInsensitivity")] }

def ex53 : Datum :=
  { id := "hanink2021_ex53"
    source := ⟨"hanink-2021", "(53)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "k'ák'aʔ dá: gé:gel-i-š-ge yá:m-aʔ"
    glossedTokens := [("k'ák'aʔ", "heron"), ("dá:", "there"), ("gé:gel-i-š-ge", "3.sit-IND-DS-IDX.ACC"), ("yá:m-aʔ", "3/3.speak-DEP")]
    glossedWords := [⟨['k', '\'', 'á', 'k', '\'', 'a', 'ʔ'], ['h', 'e', 'r', 'o', 'n'], [⟨['k', '\'', 'á', 'k', '\'', 'a', 'ʔ'], ['h', 'e', 'r', 'o', 'n'], none⟩]⟩, ⟨['d', 'á', ':'], ['t', 'h', 'e', 'r', 'e'], [⟨['d', 'á'], ['t', 'h', 'e', 'r', 'e'], none⟩]⟩, ⟨['g', 'é', ':', 'g', 'e', 'l', '-', 'i', '-', 'š', '-', 'g', 'e'], ['3', '.', 's', 'i', 't', '-', 'I', 'N', 'D', '-', 'D', 'S', '-', 'I', 'D', 'X', '.', 'A', 'C', 'C'], [⟨['g', 'é', 'g', 'e', 'l'], ['3', '.', 's', 'i', 't'], none⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩, ⟨['š'], ['D', 'S'], some '-'⟩, ⟨['g', 'e'], ['I', 'D', 'X', '.', 'A', 'C', 'C'], some '-'⟩]⟩, ⟨['y', 'á', ':', 'm', '-', 'a', 'ʔ'], ['3', '/', '3', '.', 's', 'p', 'e', 'a', 'k', '-', 'D', 'E', 'P'], [⟨['y', 'á', 'm'], ['3', '/', '3', '.', 's', 'p', 'e', 'a', 'k'], none⟩, ⟨['a', 'ʔ'], ['D', 'E', 'P'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "A bear is looking for her cubs, and comes to a river."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("phenomenon", "restrictiveness"), ("reading", "existential")] }

def ex54 : Datum :=
  { id := "hanink2021_ex54"
    source := ⟨"hanink-2021", "(54)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "súkuʔ baŋáya ʔ-éʔ-i-š-ge daʔmóʔmoʔ bóŋi-yi-š-gi p'á:š-ug-i"
    glossedTokens := [("súkuʔ", "dog"), ("baŋáya", "outside"), ("ʔ-éʔ-i-š-ge", "3-be-IND-DS-IDX.ACC"), ("daʔmóʔmoʔ", "woman"), ("bóŋi-yi-š-gi", "3/3.call-IND-DS-IDX.NOM"), ("p'á:š-ug-i", "3.enter-hither-IND")]
    glossedWords := [⟨['s', 'ú', 'k', 'u', 'ʔ'], ['d', 'o', 'g'], [⟨['s', 'ú', 'k', 'u', 'ʔ'], ['d', 'o', 'g'], none⟩]⟩, ⟨['b', 'a', 'ŋ', 'á', 'y', 'a'], ['o', 'u', 't', 's', 'i', 'd', 'e'], [⟨['b', 'a', 'ŋ', 'á', 'y', 'a'], ['o', 'u', 't', 's', 'i', 'd', 'e'], none⟩]⟩, ⟨['ʔ', '-', 'é', 'ʔ', '-', 'i', '-', 'š', '-', 'g', 'e'], ['3', '-', 'b', 'e', '-', 'I', 'N', 'D', '-', 'D', 'S', '-', 'I', 'D', 'X', '.', 'A', 'C', 'C'], [⟨['ʔ'], ['3'], none⟩, ⟨['é', 'ʔ'], ['b', 'e'], some '-'⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩, ⟨['š'], ['D', 'S'], some '-'⟩, ⟨['g', 'e'], ['I', 'D', 'X', '.', 'A', 'C', 'C'], some '-'⟩]⟩, ⟨['d', 'a', 'ʔ', 'm', 'ó', 'ʔ', 'm', 'o', 'ʔ'], ['w', 'o', 'm', 'a', 'n'], [⟨['d', 'a', 'ʔ', 'm', 'ó', 'ʔ', 'm', 'o', 'ʔ'], ['w', 'o', 'm', 'a', 'n'], none⟩]⟩, ⟨['b', 'ó', 'ŋ', 'i', '-', 'y', 'i', '-', 'š', '-', 'g', 'i'], ['3', '/', '3', '.', 'c', 'a', 'l', 'l', '-', 'I', 'N', 'D', '-', 'D', 'S', '-', 'I', 'D', 'X', '.', 'N', 'O', 'M'], [⟨['b', 'ó', 'ŋ', 'i'], ['3', '/', '3', '.', 'c', 'a', 'l', 'l'], none⟩, ⟨['y', 'i'], ['I', 'N', 'D'], some '-'⟩, ⟨['š'], ['D', 'S'], some '-'⟩, ⟨['g', 'i'], ['I', 'D', 'X', '.', 'N', 'O', 'M'], some '-'⟩]⟩, ⟨['p', '\'', 'á', ':', 'š', '-', 'u', 'g', '-', 'i'], ['3', '.', 'e', 'n', 't', 'e', 'r', '-', 'h', 'i', 't', 'h', 'e', 'r', '-', 'I', 'N', 'D'], [⟨['p', '\'', 'á', 'š'], ['3', '.', 'e', 'n', 't', 'e', 'r'], none⟩, ⟨['u', 'g'], ['h', 'i', 't', 'h', 'e', 'r'], some '-'⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("phenomenon", "restrictiveness")] }

def ex56 : Datum :=
  { id := "hanink2021_ex56"
    source := ⟨"hanink-2021", "(56)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "Adele gawá:yɨʔ gaʔlám-i-š-gi Múʔuš-úweʔ-i"
    glossedTokens := [("Adele", "Adele"), ("gawá:yɨʔ", "horse"), ("gaʔlám-i-š-gi", "3/3.like-IND-DS-IDX.NOM"), ("Múʔuš-úweʔ-i", "3.run-hence-IND")]
    glossedWords := [⟨['A', 'd', 'e', 'l', 'e'], ['A', 'd', 'e', 'l', 'e'], [⟨['A', 'd', 'e', 'l', 'e'], ['A', 'd', 'e', 'l', 'e'], none⟩]⟩, ⟨['g', 'a', 'w', 'á', ':', 'y', 'ɨ', 'ʔ'], ['h', 'o', 'r', 's', 'e'], [⟨['g', 'a', 'w', 'á', 'y', 'ɨ', 'ʔ'], ['h', 'o', 'r', 's', 'e'], none⟩]⟩, ⟨['g', 'a', 'ʔ', 'l', 'á', 'm', '-', 'i', '-', 'š', '-', 'g', 'i'], ['3', '/', '3', '.', 'l', 'i', 'k', 'e', '-', 'I', 'N', 'D', '-', 'D', 'S', '-', 'I', 'D', 'X', '.', 'N', 'O', 'M'], [⟨['g', 'a', 'ʔ', 'l', 'á', 'm'], ['3', '/', '3', '.', 'l', 'i', 'k', 'e'], none⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩, ⟨['š'], ['D', 'S'], some '-'⟩, ⟨['g', 'i'], ['I', 'D', 'X', '.', 'N', 'O', 'M'], some '-'⟩]⟩, ⟨['M', 'ú', 'ʔ', 'u', 'š', '-', 'ú', 'w', 'e', 'ʔ', '-', 'i'], ['3', '.', 'r', 'u', 'n', '-', 'h', 'e', 'n', 'c', 'e', '-', 'I', 'N', 'D'], [⟨['M', 'ú', 'ʔ', 'u', 'š'], ['3', '.', 'r', 'u', 'n'], none⟩, ⟨['ú', 'w', 'e', 'ʔ'], ['h', 'e', 'n', 'c', 'e'], some '-'⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "You ask what is going on. Someone responds."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.1"), ("phenomenon", "internallyHeadedRelative")] }

def ex91 : Datum :=
  { id := "hanink2021_ex91"
    source := ⟨"hanink-2021", "(91)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "daʔmoʔmóʔmoʔ p'á:š-ug-i-š-ge di-sú:dɨm-i"
    glossedTokens := [("daʔmoʔmóʔmoʔ", "woman.R"), ("p'á:š-ug-i-š-ge", "3.enter-hither-IND-DS-IDX.ACC"), ("di-sú:dɨm-i", "1/3-look.at-IND")]
    glossedWords := [⟨['d', 'a', 'ʔ', 'm', 'o', 'ʔ', 'm', 'ó', 'ʔ', 'm', 'o', 'ʔ'], ['w', 'o', 'm', 'a', 'n', '.', 'R'], [⟨['d', 'a', 'ʔ', 'm', 'o', 'ʔ', 'm', 'ó', 'ʔ', 'm', 'o', 'ʔ'], ['w', 'o', 'm', 'a', 'n', '.', 'R'], none⟩]⟩, ⟨['p', '\'', 'á', ':', 'š', '-', 'u', 'g', '-', 'i', '-', 'š', '-', 'g', 'e'], ['3', '.', 'e', 'n', 't', 'e', 'r', '-', 'h', 'i', 't', 'h', 'e', 'r', '-', 'I', 'N', 'D', '-', 'D', 'S', '-', 'I', 'D', 'X', '.', 'A', 'C', 'C'], [⟨['p', '\'', 'á', 'š'], ['3', '.', 'e', 'n', 't', 'e', 'r'], none⟩, ⟨['u', 'g'], ['h', 'i', 't', 'h', 'e', 'r'], some '-'⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩, ⟨['š'], ['D', 'S'], some '-'⟩, ⟨['g', 'e'], ['I', 'D', 'X', '.', 'A', 'C', 'C'], some '-'⟩]⟩, ⟨['d', 'i', '-', 's', 'ú', ':', 'd', 'ɨ', 'm', '-', 'i'], ['1', '/', '3', '-', 'l', 'o', 'o', 'k', '.', 'a', 't', '-', 'I', 'N', 'D'], [⟨['d', 'i'], ['1', '/', '3'], none⟩, ⟨['s', 'ú', 'd', 'ɨ', 'm'], ['l', 'o', 'o', 'k', '.', 'a', 't'], some '-'⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("daʔmoʔmóʔmoʔ p'á:š-ug-i-š-ge-w di-sú:dɨm-i", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "4.5"), ("phenomenon", "noFeatureTransmission")] }

def ex96 : Datum :=
  { id := "hanink2021_ex96"
    source := ⟨"hanink-2021", "(96)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "ʔló:t Adele hádi-gi mé:hu ʔ-í:gi-yi-š-gi ʔwáʔ ʔ-éʔ-i"
    glossedTokens := [("ʔló:t", "yesterday"), ("Adele", "Adele"), ("hádi-gi", "DIST-IDX.NOM"), ("mé:hu", "boy"), ("ʔ-í:gi-yi-š-gi", "3/3-see-IND-DS-IDX.NOM"), ("ʔwáʔ", "here"), ("ʔ-éʔ-i", "3-be-IND")]
    glossedWords := [⟨['ʔ', 'l', 'ó', ':', 't'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['ʔ', 'l', 'ó', 't'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩, ⟨['A', 'd', 'e', 'l', 'e'], ['A', 'd', 'e', 'l', 'e'], [⟨['A', 'd', 'e', 'l', 'e'], ['A', 'd', 'e', 'l', 'e'], none⟩]⟩, ⟨['h', 'á', 'd', 'i', '-', 'g', 'i'], ['D', 'I', 'S', 'T', '-', 'I', 'D', 'X', '.', 'N', 'O', 'M'], [⟨['h', 'á', 'd', 'i'], ['D', 'I', 'S', 'T'], none⟩, ⟨['g', 'i'], ['I', 'D', 'X', '.', 'N', 'O', 'M'], some '-'⟩]⟩, ⟨['m', 'é', ':', 'h', 'u'], ['b', 'o', 'y'], [⟨['m', 'é', 'h', 'u'], ['b', 'o', 'y'], none⟩]⟩, ⟨['ʔ', '-', 'í', ':', 'g', 'i', '-', 'y', 'i', '-', 'š', '-', 'g', 'i'], ['3', '/', '3', '-', 's', 'e', 'e', '-', 'I', 'N', 'D', '-', 'D', 'S', '-', 'I', 'D', 'X', '.', 'N', 'O', 'M'], [⟨['ʔ'], ['3', '/', '3'], none⟩, ⟨['í', 'g', 'i'], ['s', 'e', 'e'], some '-'⟩, ⟨['y', 'i'], ['I', 'N', 'D'], some '-'⟩, ⟨['š'], ['D', 'S'], some '-'⟩, ⟨['g', 'i'], ['I', 'D', 'X', '.', 'N', 'O', 'M'], some '-'⟩]⟩, ⟨['ʔ', 'w', 'á', 'ʔ'], ['h', 'e', 'r', 'e'], [⟨['ʔ', 'w', 'á', 'ʔ'], ['h', 'e', 'r', 'e'], none⟩]⟩, ⟨['ʔ', '-', 'é', 'ʔ', '-', 'i'], ['3', '-', 'b', 'e', '-', 'I', 'N', 'D'], [⟨['ʔ'], ['3'], none⟩, ⟨['é', 'ʔ'], ['b', 'e'], some '-'⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.1"), ("phenomenon", "indefinitenessRestriction")] }

def ex98 : Datum :=
  { id := "hanink2021_ex98"
    source := ⟨"hanink-2021", "(98)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "dak'uláŋaʔ míʔle-w gawá:yɨʔ baŋáya gúm-úweʔ-i-š-ge di-sú:dɨm-i"
    glossedTokens := [("dak'uláŋaʔ", "cowboy"), ("míʔle-w", "all-AN.PL"), ("gawá:yɨʔ", "horse"), ("baŋáya", "outside"), ("gúm-úweʔ-i-š-ge", "3/3.take.out-hence-IND-DS-IDX.ACC"), ("di-sú:dɨm-i", "1/3-look.at-IND")]
    glossedWords := [⟨['d', 'a', 'k', '\'', 'u', 'l', 'á', 'ŋ', 'a', 'ʔ'], ['c', 'o', 'w', 'b', 'o', 'y'], [⟨['d', 'a', 'k', '\'', 'u', 'l', 'á', 'ŋ', 'a', 'ʔ'], ['c', 'o', 'w', 'b', 'o', 'y'], none⟩]⟩, ⟨['m', 'í', 'ʔ', 'l', 'e', '-', 'w'], ['a', 'l', 'l', '-', 'A', 'N', '.', 'P', 'L'], [⟨['m', 'í', 'ʔ', 'l', 'e'], ['a', 'l', 'l'], none⟩, ⟨['w'], ['A', 'N', '.', 'P', 'L'], some '-'⟩]⟩, ⟨['g', 'a', 'w', 'á', ':', 'y', 'ɨ', 'ʔ'], ['h', 'o', 'r', 's', 'e'], [⟨['g', 'a', 'w', 'á', 'y', 'ɨ', 'ʔ'], ['h', 'o', 'r', 's', 'e'], none⟩]⟩, ⟨['b', 'a', 'ŋ', 'á', 'y', 'a'], ['o', 'u', 't', 's', 'i', 'd', 'e'], [⟨['b', 'a', 'ŋ', 'á', 'y', 'a'], ['o', 'u', 't', 's', 'i', 'd', 'e'], none⟩]⟩, ⟨['g', 'ú', 'm', '-', 'ú', 'w', 'e', 'ʔ', '-', 'i', '-', 'š', '-', 'g', 'e'], ['3', '/', '3', '.', 't', 'a', 'k', 'e', '.', 'o', 'u', 't', '-', 'h', 'e', 'n', 'c', 'e', '-', 'I', 'N', 'D', '-', 'D', 'S', '-', 'I', 'D', 'X', '.', 'A', 'C', 'C'], [⟨['g', 'ú', 'm'], ['3', '/', '3', '.', 't', 'a', 'k', 'e', '.', 'o', 'u', 't'], none⟩, ⟨['ú', 'w', 'e', 'ʔ'], ['h', 'e', 'n', 'c', 'e'], some '-'⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩, ⟨['š'], ['D', 'S'], some '-'⟩, ⟨['g', 'e'], ['I', 'D', 'X', '.', 'A', 'C', 'C'], some '-'⟩]⟩, ⟨['d', 'i', '-', 's', 'ú', ':', 'd', 'ɨ', 'm', '-', 'i'], ['1', '/', '3', '-', 'l', 'o', 'o', 'k', '.', 'a', 't', '-', 'I', 'N', 'D'], [⟨['d', 'i'], ['1', '/', '3'], none⟩, ⟨['s', 'ú', 'd', 'ɨ', 'm'], ['l', 'o', 'o', 'k', '.', 'a', 't'], some '-'⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.1"), ("phenomenon", "quantifiedHead")] }

def ex102 : Datum :=
  { id := "hanink2021_ex102"
    source := ⟨"hanink-2021", "(102)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "ʔiŋa baŋáya gawá:yɨʔ míʔle-w-ŋa gúm-úweʔ-é:s-i"
    glossedTokens := [("ʔiŋa", "but"), ("baŋáya", "outside"), ("gawá:yɨʔ", "horse"), ("míʔle-w-ŋa", "all-PL-NC"), ("gúm-úweʔ-é:s-i", "3/3.take.out-hence-NEG-IND")]
    glossedWords := [⟨['ʔ', 'i', 'ŋ', 'a'], ['b', 'u', 't'], [⟨['ʔ', 'i', 'ŋ', 'a'], ['b', 'u', 't'], none⟩]⟩, ⟨['b', 'a', 'ŋ', 'á', 'y', 'a'], ['o', 'u', 't', 's', 'i', 'd', 'e'], [⟨['b', 'a', 'ŋ', 'á', 'y', 'a'], ['o', 'u', 't', 's', 'i', 'd', 'e'], none⟩]⟩, ⟨['g', 'a', 'w', 'á', ':', 'y', 'ɨ', 'ʔ'], ['h', 'o', 'r', 's', 'e'], [⟨['g', 'a', 'w', 'á', 'y', 'ɨ', 'ʔ'], ['h', 'o', 'r', 's', 'e'], none⟩]⟩, ⟨['m', 'í', 'ʔ', 'l', 'e', '-', 'w', '-', 'ŋ', 'a'], ['a', 'l', 'l', '-', 'P', 'L', '-', 'N', 'C'], [⟨['m', 'í', 'ʔ', 'l', 'e'], ['a', 'l', 'l'], none⟩, ⟨['w'], ['P', 'L'], some '-'⟩, ⟨['ŋ', 'a'], ['N', 'C'], some '-'⟩]⟩, ⟨['g', 'ú', 'm', '-', 'ú', 'w', 'e', 'ʔ', '-', 'é', ':', 's', '-', 'i'], ['3', '/', '3', '.', 't', 'a', 'k', 'e', '.', 'o', 'u', 't', '-', 'h', 'e', 'n', 'c', 'e', '-', 'N', 'E', 'G', '-', 'I', 'N', 'D'], [⟨['g', 'ú', 'm'], ['3', '/', '3', '.', 't', 'a', 'k', 'e', '.', 'o', 'u', 't'], none⟩, ⟨['ú', 'w', 'e', 'ʔ'], ['h', 'e', 'n', 'c', 'e'], some '-'⟩, ⟨['é', 's'], ['N', 'E', 'G'], some '-'⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Uttered after (98)."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.1"), ("phenomenon", "quantifiedHead")] }

def ex103 : Datum :=
  { id := "hanink2021_ex103"
    source := ⟨"hanink-2021", "(103)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "míʔle-w dak'uláŋaʔ gawá:yɨʔ baŋáya gúm-úweʔ-i-š-ge di-sú:dɨm-i"
    glossedTokens := [("míʔle-w", "all-AN.PL"), ("dak'uláŋaʔ", "cowboy"), ("gawá:yɨʔ", "horse"), ("baŋáya", "outside"), ("gúm-úweʔ-i-š-ge", "3/3.take.out-hence-IND-DS-IDX.ACC"), ("di-sú:dɨm-i", "1/3-look.at-IND")]
    glossedWords := [⟨['m', 'í', 'ʔ', 'l', 'e', '-', 'w'], ['a', 'l', 'l', '-', 'A', 'N', '.', 'P', 'L'], [⟨['m', 'í', 'ʔ', 'l', 'e'], ['a', 'l', 'l'], none⟩, ⟨['w'], ['A', 'N', '.', 'P', 'L'], some '-'⟩]⟩, ⟨['d', 'a', 'k', '\'', 'u', 'l', 'á', 'ŋ', 'a', 'ʔ'], ['c', 'o', 'w', 'b', 'o', 'y'], [⟨['d', 'a', 'k', '\'', 'u', 'l', 'á', 'ŋ', 'a', 'ʔ'], ['c', 'o', 'w', 'b', 'o', 'y'], none⟩]⟩, ⟨['g', 'a', 'w', 'á', ':', 'y', 'ɨ', 'ʔ'], ['h', 'o', 'r', 's', 'e'], [⟨['g', 'a', 'w', 'á', 'y', 'ɨ', 'ʔ'], ['h', 'o', 'r', 's', 'e'], none⟩]⟩, ⟨['b', 'a', 'ŋ', 'á', 'y', 'a'], ['o', 'u', 't', 's', 'i', 'd', 'e'], [⟨['b', 'a', 'ŋ', 'á', 'y', 'a'], ['o', 'u', 't', 's', 'i', 'd', 'e'], none⟩]⟩, ⟨['g', 'ú', 'm', '-', 'ú', 'w', 'e', 'ʔ', '-', 'i', '-', 'š', '-', 'g', 'e'], ['3', '/', '3', '.', 't', 'a', 'k', 'e', '.', 'o', 'u', 't', '-', 'h', 'e', 'n', 'c', 'e', '-', 'I', 'N', 'D', '-', 'D', 'S', '-', 'I', 'D', 'X', '.', 'A', 'C', 'C'], [⟨['g', 'ú', 'm'], ['3', '/', '3', '.', 't', 'a', 'k', 'e', '.', 'o', 'u', 't'], none⟩, ⟨['ú', 'w', 'e', 'ʔ'], ['h', 'e', 'n', 'c', 'e'], some '-'⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩, ⟨['š'], ['D', 'S'], some '-'⟩, ⟨['g', 'e'], ['I', 'D', 'X', '.', 'A', 'C', 'C'], some '-'⟩]⟩, ⟨['d', 'i', '-', 's', 'ú', ':', 'd', 'ɨ', 'm', '-', 'i'], ['1', '/', '3', '-', 'l', 'o', 'o', 'k', '.', 'a', 't', '-', 'I', 'N', 'D'], [⟨['d', 'i'], ['1', '/', '3'], none⟩, ⟨['s', 'ú', 'd', 'ɨ', 'm'], ['l', 'o', 'o', 'k', '.', 'a', 't'], some '-'⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.1"), ("phenomenon", "quantifiedHead")] }

def ex104 : Datum :=
  { id := "hanink2021_ex104"
    source := ⟨"hanink-2021", "(104)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "ʔum-wagayáyʔ-i-š-ge di-dámal-i"
    glossedTokens := [("ʔum-wagayáyʔ-i-š-ge", "2-talk-IND-DS-IDX.ACC"), ("di-dámal-i", "1/3-hear-IND")]
    glossedWords := [⟨['ʔ', 'u', 'm', '-', 'w', 'a', 'g', 'a', 'y', 'á', 'y', 'ʔ', '-', 'i', '-', 'š', '-', 'g', 'e'], ['2', '-', 't', 'a', 'l', 'k', '-', 'I', 'N', 'D', '-', 'D', 'S', '-', 'I', 'D', 'X', '.', 'A', 'C', 'C'], [⟨['ʔ', 'u', 'm'], ['2'], none⟩, ⟨['w', 'a', 'g', 'a', 'y', 'á', 'y', 'ʔ'], ['t', 'a', 'l', 'k'], some '-'⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩, ⟨['š'], ['D', 'S'], some '-'⟩, ⟨['g', 'e'], ['I', 'D', 'X', '.', 'A', 'C', 'C'], some '-'⟩]⟩, ⟨['d', 'i', '-', 'd', 'á', 'm', 'a', 'l', '-', 'i'], ['1', '/', '3', '-', 'h', 'e', 'a', 'r', '-', 'I', 'N', 'D'], [⟨['d', 'i'], ['1', '/', '3'], none⟩, ⟨['d', 'á', 'm', 'a', 'l'], ['h', 'e', 'a', 'r'], some '-'⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.2"), ("phenomenon", "perceptionReading")] }

def ex105 : Datum :=
  { id := "hanink2021_ex105"
    source := ⟨"hanink-2021", "(105)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "w-álag-éweʔ-i-š-ge l-í:gi-yi"
    glossedTokens := [("w-álag-éweʔ-i-š-ge", "STAT-shine-hence-IND-DS-IDX.ACC"), ("l-í:gi-yi", "1/3-see-IND")]
    glossedWords := [⟨['w', '-', 'á', 'l', 'a', 'g', '-', 'é', 'w', 'e', 'ʔ', '-', 'i', '-', 'š', '-', 'g', 'e'], ['S', 'T', 'A', 'T', '-', 's', 'h', 'i', 'n', 'e', '-', 'h', 'e', 'n', 'c', 'e', '-', 'I', 'N', 'D', '-', 'D', 'S', '-', 'I', 'D', 'X', '.', 'A', 'C', 'C'], [⟨['w'], ['S', 'T', 'A', 'T'], none⟩, ⟨['á', 'l', 'a', 'g'], ['s', 'h', 'i', 'n', 'e'], some '-'⟩, ⟨['é', 'w', 'e', 'ʔ'], ['h', 'e', 'n', 'c', 'e'], some '-'⟩, ⟨['i'], ['I', 'N', 'D'], some '-'⟩, ⟨['š'], ['D', 'S'], some '-'⟩, ⟨['g', 'e'], ['I', 'D', 'X', '.', 'A', 'C', 'C'], some '-'⟩]⟩, ⟨['l', '-', 'í', ':', 'g', 'i', '-', 'y', 'i'], ['1', '/', '3', '-', 's', 'e', 'e', '-', 'I', 'N', 'D'], [⟨['l'], ['1', '/', '3'], none⟩, ⟨['í', 'g', 'i'], ['s', 'e', 'e'], some '-'⟩, ⟨['y', 'i'], ['I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.2"), ("phenomenon", "perceptionReading")] }

def ex120a : Datum :=
  { id := "hanink2021_ex120a"
    source := ⟨"hanink-2021", "(120a)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "gé-ši l-í:gi-yi"
    glossedTokens := [("gé-ši", "IDX.ACC-DU"), ("l-í:gi-yi", "1-see-IND")]
    glossedWords := [⟨['g', 'é', '-', 'š', 'i'], ['I', 'D', 'X', '.', 'A', 'C', 'C', '-', 'D', 'U'], [⟨['g', 'é'], ['I', 'D', 'X', '.', 'A', 'C', 'C'], none⟩, ⟨['š', 'i'], ['D', 'U'], some '-'⟩]⟩, ⟨['l', '-', 'í', ':', 'g', 'i', '-', 'y', 'i'], ['1', '-', 's', 'e', 'e', '-', 'I', 'N', 'D'], [⟨['l'], ['1'], none⟩, ⟨['í', 'g', 'i'], ['s', 'e', 'e'], some '-'⟩, ⟨['y', 'i'], ['I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.3"), ("phenomenon", "pronounConcord"), ("number", "dual")] }

def ex120b : Datum :=
  { id := "hanink2021_ex120b"
    source := ⟨"hanink-2021", "(120b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "gé-w l-í:gi-yi"
    glossedTokens := [("gé-w", "IDX.ACC-PL"), ("l-í:gi-yi", "1-see-IND")]
    glossedWords := [⟨['g', 'é', '-', 'w'], ['I', 'D', 'X', '.', 'A', 'C', 'C', '-', 'P', 'L'], [⟨['g', 'é'], ['I', 'D', 'X', '.', 'A', 'C', 'C'], none⟩, ⟨['w'], ['P', 'L'], some '-'⟩]⟩, ⟨['l', '-', 'í', ':', 'g', 'i', '-', 'y', 'i'], ['1', '-', 's', 'e', 'e', '-', 'I', 'N', 'D'], [⟨['l'], ['1'], none⟩, ⟨['í', 'g', 'i'], ['s', 'e', 'e'], some '-'⟩, ⟨['y', 'i'], ['I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.3"), ("phenomenon", "pronounConcord"), ("number", "plural")] }

def ex121a : Datum :=
  { id := "hanink2021_ex121a"
    source := ⟨"hanink-2021", "(121a)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "míʔle-ši t'elí:liwhu"
    glossedTokens := [("míʔle-ši", "all-DU"), ("t'elí:liwhu", "man.R")]
    glossedWords := [⟨['m', 'í', 'ʔ', 'l', 'e', '-', 'š', 'i'], ['a', 'l', 'l', '-', 'D', 'U'], [⟨['m', 'í', 'ʔ', 'l', 'e'], ['a', 'l', 'l'], none⟩, ⟨['š', 'i'], ['D', 'U'], some '-'⟩]⟩, ⟨['t', '\'', 'e', 'l', 'í', ':', 'l', 'i', 'w', 'h', 'u'], ['m', 'a', 'n', '.', 'R'], [⟨['t', '\'', 'e', 'l', 'í', 'l', 'i', 'w', 'h', 'u'], ['m', 'a', 'n', '.', 'R'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.3"), ("phenomenon", "modifierConcord"), ("number", "dual")] }

def ex121b : Datum :=
  { id := "hanink2021_ex121b"
    source := ⟨"hanink-2021", "(121b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "hésgil-ši di-ʔisá:sa"
    glossedTokens := [("hésgil-ši", "two-DU"), ("di-ʔisá:sa", "1-older.sister.R")]
    glossedWords := [⟨['h', 'é', 's', 'g', 'i', 'l', '-', 'š', 'i'], ['t', 'w', 'o', '-', 'D', 'U'], [⟨['h', 'é', 's', 'g', 'i', 'l'], ['t', 'w', 'o'], none⟩, ⟨['š', 'i'], ['D', 'U'], some '-'⟩]⟩, ⟨['d', 'i', '-', 'ʔ', 'i', 's', 'á', ':', 's', 'a'], ['1', '-', 'o', 'l', 'd', 'e', 'r', '.', 's', 'i', 's', 't', 'e', 'r', '.', 'R'], [⟨['d', 'i'], ['1'], none⟩, ⟨['ʔ', 'i', 's', 'á', 's', 'a'], ['o', 'l', 'd', 'e', 'r', '.', 's', 'i', 's', 't', 'e', 'r', '.', 'R'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.3"), ("phenomenon", "modifierConcord"), ("number", "dual")] }

def ex122a : Datum :=
  { id := "hanink2021_ex122a"
    source := ⟨"hanink-2021", "(122a)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "t'é:k'e-w dílek"
    glossedTokens := [("t'é:k'e-w", "many-PL"), ("dílek", "duck")]
    glossedWords := [⟨['t', '\'', 'é', ':', 'k', '\'', 'e', '-', 'w'], ['m', 'a', 'n', 'y', '-', 'P', 'L'], [⟨['t', '\'', 'é', 'k', '\'', 'e'], ['m', 'a', 'n', 'y'], none⟩, ⟨['w'], ['P', 'L'], some '-'⟩]⟩, ⟨['d', 'í', 'l', 'e', 'k'], ['d', 'u', 'c', 'k'], [⟨['d', 'í', 'l', 'e', 'k'], ['d', 'u', 'c', 'k'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.3"), ("phenomenon", "modifierConcord"), ("number", "plural")] }

def ex122b : Datum :=
  { id := "hanink2021_ex122b"
    source := ⟨"hanink-2021", "(122b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "hélme-w di-wic'úc'uk"
    glossedTokens := [("hélme-w", "three-PL"), ("di-wic'úc'uk", "1.POSS-younger.sister")]
    glossedWords := [⟨['h', 'é', 'l', 'm', 'e', '-', 'w'], ['t', 'h', 'r', 'e', 'e', '-', 'P', 'L'], [⟨['h', 'é', 'l', 'm', 'e'], ['t', 'h', 'r', 'e', 'e'], none⟩, ⟨['w'], ['P', 'L'], some '-'⟩]⟩, ⟨['d', 'i', '-', 'w', 'i', 'c', '\'', 'ú', 'c', '\'', 'u', 'k'], ['1', '.', 'P', 'O', 'S', 'S', '-', 'y', 'o', 'u', 'n', 'g', 'e', 'r', '.', 's', 'i', 's', 't', 'e', 'r'], [⟨['d', 'i'], ['1', '.', 'P', 'O', 'S', 'S'], none⟩, ⟨['w', 'i', 'c', '\'', 'ú', 'c', '\'', 'u', 'k'], ['y', 'o', 'u', 'n', 'g', 'e', 'r', '.', 's', 'i', 's', 't', 'e', 'r'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.3"), ("phenomenon", "modifierConcord"), ("number", "plural")] }

def all : List Datum := [ex1, ex2, ex3, ex19, ex20, ex21, ex22, ex23, ex25a, ex25b, ex27, ex41, ex45, ex46, ex47, ex50, ex51, ex53, ex54, ex56, ex91, ex96, ex98, ex102, ex103, ex104, ex105, ex120a, ex120b, ex121a, ex121b, ex122a, ex122b]

end Hanink2021.Examples
