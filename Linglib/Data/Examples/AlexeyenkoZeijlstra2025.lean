module

public import Linglib.Data.Examples.Schema

/-!
# `AlexeyenkoZeijlstra2025` — typed example data

Auto-generated from `Linglib/Data/Examples/AlexeyenkoZeijlstra2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AlexeyenkoZeijlstra2025.Examples`.
-/

@[expose] public section

namespace AlexeyenkoZeijlstra2025.Examples

def az2025_1a : Datum :=
  { id := "az2025_1a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She is proud of her daughter."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "proud"), ("dependent", "of")] }

def az2025_1b : Datum :=
  { id := "az2025_1b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "a proud of her daughter mother"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("head", "proud"), ("noun", "mother"), ("dependent", "of")] }

def az2025_2a : Datum :=
  { id := "az2025_2a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(2a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Ine perifanos ɣia to ɣio tu."
    glossedTokens := [("Ine", "is"), ("perifanos", "proud.M.SG"), ("ɣia", "for"), ("to", "the"), ("ɣio", "son.ACC"), ("tu", "his")]
    glossedWords := [⟨['I', 'n', 'e'], ['i', 's'], [⟨['I', 'n', 'e'], ['i', 's'], none⟩]⟩, ⟨['p', 'e', 'r', 'i', 'f', 'a', 'n', 'o', 's'], ['p', 'r', 'o', 'u', 'd', '.', 'M', '.', 'S', 'G'], [⟨['p', 'e', 'r', 'i', 'f', 'a', 'n', 'o', 's'], ['p', 'r', 'o', 'u', 'd', '.', 'M', '.', 'S', 'G'], none⟩]⟩, ⟨['ɣ', 'i', 'a'], ['f', 'o', 'r'], [⟨['ɣ', 'i', 'a'], ['f', 'o', 'r'], none⟩]⟩, ⟨['t', 'o'], ['t', 'h', 'e'], [⟨['t', 'o'], ['t', 'h', 'e'], none⟩]⟩, ⟨['ɣ', 'i', 'o'], ['s', 'o', 'n', '.', 'A', 'C', 'C'], [⟨['ɣ', 'i', 'o'], ['s', 'o', 'n', '.', 'A', 'C', 'C'], none⟩]⟩, ⟨['t', 'u'], ['h', 'i', 's'], [⟨['t', 'u'], ['h', 'i', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "perifanos"), ("dependent", "ɣia")] }

def az2025_2b : Datum :=
  { id := "az2025_2b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(2b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "o perifanos ɣia to ɣio tu pateras"
    glossedTokens := [("o", "the"), ("perifanos", "proud.M.SG"), ("ɣia", "for"), ("to", "the"), ("ɣio", "son.ACC"), ("tu", "his"), ("pateras", "father")]
    glossedWords := [⟨['o'], ['t', 'h', 'e'], [⟨['o'], ['t', 'h', 'e'], none⟩]⟩, ⟨['p', 'e', 'r', 'i', 'f', 'a', 'n', 'o', 's'], ['p', 'r', 'o', 'u', 'd', '.', 'M', '.', 'S', 'G'], [⟨['p', 'e', 'r', 'i', 'f', 'a', 'n', 'o', 's'], ['p', 'r', 'o', 'u', 'd', '.', 'M', '.', 'S', 'G'], none⟩]⟩, ⟨['ɣ', 'i', 'a'], ['f', 'o', 'r'], [⟨['ɣ', 'i', 'a'], ['f', 'o', 'r'], none⟩]⟩, ⟨['t', 'o'], ['t', 'h', 'e'], [⟨['t', 'o'], ['t', 'h', 'e'], none⟩]⟩, ⟨['ɣ', 'i', 'o'], ['s', 'o', 'n', '.', 'A', 'C', 'C'], [⟨['ɣ', 'i', 'o'], ['s', 'o', 'n', '.', 'A', 'C', 'C'], none⟩]⟩, ⟨['t', 'u'], ['h', 'i', 's'], [⟨['t', 'u'], ['h', 'i', 's'], none⟩]⟩, ⟨['p', 'a', 't', 'e', 'r', 'a', 's'], ['f', 'a', 't', 'h', 'e', 'r'], [⟨['p', 'a', 't', 'e', 'r', 'a', 's'], ['f', 'a', 't', 'h', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "perifanos"), ("noun", "pateras"), ("dependent", "ɣia")] }

def az2025_3a : Datum :=
  { id := "az2025_3a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(3a)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "Bere lanaz harro-a dago."
    glossedTokens := [("Bere", "her"), ("lanaz", "work.INS"), ("harro-a", "proud-DET"), ("dago", "is")]
    glossedWords := [⟨['B', 'e', 'r', 'e'], ['h', 'e', 'r'], [⟨['B', 'e', 'r', 'e'], ['h', 'e', 'r'], none⟩]⟩, ⟨['l', 'a', 'n', 'a', 'z'], ['w', 'o', 'r', 'k', '.', 'I', 'N', 'S'], [⟨['l', 'a', 'n', 'a', 'z'], ['w', 'o', 'r', 'k', '.', 'I', 'N', 'S'], none⟩]⟩, ⟨['h', 'a', 'r', 'r', 'o', '-', 'a'], ['p', 'r', 'o', 'u', 'd', '-', 'D', 'E', 'T'], [⟨['h', 'a', 'r', 'r', 'o'], ['p', 'r', 'o', 'u', 'd'], none⟩, ⟨['a'], ['D', 'E', 'T'], some '-'⟩]⟩, ⟨['d', 'a', 'g', 'o'], ['i', 's'], [⟨['d', 'a', 'g', 'o'], ['i', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "harro-a"), ("dependent", "Bere")] }

def az2025_3b : Datum :=
  { id := "az2025_3b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(3b)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "emakume bere lanaz harro-a"
    glossedTokens := [("emakume", "woman"), ("bere", "her"), ("lanaz", "work.INS"), ("harro-a", "proud-DET")]
    glossedWords := [⟨['e', 'm', 'a', 'k', 'u', 'm', 'e'], ['w', 'o', 'm', 'a', 'n'], [⟨['e', 'm', 'a', 'k', 'u', 'm', 'e'], ['w', 'o', 'm', 'a', 'n'], none⟩]⟩, ⟨['b', 'e', 'r', 'e'], ['h', 'e', 'r'], [⟨['b', 'e', 'r', 'e'], ['h', 'e', 'r'], none⟩]⟩, ⟨['l', 'a', 'n', 'a', 'z'], ['w', 'o', 'r', 'k', '.', 'I', 'N', 'S'], [⟨['l', 'a', 'n', 'a', 'z'], ['w', 'o', 'r', 'k', '.', 'I', 'N', 'S'], none⟩]⟩, ⟨['h', 'a', 'r', 'r', 'o', '-', 'a'], ['p', 'r', 'o', 'u', 'd', '-', 'D', 'E', 'T'], [⟨['h', 'a', 'r', 'r', 'o'], ['p', 'r', 'o', 'u', 'd'], none⟩, ⟨['a'], ['D', 'E', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("head", "harro-a"), ("noun", "emakume"), ("dependent", "bere")] }

def az2025_4a : Datum :=
  { id := "az2025_4a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(4a)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Anha be farzand-an=e xod moftaxar-∅-and."
    glossedTokens := [("Anha", "they"), ("be", "in"), ("farzand-an=e", "child-PL=LNK"), ("xod", "own"), ("moftaxar-∅-and", "proud-COP.PRS-3PL")]
    glossedWords := [⟨['A', 'n', 'h', 'a'], ['t', 'h', 'e', 'y'], [⟨['A', 'n', 'h', 'a'], ['t', 'h', 'e', 'y'], none⟩]⟩, ⟨['b', 'e'], ['i', 'n'], [⟨['b', 'e'], ['i', 'n'], none⟩]⟩, ⟨['f', 'a', 'r', 'z', 'a', 'n', 'd', '-', 'a', 'n', '=', 'e'], ['c', 'h', 'i', 'l', 'd', '-', 'P', 'L', '=', 'L', 'N', 'K'], [⟨['f', 'a', 'r', 'z', 'a', 'n', 'd'], ['c', 'h', 'i', 'l', 'd'], none⟩, ⟨['a', 'n'], ['P', 'L'], some '-'⟩, ⟨['e'], ['L', 'N', 'K'], some '='⟩]⟩, ⟨['x', 'o', 'd'], ['o', 'w', 'n'], [⟨['x', 'o', 'd'], ['o', 'w', 'n'], none⟩]⟩, ⟨['m', 'o', 'f', 't', 'a', 'x', 'a', 'r', '-', '∅', '-', 'a', 'n', 'd'], ['p', 'r', 'o', 'u', 'd', '-', 'C', 'O', 'P', '.', 'P', 'R', 'S', '-', '3', 'P', 'L'], [⟨['m', 'o', 'f', 't', 'a', 'x', 'a', 'r'], ['p', 'r', 'o', 'u', 'd'], none⟩, ⟨['∅'], ['C', 'O', 'P', '.', 'P', 'R', 'S'], some '-'⟩, ⟨['a', 'n', 'd'], ['3', 'P', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "moftaxar-∅-and"), ("dependent", "be")] }

def az2025_4b : Datum :=
  { id := "az2025_4b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(4b)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "madar-an=e be farzand-an=e xod moftaxar"
    glossedTokens := [("madar-an=e", "mother-PL=LNK"), ("be", "in"), ("farzand-an=e", "child-PL=LNK"), ("xod", "own"), ("moftaxar", "proud")]
    glossedWords := [⟨['m', 'a', 'd', 'a', 'r', '-', 'a', 'n', '=', 'e'], ['m', 'o', 't', 'h', 'e', 'r', '-', 'P', 'L', '=', 'L', 'N', 'K'], [⟨['m', 'a', 'd', 'a', 'r'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['a', 'n'], ['P', 'L'], some '-'⟩, ⟨['e'], ['L', 'N', 'K'], some '='⟩]⟩, ⟨['b', 'e'], ['i', 'n'], [⟨['b', 'e'], ['i', 'n'], none⟩]⟩, ⟨['f', 'a', 'r', 'z', 'a', 'n', 'd', '-', 'a', 'n', '=', 'e'], ['c', 'h', 'i', 'l', 'd', '-', 'P', 'L', '=', 'L', 'N', 'K'], [⟨['f', 'a', 'r', 'z', 'a', 'n', 'd'], ['c', 'h', 'i', 'l', 'd'], none⟩, ⟨['a', 'n'], ['P', 'L'], some '-'⟩, ⟨['e'], ['L', 'N', 'K'], some '='⟩]⟩, ⟨['x', 'o', 'd'], ['o', 'w', 'n'], [⟨['x', 'o', 'd'], ['o', 'w', 'n'], none⟩]⟩, ⟨['m', 'o', 'f', 't', 'a', 'x', 'a', 'r'], ['p', 'r', 'o', 'u', 'd'], [⟨['m', 'o', 'f', 't', 'a', 'x', 'a', 'r'], ['p', 'r', 'o', 'u', 'd'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "moftaxar"), ("attributivizer", "clitic"), ("noun", "madar-an=e"), ("dependent", "be")] }

def az2025_7a : Datum :=
  { id := "az2025_7a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "a smoothly running meeting"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "running"), ("noun", "meeting"), ("dependent", "smoothly")] }

def az2025_7b : Datum :=
  { id := "az2025_7b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "a running smoothly meeting"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("head", "running"), ("noun", "meeting"), ("dependent", "smoothly")] }

def az2025_8 : Datum :=
  { id := "az2025_8"
    source := ⟨"alexeyenko-zeijlstra-2025", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the proud of his children man"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("head", "proud"), ("noun", "man"), ("dependent", "of")] }

def az2025_9a : Datum :=
  { id := "az2025_9a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the proud that her daughter is a student woman"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("head", "proud"), ("noun", "woman"), ("dependent", "that")] }

def az2025_9b : Datum :=
  { id := "az2025_9b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the wearing a coat person"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("head", "wearing"), ("noun", "person"), ("dependent", "a")] }

def az2025_10a : Datum :=
  { id := "az2025_10a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the to Bill letter"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("head", "to"), ("noun", "letter"), ("dependent", "Bill")] }

def az2025_10b : Datum :=
  { id := "az2025_10b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "a which I published in 1991 book"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("head", "which"), ("noun", "book"), ("dependent", "I")] }

def az2025_15 : Datum :=
  { id := "az2025_15"
    source := ⟨"alexeyenko-zeijlstra-2025", "(15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is a tall enough guy to play basketball."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "tall"), ("attributivizer", "null"), ("noun", "guy"), ("degree", "enough")] }

def az2025_16 : Datum :=
  { id := "az2025_16"
    source := ⟨"alexeyenko-zeijlstra-2025", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is a tall enough to play basketball guy."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("head", "tall"), ("noun", "guy"), ("dependent", "to"), ("degree", "enough")] }

def az2025_17a : Datum :=
  { id := "az2025_17a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(17a)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "es bič'-i aris damok'ideb-ul-i tavis deda-ze."
    glossedTokens := [("es", "this"), ("bič'-i", "boy-NOM"), ("aris", "is"), ("damok'ideb-ul-i", "depend-PTCP-NOM"), ("tavis", "his.DAT"), ("deda-ze", "mother-on")]
    glossedWords := [⟨['e', 's'], ['t', 'h', 'i', 's'], [⟨['e', 's'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['b', 'i', 'č', '\'', '-', 'i'], ['b', 'o', 'y', '-', 'N', 'O', 'M'], [⟨['b', 'i', 'č', '\''], ['b', 'o', 'y'], none⟩, ⟨['i'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['a', 'r', 'i', 's'], ['i', 's'], [⟨['a', 'r', 'i', 's'], ['i', 's'], none⟩]⟩, ⟨['d', 'a', 'm', 'o', 'k', '\'', 'i', 'd', 'e', 'b', '-', 'u', 'l', '-', 'i'], ['d', 'e', 'p', 'e', 'n', 'd', '-', 'P', 'T', 'C', 'P', '-', 'N', 'O', 'M'], [⟨['d', 'a', 'm', 'o', 'k', '\'', 'i', 'd', 'e', 'b'], ['d', 'e', 'p', 'e', 'n', 'd'], none⟩, ⟨['u', 'l'], ['P', 'T', 'C', 'P'], some '-'⟩, ⟨['i'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['t', 'a', 'v', 'i', 's'], ['h', 'i', 's', '.', 'D', 'A', 'T'], [⟨['t', 'a', 'v', 'i', 's'], ['h', 'i', 's', '.', 'D', 'A', 'T'], none⟩]⟩, ⟨['d', 'e', 'd', 'a', '-', 'z', 'e'], ['m', 'o', 't', 'h', 'e', 'r', '-', 'o', 'n'], [⟨['d', 'e', 'd', 'a'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['z', 'e'], ['o', 'n'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "damok'ideb-ul-i"), ("dependent", "tavis")] }

def az2025_17b : Datum :=
  { id := "az2025_17b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(17b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "damok'ideb-ul-i tavis deda-ze bič'-i"
    glossedTokens := [("damok'ideb-ul-i", "depend-PTCP-NOM"), ("tavis", "his.DAT"), ("deda-ze", "mother-on"), ("bič'-i", "boy-NOM")]
    glossedWords := [⟨['d', 'a', 'm', 'o', 'k', '\'', 'i', 'd', 'e', 'b', '-', 'u', 'l', '-', 'i'], ['d', 'e', 'p', 'e', 'n', 'd', '-', 'P', 'T', 'C', 'P', '-', 'N', 'O', 'M'], [⟨['d', 'a', 'm', 'o', 'k', '\'', 'i', 'd', 'e', 'b'], ['d', 'e', 'p', 'e', 'n', 'd'], none⟩, ⟨['u', 'l'], ['P', 'T', 'C', 'P'], some '-'⟩, ⟨['i'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['t', 'a', 'v', 'i', 's'], ['h', 'i', 's', '.', 'D', 'A', 'T'], [⟨['t', 'a', 'v', 'i', 's'], ['h', 'i', 's', '.', 'D', 'A', 'T'], none⟩]⟩, ⟨['d', 'e', 'd', 'a', '-', 'z', 'e'], ['m', 'o', 't', 'h', 'e', 'r', '-', 'o', 'n'], [⟨['d', 'e', 'd', 'a'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['z', 'e'], ['o', 'n'], some '-'⟩]⟩, ⟨['b', 'i', 'č', '\'', '-', 'i'], ['b', 'o', 'y', '-', 'N', 'O', 'M'], [⟨['b', 'i', 'č', '\''], ['b', 'o', 'y'], none⟩, ⟨['i'], ['N', 'O', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("head", "damok'ideb-ul-i"), ("noun", "bič'-i"), ("dependent", "tavis")] }

def az2025_18a : Datum :=
  { id := "az2025_18a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(18a)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "János független a szüle-i-től."
    glossedTokens := [("János", "János"), ("független", "independent"), ("a", "the"), ("szüle-i-től", "parents-POSS.3SG-from")]
    glossedWords := [⟨['J', 'á', 'n', 'o', 's'], ['J', 'á', 'n', 'o', 's'], [⟨['J', 'á', 'n', 'o', 's'], ['J', 'á', 'n', 'o', 's'], none⟩]⟩, ⟨['f', 'ü', 'g', 'g', 'e', 't', 'l', 'e', 'n'], ['i', 'n', 'd', 'e', 'p', 'e', 'n', 'd', 'e', 'n', 't'], [⟨['f', 'ü', 'g', 'g', 'e', 't', 'l', 'e', 'n'], ['i', 'n', 'd', 'e', 'p', 'e', 'n', 'd', 'e', 'n', 't'], none⟩]⟩, ⟨['a'], ['t', 'h', 'e'], [⟨['a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['s', 'z', 'ü', 'l', 'e', '-', 'i', '-', 't', 'ő', 'l'], ['p', 'a', 'r', 'e', 'n', 't', 's', '-', 'P', 'O', 'S', 'S', '.', '3', 'S', 'G', '-', 'f', 'r', 'o', 'm'], [⟨['s', 'z', 'ü', 'l', 'e'], ['p', 'a', 'r', 'e', 'n', 't', 's'], none⟩, ⟨['i'], ['P', 'O', 'S', 'S', '.', '3', 'S', 'G'], some '-'⟩, ⟨['t', 'ő', 'l'], ['f', 'r', 'o', 'm'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "független"), ("dependent", "a")] }

def az2025_18b : Datum :=
  { id := "az2025_18b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(18b)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "egy független a szüle-i-től fiú"
    glossedTokens := [("egy", "a"), ("független", "independent"), ("a", "the"), ("szüle-i-től", "parents-POSS.3SG-from"), ("fiú", "boy")]
    glossedWords := [⟨['e', 'g', 'y'], ['a'], [⟨['e', 'g', 'y'], ['a'], none⟩]⟩, ⟨['f', 'ü', 'g', 'g', 'e', 't', 'l', 'e', 'n'], ['i', 'n', 'd', 'e', 'p', 'e', 'n', 'd', 'e', 'n', 't'], [⟨['f', 'ü', 'g', 'g', 'e', 't', 'l', 'e', 'n'], ['i', 'n', 'd', 'e', 'p', 'e', 'n', 'd', 'e', 'n', 't'], none⟩]⟩, ⟨['a'], ['t', 'h', 'e'], [⟨['a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['s', 'z', 'ü', 'l', 'e', '-', 'i', '-', 't', 'ő', 'l'], ['p', 'a', 'r', 'e', 'n', 't', 's', '-', 'P', 'O', 'S', 'S', '.', '3', 'S', 'G', '-', 'f', 'r', 'o', 'm'], [⟨['s', 'z', 'ü', 'l', 'e'], ['p', 'a', 'r', 'e', 'n', 't', 's'], none⟩, ⟨['i'], ['P', 'O', 'S', 'S', '.', '3', 'S', 'G'], some '-'⟩, ⟨['t', 'ő', 'l'], ['f', 'r', 'o', 'm'], some '-'⟩]⟩, ⟨['f', 'i', 'ú'], ['b', 'o', 'y'], [⟨['f', 'i', 'ú'], ['b', 'o', 'y'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("head", "független"), ("noun", "fiú"), ("dependent", "a")] }

def az2025_19a : Datum :=
  { id := "az2025_19a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(19a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Jón er stolt-ur af syni sínum."
    glossedTokens := [("Jón", "Jón"), ("er", "is"), ("stolt-ur", "proud-M.SG.NOM.STRONG"), ("af", "on"), ("syni", "son.DAT"), ("sínum", "his.DAT")]
    glossedWords := [⟨['J', 'ó', 'n'], ['J', 'ó', 'n'], [⟨['J', 'ó', 'n'], ['J', 'ó', 'n'], none⟩]⟩, ⟨['e', 'r'], ['i', 's'], [⟨['e', 'r'], ['i', 's'], none⟩]⟩, ⟨['s', 't', 'o', 'l', 't', '-', 'u', 'r'], ['p', 'r', 'o', 'u', 'd', '-', 'M', '.', 'S', 'G', '.', 'N', 'O', 'M', '.', 'S', 'T', 'R', 'O', 'N', 'G'], [⟨['s', 't', 'o', 'l', 't'], ['p', 'r', 'o', 'u', 'd'], none⟩, ⟨['u', 'r'], ['M', '.', 'S', 'G', '.', 'N', 'O', 'M', '.', 'S', 'T', 'R', 'O', 'N', 'G'], some '-'⟩]⟩, ⟨['a', 'f'], ['o', 'n'], [⟨['a', 'f'], ['o', 'n'], none⟩]⟩, ⟨['s', 'y', 'n', 'i'], ['s', 'o', 'n', '.', 'D', 'A', 'T'], [⟨['s', 'y', 'n', 'i'], ['s', 'o', 'n', '.', 'D', 'A', 'T'], none⟩]⟩, ⟨['s', 'í', 'n', 'u', 'm'], ['h', 'i', 's', '.', 'D', 'A', 'T'], [⟨['s', 'í', 'n', 'u', 'm'], ['h', 'i', 's', '.', 'D', 'A', 'T'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "stolt-ur"), ("dependent", "af")] }

def az2025_19b : Datum :=
  { id := "az2025_19b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(19b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "stolt-ur af syni sínum faðir"
    glossedTokens := [("stolt-ur", "proud-M.SG.NOM.STRONG"), ("af", "on"), ("syni", "son.DAT"), ("sínum", "his.DAT"), ("faðir", "father")]
    glossedWords := [⟨['s', 't', 'o', 'l', 't', '-', 'u', 'r'], ['p', 'r', 'o', 'u', 'd', '-', 'M', '.', 'S', 'G', '.', 'N', 'O', 'M', '.', 'S', 'T', 'R', 'O', 'N', 'G'], [⟨['s', 't', 'o', 'l', 't'], ['p', 'r', 'o', 'u', 'd'], none⟩, ⟨['u', 'r'], ['M', '.', 'S', 'G', '.', 'N', 'O', 'M', '.', 'S', 'T', 'R', 'O', 'N', 'G'], some '-'⟩]⟩, ⟨['a', 'f'], ['o', 'n'], [⟨['a', 'f'], ['o', 'n'], none⟩]⟩, ⟨['s', 'y', 'n', 'i'], ['s', 'o', 'n', '.', 'D', 'A', 'T'], [⟨['s', 'y', 'n', 'i'], ['s', 'o', 'n', '.', 'D', 'A', 'T'], none⟩]⟩, ⟨['s', 'í', 'n', 'u', 'm'], ['h', 'i', 's', '.', 'D', 'A', 'T'], [⟨['s', 'í', 'n', 'u', 'm'], ['h', 'i', 's', '.', 'D', 'A', 'T'], none⟩]⟩, ⟨['f', 'a', 'ð', 'i', 'r'], ['f', 'a', 't', 'h', 'e', 'r'], [⟨['f', 'a', 'ð', 'i', 'r'], ['f', 'a', 't', 'h', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("head", "stolt-ur"), ("noun", "faðir"), ("dependent", "af")] }

def az2025_20a : Datum :=
  { id := "az2025_20a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(20a)"⟩
    reportedIn := none
    language := "nucl1235"
    primaryText := "(Na) hpart ē ir tłay-ov."
    glossedTokens := [("(Na)", "3SG"), ("hpart", "proud"), ("ē", "COP.3SG"), ("ir", "REFL.3SG.GEN"), ("tłay-ov", "boy-INS")]
    glossedWords := [⟨['(', 'N', 'a', ')'], ['3', 'S', 'G'], [⟨['N', 'a'], ['3', 'S', 'G'], none⟩]⟩, ⟨['h', 'p', 'a', 'r', 't'], ['p', 'r', 'o', 'u', 'd'], [⟨['h', 'p', 'a', 'r', 't'], ['p', 'r', 'o', 'u', 'd'], none⟩]⟩, ⟨['ē'], ['C', 'O', 'P', '.', '3', 'S', 'G'], [⟨['ē'], ['C', 'O', 'P', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['i', 'r'], ['R', 'E', 'F', 'L', '.', '3', 'S', 'G', '.', 'G', 'E', 'N'], [⟨['i', 'r'], ['R', 'E', 'F', 'L', '.', '3', 'S', 'G', '.', 'G', 'E', 'N'], none⟩]⟩, ⟨['t', 'ł', 'a', 'y', '-', 'o', 'v'], ['b', 'o', 'y', '-', 'I', 'N', 'S'], [⟨['t', 'ł', 'a', 'y'], ['b', 'o', 'y'], none⟩, ⟨['o', 'v'], ['I', 'N', 'S'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "hpart"), ("dependent", "ir")] }

def az2025_20b : Datum :=
  { id := "az2025_20b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(20b)"⟩
    reportedIn := none
    language := "nucl1235"
    primaryText := "hpart ir tłay-ov hayr"
    glossedTokens := [("hpart", "proud"), ("ir", "REFL.3SG.GEN"), ("tłay-ov", "boy-INS"), ("hayr", "father")]
    glossedWords := [⟨['h', 'p', 'a', 'r', 't'], ['p', 'r', 'o', 'u', 'd'], [⟨['h', 'p', 'a', 'r', 't'], ['p', 'r', 'o', 'u', 'd'], none⟩]⟩, ⟨['i', 'r'], ['R', 'E', 'F', 'L', '.', '3', 'S', 'G', '.', 'G', 'E', 'N'], [⟨['i', 'r'], ['R', 'E', 'F', 'L', '.', '3', 'S', 'G', '.', 'G', 'E', 'N'], none⟩]⟩, ⟨['t', 'ł', 'a', 'y', '-', 'o', 'v'], ['b', 'o', 'y', '-', 'I', 'N', 'S'], [⟨['t', 'ł', 'a', 'y'], ['b', 'o', 'y'], none⟩, ⟨['o', 'v'], ['I', 'N', 'S'], some '-'⟩]⟩, ⟨['h', 'a', 'y', 'r'], ['f', 'a', 't', 'h', 'e', 'r'], [⟨['h', 'a', 'y', 'r'], ['f', 'a', 't', 'h', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("head", "hpart"), ("noun", "hayr"), ("dependent", "ir")] }

def az2025_21a : Datum :=
  { id := "az2025_21a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(21a)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "On je ponosan na svog sina."
    glossedTokens := [("On", "he"), ("je", "is"), ("ponosan", "proud.SHORT"), ("na", "on"), ("svog", "his"), ("sina", "son")]
    glossedWords := [⟨['O', 'n'], ['h', 'e'], [⟨['O', 'n'], ['h', 'e'], none⟩]⟩, ⟨['j', 'e'], ['i', 's'], [⟨['j', 'e'], ['i', 's'], none⟩]⟩, ⟨['p', 'o', 'n', 'o', 's', 'a', 'n'], ['p', 'r', 'o', 'u', 'd', '.', 'S', 'H', 'O', 'R', 'T'], [⟨['p', 'o', 'n', 'o', 's', 'a', 'n'], ['p', 'r', 'o', 'u', 'd', '.', 'S', 'H', 'O', 'R', 'T'], none⟩]⟩, ⟨['n', 'a'], ['o', 'n'], [⟨['n', 'a'], ['o', 'n'], none⟩]⟩, ⟨['s', 'v', 'o', 'g'], ['h', 'i', 's'], [⟨['s', 'v', 'o', 'g'], ['h', 'i', 's'], none⟩]⟩, ⟨['s', 'i', 'n', 'a'], ['s', 'o', 'n'], [⟨['s', 'i', 'n', 'a'], ['s', 'o', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "ponosan"), ("dependent", "na")] }

def az2025_21b : Datum :=
  { id := "az2025_21b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(21b)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "ponosan na svog sina otac"
    glossedTokens := [("ponosan", "proud.SHORT"), ("na", "on"), ("svog", "his"), ("sina", "son"), ("otac", "father")]
    glossedWords := [⟨['p', 'o', 'n', 'o', 's', 'a', 'n'], ['p', 'r', 'o', 'u', 'd', '.', 'S', 'H', 'O', 'R', 'T'], [⟨['p', 'o', 'n', 'o', 's', 'a', 'n'], ['p', 'r', 'o', 'u', 'd', '.', 'S', 'H', 'O', 'R', 'T'], none⟩]⟩, ⟨['n', 'a'], ['o', 'n'], [⟨['n', 'a'], ['o', 'n'], none⟩]⟩, ⟨['s', 'v', 'o', 'g'], ['h', 'i', 's'], [⟨['s', 'v', 'o', 'g'], ['h', 'i', 's'], none⟩]⟩, ⟨['s', 'i', 'n', 'a'], ['s', 'o', 'n'], [⟨['s', 'i', 'n', 'a'], ['s', 'o', 'n'], none⟩]⟩, ⟨['o', 't', 'a', 'c'], ['f', 'a', 't', 'h', 'e', 'r'], [⟨['o', 't', 'a', 'c'], ['f', 'a', 't', 'h', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("head", "ponosan"), ("noun", "otac"), ("dependent", "na")] }

def az2025_23b : Datum :=
  { id := "az2025_23b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(23b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I filikes pros tin Turkia χores apariθmunte os eksis"
    glossedTokens := [("I", "the"), ("filikes", "friendly"), ("pros", "towards"), ("tin", "the"), ("Turkia", "Turkey"), ("χores", "countries"), ("apariθmunte", "are.listed"), ("os", "as"), ("eksis", "following")]
    glossedWords := [⟨['I'], ['t', 'h', 'e'], [⟨['I'], ['t', 'h', 'e'], none⟩]⟩, ⟨['f', 'i', 'l', 'i', 'k', 'e', 's'], ['f', 'r', 'i', 'e', 'n', 'd', 'l', 'y'], [⟨['f', 'i', 'l', 'i', 'k', 'e', 's'], ['f', 'r', 'i', 'e', 'n', 'd', 'l', 'y'], none⟩]⟩, ⟨['p', 'r', 'o', 's'], ['t', 'o', 'w', 'a', 'r', 'd', 's'], [⟨['p', 'r', 'o', 's'], ['t', 'o', 'w', 'a', 'r', 'd', 's'], none⟩]⟩, ⟨['t', 'i', 'n'], ['t', 'h', 'e'], [⟨['t', 'i', 'n'], ['t', 'h', 'e'], none⟩]⟩, ⟨['T', 'u', 'r', 'k', 'i', 'a'], ['T', 'u', 'r', 'k', 'e', 'y'], [⟨['T', 'u', 'r', 'k', 'i', 'a'], ['T', 'u', 'r', 'k', 'e', 'y'], none⟩]⟩, ⟨['χ', 'o', 'r', 'e', 's'], ['c', 'o', 'u', 'n', 't', 'r', 'i', 'e', 's'], [⟨['χ', 'o', 'r', 'e', 's'], ['c', 'o', 'u', 'n', 't', 'r', 'i', 'e', 's'], none⟩]⟩, ⟨['a', 'p', 'a', 'r', 'i', 'θ', 'm', 'u', 'n', 't', 'e'], ['a', 'r', 'e', '.', 'l', 'i', 's', 't', 'e', 'd'], [⟨['a', 'p', 'a', 'r', 'i', 'θ', 'm', 'u', 'n', 't', 'e'], ['a', 'r', 'e', '.', 'l', 'i', 's', 't', 'e', 'd'], none⟩]⟩, ⟨['o', 's'], ['a', 's'], [⟨['o', 's'], ['a', 's'], none⟩]⟩, ⟨['e', 'k', 's', 'i', 's'], ['f', 'o', 'l', 'l', 'o', 'w', 'i', 'n', 'g'], [⟨['e', 'k', 's', 'i', 's'], ['f', 'o', 'l', 'l', 'o', 'w', 'i', 'n', 'g'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "filikes"), ("noun", "χores"), ("dependent", "pros")] }

def az2025_24c : Datum :=
  { id := "az2025_24c"
    source := ⟨"alexeyenko-zeijlstra-2025", "(24c)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Inogda on zažmurival ustavšyje ot plohogo osveščenija glaza"
    glossedTokens := [("Inogda", "sometimes"), ("on", "he"), ("zažmurival", "closed.tightly"), ("ustavšyje", "tired"), ("ot", "from"), ("plohogo", "bad"), ("osveščenija", "lighting"), ("glaza", "eyes")]
    glossedWords := [⟨['I', 'n', 'o', 'g', 'd', 'a'], ['s', 'o', 'm', 'e', 't', 'i', 'm', 'e', 's'], [⟨['I', 'n', 'o', 'g', 'd', 'a'], ['s', 'o', 'm', 'e', 't', 'i', 'm', 'e', 's'], none⟩]⟩, ⟨['o', 'n'], ['h', 'e'], [⟨['o', 'n'], ['h', 'e'], none⟩]⟩, ⟨['z', 'a', 'ž', 'm', 'u', 'r', 'i', 'v', 'a', 'l'], ['c', 'l', 'o', 's', 'e', 'd', '.', 't', 'i', 'g', 'h', 't', 'l', 'y'], [⟨['z', 'a', 'ž', 'm', 'u', 'r', 'i', 'v', 'a', 'l'], ['c', 'l', 'o', 's', 'e', 'd', '.', 't', 'i', 'g', 'h', 't', 'l', 'y'], none⟩]⟩, ⟨['u', 's', 't', 'a', 'v', 'š', 'y', 'j', 'e'], ['t', 'i', 'r', 'e', 'd'], [⟨['u', 's', 't', 'a', 'v', 'š', 'y', 'j', 'e'], ['t', 'i', 'r', 'e', 'd'], none⟩]⟩, ⟨['o', 't'], ['f', 'r', 'o', 'm'], [⟨['o', 't'], ['f', 'r', 'o', 'm'], none⟩]⟩, ⟨['p', 'l', 'o', 'h', 'o', 'g', 'o'], ['b', 'a', 'd'], [⟨['p', 'l', 'o', 'h', 'o', 'g', 'o'], ['b', 'a', 'd'], none⟩]⟩, ⟨['o', 's', 'v', 'e', 'š', 'č', 'e', 'n', 'i', 'j', 'a'], ['l', 'i', 'g', 'h', 't', 'i', 'n', 'g'], [⟨['o', 's', 'v', 'e', 'š', 'č', 'e', 'n', 'i', 'j', 'a'], ['l', 'i', 'g', 'h', 't', 'i', 'n', 'g'], none⟩]⟩, ⟨['g', 'l', 'a', 'z', 'a'], ['e', 'y', 'e', 's'], [⟨['g', 'l', 'a', 'z', 'a'], ['e', 'y', 'e', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "ustavšyje"), ("noun", "glaza"), ("dependent", "ot")] }

def az2025_26 : Datum :=
  { id := "az2025_26"
    source := ⟨"alexeyenko-zeijlstra-2025", "(26)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "yí-ge dúlì yú fùmǔ de qīngshàonián"
    glossedTokens := [("yí-ge", "one-CLF"), ("dúlì", "independent"), ("yú", "from"), ("fùmǔ", "parents"), ("de", "LNK"), ("qīngshàonián", "teenager")]
    glossedWords := [⟨['y', 'í', '-', 'g', 'e'], ['o', 'n', 'e', '-', 'C', 'L', 'F'], [⟨['y', 'í'], ['o', 'n', 'e'], none⟩, ⟨['g', 'e'], ['C', 'L', 'F'], some '-'⟩]⟩, ⟨['d', 'ú', 'l', 'ì'], ['i', 'n', 'd', 'e', 'p', 'e', 'n', 'd', 'e', 'n', 't'], [⟨['d', 'ú', 'l', 'ì'], ['i', 'n', 'd', 'e', 'p', 'e', 'n', 'd', 'e', 'n', 't'], none⟩]⟩, ⟨['y', 'ú'], ['f', 'r', 'o', 'm'], [⟨['y', 'ú'], ['f', 'r', 'o', 'm'], none⟩]⟩, ⟨['f', 'ù', 'm', 'ǔ'], ['p', 'a', 'r', 'e', 'n', 't', 's'], [⟨['f', 'ù', 'm', 'ǔ'], ['p', 'a', 'r', 'e', 'n', 't', 's'], none⟩]⟩, ⟨['d', 'e'], ['L', 'N', 'K'], [⟨['d', 'e'], ['L', 'N', 'K'], none⟩]⟩, ⟨['q', 'ī', 'n', 'g', 's', 'h', 'à', 'o', 'n', 'i', 'á', 'n'], ['t', 'e', 'e', 'n', 'a', 'g', 'e', 'r'], [⟨['q', 'ī', 'n', 'g', 's', 'h', 'à', 'o', 'n', 'i', 'á', 'n'], ['t', 'e', 'e', 'n', 'a', 'g', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "dúlì"), ("attributivizer", "clitic"), ("noun", "qīngshàonián"), ("dependent", "yú")] }

def az2025_27 : Datum :=
  { id := "az2025_27"
    source := ⟨"alexeyenko-zeijlstra-2025", "(27)"⟩
    reportedIn := none
    language := "taga1270"
    primaryText := "Naghahanap ako ng bagay (para) sa bata=ng damit."
    glossedTokens := [("Naghahanap", "AV.PROG.search"), ("ako", "1SG.NOM"), ("ng", "GEN"), ("bagay", "suitable"), ("(para)", "for"), ("sa", "DAT"), ("bata=ng", "child=LNK"), ("damit", "dress")]
    glossedWords := [⟨['N', 'a', 'g', 'h', 'a', 'h', 'a', 'n', 'a', 'p'], ['A', 'V', '.', 'P', 'R', 'O', 'G', '.', 's', 'e', 'a', 'r', 'c', 'h'], [⟨['N', 'a', 'g', 'h', 'a', 'h', 'a', 'n', 'a', 'p'], ['A', 'V', '.', 'P', 'R', 'O', 'G', '.', 's', 'e', 'a', 'r', 'c', 'h'], none⟩]⟩, ⟨['a', 'k', 'o'], ['1', 'S', 'G', '.', 'N', 'O', 'M'], [⟨['a', 'k', 'o'], ['1', 'S', 'G', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['n', 'g'], ['G', 'E', 'N'], [⟨['n', 'g'], ['G', 'E', 'N'], none⟩]⟩, ⟨['b', 'a', 'g', 'a', 'y'], ['s', 'u', 'i', 't', 'a', 'b', 'l', 'e'], [⟨['b', 'a', 'g', 'a', 'y'], ['s', 'u', 'i', 't', 'a', 'b', 'l', 'e'], none⟩]⟩, ⟨['(', 'p', 'a', 'r', 'a', ')'], ['f', 'o', 'r'], [⟨['p', 'a', 'r', 'a'], ['f', 'o', 'r'], none⟩]⟩, ⟨['s', 'a'], ['D', 'A', 'T'], [⟨['s', 'a'], ['D', 'A', 'T'], none⟩]⟩, ⟨['b', 'a', 't', 'a', '=', 'n', 'g'], ['c', 'h', 'i', 'l', 'd', '=', 'L', 'N', 'K'], [⟨['b', 'a', 't', 'a'], ['c', 'h', 'i', 'l', 'd'], none⟩, ⟨['n', 'g'], ['L', 'N', 'K'], some '='⟩]⟩, ⟨['d', 'a', 'm', 'i', 't'], ['d', 'r', 'e', 's', 's'], [⟨['d', 'a', 'm', 'i', 't'], ['d', 'r', 'e', 's', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "bagay"), ("attributivizer", "clitic"), ("noun", "damit"), ("dependent", "(para)")] }

def az2025_28b : Datum :=
  { id := "az2025_28b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(28b)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "emakume harro-a"
    glossedTokens := [("emakume", "woman"), ("harro-a", "proud-DET")]
    glossedWords := [⟨['e', 'm', 'a', 'k', 'u', 'm', 'e'], ['w', 'o', 'm', 'a', 'n'], [⟨['e', 'm', 'a', 'k', 'u', 'm', 'e'], ['w', 'o', 'm', 'a', 'n'], none⟩]⟩, ⟨['h', 'a', 'r', 'r', 'o', '-', 'a'], ['p', 'r', 'o', 'u', 'd', '-', 'D', 'E', 'T'], [⟨['h', 'a', 'r', 'r', 'o'], ['p', 'r', 'o', 'u', 'd'], none⟩, ⟨['a'], ['D', 'E', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "harro-a"), ("noun", "emakume")] }

def az2025_28d : Datum :=
  { id := "az2025_28d"
    source := ⟨"alexeyenko-zeijlstra-2025", "(28d)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "bere lanaz harro-a dagoen emakume-a"
    glossedTokens := [("bere", "her"), ("lanaz", "work.INS"), ("harro-a", "proud-DET"), ("dagoen", "is.COMP"), ("emakume-a", "woman-DET")]
    glossedWords := [⟨['b', 'e', 'r', 'e'], ['h', 'e', 'r'], [⟨['b', 'e', 'r', 'e'], ['h', 'e', 'r'], none⟩]⟩, ⟨['l', 'a', 'n', 'a', 'z'], ['w', 'o', 'r', 'k', '.', 'I', 'N', 'S'], [⟨['l', 'a', 'n', 'a', 'z'], ['w', 'o', 'r', 'k', '.', 'I', 'N', 'S'], none⟩]⟩, ⟨['h', 'a', 'r', 'r', 'o', '-', 'a'], ['p', 'r', 'o', 'u', 'd', '-', 'D', 'E', 'T'], [⟨['h', 'a', 'r', 'r', 'o'], ['p', 'r', 'o', 'u', 'd'], none⟩, ⟨['a'], ['D', 'E', 'T'], some '-'⟩]⟩, ⟨['d', 'a', 'g', 'o', 'e', 'n'], ['i', 's', '.', 'C', 'O', 'M', 'P'], [⟨['d', 'a', 'g', 'o', 'e', 'n'], ['i', 's', '.', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['e', 'm', 'a', 'k', 'u', 'm', 'e', '-', 'a'], ['w', 'o', 'm', 'a', 'n', '-', 'D', 'E', 'T'], [⟨['e', 'm', 'a', 'k', 'u', 'm', 'e'], ['w', 'o', 'm', 'a', 'n'], none⟩, ⟨['a'], ['D', 'E', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "harro-a"), ("noun", "emakume-a"), ("dependent", "bere"), ("construction", "relative")] }

def az2025_29a : Datum :=
  { id := "az2025_29a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(29a)"⟩
    reportedIn := none
    language := "chac1251"
    primaryText := "naa motó tsi ʂo yói karetera ka=tí."
    glossedTokens := [("naa", "DEM"), ("motó", "motorcycle"), ("tsi", "PTCL"), ("ʂo", "DECL"), ("yói", "bad"), ("karetera", "highway"), ("ka=tí", "go=NMLZ:PURP")]
    glossedWords := [⟨['n', 'a', 'a'], ['D', 'E', 'M'], [⟨['n', 'a', 'a'], ['D', 'E', 'M'], none⟩]⟩, ⟨['m', 'o', 't', 'ó'], ['m', 'o', 't', 'o', 'r', 'c', 'y', 'c', 'l', 'e'], [⟨['m', 'o', 't', 'ó'], ['m', 'o', 't', 'o', 'r', 'c', 'y', 'c', 'l', 'e'], none⟩]⟩, ⟨['t', 's', 'i'], ['P', 'T', 'C', 'L'], [⟨['t', 's', 'i'], ['P', 'T', 'C', 'L'], none⟩]⟩, ⟨['ʂ', 'o'], ['D', 'E', 'C', 'L'], [⟨['ʂ', 'o'], ['D', 'E', 'C', 'L'], none⟩]⟩, ⟨['y', 'ó', 'i'], ['b', 'a', 'd'], [⟨['y', 'ó', 'i'], ['b', 'a', 'd'], none⟩]⟩, ⟨['k', 'a', 'r', 'e', 't', 'e', 'r', 'a'], ['h', 'i', 'g', 'h', 'w', 'a', 'y'], [⟨['k', 'a', 'r', 'e', 't', 'e', 'r', 'a'], ['h', 'i', 'g', 'h', 'w', 'a', 'y'], none⟩]⟩, ⟨['k', 'a', '=', 't', 'í'], ['g', 'o', '=', 'N', 'M', 'L', 'Z', ':', 'P', 'U', 'R', 'P'], [⟨['k', 'a'], ['g', 'o'], none⟩, ⟨['t', 'í'], ['N', 'M', 'L', 'Z', ':', 'P', 'U', 'R', 'P'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("naa motó tsi ʂo karetera ka=tí yói.", .acceptable)]
    readings := []
    paperFeatures := [("head", "yói"), ("dependent", "karetera")] }

def az2025_29b : Datum :=
  { id := "az2025_29b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(29b)"⟩
    reportedIn := none
    language := "chac1251"
    primaryText := "motó yói karetera ka=tí kopi=ki paɨ."
    glossedTokens := [("motó", "motorcycle"), ("yói", "bad"), ("karetera", "highway"), ("ka=tí", "go=NMLZ:PURP"), ("kopi=ki", "buy=DECL.NPST"), ("paɨ", "Paë")]
    glossedWords := [⟨['m', 'o', 't', 'ó'], ['m', 'o', 't', 'o', 'r', 'c', 'y', 'c', 'l', 'e'], [⟨['m', 'o', 't', 'ó'], ['m', 'o', 't', 'o', 'r', 'c', 'y', 'c', 'l', 'e'], none⟩]⟩, ⟨['y', 'ó', 'i'], ['b', 'a', 'd'], [⟨['y', 'ó', 'i'], ['b', 'a', 'd'], none⟩]⟩, ⟨['k', 'a', 'r', 'e', 't', 'e', 'r', 'a'], ['h', 'i', 'g', 'h', 'w', 'a', 'y'], [⟨['k', 'a', 'r', 'e', 't', 'e', 'r', 'a'], ['h', 'i', 'g', 'h', 'w', 'a', 'y'], none⟩]⟩, ⟨['k', 'a', '=', 't', 'í'], ['g', 'o', '=', 'N', 'M', 'L', 'Z', ':', 'P', 'U', 'R', 'P'], [⟨['k', 'a'], ['g', 'o'], none⟩, ⟨['t', 'í'], ['N', 'M', 'L', 'Z', ':', 'P', 'U', 'R', 'P'], some '='⟩]⟩, ⟨['k', 'o', 'p', 'i', '=', 'k', 'i'], ['b', 'u', 'y', '=', 'D', 'E', 'C', 'L', '.', 'N', 'P', 'S', 'T'], [⟨['k', 'o', 'p', 'i'], ['b', 'u', 'y'], none⟩, ⟨['k', 'i'], ['D', 'E', 'C', 'L', '.', 'N', 'P', 'S', 'T'], some '='⟩]⟩, ⟨['p', 'a', 'ɨ'], ['P', 'a', 'ë'], [⟨['p', 'a', 'ɨ'], ['P', 'a', 'ë'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("motó karetera ka=tí yói kopi=ki paɨ.", .ungrammatical)]
    readings := []
    paperFeatures := [("head", "yói"), ("noun", "motó"), ("dependent", "karetera")] }

def az2025_29c : Datum :=
  { id := "az2025_29c"
    source := ⟨"alexeyenko-zeijlstra-2025", "(29c)"⟩
    reportedIn := none
    language := "chac1251"
    primaryText := "motó karetera ka=tí yói=ka kopi=ki paɨ."
    glossedTokens := [("motó", "motorcycle"), ("karetera", "highway"), ("ka=tí", "go=NMLZ:PURP"), ("yói=ka", "bad=REL"), ("kopi=ki", "buy=DECL.NPST"), ("paɨ", "Paë")]
    glossedWords := [⟨['m', 'o', 't', 'ó'], ['m', 'o', 't', 'o', 'r', 'c', 'y', 'c', 'l', 'e'], [⟨['m', 'o', 't', 'ó'], ['m', 'o', 't', 'o', 'r', 'c', 'y', 'c', 'l', 'e'], none⟩]⟩, ⟨['k', 'a', 'r', 'e', 't', 'e', 'r', 'a'], ['h', 'i', 'g', 'h', 'w', 'a', 'y'], [⟨['k', 'a', 'r', 'e', 't', 'e', 'r', 'a'], ['h', 'i', 'g', 'h', 'w', 'a', 'y'], none⟩]⟩, ⟨['k', 'a', '=', 't', 'í'], ['g', 'o', '=', 'N', 'M', 'L', 'Z', ':', 'P', 'U', 'R', 'P'], [⟨['k', 'a'], ['g', 'o'], none⟩, ⟨['t', 'í'], ['N', 'M', 'L', 'Z', ':', 'P', 'U', 'R', 'P'], some '='⟩]⟩, ⟨['y', 'ó', 'i', '=', 'k', 'a'], ['b', 'a', 'd', '=', 'R', 'E', 'L'], [⟨['y', 'ó', 'i'], ['b', 'a', 'd'], none⟩, ⟨['k', 'a'], ['R', 'E', 'L'], some '='⟩]⟩, ⟨['k', 'o', 'p', 'i', '=', 'k', 'i'], ['b', 'u', 'y', '=', 'D', 'E', 'C', 'L', '.', 'N', 'P', 'S', 'T'], [⟨['k', 'o', 'p', 'i'], ['b', 'u', 'y'], none⟩, ⟨['k', 'i'], ['D', 'E', 'C', 'L', '.', 'N', 'P', 'S', 'T'], some '='⟩]⟩, ⟨['p', 'a', 'ɨ'], ['P', 'a', 'ë'], [⟨['p', 'a', 'ɨ'], ['P', 'a', 'ë'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "yói=ka"), ("noun", "motó"), ("dependent", "karetera"), ("construction", "relative")] }

def az2025_30a : Datum :=
  { id := "az2025_30a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(30a)"⟩
    reportedIn := none
    language := "east2652"
    primaryText := "nam-i-ce-∅-i kun dureys-umma=tti boon-aa-ɗa."
    glossedTokens := [("nam-i-ce-∅-i", "person-EP-SGV-NOM-EP"), ("kun", "this"), ("dureys-umma=tti", "rich-NMLZ=LOC"), ("boon-aa-ɗa", "proud-M-COP")]
    glossedWords := [⟨['n', 'a', 'm', '-', 'i', '-', 'c', 'e', '-', '∅', '-', 'i'], ['p', 'e', 'r', 's', 'o', 'n', '-', 'E', 'P', '-', 'S', 'G', 'V', '-', 'N', 'O', 'M', '-', 'E', 'P'], [⟨['n', 'a', 'm'], ['p', 'e', 'r', 's', 'o', 'n'], none⟩, ⟨['i'], ['E', 'P'], some '-'⟩, ⟨['c', 'e'], ['S', 'G', 'V'], some '-'⟩, ⟨['∅'], ['N', 'O', 'M'], some '-'⟩, ⟨['i'], ['E', 'P'], some '-'⟩]⟩, ⟨['k', 'u', 'n'], ['t', 'h', 'i', 's'], [⟨['k', 'u', 'n'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['d', 'u', 'r', 'e', 'y', 's', '-', 'u', 'm', 'm', 'a', '=', 't', 't', 'i'], ['r', 'i', 'c', 'h', '-', 'N', 'M', 'L', 'Z', '=', 'L', 'O', 'C'], [⟨['d', 'u', 'r', 'e', 'y', 's'], ['r', 'i', 'c', 'h'], none⟩, ⟨['u', 'm', 'm', 'a'], ['N', 'M', 'L', 'Z'], some '-'⟩, ⟨['t', 't', 'i'], ['L', 'O', 'C'], some '='⟩]⟩, ⟨['b', 'o', 'o', 'n', '-', 'a', 'a', '-', 'ɗ', 'a'], ['p', 'r', 'o', 'u', 'd', '-', 'M', '-', 'C', 'O', 'P'], [⟨['b', 'o', 'o', 'n'], ['p', 'r', 'o', 'u', 'd'], none⟩, ⟨['a', 'a'], ['M'], some '-'⟩, ⟨['ɗ', 'a'], ['C', 'O', 'P'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "boon-aa-ɗa"), ("dependent", "dureys-umma=tti")] }

def az2025_30b : Datum :=
  { id := "az2025_30b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(30b)"⟩
    reportedIn := none
    language := "east2652"
    primaryText := "Muussa nama boon-aa-ɗa."
    glossedTokens := [("Muussa", "Muussa"), ("nama", "person"), ("boon-aa-ɗa", "proud-M-COP")]
    glossedWords := [⟨['M', 'u', 'u', 's', 's', 'a'], ['M', 'u', 'u', 's', 's', 'a'], [⟨['M', 'u', 'u', 's', 's', 'a'], ['M', 'u', 'u', 's', 's', 'a'], none⟩]⟩, ⟨['n', 'a', 'm', 'a'], ['p', 'e', 'r', 's', 'o', 'n'], [⟨['n', 'a', 'm', 'a'], ['p', 'e', 'r', 's', 'o', 'n'], none⟩]⟩, ⟨['b', 'o', 'o', 'n', '-', 'a', 'a', '-', 'ɗ', 'a'], ['p', 'r', 'o', 'u', 'd', '-', 'M', '-', 'C', 'O', 'P'], [⟨['b', 'o', 'o', 'n'], ['p', 'r', 'o', 'u', 'd'], none⟩, ⟨['a', 'a'], ['M'], some '-'⟩, ⟨['ɗ', 'a'], ['C', 'O', 'P'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "boon-aa-ɗa"), ("noun", "nama")] }

def az2025_30c : Datum :=
  { id := "az2025_30c"
    source := ⟨"alexeyenko-zeijlstra-2025", "(30c)"⟩
    reportedIn := none
    language := "east2652"
    primaryText := "Muussa nama dureys-umma=tti boon-aa-ɗa."
    glossedTokens := [("Muussa", "Muussa"), ("nama", "person"), ("dureys-umma=tti", "rich-NMLZ=LOC"), ("boon-aa-ɗa", "proud-M-COP")]
    glossedWords := [⟨['M', 'u', 'u', 's', 's', 'a'], ['M', 'u', 'u', 's', 's', 'a'], [⟨['M', 'u', 'u', 's', 's', 'a'], ['M', 'u', 'u', 's', 's', 'a'], none⟩]⟩, ⟨['n', 'a', 'm', 'a'], ['p', 'e', 'r', 's', 'o', 'n'], [⟨['n', 'a', 'm', 'a'], ['p', 'e', 'r', 's', 'o', 'n'], none⟩]⟩, ⟨['d', 'u', 'r', 'e', 'y', 's', '-', 'u', 'm', 'm', 'a', '=', 't', 't', 'i'], ['r', 'i', 'c', 'h', '-', 'N', 'M', 'L', 'Z', '=', 'L', 'O', 'C'], [⟨['d', 'u', 'r', 'e', 'y', 's'], ['r', 'i', 'c', 'h'], none⟩, ⟨['u', 'm', 'm', 'a'], ['N', 'M', 'L', 'Z'], some '-'⟩, ⟨['t', 't', 'i'], ['L', 'O', 'C'], some '='⟩]⟩, ⟨['b', 'o', 'o', 'n', '-', 'a', 'a', '-', 'ɗ', 'a'], ['p', 'r', 'o', 'u', 'd', '-', 'M', '-', 'C', 'O', 'P'], [⟨['b', 'o', 'o', 'n'], ['p', 'r', 'o', 'u', 'd'], none⟩, ⟨['a', 'a'], ['M'], some '-'⟩, ⟨['ɗ', 'a'], ['C', 'O', 'P'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("head", "boon-aa-ɗa"), ("noun", "nama"), ("dependent", "dureys-umma=tti")] }

def az2025_30d : Datum :=
  { id := "az2025_30d"
    source := ⟨"alexeyenko-zeijlstra-2025", "(30d)"⟩
    reportedIn := none
    language := "east2652"
    primaryText := "Muussa nama dureys-umma=tti boon-∅-u."
    glossedTokens := [("Muussa", "Muussa"), ("nama", "person"), ("dureys-umma=tti", "rich-NMLZ=LOC"), ("boon-∅-u", "proud-3SG.M-DPT")]
    glossedWords := [⟨['M', 'u', 'u', 's', 's', 'a'], ['M', 'u', 'u', 's', 's', 'a'], [⟨['M', 'u', 'u', 's', 's', 'a'], ['M', 'u', 'u', 's', 's', 'a'], none⟩]⟩, ⟨['n', 'a', 'm', 'a'], ['p', 'e', 'r', 's', 'o', 'n'], [⟨['n', 'a', 'm', 'a'], ['p', 'e', 'r', 's', 'o', 'n'], none⟩]⟩, ⟨['d', 'u', 'r', 'e', 'y', 's', '-', 'u', 'm', 'm', 'a', '=', 't', 't', 'i'], ['r', 'i', 'c', 'h', '-', 'N', 'M', 'L', 'Z', '=', 'L', 'O', 'C'], [⟨['d', 'u', 'r', 'e', 'y', 's'], ['r', 'i', 'c', 'h'], none⟩, ⟨['u', 'm', 'm', 'a'], ['N', 'M', 'L', 'Z'], some '-'⟩, ⟨['t', 't', 'i'], ['L', 'O', 'C'], some '='⟩]⟩, ⟨['b', 'o', 'o', 'n', '-', '∅', '-', 'u'], ['p', 'r', 'o', 'u', 'd', '-', '3', 'S', 'G', '.', 'M', '-', 'D', 'P', 'T'], [⟨['b', 'o', 'o', 'n'], ['p', 'r', 'o', 'u', 'd'], none⟩, ⟨['∅'], ['3', 'S', 'G', '.', 'M'], some '-'⟩, ⟨['u'], ['D', 'P', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "boon-∅-u"), ("noun", "nama"), ("dependent", "dureys-umma=tti"), ("construction", "relative")] }

def az2025_31 : Datum :=
  { id := "az2025_31"
    source := ⟨"alexeyenko-zeijlstra-2025", "(31)"⟩
    reportedIn := none
    language := "kala1399"
    primaryText := "nukappiaqqa-p qimmi-mut kii-sit-tu-p uqaluttuar-aa."
    glossedTokens := [("nukappiaqqa-p", "boy-ERG.SG"), ("qimmi-mut", "dog-ALL.SG"), ("kii-sit-tu-p", "bite-CAUS-INTR.PTCP-ERG.SG"), ("uqaluttuar-aa", "tell.about-3SG>3SG.IND")]
    glossedWords := [⟨['n', 'u', 'k', 'a', 'p', 'p', 'i', 'a', 'q', 'q', 'a', '-', 'p'], ['b', 'o', 'y', '-', 'E', 'R', 'G', '.', 'S', 'G'], [⟨['n', 'u', 'k', 'a', 'p', 'p', 'i', 'a', 'q', 'q', 'a'], ['b', 'o', 'y'], none⟩, ⟨['p'], ['E', 'R', 'G', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['q', 'i', 'm', 'm', 'i', '-', 'm', 'u', 't'], ['d', 'o', 'g', '-', 'A', 'L', 'L', '.', 'S', 'G'], [⟨['q', 'i', 'm', 'm', 'i'], ['d', 'o', 'g'], none⟩, ⟨['m', 'u', 't'], ['A', 'L', 'L', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['k', 'i', 'i', '-', 's', 'i', 't', '-', 't', 'u', '-', 'p'], ['b', 'i', 't', 'e', '-', 'C', 'A', 'U', 'S', '-', 'I', 'N', 'T', 'R', '.', 'P', 'T', 'C', 'P', '-', 'E', 'R', 'G', '.', 'S', 'G'], [⟨['k', 'i', 'i'], ['b', 'i', 't', 'e'], none⟩, ⟨['s', 'i', 't'], ['C', 'A', 'U', 'S'], some '-'⟩, ⟨['t', 'u'], ['I', 'N', 'T', 'R', '.', 'P', 'T', 'C', 'P'], some '-'⟩, ⟨['p'], ['E', 'R', 'G', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['u', 'q', 'a', 'l', 'u', 't', 't', 'u', 'a', 'r', '-', 'a', 'a'], ['t', 'e', 'l', 'l', '.', 'a', 'b', 'o', 'u', 't', '-', '3', 'S', 'G', '>', '3', 'S', 'G', '.', 'I', 'N', 'D'], [⟨['u', 'q', 'a', 'l', 'u', 't', 't', 'u', 'a', 'r'], ['t', 'e', 'l', 'l', '.', 'a', 'b', 'o', 'u', 't'], none⟩, ⟨['a', 'a'], ['3', 'S', 'G', '>', '3', 'S', 'G', '.', 'I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "kii-sit-tu-p"), ("noun", "nukappiaqqa-p"), ("dependent", "qimmi-mut")] }

def az2025_32 : Datum :=
  { id := "az2025_32"
    source := ⟨"alexeyenko-zeijlstra-2025", "(32)"⟩
    reportedIn := none
    language := "aton1241"
    primaryText := "naŋʔ=məŋ gore jal=na rak-khal =gaba =aw"
    glossedTokens := [("naŋʔ=məŋ", "2SG=GEN"), ("gore", "horse"), ("jal=na", "run=DAT"), ("rak-khal", "strong-CMPR/SPRL"), ("=gaba", "=ATTR"), ("=aw", "=REF")]
    glossedWords := [⟨['n', 'a', 'ŋ', 'ʔ', '=', 'm', 'ə', 'ŋ'], ['2', 'S', 'G', '=', 'G', 'E', 'N'], [⟨['n', 'a', 'ŋ', 'ʔ'], ['2', 'S', 'G'], none⟩, ⟨['m', 'ə', 'ŋ'], ['G', 'E', 'N'], some '='⟩]⟩, ⟨['g', 'o', 'r', 'e'], ['h', 'o', 'r', 's', 'e'], [⟨['g', 'o', 'r', 'e'], ['h', 'o', 'r', 's', 'e'], none⟩]⟩, ⟨['j', 'a', 'l', '=', 'n', 'a'], ['r', 'u', 'n', '=', 'D', 'A', 'T'], [⟨['j', 'a', 'l'], ['r', 'u', 'n'], none⟩, ⟨['n', 'a'], ['D', 'A', 'T'], some '='⟩]⟩, ⟨['r', 'a', 'k', '-', 'k', 'h', 'a', 'l'], ['s', 't', 'r', 'o', 'n', 'g', '-', 'C', 'M', 'P', 'R', '/', 'S', 'P', 'R', 'L'], [⟨['r', 'a', 'k'], ['s', 't', 'r', 'o', 'n', 'g'], none⟩, ⟨['k', 'h', 'a', 'l'], ['C', 'M', 'P', 'R', '/', 'S', 'P', 'R', 'L'], some '-'⟩]⟩, ⟨['=', 'g', 'a', 'b', 'a'], ['=', 'A', 'T', 'T', 'R'], [⟨['g', 'a', 'b', 'a'], ['A', 'T', 'T', 'R'], some '='⟩]⟩, ⟨['=', 'a', 'w'], ['=', 'R', 'E', 'F'], [⟨['a', 'w'], ['R', 'E', 'F'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "rak-khal"), ("attributivizer", "clitic"), ("noun", "gore"), ("dependent", "jal=na")] }

def az2025_35 : Datum :=
  { id := "az2025_35"
    source := ⟨"alexeyenko-zeijlstra-2025", "(35)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "in praestantibus in re publica gubernanda viris"
    glossedTokens := [("in", "in"), ("praestantibus", "excellent.ABL.M.PL"), ("in", "in"), ("re", "thing"), ("publica", "public"), ("gubernanda", "to.be.governed"), ("viris", "man.ABL.M.PL")]
    glossedWords := [⟨['i', 'n'], ['i', 'n'], [⟨['i', 'n'], ['i', 'n'], none⟩]⟩, ⟨['p', 'r', 'a', 'e', 's', 't', 'a', 'n', 't', 'i', 'b', 'u', 's'], ['e', 'x', 'c', 'e', 'l', 'l', 'e', 'n', 't', '.', 'A', 'B', 'L', '.', 'M', '.', 'P', 'L'], [⟨['p', 'r', 'a', 'e', 's', 't', 'a', 'n', 't', 'i', 'b', 'u', 's'], ['e', 'x', 'c', 'e', 'l', 'l', 'e', 'n', 't', '.', 'A', 'B', 'L', '.', 'M', '.', 'P', 'L'], none⟩]⟩, ⟨['i', 'n'], ['i', 'n'], [⟨['i', 'n'], ['i', 'n'], none⟩]⟩, ⟨['r', 'e'], ['t', 'h', 'i', 'n', 'g'], [⟨['r', 'e'], ['t', 'h', 'i', 'n', 'g'], none⟩]⟩, ⟨['p', 'u', 'b', 'l', 'i', 'c', 'a'], ['p', 'u', 'b', 'l', 'i', 'c'], [⟨['p', 'u', 'b', 'l', 'i', 'c', 'a'], ['p', 'u', 'b', 'l', 'i', 'c'], none⟩]⟩, ⟨['g', 'u', 'b', 'e', 'r', 'n', 'a', 'n', 'd', 'a'], ['t', 'o', '.', 'b', 'e', '.', 'g', 'o', 'v', 'e', 'r', 'n', 'e', 'd'], [⟨['g', 'u', 'b', 'e', 'r', 'n', 'a', 'n', 'd', 'a'], ['t', 'o', '.', 'b', 'e', '.', 'g', 'o', 'v', 'e', 'r', 'n', 'e', 'd'], none⟩]⟩, ⟨['v', 'i', 'r', 'i', 's'], ['m', 'a', 'n', '.', 'A', 'B', 'L', '.', 'M', '.', 'P', 'L'], [⟨['v', 'i', 'r', 'i', 's'], ['m', 'a', 'n', '.', 'A', 'B', 'L', '.', 'M', '.', 'P', 'L'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "praestantibus"), ("noun", "viris"), ("dependent", "re")] }

def az2025_36a : Datum :=
  { id := "az2025_36a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(36a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "nei bravi in matematica studenti"
    glossedTokens := [("nei", "in.the.M.PL"), ("bravi", "good.M.PL"), ("in", "in"), ("matematica", "math"), ("studenti", "student.M.PL")]
    glossedWords := [⟨['n', 'e', 'i'], ['i', 'n', '.', 't', 'h', 'e', '.', 'M', '.', 'P', 'L'], [⟨['n', 'e', 'i'], ['i', 'n', '.', 't', 'h', 'e', '.', 'M', '.', 'P', 'L'], none⟩]⟩, ⟨['b', 'r', 'a', 'v', 'i'], ['g', 'o', 'o', 'd', '.', 'M', '.', 'P', 'L'], [⟨['b', 'r', 'a', 'v', 'i'], ['g', 'o', 'o', 'd', '.', 'M', '.', 'P', 'L'], none⟩]⟩, ⟨['i', 'n'], ['i', 'n'], [⟨['i', 'n'], ['i', 'n'], none⟩]⟩, ⟨['m', 'a', 't', 'e', 'm', 'a', 't', 'i', 'c', 'a'], ['m', 'a', 't', 'h'], [⟨['m', 'a', 't', 'e', 'm', 'a', 't', 'i', 'c', 'a'], ['m', 'a', 't', 'h'], none⟩]⟩, ⟨['s', 't', 'u', 'd', 'e', 'n', 't', 'i'], ['s', 't', 'u', 'd', 'e', 'n', 't', '.', 'M', '.', 'P', 'L'], [⟨['s', 't', 'u', 'd', 'e', 'n', 't', 'i'], ['s', 't', 'u', 'd', 'e', 'n', 't', '.', 'M', '.', 'P', 'L'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("head", "bravi"), ("noun", "studenti"), ("dependent", "in")] }

def az2025_36b : Datum :=
  { id := "az2025_36b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(36b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "negli studenti bravi in matematica"
    glossedTokens := [("negli", "in.the.M.PL"), ("studenti", "student.M.PL"), ("bravi", "good.M.PL"), ("in", "in"), ("matematica", "math")]
    glossedWords := [⟨['n', 'e', 'g', 'l', 'i'], ['i', 'n', '.', 't', 'h', 'e', '.', 'M', '.', 'P', 'L'], [⟨['n', 'e', 'g', 'l', 'i'], ['i', 'n', '.', 't', 'h', 'e', '.', 'M', '.', 'P', 'L'], none⟩]⟩, ⟨['s', 't', 'u', 'd', 'e', 'n', 't', 'i'], ['s', 't', 'u', 'd', 'e', 'n', 't', '.', 'M', '.', 'P', 'L'], [⟨['s', 't', 'u', 'd', 'e', 'n', 't', 'i'], ['s', 't', 'u', 'd', 'e', 'n', 't', '.', 'M', '.', 'P', 'L'], none⟩]⟩, ⟨['b', 'r', 'a', 'v', 'i'], ['g', 'o', 'o', 'd', '.', 'M', '.', 'P', 'L'], [⟨['b', 'r', 'a', 'v', 'i'], ['g', 'o', 'o', 'd', '.', 'M', '.', 'P', 'L'], none⟩]⟩, ⟨['i', 'n'], ['i', 'n'], [⟨['i', 'n'], ['i', 'n'], none⟩]⟩, ⟨['m', 'a', 't', 'e', 'm', 'a', 't', 'i', 'c', 'a'], ['m', 'a', 't', 'h'], [⟨['m', 'a', 't', 'e', 'm', 'a', 't', 'i', 'c', 'a'], ['m', 'a', 't', 'h'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "bravi"), ("noun", "studenti"), ("dependent", "in")] }

def az2025_36c : Datum :=
  { id := "az2025_36c"
    source := ⟨"alexeyenko-zeijlstra-2025", "(36c)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "nei bravi studenti"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "bravi"), ("noun", "studenti")] }

def az2025_36d : Datum :=
  { id := "az2025_36d"
    source := ⟨"alexeyenko-zeijlstra-2025", "(36d)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "negli studenti bravi"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("head", "bravi"), ("noun", "studenti")] }

def az2025_37a : Datum :=
  { id := "az2025_37a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(37a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "(Aftos) ine perifan-os."
    glossedTokens := [("(Aftos)", "he"), ("ine", "is"), ("perifan-os", "proud-M.SG.NOM")]
    glossedWords := [⟨['(', 'A', 'f', 't', 'o', 's', ')'], ['h', 'e'], [⟨['A', 'f', 't', 'o', 's'], ['h', 'e'], none⟩]⟩, ⟨['i', 'n', 'e'], ['i', 's'], [⟨['i', 'n', 'e'], ['i', 's'], none⟩]⟩, ⟨['p', 'e', 'r', 'i', 'f', 'a', 'n', '-', 'o', 's'], ['p', 'r', 'o', 'u', 'd', '-', 'M', '.', 'S', 'G', '.', 'N', 'O', 'M'], [⟨['p', 'e', 'r', 'i', 'f', 'a', 'n'], ['p', 'r', 'o', 'u', 'd'], none⟩, ⟨['o', 's'], ['M', '.', 'S', 'G', '.', 'N', 'O', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("(Aftos) ine perifan.", .ungrammatical)]
    readings := []
    paperFeatures := [("head", "perifan-os"), ("marker", "agreement")] }

def az2025_37b : Datum :=
  { id := "az2025_37b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(37b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "o perifan-os pateras"
    glossedTokens := [("o", "the"), ("perifan-os", "proud-M.SG.NOM"), ("pateras", "father")]
    glossedWords := [⟨['o'], ['t', 'h', 'e'], [⟨['o'], ['t', 'h', 'e'], none⟩]⟩, ⟨['p', 'e', 'r', 'i', 'f', 'a', 'n', '-', 'o', 's'], ['p', 'r', 'o', 'u', 'd', '-', 'M', '.', 'S', 'G', '.', 'N', 'O', 'M'], [⟨['p', 'e', 'r', 'i', 'f', 'a', 'n'], ['p', 'r', 'o', 'u', 'd'], none⟩, ⟨['o', 's'], ['M', '.', 'S', 'G', '.', 'N', 'O', 'M'], some '-'⟩]⟩, ⟨['p', 'a', 't', 'e', 'r', 'a', 's'], ['f', 'a', 't', 'h', 'e', 'r'], [⟨['p', 'a', 't', 'e', 'r', 'a', 's'], ['f', 'a', 't', 'h', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("o perifan pateras", .ungrammatical)]
    readings := []
    paperFeatures := [("head", "perifan-os"), ("marker", "agreement"), ("noun", "pateras")] }

def az2025_38a : Datum :=
  { id := "az2025_38a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(38a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Er ist stolz."
    glossedTokens := [("Er", "he"), ("ist", "is"), ("stolz", "proud")]
    glossedWords := [⟨['E', 'r'], ['h', 'e'], [⟨['E', 'r'], ['h', 'e'], none⟩]⟩, ⟨['i', 's', 't'], ['i', 's'], [⟨['i', 's', 't'], ['i', 's'], none⟩]⟩, ⟨['s', 't', 'o', 'l', 'z'], ['p', 'r', 'o', 'u', 'd'], [⟨['s', 't', 'o', 'l', 'z'], ['p', 'r', 'o', 'u', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Er ist stolz-er.", .ungrammatical)]
    readings := []
    paperFeatures := [("head", "stolz"), ("marker", "bare")] }

def az2025_38b : Datum :=
  { id := "az2025_38b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(38b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "stolz-er Vater"
    glossedTokens := [("stolz-er", "proud-M.SG.NOM.STRONG"), ("Vater", "father")]
    glossedWords := [⟨['s', 't', 'o', 'l', 'z', '-', 'e', 'r'], ['p', 'r', 'o', 'u', 'd', '-', 'M', '.', 'S', 'G', '.', 'N', 'O', 'M', '.', 'S', 'T', 'R', 'O', 'N', 'G'], [⟨['s', 't', 'o', 'l', 'z'], ['p', 'r', 'o', 'u', 'd'], none⟩, ⟨['e', 'r'], ['M', '.', 'S', 'G', '.', 'N', 'O', 'M', '.', 'S', 'T', 'R', 'O', 'N', 'G'], some '-'⟩]⟩, ⟨['V', 'a', 't', 'e', 'r'], ['f', 'a', 't', 'h', 'e', 'r'], [⟨['V', 'a', 't', 'e', 'r'], ['f', 'a', 't', 'h', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("stolz Vater", .ungrammatical)]
    readings := []
    paperFeatures := [("head", "stolz-er"), ("marker", "agreement"), ("noun", "Vater")] }

def az2025_39a : Datum :=
  { id := "az2025_39a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(39a)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Ona umn-aja."
    glossedTokens := [("Ona", "she"), ("umn-aja", "smart-LONG.F.SG.NOM")]
    glossedWords := [⟨['O', 'n', 'a'], ['s', 'h', 'e'], [⟨['O', 'n', 'a'], ['s', 'h', 'e'], none⟩]⟩, ⟨['u', 'm', 'n', '-', 'a', 'j', 'a'], ['s', 'm', 'a', 'r', 't', '-', 'L', 'O', 'N', 'G', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M'], [⟨['u', 'm', 'n'], ['s', 'm', 'a', 'r', 't'], none⟩, ⟨['a', 'j', 'a'], ['L', 'O', 'N', 'G', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Ona umn-a.", .acceptable)]
    readings := []
    paperFeatures := [("head", "umn-aja"), ("form", "long")] }

def az2025_39b : Datum :=
  { id := "az2025_39b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(39b)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "umn-aja d'evočka"
    glossedTokens := [("umn-aja", "smart-LONG"), ("d'evočka", "girl")]
    glossedWords := [⟨['u', 'm', 'n', '-', 'a', 'j', 'a'], ['s', 'm', 'a', 'r', 't', '-', 'L', 'O', 'N', 'G'], [⟨['u', 'm', 'n'], ['s', 'm', 'a', 'r', 't'], none⟩, ⟨['a', 'j', 'a'], ['L', 'O', 'N', 'G'], some '-'⟩]⟩, ⟨['d', '\'', 'e', 'v', 'o', 'č', 'k', 'a'], ['g', 'i', 'r', 'l'], [⟨['d', '\'', 'e', 'v', 'o', 'č', 'k', 'a'], ['g', 'i', 'r', 'l'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("umn-a d'evočka", .ungrammatical)]
    readings := []
    paperFeatures := [("head", "umn-aja"), ("form", "long"), ("noun", "d'evočka")] }

def az2025_40b : Datum :=
  { id := "az2025_40b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(40b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Jón er af syni sínum stolt-ur."
    glossedTokens := [("Jón", "Jón"), ("er", "is"), ("af", "on"), ("syni", "son.DAT"), ("sínum", "his.DAT"), ("stolt-ur", "proud-M.SG.NOM.STRONG")]
    glossedWords := [⟨['J', 'ó', 'n'], ['J', 'ó', 'n'], [⟨['J', 'ó', 'n'], ['J', 'ó', 'n'], none⟩]⟩, ⟨['e', 'r'], ['i', 's'], [⟨['e', 'r'], ['i', 's'], none⟩]⟩, ⟨['a', 'f'], ['o', 'n'], [⟨['a', 'f'], ['o', 'n'], none⟩]⟩, ⟨['s', 'y', 'n', 'i'], ['s', 'o', 'n', '.', 'D', 'A', 'T'], [⟨['s', 'y', 'n', 'i'], ['s', 'o', 'n', '.', 'D', 'A', 'T'], none⟩]⟩, ⟨['s', 'í', 'n', 'u', 'm'], ['h', 'i', 's', '.', 'D', 'A', 'T'], [⟨['s', 'í', 'n', 'u', 'm'], ['h', 'i', 's', '.', 'D', 'A', 'T'], none⟩]⟩, ⟨['s', 't', 'o', 'l', 't', '-', 'u', 'r'], ['p', 'r', 'o', 'u', 'd', '-', 'M', '.', 'S', 'G', '.', 'N', 'O', 'M', '.', 'S', 'T', 'R', 'O', 'N', 'G'], [⟨['s', 't', 'o', 'l', 't'], ['p', 'r', 'o', 'u', 'd'], none⟩, ⟨['u', 'r'], ['M', '.', 'S', 'G', '.', 'N', 'O', 'M', '.', 'S', 'T', 'R', 'O', 'N', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "stolt-ur"), ("dependent", "af")] }

def az2025_41b : Datum :=
  { id := "az2025_41b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(41b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "af syni sínum stolt-ur faðir"
    glossedTokens := [("af", "on"), ("syni", "son.DAT"), ("sínum", "his.DAT"), ("stolt-ur", "proud-M.SG.NOM.STRONG"), ("faðir", "father")]
    glossedWords := [⟨['a', 'f'], ['o', 'n'], [⟨['a', 'f'], ['o', 'n'], none⟩]⟩, ⟨['s', 'y', 'n', 'i'], ['s', 'o', 'n', '.', 'D', 'A', 'T'], [⟨['s', 'y', 'n', 'i'], ['s', 'o', 'n', '.', 'D', 'A', 'T'], none⟩]⟩, ⟨['s', 'í', 'n', 'u', 'm'], ['h', 'i', 's', '.', 'D', 'A', 'T'], [⟨['s', 'í', 'n', 'u', 'm'], ['h', 'i', 's', '.', 'D', 'A', 'T'], none⟩]⟩, ⟨['s', 't', 'o', 'l', 't', '-', 'u', 'r'], ['p', 'r', 'o', 'u', 'd', '-', 'M', '.', 'S', 'G', '.', 'N', 'O', 'M', '.', 'S', 'T', 'R', 'O', 'N', 'G'], [⟨['s', 't', 'o', 'l', 't'], ['p', 'r', 'o', 'u', 'd'], none⟩, ⟨['u', 'r'], ['M', '.', 'S', 'G', '.', 'N', 'O', 'M', '.', 'S', 'T', 'R', 'O', 'N', 'G'], some '-'⟩]⟩, ⟨['f', 'a', 'ð', 'i', 'r'], ['f', 'a', 't', 'h', 'e', 'r'], [⟨['f', 'a', 'ð', 'i', 'r'], ['f', 'a', 't', 'h', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "stolt-ur"), ("noun", "faðir"), ("dependent", "af")] }

def az2025_42a : Datum :=
  { id := "az2025_42a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(42a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Jón er stolt-ur."
    glossedTokens := [("Jón", "Jón"), ("er", "is"), ("stolt-ur", "proud-M.SG.NOM.STRONG")]
    glossedWords := [⟨['J', 'ó', 'n'], ['J', 'ó', 'n'], [⟨['J', 'ó', 'n'], ['J', 'ó', 'n'], none⟩]⟩, ⟨['e', 'r'], ['i', 's'], [⟨['e', 'r'], ['i', 's'], none⟩]⟩, ⟨['s', 't', 'o', 'l', 't', '-', 'u', 'r'], ['p', 'r', 'o', 'u', 'd', '-', 'M', '.', 'S', 'G', '.', 'N', 'O', 'M', '.', 'S', 'T', 'R', 'O', 'N', 'G'], [⟨['s', 't', 'o', 'l', 't'], ['p', 'r', 'o', 'u', 'd'], none⟩, ⟨['u', 'r'], ['M', '.', 'S', 'G', '.', 'N', 'O', 'M', '.', 'S', 'T', 'R', 'O', 'N', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Jón er stolt-i.", .ungrammatical)]
    readings := []
    paperFeatures := [("head", "stolt-ur"), ("form", "strong")] }

def az2025_42b : Datum :=
  { id := "az2025_42b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(42b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "stolt-ur faðir"
    glossedTokens := [("stolt-ur", "proud-M.SG.NOM.STRONG"), ("faðir", "father")]
    glossedWords := [⟨['s', 't', 'o', 'l', 't', '-', 'u', 'r'], ['p', 'r', 'o', 'u', 'd', '-', 'M', '.', 'S', 'G', '.', 'N', 'O', 'M', '.', 'S', 'T', 'R', 'O', 'N', 'G'], [⟨['s', 't', 'o', 'l', 't'], ['p', 'r', 'o', 'u', 'd'], none⟩, ⟨['u', 'r'], ['M', '.', 'S', 'G', '.', 'N', 'O', 'M', '.', 'S', 'T', 'R', 'O', 'N', 'G'], some '-'⟩]⟩, ⟨['f', 'a', 'ð', 'i', 'r'], ['f', 'a', 't', 'h', 'e', 'r'], [⟨['f', 'a', 'ð', 'i', 'r'], ['f', 'a', 't', 'h', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("stolt-i faðir", .ungrammatical)]
    readings := []
    paperFeatures := [("head", "stolt-ur"), ("form", "strong"), ("definiteness", "indefinite"), ("noun", "faðir")] }

def az2025_42c : Datum :=
  { id := "az2025_42c"
    source := ⟨"alexeyenko-zeijlstra-2025", "(42c)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "stolt-i faðir-inn"
    glossedTokens := [("stolt-i", "proud-M.SG.NOM.WEAK"), ("faðir-inn", "father-DEF.M.SG")]
    glossedWords := [⟨['s', 't', 'o', 'l', 't', '-', 'i'], ['p', 'r', 'o', 'u', 'd', '-', 'M', '.', 'S', 'G', '.', 'N', 'O', 'M', '.', 'W', 'E', 'A', 'K'], [⟨['s', 't', 'o', 'l', 't'], ['p', 'r', 'o', 'u', 'd'], none⟩, ⟨['i'], ['M', '.', 'S', 'G', '.', 'N', 'O', 'M', '.', 'W', 'E', 'A', 'K'], some '-'⟩]⟩, ⟨['f', 'a', 'ð', 'i', 'r', '-', 'i', 'n', 'n'], ['f', 'a', 't', 'h', 'e', 'r', '-', 'D', 'E', 'F', '.', 'M', '.', 'S', 'G'], [⟨['f', 'a', 'ð', 'i', 'r'], ['f', 'a', 't', 'h', 'e', 'r'], none⟩, ⟨['i', 'n', 'n'], ['D', 'E', 'F', '.', 'M', '.', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "stolt-i"), ("form", "weak"), ("definiteness", "definite"), ("noun", "faðir-inn")] }

def az2025_42d : Datum :=
  { id := "az2025_42d"
    source := ⟨"alexeyenko-zeijlstra-2025", "(42d)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "stolt-ur faðir-inn"
    glossedTokens := [("stolt-ur", "proud-M.SG.NOM.STRONG"), ("faðir-inn", "father-DEF.M.SG")]
    glossedWords := [⟨['s', 't', 'o', 'l', 't', '-', 'u', 'r'], ['p', 'r', 'o', 'u', 'd', '-', 'M', '.', 'S', 'G', '.', 'N', 'O', 'M', '.', 'S', 'T', 'R', 'O', 'N', 'G'], [⟨['s', 't', 'o', 'l', 't'], ['p', 'r', 'o', 'u', 'd'], none⟩, ⟨['u', 'r'], ['M', '.', 'S', 'G', '.', 'N', 'O', 'M', '.', 'S', 'T', 'R', 'O', 'N', 'G'], some '-'⟩]⟩, ⟨['f', 'a', 'ð', 'i', 'r', '-', 'i', 'n', 'n'], ['f', 'a', 't', 'h', 'e', 'r', '-', 'D', 'E', 'F', '.', 'M', '.', 'S', 'G'], [⟨['f', 'a', 'ð', 'i', 'r'], ['f', 'a', 't', 'h', 'e', 'r'], none⟩, ⟨['i', 'n', 'n'], ['D', 'E', 'F', '.', 'M', '.', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "stolt-ur"), ("form", "strong"), ("definiteness", "definite"), ("reading", "nonrestrictive"), ("noun", "faðir-inn")] }

def az2025_43a : Datum :=
  { id := "az2025_43a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(43a)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Goran je lijep."
    glossedTokens := [("Goran", "Goran"), ("je", "is"), ("lijep", "nice.SHORT")]
    glossedWords := [⟨['G', 'o', 'r', 'a', 'n'], ['G', 'o', 'r', 'a', 'n'], [⟨['G', 'o', 'r', 'a', 'n'], ['G', 'o', 'r', 'a', 'n'], none⟩]⟩, ⟨['j', 'e'], ['i', 's'], [⟨['j', 'e'], ['i', 's'], none⟩]⟩, ⟨['l', 'i', 'j', 'e', 'p'], ['n', 'i', 'c', 'e', '.', 'S', 'H', 'O', 'R', 'T'], [⟨['l', 'i', 'j', 'e', 'p'], ['n', 'i', 'c', 'e', '.', 'S', 'H', 'O', 'R', 'T'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Goran je lijepi.", .ungrammatical)]
    readings := []
    paperFeatures := [("head", "lijep"), ("form", "short")] }

def az2025_43b : Datum :=
  { id := "az2025_43b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(43b)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "lijep momak"
    glossedTokens := [("lijep", "nice.SHORT"), ("momak", "young.man")]
    glossedWords := [⟨['l', 'i', 'j', 'e', 'p'], ['n', 'i', 'c', 'e', '.', 'S', 'H', 'O', 'R', 'T'], [⟨['l', 'i', 'j', 'e', 'p'], ['n', 'i', 'c', 'e', '.', 'S', 'H', 'O', 'R', 'T'], none⟩]⟩, ⟨['m', 'o', 'm', 'a', 'k'], ['y', 'o', 'u', 'n', 'g', '.', 'm', 'a', 'n'], [⟨['m', 'o', 'm', 'a', 'k'], ['y', 'o', 'u', 'n', 'g', '.', 'm', 'a', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "lijep"), ("form", "short"), ("definiteness", "indefinite"), ("noun", "momak")] }

def az2025_43c : Datum :=
  { id := "az2025_43c"
    source := ⟨"alexeyenko-zeijlstra-2025", "(43c)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "lijepi momak"
    glossedTokens := [("lijepi", "nice.LONG"), ("momak", "young.man")]
    glossedWords := [⟨['l', 'i', 'j', 'e', 'p', 'i'], ['n', 'i', 'c', 'e', '.', 'L', 'O', 'N', 'G'], [⟨['l', 'i', 'j', 'e', 'p', 'i'], ['n', 'i', 'c', 'e', '.', 'L', 'O', 'N', 'G'], none⟩]⟩, ⟨['m', 'o', 'm', 'a', 'k'], ['y', 'o', 'u', 'n', 'g', '.', 'm', 'a', 'n'], [⟨['m', 'o', 'm', 'a', 'k'], ['y', 'o', 'u', 'n', 'g', '.', 'm', 'a', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "lijepi"), ("form", "long"), ("definiteness", "definite"), ("noun", "momak")] }

def az2025_62 : Datum :=
  { id := "az2025_62"
    source := ⟨"alexeyenko-zeijlstra-2025", "(62)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Maria ist stolz auf ihre Tochter."
    glossedTokens := [("Maria", "Maria"), ("ist", "is"), ("stolz", "proud"), ("auf", "on"), ("ihre", "her"), ("Tochter", "daughter")]
    glossedWords := [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['i', 's', 't'], ['i', 's'], [⟨['i', 's', 't'], ['i', 's'], none⟩]⟩, ⟨['s', 't', 'o', 'l', 'z'], ['p', 'r', 'o', 'u', 'd'], [⟨['s', 't', 'o', 'l', 'z'], ['p', 'r', 'o', 'u', 'd'], none⟩]⟩, ⟨['a', 'u', 'f'], ['o', 'n'], [⟨['a', 'u', 'f'], ['o', 'n'], none⟩]⟩, ⟨['i', 'h', 'r', 'e'], ['h', 'e', 'r'], [⟨['i', 'h', 'r', 'e'], ['h', 'e', 'r'], none⟩]⟩, ⟨['T', 'o', 'c', 'h', 't', 'e', 'r'], ['d', 'a', 'u', 'g', 'h', 't', 'e', 'r'], [⟨['T', 'o', 'c', 'h', 't', 'e', 'r'], ['d', 'a', 'u', 'g', 'h', 't', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Maria ist auf ihre Tochter stolz.", .acceptable)]
    readings := []
    paperFeatures := [("head", "stolz"), ("dependent", "auf")] }

def az2025_63a : Datum :=
  { id := "az2025_63a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(63a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "die stolz auf ihre Tochter-e Mutter"
    glossedTokens := [("die", "the"), ("stolz", "proud"), ("auf", "on"), ("ihre", "her"), ("Tochter-e", "daughter-ATTR.F.SG.NOM"), ("Mutter", "mother")]
    glossedWords := [⟨['d', 'i', 'e'], ['t', 'h', 'e'], [⟨['d', 'i', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['s', 't', 'o', 'l', 'z'], ['p', 'r', 'o', 'u', 'd'], [⟨['s', 't', 'o', 'l', 'z'], ['p', 'r', 'o', 'u', 'd'], none⟩]⟩, ⟨['a', 'u', 'f'], ['o', 'n'], [⟨['a', 'u', 'f'], ['o', 'n'], none⟩]⟩, ⟨['i', 'h', 'r', 'e'], ['h', 'e', 'r'], [⟨['i', 'h', 'r', 'e'], ['h', 'e', 'r'], none⟩]⟩, ⟨['T', 'o', 'c', 'h', 't', 'e', 'r', '-', 'e'], ['d', 'a', 'u', 'g', 'h', 't', 'e', 'r', '-', 'A', 'T', 'T', 'R', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M'], [⟨['T', 'o', 'c', 'h', 't', 'e', 'r'], ['d', 'a', 'u', 'g', 'h', 't', 'e', 'r'], none⟩, ⟨['e'], ['A', 'T', 'T', 'R', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M'], some '-'⟩]⟩, ⟨['M', 'u', 't', 't', 'e', 'r'], ['m', 'o', 't', 'h', 'e', 'r'], [⟨['M', 'u', 't', 't', 'e', 'r'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("head", "stolz"), ("attributivizer", "affix"), ("noun", "Mutter"), ("dependent", "auf")] }

def az2025_63b : Datum :=
  { id := "az2025_63b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(63b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "die auf ihre Tochter stolz-e Mutter"
    glossedTokens := [("die", "the"), ("auf", "on"), ("ihre", "her"), ("Tochter", "daughter"), ("stolz-e", "proud-ATTR.F.SG.NOM"), ("Mutter", "mother")]
    glossedWords := [⟨['d', 'i', 'e'], ['t', 'h', 'e'], [⟨['d', 'i', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['a', 'u', 'f'], ['o', 'n'], [⟨['a', 'u', 'f'], ['o', 'n'], none⟩]⟩, ⟨['i', 'h', 'r', 'e'], ['h', 'e', 'r'], [⟨['i', 'h', 'r', 'e'], ['h', 'e', 'r'], none⟩]⟩, ⟨['T', 'o', 'c', 'h', 't', 'e', 'r'], ['d', 'a', 'u', 'g', 'h', 't', 'e', 'r'], [⟨['T', 'o', 'c', 'h', 't', 'e', 'r'], ['d', 'a', 'u', 'g', 'h', 't', 'e', 'r'], none⟩]⟩, ⟨['s', 't', 'o', 'l', 'z', '-', 'e'], ['p', 'r', 'o', 'u', 'd', '-', 'A', 'T', 'T', 'R', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M'], [⟨['s', 't', 'o', 'l', 'z'], ['p', 'r', 'o', 'u', 'd'], none⟩, ⟨['e'], ['A', 'T', 'T', 'R', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M'], some '-'⟩]⟩, ⟨['M', 'u', 't', 't', 'e', 'r'], ['m', 'o', 't', 'h', 'e', 'r'], [⟨['M', 'u', 't', 't', 'e', 'r'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "stolz-e"), ("attributivizer", "affix"), ("noun", "Mutter"), ("dependent", "auf")] }

def az2025_66a : Datum :=
  { id := "az2025_66a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(66a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "een op haar moeder trots-e vrouw"
    glossedTokens := [("een", "a"), ("op", "of"), ("haar", "her"), ("moeder", "mother"), ("trots-e", "proud-ATTR"), ("vrouw", "woman")]
    glossedWords := [⟨['e', 'e', 'n'], ['a'], [⟨['e', 'e', 'n'], ['a'], none⟩]⟩, ⟨['o', 'p'], ['o', 'f'], [⟨['o', 'p'], ['o', 'f'], none⟩]⟩, ⟨['h', 'a', 'a', 'r'], ['h', 'e', 'r'], [⟨['h', 'a', 'a', 'r'], ['h', 'e', 'r'], none⟩]⟩, ⟨['m', 'o', 'e', 'd', 'e', 'r'], ['m', 'o', 't', 'h', 'e', 'r'], [⟨['m', 'o', 'e', 'd', 'e', 'r'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩]⟩, ⟨['t', 'r', 'o', 't', 's', '-', 'e'], ['p', 'r', 'o', 'u', 'd', '-', 'A', 'T', 'T', 'R'], [⟨['t', 'r', 'o', 't', 's'], ['p', 'r', 'o', 'u', 'd'], none⟩, ⟨['e'], ['A', 'T', 'T', 'R'], some '-'⟩]⟩, ⟨['v', 'r', 'o', 'u', 'w'], ['w', 'o', 'm', 'a', 'n'], [⟨['v', 'r', 'o', 'u', 'w'], ['w', 'o', 'm', 'a', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "trots-e"), ("attributivizer", "affix"), ("noun", "vrouw"), ("dependent", "op")] }

def az2025_66b : Datum :=
  { id := "az2025_66b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(66b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "een trots op haar moeder-e vrouw"
    glossedTokens := [("een", "a"), ("trots", "proud"), ("op", "of"), ("haar", "her"), ("moeder-e", "mother-ATTR"), ("vrouw", "woman")]
    glossedWords := [⟨['e', 'e', 'n'], ['a'], [⟨['e', 'e', 'n'], ['a'], none⟩]⟩, ⟨['t', 'r', 'o', 't', 's'], ['p', 'r', 'o', 'u', 'd'], [⟨['t', 'r', 'o', 't', 's'], ['p', 'r', 'o', 'u', 'd'], none⟩]⟩, ⟨['o', 'p'], ['o', 'f'], [⟨['o', 'p'], ['o', 'f'], none⟩]⟩, ⟨['h', 'a', 'a', 'r'], ['h', 'e', 'r'], [⟨['h', 'a', 'a', 'r'], ['h', 'e', 'r'], none⟩]⟩, ⟨['m', 'o', 'e', 'd', 'e', 'r', '-', 'e'], ['m', 'o', 't', 'h', 'e', 'r', '-', 'A', 'T', 'T', 'R'], [⟨['m', 'o', 'e', 'd', 'e', 'r'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['e'], ['A', 'T', 'T', 'R'], some '-'⟩]⟩, ⟨['v', 'r', 'o', 'u', 'w'], ['w', 'o', 'm', 'a', 'n'], [⟨['v', 'r', 'o', 'u', 'w'], ['w', 'o', 'm', 'a', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("head", "trots"), ("attributivizer", "affix"), ("noun", "vrouw"), ("dependent", "op")] }

def az2025_66c : Datum :=
  { id := "az2025_66c"
    source := ⟨"alexeyenko-zeijlstra-2025", "(66c)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "een trots-e op haar moeder vrouw"
    glossedTokens := [("een", "a"), ("trots-e", "proud-ATTR"), ("op", "of"), ("haar", "her"), ("moeder", "mother"), ("vrouw", "woman")]
    glossedWords := [⟨['e', 'e', 'n'], ['a'], [⟨['e', 'e', 'n'], ['a'], none⟩]⟩, ⟨['t', 'r', 'o', 't', 's', '-', 'e'], ['p', 'r', 'o', 'u', 'd', '-', 'A', 'T', 'T', 'R'], [⟨['t', 'r', 'o', 't', 's'], ['p', 'r', 'o', 'u', 'd'], none⟩, ⟨['e'], ['A', 'T', 'T', 'R'], some '-'⟩]⟩, ⟨['o', 'p'], ['o', 'f'], [⟨['o', 'p'], ['o', 'f'], none⟩]⟩, ⟨['h', 'a', 'a', 'r'], ['h', 'e', 'r'], [⟨['h', 'a', 'a', 'r'], ['h', 'e', 'r'], none⟩]⟩, ⟨['m', 'o', 'e', 'd', 'e', 'r'], ['m', 'o', 't', 'h', 'e', 'r'], [⟨['m', 'o', 'e', 'd', 'e', 'r'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩]⟩, ⟨['v', 'r', 'o', 'u', 'w'], ['w', 'o', 'm', 'a', 'n'], [⟨['v', 'r', 'o', 'u', 'w'], ['w', 'o', 'm', 'a', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("head", "trots-e"), ("attributivizer", "affix"), ("noun", "vrouw"), ("dependent", "op")] }

def az2025_67a : Datum :=
  { id := "az2025_67a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(67a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "een op haar vader trots-∅ kind"
    glossedTokens := [("een", "a"), ("op", "of"), ("haar", "her"), ("vader", "father"), ("trots-∅", "proud-ATTR"), ("kind", "child")]
    glossedWords := [⟨['e', 'e', 'n'], ['a'], [⟨['e', 'e', 'n'], ['a'], none⟩]⟩, ⟨['o', 'p'], ['o', 'f'], [⟨['o', 'p'], ['o', 'f'], none⟩]⟩, ⟨['h', 'a', 'a', 'r'], ['h', 'e', 'r'], [⟨['h', 'a', 'a', 'r'], ['h', 'e', 'r'], none⟩]⟩, ⟨['v', 'a', 'd', 'e', 'r'], ['f', 'a', 't', 'h', 'e', 'r'], [⟨['v', 'a', 'd', 'e', 'r'], ['f', 'a', 't', 'h', 'e', 'r'], none⟩]⟩, ⟨['t', 'r', 'o', 't', 's', '-', '∅'], ['p', 'r', 'o', 'u', 'd', '-', 'A', 'T', 'T', 'R'], [⟨['t', 'r', 'o', 't', 's'], ['p', 'r', 'o', 'u', 'd'], none⟩, ⟨['∅'], ['A', 'T', 'T', 'R'], some '-'⟩]⟩, ⟨['k', 'i', 'n', 'd'], ['c', 'h', 'i', 'l', 'd'], [⟨['k', 'i', 'n', 'd'], ['c', 'h', 'i', 'l', 'd'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "trots-∅"), ("attributivizer", "null"), ("noun", "kind"), ("dependent", "op")] }

def az2025_67b : Datum :=
  { id := "az2025_67b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(67b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "een trots op haar vader-∅ kind"
    glossedTokens := [("een", "a"), ("trots", "proud"), ("op", "of"), ("haar", "her"), ("vader-∅", "father-ATTR"), ("kind", "child")]
    glossedWords := [⟨['e', 'e', 'n'], ['a'], [⟨['e', 'e', 'n'], ['a'], none⟩]⟩, ⟨['t', 'r', 'o', 't', 's'], ['p', 'r', 'o', 'u', 'd'], [⟨['t', 'r', 'o', 't', 's'], ['p', 'r', 'o', 'u', 'd'], none⟩]⟩, ⟨['o', 'p'], ['o', 'f'], [⟨['o', 'p'], ['o', 'f'], none⟩]⟩, ⟨['h', 'a', 'a', 'r'], ['h', 'e', 'r'], [⟨['h', 'a', 'a', 'r'], ['h', 'e', 'r'], none⟩]⟩, ⟨['v', 'a', 'd', 'e', 'r', '-', '∅'], ['f', 'a', 't', 'h', 'e', 'r', '-', 'A', 'T', 'T', 'R'], [⟨['v', 'a', 'd', 'e', 'r'], ['f', 'a', 't', 'h', 'e', 'r'], none⟩, ⟨['∅'], ['A', 'T', 'T', 'R'], some '-'⟩]⟩, ⟨['k', 'i', 'n', 'd'], ['c', 'h', 'i', 'l', 'd'], [⟨['k', 'i', 'n', 'd'], ['c', 'h', 'i', 'l', 'd'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("head", "trots"), ("attributivizer", "null"), ("noun", "kind"), ("dependent", "op")] }

def az2025_67c : Datum :=
  { id := "az2025_67c"
    source := ⟨"alexeyenko-zeijlstra-2025", "(67c)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "een trots-∅ op haar vader kind"
    glossedTokens := [("een", "a"), ("trots-∅", "proud-ATTR"), ("op", "of"), ("haar", "her"), ("vader", "father"), ("kind", "child")]
    glossedWords := [⟨['e', 'e', 'n'], ['a'], [⟨['e', 'e', 'n'], ['a'], none⟩]⟩, ⟨['t', 'r', 'o', 't', 's', '-', '∅'], ['p', 'r', 'o', 'u', 'd', '-', 'A', 'T', 'T', 'R'], [⟨['t', 'r', 'o', 't', 's'], ['p', 'r', 'o', 'u', 'd'], none⟩, ⟨['∅'], ['A', 'T', 'T', 'R'], some '-'⟩]⟩, ⟨['o', 'p'], ['o', 'f'], [⟨['o', 'p'], ['o', 'f'], none⟩]⟩, ⟨['h', 'a', 'a', 'r'], ['h', 'e', 'r'], [⟨['h', 'a', 'a', 'r'], ['h', 'e', 'r'], none⟩]⟩, ⟨['v', 'a', 'd', 'e', 'r'], ['f', 'a', 't', 'h', 'e', 'r'], [⟨['v', 'a', 'd', 'e', 'r'], ['f', 'a', 't', 'h', 'e', 'r'], none⟩]⟩, ⟨['k', 'i', 'n', 'd'], ['c', 'h', 'i', 'l', 'd'], [⟨['k', 'i', 'n', 'd'], ['c', 'h', 'i', 'l', 'd'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("head", "trots-∅"), ("attributivizer", "null"), ("noun", "kind"), ("dependent", "op")] }

def az2025_68a : Datum :=
  { id := "az2025_68a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(68a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "een groot genoeg-∅ kind"
    glossedTokens := [("een", "a"), ("groot", "big"), ("genoeg-∅", "enough-ATTR"), ("kind", "child")]
    glossedWords := [⟨['e', 'e', 'n'], ['a'], [⟨['e', 'e', 'n'], ['a'], none⟩]⟩, ⟨['g', 'r', 'o', 'o', 't'], ['b', 'i', 'g'], [⟨['g', 'r', 'o', 'o', 't'], ['b', 'i', 'g'], none⟩]⟩, ⟨['g', 'e', 'n', 'o', 'e', 'g', '-', '∅'], ['e', 'n', 'o', 'u', 'g', 'h', '-', 'A', 'T', 'T', 'R'], [⟨['g', 'e', 'n', 'o', 'e', 'g'], ['e', 'n', 'o', 'u', 'g', 'h'], none⟩, ⟨['∅'], ['A', 'T', 'T', 'R'], some '-'⟩]⟩, ⟨['k', 'i', 'n', 'd'], ['c', 'h', 'i', 'l', 'd'], [⟨['k', 'i', 'n', 'd'], ['c', 'h', 'i', 'l', 'd'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "groot"), ("attributivizer", "null"), ("noun", "kind"), ("degree", "genoeg-∅")] }

def az2025_68b : Datum :=
  { id := "az2025_68b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(68b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "een groot genoeg-e vrouw"
    glossedTokens := [("een", "a"), ("groot", "big"), ("genoeg-e", "enough-ATTR"), ("vrouw", "woman")]
    glossedWords := [⟨['e', 'e', 'n'], ['a'], [⟨['e', 'e', 'n'], ['a'], none⟩]⟩, ⟨['g', 'r', 'o', 'o', 't'], ['b', 'i', 'g'], [⟨['g', 'r', 'o', 'o', 't'], ['b', 'i', 'g'], none⟩]⟩, ⟨['g', 'e', 'n', 'o', 'e', 'g', '-', 'e'], ['e', 'n', 'o', 'u', 'g', 'h', '-', 'A', 'T', 'T', 'R'], [⟨['g', 'e', 'n', 'o', 'e', 'g'], ['e', 'n', 'o', 'u', 'g', 'h'], none⟩, ⟨['e'], ['A', 'T', 'T', 'R'], some '-'⟩]⟩, ⟨['v', 'r', 'o', 'u', 'w'], ['w', 'o', 'm', 'a', 'n'], [⟨['v', 'r', 'o', 'u', 'w'], ['w', 'o', 'm', 'a', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("head", "groot"), ("attributivizer", "affix"), ("noun", "vrouw"), ("degree", "genoeg-e")] }

def az2025_68c : Datum :=
  { id := "az2025_68c"
    source := ⟨"alexeyenko-zeijlstra-2025", "(68c)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "een groot-e genoeg vrouw"
    glossedTokens := [("een", "a"), ("groot-e", "big-ATTR"), ("genoeg", "enough"), ("vrouw", "woman")]
    glossedWords := [⟨['e', 'e', 'n'], ['a'], [⟨['e', 'e', 'n'], ['a'], none⟩]⟩, ⟨['g', 'r', 'o', 'o', 't', '-', 'e'], ['b', 'i', 'g', '-', 'A', 'T', 'T', 'R'], [⟨['g', 'r', 'o', 'o', 't'], ['b', 'i', 'g'], none⟩, ⟨['e'], ['A', 'T', 'T', 'R'], some '-'⟩]⟩, ⟨['g', 'e', 'n', 'o', 'e', 'g'], ['e', 'n', 'o', 'u', 'g', 'h'], [⟨['g', 'e', 'n', 'o', 'e', 'g'], ['e', 'n', 'o', 'u', 'g', 'h'], none⟩]⟩, ⟨['v', 'r', 'o', 'u', 'w'], ['w', 'o', 'm', 'a', 'n'], [⟨['v', 'r', 'o', 'u', 'w'], ['w', 'o', 'm', 'a', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("head", "groot-e"), ("noun", "vrouw"), ("degree", "genoeg")] }

def az2025_68d : Datum :=
  { id := "az2025_68d"
    source := ⟨"alexeyenko-zeijlstra-2025", "(68d)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "een groot genoeg vrouw"
    glossedTokens := [("een", "a"), ("groot", "big"), ("genoeg", "enough"), ("vrouw", "woman")]
    glossedWords := [⟨['e', 'e', 'n'], ['a'], [⟨['e', 'e', 'n'], ['a'], none⟩]⟩, ⟨['g', 'r', 'o', 'o', 't'], ['b', 'i', 'g'], [⟨['g', 'r', 'o', 'o', 't'], ['b', 'i', 'g'], none⟩]⟩, ⟨['g', 'e', 'n', 'o', 'e', 'g'], ['e', 'n', 'o', 'u', 'g', 'h'], [⟨['g', 'e', 'n', 'o', 'e', 'g'], ['e', 'n', 'o', 'u', 'g', 'h'], none⟩]⟩, ⟨['v', 'r', 'o', 'u', 'w'], ['w', 'o', 'm', 'a', 'n'], [⟨['v', 'r', 'o', 'u', 'w'], ['w', 'o', 'm', 'a', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("head", "groot"), ("noun", "vrouw"), ("degree", "genoeg")] }

def az2025_71a : Datum :=
  { id := "az2025_71a"
    source := ⟨"alexeyenko-zeijlstra-2025", "(71a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "a proud-∅ child"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "proud-∅"), ("attributivizer", "null"), ("noun", "child")] }

def az2025_71b : Datum :=
  { id := "az2025_71b"
    source := ⟨"alexeyenko-zeijlstra-2025", "(71b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "a proud of his mother-∅ child"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("head", "proud"), ("attributivizer", "null"), ("noun", "child"), ("dependent", "of")] }

def az2025_71c : Datum :=
  { id := "az2025_71c"
    source := ⟨"alexeyenko-zeijlstra-2025", "(71c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "a proud enough-∅ child"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "proud"), ("attributivizer", "null"), ("noun", "child"), ("degree", "enough-∅")] }

def all : List Datum := [az2025_1a, az2025_1b, az2025_2a, az2025_2b, az2025_3a, az2025_3b, az2025_4a, az2025_4b, az2025_7a, az2025_7b, az2025_8, az2025_9a, az2025_9b, az2025_10a, az2025_10b, az2025_15, az2025_16, az2025_17a, az2025_17b, az2025_18a, az2025_18b, az2025_19a, az2025_19b, az2025_20a, az2025_20b, az2025_21a, az2025_21b, az2025_23b, az2025_24c, az2025_26, az2025_27, az2025_28b, az2025_28d, az2025_29a, az2025_29b, az2025_29c, az2025_30a, az2025_30b, az2025_30c, az2025_30d, az2025_31, az2025_32, az2025_35, az2025_36a, az2025_36b, az2025_36c, az2025_36d, az2025_37a, az2025_37b, az2025_38a, az2025_38b, az2025_39a, az2025_39b, az2025_40b, az2025_41b, az2025_42a, az2025_42b, az2025_42c, az2025_42d, az2025_43a, az2025_43b, az2025_43c, az2025_62, az2025_63a, az2025_63b, az2025_66a, az2025_66b, az2025_66c, az2025_67a, az2025_67b, az2025_67c, az2025_68a, az2025_68b, az2025_68c, az2025_68d, az2025_71a, az2025_71b, az2025_71c]

end AlexeyenkoZeijlstra2025.Examples
