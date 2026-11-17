module

public import Linglib.Data.Examples.Schema

/-!
# `Wang2023` — typed example data

Auto-generated from `Linglib/Data/Examples/Wang2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Wang2023.Examples`.
-/

@[expose] public section

namespace Wang2023.Examples

def ex_1 : Datum :=
  { id := "wang2023_1"
    source := ⟨"wang-r-2023", "(1)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "As tu le livre?"
    glossedTokens := [("As", "have.PRES.2SG"), ("tu", "2SG"), ("le", "the"), ("livre", "book")]
    glossedWords := [⟨['A', 's'], ['h', 'a', 'v', 'e', '.', 'P', 'R', 'E', 'S', '.', '2', 'S', 'G'], [⟨['A', 's'], ['h', 'a', 'v', 'e', '.', 'P', 'R', 'E', 'S', '.', '2', 'S', 'G'], none⟩]⟩, ⟨['t', 'u'], ['2', 'S', 'G'], [⟨['t', 'u'], ['2', 'S', 'G'], none⟩]⟩, ⟨['l', 'e'], ['t', 'h', 'e'], [⟨['l', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['l', 'i', 'v', 'r', 'e'], ['b', 'o', 'o', 'k'], [⟨['l', 'i', 'v', 'r', 'e'], ['b', 'o', 'o', 'k'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("address", "familiar"), ("number", "singular")] }

def ex_2 : Datum :=
  { id := "wang2023_2"
    source := ⟨"wang-r-2023", "(2)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Avez vous le livre?"
    glossedTokens := [("Avez", "have.PRES.2PL"), ("vous", "2PL"), ("le", "the"), ("livre", "book")]
    glossedWords := [⟨['A', 'v', 'e', 'z'], ['h', 'a', 'v', 'e', '.', 'P', 'R', 'E', 'S', '.', '2', 'P', 'L'], [⟨['A', 'v', 'e', 'z'], ['h', 'a', 'v', 'e', '.', 'P', 'R', 'E', 'S', '.', '2', 'P', 'L'], none⟩]⟩, ⟨['v', 'o', 'u', 's'], ['2', 'P', 'L'], [⟨['v', 'o', 'u', 's'], ['2', 'P', 'L'], none⟩]⟩, ⟨['l', 'e'], ['t', 'h', 'e'], [⟨['l', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['l', 'i', 'v', 'r', 'e'], ['b', 'o', 'o', 'k'], [⟨['l', 'i', 'v', 'r', 'e'], ['b', 'o', 'o', 'k'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("As vous le livre?", .ungrammatical)]
    readings := []
    paperFeatures := [("address", "polite"), ("number", "plural"), ("mismatch", "referentially singular")] }

def ex_3a : Datum :=
  { id := "wang2023_3a"
    source := ⟨"wang-r-2023", "(3a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Alessandro, sei contento?"
    glossedTokens := [("Alessandro", "A"), ("sei", "2SG.COP"), ("contento", "happy.MASC")]
    glossedWords := [⟨['A', 'l', 'e', 's', 's', 'a', 'n', 'd', 'r', 'o'], ['A'], [⟨['A', 'l', 'e', 's', 's', 'a', 'n', 'd', 'r', 'o'], ['A'], none⟩]⟩, ⟨['s', 'e', 'i'], ['2', 'S', 'G', '.', 'C', 'O', 'P'], [⟨['s', 'e', 'i'], ['2', 'S', 'G', '.', 'C', 'O', 'P'], none⟩]⟩, ⟨['c', 'o', 'n', 't', 'e', 'n', 't', 'o'], ['h', 'a', 'p', 'p', 'y', '.', 'M', 'A', 'S', 'C'], [⟨['c', 'o', 'n', 't', 'e', 'n', 't', 'o'], ['h', 'a', 'p', 'p', 'y', '.', 'M', 'A', 'S', 'C'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Alessandro, è contento?", .ungrammatical)]
    readings := []
    paperFeatures := [("address", "familiar"), ("person", "second")] }

def ex_3b : Datum :=
  { id := "wang2023_3b"
    source := ⟨"wang-r-2023", "(3b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Signor Alessandro, è contento?"
    glossedTokens := [("Signor", "sir"), ("Alessandro", "A"), ("è", "3SG.COP"), ("contento", "happy.MASC")]
    glossedWords := [⟨['S', 'i', 'g', 'n', 'o', 'r'], ['s', 'i', 'r'], [⟨['S', 'i', 'g', 'n', 'o', 'r'], ['s', 'i', 'r'], none⟩]⟩, ⟨['A', 'l', 'e', 's', 's', 'a', 'n', 'd', 'r', 'o'], ['A'], [⟨['A', 'l', 'e', 's', 's', 'a', 'n', 'd', 'r', 'o'], ['A'], none⟩]⟩, ⟨['è'], ['3', 'S', 'G', '.', 'C', 'O', 'P'], [⟨['è'], ['3', 'S', 'G', '.', 'C', 'O', 'P'], none⟩]⟩, ⟨['c', 'o', 'n', 't', 'e', 'n', 't', 'o'], ['h', 'a', 'p', 'p', 'y', '.', 'M', 'A', 'S', 'C'], [⟨['c', 'o', 'n', 't', 'e', 'n', 't', 'o'], ['h', 'a', 'p', 'p', 'y', '.', 'M', 'A', 'S', 'C'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Signor Alessandro, sei contento?", .ungrammatical)]
    readings := []
    paperFeatures := [("address", "polite"), ("person", "third"), ("mismatch", "second-person addressee")] }

def ex_4a : Datum :=
  { id := "wang2023_4a"
    source := ⟨"wang-r-2023", "(4a)"⟩
    reportedIn := none
    language := "ainu1240"
    primaryText := "Ecioka rupne nispa-eci ne ruwe"
    glossedTokens := [("Ecioka", "2PL"), ("rupne", "be.grown.up"), ("nispa-eci", "man-2PL"), ("ne", "COP"), ("ruwe", "ASSERT")]
    glossedWords := [⟨['E', 'c', 'i', 'o', 'k', 'a'], ['2', 'P', 'L'], [⟨['E', 'c', 'i', 'o', 'k', 'a'], ['2', 'P', 'L'], none⟩]⟩, ⟨['r', 'u', 'p', 'n', 'e'], ['b', 'e', '.', 'g', 'r', 'o', 'w', 'n', '.', 'u', 'p'], [⟨['r', 'u', 'p', 'n', 'e'], ['b', 'e', '.', 'g', 'r', 'o', 'w', 'n', '.', 'u', 'p'], none⟩]⟩, ⟨['n', 'i', 's', 'p', 'a', '-', 'e', 'c', 'i'], ['m', 'a', 'n', '-', '2', 'P', 'L'], [⟨['n', 'i', 's', 'p', 'a'], ['m', 'a', 'n'], none⟩, ⟨['e', 'c', 'i'], ['2', 'P', 'L'], some '-'⟩]⟩, ⟨['n', 'e'], ['C', 'O', 'P'], [⟨['n', 'e'], ['C', 'O', 'P'], none⟩]⟩, ⟨['r', 'u', 'w', 'e'], ['A', 'S', 'S', 'E', 'R', 'T'], [⟨['r', 'u', 'w', 'e'], ['A', 'S', 'S', 'E', 'R', 'T'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("address", "familiar"), ("definiteness", "definite pronoun")] }

def ex_4b : Datum :=
  { id := "wang2023_4b"
    source := ⟨"wang-r-2023", "(4b)"⟩
    reportedIn := none
    language := "ainu1240"
    primaryText := "An nu no.oka"
    glossedTokens := [("An", "INDEF"), ("nu", "ask"), ("no.oka", "IMPF")]
    glossedWords := [⟨['A', 'n'], ['I', 'N', 'D', 'E', 'F'], [⟨['A', 'n'], ['I', 'N', 'D', 'E', 'F'], none⟩]⟩, ⟨['n', 'u'], ['a', 's', 'k'], [⟨['n', 'u'], ['a', 's', 'k'], none⟩]⟩, ⟨['n', 'o', '.', 'o', 'k', 'a'], ['I', 'M', 'P', 'F'], [⟨['n', 'o', 'o', 'k', 'a'], ['I', 'M', 'P', 'F'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("address", "polite"), ("definiteness", "indefinite pronoun"), ("mismatch", "definite addressee")] }

def ex_29 : Datum :=
  { id := "wang2023_29"
    source := ⟨"wang-r-2023", "(29)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "As tu le livre?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("unattested", "honorific singular")] }

def ex_30a : Datum :=
  { id := "wang2023_30a"
    source := ⟨"wang-r-2023", "(30a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Signor Alessandro, sono contento?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("unattested", "honorific first person")] }

def ex_30b : Datum :=
  { id := "wang2023_30b"
    source := ⟨"wang-r-2023", "(30b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Sei Signor Alessandro contento?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("unattested", "honorific second person")] }

def ex_31 : Datum :=
  { id := "wang2023_31"
    source := ⟨"wang-r-2023", "(31)"⟩
    reportedIn := none
    language := "ainu1240"
    primaryText := "Eani nu no.oka"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("unattested", "honorific definite")] }

def ex_48a : Datum :=
  { id := "wang2023_48a"
    source := ⟨"wang-r-2023", "(48a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How many hamsters do I own? Just one hamster, I think."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "semantic markedness"), ("number", "plural inclusive")] }

def ex_49 : Datum :=
  { id := "wang2023_49"
    source := ⟨"wang-r-2023", "(49)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every girl owns hamsters."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("each girl owns exactly one hamster", .acceptable), ("mixed: some girls own one, others several", .acceptable)]
    paperFeatures := [("diagnostic", "quantification"), ("number", "plural inclusive")] }

def ex_50 : Datum :=
  { id := "wang2023_50"
    source := ⟨"wang-r-2023", "(50)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every one of us has to call his/her mother."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Every one of us has to call my mother.", .ungrammatical), ("Every one of us has to call your mother.", .ungrammatical)]
    readings := []
    paperFeatures := [("diagnostic", "quantification"), ("person", "third unmarked")] }

def ex_53a : Datum :=
  { id := "wang2023_53a"
    source := ⟨"wang-r-2023", "(53a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I've picked up the new hamster from the store."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("definiteness", "definite"), ("presupposition", "familiarity")] }

def ex_53b : Datum :=
  { id := "wang2023_53b"
    source := ⟨"wang-r-2023", "(53b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I've picked up a new hamster from the store."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("definiteness", "indefinite")] }

def ex_60 : Datum :=
  { id := "wang2023_60"
    source := ⟨"wang-r-2023", "(60)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Avez vous le livre?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("address", "polite"), ("number", "plural"), ("case", "ceiling")] }

def ex_72 : Datum :=
  { id := "wang2023_72"
    source := ⟨"wang-r-2023", "(72)"⟩
    reportedIn := none
    language := "motl1237"
    primaryText := "Ēt! Yohē! Amyo van tō me!"
    glossedTokens := [("Ēt", "EXCLAM"), ("Yohē", "DU.VOC"), ("Amyo", "2DU.IMP"), ("van", "AORIST.go"), ("tō", "POL.IMP"), ("me", "hither")]
    glossedWords := [⟨['Ē', 't'], ['E', 'X', 'C', 'L', 'A', 'M'], [⟨['Ē', 't'], ['E', 'X', 'C', 'L', 'A', 'M'], none⟩]⟩, ⟨['Y', 'o', 'h', 'ē'], ['D', 'U', '.', 'V', 'O', 'C'], [⟨['Y', 'o', 'h', 'ē'], ['D', 'U', '.', 'V', 'O', 'C'], none⟩]⟩, ⟨['A', 'm', 'y', 'o'], ['2', 'D', 'U', '.', 'I', 'M', 'P'], [⟨['A', 'm', 'y', 'o'], ['2', 'D', 'U', '.', 'I', 'M', 'P'], none⟩]⟩, ⟨['v', 'a', 'n'], ['A', 'O', 'R', 'I', 'S', 'T', '.', 'g', 'o'], [⟨['v', 'a', 'n'], ['A', 'O', 'R', 'I', 'S', 'T', '.', 'g', 'o'], none⟩]⟩, ⟨['t', 'ō'], ['P', 'O', 'L', '.', 'I', 'M', 'P'], [⟨['t', 'ō'], ['P', 'O', 'L', '.', 'I', 'M', 'P'], none⟩]⟩, ⟨['m', 'e'], ['h', 'i', 't', 'h', 'e', 'r'], [⟨['m', 'e'], ['h', 'i', 't', 'h', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("address", "polite"), ("number", "dual"), ("system", "honorific dual only")] }

def ex_74b : Datum :=
  { id := "wang2023_74b"
    source := ⟨"wang-r-2023", "(74b)"⟩
    reportedIn := none
    language := "khar1287"
    primaryText := "iɲ-aʔ tay konon tin bhaya-ɲ-kiyar ayiˁj-kiyar."
    glossedTokens := [("iɲ-aʔ", "1SG-GEN"), ("tay", "ABL"), ("konon", "small"), ("tin", "three"), ("bhaya-ɲ-kiyar", "brother-1.POSS-3DU"), ("ayiˁj-kiyar", "COP.PRES-3DU")]
    glossedWords := [⟨['i', 'ɲ', '-', 'a', 'ʔ'], ['1', 'S', 'G', '-', 'G', 'E', 'N'], [⟨['i', 'ɲ'], ['1', 'S', 'G'], none⟩, ⟨['a', 'ʔ'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['t', 'a', 'y'], ['A', 'B', 'L'], [⟨['t', 'a', 'y'], ['A', 'B', 'L'], none⟩]⟩, ⟨['k', 'o', 'n', 'o', 'n'], ['s', 'm', 'a', 'l', 'l'], [⟨['k', 'o', 'n', 'o', 'n'], ['s', 'm', 'a', 'l', 'l'], none⟩]⟩, ⟨['t', 'i', 'n'], ['t', 'h', 'r', 'e', 'e'], [⟨['t', 'i', 'n'], ['t', 'h', 'r', 'e', 'e'], none⟩]⟩, ⟨['b', 'h', 'a', 'y', 'a', '-', 'ɲ', '-', 'k', 'i', 'y', 'a', 'r'], ['b', 'r', 'o', 't', 'h', 'e', 'r', '-', '1', '.', 'P', 'O', 'S', 'S', '-', '3', 'D', 'U'], [⟨['b', 'h', 'a', 'y', 'a'], ['b', 'r', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['ɲ'], ['1', '.', 'P', 'O', 'S', 'S'], some '-'⟩, ⟨['k', 'i', 'y', 'a', 'r'], ['3', 'D', 'U'], some '-'⟩]⟩, ⟨['a', 'y', 'i', 'ˁ', 'j', '-', 'k', 'i', 'y', 'a', 'r'], ['C', 'O', 'P', '.', 'P', 'R', 'E', 'S', '-', '3', 'D', 'U'], [⟨['a', 'y', 'i', 'ˁ', 'j'], ['C', 'O', 'P', '.', 'P', 'R', 'E', 'S'], none⟩, ⟨['k', 'i', 'y', 'a', 'r'], ['3', 'D', 'U'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reference", "polite"), ("number", "dual for three referents"), ("system", "honorific dual only")] }

def ex_75a : Datum :=
  { id := "wang2023_75a"
    source := ⟨"wang-r-2023", "(75a)"⟩
    reportedIn := none
    language := "slov1268"
    primaryText := "Ali se boste Vi used-l-i?"
    glossedTokens := [("Ali", "Q"), ("se", "REFLX"), ("boste", "AUX.FUT.2PL"), ("Vi", "2PL"), ("used-l-i", "sit-PART-PL.MASC")]
    glossedWords := [⟨['A', 'l', 'i'], ['Q'], [⟨['A', 'l', 'i'], ['Q'], none⟩]⟩, ⟨['s', 'e'], ['R', 'E', 'F', 'L', 'X'], [⟨['s', 'e'], ['R', 'E', 'F', 'L', 'X'], none⟩]⟩, ⟨['b', 'o', 's', 't', 'e'], ['A', 'U', 'X', '.', 'F', 'U', 'T', '.', '2', 'P', 'L'], [⟨['b', 'o', 's', 't', 'e'], ['A', 'U', 'X', '.', 'F', 'U', 'T', '.', '2', 'P', 'L'], none⟩]⟩, ⟨['V', 'i'], ['2', 'P', 'L'], [⟨['V', 'i'], ['2', 'P', 'L'], none⟩]⟩, ⟨['u', 's', 'e', 'd', '-', 'l', '-', 'i'], ['s', 'i', 't', '-', 'P', 'A', 'R', 'T', '-', 'P', 'L', '.', 'M', 'A', 'S', 'C'], [⟨['u', 's', 'e', 'd'], ['s', 'i', 't'], none⟩, ⟨['l'], ['P', 'A', 'R', 'T'], some '-'⟩, ⟨['i'], ['P', 'L', '.', 'M', 'A', 'S', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("address", "polite"), ("number", "plural"), ("system", "honorific plural only")] }

def ex_75b : Datum :=
  { id := "wang2023_75b"
    source := ⟨"wang-r-2023", "(75b)"⟩
    reportedIn := none
    language := "slov1268"
    primaryText := "Ali se bosta Vidva used-l-a?"
    glossedTokens := [("Ali", "Q"), ("se", "REFLX"), ("bosta", "AUX.FUT.2DU"), ("Vidva", "2DU"), ("used-l-a", "sit-PART-DU.MASC")]
    glossedWords := [⟨['A', 'l', 'i'], ['Q'], [⟨['A', 'l', 'i'], ['Q'], none⟩]⟩, ⟨['s', 'e'], ['R', 'E', 'F', 'L', 'X'], [⟨['s', 'e'], ['R', 'E', 'F', 'L', 'X'], none⟩]⟩, ⟨['b', 'o', 's', 't', 'a'], ['A', 'U', 'X', '.', 'F', 'U', 'T', '.', '2', 'D', 'U'], [⟨['b', 'o', 's', 't', 'a'], ['A', 'U', 'X', '.', 'F', 'U', 'T', '.', '2', 'D', 'U'], none⟩]⟩, ⟨['V', 'i', 'd', 'v', 'a'], ['2', 'D', 'U'], [⟨['V', 'i', 'd', 'v', 'a'], ['2', 'D', 'U'], none⟩]⟩, ⟨['u', 's', 'e', 'd', '-', 'l', '-', 'a'], ['s', 'i', 't', '-', 'P', 'A', 'R', 'T', '-', 'D', 'U', '.', 'M', 'A', 'S', 'C'], [⟨['u', 's', 'e', 'd'], ['s', 'i', 't'], none⟩, ⟨['l'], ['P', 'A', 'R', 'T'], some '-'⟩, ⟨['a'], ['D', 'U', '.', 'M', 'A', 'S', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("address", "plain dual"), ("number", "dual")] }

def ex_78a : Datum :=
  { id := "wang2023_78a"
    source := ⟨"wang-r-2023", "(78a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mele1250"
    primaryText := "korua/koteu ku-roro."
    glossedTokens := [("korua/koteu", "2DU/2PL"), ("ku-roro", "PF-go.NSG")]
    glossedWords := [⟨['k', 'o', 'r', 'u', 'a', '/', 'k', 'o', 't', 'e', 'u'], ['2', 'D', 'U', '/', '2', 'P', 'L'], [⟨['k', 'o', 'r', 'u', 'a', '/', 'k', 'o', 't', 'e', 'u'], ['2', 'D', 'U', '/', '2', 'P', 'L'], none⟩]⟩, ⟨['k', 'u', '-', 'r', 'o', 'r', 'o'], ['P', 'F', '-', 'g', 'o', '.', 'N', 'S', 'G'], [⟨['k', 'u'], ['P', 'F'], none⟩, ⟨['r', 'o', 'r', 'o'], ['g', 'o', '.', 'N', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("address", "polite"), ("number", "dual or plural"), ("system", "non-escalating")] }

def ex_81 : Datum :=
  { id := "wang2023_81"
    source := ⟨"wang-r-2023", "(81)"⟩
    reportedIn := none
    language := "slov1268"
    primaryText := "Vsak študent je prinesel s seboj svoj-i knjig-i."
    glossedTokens := [("Vsak", "every"), ("študent", "student"), ("je", "be.SG"), ("prinesel", "brought.MASC"), ("s", "with"), ("seboj", "self"), ("svoj-i", "his-DU"), ("knjig-i", "book-DU")]
    glossedWords := [⟨['V', 's', 'a', 'k'], ['e', 'v', 'e', 'r', 'y'], [⟨['V', 's', 'a', 'k'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['š', 't', 'u', 'd', 'e', 'n', 't'], ['s', 't', 'u', 'd', 'e', 'n', 't'], [⟨['š', 't', 'u', 'd', 'e', 'n', 't'], ['s', 't', 'u', 'd', 'e', 'n', 't'], none⟩]⟩, ⟨['j', 'e'], ['b', 'e', '.', 'S', 'G'], [⟨['j', 'e'], ['b', 'e', '.', 'S', 'G'], none⟩]⟩, ⟨['p', 'r', 'i', 'n', 'e', 's', 'e', 'l'], ['b', 'r', 'o', 'u', 'g', 'h', 't', '.', 'M', 'A', 'S', 'C'], [⟨['p', 'r', 'i', 'n', 'e', 's', 'e', 'l'], ['b', 'r', 'o', 'u', 'g', 'h', 't', '.', 'M', 'A', 'S', 'C'], none⟩]⟩, ⟨['s'], ['w', 'i', 't', 'h'], [⟨['s'], ['w', 'i', 't', 'h'], none⟩]⟩, ⟨['s', 'e', 'b', 'o', 'j'], ['s', 'e', 'l', 'f'], [⟨['s', 'e', 'b', 'o', 'j'], ['s', 'e', 'l', 'f'], none⟩]⟩, ⟨['s', 'v', 'o', 'j', '-', 'i'], ['h', 'i', 's', '-', 'D', 'U'], [⟨['s', 'v', 'o', 'j'], ['h', 'i', 's'], none⟩, ⟨['i'], ['D', 'U'], some '-'⟩]⟩, ⟨['k', 'n', 'j', 'i', 'g', '-', 'i'], ['b', 'o', 'o', 'k', '-', 'D', 'U'], [⟨['k', 'n', 'j', 'i', 'g'], ['b', 'o', 'o', 'k'], none⟩, ⟨['i'], ['D', 'U'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "quantification"), ("number", "dual intermediate")] }

def all : List Datum := [ex_1, ex_2, ex_3a, ex_3b, ex_4a, ex_4b, ex_29, ex_30a, ex_30b, ex_31, ex_48a, ex_49, ex_50, ex_53a, ex_53b, ex_60, ex_72, ex_74b, ex_75a, ex_75b, ex_78a, ex_81]

end Wang2023.Examples
