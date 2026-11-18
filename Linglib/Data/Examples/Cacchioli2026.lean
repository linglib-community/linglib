module

public import Linglib.Data.Examples.Schema

/-!
# `Cacchioli2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Cacchioli2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Cacchioli2026.Examples`.
-/

@[expose] public section

namespace Cacchioli2026.Examples

def ex_5b : Datum :=
  { id := "cacchioli2026_5b"
    source := ⟨"cacchioli-2026", "ch. 5, ex. (5b)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "mɨs dɨm-ay ʔaj-ts'awɛtɨ-n"
    glossedTokens := [("mɨs", "with"), ("dɨm-ay", "cat-POSS.1S"), ("ʔaj-Ø-ts'awɛtɨ-n", "NEG-SM.1S-play.IPFV-NEG")]
    glossedWords := [⟨['m', 'ɨ', 's'], ['w', 'i', 't', 'h'], [⟨['m', 'ɨ', 's'], ['w', 'i', 't', 'h'], none⟩]⟩, ⟨['d', 'ɨ', 'm', '-', 'a', 'y'], ['c', 'a', 't', '-', 'P', 'O', 'S', 'S', '.', '1', 'S'], [⟨['d', 'ɨ', 'm'], ['c', 'a', 't'], none⟩, ⟨['a', 'y'], ['P', 'O', 'S', 'S', '.', '1', 'S'], some '-'⟩]⟩, ⟨['ʔ', 'a', 'j', '-', 'Ø', '-', 't', 's', '\'', 'a', 'w', 'ɛ', 't', 'ɨ', '-', 'n'], ['N', 'E', 'G', '-', 'S', 'M', '.', '1', 'S', '-', 'p', 'l', 'a', 'y', '.', 'I', 'P', 'F', 'V', '-', 'N', 'E', 'G'], [⟨['ʔ', 'a', 'j'], ['N', 'E', 'G'], none⟩, ⟨['Ø'], ['S', 'M', '.', '1', 'S'], some '-'⟩, ⟨['t', 's', '\'', 'a', 'w', 'ɛ', 't', 'ɨ'], ['p', 'l', 'a', 'y', '.', 'I', 'P', 'F', 'V'], some '-'⟩, ⟨['n'], ['N', 'E', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "root")] }

def ex_12a : Datum :=
  { id := "cacchioli2026_12a"
    source := ⟨"cacchioli-2026", "ch. 5, ex. (12a)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "ʔɨt-om ʔanɛ z-ɛj-nbɨb-om mɛts'ħafti ʔab-t-i ʔarmadyo ʔall-ɛwo"
    glossedTokens := [("ʔɨt-om", "DIST-MP"), ("ʔanɛ", "I"), ("z-ɛj-Ø-nbɨb-om", "REL-NEG-SM.1S-read.IPFV-OM.3MP"), ("mɛts'ħafti", "book.MP"), ("ʔab-t-i", "PREP-DIST-MS"), ("ʔarmadyo", "cabinet"), ("ʔall-ɛwo", "BE1.PRES-SM.3MP")]
    glossedWords := [⟨['ʔ', 'ɨ', 't', '-', 'o', 'm'], ['D', 'I', 'S', 'T', '-', 'M', 'P'], [⟨['ʔ', 'ɨ', 't'], ['D', 'I', 'S', 'T'], none⟩, ⟨['o', 'm'], ['M', 'P'], some '-'⟩]⟩, ⟨['ʔ', 'a', 'n', 'ɛ'], ['I'], [⟨['ʔ', 'a', 'n', 'ɛ'], ['I'], none⟩]⟩, ⟨['z', '-', 'ɛ', 'j', '-', 'Ø', '-', 'n', 'b', 'ɨ', 'b', '-', 'o', 'm'], ['R', 'E', 'L', '-', 'N', 'E', 'G', '-', 'S', 'M', '.', '1', 'S', '-', 'r', 'e', 'a', 'd', '.', 'I', 'P', 'F', 'V', '-', 'O', 'M', '.', '3', 'M', 'P'], [⟨['z'], ['R', 'E', 'L'], none⟩, ⟨['ɛ', 'j'], ['N', 'E', 'G'], some '-'⟩, ⟨['Ø'], ['S', 'M', '.', '1', 'S'], some '-'⟩, ⟨['n', 'b', 'ɨ', 'b'], ['r', 'e', 'a', 'd', '.', 'I', 'P', 'F', 'V'], some '-'⟩, ⟨['o', 'm'], ['O', 'M', '.', '3', 'M', 'P'], some '-'⟩]⟩, ⟨['m', 'ɛ', 't', 's', '\'', 'ħ', 'a', 'f', 't', 'i'], ['b', 'o', 'o', 'k', '.', 'M', 'P'], [⟨['m', 'ɛ', 't', 's', '\'', 'ħ', 'a', 'f', 't', 'i'], ['b', 'o', 'o', 'k', '.', 'M', 'P'], none⟩]⟩, ⟨['ʔ', 'a', 'b', '-', 't', '-', 'i'], ['P', 'R', 'E', 'P', '-', 'D', 'I', 'S', 'T', '-', 'M', 'S'], [⟨['ʔ', 'a', 'b'], ['P', 'R', 'E', 'P'], none⟩, ⟨['t'], ['D', 'I', 'S', 'T'], some '-'⟩, ⟨['i'], ['M', 'S'], some '-'⟩]⟩, ⟨['ʔ', 'a', 'r', 'm', 'a', 'd', 'y', 'o'], ['c', 'a', 'b', 'i', 'n', 'e', 't'], [⟨['ʔ', 'a', 'r', 'm', 'a', 'd', 'y', 'o'], ['c', 'a', 'b', 'i', 'n', 'e', 't'], none⟩]⟩, ⟨['ʔ', 'a', 'l', 'l', '-', 'ɛ', 'w', 'o'], ['B', 'E', '1', '.', 'P', 'R', 'E', 'S', '-', 'S', 'M', '.', '3', 'M', 'P'], [⟨['ʔ', 'a', 'l', 'l'], ['B', 'E', '1', '.', 'P', 'R', 'E', 'S'], none⟩, ⟨['ɛ', 'w', 'o'], ['S', 'M', '.', '3', 'M', 'P'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("ʔɨt-om ʔanɛ z-ɨ-nbɨb-om-n mɛts'ħafti ʔab-t-i ʔarmadyo ʔall-ɛwo", .ungrammatical), ("ʔɨt-om ʔanɛ z-ɛj-nbɨb-om-n mɛts'ħafti ʔab-t-i ʔarmadyo ʔall-ɛwo", .ungrammatical)]
    readings := []
    paperFeatures := [("clause", "relative")] }

def ex_14 : Datum :=
  { id := "cacchioli2026_14"
    source := ⟨"cacchioli-2026", "ch. 5, ex. (14)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "Kidanɛ mɛts'ħafti z-ɛj-nbib jɨ-mɛsɨl"
    glossedTokens := [("Kidanɛ", "Kidane"), ("mɛts'ħafti", "book.MP"), ("z-ɛj-Ø-nbib", "REL-NEG-SM.3MS-read.IPFV"), ("jɨ-mɛsɨl", "SM.3MS-seem.IPFV")]
    glossedWords := [⟨['K', 'i', 'd', 'a', 'n', 'ɛ'], ['K', 'i', 'd', 'a', 'n', 'e'], [⟨['K', 'i', 'd', 'a', 'n', 'ɛ'], ['K', 'i', 'd', 'a', 'n', 'e'], none⟩]⟩, ⟨['m', 'ɛ', 't', 's', '\'', 'ħ', 'a', 'f', 't', 'i'], ['b', 'o', 'o', 'k', '.', 'M', 'P'], [⟨['m', 'ɛ', 't', 's', '\'', 'ħ', 'a', 'f', 't', 'i'], ['b', 'o', 'o', 'k', '.', 'M', 'P'], none⟩]⟩, ⟨['z', '-', 'ɛ', 'j', '-', 'Ø', '-', 'n', 'b', 'i', 'b'], ['R', 'E', 'L', '-', 'N', 'E', 'G', '-', 'S', 'M', '.', '3', 'M', 'S', '-', 'r', 'e', 'a', 'd', '.', 'I', 'P', 'F', 'V'], [⟨['z'], ['R', 'E', 'L'], none⟩, ⟨['ɛ', 'j'], ['N', 'E', 'G'], some '-'⟩, ⟨['Ø'], ['S', 'M', '.', '3', 'M', 'S'], some '-'⟩, ⟨['n', 'b', 'i', 'b'], ['r', 'e', 'a', 'd', '.', 'I', 'P', 'F', 'V'], some '-'⟩]⟩, ⟨['j', 'ɨ', '-', 'm', 'ɛ', 's', 'ɨ', 'l'], ['S', 'M', '.', '3', 'M', 'S', '-', 's', 'e', 'e', 'm', '.', 'I', 'P', 'F', 'V'], [⟨['j', 'ɨ'], ['S', 'M', '.', '3', 'M', 'S'], none⟩, ⟨['m', 'ɛ', 's', 'ɨ', 'l'], ['s', 'e', 'e', 'm', '.', 'I', 'P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "seem")] }

def ex_15 : Datum :=
  { id := "cacchioli2026_15"
    source := ⟨"cacchioli-2026", "ch. 5, ex. (15)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "nɨssu ʔɨntɛ z-ɛj-xɛjɨd k-ɨ-bɛli ʔijj-ɛ"
    glossedTokens := [("nɨssu", "he"), ("ʔɨntɛ", "if"), ("z-ɛj-Ø-xɛjɨd", "REL-NEG-SM.3MS-leave.IPFV"), ("k-ɨ-bɛli", "SBJ-SM.1S-cry.IPFV"), ("ʔijj-ɛ", "BE2.PRES-SM.1S")]
    glossedWords := [⟨['n', 'ɨ', 's', 's', 'u'], ['h', 'e'], [⟨['n', 'ɨ', 's', 's', 'u'], ['h', 'e'], none⟩]⟩, ⟨['ʔ', 'ɨ', 'n', 't', 'ɛ'], ['i', 'f'], [⟨['ʔ', 'ɨ', 'n', 't', 'ɛ'], ['i', 'f'], none⟩]⟩, ⟨['z', '-', 'ɛ', 'j', '-', 'Ø', '-', 'x', 'ɛ', 'j', 'ɨ', 'd'], ['R', 'E', 'L', '-', 'N', 'E', 'G', '-', 'S', 'M', '.', '3', 'M', 'S', '-', 'l', 'e', 'a', 'v', 'e', '.', 'I', 'P', 'F', 'V'], [⟨['z'], ['R', 'E', 'L'], none⟩, ⟨['ɛ', 'j'], ['N', 'E', 'G'], some '-'⟩, ⟨['Ø'], ['S', 'M', '.', '3', 'M', 'S'], some '-'⟩, ⟨['x', 'ɛ', 'j', 'ɨ', 'd'], ['l', 'e', 'a', 'v', 'e', '.', 'I', 'P', 'F', 'V'], some '-'⟩]⟩, ⟨['k', '-', 'ɨ', '-', 'b', 'ɛ', 'l', 'i'], ['S', 'B', 'J', '-', 'S', 'M', '.', '1', 'S', '-', 'c', 'r', 'y', '.', 'I', 'P', 'F', 'V'], [⟨['k'], ['S', 'B', 'J'], none⟩, ⟨['ɨ'], ['S', 'M', '.', '1', 'S'], some '-'⟩, ⟨['b', 'ɛ', 'l', 'i'], ['c', 'r', 'y', '.', 'I', 'P', 'F', 'V'], some '-'⟩]⟩, ⟨['ʔ', 'i', 'j', 'j', '-', 'ɛ'], ['B', 'E', '2', '.', 'P', 'R', 'E', 'S', '-', 'S', 'M', '.', '1', 'S'], [⟨['ʔ', 'i', 'j', 'j'], ['B', 'E', '2', '.', 'P', 'R', 'E', 'S'], none⟩, ⟨['ɛ'], ['S', 'M', '.', '1', 'S'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "conditional")] }

def ex_16 : Datum :=
  { id := "cacchioli2026_16"
    source := ⟨"cacchioli-2026", "ch. 5, ex. (16)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "ʔaman ʔɨntay kɛm-z-ɛj-fɛttu ħatit-u-ni"
    glossedTokens := [("ʔaman", "Aman"), ("ʔɨntay", "what"), ("kɛm-z-ɛj-Ø-fɛttu", "COMP-REL-NEG-SM.1S-like.IPFV"), ("ħatit-u-ni", "ask.GER-SM.3MS-OM.1S")]
    glossedWords := [⟨['ʔ', 'a', 'm', 'a', 'n'], ['A', 'm', 'a', 'n'], [⟨['ʔ', 'a', 'm', 'a', 'n'], ['A', 'm', 'a', 'n'], none⟩]⟩, ⟨['ʔ', 'ɨ', 'n', 't', 'a', 'y'], ['w', 'h', 'a', 't'], [⟨['ʔ', 'ɨ', 'n', 't', 'a', 'y'], ['w', 'h', 'a', 't'], none⟩]⟩, ⟨['k', 'ɛ', 'm', '-', 'z', '-', 'ɛ', 'j', '-', 'Ø', '-', 'f', 'ɛ', 't', 't', 'u'], ['C', 'O', 'M', 'P', '-', 'R', 'E', 'L', '-', 'N', 'E', 'G', '-', 'S', 'M', '.', '1', 'S', '-', 'l', 'i', 'k', 'e', '.', 'I', 'P', 'F', 'V'], [⟨['k', 'ɛ', 'm'], ['C', 'O', 'M', 'P'], none⟩, ⟨['z'], ['R', 'E', 'L'], some '-'⟩, ⟨['ɛ', 'j'], ['N', 'E', 'G'], some '-'⟩, ⟨['Ø'], ['S', 'M', '.', '1', 'S'], some '-'⟩, ⟨['f', 'ɛ', 't', 't', 'u'], ['l', 'i', 'k', 'e', '.', 'I', 'P', 'F', 'V'], some '-'⟩]⟩, ⟨['ħ', 'a', 't', 'i', 't', '-', 'u', '-', 'n', 'i'], ['a', 's', 'k', '.', 'G', 'E', 'R', '-', 'S', 'M', '.', '3', 'M', 'S', '-', 'O', 'M', '.', '1', 'S'], [⟨['ħ', 'a', 't', 'i', 't'], ['a', 's', 'k', '.', 'G', 'E', 'R'], none⟩, ⟨['u'], ['S', 'M', '.', '3', 'M', 'S'], some '-'⟩, ⟨['n', 'i'], ['O', 'M', '.', '1', 'S'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "complement"), ("verb_class", "utterance"), ("typer", "kemzi"), ("matrix_verb", "ask")] }

def ex_20 : Datum :=
  { id := "cacchioli2026_20"
    source := ⟨"cacchioli-2026", "ch. 5, ex. (20)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "k-ɛj-bɛki fɛttin-ɛ"
    glossedTokens := [("k-ɛj-Ø-bɛki", "SBJ-NEG-SM.1S-cry.IPFV"), ("fɛttin-ɛ", "try.GER-SM.1S")]
    glossedWords := [⟨['k', '-', 'ɛ', 'j', '-', 'Ø', '-', 'b', 'ɛ', 'k', 'i'], ['S', 'B', 'J', '-', 'N', 'E', 'G', '-', 'S', 'M', '.', '1', 'S', '-', 'c', 'r', 'y', '.', 'I', 'P', 'F', 'V'], [⟨['k'], ['S', 'B', 'J'], none⟩, ⟨['ɛ', 'j'], ['N', 'E', 'G'], some '-'⟩, ⟨['Ø'], ['S', 'M', '.', '1', 'S'], some '-'⟩, ⟨['b', 'ɛ', 'k', 'i'], ['c', 'r', 'y', '.', 'I', 'P', 'F', 'V'], some '-'⟩]⟩, ⟨['f', 'ɛ', 't', 't', 'i', 'n', '-', 'ɛ'], ['t', 'r', 'y', '.', 'G', 'E', 'R', '-', 'S', 'M', '.', '1', 'S'], [⟨['f', 'ɛ', 't', 't', 'i', 'n'], ['t', 'r', 'y', '.', 'G', 'E', 'R'], none⟩, ⟨['ɛ'], ['S', 'M', '.', '1', 'S'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "subjunctive"), ("verb_class", "control"), ("typer", "ki"), ("matrix_verb", "try")] }

def ex_21 : Datum :=
  { id := "cacchioli2026_21"
    source := ⟨"cacchioli-2026", "ch. 5, ex. (21)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "dɛrho k-ɛj-nɛfɨr ʔaziz-u"
    glossedTokens := [("dɛrho", "chicken"), ("k-ɛj-Ø-nɛfɨr", "SBJ-NEG-SM.3MS-fly.IPFV"), ("ʔaziz-u", "order.GER-SM.3MS")]
    glossedWords := [⟨['d', 'ɛ', 'r', 'h', 'o'], ['c', 'h', 'i', 'c', 'k', 'e', 'n'], [⟨['d', 'ɛ', 'r', 'h', 'o'], ['c', 'h', 'i', 'c', 'k', 'e', 'n'], none⟩]⟩, ⟨['k', '-', 'ɛ', 'j', '-', 'Ø', '-', 'n', 'ɛ', 'f', 'ɨ', 'r'], ['S', 'B', 'J', '-', 'N', 'E', 'G', '-', 'S', 'M', '.', '3', 'M', 'S', '-', 'f', 'l', 'y', '.', 'I', 'P', 'F', 'V'], [⟨['k'], ['S', 'B', 'J'], none⟩, ⟨['ɛ', 'j'], ['N', 'E', 'G'], some '-'⟩, ⟨['Ø'], ['S', 'M', '.', '3', 'M', 'S'], some '-'⟩, ⟨['n', 'ɛ', 'f', 'ɨ', 'r'], ['f', 'l', 'y', '.', 'I', 'P', 'F', 'V'], some '-'⟩]⟩, ⟨['ʔ', 'a', 'z', 'i', 'z', '-', 'u'], ['o', 'r', 'd', 'e', 'r', '.', 'G', 'E', 'R', '-', 'S', 'M', '.', '3', 'M', 'S'], [⟨['ʔ', 'a', 'z', 'i', 'z'], ['o', 'r', 'd', 'e', 'r', '.', 'G', 'E', 'R'], none⟩, ⟨['u'], ['S', 'M', '.', '3', 'M', 'S'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "subjunctive"), ("verb_class", "directive"), ("typer", "ki"), ("matrix_verb", "order")] }

def ex_22 : Datum :=
  { id := "cacchioli2026_22"
    source := ⟨"cacchioli-2026", "ch. 5, ex. (22)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "ʔɨt-a sɛbɛjɨti k-ɛj-tɨ-xɛjjɨd dɛli-na"
    glossedTokens := [("ʔɨt-a", "DIST-FS"), ("sɛbɛjɨti", "woman"), ("k-ɛj-tɨ-xɛjjɨd", "SBJ-NEG-SM.3FS-go.IPFV"), ("dɛli-na", "want.GER-SM.1P")]
    glossedWords := [⟨['ʔ', 'ɨ', 't', '-', 'a'], ['D', 'I', 'S', 'T', '-', 'F', 'S'], [⟨['ʔ', 'ɨ', 't'], ['D', 'I', 'S', 'T'], none⟩, ⟨['a'], ['F', 'S'], some '-'⟩]⟩, ⟨['s', 'ɛ', 'b', 'ɛ', 'j', 'ɨ', 't', 'i'], ['w', 'o', 'm', 'a', 'n'], [⟨['s', 'ɛ', 'b', 'ɛ', 'j', 'ɨ', 't', 'i'], ['w', 'o', 'm', 'a', 'n'], none⟩]⟩, ⟨['k', '-', 'ɛ', 'j', '-', 't', 'ɨ', '-', 'x', 'ɛ', 'j', 'j', 'ɨ', 'd'], ['S', 'B', 'J', '-', 'N', 'E', 'G', '-', 'S', 'M', '.', '3', 'F', 'S', '-', 'g', 'o', '.', 'I', 'P', 'F', 'V'], [⟨['k'], ['S', 'B', 'J'], none⟩, ⟨['ɛ', 'j'], ['N', 'E', 'G'], some '-'⟩, ⟨['t', 'ɨ'], ['S', 'M', '.', '3', 'F', 'S'], some '-'⟩, ⟨['x', 'ɛ', 'j', 'j', 'ɨ', 'd'], ['g', 'o', '.', 'I', 'P', 'F', 'V'], some '-'⟩]⟩, ⟨['d', 'ɛ', 'l', 'i', '-', 'n', 'a'], ['w', 'a', 'n', 't', '.', 'G', 'E', 'R', '-', 'S', 'M', '.', '1', 'P'], [⟨['d', 'ɛ', 'l', 'i'], ['w', 'a', 'n', 't', '.', 'G', 'E', 'R'], none⟩, ⟨['n', 'a'], ['S', 'M', '.', '1', 'P'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "subjunctive"), ("verb_class", "desire"), ("typer", "ki"), ("matrix_verb", "want")] }

def ex_23 : Datum :=
  { id := "cacchioli2026_23"
    source := ⟨"cacchioli-2026", "ch. 5, ex. (23)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "n-ɨt-i ʔanbɛsa k-ɛj-bɛrbɛr ʁɛs tɛzawir-ɛ"
    glossedTokens := [("n-ɨt-i", "DOM-DIST-MS"), ("ʔanbɛsa", "lion"), ("k-ɛj-Ø-bɛrbɛr", "SBJ-NEG-SM.3MS-wake_up.IPFV"), ("ʁɛs", "slowly"), ("tɛzawir-ɛ", "walk.GER-SM.1S")]
    glossedWords := [⟨['n', '-', 'ɨ', 't', '-', 'i'], ['D', 'O', 'M', '-', 'D', 'I', 'S', 'T', '-', 'M', 'S'], [⟨['n'], ['D', 'O', 'M'], none⟩, ⟨['ɨ', 't'], ['D', 'I', 'S', 'T'], some '-'⟩, ⟨['i'], ['M', 'S'], some '-'⟩]⟩, ⟨['ʔ', 'a', 'n', 'b', 'ɛ', 's', 'a'], ['l', 'i', 'o', 'n'], [⟨['ʔ', 'a', 'n', 'b', 'ɛ', 's', 'a'], ['l', 'i', 'o', 'n'], none⟩]⟩, ⟨['k', '-', 'ɛ', 'j', '-', 'Ø', '-', 'b', 'ɛ', 'r', 'b', 'ɛ', 'r'], ['S', 'B', 'J', '-', 'N', 'E', 'G', '-', 'S', 'M', '.', '3', 'M', 'S', '-', 'w', 'a', 'k', 'e', '_', 'u', 'p', '.', 'I', 'P', 'F', 'V'], [⟨['k'], ['S', 'B', 'J'], none⟩, ⟨['ɛ', 'j'], ['N', 'E', 'G'], some '-'⟩, ⟨['Ø'], ['S', 'M', '.', '3', 'M', 'S'], some '-'⟩, ⟨['b', 'ɛ', 'r', 'b', 'ɛ', 'r'], ['w', 'a', 'k', 'e', '_', 'u', 'p', '.', 'I', 'P', 'F', 'V'], some '-'⟩]⟩, ⟨['ʁ', 'ɛ', 's'], ['s', 'l', 'o', 'w', 'l', 'y'], [⟨['ʁ', 'ɛ', 's'], ['s', 'l', 'o', 'w', 'l', 'y'], none⟩]⟩, ⟨['t', 'ɛ', 'z', 'a', 'w', 'i', 'r', '-', 'ɛ'], ['w', 'a', 'l', 'k', '.', 'G', 'E', 'R', '-', 'S', 'M', '.', '1', 'S'], [⟨['t', 'ɛ', 'z', 'a', 'w', 'i', 'r'], ['w', 'a', 'l', 'k', '.', 'G', 'E', 'R'], none⟩, ⟨['ɛ'], ['S', 'M', '.', '1', 'S'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "purpose")] }

def ex_24 : Datum :=
  { id := "cacchioli2026_24"
    source := ⟨"cacchioli-2026", "ch. 5, ex. (24)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "Tɛwɛldɛ ʔɨħmɨlti ʔaj-k-ɨ-bɛlʔɨ-n ʔijj-u"
    glossedTokens := [("Tɛwɛldɛ", "Tewelde"), ("ʔɨħmɨlti", "vegetables"), ("ʔaj-k-ɨ-bɛlʔɨ-n", "NEG-SBJ-SM.3MS-eat.IPFV-NEG"), ("ʔijj-u", "BE2.PRES-SM.3MS")]
    glossedWords := [⟨['T', 'ɛ', 'w', 'ɛ', 'l', 'd', 'ɛ'], ['T', 'e', 'w', 'e', 'l', 'd', 'e'], [⟨['T', 'ɛ', 'w', 'ɛ', 'l', 'd', 'ɛ'], ['T', 'e', 'w', 'e', 'l', 'd', 'e'], none⟩]⟩, ⟨['ʔ', 'ɨ', 'ħ', 'm', 'ɨ', 'l', 't', 'i'], ['v', 'e', 'g', 'e', 't', 'a', 'b', 'l', 'e', 's'], [⟨['ʔ', 'ɨ', 'ħ', 'm', 'ɨ', 'l', 't', 'i'], ['v', 'e', 'g', 'e', 't', 'a', 'b', 'l', 'e', 's'], none⟩]⟩, ⟨['ʔ', 'a', 'j', '-', 'k', '-', 'ɨ', '-', 'b', 'ɛ', 'l', 'ʔ', 'ɨ', '-', 'n'], ['N', 'E', 'G', '-', 'S', 'B', 'J', '-', 'S', 'M', '.', '3', 'M', 'S', '-', 'e', 'a', 't', '.', 'I', 'P', 'F', 'V', '-', 'N', 'E', 'G'], [⟨['ʔ', 'a', 'j'], ['N', 'E', 'G'], none⟩, ⟨['k'], ['S', 'B', 'J'], some '-'⟩, ⟨['ɨ'], ['S', 'M', '.', '3', 'M', 'S'], some '-'⟩, ⟨['b', 'ɛ', 'l', 'ʔ', 'ɨ'], ['e', 'a', 't', '.', 'I', 'P', 'F', 'V'], some '-'⟩, ⟨['n'], ['N', 'E', 'G'], some '-'⟩]⟩, ⟨['ʔ', 'i', 'j', 'j', '-', 'u'], ['B', 'E', '2', '.', 'P', 'R', 'E', 'S', '-', 'S', 'M', '.', '3', 'M', 'S'], [⟨['ʔ', 'i', 'j', 'j'], ['B', 'E', '2', '.', 'P', 'R', 'E', 'S'], none⟩, ⟨['u'], ['S', 'M', '.', '3', 'M', 'S'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "future")] }

def ex_25 : Datum :=
  { id := "cacchioli2026_25"
    source := ⟨"cacchioli-2026", "ch. 5, ex. (25)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "dɛrho ʔaj-nɨfɨrɨ-n ʔɨl-ɛ gɛlits'-ɛ"
    glossedTokens := [("dɛrho", "chicken"), ("ʔaj-Ø-nɨfɨrɨ-n", "NEG-SM.3MS-fly.IPFV-NEG"), ("ʔɨl-ɛ", "COMP-SM.1S"), ("gɛlits'-ɛ", "explain.GER-SM.1S")]
    glossedWords := [⟨['d', 'ɛ', 'r', 'h', 'o'], ['c', 'h', 'i', 'c', 'k', 'e', 'n'], [⟨['d', 'ɛ', 'r', 'h', 'o'], ['c', 'h', 'i', 'c', 'k', 'e', 'n'], none⟩]⟩, ⟨['ʔ', 'a', 'j', '-', 'Ø', '-', 'n', 'ɨ', 'f', 'ɨ', 'r', 'ɨ', '-', 'n'], ['N', 'E', 'G', '-', 'S', 'M', '.', '3', 'M', 'S', '-', 'f', 'l', 'y', '.', 'I', 'P', 'F', 'V', '-', 'N', 'E', 'G'], [⟨['ʔ', 'a', 'j'], ['N', 'E', 'G'], none⟩, ⟨['Ø'], ['S', 'M', '.', '3', 'M', 'S'], some '-'⟩, ⟨['n', 'ɨ', 'f', 'ɨ', 'r', 'ɨ'], ['f', 'l', 'y', '.', 'I', 'P', 'F', 'V'], some '-'⟩, ⟨['n'], ['N', 'E', 'G'], some '-'⟩]⟩, ⟨['ʔ', 'ɨ', 'l', '-', 'ɛ'], ['C', 'O', 'M', 'P', '-', 'S', 'M', '.', '1', 'S'], [⟨['ʔ', 'ɨ', 'l'], ['C', 'O', 'M', 'P'], none⟩, ⟨['ɛ'], ['S', 'M', '.', '1', 'S'], some '-'⟩]⟩, ⟨['g', 'ɛ', 'l', 'i', 't', 's', '\'', '-', 'ɛ'], ['e', 'x', 'p', 'l', 'a', 'i', 'n', '.', 'G', 'E', 'R', '-', 'S', 'M', '.', '1', 'S'], [⟨['g', 'ɛ', 'l', 'i', 't', 's', '\''], ['e', 'x', 'p', 'l', 'a', 'i', 'n', '.', 'G', 'E', 'R'], none⟩, ⟨['ɛ'], ['S', 'M', '.', '1', 'S'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("dɛrho ʔaj-nɨfɨrɨ ʔɨl-ɛ gɛlits'-ɛ", .ungrammatical)]
    readings := []
    paperFeatures := [("clause", "ilu"), ("verb_class", "utterance"), ("typer", "ilu"), ("matrix_verb", "explain")] }

def ex_29 : Datum :=
  { id := "cacchioli2026_29"
    source := ⟨"cacchioli-2026", "ch. 3, ex. (29)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "bzuħ gɨzie nɨsu sinɛma kɛm-z-ɨ-xɛjjɨd jɨ-fɛllɨt'"
    glossedTokens := [("bzuħ gɨzie", "often"), ("nɨsu", "he"), ("sinɛma", "cinema"), ("kɛm-z-ɨ-xɛjjɨd", "COMP-REL-SM.3MS-go.IPFV"), ("jɨ-fɛllɨt'", "SM.1S-know.IPFV")]
    glossedWords := [⟨['b', 'z', 'u', 'ħ', ' ', 'g', 'ɨ', 'z', 'i', 'e'], ['o', 'f', 't', 'e', 'n'], [⟨['b', 'z', 'u', 'ħ', ' ', 'g', 'ɨ', 'z', 'i', 'e'], ['o', 'f', 't', 'e', 'n'], none⟩]⟩, ⟨['n', 'ɨ', 's', 'u'], ['h', 'e'], [⟨['n', 'ɨ', 's', 'u'], ['h', 'e'], none⟩]⟩, ⟨['s', 'i', 'n', 'ɛ', 'm', 'a'], ['c', 'i', 'n', 'e', 'm', 'a'], [⟨['s', 'i', 'n', 'ɛ', 'm', 'a'], ['c', 'i', 'n', 'e', 'm', 'a'], none⟩]⟩, ⟨['k', 'ɛ', 'm', '-', 'z', '-', 'ɨ', '-', 'x', 'ɛ', 'j', 'j', 'ɨ', 'd'], ['C', 'O', 'M', 'P', '-', 'R', 'E', 'L', '-', 'S', 'M', '.', '3', 'M', 'S', '-', 'g', 'o', '.', 'I', 'P', 'F', 'V'], [⟨['k', 'ɛ', 'm'], ['C', 'O', 'M', 'P'], none⟩, ⟨['z'], ['R', 'E', 'L'], some '-'⟩, ⟨['ɨ'], ['S', 'M', '.', '3', 'M', 'S'], some '-'⟩, ⟨['x', 'ɛ', 'j', 'j', 'ɨ', 'd'], ['g', 'o', '.', 'I', 'P', 'F', 'V'], some '-'⟩]⟩, ⟨['j', 'ɨ', '-', 'f', 'ɛ', 'l', 'l', 'ɨ', 't', '\''], ['S', 'M', '.', '1', 'S', '-', 'k', 'n', 'o', 'w', '.', 'I', 'P', 'F', 'V'], [⟨['j', 'ɨ'], ['S', 'M', '.', '1', 'S'], none⟩, ⟨['f', 'ɛ', 'l', 'l', 'ɨ', 't', '\''], ['k', 'n', 'o', 'w', '.', 'I', 'P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb_class", "factive"), ("typer", "kemzi"), ("matrix_verb", "know")] }

def ex_30 : Datum :=
  { id := "cacchioli2026_30"
    source := ⟨"cacchioli-2026", "ch. 3, ex. (30)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "fadus gɨzɨɛ kɛm-z-ɨ-mɛts'ɨʔ rɛsiʕ-ɛ"
    glossedTokens := [("fadus", "noon"), ("gɨzɨɛ", "time"), ("kɛm-z-ɨ-mɛts'ɨʔ", "COMP-REL-SM.3MS-come.IPFV"), ("rɛsiʕ-ɛ", "forget.GER-SM.1S")]
    glossedWords := [⟨['f', 'a', 'd', 'u', 's'], ['n', 'o', 'o', 'n'], [⟨['f', 'a', 'd', 'u', 's'], ['n', 'o', 'o', 'n'], none⟩]⟩, ⟨['g', 'ɨ', 'z', 'ɨ', 'ɛ'], ['t', 'i', 'm', 'e'], [⟨['g', 'ɨ', 'z', 'ɨ', 'ɛ'], ['t', 'i', 'm', 'e'], none⟩]⟩, ⟨['k', 'ɛ', 'm', '-', 'z', '-', 'ɨ', '-', 'm', 'ɛ', 't', 's', '\'', 'ɨ', 'ʔ'], ['C', 'O', 'M', 'P', '-', 'R', 'E', 'L', '-', 'S', 'M', '.', '3', 'M', 'S', '-', 'c', 'o', 'm', 'e', '.', 'I', 'P', 'F', 'V'], [⟨['k', 'ɛ', 'm'], ['C', 'O', 'M', 'P'], none⟩, ⟨['z'], ['R', 'E', 'L'], some '-'⟩, ⟨['ɨ'], ['S', 'M', '.', '3', 'M', 'S'], some '-'⟩, ⟨['m', 'ɛ', 't', 's', '\'', 'ɨ', 'ʔ'], ['c', 'o', 'm', 'e', '.', 'I', 'P', 'F', 'V'], some '-'⟩]⟩, ⟨['r', 'ɛ', 's', 'i', 'ʕ', '-', 'ɛ'], ['f', 'o', 'r', 'g', 'e', 't', '.', 'G', 'E', 'R', '-', 'S', 'M', '.', '1', 'S'], [⟨['r', 'ɛ', 's', 'i', 'ʕ'], ['f', 'o', 'r', 'g', 'e', 't', '.', 'G', 'E', 'R'], none⟩, ⟨['ɛ'], ['S', 'M', '.', '1', 'S'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb_class", "factive"), ("typer", "kemzi"), ("matrix_verb", "forget")] }

def ex_31 : Datum :=
  { id := "cacchioli2026_31"
    source := ⟨"cacchioli-2026", "ch. 3, ex. (31)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "kɛm-z-ɨ-fɛt-wa jɨ-ʔɛmɨn"
    glossedTokens := [("kɛm-z-ɨ-fɛt-wa", "COMP-REL-SM.3MS-like.IPFV-OM.3FS"), ("jɨ-ʔɛmɨn", "SM.3MS-admit.IPFV")]
    glossedWords := [⟨['k', 'ɛ', 'm', '-', 'z', '-', 'ɨ', '-', 'f', 'ɛ', 't', '-', 'w', 'a'], ['C', 'O', 'M', 'P', '-', 'R', 'E', 'L', '-', 'S', 'M', '.', '3', 'M', 'S', '-', 'l', 'i', 'k', 'e', '.', 'I', 'P', 'F', 'V', '-', 'O', 'M', '.', '3', 'F', 'S'], [⟨['k', 'ɛ', 'm'], ['C', 'O', 'M', 'P'], none⟩, ⟨['z'], ['R', 'E', 'L'], some '-'⟩, ⟨['ɨ'], ['S', 'M', '.', '3', 'M', 'S'], some '-'⟩, ⟨['f', 'ɛ', 't'], ['l', 'i', 'k', 'e', '.', 'I', 'P', 'F', 'V'], some '-'⟩, ⟨['w', 'a'], ['O', 'M', '.', '3', 'F', 'S'], some '-'⟩]⟩, ⟨['j', 'ɨ', '-', 'ʔ', 'ɛ', 'm', 'ɨ', 'n'], ['S', 'M', '.', '3', 'M', 'S', '-', 'a', 'd', 'm', 'i', 't', '.', 'I', 'P', 'F', 'V'], [⟨['j', 'ɨ'], ['S', 'M', '.', '3', 'M', 'S'], none⟩, ⟨['ʔ', 'ɛ', 'm', 'ɨ', 'n'], ['a', 'd', 'm', 'i', 't', '.', 'I', 'P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb_class", "factive"), ("typer", "kemzi"), ("matrix_verb", "admit")] }

def ex_32 : Datum :=
  { id := "cacchioli2026_32"
    source := ⟨"cacchioli-2026", "ch. 3, ex. (32)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "ħaʃɛrɛ-tat kɛm-z-ɨ-fɛttu jɨ-qɛbɨl"
    glossedTokens := [("ħaʃɛrɛ-tat", "spider.P"), ("kɛm-z-ɨ-fɛttu", "COMP-REL-SM.1S-like.IPFV"), ("jɨ-qɛbɨl", "SM.1S-accept.IPFV")]
    glossedWords := [⟨['ħ', 'a', 'ʃ', 'ɛ', 'r', 'ɛ', '-', 't', 'a', 't'], ['s', 'p', 'i', 'd', 'e', 'r', '.', 'P'], []⟩, ⟨['k', 'ɛ', 'm', '-', 'z', '-', 'ɨ', '-', 'f', 'ɛ', 't', 't', 'u'], ['C', 'O', 'M', 'P', '-', 'R', 'E', 'L', '-', 'S', 'M', '.', '1', 'S', '-', 'l', 'i', 'k', 'e', '.', 'I', 'P', 'F', 'V'], [⟨['k', 'ɛ', 'm'], ['C', 'O', 'M', 'P'], none⟩, ⟨['z'], ['R', 'E', 'L'], some '-'⟩, ⟨['ɨ'], ['S', 'M', '.', '1', 'S'], some '-'⟩, ⟨['f', 'ɛ', 't', 't', 'u'], ['l', 'i', 'k', 'e', '.', 'I', 'P', 'F', 'V'], some '-'⟩]⟩, ⟨['j', 'ɨ', '-', 'q', 'ɛ', 'b', 'ɨ', 'l'], ['S', 'M', '.', '1', 'S', '-', 'a', 'c', 'c', 'e', 'p', 't', '.', 'I', 'P', 'F', 'V'], [⟨['j', 'ɨ'], ['S', 'M', '.', '1', 'S'], none⟩, ⟨['q', 'ɛ', 'b', 'ɨ', 'l'], ['a', 'c', 'c', 'e', 'p', 't', '.', 'I', 'P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb_class", "factive"), ("typer", "kemzi"), ("matrix_verb", "accept")] }

def ex_33 : Datum :=
  { id := "cacchioli2026_33"
    source := ⟨"cacchioli-2026", "ch. 3, ex. (33)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "ʔaman Tɛsfay mɛts'ħafti kɛm-z-ɨ-ʃɛjɨt jɨ-ħasɨb"
    glossedTokens := [("ʔaman", "Aman"), ("Tɛsfay", "Tesfay"), ("mɛts'ħafti", "book.FP"), ("kɛm-z-ɨ-ʃɛjɨt", "COMP-REL-SM.3MS-sell.IPFV"), ("jɨ-ħasɨb", "SM.3MS-think.IPFV")]
    glossedWords := [⟨['ʔ', 'a', 'm', 'a', 'n'], ['A', 'm', 'a', 'n'], [⟨['ʔ', 'a', 'm', 'a', 'n'], ['A', 'm', 'a', 'n'], none⟩]⟩, ⟨['T', 'ɛ', 's', 'f', 'a', 'y'], ['T', 'e', 's', 'f', 'a', 'y'], [⟨['T', 'ɛ', 's', 'f', 'a', 'y'], ['T', 'e', 's', 'f', 'a', 'y'], none⟩]⟩, ⟨['m', 'ɛ', 't', 's', '\'', 'ħ', 'a', 'f', 't', 'i'], ['b', 'o', 'o', 'k', '.', 'F', 'P'], [⟨['m', 'ɛ', 't', 's', '\'', 'ħ', 'a', 'f', 't', 'i'], ['b', 'o', 'o', 'k', '.', 'F', 'P'], none⟩]⟩, ⟨['k', 'ɛ', 'm', '-', 'z', '-', 'ɨ', '-', 'ʃ', 'ɛ', 'j', 'ɨ', 't'], ['C', 'O', 'M', 'P', '-', 'R', 'E', 'L', '-', 'S', 'M', '.', '3', 'M', 'S', '-', 's', 'e', 'l', 'l', '.', 'I', 'P', 'F', 'V'], [⟨['k', 'ɛ', 'm'], ['C', 'O', 'M', 'P'], none⟩, ⟨['z'], ['R', 'E', 'L'], some '-'⟩, ⟨['ɨ'], ['S', 'M', '.', '3', 'M', 'S'], some '-'⟩, ⟨['ʃ', 'ɛ', 'j', 'ɨ', 't'], ['s', 'e', 'l', 'l', '.', 'I', 'P', 'F', 'V'], some '-'⟩]⟩, ⟨['j', 'ɨ', '-', 'ħ', 'a', 's', 'ɨ', 'b'], ['S', 'M', '.', '3', 'M', 'S', '-', 't', 'h', 'i', 'n', 'k', '.', 'I', 'P', 'F', 'V'], [⟨['j', 'ɨ'], ['S', 'M', '.', '3', 'M', 'S'], none⟩, ⟨['ħ', 'a', 's', 'ɨ', 'b'], ['t', 'h', 'i', 'n', 'k', '.', 'I', 'P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb_class", "cognitive_non_factive"), ("typer", "kemzi"), ("matrix_verb", "think")] }

def ex_34 : Datum :=
  { id := "cacchioli2026_34"
    source := ⟨"cacchioli-2026", "ch. 3, ex. (34)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "ʔaman Tɛsfay mɛts'ħafti kɛm-z-ɨ-ʃɛjɨt jɨ-ʔamɨn"
    glossedTokens := [("ʔaman", "Aman"), ("Tɛsfay", "Tesfay"), ("mɛts'ħafti", "book.FP"), ("kɛm-z-ɨ-ʃɛjɨt", "COMP-REL-SM.3MS-sell.IPFV"), ("jɨ-ʔamɨn", "SM.3MS-believe.IPFV")]
    glossedWords := [⟨['ʔ', 'a', 'm', 'a', 'n'], ['A', 'm', 'a', 'n'], [⟨['ʔ', 'a', 'm', 'a', 'n'], ['A', 'm', 'a', 'n'], none⟩]⟩, ⟨['T', 'ɛ', 's', 'f', 'a', 'y'], ['T', 'e', 's', 'f', 'a', 'y'], [⟨['T', 'ɛ', 's', 'f', 'a', 'y'], ['T', 'e', 's', 'f', 'a', 'y'], none⟩]⟩, ⟨['m', 'ɛ', 't', 's', '\'', 'ħ', 'a', 'f', 't', 'i'], ['b', 'o', 'o', 'k', '.', 'F', 'P'], [⟨['m', 'ɛ', 't', 's', '\'', 'ħ', 'a', 'f', 't', 'i'], ['b', 'o', 'o', 'k', '.', 'F', 'P'], none⟩]⟩, ⟨['k', 'ɛ', 'm', '-', 'z', '-', 'ɨ', '-', 'ʃ', 'ɛ', 'j', 'ɨ', 't'], ['C', 'O', 'M', 'P', '-', 'R', 'E', 'L', '-', 'S', 'M', '.', '3', 'M', 'S', '-', 's', 'e', 'l', 'l', '.', 'I', 'P', 'F', 'V'], [⟨['k', 'ɛ', 'm'], ['C', 'O', 'M', 'P'], none⟩, ⟨['z'], ['R', 'E', 'L'], some '-'⟩, ⟨['ɨ'], ['S', 'M', '.', '3', 'M', 'S'], some '-'⟩, ⟨['ʃ', 'ɛ', 'j', 'ɨ', 't'], ['s', 'e', 'l', 'l', '.', 'I', 'P', 'F', 'V'], some '-'⟩]⟩, ⟨['j', 'ɨ', '-', 'ʔ', 'a', 'm', 'ɨ', 'n'], ['S', 'M', '.', '3', 'M', 'S', '-', 'b', 'e', 'l', 'i', 'e', 'v', 'e', '.', 'I', 'P', 'F', 'V'], [⟨['j', 'ɨ'], ['S', 'M', '.', '3', 'M', 'S'], none⟩, ⟨['ʔ', 'a', 'm', 'ɨ', 'n'], ['b', 'e', 'l', 'i', 'e', 'v', 'e', '.', 'I', 'P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb_class", "cognitive_non_factive"), ("typer", "kemzi"), ("matrix_verb", "believe")] }

def ex_35 : Datum :=
  { id := "cacchioli2026_35"
    source := ⟨"cacchioli-2026", "ch. 3, ex. (35)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "nsu gɛnzɛb kɛm-z-ɨ-sɛrrɨx jɨ-t'ɨrɨt'r-o"
    glossedTokens := [("nsu", "he"), ("gɛnzɛb", "money"), ("kɛm-z-ɨ-sɛrrɨx", "COMP-REL-SM.3MS-steal.IPFV"), ("jɨ-t'ɨrɨt'r-o", "SM.3MS-suspect.IPFV-OM.3MS")]
    glossedWords := [⟨['n', 's', 'u'], ['h', 'e'], [⟨['n', 's', 'u'], ['h', 'e'], none⟩]⟩, ⟨['g', 'ɛ', 'n', 'z', 'ɛ', 'b'], ['m', 'o', 'n', 'e', 'y'], [⟨['g', 'ɛ', 'n', 'z', 'ɛ', 'b'], ['m', 'o', 'n', 'e', 'y'], none⟩]⟩, ⟨['k', 'ɛ', 'm', '-', 'z', '-', 'ɨ', '-', 's', 'ɛ', 'r', 'r', 'ɨ', 'x'], ['C', 'O', 'M', 'P', '-', 'R', 'E', 'L', '-', 'S', 'M', '.', '3', 'M', 'S', '-', 's', 't', 'e', 'a', 'l', '.', 'I', 'P', 'F', 'V'], [⟨['k', 'ɛ', 'm'], ['C', 'O', 'M', 'P'], none⟩, ⟨['z'], ['R', 'E', 'L'], some '-'⟩, ⟨['ɨ'], ['S', 'M', '.', '3', 'M', 'S'], some '-'⟩, ⟨['s', 'ɛ', 'r', 'r', 'ɨ', 'x'], ['s', 't', 'e', 'a', 'l', '.', 'I', 'P', 'F', 'V'], some '-'⟩]⟩, ⟨['j', 'ɨ', '-', 't', '\'', 'ɨ', 'r', 'ɨ', 't', '\'', 'r', '-', 'o'], ['S', 'M', '.', '3', 'M', 'S', '-', 's', 'u', 's', 'p', 'e', 'c', 't', '.', 'I', 'P', 'F', 'V', '-', 'O', 'M', '.', '3', 'M', 'S'], [⟨['j', 'ɨ'], ['S', 'M', '.', '3', 'M', 'S'], none⟩, ⟨['t', '\'', 'ɨ', 'r', 'ɨ', 't', '\'', 'r'], ['s', 'u', 's', 'p', 'e', 'c', 't', '.', 'I', 'P', 'F', 'V'], some '-'⟩, ⟨['o'], ['O', 'M', '.', '3', 'M', 'S'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb_class", "cognitive_non_factive"), ("typer", "kemzi"), ("matrix_verb", "suspect")] }

def ex_51 : Datum :=
  { id := "cacchioli2026_51"
    source := ⟨"cacchioli-2026", "ch. 3, ex. (51)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "qɛbaʔi kɛm-zɨ-kon-ɨt sɛmiʕ-ɛ"
    glossedTokens := [("qɛbaʔi", "painter"), ("kɛm-zɨ-kon-ɨt", "COMP-REL-become.PFV-SM.3FS"), ("sɛmiʕ-ɛ", "hear.GER-SM.1S")]
    glossedWords := [⟨['q', 'ɛ', 'b', 'a', 'ʔ', 'i'], ['p', 'a', 'i', 'n', 't', 'e', 'r'], [⟨['q', 'ɛ', 'b', 'a', 'ʔ', 'i'], ['p', 'a', 'i', 'n', 't', 'e', 'r'], none⟩]⟩, ⟨['k', 'ɛ', 'm', '-', 'z', 'ɨ', '-', 'k', 'o', 'n', '-', 'ɨ', 't'], ['C', 'O', 'M', 'P', '-', 'R', 'E', 'L', '-', 'b', 'e', 'c', 'o', 'm', 'e', '.', 'P', 'F', 'V', '-', 'S', 'M', '.', '3', 'F', 'S'], [⟨['k', 'ɛ', 'm'], ['C', 'O', 'M', 'P'], none⟩, ⟨['z', 'ɨ'], ['R', 'E', 'L'], some '-'⟩, ⟨['k', 'o', 'n'], ['b', 'e', 'c', 'o', 'm', 'e', '.', 'P', 'F', 'V'], some '-'⟩, ⟨['ɨ', 't'], ['S', 'M', '.', '3', 'F', 'S'], some '-'⟩]⟩, ⟨['s', 'ɛ', 'm', 'i', 'ʕ', '-', 'ɛ'], ['h', 'e', 'a', 'r', '.', 'G', 'E', 'R', '-', 'S', 'M', '.', '1', 'S'], [⟨['s', 'ɛ', 'm', 'i', 'ʕ'], ['h', 'e', 'a', 'r', '.', 'G', 'E', 'R'], none⟩, ⟨['ɛ'], ['S', 'M', '.', '1', 'S'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb_class", "perception"), ("typer", "kemzi"), ("matrix_verb", "hear")] }

def ex_52a : Datum :=
  { id := "cacchioli2026_52a"
    source := ⟨"cacchioli-2026", "ch. 3, ex. (52a)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "nɨsatom kɛm-zɨ-tɛmɛrʕa-wu rɨʔɛy-ɛ"
    glossedTokens := [("nɨsatom", "they"), ("kɛm-zɨ-Ø-tɛmɛrʕa-wu", "COMP-REL-SM.3MP-marry.IPFV-SM.3MP"), ("rɨʔɛy-ɛ", "see.GER-SM.1S")]
    glossedWords := [⟨['n', 'ɨ', 's', 'a', 't', 'o', 'm'], ['t', 'h', 'e', 'y'], [⟨['n', 'ɨ', 's', 'a', 't', 'o', 'm'], ['t', 'h', 'e', 'y'], none⟩]⟩, ⟨['k', 'ɛ', 'm', '-', 'z', 'ɨ', '-', 'Ø', '-', 't', 'ɛ', 'm', 'ɛ', 'r', 'ʕ', 'a', '-', 'w', 'u'], ['C', 'O', 'M', 'P', '-', 'R', 'E', 'L', '-', 'S', 'M', '.', '3', 'M', 'P', '-', 'm', 'a', 'r', 'r', 'y', '.', 'I', 'P', 'F', 'V', '-', 'S', 'M', '.', '3', 'M', 'P'], [⟨['k', 'ɛ', 'm'], ['C', 'O', 'M', 'P'], none⟩, ⟨['z', 'ɨ'], ['R', 'E', 'L'], some '-'⟩, ⟨['Ø'], ['S', 'M', '.', '3', 'M', 'P'], some '-'⟩, ⟨['t', 'ɛ', 'm', 'ɛ', 'r', 'ʕ', 'a'], ['m', 'a', 'r', 'r', 'y', '.', 'I', 'P', 'F', 'V'], some '-'⟩, ⟨['w', 'u'], ['S', 'M', '.', '3', 'M', 'P'], some '-'⟩]⟩, ⟨['r', 'ɨ', 'ʔ', 'ɛ', 'y', '-', 'ɛ'], ['s', 'e', 'e', '.', 'G', 'E', 'R', '-', 'S', 'M', '.', '1', 'S'], [⟨['r', 'ɨ', 'ʔ', 'ɛ', 'y'], ['s', 'e', 'e', '.', 'G', 'E', 'R'], none⟩, ⟨['ɛ'], ['S', 'M', '.', '1', 'S'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("nɨsatom kɛm-zɨ-tɛmɛrʕa-wu ʔɨl-ɛ rɨʔɛy-ɛ", .ungrammatical)]
    readings := []
    paperFeatures := [("verb_class", "perception"), ("typer", "kemzi"), ("matrix_verb", "see")] }

def ex_53 : Datum :=
  { id := "cacchioli2026_53"
    source := ⟨"cacchioli-2026", "ch. 3, ex. (53)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "nsu gɛnzɛb jɨ-sɛrrɨx ʔɨl-ɛ jɨ-t'ɨrɨt'r-o"
    glossedTokens := [("nsu", "he"), ("gɛnzɛb", "money"), ("jɨ-sɛrrɨx", "SM.3MS-steal.IPFV"), ("ʔɨl-ɛ", "COMP-SM.1S"), ("jɨ-t'ɨrɨt'r-o", "SM.1S-suspect.IPFV-OM.3MS")]
    glossedWords := [⟨['n', 's', 'u'], ['h', 'e'], [⟨['n', 's', 'u'], ['h', 'e'], none⟩]⟩, ⟨['g', 'ɛ', 'n', 'z', 'ɛ', 'b'], ['m', 'o', 'n', 'e', 'y'], [⟨['g', 'ɛ', 'n', 'z', 'ɛ', 'b'], ['m', 'o', 'n', 'e', 'y'], none⟩]⟩, ⟨['j', 'ɨ', '-', 's', 'ɛ', 'r', 'r', 'ɨ', 'x'], ['S', 'M', '.', '3', 'M', 'S', '-', 's', 't', 'e', 'a', 'l', '.', 'I', 'P', 'F', 'V'], [⟨['j', 'ɨ'], ['S', 'M', '.', '3', 'M', 'S'], none⟩, ⟨['s', 'ɛ', 'r', 'r', 'ɨ', 'x'], ['s', 't', 'e', 'a', 'l', '.', 'I', 'P', 'F', 'V'], some '-'⟩]⟩, ⟨['ʔ', 'ɨ', 'l', '-', 'ɛ'], ['C', 'O', 'M', 'P', '-', 'S', 'M', '.', '1', 'S'], [⟨['ʔ', 'ɨ', 'l'], ['C', 'O', 'M', 'P'], none⟩, ⟨['ɛ'], ['S', 'M', '.', '1', 'S'], some '-'⟩]⟩, ⟨['j', 'ɨ', '-', 't', '\'', 'ɨ', 'r', 'ɨ', 't', '\'', 'r', '-', 'o'], ['S', 'M', '.', '1', 'S', '-', 's', 'u', 's', 'p', 'e', 'c', 't', '.', 'I', 'P', 'F', 'V', '-', 'O', 'M', '.', '3', 'M', 'S'], [⟨['j', 'ɨ'], ['S', 'M', '.', '1', 'S'], none⟩, ⟨['t', '\'', 'ɨ', 'r', 'ɨ', 't', '\'', 'r'], ['s', 'u', 's', 'p', 'e', 'c', 't', '.', 'I', 'P', 'F', 'V'], some '-'⟩, ⟨['o'], ['O', 'M', '.', '3', 'M', 'S'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb_class", "cognitive_non_factive"), ("typer", "ilu"), ("matrix_verb", "suspect")] }

def ex_54 : Datum :=
  { id := "cacchioli2026_54"
    source := ⟨"cacchioli-2026", "ch. 3, ex. (54)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "Tɛsfay ʔaman kɛlbi gɛziʔ-u ʔɨl-u ħalim-u"
    glossedTokens := [("Tɛsfay", "Tesfay"), ("ʔaman", "Aman"), ("kɛlbi", "dog"), ("gɛziʔ-u", "buy.GER-SM.3MS"), ("ʔɨl-u", "COMP-SM.3MS"), ("ħalim-u", "dream.GER-SM.3MS")]
    glossedWords := [⟨['T', 'ɛ', 's', 'f', 'a', 'y'], ['T', 'e', 's', 'f', 'a', 'y'], [⟨['T', 'ɛ', 's', 'f', 'a', 'y'], ['T', 'e', 's', 'f', 'a', 'y'], none⟩]⟩, ⟨['ʔ', 'a', 'm', 'a', 'n'], ['A', 'm', 'a', 'n'], [⟨['ʔ', 'a', 'm', 'a', 'n'], ['A', 'm', 'a', 'n'], none⟩]⟩, ⟨['k', 'ɛ', 'l', 'b', 'i'], ['d', 'o', 'g'], [⟨['k', 'ɛ', 'l', 'b', 'i'], ['d', 'o', 'g'], none⟩]⟩, ⟨['g', 'ɛ', 'z', 'i', 'ʔ', '-', 'u'], ['b', 'u', 'y', '.', 'G', 'E', 'R', '-', 'S', 'M', '.', '3', 'M', 'S'], [⟨['g', 'ɛ', 'z', 'i', 'ʔ'], ['b', 'u', 'y', '.', 'G', 'E', 'R'], none⟩, ⟨['u'], ['S', 'M', '.', '3', 'M', 'S'], some '-'⟩]⟩, ⟨['ʔ', 'ɨ', 'l', '-', 'u'], ['C', 'O', 'M', 'P', '-', 'S', 'M', '.', '3', 'M', 'S'], [⟨['ʔ', 'ɨ', 'l'], ['C', 'O', 'M', 'P'], none⟩, ⟨['u'], ['S', 'M', '.', '3', 'M', 'S'], some '-'⟩]⟩, ⟨['ħ', 'a', 'l', 'i', 'm', '-', 'u'], ['d', 'r', 'e', 'a', 'm', '.', 'G', 'E', 'R', '-', 'S', 'M', '.', '3', 'M', 'S'], [⟨['ħ', 'a', 'l', 'i', 'm'], ['d', 'r', 'e', 'a', 'm', '.', 'G', 'E', 'R'], none⟩, ⟨['u'], ['S', 'M', '.', '3', 'M', 'S'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb_class", "fiction"), ("typer", "ilu"), ("matrix_verb", "dream")] }

def ex_55 : Datum :=
  { id := "cacchioli2026_55"
    source := ⟨"cacchioli-2026", "ch. 3, ex. (55)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "dɛmamu ʔanats'u jɨ-bɛlɨʕ-u ʔɨl-ɛ ʔanbib-ɛ"
    glossedTokens := [("dɛmamu", "cat.MP"), ("ʔanats'u", "mouse.MP"), ("jɨ-bɛlɨʕ-u", "SM.3MP-eat.IPFV-SM.3MP"), ("ʔɨl-ɛ", "COMP-SM.1S"), ("ʔanbib-ɛ", "read.GER-SM.1S")]
    glossedWords := [⟨['d', 'ɛ', 'm', 'a', 'm', 'u'], ['c', 'a', 't', '.', 'M', 'P'], [⟨['d', 'ɛ', 'm', 'a', 'm', 'u'], ['c', 'a', 't', '.', 'M', 'P'], none⟩]⟩, ⟨['ʔ', 'a', 'n', 'a', 't', 's', '\'', 'u'], ['m', 'o', 'u', 's', 'e', '.', 'M', 'P'], [⟨['ʔ', 'a', 'n', 'a', 't', 's', '\'', 'u'], ['m', 'o', 'u', 's', 'e', '.', 'M', 'P'], none⟩]⟩, ⟨['j', 'ɨ', '-', 'b', 'ɛ', 'l', 'ɨ', 'ʕ', '-', 'u'], ['S', 'M', '.', '3', 'M', 'P', '-', 'e', 'a', 't', '.', 'I', 'P', 'F', 'V', '-', 'S', 'M', '.', '3', 'M', 'P'], [⟨['j', 'ɨ'], ['S', 'M', '.', '3', 'M', 'P'], none⟩, ⟨['b', 'ɛ', 'l', 'ɨ', 'ʕ'], ['e', 'a', 't', '.', 'I', 'P', 'F', 'V'], some '-'⟩, ⟨['u'], ['S', 'M', '.', '3', 'M', 'P'], some '-'⟩]⟩, ⟨['ʔ', 'ɨ', 'l', '-', 'ɛ'], ['C', 'O', 'M', 'P', '-', 'S', 'M', '.', '1', 'S'], [⟨['ʔ', 'ɨ', 'l'], ['C', 'O', 'M', 'P'], none⟩, ⟨['ɛ'], ['S', 'M', '.', '1', 'S'], some '-'⟩]⟩, ⟨['ʔ', 'a', 'n', 'b', 'i', 'b', '-', 'ɛ'], ['r', 'e', 'a', 'd', '.', 'G', 'E', 'R', '-', 'S', 'M', '.', '1', 'S'], [⟨['ʔ', 'a', 'n', 'b', 'i', 'b'], ['r', 'e', 'a', 'd', '.', 'G', 'E', 'R'], none⟩, ⟨['ɛ'], ['S', 'M', '.', '1', 'S'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb_class", "utterance"), ("typer", "ilu"), ("matrix_verb", "read")] }

def all : List Datum := [ex_5b, ex_12a, ex_14, ex_15, ex_16, ex_20, ex_21, ex_22, ex_23, ex_24, ex_25, ex_29, ex_30, ex_31, ex_32, ex_33, ex_34, ex_35, ex_51, ex_52a, ex_53, ex_54, ex_55]

end Cacchioli2026.Examples
