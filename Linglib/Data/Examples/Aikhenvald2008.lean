module

public import Linglib.Data.Examples.Schema

/-!
# `Aikhenvald2008` — typed example data

Auto-generated from `Linglib/Data/Examples/Aikhenvald2008.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Aikhenvald2008.Examples`.
-/

@[expose] public section

namespace Aikhenvald2008.Examples

def ex18_17 : Datum :=
  { id := "aikhenvald2008_ex18_17"
    source := ⟨"aikhenvald-2008", "18.17"⟩
    reportedIn := none
    language := "mana1298"
    primaryText := "dǝ-kǝ-dǝ ñan gu kǝ-ku kiya-dǝ-k ata gra:d"
    glossedTokens := [("dǝ-kǝ-dǝ", "he-POSS-masc.sg"), ("ñan", "child"), ("gu", "water"), ("kǝ-ku", "consume-COMPL.SS"), ("kiya-dǝ-k", "die-3masc.sg-COMPL.DS"), ("ata", "then"), ("gra:d", "cry+3masc.sgBAS.P")]
    glossedWords := [⟨['d', 'ǝ', '-', 'k', 'ǝ', '-', 'd', 'ǝ'], ['h', 'e', '-', 'P', 'O', 'S', 'S', '-', 'm', 'a', 's', 'c', '.', 's', 'g'], [⟨['d', 'ǝ'], ['h', 'e'], none⟩, ⟨['k', 'ǝ'], ['P', 'O', 'S', 'S'], some '-'⟩, ⟨['d', 'ǝ'], ['m', 'a', 's', 'c', '.', 's', 'g'], some '-'⟩]⟩, ⟨['ñ', 'a', 'n'], ['c', 'h', 'i', 'l', 'd'], [⟨['ñ', 'a', 'n'], ['c', 'h', 'i', 'l', 'd'], none⟩]⟩, ⟨['g', 'u'], ['w', 'a', 't', 'e', 'r'], [⟨['g', 'u'], ['w', 'a', 't', 'e', 'r'], none⟩]⟩, ⟨['k', 'ǝ', '-', 'k', 'u'], ['c', 'o', 'n', 's', 'u', 'm', 'e', '-', 'C', 'O', 'M', 'P', 'L', '.', 'S', 'S'], [⟨['k', 'ǝ'], ['c', 'o', 'n', 's', 'u', 'm', 'e'], none⟩, ⟨['k', 'u'], ['C', 'O', 'M', 'P', 'L', '.', 'S', 'S'], some '-'⟩]⟩, ⟨['k', 'i', 'y', 'a', '-', 'd', 'ǝ', '-', 'k'], ['d', 'i', 'e', '-', '3', 'm', 'a', 's', 'c', '.', 's', 'g', '-', 'C', 'O', 'M', 'P', 'L', '.', 'D', 'S'], [⟨['k', 'i', 'y', 'a'], ['d', 'i', 'e'], none⟩, ⟨['d', 'ǝ'], ['3', 'm', 'a', 's', 'c', '.', 's', 'g'], some '-'⟩, ⟨['k'], ['C', 'O', 'M', 'P', 'L', '.', 'D', 'S'], some '-'⟩]⟩, ⟨['a', 't', 'a'], ['t', 'h', 'e', 'n'], [⟨['a', 't', 'a'], ['t', 'h', 'e', 'n'], none⟩]⟩, ⟨['g', 'r', 'a', ':', 'd'], ['c', 'r', 'y', '+', '3', 'm', 'a', 's', 'c', '.', 's', 'g', 'B', 'A', 'S', '.', 'P'], [⟨['g', 'r', 'a', 'd'], ['c', 'r', 'y', '+', '3', 'm', 'a', 's', 'c', '.', 's', 'g', 'B', 'A', 'S', '.', 'P'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("after", .acceptable), ("because", .acceptable)]
    paperFeatures := [] }

def ex18_53 : Datum :=
  { id := "aikhenvald2008_ex18_53"
    source := ⟨"aikhenvald-2008", "18.53"⟩
    reportedIn := none
    language := "mana1298"
    primaryText := "dǝ-kǝ-dǝ ñan kiya-n napa-dǝ-k sǝbǝn-ǝn napa-ku makǝn ata ra:d"
    glossedTokens := [("dǝ-kǝ-dǝ", "he-POSS-masc.sg"), ("ñan", "child"), ("kiya-n", "die-SEQ"), ("napa-dǝ-k", "COMPL.VB-3masc.sg-COMPL.DS"), ("sǝbǝn-ǝn", "return-SEQ"), ("napa-ku", "COMPL.VB-COMPL.SS"), ("makǝn", "in.mourning"), ("ata", "then"), ("ra:d", "sit+3masc.sgBAS.P")]
    glossedWords := [⟨['d', 'ǝ', '-', 'k', 'ǝ', '-', 'd', 'ǝ'], ['h', 'e', '-', 'P', 'O', 'S', 'S', '-', 'm', 'a', 's', 'c', '.', 's', 'g'], [⟨['d', 'ǝ'], ['h', 'e'], none⟩, ⟨['k', 'ǝ'], ['P', 'O', 'S', 'S'], some '-'⟩, ⟨['d', 'ǝ'], ['m', 'a', 's', 'c', '.', 's', 'g'], some '-'⟩]⟩, ⟨['ñ', 'a', 'n'], ['c', 'h', 'i', 'l', 'd'], [⟨['ñ', 'a', 'n'], ['c', 'h', 'i', 'l', 'd'], none⟩]⟩, ⟨['k', 'i', 'y', 'a', '-', 'n'], ['d', 'i', 'e', '-', 'S', 'E', 'Q'], [⟨['k', 'i', 'y', 'a'], ['d', 'i', 'e'], none⟩, ⟨['n'], ['S', 'E', 'Q'], some '-'⟩]⟩, ⟨['n', 'a', 'p', 'a', '-', 'd', 'ǝ', '-', 'k'], ['C', 'O', 'M', 'P', 'L', '.', 'V', 'B', '-', '3', 'm', 'a', 's', 'c', '.', 's', 'g', '-', 'C', 'O', 'M', 'P', 'L', '.', 'D', 'S'], [⟨['n', 'a', 'p', 'a'], ['C', 'O', 'M', 'P', 'L', '.', 'V', 'B'], none⟩, ⟨['d', 'ǝ'], ['3', 'm', 'a', 's', 'c', '.', 's', 'g'], some '-'⟩, ⟨['k'], ['C', 'O', 'M', 'P', 'L', '.', 'D', 'S'], some '-'⟩]⟩, ⟨['s', 'ǝ', 'b', 'ǝ', 'n', '-', 'ǝ', 'n'], ['r', 'e', 't', 'u', 'r', 'n', '-', 'S', 'E', 'Q'], [⟨['s', 'ǝ', 'b', 'ǝ', 'n'], ['r', 'e', 't', 'u', 'r', 'n'], none⟩, ⟨['ǝ', 'n'], ['S', 'E', 'Q'], some '-'⟩]⟩, ⟨['n', 'a', 'p', 'a', '-', 'k', 'u'], ['C', 'O', 'M', 'P', 'L', '.', 'V', 'B', '-', 'C', 'O', 'M', 'P', 'L', '.', 'S', 'S'], [⟨['n', 'a', 'p', 'a'], ['C', 'O', 'M', 'P', 'L', '.', 'V', 'B'], none⟩, ⟨['k', 'u'], ['C', 'O', 'M', 'P', 'L', '.', 'S', 'S'], some '-'⟩]⟩, ⟨['m', 'a', 'k', 'ǝ', 'n'], ['i', 'n', '.', 'm', 'o', 'u', 'r', 'n', 'i', 'n', 'g'], [⟨['m', 'a', 'k', 'ǝ', 'n'], ['i', 'n', '.', 'm', 'o', 'u', 'r', 'n', 'i', 'n', 'g'], none⟩]⟩, ⟨['a', 't', 'a'], ['t', 'h', 'e', 'n'], [⟨['a', 't', 'a'], ['t', 'h', 'e', 'n'], none⟩]⟩, ⟨['r', 'a', ':', 'd'], ['s', 'i', 't', '+', '3', 'm', 'a', 's', 'c', '.', 's', 'g', 'B', 'A', 'S', '.', 'P'], [⟨['r', 'a', 'd'], ['s', 'i', 't', '+', '3', 'm', 'a', 's', 'c', '.', 's', 'g', 'B', 'A', 'S', '.', 'P'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("after", .acceptable), ("because", .unacceptable)]
    paperFeatures := [] }

def all : List Datum := [ex18_17, ex18_53]

end Aikhenvald2008.Examples
