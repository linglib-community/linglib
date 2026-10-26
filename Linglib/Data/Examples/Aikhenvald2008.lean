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
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("after", .acceptable), ("because", .unacceptable)]
    paperFeatures := [] }

def all : List Datum := [ex18_17, ex18_53]

end Aikhenvald2008.Examples
