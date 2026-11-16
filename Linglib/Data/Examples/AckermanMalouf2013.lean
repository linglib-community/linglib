module

public import Linglib.Data.Examples.Schema

/-!
# `AckermanMalouf2013` — typed example data

Auto-generated from `Linglib/Data/Examples/AckermanMalouf2013.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AckermanMalouf2013.Examples`.
-/

@[expose] public section

namespace AckermanMalouf2013.Examples

def ex_1 : Datum :=
  { id := "ackermanmalouf2013_1"
    source := ⟨"ackerman-malouf-2013", "(1)"⟩
    reportedIn := none
    language := "kala1399"
    primaryText := "aju-nngit-su-liur-vigi-nnit-tuar-tu-u-nngil-aq"
    glossedTokens := [("aju-", "be.good"), ("nngit-", "NEG"), ("su-", "PART"), ("liur-", "make"), ("vigi-", "have.as.place.of"), ("nnit-", "ANTIP"), ("tuar-", "all.the.time"), ("tu-", "PART"), ("u-", "be"), ("nngil-", "NEG"), ("aq", "3SG.IND")]
    glossedWords := [⟨['a', 'j', 'u', '-'], ['b', 'e', '.', 'g', 'o', 'o', 'd'], []⟩, ⟨['n', 'n', 'g', 'i', 't', '-'], ['N', 'E', 'G'], []⟩, ⟨['s', 'u', '-'], ['P', 'A', 'R', 'T'], []⟩, ⟨['l', 'i', 'u', 'r', '-'], ['m', 'a', 'k', 'e'], []⟩, ⟨['v', 'i', 'g', 'i', '-'], ['h', 'a', 'v', 'e', '.', 'a', 's', '.', 'p', 'l', 'a', 'c', 'e', '.', 'o', 'f'], []⟩, ⟨['n', 'n', 'i', 't', '-'], ['A', 'N', 'T', 'I', 'P'], []⟩, ⟨['t', 'u', 'a', 'r', '-'], ['a', 'l', 'l', '.', 't', 'h', 'e', '.', 't', 'i', 'm', 'e'], []⟩, ⟨['t', 'u', '-'], ['P', 'A', 'R', 'T'], []⟩, ⟨['u', '-'], ['b', 'e'], []⟩, ⟨['n', 'n', 'g', 'i', 'l', '-'], ['N', 'E', 'G'], []⟩, ⟨['a', 'q'], ['3', 'S', 'G', '.', 'I', 'N', 'D'], [⟨['a', 'q'], ['3', 'S', 'G', '.', 'I', 'N', 'D'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "polysynthesis"), ("complexity", "enumerative")] }

def all : List Datum := [ex_1]

end AckermanMalouf2013.Examples
