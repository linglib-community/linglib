module

public import Linglib.Data.Examples.Schema

/-!
# `Merchant2001` — typed example data

Auto-generated from `Linglib/Data/Examples/Merchant2001.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Merchant2001.Examples`.
-/

@[expose] public section

namespace Merchant2001.Examples

def german_case_match : Datum :=
  { id := "merchant2001_german_case_match"
    source := ⟨"merchant-2001", "ch. 2, (13)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Er will jemandem schmeicheln, aber sie wissen nicht, wem."
    glossedTokens := [("Er", "he"), ("will", "wants"), ("jemandem", "someone.DAT"), ("schmeicheln", "flatter"), ("aber", "but"), ("sie", "they"), ("wissen", "know"), ("nicht", "not"), ("wem", "who.DAT")]
    glossedWords := [⟨['E', 'r'], ['h', 'e'], [⟨['E', 'r'], ['h', 'e'], none⟩]⟩, ⟨['w', 'i', 'l', 'l'], ['w', 'a', 'n', 't', 's'], [⟨['w', 'i', 'l', 'l'], ['w', 'a', 'n', 't', 's'], none⟩]⟩, ⟨['j', 'e', 'm', 'a', 'n', 'd', 'e', 'm'], ['s', 'o', 'm', 'e', 'o', 'n', 'e', '.', 'D', 'A', 'T'], [⟨['j', 'e', 'm', 'a', 'n', 'd', 'e', 'm'], ['s', 'o', 'm', 'e', 'o', 'n', 'e', '.', 'D', 'A', 'T'], none⟩]⟩, ⟨['s', 'c', 'h', 'm', 'e', 'i', 'c', 'h', 'e', 'l', 'n'], ['f', 'l', 'a', 't', 't', 'e', 'r'], [⟨['s', 'c', 'h', 'm', 'e', 'i', 'c', 'h', 'e', 'l', 'n'], ['f', 'l', 'a', 't', 't', 'e', 'r'], none⟩]⟩, ⟨['a', 'b', 'e', 'r'], ['b', 'u', 't'], [⟨['a', 'b', 'e', 'r'], ['b', 'u', 't'], none⟩]⟩, ⟨['s', 'i', 'e'], ['t', 'h', 'e', 'y'], [⟨['s', 'i', 'e'], ['t', 'h', 'e', 'y'], none⟩]⟩, ⟨['w', 'i', 's', 's', 'e', 'n'], ['k', 'n', 'o', 'w'], [⟨['w', 'i', 's', 's', 'e', 'n'], ['k', 'n', 'o', 'w'], none⟩]⟩, ⟨['n', 'i', 'c', 'h', 't'], ['n', 'o', 't'], [⟨['n', 'i', 'c', 'h', 't'], ['n', 'o', 't'], none⟩]⟩, ⟨['w', 'e', 'm'], ['w', 'h', 'o', '.', 'D', 'A', 'T'], [⟨['w', 'e', 'm'], ['w', 'h', 'o', '.', 'D', 'A', 'T'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Er will jemandem schmeicheln, aber sie wissen nicht, wen.", .ungrammatical)]
    readings := []
    paperFeatures := [("phenomenon", "sluicing"), ("whPhraseCase", "dative"), ("innerAntecedentCase", "dative")] }

def all : List Datum := [german_case_match]

end Merchant2001.Examples
