module

public import Linglib.Data.Examples.Schema

/-!
# `ChandleeEtAl2019` — typed example data

Auto-generated from `Linglib/Data/Examples/ChandleeEtAl2019.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ChandleeEtAl2019.Examples`.
-/

@[expose] public section

namespace ChandleeEtAl2019.Examples

def hasxintilawas : Datum :=
  { id := "chandleeetal2019_hasxintilawas"
    source := ⟨"chandlee-eyraud-heinz-jardine-rawski-2019", "section 5.2"⟩
    reportedIn := none
    method := some .description
    language := "ines1240"
    primaryText := "hasxintilawas"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.2")] }

def hasxintilawaesh : Datum :=
  { id := "chandleeetal2019_hasxintilawaesh"
    source := ⟨"chandlee-eyraud-heinz-jardine-rawski-2019", "section 5.2"⟩
    reportedIn := none
    method := some .description
    language := "ines1240"
    primaryText := "hasxintilawaʃ"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.2")] }

def all : List Datum := [hasxintilawas, hasxintilawaesh]

end ChandleeEtAl2019.Examples
