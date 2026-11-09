module

public import Linglib.Data.Examples.Schema

/-!
# `VanDerWouden1997` — typed example data

Auto-generated from `Linglib/Data/Examples/VanDerWouden1997.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace VanDerWouden1997.Examples`.
-/

@[expose] public section

namespace VanDerWouden1997.Examples

def ex_184a : Datum :=
  { id := "vanderwouden1997_184a"
    source := ⟨"vanderwouden-1997", "(184a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Een van de kinderen gaat ooit bij oma op bezoek."
    glossedTokens := [("Een", "one"), ("van", "of"), ("de", "the"), ("kinderen", "children"), ("gaat", "goes"), ("ooit", "ever"), ("bij", "with"), ("oma", "granny"), ("op", "on"), ("bezoek", "visit")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("item", "ooit"), ("context", "notMonotoneDecreasing")] }

def ex_184b : Datum :=
  { id := "vanderwouden1997_184b"
    source := ⟨"vanderwouden-1997", "(184b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Weinig kinderen gaan ooit bij oma op bezoek."
    glossedTokens := [("Weinig", "few"), ("kinderen", "children"), ("gaan", "go"), ("ooit", "ever"), ("bij", "with"), ("oma", "granny"), ("op", "on"), ("bezoek", "visit")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "ooit"), ("context", "monotoneDecreasing")] }

def ex_184c : Datum :=
  { id := "vanderwouden1997_184c"
    source := ⟨"vanderwouden-1997", "(184c)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Geen van de kinderen gaat ooit bij oma op bezoek."
    glossedTokens := [("Geen", "none"), ("van", "of"), ("de", "the"), ("kinderen", "children"), ("gaat", "goes"), ("ooit", "ever"), ("bij", "with"), ("oma", "granny"), ("op", "on"), ("bezoek", "visit")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "ooit"), ("context", "antiAdditive")] }

def ex_184d : Datum :=
  { id := "vanderwouden1997_184d"
    source := ⟨"vanderwouden-1997", "(184d)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Een van de kinderen gaat niet ooit bij oma op bezoek."
    glossedTokens := [("Een", "one"), ("van", "of"), ("de", "the"), ("kinderen", "children"), ("gaat", "goes"), ("niet", "not"), ("ooit", "ever"), ("bij", "with"), ("oma", "granny"), ("op", "on"), ("bezoek", "visit")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("item", "ooit"), ("context", "antimorphic")] }

def ex_228b : Datum :=
  { id := "vanderwouden1997_228b"
    source := ⟨"vanderwouden-1997", "(228b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Alle boeren die geslagen hoeven te worden bezitten een ezel."
    glossedTokens := [("Alle", "All"), ("boeren", "farmers"), ("die", "that"), ("geslagen", "beaten"), ("hoeven", "need"), ("te", "to"), ("worden", "become"), ("bezitten", "own"), ("een", "a"), ("ezel", "donkey")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("item", "hoeven"), ("context", "universalRestrictor")] }

def ex_228d : Datum :=
  { id := "vanderwouden1997_228d"
    source := ⟨"vanderwouden-1997", "(228d)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Geen boer die een ezel hoeft te bezitten wordt geslagen."
    glossedTokens := [("Geen", "No"), ("boer", "farmer"), ("die", "who"), ("een", "a"), ("ezel", "donkey"), ("hoeft", "needs"), ("te", "to"), ("bezitten", "own"), ("wordt", "is"), ("geslagen", "beaten")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("item", "hoeven"), ("context", "geenRestrictor")] }

def ex_229b : Datum :=
  { id := "vanderwouden1997_229b"
    source := ⟨"vanderwouden-1997", "(229b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Hoef je huiswerk te maken?"
    glossedTokens := [("Hoef", "Need"), ("je", "you"), ("huiswerk", "homework"), ("te", "to"), ("maken", "do")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("item", "hoeven"), ("context", "question")] }

def ex_229d : Datum :=
  { id := "vanderwouden1997_229d"
    source := ⟨"vanderwouden-1997", "(229d)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Als je huiswerk hoeft te maken mag je geen tv kijken."
    glossedTokens := [("Als", "If"), ("je", "you"), ("huiswerk", "homework"), ("hoeft", "need"), ("te", "to"), ("maken", "do"), ("mag", "may"), ("je", "you"), ("geen", "no"), ("tv", "tv"), ("kijken", "watch")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("item", "hoeven"), ("context", "conditionalAntecedent")] }

def ex_232a : Datum :=
  { id := "vanderwouden1997_232a"
    source := ⟨"vanderwouden-1997", "(232a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Hij rijdt harder dan hij hoeft."
    glossedTokens := [("Hij", "He"), ("rijdt", "drives"), ("harder", "faster"), ("dan", "than"), ("hij", "he"), ("hoeft", "needs")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "hoeven"), ("context", "clausalComparative")] }

def ex_233a : Datum :=
  { id := "vanderwouden1997_233a"
    source := ⟨"vanderwouden-1997", "(233a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Dit is de laatste student die we hoeven te bestraffen."
    glossedTokens := [("Dit", "This"), ("is", "is"), ("de", "the"), ("laatste", "last"), ("student", "student"), ("die", ""), ("we", "we"), ("hoeven", "need"), ("te", "to"), ("bestraffen", "punish")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "hoeven"), ("context", "superlative")] }

def ex_234a : Datum :=
  { id := "vanderwouden1997_234a"
    source := ⟨"vanderwouden-1997", "(234a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Alles wat we hoeven te weten staat in dit boek."
    glossedTokens := [("Alles", "Everything"), ("wat", "which"), ("we", "we"), ("hoeven", "need"), ("te", "to"), ("weten", "know"), ("staat", "stands"), ("in", "in"), ("dit", "this"), ("boek", "book")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "hoeven"), ("context", "universalRestrictor")] }

def ex_234c : Datum :=
  { id := "vanderwouden1997_234c"
    source := ⟨"vanderwouden-1997", "(234c)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Ik geloof niet, dat we nog iemand hoeven te waarschuwen."
    glossedTokens := [("Ik", "I"), ("geloof", "believe"), ("niet", "not"), ("dat", "that"), ("we", "we"), ("nog", "still"), ("iemand", "anybody"), ("hoeven", "need"), ("te", "to"), ("waarschuwen", "warn")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "hoeven"), ("context", "doubtVerb")] }

def ex_234e : Datum :=
  { id := "vanderwouden1997_234e"
    source := ⟨"vanderwouden-1997", "(234e)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Ik heb nog een uur voordat ik weg hoef."
    glossedTokens := [("Ik", "I"), ("heb", "have"), ("nog", "still"), ("een", "an"), ("uur", "hour"), ("voordat", "before"), ("ik", "I"), ("weg", "away"), ("hoef", "need")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "hoeven"), ("context", "beforeClause")] }

def all : List Datum := [ex_184a, ex_184b, ex_184c, ex_184d, ex_228b, ex_228d, ex_229b, ex_229d, ex_232a, ex_233a, ex_234a, ex_234c, ex_234e]

end VanDerWouden1997.Examples
