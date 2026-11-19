module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `PullumGazdar1982` — typed example data

Auto-generated from `Linglib/Data/Examples/PullumGazdar1982.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace PullumGazdar1982.Examples`.
-/

@[expose] public section

namespace PullumGazdar1982.Examples

def ex18a : Datum :=
  { id := "pullumgazdar1982_ex18a"
    source := ⟨"pullum-gazdar-1982", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The woman and the men smokes and drinks respectively."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("subject", "the woman"), ("subject", "the men"), ("verb", "smokes"), ("verb", "drinks")] }

def ex18b : Datum :=
  { id := "pullumgazdar1982_ex18b"
    source := ⟨"pullum-gazdar-1982", "(18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The woman and the men smokes and drink respectively."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("subject", "the woman"), ("subject", "the men"), ("verb", "smokes"), ("verb", "drink")] }

def ex18c : Datum :=
  { id := "pullumgazdar1982_ex18c"
    source := ⟨"pullum-gazdar-1982", "(18c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The woman and the men smoke and drinks respectively."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("subject", "the woman"), ("subject", "the men"), ("verb", "smoke"), ("verb", "drinks")] }

def ex18d : Datum :=
  { id := "pullumgazdar1982_ex18d"
    source := ⟨"pullum-gazdar-1982", "(18d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The woman and the men smoke and drink respectively."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("subject", "the woman"), ("subject", "the men"), ("verb", "smoke"), ("verb", "drink")] }

def ex19a : Datum :=
  { id := "pullumgazdar1982_ex19a"
    source := ⟨"pullum-gazdar-1982", "(19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The man and the woman smokes and drinks respectively."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("subject", "the man"), ("subject", "the woman"), ("verb", "smokes"), ("verb", "drinks")] }

def ex19b : Datum :=
  { id := "pullumgazdar1982_ex19b"
    source := ⟨"pullum-gazdar-1982", "(19b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The man and the woman smoke and drink respectively."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "the man"), ("subject", "the woman"), ("verb", "smoke"), ("verb", "drink")] }

def ex25 : Datum :=
  { id := "pullumgazdar1982_ex25"
    source := ⟨"pullum-gazdar-1982", "(25)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "dat Jan Marie Pieter Arabisch laat zien schrijven"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("word", "Marie"), ("word", "Pieter"), ("word", "Arabisch"), ("word", "laat"), ("word", "zien"), ("word", "schrijven")] }

def ex26 : Datum :=
  { id := "pullumgazdar1982_ex26"
    source := ⟨"pullum-gazdar-1982", "(26)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "dat Jan Marie Pieter Arabisch laat zien liegen"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("word", "Marie"), ("word", "Pieter"), ("word", "Arabisch"), ("word", "laat"), ("word", "zien"), ("word", "liegen")] }

def ex27 : Datum :=
  { id := "pullumgazdar1982_ex27"
    source := ⟨"pullum-gazdar-1982", "(27)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "dat Jan Marie Pieter Arabisch Hans laat zien schrijven"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("word", "Marie"), ("word", "Pieter"), ("word", "Arabisch"), ("word", "Hans"), ("word", "laat"), ("word", "zien"), ("word", "schrijven")] }

def ex28 : Datum :=
  { id := "pullumgazdar1982_ex28"
    source := ⟨"pullum-gazdar-1982", "(28)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "dat Jan Marie Pieter Arabisch wil laten zien schrijven"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("word", "Marie"), ("word", "Pieter"), ("word", "Arabisch"), ("word", "wil"), ("word", "laten"), ("word", "zien"), ("word", "schrijven")] }

def ex31 : Datum :=
  { id := "pullumgazdar1982_ex31"
    source := ⟨"pullum-gazdar-1982", "(31)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "(dat Jan) Marie Arabisch Pieter wil laten zien schrijven"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("word", "Marie"), ("word", "Arabisch"), ("word", "Pieter"), ("word", "wil"), ("word", "laten"), ("word", "zien"), ("word", "schrijven")] }

def ex38 : Datum :=
  { id := "pullumgazdar1982_ex38"
    source := ⟨"pullum-gazdar-1982", "(38)"⟩
    reportedIn := none
    method := some .elicitation
    language := "moha1258"
    primaryText := "iʔi knuhsnuhweʔs thikʌ kanuhsa"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("incorporated", "nuhs"), ("external", "nuhs")] }

def ex39 : Datum :=
  { id := "pullumgazdar1982_ex39"
    source := ⟨"pullum-gazdar-1982", "(39)"⟩
    reportedIn := none
    language := "moha1258"
    primaryText := "waʔkhnekahnínuʔ ne otsìʔtsaʔ"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("incorporated", "hnek"), ("external", "tsiʔts")] }

def ex40 : Datum :=
  { id := "pullumgazdar1982_ex40"
    source := ⟨"pullum-gazdar-1982", "(40)"⟩
    reportedIn := none
    language := "moha1258"
    primaryText := "wakeselehtahni:nuʔseʔ neʔ 'bike'"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("incorporated", "seleht"), ("external", "bike")] }

def ex41a : Datum :=
  { id := "pullumgazdar1982_ex41a"
    source := ⟨"pullum-gazdar-1982", "(41a)"⟩
    reportedIn := none
    language := "moha1258"
    primaryText := "kanuhsrakʌ thikʌ kanuhsa"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("incorporated", "nuhs"), ("external", "nuhs")] }

def ex41b : Datum :=
  { id := "pullumgazdar1982_ex41b"
    source := ⟨"pullum-gazdar-1982", "(41b)"⟩
    reportedIn := none
    language := "moha1258"
    primaryText := "kanuhsrakʌ thikʌ"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("incorporated", "nuhs")] }

def ex42 : Datum :=
  { id := "pullumgazdar1982_ex42"
    source := ⟨"pullum-gazdar-1982", "(42)"⟩
    reportedIn := none
    method := some .corpus
    language := "moha1258"
    primaryText := "keliʔwanú:weʔs kiʔ"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("incorporated", "liʔw")] }

def ex43a : Datum :=
  { id := "pullumgazdar1982_ex43a"
    source := ⟨"pullum-gazdar-1982", "(43a)"⟩
    reportedIn := none
    language := "moha1258"
    primaryText := "iʔi k-nuhweʔs ne ka-nuhs-aʔ"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("external", "nuhs")] }

def ex43b : Datum :=
  { id := "pullumgazdar1982_ex43b"
    source := ⟨"pullum-gazdar-1982", "(43b)"⟩
    reportedIn := none
    language := "moha1258"
    primaryText := "iʔi k-nuhweʔs ne sawatis hra-o-nuhs-aʔ"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("external", "nuhs")] }

def ex43c : Datum :=
  { id := "pullumgazdar1982_ex43c"
    source := ⟨"pullum-gazdar-1982", "(43c)"⟩
    reportedIn := none
    language := "moha1258"
    primaryText := "iʔi k-nuhs-nuhweʔs ne sawatis hrao-nuhs-aʔ"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("incorporated", "nuhs"), ("external", "nuhs")] }

def ex43d : Datum :=
  { id := "pullumgazdar1982_ex43d"
    source := ⟨"pullum-gazdar-1982", "(43d)"⟩
    reportedIn := none
    language := "moha1258"
    primaryText := "iʔi hrai-nuhs-nuhweʔs ne sawatis"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("incorporated", "nuhs"), ("external", "sawatis")] }

def ex43e : Datum :=
  { id := "pullumgazdar1982_ex43e"
    source := ⟨"pullum-gazdar-1982", "(43e)"⟩
    reportedIn := none
    language := "moha1258"
    primaryText := "iʔi hrai-nuhweʔs ne sawatis hrao-nuhs-aʔ"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("external", "nuhs")] }

def all : List Datum := [ex18a, ex18b, ex18c, ex18d, ex19a, ex19b, ex25, ex26, ex27, ex28, ex31, ex38, ex39, ex40, ex41a, ex41b, ex42, ex43a, ex43b, ex43c, ex43d, ex43e]

/-- The conjoined subject noun phrases of a *respectively* sentence, in order. -/
inductive Subject where
  /-- the woman: singular -/
  | theWoman
  /-- the men: plural -/
  | theMen
  /-- the man: singular -/
  | theMan
  deriving DecidableEq, Repr, Fintype

/-- The values a row records under `subject`. -/
def subjects (e : Datum) : List Subject :=
  (e.features "subject").filterMap (List.lookup · [("the woman", .theWoman), ("the men", .theMen), ("the man", .theMan)])

/-- The conjoined verbs of a *respectively* sentence, in order. -/
inductive Verb where
  /-- smokes: third person singular present -/
  | smokes
  /-- drinks: third person singular present -/
  | drinks
  /-- smoke: plural present -/
  | smoke
  /-- drink: plural present -/
  | drink
  deriving DecidableEq, Repr, Fintype

/-- The values a row records under `verb`. -/
def verbs (e : Datum) : List Verb :=
  (e.features "verb").filterMap (List.lookup · [("smokes", .smokes), ("drinks", .drinks), ("smoke", .smoke), ("drink", .drink)])

/-- The words of the bracketed Dutch verb phrase, in order. -/
inductive DutchWord where
  /-- Marie: a personal name -/
  | marie
  /-- Pieter: a personal name -/
  | pieter
  /-- Arabisch: 'Arabic' -/
  | arabisch
  /-- Hans: a personal name -/
  | hans
  /-- laat: 'let', finite -/
  | laat
  /-- wil: 'will', finite -/
  | wil
  /-- laten: 'let', infinitive -/
  | laten
  /-- zien: 'see', infinitive -/
  | zien
  /-- schrijven: 'write', infinitive -/
  | schrijven
  /-- liegen: 'lie', infinitive -/
  | liegen
  deriving DecidableEq, Repr, Fintype

/-- The values a row records under `word`. -/
def words (e : Datum) : List DutchWord :=
  (e.features "word").filterMap (List.lookup · [("Marie", .marie), ("Pieter", .pieter), ("Arabisch", .arabisch), ("Hans", .hans),
    ("laat", .laat), ("wil", .wil), ("laten", .laten), ("zien", .zien),
    ("schrijven", .schrijven), ("liegen", .liegen)])

end PullumGazdar1982.Examples
