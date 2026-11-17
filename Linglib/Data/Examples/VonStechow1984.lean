module

public import Linglib.Data.Examples.Schema

/-!
# `VonStechow1984` — typed example data

Auto-generated from `Linglib/Data/Examples/VonStechow1984.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace VonStechow1984.Examples`.
-/

@[expose] public section

namespace VonStechow1984.Examples

def yacht : Datum :=
  { id := "vonstechow1984_yacht"
    source := ⟨"russell-1905", "the yacht anecdote"⟩
    reportedIn := some ⟨"von-stechow-1984", "(1)"⟩
    language := "stan1293"
    primaryText := "I thought that your yacht was larger than it is"
    glossedTokens := []
    context := "A guest to a touchy yacht owner, on first seeing the yacht."
    judgment := .acceptable
    contrasts := []
    readings := [("de re: ACTUALLY in the than-clause, consistent thought", .acceptable), ("de dicto: no ACTUALLY, contradictory thought", .unacceptable)]
    paperFeatures := [("phenomenon", "RA")] }

def ex26 : Datum :=
  { id := "vonstechow1984_ex26"
    source := ⟨"von-stechow-1984", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Mary had smoked less (than she did), she would be healthier (than she is)"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("informative: than-clauses anchored to the actual world by ACTUALLY", .acceptable), ("trivial: than-clauses evaluated in the counterfactual world, antecedent and consequent contradictory", .unacceptable)]
    paperFeatures := [("phenomenon", "AC")] }

def exIII : Datum :=
  { id := "vonstechow1984_exIII"
    source := ⟨"von-stechow-1984", "(iii)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ede is cleverer than anyone of us"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "NPI"), ("polarityItem", "anyone"), ("polarity", "negative")] }

def exIV : Datum :=
  { id := "vonstechow1984_exIV"
    source := ⟨"von-stechow-1984", "(iv)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Max is as well as ever"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "NPI"), ("polarityItem", "ever"), ("polarity", "negative")] }

def ex70 : Datum :=
  { id := "vonstechow1984_ex70"
    source := ⟨"von-stechow-1984", "(70)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Any of my friends could ever solve these problems faster than Ede"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "NPI"), ("polarityItem", "any, ever"), ("polarity", "negative")] }

def ex71 : Datum :=
  { id := "vonstechow1984_ex71"
    source := ⟨"von-stechow-1984", "(71)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ede could solve these problems faster than any of my friends could ever do"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "NPI"), ("polarityItem", "any, ever"), ("polarity", "negative")] }

def ex72a : Datum :=
  { id := "vonstechow1984_ex72a"
    source := ⟨"von-stechow-1984", "(72a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You have already got less support than he has"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "NPI"), ("polarityItem", "already"), ("polarity", "positive")] }

def ex72b : Datum :=
  { id := "vonstechow1984_ex72b"
    source := ⟨"von-stechow-1984", "(72b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He has got more support than you already have"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "NPI"), ("polarityItem", "already"), ("polarity", "positive")] }

def exV : Datum :=
  { id := "vonstechow1984_exV"
    source := ⟨"von-stechow-1984", "(v)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Konstanz is nicer than Düsseldorf or Stuttgart"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "Q&C"), ("entails", "Konstanz is nicer than Düsseldorf and Stuttgart")] }

def exVI : Datum :=
  { id := "vonstechow1984_exVI"
    source := ⟨"von-stechow-1984", "(vi)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ede is fatter than anyone of us"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "Q&C"), ("entails", "Ede is fatter than everyone of us")] }

def exVII : Datum :=
  { id := "vonstechow1984_exVII"
    source := ⟨"von-stechow-1984", "(vii)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ede is fatter than Max"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "UI"), ("doesNotEntail", "Ede is fatter than everyone")] }

def ex99a : Datum :=
  { id := "vonstechow1984_ex99a"
    source := ⟨"von-stechow-1984", "(99a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Irene is prettier than neither Ede nor Senta"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "NQ")] }

def ex99b : Datum :=
  { id := "vonstechow1984_ex99b"
    source := ⟨"von-stechow-1984", "(99b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Irene is prettier than no one of us"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "NQ")] }

def exX : Datum :=
  { id := "vonstechow1984_exX"
    source := ⟨"von-stechow-1984", "(x)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A polar bear could be bigger than a grizzly bear could be"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "modal")] }

def exXI : Datum :=
  { id := "vonstechow1984_exXI"
    source := ⟨"von-stechow-1984", "(xi)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "More silly lectures have been given by more silly professors than I expected"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "multihead")] }

def ex171a : Datum :=
  { id := "vonstechow1984_ex171a"
    source := ⟨"von-stechow-1984", "(171a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is six inches taller than Mary"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "DR")] }

def ex171b : Datum :=
  { id := "vonstechow1984_ex171b"
    source := ⟨"von-stechow-1984", "(171b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ede is twice as fat as Angelika"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "DR")] }

def ex171c : Datum :=
  { id := "vonstechow1984_ex171c"
    source := ⟨"von-stechow-1984", "(171c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ede is more tall than broad"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "DR")] }

def ex217 : Datum :=
  { id := "vonstechow1984_ex217"
    source := ⟨"von-stechow-1984", "(217)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "At least 6 more toads than frogs croak"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "crossCategory"), ("category", "plural noun"), ("measure", "cardinality")] }

def ex218 : Datum :=
  { id := "vonstechow1984_ex218"
    source := ⟨"von-stechow-1984", "(218)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ede owns at most 3 ounces more gold than Kurt"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "crossCategory"), ("category", "mass noun"), ("measure", "amount of the totality")] }

def ex224c : Datum :=
  { id := "vonstechow1984_ex224c"
    source := ⟨"von-stechow-1984", "(224c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Tristan yells three times as loudly as Otto"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "crossCategory"), ("category", "adverb"), ("measure", "loudness")] }

def ex227 : Datum :=
  { id := "vonstechow1984_ex227"
    source := ⟨"von-stechow-1984", "(227)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This pack is at least fifty kilos too heavy to lift"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "too"), ("paraphrase", "If one could lift this pack, then it would be at least 50 kg less heavy than it actually is")] }

def ex230 : Datum :=
  { id := "vonstechow1984_ex230"
    source := ⟨"von-stechow-1984", "(230)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The weather is too good to stay at home"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "too")] }

def all : List Datum := [yacht, ex26, exIII, exIV, ex70, ex71, ex72a, ex72b, exV, exVI, exVII, ex99a, ex99b, exX, exXI, ex171a, ex171b, ex171c, ex217, ex218, ex224c, ex227, ex230]

end VonStechow1984.Examples
