module

public import Linglib.Data.Examples.Schema

/-!
# `Krifka1998` — typed example data

Auto-generated from `Linglib/Data/Examples/Krifka1998.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Krifka1998.Examples`.
-/

@[expose] public section

namespace Krifka1998.Examples

def ex11a : Datum :=
  { id := "krifka1998_ex11a"
    source := ⟨"krifka-1998", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "two kilograms of apples"
    glossedTokens := []
    context := "Nominal measure construction with an extensive measure function."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("measureFunction", "extensive")] }

def ex11b : Datum :=
  { id := "krifka1998_ex11b"
    source := ⟨"krifka-1998", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "two bags of money"
    glossedTokens := []
    context := "A container used as an extensive measure function."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("measureFunction", "extensive")] }

def ex11c : Datum :=
  { id := "krifka1998_ex11c"
    source := ⟨"krifka-1998", "(11c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "sixty degree Celsius of water"
    glossedTokens := []
    context := "Nominal measure construction with a non-extensive measure function."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("measureFunction", "nonExtensive")] }

def ex11d : Datum :=
  { id := "krifka1998_ex11d"
    source := ⟨"krifka-1998", "(11d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "eighteen carats of gold"
    glossedTokens := []
    context := "Nominal measure construction with a non-extensive measure function."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("measureFunction", "nonExtensive")] }

def ex12c : Datum :=
  { id := "krifka1998_ex12c"
    source := ⟨"krifka-1998", "(12c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "hundred grams of five hundred meters of wool"
    glossedTokens := []
    context := "A measure phrase applied to a predicate that is already quantized; contrast (12a) hundred grams of wool and (12b) five hundred meters of wool."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("measureFunction", "extensive")] }

def ex58 : Datum :=
  { id := "krifka1998_ex58"
    source := ⟨"krifka-1998", "(58)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is an incredibly fast eater. Yesterday she ate peanuts in 0.43 seconds!"
    glossedTokens := []
    context := "An interval adverbial with a non-quantized but temporally atomic predicate."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "in")] }

def ex60a : Datum :=
  { id := "krifka1998_ex60a"
    source := ⟨"krifka-1998", "(60a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary wrote something in 10 minutes."
    glossedTokens := []
    context := "A non-quantized object that nevertheless yields a telic predicate; the paper gives the indefinite wide scope over the adverbial."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "in")] }

def ex60b : Datum :=
  { id := "krifka1998_ex60b"
    source := ⟨"krifka-1998", "(60b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary ate more than three apples in an hour."
    glossedTokens := []
    context := "A non-quantized, cumulative object that nevertheless yields a telic predicate."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "in")] }

def ex60c : Datum :=
  { id := "krifka1998_ex60c"
    source := ⟨"krifka-1998", "(60c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary ate a quantity of porridge in an hour."
    glossedTokens := []
    context := "A non-quantized, cumulative object that nevertheless yields a telic predicate."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "in")] }

def ex66a : Datum :=
  { id := "krifka1998_ex66a"
    source := ⟨"krifka-1998", "(66a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Juan se tomó una copa de vino anoche antes de acostarse."
    glossedTokens := []
    context := "The reflexive clitic se with a telic predicate."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clitic", "se")] }

def ex66b : Datum :=
  { id := "krifka1998_ex66b"
    source := ⟨"krifka-1998", "(66b)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Juan se tomó vino anoche antes de acostarse."
    glossedTokens := []
    context := "The reflexive clitic se with an atelic predicate; without se the sentence is fine."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("clitic", "se")] }

def ex74 : Datum :=
  { id := "krifka1998_ex74"
    source := ⟨"krifka-1998", "(74)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary walked from the university to the capitol."
    glossedTokens := []
    context := "A movement with a specified source and goal; telic, so it takes in an hour."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("path", "sourceGoal")] }

def ex75 : Datum :=
  { id := "krifka1998_ex75"
    source := ⟨"krifka-1998", "(75)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary walked from the university towards the capitol."
    glossedTokens := []
    context := "A movement with a specified source and direction, read as an initial part of a movement to the goal; not telic."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("path", "sourceDirection")] }

def ex75_in : Datum :=
  { id := "krifka1998_ex75_in"
    source := ⟨"krifka-1998", "(75)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "walk from the university towards the capitol in an hour"
    glossedTokens := []
    context := "An interval adverbial with a directed but goalless movement."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("path", "sourceDirection"), ("adverbial", "in")] }

def ex77a_in : Datum :=
  { id := "krifka1998_ex77a_in"
    source := ⟨"krifka-1998", "(77a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary baked the lobster till half done in an hour."
    glossedTokens := []
    context := "A change on the scale of doneness with an explicitly specified goal."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("goal", "specified"), ("adverbial", "in")] }

def ex77a_for : Datum :=
  { id := "krifka1998_ex77a_for"
    source := ⟨"krifka-1998", "(77a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary baked the lobster till half done for an hour."
    glossedTokens := []
    context := "A change on the scale of doneness with an explicitly specified goal."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("goal", "specified"), ("adverbial", "for")] }

def ex77b_in : Datum :=
  { id := "krifka1998_ex77b_in"
    source := ⟨"krifka-1998", "(77b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary whipped the cream stiff in an hour."
    glossedTokens := []
    context := "A resultative adjective specifying the goal of the change."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("goal", "specified"), ("adverbial", "in")] }

def ex77b_for : Datum :=
  { id := "krifka1998_ex77b_for"
    source := ⟨"krifka-1998", "(77b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary whipped the cream stiff for an hour."
    glossedTokens := []
    context := "A resultative adjective specifying the goal of the change."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("goal", "specified"), ("adverbial", "for")] }

def ex77c : Datum :=
  { id := "krifka1998_ex77c"
    source := ⟨"krifka-1998", "(77c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary baked the lobster (in an hour / for an hour)."
    glossedTokens := []
    context := "Ambiguous between a change to the natural end state, which takes in an hour, and the bare process, which takes for an hour."
    judgment := .acceptable
    contrasts := []
    readings := [("goal reached (in an hour)", .acceptable), ("process only (for an hour)", .acceptable)]
    paperFeatures := [("goal", "implicit")] }

def ex78 : Datum :=
  { id := "krifka1998_ex78"
    source := ⟨"krifka-1998", "(78)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary arrived in London."
    glossedTokens := []
    context := "An achievement, read as the minimal final part of a movement to London."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("path", "goal")] }

def all : List Datum := [ex11a, ex11b, ex11c, ex11d, ex12c, ex58, ex60a, ex60b, ex60c, ex66a, ex66b, ex74, ex75, ex75_in, ex77a_in, ex77a_for, ex77b_in, ex77b_for, ex77c, ex78]

end Krifka1998.Examples
