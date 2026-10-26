module

public import Linglib.Data.Examples.Schema

/-!
# `GinzburgFernandezSchlangen2014` — typed example data

Auto-generated from `Linglib/Data/Examples/GinzburgFernandezSchlangen2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace GinzburgFernandezSchlangen2014.Examples`.
-/

@[expose] public section

namespace GinzburgFernandezSchlangen2014.Examples

def ex_37d : Datum :=
  { id := "ginzburgfernandezschlangen2014_37d"
    source := ⟨"ginzburg-fernandez-schlangen-2014", "(37a), (37d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Is Bo here? B: You mean Jo."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("rule", "backward looking"), ("turn", "taken"), ("u0", "Bo"), ("answer", "Jo")] }

def ex_41 : Datum :=
  { id := "ginzburgfernandezschlangen2014_41"
    source := ⟨"ginzburg-fernandez-schlangen-2014", "(41)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Is Georges here? I meant Jacques."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("rule", "backward looking"), ("turn", "kept"), ("u0", "Georges"), ("answer", "Jacques")] }

def ex_49 : Datum :=
  { id := "ginzburgfernandezschlangen2014_49"
    source := ⟨"ginzburg-fernandez-schlangen-2014", "(49)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Take that book in I mean from the shelf"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("rule", "backward looking"), ("turn", "kept"), ("u0", "in"), ("answer", "from")] }

def ex_54 : Datum :=
  { id := "ginzburgfernandezschlangen2014_54"
    source := ⟨"ginzburg-fernandez-schlangen-2014", "(54)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Have you seen Mark's erm earphones? Headphones."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("I mean headphones", .acceptable)]
    paperFeatures := [("rule", "backward looking"), ("turn", "kept"), ("u0", "earphones"), ("answer", "headphones")] }

def iv_swimming : Datum :=
  { id := "ginzburgfernandezschlangen2014_iv_swimming"
    source := ⟨"ginzburg-fernandez-schlangen-2014", "§4 (iv)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I was a little bit + swimming"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := [("I was swimming", .unacceptable)]
    paperFeatures := [("rule", "backward looking"), ("turn", "kept"), ("u0", "a little bit"), ("answer", "swimming")] }

def iv_quite_a_bit : Datum :=
  { id := "ginzburgfernandezschlangen2014_iv_quite_a_bit"
    source := ⟨"ginzburg-fernandez-schlangen-2014", "§4 (iv)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I was a little bit + actually, quite a bit shocked by that"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("I was quite a bit shocked by that", .acceptable)]
    paperFeatures := [("rule", "backward looking"), ("turn", "kept"), ("u0", "a little bit"), ("answer", "quite a bit")] }

def ex_67 : Datum :=
  { id := "ginzburgfernandezschlangen2014_67"
    source := ⟨"ginzburg-fernandez-schlangen-2014", "(67)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Show flights arriving in uh Boston."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("rule", "forward looking"), ("turn", "kept"), ("u0", "in"), ("answer", "Boston")] }

def ex_11a : Datum :=
  { id := "ginzburgfernandezschlangen2014_11a"
    source := ⟨"ginzburg-fernandez-schlangen-2014", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Chilli, has, has, has never really been [pause] er B: A big seller."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("rule", "forward looking"), ("turn", "taken"), ("u0", "been"), ("answer", "a big seller")] }

def ex_72a : Datum :=
  { id := "ginzburgfernandezschlangen2014_72a"
    source := ⟨"ginzburg-fernandez-schlangen-2014", "(72a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Carol: Well it's (pause) it's (pause) er (pause) what's his name? Bernard Matthews' turkey roast."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("rule", "forward looking"), ("turn", "kept"), ("u0", "it's"), ("query", "what's his name")] }

def all : List Datum := [ex_37d, ex_41, ex_49, ex_54, iv_swimming, iv_quite_a_bit, ex_67, ex_11a, ex_72a]

end GinzburgFernandezSchlangen2014.Examples
