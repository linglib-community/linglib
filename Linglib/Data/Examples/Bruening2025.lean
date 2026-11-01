module

public import Linglib.Data.Examples.Schema

/-!
# `Bruening2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Bruening2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Bruening2025.Examples`.
-/

@[expose] public section

namespace Bruening2025.Examples

def ex_9 : Datum :=
  { id := "bruening2025_9"
    source := ⟨"patejuk-przepiorkowski-2023", "(82)"⟩
    reportedIn := some ⟨"bruening-2025", "(9)"⟩
    language := "stan1293"
    primaryText := "Xenocrates . . . believed that stars are fiery Olympian Gods and in the existence of sublunary daimons and elemental spirits."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "argument"), ("selector", "precedes"), ("selects", "CP"), ("selects", "PP"), ("conjunct", "CP"), ("conjunct", "PP")] }

def ex_10 : Datum :=
  { id := "bruening2025_10"
    source := ⟨"patejuk-przepiorkowski-2023", "(43)"⟩
    reportedIn := some ⟨"bruening-2025", "(10)"⟩
    language := "stan1293"
    primaryText := "This boycott would show not only that there is a price to pay but also our great unity in the face of oppression."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "argument"), ("selector", "precedes"), ("selects", "CP"), ("selects", "NP"), ("conjunct", "CP"), ("conjunct", "NP")] }

def ex_14a : Datum :=
  { id := "bruening2025_14a"
    source := ⟨"patejuk-przepiorkowski-2023", "(25)"⟩
    reportedIn := some ⟨"bruening-2025", "(14a)"⟩
    language := "stan1293"
    primaryText := ". . . this promotion will only last for three days or until all stocks run out."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "argument"), ("selector", "precedes"), ("selects", "PP"), ("selects", "CP"), ("conjunct", "PP"), ("conjunct", "CP")] }

def ex_14b : Datum :=
  { id := "bruening2025_14b"
    source := ⟨"bruening-2025", "(14b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It will last for three days or unlimited."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "argument"), ("selector", "precedes"), ("selects", "PP"), ("selects", "CP"), ("conjunct", "PP"), ("conjunct", "AP")] }

def ex_17a_ap : Datum :=
  { id := "bruening2025_17a_ap"
    source := ⟨"bruening-2025", "(17a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She ended up broken-hearted."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "selection"), ("verb", "end up"), ("complement", "AP")] }

def ex_17a_np : Datum :=
  { id := "bruening2025_17a_np"
    source := ⟨"bruening-2025", "(17a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She ended up a cold-hearted cynic."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "selection"), ("verb", "end up"), ("complement", "NP")] }

def ex_17b_ap : Datum :=
  { id := "bruening2025_17b_ap"
    source := ⟨"bruening-2025", "(17b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The cookies turned out disgusting."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "selection"), ("verb", "turn out"), ("complement", "AP")] }

def ex_17b_np : Datum :=
  { id := "bruening2025_17b_np"
    source := ⟨"bruening-2025", "(17b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The cookies turned out a success."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "selection"), ("verb", "turn out"), ("complement", "NP")] }

def ex_17c_ing : Datum :=
  { id := "bruening2025_17c_ing"
    source := ⟨"bruening-2025", "(17c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They ended up liking sweat lodges."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "selection"), ("verb", "end up"), ("complement", "-ing")] }

def ex_17c_to : Datum :=
  { id := "bruening2025_17c_to"
    source := ⟨"bruening-2025", "(17c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They ended up to like sweat lodges."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "selection"), ("verb", "end up"), ("complement", "to")] }

def ex_17d_to : Datum :=
  { id := "bruening2025_17d_to"
    source := ⟨"bruening-2025", "(17d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They turned out to like sweat lodges."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "selection"), ("verb", "turn out"), ("complement", "to")] }

def ex_17d_ing : Datum :=
  { id := "bruening2025_17d_ing"
    source := ⟨"bruening-2025", "(17d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They turned out liking sweat lodges."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "selection"), ("verb", "turn out"), ("complement", "-ing")] }

def ex_20a : Datum :=
  { id := "bruening2025_20a"
    source := ⟨"bruening-2025", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the future nominal king"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "stacked"), ("host", "N"), ("modifier", "AP"), ("modifier", "AP")] }

def ex_20b : Datum :=
  { id := "bruening2025_20b"
    source := ⟨"bruening-2025", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the once nominal king"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "stacked"), ("host", "N"), ("modifier", "non-ly AdvP"), ("modifier", "AP")] }

def ex_22a : Datum :=
  { id := "bruening2025_22a"
    source := ⟨"patejuk-przepiorkowski-2023", "(74)"⟩
    reportedIn := some ⟨"bruening-2025", "(22a)"⟩
    language := "stan1293"
    primaryText := "Many years ago Korn's father had dealings with the now president."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "modifiers"), ("host", "N"), ("modifier", "non-ly AdvP")] }

def ex_22b : Datum :=
  { id := "bruening2025_22b"
    source := ⟨"patejuk-przepiorkowski-2023", "(75)"⟩
    reportedIn := some ⟨"bruening-2025", "(22b)"⟩
    language := "stan1293"
    primaryText := "They call him the Thane of Glamis, Thane of Cawdor, and the soon king."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "modifiers"), ("host", "N"), ("modifier", "non-ly AdvP")] }

def ex_36a : Datum :=
  { id := "bruening2025_36a"
    source := ⟨"bruening-2025", "(36a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Reconciliation isn't a destination; it's an always and ongoing effort."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "modifiers"), ("host", "N"), ("modifier", "non-ly AdvP"), ("modifier", "AP")] }

def ex_36b : Datum :=
  { id := "bruening2025_36b"
    source := ⟨"bruening-2025", "(36b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "an always effort"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "modifiers"), ("host", "N"), ("modifier", "non-ly AdvP")] }

def ex_36c : Datum :=
  { id := "bruening2025_36c"
    source := ⟨"bruening-2025", "(36c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "An Often and Familiar Ghost"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "modifiers"), ("host", "N"), ("modifier", "non-ly AdvP"), ("modifier", "AP")] }

def ex_36d : Datum :=
  { id := "bruening2025_36d"
    source := ⟨"bruening-2025", "(36d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "an often ghost"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "modifiers"), ("host", "N"), ("modifier", "non-ly AdvP")] }

def ex_36e : Datum :=
  { id := "bruening2025_36e"
    source := ⟨"bruening-2025", "(36e)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Common symptoms include an often and intense itching."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "modifiers"), ("host", "N"), ("modifier", "non-ly AdvP"), ("modifier", "AP")] }

def ex_36f : Datum :=
  { id := "bruening2025_36f"
    source := ⟨"bruening-2025", "(36f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "an often itching"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "modifiers"), ("host", "N"), ("modifier", "non-ly AdvP")] }

def ex_36g : Datum :=
  { id := "bruening2025_36g"
    source := ⟨"bruening-2025", "(36g)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "and mixed lamellar stacks are a seldom and questionable exception"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "modifiers"), ("host", "N"), ("modifier", "non-ly AdvP"), ("modifier", "AP")] }

def ex_36h : Datum :=
  { id := "bruening2025_36h"
    source := ⟨"bruening-2025", "(36h)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "a seldom exception"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "modifiers"), ("host", "N"), ("modifier", "non-ly AdvP")] }

def ex_38a : Datum :=
  { id := "bruening2025_38a"
    source := ⟨"bruening-2025", "(38a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We were discussing the issue of snake locomotion and that no one understands how anesthesia works."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "argument"), ("selector", "precedes"), ("selects", "NP"), ("conjunct", "NP"), ("conjunct", "CP")] }

def ex_38b : Datum :=
  { id := "bruening2025_38b"
    source := ⟨"bruening-2025", "(38b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We were contemplating the possible existence of dream worlds and that the dinosaurs were not really killed by an asteroid."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "argument"), ("selector", "precedes"), ("selects", "NP"), ("conjunct", "NP"), ("conjunct", "CP")] }

def ex_39a : Datum :=
  { id := "bruening2025_39a"
    source := ⟨"bruening-2025", "(39a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We were anxious about money being short and that it was getting harder and harder to get jobs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "argument"), ("selector", "precedes"), ("selects", "NP"), ("conjunct", "NP"), ("conjunct", "CP")] }

def ex_39b : Datum :=
  { id := "bruening2025_39b"
    source := ⟨"bruening-2025", "(39b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This analysis accounts for first conjunct agreement and that dual is more marked than plural."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "argument"), ("selector", "precedes"), ("selects", "NP"), ("conjunct", "NP"), ("conjunct", "CP")] }

def ex_42b_withdrew : Datum :=
  { id := "bruening2025_42b_withdrew"
    source := ⟨"patejuk-przepiorkowski-2023", "(51)"⟩
    reportedIn := some ⟨"bruening-2025", "(42b)"⟩
    language := "stan1293"
    primaryText := "He withdrew that Homer is a genius."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "argument"), ("selector", "precedes"), ("selects", "NP"), ("conjunct", "CP")] }

def ex_42b_strengthens : Datum :=
  { id := "bruening2025_42b_strengthens"
    source := ⟨"patejuk-przepiorkowski-2023", "(51)"⟩
    reportedIn := some ⟨"bruening-2025", "(42b)"⟩
    language := "stan1293"
    primaryText := "This strengthens that Homer is a genius."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "argument"), ("selector", "precedes"), ("selects", "NP"), ("conjunct", "CP")] }

def ex_42c_withdrew : Datum :=
  { id := "bruening2025_42c_withdrew"
    source := ⟨"patejuk-przepiorkowski-2023", "(52)"⟩
    reportedIn := some ⟨"bruening-2025", "(42c)"⟩
    language := "stan1293"
    primaryText := "He withdrew this claim and that Homer is a genius."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "semantic"), ("selector", "precedes"), ("selects", "NP"), ("conjunct", "NP"), ("conjunct", "CP")] }

def ex_42c_strengthens : Datum :=
  { id := "bruening2025_42c_strengthens"
    source := ⟨"patejuk-przepiorkowski-2023", "(52)"⟩
    reportedIn := some ⟨"bruening-2025", "(42c)"⟩
    language := "stan1293"
    primaryText := "This strengthens this claim and that Homer is a genius."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "semantic"), ("selector", "precedes"), ("selects", "NP"), ("conjunct", "NP"), ("conjunct", "CP")] }

def ex_52a : Datum :=
  { id := "bruening2025_52a"
    source := ⟨"bruening-2025", "(52a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We weren't thinking about that we might not be welcome."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "argument"), ("selector", "precedes"), ("selects", "NP"), ("conjunct", "CP")] }

def ex_66a : Datum :=
  { id := "bruening2025_66a"
    source := ⟨"bruening-2025", "(66a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the future beloved king"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "stacked"), ("host", "N"), ("modifier", "AP"), ("modifier", "AP")] }

def ex_66b : Datum :=
  { id := "bruening2025_66b"
    source := ⟨"bruening-2025", "(66b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the once beloved king"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "stacked"), ("host", "N"), ("modifier", "non-ly AdvP"), ("modifier", "AP")] }

def ex_67a : Datum :=
  { id := "bruening2025_67a"
    source := ⟨"bruening-2025", "(67a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the twice happy winner"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "stacked"), ("host", "N"), ("modifier", "non-ly AdvP"), ("modifier", "AP")] }

def ex_67b : Datum :=
  { id := "bruening2025_67b"
    source := ⟨"bruening-2025", "(67b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "a soon short visit"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "stacked"), ("host", "N"), ("modifier", "non-ly AdvP"), ("modifier", "AP")] }

def ex_97a_twotimes : Datum :=
  { id := "bruening2025_97a_twotimes"
    source := ⟨"bruening-2025", "(97a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She is two times taller than him."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "modifiers"), ("host", "CMPR"), ("modifier", "MP")] }

def ex_97a_twice : Datum :=
  { id := "bruening2025_97a_twice"
    source := ⟨"bruening-2025", "(97a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She is twice taller than him."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "modifiers"), ("host", "CMPR"), ("modifier", "non-ly AdvP")] }

def ex_97b : Datum :=
  { id := "bruening2025_97b"
    source := ⟨"bruening-2025", "(97b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She is twice as tall as him."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "modifiers"), ("host", "equative"), ("modifier", "non-ly AdvP")] }

def ex_98a : Datum :=
  { id := "bruening2025_98a"
    source := ⟨"bruening-2025", "(98a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She is twice and maybe even three times taller than he is."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "modifiers"), ("host", "CMPR"), ("modifier", "non-ly AdvP"), ("modifier", "MP")] }

def ex_98b : Datum :=
  { id := "bruening2025_98b"
    source := ⟨"bruening-2025", "(98b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She is one point five times or even twice taller than he is."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "modifiers"), ("host", "CMPR"), ("modifier", "MP"), ("modifier", "non-ly AdvP")] }

def ex_99a : Datum :=
  { id := "bruening2025_99a"
    source := ⟨"bruening-2025", "(99a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "In well-drained soil, the planting hole should be at least twice and preferably five times wider than the root ball."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "modifiers"), ("host", "CMPR"), ("modifier", "non-ly AdvP"), ("modifier", "MP")] }

def ex_99b : Datum :=
  { id := "bruening2025_99b"
    source := ⟨"bruening-2025", "(99b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "For isotropic materials, the area and volumetric thermal expansion coefficient are, respectively, approximately twice and three times larger than the linear thermal expansion coefficient."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "modifiers"), ("host", "CMPR"), ("modifier", "non-ly AdvP"), ("modifier", "MP")] }

def all : List Datum := [ex_9, ex_10, ex_14a, ex_14b, ex_17a_ap, ex_17a_np, ex_17b_ap, ex_17b_np, ex_17c_ing, ex_17c_to, ex_17d_to, ex_17d_ing, ex_20a, ex_20b, ex_22a, ex_22b, ex_36a, ex_36b, ex_36c, ex_36d, ex_36e, ex_36f, ex_36g, ex_36h, ex_38a, ex_38b, ex_39a, ex_39b, ex_42b_withdrew, ex_42b_strengthens, ex_42c_withdrew, ex_42c_strengthens, ex_52a, ex_66a, ex_66b, ex_67a, ex_67b, ex_97a_twotimes, ex_97a_twice, ex_97b, ex_98a, ex_98b, ex_99a, ex_99b]

end Bruening2025.Examples
