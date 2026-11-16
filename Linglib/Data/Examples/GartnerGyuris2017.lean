module

public import Linglib.Data.Examples.Schema

/-!
# `GartnerGyuris2017` — typed example data

Auto-generated from `Linglib/Data/Examples/GartnerGyuris2017.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace GartnerGyuris2017.Examples`.
-/

@[expose] public section

namespace GartnerGyuris2017.Examples

def gg2017_1 : Datum :=
  { id := "gg2017_1"
    source := ⟨"gartner-gyuris-2017", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Is it sunny outside?"
    glossedTokens := []
    context := "A enters S's windowless office in a manifestly dripping wet raincoat."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "English V1"), ("form", "PPQ"), ("dimension", "evidential"), ("value", "-")] }

def gg2017_2a : Datum :=
  { id := "gg2017_2a"
    source := ⟨"gartner-gyuris-2017", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Didn't John go to the party?"
    glossedTokens := []
    context := "S has just learned that A hosted a party last night but has no idea who did or should have attended."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "English V1"), ("form", "IN-NPQ"), ("dimension", "epistemic"), ("value", "%")] }

def gg2017_2b : Datum :=
  { id := "gg2017_2b"
    source := ⟨"gartner-gyuris-2017", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Did John not go to the party?"
    glossedTokens := []
    context := "S has just learned that A hosted a party last night but has no idea who did or should have attended."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "English V1"), ("form", "IN-NPQ"), ("dimension", "epistemic"), ("value", "%")] }

def gg2017_8_neg : Datum :=
  { id := "gg2017_8_neg"
    source := ⟨"gartner-gyuris-2017", "(8)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Süt-e a nap?"
    glossedTokens := [("Süt-e", "shine-Q"), ("a", "the"), ("nap", "sun")]
    glossedWords := [⟨[['S', 'ü', 't'], ['e']], [['s', 'h', 'i', 'n', 'e'], ['Q']]⟩, ⟨[['a']], [['t', 'h', 'e']]⟩, ⟨[['n', 'a', 'p']], [['s', 'u', 'n']]⟩]
    lgrConformance := some .morphemeAligned
    context := "A enters S's windowless office in a manifestly dripping wet raincoat."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Hungarian e"), ("form", "PPQ"), ("dimension", "evidential"), ("value", "-")] }

def gg2017_8_pos : Datum :=
  { id := "gg2017_8_pos"
    source := ⟨"gartner-gyuris-2017", "(8)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Süt-e a nap?"
    glossedTokens := [("Süt-e", "shine-Q"), ("a", "the"), ("nap", "sun")]
    glossedWords := [⟨[['S', 'ü', 't'], ['e']], [['s', 'h', 'i', 'n', 'e'], ['Q']]⟩, ⟨[['a']], [['t', 'h', 'e']]⟩, ⟨[['n', 'a', 'p']], [['s', 'u', 'n']]⟩]
    lgrConformance := some .morphemeAligned
    context := "A comes in with dark sunglasses, T-shirt, shorts, a straw hat and suntan lotion, humming a song about sunshine."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Hungarian e"), ("form", "PPQ"), ("dimension", "evidential"), ("value", "+")] }

def gg2017_9a : Datum :=
  { id := "gg2017_9a"
    source := ⟨"gartner-gyuris-2017", "(9a)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Nincs-e itt egy francia étterem?"
    glossedTokens := [("Nincs-e", "not.is-Q"), ("itt", "here"), ("egy", "a"), ("francia", "French"), ("étterem", "restaurant")]
    glossedWords := [⟨[['N', 'i', 'n', 'c', 's'], ['e']], [['n', 'o', 't', '.', 'i', 's'], ['Q']]⟩, ⟨[['i', 't', 't']], [['h', 'e', 'r', 'e']]⟩, ⟨[['e', 'g', 'y']], [['a']]⟩, ⟨[['f', 'r', 'a', 'n', 'c', 'i', 'a']], [['F', 'r', 'e', 'n', 'c', 'h']]⟩, ⟨[['é', 't', 't', 'e', 'r', 'e', 'm']], [['r', 'e', 's', 't', 'a', 'u', 'r', 'a', 'n', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := "S and A stand in front of a billboard in a small village saying that the last restaurant there has just closed for good."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Hungarian e"), ("form", "ON-NPQ"), ("dimension", "evidential"), ("value", "-")] }

def gg2017_9b : Datum :=
  { id := "gg2017_9b"
    source := ⟨"gartner-gyuris-2017", "(9b)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Nincs-e itt egy étterem?"
    glossedTokens := []
    context := "The billboard announces the opening of several new restaurants in the village."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Hungarian e"), ("form", "ON-NPQ"), ("dimension", "evidential"), ("value", "+")] }

def all : List Datum := [gg2017_1, gg2017_2a, gg2017_2b, gg2017_8_neg, gg2017_8_pos, gg2017_9a, gg2017_9b]

end GartnerGyuris2017.Examples
