module

public import Linglib.Data.Examples.Schema

/-!
# `Beaver2004` — typed example data

Auto-generated from `Linglib/Data/Examples/Beaver2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Beaver2004.Examples`.
-/

@[expose] public section

namespace Beaver2004.Examples

def ex_1 : Datum :=
  { id := "beaver2004_1"
    source := ⟨"beaver-2004", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane likes Mary. She often brings her flowers. She chats with her for ages."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("In (1c), she = Jane and her = Mary", .acceptable)]
    paperFeatures := [("transition", "continue")] }

def ex_2 : Datum :=
  { id := "beaver2004_2"
    source := ⟨"beaver-2004", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary likes tennis. She plays Jim quite often. He used to play doubles with Mary."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("He = Jim and the two Marys corefer", .marginal)]
    paperFeatures := [("phenomenon", "rule 1 violation"), ("felicity", "infelicitous")] }

def ex_5 : Datum :=
  { id := "beaver2004_5"
    source := ⟨"beaver-2004", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane likes Mary. She often visits her for tea. The woman is a compulsive tea drinker."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("She = Jane, her = Mary; the woman = Jane", .acceptable)]
    paperFeatures := [("phenomenon", "definite description resolution")] }

def ex_8 : Datum :=
  { id := "beaver2004_8"
    source := ⟨"beaver-2004", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane likes Mary. She often goes around for tea with her. She chats with the young woman for ages."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("She = Jane, the young woman = Mary", .acceptable)]
    paperFeatures := [("transition", "continue")] }

def ex_9 : Datum :=
  { id := "beaver2004_9"
    source := ⟨"beaver-2004", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane is happy. Mary gave her a present. She smiled."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("She = Jane, the topic, not the previous subject Mary", .acceptable)]
    paperFeatures := [("transition", "continue")] }

def ex_12 : Datum :=
  { id := "beaver2004_12"
    source := ⟨"beaver-2004", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane is happy. She was congratulated by Freda, and Mary gave her a present."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("her = Jane", .acceptable)]
    paperFeatures := [("transition", "retain")] }

def ex_14 : Datum :=
  { id := "beaver2004_14"
    source := ⟨"beaver-2004", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane is happy. Mary gave her a present. She smiled at her."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("She = Mary, her = Jane", .acceptable)]
    paperFeatures := [("transition", "smooth shift")] }

def ex_16 : Datum :=
  { id := "beaver2004_16"
    source := ⟨"beaver-2004", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane is happy. Mary gave her a present. Somebody unwrapped it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("it = the present", .acceptable)]
    paperFeatures := [("transition", "rough shift")] }

def ex_23 : Datum :=
  { id := "beaver2004_23"
    source := ⟨"beaver-2004", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A great refinement among armorial signets was to reproduce not only the coat-of-arms but the correct tinctures; they were repeated in colour on the reverse side and the crystal would then be set in the gold bezel."
    glossedTokens := []
    context := "Corpus example from museum-object descriptions."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "rule 1 violation")] }

def ex_24 : Datum :=
  { id := "beaver2004_24"
    source := ⟨"beaver-2004", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John went to his favorite music store to buy a piano. He had frequented the store for many years. He was excited to be going to the store to actually buy a piano. It was the biggest music store in the area. It had just the kind of piano that he wanted. It was closing just as John arrived."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "text coherence")] }

def ex_25 : Datum :=
  { id := "beaver2004_25"
    source := ⟨"beaver-2004", "(25)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John went to his favorite music store to buy a piano. It was a store John had frequented for many years. He was excited to be going to the store to actually buy a piano. It was the biggest music store in the area. He knew that it had just the kind of piano that he wanted. It was closing just as John arrived."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "text coherence"), ("felicity", "infelicitous")] }

def ex_28 : Datum :=
  { id := "beaver2004_28"
    source := ⟨"beaver-2004", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fred was eating. He saw Jim. HE winked."
    glossedTokens := []
    context := "The speaker wants to convey that Jim winked."
    judgment := .acceptable
    contrasts := []
    readings := [("Stressed HE = Jim (switch reference)", .acceptable)]
    paperFeatures := [("phenomenon", "stressed pronoun")] }

def all : List Datum := [ex_1, ex_2, ex_5, ex_8, ex_9, ex_12, ex_14, ex_16, ex_23, ex_24, ex_25, ex_28]

end Beaver2004.Examples
