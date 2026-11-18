module

public import Linglib.Data.Examples.Schema

/-!
# `Ozaki2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Ozaki2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Ozaki2026.Examples`.
-/

@[expose] public section

namespace Ozaki2026.Examples

def ex1_acc : Datum :=
  { id := "ozaki2026_ex1_acc"
    source := ⟨"ozaki-2026", "(1)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taro-ga mura-o hanare-ta."
    glossedTokens := []
    context := "The source of the departure verb marked accusative."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "hanareru"), ("marking", "acc"), ("diagnostic", "alternation")] }

def ex1_abl : Datum :=
  { id := "ozaki2026_ex1_abl"
    source := ⟨"ozaki-2026", "(1)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taro-ga mura-kara hanare-ta."
    glossedTokens := []
    context := "The source of the departure verb marked ablative."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "hanareru"), ("marking", "abl"), ("diagnostic", "alternation")] }

def ex9_acc : Datum :=
  { id := "ozaki2026_ex9_acc"
    source := ⟨"ozaki-2026", "(9)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taro-wa suguni eki-o deta ga, Hanako-wa suguni denakatta."
    glossedTokens := []
    context := "Ellipsis of the accusative source under the overt adjunct suguni 'quickly': the continuation (10), 'Hanako exited the ticket gate quickly, but she took time to exit the station', is not contradictory, so the elided-source reading is available and the source is an argument by the generalization of Funakoshi (2016)."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "deru"), ("marking", "acc"), ("diagnostic", "ellipsis")] }

def ex9_abl : Datum :=
  { id := "ozaki2026_ex9_abl"
    source := ⟨"ozaki-2026", "(9)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taro-wa suguni eki-kara deta ga, Hanako-wa suguni denakatta."
    glossedTokens := []
    context := "Ellipsis of the ablative source under the overt adjunct suguni 'quickly'; the continuation (10) is not contradictory, so the source is an argument whatever its marking."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "deru"), ("marking", "abl"), ("diagnostic", "ellipsis")] }

def ex13_acc : Datum :=
  { id := "ozaki2026_ex13_acc"
    source := ⟨"ozaki-2026", "(13)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Mura-o Taro-wa Hanako-ga hanareta to itta."
    glossedTokens := []
    context := "Long-distance scrambling of the accusative source out of the embedded clause, available to arguments but not adjuncts (Saito 1985)."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "hanareru"), ("marking", "acc"), ("diagnostic", "scrambling")] }

def ex13_abl : Datum :=
  { id := "ozaki2026_ex13_abl"
    source := ⟨"ozaki-2026", "(13)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Mura-kara Taro-wa Hanako-ga hanareta to itta."
    glossedTokens := []
    context := "Long-distance scrambling of the ablative source out of the embedded clause."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "hanareru"), ("marking", "abl"), ("diagnostic", "scrambling")] }

def ex14 : Datum :=
  { id := "ozaki2026_ex14"
    source := ⟨"ozaki-2026", "(14)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Sono mura-ga Taro-ni hanare-rare-ta."
    glossedTokens := []
    context := "The passive with dative marking on the leaver: an indirect passive, the construction available to unaccusatives, not a direct passive."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "hanareru"), ("marking", "none"), ("diagnostic", "indirect_passive")] }

def ex20 : Datum :=
  { id := "ozaki2026_ex20"
    source := ⟨"ozaki-2026", "(20)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Sono mura-ga Taro-niyotte hanare-rare-ta."
    glossedTokens := []
    context := "The direct passive, diagnosed by niyotte in place of the dative marker (Jo and Seo 2023), which only a verb with thematic Voice can undergo."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "hanareru"), ("marking", "none"), ("diagnostic", "direct_passive")] }

def ex26_acc : Datum :=
  { id := "ozaki2026_ex26_acc"
    source := ⟨"ozaki-2026", "(26)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Nani-o Taro-wa mura-o hanare-teir-u no?"
    glossedTokens := []
    context := "The accusative wh-adjunct nani-o 'what-ACC' in its 'why' reading (Kurafuji 1997), available with unergatives and transitives but not with unaccusatives."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "hanareru"), ("marking", "acc"), ("diagnostic", "nani_o")] }

def ex26_abl : Datum :=
  { id := "ozaki2026_ex26_abl"
    source := ⟨"ozaki-2026", "(26)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Nani-o Taro-wa mura-kara hanare-teir-u no?"
    glossedTokens := []
    context := "The accusative wh-adjunct in its 'why' reading with the ablative source: unavailable as with unaccusatives."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "hanareru"), ("marking", "abl"), ("diagnostic", "nani_o")] }

def all : List Datum := [ex1_acc, ex1_abl, ex9_acc, ex9_abl, ex13_acc, ex13_abl, ex14, ex20, ex26_acc, ex26_abl]

end Ozaki2026.Examples
