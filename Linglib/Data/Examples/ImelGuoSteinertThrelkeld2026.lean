module

public import Linglib.Data.Examples.Schema

/-!
# `ImelGuoSteinertThrelkeld2026` — typed example data

Auto-generated from `Linglib/Data/Examples/ImelGuoSteinertThrelkeld2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ImelGuoSteinertThrelkeld2026.Examples`.
-/

@[expose] public section

namespace ImelGuoSteinertThrelkeld2026.Examples

def s1a : Datum :=
  { id := "imelguosteinertthrelkeld2026_s1a"
    source := ⟨"imel-guo-steinert-threlkeld-2026", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It must be raining."
    glossedTokens := []
    context := "A friend walks in and shakes off a wet umbrella. You say:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "Modality"), ("force", "strong"), ("flavor", "epistemic")] }

def s1b : Datum :=
  { id := "imelguosteinertthrelkeld2026_s1b"
    source := ⟨"imel-guo-steinert-threlkeld-2026", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You must upload your homework as a PDF."
    glossedTokens := []
    context := "You are reading the specifications of a homework assignment. It partially reads:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "Modality"), ("force", "strong"), ("flavor", "deontic")] }

def s2a : Datum :=
  { id := "imelguosteinertthrelkeld2026_s2a"
    source := ⟨"imel-guo-steinert-threlkeld-2026", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It may be raining."
    glossedTokens := []
    context := "A friend is leaving and grabs an umbrella on the way out, saying:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "Modality"), ("force", "weak"), ("flavor", "epistemic")] }

def s2b : Datum :=
  { id := "imelguosteinertthrelkeld2026_s2b"
    source := ⟨"imel-guo-steinert-threlkeld-2026", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may have a cookie."
    glossedTokens := []
    context := "A mother offers a treat to a child for finishing an assignment:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "Modality"), ("force", "weak"), ("flavor", "deontic")] }

def s3a : Datum :=
  { id := "imelguosteinertthrelkeld2026_s3a"
    source := ⟨"imel-guo-steinert-threlkeld-2026", "(3a)"⟩
    reportedIn := none
    language := "lill1248"
    primaryText := "nilh k'a lh(el)-(t)-en-s-wá(7)-(a) ptinus-em-sút"
    glossedTokens := [("nilh", "FOC"), ("k'a", "INFER"), ("lh(el)-(t)-en-s-wá(7)-(a)", "from-DET-1SG.POSS-NOM-IMPF-DET"), ("ptinus-em-sút", "think-MID-OOC")]
    glossedWords := [⟨[['n', 'i', 'l', 'h']], [['F', 'O', 'C']]⟩, ⟨[['k', '\'', 'a']], [['I', 'N', 'F', 'E', 'R']]⟩, ⟨[['l', 'h', 'e', 'l'], ['t'], ['e', 'n'], ['s'], ['w', 'á', '7'], ['a']], [['f', 'r', 'o', 'm'], ['D', 'E', 'T'], ['1', 'S', 'G', '.', 'P', 'O', 'S', 'S'], ['N', 'O', 'M'], ['I', 'M', 'P', 'F'], ['D', 'E', 'T']]⟩, ⟨[['p', 't', 'i', 'n', 'u', 's'], ['e', 'm'], ['s', 'ú', 't']], [['t', 'h', 'i', 'n', 'k'], ['M', 'I', 'D'], ['O', 'O', 'C']]⟩]
    lgrConformance := some .morphemeAligned
    context := "You have a headache that won't go away, so you go to the doctor. All the tests show negative. There is nothing wrong, so it must just be tension."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "Modality"), ("source", "Rullmann et al. 2008:321, (5c)"), ("force", "strong"), ("flavor", "epistemic")] }

def s3b : Datum :=
  { id := "imelguosteinertthrelkeld2026_s3b"
    source := ⟨"imel-guo-steinert-threlkeld-2026", "(3b)"⟩
    reportedIn := none
    language := "lill1248"
    primaryText := "plan k'a qwatsáts"
    glossedTokens := [("plan", "already"), ("k'a", "INFER"), ("qwatsáts", "leave")]
    glossedWords := [⟨[['p', 'l', 'a', 'n']], [['a', 'l', 'r', 'e', 'a', 'd', 'y']]⟩, ⟨[['k', '\'', 'a']], [['I', 'N', 'F', 'E', 'R']]⟩, ⟨[['q', 'w', 'a', 't', 's', 'á', 't', 's']], [['l', 'e', 'a', 'v', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := "His car isn't there."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "Modality"), ("source", "Rullmann et al. 2008:321, (5e)"), ("force", "weak"), ("flavor", "epistemic")] }

def all : List Datum := [s1a, s1b, s2a, s2b, s3a, s3b]

end ImelGuoSteinertThrelkeld2026.Examples
