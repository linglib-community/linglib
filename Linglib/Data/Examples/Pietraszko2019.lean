module

public import Linglib.Data.Examples.Schema

/-!
# `Pietraszko2019` — typed example data

Auto-generated from `Linglib/Data/Examples/Pietraszko2019.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Pietraszko2019.Examples`.
-/

@[expose] public section

namespace Pietraszko2019.Examples

def ex_4 : Datum :=
  { id := "pietraszko2019_4"
    source := ⟨"pietraszko-2019", "(4)"⟩
    reportedIn := none
    language := "nort2795"
    primaryText := "Ngicabanga u-kuthi usukile."
    glossedTokens := [("Ngicabanga", "1SG.thought"), ("u-kuthi", "AUG-COMP"), ("usukile", "1.left")]
    glossedWords := [⟨[['N', 'g', 'i', 'c', 'a', 'b', 'a', 'n', 'g', 'a']], [['1', 'S', 'G', '.', 't', 'h', 'o', 'u', 'g', 'h', 't']]⟩, ⟨[['u'], ['k', 'u', 't', 'h', 'i']], [['A', 'U', 'G'], ['C', 'O', 'M', 'P']]⟩, ⟨[['u', 's', 'u', 'k', 'i', 'l', 'e']], [['1', '.', 'l', 'e', 'f', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "cabanga"), ("role", "complement"), ("mood", "indicative")] }

def ex_7a : Datum :=
  { id := "pietraszko2019_7a"
    source := ⟨"pietraszko-2019", "(7a)"⟩
    reportedIn := none
    language := "nort2795"
    primaryText := "Ngi-ya-ku-funa ukudla."
    glossedTokens := [("Ngi-ya-ku-funa", "1SG.SBJ-DSJ-15.OBJ-want"), ("ukudla", "15.food")]
    glossedWords := [⟨[['N', 'g', 'i'], ['y', 'a'], ['k', 'u'], ['f', 'u', 'n', 'a']], [['1', 'S', 'G', '.', 'S', 'B', 'J'], ['D', 'S', 'J'], ['1', '5', '.', 'O', 'B', 'J'], ['w', 'a', 'n', 't']]⟩, ⟨[['u', 'k', 'u', 'd', 'l', 'a']], [['1', '5', '.', 'f', 'o', 'o', 'd']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Ngi-ku-funa ukudla.", .ungrammatical)]
    readings := []
    paperFeatures := [("verb", "funa"), ("role", "complement"), ("diagnostic", "objectMarking")] }

def ex_7b : Datum :=
  { id := "pietraszko2019_7b"
    source := ⟨"pietraszko-2019", "(7b)"⟩
    reportedIn := none
    language := "nort2795"
    primaryText := "Ngi-ya-ku-funa ukuthi uZodwa a-pheke."
    glossedTokens := [("Ngi-ya-ku-funa", "1SG.SBJ-DSJ-15.OBJ-want"), ("ukuthi", "15.COMP"), ("uZodwa", "1.Zodwa"), ("a-pheke", "1.SBJ-cook")]
    glossedWords := [⟨[['N', 'g', 'i'], ['y', 'a'], ['k', 'u'], ['f', 'u', 'n', 'a']], [['1', 'S', 'G', '.', 'S', 'B', 'J'], ['D', 'S', 'J'], ['1', '5', '.', 'O', 'B', 'J'], ['w', 'a', 'n', 't']]⟩, ⟨[['u', 'k', 'u', 't', 'h', 'i']], [['1', '5', '.', 'C', 'O', 'M', 'P']]⟩, ⟨[['u', 'Z', 'o', 'd', 'w', 'a']], [['1', '.', 'Z', 'o', 'd', 'w', 'a']]⟩, ⟨[['a'], ['p', 'h', 'e', 'k', 'e']], [['1', '.', 'S', 'B', 'J'], ['c', 'o', 'o', 'k']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Ngi-ku-funa ukuthi uZodwa a-pheke.", .ungrammatical)]
    readings := []
    paperFeatures := [("verb", "funa"), ("role", "complement"), ("mood", "subjunctive"), ("diagnostic", "objectMarking")] }

def ex_14 : Datum :=
  { id := "pietraszko2019_14"
    source := ⟨"pietraszko-2019", "(14)"⟩
    reportedIn := none
    language := "nort2795"
    primaryText := "Ngi-dan-is-w-e yi-kuthi u-sukile."
    glossedTokens := [("Ngi-dan-is-w-e", "1SG.SBJ-worry-CAUS-PASS-PST"), ("yi-kuthi", "OBL-15.COMP"), ("u-sukile", "2SG.SBJ-left")]
    glossedWords := [⟨[['N', 'g', 'i'], ['d', 'a', 'n'], ['i', 's'], ['w'], ['e']], [['1', 'S', 'G', '.', 'S', 'B', 'J'], ['w', 'o', 'r', 'r', 'y'], ['C', 'A', 'U', 'S'], ['P', 'A', 'S', 'S'], ['P', 'S', 'T']]⟩, ⟨[['y', 'i'], ['k', 'u', 't', 'h', 'i']], [['O', 'B', 'L'], ['1', '5', '.', 'C', 'O', 'M', 'P']]⟩, ⟨[['u'], ['s', 'u', 'k', 'i', 'l', 'e']], [['2', 'S', 'G', '.', 'S', 'B', 'J'], ['l', 'e', 'f', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "danisa"), ("role", "obliquePassiveSubject")] }

def ex_20b : Datum :=
  { id := "pietraszko2019_20b"
    source := ⟨"pietraszko-2019", "(20b)"⟩
    reportedIn := none
    language := "nort2795"
    primaryText := "Si-khuluma nga u-kuthi abantu babambane."
    glossedTokens := [("Si-khuluma", "1PL.SBJ-talk"), ("nga", "about"), ("u-kuthi", "AUG-15.COMP"), ("abantu", "people"), ("babambane", "be.united")]
    glossedWords := [⟨[['S', 'i'], ['k', 'h', 'u', 'l', 'u', 'm', 'a']], [['1', 'P', 'L', '.', 'S', 'B', 'J'], ['t', 'a', 'l', 'k']]⟩, ⟨[['n', 'g', 'a']], [['a', 'b', 'o', 'u', 't']]⟩, ⟨[['u'], ['k', 'u', 't', 'h', 'i']], [['A', 'U', 'G'], ['1', '5', '.', 'C', 'O', 'M', 'P']]⟩, ⟨[['a', 'b', 'a', 'n', 't', 'u']], [['p', 'e', 'o', 'p', 'l', 'e']]⟩, ⟨[['b', 'a', 'b', 'a', 'm', 'b', 'a', 'n', 'e']], [['b', 'e', '.', 'u', 'n', 'i', 't', 'e', 'd']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "khuluma nga"), ("role", "prepositionObject")] }

def ex_22 : Datum :=
  { id := "pietraszko2019_22"
    source := ⟨"pietraszko-2019", "(22)"⟩
    reportedIn := none
    language := "nort2795"
    primaryText := "Ukuthi izitha zi-za-buya ku-bal-iw-e e-roof-ini."
    glossedTokens := [("Ukuthi", "15.COMP"), ("izitha", "10.enemies"), ("zi-za-buya", "10.SBJ-FUT-come"), ("ku-bal-iw-e", "15.SBJ-write-PASS-PST"), ("e-roof-ini", "LOC-roof-LOC")]
    glossedWords := [⟨[['U', 'k', 'u', 't', 'h', 'i']], [['1', '5', '.', 'C', 'O', 'M', 'P']]⟩, ⟨[['i', 'z', 'i', 't', 'h', 'a']], [['1', '0', '.', 'e', 'n', 'e', 'm', 'i', 'e', 's']]⟩, ⟨[['z', 'i'], ['z', 'a'], ['b', 'u', 'y', 'a']], [['1', '0', '.', 'S', 'B', 'J'], ['F', 'U', 'T'], ['c', 'o', 'm', 'e']]⟩, ⟨[['k', 'u'], ['b', 'a', 'l'], ['i', 'w'], ['e']], [['1', '5', '.', 'S', 'B', 'J'], ['w', 'r', 'i', 't', 'e'], ['P', 'A', 'S', 'S'], ['P', 'S', 'T']]⟩, ⟨[['e'], ['r', 'o', 'o', 'f'], ['i', 'n', 'i']], [['L', 'O', 'C'], ['r', 'o', 'o', 'f'], ['L', 'O', 'C']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "bala"), ("role", "subject")] }

def all : List Datum := [ex_4, ex_7a, ex_7b, ex_14, ex_20b, ex_22]

end Pietraszko2019.Examples
