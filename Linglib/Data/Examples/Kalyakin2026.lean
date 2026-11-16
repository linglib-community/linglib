module

public import Linglib.Data.Examples.Schema

/-!
# `Kalyakin2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Kalyakin2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Kalyakin2026.Examples`.
-/

@[expose] public section

namespace Kalyakin2026.Examples

def ex3 : Datum :=
  { id := "kalyakin2026_ex3"
    source := ⟨"kalyakin-2026", "(3)"⟩
    reportedIn := none
    language := "muir1238"
    primaryText := "Pat’imat-li χureg wana b-arq’-ib, Ashura-li=ra ⟨χureg wana⟩ b-arq’-ib"
    glossedTokens := [("Pat’imat-li", "Patimat-ERG"), ("χureg", "food.ABS"), ("wana", "warm"), ("b-arq’-ib,", "N-make.PFV-AOR"), ("Ashura-li=ra", "Ashura-ERG=ADD"), ("⟨χureg", "food.ABS"), ("wana⟩", "warm"), ("b-arq’-ib", "N-make.PFV-AOR")]
    glossedWords := [⟨[['P', 'a', 't', '’', 'i', 'm', 'a', 't'], ['l', 'i']], [['P', 'a', 't', 'i', 'm', 'a', 't'], ['E', 'R', 'G']]⟩, ⟨[['χ', 'u', 'r', 'e', 'g']], [['f', 'o', 'o', 'd', '.', 'A', 'B', 'S']]⟩, ⟨[['w', 'a', 'n', 'a']], [['w', 'a', 'r', 'm']]⟩, ⟨[['b'], ['a', 'r', 'q', '’'], ['i', 'b']], [['N'], ['m', 'a', 'k', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R']]⟩, ⟨[['A', 's', 'h', 'u', 'r', 'a'], ['l', 'i'], ['r', 'a']], [['A', 's', 'h', 'u', 'r', 'a'], ['E', 'R', 'G'], ['A', 'D', 'D']]⟩, ⟨[['⟨', 'χ', 'u', 'r', 'e', 'g']], [['f', 'o', 'o', 'd', '.', 'A', 'B', 'S']]⟩, ⟨[['w', 'a', 'n', 'a', '⟩']], [['w', 'a', 'r', 'm']]⟩, ⟨[['b'], ['a', 'r', 'q', '’'], ['i', 'b']], [['N'], ['m', 'a', 'k', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "state")] }

def ex29 : Datum :=
  { id := "kalyakin2026_ex29"
    source := ⟨"kalyakin-2026", "(29)"⟩
    reportedIn := none
    language := "muir1238"
    primaryText := "Učitil-li Musa parʁat w-arq’-b=akːu, pro ⟨tᵢ parʁat⟩ w-arq’-ib ʡaˤbdullaᵢ"
    glossedTokens := [("Učitil-li", "teacher-ERG"), ("Musa", "Musa.ABS"), ("parʁat", "calm"), ("w-arq’-b=akːu,", "M-make.PFV-AOR=NEG.COP"), ("pro", ""), ("⟨tᵢ", ""), ("parʁat⟩", "calm"), ("w-arq’-ib", "M-make.PFV-AOR"), ("ʡaˤbdullaᵢ", "Abdullah.ABS")]
    glossedWords := [⟨[['U', 'č', 'i', 't', 'i', 'l'], ['l', 'i']], [['t', 'e', 'a', 'c', 'h', 'e', 'r'], ['E', 'R', 'G']]⟩, ⟨[['M', 'u', 's', 'a']], [['M', 'u', 's', 'a', '.', 'A', 'B', 'S']]⟩, ⟨[['p', 'a', 'r', 'ʁ', 'a', 't']], [['c', 'a', 'l', 'm']]⟩, ⟨[['w'], ['a', 'r', 'q', '’'], ['b'], ['a', 'k', 'ː', 'u']], [['M'], ['m', 'a', 'k', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R'], ['N', 'E', 'G', '.', 'C', 'O', 'P']]⟩, ⟨[['p', 'r', 'o']], [[]]⟩, ⟨[['⟨', 't', 'ᵢ']], [[]]⟩, ⟨[['p', 'a', 'r', 'ʁ', 'a', 't', '⟩']], [['c', 'a', 'l', 'm']]⟩, ⟨[['w'], ['a', 'r', 'q', '’'], ['i', 'b']], [['M'], ['m', 'a', 'k', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R']]⟩, ⟨[['ʡ', 'a', 'ˤ', 'b', 'd', 'u', 'l', 'l', 'a', 'ᵢ']], [['A', 'b', 'd', 'u', 'l', 'l', 'a', 'h', '.', 'A', 'B', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "state"), ("contrastiveFocus", "yes")] }

def ex30a : Datum :=
  { id := "kalyakin2026_ex30a"
    source := ⟨"kalyakin-2026", "(30a)"⟩
    reportedIn := none
    language := "muir1238"
    primaryText := "Učitil-li Musa parʁat w-arq’-ib, pro Pat’imatᵢ ⟨tᵢ parʁat⟩ r-arq’-b=akːu"
    glossedTokens := [("Učitil-li", "teacher-ERG"), ("Musa", "Musa.ABS"), ("parʁat", "calm"), ("w-arq’-ib,", "M-make.PFV-AOR"), ("pro", ""), ("Pat’imatᵢ", "Patimat.ABS"), ("⟨tᵢ", ""), ("parʁat⟩", "calm"), ("r-arq’-b=akːu", "F-make.PFV-AOR=NEG.COP")]
    glossedWords := [⟨[['U', 'č', 'i', 't', 'i', 'l'], ['l', 'i']], [['t', 'e', 'a', 'c', 'h', 'e', 'r'], ['E', 'R', 'G']]⟩, ⟨[['M', 'u', 's', 'a']], [['M', 'u', 's', 'a', '.', 'A', 'B', 'S']]⟩, ⟨[['p', 'a', 'r', 'ʁ', 'a', 't']], [['c', 'a', 'l', 'm']]⟩, ⟨[['w'], ['a', 'r', 'q', '’'], ['i', 'b']], [['M'], ['m', 'a', 'k', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R']]⟩, ⟨[['p', 'r', 'o']], [[]]⟩, ⟨[['P', 'a', 't', '’', 'i', 'm', 'a', 't', 'ᵢ']], [['P', 'a', 't', 'i', 'm', 'a', 't', '.', 'A', 'B', 'S']]⟩, ⟨[['⟨', 't', 'ᵢ']], [[]]⟩, ⟨[['p', 'a', 'r', 'ʁ', 'a', 't', '⟩']], [['c', 'a', 'l', 'm']]⟩, ⟨[['r'], ['a', 'r', 'q', '’'], ['b'], ['a', 'k', 'ː', 'u']], [['F'], ['m', 'a', 'k', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R'], ['N', 'E', 'G', '.', 'C', 'O', 'P']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "state"), ("contrastiveFocus", "yes")] }

def ex30b : Datum :=
  { id := "kalyakin2026_ex30b"
    source := ⟨"kalyakin-2026", "(30b)"⟩
    reportedIn := none
    language := "muir1238"
    primaryText := "Učitil-li Musa parʁat w-arq’-ib, direktur-li=ra Musaᵢ ⟨tᵢ parʁat⟩ w-arq’-ib"
    glossedTokens := [("Učitil-li", "teacher-ERG"), ("Musa", "Musa.ABS"), ("parʁat", "calm"), ("w-arq’-ib,", "M-make.PFV-AOR"), ("direktur-li=ra", "principal-ERG=ADD"), ("Musaᵢ", "Musa.ABS"), ("⟨tᵢ", ""), ("parʁat⟩", "calm"), ("w-arq’-ib", "M-make.PFV-AOR")]
    glossedWords := [⟨[['U', 'č', 'i', 't', 'i', 'l'], ['l', 'i']], [['t', 'e', 'a', 'c', 'h', 'e', 'r'], ['E', 'R', 'G']]⟩, ⟨[['M', 'u', 's', 'a']], [['M', 'u', 's', 'a', '.', 'A', 'B', 'S']]⟩, ⟨[['p', 'a', 'r', 'ʁ', 'a', 't']], [['c', 'a', 'l', 'm']]⟩, ⟨[['w'], ['a', 'r', 'q', '’'], ['i', 'b']], [['M'], ['m', 'a', 'k', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R']]⟩, ⟨[['d', 'i', 'r', 'e', 'k', 't', 'u', 'r'], ['l', 'i'], ['r', 'a']], [['p', 'r', 'i', 'n', 'c', 'i', 'p', 'a', 'l'], ['E', 'R', 'G'], ['A', 'D', 'D']]⟩, ⟨[['M', 'u', 's', 'a', 'ᵢ']], [['M', 'u', 's', 'a', '.', 'A', 'B', 'S']]⟩, ⟨[['⟨', 't', 'ᵢ']], [[]]⟩, ⟨[['p', 'a', 'r', 'ʁ', 'a', 't', '⟩']], [['c', 'a', 'l', 'm']]⟩, ⟨[['w'], ['a', 'r', 'q', '’'], ['i', 'b']], [['M'], ['m', 'a', 'k', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("root", "state")] }

def ex32 : Datum :=
  { id := "kalyakin2026_ex32"
    source := ⟨"kalyakin-2026", "(32)"⟩
    reportedIn := none
    language := "muir1238"
    primaryText := "ʡinc-bi ħint’in d-Ø-ib, pamidur-ti=raᵢ ⟨tᵢ ħint’in⟩ d-Ø-ib"
    glossedTokens := [("ʡinc-bi", "apple-PL.ABS"), ("ħint’in", "red"), ("d-Ø-ib,", "NPL-become.PFV-AOR"), ("pamidur-ti=raᵢ", "tomato-PL.ABS=ADD"), ("⟨tᵢ", ""), ("ħint’in⟩", "red"), ("d-Ø-ib", "NPL-become.PFV-AOR")]
    glossedWords := [⟨[['ʡ', 'i', 'n', 'c'], ['b', 'i']], [['a', 'p', 'p', 'l', 'e'], ['P', 'L', '.', 'A', 'B', 'S']]⟩, ⟨[['ħ', 'i', 'n', 't', '’', 'i', 'n']], [['r', 'e', 'd']]⟩, ⟨[['d'], ['Ø'], ['i', 'b']], [['N', 'P', 'L'], ['b', 'e', 'c', 'o', 'm', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R']]⟩, ⟨[['p', 'a', 'm', 'i', 'd', 'u', 'r'], ['t', 'i'], ['r', 'a', 'ᵢ']], [['t', 'o', 'm', 'a', 't', 'o'], ['P', 'L', '.', 'A', 'B', 'S'], ['A', 'D', 'D']]⟩, ⟨[['⟨', 't', 'ᵢ']], [[]]⟩, ⟨[['ħ', 'i', 'n', 't', '’', 'i', 'n', '⟩']], [['r', 'e', 'd']]⟩, ⟨[['d'], ['Ø'], ['i', 'b']], [['N', 'P', 'L'], ['b', 'e', 'c', 'o', 'm', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "state")] }

def ex36a : Datum :=
  { id := "kalyakin2026_ex36a"
    source := ⟨"kalyakin-2026", "(36a)"⟩
    reportedIn := none
    language := "muir1238"
    primaryText := "Učitil-li Murad parʁat w-arq’-ib, direktur-li=ra w-arq’-ib"
    glossedTokens := [("Učitil-li", "teacher-ERG"), ("Murad", "Murad.ABS"), ("parʁat", "calm"), ("w-arq’-ib,", "M-make.PFV-AOR"), ("direktur-li=ra", "principal-ERG=ADD"), ("w-arq’-ib", "M-make.PFV-AOR")]
    glossedWords := [⟨[['U', 'č', 'i', 't', 'i', 'l'], ['l', 'i']], [['t', 'e', 'a', 'c', 'h', 'e', 'r'], ['E', 'R', 'G']]⟩, ⟨[['M', 'u', 'r', 'a', 'd']], [['M', 'u', 'r', 'a', 'd', '.', 'A', 'B', 'S']]⟩, ⟨[['p', 'a', 'r', 'ʁ', 'a', 't']], [['c', 'a', 'l', 'm']]⟩, ⟨[['w'], ['a', 'r', 'q', '’'], ['i', 'b']], [['M'], ['m', 'a', 'k', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R']]⟩, ⟨[['d', 'i', 'r', 'e', 'k', 't', 'u', 'r'], ['l', 'i'], ['r', 'a']], [['p', 'r', 'i', 'n', 'c', 'i', 'p', 'a', 'l'], ['E', 'R', 'G'], ['A', 'D', 'D']]⟩, ⟨[['w'], ['a', 'r', 'q', '’'], ['i', 'b']], [['M'], ['m', 'a', 'k', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "state")] }

def ex36b : Datum :=
  { id := "kalyakin2026_ex36b"
    source := ⟨"kalyakin-2026", "(36b)"⟩
    reportedIn := none
    language := "muir1238"
    primaryText := "Učitil-li Murad parʁat w-arq’-ib, direktur-li=ra parʁat w-arq’-ib"
    glossedTokens := [("Učitil-li", "teacher-ERG"), ("Murad", "Murad.ABS"), ("parʁat", "calm"), ("w-arq’-ib,", "M-make.PFV-AOR"), ("direktur-li=ra", "principal-ERG=ADD"), ("parʁat", "calm"), ("w-arq’-ib", "M-make.PFV-AOR")]
    glossedWords := [⟨[['U', 'č', 'i', 't', 'i', 'l'], ['l', 'i']], [['t', 'e', 'a', 'c', 'h', 'e', 'r'], ['E', 'R', 'G']]⟩, ⟨[['M', 'u', 'r', 'a', 'd']], [['M', 'u', 'r', 'a', 'd', '.', 'A', 'B', 'S']]⟩, ⟨[['p', 'a', 'r', 'ʁ', 'a', 't']], [['c', 'a', 'l', 'm']]⟩, ⟨[['w'], ['a', 'r', 'q', '’'], ['i', 'b']], [['M'], ['m', 'a', 'k', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R']]⟩, ⟨[['d', 'i', 'r', 'e', 'k', 't', 'u', 'r'], ['l', 'i'], ['r', 'a']], [['p', 'r', 'i', 'n', 'c', 'i', 'p', 'a', 'l'], ['E', 'R', 'G'], ['A', 'D', 'D']]⟩, ⟨[['p', 'a', 'r', 'ʁ', 'a', 't']], [['c', 'a', 'l', 'm']]⟩, ⟨[['w'], ['a', 'r', 'q', '’'], ['i', 'b']], [['M'], ['m', 'a', 'k', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "state")] }

def ex36c : Datum :=
  { id := "kalyakin2026_ex36c"
    source := ⟨"kalyakin-2026", "(36c)"⟩
    reportedIn := none
    language := "muir1238"
    primaryText := "Učitil-li Murad parʁat w-arq’-ib, direktur-li=ra Murad w-arq’-ib"
    glossedTokens := [("Učitil-li", "teacher-ERG"), ("Murad", "Murad.ABS"), ("parʁat", "calm"), ("w-arq’-ib,", "M-make.PFV-AOR"), ("direktur-li=ra", "principal-ERG=ADD"), ("Murad", "Murad.ABS"), ("w-arq’-ib", "M-make.PFV-AOR")]
    glossedWords := [⟨[['U', 'č', 'i', 't', 'i', 'l'], ['l', 'i']], [['t', 'e', 'a', 'c', 'h', 'e', 'r'], ['E', 'R', 'G']]⟩, ⟨[['M', 'u', 'r', 'a', 'd']], [['M', 'u', 'r', 'a', 'd', '.', 'A', 'B', 'S']]⟩, ⟨[['p', 'a', 'r', 'ʁ', 'a', 't']], [['c', 'a', 'l', 'm']]⟩, ⟨[['w'], ['a', 'r', 'q', '’'], ['i', 'b']], [['M'], ['m', 'a', 'k', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R']]⟩, ⟨[['d', 'i', 'r', 'e', 'k', 't', 'u', 'r'], ['l', 'i'], ['r', 'a']], [['p', 'r', 'i', 'n', 'c', 'i', 'p', 'a', 'l'], ['E', 'R', 'G'], ['A', 'D', 'D']]⟩, ⟨[['M', 'u', 'r', 'a', 'd']], [['M', 'u', 'r', 'a', 'd', '.', 'A', 'B', 'S']]⟩, ⟨[['w'], ['a', 'r', 'q', '’'], ['i', 'b']], [['M'], ['m', 'a', 'k', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "state")] }

def ex37 : Datum :=
  { id := "kalyakin2026_ex37"
    source := ⟨"kalyakin-2026", "(37)"⟩
    reportedIn := none
    language := "muir1238"
    primaryText := "Učitil-li Murad parʁat w-arq’-ib, pro Rasulᵢ ⟨tᵢ parʁat⟩ w-arq’-b=akːu"
    glossedTokens := [("Učitil-li", "teacher-ERG"), ("Murad", "Murad.ABS"), ("parʁat", "calm"), ("w-arq’-ib,", "M-make.PFV-AOR"), ("pro", ""), ("Rasulᵢ", "Rasul.ABS"), ("⟨tᵢ", ""), ("parʁat⟩", "calm"), ("w-arq’-b=akːu", "M-make.PFV-AOR=NEG.COP")]
    glossedWords := [⟨[['U', 'č', 'i', 't', 'i', 'l'], ['l', 'i']], [['t', 'e', 'a', 'c', 'h', 'e', 'r'], ['E', 'R', 'G']]⟩, ⟨[['M', 'u', 'r', 'a', 'd']], [['M', 'u', 'r', 'a', 'd', '.', 'A', 'B', 'S']]⟩, ⟨[['p', 'a', 'r', 'ʁ', 'a', 't']], [['c', 'a', 'l', 'm']]⟩, ⟨[['w'], ['a', 'r', 'q', '’'], ['i', 'b']], [['M'], ['m', 'a', 'k', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R']]⟩, ⟨[['p', 'r', 'o']], [[]]⟩, ⟨[['R', 'a', 's', 'u', 'l', 'ᵢ']], [['R', 'a', 's', 'u', 'l', '.', 'A', 'B', 'S']]⟩, ⟨[['⟨', 't', 'ᵢ']], [[]]⟩, ⟨[['p', 'a', 'r', 'ʁ', 'a', 't', '⟩']], [['c', 'a', 'l', 'm']]⟩, ⟨[['w'], ['a', 'r', 'q', '’'], ['b'], ['a', 'k', 'ː', 'u']], [['M'], ['m', 'a', 'k', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R'], ['N', 'E', 'G', '.', 'C', 'O', 'P']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "state"), ("contrastiveFocus", "yes")] }

def ex52a : Datum :=
  { id := "kalyakin2026_ex52a"
    source := ⟨"kalyakin-2026", "(52a)"⟩
    reportedIn := none
    language := "muir1238"
    primaryText := "Murad-li uncːa hark b-arq’-ib, Rasul-li=ra ʡibrra ⟨uncːa hark⟩ b-arq’-ib"
    glossedTokens := [("Murad-li", "Murad-ERG"), ("uncːa", "door.ABS"), ("hark", "open"), ("b-arq’-ib,", "N-make.PFV-AOR"), ("Rasul-li=ra", "Rasul-ERG=ADD"), ("ʡibrra", "again"), ("⟨uncːa", "door.ABS"), ("hark⟩", "open"), ("b-arq’-ib", "N-make.PFV-AOR")]
    glossedWords := [⟨[['M', 'u', 'r', 'a', 'd'], ['l', 'i']], [['M', 'u', 'r', 'a', 'd'], ['E', 'R', 'G']]⟩, ⟨[['u', 'n', 'c', 'ː', 'a']], [['d', 'o', 'o', 'r', '.', 'A', 'B', 'S']]⟩, ⟨[['h', 'a', 'r', 'k']], [['o', 'p', 'e', 'n']]⟩, ⟨[['b'], ['a', 'r', 'q', '’'], ['i', 'b']], [['N'], ['m', 'a', 'k', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R']]⟩, ⟨[['R', 'a', 's', 'u', 'l'], ['l', 'i'], ['r', 'a']], [['R', 'a', 's', 'u', 'l'], ['E', 'R', 'G'], ['A', 'D', 'D']]⟩, ⟨[['ʡ', 'i', 'b', 'r', 'r', 'a']], [['a', 'g', 'a', 'i', 'n']]⟩, ⟨[['⟨', 'u', 'n', 'c', 'ː', 'a']], [['d', 'o', 'o', 'r', '.', 'A', 'B', 'S']]⟩, ⟨[['h', 'a', 'r', 'k', '⟩']], [['o', 'p', 'e', 'n']]⟩, ⟨[['b'], ['a', 'r', 'q', '’'], ['i', 'b']], [['N'], ['m', 'a', 'k', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("repetitive", .acceptable)]
    paperFeatures := [("root", "state")] }

def ex52b : Datum :=
  { id := "kalyakin2026_ex52b"
    source := ⟨"kalyakin-2026", "(52b)"⟩
    reportedIn := none
    language := "muir1238"
    primaryText := "Daʡ-li uncːa čikawq’-un, či-li-k’al il hark b-arq’-ib-li ačːʷi. aχirra Rasul-li ʡibrra ⟨uncːa hark⟩ b-arq’-ib"
    glossedTokens := [("Daʡ-li", "wind-ERG"), ("uncːa", "door.ABS"), ("čikawq’-un,", "close.PFV-AOR"), ("či-li-k’al", "who-ERG-INDEF"), ("il", "this.ADDR.ABS"), ("hark", "open"), ("b-arq’-ib-li", "N-make.PFV-AOR-CVB"), ("ačːʷi.", "NEG.COP.PST"), ("aχirra", "finally"), ("Rasul-li", "Rasul-ERG"), ("ʡibrra", "again"), ("⟨uncːa", "door.ABS"), ("hark⟩", "open"), ("b-arq’-ib", "N-make.PFV-AOR")]
    glossedWords := [⟨[['D', 'a', 'ʡ'], ['l', 'i']], [['w', 'i', 'n', 'd'], ['E', 'R', 'G']]⟩, ⟨[['u', 'n', 'c', 'ː', 'a']], [['d', 'o', 'o', 'r', '.', 'A', 'B', 'S']]⟩, ⟨[['č', 'i', 'k', 'a', 'w', 'q', '’'], ['u', 'n']], [['c', 'l', 'o', 's', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R']]⟩, ⟨[['č', 'i'], ['l', 'i'], ['k', '’', 'a', 'l']], [['w', 'h', 'o'], ['E', 'R', 'G'], ['I', 'N', 'D', 'E', 'F']]⟩, ⟨[['i', 'l']], [['t', 'h', 'i', 's', '.', 'A', 'D', 'D', 'R', '.', 'A', 'B', 'S']]⟩, ⟨[['h', 'a', 'r', 'k']], [['o', 'p', 'e', 'n']]⟩, ⟨[['b'], ['a', 'r', 'q', '’'], ['i', 'b'], ['l', 'i']], [['N'], ['m', 'a', 'k', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R'], ['C', 'V', 'B']]⟩, ⟨[['a', 'č', 'ː', 'ʷ', 'i']], [['N', 'E', 'G', '.', 'C', 'O', 'P', '.', 'P', 'S', 'T']]⟩, ⟨[['a', 'χ', 'i', 'r', 'r', 'a']], [['f', 'i', 'n', 'a', 'l', 'l', 'y']]⟩, ⟨[['R', 'a', 's', 'u', 'l'], ['l', 'i']], [['R', 'a', 's', 'u', 'l'], ['E', 'R', 'G']]⟩, ⟨[['ʡ', 'i', 'b', 'r', 'r', 'a']], [['a', 'g', 'a', 'i', 'n']]⟩, ⟨[['⟨', 'u', 'n', 'c', 'ː', 'a']], [['d', 'o', 'o', 'r', '.', 'A', 'B', 'S']]⟩, ⟨[['h', 'a', 'r', 'k', '⟩']], [['o', 'p', 'e', 'n']]⟩, ⟨[['b'], ['a', 'r', 'q', '’'], ['i', 'b']], [['N'], ['m', 'a', 'k', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("restitutive", .acceptable)]
    paperFeatures := [("root", "state")] }

def ex57 : Datum :=
  { id := "kalyakin2026_ex57"
    source := ⟨"kalyakin-2026", "(57)"⟩
    reportedIn := none
    language := "muir1238"
    primaryText := "Darħa taˤħ Ø-uq-un, rursi=ra r-uq-un"
    glossedTokens := [("Darħa", "child.ABS"), ("taˤħ", "jump"), ("Ø-uq-un,", "M-move.PFV-AOR"), ("rursi=ra", "girl.ABS=ADD"), ("r-uq-un", "F-move.PFV-AOR")]
    glossedWords := [⟨[['D', 'a', 'r', 'ħ', 'a']], [['c', 'h', 'i', 'l', 'd', '.', 'A', 'B', 'S']]⟩, ⟨[['t', 'a', 'ˤ', 'ħ']], [['j', 'u', 'm', 'p']]⟩, ⟨[['Ø'], ['u', 'q'], ['u', 'n']], [['M'], ['m', 'o', 'v', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R']]⟩, ⟨[['r', 'u', 'r', 's', 'i'], ['r', 'a']], [['g', 'i', 'r', 'l', '.', 'A', 'B', 'S'], ['A', 'D', 'D']]⟩, ⟨[['r'], ['u', 'q'], ['u', 'n']], [['F'], ['m', 'o', 'v', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("root", "manner")] }

def ex58 : Datum :=
  { id := "kalyakin2026_ex58"
    source := ⟨"kalyakin-2026", "(58)"⟩
    reportedIn := none
    method := some .elicitation
    language := "muir1238"
    primaryText := "Murad duc’ Ø-uq-un, Musa=ra Ø-uq-un"
    glossedTokens := [("Murad", "Murad-ABS"), ("duc’", "run"), ("Ø-uq-un,", "M-move.PFV-AOR"), ("Musa=ra", "Musa.ABS=ADD"), ("Ø-uq-un", "M-move.PFV-AOR")]
    glossedWords := [⟨[['M', 'u', 'r', 'a', 'd']], [['M', 'u', 'r', 'a', 'd'], ['A', 'B', 'S']]⟩, ⟨[['d', 'u', 'c', '’']], [['r', 'u', 'n']]⟩, ⟨[['Ø'], ['u', 'q'], ['u', 'n']], [['M'], ['m', 'o', 'v', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R']]⟩, ⟨[['M', 'u', 's', 'a'], ['r', 'a']], [['M', 'u', 's', 'a', '.', 'A', 'B', 'S'], ['A', 'D', 'D']]⟩, ⟨[['Ø'], ['u', 'q'], ['u', 'n']], [['M'], ['m', 'o', 'v', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("root", "manner")] }

def ex59 : Datum :=
  { id := "kalyakin2026_ex59"
    source := ⟨"kalyakin-2026", "(59)"⟩
    reportedIn := none
    language := "muir1238"
    primaryText := "Darħa ʡimč w-ik’-u-li saj, rursi=ra r-ik’-u-li sa<r>i"
    glossedTokens := [("Darħa", "child.ABS"), ("ʡimč", "sneeze"), ("w-ik’-u-li", "M-say.IPFV-PROG-CVB"), ("saj,", "COP.M"), ("rursi=ra", "girl.ABS=ADD"), ("r-ik’-u-li", "F-say.IPFV-PROG-CVB"), ("sa<r>i", "<F>COP")]
    glossedWords := [⟨[['D', 'a', 'r', 'ħ', 'a']], [['c', 'h', 'i', 'l', 'd', '.', 'A', 'B', 'S']]⟩, ⟨[['ʡ', 'i', 'm', 'č']], [['s', 'n', 'e', 'e', 'z', 'e']]⟩, ⟨[['w'], ['i', 'k', '’'], ['u'], ['l', 'i']], [['M'], ['s', 'a', 'y', '.', 'I', 'P', 'F', 'V'], ['P', 'R', 'O', 'G'], ['C', 'V', 'B']]⟩, ⟨[['s', 'a', 'j']], [['C', 'O', 'P', '.', 'M']]⟩, ⟨[['r', 'u', 'r', 's', 'i'], ['r', 'a']], [['g', 'i', 'r', 'l', '.', 'A', 'B', 'S'], ['A', 'D', 'D']]⟩, ⟨[['r'], ['i', 'k', '’'], ['u'], ['l', 'i']], [['F'], ['s', 'a', 'y', '.', 'I', 'P', 'F', 'V'], ['P', 'R', 'O', 'G'], ['C', 'V', 'B']]⟩, ⟨[['s', 'a', '<', 'r', '>', 'i']], [['<', 'F', '>', 'C', 'O', 'P']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("root", "manner")] }

def ex75 : Datum :=
  { id := "kalyakin2026_ex75"
    source := ⟨"kalyakin-2026", "(75)"⟩
    reportedIn := none
    language := "muir1238"
    primaryText := "Šin wana d-Ø-ib-li=w? Nu-ni ⟨šin wana⟩ d-arq’-ib=ra"
    glossedTokens := [("Šin", "water.ABS"), ("wana", "warm"), ("d-Ø-ib-li=w?", "NPL-become.PFV-AOR-CVB=PQ"), ("Nu-ni", "I-ERG"), ("⟨šin", "water.ABS"), ("wana⟩", "warm"), ("d-arq’-ib=ra", "NPL-make.PFV-AOR=1")]
    glossedWords := [⟨[['Š', 'i', 'n']], [['w', 'a', 't', 'e', 'r', '.', 'A', 'B', 'S']]⟩, ⟨[['w', 'a', 'n', 'a']], [['w', 'a', 'r', 'm']]⟩, ⟨[['d'], ['Ø'], ['i', 'b'], ['l', 'i'], ['w']], [['N', 'P', 'L'], ['b', 'e', 'c', 'o', 'm', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R'], ['C', 'V', 'B'], ['P', 'Q']]⟩, ⟨[['N', 'u'], ['n', 'i']], [['I'], ['E', 'R', 'G']]⟩, ⟨[['⟨', 'š', 'i', 'n']], [['w', 'a', 't', 'e', 'r', '.', 'A', 'B', 'S']]⟩, ⟨[['w', 'a', 'n', 'a', '⟩']], [['w', 'a', 'r', 'm']]⟩, ⟨[['d'], ['a', 'r', 'q', '’'], ['i', 'b'], ['r', 'a']], [['N', 'P', 'L'], ['m', 'a', 'k', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R'], ['1']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Inchoative antecedent, causative target."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "state")] }

def ex76 : Datum :=
  { id := "kalyakin2026_ex76"
    source := ⟨"kalyakin-2026", "(76)"⟩
    reportedIn := none
    language := "muir1238"
    primaryText := "Ħu-ni šin wana d-arq’-atːi=w? Il-tːiᵢ ⟨tᵢ wana⟩ d-Ø-ib"
    glossedTokens := [("Ħu-ni", "you-ERG"), ("šin", "water.ABS"), ("wana", "warm"), ("d-arq’-atːi=w?", "NPL-make.PFV-AOR.2SG=PQ"), ("Il-tːiᵢ", "this.ADDR.ABS-PL"), ("⟨tᵢ", ""), ("wana⟩", "warm"), ("d-Ø-ib", "NPL-become.PFV-AOR")]
    glossedWords := [⟨[['Ħ', 'u'], ['n', 'i']], [['y', 'o', 'u'], ['E', 'R', 'G']]⟩, ⟨[['š', 'i', 'n']], [['w', 'a', 't', 'e', 'r', '.', 'A', 'B', 'S']]⟩, ⟨[['w', 'a', 'n', 'a']], [['w', 'a', 'r', 'm']]⟩, ⟨[['d'], ['a', 'r', 'q', '’'], ['a', 't', 'ː', 'i'], ['w']], [['N', 'P', 'L'], ['m', 'a', 'k', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R', '.', '2', 'S', 'G'], ['P', 'Q']]⟩, ⟨[['I', 'l'], ['t', 'ː', 'i', 'ᵢ']], [['t', 'h', 'i', 's', '.', 'A', 'D', 'D', 'R', '.', 'A', 'B', 'S'], ['P', 'L']]⟩, ⟨[['⟨', 't', 'ᵢ']], [[]]⟩, ⟨[['w', 'a', 'n', 'a', '⟩']], [['w', 'a', 'r', 'm']]⟩, ⟨[['d'], ['Ø'], ['i', 'b']], [['N', 'P', 'L'], ['b', 'e', 'c', 'o', 'm', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Causative antecedent, inchoative target."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "state")] }

def ex78 : Datum :=
  { id := "kalyakin2026_ex78"
    source := ⟨"kalyakin-2026", "(78)"⟩
    reportedIn := none
    language := "muir1238"
    primaryText := "Pat’imat-li χureg wana b-arq’-ib, Ashura-li=ra ⟨χureg wana⟩ b-Ø-iq-ib"
    glossedTokens := [("Pat’imat-li", "Patimat-ERG"), ("χureg", "food.ABS"), ("wana", "warm"), ("b-arq’-ib,", "N-make.PFV-AOR"), ("Ashura-li=ra", "Ashura-ERG=ADD"), ("⟨χureg", "food.ABS"), ("wana⟩", "warm"), ("b-Ø-iq-ib", "N-become.PFV-CAUS-AOR")]
    glossedWords := [⟨[['P', 'a', 't', '’', 'i', 'm', 'a', 't'], ['l', 'i']], [['P', 'a', 't', 'i', 'm', 'a', 't'], ['E', 'R', 'G']]⟩, ⟨[['χ', 'u', 'r', 'e', 'g']], [['f', 'o', 'o', 'd', '.', 'A', 'B', 'S']]⟩, ⟨[['w', 'a', 'n', 'a']], [['w', 'a', 'r', 'm']]⟩, ⟨[['b'], ['a', 'r', 'q', '’'], ['i', 'b']], [['N'], ['m', 'a', 'k', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R']]⟩, ⟨[['A', 's', 'h', 'u', 'r', 'a'], ['l', 'i'], ['r', 'a']], [['A', 's', 'h', 'u', 'r', 'a'], ['E', 'R', 'G'], ['A', 'D', 'D']]⟩, ⟨[['⟨', 'χ', 'u', 'r', 'e', 'g']], [['f', 'o', 'o', 'd', '.', 'A', 'B', 'S']]⟩, ⟨[['w', 'a', 'n', 'a', '⟩']], [['w', 'a', 'r', 'm']]⟩, ⟨[['b'], ['Ø'], ['i', 'q'], ['i', 'b']], [['N'], ['b', 'e', 'c', 'o', 'm', 'e', '.', 'P', 'F', 'V'], ['C', 'A', 'U', 'S'], ['A', 'O', 'R']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "state")] }

def ex79 : Datum :=
  { id := "kalyakin2026_ex79"
    source := ⟨"kalyakin-2026", "(79)"⟩
    reportedIn := none
    language := "muir1238"
    primaryText := "Šin wana d-Ø-ib-li=w? Nu-ni ⟨šin wana⟩ d-Ø-iq-ib=ra"
    glossedTokens := [("Šin", "water.ABS"), ("wana", "warm"), ("d-Ø-ib-li=w?", "NPL-become.PFV-AOR-CVB=PQ"), ("Nu-ni", "I-ERG"), ("⟨šin", "water.ABS"), ("wana⟩", "warm"), ("d-Ø-iq-ib=ra", "NPL-become.PFV-CAUS-AOR=ADD")]
    glossedWords := [⟨[['Š', 'i', 'n']], [['w', 'a', 't', 'e', 'r', '.', 'A', 'B', 'S']]⟩, ⟨[['w', 'a', 'n', 'a']], [['w', 'a', 'r', 'm']]⟩, ⟨[['d'], ['Ø'], ['i', 'b'], ['l', 'i'], ['w']], [['N', 'P', 'L'], ['b', 'e', 'c', 'o', 'm', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R'], ['C', 'V', 'B'], ['P', 'Q']]⟩, ⟨[['N', 'u'], ['n', 'i']], [['I'], ['E', 'R', 'G']]⟩, ⟨[['⟨', 'š', 'i', 'n']], [['w', 'a', 't', 'e', 'r', '.', 'A', 'B', 'S']]⟩, ⟨[['w', 'a', 'n', 'a', '⟩']], [['w', 'a', 'r', 'm']]⟩, ⟨[['d'], ['Ø'], ['i', 'q'], ['i', 'b'], ['r', 'a']], [['N', 'P', 'L'], ['b', 'e', 'c', 'o', 'm', 'e', '.', 'P', 'F', 'V'], ['C', 'A', 'U', 'S'], ['A', 'O', 'R'], ['A', 'D', 'D']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Intransitive antecedent, causativized intransitive target."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "state")] }

def ex80 : Datum :=
  { id := "kalyakin2026_ex80"
    source := ⟨"kalyakin-2026", "(80)"⟩
    reportedIn := none
    language := "muir1238"
    primaryText := "Rasul-li šin wana d-arq’-ib-li=w? Musa-li ⟨šin wana⟩ d-arq’-iq-ib"
    glossedTokens := [("Rasul-li", "Rasul-ERG"), ("šin", "water.ABS"), ("wana", "warm"), ("d-arq’-ib-li=w?", "NPL-make.PFV-AOR-CVB=PQ"), ("Musa-li", "Musa-ERG"), ("⟨šin", "water.ABS"), ("wana⟩", "warm"), ("d-arq’-iq-ib", "NPL-make.PFV-CAUS-AOR")]
    glossedWords := [⟨[['R', 'a', 's', 'u', 'l'], ['l', 'i']], [['R', 'a', 's', 'u', 'l'], ['E', 'R', 'G']]⟩, ⟨[['š', 'i', 'n']], [['w', 'a', 't', 'e', 'r', '.', 'A', 'B', 'S']]⟩, ⟨[['w', 'a', 'n', 'a']], [['w', 'a', 'r', 'm']]⟩, ⟨[['d'], ['a', 'r', 'q', '’'], ['i', 'b'], ['l', 'i'], ['w']], [['N', 'P', 'L'], ['m', 'a', 'k', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R'], ['C', 'V', 'B'], ['P', 'Q']]⟩, ⟨[['M', 'u', 's', 'a'], ['l', 'i']], [['M', 'u', 's', 'a'], ['E', 'R', 'G']]⟩, ⟨[['⟨', 'š', 'i', 'n']], [['w', 'a', 't', 'e', 'r', '.', 'A', 'B', 'S']]⟩, ⟨[['w', 'a', 'n', 'a', '⟩']], [['w', 'a', 'r', 'm']]⟩, ⟨[['d'], ['a', 'r', 'q', '’'], ['i', 'q'], ['i', 'b']], [['N', 'P', 'L'], ['m', 'a', 'k', 'e', '.', 'P', 'F', 'V'], ['C', 'A', 'U', 'S'], ['A', 'O', 'R']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Transitive antecedent, causativized transitive target."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "state")] }

def ex80_causee : Datum :=
  { id := "kalyakin2026_ex80_causee"
    source := ⟨"kalyakin-2026", "(80)"⟩
    reportedIn := none
    language := "muir1238"
    primaryText := "Rasul-li šin wana d-arq’-ib-li=w? Musa-li il-i-cːi ⟨šin wana⟩ d-arq’-iq-ib"
    glossedTokens := [("Rasul-li", "Rasul-ERG"), ("šin", "water.ABS"), ("wana", "warm"), ("d-arq’-ib-li=w?", "NPL-make.PFV-AOR-CVB=PQ"), ("Musa-li", "Musa-ERG"), ("il-i-cːi", "this.ADDR-OBL-INTER"), ("⟨šin", "water.ABS"), ("wana⟩", "warm"), ("d-arq’-iq-ib", "NPL-make.PFV-CAUS-AOR")]
    glossedWords := [⟨[['R', 'a', 's', 'u', 'l'], ['l', 'i']], [['R', 'a', 's', 'u', 'l'], ['E', 'R', 'G']]⟩, ⟨[['š', 'i', 'n']], [['w', 'a', 't', 'e', 'r', '.', 'A', 'B', 'S']]⟩, ⟨[['w', 'a', 'n', 'a']], [['w', 'a', 'r', 'm']]⟩, ⟨[['d'], ['a', 'r', 'q', '’'], ['i', 'b'], ['l', 'i'], ['w']], [['N', 'P', 'L'], ['m', 'a', 'k', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R'], ['C', 'V', 'B'], ['P', 'Q']]⟩, ⟨[['M', 'u', 's', 'a'], ['l', 'i']], [['M', 'u', 's', 'a'], ['E', 'R', 'G']]⟩, ⟨[['i', 'l'], ['i'], ['c', 'ː', 'i']], [['t', 'h', 'i', 's', '.', 'A', 'D', 'D', 'R'], ['O', 'B', 'L'], ['I', 'N', 'T', 'E', 'R']]⟩, ⟨[['⟨', 'š', 'i', 'n']], [['w', 'a', 't', 'e', 'r', '.', 'A', 'B', 'S']]⟩, ⟨[['w', 'a', 'n', 'a', '⟩']], [['w', 'a', 'r', 'm']]⟩, ⟨[['d'], ['a', 'r', 'q', '’'], ['i', 'q'], ['i', 'b']], [['N', 'P', 'L'], ['m', 'a', 'k', 'e', '.', 'P', 'F', 'V'], ['C', 'A', 'U', 'S'], ['A', 'O', 'R']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Transitive antecedent, causativized transitive target."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "state")] }

def ex85 : Datum :=
  { id := "kalyakin2026_ex85"
    source := ⟨"kalyakin-2026", "(85)"⟩
    reportedIn := none
    language := "muir1238"
    primaryText := "Bašir-li qur-ri dawk b-irq’-u-li saj, Musa=ra ⟨qur-r-a-li dawk⟩ w-irq’-u-li saj"
    glossedTokens := [("Bašir-li", "Bashir-ERG"), ("qur-ri", "house.ABS-PL"), ("dawk", "repaired"), ("b-irq’-u-li", "NPL-make.IPFV-PROG-CVB"), ("saj,", "COP.M"), ("Musa=ra", "Musa.ABS=ADD"), ("⟨qur-r-a-li", "house-PL-OBL.PL-ERG"), ("dawk⟩", "repaired"), ("w-irq’-u-li", "M-make.IPFV-PROG-CVB"), ("saj", "COP.M")]
    glossedWords := [⟨[['B', 'a', 'š', 'i', 'r'], ['l', 'i']], [['B', 'a', 's', 'h', 'i', 'r'], ['E', 'R', 'G']]⟩, ⟨[['q', 'u', 'r'], ['r', 'i']], [['h', 'o', 'u', 's', 'e', '.', 'A', 'B', 'S'], ['P', 'L']]⟩, ⟨[['d', 'a', 'w', 'k']], [['r', 'e', 'p', 'a', 'i', 'r', 'e', 'd']]⟩, ⟨[['b'], ['i', 'r', 'q', '’'], ['u'], ['l', 'i']], [['N', 'P', 'L'], ['m', 'a', 'k', 'e', '.', 'I', 'P', 'F', 'V'], ['P', 'R', 'O', 'G'], ['C', 'V', 'B']]⟩, ⟨[['s', 'a', 'j']], [['C', 'O', 'P', '.', 'M']]⟩, ⟨[['M', 'u', 's', 'a'], ['r', 'a']], [['M', 'u', 's', 'a', '.', 'A', 'B', 'S'], ['A', 'D', 'D']]⟩, ⟨[['⟨', 'q', 'u', 'r'], ['r'], ['a'], ['l', 'i']], [['h', 'o', 'u', 's', 'e'], ['P', 'L'], ['O', 'B', 'L', '.', 'P', 'L'], ['E', 'R', 'G']]⟩, ⟨[['d', 'a', 'w', 'k', '⟩']], [['r', 'e', 'p', 'a', 'i', 'r', 'e', 'd']]⟩, ⟨[['w'], ['i', 'r', 'q', '’'], ['u'], ['l', 'i']], [['M'], ['m', 'a', 'k', 'e', '.', 'I', 'P', 'F', 'V'], ['P', 'R', 'O', 'G'], ['C', 'V', 'B']]⟩, ⟨[['s', 'a', 'j']], [['C', 'O', 'P', '.', 'M']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Transitive antecedent, antipassive target."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "state")] }

def ex86 : Datum :=
  { id := "kalyakin2026_ex86"
    source := ⟨"kalyakin-2026", "(86)"⟩
    reportedIn := none
    language := "muir1238"
    primaryText := "Bašir qur-r-a-li dawk w-irq’-u-li saj, Musa=ra ⟨qur-r-a-li dawk⟩ w-irq’-u-li saj"
    glossedTokens := [("Bašir", "Bashir.ABS"), ("qur-r-a-li", "house-PL-OBL.PL-ERG"), ("dawk", "repaired"), ("w-irq’-u-li", "M-make.IPFV-PROG-CVB"), ("saj,", "COP.M"), ("Musa=ra", "Musa.ABS=ADD"), ("⟨qur-r-a-li", "house-PL-OBL.PL-ERG"), ("dawk⟩", "repaired"), ("w-irq’-u-li", "M-make.IPFV-PROG-CVB"), ("saj", "COP.M")]
    glossedWords := [⟨[['B', 'a', 'š', 'i', 'r']], [['B', 'a', 's', 'h', 'i', 'r', '.', 'A', 'B', 'S']]⟩, ⟨[['q', 'u', 'r'], ['r'], ['a'], ['l', 'i']], [['h', 'o', 'u', 's', 'e'], ['P', 'L'], ['O', 'B', 'L', '.', 'P', 'L'], ['E', 'R', 'G']]⟩, ⟨[['d', 'a', 'w', 'k']], [['r', 'e', 'p', 'a', 'i', 'r', 'e', 'd']]⟩, ⟨[['w'], ['i', 'r', 'q', '’'], ['u'], ['l', 'i']], [['M'], ['m', 'a', 'k', 'e', '.', 'I', 'P', 'F', 'V'], ['P', 'R', 'O', 'G'], ['C', 'V', 'B']]⟩, ⟨[['s', 'a', 'j']], [['C', 'O', 'P', '.', 'M']]⟩, ⟨[['M', 'u', 's', 'a'], ['r', 'a']], [['M', 'u', 's', 'a', '.', 'A', 'B', 'S'], ['A', 'D', 'D']]⟩, ⟨[['⟨', 'q', 'u', 'r'], ['r'], ['a'], ['l', 'i']], [['h', 'o', 'u', 's', 'e'], ['P', 'L'], ['O', 'B', 'L', '.', 'P', 'L'], ['E', 'R', 'G']]⟩, ⟨[['d', 'a', 'w', 'k', '⟩']], [['r', 'e', 'p', 'a', 'i', 'r', 'e', 'd']]⟩, ⟨[['w'], ['i', 'r', 'q', '’'], ['u'], ['l', 'i']], [['M'], ['m', 'a', 'k', 'e', '.', 'I', 'P', 'F', 'V'], ['P', 'R', 'O', 'G'], ['C', 'V', 'B']]⟩, ⟨[['s', 'a', 'j']], [['C', 'O', 'P', '.', 'M']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Antipassive antecedent, antipassive target."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "state")] }

def ex88 : Datum :=
  { id := "kalyakin2026_ex88"
    source := ⟨"kalyakin-2026", "(88)"⟩
    reportedIn := none
    language := "muir1238"
    primaryText := "Pat’imat-li χureg wana b-arq’-ib, šinᵢ ⟨tᵢ wana⟩ d-Ø-ib"
    glossedTokens := [("Pat’imat-li", "Patimat-ERG"), ("χureg", "food.ABS"), ("wana", "warm"), ("b-arq’-ib,", "N-make.PFV-AOR"), ("šinᵢ", "water.ABS"), ("⟨tᵢ", ""), ("wana⟩", "warm"), ("d-Ø-ib", "NPL-become.PFV-AOR")]
    glossedWords := [⟨[['P', 'a', 't', '’', 'i', 'm', 'a', 't'], ['l', 'i']], [['P', 'a', 't', 'i', 'm', 'a', 't'], ['E', 'R', 'G']]⟩, ⟨[['χ', 'u', 'r', 'e', 'g']], [['f', 'o', 'o', 'd', '.', 'A', 'B', 'S']]⟩, ⟨[['w', 'a', 'n', 'a']], [['w', 'a', 'r', 'm']]⟩, ⟨[['b'], ['a', 'r', 'q', '’'], ['i', 'b']], [['N'], ['m', 'a', 'k', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R']]⟩, ⟨[['š', 'i', 'n', 'ᵢ']], [['w', 'a', 't', 'e', 'r', '.', 'A', 'B', 'S']]⟩, ⟨[['⟨', 't', 'ᵢ']], [[]]⟩, ⟨[['w', 'a', 'n', 'a', '⟩']], [['w', 'a', 'r', 'm']]⟩, ⟨[['d'], ['Ø'], ['i', 'b']], [['N', 'P', 'L'], ['b', 'e', 'c', 'o', 'm', 'e', '.', 'P', 'F', 'V'], ['A', 'O', 'R']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "state")] }

def all : List Datum := [ex3, ex29, ex30a, ex30b, ex32, ex36a, ex36b, ex36c, ex37, ex52a, ex52b, ex57, ex58, ex59, ex75, ex76, ex78, ex79, ex80, ex80_causee, ex85, ex86, ex88]

end Kalyakin2026.Examples
