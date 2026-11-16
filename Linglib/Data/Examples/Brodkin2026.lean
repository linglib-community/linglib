module

public import Linglib.Data.Examples.Schema

/-!
# `Brodkin2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Brodkin2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Brodkin2026.Examples`.
-/

@[expose] public section

namespace Brodkin2026.Examples

def ex_33a : Datum :=
  { id := "brodkin2026_33a"
    source := ⟨"brodkin-2026", "(33a)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "méloᴴ uwéŋanᴴ ndi wúkuᴴ éᴴ."
    glossedTokens := [("meloʔ", "want"), ("o", "2ABS"), ("u-beŋaŋ", "1ERG-give"), ("ndi", "this"), ("buku", "book"), ("e", "here")]
    glossedWords := [⟨['m', 'e', 'l', 'o', 'ʔ'], ['w', 'a', 'n', 't'], [⟨['m', 'e', 'l', 'o', 'ʔ'], ['w', 'a', 'n', 't'], none⟩]⟩, ⟨['o'], ['2', 'A', 'B', 'S'], [⟨['o'], ['2', 'A', 'B', 'S'], none⟩]⟩, ⟨['u', '-', 'b', 'e', 'ŋ', 'a', 'ŋ'], ['1', 'E', 'R', 'G', '-', 'g', 'i', 'v', 'e'], [⟨['u'], ['1', 'E', 'R', 'G'], none⟩, ⟨['b', 'e', 'ŋ', 'a', 'ŋ'], ['g', 'i', 'v', 'e'], some '-'⟩]⟩, ⟨['n', 'd', 'i'], ['t', 'h', 'i', 's'], [⟨['n', 'd', 'i'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['b', 'u', 'k', 'u'], ['b', 'o', 'o', 'k'], [⟨['b', 'u', 'k', 'u'], ['b', 'o', 'o', 'k'], none⟩]⟩, ⟨['e'], ['h', 'e', 'r', 'e'], [⟨['e'], ['h', 'e', 'r', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "this_in_hand"), ("allomorph", "short"), ("syntax", "complement")] }

def ex_33b : Datum :=
  { id := "brodkin2026_33b"
    source := ⟨"brodkin-2026", "(33b)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "méloᴴ uwéŋaᴴ ĩ́ndiᴴ éᴴ."
    glossedTokens := [("meloʔ", "want"), ("o", "2ABS"), ("u-beŋaŋ", "1ERG-give"), ("ndi", "this"), ("e", "here")]
    glossedWords := [⟨['m', 'e', 'l', 'o', 'ʔ'], ['w', 'a', 'n', 't'], [⟨['m', 'e', 'l', 'o', 'ʔ'], ['w', 'a', 'n', 't'], none⟩]⟩, ⟨['o'], ['2', 'A', 'B', 'S'], [⟨['o'], ['2', 'A', 'B', 'S'], none⟩]⟩, ⟨['u', '-', 'b', 'e', 'ŋ', 'a', 'ŋ'], ['1', 'E', 'R', 'G', '-', 'g', 'i', 'v', 'e'], [⟨['u'], ['1', 'E', 'R', 'G'], none⟩, ⟨['b', 'e', 'ŋ', 'a', 'ŋ'], ['g', 'i', 'v', 'e'], some '-'⟩]⟩, ⟨['n', 'd', 'i'], ['t', 'h', 'i', 's'], [⟨['n', 'd', 'i'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['e'], ['h', 'e', 'r', 'e'], [⟨['e'], ['h', 'e', 'r', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "this_in_hand"), ("allomorph", "long"), ("syntax", "adjunct"), ("next", "footed")] }

def ex_36a : Datum :=
  { id := "brodkin2026_36a"
    source := ⟨"brodkin-2026", "(36a)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "do anʤóroᴴ ndaŋ ŋúra wéɣaᴴ óᴴ."
    glossedTokens := [("do", "that"), ("anʤoro", "coconut"), ("ndaŋ", "not"), ("ŋura", "unripe"), ("bega", "too"), ("o", "there")]
    glossedWords := [⟨['d', 'o'], ['t', 'h', 'a', 't'], [⟨['d', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['a', 'n', 'ʤ', 'o', 'r', 'o'], ['c', 'o', 'c', 'o', 'n', 'u', 't'], [⟨['a', 'n', 'ʤ', 'o', 'r', 'o'], ['c', 'o', 'c', 'o', 'n', 'u', 't'], none⟩]⟩, ⟨['n', 'd', 'a', 'ŋ'], ['n', 'o', 't'], [⟨['n', 'd', 'a', 'ŋ'], ['n', 'o', 't'], none⟩]⟩, ⟨['ŋ', 'u', 'r', 'a'], ['u', 'n', 'r', 'i', 'p', 'e'], [⟨['ŋ', 'u', 'r', 'a'], ['u', 'n', 'r', 'i', 'p', 'e'], none⟩]⟩, ⟨['b', 'e', 'g', 'a'], ['t', 'o', 'o'], [⟨['b', 'e', 'g', 'a'], ['t', 'o', 'o'], none⟩]⟩, ⟨['o'], ['t', 'h', 'e', 'r', 'e'], [⟨['o'], ['t', 'h', 'e', 'r', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "neg"), ("allomorph", "short"), ("syntax", "complement")] }

def ex_36b : Datum :=
  { id := "brodkin2026_36b"
    source := ⟨"brodkin-2026", "(36b)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "tapi ɹo anʤóroᴴ andíaŋᴴ óᴴ."
    glossedTokens := [("tapi", "but"), ("do", "that"), ("anʤoro", "coconut"), ("ndaŋ", "not"), ("o", "there")]
    glossedWords := [⟨['t', 'a', 'p', 'i'], ['b', 'u', 't'], [⟨['t', 'a', 'p', 'i'], ['b', 'u', 't'], none⟩]⟩, ⟨['d', 'o'], ['t', 'h', 'a', 't'], [⟨['d', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['a', 'n', 'ʤ', 'o', 'r', 'o'], ['c', 'o', 'c', 'o', 'n', 'u', 't'], [⟨['a', 'n', 'ʤ', 'o', 'r', 'o'], ['c', 'o', 'c', 'o', 'n', 'u', 't'], none⟩]⟩, ⟨['n', 'd', 'a', 'ŋ'], ['n', 'o', 't'], [⟨['n', 'd', 'a', 'ŋ'], ['n', 'o', 't'], none⟩]⟩, ⟨['o'], ['t', 'h', 'e', 'r', 'e'], [⟨['o'], ['t', 'h', 'e', 'r', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "De anjoro ngura bega e, … 'This coconut is too unripe, …'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "neg"), ("allomorph", "long"), ("syntax", "adjunct"), ("next", "footed")] }

def ex_40a : Datum :=
  { id := "brodkin2026_40a"
    source := ⟨"brodkin-2026", "(40a)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "á ɹúaᴴ píllóaᴴ?"
    glossedTokens := [("a", "what"), ("dua", "still"), ("piŋ-loa", "ANTIP-sound")]
    glossedWords := [⟨['a'], ['w', 'h', 'a', 't'], [⟨['a'], ['w', 'h', 'a', 't'], none⟩]⟩, ⟨['d', 'u', 'a'], ['s', 't', 'i', 'l', 'l'], [⟨['d', 'u', 'a'], ['s', 't', 'i', 'l', 'l'], none⟩]⟩, ⟨['p', 'i', 'ŋ', '-', 'l', 'o', 'a'], ['A', 'N', 'T', 'I', 'P', '-', 's', 'o', 'u', 'n', 'd'], [⟨['p', 'i', 'ŋ'], ['A', 'N', 'T', 'I', 'P'], none⟩, ⟨['l', 'o', 'a'], ['s', 'o', 'u', 'n', 'd'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "what"), ("allomorph", "short"), ("syntax", "host")] }

def ex_40b : Datum :=
  { id := "brodkin2026_40b"
    source := ⟨"brodkin-2026", "(40b)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "ápaᴴ píllóaᴴ?"
    glossedTokens := [("a", "what"), ("piŋ-loa", "ANTIP-sound")]
    glossedWords := [⟨['a'], ['w', 'h', 'a', 't'], [⟨['a'], ['w', 'h', 'a', 't'], none⟩]⟩, ⟨['p', 'i', 'ŋ', '-', 'l', 'o', 'a'], ['A', 'N', 'T', 'I', 'P', '-', 's', 'o', 'u', 'n', 'd'], [⟨['p', 'i', 'ŋ'], ['A', 'N', 'T', 'I', 'P'], none⟩, ⟨['l', 'o', 'a'], ['s', 'o', 'u', 'n', 'd'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "what"), ("allomorph", "long"), ("syntax", "sisters"), ("next", "footed"), ("maxPhi", "same")] }

def ex_41a : Datum :=
  { id := "brodkin2026_41a"
    source := ⟨"brodkin-2026", "(41a)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "ná násamᴴ mweŋéiᴴ?"
    glossedTokens := [("na", "which"), ("nasaŋ", "every"), ("mu-eŋei", "2ERG-be.in")]
    glossedWords := [⟨['n', 'a'], ['w', 'h', 'i', 'c', 'h'], [⟨['n', 'a'], ['w', 'h', 'i', 'c', 'h'], none⟩]⟩, ⟨['n', 'a', 's', 'a', 'ŋ'], ['e', 'v', 'e', 'r', 'y'], [⟨['n', 'a', 's', 'a', 'ŋ'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['m', 'u', '-', 'e', 'ŋ', 'e', 'i'], ['2', 'E', 'R', 'G', '-', 'b', 'e', '.', 'i', 'n'], [⟨['m', 'u'], ['2', 'E', 'R', 'G'], none⟩, ⟨['e', 'ŋ', 'e', 'i'], ['b', 'e', '.', 'i', 'n'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "which"), ("allomorph", "short"), ("syntax", "host")] }

def ex_41b : Datum :=
  { id := "brodkin2026_41b"
    source := ⟨"brodkin-2026", "(41b)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "ínnaᴴ wémmeᴴ?"
    glossedTokens := [("na", "which"), ("bemme", "fall")]
    glossedWords := [⟨['n', 'a'], ['w', 'h', 'i', 'c', 'h'], [⟨['n', 'a'], ['w', 'h', 'i', 'c', 'h'], none⟩]⟩, ⟨['b', 'e', 'm', 'm', 'e'], ['f', 'a', 'l', 'l'], [⟨['b', 'e', 'm', 'm', 'e'], ['f', 'a', 'l', 'l'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "which"), ("allomorph", "long"), ("syntax", "sisters"), ("next", "footed"), ("maxPhi", "same")] }

def ex_42a : Datum :=
  { id := "brodkin2026_42a"
    source := ⟨"brodkin-2026", "(42a)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "né násamᴴ mwítaᴴ?"
    glossedTokens := [("nai", "who"), ("nasaŋ", "every"), ("mu-ita", "2ERG-see")]
    glossedWords := [⟨['n', 'a', 'i'], ['w', 'h', 'o'], [⟨['n', 'a', 'i'], ['w', 'h', 'o'], none⟩]⟩, ⟨['n', 'a', 's', 'a', 'ŋ'], ['e', 'v', 'e', 'r', 'y'], [⟨['n', 'a', 's', 'a', 'ŋ'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['m', 'u', '-', 'i', 't', 'a'], ['2', 'E', 'R', 'G', '-', 's', 'e', 'e'], [⟨['m', 'u'], ['2', 'E', 'R', 'G'], none⟩, ⟨['i', 't', 'a'], ['s', 'e', 'e'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "who"), ("allomorph", "short"), ("syntax", "host")] }

def ex_42b : Datum :=
  { id := "brodkin2026_42b"
    source := ⟨"brodkin-2026", "(42b)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "ínneᴴ lámbaᴴ?"
    glossedTokens := [("nai", "who"), ("lamba", "go")]
    glossedWords := [⟨['n', 'a', 'i'], ['w', 'h', 'o'], [⟨['n', 'a', 'i'], ['w', 'h', 'o'], none⟩]⟩, ⟨['l', 'a', 'm', 'b', 'a'], ['g', 'o'], [⟨['l', 'a', 'm', 'b', 'a'], ['g', 'o'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "who"), ("allomorph", "long"), ("syntax", "sisters"), ("next", "footed"), ("maxPhi", "same")] }

def ex_56a : Datum :=
  { id := "brodkin2026_56a"
    source := ⟨"brodkin-2026", "(56a)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "máã́paᴴ o míeʔᴴ?"
    glossedTokens := [("maŋ-apa", "VERBALIZER-what"), ("o", "2ABS"), ("mieʔ", "2PL")]
    glossedWords := [⟨['m', 'a', 'ŋ', '-', 'a', 'p', 'a'], ['V', 'E', 'R', 'B', 'A', 'L', 'I', 'Z', 'E', 'R', '-', 'w', 'h', 'a', 't'], [⟨['m', 'a', 'ŋ'], ['V', 'E', 'R', 'B', 'A', 'L', 'I', 'Z', 'E', 'R'], none⟩, ⟨['a', 'p', 'a'], ['w', 'h', 'a', 't'], some '-'⟩]⟩, ⟨['o'], ['2', 'A', 'B', 'S'], [⟨['o'], ['2', 'A', 'B', 'S'], none⟩]⟩, ⟨['m', 'i', 'e', 'ʔ'], ['2', 'P', 'L'], [⟨['m', 'i', 'e', 'ʔ'], ['2', 'P', 'L'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "what"), ("allomorph", "long"), ("syntax", "sisters"), ("affix", "verbalizer")] }

def ex_56b : Datum :=
  { id := "brodkin2026_56b"
    source := ⟨"brodkin-2026", "(56b)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "máã́pa násaŋᴴ o míeʔᴴ?"
    glossedTokens := [("maŋ-apa", "VERBALIZER-what"), ("nasaŋ", "every"), ("o", "2ABS"), ("mieʔ", "2PL")]
    glossedWords := [⟨['m', 'a', 'ŋ', '-', 'a', 'p', 'a'], ['V', 'E', 'R', 'B', 'A', 'L', 'I', 'Z', 'E', 'R', '-', 'w', 'h', 'a', 't'], [⟨['m', 'a', 'ŋ'], ['V', 'E', 'R', 'B', 'A', 'L', 'I', 'Z', 'E', 'R'], none⟩, ⟨['a', 'p', 'a'], ['w', 'h', 'a', 't'], some '-'⟩]⟩, ⟨['n', 'a', 's', 'a', 'ŋ'], ['e', 'v', 'e', 'r', 'y'], [⟨['n', 'a', 's', 'a', 'ŋ'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['o'], ['2', 'A', 'B', 'S'], [⟨['o'], ['2', 'A', 'B', 'S'], none⟩]⟩, ⟨['m', 'i', 'e', 'ʔ'], ['2', 'P', 'L'], [⟨['m', 'i', 'e', 'ʔ'], ['2', 'P', 'L'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "what"), ("allomorph", "long"), ("syntax", "host"), ("affix", "verbalizer")] }

def ex_76a : Datum :=
  { id := "brodkin2026_76a"
    source := ⟨"brodkin-2026", "(76a)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "ápaᴴ máppakéʔdeʔᴴ i?"
    glossedTokens := [("a", "what"), ("maŋ-pakeʔdeʔ", "AF-awaken"), ("i", "3ACC")]
    glossedWords := [⟨['a'], ['w', 'h', 'a', 't'], [⟨['a'], ['w', 'h', 'a', 't'], none⟩]⟩, ⟨['m', 'a', 'ŋ', '-', 'p', 'a', 'k', 'e', 'ʔ', 'd', 'e', 'ʔ'], ['A', 'F', '-', 'a', 'w', 'a', 'k', 'e', 'n'], [⟨['m', 'a', 'ŋ'], ['A', 'F'], none⟩, ⟨['p', 'a', 'k', 'e', 'ʔ', 'd', 'e', 'ʔ'], ['a', 'w', 'a', 'k', 'e', 'n'], some '-'⟩]⟩, ⟨['i'], ['3', 'A', 'C', 'C'], [⟨['i'], ['3', 'A', 'C', 'C'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "what"), ("allomorph", "long"), ("syntax", "sisters"), ("next", "footed"), ("maxPhi", "same")] }

def ex_76b : Datum :=
  { id := "brodkin2026_76b"
    source := ⟨"brodkin-2026", "(76b)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "á naᴴmáppakéʔdeʔᴴ i?"
    glossedTokens := [("a", "what"), ("na-maŋ-pakeʔdeʔ", "FUT-AF-awaken"), ("i", "3ACC")]
    glossedWords := [⟨['a'], ['w', 'h', 'a', 't'], [⟨['a'], ['w', 'h', 'a', 't'], none⟩]⟩, ⟨['n', 'a', '-', 'm', 'a', 'ŋ', '-', 'p', 'a', 'k', 'e', 'ʔ', 'd', 'e', 'ʔ'], ['F', 'U', 'T', '-', 'A', 'F', '-', 'a', 'w', 'a', 'k', 'e', 'n'], [⟨['n', 'a'], ['F', 'U', 'T'], none⟩, ⟨['m', 'a', 'ŋ'], ['A', 'F'], some '-'⟩, ⟨['p', 'a', 'k', 'e', 'ʔ', 'd', 'e', 'ʔ'], ['a', 'w', 'a', 'k', 'e', 'n'], some '-'⟩]⟩, ⟨['i'], ['3', 'A', 'C', 'C'], [⟨['i'], ['3', 'A', 'C', 'C'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "what"), ("allomorph", "short"), ("syntax", "sisters"), ("next", "unfooted"), ("maxPhi", "same")] }

def ex_77a : Datum :=
  { id := "brodkin2026_77a"
    source := ⟨"brodkin-2026", "(77a)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "ínnaᴴ kéttʃuʔᴴ?"
    glossedTokens := [("na", "which"), ("kettʃuʔ", "small")]
    glossedWords := [⟨['n', 'a'], ['w', 'h', 'i', 'c', 'h'], [⟨['n', 'a'], ['w', 'h', 'i', 'c', 'h'], none⟩]⟩, ⟨['k', 'e', 't', 't', 'ʃ', 'u', 'ʔ'], ['s', 'm', 'a', 'l', 'l'], [⟨['k', 'e', 't', 't', 'ʃ', 'u', 'ʔ'], ['s', 'm', 'a', 'l', 'l'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "which"), ("allomorph", "long"), ("syntax", "sisters"), ("next", "footed"), ("maxPhi", "same")] }

def ex_77b : Datum :=
  { id := "brodkin2026_77b"
    source := ⟨"brodkin-2026", "(77b)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "ná kaᴴrámboᴴ?"
    glossedTokens := [("na", "which"), ("karambo", "far")]
    glossedWords := [⟨['n', 'a'], ['w', 'h', 'i', 'c', 'h'], [⟨['n', 'a'], ['w', 'h', 'i', 'c', 'h'], none⟩]⟩, ⟨['k', 'a', 'r', 'a', 'm', 'b', 'o'], ['f', 'a', 'r'], [⟨['k', 'a', 'r', 'a', 'm', 'b', 'o'], ['f', 'a', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "which"), ("allomorph", "short"), ("syntax", "sisters"), ("next", "unfooted"), ("maxPhi", "same")] }

def ex_78a : Datum :=
  { id := "brodkin2026_78a"
    source := ⟨"brodkin-2026", "(78a)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "nalattʃáriᴴ i índiᴴ ɣúruᴴ éᴴ."
    glossedTokens := [("na-lattʃari", "3ERG-throw.at"), ("i", "3ABS"), ("ndi", "this"), ("guru", "teacher"), ("e", "here")]
    glossedWords := [⟨['n', 'a', '-', 'l', 'a', 't', 't', 'ʃ', 'a', 'r', 'i'], ['3', 'E', 'R', 'G', '-', 't', 'h', 'r', 'o', 'w', '.', 'a', 't'], [⟨['n', 'a'], ['3', 'E', 'R', 'G'], none⟩, ⟨['l', 'a', 't', 't', 'ʃ', 'a', 'r', 'i'], ['t', 'h', 'r', 'o', 'w', '.', 'a', 't'], some '-'⟩]⟩, ⟨['i'], ['3', 'A', 'B', 'S'], [⟨['i'], ['3', 'A', 'B', 'S'], none⟩]⟩, ⟨['n', 'd', 'i'], ['t', 'h', 'i', 's'], [⟨['n', 'd', 'i'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['g', 'u', 'r', 'u'], ['t', 'e', 'a', 'c', 'h', 'e', 'r'], [⟨['g', 'u', 'r', 'u'], ['t', 'e', 'a', 'c', 'h', 'e', 'r'], none⟩]⟩, ⟨['e'], ['h', 'e', 'r', 'e'], [⟨['e'], ['h', 'e', 'r', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "this_in_hand"), ("allomorph", "long"), ("syntax", "sisters"), ("next", "footed"), ("maxPhi", "same"), ("clause", "ditransitive")] }

def ex_78b : Datum :=
  { id := "brodkin2026_78b"
    source := ⟨"brodkin-2026", "(78b)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "nalattʃáriᴴ i ndí ɣuᴴrúnnaᴴ éᴴ."
    glossedTokens := [("na-lattʃari", "3ERG-throw.at"), ("i", "3ABS"), ("ndi", "this"), ("guru-na", "teacher-3GEN"), ("e", "here")]
    glossedWords := [⟨['n', 'a', '-', 'l', 'a', 't', 't', 'ʃ', 'a', 'r', 'i'], ['3', 'E', 'R', 'G', '-', 't', 'h', 'r', 'o', 'w', '.', 'a', 't'], [⟨['n', 'a'], ['3', 'E', 'R', 'G'], none⟩, ⟨['l', 'a', 't', 't', 'ʃ', 'a', 'r', 'i'], ['t', 'h', 'r', 'o', 'w', '.', 'a', 't'], some '-'⟩]⟩, ⟨['i'], ['3', 'A', 'B', 'S'], [⟨['i'], ['3', 'A', 'B', 'S'], none⟩]⟩, ⟨['n', 'd', 'i'], ['t', 'h', 'i', 's'], [⟨['n', 'd', 'i'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['g', 'u', 'r', 'u', '-', 'n', 'a'], ['t', 'e', 'a', 'c', 'h', 'e', 'r', '-', '3', 'G', 'E', 'N'], [⟨['g', 'u', 'r', 'u'], ['t', 'e', 'a', 'c', 'h', 'e', 'r'], none⟩, ⟨['n', 'a'], ['3', 'G', 'E', 'N'], some '-'⟩]⟩, ⟨['e'], ['h', 'e', 'r', 'e'], [⟨['e'], ['h', 'e', 'r', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "this_in_hand"), ("allomorph", "short"), ("syntax", "sisters"), ("next", "unfooted"), ("maxPhi", "same"), ("clause", "ditransitive")] }

def ex_83b : Datum :=
  { id := "brodkin2026_83b"
    source := ⟨"brodkin-2026", "(83b)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "néteᴴ i ɹó jaᴴrámmiŋᴴ óᴴ."
    glossedTokens := [("na-itai", "3ERG-look.for"), ("i", "3ABS"), ("do", "that"), ("ʤarammiŋ", "mirror"), ("o", "there")]
    glossedWords := [⟨['n', 'a', '-', 'i', 't', 'a', 'i'], ['3', 'E', 'R', 'G', '-', 'l', 'o', 'o', 'k', '.', 'f', 'o', 'r'], [⟨['n', 'a'], ['3', 'E', 'R', 'G'], none⟩, ⟨['i', 't', 'a', 'i'], ['l', 'o', 'o', 'k', '.', 'f', 'o', 'r'], some '-'⟩]⟩, ⟨['i'], ['3', 'A', 'B', 'S'], [⟨['i'], ['3', 'A', 'B', 'S'], none⟩]⟩, ⟨['d', 'o'], ['t', 'h', 'a', 't'], [⟨['d', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['ʤ', 'a', 'r', 'a', 'm', 'm', 'i', 'ŋ'], ['m', 'i', 'r', 'r', 'o', 'r'], [⟨['ʤ', 'a', 'r', 'a', 'm', 'm', 'i', 'ŋ'], ['m', 'i', 'r', 'r', 'o', 'r'], none⟩]⟩, ⟨['o'], ['t', 'h', 'e', 'r', 'e'], [⟨['o'], ['t', 'h', 'e', 'r', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "that"), ("allomorph", "short"), ("syntax", "sisters"), ("next", "unfooted"), ("maxPhi", "same")] }

def ex_84 : Datum :=
  { id := "brodkin2026_84"
    source := ⟨"brodkin-2026", "(84)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "nálliᴴ i ɹíʔoᴴ dirwambóŋiᴴ óᴴ."
    glossedTokens := [("na-alli", "3ERG-buy"), ("i", "3ABS"), ("do", "that"), ("diruamboŋi", "a.while.ago"), ("o", "there")]
    glossedWords := [⟨['n', 'a', '-', 'a', 'l', 'l', 'i'], ['3', 'E', 'R', 'G', '-', 'b', 'u', 'y'], [⟨['n', 'a'], ['3', 'E', 'R', 'G'], none⟩, ⟨['a', 'l', 'l', 'i'], ['b', 'u', 'y'], some '-'⟩]⟩, ⟨['i'], ['3', 'A', 'B', 'S'], [⟨['i'], ['3', 'A', 'B', 'S'], none⟩]⟩, ⟨['d', 'o'], ['t', 'h', 'a', 't'], [⟨['d', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['d', 'i', 'r', 'u', 'a', 'm', 'b', 'o', 'ŋ', 'i'], ['a', '.', 'w', 'h', 'i', 'l', 'e', '.', 'a', 'g', 'o'], [⟨['d', 'i', 'r', 'u', 'a', 'm', 'b', 'o', 'ŋ', 'i'], ['a', '.', 'w', 'h', 'i', 'l', 'e', '.', 'a', 'g', 'o'], none⟩]⟩, ⟨['o'], ['t', 'h', 'e', 'r', 'e'], [⟨['o'], ['t', 'h', 'e', 'r', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "that"), ("allomorph", "long"), ("syntax", "sisters"), ("next", "unfooted"), ("maxPhi", "different")] }

def ex_86a : Datum :=
  { id := "brodkin2026_86a"
    source := ⟨"brodkin-2026", "(86a)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "natínroᴴ i ɹo ɣuᴴrúnaᴴ óᴴ."
    glossedTokens := [("na-tinro", "3ERG-chase"), ("i", "3ABS"), ("do", "that"), ("guru-na", "teacher-3GEN"), ("o", "there")]
    glossedWords := [⟨['n', 'a', '-', 't', 'i', 'n', 'r', 'o'], ['3', 'E', 'R', 'G', '-', 'c', 'h', 'a', 's', 'e'], [⟨['n', 'a'], ['3', 'E', 'R', 'G'], none⟩, ⟨['t', 'i', 'n', 'r', 'o'], ['c', 'h', 'a', 's', 'e'], some '-'⟩]⟩, ⟨['i'], ['3', 'A', 'B', 'S'], [⟨['i'], ['3', 'A', 'B', 'S'], none⟩]⟩, ⟨['d', 'o'], ['t', 'h', 'a', 't'], [⟨['d', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['g', 'u', 'r', 'u', '-', 'n', 'a'], ['t', 'e', 'a', 'c', 'h', 'e', 'r', '-', '3', 'G', 'E', 'N'], [⟨['g', 'u', 'r', 'u'], ['t', 'e', 'a', 'c', 'h', 'e', 'r'], none⟩, ⟨['n', 'a'], ['3', 'G', 'E', 'N'], some '-'⟩]⟩, ⟨['o'], ['t', 'h', 'e', 'r', 'e'], [⟨['o'], ['t', 'h', 'e', 'r', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "that"), ("allomorph", "short"), ("syntax", "sisters"), ("next", "unfooted"), ("maxPhi", "same")] }

def ex_86b : Datum :=
  { id := "brodkin2026_86b"
    source := ⟨"brodkin-2026", "(86b)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "natínroᴴ i ɹíʔoᴴ gurúnaᴴ ikátʃoʔ óᴴ."
    glossedTokens := [("na-tinro", "3ERG-chase"), ("i", "3ABS"), ("do", "that"), ("guru-na", "teacher-3GEN"), ("ikatʃoʔ", "NAME"), ("o", "there")]
    glossedWords := [⟨['n', 'a', '-', 't', 'i', 'n', 'r', 'o'], ['3', 'E', 'R', 'G', '-', 'c', 'h', 'a', 's', 'e'], [⟨['n', 'a'], ['3', 'E', 'R', 'G'], none⟩, ⟨['t', 'i', 'n', 'r', 'o'], ['c', 'h', 'a', 's', 'e'], some '-'⟩]⟩, ⟨['i'], ['3', 'A', 'B', 'S'], [⟨['i'], ['3', 'A', 'B', 'S'], none⟩]⟩, ⟨['d', 'o'], ['t', 'h', 'a', 't'], [⟨['d', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['g', 'u', 'r', 'u', '-', 'n', 'a'], ['t', 'e', 'a', 'c', 'h', 'e', 'r', '-', '3', 'G', 'E', 'N'], [⟨['g', 'u', 'r', 'u'], ['t', 'e', 'a', 'c', 'h', 'e', 'r'], none⟩, ⟨['n', 'a'], ['3', 'G', 'E', 'N'], some '-'⟩]⟩, ⟨['i', 'k', 'a', 't', 'ʃ', 'o', 'ʔ'], ['N', 'A', 'M', 'E'], [⟨['i', 'k', 'a', 't', 'ʃ', 'o', 'ʔ'], ['N', 'A', 'M', 'E'], none⟩]⟩, ⟨['o'], ['t', 'h', 'e', 'r', 'e'], [⟨['o'], ['t', 'h', 'e', 'r', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "that"), ("allomorph", "long"), ("syntax", "sisters"), ("next", "unfooted"), ("maxPhi", "different")] }

def ex_92 : Datum :=
  { id := "brodkin2026_92"
    source := ⟨"brodkin-2026", "(92)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "ukiriŋaᴴ ĩ ɹó ɣuᴴrúʔuᴴ óᴴ."
    glossedTokens := [("u-kiriŋ-aŋ", "1ERG-send-APPL"), ("i", "3ABS"), ("do", "that"), ("guru-u", "teacher-1GEN"), ("o", "there")]
    glossedWords := [⟨['u', '-', 'k', 'i', 'r', 'i', 'ŋ', '-', 'a', 'ŋ'], ['1', 'E', 'R', 'G', '-', 's', 'e', 'n', 'd', '-', 'A', 'P', 'P', 'L'], [⟨['u'], ['1', 'E', 'R', 'G'], none⟩, ⟨['k', 'i', 'r', 'i', 'ŋ'], ['s', 'e', 'n', 'd'], some '-'⟩, ⟨['a', 'ŋ'], ['A', 'P', 'P', 'L'], some '-'⟩]⟩, ⟨['i'], ['3', 'A', 'B', 'S'], [⟨['i'], ['3', 'A', 'B', 'S'], none⟩]⟩, ⟨['d', 'o'], ['t', 'h', 'a', 't'], [⟨['d', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['g', 'u', 'r', 'u', '-', 'u'], ['t', 'e', 'a', 'c', 'h', 'e', 'r', '-', '1', 'G', 'E', 'N'], [⟨['g', 'u', 'r', 'u'], ['t', 'e', 'a', 'c', 'h', 'e', 'r'], none⟩, ⟨['u'], ['1', 'G', 'E', 'N'], some '-'⟩]⟩, ⟨['o'], ['t', 'h', 'e', 'r', 'e'], [⟨['o'], ['t', 'h', 'e', 'r', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "that"), ("allomorph", "short"), ("syntax", "sisters"), ("next", "unfooted"), ("maxPhi", "same"), ("clause", "ditransitive")] }

def all : List Datum := [ex_33a, ex_33b, ex_36a, ex_36b, ex_40a, ex_40b, ex_41a, ex_41b, ex_42a, ex_42b, ex_56a, ex_56b, ex_76a, ex_76b, ex_77a, ex_77b, ex_78a, ex_78b, ex_83b, ex_84, ex_86a, ex_86b, ex_92]

end Brodkin2026.Examples
