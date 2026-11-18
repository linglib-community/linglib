module

public import Linglib.Data.Examples.Schema

/-!
# `Dolatian2020` — typed example data

Auto-generated from `Linglib/Data/Examples/Dolatian2020.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Dolatian2020.Examples`.
-/

@[expose] public section

namespace Dolatian2020.Examples

def ex_1 : Datum :=
  { id := "dolatian2020_1"
    source := ⟨"dolatian-2020", "(1)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "kórd͡z, kord͡z-avór, kord͡z-avor-nér, kord͡z-avor-nér-ə"
    glossedTokens := [("kórd͡z", "work"), ("kord͡z-avór", "worker"), ("kord͡z-avor-nér", "workers"), ("kord͡z-avor-nér-ə", "with workers")]
    glossedWords := [⟨['k', 'ó', 'r', 'd', '͡', 'z'], ['w', 'o', 'r', 'k'], [⟨['k', 'ó', 'r', 'd', '͡', 'z'], ['w', 'o', 'r', 'k'], none⟩]⟩, ⟨['k', 'o', 'r', 'd', '͡', 'z', '-', 'a', 'v', 'ó', 'r'], ['w', 'o', 'r', 'k', 'e', 'r'], []⟩, ⟨['k', 'o', 'r', 'd', '͡', 'z', '-', 'a', 'v', 'o', 'r', '-', 'n', 'é', 'r'], ['w', 'o', 'r', 'k', 'e', 'r', 's'], []⟩, ⟨['k', 'o', 'r', 'd', '͡', 'z', '-', 'a', 'v', 'o', 'r', '-', 'n', 'é', 'r', '-', 'ə'], ['w', 'i', 't', 'h', ' ', 'w', 'o', 'r', 'k', 'e', 'r', 's'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("dialect", "western"), ("process", "stress")] }

def ex_2 : Datum :=
  { id := "dolatian2020_2"
    source := ⟨"dolatian-2020", "(2)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "hín, hən-utjún; teɣín, teɣn-orág"
    glossedTokens := [("hín", "old"), ("hən-utjún", "oldness"), ("teɣín", "yellow"), ("teɣn-orág", "yellowish")]
    glossedWords := [⟨['h', 'í', 'n'], ['o', 'l', 'd'], [⟨['h', 'í', 'n'], ['o', 'l', 'd'], none⟩]⟩, ⟨['h', 'ə', 'n', '-', 'u', 't', 'j', 'ú', 'n'], ['o', 'l', 'd', 'n', 'e', 's', 's'], []⟩, ⟨['t', 'e', 'ɣ', 'í', 'n'], ['y', 'e', 'l', 'l', 'o', 'w'], [⟨['t', 'e', 'ɣ', 'í', 'n'], ['y', 'e', 'l', 'l', 'o', 'w'], none⟩]⟩, ⟨['t', 'e', 'ɣ', 'n', '-', 'o', 'r', 'á', 'g'], ['y', 'e', 'l', 'l', 'o', 'w', 'i', 's', 'h'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "derivational"), ("reduction", "both")] }

def ex_3b : Datum :=
  { id := "dolatian2020_3b"
    source := ⟨"dolatian-2020", "(3b)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "had͡ʒáχ, had͡ʒaχ-él; darpér, darper-él"
    glossedTokens := [("had͡ʒáχ", "frequent"), ("had͡ʒaχ-él", "to frequent"), ("darpér", "different"), ("darper-él", "to distinguish")]
    glossedWords := [⟨['h', 'a', 'd', '͡', 'ʒ', 'á', 'χ'], ['f', 'r', 'e', 'q', 'u', 'e', 'n', 't'], [⟨['h', 'a', 'd', '͡', 'ʒ', 'á', 'χ'], ['f', 'r', 'e', 'q', 'u', 'e', 'n', 't'], none⟩]⟩, ⟨['h', 'a', 'd', '͡', 'ʒ', 'a', 'χ', '-', 'é', 'l'], ['t', 'o', ' ', 'f', 'r', 'e', 'q', 'u', 'e', 'n', 't'], []⟩, ⟨['d', 'a', 'r', 'p', 'é', 'r'], ['d', 'i', 'f', 'f', 'e', 'r', 'e', 'n', 't'], [⟨['d', 'a', 'r', 'p', 'é', 'r'], ['d', 'i', 'f', 'f', 'e', 'r', 'e', 'n', 't'], none⟩]⟩, ⟨['d', 'a', 'r', 'p', 'e', 'r', '-', 'é', 'l'], ['t', 'o', ' ', 'd', 'i', 's', 't', 'i', 'n', 'g', 'u', 'i', 's', 'h'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("had͡ʒχ-él", .ungrammatical), ("darpr-él", .ungrammatical)]
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "derivational"), ("reduction", "none")] }

def ex_4 : Datum :=
  { id := "dolatian2020_4"
    source := ⟨"dolatian-2020", "(4)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "amusín, amusn-utjún; irigún, irign-ajín"
    glossedTokens := [("amusín", "husband"), ("amusn-utjún", "marriage"), ("irigún", "evening"), ("irign-ajín", "evening (adj.)")]
    glossedWords := [⟨['a', 'm', 'u', 's', 'í', 'n'], ['h', 'u', 's', 'b', 'a', 'n', 'd'], [⟨['a', 'm', 'u', 's', 'í', 'n'], ['h', 'u', 's', 'b', 'a', 'n', 'd'], none⟩]⟩, ⟨['a', 'm', 'u', 's', 'n', '-', 'u', 't', 'j', 'ú', 'n'], ['m', 'a', 'r', 'r', 'i', 'a', 'g', 'e'], []⟩, ⟨['i', 'r', 'i', 'g', 'ú', 'n'], ['e', 'v', 'e', 'n', 'i', 'n', 'g'], [⟨['i', 'r', 'i', 'g', 'ú', 'n'], ['e', 'v', 'e', 'n', 'i', 'n', 'g'], none⟩]⟩, ⟨['i', 'r', 'i', 'g', 'n', '-', 'a', 'j', 'í', 'n'], ['e', 'v', 'e', 'n', 'i', 'n', 'g', ' ', '(', 'a', 'd', 'j', '.', ')'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("amsin-utjún", .ungrammatical), ("irgun-ajín", .ungrammatical)]
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "derivational"), ("reduction", "deletion")] }

def ex_5a : Datum :=
  { id := "dolatian2020_5a"
    source := ⟨"dolatian-2020", "(5a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "d͡zín, d͡zən-únt, d͡zən-ənt-agán"
    glossedTokens := [("d͡zín", "birth"), ("d͡zən-únt", "birth"), ("d͡zən-ənt-agán", "generative")]
    glossedWords := [⟨['d', '͡', 'z', 'í', 'n'], ['b', 'i', 'r', 't', 'h'], [⟨['d', '͡', 'z', 'í', 'n'], ['b', 'i', 'r', 't', 'h'], none⟩]⟩, ⟨['d', '͡', 'z', 'ə', 'n', '-', 'ú', 'n', 't'], ['b', 'i', 'r', 't', 'h'], []⟩, ⟨['d', '͡', 'z', 'ə', 'n', '-', 'ə', 'n', 't', '-', 'a', 'g', 'á', 'n'], ['g', 'e', 'n', 'e', 'r', 'a', 't', 'i', 'v', 'e'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "derivational"), ("reduction", "schwa")] }

def ex_5c : Datum :=
  { id := "dolatian2020_5c"
    source := ⟨"dolatian-2020", "(5c)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "kír, kər-ít͡ʃ, dúp, kər-t͡ʃ-a-dup"
    glossedTokens := [("kír", "handwriting"), ("kər-ít͡ʃ", "pen"), ("dúp", "box"), ("kər-t͡ʃ-a-dup", "pencil-box")]
    glossedWords := [⟨['k', 'í', 'r'], ['h', 'a', 'n', 'd', 'w', 'r', 'i', 't', 'i', 'n', 'g'], [⟨['k', 'í', 'r'], ['h', 'a', 'n', 'd', 'w', 'r', 'i', 't', 'i', 'n', 'g'], none⟩]⟩, ⟨['k', 'ə', 'r', '-', 'í', 't', '͡', 'ʃ'], ['p', 'e', 'n'], []⟩, ⟨['d', 'ú', 'p'], ['b', 'o', 'x'], [⟨['d', 'ú', 'p'], ['b', 'o', 'x'], none⟩]⟩, ⟨['k', 'ə', 'r', '-', 't', '͡', 'ʃ', '-', 'a', '-', 'd', 'u', 'p'], ['p', 'e', 'n', 'c', 'i', 'l', '-', 'b', 'o', 'x'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "compound"), ("reduction", "both")] }

def ex_7a : Datum :=
  { id := "dolatian2020_7a"
    source := ⟨"dolatian-2020", "(7a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "amusín, amusn-utjún, amusin-óv"
    glossedTokens := [("amusín", "husband"), ("amusn-utjún", "marriage"), ("amusin-óv", "husband-INST")]
    glossedWords := [⟨['a', 'm', 'u', 's', 'í', 'n'], ['h', 'u', 's', 'b', 'a', 'n', 'd'], [⟨['a', 'm', 'u', 's', 'í', 'n'], ['h', 'u', 's', 'b', 'a', 'n', 'd'], none⟩]⟩, ⟨['a', 'm', 'u', 's', 'n', '-', 'u', 't', 'j', 'ú', 'n'], ['m', 'a', 'r', 'r', 'i', 'a', 'g', 'e'], []⟩, ⟨['a', 'm', 'u', 's', 'i', 'n', '-', 'ó', 'v'], ['h', 'u', 's', 'b', 'a', 'n', 'd', '-', 'I', 'N', 'S', 'T'], [⟨['a', 'm', 'u', 's', 'i', 'n'], ['h', 'u', 's', 'b', 'a', 'n', 'd'], none⟩, ⟨['ó', 'v'], ['I', 'N', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "vInflection"), ("reduction", "none")] }

def ex_7b : Datum :=
  { id := "dolatian2020_7b"
    source := ⟨"dolatian-2020", "(7b)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "zərújt͡s, zərut͡s-él, zərujt͡s-óv"
    glossedTokens := [("zərújt͡s", "conversation"), ("zərut͡s-él", "to converse"), ("zərujt͡s-óv", "conversation-INST")]
    glossedWords := [⟨['z', 'ə', 'r', 'ú', 'j', 't', '͡', 's'], ['c', 'o', 'n', 'v', 'e', 'r', 's', 'a', 't', 'i', 'o', 'n'], [⟨['z', 'ə', 'r', 'ú', 'j', 't', '͡', 's'], ['c', 'o', 'n', 'v', 'e', 'r', 's', 'a', 't', 'i', 'o', 'n'], none⟩]⟩, ⟨['z', 'ə', 'r', 'u', 't', '͡', 's', '-', 'é', 'l'], ['t', 'o', ' ', 'c', 'o', 'n', 'v', 'e', 'r', 's', 'e'], []⟩, ⟨['z', 'ə', 'r', 'u', 'j', 't', '͡', 's', '-', 'ó', 'v'], ['c', 'o', 'n', 'v', 'e', 'r', 's', 'a', 't', 'i', 'o', 'n', '-', 'I', 'N', 'S', 'T'], [⟨['z', 'ə', 'r', 'u', 'j', 't', '͡', 's'], ['c', 'o', 'n', 'v', 'e', 'r', 's', 'a', 't', 'i', 'o', 'n'], none⟩, ⟨['ó', 'v'], ['I', 'N', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "vInflection"), ("reduction", "diphthong")] }

def ex_10c : Datum :=
  { id := "dolatian2020_10c"
    source := ⟨"dolatian-2020", "(10c)"⟩
    reportedIn := none
    language := "nucl1235"
    primaryText := "amusn-óv"
    glossedTokens := [("amusn-óv", "husband-INST")]
    glossedWords := [⟨['a', 'm', 'u', 's', 'n', '-', 'ó', 'v'], ['h', 'u', 's', 'b', 'a', 'n', 'd', '-', 'I', 'N', 'S', 'T'], [⟨['a', 'm', 'u', 's', 'n'], ['h', 'u', 's', 'b', 'a', 'n', 'd'], none⟩, ⟨['ó', 'v'], ['I', 'N', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("dialect", "eastern"), ("suffix", "vInflection"), ("reduction", "deletion")] }

def ex_10e : Datum :=
  { id := "dolatian2020_10e"
    source := ⟨"dolatian-2020", "(10e)"⟩
    reportedIn := none
    language := "nucl1235"
    primaryText := "amusin-nér"
    glossedTokens := [("amusin-nér", "husband-PL")]
    glossedWords := [⟨['a', 'm', 'u', 's', 'i', 'n', '-', 'n', 'é', 'r'], ['h', 'u', 's', 'b', 'a', 'n', 'd', '-', 'P', 'L'], [⟨['a', 'm', 'u', 's', 'i', 'n'], ['h', 'u', 's', 'b', 'a', 'n', 'd'], none⟩, ⟨['n', 'é', 'r'], ['P', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("dialect", "eastern"), ("suffix", "cInflection"), ("reduction", "none")] }

def ex_12a : Datum :=
  { id := "dolatian2020_12a"
    source := ⟨"dolatian-2020", "(12a)"⟩
    reportedIn := none
    language := "nucl1235"
    primaryText := "zərújt͡sʰ, zərut͡sʰ-él, zərújt͡sʰ-óv"
    glossedTokens := [("zərújt͡sʰ", "conversation"), ("zərut͡sʰ-él", "to converse"), ("zərújt͡sʰ-óv", "conversation-INST")]
    glossedWords := [⟨['z', 'ə', 'r', 'ú', 'j', 't', '͡', 's', 'ʰ'], ['c', 'o', 'n', 'v', 'e', 'r', 's', 'a', 't', 'i', 'o', 'n'], [⟨['z', 'ə', 'r', 'ú', 'j', 't', '͡', 's', 'ʰ'], ['c', 'o', 'n', 'v', 'e', 'r', 's', 'a', 't', 'i', 'o', 'n'], none⟩]⟩, ⟨['z', 'ə', 'r', 'u', 't', '͡', 's', 'ʰ', '-', 'é', 'l'], ['t', 'o', ' ', 'c', 'o', 'n', 'v', 'e', 'r', 's', 'e'], []⟩, ⟨['z', 'ə', 'r', 'ú', 'j', 't', '͡', 's', 'ʰ', '-', 'ó', 'v'], ['c', 'o', 'n', 'v', 'e', 'r', 's', 'a', 't', 'i', 'o', 'n', '-', 'I', 'N', 'S', 'T'], [⟨['z', 'ə', 'r', 'ú', 'j', 't', '͡', 's', 'ʰ'], ['c', 'o', 'n', 'v', 'e', 'r', 's', 'a', 't', 'i', 'o', 'n'], none⟩, ⟨['ó', 'v'], ['I', 'N', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("dialect", "eastern"), ("suffix", "vInflection"), ("reduction", "diphthong")] }

def ex_41 : Datum :=
  { id := "dolatian2020_41"
    source := ⟨"dolatian-2020", "(41)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "darí, darí-k; kaxtní, kaxtní-k; parí, parí-k"
    glossedTokens := [("darí", "year"), ("darí-k", "age"), ("kaxtní", "secret (adj)"), ("kaxtní-k", "secret (n)"), ("parí", "good"), ("parí-k", "charity")]
    glossedWords := [⟨['d', 'a', 'r', 'í'], ['y', 'e', 'a', 'r'], [⟨['d', 'a', 'r', 'í'], ['y', 'e', 'a', 'r'], none⟩]⟩, ⟨['d', 'a', 'r', 'í', '-', 'k'], ['a', 'g', 'e'], []⟩, ⟨['k', 'a', 'x', 't', 'n', 'í'], ['s', 'e', 'c', 'r', 'e', 't', ' ', '(', 'a', 'd', 'j', ')'], [⟨['k', 'a', 'x', 't', 'n', 'í'], ['s', 'e', 'c', 'r', 'e', 't', ' ', '(', 'a', 'd', 'j', ')'], none⟩]⟩, ⟨['k', 'a', 'x', 't', 'n', 'í', '-', 'k'], ['s', 'e', 'c', 'r', 'e', 't', ' ', '(', 'n', ')'], []⟩, ⟨['p', 'a', 'r', 'í'], ['g', 'o', 'o', 'd'], [⟨['p', 'a', 'r', 'í'], ['g', 'o', 'o', 'd'], none⟩]⟩, ⟨['p', 'a', 'r', 'í', '-', 'k'], ['c', 'h', 'a', 'r', 'i', 't', 'y'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "derivational"), ("reduction", "none")] }

def ex_42 : Datum :=
  { id := "dolatian2020_42"
    source := ⟨"dolatian-2020", "(42)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "amusín, amusn-utjún; aznív, aznəv-utjún"
    glossedTokens := [("amusín", "husband"), ("amusn-utjún", "marriage"), ("aznív", "honest"), ("aznəv-utjún", "honesty")]
    glossedWords := [⟨['a', 'm', 'u', 's', 'í', 'n'], ['h', 'u', 's', 'b', 'a', 'n', 'd'], [⟨['a', 'm', 'u', 's', 'í', 'n'], ['h', 'u', 's', 'b', 'a', 'n', 'd'], none⟩]⟩, ⟨['a', 'm', 'u', 's', 'n', '-', 'u', 't', 'j', 'ú', 'n'], ['m', 'a', 'r', 'r', 'i', 'a', 'g', 'e'], []⟩, ⟨['a', 'z', 'n', 'í', 'v'], ['h', 'o', 'n', 'e', 's', 't'], [⟨['a', 'z', 'n', 'í', 'v'], ['h', 'o', 'n', 'e', 's', 't'], none⟩]⟩, ⟨['a', 'z', 'n', 'ə', 'v', '-', 'u', 't', 'j', 'ú', 'n'], ['h', 'o', 'n', 'e', 's', 't', 'y'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("amusən-utjún", .ungrammatical), ("aznv-utjún", .ungrammatical)]
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "derivational"), ("reduction", "both")] }

def ex_47a : Datum :=
  { id := "dolatian2020_47a"
    source := ⟨"dolatian-2020", "(47a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "hivánt, hivant-anál; hankíst, hankəst-anál; amusín, amusn-anál"
    glossedTokens := [("hivánt", "sick"), ("hivant-anál", "to become sick"), ("hankíst", "relaxed"), ("hankəst-anál", "to relax"), ("amusín", "husband"), ("amusn-anál", "to marry")]
    glossedWords := [⟨['h', 'i', 'v', 'á', 'n', 't'], ['s', 'i', 'c', 'k'], [⟨['h', 'i', 'v', 'á', 'n', 't'], ['s', 'i', 'c', 'k'], none⟩]⟩, ⟨['h', 'i', 'v', 'a', 'n', 't', '-', 'a', 'n', 'á', 'l'], ['t', 'o', ' ', 'b', 'e', 'c', 'o', 'm', 'e', ' ', 's', 'i', 'c', 'k'], []⟩, ⟨['h', 'a', 'n', 'k', 'í', 's', 't'], ['r', 'e', 'l', 'a', 'x', 'e', 'd'], [⟨['h', 'a', 'n', 'k', 'í', 's', 't'], ['r', 'e', 'l', 'a', 'x', 'e', 'd'], none⟩]⟩, ⟨['h', 'a', 'n', 'k', 'ə', 's', 't', '-', 'a', 'n', 'á', 'l'], ['t', 'o', ' ', 'r', 'e', 'l', 'a', 'x'], []⟩, ⟨['a', 'm', 'u', 's', 'í', 'n'], ['h', 'u', 's', 'b', 'a', 'n', 'd'], [⟨['a', 'm', 'u', 's', 'í', 'n'], ['h', 'u', 's', 'b', 'a', 'n', 'd'], none⟩]⟩, ⟨['a', 'm', 'u', 's', 'n', '-', 'a', 'n', 'á', 'l'], ['t', 'o', ' ', 'm', 'a', 'r', 'r', 'y'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("həvant-anál", .ungrammatical), ("hankist-anál", .ungrammatical), ("amsin-anál", .ungrammatical)]
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "derivational"), ("reduction", "both")] }

def ex_48a : Datum :=
  { id := "dolatian2020_48a"
    source := ⟨"dolatian-2020", "(48a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "ázk, azk-ajín, azk-ajn-agán"
    glossedTokens := [("ázk", "nation"), ("azk-ajín", "national"), ("azk-ajn-agán", "nationalist")]
    glossedWords := [⟨['á', 'z', 'k'], ['n', 'a', 't', 'i', 'o', 'n'], [⟨['á', 'z', 'k'], ['n', 'a', 't', 'i', 'o', 'n'], none⟩]⟩, ⟨['a', 'z', 'k', '-', 'a', 'j', 'í', 'n'], ['n', 'a', 't', 'i', 'o', 'n', 'a', 'l'], []⟩, ⟨['a', 'z', 'k', '-', 'a', 'j', 'n', '-', 'a', 'g', 'á', 'n'], ['n', 'a', 't', 'i', 'o', 'n', 'a', 'l', 'i', 's', 't'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "derivational"), ("reduction", "deletion")] }

def ex_65 : Datum :=
  { id := "dolatian2020_65"
    source := ⟨"dolatian-2020", "(65)"⟩
    reportedIn := none
    language := "nucl1235"
    primaryText := "tʰúxtʰ, tʰəx.tʰ-í, tʰəx.tʰ-ít͡sʰ, tʰəx.tʰ-óv, tʰəx.tʰ-úm; amusín, amus.n-ú, amus.n-ít͡sʰ, amus.n-óv, amus.n-úm"
    glossedTokens := [("tʰúxtʰ", "paper"), ("tʰəx.tʰ-í", "paper-DAT/GEN"), ("tʰəx.tʰ-óv", "paper-INST"), ("amusín", "husband"), ("amus.n-ú", "husband-DAT/GEN"), ("amus.n-óv", "husband-INST")]
    glossedWords := [⟨['t', 'ʰ', 'ú', 'x', 't', 'ʰ'], ['p', 'a', 'p', 'e', 'r'], [⟨['t', 'ʰ', 'ú', 'x', 't', 'ʰ'], ['p', 'a', 'p', 'e', 'r'], none⟩]⟩, ⟨['t', 'ʰ', 'ə', 'x', '.', 't', 'ʰ', '-', 'í'], ['p', 'a', 'p', 'e', 'r', '-', 'D', 'A', 'T', '/', 'G', 'E', 'N'], [⟨['t', 'ʰ', 'ə', 'x', 't', 'ʰ'], ['p', 'a', 'p', 'e', 'r'], none⟩, ⟨['í'], ['D', 'A', 'T', '/', 'G', 'E', 'N'], some '-'⟩]⟩, ⟨['t', 'ʰ', 'ə', 'x', '.', 't', 'ʰ', '-', 'ó', 'v'], ['p', 'a', 'p', 'e', 'r', '-', 'I', 'N', 'S', 'T'], [⟨['t', 'ʰ', 'ə', 'x', 't', 'ʰ'], ['p', 'a', 'p', 'e', 'r'], none⟩, ⟨['ó', 'v'], ['I', 'N', 'S', 'T'], some '-'⟩]⟩, ⟨['a', 'm', 'u', 's', 'í', 'n'], ['h', 'u', 's', 'b', 'a', 'n', 'd'], [⟨['a', 'm', 'u', 's', 'í', 'n'], ['h', 'u', 's', 'b', 'a', 'n', 'd'], none⟩]⟩, ⟨['a', 'm', 'u', 's', '.', 'n', '-', 'ú'], ['h', 'u', 's', 'b', 'a', 'n', 'd', '-', 'D', 'A', 'T', '/', 'G', 'E', 'N'], [⟨['a', 'm', 'u', 's', 'n'], ['h', 'u', 's', 'b', 'a', 'n', 'd'], none⟩, ⟨['ú'], ['D', 'A', 'T', '/', 'G', 'E', 'N'], some '-'⟩]⟩, ⟨['a', 'm', 'u', 's', '.', 'n', '-', 'ó', 'v'], ['h', 'u', 's', 'b', 'a', 'n', 'd', '-', 'I', 'N', 'S', 'T'], [⟨['a', 'm', 'u', 's', 'n'], ['h', 'u', 's', 'b', 'a', 'n', 'd'], none⟩, ⟨['ó', 'v'], ['I', 'N', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("dialect", "eastern"), ("suffix", "vInflection"), ("reduction", "both")] }

def ex_66 : Datum :=
  { id := "dolatian2020_66"
    source := ⟨"dolatian-2020", "(66)"⟩
    reportedIn := none
    language := "nucl1235"
    primaryText := "tʰəx.tʰ-ér, tʰəx.tʰ-er-óv; amusin.-nér, amusin.-ner-óv"
    glossedTokens := [("tʰəx.tʰ-ér", "paper-PL"), ("tʰəx.tʰ-er-óv", "paper-PL-INST"), ("amusin.-nér", "husband-PL"), ("amusin.-ner-óv", "husband-PL-INST")]
    glossedWords := [⟨['t', 'ʰ', 'ə', 'x', '.', 't', 'ʰ', '-', 'é', 'r'], ['p', 'a', 'p', 'e', 'r', '-', 'P', 'L'], [⟨['t', 'ʰ', 'ə', 'x', 't', 'ʰ'], ['p', 'a', 'p', 'e', 'r'], none⟩, ⟨['é', 'r'], ['P', 'L'], some '-'⟩]⟩, ⟨['t', 'ʰ', 'ə', 'x', '.', 't', 'ʰ', '-', 'e', 'r', '-', 'ó', 'v'], ['p', 'a', 'p', 'e', 'r', '-', 'P', 'L', '-', 'I', 'N', 'S', 'T'], [⟨['t', 'ʰ', 'ə', 'x', 't', 'ʰ'], ['p', 'a', 'p', 'e', 'r'], none⟩, ⟨['e', 'r'], ['P', 'L'], some '-'⟩, ⟨['ó', 'v'], ['I', 'N', 'S', 'T'], some '-'⟩]⟩, ⟨['a', 'm', 'u', 's', 'i', 'n', '.', '-', 'n', 'é', 'r'], ['h', 'u', 's', 'b', 'a', 'n', 'd', '-', 'P', 'L'], [⟨['a', 'm', 'u', 's', 'i', 'n'], ['h', 'u', 's', 'b', 'a', 'n', 'd'], none⟩, ⟨['n', 'é', 'r'], ['P', 'L'], some '-'⟩]⟩, ⟨['a', 'm', 'u', 's', 'i', 'n', '.', '-', 'n', 'e', 'r', '-', 'ó', 'v'], ['h', 'u', 's', 'b', 'a', 'n', 'd', '-', 'P', 'L', '-', 'I', 'N', 'S', 'T'], [⟨['a', 'm', 'u', 's', 'i', 'n'], ['h', 'u', 's', 'b', 'a', 'n', 'd'], none⟩, ⟨['n', 'e', 'r'], ['P', 'L'], some '-'⟩, ⟨['ó', 'v'], ['I', 'N', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("dialect", "eastern"), ("suffix", "plural"), ("reduction", "both")] }

def ex_72 : Datum :=
  { id := "dolatian2020_72"
    source := ⟨"dolatian-2020", "(72)"⟩
    reportedIn := none
    language := "nucl1235"
    primaryText := "manúk, mank-akán, mank-án, manuk-í; lúrd͡ʒ, lərd͡ʒ-anál, lurd͡ʒ-í; fílm, film-ajín, film-ér"
    glossedTokens := [("manúk", "child"), ("mank-akán", "childish"), ("mank-án", "child-GEN (irreg.)"), ("manuk-í", "child-GEN (reg.)"), ("lúrd͡ʒ", "serious"), ("lərd͡ʒ-anál", "to get serious"), ("lurd͡ʒ-í", "serious-GEN"), ("fílm", "film"), ("film-ajín", "cinematic"), ("film-ér", "film-PL")]
    glossedWords := [⟨['m', 'a', 'n', 'ú', 'k'], ['c', 'h', 'i', 'l', 'd'], [⟨['m', 'a', 'n', 'ú', 'k'], ['c', 'h', 'i', 'l', 'd'], none⟩]⟩, ⟨['m', 'a', 'n', 'k', '-', 'a', 'k', 'á', 'n'], ['c', 'h', 'i', 'l', 'd', 'i', 's', 'h'], []⟩, ⟨['m', 'a', 'n', 'k', '-', 'á', 'n'], ['c', 'h', 'i', 'l', 'd', '-', 'G', 'E', 'N', ' ', '(', 'i', 'r', 'r', 'e', 'g', '.', ')'], [⟨['m', 'a', 'n', 'k'], ['c', 'h', 'i', 'l', 'd'], none⟩, ⟨['á', 'n'], ['G', 'E', 'N', ' ', '(', 'i', 'r', 'r', 'e', 'g', '.', ')'], some '-'⟩]⟩, ⟨['m', 'a', 'n', 'u', 'k', '-', 'í'], ['c', 'h', 'i', 'l', 'd', '-', 'G', 'E', 'N', ' ', '(', 'r', 'e', 'g', '.', ')'], [⟨['m', 'a', 'n', 'u', 'k'], ['c', 'h', 'i', 'l', 'd'], none⟩, ⟨['í'], ['G', 'E', 'N', ' ', '(', 'r', 'e', 'g', '.', ')'], some '-'⟩]⟩, ⟨['l', 'ú', 'r', 'd', '͡', 'ʒ'], ['s', 'e', 'r', 'i', 'o', 'u', 's'], [⟨['l', 'ú', 'r', 'd', '͡', 'ʒ'], ['s', 'e', 'r', 'i', 'o', 'u', 's'], none⟩]⟩, ⟨['l', 'ə', 'r', 'd', '͡', 'ʒ', '-', 'a', 'n', 'á', 'l'], ['t', 'o', ' ', 'g', 'e', 't', ' ', 's', 'e', 'r', 'i', 'o', 'u', 's'], []⟩, ⟨['l', 'u', 'r', 'd', '͡', 'ʒ', '-', 'í'], ['s', 'e', 'r', 'i', 'o', 'u', 's', '-', 'G', 'E', 'N'], [⟨['l', 'u', 'r', 'd', '͡', 'ʒ'], ['s', 'e', 'r', 'i', 'o', 'u', 's'], none⟩, ⟨['í'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['f', 'í', 'l', 'm'], ['f', 'i', 'l', 'm'], [⟨['f', 'í', 'l', 'm'], ['f', 'i', 'l', 'm'], none⟩]⟩, ⟨['f', 'i', 'l', 'm', '-', 'a', 'j', 'í', 'n'], ['c', 'i', 'n', 'e', 'm', 'a', 't', 'i', 'c'], []⟩, ⟨['f', 'i', 'l', 'm', '-', 'é', 'r'], ['f', 'i', 'l', 'm', '-', 'P', 'L'], [⟨['f', 'i', 'l', 'm'], ['f', 'i', 'l', 'm'], none⟩, ⟨['é', 'r'], ['P', 'L'], some '-'⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("dialect", "eastern"), ("suffix", "vInflection"), ("reduction", "none")] }

def all : List Datum := [ex_1, ex_2, ex_3b, ex_4, ex_5a, ex_5c, ex_7a, ex_7b, ex_10c, ex_10e, ex_12a, ex_41, ex_42, ex_47a, ex_48a, ex_65, ex_66, ex_72]

end Dolatian2020.Examples
