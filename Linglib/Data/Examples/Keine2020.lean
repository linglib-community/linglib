module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Keine2020` — typed example data

Auto-generated from `Linglib/Data/Examples/Keine2020.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Keine2020.Examples`.
-/

@[expose] public section

namespace Keine2020.Examples

def ex_56 : Datum :=
  { id := "keine2020_56"
    source := ⟨"keine-2020", "(56)"⟩
    reportedIn := none
    method := some .elicitation
    language := "hind1269"
    primaryText := "laṛkõ-ne roṭii khaa-nii caah-ii"
    glossedTokens := [("laṛkõ-ne", "boys-ERG"), ("roṭii", "bread.F"), ("khaa-nii", "eat-INF.F.SG"), ("caah-ii", "want-PFV.F.SG")]
    glossedWords := [⟨['l', 'a', 'ṛ', 'k', 'õ', '-', 'n', 'e'], ['b', 'o', 'y', 's', '-', 'E', 'R', 'G'], [⟨['l', 'a', 'ṛ', 'k', 'õ'], ['b', 'o', 'y', 's'], none⟩, ⟨['n', 'e'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['r', 'o', 'ṭ', 'i', 'i'], ['b', 'r', 'e', 'a', 'd', '.', 'F'], [⟨['r', 'o', 'ṭ', 'i', 'i'], ['b', 'r', 'e', 'a', 'd', '.', 'F'], none⟩]⟩, ⟨['k', 'h', 'a', 'a', '-', 'n', 'i', 'i'], ['e', 'a', 't', '-', 'I', 'N', 'F', '.', 'F', '.', 'S', 'G'], [⟨['k', 'h', 'a', 'a'], ['e', 'a', 't'], none⟩, ⟨['n', 'i', 'i'], ['I', 'N', 'F', '.', 'F', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['c', 'a', 'a', 'h', '-', 'i', 'i'], ['w', 'a', 'n', 't', '-', 'P', 'F', 'V', '.', 'F', '.', 'S', 'G'], [⟨['c', 'a', 'a', 'h'], ['w', 'a', 'n', 't'], none⟩, ⟨['i', 'i'], ['P', 'F', 'V', '.', 'F', '.', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "infinitive"), ("dependency", "lda")] }

def ex_57 : Datum :=
  { id := "keine2020_57"
    source := ⟨"keine-2020", "(57)"⟩
    reportedIn := none
    method := some .elicitation
    language := "hind1269"
    primaryText := "laṛkõ-ne roṭii khaa-naa caah-aa"
    glossedTokens := [("laṛkõ-ne", "boys-ERG"), ("roṭii", "bread.F"), ("khaa-naa", "eat-INF.M.SG"), ("caah-aa", "want-PFV.M.SG")]
    glossedWords := [⟨['l', 'a', 'ṛ', 'k', 'õ', '-', 'n', 'e'], ['b', 'o', 'y', 's', '-', 'E', 'R', 'G'], [⟨['l', 'a', 'ṛ', 'k', 'õ'], ['b', 'o', 'y', 's'], none⟩, ⟨['n', 'e'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['r', 'o', 'ṭ', 'i', 'i'], ['b', 'r', 'e', 'a', 'd', '.', 'F'], [⟨['r', 'o', 'ṭ', 'i', 'i'], ['b', 'r', 'e', 'a', 'd', '.', 'F'], none⟩]⟩, ⟨['k', 'h', 'a', 'a', '-', 'n', 'a', 'a'], ['e', 'a', 't', '-', 'I', 'N', 'F', '.', 'M', '.', 'S', 'G'], [⟨['k', 'h', 'a', 'a'], ['e', 'a', 't'], none⟩, ⟨['n', 'a', 'a'], ['I', 'N', 'F', '.', 'M', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['c', 'a', 'a', 'h', '-', 'a', 'a'], ['w', 'a', 'n', 't', '-', 'P', 'F', 'V', '.', 'M', '.', 'S', 'G'], [⟨['c', 'a', 'a', 'h'], ['w', 'a', 'n', 't'], none⟩, ⟨['a', 'a'], ['P', 'F', 'V', '.', 'M', '.', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "infinitive"), ("dependency", "defaultAgreement")] }

def ex_71_default : Datum :=
  { id := "keine2020_71_default"
    source := ⟨"keine-2020", "(71)"⟩
    reportedIn := none
    method := some .elicitation
    language := "hind1269"
    primaryText := "laṛkõ-ne soc-aa ki monaa-ne kitaab paṛh-ii thii"
    glossedTokens := [("laṛkõ-ne", "boys-ERG"), ("soc-aa", "think-PFV.M.SG"), ("ki", "that"), ("monaa-ne", "Mona-ERG"), ("kitaab", "book.F"), ("paṛh-ii", "read-PFV.F.SG"), ("thii", "be.PST.F.SG")]
    glossedWords := [⟨['l', 'a', 'ṛ', 'k', 'õ', '-', 'n', 'e'], ['b', 'o', 'y', 's', '-', 'E', 'R', 'G'], [⟨['l', 'a', 'ṛ', 'k', 'õ'], ['b', 'o', 'y', 's'], none⟩, ⟨['n', 'e'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['s', 'o', 'c', '-', 'a', 'a'], ['t', 'h', 'i', 'n', 'k', '-', 'P', 'F', 'V', '.', 'M', '.', 'S', 'G'], [⟨['s', 'o', 'c'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['a', 'a'], ['P', 'F', 'V', '.', 'M', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['k', 'i'], ['t', 'h', 'a', 't'], [⟨['k', 'i'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['m', 'o', 'n', 'a', 'a', '-', 'n', 'e'], ['M', 'o', 'n', 'a', '-', 'E', 'R', 'G'], [⟨['m', 'o', 'n', 'a', 'a'], ['M', 'o', 'n', 'a'], none⟩, ⟨['n', 'e'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['k', 'i', 't', 'a', 'a', 'b'], ['b', 'o', 'o', 'k', '.', 'F'], [⟨['k', 'i', 't', 'a', 'a', 'b'], ['b', 'o', 'o', 'k', '.', 'F'], none⟩]⟩, ⟨['p', 'a', 'ṛ', 'h', '-', 'i', 'i'], ['r', 'e', 'a', 'd', '-', 'P', 'F', 'V', '.', 'F', '.', 'S', 'G'], [⟨['p', 'a', 'ṛ', 'h'], ['r', 'e', 'a', 'd'], none⟩, ⟨['i', 'i'], ['P', 'F', 'V', '.', 'F', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['t', 'h', 'i', 'i'], ['b', 'e', '.', 'P', 'S', 'T', '.', 'F', '.', 'S', 'G'], [⟨['t', 'h', 'i', 'i'], ['b', 'e', '.', 'P', 'S', 'T', '.', 'F', '.', 'S', 'G'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "finite"), ("dependency", "defaultAgreement")] }

def ex_71_lda : Datum :=
  { id := "keine2020_71_lda"
    source := ⟨"keine-2020", "(71)"⟩
    reportedIn := none
    method := some .elicitation
    language := "hind1269"
    primaryText := "laṛkõ-ne soc-ii ki monaa-ne kitaab paṛh-ii thii"
    glossedTokens := [("laṛkõ-ne", "boys-ERG"), ("soc-ii", "think-PFV.F.SG"), ("ki", "that"), ("monaa-ne", "Mona-ERG"), ("kitaab", "book.F"), ("paṛh-ii", "read-PFV.F.SG"), ("thii", "be.PST.F.SG")]
    glossedWords := [⟨['l', 'a', 'ṛ', 'k', 'õ', '-', 'n', 'e'], ['b', 'o', 'y', 's', '-', 'E', 'R', 'G'], [⟨['l', 'a', 'ṛ', 'k', 'õ'], ['b', 'o', 'y', 's'], none⟩, ⟨['n', 'e'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['s', 'o', 'c', '-', 'i', 'i'], ['t', 'h', 'i', 'n', 'k', '-', 'P', 'F', 'V', '.', 'F', '.', 'S', 'G'], [⟨['s', 'o', 'c'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['i', 'i'], ['P', 'F', 'V', '.', 'F', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['k', 'i'], ['t', 'h', 'a', 't'], [⟨['k', 'i'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['m', 'o', 'n', 'a', 'a', '-', 'n', 'e'], ['M', 'o', 'n', 'a', '-', 'E', 'R', 'G'], [⟨['m', 'o', 'n', 'a', 'a'], ['M', 'o', 'n', 'a'], none⟩, ⟨['n', 'e'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['k', 'i', 't', 'a', 'a', 'b'], ['b', 'o', 'o', 'k', '.', 'F'], [⟨['k', 'i', 't', 'a', 'a', 'b'], ['b', 'o', 'o', 'k', '.', 'F'], none⟩]⟩, ⟨['p', 'a', 'ṛ', 'h', '-', 'i', 'i'], ['r', 'e', 'a', 'd', '-', 'P', 'F', 'V', '.', 'F', '.', 'S', 'G'], [⟨['p', 'a', 'ṛ', 'h'], ['r', 'e', 'a', 'd'], none⟩, ⟨['i', 'i'], ['P', 'F', 'V', '.', 'F', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['t', 'h', 'i', 'i'], ['b', 'e', '.', 'P', 'S', 'T', '.', 'F', '.', 'S', 'G'], [⟨['t', 'h', 'i', 'i'], ['b', 'e', '.', 'P', 'S', 'T', '.', 'F', '.', 'S', 'G'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("clause", "finite"), ("dependency", "lda")] }

def ex_73b : Datum :=
  { id := "keine2020_73b"
    source := ⟨"bhatt-2005", "p. 784"⟩
    reportedIn := some ⟨"keine-2020", "(73b)"⟩
    method := some .elicitation
    language := "hind1269"
    primaryText := "firoz-ne shabnam-kaa roṭii khaa-nii caah-ii"
    glossedTokens := [("firoz-ne", "Firoz-ERG"), ("shabnam-kaa", "Shabnam-GEN"), ("roṭii", "bread.F"), ("khaa-nii", "eat-INF.F.SG"), ("caah-ii", "want-PFV.F.SG")]
    glossedWords := [⟨['f', 'i', 'r', 'o', 'z', '-', 'n', 'e'], ['F', 'i', 'r', 'o', 'z', '-', 'E', 'R', 'G'], [⟨['f', 'i', 'r', 'o', 'z'], ['F', 'i', 'r', 'o', 'z'], none⟩, ⟨['n', 'e'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['s', 'h', 'a', 'b', 'n', 'a', 'm', '-', 'k', 'a', 'a'], ['S', 'h', 'a', 'b', 'n', 'a', 'm', '-', 'G', 'E', 'N'], [⟨['s', 'h', 'a', 'b', 'n', 'a', 'm'], ['S', 'h', 'a', 'b', 'n', 'a', 'm'], none⟩, ⟨['k', 'a', 'a'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['r', 'o', 'ṭ', 'i', 'i'], ['b', 'r', 'e', 'a', 'd', '.', 'F'], [⟨['r', 'o', 'ṭ', 'i', 'i'], ['b', 'r', 'e', 'a', 'd', '.', 'F'], none⟩]⟩, ⟨['k', 'h', 'a', 'a', '-', 'n', 'i', 'i'], ['e', 'a', 't', '-', 'I', 'N', 'F', '.', 'F', '.', 'S', 'G'], [⟨['k', 'h', 'a', 'a'], ['e', 'a', 't'], none⟩, ⟨['n', 'i', 'i'], ['I', 'N', 'F', '.', 'F', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['c', 'a', 'a', 'h', '-', 'i', 'i'], ['w', 'a', 'n', 't', '-', 'P', 'F', 'V', '.', 'F', '.', 'S', 'G'], [⟨['c', 'a', 'a', 'h'], ['w', 'a', 'n', 't'], none⟩, ⟨['i', 'i'], ['P', 'F', 'V', '.', 'F', '.', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("clause", "gerund"), ("dependency", "lda")] }

def ex_46 : Datum :=
  { id := "keine2020_46"
    source := ⟨"keine-2020", "(46)"⟩
    reportedIn := none
    method := some .elicitation
    language := "hind1269"
    primaryText := "har laṛke-ko us-kii bahin soc-tii hai ki raam-ne dekh-aa"
    glossedTokens := [("har", "every"), ("laṛke-ko", "boy-ACC"), ("us-kii", "s/he-GEN"), ("bahin", "sister"), ("soc-tii", "think-IPFV.F.SG"), ("hai", "be.PRES.3SG"), ("ki", "that"), ("raam-ne", "Ram-ERG"), ("dekh-aa", "see-PFV.M.SG")]
    glossedWords := [⟨['h', 'a', 'r'], ['e', 'v', 'e', 'r', 'y'], [⟨['h', 'a', 'r'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['l', 'a', 'ṛ', 'k', 'e', '-', 'k', 'o'], ['b', 'o', 'y', '-', 'A', 'C', 'C'], [⟨['l', 'a', 'ṛ', 'k', 'e'], ['b', 'o', 'y'], none⟩, ⟨['k', 'o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['u', 's', '-', 'k', 'i', 'i'], ['s', '/', 'h', 'e', '-', 'G', 'E', 'N'], [⟨['u', 's'], ['s', '/', 'h', 'e'], none⟩, ⟨['k', 'i', 'i'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['b', 'a', 'h', 'i', 'n'], ['s', 'i', 's', 't', 'e', 'r'], [⟨['b', 'a', 'h', 'i', 'n'], ['s', 'i', 's', 't', 'e', 'r'], none⟩]⟩, ⟨['s', 'o', 'c', '-', 't', 'i', 'i'], ['t', 'h', 'i', 'n', 'k', '-', 'I', 'P', 'F', 'V', '.', 'F', '.', 'S', 'G'], [⟨['s', 'o', 'c'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['t', 'i', 'i'], ['I', 'P', 'F', 'V', '.', 'F', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['h', 'a', 'i'], ['b', 'e', '.', 'P', 'R', 'E', 'S', '.', '3', 'S', 'G'], [⟨['h', 'a', 'i'], ['b', 'e', '.', 'P', 'R', 'E', 'S', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['k', 'i'], ['t', 'h', 'a', 't'], [⟨['k', 'i'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['r', 'a', 'a', 'm', '-', 'n', 'e'], ['R', 'a', 'm', '-', 'E', 'R', 'G'], [⟨['r', 'a', 'a', 'm'], ['R', 'a', 'm'], none⟩, ⟨['n', 'e'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['d', 'e', 'k', 'h', '-', 'a', 'a'], ['s', 'e', 'e', '-', 'P', 'F', 'V', '.', 'M', '.', 'S', 'G'], [⟨['d', 'e', 'k', 'h'], ['s', 'e', 'e'], none⟩, ⟨['a', 'a'], ['P', 'F', 'V', '.', 'M', '.', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "us-kii is not bound by the moved phrase"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "finite"), ("dependency", "movement")] }

def ex_47 : Datum :=
  { id := "keine2020_47"
    source := ⟨"keine-2020", "(47)"⟩
    reportedIn := none
    method := some .elicitation
    language := "hind1269"
    primaryText := "raam aur prataap-ko ek duusre-kii bahinõ-ne soc-aa ki sangiitaa-ne maar-aa"
    glossedTokens := [("raam", "Ram"), ("aur", "and"), ("prataap-ko", "Pratap-ACC"), ("ek", "each"), ("duusre-kii", "other-GEN"), ("bahinõ-ne", "sisters-ERG"), ("soc-aa", "think-PFV.M.SG"), ("ki", "that"), ("sangiitaa-ne", "Sangita-ERG"), ("maar-aa", "hit-PFV.M.SG")]
    glossedWords := [⟨['r', 'a', 'a', 'm'], ['R', 'a', 'm'], [⟨['r', 'a', 'a', 'm'], ['R', 'a', 'm'], none⟩]⟩, ⟨['a', 'u', 'r'], ['a', 'n', 'd'], [⟨['a', 'u', 'r'], ['a', 'n', 'd'], none⟩]⟩, ⟨['p', 'r', 'a', 't', 'a', 'a', 'p', '-', 'k', 'o'], ['P', 'r', 'a', 't', 'a', 'p', '-', 'A', 'C', 'C'], [⟨['p', 'r', 'a', 't', 'a', 'a', 'p'], ['P', 'r', 'a', 't', 'a', 'p'], none⟩, ⟨['k', 'o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['e', 'k'], ['e', 'a', 'c', 'h'], [⟨['e', 'k'], ['e', 'a', 'c', 'h'], none⟩]⟩, ⟨['d', 'u', 'u', 's', 'r', 'e', '-', 'k', 'i', 'i'], ['o', 't', 'h', 'e', 'r', '-', 'G', 'E', 'N'], [⟨['d', 'u', 'u', 's', 'r', 'e'], ['o', 't', 'h', 'e', 'r'], none⟩, ⟨['k', 'i', 'i'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['b', 'a', 'h', 'i', 'n', 'õ', '-', 'n', 'e'], ['s', 'i', 's', 't', 'e', 'r', 's', '-', 'E', 'R', 'G'], [⟨['b', 'a', 'h', 'i', 'n', 'õ'], ['s', 'i', 's', 't', 'e', 'r', 's'], none⟩, ⟨['n', 'e'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['s', 'o', 'c', '-', 'a', 'a'], ['t', 'h', 'i', 'n', 'k', '-', 'P', 'F', 'V', '.', 'M', '.', 'S', 'G'], [⟨['s', 'o', 'c'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['a', 'a'], ['P', 'F', 'V', '.', 'M', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['k', 'i'], ['t', 'h', 'a', 't'], [⟨['k', 'i'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['s', 'a', 'n', 'g', 'i', 'i', 't', 'a', 'a', '-', 'n', 'e'], ['S', 'a', 'n', 'g', 'i', 't', 'a', '-', 'E', 'R', 'G'], [⟨['s', 'a', 'n', 'g', 'i', 'i', 't', 'a', 'a'], ['S', 'a', 'n', 'g', 'i', 't', 'a'], none⟩, ⟨['n', 'e'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['m', 'a', 'a', 'r', '-', 'a', 'a'], ['h', 'i', 't', '-', 'P', 'F', 'V', '.', 'M', '.', 'S', 'G'], [⟨['m', 'a', 'a', 'r'], ['h', 'i', 't'], none⟩, ⟨['a', 'a'], ['P', 'F', 'V', '.', 'M', '.', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("clause", "finite"), ("dependency", "binding")] }

def ex_49b : Datum :=
  { id := "keine2020_49b"
    source := ⟨"keine-2020", "(49b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "hind1269"
    primaryText := "raam aur prataap-ko ek duusre-kii bahinõ-ne maar-naa caah-aa"
    glossedTokens := [("raam", "Ram"), ("aur", "and"), ("prataap-ko", "Pratap-ACC"), ("ek", "each"), ("duusre-kii", "other-GEN"), ("bahinõ-ne", "sisters-ERG"), ("maar-naa", "hit-INF.M.SG"), ("caah-aa", "want-PFV.M.SG")]
    glossedWords := [⟨['r', 'a', 'a', 'm'], ['R', 'a', 'm'], [⟨['r', 'a', 'a', 'm'], ['R', 'a', 'm'], none⟩]⟩, ⟨['a', 'u', 'r'], ['a', 'n', 'd'], [⟨['a', 'u', 'r'], ['a', 'n', 'd'], none⟩]⟩, ⟨['p', 'r', 'a', 't', 'a', 'a', 'p', '-', 'k', 'o'], ['P', 'r', 'a', 't', 'a', 'p', '-', 'A', 'C', 'C'], [⟨['p', 'r', 'a', 't', 'a', 'a', 'p'], ['P', 'r', 'a', 't', 'a', 'p'], none⟩, ⟨['k', 'o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['e', 'k'], ['e', 'a', 'c', 'h'], [⟨['e', 'k'], ['e', 'a', 'c', 'h'], none⟩]⟩, ⟨['d', 'u', 'u', 's', 'r', 'e', '-', 'k', 'i', 'i'], ['o', 't', 'h', 'e', 'r', '-', 'G', 'E', 'N'], [⟨['d', 'u', 'u', 's', 'r', 'e'], ['o', 't', 'h', 'e', 'r'], none⟩, ⟨['k', 'i', 'i'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['b', 'a', 'h', 'i', 'n', 'õ', '-', 'n', 'e'], ['s', 'i', 's', 't', 'e', 'r', 's', '-', 'E', 'R', 'G'], [⟨['b', 'a', 'h', 'i', 'n', 'õ'], ['s', 'i', 's', 't', 'e', 'r', 's'], none⟩, ⟨['n', 'e'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['m', 'a', 'a', 'r', '-', 'n', 'a', 'a'], ['h', 'i', 't', '-', 'I', 'N', 'F', '.', 'M', '.', 'S', 'G'], [⟨['m', 'a', 'a', 'r'], ['h', 'i', 't'], none⟩, ⟨['n', 'a', 'a'], ['I', 'N', 'F', '.', 'M', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['c', 'a', 'a', 'h', '-', 'a', 'a'], ['w', 'a', 'n', 't', '-', 'P', 'F', 'V', '.', 'M', '.', 'S', 'G'], [⟨['c', 'a', 'a', 'h'], ['w', 'a', 'n', 't'], none⟩, ⟨['a', 'a'], ['P', 'F', 'V', '.', 'M', '.', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "infinitive"), ("dependency", "binding")] }

def ex_50b : Datum :=
  { id := "keine2020_50b"
    source := ⟨"keine-2020", "(50b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "hind1269"
    primaryText := "kutte-ko raam-ne siitaa-kaa ghuuma-naa caah-aa"
    glossedTokens := [("kutte-ko", "dog-ACC"), ("raam-ne", "Ram-ERG"), ("siitaa-kaa", "Sita-GEN"), ("ghuuma-naa", "walk-INF.M.SG"), ("caah-aa", "want-PFV.M.SG")]
    glossedWords := [⟨['k', 'u', 't', 't', 'e', '-', 'k', 'o'], ['d', 'o', 'g', '-', 'A', 'C', 'C'], [⟨['k', 'u', 't', 't', 'e'], ['d', 'o', 'g'], none⟩, ⟨['k', 'o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['r', 'a', 'a', 'm', '-', 'n', 'e'], ['R', 'a', 'm', '-', 'E', 'R', 'G'], [⟨['r', 'a', 'a', 'm'], ['R', 'a', 'm'], none⟩, ⟨['n', 'e'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['s', 'i', 'i', 't', 'a', 'a', '-', 'k', 'a', 'a'], ['S', 'i', 't', 'a', '-', 'G', 'E', 'N'], [⟨['s', 'i', 'i', 't', 'a', 'a'], ['S', 'i', 't', 'a'], none⟩, ⟨['k', 'a', 'a'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['g', 'h', 'u', 'u', 'm', 'a', '-', 'n', 'a', 'a'], ['w', 'a', 'l', 'k', '-', 'I', 'N', 'F', '.', 'M', '.', 'S', 'G'], [⟨['g', 'h', 'u', 'u', 'm', 'a'], ['w', 'a', 'l', 'k'], none⟩, ⟨['n', 'a', 'a'], ['I', 'N', 'F', '.', 'M', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['c', 'a', 'a', 'h', '-', 'a', 'a'], ['w', 'a', 'n', 't', '-', 'P', 'F', 'V', '.', 'M', '.', 'S', 'G'], [⟨['c', 'a', 'a', 'h'], ['w', 'a', 'n', 't'], none⟩, ⟨['a', 'a'], ['P', 'F', 'V', '.', 'M', '.', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("clause", "gerund"), ("dependency", "movement")] }

def ex_91a : Datum :=
  { id := "keine2020_91a"
    source := ⟨"keine-2020", "(91a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "hind1269"
    primaryText := "pichle hafte raam-ne yah kitaab kal paṛh-naa caah-aa thaa"
    glossedTokens := [("pichle", "last"), ("hafte", "week"), ("raam-ne", "Ram-ERG"), ("yah", "this"), ("kitaab", "book.F"), ("kal", "yesterday/tomorrow"), ("paṛh-naa", "read-INF.M.SG"), ("caah-aa", "want-PFV.M.SG"), ("thaa", "be.PST.M.SG")]
    glossedWords := [⟨['p', 'i', 'c', 'h', 'l', 'e'], ['l', 'a', 's', 't'], [⟨['p', 'i', 'c', 'h', 'l', 'e'], ['l', 'a', 's', 't'], none⟩]⟩, ⟨['h', 'a', 'f', 't', 'e'], ['w', 'e', 'e', 'k'], [⟨['h', 'a', 'f', 't', 'e'], ['w', 'e', 'e', 'k'], none⟩]⟩, ⟨['r', 'a', 'a', 'm', '-', 'n', 'e'], ['R', 'a', 'm', '-', 'E', 'R', 'G'], [⟨['r', 'a', 'a', 'm'], ['R', 'a', 'm'], none⟩, ⟨['n', 'e'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['y', 'a', 'h'], ['t', 'h', 'i', 's'], [⟨['y', 'a', 'h'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['k', 'i', 't', 'a', 'a', 'b'], ['b', 'o', 'o', 'k', '.', 'F'], [⟨['k', 'i', 't', 'a', 'a', 'b'], ['b', 'o', 'o', 'k', '.', 'F'], none⟩]⟩, ⟨['k', 'a', 'l'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y', '/', 't', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['k', 'a', 'l'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y', '/', 't', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩, ⟨['p', 'a', 'ṛ', 'h', '-', 'n', 'a', 'a'], ['r', 'e', 'a', 'd', '-', 'I', 'N', 'F', '.', 'M', '.', 'S', 'G'], [⟨['p', 'a', 'ṛ', 'h'], ['r', 'e', 'a', 'd'], none⟩, ⟨['n', 'a', 'a'], ['I', 'N', 'F', '.', 'M', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['c', 'a', 'a', 'h', '-', 'a', 'a'], ['w', 'a', 'n', 't', '-', 'P', 'F', 'V', '.', 'M', '.', 'S', 'G'], [⟨['c', 'a', 'a', 'h'], ['w', 'a', 'n', 't'], none⟩, ⟨['a', 'a'], ['P', 'F', 'V', '.', 'M', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['t', 'h', 'a', 'a'], ['b', 'e', '.', 'P', 'S', 'T', '.', 'M', '.', 'S', 'G'], [⟨['t', 'h', 'a', 'a'], ['b', 'e', '.', 'P', 'S', 'T', '.', 'M', '.', 'S', 'G'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "modifiedInfinitive"), ("dependency", "defaultAgreement")] }

def ex_93a : Datum :=
  { id := "keine2020_93a"
    source := ⟨"keine-2020", "(93a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "hind1269"
    primaryText := "raam-ne khiṛkii nahĩĩ band kar-naa shuruu kar di-yaa hai"
    glossedTokens := [("raam-ne", "Ram-ERG"), ("khiṛkii", "window.F"), ("nahĩĩ", "not"), ("band", "close"), ("kar-naa", "do-INF.M.SG"), ("shuruu", "begin"), ("kar", "do"), ("di-yaa", "give-PFV.M.SG"), ("hai", "be.PRES.3SG")]
    glossedWords := [⟨['r', 'a', 'a', 'm', '-', 'n', 'e'], ['R', 'a', 'm', '-', 'E', 'R', 'G'], [⟨['r', 'a', 'a', 'm'], ['R', 'a', 'm'], none⟩, ⟨['n', 'e'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['k', 'h', 'i', 'ṛ', 'k', 'i', 'i'], ['w', 'i', 'n', 'd', 'o', 'w', '.', 'F'], [⟨['k', 'h', 'i', 'ṛ', 'k', 'i', 'i'], ['w', 'i', 'n', 'd', 'o', 'w', '.', 'F'], none⟩]⟩, ⟨['n', 'a', 'h', 'ĩ', 'ĩ'], ['n', 'o', 't'], [⟨['n', 'a', 'h', 'ĩ', 'ĩ'], ['n', 'o', 't'], none⟩]⟩, ⟨['b', 'a', 'n', 'd'], ['c', 'l', 'o', 's', 'e'], [⟨['b', 'a', 'n', 'd'], ['c', 'l', 'o', 's', 'e'], none⟩]⟩, ⟨['k', 'a', 'r', '-', 'n', 'a', 'a'], ['d', 'o', '-', 'I', 'N', 'F', '.', 'M', '.', 'S', 'G'], [⟨['k', 'a', 'r'], ['d', 'o'], none⟩, ⟨['n', 'a', 'a'], ['I', 'N', 'F', '.', 'M', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['s', 'h', 'u', 'r', 'u', 'u'], ['b', 'e', 'g', 'i', 'n'], [⟨['s', 'h', 'u', 'r', 'u', 'u'], ['b', 'e', 'g', 'i', 'n'], none⟩]⟩, ⟨['k', 'a', 'r'], ['d', 'o'], [⟨['k', 'a', 'r'], ['d', 'o'], none⟩]⟩, ⟨['d', 'i', '-', 'y', 'a', 'a'], ['g', 'i', 'v', 'e', '-', 'P', 'F', 'V', '.', 'M', '.', 'S', 'G'], [⟨['d', 'i'], ['g', 'i', 'v', 'e'], none⟩, ⟨['y', 'a', 'a'], ['P', 'F', 'V', '.', 'M', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['h', 'a', 'i'], ['b', 'e', '.', 'P', 'R', 'E', 'S', '.', '3', 'S', 'G'], [⟨['h', 'a', 'i'], ['b', 'e', '.', 'P', 'R', 'E', 'S', '.', '3', 'S', 'G'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "modifiedInfinitive"), ("dependency", "defaultAgreement")] }

def ex_93b : Datum :=
  { id := "keine2020_93b"
    source := ⟨"keine-2020", "(93b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "hind1269"
    primaryText := "raam-ne khiṛkii nahĩĩ band kar-nii shuruu kar d-ii hai"
    glossedTokens := [("raam-ne", "Ram-ERG"), ("khiṛkii", "window.F"), ("nahĩĩ", "not"), ("band", "close"), ("kar-nii", "do-INF.F.SG"), ("shuruu", "begin"), ("kar", "do"), ("d-ii", "give-PFV.F.SG"), ("hai", "be.PRES.3SG")]
    glossedWords := [⟨['r', 'a', 'a', 'm', '-', 'n', 'e'], ['R', 'a', 'm', '-', 'E', 'R', 'G'], [⟨['r', 'a', 'a', 'm'], ['R', 'a', 'm'], none⟩, ⟨['n', 'e'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['k', 'h', 'i', 'ṛ', 'k', 'i', 'i'], ['w', 'i', 'n', 'd', 'o', 'w', '.', 'F'], [⟨['k', 'h', 'i', 'ṛ', 'k', 'i', 'i'], ['w', 'i', 'n', 'd', 'o', 'w', '.', 'F'], none⟩]⟩, ⟨['n', 'a', 'h', 'ĩ', 'ĩ'], ['n', 'o', 't'], [⟨['n', 'a', 'h', 'ĩ', 'ĩ'], ['n', 'o', 't'], none⟩]⟩, ⟨['b', 'a', 'n', 'd'], ['c', 'l', 'o', 's', 'e'], [⟨['b', 'a', 'n', 'd'], ['c', 'l', 'o', 's', 'e'], none⟩]⟩, ⟨['k', 'a', 'r', '-', 'n', 'i', 'i'], ['d', 'o', '-', 'I', 'N', 'F', '.', 'F', '.', 'S', 'G'], [⟨['k', 'a', 'r'], ['d', 'o'], none⟩, ⟨['n', 'i', 'i'], ['I', 'N', 'F', '.', 'F', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['s', 'h', 'u', 'r', 'u', 'u'], ['b', 'e', 'g', 'i', 'n'], [⟨['s', 'h', 'u', 'r', 'u', 'u'], ['b', 'e', 'g', 'i', 'n'], none⟩]⟩, ⟨['k', 'a', 'r'], ['d', 'o'], [⟨['k', 'a', 'r'], ['d', 'o'], none⟩]⟩, ⟨['d', '-', 'i', 'i'], ['g', 'i', 'v', 'e', '-', 'P', 'F', 'V', '.', 'F', '.', 'S', 'G'], [⟨['d'], ['g', 'i', 'v', 'e'], none⟩, ⟨['i', 'i'], ['P', 'F', 'V', '.', 'F', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['h', 'a', 'i'], ['b', 'e', '.', 'P', 'R', 'E', 'S', '.', '3', 'S', 'G'], [⟨['h', 'a', 'i'], ['b', 'e', '.', 'P', 'R', 'E', 'S', '.', '3', 'S', 'G'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "modifiedInfinitive"), ("dependency", "lda")] }

def ex_96b_default : Datum :=
  { id := "keine2020_96b_default"
    source := ⟨"keine-2020", "(96b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "hind1269"
    primaryText := "har laṛke-se us-kii mãã-ne baat kar-naa caah-aa"
    glossedTokens := [("har", "every"), ("laṛke-se", "boy-INSTR"), ("us-kii", "s/he-GEN"), ("mãã-ne", "mother-ERG"), ("baat", "talk.F"), ("kar-naa", "do-INF.M.SG"), ("caah-aa", "want-PFV.M.SG")]
    glossedWords := [⟨['h', 'a', 'r'], ['e', 'v', 'e', 'r', 'y'], [⟨['h', 'a', 'r'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['l', 'a', 'ṛ', 'k', 'e', '-', 's', 'e'], ['b', 'o', 'y', '-', 'I', 'N', 'S', 'T', 'R'], [⟨['l', 'a', 'ṛ', 'k', 'e'], ['b', 'o', 'y'], none⟩, ⟨['s', 'e'], ['I', 'N', 'S', 'T', 'R'], some '-'⟩]⟩, ⟨['u', 's', '-', 'k', 'i', 'i'], ['s', '/', 'h', 'e', '-', 'G', 'E', 'N'], [⟨['u', 's'], ['s', '/', 'h', 'e'], none⟩, ⟨['k', 'i', 'i'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['m', 'ã', 'ã', '-', 'n', 'e'], ['m', 'o', 't', 'h', 'e', 'r', '-', 'E', 'R', 'G'], [⟨['m', 'ã', 'ã'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['n', 'e'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['b', 'a', 'a', 't'], ['t', 'a', 'l', 'k', '.', 'F'], [⟨['b', 'a', 'a', 't'], ['t', 'a', 'l', 'k', '.', 'F'], none⟩]⟩, ⟨['k', 'a', 'r', '-', 'n', 'a', 'a'], ['d', 'o', '-', 'I', 'N', 'F', '.', 'M', '.', 'S', 'G'], [⟨['k', 'a', 'r'], ['d', 'o'], none⟩, ⟨['n', 'a', 'a'], ['I', 'N', 'F', '.', 'M', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['c', 'a', 'a', 'h', '-', 'a', 'a'], ['w', 'a', 'n', 't', '-', 'P', 'F', 'V', '.', 'M', '.', 'S', 'G'], [⟨['c', 'a', 'a', 'h'], ['w', 'a', 'n', 't'], none⟩, ⟨['a', 'a'], ['P', 'F', 'V', '.', 'M', '.', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "us-kii is not bound by the moved phrase"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "infinitive"), ("dependency", "movement"), ("dependency", "defaultAgreement")] }

def ex_96c_lda : Datum :=
  { id := "keine2020_96c_lda"
    source := ⟨"keine-2020", "(96c)"⟩
    reportedIn := none
    method := some .elicitation
    language := "hind1269"
    primaryText := "har laṛke-se us-kii mãã-ne baat kar-nii caah-ii"
    glossedTokens := [("har", "every"), ("laṛke-se", "boy-INSTR"), ("us-kii", "s/he-GEN"), ("mãã-ne", "mother-ERG"), ("baat", "talk.F"), ("kar-nii", "do-INF.F.SG"), ("caah-ii", "want-PFV.F.SG")]
    glossedWords := [⟨['h', 'a', 'r'], ['e', 'v', 'e', 'r', 'y'], [⟨['h', 'a', 'r'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['l', 'a', 'ṛ', 'k', 'e', '-', 's', 'e'], ['b', 'o', 'y', '-', 'I', 'N', 'S', 'T', 'R'], [⟨['l', 'a', 'ṛ', 'k', 'e'], ['b', 'o', 'y'], none⟩, ⟨['s', 'e'], ['I', 'N', 'S', 'T', 'R'], some '-'⟩]⟩, ⟨['u', 's', '-', 'k', 'i', 'i'], ['s', '/', 'h', 'e', '-', 'G', 'E', 'N'], [⟨['u', 's'], ['s', '/', 'h', 'e'], none⟩, ⟨['k', 'i', 'i'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['m', 'ã', 'ã', '-', 'n', 'e'], ['m', 'o', 't', 'h', 'e', 'r', '-', 'E', 'R', 'G'], [⟨['m', 'ã', 'ã'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['n', 'e'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['b', 'a', 'a', 't'], ['t', 'a', 'l', 'k', '.', 'F'], [⟨['b', 'a', 'a', 't'], ['t', 'a', 'l', 'k', '.', 'F'], none⟩]⟩, ⟨['k', 'a', 'r', '-', 'n', 'i', 'i'], ['d', 'o', '-', 'I', 'N', 'F', '.', 'F', '.', 'S', 'G'], [⟨['k', 'a', 'r'], ['d', 'o'], none⟩, ⟨['n', 'i', 'i'], ['I', 'N', 'F', '.', 'F', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['c', 'a', 'a', 'h', '-', 'i', 'i'], ['w', 'a', 'n', 't', '-', 'P', 'F', 'V', '.', 'F', '.', 'S', 'G'], [⟨['c', 'a', 'a', 'h'], ['w', 'a', 'n', 't'], none⟩, ⟨['i', 'i'], ['P', 'F', 'V', '.', 'F', '.', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "us-kii is bound by the moved phrase"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "infinitive"), ("dependency", "binding"), ("dependency", "lda")] }

def ex_96c_default : Datum :=
  { id := "keine2020_96c_default"
    source := ⟨"keine-2020", "(96c)"⟩
    reportedIn := none
    method := some .elicitation
    language := "hind1269"
    primaryText := "har laṛke-se us-kii mãã-ne baat kar-naa caah-aa"
    glossedTokens := [("har", "every"), ("laṛke-se", "boy-INSTR"), ("us-kii", "s/he-GEN"), ("mãã-ne", "mother-ERG"), ("baat", "talk.F"), ("kar-naa", "do-INF.M.SG"), ("caah-aa", "want-PFV.M.SG")]
    glossedWords := [⟨['h', 'a', 'r'], ['e', 'v', 'e', 'r', 'y'], [⟨['h', 'a', 'r'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['l', 'a', 'ṛ', 'k', 'e', '-', 's', 'e'], ['b', 'o', 'y', '-', 'I', 'N', 'S', 'T', 'R'], [⟨['l', 'a', 'ṛ', 'k', 'e'], ['b', 'o', 'y'], none⟩, ⟨['s', 'e'], ['I', 'N', 'S', 'T', 'R'], some '-'⟩]⟩, ⟨['u', 's', '-', 'k', 'i', 'i'], ['s', '/', 'h', 'e', '-', 'G', 'E', 'N'], [⟨['u', 's'], ['s', '/', 'h', 'e'], none⟩, ⟨['k', 'i', 'i'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['m', 'ã', 'ã', '-', 'n', 'e'], ['m', 'o', 't', 'h', 'e', 'r', '-', 'E', 'R', 'G'], [⟨['m', 'ã', 'ã'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['n', 'e'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['b', 'a', 'a', 't'], ['t', 'a', 'l', 'k', '.', 'F'], [⟨['b', 'a', 'a', 't'], ['t', 'a', 'l', 'k', '.', 'F'], none⟩]⟩, ⟨['k', 'a', 'r', '-', 'n', 'a', 'a'], ['d', 'o', '-', 'I', 'N', 'F', '.', 'M', '.', 'S', 'G'], [⟨['k', 'a', 'r'], ['d', 'o'], none⟩, ⟨['n', 'a', 'a'], ['I', 'N', 'F', '.', 'M', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['c', 'a', 'a', 'h', '-', 'a', 'a'], ['w', 'a', 'n', 't', '-', 'P', 'F', 'V', '.', 'M', '.', 'S', 'G'], [⟨['c', 'a', 'a', 'h'], ['w', 'a', 'n', 't'], none⟩, ⟨['a', 'a'], ['P', 'F', 'V', '.', 'M', '.', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "us-kii is bound by the moved phrase"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "infinitive"), ("dependency", "binding"), ("dependency", "defaultAgreement")] }

def ex_121 : Datum :=
  { id := "keine2020_121"
    source := ⟨"keine-2020", "(121)"⟩
    reportedIn := none
    method := some .elicitation
    language := "hind1269"
    primaryText := "siitaa-ne soc-aa kis-ko ravii-ne dekh-aa?"
    glossedTokens := [("siitaa-ne", "Sita-ERG"), ("soc-aa", "think-PFV.M.SG"), ("kis-ko", "who-ACC"), ("ravii-ne", "Ravi-ERG"), ("dekh-aa", "see-PFV.M.SG")]
    glossedWords := [⟨['s', 'i', 'i', 't', 'a', 'a', '-', 'n', 'e'], ['S', 'i', 't', 'a', '-', 'E', 'R', 'G'], [⟨['s', 'i', 'i', 't', 'a', 'a'], ['S', 'i', 't', 'a'], none⟩, ⟨['n', 'e'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['s', 'o', 'c', '-', 'a', 'a'], ['t', 'h', 'i', 'n', 'k', '-', 'P', 'F', 'V', '.', 'M', '.', 'S', 'G'], [⟨['s', 'o', 'c'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['a', 'a'], ['P', 'F', 'V', '.', 'M', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['k', 'i', 's', '-', 'k', 'o'], ['w', 'h', 'o', '-', 'A', 'C', 'C'], [⟨['k', 'i', 's'], ['w', 'h', 'o'], none⟩, ⟨['k', 'o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['r', 'a', 'v', 'i', 'i', '-', 'n', 'e'], ['R', 'a', 'v', 'i', '-', 'E', 'R', 'G'], [⟨['r', 'a', 'v', 'i', 'i'], ['R', 'a', 'v', 'i'], none⟩, ⟨['n', 'e'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['d', 'e', 'k', 'h', '-', 'a', 'a'], ['s', 'e', 'e', '-', 'P', 'F', 'V', '.', 'M', '.', 'S', 'G'], [⟨['d', 'e', 'k', 'h'], ['s', 'e', 'e'], none⟩, ⟨['a', 'a'], ['P', 'F', 'V', '.', 'M', '.', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("clause", "finite"), ("dependency", "whScope")] }

def ex_123a : Datum :=
  { id := "keine2020_123a"
    source := ⟨"keine-2020", "(123a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "hind1269"
    primaryText := "raam-ne siitaa-ko kaunsii maalaa de-nii caah-ii?"
    glossedTokens := [("raam-ne", "Ram-ERG"), ("siitaa-ko", "Sita-DAT"), ("kaunsii", "which"), ("maalaa", "necklace.F"), ("de-nii", "give-INF.F.SG"), ("caah-ii", "want-PFV.F.SG")]
    glossedWords := [⟨['r', 'a', 'a', 'm', '-', 'n', 'e'], ['R', 'a', 'm', '-', 'E', 'R', 'G'], [⟨['r', 'a', 'a', 'm'], ['R', 'a', 'm'], none⟩, ⟨['n', 'e'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['s', 'i', 'i', 't', 'a', 'a', '-', 'k', 'o'], ['S', 'i', 't', 'a', '-', 'D', 'A', 'T'], [⟨['s', 'i', 'i', 't', 'a', 'a'], ['S', 'i', 't', 'a'], none⟩, ⟨['k', 'o'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['k', 'a', 'u', 'n', 's', 'i', 'i'], ['w', 'h', 'i', 'c', 'h'], [⟨['k', 'a', 'u', 'n', 's', 'i', 'i'], ['w', 'h', 'i', 'c', 'h'], none⟩]⟩, ⟨['m', 'a', 'a', 'l', 'a', 'a'], ['n', 'e', 'c', 'k', 'l', 'a', 'c', 'e', '.', 'F'], [⟨['m', 'a', 'a', 'l', 'a', 'a'], ['n', 'e', 'c', 'k', 'l', 'a', 'c', 'e', '.', 'F'], none⟩]⟩, ⟨['d', 'e', '-', 'n', 'i', 'i'], ['g', 'i', 'v', 'e', '-', 'I', 'N', 'F', '.', 'F', '.', 'S', 'G'], [⟨['d', 'e'], ['g', 'i', 'v', 'e'], none⟩, ⟨['n', 'i', 'i'], ['I', 'N', 'F', '.', 'F', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['c', 'a', 'a', 'h', '-', 'i', 'i'], ['w', 'a', 'n', 't', '-', 'P', 'F', 'V', '.', 'F', '.', 'S', 'G'], [⟨['c', 'a', 'a', 'h'], ['w', 'a', 'n', 't'], none⟩, ⟨['i', 'i'], ['P', 'F', 'V', '.', 'F', '.', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "infinitive"), ("dependency", "whScope"), ("dependency", "lda")] }

def ex_123b : Datum :=
  { id := "keine2020_123b"
    source := ⟨"keine-2020", "(123b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "hind1269"
    primaryText := "raam-ne siitaa-ko kaunsii maalaa de-naa caah-aa?"
    glossedTokens := [("raam-ne", "Ram-ERG"), ("siitaa-ko", "Sita-DAT"), ("kaunsii", "which"), ("maalaa", "necklace.F"), ("de-naa", "give-INF.M.SG"), ("caah-aa", "want-PFV.M.SG")]
    glossedWords := [⟨['r', 'a', 'a', 'm', '-', 'n', 'e'], ['R', 'a', 'm', '-', 'E', 'R', 'G'], [⟨['r', 'a', 'a', 'm'], ['R', 'a', 'm'], none⟩, ⟨['n', 'e'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['s', 'i', 'i', 't', 'a', 'a', '-', 'k', 'o'], ['S', 'i', 't', 'a', '-', 'D', 'A', 'T'], [⟨['s', 'i', 'i', 't', 'a', 'a'], ['S', 'i', 't', 'a'], none⟩, ⟨['k', 'o'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['k', 'a', 'u', 'n', 's', 'i', 'i'], ['w', 'h', 'i', 'c', 'h'], [⟨['k', 'a', 'u', 'n', 's', 'i', 'i'], ['w', 'h', 'i', 'c', 'h'], none⟩]⟩, ⟨['m', 'a', 'a', 'l', 'a', 'a'], ['n', 'e', 'c', 'k', 'l', 'a', 'c', 'e', '.', 'F'], [⟨['m', 'a', 'a', 'l', 'a', 'a'], ['n', 'e', 'c', 'k', 'l', 'a', 'c', 'e', '.', 'F'], none⟩]⟩, ⟨['d', 'e', '-', 'n', 'a', 'a'], ['g', 'i', 'v', 'e', '-', 'I', 'N', 'F', '.', 'M', '.', 'S', 'G'], [⟨['d', 'e'], ['g', 'i', 'v', 'e'], none⟩, ⟨['n', 'a', 'a'], ['I', 'N', 'F', '.', 'M', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['c', 'a', 'a', 'h', '-', 'a', 'a'], ['w', 'a', 'n', 't', '-', 'P', 'F', 'V', '.', 'M', '.', 'S', 'G'], [⟨['c', 'a', 'a', 'h'], ['w', 'a', 'n', 't'], none⟩, ⟨['a', 'a'], ['P', 'F', 'V', '.', 'M', '.', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "infinitive"), ("dependency", "whScope"), ("dependency", "defaultAgreement")] }

def ex_125 : Datum :=
  { id := "keine2020_125"
    source := ⟨"keine-2020", "(125)"⟩
    reportedIn := none
    method := some .elicitation
    language := "hind1269"
    primaryText := "pichle hafte raam-ne kal kyaa khaa-naa caah-aa thaa?"
    glossedTokens := [("pichle", "last"), ("hafte", "week"), ("raam-ne", "Ram-ERG"), ("kal", "yesterday/tomorrow"), ("kyaa", "what"), ("khaa-naa", "eat-INF.M.SG"), ("caah-aa", "want-PFV.M.SG"), ("thaa", "be.PST.M.SG")]
    glossedWords := [⟨['p', 'i', 'c', 'h', 'l', 'e'], ['l', 'a', 's', 't'], [⟨['p', 'i', 'c', 'h', 'l', 'e'], ['l', 'a', 's', 't'], none⟩]⟩, ⟨['h', 'a', 'f', 't', 'e'], ['w', 'e', 'e', 'k'], [⟨['h', 'a', 'f', 't', 'e'], ['w', 'e', 'e', 'k'], none⟩]⟩, ⟨['r', 'a', 'a', 'm', '-', 'n', 'e'], ['R', 'a', 'm', '-', 'E', 'R', 'G'], [⟨['r', 'a', 'a', 'm'], ['R', 'a', 'm'], none⟩, ⟨['n', 'e'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['k', 'a', 'l'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y', '/', 't', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['k', 'a', 'l'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y', '/', 't', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩, ⟨['k', 'y', 'a', 'a'], ['w', 'h', 'a', 't'], [⟨['k', 'y', 'a', 'a'], ['w', 'h', 'a', 't'], none⟩]⟩, ⟨['k', 'h', 'a', 'a', '-', 'n', 'a', 'a'], ['e', 'a', 't', '-', 'I', 'N', 'F', '.', 'M', '.', 'S', 'G'], [⟨['k', 'h', 'a', 'a'], ['e', 'a', 't'], none⟩, ⟨['n', 'a', 'a'], ['I', 'N', 'F', '.', 'M', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['c', 'a', 'a', 'h', '-', 'a', 'a'], ['w', 'a', 'n', 't', '-', 'P', 'F', 'V', '.', 'M', '.', 'S', 'G'], [⟨['c', 'a', 'a', 'h'], ['w', 'a', 'n', 't'], none⟩, ⟨['a', 'a'], ['P', 'F', 'V', '.', 'M', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['t', 'h', 'a', 'a'], ['b', 'e', '.', 'P', 'S', 'T', '.', 'M', '.', 'S', 'G'], [⟨['t', 'h', 'a', 'a'], ['b', 'e', '.', 'P', 'S', 'T', '.', 'M', '.', 'S', 'G'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "modifiedInfinitive"), ("dependency", "whScope")] }

def ex_127 : Datum :=
  { id := "keine2020_127"
    source := ⟨"keine-2020", "(127)"⟩
    reportedIn := none
    method := some .elicitation
    language := "hind1269"
    primaryText := "siitaa-kaa kyaa khaa-naa ravii-ko buraa lag-taa hai?"
    glossedTokens := [("siitaa-kaa", "Sita-GEN"), ("kyaa", "what"), ("khaa-naa", "eat-INF.M.SG"), ("ravii-ko", "Ravi-DAT"), ("buraa", "bad.M.SG"), ("lag-taa", "seem-IPFV.M.SG"), ("hai", "be.PRES.3SG")]
    glossedWords := [⟨['s', 'i', 'i', 't', 'a', 'a', '-', 'k', 'a', 'a'], ['S', 'i', 't', 'a', '-', 'G', 'E', 'N'], [⟨['s', 'i', 'i', 't', 'a', 'a'], ['S', 'i', 't', 'a'], none⟩, ⟨['k', 'a', 'a'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['k', 'y', 'a', 'a'], ['w', 'h', 'a', 't'], [⟨['k', 'y', 'a', 'a'], ['w', 'h', 'a', 't'], none⟩]⟩, ⟨['k', 'h', 'a', 'a', '-', 'n', 'a', 'a'], ['e', 'a', 't', '-', 'I', 'N', 'F', '.', 'M', '.', 'S', 'G'], [⟨['k', 'h', 'a', 'a'], ['e', 'a', 't'], none⟩, ⟨['n', 'a', 'a'], ['I', 'N', 'F', '.', 'M', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['r', 'a', 'v', 'i', 'i', '-', 'k', 'o'], ['R', 'a', 'v', 'i', '-', 'D', 'A', 'T'], [⟨['r', 'a', 'v', 'i', 'i'], ['R', 'a', 'v', 'i'], none⟩, ⟨['k', 'o'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['b', 'u', 'r', 'a', 'a'], ['b', 'a', 'd', '.', 'M', '.', 'S', 'G'], [⟨['b', 'u', 'r', 'a', 'a'], ['b', 'a', 'd', '.', 'M', '.', 'S', 'G'], none⟩]⟩, ⟨['l', 'a', 'g', '-', 't', 'a', 'a'], ['s', 'e', 'e', 'm', '-', 'I', 'P', 'F', 'V', '.', 'M', '.', 'S', 'G'], [⟨['l', 'a', 'g'], ['s', 'e', 'e', 'm'], none⟩, ⟨['t', 'a', 'a'], ['I', 'P', 'F', 'V', '.', 'M', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['h', 'a', 'i'], ['b', 'e', '.', 'P', 'R', 'E', 'S', '.', '3', 'S', 'G'], [⟨['h', 'a', 'i'], ['b', 'e', '.', 'P', 'R', 'E', 'S', '.', '3', 'S', 'G'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "gerund"), ("dependency", "whScope")] }

def all : List Datum := [ex_56, ex_57, ex_71_default, ex_71_lda, ex_73b, ex_46, ex_47, ex_49b, ex_50b, ex_91a, ex_93a, ex_93b, ex_96b_default, ex_96c_lda, ex_96c_default, ex_121, ex_123a, ex_123b, ex_125, ex_127]

/-- The surface type of the embedded clause. -/
inductive Clause where
  /-- finite: a finite clause -/
  | finite
  /-- infinitive: an infinitival clause without a subject, a temporal adverb or a negation of its own -/
  | infinitive
  /-- modifiedInfinitive: an infinitival clause that contains a temporal adverb or a negation of its own -/
  | modifiedInfinitive
  /-- gerund: a nonfinite clause with a genitive subject -/
  | gerund
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `clause`. -/
def clause (e : Datum) : Option Clause :=
  e.parse? "clause" [("finite", .finite), ("infinitive", .infinitive),
    ("modifiedInfinitive", .modifiedInfinitive), ("gerund", .gerund)]

/-- The dependencies a sentence shows between the matrix clause and the embedded clause. -/
inductive Dependency where
  /-- binding: a phrase moved out of the embedded clause binds a pronoun or a reciprocal from its landing site -/
  | binding
  /-- movement: a phrase is moved out of the embedded clause and binds nothing from its landing site -/
  | movement
  /-- lda: the matrix verb agrees with an argument of the embedded clause -/
  | lda
  /-- defaultAgreement: the matrix verb shows default agreement, its own arguments being case-marked and an argument of the embedded clause unmarked -/
  | defaultAgreement
  /-- whScope: a wh-phrase inside the embedded clause takes matrix scope -/
  | whScope
  deriving DecidableEq, Repr, Fintype

/-- The values a row records under `dependency`. -/
def dependencies (e : Datum) : List Dependency :=
  (e.features "dependency").filterMap (List.lookup · [("binding", .binding), ("movement", .movement), ("lda", .lda),
    ("defaultAgreement", .defaultAgreement), ("whScope", .whScope)])

end Keine2020.Examples
