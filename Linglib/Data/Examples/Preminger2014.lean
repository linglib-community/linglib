module

public import Linglib.Data.Examples.Schema
public import Mathlib.Tactic.DeriveFintype

/-!
# `Preminger2014` — typed example data

Auto-generated from `Linglib/Data/Examples/Preminger2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Preminger2014.Examples`.
-/

@[expose] public section

namespace Preminger2014.Examples

def ex_14a : Datum :=
  { id := "preminger2014_14a"
    source := ⟨"preminger-2014", "(14a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "ja ri tz'i' x-Ø-etzel-an ri sian"
    glossedTokens := [("ja", "FOC"), ("ri", "the"), ("tz'i'", "dog"), ("x-Ø-etzel-an", "COM-3SG.ABS-hate-AF"), ("ri", "the"), ("sian", "cat")]
    glossedWords := [⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['t', 'z', '\'', 'i', '\''], ['d', 'o', 'g'], [⟨['t', 'z', '\'', 'i', '\''], ['d', 'o', 'g'], none⟩]⟩, ⟨['x', '-', 'Ø', '-', 'e', 't', 'z', 'e', 'l', '-', 'a', 'n'], ['C', 'O', 'M', '-', '3', 'S', 'G', '.', 'A', 'B', 'S', '-', 'h', 'a', 't', 'e', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['Ø'], ['3', 'S', 'G', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['e', 't', 'z', 'e', 'l'], ['h', 'a', 't', 'e'], some '-'⟩, ⟨['a', 'n'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['s', 'i', 'a', 'n'], ['c', 'a', 't'], [⟨['s', 'i', 'a', 'n'], ['c', 'a', 't'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 2, "subject", none⟩, ⟨4, 2, "object", none⟩]
    paperFeatures := [] }

def ex_14b : Datum :=
  { id := "preminger2014_14b"
    source := ⟨"preminger-2014", "(14b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "ja ri xoq x-Ø-tz'et-ö ri achin"
    glossedTokens := [("ja", "FOC"), ("ri", "the"), ("xoq", "woman"), ("x-Ø-tz'et-ö", "COM-3SG.ABS-see-AF"), ("ri", "the"), ("achin", "man")]
    glossedWords := [⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['x', 'o', 'q'], ['w', 'o', 'm', 'a', 'n'], [⟨['x', 'o', 'q'], ['w', 'o', 'm', 'a', 'n'], none⟩]⟩, ⟨['x', '-', 'Ø', '-', 't', 'z', '\'', 'e', 't', '-', 'ö'], ['C', 'O', 'M', '-', '3', 'S', 'G', '.', 'A', 'B', 'S', '-', 's', 'e', 'e', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['Ø'], ['3', 'S', 'G', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['t', 'z', '\'', 'e', 't'], ['s', 'e', 'e'], some '-'⟩, ⟨['ö'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['a', 'c', 'h', 'i', 'n'], ['m', 'a', 'n'], [⟨['a', 'c', 'h', 'i', 'n'], ['m', 'a', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 2, "subject", none⟩, ⟨4, 2, "object", none⟩]
    paperFeatures := [] }

def ex_15a_2sg : Datum :=
  { id := "preminger2014_15a_2sg"
    source := ⟨"preminger-2014", "(15a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "ja rat x-at-ax-an ri achin"
    glossedTokens := [("ja", "FOC"), ("rat", "you(SG)"), ("x-at-ax-an", "COM-2SG.ABS-hear-AF"), ("ri", "the"), ("achin", "man")]
    glossedWords := [⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'a', 't'], ['y', 'o', 'u', '(', 'S', 'G', ')'], [⟨['r', 'a', 't'], ['y', 'o', 'u', '(', 'S', 'G', ')'], none⟩]⟩, ⟨['x', '-', 'a', 't', '-', 'a', 'x', '-', 'a', 'n'], ['C', 'O', 'M', '-', '2', 'S', 'G', '.', 'A', 'B', 'S', '-', 'h', 'e', 'a', 'r', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['a', 't'], ['2', 'S', 'G', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['a', 'x'], ['h', 'e', 'a', 'r'], some '-'⟩, ⟨['a', 'n'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['a', 'c', 'h', 'i', 'n'], ['m', 'a', 'n'], [⟨['a', 'c', 'h', 'i', 'n'], ['m', 'a', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "subject", some "rat"⟩, ⟨3, 2, "object", none⟩]
    paperFeatures := [] }

def ex_15a_3sg : Datum :=
  { id := "preminger2014_15a_3sg"
    source := ⟨"preminger-2014", "(15a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "ja rat x-Ø-ax-an ri achin"
    glossedTokens := [("ja", "FOC"), ("rat", "you(SG)"), ("x-Ø-ax-an", "COM-3SG.ABS-hear-AF"), ("ri", "the"), ("achin", "man")]
    glossedWords := [⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'a', 't'], ['y', 'o', 'u', '(', 'S', 'G', ')'], [⟨['r', 'a', 't'], ['y', 'o', 'u', '(', 'S', 'G', ')'], none⟩]⟩, ⟨['x', '-', 'Ø', '-', 'a', 'x', '-', 'a', 'n'], ['C', 'O', 'M', '-', '3', 'S', 'G', '.', 'A', 'B', 'S', '-', 'h', 'e', 'a', 'r', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['Ø'], ['3', 'S', 'G', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['a', 'x'], ['h', 'e', 'a', 'r'], some '-'⟩, ⟨['a', 'n'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['a', 'c', 'h', 'i', 'n'], ['m', 'a', 'n'], [⟨['a', 'c', 'h', 'i', 'n'], ['m', 'a', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨1, 1, "subject", some "rat"⟩, ⟨3, 2, "object", none⟩]
    paperFeatures := [] }

def ex_15b_2sg : Datum :=
  { id := "preminger2014_15b_2sg"
    source := ⟨"preminger-2014", "(15b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "ja ri achin x-at-ax-an rat"
    glossedTokens := [("ja", "FOC"), ("ri", "the"), ("achin", "man"), ("x-at-ax-an", "COM-2SG.ABS-hear-AF"), ("rat", "you(SG)")]
    glossedWords := [⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['a', 'c', 'h', 'i', 'n'], ['m', 'a', 'n'], [⟨['a', 'c', 'h', 'i', 'n'], ['m', 'a', 'n'], none⟩]⟩, ⟨['x', '-', 'a', 't', '-', 'a', 'x', '-', 'a', 'n'], ['C', 'O', 'M', '-', '2', 'S', 'G', '.', 'A', 'B', 'S', '-', 'h', 'e', 'a', 'r', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['a', 't'], ['2', 'S', 'G', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['a', 'x'], ['h', 'e', 'a', 'r'], some '-'⟩, ⟨['a', 'n'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'a', 't'], ['y', 'o', 'u', '(', 'S', 'G', ')'], [⟨['r', 'a', 't'], ['y', 'o', 'u', '(', 'S', 'G', ')'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 2, "subject", none⟩, ⟨4, 1, "object", some "rat"⟩]
    paperFeatures := [] }

def ex_15b_3sg : Datum :=
  { id := "preminger2014_15b_3sg"
    source := ⟨"preminger-2014", "(15b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "ja ri achin x-Ø-ax-an rat"
    glossedTokens := [("ja", "FOC"), ("ri", "the"), ("achin", "man"), ("x-Ø-ax-an", "COM-3SG.ABS-hear-AF"), ("rat", "you(SG)")]
    glossedWords := [⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['a', 'c', 'h', 'i', 'n'], ['m', 'a', 'n'], [⟨['a', 'c', 'h', 'i', 'n'], ['m', 'a', 'n'], none⟩]⟩, ⟨['x', '-', 'Ø', '-', 'a', 'x', '-', 'a', 'n'], ['C', 'O', 'M', '-', '3', 'S', 'G', '.', 'A', 'B', 'S', '-', 'h', 'e', 'a', 'r', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['Ø'], ['3', 'S', 'G', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['a', 'x'], ['h', 'e', 'a', 'r'], some '-'⟩, ⟨['a', 'n'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'a', 't'], ['y', 'o', 'u', '(', 'S', 'G', ')'], [⟨['r', 'a', 't'], ['y', 'o', 'u', '(', 'S', 'G', ')'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨1, 2, "subject", none⟩, ⟨4, 1, "object", some "rat"⟩]
    paperFeatures := [] }

def ex_17 : Datum :=
  { id := "preminger2014_17"
    source := ⟨"preminger-2014", "(17)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "ja rat x-at-ax-an rje'"
    glossedTokens := [("ja", "FOC"), ("rat", "you(SG)"), ("x-at-ax-an", "COM-2SG.ABS-hear-AF"), ("rje'", "them")]
    glossedWords := [⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'a', 't'], ['y', 'o', 'u', '(', 'S', 'G', ')'], [⟨['r', 'a', 't'], ['y', 'o', 'u', '(', 'S', 'G', ')'], none⟩]⟩, ⟨['x', '-', 'a', 't', '-', 'a', 'x', '-', 'a', 'n'], ['C', 'O', 'M', '-', '2', 'S', 'G', '.', 'A', 'B', 'S', '-', 'h', 'e', 'a', 'r', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['a', 't'], ['2', 'S', 'G', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['a', 'x'], ['h', 'e', 'a', 'r'], some '-'⟩, ⟨['a', 'n'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'j', 'e', '\''], ['t', 'h', 'e', 'm'], [⟨['r', 'j', 'e', '\''], ['t', 'h', 'e', 'm'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "subject", some "rat"⟩, ⟨3, 1, "object", some "rje"⟩]
    paperFeatures := [] }

def ex_18a_1sg : Datum :=
  { id := "preminger2014_18a_1sg"
    source := ⟨"preminger-2014", "(18a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "ja yïn x-in-ax-an ri achin"
    glossedTokens := [("ja", "FOC"), ("yïn", "me"), ("x-in-ax-an", "COM-1SG.ABS-hear-AF"), ("ri", "the"), ("achin", "man")]
    glossedWords := [⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['y', 'ï', 'n'], ['m', 'e'], [⟨['y', 'ï', 'n'], ['m', 'e'], none⟩]⟩, ⟨['x', '-', 'i', 'n', '-', 'a', 'x', '-', 'a', 'n'], ['C', 'O', 'M', '-', '1', 'S', 'G', '.', 'A', 'B', 'S', '-', 'h', 'e', 'a', 'r', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['i', 'n'], ['1', 'S', 'G', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['a', 'x'], ['h', 'e', 'a', 'r'], some '-'⟩, ⟨['a', 'n'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['a', 'c', 'h', 'i', 'n'], ['m', 'a', 'n'], [⟨['a', 'c', 'h', 'i', 'n'], ['m', 'a', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "subject", some "yin"⟩, ⟨3, 2, "object", none⟩]
    paperFeatures := [] }

def ex_18a_3sg : Datum :=
  { id := "preminger2014_18a_3sg"
    source := ⟨"preminger-2014", "(18a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "ja yïn x-Ø-ax-an ri achin"
    glossedTokens := [("ja", "FOC"), ("yïn", "me"), ("x-Ø-ax-an", "COM-3SG.ABS-hear-AF"), ("ri", "the"), ("achin", "man")]
    glossedWords := [⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['y', 'ï', 'n'], ['m', 'e'], [⟨['y', 'ï', 'n'], ['m', 'e'], none⟩]⟩, ⟨['x', '-', 'Ø', '-', 'a', 'x', '-', 'a', 'n'], ['C', 'O', 'M', '-', '3', 'S', 'G', '.', 'A', 'B', 'S', '-', 'h', 'e', 'a', 'r', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['Ø'], ['3', 'S', 'G', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['a', 'x'], ['h', 'e', 'a', 'r'], some '-'⟩, ⟨['a', 'n'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['a', 'c', 'h', 'i', 'n'], ['m', 'a', 'n'], [⟨['a', 'c', 'h', 'i', 'n'], ['m', 'a', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨1, 1, "subject", some "yin"⟩, ⟨3, 2, "object", none⟩]
    paperFeatures := [] }

def ex_18b_1sg : Datum :=
  { id := "preminger2014_18b_1sg"
    source := ⟨"preminger-2014", "(18b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "ja ri achin x-in-ax-an yïn"
    glossedTokens := [("ja", "FOC"), ("ri", "the"), ("achin", "man"), ("x-in-ax-an", "COM-1SG.ABS-hear-AF"), ("yïn", "me")]
    glossedWords := [⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['a', 'c', 'h', 'i', 'n'], ['m', 'a', 'n'], [⟨['a', 'c', 'h', 'i', 'n'], ['m', 'a', 'n'], none⟩]⟩, ⟨['x', '-', 'i', 'n', '-', 'a', 'x', '-', 'a', 'n'], ['C', 'O', 'M', '-', '1', 'S', 'G', '.', 'A', 'B', 'S', '-', 'h', 'e', 'a', 'r', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['i', 'n'], ['1', 'S', 'G', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['a', 'x'], ['h', 'e', 'a', 'r'], some '-'⟩, ⟨['a', 'n'], ['A', 'F'], some '-'⟩]⟩, ⟨['y', 'ï', 'n'], ['m', 'e'], [⟨['y', 'ï', 'n'], ['m', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 2, "subject", none⟩, ⟨4, 1, "object", some "yin"⟩]
    paperFeatures := [] }

def ex_18b_3sg : Datum :=
  { id := "preminger2014_18b_3sg"
    source := ⟨"preminger-2014", "(18b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "ja ri achin x-Ø-ax-an yïn"
    glossedTokens := [("ja", "FOC"), ("ri", "the"), ("achin", "man"), ("x-Ø-ax-an", "COM-3SG.ABS-hear-AF"), ("yïn", "me")]
    glossedWords := [⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['a', 'c', 'h', 'i', 'n'], ['m', 'a', 'n'], [⟨['a', 'c', 'h', 'i', 'n'], ['m', 'a', 'n'], none⟩]⟩, ⟨['x', '-', 'Ø', '-', 'a', 'x', '-', 'a', 'n'], ['C', 'O', 'M', '-', '3', 'S', 'G', '.', 'A', 'B', 'S', '-', 'h', 'e', 'a', 'r', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['Ø'], ['3', 'S', 'G', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['a', 'x'], ['h', 'e', 'a', 'r'], some '-'⟩, ⟨['a', 'n'], ['A', 'F'], some '-'⟩]⟩, ⟨['y', 'ï', 'n'], ['m', 'e'], [⟨['y', 'ï', 'n'], ['m', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨1, 2, "subject", none⟩, ⟨4, 1, "object", some "yin"⟩]
    paperFeatures := [] }

def ex_19a_3pl : Datum :=
  { id := "preminger2014_19a_3pl"
    source := ⟨"preminger-2014", "(19a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "ja rje' x-e-tz'et-ö rja'"
    glossedTokens := [("ja", "FOC"), ("rje'", "them"), ("x-e-tz'et-ö", "COM-3PL.ABS-see-AF"), ("rja'", "him")]
    glossedWords := [⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'j', 'e', '\''], ['t', 'h', 'e', 'm'], [⟨['r', 'j', 'e', '\''], ['t', 'h', 'e', 'm'], none⟩]⟩, ⟨['x', '-', 'e', '-', 't', 'z', '\'', 'e', 't', '-', 'ö'], ['C', 'O', 'M', '-', '3', 'P', 'L', '.', 'A', 'B', 'S', '-', 's', 'e', 'e', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['e'], ['3', 'P', 'L', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['t', 'z', '\'', 'e', 't'], ['s', 'e', 'e'], some '-'⟩, ⟨['ö'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'j', 'a', '\''], ['h', 'i', 'm'], [⟨['r', 'j', 'a', '\''], ['h', 'i', 'm'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "subject", some "rje"⟩, ⟨3, 1, "object", some "rja"⟩]
    paperFeatures := [] }

def ex_19a_3sg : Datum :=
  { id := "preminger2014_19a_3sg"
    source := ⟨"preminger-2014", "(19a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "ja rje' x-Ø-tz'et-ö rja'"
    glossedTokens := [("ja", "FOC"), ("rje'", "them"), ("x-Ø-tz'et-ö", "COM-3SG.ABS-see-AF"), ("rja'", "him")]
    glossedWords := [⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'j', 'e', '\''], ['t', 'h', 'e', 'm'], [⟨['r', 'j', 'e', '\''], ['t', 'h', 'e', 'm'], none⟩]⟩, ⟨['x', '-', 'Ø', '-', 't', 'z', '\'', 'e', 't', '-', 'ö'], ['C', 'O', 'M', '-', '3', 'S', 'G', '.', 'A', 'B', 'S', '-', 's', 'e', 'e', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['Ø'], ['3', 'S', 'G', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['t', 'z', '\'', 'e', 't'], ['s', 'e', 'e'], some '-'⟩, ⟨['ö'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'j', 'a', '\''], ['h', 'i', 'm'], [⟨['r', 'j', 'a', '\''], ['h', 'i', 'm'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨1, 1, "subject", some "rje"⟩, ⟨3, 1, "object", some "rja"⟩]
    paperFeatures := [] }

def ex_19b_3pl : Datum :=
  { id := "preminger2014_19b_3pl"
    source := ⟨"preminger-2014", "(19b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "ja rja' x-e-tz'et-ö rje'"
    glossedTokens := [("ja", "FOC"), ("rja'", "him"), ("x-e-tz'et-ö", "COM-3PL.ABS-see-AF"), ("rje'", "them")]
    glossedWords := [⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'j', 'a', '\''], ['h', 'i', 'm'], [⟨['r', 'j', 'a', '\''], ['h', 'i', 'm'], none⟩]⟩, ⟨['x', '-', 'e', '-', 't', 'z', '\'', 'e', 't', '-', 'ö'], ['C', 'O', 'M', '-', '3', 'P', 'L', '.', 'A', 'B', 'S', '-', 's', 'e', 'e', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['e'], ['3', 'P', 'L', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['t', 'z', '\'', 'e', 't'], ['s', 'e', 'e'], some '-'⟩, ⟨['ö'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'j', 'e', '\''], ['t', 'h', 'e', 'm'], [⟨['r', 'j', 'e', '\''], ['t', 'h', 'e', 'm'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "subject", some "rja"⟩, ⟨3, 1, "object", some "rje"⟩]
    paperFeatures := [] }

def ex_19b_3sg : Datum :=
  { id := "preminger2014_19b_3sg"
    source := ⟨"preminger-2014", "(19b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "ja rja' x-Ø-tz'et-ö rje'"
    glossedTokens := [("ja", "FOC"), ("rja'", "him"), ("x-Ø-tz'et-ö", "COM-3SG.ABS-see-AF"), ("rje'", "them")]
    glossedWords := [⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'j', 'a', '\''], ['h', 'i', 'm'], [⟨['r', 'j', 'a', '\''], ['h', 'i', 'm'], none⟩]⟩, ⟨['x', '-', 'Ø', '-', 't', 'z', '\'', 'e', 't', '-', 'ö'], ['C', 'O', 'M', '-', '3', 'S', 'G', '.', 'A', 'B', 'S', '-', 's', 'e', 'e', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['Ø'], ['3', 'S', 'G', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['t', 'z', '\'', 'e', 't'], ['s', 'e', 'e'], some '-'⟩, ⟨['ö'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'j', 'e', '\''], ['t', 'h', 'e', 'm'], [⟨['r', 'j', 'e', '\''], ['t', 'h', 'e', 'm'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨1, 1, "subject", some "rja"⟩, ⟨3, 1, "object", some "rje"⟩]
    paperFeatures := [] }

def ex_20a_1sg : Datum :=
  { id := "preminger2014_20a_1sg"
    source := ⟨"preminger-2014", "(20a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "ja rje' x-i-tz'et-ö yïn"
    glossedTokens := [("ja", "FOC"), ("rje'", "them"), ("x-i-tz'et-ö", "COM-1SG.ABS-see-AF"), ("yïn", "me")]
    glossedWords := [⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'j', 'e', '\''], ['t', 'h', 'e', 'm'], [⟨['r', 'j', 'e', '\''], ['t', 'h', 'e', 'm'], none⟩]⟩, ⟨['x', '-', 'i', '-', 't', 'z', '\'', 'e', 't', '-', 'ö'], ['C', 'O', 'M', '-', '1', 'S', 'G', '.', 'A', 'B', 'S', '-', 's', 'e', 'e', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['i'], ['1', 'S', 'G', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['t', 'z', '\'', 'e', 't'], ['s', 'e', 'e'], some '-'⟩, ⟨['ö'], ['A', 'F'], some '-'⟩]⟩, ⟨['y', 'ï', 'n'], ['m', 'e'], [⟨['y', 'ï', 'n'], ['m', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "subject", some "rje"⟩, ⟨3, 1, "object", some "yin"⟩]
    paperFeatures := [] }

def ex_20a_1pl : Datum :=
  { id := "preminger2014_20a_1pl"
    source := ⟨"preminger-2014", "(20a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "ja rje' x-oj-tz'et-ö yïn"
    glossedTokens := [("ja", "FOC"), ("rje'", "them"), ("x-oj-tz'et-ö", "COM-1PL.ABS-see-AF"), ("yïn", "me")]
    glossedWords := [⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'j', 'e', '\''], ['t', 'h', 'e', 'm'], [⟨['r', 'j', 'e', '\''], ['t', 'h', 'e', 'm'], none⟩]⟩, ⟨['x', '-', 'o', 'j', '-', 't', 'z', '\'', 'e', 't', '-', 'ö'], ['C', 'O', 'M', '-', '1', 'P', 'L', '.', 'A', 'B', 'S', '-', 's', 'e', 'e', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['o', 'j'], ['1', 'P', 'L', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['t', 'z', '\'', 'e', 't'], ['s', 'e', 'e'], some '-'⟩, ⟨['ö'], ['A', 'F'], some '-'⟩]⟩, ⟨['y', 'ï', 'n'], ['m', 'e'], [⟨['y', 'ï', 'n'], ['m', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨1, 1, "subject", some "rje"⟩, ⟨3, 1, "object", some "yin"⟩]
    paperFeatures := [] }

def ex_20b_1sg : Datum :=
  { id := "preminger2014_20b_1sg"
    source := ⟨"preminger-2014", "(20b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "ja yïn x-i-tz'et-ö rje'"
    glossedTokens := [("ja", "FOC"), ("yïn", "me"), ("x-i-tz'et-ö", "COM-1SG.ABS-see-AF"), ("rje'", "them")]
    glossedWords := [⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['y', 'ï', 'n'], ['m', 'e'], [⟨['y', 'ï', 'n'], ['m', 'e'], none⟩]⟩, ⟨['x', '-', 'i', '-', 't', 'z', '\'', 'e', 't', '-', 'ö'], ['C', 'O', 'M', '-', '1', 'S', 'G', '.', 'A', 'B', 'S', '-', 's', 'e', 'e', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['i'], ['1', 'S', 'G', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['t', 'z', '\'', 'e', 't'], ['s', 'e', 'e'], some '-'⟩, ⟨['ö'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'j', 'e', '\''], ['t', 'h', 'e', 'm'], [⟨['r', 'j', 'e', '\''], ['t', 'h', 'e', 'm'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "subject", some "yin"⟩, ⟨3, 1, "object", some "rje"⟩]
    paperFeatures := [] }

def ex_20b_1pl : Datum :=
  { id := "preminger2014_20b_1pl"
    source := ⟨"preminger-2014", "(20b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "ja yïn x-oj-tz'et-ö rje'"
    glossedTokens := [("ja", "FOC"), ("yïn", "me"), ("x-oj-tz'et-ö", "COM-1PL.ABS-see-AF"), ("rje'", "them")]
    glossedWords := [⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['y', 'ï', 'n'], ['m', 'e'], [⟨['y', 'ï', 'n'], ['m', 'e'], none⟩]⟩, ⟨['x', '-', 'o', 'j', '-', 't', 'z', '\'', 'e', 't', '-', 'ö'], ['C', 'O', 'M', '-', '1', 'P', 'L', '.', 'A', 'B', 'S', '-', 's', 'e', 'e', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['o', 'j'], ['1', 'P', 'L', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['t', 'z', '\'', 'e', 't'], ['s', 'e', 'e'], some '-'⟩, ⟨['ö'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'j', 'e', '\''], ['t', 'h', 'e', 'm'], [⟨['r', 'j', 'e', '\''], ['t', 'h', 'e', 'm'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨1, 1, "subject", some "yin"⟩, ⟨3, 1, "object", some "rje"⟩]
    paperFeatures := [] }

def ex_21a_1pl : Datum :=
  { id := "preminger2014_21a_1pl"
    source := ⟨"preminger-2014", "(21a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "ja rja' x-oj-tz'et-ö röj"
    glossedTokens := [("ja", "FOC"), ("rja'", "him"), ("x-oj-tz'et-ö", "COM-1PL.ABS-see-AF"), ("röj", "us")]
    glossedWords := [⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'j', 'a', '\''], ['h', 'i', 'm'], [⟨['r', 'j', 'a', '\''], ['h', 'i', 'm'], none⟩]⟩, ⟨['x', '-', 'o', 'j', '-', 't', 'z', '\'', 'e', 't', '-', 'ö'], ['C', 'O', 'M', '-', '1', 'P', 'L', '.', 'A', 'B', 'S', '-', 's', 'e', 'e', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['o', 'j'], ['1', 'P', 'L', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['t', 'z', '\'', 'e', 't'], ['s', 'e', 'e'], some '-'⟩, ⟨['ö'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'ö', 'j'], ['u', 's'], [⟨['r', 'ö', 'j'], ['u', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "subject", some "rja"⟩, ⟨3, 1, "object", some "roj"⟩]
    paperFeatures := [] }

def ex_21a_1sg : Datum :=
  { id := "preminger2014_21a_1sg"
    source := ⟨"preminger-2014", "(21a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "ja rja' x-i-tz'et-ö röj"
    glossedTokens := [("ja", "FOC"), ("rja'", "him"), ("x-i-tz'et-ö", "COM-1SG.ABS-see-AF"), ("röj", "us")]
    glossedWords := [⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'j', 'a', '\''], ['h', 'i', 'm'], [⟨['r', 'j', 'a', '\''], ['h', 'i', 'm'], none⟩]⟩, ⟨['x', '-', 'i', '-', 't', 'z', '\'', 'e', 't', '-', 'ö'], ['C', 'O', 'M', '-', '1', 'S', 'G', '.', 'A', 'B', 'S', '-', 's', 'e', 'e', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['i'], ['1', 'S', 'G', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['t', 'z', '\'', 'e', 't'], ['s', 'e', 'e'], some '-'⟩, ⟨['ö'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'ö', 'j'], ['u', 's'], [⟨['r', 'ö', 'j'], ['u', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨1, 1, "subject", some "rja"⟩, ⟨3, 1, "object", some "roj"⟩]
    paperFeatures := [] }

def ex_21b_1pl : Datum :=
  { id := "preminger2014_21b_1pl"
    source := ⟨"preminger-2014", "(21b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "ja röj x-oj-tz'et-ö rja'"
    glossedTokens := [("ja", "FOC"), ("röj", "us"), ("x-oj-tz'et-ö", "COM-1PL.ABS-see-AF"), ("rja'", "him")]
    glossedWords := [⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'ö', 'j'], ['u', 's'], [⟨['r', 'ö', 'j'], ['u', 's'], none⟩]⟩, ⟨['x', '-', 'o', 'j', '-', 't', 'z', '\'', 'e', 't', '-', 'ö'], ['C', 'O', 'M', '-', '1', 'P', 'L', '.', 'A', 'B', 'S', '-', 's', 'e', 'e', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['o', 'j'], ['1', 'P', 'L', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['t', 'z', '\'', 'e', 't'], ['s', 'e', 'e'], some '-'⟩, ⟨['ö'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'j', 'a', '\''], ['h', 'i', 'm'], [⟨['r', 'j', 'a', '\''], ['h', 'i', 'm'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "subject", some "roj"⟩, ⟨3, 1, "object", some "rja"⟩]
    paperFeatures := [] }

def ex_21b_1sg : Datum :=
  { id := "preminger2014_21b_1sg"
    source := ⟨"preminger-2014", "(21b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "ja röj x-i-tz'et-ö rja'"
    glossedTokens := [("ja", "FOC"), ("röj", "us"), ("x-i-tz'et-ö", "COM-1SG.ABS-see-AF"), ("rja'", "him")]
    glossedWords := [⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'ö', 'j'], ['u', 's'], [⟨['r', 'ö', 'j'], ['u', 's'], none⟩]⟩, ⟨['x', '-', 'i', '-', 't', 'z', '\'', 'e', 't', '-', 'ö'], ['C', 'O', 'M', '-', '1', 'S', 'G', '.', 'A', 'B', 'S', '-', 's', 'e', 'e', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['i'], ['1', 'S', 'G', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['t', 'z', '\'', 'e', 't'], ['s', 'e', 'e'], some '-'⟩, ⟨['ö'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'j', 'a', '\''], ['h', 'i', 'm'], [⟨['r', 'j', 'a', '\''], ['h', 'i', 'm'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨1, 1, "subject", some "roj"⟩, ⟨3, 1, "object", some "rja"⟩]
    paperFeatures := [] }

def ex_24a_1sg : Datum :=
  { id := "preminger2014_24a_1sg"
    source := ⟨"preminger-2014", "(24a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "ja rat x-in-ax-an yïn"
    glossedTokens := [("ja", "FOC"), ("rat", "you(SG)"), ("x-in-ax-an", "COM-1SG.ABS-hear-AF"), ("yïn", "me")]
    glossedWords := [⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'a', 't'], ['y', 'o', 'u', '(', 'S', 'G', ')'], [⟨['r', 'a', 't'], ['y', 'o', 'u', '(', 'S', 'G', ')'], none⟩]⟩, ⟨['x', '-', 'i', 'n', '-', 'a', 'x', '-', 'a', 'n'], ['C', 'O', 'M', '-', '1', 'S', 'G', '.', 'A', 'B', 'S', '-', 'h', 'e', 'a', 'r', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['i', 'n'], ['1', 'S', 'G', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['a', 'x'], ['h', 'e', 'a', 'r'], some '-'⟩, ⟨['a', 'n'], ['A', 'F'], some '-'⟩]⟩, ⟨['y', 'ï', 'n'], ['m', 'e'], [⟨['y', 'ï', 'n'], ['m', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨1, 1, "subject", some "rat"⟩, ⟨3, 1, "object", some "yin"⟩]
    paperFeatures := [] }

def ex_24a_2sg : Datum :=
  { id := "preminger2014_24a_2sg"
    source := ⟨"preminger-2014", "(24a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "ja rat x-at-ax-an yïn"
    glossedTokens := [("ja", "FOC"), ("rat", "you(SG)"), ("x-at-ax-an", "COM-2SG.ABS-hear-AF"), ("yïn", "me")]
    glossedWords := [⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'a', 't'], ['y', 'o', 'u', '(', 'S', 'G', ')'], [⟨['r', 'a', 't'], ['y', 'o', 'u', '(', 'S', 'G', ')'], none⟩]⟩, ⟨['x', '-', 'a', 't', '-', 'a', 'x', '-', 'a', 'n'], ['C', 'O', 'M', '-', '2', 'S', 'G', '.', 'A', 'B', 'S', '-', 'h', 'e', 'a', 'r', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['a', 't'], ['2', 'S', 'G', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['a', 'x'], ['h', 'e', 'a', 'r'], some '-'⟩, ⟨['a', 'n'], ['A', 'F'], some '-'⟩]⟩, ⟨['y', 'ï', 'n'], ['m', 'e'], [⟨['y', 'ï', 'n'], ['m', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨1, 1, "subject", some "rat"⟩, ⟨3, 1, "object", some "yin"⟩]
    paperFeatures := [] }

def ex_24a_3sg : Datum :=
  { id := "preminger2014_24a_3sg"
    source := ⟨"preminger-2014", "(24a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "ja rat x-Ø-ax-an yïn"
    glossedTokens := [("ja", "FOC"), ("rat", "you(SG)"), ("x-Ø-ax-an", "COM-3SG.ABS-hear-AF"), ("yïn", "me")]
    glossedWords := [⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'a', 't'], ['y', 'o', 'u', '(', 'S', 'G', ')'], [⟨['r', 'a', 't'], ['y', 'o', 'u', '(', 'S', 'G', ')'], none⟩]⟩, ⟨['x', '-', 'Ø', '-', 'a', 'x', '-', 'a', 'n'], ['C', 'O', 'M', '-', '3', 'S', 'G', '.', 'A', 'B', 'S', '-', 'h', 'e', 'a', 'r', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['Ø'], ['3', 'S', 'G', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['a', 'x'], ['h', 'e', 'a', 'r'], some '-'⟩, ⟨['a', 'n'], ['A', 'F'], some '-'⟩]⟩, ⟨['y', 'ï', 'n'], ['m', 'e'], [⟨['y', 'ï', 'n'], ['m', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨1, 1, "subject", some "rat"⟩, ⟨3, 1, "object", some "yin"⟩]
    paperFeatures := [] }

def ex_24b_1sg : Datum :=
  { id := "preminger2014_24b_1sg"
    source := ⟨"preminger-2014", "(24b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "ja yïn x-in-ax-an rat"
    glossedTokens := [("ja", "FOC"), ("yïn", "me"), ("x-in-ax-an", "COM-1SG.ABS-hear-AF"), ("rat", "you(SG)")]
    glossedWords := [⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['y', 'ï', 'n'], ['m', 'e'], [⟨['y', 'ï', 'n'], ['m', 'e'], none⟩]⟩, ⟨['x', '-', 'i', 'n', '-', 'a', 'x', '-', 'a', 'n'], ['C', 'O', 'M', '-', '1', 'S', 'G', '.', 'A', 'B', 'S', '-', 'h', 'e', 'a', 'r', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['i', 'n'], ['1', 'S', 'G', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['a', 'x'], ['h', 'e', 'a', 'r'], some '-'⟩, ⟨['a', 'n'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'a', 't'], ['y', 'o', 'u', '(', 'S', 'G', ')'], [⟨['r', 'a', 't'], ['y', 'o', 'u', '(', 'S', 'G', ')'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨1, 1, "subject", some "yin"⟩, ⟨3, 1, "object", some "rat"⟩]
    paperFeatures := [] }

def ex_24b_2sg : Datum :=
  { id := "preminger2014_24b_2sg"
    source := ⟨"preminger-2014", "(24b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "ja yïn x-at-ax-an rat"
    glossedTokens := [("ja", "FOC"), ("yïn", "me"), ("x-at-ax-an", "COM-2SG.ABS-hear-AF"), ("rat", "you(SG)")]
    glossedWords := [⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['y', 'ï', 'n'], ['m', 'e'], [⟨['y', 'ï', 'n'], ['m', 'e'], none⟩]⟩, ⟨['x', '-', 'a', 't', '-', 'a', 'x', '-', 'a', 'n'], ['C', 'O', 'M', '-', '2', 'S', 'G', '.', 'A', 'B', 'S', '-', 'h', 'e', 'a', 'r', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['a', 't'], ['2', 'S', 'G', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['a', 'x'], ['h', 'e', 'a', 'r'], some '-'⟩, ⟨['a', 'n'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'a', 't'], ['y', 'o', 'u', '(', 'S', 'G', ')'], [⟨['r', 'a', 't'], ['y', 'o', 'u', '(', 'S', 'G', ')'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨1, 1, "subject", some "yin"⟩, ⟨3, 1, "object", some "rat"⟩]
    paperFeatures := [] }

def ex_24b_3sg : Datum :=
  { id := "preminger2014_24b_3sg"
    source := ⟨"preminger-2014", "(24b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "ja yïn x-Ø-ax-an rat"
    glossedTokens := [("ja", "FOC"), ("yïn", "me"), ("x-Ø-ax-an", "COM-3SG.ABS-hear-AF"), ("rat", "you(SG)")]
    glossedWords := [⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['y', 'ï', 'n'], ['m', 'e'], [⟨['y', 'ï', 'n'], ['m', 'e'], none⟩]⟩, ⟨['x', '-', 'Ø', '-', 'a', 'x', '-', 'a', 'n'], ['C', 'O', 'M', '-', '3', 'S', 'G', '.', 'A', 'B', 'S', '-', 'h', 'e', 'a', 'r', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['Ø'], ['3', 'S', 'G', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['a', 'x'], ['h', 'e', 'a', 'r'], some '-'⟩, ⟨['a', 'n'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'a', 't'], ['y', 'o', 'u', '(', 'S', 'G', ')'], [⟨['r', 'a', 't'], ['y', 'o', 'u', '(', 'S', 'G', ')'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨1, 1, "subject", some "yin"⟩, ⟨3, 1, "object", some "rat"⟩]
    paperFeatures := [] }

def ex_77a : Datum :=
  { id := "preminger2014_77a"
    source := ⟨"preminger-2014", "(77a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "ja rje' x-oj-tz'et-ö röj"
    glossedTokens := [("ja", "FOC"), ("rje'", "them"), ("x-oj-tz'et-ö", "COM-1PL.ABS-see-AF"), ("röj", "us")]
    glossedWords := [⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'j', 'e', '\''], ['t', 'h', 'e', 'm'], [⟨['r', 'j', 'e', '\''], ['t', 'h', 'e', 'm'], none⟩]⟩, ⟨['x', '-', 'o', 'j', '-', 't', 'z', '\'', 'e', 't', '-', 'ö'], ['C', 'O', 'M', '-', '1', 'P', 'L', '.', 'A', 'B', 'S', '-', 's', 'e', 'e', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['o', 'j'], ['1', 'P', 'L', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['t', 'z', '\'', 'e', 't'], ['s', 'e', 'e'], some '-'⟩, ⟨['ö'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'ö', 'j'], ['u', 's'], [⟨['r', 'ö', 'j'], ['u', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "subject", some "rje"⟩, ⟨3, 1, "object", some "roj"⟩]
    paperFeatures := [] }

def ex_77b : Datum :=
  { id := "preminger2014_77b"
    source := ⟨"preminger-2014", "(77b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "ja röj x-oj-tz'et-ö rje'"
    glossedTokens := [("ja", "FOC"), ("röj", "us"), ("x-oj-tz'et-ö", "COM-1PL.ABS-see-AF"), ("rje'", "them")]
    glossedWords := [⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'ö', 'j'], ['u', 's'], [⟨['r', 'ö', 'j'], ['u', 's'], none⟩]⟩, ⟨['x', '-', 'o', 'j', '-', 't', 'z', '\'', 'e', 't', '-', 'ö'], ['C', 'O', 'M', '-', '1', 'P', 'L', '.', 'A', 'B', 'S', '-', 's', 'e', 'e', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['o', 'j'], ['1', 'P', 'L', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['t', 'z', '\'', 'e', 't'], ['s', 'e', 'e'], some '-'⟩, ⟨['ö'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'j', 'e', '\''], ['t', 'h', 'e', 'm'], [⟨['r', 'j', 'e', '\''], ['t', 'h', 'e', 'm'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "subject", some "roj"⟩, ⟨3, 1, "object", some "rje"⟩]
    paperFeatures := [] }

def all : List Datum := [ex_14a, ex_14b, ex_15a_2sg, ex_15a_3sg, ex_15b_2sg, ex_15b_3sg, ex_17, ex_18a_1sg, ex_18a_3sg, ex_18b_1sg, ex_18b_3sg, ex_19a_3pl, ex_19a_3sg, ex_19b_3pl, ex_19b_3sg, ex_20a_1sg, ex_20a_1pl, ex_20b_1sg, ex_20b_1pl, ex_21a_1pl, ex_21a_1sg, ex_21b_1pl, ex_21b_1sg, ex_24a_1sg, ex_24a_2sg, ex_24a_3sg, ex_24b_1sg, ex_24b_2sg, ex_24b_3sg, ex_77a, ex_77b]

/-- The two core arguments of the Agent-Focus clause. -/
inductive SpanLabel where
  /-- subject: the focused agent, before the verb -/
  | subject
  /-- object: the patient, after the verb -/
  | object
  deriving DecidableEq, Repr, Fintype

/-- The label of a span, where it is a declared one. -/
def label? (p : Datum.Span) : Option SpanLabel :=
  List.lookup p.label [("subject", .subject), ("object", .object)]

/-- The strong pronouns of the rows. -/
inductive Lexeme where
  /-- yin: the first person singular yïn -/
  | yin
  /-- rat: the second person singular rat -/
  | rat
  /-- rja: the third person singular rja' -/
  | rja
  /-- roj: the first person plural röj -/
  | roj
  /-- rje: the third person plural rje' -/
  | rje
  deriving DecidableEq, Repr, Fintype

/-- The lexeme a span is a form of, where it names a declared one. -/
def lexeme? (p : Datum.Span) : Option Lexeme :=
  p.lexeme.bind (List.lookup · [("yin", .yin), ("rat", .rat), ("rja", .rja), ("roj", .roj), ("rje", .rje)])

end Preminger2014.Examples
