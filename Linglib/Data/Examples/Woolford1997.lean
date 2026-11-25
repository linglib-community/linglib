module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Woolford1997` — typed example data

Auto-generated from `Linglib/Data/Examples/Woolford1997.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Woolford1997.Examples`.
-/

@[expose] public section

namespace Woolford1997.Examples

def ex_3 : Datum :=
  { id := "woolford1997_3"
    source := ⟨"woolford-1997", "(3)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "'ipí-Ø hi-kú-ye."
    glossedTokens := [("'ipí-Ø", "he-NOM"), ("hi-kú-ye", "3-go-ASP")]
    glossedWords := [⟨['\'', 'i', 'p', 'í', '-', 'Ø'], ['h', 'e', '-', 'N', 'O', 'M'], [⟨['\'', 'i', 'p', 'í'], ['h', 'e'], none⟩, ⟨['Ø'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['h', 'i', '-', 'k', 'ú', '-', 'y', 'e'], ['3', '-', 'g', 'o', '-', 'A', 'S', 'P'], [⟨['h', 'i'], ['3'], none⟩, ⟨['k', 'ú'], ['g', 'o'], some '-'⟩, ⟨['y', 'e'], ['A', 'S', 'P'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "nominative"), ("phi", "3sg"), ("prefix", "hi")] }

def ex_4 : Datum :=
  { id := "woolford1997_4"
    source := ⟨"woolford-1997", "(4)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Háama-Ø hi-'wí-ye wewúkiye-Ø."
    glossedTokens := [("Háama-Ø", "man-NOM"), ("hi-'wí-ye", "3-shoot-ASP"), ("wewúkiye-Ø", "elk-ACC")]
    glossedWords := [⟨['H', 'á', 'a', 'm', 'a', '-', 'Ø'], ['m', 'a', 'n', '-', 'N', 'O', 'M'], [⟨['H', 'á', 'a', 'm', 'a'], ['m', 'a', 'n'], none⟩, ⟨['Ø'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['h', 'i', '-', '\'', 'w', 'í', '-', 'y', 'e'], ['3', '-', 's', 'h', 'o', 'o', 't', '-', 'A', 'S', 'P'], [⟨['h', 'i'], ['3'], none⟩, ⟨['\'', 'w', 'í'], ['s', 'h', 'o', 'o', 't'], some '-'⟩, ⟨['y', 'e'], ['A', 'S', 'P'], some '-'⟩]⟩, ⟨['w', 'e', 'w', 'ú', 'k', 'i', 'y', 'e', '-', 'Ø'], ['e', 'l', 'k', '-', 'A', 'C', 'C'], [⟨['w', 'e', 'w', 'ú', 'k', 'i', 'y', 'e'], ['e', 'l', 'k'], none⟩, ⟨['Ø'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "nominative"), ("case", "accusative"), ("phi", "3sg"), ("phi", "3sg"), ("prefix", "hi")] }

def ex_5 : Datum :=
  { id := "woolford1997_5"
    source := ⟨"woolford-1997", "(5)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Háama-nm pée-'wi-ye wewúkiye-ne."
    glossedTokens := [("Háama-nm", "man-ERG"), ("pée-'wi-ye", "3/3-shoot-ASP"), ("wewúkiye-ne", "elk-OBJ")]
    glossedWords := [⟨['H', 'á', 'a', 'm', 'a', '-', 'n', 'm'], ['m', 'a', 'n', '-', 'E', 'R', 'G'], [⟨['H', 'á', 'a', 'm', 'a'], ['m', 'a', 'n'], none⟩, ⟨['n', 'm'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['p', 'é', 'e', '-', '\'', 'w', 'i', '-', 'y', 'e'], ['3', '/', '3', '-', 's', 'h', 'o', 'o', 't', '-', 'A', 'S', 'P'], [⟨['p', 'é', 'e'], ['3', '/', '3'], none⟩, ⟨['\'', 'w', 'i'], ['s', 'h', 'o', 'o', 't'], some '-'⟩, ⟨['y', 'e'], ['A', 'S', 'P'], some '-'⟩]⟩, ⟨['w', 'e', 'w', 'ú', 'k', 'i', 'y', 'e', '-', 'n', 'e'], ['e', 'l', 'k', '-', 'O', 'B', 'J'], [⟨['w', 'e', 'w', 'ú', 'k', 'i', 'y', 'e'], ['e', 'l', 'k'], none⟩, ⟨['n', 'e'], ['O', 'B', 'J'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "ergative"), ("case", "objective"), ("phi", "3sg"), ("phi", "3sg"), ("prefix", "pée")] }

def ex_6 : Datum :=
  { id := "woolford1997_6"
    source := ⟨"woolford-1997", "(6)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "ʔáayat-Ø hi-ʔni-ye tíim'es-Ø háama-Ø."
    glossedTokens := [("ʔáayat-Ø", "woman-NOM"), ("hi-ʔni-ye", "3-give-PAST"), ("tíim'es-Ø", "book-ACC"), ("háama-Ø", "man/husband-ACC")]
    glossedWords := [⟨['ʔ', 'á', 'a', 'y', 'a', 't', '-', 'Ø'], ['w', 'o', 'm', 'a', 'n', '-', 'N', 'O', 'M'], [⟨['ʔ', 'á', 'a', 'y', 'a', 't'], ['w', 'o', 'm', 'a', 'n'], none⟩, ⟨['Ø'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['h', 'i', '-', 'ʔ', 'n', 'i', '-', 'y', 'e'], ['3', '-', 'g', 'i', 'v', 'e', '-', 'P', 'A', 'S', 'T'], [⟨['h', 'i'], ['3'], none⟩, ⟨['ʔ', 'n', 'i'], ['g', 'i', 'v', 'e'], some '-'⟩, ⟨['y', 'e'], ['P', 'A', 'S', 'T'], some '-'⟩]⟩, ⟨['t', 'í', 'i', 'm', '\'', 'e', 's', '-', 'Ø'], ['b', 'o', 'o', 'k', '-', 'A', 'C', 'C'], [⟨['t', 'í', 'i', 'm', '\'', 'e', 's'], ['b', 'o', 'o', 'k'], none⟩, ⟨['Ø'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['h', 'á', 'a', 'm', 'a', '-', 'Ø'], ['m', 'a', 'n', '/', 'h', 'u', 's', 'b', 'a', 'n', 'd', '-', 'A', 'C', 'C'], [⟨['h', 'á', 'a', 'm', 'a'], ['m', 'a', 'n', '/', 'h', 'u', 's', 'b', 'a', 'n', 'd'], none⟩, ⟨['Ø'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "nominative"), ("case", "accusative"), ("case", "accusative"), ("phi", "3sg"), ("phi", "3sg"), ("phi", "3sg"), ("prefix", "hi")] }

def ex_7 : Datum :=
  { id := "woolford1997_7"
    source := ⟨"woolford-1997", "(7)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "ʔáayato-m pée-ʔni-ye tíim'es-Ø háama-na."
    glossedTokens := [("ʔáayato-m", "woman-ERG"), ("pée-ʔni-ye", "3/3-give-PAST"), ("tíim'es-Ø", "book-ACC"), ("háama-na", "man-OBJ")]
    glossedWords := [⟨['ʔ', 'á', 'a', 'y', 'a', 't', 'o', '-', 'm'], ['w', 'o', 'm', 'a', 'n', '-', 'E', 'R', 'G'], [⟨['ʔ', 'á', 'a', 'y', 'a', 't', 'o'], ['w', 'o', 'm', 'a', 'n'], none⟩, ⟨['m'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['p', 'é', 'e', '-', 'ʔ', 'n', 'i', '-', 'y', 'e'], ['3', '/', '3', '-', 'g', 'i', 'v', 'e', '-', 'P', 'A', 'S', 'T'], [⟨['p', 'é', 'e'], ['3', '/', '3'], none⟩, ⟨['ʔ', 'n', 'i'], ['g', 'i', 'v', 'e'], some '-'⟩, ⟨['y', 'e'], ['P', 'A', 'S', 'T'], some '-'⟩]⟩, ⟨['t', 'í', 'i', 'm', '\'', 'e', 's', '-', 'Ø'], ['b', 'o', 'o', 'k', '-', 'A', 'C', 'C'], [⟨['t', 'í', 'i', 'm', '\'', 'e', 's'], ['b', 'o', 'o', 'k'], none⟩, ⟨['Ø'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['h', 'á', 'a', 'm', 'a', '-', 'n', 'a'], ['m', 'a', 'n', '-', 'O', 'B', 'J'], [⟨['h', 'á', 'a', 'm', 'a'], ['m', 'a', 'n'], none⟩, ⟨['n', 'a'], ['O', 'B', 'J'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "ergative"), ("case", "objective"), ("case", "accusative"), ("phi", "3sg"), ("phi", "3sg"), ("phi", "3sg"), ("prefix", "pée")] }

def ex_8 : Datum :=
  { id := "woolford1997_8"
    source := ⟨"woolford-1997", "(8)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "ʔáayato-m pée-ʔni-ye haswaláya-na háama-na."
    glossedTokens := [("ʔáayato-m", "woman-ERG"), ("pée-ʔni-ye", "3/3-give-PAST"), ("haswaláya-na", "slave-OBJ"), ("háama-na", "man-DAT")]
    glossedWords := [⟨['ʔ', 'á', 'a', 'y', 'a', 't', 'o', '-', 'm'], ['w', 'o', 'm', 'a', 'n', '-', 'E', 'R', 'G'], [⟨['ʔ', 'á', 'a', 'y', 'a', 't', 'o'], ['w', 'o', 'm', 'a', 'n'], none⟩, ⟨['m'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['p', 'é', 'e', '-', 'ʔ', 'n', 'i', '-', 'y', 'e'], ['3', '/', '3', '-', 'g', 'i', 'v', 'e', '-', 'P', 'A', 'S', 'T'], [⟨['p', 'é', 'e'], ['3', '/', '3'], none⟩, ⟨['ʔ', 'n', 'i'], ['g', 'i', 'v', 'e'], some '-'⟩, ⟨['y', 'e'], ['P', 'A', 'S', 'T'], some '-'⟩]⟩, ⟨['h', 'a', 's', 'w', 'a', 'l', 'á', 'y', 'a', '-', 'n', 'a'], ['s', 'l', 'a', 'v', 'e', '-', 'O', 'B', 'J'], [⟨['h', 'a', 's', 'w', 'a', 'l', 'á', 'y', 'a'], ['s', 'l', 'a', 'v', 'e'], none⟩, ⟨['n', 'a'], ['O', 'B', 'J'], some '-'⟩]⟩, ⟨['h', 'á', 'a', 'm', 'a', '-', 'n', 'a'], ['m', 'a', 'n', '-', 'D', 'A', 'T'], [⟨['h', 'á', 'a', 'm', 'a'], ['m', 'a', 'n'], none⟩, ⟨['n', 'a'], ['D', 'A', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "ergative"), ("case", "dative"), ("case", "objective"), ("phi", "3sg"), ("phi", "3sg"), ("phi", "3sg"), ("prefix", "pée")] }

def ex_16A1 : Datum :=
  { id := "woolford1997_16A1"
    source := ⟨"woolford-1997", "(16A.1)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Nominative Accusative."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "nominative"), ("case", "accusative")] }

def ex_16A2 : Datum :=
  { id := "woolford1997_16A2"
    source := ⟨"woolford-1997", "(16A.2)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Ergative Objective."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "ergative"), ("case", "objective")] }

def ex_16B1 : Datum :=
  { id := "woolford1997_16B1"
    source := ⟨"woolford-1997", "(16B.1)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Nominative Objective."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("case", "nominative"), ("case", "objective")] }

def ex_16B2 : Datum :=
  { id := "woolford1997_16B2"
    source := ⟨"woolford-1997", "(16B.2)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Ergative Accusative."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("case", "ergative"), ("case", "accusative")] }

def ex_22A1 : Datum :=
  { id := "woolford1997_22A1"
    source := ⟨"woolford-1997", "(22A.1)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Nominative Accusative Accusative."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "nominative"), ("case", "accusative"), ("case", "accusative")] }

def ex_22A2 : Datum :=
  { id := "woolford1997_22A2"
    source := ⟨"woolford-1997", "(22A.2)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Nominative Dative Accusative."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "nominative"), ("case", "dative"), ("case", "accusative")] }

def ex_22A3 : Datum :=
  { id := "woolford1997_22A3"
    source := ⟨"woolford-1997", "(22A.3)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Ergative Objective Accusative."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "ergative"), ("case", "objective"), ("case", "accusative")] }

def ex_22A4 : Datum :=
  { id := "woolford1997_22A4"
    source := ⟨"woolford-1997", "(22A.4)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Ergative Dative Objective."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "ergative"), ("case", "dative"), ("case", "objective")] }

def ex_22B1 : Datum :=
  { id := "woolford1997_22B1"
    source := ⟨"woolford-1997", "(22B.1)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Nominative Objective Objective."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("case", "nominative"), ("case", "objective"), ("case", "objective")] }

def ex_22B2 : Datum :=
  { id := "woolford1997_22B2"
    source := ⟨"woolford-1997", "(22B.2)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Nominative Objective Accusative."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("case", "nominative"), ("case", "objective"), ("case", "accusative")] }

def ex_22B3 : Datum :=
  { id := "woolford1997_22B3"
    source := ⟨"woolford-1997", "(22B.3)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Nominative Accusative Objective."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("case", "nominative"), ("case", "accusative"), ("case", "objective")] }

def ex_22B4 : Datum :=
  { id := "woolford1997_22B4"
    source := ⟨"woolford-1997", "(22B.4)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Nominative Dative Objective."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("case", "nominative"), ("case", "dative"), ("case", "objective")] }

def ex_22B5 : Datum :=
  { id := "woolford1997_22B5"
    source := ⟨"woolford-1997", "(22B.5)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Ergative Accusative Accusative."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("case", "ergative"), ("case", "accusative"), ("case", "accusative")] }

def ex_22B6 : Datum :=
  { id := "woolford1997_22B6"
    source := ⟨"woolford-1997", "(22B.6)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Ergative Accusative Objective."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("case", "ergative"), ("case", "accusative"), ("case", "objective")] }

def ex_22B7 : Datum :=
  { id := "woolford1997_22B7"
    source := ⟨"woolford-1997", "(22B.7)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Ergative Objective Objective."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("case", "ergative"), ("case", "objective"), ("case", "objective")] }

def ex_22B8 : Datum :=
  { id := "woolford1997_22B8"
    source := ⟨"woolford-1997", "(22B.8)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Ergative Dative Accusative."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("case", "ergative"), ("case", "dative"), ("case", "accusative")] }

def ex_29a : Datum :=
  { id := "woolford1997_29a"
    source := ⟨"woolford-1997", "(29a)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Hi-kúu-se."
    glossedTokens := [("Hi-kúu-se", "3-go-ASP/SG")]
    glossedWords := [⟨['H', 'i', '-', 'k', 'ú', 'u', '-', 's', 'e'], ['3', '-', 'g', 'o', '-', 'A', 'S', 'P', '/', 'S', 'G'], [⟨['H', 'i'], ['3'], none⟩, ⟨['k', 'ú', 'u'], ['g', 'o'], some '-'⟩, ⟨['s', 'e'], ['A', 'S', 'P', '/', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "nominative"), ("phi", "3sg"), ("prefix", "hi")] }

def ex_29b : Datum :=
  { id := "woolford1997_29b"
    source := ⟨"woolford-1997", "(29b)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Hi-ku-síix."
    glossedTokens := [("Hi-ku-síix", "3-go-ASP/PL")]
    glossedWords := [⟨['H', 'i', '-', 'k', 'u', '-', 's', 'í', 'i', 'x'], ['3', '-', 'g', 'o', '-', 'A', 'S', 'P', '/', 'P', 'L'], [⟨['H', 'i'], ['3'], none⟩, ⟨['k', 'u'], ['g', 'o'], some '-'⟩, ⟨['s', 'í', 'i', 'x'], ['A', 'S', 'P', '/', 'P', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "nominative"), ("phi", "3pl"), ("prefix", "hi")] }

def ex_30a : Datum :=
  { id := "woolford1997_30a"
    source := ⟨"woolford-1997", "(30a)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Pée-ke'nip-se."
    glossedTokens := [("Pée-ke'nip-se", "3/3-bite-ASP/SG")]
    glossedWords := [⟨['P', 'é', 'e', '-', 'k', 'e', '\'', 'n', 'i', 'p', '-', 's', 'e'], ['3', '/', '3', '-', 'b', 'i', 't', 'e', '-', 'A', 'S', 'P', '/', 'S', 'G'], [⟨['P', 'é', 'e'], ['3', '/', '3'], none⟩, ⟨['k', 'e', '\'', 'n', 'i', 'p'], ['b', 'i', 't', 'e'], some '-'⟩, ⟨['s', 'e'], ['A', 'S', 'P', '/', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "ergative"), ("case", "objective"), ("phi", "3sg"), ("phi", "3sg"), ("prefix", "pée")] }

def ex_30b : Datum :=
  { id := "woolford1997_30b"
    source := ⟨"woolford-1997", "(30b)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Pée-ke'nip-six."
    glossedTokens := [("Pée-ke'nip-six", "3/3-bite-ASP/PL")]
    glossedWords := [⟨['P', 'é', 'e', '-', 'k', 'e', '\'', 'n', 'i', 'p', '-', 's', 'i', 'x'], ['3', '/', '3', '-', 'b', 'i', 't', 'e', '-', 'A', 'S', 'P', '/', 'P', 'L'], [⟨['P', 'é', 'e'], ['3', '/', '3'], none⟩, ⟨['k', 'e', '\'', 'n', 'i', 'p'], ['b', 'i', 't', 'e'], some '-'⟩, ⟨['s', 'i', 'x'], ['A', 'S', 'P', '/', 'P', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "ergative"), ("case", "objective"), ("phi", "3pl"), ("phi", "3sg"), ("prefix", "pée")] }

def ex_31a : Datum :=
  { id := "woolford1997_31a"
    source := ⟨"woolford-1997", "(31a)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Hi-kú-ye."
    glossedTokens := [("Hi-kú-ye", "3-go-ASP")]
    glossedWords := [⟨['H', 'i', '-', 'k', 'ú', '-', 'y', 'e'], ['3', '-', 'g', 'o', '-', 'A', 'S', 'P'], [⟨['H', 'i'], ['3'], none⟩, ⟨['k', 'ú'], ['g', 'o'], some '-'⟩, ⟨['y', 'e'], ['A', 'S', 'P'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "nominative"), ("phi", "3sg"), ("prefix", "hi")] }

def ex_31b : Datum :=
  { id := "woolford1997_31b"
    source := ⟨"woolford-1997", "(31b)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Hi-pe-kú-ye."
    glossedTokens := [("Hi-pe-kú-ye", "3-PL.SUBJ-go-ASP")]
    glossedWords := [⟨['H', 'i', '-', 'p', 'e', '-', 'k', 'ú', '-', 'y', 'e'], ['3', '-', 'P', 'L', '.', 'S', 'U', 'B', 'J', '-', 'g', 'o', '-', 'A', 'S', 'P'], [⟨['H', 'i'], ['3'], none⟩, ⟨['p', 'e'], ['P', 'L', '.', 'S', 'U', 'B', 'J'], some '-'⟩, ⟨['k', 'ú'], ['g', 'o'], some '-'⟩, ⟨['y', 'e'], ['A', 'S', 'P'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "nominative"), ("phi", "3pl"), ("prefix", "hi")] }

def ex_32 : Datum :=
  { id := "woolford1997_32"
    source := ⟨"woolford-1997", "(32)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Pée-pe-ke'nip-e."
    glossedTokens := [("Pée-pe-ke'nip-e", "3/3-PL.SUBJ-bite-ASP")]
    glossedWords := [⟨['P', 'é', 'e', '-', 'p', 'e', '-', 'k', 'e', '\'', 'n', 'i', 'p', '-', 'e'], ['3', '/', '3', '-', 'P', 'L', '.', 'S', 'U', 'B', 'J', '-', 'b', 'i', 't', 'e', '-', 'A', 'S', 'P'], [⟨['P', 'é', 'e'], ['3', '/', '3'], none⟩, ⟨['p', 'e'], ['P', 'L', '.', 'S', 'U', 'B', 'J'], some '-'⟩, ⟨['k', 'e', '\'', 'n', 'i', 'p'], ['b', 'i', 't', 'e'], some '-'⟩, ⟨['e'], ['A', 'S', 'P'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "ergative"), ("case", "objective"), ("phi", "3pl"), ("phi", "3sg"), ("prefix", "pée")] }

def ex_33 : Datum :=
  { id := "woolford1997_33"
    source := ⟨"woolford-1997", "(33)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "'e-pe-nées-hexn-e."
    glossedTokens := [("'e-pe-nées-hexn-e", "1/3-PL.SUBJ-PL.OBJ-see-ASP")]
    glossedWords := [⟨['\'', 'e', '-', 'p', 'e', '-', 'n', 'é', 'e', 's', '-', 'h', 'e', 'x', 'n', '-', 'e'], ['1', '/', '3', '-', 'P', 'L', '.', 'S', 'U', 'B', 'J', '-', 'P', 'L', '.', 'O', 'B', 'J', '-', 's', 'e', 'e', '-', 'A', 'S', 'P'], [⟨['\'', 'e'], ['1', '/', '3'], none⟩, ⟨['p', 'e'], ['P', 'L', '.', 'S', 'U', 'B', 'J'], some '-'⟩, ⟨['n', 'é', 'e', 's'], ['P', 'L', '.', 'O', 'B', 'J'], some '-'⟩, ⟨['h', 'e', 'x', 'n'], ['s', 'e', 'e'], some '-'⟩, ⟨['e'], ['A', 'S', 'P'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "ergative"), ("case", "objective"), ("phi", "1pl"), ("phi", "3pl"), ("prefix", "'e")] }

def ex_34 : Datum :=
  { id := "woolford1997_34"
    source := ⟨"woolford-1997", "(34)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Háama-nm hi-néec-'wi-ye wewúkiye-ne."
    glossedTokens := [("Háama-nm", "man-ERG"), ("hi-néec-'wi-ye", "3-PL.OBJ-shoot-ASP"), ("wewúkiye-ne", "elk-OBJ")]
    glossedWords := [⟨['H', 'á', 'a', 'm', 'a', '-', 'n', 'm'], ['m', 'a', 'n', '-', 'E', 'R', 'G'], [⟨['H', 'á', 'a', 'm', 'a'], ['m', 'a', 'n'], none⟩, ⟨['n', 'm'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['h', 'i', '-', 'n', 'é', 'e', 'c', '-', '\'', 'w', 'i', '-', 'y', 'e'], ['3', '-', 'P', 'L', '.', 'O', 'B', 'J', '-', 's', 'h', 'o', 'o', 't', '-', 'A', 'S', 'P'], [⟨['h', 'i'], ['3'], none⟩, ⟨['n', 'é', 'e', 'c'], ['P', 'L', '.', 'O', 'B', 'J'], some '-'⟩, ⟨['\'', 'w', 'i'], ['s', 'h', 'o', 'o', 't'], some '-'⟩, ⟨['y', 'e'], ['A', 'S', 'P'], some '-'⟩]⟩, ⟨['w', 'e', 'w', 'ú', 'k', 'i', 'y', 'e', '-', 'n', 'e'], ['e', 'l', 'k', '-', 'O', 'B', 'J'], [⟨['w', 'e', 'w', 'ú', 'k', 'i', 'y', 'e'], ['e', 'l', 'k'], none⟩, ⟨['n', 'e'], ['O', 'B', 'J'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "ergative"), ("case", "objective"), ("phi", "3sg"), ("phi", "3pl"), ("prefix", "hi")] }

def ex_37 : Datum :=
  { id := "woolford1997_37"
    source := ⟨"woolford-1997", "(37)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Hi-táamyan-a 'áatway-nim."
    glossedTokens := [("Hi-táamyan-a", "3/1-hit-ASP"), ("'áatway-nim", "old.woman-ERG")]
    glossedWords := [⟨['H', 'i', '-', 't', 'á', 'a', 'm', 'y', 'a', 'n', '-', 'a'], ['3', '/', '1', '-', 'h', 'i', 't', '-', 'A', 'S', 'P'], [⟨['H', 'i'], ['3', '/', '1'], none⟩, ⟨['t', 'á', 'a', 'm', 'y', 'a', 'n'], ['h', 'i', 't'], some '-'⟩, ⟨['a'], ['A', 'S', 'P'], some '-'⟩]⟩, ⟨['\'', 'á', 'a', 't', 'w', 'a', 'y', '-', 'n', 'i', 'm'], ['o', 'l', 'd', '.', 'w', 'o', 'm', 'a', 'n', '-', 'E', 'R', 'G'], [⟨['\'', 'á', 'a', 't', 'w', 'a', 'y'], ['o', 'l', 'd', '.', 'w', 'o', 'm', 'a', 'n'], none⟩, ⟨['n', 'i', 'm'], ['E', 'R', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "ergative"), ("case", "objective"), ("phi", "3sg"), ("phi", "1sg"), ("prefix", "hi")] }

def ex_39 : Datum :=
  { id := "woolford1997_39"
    source := ⟨"woolford-1997", "(39)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "'ip-ním pée-hexn-e walás-na."
    glossedTokens := [("'ip-ním", "he-ERG"), ("pée-hexn-e", "3/3-see-ASP"), ("walás-na", "knife-OBJ")]
    glossedWords := [⟨['\'', 'i', 'p', '-', 'n', 'í', 'm'], ['h', 'e', '-', 'E', 'R', 'G'], [⟨['\'', 'i', 'p'], ['h', 'e'], none⟩, ⟨['n', 'í', 'm'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['p', 'é', 'e', '-', 'h', 'e', 'x', 'n', '-', 'e'], ['3', '/', '3', '-', 's', 'e', 'e', '-', 'A', 'S', 'P'], [⟨['p', 'é', 'e'], ['3', '/', '3'], none⟩, ⟨['h', 'e', 'x', 'n'], ['s', 'e', 'e'], some '-'⟩, ⟨['e'], ['A', 'S', 'P'], some '-'⟩]⟩, ⟨['w', 'a', 'l', 'á', 's', '-', 'n', 'a'], ['k', 'n', 'i', 'f', 'e', '-', 'O', 'B', 'J'], [⟨['w', 'a', 'l', 'á', 's'], ['k', 'n', 'i', 'f', 'e'], none⟩, ⟨['n', 'a'], ['O', 'B', 'J'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "ergative"), ("case", "objective"), ("phi", "3sg"), ("phi", "3sg"), ("prefix", "pée")] }

def ex_40 : Datum :=
  { id := "woolford1997_40"
    source := ⟨"woolford-1997", "(40)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "'íin 'e-nées-hexn-e walás-na."
    glossedTokens := [("'íin", "I"), ("'e-nées-hexn-e", "1/3-PL.OBJ-see-ASP"), ("walás-na", "knife-OBJ")]
    glossedWords := [⟨['\'', 'í', 'i', 'n'], ['I'], [⟨['\'', 'í', 'i', 'n'], ['I'], none⟩]⟩, ⟨['\'', 'e', '-', 'n', 'é', 'e', 's', '-', 'h', 'e', 'x', 'n', '-', 'e'], ['1', '/', '3', '-', 'P', 'L', '.', 'O', 'B', 'J', '-', 's', 'e', 'e', '-', 'A', 'S', 'P'], [⟨['\'', 'e'], ['1', '/', '3'], none⟩, ⟨['n', 'é', 'e', 's'], ['P', 'L', '.', 'O', 'B', 'J'], some '-'⟩, ⟨['h', 'e', 'x', 'n'], ['s', 'e', 'e'], some '-'⟩, ⟨['e'], ['A', 'S', 'P'], some '-'⟩]⟩, ⟨['w', 'a', 'l', 'á', 's', '-', 'n', 'a'], ['k', 'n', 'i', 'f', 'e', '-', 'O', 'B', 'J'], [⟨['w', 'a', 'l', 'á', 's'], ['k', 'n', 'i', 'f', 'e'], none⟩, ⟨['n', 'a'], ['O', 'B', 'J'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "ergative"), ("case", "objective"), ("phi", "1sg"), ("phi", "3pl"), ("prefix", "'e")] }

def ex_41 : Datum :=
  { id := "woolford1997_41"
    source := ⟨"woolford-1997", "(41)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "'ee 'aw-'yáax̣n-o'qa ku's-pé wex̣weqé-ne titlúu-ne."
    glossedTokens := [("'ee", "you"), ("'aw-'yáax̣n-o'qa", "2/3-can-find"), ("ku's-pé", "places-in"), ("wex̣weqé-ne", "frog-OBJ"), ("titlúu-ne", "big-OBJ")]
    glossedWords := [⟨['\'', 'e', 'e'], ['y', 'o', 'u'], [⟨['\'', 'e', 'e'], ['y', 'o', 'u'], none⟩]⟩, ⟨['\'', 'a', 'w', '-', '\'', 'y', 'á', 'a', 'x', '̣', 'n', '-', 'o', '\'', 'q', 'a'], ['2', '/', '3', '-', 'c', 'a', 'n', '-', 'f', 'i', 'n', 'd'], [⟨['\'', 'a', 'w'], ['2', '/', '3'], none⟩, ⟨['\'', 'y', 'á', 'a', 'x', '̣', 'n'], ['c', 'a', 'n'], some '-'⟩, ⟨['o', '\'', 'q', 'a'], ['f', 'i', 'n', 'd'], some '-'⟩]⟩, ⟨['k', 'u', '\'', 's', '-', 'p', 'é'], ['p', 'l', 'a', 'c', 'e', 's', '-', 'i', 'n'], [⟨['k', 'u', '\'', 's'], ['p', 'l', 'a', 'c', 'e', 's'], none⟩, ⟨['p', 'é'], ['i', 'n'], some '-'⟩]⟩, ⟨['w', 'e', 'x', '̣', 'w', 'e', 'q', 'é', '-', 'n', 'e'], ['f', 'r', 'o', 'g', '-', 'O', 'B', 'J'], [⟨['w', 'e', 'x', '̣', 'w', 'e', 'q', 'é'], ['f', 'r', 'o', 'g'], none⟩, ⟨['n', 'e'], ['O', 'B', 'J'], some '-'⟩]⟩, ⟨['t', 'i', 't', 'l', 'ú', 'u', '-', 'n', 'e'], ['b', 'i', 'g', '-', 'O', 'B', 'J'], [⟨['t', 'i', 't', 'l', 'ú', 'u'], ['b', 'i', 'g'], none⟩, ⟨['n', 'e'], ['O', 'B', 'J'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "ergative"), ("case", "objective"), ("phi", "2sg"), ("phi", "3sg"), ("prefix", "'e")] }

def ex_42 : Datum :=
  { id := "woolford1997_42"
    source := ⟨"woolford-1997", "(42)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Kii héeneku' céep-Ø hi-'níp-e háacwal-Ø."
    glossedTokens := [("Kii", "now"), ("héeneku'", "again"), ("céep-Ø", "arrow-ACC"), ("hi-'níp-e", "3-take-ASP"), ("háacwal-Ø", "boy-NOM")]
    glossedWords := [⟨['K', 'i', 'i'], ['n', 'o', 'w'], [⟨['K', 'i', 'i'], ['n', 'o', 'w'], none⟩]⟩, ⟨['h', 'é', 'e', 'n', 'e', 'k', 'u', '\''], ['a', 'g', 'a', 'i', 'n'], [⟨['h', 'é', 'e', 'n', 'e', 'k', 'u', '\''], ['a', 'g', 'a', 'i', 'n'], none⟩]⟩, ⟨['c', 'é', 'e', 'p', '-', 'Ø'], ['a', 'r', 'r', 'o', 'w', '-', 'A', 'C', 'C'], [⟨['c', 'é', 'e', 'p'], ['a', 'r', 'r', 'o', 'w'], none⟩, ⟨['Ø'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['h', 'i', '-', '\'', 'n', 'í', 'p', '-', 'e'], ['3', '-', 't', 'a', 'k', 'e', '-', 'A', 'S', 'P'], [⟨['h', 'i'], ['3'], none⟩, ⟨['\'', 'n', 'í', 'p'], ['t', 'a', 'k', 'e'], some '-'⟩, ⟨['e'], ['A', 'S', 'P'], some '-'⟩]⟩, ⟨['h', 'á', 'a', 'c', 'w', 'a', 'l', '-', 'Ø'], ['b', 'o', 'y', '-', 'N', 'O', 'M'], [⟨['h', 'á', 'a', 'c', 'w', 'a', 'l'], ['b', 'o', 'y'], none⟩, ⟨['Ø'], ['N', 'O', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "nominative"), ("case", "accusative"), ("phi", "3sg"), ("phi", "3sg"), ("prefix", "hi")] }

def ex_43 : Datum :=
  { id := "woolford1997_43"
    source := ⟨"woolford-1997", "(43)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Kawá tax̣c qáamsit-Ø Ø-wiyáamk-o' kaa Ø-túut-nu'."
    glossedTokens := [("Kawá", "then"), ("tax̣c", "soon"), ("qáamsit-Ø", "qáamsit-ACC"), ("Ø-wiyáamk-o'", "1-peel-ASP"), ("kaa", "and"), ("Ø-túut-nu'", "1-grind-ASP")]
    glossedWords := [⟨['K', 'a', 'w', 'á'], ['t', 'h', 'e', 'n'], [⟨['K', 'a', 'w', 'á'], ['t', 'h', 'e', 'n'], none⟩]⟩, ⟨['t', 'a', 'x', '̣', 'c'], ['s', 'o', 'o', 'n'], [⟨['t', 'a', 'x', '̣', 'c'], ['s', 'o', 'o', 'n'], none⟩]⟩, ⟨['q', 'á', 'a', 'm', 's', 'i', 't', '-', 'Ø'], ['q', 'á', 'a', 'm', 's', 'i', 't', '-', 'A', 'C', 'C'], [⟨['q', 'á', 'a', 'm', 's', 'i', 't'], ['q', 'á', 'a', 'm', 's', 'i', 't'], none⟩, ⟨['Ø'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['Ø', '-', 'w', 'i', 'y', 'á', 'a', 'm', 'k', '-', 'o', '\''], ['1', '-', 'p', 'e', 'e', 'l', '-', 'A', 'S', 'P'], [⟨['Ø'], ['1'], none⟩, ⟨['w', 'i', 'y', 'á', 'a', 'm', 'k'], ['p', 'e', 'e', 'l'], some '-'⟩, ⟨['o', '\''], ['A', 'S', 'P'], some '-'⟩]⟩, ⟨['k', 'a', 'a'], ['a', 'n', 'd'], [⟨['k', 'a', 'a'], ['a', 'n', 'd'], none⟩]⟩, ⟨['Ø', '-', 't', 'ú', 'u', 't', '-', 'n', 'u', '\''], ['1', '-', 'g', 'r', 'i', 'n', 'd', '-', 'A', 'S', 'P'], [⟨['Ø'], ['1'], none⟩, ⟨['t', 'ú', 'u', 't'], ['g', 'r', 'i', 'n', 'd'], some '-'⟩, ⟨['n', 'u', '\''], ['A', 'S', 'P'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "nominative"), ("case", "accusative"), ("phi", "1sg"), ("phi", "3sg"), ("prefix", "Ø")] }

def ex_44 : Datum :=
  { id := "woolford1997_44"
    source := ⟨"woolford-1997", "(44)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Kaa qiyáaw'is nacó'x̣-Ø hi-nwíhna-'ni-s."
    glossedTokens := [("Kaa", "and"), ("qiyáaw'is", "dried"), ("nacó'x̣-Ø", "salmon-ACC"), ("hi-nwíhna-'ni-s", "3/1-leave-APPL-ASP")]
    glossedWords := [⟨['K', 'a', 'a'], ['a', 'n', 'd'], [⟨['K', 'a', 'a'], ['a', 'n', 'd'], none⟩]⟩, ⟨['q', 'i', 'y', 'á', 'a', 'w', '\'', 'i', 's'], ['d', 'r', 'i', 'e', 'd'], [⟨['q', 'i', 'y', 'á', 'a', 'w', '\'', 'i', 's'], ['d', 'r', 'i', 'e', 'd'], none⟩]⟩, ⟨['n', 'a', 'c', 'ó', '\'', 'x', '̣', '-', 'Ø'], ['s', 'a', 'l', 'm', 'o', 'n', '-', 'A', 'C', 'C'], [⟨['n', 'a', 'c', 'ó', '\'', 'x', '̣'], ['s', 'a', 'l', 'm', 'o', 'n'], none⟩, ⟨['Ø'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['h', 'i', '-', 'n', 'w', 'í', 'h', 'n', 'a', '-', '\'', 'n', 'i', '-', 's'], ['3', '/', '1', '-', 'l', 'e', 'a', 'v', 'e', '-', 'A', 'P', 'P', 'L', '-', 'A', 'S', 'P'], [⟨['h', 'i'], ['3', '/', '1'], none⟩, ⟨['n', 'w', 'í', 'h', 'n', 'a'], ['l', 'e', 'a', 'v', 'e'], some '-'⟩, ⟨['\'', 'n', 'i'], ['A', 'P', 'P', 'L'], some '-'⟩, ⟨['s'], ['A', 'S', 'P'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "ergative"), ("case", "objective"), ("case", "accusative"), ("phi", "3sg"), ("phi", "1sg"), ("phi", "3sg"), ("prefix", "hi")] }

def ex_45 : Datum :=
  { id := "woolford1997_45"
    source := ⟨"woolford-1997", "(45)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Kaa píst-Ø hi-'naxpayk-óo-ya síteqs-Ø."
    glossedTokens := [("Kaa", "and"), ("píst-Ø", "father-ACC"), ("hi-'naxpayk-óo-ya", "3-bring-DIR-ASP"), ("síteqs-Ø", "liver-ACC")]
    glossedWords := [⟨['K', 'a', 'a'], ['a', 'n', 'd'], [⟨['K', 'a', 'a'], ['a', 'n', 'd'], none⟩]⟩, ⟨['p', 'í', 's', 't', '-', 'Ø'], ['f', 'a', 't', 'h', 'e', 'r', '-', 'A', 'C', 'C'], [⟨['p', 'í', 's', 't'], ['f', 'a', 't', 'h', 'e', 'r'], none⟩, ⟨['Ø'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['h', 'i', '-', '\'', 'n', 'a', 'x', 'p', 'a', 'y', 'k', '-', 'ó', 'o', '-', 'y', 'a'], ['3', '-', 'b', 'r', 'i', 'n', 'g', '-', 'D', 'I', 'R', '-', 'A', 'S', 'P'], [⟨['h', 'i'], ['3'], none⟩, ⟨['\'', 'n', 'a', 'x', 'p', 'a', 'y', 'k'], ['b', 'r', 'i', 'n', 'g'], some '-'⟩, ⟨['ó', 'o'], ['D', 'I', 'R'], some '-'⟩, ⟨['y', 'a'], ['A', 'S', 'P'], some '-'⟩]⟩, ⟨['s', 'í', 't', 'e', 'q', 's', '-', 'Ø'], ['l', 'i', 'v', 'e', 'r', '-', 'A', 'C', 'C'], [⟨['s', 'í', 't', 'e', 'q', 's'], ['l', 'i', 'v', 'e', 'r'], none⟩, ⟨['Ø'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "nominative"), ("case", "accusative"), ("case", "accusative"), ("phi", "3sg"), ("phi", "3sg"), ("phi", "3sg"), ("prefix", "hi")] }

def ex_49 : Datum :=
  { id := "woolford1997_49"
    source := ⟨"woolford-1997", "(49)"⟩
    reportedIn := none
    method := some .description
    language := "dhan1270"
    primaryText := "Taykka-Ø ṛakkunʸT̪in."
    glossedTokens := [("Taykka-Ø", "woman-NOM"), ("ṛakkunʸT̪in", "died")]
    glossedWords := [⟨['T', 'a', 'y', 'k', 'k', 'a', '-', 'Ø'], ['w', 'o', 'm', 'a', 'n', '-', 'N', 'O', 'M'], [⟨['T', 'a', 'y', 'k', 'k', 'a'], ['w', 'o', 'm', 'a', 'n'], none⟩, ⟨['Ø'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['ṛ', 'a', 'k', 'k', 'u', 'n', 'ʸ', 'T', '̪', 'i', 'n'], ['d', 'i', 'e', 'd'], [⟨['ṛ', 'a', 'k', 'k', 'u', 'n', 'ʸ', 'T', '̪', 'i', 'n'], ['d', 'i', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "nominative")] }

def ex_50 : Datum :=
  { id := "woolford1997_50"
    source := ⟨"woolford-1997", "(50)"⟩
    reportedIn := none
    method := some .description
    language := "dhan1270"
    primaryText := "Yūlŋu-T̪u taykka-N̪a puyan."
    glossedTokens := [("Yūlŋu-T̪u", "man-ERG"), ("taykka-N̪a", "woman-OBJ"), ("puyan", "hit")]
    glossedWords := [⟨['Y', 'ū', 'l', 'ŋ', 'u', '-', 'T', '̪', 'u'], ['m', 'a', 'n', '-', 'E', 'R', 'G'], [⟨['Y', 'ū', 'l', 'ŋ', 'u'], ['m', 'a', 'n'], none⟩, ⟨['T', '̪', 'u'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['t', 'a', 'y', 'k', 'k', 'a', '-', 'N', '̪', 'a'], ['w', 'o', 'm', 'a', 'n', '-', 'O', 'B', 'J'], [⟨['t', 'a', 'y', 'k', 'k', 'a'], ['w', 'o', 'm', 'a', 'n'], none⟩, ⟨['N', '̪', 'a'], ['O', 'B', 'J'], some '-'⟩]⟩, ⟨['p', 'u', 'y', 'a', 'n'], ['h', 'i', 't'], [⟨['p', 'u', 'y', 'a', 'n'], ['h', 'i', 't'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "ergative"), ("case", "objective")] }

def ex_51 : Datum :=
  { id := "woolford1997_51"
    source := ⟨"woolford-1997", "(51)"⟩
    reportedIn := none
    method := some .description
    language := "dhan1270"
    primaryText := "Yūlŋu-T̪u yūttu-N̪a kuŋan taykka-Ku."
    glossedTokens := [("Yūlŋu-T̪u", "man-ERG"), ("yūttu-N̪a", "child-OBJ"), ("kuŋan", "give"), ("taykka-Ku", "woman-DAT")]
    glossedWords := [⟨['Y', 'ū', 'l', 'ŋ', 'u', '-', 'T', '̪', 'u'], ['m', 'a', 'n', '-', 'E', 'R', 'G'], [⟨['Y', 'ū', 'l', 'ŋ', 'u'], ['m', 'a', 'n'], none⟩, ⟨['T', '̪', 'u'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['y', 'ū', 't', 't', 'u', '-', 'N', '̪', 'a'], ['c', 'h', 'i', 'l', 'd', '-', 'O', 'B', 'J'], [⟨['y', 'ū', 't', 't', 'u'], ['c', 'h', 'i', 'l', 'd'], none⟩, ⟨['N', '̪', 'a'], ['O', 'B', 'J'], some '-'⟩]⟩, ⟨['k', 'u', 'ŋ', 'a', 'n'], ['g', 'i', 'v', 'e'], [⟨['k', 'u', 'ŋ', 'a', 'n'], ['g', 'i', 'v', 'e'], none⟩]⟩, ⟨['t', 'a', 'y', 'k', 'k', 'a', '-', 'K', 'u'], ['w', 'o', 'm', 'a', 'n', '-', 'D', 'A', 'T'], [⟨['t', 'a', 'y', 'k', 'k', 'a'], ['w', 'o', 'm', 'a', 'n'], none⟩, ⟨['K', 'u'], ['D', 'A', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "ergative"), ("case", "dative"), ("case", "objective")] }

def ex_55 : Datum :=
  { id := "woolford1997_55"
    source := ⟨"woolford-1997", "(55)"⟩
    reportedIn := none
    method := some .description
    language := "kalk1246"
    primaryText := "Maṛapai-Ø mal̪t̪a-Ø iŋka-n̪a-na."
    glossedTokens := [("Maṛapai-Ø", "women-NOM"), ("mal̪t̪a-Ø", "mob(=pl)-NOM"), ("iŋka-n̪a-na", "came-PAST-3pl.SUBJ")]
    glossedWords := [⟨['M', 'a', 'ṛ', 'a', 'p', 'a', 'i', '-', 'Ø'], ['w', 'o', 'm', 'e', 'n', '-', 'N', 'O', 'M'], [⟨['M', 'a', 'ṛ', 'a', 'p', 'a', 'i'], ['w', 'o', 'm', 'e', 'n'], none⟩, ⟨['Ø'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['m', 'a', 'l', '̪', 't', '̪', 'a', '-', 'Ø'], ['m', 'o', 'b', '(', '=', 'p', 'l', ')', '-', 'N', 'O', 'M'], []⟩, ⟨['i', 'ŋ', 'k', 'a', '-', 'n', '̪', 'a', '-', 'n', 'a'], ['c', 'a', 'm', 'e', '-', 'P', 'A', 'S', 'T', '-', '3', 'p', 'l', '.', 'S', 'U', 'B', 'J'], [⟨['i', 'ŋ', 'k', 'a'], ['c', 'a', 'm', 'e'], none⟩, ⟨['n', '̪', 'a'], ['P', 'A', 'S', 'T'], some '-'⟩, ⟨['n', 'a'], ['3', 'p', 'l', '.', 'S', 'U', 'B', 'J'], some '-'⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "nominative")] }

def ex_56 : Datum :=
  { id := "woolford1997_56"
    source := ⟨"woolford-1997", "(56)"⟩
    reportedIn := none
    method := some .description
    language := "kalk1246"
    primaryText := "Maṛapai-t̪u mal̪t̪a-yi ŋai-Ø l̪ayi-n̪a-ŋi-na makat̪i-t̪u."
    glossedTokens := [("Maṛapai-t̪u", "woman-ERG"), ("mal̪t̪a-yi", "mob-ERG"), ("ŋai-Ø", "me-OBJ"), ("l̪ayi-n̪a-ŋi-na", "hit-PAST-1sg.OBJ-3pl.SUBJ"), ("makat̪i-t̪u", "hand-INSTR")]
    glossedWords := [⟨['M', 'a', 'ṛ', 'a', 'p', 'a', 'i', '-', 't', '̪', 'u'], ['w', 'o', 'm', 'a', 'n', '-', 'E', 'R', 'G'], [⟨['M', 'a', 'ṛ', 'a', 'p', 'a', 'i'], ['w', 'o', 'm', 'a', 'n'], none⟩, ⟨['t', '̪', 'u'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['m', 'a', 'l', '̪', 't', '̪', 'a', '-', 'y', 'i'], ['m', 'o', 'b', '-', 'E', 'R', 'G'], [⟨['m', 'a', 'l', '̪', 't', '̪', 'a'], ['m', 'o', 'b'], none⟩, ⟨['y', 'i'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['ŋ', 'a', 'i', '-', 'Ø'], ['m', 'e', '-', 'O', 'B', 'J'], [⟨['ŋ', 'a', 'i'], ['m', 'e'], none⟩, ⟨['Ø'], ['O', 'B', 'J'], some '-'⟩]⟩, ⟨['l', '̪', 'a', 'y', 'i', '-', 'n', '̪', 'a', '-', 'ŋ', 'i', '-', 'n', 'a'], ['h', 'i', 't', '-', 'P', 'A', 'S', 'T', '-', '1', 's', 'g', '.', 'O', 'B', 'J', '-', '3', 'p', 'l', '.', 'S', 'U', 'B', 'J'], [⟨['l', '̪', 'a', 'y', 'i'], ['h', 'i', 't'], none⟩, ⟨['n', '̪', 'a'], ['P', 'A', 'S', 'T'], some '-'⟩, ⟨['ŋ', 'i'], ['1', 's', 'g', '.', 'O', 'B', 'J'], some '-'⟩, ⟨['n', 'a'], ['3', 'p', 'l', '.', 'S', 'U', 'B', 'J'], some '-'⟩]⟩, ⟨['m', 'a', 'k', 'a', 't', '̪', 'i', '-', 't', '̪', 'u'], ['h', 'a', 'n', 'd', '-', 'I', 'N', 'S', 'T', 'R'], [⟨['m', 'a', 'k', 'a', 't', '̪', 'i'], ['h', 'a', 'n', 'd'], none⟩, ⟨['t', '̪', 'u'], ['I', 'N', 'S', 'T', 'R'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "ergative"), ("case", "objective")] }

def ex_57 : Datum :=
  { id := "woolford1997_57"
    source := ⟨"woolford-1997", "(57)"⟩
    reportedIn := none
    method := some .description
    language := "kalk1246"
    primaryText := "Maṛapai-tu anʸa-ŋi (ŋai-Ø) piipa-Ø."
    glossedTokens := [("Maṛapai-tu", "woman-ERG"), ("anʸa-ŋi", "gave-1SG.OBJ"), ("(ŋai-Ø)", "(me-OBJ)"), ("piipa-Ø", "paper-ACC")]
    glossedWords := [⟨['M', 'a', 'ṛ', 'a', 'p', 'a', 'i', '-', 't', 'u'], ['w', 'o', 'm', 'a', 'n', '-', 'E', 'R', 'G'], [⟨['M', 'a', 'ṛ', 'a', 'p', 'a', 'i'], ['w', 'o', 'm', 'a', 'n'], none⟩, ⟨['t', 'u'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['a', 'n', 'ʸ', 'a', '-', 'ŋ', 'i'], ['g', 'a', 'v', 'e', '-', '1', 'S', 'G', '.', 'O', 'B', 'J'], [⟨['a', 'n', 'ʸ', 'a'], ['g', 'a', 'v', 'e'], none⟩, ⟨['ŋ', 'i'], ['1', 'S', 'G', '.', 'O', 'B', 'J'], some '-'⟩]⟩, ⟨['(', 'ŋ', 'a', 'i', '-', 'Ø', ')'], ['(', 'm', 'e', '-', 'O', 'B', 'J', ')'], [⟨['ŋ', 'a', 'i'], ['(', 'm', 'e'], none⟩, ⟨['Ø'], ['O', 'B', 'J', ')'], some '-'⟩]⟩, ⟨['p', 'i', 'i', 'p', 'a', '-', 'Ø'], ['p', 'a', 'p', 'e', 'r', '-', 'A', 'C', 'C'], [⟨['p', 'i', 'i', 'p', 'a'], ['p', 'a', 'p', 'e', 'r'], none⟩, ⟨['Ø'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "ergative"), ("case", "objective"), ("case", "accusative")] }

def ex_10a : Datum :=
  { id := "woolford1997_10a"
    source := ⟨"woolford-1997", "(10a)"⟩
    reportedIn := none
    method := some .description
    language := "icel1247"
    primaryText := "Konan þýddi bókina."
    glossedTokens := [("Konan", "woman-NOM"), ("þýddi", "translated"), ("bókina", "book-ACC")]
    glossedWords := [⟨['K', 'o', 'n', 'a', 'n'], ['w', 'o', 'm', 'a', 'n', '-', 'N', 'O', 'M'], []⟩, ⟨['þ', 'ý', 'd', 'd', 'i'], ['t', 'r', 'a', 'n', 's', 'l', 'a', 't', 'e', 'd'], [⟨['þ', 'ý', 'd', 'd', 'i'], ['t', 'r', 'a', 'n', 's', 'l', 'a', 't', 'e', 'd'], none⟩]⟩, ⟨['b', 'ó', 'k', 'i', 'n', 'a'], ['b', 'o', 'o', 'k', '-', 'A', 'C', 'C'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "nominative"), ("case", "accusative")] }

def ex_10b : Datum :=
  { id := "woolford1997_10b"
    source := ⟨"woolford-1997", "(10b)"⟩
    reportedIn := none
    method := some .description
    language := "icel1247"
    primaryText := "Barninu batnaði veikin."
    glossedTokens := [("Barninu", "child-DAT"), ("batnaði", "recovered-from"), ("veikin", "disease-NOM")]
    glossedWords := [⟨['B', 'a', 'r', 'n', 'i', 'n', 'u'], ['c', 'h', 'i', 'l', 'd', '-', 'D', 'A', 'T'], []⟩, ⟨['b', 'a', 't', 'n', 'a', 'ð', 'i'], ['r', 'e', 'c', 'o', 'v', 'e', 'r', 'e', 'd', '-', 'f', 'r', 'o', 'm'], []⟩, ⟨['v', 'e', 'i', 'k', 'i', 'n'], ['d', 'i', 's', 'e', 'a', 's', 'e', '-', 'N', 'O', 'M'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "dative"), ("case", "nominative")] }

def fn16i : Datum :=
  { id := "woolford1997_fn16i"
    source := ⟨"woolford-1997", "note 16 (i)"⟩
    reportedIn := none
    method := some .description
    language := "icel1247"
    primaryText := "Mér vantar hníf."
    glossedTokens := [("Mér", "me-DAT"), ("vantar", "lacks"), ("hníf", "knife-ACC")]
    glossedWords := [⟨['M', 'é', 'r'], ['m', 'e', '-', 'D', 'A', 'T'], []⟩, ⟨['v', 'a', 'n', 't', 'a', 'r'], ['l', 'a', 'c', 'k', 's'], [⟨['v', 'a', 'n', 't', 'a', 'r'], ['l', 'a', 'c', 'k', 's'], none⟩]⟩, ⟨['h', 'n', 'í', 'f'], ['k', 'n', 'i', 'f', 'e', '-', 'A', 'C', 'C'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "dative"), ("case", "lexical-accusative")] }

def fn16ii : Datum :=
  { id := "woolford1997_fn16ii"
    source := ⟨"woolford-1997", "note 16 (ii)"⟩
    reportedIn := none
    method := some .description
    language := "icel1247"
    primaryText := "Peningana vantar."
    glossedTokens := [("Peningana", "the.money-ACC"), ("vantar", "is.lacking")]
    glossedWords := [⟨['P', 'e', 'n', 'i', 'n', 'g', 'a', 'n', 'a'], ['t', 'h', 'e', '.', 'm', 'o', 'n', 'e', 'y', '-', 'A', 'C', 'C'], []⟩, ⟨['v', 'a', 'n', 't', 'a', 'r'], ['i', 's', '.', 'l', 'a', 'c', 'k', 'i', 'n', 'g'], [⟨['v', 'a', 'n', 't', 'a', 'r'], ['i', 's', '.', 'l', 'a', 'c', 'k', 'i', 'n', 'g'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "lexical-accusative")] }

def fn16iii : Datum :=
  { id := "woolford1997_fn16iii"
    source := ⟨"woolford-1997", "note 16 (iii)"⟩
    reportedIn := none
    method := some .description
    language := "faro1244"
    primaryText := "Mær líkar henda filmin."
    glossedTokens := [("Mær", "me-DAT"), ("líkar", "likes"), ("henda", "this"), ("filmin", "film-ACC")]
    glossedWords := [⟨['M', 'æ', 'r'], ['m', 'e', '-', 'D', 'A', 'T'], []⟩, ⟨['l', 'í', 'k', 'a', 'r'], ['l', 'i', 'k', 'e', 's'], [⟨['l', 'í', 'k', 'a', 'r'], ['l', 'i', 'k', 'e', 's'], none⟩]⟩, ⟨['h', 'e', 'n', 'd', 'a'], ['t', 'h', 'i', 's'], [⟨['h', 'e', 'n', 'd', 'a'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['f', 'i', 'l', 'm', 'i', 'n'], ['f', 'i', 'l', 'm', '-', 'A', 'C', 'C'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "dative"), ("case", "objective")] }

def fn18i : Datum :=
  { id := "woolford1997_fn18i"
    source := ⟨"woolford-1997", "note 18 (i)"⟩
    reportedIn := none
    method := some .description
    language := "icel1247"
    primaryText := "Bátnum hvolfdi."
    glossedTokens := [("Bátnum", "boat-DAT"), ("hvolfdi", "capsized")]
    glossedWords := [⟨['B', 'á', 't', 'n', 'u', 'm'], ['b', 'o', 'a', 't', '-', 'D', 'A', 'T'], []⟩, ⟨['h', 'v', 'o', 'l', 'f', 'd', 'i'], ['c', 'a', 'p', 's', 'i', 'z', 'e', 'd'], [⟨['h', 'v', 'o', 'l', 'f', 'd', 'i'], ['c', 'a', 'p', 's', 'i', 'z', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "dative")] }

def ex_11 : Datum :=
  { id := "woolford1997_11"
    source := ⟨"woolford-1997", "(11)"⟩
    reportedIn := none
    method := some .description
    language := "hind1269"
    primaryText := "Raam rotii khaataa thaa."
    glossedTokens := [("Raam", "Ram(masc)-NOM"), ("rotii", "bread(fem)-ACC"), ("khaataa", "eat(imp,masc)"), ("thaa", "be(past,masc)")]
    glossedWords := [⟨['R', 'a', 'a', 'm'], ['R', 'a', 'm', '(', 'm', 'a', 's', 'c', ')', '-', 'N', 'O', 'M'], []⟩, ⟨['r', 'o', 't', 'i', 'i'], ['b', 'r', 'e', 'a', 'd', '(', 'f', 'e', 'm', ')', '-', 'A', 'C', 'C'], []⟩, ⟨['k', 'h', 'a', 'a', 't', 'a', 'a'], ['e', 'a', 't', '(', 'i', 'm', 'p', ',', 'm', 'a', 's', 'c', ')'], [⟨['k', 'h', 'a', 'a', 't', 'a', 'a'], ['e', 'a', 't', '(', 'i', 'm', 'p', ',', 'm', 'a', 's', 'c', ')'], none⟩]⟩, ⟨['t', 'h', 'a', 'a'], ['b', 'e', '(', 'p', 'a', 's', 't', ',', 'm', 'a', 's', 'c', ')'], [⟨['t', 'h', 'a', 'a'], ['b', 'e', '(', 'p', 'a', 's', 't', ',', 'm', 'a', 's', 'c', ')'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "nominative"), ("case", "accusative")] }

def ex_12 : Datum :=
  { id := "woolford1997_12"
    source := ⟨"woolford-1997", "(12)"⟩
    reportedIn := none
    method := some .description
    language := "hind1269"
    primaryText := "Siitaa-ko larke pasand the."
    glossedTokens := [("Siitaa-ko", "Sita-DAT"), ("larke", "boys-NOM"), ("pasand", "like"), ("the", "be-past(plural)")]
    glossedWords := [⟨['S', 'i', 'i', 't', 'a', 'a', '-', 'k', 'o'], ['S', 'i', 't', 'a', '-', 'D', 'A', 'T'], [⟨['S', 'i', 'i', 't', 'a', 'a'], ['S', 'i', 't', 'a'], none⟩, ⟨['k', 'o'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['l', 'a', 'r', 'k', 'e'], ['b', 'o', 'y', 's', '-', 'N', 'O', 'M'], []⟩, ⟨['p', 'a', 's', 'a', 'n', 'd'], ['l', 'i', 'k', 'e'], [⟨['p', 'a', 's', 'a', 'n', 'd'], ['l', 'i', 'k', 'e'], none⟩]⟩, ⟨['t', 'h', 'e'], ['b', 'e', '-', 'p', 'a', 's', 't', '(', 'p', 'l', 'u', 'r', 'a', 'l', ')'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "dative"), ("case", "nominative")] }

def ex_13 : Datum :=
  { id := "woolford1997_13"
    source := ⟨"woolford-1997", "(13)"⟩
    reportedIn := none
    method := some .description
    language := "hind1269"
    primaryText := "Raam-ne rotii khaayii thii."
    glossedTokens := [("Raam-ne", "Ram-ERG"), ("rotii", "bread(fem)-NOM"), ("khaayii", "eat(perf,fem)"), ("thii", "be(past,fem)")]
    glossedWords := [⟨['R', 'a', 'a', 'm', '-', 'n', 'e'], ['R', 'a', 'm', '-', 'E', 'R', 'G'], [⟨['R', 'a', 'a', 'm'], ['R', 'a', 'm'], none⟩, ⟨['n', 'e'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['r', 'o', 't', 'i', 'i'], ['b', 'r', 'e', 'a', 'd', '(', 'f', 'e', 'm', ')', '-', 'N', 'O', 'M'], []⟩, ⟨['k', 'h', 'a', 'a', 'y', 'i', 'i'], ['e', 'a', 't', '(', 'p', 'e', 'r', 'f', ',', 'f', 'e', 'm', ')'], [⟨['k', 'h', 'a', 'a', 'y', 'i', 'i'], ['e', 'a', 't', '(', 'p', 'e', 'r', 'f', ',', 'f', 'e', 'm', ')'], none⟩]⟩, ⟨['t', 'h', 'i', 'i'], ['b', 'e', '(', 'p', 'a', 's', 't', ',', 'f', 'e', 'm', ')'], [⟨['t', 'h', 'i', 'i'], ['b', 'e', '(', 'p', 'a', 's', 't', ',', 'f', 'e', 'm', ')'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "ergative"), ("case", "nominative")] }

def ex_63 : Datum :=
  { id := "woolford1997_63"
    source := ⟨"woolford-1997", "(63)"⟩
    reportedIn := none
    method := some .description
    language := "hind1269"
    primaryText := "BaccoN-ne siitaa-ko dekhaa thaa."
    glossedTokens := [("BaccoN-ne", "children-ERG"), ("siitaa-ko", "Sita-DAT"), ("dekhaa", "see(perfective-masc.sg.)"), ("thaa", "be(past-masc.sg.)")]
    glossedWords := [⟨['B', 'a', 'c', 'c', 'o', 'N', '-', 'n', 'e'], ['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n', '-', 'E', 'R', 'G'], [⟨['B', 'a', 'c', 'c', 'o', 'N'], ['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n'], none⟩, ⟨['n', 'e'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['s', 'i', 'i', 't', 'a', 'a', '-', 'k', 'o'], ['S', 'i', 't', 'a', '-', 'D', 'A', 'T'], [⟨['s', 'i', 'i', 't', 'a', 'a'], ['S', 'i', 't', 'a'], none⟩, ⟨['k', 'o'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['d', 'e', 'k', 'h', 'a', 'a'], ['s', 'e', 'e', '(', 'p', 'e', 'r', 'f', 'e', 'c', 't', 'i', 'v', 'e', '-', 'm', 'a', 's', 'c', '.', 's', 'g', '.', ')'], []⟩, ⟨['t', 'h', 'a', 'a'], ['b', 'e', '(', 'p', 'a', 's', 't', '-', 'm', 'a', 's', 'c', '.', 's', 'g', '.', ')'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("case", "ergative"), ("case", "dative")] }

def ex_58_nez_nom : Datum :=
  { id := "woolford1997_58_nez_nom"
    source := ⟨"woolford-1997", "(58)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Ø"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("cell", "nominative"), ("exponent", "Ø"), ("agreement", "subject")] }

def ex_58_nez_erg : Datum :=
  { id := "woolford1997_58_nez_erg"
    source := ⟨"woolford-1997", "(58)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "nim"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("cell", "ergative"), ("exponent", "nim"), ("agreement", "subject")] }

def ex_58_nez_obj : Datum :=
  { id := "woolford1997_58_nez_obj"
    source := ⟨"woolford-1997", "(58)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "ne"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("cell", "objective"), ("exponent", "ne"), ("agreement", "object")] }

def ex_58_nez_acc : Datum :=
  { id := "woolford1997_58_nez_acc"
    source := ⟨"woolford-1997", "(58)"⟩
    reportedIn := none
    method := some .description
    language := "nezp1238"
    primaryText := "Ø"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("cell", "accusative"), ("exponent", "Ø"), ("agreement", "none")] }

def ex_58_kal_nom : Datum :=
  { id := "woolford1997_58_kal_nom"
    source := ⟨"woolford-1997", "(58)"⟩
    reportedIn := none
    method := some .description
    language := "kalk1246"
    primaryText := "Ø"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("cell", "nominative"), ("exponent", "Ø"), ("agreement", "subject")] }

def ex_58_kal_erg : Datum :=
  { id := "woolford1997_58_kal_erg"
    source := ⟨"woolford-1997", "(58)"⟩
    reportedIn := none
    method := some .description
    language := "kalk1246"
    primaryText := "t̪u"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("cell", "ergative"), ("exponent", "t̪u"), ("agreement", "subject")] }

def ex_58_kal_obj : Datum :=
  { id := "woolford1997_58_kal_obj"
    source := ⟨"woolford-1997", "(58)"⟩
    reportedIn := none
    method := some .description
    language := "kalk1246"
    primaryText := "Ø"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("cell", "objective"), ("exponent", "Ø"), ("agreement", "object")] }

def ex_58_kal_acc : Datum :=
  { id := "woolford1997_58_kal_acc"
    source := ⟨"woolford-1997", "(58)"⟩
    reportedIn := none
    method := some .description
    language := "kalk1246"
    primaryText := "Ø"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("cell", "accusative"), ("exponent", "Ø"), ("agreement", "none")] }

def all : List Datum := [ex_3, ex_4, ex_5, ex_6, ex_7, ex_8, ex_16A1, ex_16A2, ex_16B1, ex_16B2, ex_22A1, ex_22A2, ex_22A3, ex_22A4, ex_22B1, ex_22B2, ex_22B3, ex_22B4, ex_22B5, ex_22B6, ex_22B7, ex_22B8, ex_29a, ex_29b, ex_30a, ex_30b, ex_31a, ex_31b, ex_32, ex_33, ex_34, ex_37, ex_39, ex_40, ex_41, ex_42, ex_43, ex_44, ex_45, ex_49, ex_50, ex_51, ex_55, ex_56, ex_57, ex_10a, ex_10b, fn16i, fn16ii, fn16iii, fn18i, ex_11, ex_12, ex_13, ex_63, ex_58_nez_nom, ex_58_nez_erg, ex_58_nez_obj, ex_58_nez_acc, ex_58_kal_nom, ex_58_kal_erg, ex_58_kal_obj, ex_58_kal_acc]

/-- Where an argument sits at LF: the specifier of Agr-S, the specifier of Agr-O, or inside VP. -/
inductive Position where
  /-- subject: subject -/
  | specAgrS
  /-- object: object -/
  | specAgrO
  /-- none: none -/
  | inVP
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `agreement`. -/
def agreement (e : Datum) : Option Position :=
  e.parse? "agreement" [("subject", .specAgrS), ("object", .specAgrO), ("none", .inVP)]

end Woolford1997.Examples
