module

public import Linglib.Data.Examples.Schema

/-!
# `ArreguiKusumoto1998` — typed example data

Auto-generated from `Linglib/Data/Examples/ArreguiKusumoto1998.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ArreguiKusumoto1998.Examples`.
-/

@[expose] public section

namespace ArreguiKusumoto1998.Examples

def ex_1 : Datum :=
  { id := "arreguikusumoto1998_1"
    source := ⟨"arregui-kusumoto-1998", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bernhard said that Junko was sick."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .acceptable), ("shifted", .acceptable)]
    paperFeatures := [("clause", "complement"), ("matrixTense", "past"), ("embeddedTense", "past")] }

def ex_3 : Datum :=
  { id := "arreguikusumoto1998_3"
    source := ⟨"arregui-kusumoto-1998", "(3)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Bernhard-wa Junko-ga byooki-datta to itta."
    glossedTokens := [("Bernhard-wa", "Bernhard-TOP"), ("Junko-ga", "Junko-NOM"), ("byooki-datta", "sick-be.PST"), ("to", "COMP"), ("itta", "say.PST")]
    glossedWords := [⟨['B', 'e', 'r', 'n', 'h', 'a', 'r', 'd', '-', 'w', 'a'], ['B', 'e', 'r', 'n', 'h', 'a', 'r', 'd', '-', 'T', 'O', 'P'], [⟨['B', 'e', 'r', 'n', 'h', 'a', 'r', 'd'], ['B', 'e', 'r', 'n', 'h', 'a', 'r', 'd'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['J', 'u', 'n', 'k', 'o', '-', 'g', 'a'], ['J', 'u', 'n', 'k', 'o', '-', 'N', 'O', 'M'], [⟨['J', 'u', 'n', 'k', 'o'], ['J', 'u', 'n', 'k', 'o'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['b', 'y', 'o', 'o', 'k', 'i', '-', 'd', 'a', 't', 't', 'a'], ['s', 'i', 'c', 'k', '-', 'b', 'e', '.', 'P', 'S', 'T'], [⟨['b', 'y', 'o', 'o', 'k', 'i'], ['s', 'i', 'c', 'k'], none⟩, ⟨['d', 'a', 't', 't', 'a'], ['b', 'e', '.', 'P', 'S', 'T'], some '-'⟩]⟩, ⟨['t', 'o'], ['C', 'O', 'M', 'P'], [⟨['t', 'o'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['i', 't', 't', 'a'], ['s', 'a', 'y', '.', 'P', 'S', 'T'], [⟨['i', 't', 't', 'a'], ['s', 'a', 'y', '.', 'P', 'S', 'T'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("shifted", .acceptable), ("simultaneous", .unacceptable)]
    paperFeatures := [("clause", "complement"), ("matrixTense", "past"), ("embeddedTense", "past")] }

def ex_4 : Datum :=
  { id := "arreguikusumoto1998_4"
    source := ⟨"arregui-kusumoto-1998", "(4)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Bernhard-wa Junko-ga byooki-da to itta."
    glossedTokens := [("Bernhard-wa", "Bernhard-TOP"), ("Junko-ga", "Junko-NOM"), ("byooki-da", "sick-be.PRS"), ("to", "COMP"), ("itta", "say.PST")]
    glossedWords := [⟨['B', 'e', 'r', 'n', 'h', 'a', 'r', 'd', '-', 'w', 'a'], ['B', 'e', 'r', 'n', 'h', 'a', 'r', 'd', '-', 'T', 'O', 'P'], [⟨['B', 'e', 'r', 'n', 'h', 'a', 'r', 'd'], ['B', 'e', 'r', 'n', 'h', 'a', 'r', 'd'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['J', 'u', 'n', 'k', 'o', '-', 'g', 'a'], ['J', 'u', 'n', 'k', 'o', '-', 'N', 'O', 'M'], [⟨['J', 'u', 'n', 'k', 'o'], ['J', 'u', 'n', 'k', 'o'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['b', 'y', 'o', 'o', 'k', 'i', '-', 'd', 'a'], ['s', 'i', 'c', 'k', '-', 'b', 'e', '.', 'P', 'R', 'S'], [⟨['b', 'y', 'o', 'o', 'k', 'i'], ['s', 'i', 'c', 'k'], none⟩, ⟨['d', 'a'], ['b', 'e', '.', 'P', 'R', 'S'], some '-'⟩]⟩, ⟨['t', 'o'], ['C', 'O', 'M', 'P'], [⟨['t', 'o'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['i', 't', 't', 'a'], ['s', 'a', 'y', '.', 'P', 'S', 'T'], [⟨['i', 't', 't', 'a'], ['s', 'a', 'y', '.', 'P', 'S', 'T'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .acceptable)]
    paperFeatures := [("clause", "complement"), ("matrixTense", "past"), ("embeddedTense", "present")] }

def ex_5a : Datum :=
  { id := "arreguikusumoto1998_5a"
    source := ⟨"arregui-kusumoto-1998", "(5a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Junko-ga kita mae-ni Satoshi-wa kaetta."
    glossedTokens := [("Junko-ga", "Junko-NOM"), ("kita", "come.PST"), ("mae-ni", "before"), ("Satoshi-wa", "Satoshi-TOP"), ("kaetta", "leave.PST")]
    glossedWords := [⟨['J', 'u', 'n', 'k', 'o', '-', 'g', 'a'], ['J', 'u', 'n', 'k', 'o', '-', 'N', 'O', 'M'], [⟨['J', 'u', 'n', 'k', 'o'], ['J', 'u', 'n', 'k', 'o'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['k', 'i', 't', 'a'], ['c', 'o', 'm', 'e', '.', 'P', 'S', 'T'], [⟨['k', 'i', 't', 'a'], ['c', 'o', 'm', 'e', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['m', 'a', 'e', '-', 'n', 'i'], ['b', 'e', 'f', 'o', 'r', 'e'], []⟩, ⟨['S', 'a', 't', 'o', 's', 'h', 'i', '-', 'w', 'a'], ['S', 'a', 't', 'o', 's', 'h', 'i', '-', 'T', 'O', 'P'], [⟨['S', 'a', 't', 'o', 's', 'h', 'i'], ['S', 'a', 't', 'o', 's', 'h', 'i'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['k', 'a', 'e', 't', 't', 'a'], ['l', 'e', 'a', 'v', 'e', '.', 'P', 'S', 'T'], [⟨['k', 'a', 'e', 't', 't', 'a'], ['l', 'e', 'a', 'v', 'e', '.', 'P', 'S', 'T'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "before"), ("connective", "mae-ni"), ("matrixTense", "past"), ("embeddedTense", "past")] }

def ex_5b : Datum :=
  { id := "arreguikusumoto1998_5b"
    source := ⟨"arregui-kusumoto-1998", "(5b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Junko-ga kuru mae-ni Satoshi-wa kaetta."
    glossedTokens := [("Junko-ga", "Junko-NOM"), ("kuru", "come.PRS"), ("mae-ni", "before"), ("Satoshi-wa", "Satoshi-TOP"), ("kaetta", "leave.PST")]
    glossedWords := [⟨['J', 'u', 'n', 'k', 'o', '-', 'g', 'a'], ['J', 'u', 'n', 'k', 'o', '-', 'N', 'O', 'M'], [⟨['J', 'u', 'n', 'k', 'o'], ['J', 'u', 'n', 'k', 'o'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['k', 'u', 'r', 'u'], ['c', 'o', 'm', 'e', '.', 'P', 'R', 'S'], [⟨['k', 'u', 'r', 'u'], ['c', 'o', 'm', 'e', '.', 'P', 'R', 'S'], none⟩]⟩, ⟨['m', 'a', 'e', '-', 'n', 'i'], ['b', 'e', 'f', 'o', 'r', 'e'], []⟩, ⟨['S', 'a', 't', 'o', 's', 'h', 'i', '-', 'w', 'a'], ['S', 'a', 't', 'o', 's', 'h', 'i', '-', 'T', 'O', 'P'], [⟨['S', 'a', 't', 'o', 's', 'h', 'i'], ['S', 'a', 't', 'o', 's', 'h', 'i'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['k', 'a', 'e', 't', 't', 'a'], ['l', 'e', 'a', 'v', 'e', '.', 'P', 'S', 'T'], [⟨['k', 'a', 'e', 't', 't', 'a'], ['l', 'e', 'a', 'v', 'e', '.', 'P', 'S', 'T'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "before"), ("connective", "mae-ni"), ("matrixTense", "past"), ("embeddedTense", "present")] }

def ex_6a : Datum :=
  { id := "arreguikusumoto1998_6a"
    source := ⟨"arregui-kusumoto-1998", "(6a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Junko-ga kita ato-ni Satoshi-wa kaetta."
    glossedTokens := [("Junko-ga", "Junko-NOM"), ("kita", "come.PST"), ("ato-ni", "after"), ("Satoshi-wa", "Satoshi-TOP"), ("kaetta", "leave.PST")]
    glossedWords := [⟨['J', 'u', 'n', 'k', 'o', '-', 'g', 'a'], ['J', 'u', 'n', 'k', 'o', '-', 'N', 'O', 'M'], [⟨['J', 'u', 'n', 'k', 'o'], ['J', 'u', 'n', 'k', 'o'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['k', 'i', 't', 'a'], ['c', 'o', 'm', 'e', '.', 'P', 'S', 'T'], [⟨['k', 'i', 't', 'a'], ['c', 'o', 'm', 'e', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['a', 't', 'o', '-', 'n', 'i'], ['a', 'f', 't', 'e', 'r'], []⟩, ⟨['S', 'a', 't', 'o', 's', 'h', 'i', '-', 'w', 'a'], ['S', 'a', 't', 'o', 's', 'h', 'i', '-', 'T', 'O', 'P'], [⟨['S', 'a', 't', 'o', 's', 'h', 'i'], ['S', 'a', 't', 'o', 's', 'h', 'i'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['k', 'a', 'e', 't', 't', 'a'], ['l', 'e', 'a', 'v', 'e', '.', 'P', 'S', 'T'], [⟨['k', 'a', 'e', 't', 't', 'a'], ['l', 'e', 'a', 'v', 'e', '.', 'P', 'S', 'T'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "after"), ("connective", "ato-ni"), ("matrixTense", "past"), ("embeddedTense", "past")] }

def ex_6b : Datum :=
  { id := "arreguikusumoto1998_6b"
    source := ⟨"arregui-kusumoto-1998", "(6b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Junko-ga kuru ato-ni Satoshi-wa kaetta."
    glossedTokens := [("Junko-ga", "Junko-NOM"), ("kuru", "come.PRS"), ("ato-ni", "after"), ("Satoshi-wa", "Satoshi-TOP"), ("kaetta", "leave.PST")]
    glossedWords := [⟨['J', 'u', 'n', 'k', 'o', '-', 'g', 'a'], ['J', 'u', 'n', 'k', 'o', '-', 'N', 'O', 'M'], [⟨['J', 'u', 'n', 'k', 'o'], ['J', 'u', 'n', 'k', 'o'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['k', 'u', 'r', 'u'], ['c', 'o', 'm', 'e', '.', 'P', 'R', 'S'], [⟨['k', 'u', 'r', 'u'], ['c', 'o', 'm', 'e', '.', 'P', 'R', 'S'], none⟩]⟩, ⟨['a', 't', 'o', '-', 'n', 'i'], ['a', 'f', 't', 'e', 'r'], []⟩, ⟨['S', 'a', 't', 'o', 's', 'h', 'i', '-', 'w', 'a'], ['S', 'a', 't', 'o', 's', 'h', 'i', '-', 'T', 'O', 'P'], [⟨['S', 'a', 't', 'o', 's', 'h', 'i'], ['S', 'a', 't', 'o', 's', 'h', 'i'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['k', 'a', 'e', 't', 't', 'a'], ['l', 'e', 'a', 'v', 'e', '.', 'P', 'S', 'T'], [⟨['k', 'a', 'e', 't', 't', 'a'], ['l', 'e', 'a', 'v', 'e', '.', 'P', 'S', 'T'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "after"), ("connective", "ato-ni"), ("matrixTense", "past"), ("embeddedTense", "present")] }

def ex_7a : Datum :=
  { id := "arreguikusumoto1998_7a"
    source := ⟨"arregui-kusumoto-1998", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Elliott left before Eva came."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "before"), ("connective", "before"), ("matrixTense", "past"), ("embeddedTense", "past")] }

def ex_7b : Datum :=
  { id := "arreguikusumoto1998_7b"
    source := ⟨"arregui-kusumoto-1998", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Elliott left after Eva came."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "after"), ("connective", "after"), ("matrixTense", "past"), ("embeddedTense", "past")] }

def ex_8 : Datum :=
  { id := "arreguikusumoto1998_8"
    source := ⟨"arregui-kusumoto-1998", "(8)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Satoshi-ga kita toki Junko-wa heya-ni ita."
    glossedTokens := [("Satoshi-ga", "Satoshi-NOM"), ("kita", "come.PST"), ("toki", "when"), ("Junko-wa", "Junko-TOP"), ("heya-ni", "room-LOC"), ("ita", "be.PST")]
    glossedWords := [⟨['S', 'a', 't', 'o', 's', 'h', 'i', '-', 'g', 'a'], ['S', 'a', 't', 'o', 's', 'h', 'i', '-', 'N', 'O', 'M'], [⟨['S', 'a', 't', 'o', 's', 'h', 'i'], ['S', 'a', 't', 'o', 's', 'h', 'i'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['k', 'i', 't', 'a'], ['c', 'o', 'm', 'e', '.', 'P', 'S', 'T'], [⟨['k', 'i', 't', 'a'], ['c', 'o', 'm', 'e', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['t', 'o', 'k', 'i'], ['w', 'h', 'e', 'n'], [⟨['t', 'o', 'k', 'i'], ['w', 'h', 'e', 'n'], none⟩]⟩, ⟨['J', 'u', 'n', 'k', 'o', '-', 'w', 'a'], ['J', 'u', 'n', 'k', 'o', '-', 'T', 'O', 'P'], [⟨['J', 'u', 'n', 'k', 'o'], ['J', 'u', 'n', 'k', 'o'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['h', 'e', 'y', 'a', '-', 'n', 'i'], ['r', 'o', 'o', 'm', '-', 'L', 'O', 'C'], [⟨['h', 'e', 'y', 'a'], ['r', 'o', 'o', 'm'], none⟩, ⟨['n', 'i'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['i', 't', 'a'], ['b', 'e', '.', 'P', 'S', 'T'], [⟨['i', 't', 'a'], ['b', 'e', '.', 'P', 'S', 'T'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("episodic", .acceptable)]
    paperFeatures := [("clause", "when"), ("connective", "toki"), ("matrixTense", "past"), ("embeddedTense", "past")] }

def ex_9 : Datum :=
  { id := "arreguikusumoto1998_9"
    source := ⟨"arregui-kusumoto-1998", "(9)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Satoshi-ga kuru toki Junko-wa heya-ni ita."
    glossedTokens := [("Satoshi-ga", "Satoshi-NOM"), ("kuru", "come.PRS"), ("toki", "when"), ("Junko-wa", "Junko-TOP"), ("heya-ni", "room-LOC"), ("ita", "be.PST")]
    glossedWords := [⟨['S', 'a', 't', 'o', 's', 'h', 'i', '-', 'g', 'a'], ['S', 'a', 't', 'o', 's', 'h', 'i', '-', 'N', 'O', 'M'], [⟨['S', 'a', 't', 'o', 's', 'h', 'i'], ['S', 'a', 't', 'o', 's', 'h', 'i'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['k', 'u', 'r', 'u'], ['c', 'o', 'm', 'e', '.', 'P', 'R', 'S'], [⟨['k', 'u', 'r', 'u'], ['c', 'o', 'm', 'e', '.', 'P', 'R', 'S'], none⟩]⟩, ⟨['t', 'o', 'k', 'i'], ['w', 'h', 'e', 'n'], [⟨['t', 'o', 'k', 'i'], ['w', 'h', 'e', 'n'], none⟩]⟩, ⟨['J', 'u', 'n', 'k', 'o', '-', 'w', 'a'], ['J', 'u', 'n', 'k', 'o', '-', 'T', 'O', 'P'], [⟨['J', 'u', 'n', 'k', 'o'], ['J', 'u', 'n', 'k', 'o'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['h', 'e', 'y', 'a', '-', 'n', 'i'], ['r', 'o', 'o', 'm', '-', 'L', 'O', 'C'], [⟨['h', 'e', 'y', 'a'], ['r', 'o', 'o', 'm'], none⟩, ⟨['n', 'i'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['i', 't', 'a'], ['b', 'e', '.', 'P', 'S', 'T'], [⟨['i', 't', 'a'], ['b', 'e', '.', 'P', 'S', 'T'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("habitual", .acceptable)]
    paperFeatures := [("clause", "when"), ("connective", "toki"), ("matrixTense", "past"), ("embeddedTense", "present")] }

def ex_10a : Datum :=
  { id := "arreguikusumoto1998_10a"
    source := ⟨"arregui-kusumoto-1998", "(10a)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Ania powiedziała, że Marcin jest chory."
    glossedTokens := [("Ania", "Ania"), ("powiedziała", "say.PFV.PST"), ("że", "that"), ("Marcin", "Marcin"), ("jest", "be.PRS"), ("chory", "sick")]
    glossedWords := [⟨['A', 'n', 'i', 'a'], ['A', 'n', 'i', 'a'], [⟨['A', 'n', 'i', 'a'], ['A', 'n', 'i', 'a'], none⟩]⟩, ⟨['p', 'o', 'w', 'i', 'e', 'd', 'z', 'i', 'a', 'ł', 'a'], ['s', 'a', 'y', '.', 'P', 'F', 'V', '.', 'P', 'S', 'T'], [⟨['p', 'o', 'w', 'i', 'e', 'd', 'z', 'i', 'a', 'ł', 'a'], ['s', 'a', 'y', '.', 'P', 'F', 'V', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['ż', 'e'], ['t', 'h', 'a', 't'], [⟨['ż', 'e'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['M', 'a', 'r', 'c', 'i', 'n'], ['M', 'a', 'r', 'c', 'i', 'n'], [⟨['M', 'a', 'r', 'c', 'i', 'n'], ['M', 'a', 'r', 'c', 'i', 'n'], none⟩]⟩, ⟨['j', 'e', 's', 't'], ['b', 'e', '.', 'P', 'R', 'S'], [⟨['j', 'e', 's', 't'], ['b', 'e', '.', 'P', 'R', 'S'], none⟩]⟩, ⟨['c', 'h', 'o', 'r', 'y'], ['s', 'i', 'c', 'k'], [⟨['c', 'h', 'o', 'r', 'y'], ['s', 'i', 'c', 'k'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Ania said: \"Marcin is sick\"."
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .acceptable)]
    paperFeatures := [("clause", "complement"), ("matrixTense", "past"), ("embeddedTense", "present")] }

def ex_10b : Datum :=
  { id := "arreguikusumoto1998_10b"
    source := ⟨"arregui-kusumoto-1998", "(10b)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Ania powiedziała, że Marcin był chory."
    glossedTokens := [("Ania", "Ania"), ("powiedziała", "say.PFV.PST"), ("że", "that"), ("Marcin", "Marcin"), ("był", "be.PST"), ("chory", "sick")]
    glossedWords := [⟨['A', 'n', 'i', 'a'], ['A', 'n', 'i', 'a'], [⟨['A', 'n', 'i', 'a'], ['A', 'n', 'i', 'a'], none⟩]⟩, ⟨['p', 'o', 'w', 'i', 'e', 'd', 'z', 'i', 'a', 'ł', 'a'], ['s', 'a', 'y', '.', 'P', 'F', 'V', '.', 'P', 'S', 'T'], [⟨['p', 'o', 'w', 'i', 'e', 'd', 'z', 'i', 'a', 'ł', 'a'], ['s', 'a', 'y', '.', 'P', 'F', 'V', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['ż', 'e'], ['t', 'h', 'a', 't'], [⟨['ż', 'e'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['M', 'a', 'r', 'c', 'i', 'n'], ['M', 'a', 'r', 'c', 'i', 'n'], [⟨['M', 'a', 'r', 'c', 'i', 'n'], ['M', 'a', 'r', 'c', 'i', 'n'], none⟩]⟩, ⟨['b', 'y', 'ł'], ['b', 'e', '.', 'P', 'S', 'T'], [⟨['b', 'y', 'ł'], ['b', 'e', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['c', 'h', 'o', 'r', 'y'], ['s', 'i', 'c', 'k'], [⟨['c', 'h', 'o', 'r', 'y'], ['s', 'i', 'c', 'k'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Ania said: \"Marcin was sick\"."
    judgment := .acceptable
    alternatives := []
    readings := [("shifted", .acceptable), ("simultaneous", .unacceptable)]
    paperFeatures := [("clause", "complement"), ("matrixTense", "past"), ("embeddedTense", "past")] }

def ex_10c : Datum :=
  { id := "arreguikusumoto1998_10c"
    source := ⟨"arregui-kusumoto-1998", "(10c)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Ania powiedziała, że będzie padać."
    glossedTokens := [("Ania", "Ania"), ("powiedziała", "say.PFV.PST"), ("że", "that"), ("będzie", "FUT"), ("padać", "rain")]
    glossedWords := [⟨['A', 'n', 'i', 'a'], ['A', 'n', 'i', 'a'], [⟨['A', 'n', 'i', 'a'], ['A', 'n', 'i', 'a'], none⟩]⟩, ⟨['p', 'o', 'w', 'i', 'e', 'd', 'z', 'i', 'a', 'ł', 'a'], ['s', 'a', 'y', '.', 'P', 'F', 'V', '.', 'P', 'S', 'T'], [⟨['p', 'o', 'w', 'i', 'e', 'd', 'z', 'i', 'a', 'ł', 'a'], ['s', 'a', 'y', '.', 'P', 'F', 'V', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['ż', 'e'], ['t', 'h', 'a', 't'], [⟨['ż', 'e'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['b', 'ę', 'd', 'z', 'i', 'e'], ['F', 'U', 'T'], [⟨['b', 'ę', 'd', 'z', 'i', 'e'], ['F', 'U', 'T'], none⟩]⟩, ⟨['p', 'a', 'd', 'a', 'ć'], ['r', 'a', 'i', 'n'], [⟨['p', 'a', 'd', 'a', 'ć'], ['r', 'a', 'i', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("posterior", .acceptable)]
    paperFeatures := [("clause", "complement"), ("matrixTense", "past"), ("embeddedTense", "future")] }

def ex_11a : Datum :=
  { id := "arreguikusumoto1998_11a"
    source := ⟨"arregui-kusumoto-1998", "(11a)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Ania przyszła na przyjęcie zanim Marcin przyszedł."
    glossedTokens := [("Ania", "Ania"), ("przyszła", "PFV-come-PST"), ("na", "to"), ("przyjęcie", "party"), ("zanim", "before"), ("Marcin", "Marcin"), ("przyszedł", "PFV-come-PST")]
    glossedWords := [⟨['A', 'n', 'i', 'a'], ['A', 'n', 'i', 'a'], [⟨['A', 'n', 'i', 'a'], ['A', 'n', 'i', 'a'], none⟩]⟩, ⟨['p', 'r', 'z', 'y', 's', 'z', 'ł', 'a'], ['P', 'F', 'V', '-', 'c', 'o', 'm', 'e', '-', 'P', 'S', 'T'], []⟩, ⟨['n', 'a'], ['t', 'o'], [⟨['n', 'a'], ['t', 'o'], none⟩]⟩, ⟨['p', 'r', 'z', 'y', 'j', 'ę', 'c', 'i', 'e'], ['p', 'a', 'r', 't', 'y'], [⟨['p', 'r', 'z', 'y', 'j', 'ę', 'c', 'i', 'e'], ['p', 'a', 'r', 't', 'y'], none⟩]⟩, ⟨['z', 'a', 'n', 'i', 'm'], ['b', 'e', 'f', 'o', 'r', 'e'], [⟨['z', 'a', 'n', 'i', 'm'], ['b', 'e', 'f', 'o', 'r', 'e'], none⟩]⟩, ⟨['M', 'a', 'r', 'c', 'i', 'n'], ['M', 'a', 'r', 'c', 'i', 'n'], [⟨['M', 'a', 'r', 'c', 'i', 'n'], ['M', 'a', 'r', 'c', 'i', 'n'], none⟩]⟩, ⟨['p', 'r', 'z', 'y', 's', 'z', 'e', 'd', 'ł'], ['P', 'F', 'V', '-', 'c', 'o', 'm', 'e', '-', 'P', 'S', 'T'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "before"), ("connective", "zanim"), ("matrixTense", "past"), ("embeddedTense", "past")] }

def ex_11b : Datum :=
  { id := "arreguikusumoto1998_11b"
    source := ⟨"arregui-kusumoto-1998", "(11b)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Ania przyszła na przyjęcie zanim Marcin przychodzi."
    glossedTokens := [("Ania", "Ania"), ("przyszła", "PFV-come-PST"), ("na", "to"), ("przyjęcie", "party"), ("zanim", "before"), ("Marcin", "Marcin"), ("przychodzi", "PFV-come-PRS")]
    glossedWords := [⟨['A', 'n', 'i', 'a'], ['A', 'n', 'i', 'a'], [⟨['A', 'n', 'i', 'a'], ['A', 'n', 'i', 'a'], none⟩]⟩, ⟨['p', 'r', 'z', 'y', 's', 'z', 'ł', 'a'], ['P', 'F', 'V', '-', 'c', 'o', 'm', 'e', '-', 'P', 'S', 'T'], []⟩, ⟨['n', 'a'], ['t', 'o'], [⟨['n', 'a'], ['t', 'o'], none⟩]⟩, ⟨['p', 'r', 'z', 'y', 'j', 'ę', 'c', 'i', 'e'], ['p', 'a', 'r', 't', 'y'], [⟨['p', 'r', 'z', 'y', 'j', 'ę', 'c', 'i', 'e'], ['p', 'a', 'r', 't', 'y'], none⟩]⟩, ⟨['z', 'a', 'n', 'i', 'm'], ['b', 'e', 'f', 'o', 'r', 'e'], [⟨['z', 'a', 'n', 'i', 'm'], ['b', 'e', 'f', 'o', 'r', 'e'], none⟩]⟩, ⟨['M', 'a', 'r', 'c', 'i', 'n'], ['M', 'a', 'r', 'c', 'i', 'n'], [⟨['M', 'a', 'r', 'c', 'i', 'n'], ['M', 'a', 'r', 'c', 'i', 'n'], none⟩]⟩, ⟨['p', 'r', 'z', 'y', 'c', 'h', 'o', 'd', 'z', 'i'], ['P', 'F', 'V', '-', 'c', 'o', 'm', 'e', '-', 'P', 'R', 'S'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "before"), ("connective", "zanim"), ("matrixTense", "past"), ("embeddedTense", "present")] }

def ex_11c : Datum :=
  { id := "arreguikusumoto1998_11c"
    source := ⟨"arregui-kusumoto-1998", "(11c)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Ania przyszła na przyjęcie zanim Marcin przyjdzie."
    glossedTokens := [("Ania", "Ania"), ("przyszła", "PFV-come-PST"), ("na", "to"), ("przyjęcie", "party"), ("zanim", "before"), ("Marcin", "Marcin"), ("przyjdzie", "PFV-come-FUT")]
    glossedWords := [⟨['A', 'n', 'i', 'a'], ['A', 'n', 'i', 'a'], [⟨['A', 'n', 'i', 'a'], ['A', 'n', 'i', 'a'], none⟩]⟩, ⟨['p', 'r', 'z', 'y', 's', 'z', 'ł', 'a'], ['P', 'F', 'V', '-', 'c', 'o', 'm', 'e', '-', 'P', 'S', 'T'], []⟩, ⟨['n', 'a'], ['t', 'o'], [⟨['n', 'a'], ['t', 'o'], none⟩]⟩, ⟨['p', 'r', 'z', 'y', 'j', 'ę', 'c', 'i', 'e'], ['p', 'a', 'r', 't', 'y'], [⟨['p', 'r', 'z', 'y', 'j', 'ę', 'c', 'i', 'e'], ['p', 'a', 'r', 't', 'y'], none⟩]⟩, ⟨['z', 'a', 'n', 'i', 'm'], ['b', 'e', 'f', 'o', 'r', 'e'], [⟨['z', 'a', 'n', 'i', 'm'], ['b', 'e', 'f', 'o', 'r', 'e'], none⟩]⟩, ⟨['M', 'a', 'r', 'c', 'i', 'n'], ['M', 'a', 'r', 'c', 'i', 'n'], [⟨['M', 'a', 'r', 'c', 'i', 'n'], ['M', 'a', 'r', 'c', 'i', 'n'], none⟩]⟩, ⟨['p', 'r', 'z', 'y', 'j', 'd', 'z', 'i', 'e'], ['P', 'F', 'V', '-', 'c', 'o', 'm', 'e', '-', 'F', 'U', 'T'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "before"), ("connective", "zanim"), ("matrixTense", "past"), ("embeddedTense", "future")] }

def ex_12a : Datum :=
  { id := "arreguikusumoto1998_12a"
    source := ⟨"arregui-kusumoto-1998", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is sick."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "root"), ("tense", "present")] }

def ex_13a : Datum :=
  { id := "arreguikusumoto1998_13a"
    source := ⟨"arregui-kusumoto-1998", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John was sick."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "root"), ("tense", "past")] }

def ex_14 : Datum :=
  { id := "arreguikusumoto1998_14"
    source := ⟨"arregui-kusumoto-1998", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I encountered Satoshi in Amherst when you said he had left."
    glossedTokens := []
    context := "I met you in Amherst at 3:00 p.m., and you said \"Satoshi left here at 10:00 a.m. this morning\"."
    judgment := .acceptable
    alternatives := []
    readings := [("upstairs", .acceptable), ("downstairs", .acceptable)]
    paperFeatures := [("clause", "when"), ("connective", "when"), ("matrixTense", "past"), ("embeddedTense", "past"), ("embeddedClauses", "2")] }

def ex_18a : Datum :=
  { id := "arreguikusumoto1998_18a"
    source := ⟨"arregui-kusumoto-1998", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I watered the plant before it died."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("veridical", .acceptable), ("nonveridical", .acceptable)]
    paperFeatures := [("clause", "before"), ("connective", "before"), ("matrixTense", "past"), ("embeddedTense", "past")] }

def ex_18b : Datum :=
  { id := "arreguikusumoto1998_18b"
    source := ⟨"arregui-kusumoto-1998", "(18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I watered the plant after it died."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("veridical", .acceptable)]
    paperFeatures := [("clause", "after"), ("connective", "after"), ("matrixTense", "past"), ("embeddedTense", "past")] }

def ex_20a : Datum :=
  { id := "arreguikusumoto1998_20a"
    source := ⟨"arregui-kusumoto-1998", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I encountered Satoshi in Amherst after you said he had left."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("upstairs", .acceptable), ("downstairs", .acceptable)]
    paperFeatures := [("clause", "after"), ("connective", "after"), ("matrixTense", "past"), ("embeddedTense", "past"), ("embeddedClauses", "2")] }

def ex_20b : Datum :=
  { id := "arreguikusumoto1998_20b"
    source := ⟨"arregui-kusumoto-1998", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Anita left before she said she had."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("upstairs", .acceptable), ("downstairs", .acceptable)]
    paperFeatures := [("clause", "before"), ("connective", "before"), ("matrixTense", "past"), ("embeddedTense", "past"), ("embeddedClauses", "2")] }

def ex_22a : Datum :=
  { id := "arreguikusumoto1998_22a"
    source := ⟨"arregui-kusumoto-1998", "(22a)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Widziałem Lizę po tym jak powiedziała, że jej nie będzie."
    glossedTokens := [("Widziałem", "see.PFV.PST"), ("Lizę", "Lisa"), ("po tym jak", "after this how"), ("powiedziała", "say.PFV.PST"), ("że", "that"), ("jej", "her"), ("nie", "not"), ("będzie", "be.FUT")]
    glossedWords := [⟨['W', 'i', 'd', 'z', 'i', 'a', 'ł', 'e', 'm'], ['s', 'e', 'e', '.', 'P', 'F', 'V', '.', 'P', 'S', 'T'], [⟨['W', 'i', 'd', 'z', 'i', 'a', 'ł', 'e', 'm'], ['s', 'e', 'e', '.', 'P', 'F', 'V', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['L', 'i', 'z', 'ę'], ['L', 'i', 's', 'a'], [⟨['L', 'i', 'z', 'ę'], ['L', 'i', 's', 'a'], none⟩]⟩, ⟨['p', 'o', ' ', 't', 'y', 'm', ' ', 'j', 'a', 'k'], ['a', 'f', 't', 'e', 'r', ' ', 't', 'h', 'i', 's', ' ', 'h', 'o', 'w'], [⟨['p', 'o', ' ', 't', 'y', 'm', ' ', 'j', 'a', 'k'], ['a', 'f', 't', 'e', 'r', ' ', 't', 'h', 'i', 's', ' ', 'h', 'o', 'w'], none⟩]⟩, ⟨['p', 'o', 'w', 'i', 'e', 'd', 'z', 'i', 'a', 'ł', 'a'], ['s', 'a', 'y', '.', 'P', 'F', 'V', '.', 'P', 'S', 'T'], [⟨['p', 'o', 'w', 'i', 'e', 'd', 'z', 'i', 'a', 'ł', 'a'], ['s', 'a', 'y', '.', 'P', 'F', 'V', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['ż', 'e'], ['t', 'h', 'a', 't'], [⟨['ż', 'e'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['j', 'e', 'j'], ['h', 'e', 'r'], [⟨['j', 'e', 'j'], ['h', 'e', 'r'], none⟩]⟩, ⟨['n', 'i', 'e'], ['n', 'o', 't'], [⟨['n', 'i', 'e'], ['n', 'o', 't'], none⟩]⟩, ⟨['b', 'ę', 'd', 'z', 'i', 'e'], ['b', 'e', '.', 'F', 'U', 'T'], [⟨['b', 'ę', 'd', 'z', 'i', 'e'], ['b', 'e', '.', 'F', 'U', 'T'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("upstairs", .acceptable), ("downstairs", .acceptable)]
    paperFeatures := [("clause", "after"), ("connective", "po tym jak"), ("matrixTense", "past"), ("embeddedTense", "past"), ("embeddedClauses", "2")] }

def ex_22b : Datum :=
  { id := "arreguikusumoto1998_22b"
    source := ⟨"arregui-kusumoto-1998", "(22b)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Widziałem Lizę zanim powiedziała, że jej nie będzie."
    glossedTokens := [("Widziałem", "see.PFV.PST"), ("Lizę", "Lisa"), ("zanim", "before"), ("powiedziała", "say.PFV.PST"), ("że", "that"), ("jej", "her"), ("nie", "not"), ("będzie", "be.FUT")]
    glossedWords := [⟨['W', 'i', 'd', 'z', 'i', 'a', 'ł', 'e', 'm'], ['s', 'e', 'e', '.', 'P', 'F', 'V', '.', 'P', 'S', 'T'], [⟨['W', 'i', 'd', 'z', 'i', 'a', 'ł', 'e', 'm'], ['s', 'e', 'e', '.', 'P', 'F', 'V', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['L', 'i', 'z', 'ę'], ['L', 'i', 's', 'a'], [⟨['L', 'i', 'z', 'ę'], ['L', 'i', 's', 'a'], none⟩]⟩, ⟨['z', 'a', 'n', 'i', 'm'], ['b', 'e', 'f', 'o', 'r', 'e'], [⟨['z', 'a', 'n', 'i', 'm'], ['b', 'e', 'f', 'o', 'r', 'e'], none⟩]⟩, ⟨['p', 'o', 'w', 'i', 'e', 'd', 'z', 'i', 'a', 'ł', 'a'], ['s', 'a', 'y', '.', 'P', 'F', 'V', '.', 'P', 'S', 'T'], [⟨['p', 'o', 'w', 'i', 'e', 'd', 'z', 'i', 'a', 'ł', 'a'], ['s', 'a', 'y', '.', 'P', 'F', 'V', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['ż', 'e'], ['t', 'h', 'a', 't'], [⟨['ż', 'e'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['j', 'e', 'j'], ['h', 'e', 'r'], [⟨['j', 'e', 'j'], ['h', 'e', 'r'], none⟩]⟩, ⟨['n', 'i', 'e'], ['n', 'o', 't'], [⟨['n', 'i', 'e'], ['n', 'o', 't'], none⟩]⟩, ⟨['b', 'ę', 'd', 'z', 'i', 'e'], ['b', 'e', '.', 'F', 'U', 'T'], [⟨['b', 'ę', 'd', 'z', 'i', 'e'], ['b', 'e', '.', 'F', 'U', 'T'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("upstairs", .acceptable), ("downstairs", .acceptable)]
    paperFeatures := [("clause", "before"), ("connective", "zanim"), ("matrixTense", "past"), ("embeddedTense", "past"), ("embeddedClauses", "2")] }

def ex_24a : Datum :=
  { id := "arreguikusumoto1998_24a"
    source := ⟨"arregui-kusumoto-1998", "(24a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Satoshi left after Junko came."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "after"), ("connective", "after"), ("matrixTense", "past"), ("embeddedTense", "past")] }

def ex_25a : Datum :=
  { id := "arreguikusumoto1998_25a"
    source := ⟨"arregui-kusumoto-1998", "(25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Satoshi left before Junko came."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "before"), ("connective", "before"), ("matrixTense", "past"), ("embeddedTense", "past")] }

def ex_26a : Datum :=
  { id := "arreguikusumoto1998_26a"
    source := ⟨"arregui-kusumoto-1998", "(26a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Junko-wa zibun-ga kaeru to itta ato-de kaetta."
    glossedTokens := [("Junko-wa", "Junko-TOP"), ("zibun-ga", "self-NOM"), ("kaeru", "leave.PRS"), ("to", "COMP"), ("itta", "say.PST"), ("ato-de", "after"), ("kaetta", "leave.PST")]
    glossedWords := [⟨['J', 'u', 'n', 'k', 'o', '-', 'w', 'a'], ['J', 'u', 'n', 'k', 'o', '-', 'T', 'O', 'P'], [⟨['J', 'u', 'n', 'k', 'o'], ['J', 'u', 'n', 'k', 'o'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['z', 'i', 'b', 'u', 'n', '-', 'g', 'a'], ['s', 'e', 'l', 'f', '-', 'N', 'O', 'M'], [⟨['z', 'i', 'b', 'u', 'n'], ['s', 'e', 'l', 'f'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['k', 'a', 'e', 'r', 'u'], ['l', 'e', 'a', 'v', 'e', '.', 'P', 'R', 'S'], [⟨['k', 'a', 'e', 'r', 'u'], ['l', 'e', 'a', 'v', 'e', '.', 'P', 'R', 'S'], none⟩]⟩, ⟨['t', 'o'], ['C', 'O', 'M', 'P'], [⟨['t', 'o'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['i', 't', 't', 'a'], ['s', 'a', 'y', '.', 'P', 'S', 'T'], [⟨['i', 't', 't', 'a'], ['s', 'a', 'y', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['a', 't', 'o', '-', 'd', 'e'], ['a', 'f', 't', 'e', 'r'], []⟩, ⟨['k', 'a', 'e', 't', 't', 'a'], ['l', 'e', 'a', 'v', 'e', '.', 'P', 'S', 'T'], [⟨['k', 'a', 'e', 't', 't', 'a'], ['l', 'e', 'a', 'v', 'e', '.', 'P', 'S', 'T'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("upstairs", .acceptable), ("downstairs", .unacceptable)]
    paperFeatures := [("clause", "after"), ("connective", "ato-de"), ("matrixTense", "past"), ("embeddedTense", "past"), ("embeddedClauses", "2")] }

def ex_26b : Datum :=
  { id := "arreguikusumoto1998_26b"
    source := ⟨"arregui-kusumoto-1998", "(26b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Watasi-wa Satoshi-ni anata-ga kaetta to iu mae-ni Amherst-de atta."
    glossedTokens := [("Watasi-wa", "I-TOP"), ("Satoshi-ni", "Satoshi-DAT"), ("anata-ga", "you-NOM"), ("kaetta", "leave.PST"), ("to", "COMP"), ("iu", "say.PRS"), ("mae-ni", "before"), ("Amherst-de", "Amherst-LOC"), ("atta", "meet.PST")]
    glossedWords := [⟨['W', 'a', 't', 'a', 's', 'i', '-', 'w', 'a'], ['I', '-', 'T', 'O', 'P'], [⟨['W', 'a', 't', 'a', 's', 'i'], ['I'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['S', 'a', 't', 'o', 's', 'h', 'i', '-', 'n', 'i'], ['S', 'a', 't', 'o', 's', 'h', 'i', '-', 'D', 'A', 'T'], [⟨['S', 'a', 't', 'o', 's', 'h', 'i'], ['S', 'a', 't', 'o', 's', 'h', 'i'], none⟩, ⟨['n', 'i'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['a', 'n', 'a', 't', 'a', '-', 'g', 'a'], ['y', 'o', 'u', '-', 'N', 'O', 'M'], [⟨['a', 'n', 'a', 't', 'a'], ['y', 'o', 'u'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['k', 'a', 'e', 't', 't', 'a'], ['l', 'e', 'a', 'v', 'e', '.', 'P', 'S', 'T'], [⟨['k', 'a', 'e', 't', 't', 'a'], ['l', 'e', 'a', 'v', 'e', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['t', 'o'], ['C', 'O', 'M', 'P'], [⟨['t', 'o'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['i', 'u'], ['s', 'a', 'y', '.', 'P', 'R', 'S'], [⟨['i', 'u'], ['s', 'a', 'y', '.', 'P', 'R', 'S'], none⟩]⟩, ⟨['m', 'a', 'e', '-', 'n', 'i'], ['b', 'e', 'f', 'o', 'r', 'e'], []⟩, ⟨['A', 'm', 'h', 'e', 'r', 's', 't', '-', 'd', 'e'], ['A', 'm', 'h', 'e', 'r', 's', 't', '-', 'L', 'O', 'C'], [⟨['A', 'm', 'h', 'e', 'r', 's', 't'], ['A', 'm', 'h', 'e', 'r', 's', 't'], none⟩, ⟨['d', 'e'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['a', 't', 't', 'a'], ['m', 'e', 'e', 't', '.', 'P', 'S', 'T'], [⟨['a', 't', 't', 'a'], ['m', 'e', 'e', 't', '.', 'P', 'S', 'T'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("upstairs", .acceptable), ("downstairs", .unacceptable)]
    paperFeatures := [("clause", "before"), ("connective", "mae-ni"), ("matrixTense", "past"), ("embeddedTense", "present"), ("embeddedClauses", "2")] }

def ex_32 : Datum :=
  { id := "arreguikusumoto1998_32"
    source := ⟨"arregui-kusumoto-1998", "(32)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Watasi-wa Junko-ga Satoshi-ga kaetta to itta toki-ni kare-ni atta."
    glossedTokens := [("Watasi-wa", "I-TOP"), ("Junko-ga", "Junko-NOM"), ("Satoshi-ga", "Satoshi-NOM"), ("kaetta", "leave.PST"), ("to", "COMP"), ("itta", "say.PST"), ("toki-ni", "when"), ("kare-ni", "he-DAT"), ("atta", "meet.PST")]
    glossedWords := [⟨['W', 'a', 't', 'a', 's', 'i', '-', 'w', 'a'], ['I', '-', 'T', 'O', 'P'], [⟨['W', 'a', 't', 'a', 's', 'i'], ['I'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['J', 'u', 'n', 'k', 'o', '-', 'g', 'a'], ['J', 'u', 'n', 'k', 'o', '-', 'N', 'O', 'M'], [⟨['J', 'u', 'n', 'k', 'o'], ['J', 'u', 'n', 'k', 'o'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['S', 'a', 't', 'o', 's', 'h', 'i', '-', 'g', 'a'], ['S', 'a', 't', 'o', 's', 'h', 'i', '-', 'N', 'O', 'M'], [⟨['S', 'a', 't', 'o', 's', 'h', 'i'], ['S', 'a', 't', 'o', 's', 'h', 'i'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['k', 'a', 'e', 't', 't', 'a'], ['l', 'e', 'a', 'v', 'e', '.', 'P', 'S', 'T'], [⟨['k', 'a', 'e', 't', 't', 'a'], ['l', 'e', 'a', 'v', 'e', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['t', 'o'], ['C', 'O', 'M', 'P'], [⟨['t', 'o'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['i', 't', 't', 'a'], ['s', 'a', 'y', '.', 'P', 'S', 'T'], [⟨['i', 't', 't', 'a'], ['s', 'a', 'y', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['t', 'o', 'k', 'i', '-', 'n', 'i'], ['w', 'h', 'e', 'n'], []⟩, ⟨['k', 'a', 'r', 'e', '-', 'n', 'i'], ['h', 'e', '-', 'D', 'A', 'T'], [⟨['k', 'a', 'r', 'e'], ['h', 'e'], none⟩, ⟨['n', 'i'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['a', 't', 't', 'a'], ['m', 'e', 'e', 't', '.', 'P', 'S', 'T'], [⟨['a', 't', 't', 'a'], ['m', 'e', 'e', 't', '.', 'P', 'S', 'T'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("upstairs", .acceptable), ("downstairs", .acceptable)]
    paperFeatures := [("clause", "when"), ("connective", "toki-ni"), ("matrixTense", "past"), ("embeddedTense", "past"), ("embeddedClauses", "2")] }

def ex_35a : Datum :=
  { id := "arreguikusumoto1998_35a"
    source := ⟨"arregui-kusumoto-1998", "(35a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Junko-wa Satoshi-ga kuruma-o tyusyasuru basho-de kagi-o nakusita."
    glossedTokens := [("Junko-wa", "Junko-TOP"), ("Satoshi-ga", "Satoshi-NOM"), ("kuruma-o", "car-ACC"), ("tyusyasuru", "park.PRS"), ("basho-de", "place-LOC"), ("kagi-o", "key-ACC"), ("nakusita", "lose.PST")]
    glossedWords := [⟨['J', 'u', 'n', 'k', 'o', '-', 'w', 'a'], ['J', 'u', 'n', 'k', 'o', '-', 'T', 'O', 'P'], [⟨['J', 'u', 'n', 'k', 'o'], ['J', 'u', 'n', 'k', 'o'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['S', 'a', 't', 'o', 's', 'h', 'i', '-', 'g', 'a'], ['S', 'a', 't', 'o', 's', 'h', 'i', '-', 'N', 'O', 'M'], [⟨['S', 'a', 't', 'o', 's', 'h', 'i'], ['S', 'a', 't', 'o', 's', 'h', 'i'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['k', 'u', 'r', 'u', 'm', 'a', '-', 'o'], ['c', 'a', 'r', '-', 'A', 'C', 'C'], [⟨['k', 'u', 'r', 'u', 'm', 'a'], ['c', 'a', 'r'], none⟩, ⟨['o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['t', 'y', 'u', 's', 'y', 'a', 's', 'u', 'r', 'u'], ['p', 'a', 'r', 'k', '.', 'P', 'R', 'S'], [⟨['t', 'y', 'u', 's', 'y', 'a', 's', 'u', 'r', 'u'], ['p', 'a', 'r', 'k', '.', 'P', 'R', 'S'], none⟩]⟩, ⟨['b', 'a', 's', 'h', 'o', '-', 'd', 'e'], ['p', 'l', 'a', 'c', 'e', '-', 'L', 'O', 'C'], [⟨['b', 'a', 's', 'h', 'o'], ['p', 'l', 'a', 'c', 'e'], none⟩, ⟨['d', 'e'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['k', 'a', 'g', 'i', '-', 'o'], ['k', 'e', 'y', '-', 'A', 'C', 'C'], [⟨['k', 'a', 'g', 'i'], ['k', 'e', 'y'], none⟩, ⟨['o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['n', 'a', 'k', 'u', 's', 'i', 't', 'a'], ['l', 'o', 's', 'e', '.', 'P', 'S', 'T'], [⟨['n', 'a', 'k', 'u', 's', 'i', 't', 'a'], ['l', 'o', 's', 'e', '.', 'P', 'S', 'T'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("habitual", .acceptable)]
    paperFeatures := [("clause", "relative"), ("matrixTense", "past"), ("embeddedTense", "present")] }

def ex_35b : Datum :=
  { id := "arreguikusumoto1998_35b"
    source := ⟨"arregui-kusumoto-1998", "(35b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Junko-wa Satoshi-ga kuruma-o tyushasita basho-de kagi-o nakusita."
    glossedTokens := [("Junko-wa", "Junko-TOP"), ("Satoshi-ga", "Satoshi-NOM"), ("kuruma-o", "car-ACC"), ("tyushasita", "park.PST"), ("basho-de", "place-LOC"), ("kagi-o", "key-ACC"), ("nakusita", "lose.PST")]
    glossedWords := [⟨['J', 'u', 'n', 'k', 'o', '-', 'w', 'a'], ['J', 'u', 'n', 'k', 'o', '-', 'T', 'O', 'P'], [⟨['J', 'u', 'n', 'k', 'o'], ['J', 'u', 'n', 'k', 'o'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['S', 'a', 't', 'o', 's', 'h', 'i', '-', 'g', 'a'], ['S', 'a', 't', 'o', 's', 'h', 'i', '-', 'N', 'O', 'M'], [⟨['S', 'a', 't', 'o', 's', 'h', 'i'], ['S', 'a', 't', 'o', 's', 'h', 'i'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['k', 'u', 'r', 'u', 'm', 'a', '-', 'o'], ['c', 'a', 'r', '-', 'A', 'C', 'C'], [⟨['k', 'u', 'r', 'u', 'm', 'a'], ['c', 'a', 'r'], none⟩, ⟨['o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['t', 'y', 'u', 's', 'h', 'a', 's', 'i', 't', 'a'], ['p', 'a', 'r', 'k', '.', 'P', 'S', 'T'], [⟨['t', 'y', 'u', 's', 'h', 'a', 's', 'i', 't', 'a'], ['p', 'a', 'r', 'k', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['b', 'a', 's', 'h', 'o', '-', 'd', 'e'], ['p', 'l', 'a', 'c', 'e', '-', 'L', 'O', 'C'], [⟨['b', 'a', 's', 'h', 'o'], ['p', 'l', 'a', 'c', 'e'], none⟩, ⟨['d', 'e'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['k', 'a', 'g', 'i', '-', 'o'], ['k', 'e', 'y', '-', 'A', 'C', 'C'], [⟨['k', 'a', 'g', 'i'], ['k', 'e', 'y'], none⟩, ⟨['o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['n', 'a', 'k', 'u', 's', 'i', 't', 'a'], ['l', 'o', 's', 'e', '.', 'P', 'S', 'T'], [⟨['n', 'a', 'k', 'u', 's', 'i', 't', 'a'], ['l', 'o', 's', 'e', '.', 'P', 'S', 'T'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("episodic", .acceptable)]
    paperFeatures := [("clause", "relative"), ("matrixTense", "past"), ("embeddedTense", "past")] }

def ex_36a : Datum :=
  { id := "arreguikusumoto1998_36a"
    source := ⟨"arregui-kusumoto-1998", "(36a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Maisyuu kuru hito-wa Hanako-to Taroo desita."
    glossedTokens := [("Maisyuu", "every.week"), ("kuru", "come.PRS"), ("hito-wa", "people-TOP"), ("Hanako-to", "Hanako-and"), ("Taroo", "Taroo"), ("desita", "be.PST")]
    glossedWords := [⟨['M', 'a', 'i', 's', 'y', 'u', 'u'], ['e', 'v', 'e', 'r', 'y', '.', 'w', 'e', 'e', 'k'], [⟨['M', 'a', 'i', 's', 'y', 'u', 'u'], ['e', 'v', 'e', 'r', 'y', '.', 'w', 'e', 'e', 'k'], none⟩]⟩, ⟨['k', 'u', 'r', 'u'], ['c', 'o', 'm', 'e', '.', 'P', 'R', 'S'], [⟨['k', 'u', 'r', 'u'], ['c', 'o', 'm', 'e', '.', 'P', 'R', 'S'], none⟩]⟩, ⟨['h', 'i', 't', 'o', '-', 'w', 'a'], ['p', 'e', 'o', 'p', 'l', 'e', '-', 'T', 'O', 'P'], [⟨['h', 'i', 't', 'o'], ['p', 'e', 'o', 'p', 'l', 'e'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['H', 'a', 'n', 'a', 'k', 'o', '-', 't', 'o'], ['H', 'a', 'n', 'a', 'k', 'o', '-', 'a', 'n', 'd'], [⟨['H', 'a', 'n', 'a', 'k', 'o'], ['H', 'a', 'n', 'a', 'k', 'o'], none⟩, ⟨['t', 'o'], ['a', 'n', 'd'], some '-'⟩]⟩, ⟨['T', 'a', 'r', 'o', 'o'], ['T', 'a', 'r', 'o', 'o'], [⟨['T', 'a', 'r', 'o', 'o'], ['T', 'a', 'r', 'o', 'o'], none⟩]⟩, ⟨['d', 'e', 's', 'i', 't', 'a'], ['b', 'e', '.', 'P', 'S', 'T'], [⟨['d', 'e', 's', 'i', 't', 'a'], ['b', 'e', '.', 'P', 'S', 'T'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("habitual", .acceptable)]
    paperFeatures := [("clause", "relative"), ("matrixTense", "past"), ("embeddedTense", "present")] }

def ex_36b : Datum :=
  { id := "arreguikusumoto1998_36b"
    source := ⟨"arregui-kusumoto-1998", "(36b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Maisyuu kita hito-wa Hanako-to Taroo desita."
    glossedTokens := [("Maisyuu", "every.week"), ("kita", "come.PST"), ("hito-wa", "people-TOP"), ("Hanako-to", "Hanako-and"), ("Taroo", "Taroo"), ("desita", "be.PST")]
    glossedWords := [⟨['M', 'a', 'i', 's', 'y', 'u', 'u'], ['e', 'v', 'e', 'r', 'y', '.', 'w', 'e', 'e', 'k'], [⟨['M', 'a', 'i', 's', 'y', 'u', 'u'], ['e', 'v', 'e', 'r', 'y', '.', 'w', 'e', 'e', 'k'], none⟩]⟩, ⟨['k', 'i', 't', 'a'], ['c', 'o', 'm', 'e', '.', 'P', 'S', 'T'], [⟨['k', 'i', 't', 'a'], ['c', 'o', 'm', 'e', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['h', 'i', 't', 'o', '-', 'w', 'a'], ['p', 'e', 'o', 'p', 'l', 'e', '-', 'T', 'O', 'P'], [⟨['h', 'i', 't', 'o'], ['p', 'e', 'o', 'p', 'l', 'e'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['H', 'a', 'n', 'a', 'k', 'o', '-', 't', 'o'], ['H', 'a', 'n', 'a', 'k', 'o', '-', 'a', 'n', 'd'], [⟨['H', 'a', 'n', 'a', 'k', 'o'], ['H', 'a', 'n', 'a', 'k', 'o'], none⟩, ⟨['t', 'o'], ['a', 'n', 'd'], some '-'⟩]⟩, ⟨['T', 'a', 'r', 'o', 'o'], ['T', 'a', 'r', 'o', 'o'], [⟨['T', 'a', 'r', 'o', 'o'], ['T', 'a', 'r', 'o', 'o'], none⟩]⟩, ⟨['d', 'e', 's', 'i', 't', 'a'], ['b', 'e', '.', 'P', 'S', 'T'], [⟨['d', 'e', 's', 'i', 't', 'a'], ['b', 'e', '.', 'P', 'S', 'T'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("episodic", .acceptable)]
    paperFeatures := [("clause", "relative"), ("matrixTense", "past"), ("embeddedTense", "past")] }

def fn1_i : Datum :=
  { id := "arreguikusumoto1998_fn1_i"
    source := ⟨"arregui-kusumoto-1998", "fn. 1 (i)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Junko-wa asita Berlin-ni kuru."
    glossedTokens := [("Junko-wa", "Junko-TOP"), ("asita", "tomorrow"), ("Berlin-ni", "Berlin-to"), ("kuru", "come.PRS")]
    glossedWords := [⟨['J', 'u', 'n', 'k', 'o', '-', 'w', 'a'], ['J', 'u', 'n', 'k', 'o', '-', 'T', 'O', 'P'], [⟨['J', 'u', 'n', 'k', 'o'], ['J', 'u', 'n', 'k', 'o'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['a', 's', 'i', 't', 'a'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['a', 's', 'i', 't', 'a'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩, ⟨['B', 'e', 'r', 'l', 'i', 'n', '-', 'n', 'i'], ['B', 'e', 'r', 'l', 'i', 'n', '-', 't', 'o'], [⟨['B', 'e', 'r', 'l', 'i', 'n'], ['B', 'e', 'r', 'l', 'i', 'n'], none⟩, ⟨['n', 'i'], ['t', 'o'], some '-'⟩]⟩, ⟨['k', 'u', 'r', 'u'], ['c', 'o', 'm', 'e', '.', 'P', 'R', 'S'], [⟨['k', 'u', 'r', 'u'], ['c', 'o', 'm', 'e', '.', 'P', 'R', 'S'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("future", .acceptable)]
    paperFeatures := [("clause", "root"), ("tense", "present")] }

def fn3_ia : Datum :=
  { id := "arreguikusumoto1998_fn3_ia"
    source := ⟨"arregui-kusumoto-1998", "fn. 3 (i-a)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Ania przyszła na przyjęcie po tym jak Marcin wyszedł."
    glossedTokens := [("Ania", "Ania"), ("przyszła", "PFV-come-PST"), ("na", "to"), ("przyjęcie", "party"), ("po tym jak", "after this how"), ("Marcin", "Marcin"), ("wyszedł", "PFV-leave-PST")]
    glossedWords := [⟨['A', 'n', 'i', 'a'], ['A', 'n', 'i', 'a'], [⟨['A', 'n', 'i', 'a'], ['A', 'n', 'i', 'a'], none⟩]⟩, ⟨['p', 'r', 'z', 'y', 's', 'z', 'ł', 'a'], ['P', 'F', 'V', '-', 'c', 'o', 'm', 'e', '-', 'P', 'S', 'T'], []⟩, ⟨['n', 'a'], ['t', 'o'], [⟨['n', 'a'], ['t', 'o'], none⟩]⟩, ⟨['p', 'r', 'z', 'y', 'j', 'ę', 'c', 'i', 'e'], ['p', 'a', 'r', 't', 'y'], [⟨['p', 'r', 'z', 'y', 'j', 'ę', 'c', 'i', 'e'], ['p', 'a', 'r', 't', 'y'], none⟩]⟩, ⟨['p', 'o', ' ', 't', 'y', 'm', ' ', 'j', 'a', 'k'], ['a', 'f', 't', 'e', 'r', ' ', 't', 'h', 'i', 's', ' ', 'h', 'o', 'w'], [⟨['p', 'o', ' ', 't', 'y', 'm', ' ', 'j', 'a', 'k'], ['a', 'f', 't', 'e', 'r', ' ', 't', 'h', 'i', 's', ' ', 'h', 'o', 'w'], none⟩]⟩, ⟨['M', 'a', 'r', 'c', 'i', 'n'], ['M', 'a', 'r', 'c', 'i', 'n'], [⟨['M', 'a', 'r', 'c', 'i', 'n'], ['M', 'a', 'r', 'c', 'i', 'n'], none⟩]⟩, ⟨['w', 'y', 's', 'z', 'e', 'd', 'ł'], ['P', 'F', 'V', '-', 'l', 'e', 'a', 'v', 'e', '-', 'P', 'S', 'T'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "after"), ("connective", "po tym jak"), ("matrixTense", "past"), ("embeddedTense", "past")] }

def fn3_ib : Datum :=
  { id := "arreguikusumoto1998_fn3_ib"
    source := ⟨"arregui-kusumoto-1998", "fn. 3 (i-b)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Ania przyszła na przyjęcie po tym jak Marcin wychodzi."
    glossedTokens := [("Ania", "Ania"), ("przyszła", "PFV-come-PST"), ("na", "to"), ("przyjęcie", "party"), ("po tym jak", "after this how"), ("Marcin", "Marcin"), ("wychodzi", "PFV-leave-PRS")]
    glossedWords := [⟨['A', 'n', 'i', 'a'], ['A', 'n', 'i', 'a'], [⟨['A', 'n', 'i', 'a'], ['A', 'n', 'i', 'a'], none⟩]⟩, ⟨['p', 'r', 'z', 'y', 's', 'z', 'ł', 'a'], ['P', 'F', 'V', '-', 'c', 'o', 'm', 'e', '-', 'P', 'S', 'T'], []⟩, ⟨['n', 'a'], ['t', 'o'], [⟨['n', 'a'], ['t', 'o'], none⟩]⟩, ⟨['p', 'r', 'z', 'y', 'j', 'ę', 'c', 'i', 'e'], ['p', 'a', 'r', 't', 'y'], [⟨['p', 'r', 'z', 'y', 'j', 'ę', 'c', 'i', 'e'], ['p', 'a', 'r', 't', 'y'], none⟩]⟩, ⟨['p', 'o', ' ', 't', 'y', 'm', ' ', 'j', 'a', 'k'], ['a', 'f', 't', 'e', 'r', ' ', 't', 'h', 'i', 's', ' ', 'h', 'o', 'w'], [⟨['p', 'o', ' ', 't', 'y', 'm', ' ', 'j', 'a', 'k'], ['a', 'f', 't', 'e', 'r', ' ', 't', 'h', 'i', 's', ' ', 'h', 'o', 'w'], none⟩]⟩, ⟨['M', 'a', 'r', 'c', 'i', 'n'], ['M', 'a', 'r', 'c', 'i', 'n'], [⟨['M', 'a', 'r', 'c', 'i', 'n'], ['M', 'a', 'r', 'c', 'i', 'n'], none⟩]⟩, ⟨['w', 'y', 'c', 'h', 'o', 'd', 'z', 'i'], ['P', 'F', 'V', '-', 'l', 'e', 'a', 'v', 'e', '-', 'P', 'R', 'S'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "after"), ("connective", "po tym jak"), ("matrixTense", "past"), ("embeddedTense", "present")] }

def all : List Datum := [ex_1, ex_3, ex_4, ex_5a, ex_5b, ex_6a, ex_6b, ex_7a, ex_7b, ex_8, ex_9, ex_10a, ex_10b, ex_10c, ex_11a, ex_11b, ex_11c, ex_12a, ex_13a, ex_14, ex_18a, ex_18b, ex_20a, ex_20b, ex_22a, ex_22b, ex_24a, ex_25a, ex_26a, ex_26b, ex_32, ex_35a, ex_35b, ex_36a, ex_36b, fn1_i, fn3_ia, fn3_ib]

end ArreguiKusumoto1998.Examples
