module

public import Linglib.Data.Examples.Schema

/-!
# `Wood2015` — typed example data

Auto-generated from `Linglib/Data/Examples/Wood2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Wood2015.Examples`.
-/

@[expose] public section

namespace Wood2015.Examples

def ex_1 : Datum :=
  { id := "wood2015_1"
    source := ⟨"wood-2015", "Ch. 2 (1a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Jóna og Siggi kysstust eftir ballið."
    glossedTokens := [("Jóna", "Jóna.NOM"), ("og", "and"), ("Siggi", "Siggi.NOM"), ("kysstust", "kissed-ST"), ("eftir", "after"), ("ballið", "dance.the")]
    glossedWords := [⟨['J', 'ó', 'n', 'a'], ['J', 'ó', 'n', 'a', '.', 'N', 'O', 'M'], [⟨['J', 'ó', 'n', 'a'], ['J', 'ó', 'n', 'a', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['o', 'g'], ['a', 'n', 'd'], [⟨['o', 'g'], ['a', 'n', 'd'], none⟩]⟩, ⟨['S', 'i', 'g', 'g', 'i'], ['S', 'i', 'g', 'g', 'i', '.', 'N', 'O', 'M'], [⟨['S', 'i', 'g', 'g', 'i'], ['S', 'i', 'g', 'g', 'i', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['k', 'y', 's', 's', 't', 'u', 's', 't'], ['k', 'i', 's', 's', 'e', 'd', '-', 'S', 'T'], []⟩, ⟨['e', 'f', 't', 'i', 'r'], ['a', 'f', 't', 'e', 'r'], [⟨['e', 'f', 't', 'i', 'r'], ['a', 'f', 't', 'e', 'r'], none⟩]⟩, ⟨['b', 'a', 'l', 'l', 'i', 'ð'], ['d', 'a', 'n', 'c', 'e', '.', 't', 'h', 'e'], [⟨['b', 'a', 'l', 'l', 'i', 'ð'], ['d', 'a', 'n', 'c', 'e', '.', 't', 'h', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("use", "reciprocal")] }

def ex_2 : Datum :=
  { id := "wood2015_2"
    source := ⟨"wood-2015", "Ch. 2 (1b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Jón dulbjóst sem prestur."
    glossedTokens := [("Jón", "John.NOM"), ("dulbjóst", "disguised-ST"), ("sem", "as"), ("prestur", "priest")]
    glossedWords := [⟨['J', 'ó', 'n'], ['J', 'o', 'h', 'n', '.', 'N', 'O', 'M'], [⟨['J', 'ó', 'n'], ['J', 'o', 'h', 'n', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['d', 'u', 'l', 'b', 'j', 'ó', 's', 't'], ['d', 'i', 's', 'g', 'u', 'i', 's', 'e', 'd', '-', 'S', 'T'], []⟩, ⟨['s', 'e', 'm'], ['a', 's'], [⟨['s', 'e', 'm'], ['a', 's'], none⟩]⟩, ⟨['p', 'r', 'e', 's', 't', 'u', 'r'], ['p', 'r', 'i', 'e', 's', 't'], [⟨['p', 'r', 'e', 's', 't', 'u', 'r'], ['p', 'r', 'i', 'e', 's', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("use", "reflexive")] }

def ex_3 : Datum :=
  { id := "wood2015_3"
    source := ⟨"wood-2015", "Ch. 2 (1c)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Glugginn opnaðist af sjálfu sér."
    glossedTokens := [("Glugginn", "window.the.NOM"), ("opnaðist", "opened-ST"), ("af sjálfu sér", "by itself")]
    glossedWords := [⟨['G', 'l', 'u', 'g', 'g', 'i', 'n', 'n'], ['w', 'i', 'n', 'd', 'o', 'w', '.', 't', 'h', 'e', '.', 'N', 'O', 'M'], [⟨['G', 'l', 'u', 'g', 'g', 'i', 'n', 'n'], ['w', 'i', 'n', 'd', 'o', 'w', '.', 't', 'h', 'e', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['o', 'p', 'n', 'a', 'ð', 'i', 's', 't'], ['o', 'p', 'e', 'n', 'e', 'd', '-', 'S', 'T'], []⟩, ⟨['a', 'f', ' ', 's', 'j', 'á', 'l', 'f', 'u', ' ', 's', 'é', 'r'], ['b', 'y', ' ', 'i', 't', 's', 'e', 'l', 'f'], [⟨['a', 'f', ' ', 's', 'j', 'á', 'l', 'f', 'u', ' ', 's', 'é', 'r'], ['b', 'y', ' ', 'i', 't', 's', 'e', 'l', 'f'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("use", "anticausative")] }

def ex_4 : Datum :=
  { id := "wood2015_4"
    source := ⟨"wood-2015", "Ch. 2 (1d)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Rafmagnsbílar seljast (vel) hér."
    glossedTokens := [("Rafmagnsbílar", "electric.cars.NOM"), ("seljast", "sell-ST"), ("(vel)", "(well)"), ("hér", "here")]
    glossedWords := [⟨['R', 'a', 'f', 'm', 'a', 'g', 'n', 's', 'b', 'í', 'l', 'a', 'r'], ['e', 'l', 'e', 'c', 't', 'r', 'i', 'c', '.', 'c', 'a', 'r', 's', '.', 'N', 'O', 'M'], [⟨['R', 'a', 'f', 'm', 'a', 'g', 'n', 's', 'b', 'í', 'l', 'a', 'r'], ['e', 'l', 'e', 'c', 't', 'r', 'i', 'c', '.', 'c', 'a', 'r', 's', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['s', 'e', 'l', 'j', 'a', 's', 't'], ['s', 'e', 'l', 'l', '-', 'S', 'T'], []⟩, ⟨['(', 'v', 'e', 'l', ')'], ['(', 'w', 'e', 'l', 'l', ')'], [⟨['v', 'e', 'l'], ['(', 'w', 'e', 'l', 'l', ')'], none⟩]⟩, ⟨['h', 'é', 'r'], ['h', 'e', 'r', 'e'], [⟨['h', 'é', 'r'], ['h', 'e', 'r', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("use", "generic middle")] }

def ex_5 : Datum :=
  { id := "wood2015_5"
    source := ⟨"wood-2015", "Ch. 3 (16a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Fólk dýp-ka-ði skurðinn."
    glossedTokens := [("Fólk", "people.NOM"), ("dýp-ka-ði", "deep-KA-ed"), ("skurðinn", "ditch.the.ACC")]
    glossedWords := [⟨['F', 'ó', 'l', 'k'], ['p', 'e', 'o', 'p', 'l', 'e', '.', 'N', 'O', 'M'], [⟨['F', 'ó', 'l', 'k'], ['p', 'e', 'o', 'p', 'l', 'e', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['d', 'ý', 'p', '-', 'k', 'a', '-', 'ð', 'i'], ['d', 'e', 'e', 'p', '-', 'K', 'A', '-', 'e', 'd'], [⟨['d', 'ý', 'p'], ['d', 'e', 'e', 'p'], none⟩, ⟨['k', 'a'], ['K', 'A'], some '-'⟩, ⟨['ð', 'i'], ['e', 'd'], some '-'⟩]⟩, ⟨['s', 'k', 'u', 'r', 'ð', 'i', 'n', 'n'], ['d', 'i', 't', 'c', 'h', '.', 't', 'h', 'e', '.', 'A', 'C', 'C'], [⟨['s', 'k', 'u', 'r', 'ð', 'i', 'n', 'n'], ['d', 'i', 't', 'c', 'h', '.', 't', 'h', 'e', '.', 'A', 'C', 'C'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("exponent", "-ka"), ("voice", "Voice{D}")] }

def ex_6 : Datum :=
  { id := "wood2015_6"
    source := ⟨"wood-2015", "Ch. 3 (16b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Skurðurinn dýp-ka-ði."
    glossedTokens := [("Skurðurinn", "ditch.the.NOM"), ("dýp-ka-ði", "deep-KA-ed")]
    glossedWords := [⟨['S', 'k', 'u', 'r', 'ð', 'u', 'r', 'i', 'n', 'n'], ['d', 'i', 't', 'c', 'h', '.', 't', 'h', 'e', '.', 'N', 'O', 'M'], [⟨['S', 'k', 'u', 'r', 'ð', 'u', 'r', 'i', 'n', 'n'], ['d', 'i', 't', 'c', 'h', '.', 't', 'h', 'e', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['d', 'ý', 'p', '-', 'k', 'a', '-', 'ð', 'i'], ['d', 'e', 'e', 'p', '-', 'K', 'A', '-', 'e', 'd'], [⟨['d', 'ý', 'p'], ['d', 'e', 'e', 'p'], none⟩, ⟨['k', 'a'], ['K', 'A'], some '-'⟩, ⟨['ð', 'i'], ['e', 'd'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("exponent", "-ka"), ("voice", "Voice{}")] }

def ex_7 : Datum :=
  { id := "wood2015_7"
    source := ⟨"wood-2015", "Ch. 3 (20a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Jón hita-ði vatnið."
    glossedTokens := [("Jón", "John.NOM"), ("hita-ði", "heat-3SG.PST"), ("vatnið", "water.the.ACC")]
    glossedWords := [⟨['J', 'ó', 'n'], ['J', 'o', 'h', 'n', '.', 'N', 'O', 'M'], [⟨['J', 'ó', 'n'], ['J', 'o', 'h', 'n', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['h', 'i', 't', 'a', '-', 'ð', 'i'], ['h', 'e', 'a', 't', '-', '3', 'S', 'G', '.', 'P', 'S', 'T'], [⟨['h', 'i', 't', 'a'], ['h', 'e', 'a', 't'], none⟩, ⟨['ð', 'i'], ['3', 'S', 'G', '.', 'P', 'S', 'T'], some '-'⟩]⟩, ⟨['v', 'a', 't', 'n', 'i', 'ð'], ['w', 'a', 't', 'e', 'r', '.', 't', 'h', 'e', '.', 'A', 'C', 'C'], [⟨['v', 'a', 't', 'n', 'i', 'ð'], ['w', 'a', 't', 'e', 'r', '.', 't', 'h', 'e', '.', 'A', 'C', 'C'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("voice", "Voice{D}")] }

def ex_8 : Datum :=
  { id := "wood2015_8"
    source := ⟨"wood-2015", "Ch. 3 (20b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Vatnið hit-na-ði."
    glossedTokens := [("Vatnið", "water.the.NOM"), ("hit-na-ði", "heat-NA-3SG.PST")]
    glossedWords := [⟨['V', 'a', 't', 'n', 'i', 'ð'], ['w', 'a', 't', 'e', 'r', '.', 't', 'h', 'e', '.', 'N', 'O', 'M'], [⟨['V', 'a', 't', 'n', 'i', 'ð'], ['w', 'a', 't', 'e', 'r', '.', 't', 'h', 'e', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['h', 'i', 't', '-', 'n', 'a', '-', 'ð', 'i'], ['h', 'e', 'a', 't', '-', 'N', 'A', '-', '3', 'S', 'G', '.', 'P', 'S', 'T'], [⟨['h', 'i', 't'], ['h', 'e', 'a', 't'], none⟩, ⟨['n', 'a'], ['N', 'A'], some '-'⟩, ⟨['ð', 'i'], ['3', 'S', 'G', '.', 'P', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("exponent", "-na"), ("voice", "Voice{}")] }

def ex_9 : Datum :=
  { id := "wood2015_9"
    source := ⟨"wood-2015", "Ch. 3 (52)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Dyrnar opnuðust."
    glossedTokens := [("Dyrnar", "door.the.NOM"), ("opnuðust", "opened-ST")]
    glossedWords := [⟨['D', 'y', 'r', 'n', 'a', 'r'], ['d', 'o', 'o', 'r', '.', 't', 'h', 'e', '.', 'N', 'O', 'M'], [⟨['D', 'y', 'r', 'n', 'a', 'r'], ['d', 'o', 'o', 'r', '.', 't', 'h', 'e', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['o', 'p', 'n', 'u', 'ð', 'u', 's', 't'], ['o', 'p', 'e', 'n', 'e', 'd', '-', 'S', 'T'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("use", "anticausative"), ("site", "SpecVoiceP")] }

def ex_10 : Datum :=
  { id := "wood2015_10"
    source := ⟨"wood-2015", "Ch. 3 (70)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Rúðan splundraðist."
    glossedTokens := [("Rúðan", "window.the.NOM"), ("splundraðist", "shattered-ST")]
    glossedWords := [⟨['R', 'ú', 'ð', 'a', 'n'], ['w', 'i', 'n', 'd', 'o', 'w', '.', 't', 'h', 'e', '.', 'N', 'O', 'M'], [⟨['R', 'ú', 'ð', 'a', 'n'], ['w', 'i', 'n', 'd', 'o', 'w', '.', 't', 'h', 'e', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['s', 'p', 'l', 'u', 'n', 'd', 'r', 'a', 'ð', 'i', 's', 't'], ['s', 'h', 'a', 't', 't', 'e', 'r', 'e', 'd', '-', 'S', 'T'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("use", "anticausative"), ("site", "SpecVoiceP")] }

def ex_11 : Datum :=
  { id := "wood2015_11"
    source := ⟨"wood-2015", "Ch. 3 (72a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Konan myrti manninn."
    glossedTokens := [("Konan", "woman.the.NOM"), ("myrti", "murdered"), ("manninn", "man.the.ACC")]
    glossedWords := [⟨['K', 'o', 'n', 'a', 'n'], ['w', 'o', 'm', 'a', 'n', '.', 't', 'h', 'e', '.', 'N', 'O', 'M'], [⟨['K', 'o', 'n', 'a', 'n'], ['w', 'o', 'm', 'a', 'n', '.', 't', 'h', 'e', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['m', 'y', 'r', 't', 'i'], ['m', 'u', 'r', 'd', 'e', 'r', 'e', 'd'], [⟨['m', 'y', 'r', 't', 'i'], ['m', 'u', 'r', 'd', 'e', 'r', 'e', 'd'], none⟩]⟩, ⟨['m', 'a', 'n', 'n', 'i', 'n', 'n'], ['m', 'a', 'n', '.', 't', 'h', 'e', '.', 'A', 'C', 'C'], [⟨['m', 'a', 'n', 'n', 'i', 'n', 'n'], ['m', 'a', 'n', '.', 't', 'h', 'e', '.', 'A', 'C', 'C'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("voice", "agentive")] }

def ex_12 : Datum :=
  { id := "wood2015_12"
    source := ⟨"wood-2015", "Ch. 3 (72b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Hraunstraumurinn myrti manninn."
    glossedTokens := [("Hraunstraumurinn", "lava.stream.the.NOM"), ("myrti", "murdered"), ("manninn", "man.the.ACC")]
    glossedWords := [⟨['H', 'r', 'a', 'u', 'n', 's', 't', 'r', 'a', 'u', 'm', 'u', 'r', 'i', 'n', 'n'], ['l', 'a', 'v', 'a', '.', 's', 't', 'r', 'e', 'a', 'm', '.', 't', 'h', 'e', '.', 'N', 'O', 'M'], [⟨['H', 'r', 'a', 'u', 'n', 's', 't', 'r', 'a', 'u', 'm', 'u', 'r', 'i', 'n', 'n'], ['l', 'a', 'v', 'a', '.', 's', 't', 'r', 'e', 'a', 'm', '.', 't', 'h', 'e', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['m', 'y', 'r', 't', 'i'], ['m', 'u', 'r', 'd', 'e', 'r', 'e', 'd'], [⟨['m', 'y', 'r', 't', 'i'], ['m', 'u', 'r', 'd', 'e', 'r', 'e', 'd'], none⟩]⟩, ⟨['m', 'a', 'n', 'n', 'i', 'n', 'n'], ['m', 'a', 'n', '.', 't', 'h', 'e', '.', 'A', 'C', 'C'], [⟨['m', 'a', 'n', 'n', 'i', 'n', 'n'], ['m', 'a', 'n', '.', 't', 'h', 'e', '.', 'A', 'C', 'C'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("voice", "agentive")] }

def ex_13 : Datum :=
  { id := "wood2015_13"
    source := ⟨"wood-2015", "Ch. 3 (72c)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Maðurinn myrti(st)."
    glossedTokens := [("Maðurinn", "man.the.NOM"), ("myrti(st)", "murdered-ST")]
    glossedWords := [⟨['M', 'a', 'ð', 'u', 'r', 'i', 'n', 'n'], ['m', 'a', 'n', '.', 't', 'h', 'e', '.', 'N', 'O', 'M'], [⟨['M', 'a', 'ð', 'u', 'r', 'i', 'n', 'n'], ['m', 'a', 'n', '.', 't', 'h', 'e', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['m', 'y', 'r', 't', 'i', '(', 's', 't', ')'], ['m', 'u', 'r', 'd', 'e', 'r', 'e', 'd', '-', 'S', 'T'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("use", "anticausative")] }

def ex_14 : Datum :=
  { id := "wood2015_14"
    source := ⟨"wood-2015", "Ch. 5 (47a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Bjartur gaf sjálfum sér bókina í jólagjöf."
    glossedTokens := [("Bjartur", "Bjartur.NOM"), ("gaf", "gave"), ("sjálfum", "self"), ("sér", "REFL.DAT"), ("bókina", "book.the.ACC"), ("í", "in"), ("jólagjöf", "christmas.gift")]
    glossedWords := [⟨['B', 'j', 'a', 'r', 't', 'u', 'r'], ['B', 'j', 'a', 'r', 't', 'u', 'r', '.', 'N', 'O', 'M'], [⟨['B', 'j', 'a', 'r', 't', 'u', 'r'], ['B', 'j', 'a', 'r', 't', 'u', 'r', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['g', 'a', 'f'], ['g', 'a', 'v', 'e'], [⟨['g', 'a', 'f'], ['g', 'a', 'v', 'e'], none⟩]⟩, ⟨['s', 'j', 'á', 'l', 'f', 'u', 'm'], ['s', 'e', 'l', 'f'], [⟨['s', 'j', 'á', 'l', 'f', 'u', 'm'], ['s', 'e', 'l', 'f'], none⟩]⟩, ⟨['s', 'é', 'r'], ['R', 'E', 'F', 'L', '.', 'D', 'A', 'T'], [⟨['s', 'é', 'r'], ['R', 'E', 'F', 'L', '.', 'D', 'A', 'T'], none⟩]⟩, ⟨['b', 'ó', 'k', 'i', 'n', 'a'], ['b', 'o', 'o', 'k', '.', 't', 'h', 'e', '.', 'A', 'C', 'C'], [⟨['b', 'ó', 'k', 'i', 'n', 'a'], ['b', 'o', 'o', 'k', '.', 't', 'h', 'e', '.', 'A', 'C', 'C'], none⟩]⟩, ⟨['í'], ['i', 'n'], [⟨['í'], ['i', 'n'], none⟩]⟩, ⟨['j', 'ó', 'l', 'a', 'g', 'j', 'ö', 'f'], ['c', 'h', 'r', 'i', 's', 't', 'm', 'a', 's', '.', 'g', 'i', 'f', 't'], [⟨['j', 'ó', 'l', 'a', 'g', 'j', 'ö', 'f'], ['c', 'h', 'r', 'i', 's', 't', 'm', 'a', 's', '.', 'g', 'i', 'f', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("position", "SpecApplP")] }

def ex_15 : Datum :=
  { id := "wood2015_15"
    source := ⟨"wood-2015", "Ch. 5 (47b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Bjartur gafst bókina í jólagjöf."
    glossedTokens := [("Bjartur", "Bjartur.NOM"), ("gafst", "gave-ST"), ("bókina", "book.the.ACC"), ("í", "in"), ("jólagjöf", "christmas.gift")]
    glossedWords := [⟨['B', 'j', 'a', 'r', 't', 'u', 'r'], ['B', 'j', 'a', 'r', 't', 'u', 'r', '.', 'N', 'O', 'M'], [⟨['B', 'j', 'a', 'r', 't', 'u', 'r'], ['B', 'j', 'a', 'r', 't', 'u', 'r', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['g', 'a', 'f', 's', 't'], ['g', 'a', 'v', 'e', '-', 'S', 'T'], []⟩, ⟨['b', 'ó', 'k', 'i', 'n', 'a'], ['b', 'o', 'o', 'k', '.', 't', 'h', 'e', '.', 'A', 'C', 'C'], [⟨['b', 'ó', 'k', 'i', 'n', 'a'], ['b', 'o', 'o', 'k', '.', 't', 'h', 'e', '.', 'A', 'C', 'C'], none⟩]⟩, ⟨['í'], ['i', 'n'], [⟨['í'], ['i', 'n'], none⟩]⟩, ⟨['j', 'ó', 'l', 'a', 'g', 'j', 'ö', 'f'], ['c', 'h', 'r', 'i', 's', 't', 'm', 'a', 's', '.', 'g', 'i', 'f', 't'], [⟨['j', 'ó', 'l', 'a', 'g', 'j', 'ö', 'f'], ['c', 'h', 'r', 'i', 's', 't', 'm', 'a', 's', '.', 'g', 'i', 'f', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("position", "SpecApplP")] }

def ex_16 : Datum :=
  { id := "wood2015_16"
    source := ⟨"wood-2015", "Ch. 5 (52a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Fólk leyfði þeim alla hluti."
    glossedTokens := [("Fólk", "people.NOM"), ("leyfði", "allowed"), ("þeim", "them.DAT"), ("alla", "all"), ("hluti", "things.ACC")]
    glossedWords := [⟨['F', 'ó', 'l', 'k'], ['p', 'e', 'o', 'p', 'l', 'e', '.', 'N', 'O', 'M'], [⟨['F', 'ó', 'l', 'k'], ['p', 'e', 'o', 'p', 'l', 'e', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['l', 'e', 'y', 'f', 'ð', 'i'], ['a', 'l', 'l', 'o', 'w', 'e', 'd'], [⟨['l', 'e', 'y', 'f', 'ð', 'i'], ['a', 'l', 'l', 'o', 'w', 'e', 'd'], none⟩]⟩, ⟨['þ', 'e', 'i', 'm'], ['t', 'h', 'e', 'm', '.', 'D', 'A', 'T'], [⟨['þ', 'e', 'i', 'm'], ['t', 'h', 'e', 'm', '.', 'D', 'A', 'T'], none⟩]⟩, ⟨['a', 'l', 'l', 'a'], ['a', 'l', 'l'], [⟨['a', 'l', 'l', 'a'], ['a', 'l', 'l'], none⟩]⟩, ⟨['h', 'l', 'u', 't', 'i'], ['t', 'h', 'i', 'n', 'g', 's', '.', 'A', 'C', 'C'], [⟨['h', 'l', 'u', 't', 'i'], ['t', 'h', 'i', 'n', 'g', 's', '.', 'A', 'C', 'C'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("dative", "Appl")] }

def ex_17 : Datum :=
  { id := "wood2015_17"
    source := ⟨"wood-2015", "Ch. 5 (52b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Þeim leyfðust allir hlutir."
    glossedTokens := [("Þeim", "them.DAT"), ("leyfðust", "allowed-ST"), ("allir", "all"), ("hlutir", "things.NOM")]
    glossedWords := [⟨['Þ', 'e', 'i', 'm'], ['t', 'h', 'e', 'm', '.', 'D', 'A', 'T'], [⟨['Þ', 'e', 'i', 'm'], ['t', 'h', 'e', 'm', '.', 'D', 'A', 'T'], none⟩]⟩, ⟨['l', 'e', 'y', 'f', 'ð', 'u', 's', 't'], ['a', 'l', 'l', 'o', 'w', 'e', 'd', '-', 'S', 'T'], []⟩, ⟨['a', 'l', 'l', 'i', 'r'], ['a', 'l', 'l'], [⟨['a', 'l', 'l', 'i', 'r'], ['a', 'l', 'l'], none⟩]⟩, ⟨['h', 'l', 'u', 't', 'i', 'r'], ['t', 'h', 'i', 'n', 'g', 's', '.', 'N', 'O', 'M'], [⟨['h', 'l', 'u', 't', 'i', 'r'], ['t', 'h', 'i', 'n', 'g', 's', '.', 'N', 'O', 'M'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("dative", "Appl")] }

def ex_18 : Datum :=
  { id := "wood2015_18"
    source := ⟨"wood-2015", "Ch. 5 (53a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Ásta splundraði rúðunni."
    glossedTokens := [("Ásta", "Ásta.NOM"), ("splundraði", "shattered"), ("rúðunni", "window.the.DAT")]
    glossedWords := [⟨['Á', 's', 't', 'a'], ['Á', 's', 't', 'a', '.', 'N', 'O', 'M'], [⟨['Á', 's', 't', 'a'], ['Á', 's', 't', 'a', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['s', 'p', 'l', 'u', 'n', 'd', 'r', 'a', 'ð', 'i'], ['s', 'h', 'a', 't', 't', 'e', 'r', 'e', 'd'], [⟨['s', 'p', 'l', 'u', 'n', 'd', 'r', 'a', 'ð', 'i'], ['s', 'h', 'a', 't', 't', 'e', 'r', 'e', 'd'], none⟩]⟩, ⟨['r', 'ú', 'ð', 'u', 'n', 'n', 'i'], ['w', 'i', 'n', 'd', 'o', 'w', '.', 't', 'h', 'e', '.', 'D', 'A', 'T'], [⟨['r', 'ú', 'ð', 'u', 'n', 'n', 'i'], ['w', 'i', 'n', 'd', 'o', 'w', '.', 't', 'h', 'e', '.', 'D', 'A', 'T'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("dative", "direct object")] }

def ex_19 : Datum :=
  { id := "wood2015_19"
    source := ⟨"wood-2015", "Ch. 5 (53b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Rúðan splundraðist."
    glossedTokens := [("Rúðan", "window.the.NOM"), ("splundraðist", "shattered-ST")]
    glossedWords := [⟨['R', 'ú', 'ð', 'a', 'n'], ['w', 'i', 'n', 'd', 'o', 'w', '.', 't', 'h', 'e', '.', 'N', 'O', 'M'], [⟨['R', 'ú', 'ð', 'a', 'n'], ['w', 'i', 'n', 'd', 'o', 'w', '.', 't', 'h', 'e', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['s', 'p', 'l', 'u', 'n', 'd', 'r', 'a', 'ð', 'i', 's', 't'], ['s', 'h', 'a', 't', 't', 'e', 'r', 'e', 'd', '-', 'S', 'T'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("dative", "direct object")] }

def ex_20 : Datum :=
  { id := "wood2015_20"
    source := ⟨"wood-2015", "Ch. 5 (92a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Henni leiddist Ólafur."
    glossedTokens := [("Henni", "her.DAT"), ("leiddist", "bored-ST"), ("Ólafur", "Ólafur.NOM")]
    glossedWords := [⟨['H', 'e', 'n', 'n', 'i'], ['h', 'e', 'r', '.', 'D', 'A', 'T'], [⟨['H', 'e', 'n', 'n', 'i'], ['h', 'e', 'r', '.', 'D', 'A', 'T'], none⟩]⟩, ⟨['l', 'e', 'i', 'd', 'd', 'i', 's', 't'], ['b', 'o', 'r', 'e', 'd', '-', 'S', 'T'], []⟩, ⟨['Ó', 'l', 'a', 'f', 'u', 'r'], ['Ó', 'l', 'a', 'f', 'u', 'r', '.', 'N', 'O', 'M'], [⟨['Ó', 'l', 'a', 'f', 'u', 'r'], ['Ó', 'l', 'a', 'f', 'u', 'r', '.', 'N', 'O', 'M'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("use", "subject experiencer"), ("site", "SpecVoiceP")] }

def ex_21 : Datum :=
  { id := "wood2015_21"
    source := ⟨"wood-2015", "Ch. 6 (55a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Jóna og Siggi kysstust."
    glossedTokens := [("Jóna", "Jóna"), ("og", "and"), ("Siggi", "Siggi"), ("kysstust", "kissed-ST")]
    glossedWords := [⟨['J', 'ó', 'n', 'a'], ['J', 'ó', 'n', 'a'], [⟨['J', 'ó', 'n', 'a'], ['J', 'ó', 'n', 'a'], none⟩]⟩, ⟨['o', 'g'], ['a', 'n', 'd'], [⟨['o', 'g'], ['a', 'n', 'd'], none⟩]⟩, ⟨['S', 'i', 'g', 'g', 'i'], ['S', 'i', 'g', 'g', 'i'], [⟨['S', 'i', 'g', 'g', 'i'], ['S', 'i', 'g', 'g', 'i'], none⟩]⟩, ⟨['k', 'y', 's', 's', 't', 'u', 's', 't'], ['k', 'i', 's', 's', 'e', 'd', '-', 'S', 'T'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("use", "reciprocal"), ("type", "2")] }

def ex_22 : Datum :=
  { id := "wood2015_22"
    source := ⟨"wood-2015", "Ch. 6 (55b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Jóna kysstist við Sigga."
    glossedTokens := [("Jóna", "Jóna"), ("kysstist", "kissed-ST"), ("við", "with"), ("Sigga", "Siggi")]
    glossedWords := [⟨['J', 'ó', 'n', 'a'], ['J', 'ó', 'n', 'a'], [⟨['J', 'ó', 'n', 'a'], ['J', 'ó', 'n', 'a'], none⟩]⟩, ⟨['k', 'y', 's', 's', 't', 'i', 's', 't'], ['k', 'i', 's', 's', 'e', 'd', '-', 'S', 'T'], []⟩, ⟨['v', 'i', 'ð'], ['w', 'i', 't', 'h'], [⟨['v', 'i', 'ð'], ['w', 'i', 't', 'h'], none⟩]⟩, ⟨['S', 'i', 'g', 'g', 'a'], ['S', 'i', 'g', 'g', 'i'], [⟨['S', 'i', 'g', 'g', 'a'], ['S', 'i', 'g', 'g', 'i'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("use", "reciprocal"), ("type", "2")] }

def ex_23 : Datum :=
  { id := "wood2015_23"
    source := ⟨"wood-2015", "Ch. 6 (76b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Keisarinn klæddist nýjum fötum."
    glossedTokens := [("Keisarinn", "emperor.the.NOM"), ("klæddist", "dressed-ST"), ("nýjum", "new"), ("fötum", "clothes.DAT")]
    glossedWords := [⟨['K', 'e', 'i', 's', 'a', 'r', 'i', 'n', 'n'], ['e', 'm', 'p', 'e', 'r', 'o', 'r', '.', 't', 'h', 'e', '.', 'N', 'O', 'M'], [⟨['K', 'e', 'i', 's', 'a', 'r', 'i', 'n', 'n'], ['e', 'm', 'p', 'e', 'r', 'o', 'r', '.', 't', 'h', 'e', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['k', 'l', 'æ', 'd', 'd', 'i', 's', 't'], ['d', 'r', 'e', 's', 's', 'e', 'd', '-', 'S', 'T'], []⟩, ⟨['n', 'ý', 'j', 'u', 'm'], ['n', 'e', 'w'], [⟨['n', 'ý', 'j', 'u', 'm'], ['n', 'e', 'w'], none⟩]⟩, ⟨['f', 'ö', 't', 'u', 'm'], ['c', 'l', 'o', 't', 'h', 'e', 's', '.', 'D', 'A', 'T'], [⟨['f', 'ö', 't', 'u', 'm'], ['c', 'l', 'o', 't', 'h', 'e', 's', '.', 'D', 'A', 'T'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("use", "reflexive")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, ex_10, ex_11, ex_12, ex_13, ex_14, ex_15, ex_16, ex_17, ex_18, ex_19, ex_20, ex_21, ex_22, ex_23]

end Wood2015.Examples
