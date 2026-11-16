module

public import Linglib.Data.Examples.Schema

/-!
# `Dixon1994` — typed example data

Auto-generated from `Linglib/Data/Examples/Dixon1994.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Dixon1994.Examples`.
-/

@[expose] public section

namespace Dixon1994.Examples

def ex_1_2_5 : Datum :=
  { id := "dixon1994_1_2_5"
    source := ⟨"dixon-1994", "§1.2 (5)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma banaga-nʸu"
    glossedTokens := [("ŋuma", "father.ABS"), ("banaga-nʸu", "return-NONFUT")]
    glossedWords := [⟨['ŋ', 'u', 'm', 'a'], ['f', 'a', 't', 'h', 'e', 'r', '.', 'A', 'B', 'S'], [⟨['ŋ', 'u', 'm', 'a'], ['f', 'a', 't', 'h', 'e', 'r', '.', 'A', 'B', 'S'], none⟩]⟩, ⟨['b', 'a', 'n', 'a', 'g', 'a', '-', 'n', 'ʸ', 'u'], ['r', 'e', 't', 'u', 'r', 'n', '-', 'N', 'O', 'N', 'F', 'U', 'T'], [⟨['b', 'a', 'n', 'a', 'g', 'a'], ['r', 'e', 't', 'u', 'r', 'n'], none⟩, ⟨['n', 'ʸ', 'u'], ['N', 'O', 'N', 'F', 'U', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "simple"), ("function", "S")] }

def ex_1_2_7 : Datum :=
  { id := "dixon1994_1_2_7"
    source := ⟨"dixon-1994", "§1.2 (7)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma yabu-ŋgu bura-n"
    glossedTokens := [("ŋuma", "father.ABS"), ("yabu-ŋgu", "mother-ERG"), ("bura-n", "see-NONFUT")]
    glossedWords := [⟨['ŋ', 'u', 'm', 'a'], ['f', 'a', 't', 'h', 'e', 'r', '.', 'A', 'B', 'S'], [⟨['ŋ', 'u', 'm', 'a'], ['f', 'a', 't', 'h', 'e', 'r', '.', 'A', 'B', 'S'], none⟩]⟩, ⟨['y', 'a', 'b', 'u', '-', 'ŋ', 'g', 'u'], ['m', 'o', 't', 'h', 'e', 'r', '-', 'E', 'R', 'G'], [⟨['y', 'a', 'b', 'u'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['ŋ', 'g', 'u'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['b', 'u', 'r', 'a', '-', 'n'], ['s', 'e', 'e', '-', 'N', 'O', 'N', 'F', 'U', 'T'], [⟨['b', 'u', 'r', 'a'], ['s', 'e', 'e'], none⟩, ⟨['n'], ['N', 'O', 'N', 'F', 'U', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "simple"), ("function", "AO")] }

def ex_1_2_12 : Datum :=
  { id := "dixon1994_1_2_12"
    source := ⟨"dixon-1994", "§1.2 (12)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma bural-ŋa-nʸu yabu-gu"
    glossedTokens := [("ŋuma", "father.ABS"), ("bural-ŋa-nʸu", "see-ANTIPASS-NONFUT"), ("yabu-gu", "mother-DAT")]
    glossedWords := [⟨['ŋ', 'u', 'm', 'a'], ['f', 'a', 't', 'h', 'e', 'r', '.', 'A', 'B', 'S'], [⟨['ŋ', 'u', 'm', 'a'], ['f', 'a', 't', 'h', 'e', 'r', '.', 'A', 'B', 'S'], none⟩]⟩, ⟨['b', 'u', 'r', 'a', 'l', '-', 'ŋ', 'a', '-', 'n', 'ʸ', 'u'], ['s', 'e', 'e', '-', 'A', 'N', 'T', 'I', 'P', 'A', 'S', 'S', '-', 'N', 'O', 'N', 'F', 'U', 'T'], [⟨['b', 'u', 'r', 'a', 'l'], ['s', 'e', 'e'], none⟩, ⟨['ŋ', 'a'], ['A', 'N', 'T', 'I', 'P', 'A', 'S', 'S'], some '-'⟩, ⟨['n', 'ʸ', 'u'], ['N', 'O', 'N', 'F', 'U', 'T'], some '-'⟩]⟩, ⟨['y', 'a', 'b', 'u', '-', 'g', 'u'], ['m', 'o', 't', 'h', 'e', 'r', '-', 'D', 'A', 'T'], [⟨['y', 'a', 'b', 'u'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['g', 'u'], ['D', 'A', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "antipassive"), ("function", "S")] }

def ex_15 : Datum :=
  { id := "dixon1994_15"
    source := ⟨"dixon-1994", "§6.2.2 (15)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "nʸurra ŋana-na bura-n"
    glossedTokens := [("nʸurra", "you.all.NOM"), ("ŋana-na", "we.all-ACC"), ("bura-n", "see-NONFUT")]
    glossedWords := [⟨['n', 'ʸ', 'u', 'r', 'r', 'a'], ['y', 'o', 'u', '.', 'a', 'l', 'l', '.', 'N', 'O', 'M'], [⟨['n', 'ʸ', 'u', 'r', 'r', 'a'], ['y', 'o', 'u', '.', 'a', 'l', 'l', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['ŋ', 'a', 'n', 'a', '-', 'n', 'a'], ['w', 'e', '.', 'a', 'l', 'l', '-', 'A', 'C', 'C'], [⟨['ŋ', 'a', 'n', 'a'], ['w', 'e', '.', 'a', 'l', 'l'], none⟩, ⟨['n', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['b', 'u', 'r', 'a', '-', 'n'], ['s', 'e', 'e', '-', 'N', 'O', 'N', 'F', 'U', 'T'], [⟨['b', 'u', 'r', 'a'], ['s', 'e', 'e'], none⟩, ⟨['n'], ['N', 'O', 'N', 'F', 'U', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "simple"), ("function", "AO")] }

def ex_17 : Datum :=
  { id := "dixon1994_17"
    source := ⟨"dixon-1994", "§6.2.2 (17)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma banaga-nʸu miyanda-nʸu"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "S"), ("second", "S"), ("derivation", "none")] }

def ex_19 : Datum :=
  { id := "dixon1994_19"
    source := ⟨"dixon-1994", "§6.2.2 (19)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma banaga-nʸu yabu-ŋgu bura-n"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "S"), ("second", "O"), ("derivation", "none")] }

def ex_20 : Datum :=
  { id := "dixon1994_20"
    source := ⟨"dixon-1994", "§6.2.2 (20)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋana banaga-nʸu nʸurra bura-n"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "S"), ("second", "O"), ("derivation", "none")] }

def ex_21 : Datum :=
  { id := "dixon1994_21"
    source := ⟨"dixon-1994", "§6.2.2 (21)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma yabu-ŋgu bura-n banaga-nʸu"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "O"), ("second", "S"), ("derivation", "none")] }

def ex_24 : Datum :=
  { id := "dixon1994_24"
    source := ⟨"dixon-1994", "§6.2.2 (24)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma yabu-ŋgu bura-n jaja-ŋgu ŋamba-n"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "O"), ("second", "O"), ("derivation", "none")] }

def ex_28 : Datum :=
  { id := "dixon1994_28"
    source := ⟨"dixon-1994", "§6.2.2 (28)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma yabu-ŋgu bura-n (yabu-ŋgu) ŋamba-n"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "O"), ("second", "O"), ("derivation", "none")] }

def ex_32 : Datum :=
  { id := "dixon1994_32"
    source := ⟨"dixon-1994", "§6.2.2 (32)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma bural-ŋa-nʸu yabu-gu"
    glossedTokens := [("ŋuma", "father.ABS"), ("bural-ŋa-nʸu", "see-ANTIPASS-NONFUT"), ("yabu-gu", "mother-DAT")]
    glossedWords := [⟨['ŋ', 'u', 'm', 'a'], ['f', 'a', 't', 'h', 'e', 'r', '.', 'A', 'B', 'S'], [⟨['ŋ', 'u', 'm', 'a'], ['f', 'a', 't', 'h', 'e', 'r', '.', 'A', 'B', 'S'], none⟩]⟩, ⟨['b', 'u', 'r', 'a', 'l', '-', 'ŋ', 'a', '-', 'n', 'ʸ', 'u'], ['s', 'e', 'e', '-', 'A', 'N', 'T', 'I', 'P', 'A', 'S', 'S', '-', 'N', 'O', 'N', 'F', 'U', 'T'], [⟨['b', 'u', 'r', 'a', 'l'], ['s', 'e', 'e'], none⟩, ⟨['ŋ', 'a'], ['A', 'N', 'T', 'I', 'P', 'A', 'S', 'S'], some '-'⟩, ⟨['n', 'ʸ', 'u'], ['N', 'O', 'N', 'F', 'U', 'T'], some '-'⟩]⟩, ⟨['y', 'a', 'b', 'u', '-', 'g', 'u'], ['m', 'o', 't', 'h', 'e', 'r', '-', 'D', 'A', 'T'], [⟨['y', 'a', 'b', 'u'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['g', 'u'], ['D', 'A', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "antipassive"), ("function", "S")] }

def ex_33 : Datum :=
  { id := "dixon1994_33"
    source := ⟨"dixon-1994", "§6.2.2 (33)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋana bural-ŋa-nʸu nʸurra-ngu"
    glossedTokens := [("ŋana", "we.all.NOM"), ("bural-ŋa-nʸu", "see-ANTIPASS-NONFUT"), ("nʸurra-ngu", "you.all-DAT")]
    glossedWords := [⟨['ŋ', 'a', 'n', 'a'], ['w', 'e', '.', 'a', 'l', 'l', '.', 'N', 'O', 'M'], [⟨['ŋ', 'a', 'n', 'a'], ['w', 'e', '.', 'a', 'l', 'l', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['b', 'u', 'r', 'a', 'l', '-', 'ŋ', 'a', '-', 'n', 'ʸ', 'u'], ['s', 'e', 'e', '-', 'A', 'N', 'T', 'I', 'P', 'A', 'S', 'S', '-', 'N', 'O', 'N', 'F', 'U', 'T'], [⟨['b', 'u', 'r', 'a', 'l'], ['s', 'e', 'e'], none⟩, ⟨['ŋ', 'a'], ['A', 'N', 'T', 'I', 'P', 'A', 'S', 'S'], some '-'⟩, ⟨['n', 'ʸ', 'u'], ['N', 'O', 'N', 'F', 'U', 'T'], some '-'⟩]⟩, ⟨['n', 'ʸ', 'u', 'r', 'r', 'a', '-', 'n', 'g', 'u'], ['y', 'o', 'u', '.', 'a', 'l', 'l', '-', 'D', 'A', 'T'], [⟨['n', 'ʸ', 'u', 'r', 'r', 'a'], ['y', 'o', 'u', '.', 'a', 'l', 'l'], none⟩, ⟨['n', 'g', 'u'], ['D', 'A', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "antipassive"), ("function", "S")] }

def ex_34 : Datum :=
  { id := "dixon1994_34"
    source := ⟨"dixon-1994", "§6.2.2 (34)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma banaga-nʸu bural-ŋa-nʸu yabu-gu"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "S"), ("second", "A"), ("derivation", "antipassive")] }

def ex_36 : Datum :=
  { id := "dixon1994_36"
    source := ⟨"dixon-1994", "§6.2.2 (36)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma jaja-ŋgu ŋamba-n bural-ŋa-nʸu yabu-gu"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "O"), ("second", "A"), ("derivation", "antipassive")] }

def ex_39 : Datum :=
  { id := "dixon1994_39"
    source := ⟨"dixon-1994", "§6.2.2 (39)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma yabu-ŋgu ŋamba-n bural-ŋa-nʸu yabu-gu"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "O"), ("second", "A"), ("derivation", "antipassive")] }

def ex_42 : Datum :=
  { id := "dixon1994_42"
    source := ⟨"dixon-1994", "§6.2.2 (42)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma bural-ŋa-nʸu yabu-gu banaga-nʸu"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "A"), ("second", "S"), ("derivation", "antipassive")] }

def ex_44 : Datum :=
  { id := "dixon1994_44"
    source := ⟨"dixon-1994", "§6.2.2 (44)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma bural-ŋa-nʸu yabu-gu jaja-ŋgu ŋamba-n"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "A"), ("second", "O"), ("derivation", "antipassive")] }

def ex_46 : Datum :=
  { id := "dixon1994_46"
    source := ⟨"dixon-1994", "§6.2.2 (46)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "yabu ŋuma-ŋgu bura-n (ŋuma) banaga-ŋurra"
    glossedTokens := [("yabu", "mother.ABS"), ("ŋuma-ŋgu", "father-ERG"), ("bura-n", "see-NONFUT"), ("(ŋuma)", "father.ABS"), ("banaga-ŋurra", "return-ŊURRA")]
    glossedWords := [⟨['y', 'a', 'b', 'u'], ['m', 'o', 't', 'h', 'e', 'r', '.', 'A', 'B', 'S'], [⟨['y', 'a', 'b', 'u'], ['m', 'o', 't', 'h', 'e', 'r', '.', 'A', 'B', 'S'], none⟩]⟩, ⟨['ŋ', 'u', 'm', 'a', '-', 'ŋ', 'g', 'u'], ['f', 'a', 't', 'h', 'e', 'r', '-', 'E', 'R', 'G'], [⟨['ŋ', 'u', 'm', 'a'], ['f', 'a', 't', 'h', 'e', 'r'], none⟩, ⟨['ŋ', 'g', 'u'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['b', 'u', 'r', 'a', '-', 'n'], ['s', 'e', 'e', '-', 'N', 'O', 'N', 'F', 'U', 'T'], [⟨['b', 'u', 'r', 'a'], ['s', 'e', 'e'], none⟩, ⟨['n'], ['N', 'O', 'N', 'F', 'U', 'T'], some '-'⟩]⟩, ⟨['(', 'ŋ', 'u', 'm', 'a', ')'], ['f', 'a', 't', 'h', 'e', 'r', '.', 'A', 'B', 'S'], [⟨['ŋ', 'u', 'm', 'a'], ['f', 'a', 't', 'h', 'e', 'r', '.', 'A', 'B', 'S'], none⟩]⟩, ⟨['b', 'a', 'n', 'a', 'g', 'a', '-', 'ŋ', 'u', 'r', 'r', 'a'], ['r', 'e', 't', 'u', 'r', 'n', '-', 'Ŋ', 'U', 'R', 'R', 'A'], [⟨['b', 'a', 'n', 'a', 'g', 'a'], ['r', 'e', 't', 'u', 'r', 'n'], none⟩, ⟨['ŋ', 'u', 'r', 'r', 'a'], ['Ŋ', 'U', 'R', 'R', 'A'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "A"), ("second", "S"), ("derivation", "ngurra")] }

def ex_52 : Datum :=
  { id := "dixon1994_52"
    source := ⟨"dixon-1994", "§6.2.2 (52)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma bural-ŋa-nʸu yabu-gu ŋambal-ŋa-nʸu jaja-gu"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "A"), ("second", "A"), ("derivation", "antipassive")] }

def ex_56 : Datum :=
  { id := "dixon1994_56"
    source := ⟨"dixon-1994", "§6.2.2 (56)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma banaga-nʸu yabu-ŋgu bura-li"
    glossedTokens := [("ŋuma", "father.ABS"), ("banaga-nʸu", "return-NONFUT"), ("yabu-ŋgu", "mother-ERG"), ("bura-li", "see-PURP")]
    glossedWords := [⟨['ŋ', 'u', 'm', 'a'], ['f', 'a', 't', 'h', 'e', 'r', '.', 'A', 'B', 'S'], [⟨['ŋ', 'u', 'm', 'a'], ['f', 'a', 't', 'h', 'e', 'r', '.', 'A', 'B', 'S'], none⟩]⟩, ⟨['b', 'a', 'n', 'a', 'g', 'a', '-', 'n', 'ʸ', 'u'], ['r', 'e', 't', 'u', 'r', 'n', '-', 'N', 'O', 'N', 'F', 'U', 'T'], [⟨['b', 'a', 'n', 'a', 'g', 'a'], ['r', 'e', 't', 'u', 'r', 'n'], none⟩, ⟨['n', 'ʸ', 'u'], ['N', 'O', 'N', 'F', 'U', 'T'], some '-'⟩]⟩, ⟨['y', 'a', 'b', 'u', '-', 'ŋ', 'g', 'u'], ['m', 'o', 't', 'h', 'e', 'r', '-', 'E', 'R', 'G'], [⟨['y', 'a', 'b', 'u'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['ŋ', 'g', 'u'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['b', 'u', 'r', 'a', '-', 'l', 'i'], ['s', 'e', 'e', '-', 'P', 'U', 'R', 'P'], [⟨['b', 'u', 'r', 'a'], ['s', 'e', 'e'], none⟩, ⟨['l', 'i'], ['P', 'U', 'R', 'P'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "purposive"), ("first", "S"), ("second", "O"), ("derivation", "none")] }

def ex_57 : Datum :=
  { id := "dixon1994_57"
    source := ⟨"dixon-1994", "§6.2.2 (57)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma banaga-nʸu bural-ŋa-ygu yabu-gu"
    glossedTokens := [("ŋuma", "father.ABS"), ("banaga-nʸu", "return-NONFUT"), ("bural-ŋa-ygu", "see-ANTIPASS-PURP"), ("yabu-gu", "mother-DAT")]
    glossedWords := [⟨['ŋ', 'u', 'm', 'a'], ['f', 'a', 't', 'h', 'e', 'r', '.', 'A', 'B', 'S'], [⟨['ŋ', 'u', 'm', 'a'], ['f', 'a', 't', 'h', 'e', 'r', '.', 'A', 'B', 'S'], none⟩]⟩, ⟨['b', 'a', 'n', 'a', 'g', 'a', '-', 'n', 'ʸ', 'u'], ['r', 'e', 't', 'u', 'r', 'n', '-', 'N', 'O', 'N', 'F', 'U', 'T'], [⟨['b', 'a', 'n', 'a', 'g', 'a'], ['r', 'e', 't', 'u', 'r', 'n'], none⟩, ⟨['n', 'ʸ', 'u'], ['N', 'O', 'N', 'F', 'U', 'T'], some '-'⟩]⟩, ⟨['b', 'u', 'r', 'a', 'l', '-', 'ŋ', 'a', '-', 'y', 'g', 'u'], ['s', 'e', 'e', '-', 'A', 'N', 'T', 'I', 'P', 'A', 'S', 'S', '-', 'P', 'U', 'R', 'P'], [⟨['b', 'u', 'r', 'a', 'l'], ['s', 'e', 'e'], none⟩, ⟨['ŋ', 'a'], ['A', 'N', 'T', 'I', 'P', 'A', 'S', 'S'], some '-'⟩, ⟨['y', 'g', 'u'], ['P', 'U', 'R', 'P'], some '-'⟩]⟩, ⟨['y', 'a', 'b', 'u', '-', 'g', 'u'], ['m', 'o', 't', 'h', 'e', 'r', '-', 'D', 'A', 'T'], [⟨['y', 'a', 'b', 'u'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['g', 'u'], ['D', 'A', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "purposive"), ("first", "S"), ("second", "A"), ("derivation", "antipassive")] }

def ex_59 : Datum :=
  { id := "dixon1994_59"
    source := ⟨"dixon-1994", "§6.2.2 (59)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "yabu ŋuma-ŋgu giga-n gubi-ŋgu mawa-li"
    glossedTokens := [("yabu", "mother.ABS"), ("ŋuma-ŋgu", "father-ERG"), ("giga-n", "tell.to.do-NONFUT"), ("gubi-ŋgu", "doctor-ERG"), ("mawa-li", "examine-PURP")]
    glossedWords := [⟨['y', 'a', 'b', 'u'], ['m', 'o', 't', 'h', 'e', 'r', '.', 'A', 'B', 'S'], [⟨['y', 'a', 'b', 'u'], ['m', 'o', 't', 'h', 'e', 'r', '.', 'A', 'B', 'S'], none⟩]⟩, ⟨['ŋ', 'u', 'm', 'a', '-', 'ŋ', 'g', 'u'], ['f', 'a', 't', 'h', 'e', 'r', '-', 'E', 'R', 'G'], [⟨['ŋ', 'u', 'm', 'a'], ['f', 'a', 't', 'h', 'e', 'r'], none⟩, ⟨['ŋ', 'g', 'u'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['g', 'i', 'g', 'a', '-', 'n'], ['t', 'e', 'l', 'l', '.', 't', 'o', '.', 'd', 'o', '-', 'N', 'O', 'N', 'F', 'U', 'T'], [⟨['g', 'i', 'g', 'a'], ['t', 'e', 'l', 'l', '.', 't', 'o', '.', 'd', 'o'], none⟩, ⟨['n'], ['N', 'O', 'N', 'F', 'U', 'T'], some '-'⟩]⟩, ⟨['g', 'u', 'b', 'i', '-', 'ŋ', 'g', 'u'], ['d', 'o', 'c', 't', 'o', 'r', '-', 'E', 'R', 'G'], [⟨['g', 'u', 'b', 'i'], ['d', 'o', 'c', 't', 'o', 'r'], none⟩, ⟨['ŋ', 'g', 'u'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['m', 'a', 'w', 'a', '-', 'l', 'i'], ['e', 'x', 'a', 'm', 'i', 'n', 'e', '-', 'P', 'U', 'R', 'P'], [⟨['m', 'a', 'w', 'a'], ['e', 'x', 'a', 'm', 'i', 'n', 'e'], none⟩, ⟨['l', 'i'], ['P', 'U', 'R', 'P'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "purposive"), ("first", "O"), ("second", "O"), ("derivation", "none")] }

def ex_60 : Datum :=
  { id := "dixon1994_60"
    source := ⟨"dixon-1994", "§6.2.2 (60)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "yabu ŋuma-ŋgu giga-n bural-ŋa-ygu jaja-gu"
    glossedTokens := [("yabu", "mother.ABS"), ("ŋuma-ŋgu", "father-ERG"), ("giga-n", "tell.to.do-NONFUT"), ("bural-ŋa-ygu", "see-ANTIPASS-PURP"), ("jaja-gu", "child-DAT")]
    glossedWords := [⟨['y', 'a', 'b', 'u'], ['m', 'o', 't', 'h', 'e', 'r', '.', 'A', 'B', 'S'], [⟨['y', 'a', 'b', 'u'], ['m', 'o', 't', 'h', 'e', 'r', '.', 'A', 'B', 'S'], none⟩]⟩, ⟨['ŋ', 'u', 'm', 'a', '-', 'ŋ', 'g', 'u'], ['f', 'a', 't', 'h', 'e', 'r', '-', 'E', 'R', 'G'], [⟨['ŋ', 'u', 'm', 'a'], ['f', 'a', 't', 'h', 'e', 'r'], none⟩, ⟨['ŋ', 'g', 'u'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['g', 'i', 'g', 'a', '-', 'n'], ['t', 'e', 'l', 'l', '.', 't', 'o', '.', 'd', 'o', '-', 'N', 'O', 'N', 'F', 'U', 'T'], [⟨['g', 'i', 'g', 'a'], ['t', 'e', 'l', 'l', '.', 't', 'o', '.', 'd', 'o'], none⟩, ⟨['n'], ['N', 'O', 'N', 'F', 'U', 'T'], some '-'⟩]⟩, ⟨['b', 'u', 'r', 'a', 'l', '-', 'ŋ', 'a', '-', 'y', 'g', 'u'], ['s', 'e', 'e', '-', 'A', 'N', 'T', 'I', 'P', 'A', 'S', 'S', '-', 'P', 'U', 'R', 'P'], [⟨['b', 'u', 'r', 'a', 'l'], ['s', 'e', 'e'], none⟩, ⟨['ŋ', 'a'], ['A', 'N', 'T', 'I', 'P', 'A', 'S', 'S'], some '-'⟩, ⟨['y', 'g', 'u'], ['P', 'U', 'R', 'P'], some '-'⟩]⟩, ⟨['j', 'a', 'j', 'a', '-', 'g', 'u'], ['c', 'h', 'i', 'l', 'd', '-', 'D', 'A', 'T'], [⟨['j', 'a', 'j', 'a'], ['c', 'h', 'i', 'l', 'd'], none⟩, ⟨['g', 'u'], ['D', 'A', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "purposive"), ("first", "O"), ("second", "A"), ("derivation", "antipassive")] }

def ex_61 : Datum :=
  { id := "dixon1994_61"
    source := ⟨"dixon-1994", "§6.2.2 (61)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma banaga-ŋu yabu-ŋgu bura-n"
    glossedTokens := [("ŋuma", "father.ABS"), ("banaga-ŋu", "return-REL.ABS"), ("yabu-ŋgu", "mother-ERG"), ("bura-n", "see-NONFUT")]
    glossedWords := [⟨['ŋ', 'u', 'm', 'a'], ['f', 'a', 't', 'h', 'e', 'r', '.', 'A', 'B', 'S'], [⟨['ŋ', 'u', 'm', 'a'], ['f', 'a', 't', 'h', 'e', 'r', '.', 'A', 'B', 'S'], none⟩]⟩, ⟨['b', 'a', 'n', 'a', 'g', 'a', '-', 'ŋ', 'u'], ['r', 'e', 't', 'u', 'r', 'n', '-', 'R', 'E', 'L', '.', 'A', 'B', 'S'], [⟨['b', 'a', 'n', 'a', 'g', 'a'], ['r', 'e', 't', 'u', 'r', 'n'], none⟩, ⟨['ŋ', 'u'], ['R', 'E', 'L', '.', 'A', 'B', 'S'], some '-'⟩]⟩, ⟨['y', 'a', 'b', 'u', '-', 'ŋ', 'g', 'u'], ['m', 'o', 't', 'h', 'e', 'r', '-', 'E', 'R', 'G'], [⟨['y', 'a', 'b', 'u'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['ŋ', 'g', 'u'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['b', 'u', 'r', 'a', '-', 'n'], ['s', 'e', 'e', '-', 'N', 'O', 'N', 'F', 'U', 'T'], [⟨['b', 'u', 'r', 'a'], ['s', 'e', 'e'], none⟩, ⟨['n'], ['N', 'O', 'N', 'F', 'U', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "relative"), ("first", "O"), ("second", "S"), ("derivation", "none")] }

def ex_62 : Datum :=
  { id := "dixon1994_62"
    source := ⟨"dixon-1994", "§6.2.2 (62)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma yabu-ŋgu banaga-ŋu-rru bura-n"
    glossedTokens := [("ŋuma", "father.ABS"), ("yabu-ŋgu", "mother-ERG"), ("banaga-ŋu-rru", "return-REL-ERG"), ("bura-n", "see-NONFUT")]
    glossedWords := [⟨['ŋ', 'u', 'm', 'a'], ['f', 'a', 't', 'h', 'e', 'r', '.', 'A', 'B', 'S'], [⟨['ŋ', 'u', 'm', 'a'], ['f', 'a', 't', 'h', 'e', 'r', '.', 'A', 'B', 'S'], none⟩]⟩, ⟨['y', 'a', 'b', 'u', '-', 'ŋ', 'g', 'u'], ['m', 'o', 't', 'h', 'e', 'r', '-', 'E', 'R', 'G'], [⟨['y', 'a', 'b', 'u'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['ŋ', 'g', 'u'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['b', 'a', 'n', 'a', 'g', 'a', '-', 'ŋ', 'u', '-', 'r', 'r', 'u'], ['r', 'e', 't', 'u', 'r', 'n', '-', 'R', 'E', 'L', '-', 'E', 'R', 'G'], [⟨['b', 'a', 'n', 'a', 'g', 'a'], ['r', 'e', 't', 'u', 'r', 'n'], none⟩, ⟨['ŋ', 'u'], ['R', 'E', 'L'], some '-'⟩, ⟨['r', 'r', 'u'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['b', 'u', 'r', 'a', '-', 'n'], ['s', 'e', 'e', '-', 'N', 'O', 'N', 'F', 'U', 'T'], [⟨['b', 'u', 'r', 'a'], ['s', 'e', 'e'], none⟩, ⟨['n'], ['N', 'O', 'N', 'F', 'U', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "relative"), ("first", "A"), ("second", "S"), ("derivation", "none")] }

def ex_63 : Datum :=
  { id := "dixon1994_63"
    source := ⟨"dixon-1994", "§6.2.2 (63)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "yabu bural-ŋa-ŋu ŋuma-gu banaga-nʸu"
    glossedTokens := [("yabu", "mother.ABS"), ("bural-ŋa-ŋu", "see-ANTIPASS-REL.ABS"), ("ŋuma-gu", "father-DAT"), ("banaga-nʸu", "return-NONFUT")]
    glossedWords := [⟨['y', 'a', 'b', 'u'], ['m', 'o', 't', 'h', 'e', 'r', '.', 'A', 'B', 'S'], [⟨['y', 'a', 'b', 'u'], ['m', 'o', 't', 'h', 'e', 'r', '.', 'A', 'B', 'S'], none⟩]⟩, ⟨['b', 'u', 'r', 'a', 'l', '-', 'ŋ', 'a', '-', 'ŋ', 'u'], ['s', 'e', 'e', '-', 'A', 'N', 'T', 'I', 'P', 'A', 'S', 'S', '-', 'R', 'E', 'L', '.', 'A', 'B', 'S'], [⟨['b', 'u', 'r', 'a', 'l'], ['s', 'e', 'e'], none⟩, ⟨['ŋ', 'a'], ['A', 'N', 'T', 'I', 'P', 'A', 'S', 'S'], some '-'⟩, ⟨['ŋ', 'u'], ['R', 'E', 'L', '.', 'A', 'B', 'S'], some '-'⟩]⟩, ⟨['ŋ', 'u', 'm', 'a', '-', 'g', 'u'], ['f', 'a', 't', 'h', 'e', 'r', '-', 'D', 'A', 'T'], [⟨['ŋ', 'u', 'm', 'a'], ['f', 'a', 't', 'h', 'e', 'r'], none⟩, ⟨['g', 'u'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['b', 'a', 'n', 'a', 'g', 'a', '-', 'n', 'ʸ', 'u'], ['r', 'e', 't', 'u', 'r', 'n', '-', 'N', 'O', 'N', 'F', 'U', 'T'], [⟨['b', 'a', 'n', 'a', 'g', 'a'], ['r', 'e', 't', 'u', 'r', 'n'], none⟩, ⟨['n', 'ʸ', 'u'], ['N', 'O', 'N', 'F', 'U', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "relative"), ("first", "S"), ("second", "A"), ("derivation", "antipassive")] }

def ex_66 : Datum :=
  { id := "dixon1994_66"
    source := ⟨"dixon-1994", "§6.2.2 (66)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "yugu ŋuma-ŋgu balgal-ma-n yabu-gu"
    glossedTokens := [("yugu", "stick"), ("ŋuma-ŋgu", "father-ERG"), ("balgal-ma-n", "hit-INSTV-NONFUT"), ("yabu-gu", "mother-DAT")]
    glossedWords := [⟨['y', 'u', 'g', 'u'], ['s', 't', 'i', 'c', 'k'], [⟨['y', 'u', 'g', 'u'], ['s', 't', 'i', 'c', 'k'], none⟩]⟩, ⟨['ŋ', 'u', 'm', 'a', '-', 'ŋ', 'g', 'u'], ['f', 'a', 't', 'h', 'e', 'r', '-', 'E', 'R', 'G'], [⟨['ŋ', 'u', 'm', 'a'], ['f', 'a', 't', 'h', 'e', 'r'], none⟩, ⟨['ŋ', 'g', 'u'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['b', 'a', 'l', 'g', 'a', 'l', '-', 'm', 'a', '-', 'n'], ['h', 'i', 't', '-', 'I', 'N', 'S', 'T', 'V', '-', 'N', 'O', 'N', 'F', 'U', 'T'], [⟨['b', 'a', 'l', 'g', 'a', 'l'], ['h', 'i', 't'], none⟩, ⟨['m', 'a'], ['I', 'N', 'S', 'T', 'V'], some '-'⟩, ⟨['n'], ['N', 'O', 'N', 'F', 'U', 'T'], some '-'⟩]⟩, ⟨['y', 'a', 'b', 'u', '-', 'g', 'u'], ['m', 'o', 't', 'h', 'e', 'r', '-', 'D', 'A', 'T'], [⟨['y', 'a', 'b', 'u'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['g', 'u'], ['D', 'A', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "instrumentive"), ("function", "O")] }

def ex_68 : Datum :=
  { id := "dixon1994_68"
    source := ⟨"dixon-1994", "§6.2.2 (68)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "yugu ŋuma-ŋgu balgal-ma-ŋu yabu-gu jaja-ŋgu bura-n"
    glossedTokens := [("yugu", "stick.ABS"), ("ŋuma-ŋgu", "father-ERG"), ("balgal-ma-ŋu", "hit-INSTV-REL.ABS"), ("yabu-gu", "mother-DAT"), ("jaja-ŋgu", "child-ERG"), ("bura-n", "see-NONFUT")]
    glossedWords := [⟨['y', 'u', 'g', 'u'], ['s', 't', 'i', 'c', 'k', '.', 'A', 'B', 'S'], [⟨['y', 'u', 'g', 'u'], ['s', 't', 'i', 'c', 'k', '.', 'A', 'B', 'S'], none⟩]⟩, ⟨['ŋ', 'u', 'm', 'a', '-', 'ŋ', 'g', 'u'], ['f', 'a', 't', 'h', 'e', 'r', '-', 'E', 'R', 'G'], [⟨['ŋ', 'u', 'm', 'a'], ['f', 'a', 't', 'h', 'e', 'r'], none⟩, ⟨['ŋ', 'g', 'u'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['b', 'a', 'l', 'g', 'a', 'l', '-', 'm', 'a', '-', 'ŋ', 'u'], ['h', 'i', 't', '-', 'I', 'N', 'S', 'T', 'V', '-', 'R', 'E', 'L', '.', 'A', 'B', 'S'], [⟨['b', 'a', 'l', 'g', 'a', 'l'], ['h', 'i', 't'], none⟩, ⟨['m', 'a'], ['I', 'N', 'S', 'T', 'V'], some '-'⟩, ⟨['ŋ', 'u'], ['R', 'E', 'L', '.', 'A', 'B', 'S'], some '-'⟩]⟩, ⟨['y', 'a', 'b', 'u', '-', 'g', 'u'], ['m', 'o', 't', 'h', 'e', 'r', '-', 'D', 'A', 'T'], [⟨['y', 'a', 'b', 'u'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['g', 'u'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['j', 'a', 'j', 'a', '-', 'ŋ', 'g', 'u'], ['c', 'h', 'i', 'l', 'd', '-', 'E', 'R', 'G'], [⟨['j', 'a', 'j', 'a'], ['c', 'h', 'i', 'l', 'd'], none⟩, ⟨['ŋ', 'g', 'u'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['b', 'u', 'r', 'a', '-', 'n'], ['s', 'e', 'e', '-', 'N', 'O', 'N', 'F', 'U', 'T'], [⟨['b', 'u', 'r', 'a'], ['s', 'e', 'e'], none⟩, ⟨['n'], ['N', 'O', 'N', 'F', 'U', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "relative"), ("first", "O"), ("second", "O"), ("derivation", "instrumentive")] }

def en_a : Datum :=
  { id := "dixon1994_en_a"
    source := ⟨"dixon-1994", "§6.2.1 (a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill entered and sat down."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "S"), ("second", "S"), ("derivation", "none")] }

def en_b : Datum :=
  { id := "dixon1994_en_b"
    source := ⟨"dixon-1994", "§6.2.1 (b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill entered and was seen by Fred."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "S"), ("second", "O"), ("derivation", "passive")] }

def en_c : Datum :=
  { id := "dixon1994_en_c"
    source := ⟨"dixon-1994", "§6.2.1 (c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill entered and saw Fred."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "S"), ("second", "A"), ("derivation", "none")] }

def en_d : Datum :=
  { id := "dixon1994_en_d"
    source := ⟨"dixon-1994", "§6.2.1 (d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill was seen by Fred and laughed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "O"), ("second", "S"), ("derivation", "passive")] }

def en_e : Datum :=
  { id := "dixon1994_en_e"
    source := ⟨"dixon-1994", "§6.2.1 (e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fred saw Bill and laughed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "A"), ("second", "S"), ("derivation", "none")] }

def en_f : Datum :=
  { id := "dixon1994_en_f"
    source := ⟨"dixon-1994", "§6.2.1 (f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill was kicked by Tom and punched by Bob."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Tom kicked and Bob punched Bill.", .acceptable)]
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "O"), ("second", "O"), ("derivation", "passive")] }

def en_g : Datum :=
  { id := "dixon1994_en_g"
    source := ⟨"dixon-1994", "§6.2.1 (g)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bob kicked Jim and punched Bill."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "A"), ("second", "A"), ("derivation", "none")] }

def en_h : Datum :=
  { id := "dixon1994_en_h"
    source := ⟨"dixon-1994", "§6.2.1 (h)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bob was kicked by Tom and punched Bill."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "O"), ("second", "A"), ("derivation", "passive")] }

def en_i : Datum :=
  { id := "dixon1994_en_i"
    source := ⟨"dixon-1994", "§6.2.1 (i)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bob punched Bill and was kicked by Tom."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "A"), ("second", "O"), ("derivation", "passive")] }

def en_j : Datum :=
  { id := "dixon1994_en_j"
    source := ⟨"dixon-1994", "§6.2.1 (j)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fred punched and kicked Bill."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Fred punched Bill and kicked him.", .acceptable)]
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "A"), ("second", "A"), ("derivation", "none")] }

def en_k : Datum :=
  { id := "dixon1994_en_k"
    source := ⟨"dixon-1994", "§6.2.1 (k)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fred punched Bill and was kicked by him."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Fred punched and was kicked by Bill.", .acceptable)]
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "A"), ("second", "O"), ("derivation", "passive")] }

def all : List Datum := [ex_1_2_5, ex_1_2_7, ex_1_2_12, ex_15, ex_17, ex_19, ex_20, ex_21, ex_24, ex_28, ex_32, ex_33, ex_34, ex_36, ex_39, ex_42, ex_44, ex_46, ex_52, ex_56, ex_57, ex_59, ex_60, ex_61, ex_62, ex_63, ex_66, ex_68, en_a, en_b, en_c, en_d, en_e, en_f, en_g, en_h, en_i, en_j, en_k]

end Dixon1994.Examples
