module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Aitha2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Aitha2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Aitha2026.Examples`.
-/

@[expose] public section

namespace Aitha2026.Examples

def house_nom : Datum :=
  { id := "aitha2026_house_nom"
    source := ⟨"aitha-2026", "(1)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "illuø"
    glossedTokens := [("il-lu-ø", "house-n-NOM")]
    glossedWords := [⟨['i', 'l', '-', 'l', 'u', '-', 'ø'], ['h', 'o', 'u', 's', 'e', '-', 'n', '-', 'N', 'O', 'M'], [⟨['i', 'l'], ['h', 'o', 'u', 's', 'e'], none⟩, ⟨['l', 'u'], ['n'], some '-'⟩, ⟨['ø'], ['N', 'O', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "strong"), ("alternation", "lu")] }

def house_acc : Datum :=
  { id := "aitha2026_house_acc"
    source := ⟨"aitha-2026", "(1)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "inṭini"
    glossedTokens := [("in-ṭi-ni", "house-n-ACC")]
    glossedWords := [⟨['i', 'n', '-', 'ṭ', 'i', '-', 'n', 'i'], ['h', 'o', 'u', 's', 'e', '-', 'n', '-', 'A', 'C', 'C'], [⟨['i', 'n'], ['h', 'o', 'u', 's', 'e'], none⟩, ⟨['ṭ', 'i'], ['n'], some '-'⟩, ⟨['n', 'i'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "strong"), ("alternation", "lu"), ("follower", "case"), ("weight", "light")] }

def house_gen : Datum :=
  { id := "aitha2026_house_gen"
    source := ⟨"aitha-2026", "(1)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "inṭiø"
    glossedTokens := [("in-ṭi-ø", "house-n-GEN")]
    glossedWords := [⟨['i', 'n', '-', 'ṭ', 'i', '-', 'ø'], ['h', 'o', 'u', 's', 'e', '-', 'n', '-', 'G', 'E', 'N'], [⟨['i', 'n'], ['h', 'o', 'u', 's', 'e'], none⟩, ⟨['ṭ', 'i'], ['n'], some '-'⟩, ⟨['ø'], ['G', 'E', 'N'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "strong"), ("alternation", "lu")] }

def house_dat : Datum :=
  { id := "aitha2026_house_dat"
    source := ⟨"aitha-2026", "(1)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "inṭiki"
    glossedTokens := [("in-ṭi-ki", "house-n-DAT")]
    glossedWords := [⟨['i', 'n', '-', 'ṭ', 'i', '-', 'k', 'i'], ['h', 'o', 'u', 's', 'e', '-', 'n', '-', 'D', 'A', 'T'], [⟨['i', 'n'], ['h', 'o', 'u', 's', 'e'], none⟩, ⟨['ṭ', 'i'], ['n'], some '-'⟩, ⟨['k', 'i'], ['D', 'A', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "strong"), ("alternation", "lu"), ("follower", "case"), ("weight", "light")] }

def house_p : Datum :=
  { id := "aitha2026_house_p"
    source := ⟨"aitha-2026", "(1)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "inṭilō"
    glossedTokens := [("in-ṭi-lō", "house-n-in")]
    glossedWords := [⟨['i', 'n', '-', 'ṭ', 'i', '-', 'l', 'ō'], ['h', 'o', 'u', 's', 'e', '-', 'n', '-', 'i', 'n'], [⟨['i', 'n'], ['h', 'o', 'u', 's', 'e'], none⟩, ⟨['ṭ', 'i'], ['n'], some '-'⟩, ⟨['l', 'ō'], ['i', 'n'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "strong"), ("alternation", "lu"), ("follower", "postposition"), ("weight", "heavy")] }

def town_nom : Datum :=
  { id := "aitha2026_town_nom"
    source := ⟨"aitha-2026", "(2)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "ūruø"
    glossedTokens := [("ūr-u-ø", "town-n-NOM")]
    glossedWords := [⟨['ū', 'r', '-', 'u', '-', 'ø'], ['t', 'o', 'w', 'n', '-', 'n', '-', 'N', 'O', 'M'], [⟨['ū', 'r'], ['t', 'o', 'w', 'n'], none⟩, ⟨['u'], ['n'], some '-'⟩, ⟨['ø'], ['N', 'O', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "strong"), ("alternation", "u")] }

def town_dat : Datum :=
  { id := "aitha2026_town_dat"
    source := ⟨"aitha-2026", "(2)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "ūriki"
    glossedTokens := [("ūr-i-ki", "town-n-DAT")]
    glossedWords := [⟨['ū', 'r', '-', 'i', '-', 'k', 'i'], ['t', 'o', 'w', 'n', '-', 'n', '-', 'D', 'A', 'T'], [⟨['ū', 'r'], ['t', 'o', 'w', 'n'], none⟩, ⟨['i'], ['n'], some '-'⟩, ⟨['k', 'i'], ['D', 'A', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "strong"), ("alternation", "u"), ("follower", "case"), ("weight", "light")] }

def husband_nom : Datum :=
  { id := "aitha2026_husband_nom"
    source := ⟨"aitha-2026", "(2)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "moguḍuø"
    glossedTokens := [("moguḍ-u-ø", "husband-n-NOM")]
    glossedWords := [⟨['m', 'o', 'g', 'u', 'ḍ', '-', 'u', '-', 'ø'], ['h', 'u', 's', 'b', 'a', 'n', 'd', '-', 'n', '-', 'N', 'O', 'M'], [⟨['m', 'o', 'g', 'u', 'ḍ'], ['h', 'u', 's', 'b', 'a', 'n', 'd'], none⟩, ⟨['u'], ['n'], some '-'⟩, ⟨['ø'], ['N', 'O', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "strong"), ("alternation", "u")] }

def husband_dat : Datum :=
  { id := "aitha2026_husband_dat"
    source := ⟨"aitha-2026", "(2)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "moguḍiki"
    glossedTokens := [("moguḍ-i-ki", "husband-n-DAT")]
    glossedWords := [⟨['m', 'o', 'g', 'u', 'ḍ', '-', 'i', '-', 'k', 'i'], ['h', 'u', 's', 'b', 'a', 'n', 'd', '-', 'n', '-', 'D', 'A', 'T'], [⟨['m', 'o', 'g', 'u', 'ḍ'], ['h', 'u', 's', 'b', 'a', 'n', 'd'], none⟩, ⟨['i'], ['n'], some '-'⟩, ⟨['k', 'i'], ['D', 'A', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "strong"), ("alternation", "u"), ("follower", "case"), ("weight", "light")] }

def bow_nom : Datum :=
  { id := "aitha2026_bow_nom"
    source := ⟨"aitha-2026", "(2)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "villuø"
    glossedTokens := [("vil-lu-ø", "bow-n-NOM")]
    glossedWords := [⟨['v', 'i', 'l', '-', 'l', 'u', '-', 'ø'], ['b', 'o', 'w', '-', 'n', '-', 'N', 'O', 'M'], [⟨['v', 'i', 'l'], ['b', 'o', 'w'], none⟩, ⟨['l', 'u'], ['n'], some '-'⟩, ⟨['ø'], ['N', 'O', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "strong"), ("alternation", "lu")] }

def bow_dat : Datum :=
  { id := "aitha2026_bow_dat"
    source := ⟨"aitha-2026", "(2)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "vinṭiki"
    glossedTokens := [("vin-ṭi-ki", "bow-n-DAT")]
    glossedWords := [⟨['v', 'i', 'n', '-', 'ṭ', 'i', '-', 'k', 'i'], ['b', 'o', 'w', '-', 'n', '-', 'D', 'A', 'T'], [⟨['v', 'i', 'n'], ['b', 'o', 'w'], none⟩, ⟨['ṭ', 'i'], ['n'], some '-'⟩, ⟨['k', 'i'], ['D', 'A', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "strong"), ("alternation", "lu"), ("follower", "case"), ("weight", "light")] }

def eye_nom : Datum :=
  { id := "aitha2026_eye_nom"
    source := ⟨"aitha-2026", "(2)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "kannuø"
    glossedTokens := [("kan-nu-ø", "eye-n-NOM")]
    glossedWords := [⟨['k', 'a', 'n', '-', 'n', 'u', '-', 'ø'], ['e', 'y', 'e', '-', 'n', '-', 'N', 'O', 'M'], [⟨['k', 'a', 'n'], ['e', 'y', 'e'], none⟩, ⟨['n', 'u'], ['n'], some '-'⟩, ⟨['ø'], ['N', 'O', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "strong"), ("alternation", "nu")] }

def eye_dat : Datum :=
  { id := "aitha2026_eye_dat"
    source := ⟨"aitha-2026", "(2)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "kanṭiki"
    glossedTokens := [("kan-ṭi-ki", "eye-n-DAT")]
    glossedWords := [⟨['k', 'a', 'n', '-', 'ṭ', 'i', '-', 'k', 'i'], ['e', 'y', 'e', '-', 'n', '-', 'D', 'A', 'T'], [⟨['k', 'a', 'n'], ['e', 'y', 'e'], none⟩, ⟨['ṭ', 'i'], ['n'], some '-'⟩, ⟨['k', 'i'], ['D', 'A', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "strong"), ("alternation", "nu"), ("follower", "case"), ("weight", "light")] }

def tooth_nom : Datum :=
  { id := "aitha2026_tooth_nom"
    source := ⟨"aitha-2026", "(2)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "pannuø"
    glossedTokens := [("pan-nu-ø", "tooth-n-NOM")]
    glossedWords := [⟨['p', 'a', 'n', '-', 'n', 'u', '-', 'ø'], ['t', 'o', 'o', 't', 'h', '-', 'n', '-', 'N', 'O', 'M'], [⟨['p', 'a', 'n'], ['t', 'o', 'o', 't', 'h'], none⟩, ⟨['n', 'u'], ['n'], some '-'⟩, ⟨['ø'], ['N', 'O', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "strong"), ("alternation", "nu")] }

def tooth_dat : Datum :=
  { id := "aitha2026_tooth_dat"
    source := ⟨"aitha-2026", "(2)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "panṭiki"
    glossedTokens := [("pan-ṭi-ki", "tooth-n-DAT")]
    glossedWords := [⟨['p', 'a', 'n', '-', 'ṭ', 'i', '-', 'k', 'i'], ['t', 'o', 'o', 't', 'h', '-', 'n', '-', 'D', 'A', 'T'], [⟨['p', 'a', 'n'], ['t', 'o', 'o', 't', 'h'], none⟩, ⟨['ṭ', 'i'], ['n'], some '-'⟩, ⟨['k', 'i'], ['D', 'A', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "strong"), ("alternation", "nu"), ("follower", "case"), ("weight", "light")] }

def nest_nom : Datum :=
  { id := "aitha2026_nest_nom"
    source := ⟨"aitha-2026", "(2)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "gūḍuø"
    glossedTokens := [("gū-ḍu-ø", "nest-n-NOM")]
    glossedWords := [⟨['g', 'ū', '-', 'ḍ', 'u', '-', 'ø'], ['n', 'e', 's', 't', '-', 'n', '-', 'N', 'O', 'M'], [⟨['g', 'ū'], ['n', 'e', 's', 't'], none⟩, ⟨['ḍ', 'u'], ['n'], some '-'⟩, ⟨['ø'], ['N', 'O', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "strong"), ("alternation", "du")] }

def nest_dat : Datum :=
  { id := "aitha2026_nest_dat"
    source := ⟨"aitha-2026", "(2)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "gūṭiki"
    glossedTokens := [("gū-ṭi-ki", "nest-n-DAT")]
    glossedWords := [⟨['g', 'ū', '-', 'ṭ', 'i', '-', 'k', 'i'], ['n', 'e', 's', 't', '-', 'n', '-', 'D', 'A', 'T'], [⟨['g', 'ū'], ['n', 'e', 's', 't'], none⟩, ⟨['ṭ', 'i'], ['n'], some '-'⟩, ⟨['k', 'i'], ['D', 'A', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "strong"), ("alternation", "du"), ("follower", "case"), ("weight", "light")] }

def stream_nom : Datum :=
  { id := "aitha2026_stream_nom"
    source := ⟨"aitha-2026", "(2)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "ēruø"
    glossedTokens := [("ē-ru-ø", "stream-n-NOM")]
    glossedWords := [⟨['ē', '-', 'r', 'u', '-', 'ø'], ['s', 't', 'r', 'e', 'a', 'm', '-', 'n', '-', 'N', 'O', 'M'], [⟨['ē'], ['s', 't', 'r', 'e', 'a', 'm'], none⟩, ⟨['r', 'u'], ['n'], some '-'⟩, ⟨['ø'], ['N', 'O', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "strong"), ("alternation", "ru")] }

def stream_dat : Datum :=
  { id := "aitha2026_stream_dat"
    source := ⟨"aitha-2026", "(2)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "ēṭiki"
    glossedTokens := [("ē-ṭi-ki", "stream-n-DAT")]
    glossedWords := [⟨['ē', '-', 'ṭ', 'i', '-', 'k', 'i'], ['s', 't', 'r', 'e', 'a', 'm', '-', 'n', '-', 'D', 'A', 'T'], [⟨['ē'], ['s', 't', 'r', 'e', 'a', 'm'], none⟩, ⟨['ṭ', 'i'], ['n'], some '-'⟩, ⟨['k', 'i'], ['D', 'A', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "strong"), ("alternation", "ru"), ("follower", "case"), ("weight", "light")] }

def mouth_nom : Datum :=
  { id := "aitha2026_mouth_nom"
    source := ⟨"aitha-2026", "(2)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "nōruø"
    glossedTokens := [("nō-ru-ø", "mouth-n-NOM")]
    glossedWords := [⟨['n', 'ō', '-', 'r', 'u', '-', 'ø'], ['m', 'o', 'u', 't', 'h', '-', 'n', '-', 'N', 'O', 'M'], [⟨['n', 'ō'], ['m', 'o', 'u', 't', 'h'], none⟩, ⟨['r', 'u'], ['n'], some '-'⟩, ⟨['ø'], ['N', 'O', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "strong"), ("alternation", "ru")] }

def mouth_dat : Datum :=
  { id := "aitha2026_mouth_dat"
    source := ⟨"aitha-2026", "(2)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "nōṭiki"
    glossedTokens := [("nō-ṭi-ki", "mouth-n-DAT")]
    glossedWords := [⟨['n', 'ō', '-', 'ṭ', 'i', '-', 'k', 'i'], ['m', 'o', 'u', 't', 'h', '-', 'n', '-', 'D', 'A', 'T'], [⟨['n', 'ō'], ['m', 'o', 'u', 't', 'h'], none⟩, ⟨['ṭ', 'i'], ['n'], some '-'⟩, ⟨['k', 'i'], ['D', 'A', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "strong"), ("alternation", "ru"), ("follower", "case"), ("weight", "light")] }

def plough_nom : Datum :=
  { id := "aitha2026_plough_nom"
    source := ⟨"aitha-2026", "(2)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "nāgaliø"
    glossedTokens := [("nāga-li-ø", "plough-n-NOM")]
    glossedWords := [⟨['n', 'ā', 'g', 'a', '-', 'l', 'i', '-', 'ø'], ['p', 'l', 'o', 'u', 'g', 'h', '-', 'n', '-', 'N', 'O', 'M'], [⟨['n', 'ā', 'g', 'a'], ['p', 'l', 'o', 'u', 'g', 'h'], none⟩, ⟨['l', 'i'], ['n'], some '-'⟩, ⟨['ø'], ['N', 'O', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "strong"), ("alternation", "li")] }

def plough_dat : Datum :=
  { id := "aitha2026_plough_dat"
    source := ⟨"aitha-2026", "(2)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "nāgaṭiki"
    glossedTokens := [("nāga-ṭi-ki", "plough-n-DAT")]
    glossedWords := [⟨['n', 'ā', 'g', 'a', '-', 'ṭ', 'i', '-', 'k', 'i'], ['p', 'l', 'o', 'u', 'g', 'h', '-', 'n', '-', 'D', 'A', 'T'], [⟨['n', 'ā', 'g', 'a'], ['p', 'l', 'o', 'u', 'g', 'h'], none⟩, ⟨['ṭ', 'i'], ['n'], some '-'⟩, ⟨['k', 'i'], ['D', 'A', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "strong"), ("alternation", "li"), ("follower", "case"), ("weight", "light")] }

def ghee_nom : Datum :=
  { id := "aitha2026_ghee_nom"
    source := ⟨"aitha-2026", "(2)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "nēyiø"
    glossedTokens := [("nē-yi-ø", "ghee-n-NOM")]
    glossedWords := [⟨['n', 'ē', '-', 'y', 'i', '-', 'ø'], ['g', 'h', 'e', 'e', '-', 'n', '-', 'N', 'O', 'M'], [⟨['n', 'ē'], ['g', 'h', 'e', 'e'], none⟩, ⟨['y', 'i'], ['n'], some '-'⟩, ⟨['ø'], ['N', 'O', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "strong"), ("alternation", "yi")] }

def ghee_dat : Datum :=
  { id := "aitha2026_ghee_dat"
    source := ⟨"aitha-2026", "(2)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "nētiki"
    glossedTokens := [("nē-ti-ki", "ghee-n-DAT")]
    glossedWords := [⟨['n', 'ē', '-', 't', 'i', '-', 'k', 'i'], ['g', 'h', 'e', 'e', '-', 'n', '-', 'D', 'A', 'T'], [⟨['n', 'ē'], ['g', 'h', 'e', 'e'], none⟩, ⟨['t', 'i'], ['n'], some '-'⟩, ⟨['k', 'i'], ['D', 'A', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "strong"), ("alternation", "yi"), ("follower", "case"), ("weight", "light")] }

def well_nom : Datum :=
  { id := "aitha2026_well_nom"
    source := ⟨"aitha-2026", "(2)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "nūyiø"
    glossedTokens := [("nū-yi-ø", "well-n-NOM")]
    glossedWords := [⟨['n', 'ū', '-', 'y', 'i', '-', 'ø'], ['w', 'e', 'l', 'l', '-', 'n', '-', 'N', 'O', 'M'], [⟨['n', 'ū'], ['w', 'e', 'l', 'l'], none⟩, ⟨['y', 'i'], ['n'], some '-'⟩, ⟨['ø'], ['N', 'O', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "strong"), ("alternation", "yi")] }

def well_dat : Datum :=
  { id := "aitha2026_well_dat"
    source := ⟨"aitha-2026", "(2)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "nūtiki"
    glossedTokens := [("nū-ti-ki", "well-n-DAT")]
    glossedWords := [⟨['n', 'ū', '-', 't', 'i', '-', 'k', 'i'], ['w', 'e', 'l', 'l', '-', 'n', '-', 'D', 'A', 'T'], [⟨['n', 'ū'], ['w', 'e', 'l', 'l'], none⟩, ⟨['t', 'i'], ['n'], some '-'⟩, ⟨['k', 'i'], ['D', 'A', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "strong"), ("alternation", "yi"), ("follower", "case"), ("weight", "light")] }

def ocean_nom : Datum :=
  { id := "aitha2026_ocean_nom"
    source := ⟨"aitha-2026", "(8)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "samudramø"
    glossedTokens := [("samudr-am-ø", "ocean-n-NOM")]
    glossedWords := [⟨['s', 'a', 'm', 'u', 'd', 'r', '-', 'a', 'm', '-', 'ø'], ['o', 'c', 'e', 'a', 'n', '-', 'n', '-', 'N', 'O', 'M'], [⟨['s', 'a', 'm', 'u', 'd', 'r'], ['o', 'c', 'e', 'a', 'n'], none⟩, ⟨['a', 'm'], ['n'], some '-'⟩, ⟨['ø'], ['N', 'O', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "weak"), ("alternant", "short")] }

def ocean_acc : Datum :=
  { id := "aitha2026_ocean_acc"
    source := ⟨"aitha-2026", "(8)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "samudrānini"
    glossedTokens := [("samudr-āni-ni", "ocean-n-ACC")]
    glossedWords := [⟨['s', 'a', 'm', 'u', 'd', 'r', '-', 'ā', 'n', 'i', '-', 'n', 'i'], ['o', 'c', 'e', 'a', 'n', '-', 'n', '-', 'A', 'C', 'C'], [⟨['s', 'a', 'm', 'u', 'd', 'r'], ['o', 'c', 'e', 'a', 'n'], none⟩, ⟨['ā', 'n', 'i'], ['n'], some '-'⟩, ⟨['n', 'i'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "weak"), ("follower", "case"), ("weight", "light"), ("alternant", "long")] }

def ocean_gen : Datum :=
  { id := "aitha2026_ocean_gen"
    source := ⟨"aitha-2026", "(8)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "samudramø"
    glossedTokens := [("samudr-am-ø", "ocean-n-GEN")]
    glossedWords := [⟨['s', 'a', 'm', 'u', 'd', 'r', '-', 'a', 'm', '-', 'ø'], ['o', 'c', 'e', 'a', 'n', '-', 'n', '-', 'G', 'E', 'N'], [⟨['s', 'a', 'm', 'u', 'd', 'r'], ['o', 'c', 'e', 'a', 'n'], none⟩, ⟨['a', 'm'], ['n'], some '-'⟩, ⟨['ø'], ['G', 'E', 'N'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "weak"), ("alternant", "short")] }

def ocean_dat : Datum :=
  { id := "aitha2026_ocean_dat"
    source := ⟨"aitha-2026", "(8)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "samudrāniki"
    glossedTokens := [("samudr-āni-ki", "ocean-n-DAT")]
    glossedWords := [⟨['s', 'a', 'm', 'u', 'd', 'r', '-', 'ā', 'n', 'i', '-', 'k', 'i'], ['o', 'c', 'e', 'a', 'n', '-', 'n', '-', 'D', 'A', 'T'], [⟨['s', 'a', 'm', 'u', 'd', 'r'], ['o', 'c', 'e', 'a', 'n'], none⟩, ⟨['ā', 'n', 'i'], ['n'], some '-'⟩, ⟨['k', 'i'], ['D', 'A', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "weak"), ("follower", "case"), ("weight", "light"), ("alternant", "long")] }

def ocean_p : Datum :=
  { id := "aitha2026_ocean_p"
    source := ⟨"aitha-2026", "(8)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "samudramlō"
    glossedTokens := [("samudr-am-lō", "ocean-n-in")]
    glossedWords := [⟨['s', 'a', 'm', 'u', 'd', 'r', '-', 'a', 'm', '-', 'l', 'ō'], ['o', 'c', 'e', 'a', 'n', '-', 'n', '-', 'i', 'n'], [⟨['s', 'a', 'm', 'u', 'd', 'r'], ['o', 'c', 'e', 'a', 'n'], none⟩, ⟨['a', 'm'], ['n'], some '-'⟩, ⟨['l', 'ō'], ['i', 'n'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "weak"), ("follower", "postposition"), ("weight", "heavy"), ("alternant", "short")] }

def ocean_1sg : Datum :=
  { id := "aitha2026_ocean_1sg"
    source := ⟨"aitha-2026", "(13)"⟩
    reportedIn := none
    language := "telu1262"
    primaryText := "samudrānini"
    glossedTokens := [("samudr-āni-ni", "ocean-n-1SG")]
    glossedWords := [⟨['s', 'a', 'm', 'u', 'd', 'r', '-', 'ā', 'n', 'i', '-', 'n', 'i'], ['o', 'c', 'e', 'a', 'n', '-', 'n', '-', '1', 'S', 'G'], [⟨['s', 'a', 'm', 'u', 'd', 'r'], ['o', 'c', 'e', 'a', 'n'], none⟩, ⟨['ā', 'n', 'i'], ['n'], some '-'⟩, ⟨['n', 'i'], ['1', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "weak"), ("follower", "agreement"), ("weight", "light"), ("alternant", "long")] }

def ocean_2sg : Datum :=
  { id := "aitha2026_ocean_2sg"
    source := ⟨"aitha-2026", "(14)"⟩
    reportedIn := none
    language := "telu1262"
    primaryText := "samudrānivi"
    glossedTokens := [("samudr-āni-vi", "ocean-n-2SG")]
    glossedWords := [⟨['s', 'a', 'm', 'u', 'd', 'r', '-', 'ā', 'n', 'i', '-', 'v', 'i'], ['o', 'c', 'e', 'a', 'n', '-', 'n', '-', '2', 'S', 'G'], [⟨['s', 'a', 'm', 'u', 'd', 'r'], ['o', 'c', 'e', 'a', 'n'], none⟩, ⟨['ā', 'n', 'i'], ['n'], some '-'⟩, ⟨['v', 'i'], ['2', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "weak"), ("follower", "agreement"), ("weight", "light"), ("alternant", "long")] }

def ocean_3sg : Datum :=
  { id := "aitha2026_ocean_3sg"
    source := ⟨"aitha-2026", "(15)"⟩
    reportedIn := none
    language := "telu1262"
    primaryText := "samudramø"
    glossedTokens := [("samudr-am-ø", "ocean-n-3SG")]
    glossedWords := [⟨['s', 'a', 'm', 'u', 'd', 'r', '-', 'a', 'm', '-', 'ø'], ['o', 'c', 'e', 'a', 'n', '-', 'n', '-', '3', 'S', 'G'], [⟨['s', 'a', 'm', 'u', 'd', 'r'], ['o', 'c', 'e', 'a', 'n'], none⟩, ⟨['a', 'm'], ['n'], some '-'⟩, ⟨['ø'], ['3', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "weak"), ("alternant", "short")] }

def picture_1sg_apc : Datum :=
  { id := "aitha2026_picture_1sg_apc"
    source := ⟨"aitha-2026", "(16)"⟩
    reportedIn := none
    language := "telu1262"
    primaryText := "citrānini"
    glossedTokens := [("citr-āni-ni", "picture-n-1SG")]
    glossedWords := [⟨['c', 'i', 't', 'r', '-', 'ā', 'n', 'i', '-', 'n', 'i'], ['p', 'i', 'c', 't', 'u', 'r', 'e', '-', 'n', '-', '1', 'S', 'G'], [⟨['c', 'i', 't', 'r'], ['p', 'i', 'c', 't', 'u', 'r', 'e'], none⟩, ⟨['ā', 'n', 'i'], ['n'], some '-'⟩, ⟨['n', 'i'], ['1', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "weak"), ("follower", "agreement"), ("weight", "light"), ("alternant", "long")] }

def ocean_whole_acc : Datum :=
  { id := "aitha2026_ocean_whole_acc"
    source := ⟨"aitha-2026", "(17)"⟩
    reportedIn := none
    language := "telu1262"
    primaryText := "samudramantaṭini"
    glossedTokens := [("samudr-am-antaṭi-ni", "ocean-n-whole-ACC")]
    glossedWords := [⟨['s', 'a', 'm', 'u', 'd', 'r', '-', 'a', 'm', '-', 'a', 'n', 't', 'a', 'ṭ', 'i', '-', 'n', 'i'], ['o', 'c', 'e', 'a', 'n', '-', 'n', '-', 'w', 'h', 'o', 'l', 'e', '-', 'A', 'C', 'C'], [⟨['s', 'a', 'm', 'u', 'd', 'r'], ['o', 'c', 'e', 'a', 'n'], none⟩, ⟨['a', 'm'], ['n'], some '-'⟩, ⟨['a', 'n', 't', 'a', 'ṭ', 'i'], ['w', 'h', 'o', 'l', 'e'], some '-'⟩, ⟨['n', 'i'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "weak"), ("follower", "quantifier"), ("weight", "heavy"), ("alternant", "short")] }

def ocean_about : Datum :=
  { id := "aitha2026_ocean_about"
    source := ⟨"aitha-2026", "(18)"⟩
    reportedIn := none
    language := "telu1262"
    primaryText := "samudramgurinci"
    glossedTokens := [("samudr-am-gurinci", "ocean-n-about")]
    glossedWords := [⟨['s', 'a', 'm', 'u', 'd', 'r', '-', 'a', 'm', '-', 'g', 'u', 'r', 'i', 'n', 'c', 'i'], ['o', 'c', 'e', 'a', 'n', '-', 'n', '-', 'a', 'b', 'o', 'u', 't'], [⟨['s', 'a', 'm', 'u', 'd', 'r'], ['o', 'c', 'e', 'a', 'n'], none⟩, ⟨['a', 'm'], ['n'], some '-'⟩, ⟨['g', 'u', 'r', 'i', 'n', 'c', 'i'], ['a', 'b', 'o', 'u', 't'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "weak"), ("follower", "postposition"), ("weight", "light"), ("alternant", "short")] }

def ocean_infront : Datum :=
  { id := "aitha2026_ocean_infront"
    source := ⟨"aitha-2026", "(18)"⟩
    reportedIn := none
    language := "telu1262"
    primaryText := "samudrameduru"
    glossedTokens := [("samudr-am-eduru", "ocean-n-in.front.of")]
    glossedWords := [⟨['s', 'a', 'm', 'u', 'd', 'r', '-', 'a', 'm', '-', 'e', 'd', 'u', 'r', 'u'], ['o', 'c', 'e', 'a', 'n', '-', 'n', '-', 'i', 'n', '.', 'f', 'r', 'o', 'n', 't', '.', 'o', 'f'], [⟨['s', 'a', 'm', 'u', 'd', 'r'], ['o', 'c', 'e', 'a', 'n'], none⟩, ⟨['a', 'm'], ['n'], some '-'⟩, ⟨['e', 'd', 'u', 'r', 'u'], ['i', 'n', '.', 'f', 'r', 'o', 'n', 't', '.', 'o', 'f'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "weak"), ("follower", "postposition"), ("weight", "light"), ("alternant", "short")] }

def house_1sg : Datum :=
  { id := "aitha2026_house_1sg"
    source := ⟨"aitha-2026", "fn. 6"⟩
    reportedIn := none
    language := "telu1262"
    primaryText := "illuni"
    glossedTokens := [("il-lu-ni", "house-n-1SG")]
    glossedWords := [⟨['i', 'l', '-', 'l', 'u', '-', 'n', 'i'], ['h', 'o', 'u', 's', 'e', '-', 'n', '-', '1', 'S', 'G'], [⟨['i', 'l'], ['h', 'o', 'u', 's', 'e'], none⟩, ⟨['l', 'u'], ['n'], some '-'⟩, ⟨['n', 'i'], ['1', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "strong"), ("alternation", "lu"), ("follower", "agreement"), ("weight", "light")] }

def ocean_pl_nom : Datum :=
  { id := "aitha2026_ocean_pl_nom"
    source := ⟨"aitha-2026", "(39)"⟩
    reportedIn := none
    language := "telu1262"
    primaryText := "samudrāluø"
    glossedTokens := [("samudr-ā-lu-ø", "ocean-n-PL-NOM")]
    glossedWords := [⟨['s', 'a', 'm', 'u', 'd', 'r', '-', 'ā', '-', 'l', 'u', '-', 'ø'], ['o', 'c', 'e', 'a', 'n', '-', 'n', '-', 'P', 'L', '-', 'N', 'O', 'M'], [⟨['s', 'a', 'm', 'u', 'd', 'r'], ['o', 'c', 'e', 'a', 'n'], none⟩, ⟨['ā'], ['n'], some '-'⟩, ⟨['l', 'u'], ['P', 'L'], some '-'⟩, ⟨['ø'], ['N', 'O', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "weak"), ("follower", "plural"), ("weight", "light")] }

def ocean_pl_acc : Datum :=
  { id := "aitha2026_ocean_pl_acc"
    source := ⟨"aitha-2026", "(39)"⟩
    reportedIn := none
    language := "telu1262"
    primaryText := "samudrālani"
    glossedTokens := [("samudr-ā-la-ni", "ocean-n-PL-ACC")]
    glossedWords := [⟨['s', 'a', 'm', 'u', 'd', 'r', '-', 'ā', '-', 'l', 'a', '-', 'n', 'i'], ['o', 'c', 'e', 'a', 'n', '-', 'n', '-', 'P', 'L', '-', 'A', 'C', 'C'], [⟨['s', 'a', 'm', 'u', 'd', 'r'], ['o', 'c', 'e', 'a', 'n'], none⟩, ⟨['ā'], ['n'], some '-'⟩, ⟨['l', 'a'], ['P', 'L'], some '-'⟩, ⟨['n', 'i'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "weak"), ("follower", "plural"), ("weight", "light")] }

def ocean_pl_gen : Datum :=
  { id := "aitha2026_ocean_pl_gen"
    source := ⟨"aitha-2026", "(39)"⟩
    reportedIn := none
    language := "telu1262"
    primaryText := "samudrālaø"
    glossedTokens := [("samudr-ā-la-ø", "ocean-n-PL-GEN")]
    glossedWords := [⟨['s', 'a', 'm', 'u', 'd', 'r', '-', 'ā', '-', 'l', 'a', '-', 'ø'], ['o', 'c', 'e', 'a', 'n', '-', 'n', '-', 'P', 'L', '-', 'G', 'E', 'N'], [⟨['s', 'a', 'm', 'u', 'd', 'r'], ['o', 'c', 'e', 'a', 'n'], none⟩, ⟨['ā'], ['n'], some '-'⟩, ⟨['l', 'a'], ['P', 'L'], some '-'⟩, ⟨['ø'], ['G', 'E', 'N'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "weak"), ("follower", "plural"), ("weight", "light")] }

def ocean_pl_dat : Datum :=
  { id := "aitha2026_ocean_pl_dat"
    source := ⟨"aitha-2026", "(39)"⟩
    reportedIn := none
    language := "telu1262"
    primaryText := "samudrālaki"
    glossedTokens := [("samudr-ā-la-ki", "ocean-n-PL-DAT")]
    glossedWords := [⟨['s', 'a', 'm', 'u', 'd', 'r', '-', 'ā', '-', 'l', 'a', '-', 'k', 'i'], ['o', 'c', 'e', 'a', 'n', '-', 'n', '-', 'P', 'L', '-', 'D', 'A', 'T'], [⟨['s', 'a', 'm', 'u', 'd', 'r'], ['o', 'c', 'e', 'a', 'n'], none⟩, ⟨['ā'], ['n'], some '-'⟩, ⟨['l', 'a'], ['P', 'L'], some '-'⟩, ⟨['k', 'i'], ['D', 'A', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "weak"), ("follower", "plural"), ("weight", "light")] }

def ocean_pl_p : Datum :=
  { id := "aitha2026_ocean_pl_p"
    source := ⟨"aitha-2026", "(39)"⟩
    reportedIn := none
    language := "telu1262"
    primaryText := "samudrālalō"
    glossedTokens := [("samudr-ā-la-lō", "ocean-n-PL-in")]
    glossedWords := [⟨['s', 'a', 'm', 'u', 'd', 'r', '-', 'ā', '-', 'l', 'a', '-', 'l', 'ō'], ['o', 'c', 'e', 'a', 'n', '-', 'n', '-', 'P', 'L', '-', 'i', 'n'], [⟨['s', 'a', 'm', 'u', 'd', 'r'], ['o', 'c', 'e', 'a', 'n'], none⟩, ⟨['ā'], ['n'], some '-'⟩, ⟨['l', 'a'], ['P', 'L'], some '-'⟩, ⟨['l', 'ō'], ['i', 'n'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "weak"), ("follower", "plural"), ("weight", "light")] }

def bet_nom : Datum :=
  { id := "aitha2026_bet_nom"
    source := ⟨"aitha-2026", "(6)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "pand-em-ø"
    glossedTokens := [("pand-em-ø", "bet-n-NOM")]
    glossedWords := [⟨['p', 'a', 'n', 'd', '-', 'e', 'm', '-', 'ø'], ['b', 'e', 't', '-', 'n', '-', 'N', 'O', 'M'], [⟨['p', 'a', 'n', 'd'], ['b', 'e', 't'], none⟩, ⟨['e', 'm'], ['n'], some '-'⟩, ⟨['ø'], ['N', 'O', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "weak"), ("alternant", "short")] }

def bet_acc : Datum :=
  { id := "aitha2026_bet_acc"
    source := ⟨"aitha-2026", "(6)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "pand-ǣni-ni"
    glossedTokens := [("pand-ǣni-ni", "bet-n-ACC")]
    glossedWords := [⟨['p', 'a', 'n', 'd', '-', 'ǣ', 'n', 'i', '-', 'n', 'i'], ['b', 'e', 't', '-', 'n', '-', 'A', 'C', 'C'], [⟨['p', 'a', 'n', 'd'], ['b', 'e', 't'], none⟩, ⟨['ǣ', 'n', 'i'], ['n'], some '-'⟩, ⟨['n', 'i'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "weak"), ("follower", "case"), ("weight", "light"), ("alternant", "long")] }

def bet_gen : Datum :=
  { id := "aitha2026_bet_gen"
    source := ⟨"aitha-2026", "(6)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "pand-em-ø"
    glossedTokens := [("pand-em-ø", "bet-n-GEN")]
    glossedWords := [⟨['p', 'a', 'n', 'd', '-', 'e', 'm', '-', 'ø'], ['b', 'e', 't', '-', 'n', '-', 'G', 'E', 'N'], [⟨['p', 'a', 'n', 'd'], ['b', 'e', 't'], none⟩, ⟨['e', 'm'], ['n'], some '-'⟩, ⟨['ø'], ['G', 'E', 'N'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "weak"), ("alternant", "short")] }

def bet_dat : Datum :=
  { id := "aitha2026_bet_dat"
    source := ⟨"aitha-2026", "(6)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "pand-ǣni-ki"
    glossedTokens := [("pand-ǣni-ki", "bet-n-DAT")]
    glossedWords := [⟨['p', 'a', 'n', 'd', '-', 'ǣ', 'n', 'i', '-', 'k', 'i'], ['b', 'e', 't', '-', 'n', '-', 'D', 'A', 'T'], [⟨['p', 'a', 'n', 'd'], ['b', 'e', 't'], none⟩, ⟨['ǣ', 'n', 'i'], ['n'], some '-'⟩, ⟨['k', 'i'], ['D', 'A', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "weak"), ("follower", "case"), ("weight", "light"), ("alternant", "long")] }

def bet_p : Datum :=
  { id := "aitha2026_bet_p"
    source := ⟨"aitha-2026", "(6)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "pand-em-lō"
    glossedTokens := [("pand-em-lō", "bet-n-in")]
    glossedWords := [⟨['p', 'a', 'n', 'd', '-', 'e', 'm', '-', 'l', 'ō'], ['b', 'e', 't', '-', 'n', '-', 'i', 'n'], [⟨['p', 'a', 'n', 'd'], ['b', 'e', 't'], none⟩, ⟨['e', 'm'], ['n'], some '-'⟩, ⟨['l', 'ō'], ['i', 'n'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "weak"), ("follower", "postposition"), ("weight", "heavy"), ("alternant", "short")] }

def wife_nom : Datum :=
  { id := "aitha2026_wife_nom"
    source := ⟨"aitha-2026", "(7)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "peḷḷ-ām-ø"
    glossedTokens := [("peḷḷ-ām-ø", "wife-n-NOM")]
    glossedWords := [⟨['p', 'e', 'ḷ', 'ḷ', '-', 'ā', 'm', '-', 'ø'], ['w', 'i', 'f', 'e', '-', 'n', '-', 'N', 'O', 'M'], [⟨['p', 'e', 'ḷ', 'ḷ'], ['w', 'i', 'f', 'e'], none⟩, ⟨['ā', 'm'], ['n'], some '-'⟩, ⟨['ø'], ['N', 'O', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "weak"), ("alternant", "short")] }

def wife_acc : Datum :=
  { id := "aitha2026_wife_acc"
    source := ⟨"aitha-2026", "(7)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "peḷḷ-āni-ni"
    glossedTokens := [("peḷḷ-āni-ni", "wife-n-ACC")]
    glossedWords := [⟨['p', 'e', 'ḷ', 'ḷ', '-', 'ā', 'n', 'i', '-', 'n', 'i'], ['w', 'i', 'f', 'e', '-', 'n', '-', 'A', 'C', 'C'], [⟨['p', 'e', 'ḷ', 'ḷ'], ['w', 'i', 'f', 'e'], none⟩, ⟨['ā', 'n', 'i'], ['n'], some '-'⟩, ⟨['n', 'i'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "weak"), ("follower", "case"), ("weight", "light"), ("alternant", "long")] }

def wife_gen : Datum :=
  { id := "aitha2026_wife_gen"
    source := ⟨"aitha-2026", "(7)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "peḷḷ-ām-ø"
    glossedTokens := [("peḷḷ-ām-ø", "wife-n-GEN")]
    glossedWords := [⟨['p', 'e', 'ḷ', 'ḷ', '-', 'ā', 'm', '-', 'ø'], ['w', 'i', 'f', 'e', '-', 'n', '-', 'G', 'E', 'N'], [⟨['p', 'e', 'ḷ', 'ḷ'], ['w', 'i', 'f', 'e'], none⟩, ⟨['ā', 'm'], ['n'], some '-'⟩, ⟨['ø'], ['G', 'E', 'N'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "weak"), ("alternant", "short")] }

def wife_dat : Datum :=
  { id := "aitha2026_wife_dat"
    source := ⟨"aitha-2026", "(7)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "peḷḷ-āni-ki"
    glossedTokens := [("peḷḷ-āni-ki", "wife-n-DAT")]
    glossedWords := [⟨['p', 'e', 'ḷ', 'ḷ', '-', 'ā', 'n', 'i', '-', 'k', 'i'], ['w', 'i', 'f', 'e', '-', 'n', '-', 'D', 'A', 'T'], [⟨['p', 'e', 'ḷ', 'ḷ'], ['w', 'i', 'f', 'e'], none⟩, ⟨['ā', 'n', 'i'], ['n'], some '-'⟩, ⟨['k', 'i'], ['D', 'A', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "weak"), ("follower", "case"), ("weight", "light"), ("alternant", "long")] }

def wife_p : Datum :=
  { id := "aitha2026_wife_p"
    source := ⟨"aitha-2026", "(7)"⟩
    reportedIn := none
    method := some .description
    language := "telu1262"
    primaryText := "peḷḷ-ām-lō"
    glossedTokens := [("peḷḷ-ām-lō", "wife-n-in")]
    glossedWords := [⟨['p', 'e', 'ḷ', 'ḷ', '-', 'ā', 'm', '-', 'l', 'ō'], ['w', 'i', 'f', 'e', '-', 'n', '-', 'i', 'n'], [⟨['p', 'e', 'ḷ', 'ḷ'], ['w', 'i', 'f', 'e'], none⟩, ⟨['ā', 'm'], ['n'], some '-'⟩, ⟨['l', 'ō'], ['i', 'n'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "weak"), ("follower", "postposition"), ("weight", "heavy"), ("alternant", "short")] }

def those_all_acc : Datum :=
  { id := "aitha2026_those_all_acc"
    source := ⟨"aitha-2026", "(33)"⟩
    reportedIn := none
    method := some .elicitation
    language := "telu1262"
    primaryText := "nēnu vāṭ-anniṭi-ni cūs-ā-nu"
    glossedTokens := [("nēnu", "1SG.NOM"), ("vāṭ-anniṭi-ni", "3PL.NONHUM.OBL-all-ACC"), ("cūs-ā-nu", "see-PST-1SG")]
    glossedWords := [⟨['n', 'ē', 'n', 'u'], ['1', 'S', 'G', '.', 'N', 'O', 'M'], [⟨['n', 'ē', 'n', 'u'], ['1', 'S', 'G', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['v', 'ā', 'ṭ', '-', 'a', 'n', 'n', 'i', 'ṭ', 'i', '-', 'n', 'i'], ['3', 'P', 'L', '.', 'N', 'O', 'N', 'H', 'U', 'M', '.', 'O', 'B', 'L', '-', 'a', 'l', 'l', '-', 'A', 'C', 'C'], [⟨['v', 'ā', 'ṭ'], ['3', 'P', 'L', '.', 'N', 'O', 'N', 'H', 'U', 'M', '.', 'O', 'B', 'L'], none⟩, ⟨['a', 'n', 'n', 'i', 'ṭ', 'i'], ['a', 'l', 'l'], some '-'⟩, ⟨['n', 'i'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['c', 'ū', 's', '-', 'ā', '-', 'n', 'u'], ['s', 'e', 'e', '-', 'P', 'S', 'T', '-', '1', 'S', 'G'], [⟨['c', 'ū', 's'], ['s', 'e', 'e'], none⟩, ⟨['ā'], ['P', 'S', 'T'], some '-'⟩, ⟨['n', 'u'], ['1', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "strong"), ("follower", "quantifier"), ("weight", "heavy")] }

def ocean_whole_acc_sentence : Datum :=
  { id := "aitha2026_ocean_whole_acc_sentence"
    source := ⟨"aitha-2026", "(34)"⟩
    reportedIn := none
    method := some .elicitation
    language := "telu1262"
    primaryText := "nēnu samudram-antaṭi-ni cūs-ā-nu"
    glossedTokens := [("nēnu", "1SG.NOM"), ("samudram-antaṭi-ni", "ocean.NOM-whole-ACC"), ("cūs-ā-nu", "see-PST-1SG")]
    glossedWords := [⟨['n', 'ē', 'n', 'u'], ['1', 'S', 'G', '.', 'N', 'O', 'M'], [⟨['n', 'ē', 'n', 'u'], ['1', 'S', 'G', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['s', 'a', 'm', 'u', 'd', 'r', 'a', 'm', '-', 'a', 'n', 't', 'a', 'ṭ', 'i', '-', 'n', 'i'], ['o', 'c', 'e', 'a', 'n', '.', 'N', 'O', 'M', '-', 'w', 'h', 'o', 'l', 'e', '-', 'A', 'C', 'C'], [⟨['s', 'a', 'm', 'u', 'd', 'r', 'a', 'm'], ['o', 'c', 'e', 'a', 'n', '.', 'N', 'O', 'M'], none⟩, ⟨['a', 'n', 't', 'a', 'ṭ', 'i'], ['w', 'h', 'o', 'l', 'e'], some '-'⟩, ⟨['n', 'i'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['c', 'ū', 's', '-', 'ā', '-', 'n', 'u'], ['s', 'e', 'e', '-', 'P', 'S', 'T', '-', '1', 'S', 'G'], [⟨['c', 'ū', 's'], ['s', 'e', 'e'], none⟩, ⟨['ā'], ['P', 'S', 'T'], some '-'⟩, ⟨['n', 'u'], ['1', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "weak"), ("follower", "quantifier"), ("weight", "heavy"), ("alternant", "short")] }

def those_all_nom : Datum :=
  { id := "aitha2026_those_all_nom"
    source := ⟨"aitha-2026", "(35)"⟩
    reportedIn := none
    method := some .elicitation
    language := "telu1262"
    primaryText := "av-anni bāgun-nā-yi"
    glossedTokens := [("av-anni", "3PL.NONHUM-all.NOM"), ("bāgun-nā-yi", "be.good-PST-3PL.NONHUM")]
    glossedWords := [⟨['a', 'v', '-', 'a', 'n', 'n', 'i'], ['3', 'P', 'L', '.', 'N', 'O', 'N', 'H', 'U', 'M', '-', 'a', 'l', 'l', '.', 'N', 'O', 'M'], [⟨['a', 'v'], ['3', 'P', 'L', '.', 'N', 'O', 'N', 'H', 'U', 'M'], none⟩, ⟨['a', 'n', 'n', 'i'], ['a', 'l', 'l', '.', 'N', 'O', 'M'], some '-'⟩]⟩, ⟨['b', 'ā', 'g', 'u', 'n', '-', 'n', 'ā', '-', 'y', 'i'], ['b', 'e', '.', 'g', 'o', 'o', 'd', '-', 'P', 'S', 'T', '-', '3', 'P', 'L', '.', 'N', 'O', 'N', 'H', 'U', 'M'], [⟨['b', 'ā', 'g', 'u', 'n'], ['b', 'e', '.', 'g', 'o', 'o', 'd'], none⟩, ⟨['n', 'ā'], ['P', 'S', 'T'], some '-'⟩, ⟨['y', 'i'], ['3', 'P', 'L', '.', 'N', 'O', 'N', 'H', 'U', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("class", "strong"), ("follower", "quantifier"), ("weight", "heavy")] }

def those_all_nom_obl : Datum :=
  { id := "aitha2026_those_all_nom_obl"
    source := ⟨"aitha-2026", "(36)"⟩
    reportedIn := none
    method := some .elicitation
    language := "telu1262"
    primaryText := "vāṭ-anni bāgun-nā-yi"
    glossedTokens := [("vāṭ-anni", "3PL.NONHUM.OBL-all.NOM"), ("bāgun-nā-yi", "be.good-PST-3PL.NONHUM")]
    glossedWords := [⟨['v', 'ā', 'ṭ', '-', 'a', 'n', 'n', 'i'], ['3', 'P', 'L', '.', 'N', 'O', 'N', 'H', 'U', 'M', '.', 'O', 'B', 'L', '-', 'a', 'l', 'l', '.', 'N', 'O', 'M'], [⟨['v', 'ā', 'ṭ'], ['3', 'P', 'L', '.', 'N', 'O', 'N', 'H', 'U', 'M', '.', 'O', 'B', 'L'], none⟩, ⟨['a', 'n', 'n', 'i'], ['a', 'l', 'l', '.', 'N', 'O', 'M'], some '-'⟩]⟩, ⟨['b', 'ā', 'g', 'u', 'n', '-', 'n', 'ā', '-', 'y', 'i'], ['b', 'e', '.', 'g', 'o', 'o', 'd', '-', 'P', 'S', 'T', '-', '3', 'P', 'L', '.', 'N', 'O', 'N', 'H', 'U', 'M'], [⟨['b', 'ā', 'g', 'u', 'n'], ['b', 'e', '.', 'g', 'o', 'o', 'd'], none⟩, ⟨['n', 'ā'], ['P', 'S', 'T'], some '-'⟩, ⟨['y', 'i'], ['3', 'P', 'L', '.', 'N', 'O', 'N', 'H', 'U', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("class", "strong"), ("follower", "quantifier"), ("weight", "heavy")] }

def all : List Datum := [house_nom, house_acc, house_gen, house_dat, house_p, town_nom, town_dat, husband_nom, husband_dat, bow_nom, bow_dat, eye_nom, eye_dat, tooth_nom, tooth_dat, nest_nom, nest_dat, stream_nom, stream_dat, mouth_nom, mouth_dat, plough_nom, plough_dat, ghee_nom, ghee_dat, well_nom, well_dat, ocean_nom, ocean_acc, ocean_gen, ocean_dat, ocean_p, ocean_1sg, ocean_2sg, ocean_3sg, picture_1sg_apc, ocean_whole_acc, ocean_about, ocean_infront, house_1sg, ocean_pl_nom, ocean_pl_acc, ocean_pl_gen, ocean_pl_dat, ocean_pl_p, bet_nom, bet_acc, bet_gen, bet_dat, bet_p, wife_nom, wife_acc, wife_gen, wife_dat, wife_p, those_all_acc, ocean_whole_acc_sentence, those_all_nom, those_all_nom_obl]

/-- The two classes of alternating nouns. -/
inductive NounClass where
  /-- strong: strongly suppletive: the exponent of n differs between the nominative and every other case (§2) -/
  | strong
  /-- weak: weakly suppletive: n is *-am* or *-āni* (§3) -/
  | weak
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `class`. -/
def nounClass (e : Datum) : Option NounClass :=
  e.parse? "class" [("strong", .strong), ("weak", .weak)]

/-- The rows of (2): the nominative exponent of n that a strong noun takes. -/
inductive Alternation where
  /-- u: *-u* ~ *-i* -/
  | u
  /-- lu: *-lu* ~ *-ṭi* -/
  | lu
  /-- nu: *-nu* ~ *-ṭi* -/
  | nu
  /-- du: *-ḍu* ~ *-ṭi* -/
  | du
  /-- ru: *-ru* ~ *-ṭi* -/
  | ru
  /-- li: *-li* ~ *-ṭi* -/
  | li
  /-- yi: *-yi* ~ *-ti* -/
  | yi
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `alternation`. -/
def alternation (e : Datum) : Option Alternation :=
  e.parse? "alternation" [("u", .u), ("lu", .lu), ("nu", .nu), ("du", .du), ("ru", .ru), ("li", .li), ("yi", .yi)]

/-- The overt morpheme after the noun stem, where there is one. -/
inductive Follower where
  /-- case: a case suffix -/
  | case
  /-- agreement: a nominal agreement suffix (12) -/
  | agreement
  /-- quantifier: a postposed quantifier -/
  | quantifier
  /-- postposition: a postposition -/
  | postposition
  /-- plural: the plural suffix -/
  | plural
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `follower`. -/
def follower (e : Datum) : Option Follower :=
  e.parse? "follower" [("case", .case), ("agreement", .agreement), ("quantifier", .quantifier),
    ("postposition", .postposition), ("plural", .plural)]

/-- The weight of the first syllable of the morpheme after the noun stem. -/
inductive Weight where
  /-- light: a short vowel and no coda -/
  | light
  /-- heavy: a long vowel or a coda -/
  | heavy
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `weight`. -/
def weight (e : Datum) : Option Weight :=
  e.parse? "weight" [("light", .light), ("heavy", .heavy)]

/-- The form of a singular weak noun. -/
inductive Alternant where
  /-- long: the long form, *-āni* -/
  | long
  /-- short: the short form, *-am* -/
  | short
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `alternant`. -/
def alternant (e : Datum) : Option Alternant :=
  e.parse? "alternant" [("long", .long), ("short", .short)]

end Aitha2026.Examples
