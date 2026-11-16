module

public import Linglib.Data.Examples.Schema

/-!
# `Hyman2006` — typed example data

Auto-generated from `Linglib/Data/Examples/Hyman2006.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Hyman2006.Examples`.
-/

@[expose] public section

namespace Hyman2006.Examples

def makura : Datum :=
  { id := "hyman2006_makura"
    source := ⟨"hyman-2006", "(4)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "makura ga"
    glossedTokens := [("makura", "pillow"), ("ga", "NOM")]
    glossedWords := [⟨['m', 'a', 'k', 'u', 'r', 'a'], ['p', 'i', 'l', 'l', 'o', 'w'], [⟨['m', 'a', 'k', 'u', 'r', 'a'], ['p', 'i', 'l', 'l', 'o', 'w'], none⟩]⟩, ⟨['g', 'a'], ['N', 'O', 'M'], [⟨['g', 'a'], ['N', 'O', 'M'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("output", "mákùrà gà"), ("accent", "initial mora")] }

def kokoro : Datum :=
  { id := "hyman2006_kokoro"
    source := ⟨"hyman-2006", "(4)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "kokoro ga"
    glossedTokens := [("kokoro", "heart"), ("ga", "NOM")]
    glossedWords := [⟨['k', 'o', 'k', 'o', 'r', 'o'], ['h', 'e', 'a', 'r', 't'], [⟨['k', 'o', 'k', 'o', 'r', 'o'], ['h', 'e', 'a', 'r', 't'], none⟩]⟩, ⟨['g', 'a'], ['N', 'O', 'M'], [⟨['g', 'a'], ['N', 'O', 'M'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("output", "kókórò gà"), ("accent", "second mora")] }

def atama : Datum :=
  { id := "hyman2006_atama"
    source := ⟨"hyman-2006", "(4)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "atama ga"
    glossedTokens := [("atama", "head"), ("ga", "NOM")]
    glossedWords := [⟨['a', 't', 'a', 'm', 'a'], ['h', 'e', 'a', 'd'], [⟨['a', 't', 'a', 'm', 'a'], ['h', 'e', 'a', 'd'], none⟩]⟩, ⟨['g', 'a'], ['N', 'O', 'M'], [⟨['g', 'a'], ['N', 'O', 'M'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("output", "átámá gà"), ("accent", "final mora")] }

def sakana : Datum :=
  { id := "hyman2006_sakana"
    source := ⟨"hyman-2006", "(4)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "sakana ga"
    glossedTokens := [("sakana", "fish"), ("ga", "NOM")]
    glossedWords := [⟨['s', 'a', 'k', 'a', 'n', 'a'], ['f', 'i', 's', 'h'], [⟨['s', 'a', 'k', 'a', 'n', 'a'], ['f', 'i', 's', 'h'], none⟩]⟩, ⟨['g', 'a'], ['N', 'O', 'M'], [⟨['g', 'a'], ['N', 'O', 'M'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("output", "sákáná gá"), ("accent", "none"), ("note", "unaccented: no pitch drop")] }

def all : List Datum := [makura, kokoro, atama, sakana]

end Hyman2006.Examples
