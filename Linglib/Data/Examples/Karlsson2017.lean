module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Karlsson2017` — typed example data

Auto-generated from `Linglib/Data/Examples/Karlsson2017.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Karlsson2017.Examples`.
-/

@[expose] public section

namespace Karlsson2017.Examples

def neg1 : Datum :=
  { id := "karlsson2017_neg1"
    source := ⟨"karlsson-2017", "12.2.2 (1)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "En lähetä tekstiviestiä."
    glossedTokens := [("E-n", ""), ("+lähetä", ""), ("teksti=viesti-ä.", "")]
    glossedWords := [⟨['E', '-', 'n'], [], [⟨['E'], [], none⟩, ⟨['n'], [], some '-'⟩]⟩, ⟨['+', 'l', 'ä', 'h', 'e', 't', 'ä'], [], [⟨['l', 'ä', 'h', 'e', 't', 'ä'], [], none⟩]⟩, ⟨['t', 'e', 'k', 's', 't', 'i', '=', 'v', 'i', 'e', 's', 't', 'i', '-', 'ä', '.'], [], [⟨['t', 'e', 'k', 's', 't', 'i'], [], none⟩, ⟨['v', 'i', 'e', 's', 't', 'i'], [], some '='⟩, ⟨['ä'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "object", none⟩]
    paperFeatures := [("section", "12.2.2"), ("negated", "yes"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "other"), ("number", "singular"), ("clause", "finite")] }

def neg2 : Datum :=
  { id := "karlsson2017_neg2"
    source := ⟨"karlsson-2017", "12.2.2 (1)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Pekka ei nähnyt Leenaa."
    glossedTokens := [("Pekka", ""), ("ei", ""), ("näh-nyt", ""), ("Leena-a.", "")]
    glossedWords := [⟨['P', 'e', 'k', 'k', 'a'], [], [⟨['P', 'e', 'k', 'k', 'a'], [], none⟩]⟩, ⟨['e', 'i'], [], [⟨['e', 'i'], [], none⟩]⟩, ⟨['n', 'ä', 'h', '-', 'n', 'y', 't'], [], [⟨['n', 'ä', 'h'], [], none⟩, ⟨['n', 'y', 't'], [], some '-'⟩]⟩, ⟨['L', 'e', 'e', 'n', 'a', '-', 'a', '.'], [], [⟨['L', 'e', 'e', 'n', 'a'], [], none⟩, ⟨['a'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "object", none⟩]
    paperFeatures := [("section", "12.2.2"), ("negated", "yes"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "other"), ("number", "singular"), ("clause", "finite")] }

def neg3 : Datum :=
  { id := "karlsson2017_neg3"
    source := ⟨"karlsson-2017", "12.2.2 (1)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "En tunne noita miehiä."
    glossedTokens := [("E-n", ""), ("+tunne", ""), ("no-i-ta", ""), ("mieh-i-ä.", "")]
    glossedWords := [⟨['E', '-', 'n'], [], [⟨['E'], [], none⟩, ⟨['n'], [], some '-'⟩]⟩, ⟨['+', 't', 'u', 'n', 'n', 'e'], [], [⟨['t', 'u', 'n', 'n', 'e'], [], none⟩]⟩, ⟨['n', 'o', '-', 'i', '-', 't', 'a'], [], [⟨['n', 'o'], [], none⟩, ⟨['i'], [], some '-'⟩, ⟨['t', 'a'], [], some '-'⟩]⟩, ⟨['m', 'i', 'e', 'h', '-', 'i', '-', 'ä', '.'], [], [⟨['m', 'i', 'e', 'h'], [], none⟩, ⟨['i'], [], some '-'⟩, ⟨['ä'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "object", none⟩]
    paperFeatures := [("section", "12.2.2"), ("negated", "yes"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "other"), ("number", "plural"), ("clause", "finite")] }

def neg4 : Datum :=
  { id := "karlsson2017_neg4"
    source := ⟨"karlsson-2017", "12.2.2 (1)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "En ole tavannut häntä."
    glossedTokens := [("E-n", ""), ("ole", ""), ("+tavan-nut", ""), ("hän-tä.", "")]
    glossedWords := [⟨['E', '-', 'n'], [], [⟨['E'], [], none⟩, ⟨['n'], [], some '-'⟩]⟩, ⟨['o', 'l', 'e'], [], [⟨['o', 'l', 'e'], [], none⟩]⟩, ⟨['+', 't', 'a', 'v', 'a', 'n', '-', 'n', 'u', 't'], [], [⟨['t', 'a', 'v', 'a', 'n'], [], none⟩, ⟨['n', 'u', 't'], [], some '-'⟩]⟩, ⟨['h', 'ä', 'n', '-', 't', 'ä', '.'], [], [⟨['h', 'ä', 'n'], [], none⟩, ⟨['t', 'ä'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "object", none⟩]
    paperFeatures := [("section", "12.2.2"), ("negated", "yes"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "personalPronoun"), ("number", "singular"), ("clause", "finite")] }

def ex_2a_read_part : Datum :=
  { id := "karlsson2017_2a_read_part"
    source := ⟨"karlsson-2017", "12.2.2 (2a)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Tyttö luki kirjaa."
    glossedTokens := [("Tyttö", ""), ("luk-i", ""), ("kirja-a.", "")]
    glossedWords := [⟨['T', 'y', 't', 't', 'ö'], [], [⟨['T', 'y', 't', 't', 'ö'], [], none⟩]⟩, ⟨['l', 'u', 'k', '-', 'i'], [], [⟨['l', 'u', 'k'], [], none⟩, ⟨['i'], [], some '-'⟩]⟩, ⟨['k', 'i', 'r', 'j', 'a', '-', 'a', '.'], [], [⟨['k', 'i', 'r', 'j', 'a'], [], none⟩, ⟨['a'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "object", none⟩]
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "irresultative"), ("quantity", "definite"), ("nominal", "other"), ("number", "singular"), ("clause", "finite")] }

def ex_2a_read_tot : Datum :=
  { id := "karlsson2017_2a_read_tot"
    source := ⟨"karlsson-2017", "12.2.2 (2a)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Tyttö luki kirjan."
    glossedTokens := [("Tyttö", ""), ("luki", ""), ("kirja-n.", "")]
    glossedWords := [⟨['T', 'y', 't', 't', 'ö'], [], [⟨['T', 'y', 't', 't', 'ö'], [], none⟩]⟩, ⟨['l', 'u', 'k', 'i'], [], [⟨['l', 'u', 'k', 'i'], [], none⟩]⟩, ⟨['k', 'i', 'r', 'j', 'a', '-', 'n', '.'], [], [⟨['k', 'i', 'r', 'j', 'a'], [], none⟩, ⟨['n'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "object", none⟩]
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "other"), ("number", "singular"), ("clause", "finite")] }

def ex_2a_drive_part : Datum :=
  { id := "karlsson2017_2a_drive_part"
    source := ⟨"karlsson-2017", "12.2.2 (2a)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Hän ajaa autoa."
    glossedTokens := [("Hän", ""), ("aja-a", ""), ("auto-a.", "")]
    glossedWords := [⟨['H', 'ä', 'n'], [], [⟨['H', 'ä', 'n'], [], none⟩]⟩, ⟨['a', 'j', 'a', '-', 'a'], [], [⟨['a', 'j', 'a'], [], none⟩, ⟨['a'], [], some '-'⟩]⟩, ⟨['a', 'u', 't', 'o', '-', 'a', '.'], [], [⟨['a', 'u', 't', 'o'], [], none⟩, ⟨['a'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "object", none⟩]
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "irresultative"), ("quantity", "definite"), ("nominal", "other"), ("number", "singular"), ("clause", "finite")] }

def ex_2a_drive_tot : Datum :=
  { id := "karlsson2017_2a_drive_tot"
    source := ⟨"karlsson-2017", "12.2.2 (2a)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Hän ajaa auton talliin."
    glossedTokens := [("Hän", ""), ("aja-a", ""), ("auto-n", ""), ("talliin.", "")]
    glossedWords := [⟨['H', 'ä', 'n'], [], [⟨['H', 'ä', 'n'], [], none⟩]⟩, ⟨['a', 'j', 'a', '-', 'a'], [], [⟨['a', 'j', 'a'], [], none⟩, ⟨['a'], [], some '-'⟩]⟩, ⟨['a', 'u', 't', 'o', '-', 'n'], [], [⟨['a', 'u', 't', 'o'], [], none⟩, ⟨['n'], [], some '-'⟩]⟩, ⟨['t', 'a', 'l', 'l', 'i', 'i', 'n', '.'], [], [⟨['t', 'a', 'l', 'l', 'i', 'i', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "object", none⟩]
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "other"), ("number", "singular"), ("clause", "finite")] }

def ex_2a_shoot_part : Datum :=
  { id := "karlsson2017_2a_shoot_part"
    source := ⟨"karlsson-2017", "12.2.2 (2a)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Metsästäjä ampui lintua."
    glossedTokens := [("Metsä>stä>jä", ""), ("ampu-i", ""), ("lintu-a.", "")]
    glossedWords := [⟨['M', 'e', 't', 's', 'ä', '>', 's', 't', 'ä', '>', 'j', 'ä'], [], [⟨['M', 'e', 't', 's', 'ä'], [], none⟩, ⟨['s', 't', 'ä'], [], some '>'⟩, ⟨['j', 'ä'], [], some '>'⟩]⟩, ⟨['a', 'm', 'p', 'u', '-', 'i'], [], [⟨['a', 'm', 'p', 'u'], [], none⟩, ⟨['i'], [], some '-'⟩]⟩, ⟨['l', 'i', 'n', 't', 'u', '-', 'a', '.'], [], [⟨['l', 'i', 'n', 't', 'u'], [], none⟩, ⟨['a'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "object", none⟩]
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "irresultative"), ("quantity", "definite"), ("nominal", "other"), ("number", "singular"), ("clause", "finite")] }

def ex_2a_shoot_tot : Datum :=
  { id := "karlsson2017_2a_shoot_tot"
    source := ⟨"karlsson-2017", "12.2.2 (2a)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Metsästäjä ampui linnun."
    glossedTokens := [("Metsä>stä>jä", ""), ("ampu-i", ""), ("linnu-n.", "")]
    glossedWords := [⟨['M', 'e', 't', 's', 'ä', '>', 's', 't', 'ä', '>', 'j', 'ä'], [], [⟨['M', 'e', 't', 's', 'ä'], [], none⟩, ⟨['s', 't', 'ä'], [], some '>'⟩, ⟨['j', 'ä'], [], some '>'⟩]⟩, ⟨['a', 'm', 'p', 'u', '-', 'i'], [], [⟨['a', 'm', 'p', 'u'], [], none⟩, ⟨['i'], [], some '-'⟩]⟩, ⟨['l', 'i', 'n', 'n', 'u', '-', 'n', '.'], [], [⟨['l', 'i', 'n', 'n', 'u'], [], none⟩, ⟨['n'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "object", none⟩]
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "other"), ("number", "singular"), ("clause", "finite")] }

def ex_2b_love : Datum :=
  { id := "karlsson2017_2b_love"
    source := ⟨"karlsson-2017", "12.2.2 (2b)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Rakastan tuota miestä."
    glossedTokens := [("Rakas>ta-n", ""), ("tuo-ta", ""), ("mies-tä.", "")]
    glossedWords := [⟨['R', 'a', 'k', 'a', 's', '>', 't', 'a', '-', 'n'], [], [⟨['R', 'a', 'k', 'a', 's'], [], none⟩, ⟨['t', 'a'], [], some '>'⟩, ⟨['n'], [], some '-'⟩]⟩, ⟨['t', 'u', 'o', '-', 't', 'a'], [], [⟨['t', 'u', 'o'], [], none⟩, ⟨['t', 'a'], [], some '-'⟩]⟩, ⟨['m', 'i', 'e', 's', '-', 't', 'ä', '.'], [], [⟨['m', 'i', 'e', 's'], [], none⟩, ⟨['t', 'ä'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "object", none⟩]
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "irresultative"), ("quantity", "definite"), ("nominal", "other"), ("number", "singular"), ("clause", "finite")] }

def ex_2b_interest : Datum :=
  { id := "karlsson2017_2b_interest"
    source := ⟨"karlsson-2017", "12.2.2 (2b)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Suomi kiinnostaa minua."
    glossedTokens := [("Suomi", ""), ("kiinnosta-a", ""), ("minu-a.", "")]
    glossedWords := [⟨['S', 'u', 'o', 'm', 'i'], [], [⟨['S', 'u', 'o', 'm', 'i'], [], none⟩]⟩, ⟨['k', 'i', 'i', 'n', 'n', 'o', 's', 't', 'a', '-', 'a'], [], [⟨['k', 'i', 'i', 'n', 'n', 'o', 's', 't', 'a'], [], none⟩, ⟨['a'], [], some '-'⟩]⟩, ⟨['m', 'i', 'n', 'u', '-', 'a', '.'], [], [⟨['m', 'i', 'n', 'u'], [], none⟩, ⟨['a'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "object", none⟩]
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "irresultative"), ("quantity", "definite"), ("nominal", "personalPronoun"), ("number", "singular"), ("clause", "finite")] }

def ex_2b_fear : Datum :=
  { id := "karlsson2017_2b_fear"
    source := ⟨"karlsson-2017", "12.2.2 (2b)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Pelkäätkö koiria?"
    glossedTokens := [("Pelkää-t-kö", ""), ("koir-i-a?", "")]
    glossedWords := [⟨['P', 'e', 'l', 'k', 'ä', 'ä', '-', 't', '-', 'k', 'ö'], [], [⟨['P', 'e', 'l', 'k', 'ä', 'ä'], [], none⟩, ⟨['t'], [], some '-'⟩, ⟨['k', 'ö'], [], some '-'⟩]⟩, ⟨['k', 'o', 'i', 'r', '-', 'i', '-', 'a', '?'], [], [⟨['k', 'o', 'i', 'r'], [], none⟩, ⟨['i'], [], some '-'⟩, ⟨['a'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "object", none⟩]
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "irresultative"), ("quantity", "indefinite"), ("nominal", "other"), ("number", "plural"), ("clause", "finite")] }

def ex_3_icecream_part : Datum :=
  { id := "karlsson2017_3_icecream_part"
    source := ⟨"karlsson-2017", "12.2.2 (3)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Ostan jäätelöä."
    glossedTokens := [("Osta-n", ""), ("jäätelö-ä.", "")]
    glossedWords := [⟨['O', 's', 't', 'a', '-', 'n'], [], [⟨['O', 's', 't', 'a'], [], none⟩, ⟨['n'], [], some '-'⟩]⟩, ⟨['j', 'ä', 'ä', 't', 'e', 'l', 'ö', '-', 'ä', '.'], [], [⟨['j', 'ä', 'ä', 't', 'e', 'l', 'ö'], [], none⟩, ⟨['ä'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "object", none⟩]
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "indefinite"), ("nominal", "other"), ("number", "singular"), ("clause", "finite")] }

def ex_3_icecream_tot : Datum :=
  { id := "karlsson2017_3_icecream_tot"
    source := ⟨"karlsson-2017", "12.2.2 (3)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Ostan jäätelön."
    glossedTokens := [("Osta-n", ""), ("jäätelö-n.", "")]
    glossedWords := [⟨['O', 's', 't', 'a', '-', 'n'], [], [⟨['O', 's', 't', 'a'], [], none⟩, ⟨['n'], [], some '-'⟩]⟩, ⟨['j', 'ä', 'ä', 't', 'e', 'l', 'ö', '-', 'n', '.'], [], [⟨['j', 'ä', 'ä', 't', 'e', 'l', 'ö'], [], none⟩, ⟨['n'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "object", none⟩]
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "other"), ("number", "singular"), ("clause", "finite")] }

def ex_3_beer_part : Datum :=
  { id := "karlsson2017_3_beer_part"
    source := ⟨"karlsson-2017", "12.2.2 (3)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Simo juo olutta."
    glossedTokens := [("Simo", ""), ("juo", ""), ("olut-ta.", "")]
    glossedWords := [⟨['S', 'i', 'm', 'o'], [], [⟨['S', 'i', 'm', 'o'], [], none⟩]⟩, ⟨['j', 'u', 'o'], [], [⟨['j', 'u', 'o'], [], none⟩]⟩, ⟨['o', 'l', 'u', 't', '-', 't', 'a', '.'], [], [⟨['o', 'l', 'u', 't'], [], none⟩, ⟨['t', 'a'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "object", none⟩]
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "indefinite"), ("nominal", "other"), ("number", "singular"), ("clause", "finite")] }

def ex_3_beer_tot : Datum :=
  { id := "karlsson2017_3_beer_tot"
    source := ⟨"karlsson-2017", "12.2.2 (3)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Simo juo oluen."
    glossedTokens := [("Simo", ""), ("juo", ""), ("olue-n.", "")]
    glossedWords := [⟨['S', 'i', 'm', 'o'], [], [⟨['S', 'i', 'm', 'o'], [], none⟩]⟩, ⟨['j', 'u', 'o'], [], [⟨['j', 'u', 'o'], [], none⟩]⟩, ⟨['o', 'l', 'u', 'e', '-', 'n', '.'], [], [⟨['o', 'l', 'u', 'e'], [], none⟩, ⟨['n'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "object", none⟩]
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "other"), ("number", "singular"), ("clause", "finite")] }

def ex_3_people_part : Datum :=
  { id := "karlsson2017_3_people_part"
    source := ⟨"karlsson-2017", "12.2.2 (3)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Näen ihmisiä."
    glossedTokens := [("+Näe-n", ""), ("ihmis-i-ä.", "")]
    glossedWords := [⟨['+', 'N', 'ä', 'e', '-', 'n'], [], [⟨['N', 'ä', 'e'], [], none⟩, ⟨['n'], [], some '-'⟩]⟩, ⟨['i', 'h', 'm', 'i', 's', '-', 'i', '-', 'ä', '.'], [], [⟨['i', 'h', 'm', 'i', 's'], [], none⟩, ⟨['i'], [], some '-'⟩, ⟨['ä'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "object", none⟩]
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "indefinite"), ("nominal", "other"), ("number", "plural"), ("clause", "finite")] }

def ex_3_people_tot : Datum :=
  { id := "karlsson2017_3_people_tot"
    source := ⟨"karlsson-2017", "12.2.2 (3)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Näen ihmiset."
    glossedTokens := [("Näen", ""), ("ihmise-t.", "")]
    glossedWords := [⟨['N', 'ä', 'e', 'n'], [], [⟨['N', 'ä', 'e', 'n'], [], none⟩]⟩, ⟨['i', 'h', 'm', 'i', 's', 'e', '-', 't', '.'], [], [⟨['i', 'h', 'm', 'i', 's', 'e'], [], none⟩, ⟨['t'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "object", none⟩]
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "other"), ("number", "plural"), ("clause", "finite")] }

def ex_3_guests_part : Datum :=
  { id := "karlsson2017_3_guests_part"
    source := ⟨"karlsson-2017", "12.2.2 (3)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Tuula tapaa vieraita."
    glossedTokens := [("Tuula", ""), ("tapaa", ""), ("viera-i-ta.", "")]
    glossedWords := [⟨['T', 'u', 'u', 'l', 'a'], [], [⟨['T', 'u', 'u', 'l', 'a'], [], none⟩]⟩, ⟨['t', 'a', 'p', 'a', 'a'], [], [⟨['t', 'a', 'p', 'a', 'a'], [], none⟩]⟩, ⟨['v', 'i', 'e', 'r', 'a', '-', 'i', '-', 't', 'a', '.'], [], [⟨['v', 'i', 'e', 'r', 'a'], [], none⟩, ⟨['i'], [], some '-'⟩, ⟨['t', 'a'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "object", none⟩]
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "indefinite"), ("nominal", "other"), ("number", "plural"), ("clause", "finite")] }

def ex_3_guests_tot : Datum :=
  { id := "karlsson2017_3_guests_tot"
    source := ⟨"karlsson-2017", "12.2.2 (3)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Tuula tapaa vieraat."
    glossedTokens := [("Tuula", ""), ("tapaa", ""), ("vieraa-t.", "")]
    glossedWords := [⟨['T', 'u', 'u', 'l', 'a'], [], [⟨['T', 'u', 'u', 'l', 'a'], [], none⟩]⟩, ⟨['t', 'a', 'p', 'a', 'a'], [], [⟨['t', 'a', 'p', 'a', 'a'], [], none⟩]⟩, ⟨['v', 'i', 'e', 'r', 'a', 'a', '-', 't', '.'], [], [⟨['v', 'i', 'e', 'r', 'a', 'a'], [], none⟩, ⟨['t'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "object", none⟩]
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "other"), ("number", "plural"), ("clause", "finite")] }

def tot_message : Datum :=
  { id := "karlsson2017_tot_message"
    source := ⟨"karlsson-2017", "12.2.2"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "(Minä) lähetän tekstiviestin."
    glossedTokens := [("(Minä)", ""), ("+lähetä-n", ""), ("teksti=viesti-n.", "")]
    glossedWords := [⟨['(', 'M', 'i', 'n', 'ä', ')'], [], [⟨['M', 'i', 'n', 'ä'], [], none⟩]⟩, ⟨['+', 'l', 'ä', 'h', 'e', 't', 'ä', '-', 'n'], [], [⟨['l', 'ä', 'h', 'e', 't', 'ä'], [], none⟩, ⟨['n'], [], some '-'⟩]⟩, ⟨['t', 'e', 'k', 's', 't', 'i', '=', 'v', 'i', 'e', 's', 't', 'i', '-', 'n', '.'], [], [⟨['t', 'e', 'k', 's', 't', 'i'], [], none⟩, ⟨['v', 'i', 'e', 's', 't', 'i'], [], some '='⟩, ⟨['n'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "object", none⟩]
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "other"), ("number", "singular"), ("clause", "finite")] }

def tot_milk : Datum :=
  { id := "karlsson2017_tot_milk"
    source := ⟨"karlsson-2017", "12.2.2"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Silja joi maidon."
    glossedTokens := [("Silja", ""), ("jo-i", ""), ("+maido-n.", "")]
    glossedWords := [⟨['S', 'i', 'l', 'j', 'a'], [], [⟨['S', 'i', 'l', 'j', 'a'], [], none⟩]⟩, ⟨['j', 'o', '-', 'i'], [], [⟨['j', 'o'], [], none⟩, ⟨['i'], [], some '-'⟩]⟩, ⟨['+', 'm', 'a', 'i', 'd', 'o', '-', 'n', '.'], [], [⟨['m', 'a', 'i', 'd', 'o'], [], none⟩, ⟨['n'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "object", none⟩]
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "other"), ("number", "singular"), ("clause", "finite")] }

def tot_car_imp : Datum :=
  { id := "karlsson2017_tot_car_imp"
    source := ⟨"karlsson-2017", "12.2.2"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Osta auto."
    glossedTokens := [("Osta", ""), ("auto.", "")]
    glossedWords := [⟨['O', 's', 't', 'a'], [], [⟨['O', 's', 't', 'a'], [], none⟩]⟩, ⟨['a', 'u', 't', 'o', '.'], [], [⟨['a', 'u', 't', 'o'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "object", none⟩]
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "other"), ("number", "singular"), ("clause", "imperative")] }

def tot_computers : Datum :=
  { id := "karlsson2017_tot_computers"
    source := ⟨"karlsson-2017", "12.2.2"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Tietokoneet hankittiin halvalla."
    glossedTokens := [("Tiet>o=konee-t", ""), ("hankittiin", ""), ("+halva-lla.", "")]
    glossedWords := [⟨['T', 'i', 'e', 't', '>', 'o', '=', 'k', 'o', 'n', 'e', 'e', '-', 't'], [], [⟨['T', 'i', 'e', 't'], [], none⟩, ⟨['o'], [], some '>'⟩, ⟨['k', 'o', 'n', 'e', 'e'], [], some '='⟩, ⟨['t'], [], some '-'⟩]⟩, ⟨['h', 'a', 'n', 'k', 'i', 't', 't', 'i', 'i', 'n'], [], [⟨['h', 'a', 'n', 'k', 'i', 't', 't', 'i', 'i', 'n'], [], none⟩]⟩, ⟨['+', 'h', 'a', 'l', 'v', 'a', '-', 'l', 'l', 'a', '.'], [], [⟨['h', 'a', 'l', 'v', 'a'], [], none⟩, ⟨['l', 'l', 'a'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "object", none⟩]
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "other"), ("number", "plural"), ("clause", "passive")] }

def tot_cars : Datum :=
  { id := "karlsson2017_tot_cars"
    source := ⟨"karlsson-2017", "12.2.2"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Ostamme autot."
    glossedTokens := [("Osta-mme", ""), ("auto-t.", "")]
    glossedWords := [⟨['O', 's', 't', 'a', '-', 'm', 'm', 'e'], [], [⟨['O', 's', 't', 'a'], [], none⟩, ⟨['m', 'm', 'e'], [], some '-'⟩]⟩, ⟨['a', 'u', 't', 'o', '-', 't', '.'], [], [⟨['a', 'u', 't', 'o'], [], none⟩, ⟨['t'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "object", none⟩]
    paperFeatures := [("section", "12.2.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "other"), ("number", "plural"), ("clause", "finite")] }

def acc_took : Datum :=
  { id := "karlsson2017_acc_took"
    source := ⟨"karlsson-2017", "13.3.2 (1)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Risto vei minut elokuviin."
    glossedTokens := [("Risto", ""), ("ve-i", ""), ("minu-t", ""), ("elo=kuv-i-in.", "")]
    glossedWords := [⟨['R', 'i', 's', 't', 'o'], [], [⟨['R', 'i', 's', 't', 'o'], [], none⟩]⟩, ⟨['v', 'e', '-', 'i'], [], [⟨['v', 'e'], [], none⟩, ⟨['i'], [], some '-'⟩]⟩, ⟨['m', 'i', 'n', 'u', '-', 't'], [], [⟨['m', 'i', 'n', 'u'], [], none⟩, ⟨['t'], [], some '-'⟩]⟩, ⟨['e', 'l', 'o', '=', 'k', 'u', 'v', '-', 'i', '-', 'i', 'n', '.'], [], [⟨['e', 'l', 'o'], [], none⟩, ⟨['k', 'u', 'v'], [], some '='⟩, ⟨['i'], [], some '-'⟩, ⟨['i', 'n'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "object", none⟩]
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "personalPronoun"), ("number", "singular"), ("clause", "finite")] }

def acc_take_imp : Datum :=
  { id := "karlsson2017_acc_take_imp"
    source := ⟨"karlsson-2017", "13.3.2 (1)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Vie minut elokuviin!"
    glossedTokens := [("Vie", ""), ("minu-t", ""), ("elo=kuv-i-in!", "")]
    glossedWords := [⟨['V', 'i', 'e'], [], [⟨['V', 'i', 'e'], [], none⟩]⟩, ⟨['m', 'i', 'n', 'u', '-', 't'], [], [⟨['m', 'i', 'n', 'u'], [], none⟩, ⟨['t'], [], some '-'⟩]⟩, ⟨['e', 'l', 'o', '=', 'k', 'u', 'v', '-', 'i', '-', 'i', 'n', '!'], [], [⟨['e', 'l', 'o'], [], none⟩, ⟨['k', 'u', 'v'], [], some '='⟩, ⟨['i'], [], some '-'⟩, ⟨['i', 'n'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "object", none⟩]
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "personalPronoun"), ("number", "singular"), ("clause", "imperative")] }

def acc_taken : Datum :=
  { id := "karlsson2017_acc_taken"
    source := ⟨"karlsson-2017", "13.3.2 (1)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Minut vietiin elokuviin."
    glossedTokens := [("Minu-t", ""), ("vie-t-i-in", ""), ("elo=kuv-i-in.", "")]
    glossedWords := [⟨['M', 'i', 'n', 'u', '-', 't'], [], [⟨['M', 'i', 'n', 'u'], [], none⟩, ⟨['t'], [], some '-'⟩]⟩, ⟨['v', 'i', 'e', '-', 't', '-', 'i', '-', 'i', 'n'], [], [⟨['v', 'i', 'e'], [], none⟩, ⟨['t'], [], some '-'⟩, ⟨['i'], [], some '-'⟩, ⟨['i', 'n'], [], some '-'⟩]⟩, ⟨['e', 'l', 'o', '=', 'k', 'u', 'v', '-', 'i', '-', 'i', 'n', '.'], [], [⟨['e', 'l', 'o'], [], none⟩, ⟨['k', 'u', 'v'], [], some '='⟩, ⟨['i'], [], some '-'⟩, ⟨['i', 'n'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "object", none⟩]
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "personalPronoun"), ("number", "singular"), ("clause", "passive")] }

def acc_whom : Datum :=
  { id := "karlsson2017_acc_whom"
    source := ⟨"karlsson-2017", "13.3.2 (1)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Kenet näit?"
    glossedTokens := [("Kene-t", ""), ("+nä-i-t?", "")]
    glossedWords := [⟨['K', 'e', 'n', 'e', '-', 't'], [], [⟨['K', 'e', 'n', 'e'], [], none⟩, ⟨['t'], [], some '-'⟩]⟩, ⟨['+', 'n', 'ä', '-', 'i', '-', 't', '?'], [], [⟨['n', 'ä'], [], none⟩, ⟨['i'], [], some '-'⟩, ⟨['t'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "object", none⟩]
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "personalPronoun"), ("number", "singular"), ("clause", "finite")] }

def pl_articles : Datum :=
  { id := "karlsson2017_pl_articles"
    source := ⟨"karlsson-2017", "13.3.2 (2)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Luen artikkelit."
    glossedTokens := [("+Lue-n", ""), ("artikkeli-t.", "")]
    glossedWords := [⟨['+', 'L', 'u', 'e', '-', 'n'], [], [⟨['L', 'u', 'e'], [], none⟩, ⟨['n'], [], some '-'⟩]⟩, ⟨['a', 'r', 't', 'i', 'k', 'k', 'e', 'l', 'i', '-', 't', '.'], [], [⟨['a', 'r', 't', 'i', 'k', 'k', 'e', 'l', 'i'], [], none⟩, ⟨['t'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "object", none⟩]
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "other"), ("number", "plural"), ("clause", "finite")] }

def pl_children_imp : Datum :=
  { id := "karlsson2017_pl_children_imp"
    source := ⟨"karlsson-2017", "13.3.2 (2)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Vie lapset tarhaan."
    glossedTokens := [("Vie", ""), ("lapse-t", ""), ("tarha-an.", "")]
    glossedWords := [⟨['V', 'i', 'e'], [], [⟨['V', 'i', 'e'], [], none⟩]⟩, ⟨['l', 'a', 'p', 's', 'e', '-', 't'], [], [⟨['l', 'a', 'p', 's', 'e'], [], none⟩, ⟨['t'], [], some '-'⟩]⟩, ⟨['t', 'a', 'r', 'h', 'a', '-', 'a', 'n', '.'], [], [⟨['t', 'a', 'r', 'h', 'a'], [], none⟩, ⟨['a', 'n'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "object", none⟩]
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "other"), ("number", "plural"), ("clause", "imperative")] }

def pl_children_pass : Datum :=
  { id := "karlsson2017_pl_children_pass"
    source := ⟨"karlsson-2017", "13.3.2 (2)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Lapset vietiin tarhaan."
    glossedTokens := [("Lapse-t", ""), ("vie-t-i-in", ""), ("tarha-an.", "")]
    glossedWords := [⟨['L', 'a', 'p', 's', 'e', '-', 't'], [], [⟨['L', 'a', 'p', 's', 'e'], [], none⟩, ⟨['t'], [], some '-'⟩]⟩, ⟨['v', 'i', 'e', '-', 't', '-', 'i', '-', 'i', 'n'], [], [⟨['v', 'i', 'e'], [], none⟩, ⟨['t'], [], some '-'⟩, ⟨['i'], [], some '-'⟩, ⟨['i', 'n'], [], some '-'⟩]⟩, ⟨['t', 'a', 'r', 'h', 'a', '-', 'a', 'n', '.'], [], [⟨['t', 'a', 'r', 'h', 'a'], [], none⟩, ⟨['a', 'n'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "object", none⟩]
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "other"), ("number", "plural"), ("clause", "passive")] }

def num_articles : Datum :=
  { id := "karlsson2017_num_articles"
    source := ⟨"karlsson-2017", "13.3.2 (3)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Luen kaksi artikkelia."
    glossedTokens := [("+Lue-n", ""), ("kaksi", ""), ("artikkeli-a.", "")]
    glossedWords := [⟨['+', 'L', 'u', 'e', '-', 'n'], [], [⟨['L', 'u', 'e'], [], none⟩, ⟨['n'], [], some '-'⟩]⟩, ⟨['k', 'a', 'k', 's', 'i'], [], [⟨['k', 'a', 'k', 's', 'i'], [], none⟩]⟩, ⟨['a', 'r', 't', 'i', 'k', 'k', 'e', 'l', 'i', '-', 'a', '.'], [], [⟨['a', 'r', 't', 'i', 'k', 'k', 'e', 'l', 'i'], [], none⟩, ⟨['a'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "object", none⟩]
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "numeral"), ("number", "singular"), ("clause", "finite")] }

def num_children_imp : Datum :=
  { id := "karlsson2017_num_children_imp"
    source := ⟨"karlsson-2017", "13.3.2 (3)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Vie nuo kolme lasta ulos."
    glossedTokens := [("Vie", ""), ("nuo", ""), ("kolme", ""), ("las-ta", ""), ("ulos.", "")]
    glossedWords := [⟨['V', 'i', 'e'], [], [⟨['V', 'i', 'e'], [], none⟩]⟩, ⟨['n', 'u', 'o'], [], [⟨['n', 'u', 'o'], [], none⟩]⟩, ⟨['k', 'o', 'l', 'm', 'e'], [], [⟨['k', 'o', 'l', 'm', 'e'], [], none⟩]⟩, ⟨['l', 'a', 's', '-', 't', 'a'], [], [⟨['l', 'a', 's'], [], none⟩, ⟨['t', 'a'], [], some '-'⟩]⟩, ⟨['u', 'l', 'o', 's', '.'], [], [⟨['u', 'l', 'o', 's'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "object", none⟩]
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "numeral"), ("number", "singular"), ("clause", "imperative")] }

def num_children_pass : Datum :=
  { id := "karlsson2017_num_children_pass"
    source := ⟨"karlsson-2017", "13.3.2 (3)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Kolme lasta vietiin tarhaan."
    glossedTokens := [("Kolme", ""), ("las-ta", ""), ("vie-t-i-in", ""), ("tarha-an.", "")]
    glossedWords := [⟨['K', 'o', 'l', 'm', 'e'], [], [⟨['K', 'o', 'l', 'm', 'e'], [], none⟩]⟩, ⟨['l', 'a', 's', '-', 't', 'a'], [], [⟨['l', 'a', 's'], [], none⟩, ⟨['t', 'a'], [], some '-'⟩]⟩, ⟨['v', 'i', 'e', '-', 't', '-', 'i', '-', 'i', 'n'], [], [⟨['v', 'i', 'e'], [], none⟩, ⟨['t'], [], some '-'⟩, ⟨['i'], [], some '-'⟩, ⟨['i', 'n'], [], some '-'⟩]⟩, ⟨['t', 'a', 'r', 'h', 'a', '-', 'a', 'n', '.'], [], [⟨['t', 'a', 'r', 'h', 'a'], [], none⟩, ⟨['a', 'n'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "object", none⟩]
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "numeral"), ("number", "singular"), ("clause", "passive")] }

def sg_camera : Datum :=
  { id := "karlsson2017_sg_camera"
    source := ⟨"karlsson-2017", "13.3.2 (4)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "(Minä) ostan digikameran."
    glossedTokens := [("(Minä)", ""), ("osta-n", ""), ("digi=kamera-n.", "")]
    glossedWords := [⟨['(', 'M', 'i', 'n', 'ä', ')'], [], [⟨['M', 'i', 'n', 'ä'], [], none⟩]⟩, ⟨['o', 's', 't', 'a', '-', 'n'], [], [⟨['o', 's', 't', 'a'], [], none⟩, ⟨['n'], [], some '-'⟩]⟩, ⟨['d', 'i', 'g', 'i', '=', 'k', 'a', 'm', 'e', 'r', 'a', '-', 'n', '.'], [], [⟨['d', 'i', 'g', 'i'], [], none⟩, ⟨['k', 'a', 'm', 'e', 'r', 'a'], [], some '='⟩, ⟨['n'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "object", none⟩]
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "other"), ("number", "singular"), ("clause", "finite")] }

def sg_child : Datum :=
  { id := "karlsson2017_sg_child"
    source := ⟨"karlsson-2017", "13.3.2 (4)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Isä vie lapsen tarhaan."
    glossedTokens := [("Isä", ""), ("vie", ""), ("lapse-n", ""), ("tarha-an.", "")]
    glossedWords := [⟨['I', 's', 'ä'], [], [⟨['I', 's', 'ä'], [], none⟩]⟩, ⟨['v', 'i', 'e'], [], [⟨['v', 'i', 'e'], [], none⟩]⟩, ⟨['l', 'a', 'p', 's', 'e', '-', 'n'], [], [⟨['l', 'a', 'p', 's', 'e'], [], none⟩, ⟨['n'], [], some '-'⟩]⟩, ⟨['t', 'a', 'r', 'h', 'a', '-', 'a', 'n', '.'], [], [⟨['t', 'a', 'r', 'h', 'a'], [], none⟩, ⟨['a', 'n'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "object", none⟩]
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "other"), ("number", "singular"), ("clause", "finite")] }

def sg_window : Datum :=
  { id := "karlsson2017_sg_window"
    source := ⟨"karlsson-2017", "13.3.2 (4)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Sylvi avaa ikkunan."
    glossedTokens := [("Sylvi", ""), ("avaa", ""), ("ikkuna-n.", "")]
    glossedWords := [⟨['S', 'y', 'l', 'v', 'i'], [], [⟨['S', 'y', 'l', 'v', 'i'], [], none⟩]⟩, ⟨['a', 'v', 'a', 'a'], [], [⟨['a', 'v', 'a', 'a'], [], none⟩]⟩, ⟨['i', 'k', 'k', 'u', 'n', 'a', '-', 'n', '.'], [], [⟨['i', 'k', 'k', 'u', 'n', 'a'], [], none⟩, ⟨['n'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "object", none⟩]
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "other"), ("number", "singular"), ("clause", "finite")] }

def sg_paper_imp : Datum :=
  { id := "karlsson2017_sg_paper_imp"
    source := ⟨"karlsson-2017", "13.3.2 (4)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Osta lehti!"
    glossedTokens := [("Osta", ""), ("lehti!", "")]
    glossedWords := [⟨['O', 's', 't', 'a'], [], [⟨['O', 's', 't', 'a'], [], none⟩]⟩, ⟨['l', 'e', 'h', 't', 'i', '!'], [], [⟨['l', 'e', 'h', 't', 'i'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "object", none⟩]
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "other"), ("number", "singular"), ("clause", "imperative")] }

def sg_book_pass : Datum :=
  { id := "karlsson2017_sg_book_pass"
    source := ⟨"karlsson-2017", "13.3.2 (4)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Ostettiin kirja."
    glossedTokens := [("Oste-tt-i-in", ""), ("kirja.", "")]
    glossedWords := [⟨['O', 's', 't', 'e', '-', 't', 't', '-', 'i', '-', 'i', 'n'], [], [⟨['O', 's', 't', 'e'], [], none⟩, ⟨['t', 't'], [], some '-'⟩, ⟨['i'], [], some '-'⟩, ⟨['i', 'n'], [], some '-'⟩]⟩, ⟨['k', 'i', 'r', 'j', 'a', '.'], [], [⟨['k', 'i', 'r', 'j', 'a'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "object", none⟩]
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "other"), ("number", "singular"), ("clause", "passive")] }

def sg_dog_pass : Datum :=
  { id := "karlsson2017_sg_dog_pass"
    source := ⟨"karlsson-2017", "13.3.2 (4)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Koira vietiin pois."
    glossedTokens := [("Koira", ""), ("vie-t-i-in", ""), ("pois.", "")]
    glossedWords := [⟨['K', 'o', 'i', 'r', 'a'], [], [⟨['K', 'o', 'i', 'r', 'a'], [], none⟩]⟩, ⟨['v', 'i', 'e', '-', 't', '-', 'i', '-', 'i', 'n'], [], [⟨['v', 'i', 'e'], [], none⟩, ⟨['t'], [], some '-'⟩, ⟨['i'], [], some '-'⟩, ⟨['i', 'n'], [], some '-'⟩]⟩, ⟨['p', 'o', 'i', 's', '.'], [], [⟨['p', 'o', 'i', 's'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "object", none⟩]
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "other"), ("number", "singular"), ("clause", "passive")] }

def sg_book_must : Datum :=
  { id := "karlsson2017_sg_book_must"
    source := ⟨"karlsson-2017", "13.3.2 (4)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Minun täytyy ostaa kirja."
    glossedTokens := [("Minu-n", ""), ("täyty-y", ""), ("osta-a", ""), ("kirja.", "")]
    glossedWords := [⟨['M', 'i', 'n', 'u', '-', 'n'], [], [⟨['M', 'i', 'n', 'u'], [], none⟩, ⟨['n'], [], some '-'⟩]⟩, ⟨['t', 'ä', 'y', 't', 'y', '-', 'y'], [], [⟨['t', 'ä', 'y', 't', 'y'], [], none⟩, ⟨['y'], [], some '-'⟩]⟩, ⟨['o', 's', 't', 'a', '-', 'a'], [], [⟨['o', 's', 't', 'a'], [], none⟩, ⟨['a'], [], some '-'⟩]⟩, ⟨['k', 'i', 'r', 'j', 'a', '.'], [], [⟨['k', 'i', 'r', 'j', 'a'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "object", none⟩]
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "other"), ("number", "singular"), ("clause", "obligation")] }

def sg_house_inf : Datum :=
  { id := "karlsson2017_sg_house_inf"
    source := ⟨"karlsson-2017", "13.3.2 (4)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "On vaikea ostaa talo."
    glossedTokens := [("On", ""), ("vaikea", ""), ("osta-a", ""), ("talo.", "")]
    glossedWords := [⟨['O', 'n'], [], [⟨['O', 'n'], [], none⟩]⟩, ⟨['v', 'a', 'i', 'k', 'e', 'a'], [], [⟨['v', 'a', 'i', 'k', 'e', 'a'], [], none⟩]⟩, ⟨['o', 's', 't', 'a', '-', 'a'], [], [⟨['o', 's', 't', 'a'], [], none⟩, ⟨['a'], [], some '-'⟩]⟩, ⟨['t', 'a', 'l', 'o', '.'], [], [⟨['t', 'a', 'l', 'o'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "object", none⟩]
    paperFeatures := [("section", "13.3.2"), ("negated", "no"), ("aspect", "resultative"), ("quantity", "definite"), ("nominal", "other"), ("number", "singular"), ("clause", "infinitival")] }

def all : List Datum := [neg1, neg2, neg3, neg4, ex_2a_read_part, ex_2a_read_tot, ex_2a_drive_part, ex_2a_drive_tot, ex_2a_shoot_part, ex_2a_shoot_tot, ex_2b_love, ex_2b_interest, ex_2b_fear, ex_3_icecream_part, ex_3_icecream_tot, ex_3_beer_part, ex_3_beer_tot, ex_3_people_part, ex_3_people_tot, ex_3_guests_part, ex_3_guests_tot, tot_message, tot_milk, tot_car_imp, tot_computers, tot_cars, acc_took, acc_take_imp, acc_taken, acc_whom, pl_articles, pl_children_imp, pl_children_pass, num_articles, num_children_imp, num_children_pass, sg_camera, sg_child, sg_window, sg_paper_imp, sg_book_pass, sg_dog_pass, sg_book_must, sg_house_inf]

/-- Whether the action leads to an 'important' final result (section 12.2.2, rule 2a), as *Tyttö luk-i kirja-n* 'The girl read (= completed reading) a/the book' does and *Tyttö luk-i kirja-a* 'The girl was reading a/the book' does not. -/
inductive Resultativity where
  /-- resultative: resultative -/
  | resultative
  /-- irresultative: irresultative -/
  | irresultative
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `aspect`. -/
def aspect (e : Datum) : Option Resultativity :=
  e.parse? "aspect" [("resultative", .resultative), ("irresultative", .irresultative)]

/-- The quantity an object expresses (section 12.2.2, rule 3): a whole or a definite quantity, or an indefinite, non-limited quantity, as divisible and plural words express. It is not the definiteness of the object: *Osta-n jäätelö-n* 'I('ll) buy an/the ice-cream' expresses a definite quantity on either reading. -/
inductive Quantity where
  /-- definite: definite -/
  | definite
  /-- indefinite: indefinite -/
  | indefinite
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `quantity`. -/
def quantity (e : Datum) : Option Quantity :=
  e.parse? "quantity" [("definite", .definite), ("indefinite", .indefinite)]

/-- The kind of nominal serving as object, as the total-object rules of section 13.3.2 tell them apart: a personal pronoun or *kuka* 'who' (rule 1), a numeral heading its phrase (rule 3), or any other nominal, plural (rule 2) or singular (rule 4). -/
inductive Nominal where
  /-- personalPronoun: personalPronoun -/
  | personalPronoun
  /-- numeral: numeral -/
  | numeral
  /-- other: other -/
  | other
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `nominal`. -/
def nominal (e : Datum) : Option Nominal :=
  e.parse? "nominal" [("personalPronoun", .personalPronoun), ("numeral", .numeral), ("other", .other)]

/-- The clause types, the last four being those under which a singular total object is in the nominative (section 13.3.2, rule 4b). -/
inductive Clause where
  /-- finite: finite -/
  | finite
  /-- imperative: imperative -/
  | imperative
  /-- passive: passive -/
  | passive
  /-- obligation: obligation -/
  | obligation
  /-- infinitival: infinitival -/
  | infinitival
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `clause`. -/
def clause (e : Datum) : Option Clause :=
  e.parse? "clause" [("finite", .finite), ("imperative", .imperative), ("passive", .passive),
    ("obligation", .obligation), ("infinitival", .infinitival)]

/-- The labels of the spans the rows mark. -/
inductive SpanLabel where
  /-- object: the noun or pronoun heading the object, which the grammar prints in italics -/
  | object
  deriving DecidableEq, Repr, Fintype

/-- The label of a span, where it is a declared one. -/
def label? (p : Datum.Span) : Option SpanLabel :=
  List.lookup p.label [("object", .object)]

/-- The boundaries the grammar's notation marks within a word. -/
inductive Boundary where
  /-- `-`: between a stem and an inflectional ending or a clitic, or between two of these -/
  | inflection
  /-- `=`: between the words of a compound -/
  | compound
  /-- `>`: before a derivational suffix -/
  | derivation
  deriving DecidableEq, Repr, Fintype

/-- The boundary before a morpheme, by the symbol the source writes there. -/
def boundary? (m : GlossedMorpheme) : Option Boundary :=
  m.sep.bind (List.lookup · [('-', .inflection), ('=', .compound), ('>', .derivation)])

end Karlsson2017.Examples
