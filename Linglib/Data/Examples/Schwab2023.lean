module

public import Linglib.Data.Examples.Schema

/-!
# `Schwab2023` — typed example data

Auto-generated from `Linglib/Data/Examples/Schwab2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Schwab2023.Examples`.
-/

@[expose] public section

namespace Schwab2023.Examples

def ex7a_jemals : Datum :=
  { id := "schwab2023_ex7a_jemals"
    source := ⟨"schwab-2023", "(7a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Bauer, der kein Pestizid verwendete, war jemals von dem Ernteertrag begeistert."
    glossedTokens := [("Der", "the"), ("Bauer", "farmer"), ("der", "who"), ("kein", "no"), ("Pestizid", "pesticide"), ("verwendete", "used"), ("war", "was"), ("jemals", "ever"), ("von", "by"), ("dem", "the"), ("Ernteertrag", "crop_yield"), ("begeistert", "amazed")]
    glossedWords := [⟨[['D', 'e', 'r']], [['t', 'h', 'e']]⟩, ⟨[['B', 'a', 'u', 'e', 'r']], [['f', 'a', 'r', 'm', 'e', 'r']]⟩, ⟨[['d', 'e', 'r']], [['w', 'h', 'o']]⟩, ⟨[['k', 'e', 'i', 'n']], [['n', 'o']]⟩, ⟨[['P', 'e', 's', 't', 'i', 'z', 'i', 'd']], [['p', 'e', 's', 't', 'i', 'c', 'i', 'd', 'e']]⟩, ⟨[['v', 'e', 'r', 'w', 'e', 'n', 'd', 'e', 't', 'e']], [['u', 's', 'e', 'd']]⟩, ⟨[['w', 'a', 'r']], [['w', 'a', 's']]⟩, ⟨[['j', 'e', 'm', 'a', 'l', 's']], [['e', 'v', 'e', 'r']]⟩, ⟨[['v', 'o', 'n']], [['b', 'y']]⟩, ⟨[['d', 'e', 'm']], [['t', 'h', 'e']]⟩, ⟨[['E', 'r', 'n', 't', 'e', 'e', 'r', 't', 'r', 'a', 'g']], [['c', 'r', 'o', 'p', '_', 'y', 'i', 'e', 'l', 'd']]⟩, ⟨[['b', 'e', 'g', 'e', 'i', 's', 't', 'e', 'r', 't']], [['a', 'm', 'a', 'z', 'e', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("npi", "jemals"), ("npiType", "strengthening"), ("negation", "rc"), ("extraction", "subject")] }

def ex7b_jemals : Datum :=
  { id := "schwab2023_ex7b_jemals"
    source := ⟨"schwab-2023", "(7b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Kein Bauer, der das Pestizid verwendete, war jemals von dem Ernteertrag begeistert."
    glossedTokens := [("Kein", "no"), ("Bauer", "farmer"), ("der", "who"), ("das", "the"), ("Pestizid", "pesticide"), ("verwendete", "used"), ("war", "was"), ("jemals", "ever"), ("von", "by"), ("dem", "the"), ("Ernteertrag", "crop_yield"), ("begeistert", "amazed")]
    glossedWords := [⟨[['K', 'e', 'i', 'n']], [['n', 'o']]⟩, ⟨[['B', 'a', 'u', 'e', 'r']], [['f', 'a', 'r', 'm', 'e', 'r']]⟩, ⟨[['d', 'e', 'r']], [['w', 'h', 'o']]⟩, ⟨[['d', 'a', 's']], [['t', 'h', 'e']]⟩, ⟨[['P', 'e', 's', 't', 'i', 'z', 'i', 'd']], [['p', 'e', 's', 't', 'i', 'c', 'i', 'd', 'e']]⟩, ⟨[['v', 'e', 'r', 'w', 'e', 'n', 'd', 'e', 't', 'e']], [['u', 's', 'e', 'd']]⟩, ⟨[['w', 'a', 'r']], [['w', 'a', 's']]⟩, ⟨[['j', 'e', 'm', 'a', 'l', 's']], [['e', 'v', 'e', 'r']]⟩, ⟨[['v', 'o', 'n']], [['b', 'y']]⟩, ⟨[['d', 'e', 'm']], [['t', 'h', 'e']]⟩, ⟨[['E', 'r', 'n', 't', 'e', 'e', 'r', 't', 'r', 'a', 'g']], [['c', 'r', 'o', 'p', '_', 'y', 'i', 'e', 'l', 'd']]⟩, ⟨[['b', 'e', 'g', 'e', 'i', 's', 't', 'e', 'r', 't']], [['a', 'm', 'a', 'z', 'e', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("npi", "jemals"), ("npiType", "strengthening"), ("negation", "matrix"), ("extraction", "subject")] }

def ex7c_jemals : Datum :=
  { id := "schwab2023_ex7c_jemals"
    source := ⟨"schwab-2023", "(7c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Bauer, der das Pestizid verwendete, war jemals von dem Ernteertrag begeistert."
    glossedTokens := [("Der", "the"), ("Bauer", "farmer"), ("der", "who"), ("das", "the"), ("Pestizid", "pesticide"), ("verwendete", "used"), ("war", "was"), ("jemals", "ever"), ("von", "by"), ("dem", "the"), ("Ernteertrag", "crop_yield"), ("begeistert", "amazed")]
    glossedWords := [⟨[['D', 'e', 'r']], [['t', 'h', 'e']]⟩, ⟨[['B', 'a', 'u', 'e', 'r']], [['f', 'a', 'r', 'm', 'e', 'r']]⟩, ⟨[['d', 'e', 'r']], [['w', 'h', 'o']]⟩, ⟨[['d', 'a', 's']], [['t', 'h', 'e']]⟩, ⟨[['P', 'e', 's', 't', 'i', 'z', 'i', 'd']], [['p', 'e', 's', 't', 'i', 'c', 'i', 'd', 'e']]⟩, ⟨[['v', 'e', 'r', 'w', 'e', 'n', 'd', 'e', 't', 'e']], [['u', 's', 'e', 'd']]⟩, ⟨[['w', 'a', 'r']], [['w', 'a', 's']]⟩, ⟨[['j', 'e', 'm', 'a', 'l', 's']], [['e', 'v', 'e', 'r']]⟩, ⟨[['v', 'o', 'n']], [['b', 'y']]⟩, ⟨[['d', 'e', 'm']], [['t', 'h', 'e']]⟩, ⟨[['E', 'r', 'n', 't', 'e', 'e', 'r', 't', 'r', 'a', 'g']], [['c', 'r', 'o', 'p', '_', 'y', 'i', 'e', 'l', 'd']]⟩, ⟨[['b', 'e', 'g', 'e', 'i', 's', 't', 'e', 'r', 't']], [['a', 'm', 'a', 'z', 'e', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("npi", "jemals"), ("npiType", "strengthening"), ("negation", "none"), ("extraction", "subject")] }

def ex7a_sorecht : Datum :=
  { id := "schwab2023_ex7a_sorecht"
    source := ⟨"schwab-2023", "(7a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Bauer, der kein Pestizid verwendete, war so recht von dem Ernteertrag begeistert."
    glossedTokens := [("Der", "the"), ("Bauer", "farmer"), ("der", "who"), ("kein", "no"), ("Pestizid", "pesticide"), ("verwendete", "used"), ("war", "was"), ("so recht", "really"), ("von", "by"), ("dem", "the"), ("Ernteertrag", "crop_yield"), ("begeistert", "amazed")]
    glossedWords := [⟨[['D', 'e', 'r']], [['t', 'h', 'e']]⟩, ⟨[['B', 'a', 'u', 'e', 'r']], [['f', 'a', 'r', 'm', 'e', 'r']]⟩, ⟨[['d', 'e', 'r']], [['w', 'h', 'o']]⟩, ⟨[['k', 'e', 'i', 'n']], [['n', 'o']]⟩, ⟨[['P', 'e', 's', 't', 'i', 'z', 'i', 'd']], [['p', 'e', 's', 't', 'i', 'c', 'i', 'd', 'e']]⟩, ⟨[['v', 'e', 'r', 'w', 'e', 'n', 'd', 'e', 't', 'e']], [['u', 's', 'e', 'd']]⟩, ⟨[['w', 'a', 'r']], [['w', 'a', 's']]⟩, ⟨[['s', 'o', ' ', 'r', 'e', 'c', 'h', 't']], [['r', 'e', 'a', 'l', 'l', 'y']]⟩, ⟨[['v', 'o', 'n']], [['b', 'y']]⟩, ⟨[['d', 'e', 'm']], [['t', 'h', 'e']]⟩, ⟨[['E', 'r', 'n', 't', 'e', 'e', 'r', 't', 'r', 'a', 'g']], [['c', 'r', 'o', 'p', '_', 'y', 'i', 'e', 'l', 'd']]⟩, ⟨[['b', 'e', 'g', 'e', 'i', 's', 't', 'e', 'r', 't']], [['a', 'm', 'a', 'z', 'e', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("npi", "so recht"), ("npiType", "attenuating"), ("negation", "rc"), ("extraction", "subject")] }

def ex7b_sorecht : Datum :=
  { id := "schwab2023_ex7b_sorecht"
    source := ⟨"schwab-2023", "(7b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Kein Bauer, der das Pestizid verwendete, war so recht von dem Ernteertrag begeistert."
    glossedTokens := [("Kein", "no"), ("Bauer", "farmer"), ("der", "who"), ("das", "the"), ("Pestizid", "pesticide"), ("verwendete", "used"), ("war", "was"), ("so recht", "really"), ("von", "by"), ("dem", "the"), ("Ernteertrag", "crop_yield"), ("begeistert", "amazed")]
    glossedWords := [⟨[['K', 'e', 'i', 'n']], [['n', 'o']]⟩, ⟨[['B', 'a', 'u', 'e', 'r']], [['f', 'a', 'r', 'm', 'e', 'r']]⟩, ⟨[['d', 'e', 'r']], [['w', 'h', 'o']]⟩, ⟨[['d', 'a', 's']], [['t', 'h', 'e']]⟩, ⟨[['P', 'e', 's', 't', 'i', 'z', 'i', 'd']], [['p', 'e', 's', 't', 'i', 'c', 'i', 'd', 'e']]⟩, ⟨[['v', 'e', 'r', 'w', 'e', 'n', 'd', 'e', 't', 'e']], [['u', 's', 'e', 'd']]⟩, ⟨[['w', 'a', 'r']], [['w', 'a', 's']]⟩, ⟨[['s', 'o', ' ', 'r', 'e', 'c', 'h', 't']], [['r', 'e', 'a', 'l', 'l', 'y']]⟩, ⟨[['v', 'o', 'n']], [['b', 'y']]⟩, ⟨[['d', 'e', 'm']], [['t', 'h', 'e']]⟩, ⟨[['E', 'r', 'n', 't', 'e', 'e', 'r', 't', 'r', 'a', 'g']], [['c', 'r', 'o', 'p', '_', 'y', 'i', 'e', 'l', 'd']]⟩, ⟨[['b', 'e', 'g', 'e', 'i', 's', 't', 'e', 'r', 't']], [['a', 'm', 'a', 'z', 'e', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("npi", "so recht"), ("npiType", "attenuating"), ("negation", "matrix"), ("extraction", "subject")] }

def ex7c_sorecht : Datum :=
  { id := "schwab2023_ex7c_sorecht"
    source := ⟨"schwab-2023", "(7c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Bauer, der das Pestizid verwendete, war so recht von dem Ernteertrag begeistert."
    glossedTokens := [("Der", "the"), ("Bauer", "farmer"), ("der", "who"), ("das", "the"), ("Pestizid", "pesticide"), ("verwendete", "used"), ("war", "was"), ("so recht", "really"), ("von", "by"), ("dem", "the"), ("Ernteertrag", "crop_yield"), ("begeistert", "amazed")]
    glossedWords := [⟨[['D', 'e', 'r']], [['t', 'h', 'e']]⟩, ⟨[['B', 'a', 'u', 'e', 'r']], [['f', 'a', 'r', 'm', 'e', 'r']]⟩, ⟨[['d', 'e', 'r']], [['w', 'h', 'o']]⟩, ⟨[['d', 'a', 's']], [['t', 'h', 'e']]⟩, ⟨[['P', 'e', 's', 't', 'i', 'z', 'i', 'd']], [['p', 'e', 's', 't', 'i', 'c', 'i', 'd', 'e']]⟩, ⟨[['v', 'e', 'r', 'w', 'e', 'n', 'd', 'e', 't', 'e']], [['u', 's', 'e', 'd']]⟩, ⟨[['w', 'a', 'r']], [['w', 'a', 's']]⟩, ⟨[['s', 'o', ' ', 'r', 'e', 'c', 'h', 't']], [['r', 'e', 'a', 'l', 'l', 'y']]⟩, ⟨[['v', 'o', 'n']], [['b', 'y']]⟩, ⟨[['d', 'e', 'm']], [['t', 'h', 'e']]⟩, ⟨[['E', 'r', 'n', 't', 'e', 'e', 'r', 't', 'r', 'a', 'g']], [['c', 'r', 'o', 'p', '_', 'y', 'i', 'e', 'l', 'd']]⟩, ⟨[['b', 'e', 'g', 'e', 'i', 's', 't', 'e', 'r', 't']], [['a', 'm', 'a', 'z', 'e', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("npi", "so recht"), ("npiType", "attenuating"), ("negation", "none"), ("extraction", "subject")] }

def ex8a_jemals : Datum :=
  { id := "schwab2023_ex8a_jemals"
    source := ⟨"schwab-2023", "(8a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Sänger, den kein Label unterstützte, war jemals in der Musikbranche erfolgreich."
    glossedTokens := [("Der", "the"), ("Sänger", "singer"), ("den", "whom"), ("kein", "no"), ("Label", "label"), ("unterstützte", "supported"), ("war", "was"), ("jemals", "ever"), ("in", "in"), ("der", "the"), ("Musikbranche", "music_business"), ("erfolgreich", "successful")]
    glossedWords := [⟨[['D', 'e', 'r']], [['t', 'h', 'e']]⟩, ⟨[['S', 'ä', 'n', 'g', 'e', 'r']], [['s', 'i', 'n', 'g', 'e', 'r']]⟩, ⟨[['d', 'e', 'n']], [['w', 'h', 'o', 'm']]⟩, ⟨[['k', 'e', 'i', 'n']], [['n', 'o']]⟩, ⟨[['L', 'a', 'b', 'e', 'l']], [['l', 'a', 'b', 'e', 'l']]⟩, ⟨[['u', 'n', 't', 'e', 'r', 's', 't', 'ü', 't', 'z', 't', 'e']], [['s', 'u', 'p', 'p', 'o', 'r', 't', 'e', 'd']]⟩, ⟨[['w', 'a', 'r']], [['w', 'a', 's']]⟩, ⟨[['j', 'e', 'm', 'a', 'l', 's']], [['e', 'v', 'e', 'r']]⟩, ⟨[['i', 'n']], [['i', 'n']]⟩, ⟨[['d', 'e', 'r']], [['t', 'h', 'e']]⟩, ⟨[['M', 'u', 's', 'i', 'k', 'b', 'r', 'a', 'n', 'c', 'h', 'e']], [['m', 'u', 's', 'i', 'c', '_', 'b', 'u', 's', 'i', 'n', 'e', 's', 's']]⟩, ⟨[['e', 'r', 'f', 'o', 'l', 'g', 'r', 'e', 'i', 'c', 'h']], [['s', 'u', 'c', 'c', 'e', 's', 's', 'f', 'u', 'l']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("npi", "jemals"), ("npiType", "strengthening"), ("negation", "rc"), ("extraction", "object")] }

def ex8b_jemals : Datum :=
  { id := "schwab2023_ex8b_jemals"
    source := ⟨"schwab-2023", "(8b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Kein Sänger, den das Label unterstützte, war jemals in der Musikbranche erfolgreich."
    glossedTokens := [("Kein", "no"), ("Sänger", "singer"), ("den", "whom"), ("das", "the"), ("Label", "label"), ("unterstützte", "supported"), ("war", "was"), ("jemals", "ever"), ("in", "in"), ("der", "the"), ("Musikbranche", "music_business"), ("erfolgreich", "successful")]
    glossedWords := [⟨[['K', 'e', 'i', 'n']], [['n', 'o']]⟩, ⟨[['S', 'ä', 'n', 'g', 'e', 'r']], [['s', 'i', 'n', 'g', 'e', 'r']]⟩, ⟨[['d', 'e', 'n']], [['w', 'h', 'o', 'm']]⟩, ⟨[['d', 'a', 's']], [['t', 'h', 'e']]⟩, ⟨[['L', 'a', 'b', 'e', 'l']], [['l', 'a', 'b', 'e', 'l']]⟩, ⟨[['u', 'n', 't', 'e', 'r', 's', 't', 'ü', 't', 'z', 't', 'e']], [['s', 'u', 'p', 'p', 'o', 'r', 't', 'e', 'd']]⟩, ⟨[['w', 'a', 'r']], [['w', 'a', 's']]⟩, ⟨[['j', 'e', 'm', 'a', 'l', 's']], [['e', 'v', 'e', 'r']]⟩, ⟨[['i', 'n']], [['i', 'n']]⟩, ⟨[['d', 'e', 'r']], [['t', 'h', 'e']]⟩, ⟨[['M', 'u', 's', 'i', 'k', 'b', 'r', 'a', 'n', 'c', 'h', 'e']], [['m', 'u', 's', 'i', 'c', '_', 'b', 'u', 's', 'i', 'n', 'e', 's', 's']]⟩, ⟨[['e', 'r', 'f', 'o', 'l', 'g', 'r', 'e', 'i', 'c', 'h']], [['s', 'u', 'c', 'c', 'e', 's', 's', 'f', 'u', 'l']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("npi", "jemals"), ("npiType", "strengthening"), ("negation", "matrix"), ("extraction", "object")] }

def ex8c_jemals : Datum :=
  { id := "schwab2023_ex8c_jemals"
    source := ⟨"schwab-2023", "(8c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Sänger, den das Label unterstützte, war jemals in der Musikbranche erfolgreich."
    glossedTokens := [("Der", "the"), ("Sänger", "singer"), ("den", "whom"), ("das", "the"), ("Label", "label"), ("unterstützte", "supported"), ("war", "was"), ("jemals", "ever"), ("in", "in"), ("der", "the"), ("Musikbranche", "music_business"), ("erfolgreich", "successful")]
    glossedWords := [⟨[['D', 'e', 'r']], [['t', 'h', 'e']]⟩, ⟨[['S', 'ä', 'n', 'g', 'e', 'r']], [['s', 'i', 'n', 'g', 'e', 'r']]⟩, ⟨[['d', 'e', 'n']], [['w', 'h', 'o', 'm']]⟩, ⟨[['d', 'a', 's']], [['t', 'h', 'e']]⟩, ⟨[['L', 'a', 'b', 'e', 'l']], [['l', 'a', 'b', 'e', 'l']]⟩, ⟨[['u', 'n', 't', 'e', 'r', 's', 't', 'ü', 't', 'z', 't', 'e']], [['s', 'u', 'p', 'p', 'o', 'r', 't', 'e', 'd']]⟩, ⟨[['w', 'a', 'r']], [['w', 'a', 's']]⟩, ⟨[['j', 'e', 'm', 'a', 'l', 's']], [['e', 'v', 'e', 'r']]⟩, ⟨[['i', 'n']], [['i', 'n']]⟩, ⟨[['d', 'e', 'r']], [['t', 'h', 'e']]⟩, ⟨[['M', 'u', 's', 'i', 'k', 'b', 'r', 'a', 'n', 'c', 'h', 'e']], [['m', 'u', 's', 'i', 'c', '_', 'b', 'u', 's', 'i', 'n', 'e', 's', 's']]⟩, ⟨[['e', 'r', 'f', 'o', 'l', 'g', 'r', 'e', 'i', 'c', 'h']], [['s', 'u', 'c', 'c', 'e', 's', 's', 'f', 'u', 'l']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("npi", "jemals"), ("npiType", "strengthening"), ("negation", "none"), ("extraction", "object")] }

def ex8a_sorecht : Datum :=
  { id := "schwab2023_ex8a_sorecht"
    source := ⟨"schwab-2023", "(8a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Sänger, den kein Label unterstützte, war so recht in der Musikbranche erfolgreich."
    glossedTokens := [("Der", "the"), ("Sänger", "singer"), ("den", "whom"), ("kein", "no"), ("Label", "label"), ("unterstützte", "supported"), ("war", "was"), ("so recht", "really"), ("in", "in"), ("der", "the"), ("Musikbranche", "music_business"), ("erfolgreich", "successful")]
    glossedWords := [⟨[['D', 'e', 'r']], [['t', 'h', 'e']]⟩, ⟨[['S', 'ä', 'n', 'g', 'e', 'r']], [['s', 'i', 'n', 'g', 'e', 'r']]⟩, ⟨[['d', 'e', 'n']], [['w', 'h', 'o', 'm']]⟩, ⟨[['k', 'e', 'i', 'n']], [['n', 'o']]⟩, ⟨[['L', 'a', 'b', 'e', 'l']], [['l', 'a', 'b', 'e', 'l']]⟩, ⟨[['u', 'n', 't', 'e', 'r', 's', 't', 'ü', 't', 'z', 't', 'e']], [['s', 'u', 'p', 'p', 'o', 'r', 't', 'e', 'd']]⟩, ⟨[['w', 'a', 'r']], [['w', 'a', 's']]⟩, ⟨[['s', 'o', ' ', 'r', 'e', 'c', 'h', 't']], [['r', 'e', 'a', 'l', 'l', 'y']]⟩, ⟨[['i', 'n']], [['i', 'n']]⟩, ⟨[['d', 'e', 'r']], [['t', 'h', 'e']]⟩, ⟨[['M', 'u', 's', 'i', 'k', 'b', 'r', 'a', 'n', 'c', 'h', 'e']], [['m', 'u', 's', 'i', 'c', '_', 'b', 'u', 's', 'i', 'n', 'e', 's', 's']]⟩, ⟨[['e', 'r', 'f', 'o', 'l', 'g', 'r', 'e', 'i', 'c', 'h']], [['s', 'u', 'c', 'c', 'e', 's', 's', 'f', 'u', 'l']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("npi", "so recht"), ("npiType", "attenuating"), ("negation", "rc"), ("extraction", "object")] }

def ex8b_sorecht : Datum :=
  { id := "schwab2023_ex8b_sorecht"
    source := ⟨"schwab-2023", "(8b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Kein Sänger, den das Label unterstützte, war so recht in der Musikbranche erfolgreich."
    glossedTokens := [("Kein", "no"), ("Sänger", "singer"), ("den", "whom"), ("das", "the"), ("Label", "label"), ("unterstützte", "supported"), ("war", "was"), ("so recht", "really"), ("in", "in"), ("der", "the"), ("Musikbranche", "music_business"), ("erfolgreich", "successful")]
    glossedWords := [⟨[['K', 'e', 'i', 'n']], [['n', 'o']]⟩, ⟨[['S', 'ä', 'n', 'g', 'e', 'r']], [['s', 'i', 'n', 'g', 'e', 'r']]⟩, ⟨[['d', 'e', 'n']], [['w', 'h', 'o', 'm']]⟩, ⟨[['d', 'a', 's']], [['t', 'h', 'e']]⟩, ⟨[['L', 'a', 'b', 'e', 'l']], [['l', 'a', 'b', 'e', 'l']]⟩, ⟨[['u', 'n', 't', 'e', 'r', 's', 't', 'ü', 't', 'z', 't', 'e']], [['s', 'u', 'p', 'p', 'o', 'r', 't', 'e', 'd']]⟩, ⟨[['w', 'a', 'r']], [['w', 'a', 's']]⟩, ⟨[['s', 'o', ' ', 'r', 'e', 'c', 'h', 't']], [['r', 'e', 'a', 'l', 'l', 'y']]⟩, ⟨[['i', 'n']], [['i', 'n']]⟩, ⟨[['d', 'e', 'r']], [['t', 'h', 'e']]⟩, ⟨[['M', 'u', 's', 'i', 'k', 'b', 'r', 'a', 'n', 'c', 'h', 'e']], [['m', 'u', 's', 'i', 'c', '_', 'b', 'u', 's', 'i', 'n', 'e', 's', 's']]⟩, ⟨[['e', 'r', 'f', 'o', 'l', 'g', 'r', 'e', 'i', 'c', 'h']], [['s', 'u', 'c', 'c', 'e', 's', 's', 'f', 'u', 'l']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("npi", "so recht"), ("npiType", "attenuating"), ("negation", "matrix"), ("extraction", "object")] }

def ex8c_sorecht : Datum :=
  { id := "schwab2023_ex8c_sorecht"
    source := ⟨"schwab-2023", "(8c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Sänger, den das Label unterstützte, war so recht in der Musikbranche erfolgreich."
    glossedTokens := [("Der", "the"), ("Sänger", "singer"), ("den", "whom"), ("das", "the"), ("Label", "label"), ("unterstützte", "supported"), ("war", "was"), ("so recht", "really"), ("in", "in"), ("der", "the"), ("Musikbranche", "music_business"), ("erfolgreich", "successful")]
    glossedWords := [⟨[['D', 'e', 'r']], [['t', 'h', 'e']]⟩, ⟨[['S', 'ä', 'n', 'g', 'e', 'r']], [['s', 'i', 'n', 'g', 'e', 'r']]⟩, ⟨[['d', 'e', 'n']], [['w', 'h', 'o', 'm']]⟩, ⟨[['d', 'a', 's']], [['t', 'h', 'e']]⟩, ⟨[['L', 'a', 'b', 'e', 'l']], [['l', 'a', 'b', 'e', 'l']]⟩, ⟨[['u', 'n', 't', 'e', 'r', 's', 't', 'ü', 't', 'z', 't', 'e']], [['s', 'u', 'p', 'p', 'o', 'r', 't', 'e', 'd']]⟩, ⟨[['w', 'a', 'r']], [['w', 'a', 's']]⟩, ⟨[['s', 'o', ' ', 'r', 'e', 'c', 'h', 't']], [['r', 'e', 'a', 'l', 'l', 'y']]⟩, ⟨[['i', 'n']], [['i', 'n']]⟩, ⟨[['d', 'e', 'r']], [['t', 'h', 'e']]⟩, ⟨[['M', 'u', 's', 'i', 'k', 'b', 'r', 'a', 'n', 'c', 'h', 'e']], [['m', 'u', 's', 'i', 'c', '_', 'b', 'u', 's', 'i', 'n', 'e', 's', 's']]⟩, ⟨[['e', 'r', 'f', 'o', 'l', 'g', 'r', 'e', 'i', 'c', 'h']], [['s', 'u', 'c', 'c', 'e', 's', 's', 'f', 'u', 'l']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("npi", "so recht"), ("npiType", "attenuating"), ("negation", "none"), ("extraction", "object")] }

def all : List Datum := [ex7a_jemals, ex7b_jemals, ex7c_jemals, ex7a_sorecht, ex7b_sorecht, ex7c_sorecht, ex8a_jemals, ex8b_jemals, ex8c_jemals, ex8a_sorecht, ex8b_sorecht, ex8c_sorecht]

end Schwab2023.Examples
