module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `ElliottNicolaeSauerland2022` — typed example data

Auto-generated from `Linglib/Data/Examples/ElliottNicolaeSauerland2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ElliottNicolaeSauerland2022.Examples`.
-/

@[expose] public section

namespace ElliottNicolaeSauerland2022.Examples

def ex_2 : Datum :=
  { id := "elliottnicolaesauerland2022_2"
    source := ⟨"elliott-nicolae-sauerland-2022", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which employee left early?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("singular answer", .acceptable), ("plural answer", .unacceptable)]
    paperFeatures := [("type", "SCI")] }

def ex_3 : Datum :=
  { id := "elliottnicolaesauerland2022_3"
    source := ⟨"elliott-nicolae-sauerland-2022", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which employees left early?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("singular answer", .unacceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "PCI")] }

def ex_11 : Datum :=
  { id := "elliottnicolaesauerland2022_11"
    source := ⟨"elliott-nicolae-sauerland-2022", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who is leaving early?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Who are leaving early?", .ungrammatical)]
    readings := [("singular answer", .acceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "BI")] }

def ex_12 : Datum :=
  { id := "elliottnicolaesauerland2022_12"
    source := ⟨"elliott-nicolae-sauerland-2022", "(12)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Pjos andras efige noris?"
    glossedTokens := [("Pjos", "who.SG"), ("andras", "man.SG"), ("efige", "left"), ("noris", "early")]
    glossedWords := [⟨['P', 'j', 'o', 's'], ['w', 'h', 'o', '.', 'S', 'G'], [⟨['P', 'j', 'o', 's'], ['w', 'h', 'o', '.', 'S', 'G'], none⟩]⟩, ⟨['a', 'n', 'd', 'r', 'a', 's'], ['m', 'a', 'n', '.', 'S', 'G'], [⟨['a', 'n', 'd', 'r', 'a', 's'], ['m', 'a', 'n', '.', 'S', 'G'], none⟩]⟩, ⟨['e', 'f', 'i', 'g', 'e'], ['l', 'e', 'f', 't'], [⟨['e', 'f', 'i', 'g', 'e'], ['l', 'e', 'f', 't'], none⟩]⟩, ⟨['n', 'o', 'r', 'i', 's'], ['e', 'a', 'r', 'l', 'y'], [⟨['n', 'o', 'r', 'i', 's'], ['e', 'a', 'r', 'l', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("singular answer", .acceptable), ("plural answer", .unacceptable)]
    paperFeatures := [("type", "SCI")] }

def ex_13 : Datum :=
  { id := "elliottnicolaesauerland2022_13"
    source := ⟨"elliott-nicolae-sauerland-2022", "(13)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Melyik fiú ment el?"
    glossedTokens := [("Melyik", "which"), ("fiú", "boy.SG"), ("ment", "goes"), ("el", "away")]
    glossedWords := [⟨['M', 'e', 'l', 'y', 'i', 'k'], ['w', 'h', 'i', 'c', 'h'], [⟨['M', 'e', 'l', 'y', 'i', 'k'], ['w', 'h', 'i', 'c', 'h'], none⟩]⟩, ⟨['f', 'i', 'ú'], ['b', 'o', 'y', '.', 'S', 'G'], [⟨['f', 'i', 'ú'], ['b', 'o', 'y', '.', 'S', 'G'], none⟩]⟩, ⟨['m', 'e', 'n', 't'], ['g', 'o', 'e', 's'], [⟨['m', 'e', 'n', 't'], ['g', 'o', 'e', 's'], none⟩]⟩, ⟨['e', 'l'], ['a', 'w', 'a', 'y'], [⟨['e', 'l'], ['a', 'w', 'a', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("singular answer", .acceptable), ("plural answer", .unacceptable)]
    paperFeatures := [("type", "SCI")] }

def ex_14 : Datum :=
  { id := "elliottnicolaesauerland2022_14"
    source := ⟨"elliott-nicolae-sauerland-2022", "(14)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Qué chico se fue pronto?"
    glossedTokens := [("Qué", "which"), ("chico", "boy.SG"), ("se", "REFL"), ("fue", "left"), ("pronto", "early")]
    glossedWords := [⟨['Q', 'u', 'é'], ['w', 'h', 'i', 'c', 'h'], [⟨['Q', 'u', 'é'], ['w', 'h', 'i', 'c', 'h'], none⟩]⟩, ⟨['c', 'h', 'i', 'c', 'o'], ['b', 'o', 'y', '.', 'S', 'G'], [⟨['c', 'h', 'i', 'c', 'o'], ['b', 'o', 'y', '.', 'S', 'G'], none⟩]⟩, ⟨['s', 'e'], ['R', 'E', 'F', 'L'], [⟨['s', 'e'], ['R', 'E', 'F', 'L'], none⟩]⟩, ⟨['f', 'u', 'e'], ['l', 'e', 'f', 't'], [⟨['f', 'u', 'e'], ['l', 'e', 'f', 't'], none⟩]⟩, ⟨['p', 'r', 'o', 'n', 't', 'o'], ['e', 'a', 'r', 'l', 'y'], [⟨['p', 'r', 'o', 'n', 't', 'o'], ['e', 'a', 'r', 'l', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("singular answer", .acceptable), ("plural answer", .unacceptable)]
    paperFeatures := [("type", "SCI")] }

def ex_15 : Datum :=
  { id := "elliottnicolaesauerland2022_15"
    source := ⟨"elliott-nicolae-sauerland-2022", "(15)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Pji andres efigan noris?"
    glossedTokens := [("Pji", "who.PL"), ("andres", "man.PL"), ("efigan", "left"), ("noris", "early")]
    glossedWords := [⟨['P', 'j', 'i'], ['w', 'h', 'o', '.', 'P', 'L'], [⟨['P', 'j', 'i'], ['w', 'h', 'o', '.', 'P', 'L'], none⟩]⟩, ⟨['a', 'n', 'd', 'r', 'e', 's'], ['m', 'a', 'n', '.', 'P', 'L'], [⟨['a', 'n', 'd', 'r', 'e', 's'], ['m', 'a', 'n', '.', 'P', 'L'], none⟩]⟩, ⟨['e', 'f', 'i', 'g', 'a', 'n'], ['l', 'e', 'f', 't'], [⟨['e', 'f', 'i', 'g', 'a', 'n'], ['l', 'e', 'f', 't'], none⟩]⟩, ⟨['n', 'o', 'r', 'i', 's'], ['e', 'a', 'r', 'l', 'y'], [⟨['n', 'o', 'r', 'i', 's'], ['e', 'a', 'r', 'l', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("singular answer", .unacceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "PCI")] }

def ex_16 : Datum :=
  { id := "elliottnicolaesauerland2022_16"
    source := ⟨"elliott-nicolae-sauerland-2022", "(16)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Melyik fiúk mentek el?"
    glossedTokens := [("Melyik", "which"), ("fiúk", "boy.PL"), ("mentek", "went"), ("el", "away")]
    glossedWords := [⟨['M', 'e', 'l', 'y', 'i', 'k'], ['w', 'h', 'i', 'c', 'h'], [⟨['M', 'e', 'l', 'y', 'i', 'k'], ['w', 'h', 'i', 'c', 'h'], none⟩]⟩, ⟨['f', 'i', 'ú', 'k'], ['b', 'o', 'y', '.', 'P', 'L'], [⟨['f', 'i', 'ú', 'k'], ['b', 'o', 'y', '.', 'P', 'L'], none⟩]⟩, ⟨['m', 'e', 'n', 't', 'e', 'k'], ['w', 'e', 'n', 't'], [⟨['m', 'e', 'n', 't', 'e', 'k'], ['w', 'e', 'n', 't'], none⟩]⟩, ⟨['e', 'l'], ['a', 'w', 'a', 'y'], [⟨['e', 'l'], ['a', 'w', 'a', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("singular answer", .unacceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "PCI")] }

def ex_17 : Datum :=
  { id := "elliottnicolaesauerland2022_17"
    source := ⟨"elliott-nicolae-sauerland-2022", "(17)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Qué chicos se fueron pronto?"
    glossedTokens := [("Qué", "which"), ("chicos", "boy.PL"), ("se", "REFL"), ("fueron", "left"), ("pronto", "early")]
    glossedWords := [⟨['Q', 'u', 'é'], ['w', 'h', 'i', 'c', 'h'], [⟨['Q', 'u', 'é'], ['w', 'h', 'i', 'c', 'h'], none⟩]⟩, ⟨['c', 'h', 'i', 'c', 'o', 's'], ['b', 'o', 'y', '.', 'P', 'L'], [⟨['c', 'h', 'i', 'c', 'o', 's'], ['b', 'o', 'y', '.', 'P', 'L'], none⟩]⟩, ⟨['s', 'e'], ['R', 'E', 'F', 'L'], [⟨['s', 'e'], ['R', 'E', 'F', 'L'], none⟩]⟩, ⟨['f', 'u', 'e', 'r', 'o', 'n'], ['l', 'e', 'f', 't'], [⟨['f', 'u', 'e', 'r', 'o', 'n'], ['l', 'e', 'f', 't'], none⟩]⟩, ⟨['p', 'r', 'o', 'n', 't', 'o'], ['e', 'a', 'r', 'l', 'y'], [⟨['p', 'r', 'o', 'n', 't', 'o'], ['e', 'a', 'r', 'l', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("singular answer", .unacceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "PCI")] }

def ex_18 : Datum :=
  { id := "elliottnicolaesauerland2022_18"
    source := ⟨"elliott-nicolae-sauerland-2022", "(18)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Pjos efige noris?"
    glossedTokens := [("Pjos", "who.SG"), ("efige", "left"), ("noris", "early")]
    glossedWords := [⟨['P', 'j', 'o', 's'], ['w', 'h', 'o', '.', 'S', 'G'], [⟨['P', 'j', 'o', 's'], ['w', 'h', 'o', '.', 'S', 'G'], none⟩]⟩, ⟨['e', 'f', 'i', 'g', 'e'], ['l', 'e', 'f', 't'], [⟨['e', 'f', 'i', 'g', 'e'], ['l', 'e', 'f', 't'], none⟩]⟩, ⟨['n', 'o', 'r', 'i', 's'], ['e', 'a', 'r', 'l', 'y'], [⟨['n', 'o', 'r', 'i', 's'], ['e', 'a', 'r', 'l', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("singular answer", .acceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "SBI")] }

def ex_19 : Datum :=
  { id := "elliottnicolaesauerland2022_19"
    source := ⟨"elliott-nicolae-sauerland-2022", "(19)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Ki énekel?"
    glossedTokens := [("Ki", "who.SG"), ("énekel", "sings")]
    glossedWords := [⟨['K', 'i'], ['w', 'h', 'o', '.', 'S', 'G'], [⟨['K', 'i'], ['w', 'h', 'o', '.', 'S', 'G'], none⟩]⟩, ⟨['é', 'n', 'e', 'k', 'e', 'l'], ['s', 'i', 'n', 'g', 's'], [⟨['é', 'n', 'e', 'k', 'e', 'l'], ['s', 'i', 'n', 'g', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("singular answer", .acceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "SBI")] }

def ex_20 : Datum :=
  { id := "elliottnicolaesauerland2022_20"
    source := ⟨"elliott-nicolae-sauerland-2022", "(20)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Quién se fue pronto?"
    glossedTokens := [("Quién", "who.SG"), ("se", "REFL"), ("fue", "left"), ("pronto", "early")]
    glossedWords := [⟨['Q', 'u', 'i', 'é', 'n'], ['w', 'h', 'o', '.', 'S', 'G'], [⟨['Q', 'u', 'i', 'é', 'n'], ['w', 'h', 'o', '.', 'S', 'G'], none⟩]⟩, ⟨['s', 'e'], ['R', 'E', 'F', 'L'], [⟨['s', 'e'], ['R', 'E', 'F', 'L'], none⟩]⟩, ⟨['f', 'u', 'e'], ['l', 'e', 'f', 't'], [⟨['f', 'u', 'e'], ['l', 'e', 'f', 't'], none⟩]⟩, ⟨['p', 'r', 'o', 'n', 't', 'o'], ['e', 'a', 'r', 'l', 'y'], [⟨['p', 'r', 'o', 'n', 't', 'o'], ['e', 'a', 'r', 'l', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("singular answer", .acceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "SBI")] }

def ex_21 : Datum :=
  { id := "elliottnicolaesauerland2022_21"
    source := ⟨"elliott-nicolae-sauerland-2022", "(21)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Pji efigan noris?"
    glossedTokens := [("Pji", "who.PL"), ("efigan", "left"), ("noris", "early")]
    glossedWords := [⟨['P', 'j', 'i'], ['w', 'h', 'o', '.', 'P', 'L'], [⟨['P', 'j', 'i'], ['w', 'h', 'o', '.', 'P', 'L'], none⟩]⟩, ⟨['e', 'f', 'i', 'g', 'a', 'n'], ['l', 'e', 'f', 't'], [⟨['e', 'f', 'i', 'g', 'a', 'n'], ['l', 'e', 'f', 't'], none⟩]⟩, ⟨['n', 'o', 'r', 'i', 's'], ['e', 'a', 'r', 'l', 'y'], [⟨['n', 'o', 'r', 'i', 's'], ['e', 'a', 'r', 'l', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("singular answer", .unacceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "PBI")] }

def ex_22 : Datum :=
  { id := "elliottnicolaesauerland2022_22"
    source := ⟨"elliott-nicolae-sauerland-2022", "(22)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Kik énekelnek?"
    glossedTokens := [("Kik", "who.PL"), ("énekelnek", "sing")]
    glossedWords := [⟨['K', 'i', 'k'], ['w', 'h', 'o', '.', 'P', 'L'], [⟨['K', 'i', 'k'], ['w', 'h', 'o', '.', 'P', 'L'], none⟩]⟩, ⟨['é', 'n', 'e', 'k', 'e', 'l', 'n', 'e', 'k'], ['s', 'i', 'n', 'g'], [⟨['é', 'n', 'e', 'k', 'e', 'l', 'n', 'e', 'k'], ['s', 'i', 'n', 'g'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("singular answer", .unacceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "PBI")] }

def ex_23 : Datum :=
  { id := "elliottnicolaesauerland2022_23"
    source := ⟨"elliott-nicolae-sauerland-2022", "(23)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Quiénes se fueron pronto?"
    glossedTokens := [("Quiénes", "who.PL"), ("se", "REFL"), ("fueron", "left"), ("pronto", "early")]
    glossedWords := [⟨['Q', 'u', 'i', 'é', 'n', 'e', 's'], ['w', 'h', 'o', '.', 'P', 'L'], [⟨['Q', 'u', 'i', 'é', 'n', 'e', 's'], ['w', 'h', 'o', '.', 'P', 'L'], none⟩]⟩, ⟨['s', 'e'], ['R', 'E', 'F', 'L'], [⟨['s', 'e'], ['R', 'E', 'F', 'L'], none⟩]⟩, ⟨['f', 'u', 'e', 'r', 'o', 'n'], ['l', 'e', 'f', 't'], [⟨['f', 'u', 'e', 'r', 'o', 'n'], ['l', 'e', 'f', 't'], none⟩]⟩, ⟨['p', 'r', 'o', 'n', 't', 'o'], ['e', 'a', 'r', 'l', 'y'], [⟨['p', 'r', 'o', 'n', 't', 'o'], ['e', 'a', 'r', 'l', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("singular answer", .unacceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "PBI")] }

def ex_24a : Datum :=
  { id := "elliottnicolaesauerland2022_24a"
    source := ⟨"elliott-nicolae-sauerland-2022", "(24a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "pero no me acuerdo quién"
    glossedTokens := [("pero", "but"), ("no", "not"), ("me", "REFL"), ("acuerdo", "remember"), ("quién", "who.SG")]
    glossedWords := [⟨['p', 'e', 'r', 'o'], ['b', 'u', 't'], [⟨['p', 'e', 'r', 'o'], ['b', 'u', 't'], none⟩]⟩, ⟨['n', 'o'], ['n', 'o', 't'], [⟨['n', 'o'], ['n', 'o', 't'], none⟩]⟩, ⟨['m', 'e'], ['R', 'E', 'F', 'L'], [⟨['m', 'e'], ['R', 'E', 'F', 'L'], none⟩]⟩, ⟨['a', 'c', 'u', 'e', 'r', 'd', 'o'], ['r', 'e', 'm', 'e', 'm', 'b', 'e', 'r'], [⟨['a', 'c', 'u', 'e', 'r', 'd', 'o'], ['r', 'e', 'm', 'e', 'm', 'b', 'e', 'r'], none⟩]⟩, ⟨['q', 'u', 'i', 'é', 'n'], ['w', 'h', 'o', '.', 'S', 'G'], [⟨['q', 'u', 'i', 'é', 'n'], ['w', 'h', 'o', '.', 'S', 'G'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "One of my friends called"
    judgment := .acceptable
    contrasts := [("pero no me acuerdo quiénes", .unacceptable)]
    readings := []
    paperFeatures := [("context", "exactlyOne"), ("form", "quien"), ("rival", "quienes")] }

def ex_24b : Datum :=
  { id := "elliottnicolaesauerland2022_24b"
    source := ⟨"elliott-nicolae-sauerland-2022", "(24b)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "pero no me acuerdo quién"
    glossedTokens := [("pero", "but"), ("no", "not"), ("me", "REFL"), ("acuerdo", "remember"), ("quién", "who.SG")]
    glossedWords := [⟨['p', 'e', 'r', 'o'], ['b', 'u', 't'], [⟨['p', 'e', 'r', 'o'], ['b', 'u', 't'], none⟩]⟩, ⟨['n', 'o'], ['n', 'o', 't'], [⟨['n', 'o'], ['n', 'o', 't'], none⟩]⟩, ⟨['m', 'e'], ['R', 'E', 'F', 'L'], [⟨['m', 'e'], ['R', 'E', 'F', 'L'], none⟩]⟩, ⟨['a', 'c', 'u', 'e', 'r', 'd', 'o'], ['r', 'e', 'm', 'e', 'm', 'b', 'e', 'r'], [⟨['a', 'c', 'u', 'e', 'r', 'd', 'o'], ['r', 'e', 'm', 'e', 'm', 'b', 'e', 'r'], none⟩]⟩, ⟨['q', 'u', 'i', 'é', 'n'], ['w', 'h', 'o', '.', 'S', 'G'], [⟨['q', 'u', 'i', 'é', 'n'], ['w', 'h', 'o', '.', 'S', 'G'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "At least one person called"
    judgment := .acceptable
    contrasts := [("pero no me acuerdo quiénes", .unacceptable)]
    readings := []
    paperFeatures := [("context", "atLeastOne"), ("form", "quien"), ("rival", "quienes")] }

def ex_24c : Datum :=
  { id := "elliottnicolaesauerland2022_24c"
    source := ⟨"elliott-nicolae-sauerland-2022", "(24c)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "pero no me acuerdo quiénes"
    glossedTokens := [("pero", "but"), ("no", "not"), ("me", "REFL"), ("acuerdo", "remember"), ("quiénes", "who.PL")]
    glossedWords := [⟨['p', 'e', 'r', 'o'], ['b', 'u', 't'], [⟨['p', 'e', 'r', 'o'], ['b', 'u', 't'], none⟩]⟩, ⟨['n', 'o'], ['n', 'o', 't'], [⟨['n', 'o'], ['n', 'o', 't'], none⟩]⟩, ⟨['m', 'e'], ['R', 'E', 'F', 'L'], [⟨['m', 'e'], ['R', 'E', 'F', 'L'], none⟩]⟩, ⟨['a', 'c', 'u', 'e', 'r', 'd', 'o'], ['r', 'e', 'm', 'e', 'm', 'b', 'e', 'r'], [⟨['a', 'c', 'u', 'e', 'r', 'd', 'o'], ['r', 'e', 'm', 'e', 'm', 'b', 'e', 'r'], none⟩]⟩, ⟨['q', 'u', 'i', 'é', 'n', 'e', 's'], ['w', 'h', 'o', '.', 'P', 'L'], [⟨['q', 'u', 'i', 'é', 'n', 'e', 's'], ['w', 'h', 'o', '.', 'P', 'L'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Several friends called"
    judgment := .acceptable
    contrasts := [("pero no me acuerdo quién", .questionable)]
    readings := []
    paperFeatures := [("context", "several"), ("antecedent", "plural"), ("form", "quienes"), ("rival", "quien")] }

def ex_25 : Datum :=
  { id := "elliottnicolaesauerland2022_25"
    source := ⟨"elliott-nicolae-sauerland-2022", "(25)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Juan no sabe qué amigos van a venir a la fiesta"
    glossedTokens := [("Juan", "Juan"), ("no", "not"), ("sabe", "know"), ("qué", "which"), ("amigos", "friends"), ("van", "will"), ("a", "a"), ("venir", "come"), ("a", "to"), ("la", "the"), ("fiesta", "party")]
    glossedWords := [⟨['J', 'u', 'a', 'n'], ['J', 'u', 'a', 'n'], [⟨['J', 'u', 'a', 'n'], ['J', 'u', 'a', 'n'], none⟩]⟩, ⟨['n', 'o'], ['n', 'o', 't'], [⟨['n', 'o'], ['n', 'o', 't'], none⟩]⟩, ⟨['s', 'a', 'b', 'e'], ['k', 'n', 'o', 'w'], [⟨['s', 'a', 'b', 'e'], ['k', 'n', 'o', 'w'], none⟩]⟩, ⟨['q', 'u', 'é'], ['w', 'h', 'i', 'c', 'h'], [⟨['q', 'u', 'é'], ['w', 'h', 'i', 'c', 'h'], none⟩]⟩, ⟨['a', 'm', 'i', 'g', 'o', 's'], ['f', 'r', 'i', 'e', 'n', 'd', 's'], [⟨['a', 'm', 'i', 'g', 'o', 's'], ['f', 'r', 'i', 'e', 'n', 'd', 's'], none⟩]⟩, ⟨['v', 'a', 'n'], ['w', 'i', 'l', 'l'], [⟨['v', 'a', 'n'], ['w', 'i', 'l', 'l'], none⟩]⟩, ⟨['a'], ['a'], [⟨['a'], ['a'], none⟩]⟩, ⟨['v', 'e', 'n', 'i', 'r'], ['c', 'o', 'm', 'e'], [⟨['v', 'e', 'n', 'i', 'r'], ['c', 'o', 'm', 'e'], none⟩]⟩, ⟨['a'], ['t', 'o'], [⟨['a'], ['t', 'o'], none⟩]⟩, ⟨['l', 'a'], ['t', 'h', 'e'], [⟨['l', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['f', 'i', 'e', 's', 't', 'a'], ['p', 'a', 'r', 't', 'y'], [⟨['f', 'i', 'e', 's', 't', 'a'], ['p', 'a', 'r', 't', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Juan is expecting at least one friend to come to the party."
    judgment := .acceptable
    contrasts := [("Juan no sabe quiénes van a venir a la fiesta", .unacceptable)]
    readings := []
    paperFeatures := [("context", "atLeastOne"), ("form", "quePl"), ("rival", "quienes")] }

def ex_57 : Datum :=
  { id := "elliottnicolaesauerland2022_57"
    source := ⟨"maldonado-2020", "n. 16 (i)"⟩
    reportedIn := some ⟨"elliott-nicolae-sauerland-2022", "(57)"⟩
    language := "stan1288"
    primaryText := "¿Quién hay en la fiesta?"
    glossedTokens := [("Quién", "who.SG"), ("hay", "was"), ("en", "at"), ("la", "the"), ("fiesta", "party")]
    glossedWords := [⟨['Q', 'u', 'i', 'é', 'n'], ['w', 'h', 'o', '.', 'S', 'G'], [⟨['Q', 'u', 'i', 'é', 'n'], ['w', 'h', 'o', '.', 'S', 'G'], none⟩]⟩, ⟨['h', 'a', 'y'], ['w', 'a', 's'], [⟨['h', 'a', 'y'], ['w', 'a', 's'], none⟩]⟩, ⟨['e', 'n'], ['a', 't'], [⟨['e', 'n'], ['a', 't'], none⟩]⟩, ⟨['l', 'a'], ['t', 'h', 'e'], [⟨['l', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['f', 'i', 'e', 's', 't', 'a'], ['p', 'a', 'r', 't', 'y'], [⟨['f', 'i', 'e', 's', 't', 'a'], ['p', 'a', 'r', 't', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "A context that does not satisfy existence."
    judgment := .acceptable
    contrasts := [("¿Quiénes hay en la fiesta?", .unacceptable)]
    readings := []
    paperFeatures := [("context", "noExistence"), ("form", "quien"), ("rival", "quienes")] }

def ex_59 : Datum :=
  { id := "elliottnicolaesauerland2022_59"
    source := ⟨"maldonado-2020", "(15b)"⟩
    reportedIn := some ⟨"elliott-nicolae-sauerland-2022", "(59)"⟩
    language := "stan1288"
    primaryText := "Juan no sabe quiénes van a venir a la fiesta"
    glossedTokens := [("Juan", "Juan"), ("no", "not"), ("sabe", "know"), ("quiénes", "who.PL"), ("van", "will"), ("a", "a"), ("venir", "come"), ("a", "to"), ("la", "the"), ("fiesta", "party")]
    glossedWords := [⟨['J', 'u', 'a', 'n'], ['J', 'u', 'a', 'n'], [⟨['J', 'u', 'a', 'n'], ['J', 'u', 'a', 'n'], none⟩]⟩, ⟨['n', 'o'], ['n', 'o', 't'], [⟨['n', 'o'], ['n', 'o', 't'], none⟩]⟩, ⟨['s', 'a', 'b', 'e'], ['k', 'n', 'o', 'w'], [⟨['s', 'a', 'b', 'e'], ['k', 'n', 'o', 'w'], none⟩]⟩, ⟨['q', 'u', 'i', 'é', 'n', 'e', 's'], ['w', 'h', 'o', '.', 'P', 'L'], [⟨['q', 'u', 'i', 'é', 'n', 'e', 's'], ['w', 'h', 'o', '.', 'P', 'L'], none⟩]⟩, ⟨['v', 'a', 'n'], ['w', 'i', 'l', 'l'], [⟨['v', 'a', 'n'], ['w', 'i', 'l', 'l'], none⟩]⟩, ⟨['a'], ['a'], [⟨['a'], ['a'], none⟩]⟩, ⟨['v', 'e', 'n', 'i', 'r'], ['c', 'o', 'm', 'e'], [⟨['v', 'e', 'n', 'i', 'r'], ['c', 'o', 'm', 'e'], none⟩]⟩, ⟨['a'], ['t', 'o'], [⟨['a'], ['t', 'o'], none⟩]⟩, ⟨['l', 'a'], ['t', 'h', 'e'], [⟨['l', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['f', 'i', 'e', 's', 't', 'a'], ['p', 'a', 'r', 't', 'y'], [⟨['f', 'i', 'e', 's', 't', 'a'], ['p', 'a', 'r', 't', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Juan is expecting at least one of his friends to come with him to the party."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "atLeastOne"), ("form", "quienes")] }

def ex_66 : Datum :=
  { id := "elliottnicolaesauerland2022_66"
    source := ⟨"elliott-nicolae-sauerland-2022", "(66)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Juan no sabe qué amigos van a venir"
    glossedTokens := [("Juan", "Juan"), ("no", "not"), ("sabe", "know"), ("qué", "which"), ("amigos", "friend.PL"), ("van", "go"), ("a", "PREP"), ("venir", "come")]
    glossedWords := [⟨['J', 'u', 'a', 'n'], ['J', 'u', 'a', 'n'], [⟨['J', 'u', 'a', 'n'], ['J', 'u', 'a', 'n'], none⟩]⟩, ⟨['n', 'o'], ['n', 'o', 't'], [⟨['n', 'o'], ['n', 'o', 't'], none⟩]⟩, ⟨['s', 'a', 'b', 'e'], ['k', 'n', 'o', 'w'], [⟨['s', 'a', 'b', 'e'], ['k', 'n', 'o', 'w'], none⟩]⟩, ⟨['q', 'u', 'é'], ['w', 'h', 'i', 'c', 'h'], [⟨['q', 'u', 'é'], ['w', 'h', 'i', 'c', 'h'], none⟩]⟩, ⟨['a', 'm', 'i', 'g', 'o', 's'], ['f', 'r', 'i', 'e', 'n', 'd', '.', 'P', 'L'], [⟨['a', 'm', 'i', 'g', 'o', 's'], ['f', 'r', 'i', 'e', 'n', 'd', '.', 'P', 'L'], none⟩]⟩, ⟨['v', 'a', 'n'], ['g', 'o'], [⟨['v', 'a', 'n'], ['g', 'o'], none⟩]⟩, ⟨['a'], ['P', 'R', 'E', 'P'], [⟨['a'], ['P', 'R', 'E', 'P'], none⟩]⟩, ⟨['v', 'e', 'n', 'i', 'r'], ['c', 'o', 'm', 'e'], [⟨['v', 'e', 'n', 'i', 'r'], ['c', 'o', 'm', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Juan is expecting at least one friend to come to the party, but two or more might come."
    judgment := .acceptable
    contrasts := [("Juan no sabe qué amigo van a venir", .unacceptable)]
    readings := []
    paperFeatures := [("context", "atLeastOne"), ("form", "quePl"), ("rival", "queSg")] }

def ex_68 : Datum :=
  { id := "elliottnicolaesauerland2022_68"
    source := ⟨"maldonado-2020", "(18a)"⟩
    reportedIn := some ⟨"elliott-nicolae-sauerland-2022", "(68)"⟩
    language := "stan1288"
    primaryText := "¿Quién está ahí?"
    glossedTokens := [("Quién", "who.SG"), ("está", "is"), ("ahí", "there")]
    glossedWords := [⟨['Q', 'u', 'i', 'é', 'n'], ['w', 'h', 'o', '.', 'S', 'G'], [⟨['Q', 'u', 'i', 'é', 'n'], ['w', 'h', 'o', '.', 'S', 'G'], none⟩]⟩, ⟨['e', 's', 't', 'á'], ['i', 's'], [⟨['e', 's', 't', 'á'], ['i', 's'], none⟩]⟩, ⟨['a', 'h', 'í'], ['t', 'h', 'e', 'r', 'e'], [⟨['a', 'h', 'í'], ['t', 'h', 'e', 'r', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Mary and John arrive at their apartment, where there is supposed to be no one. They hear two people whispering inside. Mary asks:"
    judgment := .acceptable
    contrasts := [("¿Quiénes está ahí?", .unacceptable)]
    readings := []
    paperFeatures := [("context", "twoWhispering"), ("form", "quien"), ("rival", "quienes")] }

def n19i : Datum :=
  { id := "elliottnicolaesauerland2022_n19i"
    source := ⟨"elliott-nicolae-sauerland-2022", "n. 19 (i)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1288"
    primaryText := "¿Quién entró en la habitación?"
    glossedTokens := [("Quién", "who.SG"), ("entró", "entered.SG"), ("en", "in"), ("la", "the"), ("habitación", "room")]
    glossedWords := [⟨['Q', 'u', 'i', 'é', 'n'], ['w', 'h', 'o', '.', 'S', 'G'], [⟨['Q', 'u', 'i', 'é', 'n'], ['w', 'h', 'o', '.', 'S', 'G'], none⟩]⟩, ⟨['e', 'n', 't', 'r', 'ó'], ['e', 'n', 't', 'e', 'r', 'e', 'd', '.', 'S', 'G'], [⟨['e', 'n', 't', 'r', 'ó'], ['e', 'n', 't', 'e', 'r', 'e', 'd', '.', 'S', 'G'], none⟩]⟩, ⟨['e', 'n'], ['i', 'n'], [⟨['e', 'n'], ['i', 'n'], none⟩]⟩, ⟨['l', 'a'], ['t', 'h', 'e'], [⟨['l', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['h', 'a', 'b', 'i', 't', 'a', 'c', 'i', 'ó', 'n'], ['r', 'o', 'o', 'm'], [⟨['h', 'a', 'b', 'i', 't', 'a', 'c', 'i', 'ó', 'n'], ['r', 'o', 'o', 'm'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "The speaker isn't certain if anyone entered the room, but if someone did, it was at least two people."
    judgment := .acceptable
    contrasts := [("¿Quénes entraron en la habitación?", .unacceptable)]
    readings := []
    paperFeatures := [("context", "zeroOrSeveral"), ("form", "quien"), ("rival", "quienes")] }

def ex_76 : Datum :=
  { id := "elliottnicolaesauerland2022_76"
    source := ⟨"elliott-nicolae-sauerland-2022", "(76)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Quiénes formaron un grupo?"
    glossedTokens := [("Quiénes", "who.PL"), ("formaron", "formed"), ("un", "a"), ("grupo", "group")]
    glossedWords := [⟨['Q', 'u', 'i', 'é', 'n', 'e', 's'], ['w', 'h', 'o', '.', 'P', 'L'], [⟨['Q', 'u', 'i', 'é', 'n', 'e', 's'], ['w', 'h', 'o', '.', 'P', 'L'], none⟩]⟩, ⟨['f', 'o', 'r', 'm', 'a', 'r', 'o', 'n'], ['f', 'o', 'r', 'm', 'e', 'd'], [⟨['f', 'o', 'r', 'm', 'a', 'r', 'o', 'n'], ['f', 'o', 'r', 'm', 'e', 'd'], none⟩]⟩, ⟨['u', 'n'], ['a'], [⟨['u', 'n'], ['a'], none⟩]⟩, ⟨['g', 'r', 'u', 'p', 'o'], ['g', 'r', 'o', 'u', 'p'], [⟨['g', 'r', 'u', 'p', 'o'], ['g', 'r', 'o', 'u', 'p'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("two-group answer", .acceptable)]
    paperFeatures := [("type", "PBI")] }

def ex_79 : Datum :=
  { id := "elliottnicolaesauerland2022_79"
    source := ⟨"elliott-nicolae-sauerland-2022", "(79)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Quién se reunió en el patio?"
    glossedTokens := [("Quién", "who.SG"), ("se", "REFL"), ("reunió", "gathered"), ("en", "in"), ("el", "the"), ("patio", "playground")]
    glossedWords := [⟨['Q', 'u', 'i', 'é', 'n'], ['w', 'h', 'o', '.', 'S', 'G'], [⟨['Q', 'u', 'i', 'é', 'n'], ['w', 'h', 'o', '.', 'S', 'G'], none⟩]⟩, ⟨['s', 'e'], ['R', 'E', 'F', 'L'], [⟨['s', 'e'], ['R', 'E', 'F', 'L'], none⟩]⟩, ⟨['r', 'e', 'u', 'n', 'i', 'ó'], ['g', 'a', 't', 'h', 'e', 'r', 'e', 'd'], [⟨['r', 'e', 'u', 'n', 'i', 'ó'], ['g', 'a', 't', 'h', 'e', 'r', 'e', 'd'], none⟩]⟩, ⟨['e', 'n'], ['i', 'n'], [⟨['e', 'n'], ['i', 'n'], none⟩]⟩, ⟨['e', 'l'], ['t', 'h', 'e'], [⟨['e', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['p', 'a', 't', 'i', 'o'], ['p', 'l', 'a', 'y', 'g', 'r', 'o', 'u', 'n', 'd'], [⟨['p', 'a', 't', 'i', 'o'], ['p', 'l', 'a', 'y', 'g', 'r', 'o', 'u', 'n', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("type", "SBI")] }

def ex_80 : Datum :=
  { id := "elliottnicolaesauerland2022_80"
    source := ⟨"elliott-nicolae-sauerland-2022", "(80)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Quién formó un grupo?"
    glossedTokens := [("Quién", "who.SG"), ("formó", "formed"), ("un", "a"), ("grupo", "group")]
    glossedWords := [⟨['Q', 'u', 'i', 'é', 'n'], ['w', 'h', 'o', '.', 'S', 'G'], [⟨['Q', 'u', 'i', 'é', 'n'], ['w', 'h', 'o', '.', 'S', 'G'], none⟩]⟩, ⟨['f', 'o', 'r', 'm', 'ó'], ['f', 'o', 'r', 'm', 'e', 'd'], [⟨['f', 'o', 'r', 'm', 'ó'], ['f', 'o', 'r', 'm', 'e', 'd'], none⟩]⟩, ⟨['u', 'n'], ['a'], [⟨['u', 'n'], ['a'], none⟩]⟩, ⟨['g', 'r', 'u', 'p', 'o'], ['g', 'r', 'o', 'u', 'p'], [⟨['g', 'r', 'u', 'p', 'o'], ['g', 'r', 'o', 'u', 'p'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("type", "SBI")] }

def ex_81 : Datum :=
  { id := "elliottnicolaesauerland2022_81"
    source := ⟨"elliott-nicolae-sauerland-2022", "(81)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Quién pesa 300kg?"
    glossedTokens := [("Quién", "who.SG"), ("pesa", "weighs"), ("300kg", "300kg")]
    glossedWords := [⟨['Q', 'u', 'i', 'é', 'n'], ['w', 'h', 'o', '.', 'S', 'G'], [⟨['Q', 'u', 'i', 'é', 'n'], ['w', 'h', 'o', '.', 'S', 'G'], none⟩]⟩, ⟨['p', 'e', 's', 'a'], ['w', 'e', 'i', 'g', 'h', 's'], [⟨['p', 'e', 's', 'a'], ['w', 'e', 'i', 'g', 'h', 's'], none⟩]⟩, ⟨['3', '0', '0', 'k', 'g'], ['3', '0', '0', 'k', 'g'], [⟨['3', '0', '0', 'k', 'g'], ['3', '0', '0', 'k', 'g'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("distributive answer", .acceptable), ("collective answer", .unacceptable)]
    paperFeatures := [("type", "SBI")] }

def ex_82 : Datum :=
  { id := "elliottnicolaesauerland2022_82"
    source := ⟨"elliott-nicolae-sauerland-2022", "(82)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Quiénes bebieron 40 cervezas juntos?"
    glossedTokens := [("Quiénes", "who.PL"), ("bebieron", "drink.PL"), ("40", "40"), ("cervezas", "beer"), ("juntos", "together")]
    glossedWords := [⟨['Q', 'u', 'i', 'é', 'n', 'e', 's'], ['w', 'h', 'o', '.', 'P', 'L'], [⟨['Q', 'u', 'i', 'é', 'n', 'e', 's'], ['w', 'h', 'o', '.', 'P', 'L'], none⟩]⟩, ⟨['b', 'e', 'b', 'i', 'e', 'r', 'o', 'n'], ['d', 'r', 'i', 'n', 'k', '.', 'P', 'L'], [⟨['b', 'e', 'b', 'i', 'e', 'r', 'o', 'n'], ['d', 'r', 'i', 'n', 'k', '.', 'P', 'L'], none⟩]⟩, ⟨['4', '0'], ['4', '0'], [⟨['4', '0'], ['4', '0'], none⟩]⟩, ⟨['c', 'e', 'r', 'v', 'e', 'z', 'a', 's'], ['b', 'e', 'e', 'r'], [⟨['c', 'e', 'r', 'v', 'e', 'z', 'a', 's'], ['b', 'e', 'e', 'r'], none⟩]⟩, ⟨['j', 'u', 'n', 't', 'o', 's'], ['t', 'o', 'g', 'e', 't', 'h', 'e', 'r'], [⟨['j', 'u', 'n', 't', 'o', 's'], ['t', 'o', 'g', 'e', 't', 'h', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("¿Quién bebió 40 cervezas juntos?", .unacceptable)]
    readings := []
    paperFeatures := [("type", "PBI")] }

def all : List Datum := [ex_2, ex_3, ex_11, ex_12, ex_13, ex_14, ex_15, ex_16, ex_17, ex_18, ex_19, ex_20, ex_21, ex_22, ex_23, ex_24a, ex_24b, ex_24c, ex_25, ex_57, ex_59, ex_66, ex_68, n19i, ex_76, ex_79, ex_80, ex_81, ex_82]

/-- The type of interrogative phrase. -/
inductive PhraseType where
  /-- SCI: a singular complex interrogative -/
  | singularComplex
  /-- PCI: a plural complex interrogative -/
  | pluralComplex
  /-- BI: a bare interrogative unmarked for number -/
  | bare
  /-- SBI: a singular bare interrogative -/
  | singularBare
  /-- PBI: a plural bare interrogative -/
  | pluralBare
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `type`. -/
def phraseType (e : Datum) : Option PhraseType :=
  e.parse? "type" [("SCI", .singularComplex), ("PCI", .pluralComplex), ("BI", .bare), ("SBI", .singularBare),
    ("PBI", .pluralBare)]

/-- What the context settles about how many individuals satisfy the question's nucleus. -/
inductive Context where
  /-- exactlyOne: exactly one does -/
  | exactlyOne
  /-- atLeastOne: at least one does -/
  | atLeastOne
  /-- several: several do -/
  | several
  /-- noExistence: it is open whether any does -/
  | noExistence
  /-- twoWhispering: two people are heard whispering -/
  | twoWhispering
  /-- zeroOrSeveral: none or several do -/
  | zeroOrSeveral
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `context`. -/
def context (e : Datum) : Option Context :=
  e.parse? "context" [("exactlyOne", .exactlyOne), ("atLeastOne", .atLeastOne), ("several", .several),
    ("noExistence", .noExistence), ("twoWhispering", .twoWhispering),
    ("zeroOrSeveral", .zeroOrSeveral)]

end ElliottNicolaeSauerland2022.Examples
