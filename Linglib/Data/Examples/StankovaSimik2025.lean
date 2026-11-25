module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `StankovaSimik2025` — typed example data

Auto-generated from `Linglib/Data/Examples/StankovaSimik2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace StankovaSimik2025.Examples`.
-/

@[expose] public section

namespace StankovaSimik2025.Examples

def ex13_v1_nci : Datum :=
  { id := "stankovasimik2025_ex13_v1_nci"
    source := ⟨"stankova-simik-2025", "(13) B"⟩
    reportedIn := none
    method := some .experiment
    language := "czec1258"
    primaryText := "Nezasadila tam Dana žádné květiny?"
    glossedTokens := [("Nezasadila", "NEG.planted"), ("tam", "there"), ("Dana", "Dana"), ("žádné", "DET.NCI"), ("květiny", "flowers")]
    glossedWords := [⟨['N', 'e', 'z', 'a', 's', 'a', 'd', 'i', 'l', 'a'], ['N', 'E', 'G', '.', 'p', 'l', 'a', 'n', 't', 'e', 'd'], [⟨['N', 'e', 'z', 'a', 's', 'a', 'd', 'i', 'l', 'a'], ['N', 'E', 'G', '.', 'p', 'l', 'a', 'n', 't', 'e', 'd'], none⟩]⟩, ⟨['t', 'a', 'm'], ['t', 'h', 'e', 'r', 'e'], [⟨['t', 'a', 'm'], ['t', 'h', 'e', 'r', 'e'], none⟩]⟩, ⟨['D', 'a', 'n', 'a'], ['D', 'a', 'n', 'a'], [⟨['D', 'a', 'n', 'a'], ['D', 'a', 'n', 'a'], none⟩]⟩, ⟨['ž', 'á', 'd', 'n', 'é'], ['D', 'E', 'T', '.', 'N', 'C', 'I'], [⟨['ž', 'á', 'd', 'n', 'é'], ['D', 'E', 'T', '.', 'N', 'C', 'I'], none⟩]⟩, ⟨['k', 'v', 'ě', 't', 'i', 'n', 'y'], ['f', 'l', 'o', 'w', 'e', 'r', 's'], [⟨['k', 'v', 'ě', 't', 'i', 'n', 'y'], ['f', 'l', 'o', 'w', 'e', 'r', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Dana má na zahradě záhon, který vybudovala před rokem. ('Dana has a garden bed, which she built a year ago.' — neutral, implying neither p nor ¬p)"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("order", "v1"), ("polarity", "negative"), ("indefinite", "nci"), ("context", "neutral")] }

def ex13_v1_ppi : Datum :=
  { id := "stankovasimik2025_ex13_v1_ppi"
    source := ⟨"stankova-simik-2025", "(13) B"⟩
    reportedIn := none
    method := some .experiment
    language := "czec1258"
    primaryText := "Nezasadila tam Dana nějaké květiny?"
    glossedTokens := [("Nezasadila", "NEG.planted"), ("tam", "there"), ("Dana", "Dana"), ("nějaké", "DET.PPI"), ("květiny", "flowers")]
    glossedWords := [⟨['N', 'e', 'z', 'a', 's', 'a', 'd', 'i', 'l', 'a'], ['N', 'E', 'G', '.', 'p', 'l', 'a', 'n', 't', 'e', 'd'], [⟨['N', 'e', 'z', 'a', 's', 'a', 'd', 'i', 'l', 'a'], ['N', 'E', 'G', '.', 'p', 'l', 'a', 'n', 't', 'e', 'd'], none⟩]⟩, ⟨['t', 'a', 'm'], ['t', 'h', 'e', 'r', 'e'], [⟨['t', 'a', 'm'], ['t', 'h', 'e', 'r', 'e'], none⟩]⟩, ⟨['D', 'a', 'n', 'a'], ['D', 'a', 'n', 'a'], [⟨['D', 'a', 'n', 'a'], ['D', 'a', 'n', 'a'], none⟩]⟩, ⟨['n', 'ě', 'j', 'a', 'k', 'é'], ['D', 'E', 'T', '.', 'P', 'P', 'I'], [⟨['n', 'ě', 'j', 'a', 'k', 'é'], ['D', 'E', 'T', '.', 'P', 'P', 'I'], none⟩]⟩, ⟨['k', 'v', 'ě', 't', 'i', 'n', 'y'], ['f', 'l', 'o', 'w', 'e', 'r', 's'], [⟨['k', 'v', 'ě', 't', 'i', 'n', 'y'], ['f', 'l', 'o', 'w', 'e', 'r', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Dana má na zahradě záhon, který vybudovala před rokem. ('Dana has a garden bed, which she built a year ago.' — neutral, implying neither p nor ¬p)"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("order", "v1"), ("polarity", "negative"), ("indefinite", "ppi"), ("context", "neutral")] }

def ex13_nonv1_nci : Datum :=
  { id := "stankovasimik2025_ex13_nonv1_nci"
    source := ⟨"stankova-simik-2025", "(13) B′"⟩
    reportedIn := none
    method := some .experiment
    language := "czec1258"
    primaryText := "Dana tam nezasadila žádné květiny?"
    glossedTokens := [("Dana", "Dana"), ("tam", "there"), ("nezasadila", "NEG.planted"), ("žádné", "DET.NCI"), ("květiny", "flowers")]
    glossedWords := [⟨['D', 'a', 'n', 'a'], ['D', 'a', 'n', 'a'], [⟨['D', 'a', 'n', 'a'], ['D', 'a', 'n', 'a'], none⟩]⟩, ⟨['t', 'a', 'm'], ['t', 'h', 'e', 'r', 'e'], [⟨['t', 'a', 'm'], ['t', 'h', 'e', 'r', 'e'], none⟩]⟩, ⟨['n', 'e', 'z', 'a', 's', 'a', 'd', 'i', 'l', 'a'], ['N', 'E', 'G', '.', 'p', 'l', 'a', 'n', 't', 'e', 'd'], [⟨['n', 'e', 'z', 'a', 's', 'a', 'd', 'i', 'l', 'a'], ['N', 'E', 'G', '.', 'p', 'l', 'a', 'n', 't', 'e', 'd'], none⟩]⟩, ⟨['ž', 'á', 'd', 'n', 'é'], ['D', 'E', 'T', '.', 'N', 'C', 'I'], [⟨['ž', 'á', 'd', 'n', 'é'], ['D', 'E', 'T', '.', 'N', 'C', 'I'], none⟩]⟩, ⟨['k', 'v', 'ě', 't', 'i', 'n', 'y'], ['f', 'l', 'o', 'w', 'e', 'r', 's'], [⟨['k', 'v', 'ě', 't', 'i', 'n', 'y'], ['f', 'l', 'o', 'w', 'e', 'r', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Dana má na zahradě záhon, kam zasadila zeleninu. ('Dana has a garden bed, where she planted vegetables.' — negative, implying ¬p)"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("order", "nonV1"), ("polarity", "negative"), ("indefinite", "nci"), ("context", "negative")] }

def ex13_nonv1_ppi : Datum :=
  { id := "stankovasimik2025_ex13_nonv1_ppi"
    source := ⟨"stankova-simik-2025", "(13) B′"⟩
    reportedIn := none
    method := some .experiment
    language := "czec1258"
    primaryText := "Dana tam nezasadila nějaké květiny?"
    glossedTokens := [("Dana", "Dana"), ("tam", "there"), ("nezasadila", "NEG.planted"), ("nějaké", "DET.PPI"), ("květiny", "flowers")]
    glossedWords := [⟨['D', 'a', 'n', 'a'], ['D', 'a', 'n', 'a'], [⟨['D', 'a', 'n', 'a'], ['D', 'a', 'n', 'a'], none⟩]⟩, ⟨['t', 'a', 'm'], ['t', 'h', 'e', 'r', 'e'], [⟨['t', 'a', 'm'], ['t', 'h', 'e', 'r', 'e'], none⟩]⟩, ⟨['n', 'e', 'z', 'a', 's', 'a', 'd', 'i', 'l', 'a'], ['N', 'E', 'G', '.', 'p', 'l', 'a', 'n', 't', 'e', 'd'], [⟨['n', 'e', 'z', 'a', 's', 'a', 'd', 'i', 'l', 'a'], ['N', 'E', 'G', '.', 'p', 'l', 'a', 'n', 't', 'e', 'd'], none⟩]⟩, ⟨['n', 'ě', 'j', 'a', 'k', 'é'], ['D', 'E', 'T', '.', 'P', 'P', 'I'], [⟨['n', 'ě', 'j', 'a', 'k', 'é'], ['D', 'E', 'T', '.', 'P', 'P', 'I'], none⟩]⟩, ⟨['k', 'v', 'ě', 't', 'i', 'n', 'y'], ['f', 'l', 'o', 'w', 'e', 'r', 's'], [⟨['k', 'v', 'ě', 't', 'i', 'n', 'y'], ['f', 'l', 'o', 'w', 'e', 'r', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Dana má na zahradě záhon, kam zasadila zeleninu. ('Dana has a garden bed, where she planted vegetables.' — negative, implying ¬p)"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("order", "nonV1"), ("polarity", "negative"), ("indefinite", "ppi"), ("context", "negative")] }

def ex14 : Datum :=
  { id := "stankovasimik2025_ex14"
    source := ⟨"stankova-simik-2025", "(14) B"⟩
    reportedIn := none
    method := some .experiment
    language := "czec1258"
    primaryText := "Nevyhrála Eva nějakou cenu?"
    glossedTokens := [("Nevyhrála", "NEG.won"), ("Eva", "Eva"), ("nějakou", "DET.PPI"), ("cenu", "prize")]
    glossedWords := [⟨['N', 'e', 'v', 'y', 'h', 'r', 'á', 'l', 'a'], ['N', 'E', 'G', '.', 'w', 'o', 'n'], [⟨['N', 'e', 'v', 'y', 'h', 'r', 'á', 'l', 'a'], ['N', 'E', 'G', '.', 'w', 'o', 'n'], none⟩]⟩, ⟨['E', 'v', 'a'], ['E', 'v', 'a'], [⟨['E', 'v', 'a'], ['E', 'v', 'a'], none⟩]⟩, ⟨['n', 'ě', 'j', 'a', 'k', 'o', 'u'], ['D', 'E', 'T', '.', 'P', 'P', 'I'], [⟨['n', 'ě', 'j', 'a', 'k', 'o', 'u'], ['D', 'E', 'T', '.', 'P', 'P', 'I'], none⟩]⟩, ⟨['c', 'e', 'n', 'u'], ['p', 'r', 'i', 'z', 'e'], [⟨['c', 'e', 'n', 'u'], ['p', 'r', 'i', 'z', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Eva se zúčastnila lingvistické olympiády, kde skončila jako první. ('Eva participated in a linguistic olympiad, where she won the first place.' — positive evidence for p)"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("order", "v1"), ("polarity", "negative"), ("indefinite", "ppi"), ("context", "positive")] }

def ex16a : Datum :=
  { id := "stankovasimik2025_ex16a"
    source := ⟨"stankova-simik-2025", "(16a)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Nepojede Karel náhodou do Brna?"
    glossedTokens := [("Nepojede", "NEG.go.FUT"), ("Karel", "Karel"), ("náhodou", "NÁHODOU"), ("do", "to"), ("Brna", "Brno")]
    glossedWords := [⟨['N', 'e', 'p', 'o', 'j', 'e', 'd', 'e'], ['N', 'E', 'G', '.', 'g', 'o', '.', 'F', 'U', 'T'], [⟨['N', 'e', 'p', 'o', 'j', 'e', 'd', 'e'], ['N', 'E', 'G', '.', 'g', 'o', '.', 'F', 'U', 'T'], none⟩]⟩, ⟨['K', 'a', 'r', 'e', 'l'], ['K', 'a', 'r', 'e', 'l'], [⟨['K', 'a', 'r', 'e', 'l'], ['K', 'a', 'r', 'e', 'l'], none⟩]⟩, ⟨['n', 'á', 'h', 'o', 'd', 'o', 'u'], ['N', 'Á', 'H', 'O', 'D', 'O', 'U'], [⟨['n', 'á', 'h', 'o', 'd', 'o', 'u'], ['N', 'Á', 'H', 'O', 'D', 'O', 'U'], none⟩]⟩, ⟨['d', 'o'], ['t', 'o'], [⟨['d', 'o'], ['t', 'o'], none⟩]⟩, ⟨['B', 'r', 'n', 'a'], ['B', 'r', 'n', 'o'], [⟨['B', 'r', 'n', 'a'], ['B', 'r', 'n', 'o'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("order", "v1"), ("polarity", "negative"), ("particle", "náhodou")] }

def ex16b : Datum :=
  { id := "stankovasimik2025_ex16b"
    source := ⟨"stankova-simik-2025", "(16b)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Pojede Karel náhodou do Brna?"
    glossedTokens := [("Pojede", "go.FUT"), ("Karel", "Karel"), ("náhodou", "NÁHODOU"), ("do", "to"), ("Brna", "Brno")]
    glossedWords := [⟨['P', 'o', 'j', 'e', 'd', 'e'], ['g', 'o', '.', 'F', 'U', 'T'], [⟨['P', 'o', 'j', 'e', 'd', 'e'], ['g', 'o', '.', 'F', 'U', 'T'], none⟩]⟩, ⟨['K', 'a', 'r', 'e', 'l'], ['K', 'a', 'r', 'e', 'l'], [⟨['K', 'a', 'r', 'e', 'l'], ['K', 'a', 'r', 'e', 'l'], none⟩]⟩, ⟨['n', 'á', 'h', 'o', 'd', 'o', 'u'], ['N', 'Á', 'H', 'O', 'D', 'O', 'U'], [⟨['n', 'á', 'h', 'o', 'd', 'o', 'u'], ['N', 'Á', 'H', 'O', 'D', 'O', 'U'], none⟩]⟩, ⟨['d', 'o'], ['t', 'o'], [⟨['d', 'o'], ['t', 'o'], none⟩]⟩, ⟨['B', 'r', 'n', 'a'], ['B', 'r', 'n', 'o'], [⟨['B', 'r', 'n', 'a'], ['B', 'r', 'n', 'o'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("order", "v1"), ("polarity", "positive"), ("particle", "náhodou")] }

def ex17_ppi : Datum :=
  { id := "stankovasimik2025_ex17_ppi"
    source := ⟨"stankova-simik-2025", "(17) B"⟩
    reportedIn := none
    method := some .experiment
    language := "czec1258"
    primaryText := "Nezarezervoval si Mikuláš náhodou nějaké sedadlo?"
    glossedTokens := [("Nezarezervoval", "NEG.booked"), ("si", "REFL"), ("Mikuláš", "Mikuláš"), ("náhodou", "NÁHODOU"), ("nějaké", "DET.PPI"), ("sedadlo", "seat")]
    glossedWords := [⟨['N', 'e', 'z', 'a', 'r', 'e', 'z', 'e', 'r', 'v', 'o', 'v', 'a', 'l'], ['N', 'E', 'G', '.', 'b', 'o', 'o', 'k', 'e', 'd'], [⟨['N', 'e', 'z', 'a', 'r', 'e', 'z', 'e', 'r', 'v', 'o', 'v', 'a', 'l'], ['N', 'E', 'G', '.', 'b', 'o', 'o', 'k', 'e', 'd'], none⟩]⟩, ⟨['s', 'i'], ['R', 'E', 'F', 'L'], [⟨['s', 'i'], ['R', 'E', 'F', 'L'], none⟩]⟩, ⟨['M', 'i', 'k', 'u', 'l', 'á', 'š'], ['M', 'i', 'k', 'u', 'l', 'á', 'š'], [⟨['M', 'i', 'k', 'u', 'l', 'á', 'š'], ['M', 'i', 'k', 'u', 'l', 'á', 'š'], none⟩]⟩, ⟨['n', 'á', 'h', 'o', 'd', 'o', 'u'], ['N', 'Á', 'H', 'O', 'D', 'O', 'U'], [⟨['n', 'á', 'h', 'o', 'd', 'o', 'u'], ['N', 'Á', 'H', 'O', 'D', 'O', 'U'], none⟩]⟩, ⟨['n', 'ě', 'j', 'a', 'k', 'é'], ['D', 'E', 'T', '.', 'P', 'P', 'I'], [⟨['n', 'ě', 'j', 'a', 'k', 'é'], ['D', 'E', 'T', '.', 'P', 'P', 'I'], none⟩]⟩, ⟨['s', 'e', 'd', 'a', 'd', 'l', 'o'], ['s', 'e', 'a', 't'], [⟨['s', 'e', 'd', 'a', 'd', 'l', 'o'], ['s', 'e', 'a', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Mikuláš cestoval vlakem, který jel do Košic. ('Mikuláš was on the train which went to Košice.' — neutral)"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("order", "v1"), ("polarity", "negative"), ("indefinite", "ppi"), ("context", "neutral"), ("particle", "náhodou")] }

def ex17_nci : Datum :=
  { id := "stankovasimik2025_ex17_nci"
    source := ⟨"stankova-simik-2025", "(17) B"⟩
    reportedIn := none
    method := some .experiment
    language := "czec1258"
    primaryText := "Nezarezervoval si Mikuláš náhodou žádné sedadlo?"
    glossedTokens := [("Nezarezervoval", "NEG.booked"), ("si", "REFL"), ("Mikuláš", "Mikuláš"), ("náhodou", "NÁHODOU"), ("žádné", "DET.NCI"), ("sedadlo", "seat")]
    glossedWords := [⟨['N', 'e', 'z', 'a', 'r', 'e', 'z', 'e', 'r', 'v', 'o', 'v', 'a', 'l'], ['N', 'E', 'G', '.', 'b', 'o', 'o', 'k', 'e', 'd'], [⟨['N', 'e', 'z', 'a', 'r', 'e', 'z', 'e', 'r', 'v', 'o', 'v', 'a', 'l'], ['N', 'E', 'G', '.', 'b', 'o', 'o', 'k', 'e', 'd'], none⟩]⟩, ⟨['s', 'i'], ['R', 'E', 'F', 'L'], [⟨['s', 'i'], ['R', 'E', 'F', 'L'], none⟩]⟩, ⟨['M', 'i', 'k', 'u', 'l', 'á', 'š'], ['M', 'i', 'k', 'u', 'l', 'á', 'š'], [⟨['M', 'i', 'k', 'u', 'l', 'á', 'š'], ['M', 'i', 'k', 'u', 'l', 'á', 'š'], none⟩]⟩, ⟨['n', 'á', 'h', 'o', 'd', 'o', 'u'], ['N', 'Á', 'H', 'O', 'D', 'O', 'U'], [⟨['n', 'á', 'h', 'o', 'd', 'o', 'u'], ['N', 'Á', 'H', 'O', 'D', 'O', 'U'], none⟩]⟩, ⟨['ž', 'á', 'd', 'n', 'é'], ['D', 'E', 'T', '.', 'N', 'C', 'I'], [⟨['ž', 'á', 'd', 'n', 'é'], ['D', 'E', 'T', '.', 'N', 'C', 'I'], none⟩]⟩, ⟨['s', 'e', 'd', 'a', 'd', 'l', 'o'], ['s', 'e', 'a', 't'], [⟨['s', 'e', 'd', 'a', 'd', 'l', 'o'], ['s', 'e', 'a', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Mikuláš cestoval vlakem, který jel do Košic. ('Mikuláš was on the train which went to Košice.' — neutral)"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("order", "v1"), ("polarity", "negative"), ("indefinite", "nci"), ("context", "neutral"), ("particle", "náhodou")] }

def ex18 : Datum :=
  { id := "stankovasimik2025_ex18"
    source := ⟨"stankova-simik-2025", "(18) B"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "A Petr si náhodou nekoupil nějakou knihu?"
    glossedTokens := [("A", "and"), ("Petr", "Petr"), ("si", "REFL"), ("náhodou", "NÁHODOU"), ("nekoupil", "NEG.bought"), ("nějakou", "DET.PPI"), ("knihu", "book")]
    glossedWords := [⟨['A'], ['a', 'n', 'd'], [⟨['A'], ['a', 'n', 'd'], none⟩]⟩, ⟨['P', 'e', 't', 'r'], ['P', 'e', 't', 'r'], [⟨['P', 'e', 't', 'r'], ['P', 'e', 't', 'r'], none⟩]⟩, ⟨['s', 'i'], ['R', 'E', 'F', 'L'], [⟨['s', 'i'], ['R', 'E', 'F', 'L'], none⟩]⟩, ⟨['n', 'á', 'h', 'o', 'd', 'o', 'u'], ['N', 'Á', 'H', 'O', 'D', 'O', 'U'], [⟨['n', 'á', 'h', 'o', 'd', 'o', 'u'], ['N', 'Á', 'H', 'O', 'D', 'O', 'U'], none⟩]⟩, ⟨['n', 'e', 'k', 'o', 'u', 'p', 'i', 'l'], ['N', 'E', 'G', '.', 'b', 'o', 'u', 'g', 'h', 't'], [⟨['n', 'e', 'k', 'o', 'u', 'p', 'i', 'l'], ['N', 'E', 'G', '.', 'b', 'o', 'u', 'g', 'h', 't'], none⟩]⟩, ⟨['n', 'ě', 'j', 'a', 'k', 'o', 'u'], ['D', 'E', 'T', '.', 'P', 'P', 'I'], [⟨['n', 'ě', 'j', 'a', 'k', 'o', 'u'], ['D', 'E', 'T', '.', 'P', 'P', 'I'], none⟩]⟩, ⟨['k', 'n', 'i', 'h', 'u'], ['b', 'o', 'o', 'k'], [⟨['k', 'n', 'i', 'h', 'u'], ['b', 'o', 'o', 'k'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Hanka si koupila knihu. ('Hanka bought a book.')"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("order", "nonV1"), ("polarity", "negative"), ("indefinite", "ppi"), ("particle", "náhodou")] }

def ex18_nci : Datum :=
  { id := "stankovasimik2025_ex18_nci"
    source := ⟨"stankova-simik-2025", "(18) B"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "A Petr si náhodou nekoupil žádnou knihu?"
    glossedTokens := [("A", "and"), ("Petr", "Petr"), ("si", "REFL"), ("náhodou", "NÁHODOU"), ("nekoupil", "NEG.bought"), ("žádnou", "DET.NCI"), ("knihu", "book")]
    glossedWords := [⟨['A'], ['a', 'n', 'd'], [⟨['A'], ['a', 'n', 'd'], none⟩]⟩, ⟨['P', 'e', 't', 'r'], ['P', 'e', 't', 'r'], [⟨['P', 'e', 't', 'r'], ['P', 'e', 't', 'r'], none⟩]⟩, ⟨['s', 'i'], ['R', 'E', 'F', 'L'], [⟨['s', 'i'], ['R', 'E', 'F', 'L'], none⟩]⟩, ⟨['n', 'á', 'h', 'o', 'd', 'o', 'u'], ['N', 'Á', 'H', 'O', 'D', 'O', 'U'], [⟨['n', 'á', 'h', 'o', 'd', 'o', 'u'], ['N', 'Á', 'H', 'O', 'D', 'O', 'U'], none⟩]⟩, ⟨['n', 'e', 'k', 'o', 'u', 'p', 'i', 'l'], ['N', 'E', 'G', '.', 'b', 'o', 'u', 'g', 'h', 't'], [⟨['n', 'e', 'k', 'o', 'u', 'p', 'i', 'l'], ['N', 'E', 'G', '.', 'b', 'o', 'u', 'g', 'h', 't'], none⟩]⟩, ⟨['ž', 'á', 'd', 'n', 'o', 'u'], ['D', 'E', 'T', '.', 'N', 'C', 'I'], [⟨['ž', 'á', 'd', 'n', 'o', 'u'], ['D', 'E', 'T', '.', 'N', 'C', 'I'], none⟩]⟩, ⟨['k', 'n', 'i', 'h', 'u'], ['b', 'o', 'o', 'k'], [⟨['k', 'n', 'i', 'h', 'u'], ['b', 'o', 'o', 'k'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Hanka si koupila knihu. ('Hanka bought a book.')"
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("order", "nonV1"), ("polarity", "negative"), ("indefinite", "nci"), ("particle", "náhodou")] }

def all : List Datum := [ex13_v1_nci, ex13_v1_ppi, ex13_nonv1_nci, ex13_nonv1_ppi, ex14, ex16a, ex16b, ex17_ppi, ex17_nci, ex18, ex18_nci]

/-- The position of the finite verb. -/
inductive WordOrder where
  /-- v1: the finite verb is clause-initial, interrogative word order -/
  | v1
  /-- nonV1: the finite verb is in situ, declarative word order -/
  | nonV1
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `order`. -/
def order (e : Datum) : Option WordOrder :=
  e.parse? "order" [("v1", .v1), ("nonV1", .nonV1)]

/-- Whether the finite verb is negated. -/
inductive QuestionPolarity where
  /-- positive: an affirmative finite verb -/
  | positive
  /-- negative: a finite verb with the negative prefix -/
  | negative
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `polarity`. -/
def polarity (e : Datum) : Option QuestionPolarity :=
  e.parse? "polarity" [("positive", .positive), ("negative", .negative)]

/-- The indefinite determiner the experiments manipulate. -/
inductive Indefinite where
  /-- nci: the negative concord item *žádný*, a proxy for inner negation -/
  | nci
  /-- ppi: the positive polarity item *nějaký*, a proxy for outer negation -/
  | ppi
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `indefinite`. -/
def indefinite (e : Datum) : Option Indefinite :=
  e.parse? "indefinite" [("nci", .nci), ("ppi", .ppi)]

/-- The contextual evidence of the preceding utterance. -/
inductive Context where
  /-- negative: the context implies that the prejacent is false -/
  | negative
  /-- neutral: the context implies neither answer -/
  | neutral
  /-- positive: the context implies that the prejacent is true -/
  | positive
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `context`. -/
def context (e : Datum) : Option Context :=
  e.parse? "context" [("negative", .negative), ("neutral", .neutral), ("positive", .positive)]

/-- The examples of the file. -/
inductive Example where
  | ex13_v1_nci
  | ex13_v1_ppi
  | ex13_nonv1_nci
  | ex13_nonv1_ppi
  | ex14
  | ex16a
  | ex16b
  | ex17_ppi
  | ex17_nci
  | ex18
  | ex18_nci
  deriving DecidableEq, Repr, Fintype

/-- Every example of the file, in its order. -/
def Example.all : List Example :=
  [.ex13_v1_nci, .ex13_v1_ppi, .ex13_nonv1_nci, .ex13_nonv1_ppi, .ex14, .ex16a, .ex16b,
    .ex17_ppi, .ex17_nci, .ex18, .ex18_nci]

/-- The row of an example. -/
def Example.datum : Example → Datum
  | .ex13_v1_nci => _root_.StankovaSimik2025.Examples.ex13_v1_nci
  | .ex13_v1_ppi => _root_.StankovaSimik2025.Examples.ex13_v1_ppi
  | .ex13_nonv1_nci => _root_.StankovaSimik2025.Examples.ex13_nonv1_nci
  | .ex13_nonv1_ppi => _root_.StankovaSimik2025.Examples.ex13_nonv1_ppi
  | .ex14 => _root_.StankovaSimik2025.Examples.ex14
  | .ex16a => _root_.StankovaSimik2025.Examples.ex16a
  | .ex16b => _root_.StankovaSimik2025.Examples.ex16b
  | .ex17_ppi => _root_.StankovaSimik2025.Examples.ex17_ppi
  | .ex17_nci => _root_.StankovaSimik2025.Examples.ex17_nci
  | .ex18 => _root_.StankovaSimik2025.Examples.ex18
  | .ex18_nci => _root_.StankovaSimik2025.Examples.ex18_nci

theorem Example.map_datum_all :
    Example.all.map Example.datum = _root_.StankovaSimik2025.Examples.all := rfl

/-- The value the example records under `order`. -/
def Example.order : Example → Option WordOrder
  | .ex13_v1_nci => some .v1
  | .ex13_v1_ppi => some .v1
  | .ex13_nonv1_nci => some .nonV1
  | .ex13_nonv1_ppi => some .nonV1
  | .ex14 => some .v1
  | .ex16a => some .v1
  | .ex16b => some .v1
  | .ex17_ppi => some .v1
  | .ex17_nci => some .v1
  | .ex18 => some .nonV1
  | .ex18_nci => some .nonV1

theorem Example.order_datum :
    ∀ x : Example, _root_.StankovaSimik2025.Examples.order x.datum = x.order := by
  decide +kernel

/-- The value the example records under `polarity`. -/
def Example.polarity : Example → Option QuestionPolarity
  | .ex13_v1_nci => some .negative
  | .ex13_v1_ppi => some .negative
  | .ex13_nonv1_nci => some .negative
  | .ex13_nonv1_ppi => some .negative
  | .ex14 => some .negative
  | .ex16a => some .negative
  | .ex16b => some .positive
  | .ex17_ppi => some .negative
  | .ex17_nci => some .negative
  | .ex18 => some .negative
  | .ex18_nci => some .negative

theorem Example.polarity_datum :
    ∀ x : Example, _root_.StankovaSimik2025.Examples.polarity x.datum = x.polarity := by
  decide +kernel

/-- The value the example records under `indefinite`. -/
def Example.indefinite : Example → Option Indefinite
  | .ex13_v1_nci => some .nci
  | .ex13_v1_ppi => some .ppi
  | .ex13_nonv1_nci => some .nci
  | .ex13_nonv1_ppi => some .ppi
  | .ex14 => some .ppi
  | .ex16a => none
  | .ex16b => none
  | .ex17_ppi => some .ppi
  | .ex17_nci => some .nci
  | .ex18 => some .ppi
  | .ex18_nci => some .nci

theorem Example.indefinite_datum :
    ∀ x : Example, _root_.StankovaSimik2025.Examples.indefinite x.datum = x.indefinite := by
  decide +kernel

/-- The value the example records under `context`. -/
def Example.context : Example → Option Context
  | .ex13_v1_nci => some .neutral
  | .ex13_v1_ppi => some .neutral
  | .ex13_nonv1_nci => some .negative
  | .ex13_nonv1_ppi => some .negative
  | .ex14 => some .positive
  | .ex16a => none
  | .ex16b => none
  | .ex17_ppi => some .neutral
  | .ex17_nci => some .neutral
  | .ex18 => none
  | .ex18_nci => none

theorem Example.context_datum :
    ∀ x : Example, _root_.StankovaSimik2025.Examples.context x.datum = x.context := by
  decide +kernel

end StankovaSimik2025.Examples
