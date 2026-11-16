module

public import Linglib.Data.Examples.Schema

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
    alternatives := []
    readings := []
    paperFeatures := [("verbPosition", "v1"), ("indefinite", "nci"), ("context", "neutral")] }

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
    alternatives := []
    readings := []
    paperFeatures := [("verbPosition", "v1"), ("indefinite", "ppi"), ("context", "neutral")] }

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
    alternatives := []
    readings := []
    paperFeatures := [("verbPosition", "nonv1"), ("indefinite", "nci"), ("context", "negative")] }

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
    alternatives := []
    readings := []
    paperFeatures := [("verbPosition", "nonv1"), ("indefinite", "ppi"), ("context", "negative")] }

def ex14 : Datum :=
  { id := "stankovasimik2025_ex14"
    source := ⟨"stankova-simik-2025", "(14) B"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Nevyhrála Eva nějakou cenu?"
    glossedTokens := [("Nevyhrála", "NEG.won"), ("Eva", "Eva"), ("nějakou", "DET.PPI"), ("cenu", "prize")]
    glossedWords := [⟨['N', 'e', 'v', 'y', 'h', 'r', 'á', 'l', 'a'], ['N', 'E', 'G', '.', 'w', 'o', 'n'], [⟨['N', 'e', 'v', 'y', 'h', 'r', 'á', 'l', 'a'], ['N', 'E', 'G', '.', 'w', 'o', 'n'], none⟩]⟩, ⟨['E', 'v', 'a'], ['E', 'v', 'a'], [⟨['E', 'v', 'a'], ['E', 'v', 'a'], none⟩]⟩, ⟨['n', 'ě', 'j', 'a', 'k', 'o', 'u'], ['D', 'E', 'T', '.', 'P', 'P', 'I'], [⟨['n', 'ě', 'j', 'a', 'k', 'o', 'u'], ['D', 'E', 'T', '.', 'P', 'P', 'I'], none⟩]⟩, ⟨['c', 'e', 'n', 'u'], ['p', 'r', 'i', 'z', 'e'], [⟨['c', 'e', 'n', 'u'], ['p', 'r', 'i', 'z', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Eva se zúčastnila lingvistické olympiády, kde skončila jako první. ('Eva participated in a linguistic olympiad, where she won the first place.' — positive evidence for p)"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verbPosition", "v1"), ("indefinite", "ppi"), ("context", "positive")] }

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
    alternatives := []
    readings := []
    paperFeatures := [("particle", "nahodou"), ("verbPosition", "v1"), ("indefinite", "ppi"), ("context", "neutral")] }

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
    alternatives := []
    readings := []
    paperFeatures := [("particle", "nahodou"), ("verbPosition", "v1"), ("indefinite", "nci"), ("context", "neutral")] }

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
    alternatives := [("A Petr si náhodou nekoupil žádnou knihu?", .ungrammatical)]
    readings := []
    paperFeatures := [("particle", "nahodou"), ("verbPosition", "nonv1"), ("indefinite", "ppi")] }

def all : List Datum := [ex13_v1_nci, ex13_v1_ppi, ex13_nonv1_nci, ex13_nonv1_ppi, ex14, ex17_ppi, ex17_nci, ex18]

end StankovaSimik2025.Examples
