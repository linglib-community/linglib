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
    glossedWords := [⟨[['N', 'e', 'z', 'a', 's', 'a', 'd', 'i', 'l', 'a']], [['N', 'E', 'G', '.', 'p', 'l', 'a', 'n', 't', 'e', 'd']]⟩, ⟨[['t', 'a', 'm']], [['t', 'h', 'e', 'r', 'e']]⟩, ⟨[['D', 'a', 'n', 'a']], [['D', 'a', 'n', 'a']]⟩, ⟨[['ž', 'á', 'd', 'n', 'é']], [['D', 'E', 'T', '.', 'N', 'C', 'I']]⟩, ⟨[['k', 'v', 'ě', 't', 'i', 'n', 'y']], [['f', 'l', 'o', 'w', 'e', 'r', 's']]⟩]
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
    glossedWords := [⟨[['N', 'e', 'z', 'a', 's', 'a', 'd', 'i', 'l', 'a']], [['N', 'E', 'G', '.', 'p', 'l', 'a', 'n', 't', 'e', 'd']]⟩, ⟨[['t', 'a', 'm']], [['t', 'h', 'e', 'r', 'e']]⟩, ⟨[['D', 'a', 'n', 'a']], [['D', 'a', 'n', 'a']]⟩, ⟨[['n', 'ě', 'j', 'a', 'k', 'é']], [['D', 'E', 'T', '.', 'P', 'P', 'I']]⟩, ⟨[['k', 'v', 'ě', 't', 'i', 'n', 'y']], [['f', 'l', 'o', 'w', 'e', 'r', 's']]⟩]
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
    glossedWords := [⟨[['D', 'a', 'n', 'a']], [['D', 'a', 'n', 'a']]⟩, ⟨[['t', 'a', 'm']], [['t', 'h', 'e', 'r', 'e']]⟩, ⟨[['n', 'e', 'z', 'a', 's', 'a', 'd', 'i', 'l', 'a']], [['N', 'E', 'G', '.', 'p', 'l', 'a', 'n', 't', 'e', 'd']]⟩, ⟨[['ž', 'á', 'd', 'n', 'é']], [['D', 'E', 'T', '.', 'N', 'C', 'I']]⟩, ⟨[['k', 'v', 'ě', 't', 'i', 'n', 'y']], [['f', 'l', 'o', 'w', 'e', 'r', 's']]⟩]
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
    glossedWords := [⟨[['D', 'a', 'n', 'a']], [['D', 'a', 'n', 'a']]⟩, ⟨[['t', 'a', 'm']], [['t', 'h', 'e', 'r', 'e']]⟩, ⟨[['n', 'e', 'z', 'a', 's', 'a', 'd', 'i', 'l', 'a']], [['N', 'E', 'G', '.', 'p', 'l', 'a', 'n', 't', 'e', 'd']]⟩, ⟨[['n', 'ě', 'j', 'a', 'k', 'é']], [['D', 'E', 'T', '.', 'P', 'P', 'I']]⟩, ⟨[['k', 'v', 'ě', 't', 'i', 'n', 'y']], [['f', 'l', 'o', 'w', 'e', 'r', 's']]⟩]
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
    glossedWords := [⟨[['N', 'e', 'v', 'y', 'h', 'r', 'á', 'l', 'a']], [['N', 'E', 'G', '.', 'w', 'o', 'n']]⟩, ⟨[['E', 'v', 'a']], [['E', 'v', 'a']]⟩, ⟨[['n', 'ě', 'j', 'a', 'k', 'o', 'u']], [['D', 'E', 'T', '.', 'P', 'P', 'I']]⟩, ⟨[['c', 'e', 'n', 'u']], [['p', 'r', 'i', 'z', 'e']]⟩]
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
    glossedWords := [⟨[['N', 'e', 'z', 'a', 'r', 'e', 'z', 'e', 'r', 'v', 'o', 'v', 'a', 'l']], [['N', 'E', 'G', '.', 'b', 'o', 'o', 'k', 'e', 'd']]⟩, ⟨[['s', 'i']], [['R', 'E', 'F', 'L']]⟩, ⟨[['M', 'i', 'k', 'u', 'l', 'á', 'š']], [['M', 'i', 'k', 'u', 'l', 'á', 'š']]⟩, ⟨[['n', 'á', 'h', 'o', 'd', 'o', 'u']], [['N', 'Á', 'H', 'O', 'D', 'O', 'U']]⟩, ⟨[['n', 'ě', 'j', 'a', 'k', 'é']], [['D', 'E', 'T', '.', 'P', 'P', 'I']]⟩, ⟨[['s', 'e', 'd', 'a', 'd', 'l', 'o']], [['s', 'e', 'a', 't']]⟩]
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
    glossedWords := [⟨[['N', 'e', 'z', 'a', 'r', 'e', 'z', 'e', 'r', 'v', 'o', 'v', 'a', 'l']], [['N', 'E', 'G', '.', 'b', 'o', 'o', 'k', 'e', 'd']]⟩, ⟨[['s', 'i']], [['R', 'E', 'F', 'L']]⟩, ⟨[['M', 'i', 'k', 'u', 'l', 'á', 'š']], [['M', 'i', 'k', 'u', 'l', 'á', 'š']]⟩, ⟨[['n', 'á', 'h', 'o', 'd', 'o', 'u']], [['N', 'Á', 'H', 'O', 'D', 'O', 'U']]⟩, ⟨[['ž', 'á', 'd', 'n', 'é']], [['D', 'E', 'T', '.', 'N', 'C', 'I']]⟩, ⟨[['s', 'e', 'd', 'a', 'd', 'l', 'o']], [['s', 'e', 'a', 't']]⟩]
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
    glossedWords := [⟨[['A']], [['a', 'n', 'd']]⟩, ⟨[['P', 'e', 't', 'r']], [['P', 'e', 't', 'r']]⟩, ⟨[['s', 'i']], [['R', 'E', 'F', 'L']]⟩, ⟨[['n', 'á', 'h', 'o', 'd', 'o', 'u']], [['N', 'Á', 'H', 'O', 'D', 'O', 'U']]⟩, ⟨[['n', 'e', 'k', 'o', 'u', 'p', 'i', 'l']], [['N', 'E', 'G', '.', 'b', 'o', 'u', 'g', 'h', 't']]⟩, ⟨[['n', 'ě', 'j', 'a', 'k', 'o', 'u']], [['D', 'E', 'T', '.', 'P', 'P', 'I']]⟩, ⟨[['k', 'n', 'i', 'h', 'u']], [['b', 'o', 'o', 'k']]⟩]
    lgrConformance := some .wordAligned
    context := "Hanka si koupila knihu. ('Hanka bought a book.')"
    judgment := .acceptable
    alternatives := [("A Petr si náhodou nekoupil žádnou knihu?", .ungrammatical)]
    readings := []
    paperFeatures := [("particle", "nahodou"), ("verbPosition", "nonv1"), ("indefinite", "ppi")] }

def all : List Datum := [ex13_v1_nci, ex13_v1_ppi, ex13_nonv1_nci, ex13_nonv1_ppi, ex14, ex17_ppi, ex17_nci, ex18]

end StankovaSimik2025.Examples
