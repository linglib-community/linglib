module

public import Linglib.Data.Examples.Schema

/-!
# `Benz2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Benz2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Benz2025.Examples`.
-/

@[expose] public section

namespace Benz2025.Examples

def ex32a : Datum :=
  { id := "benz2025_ex32a"
    source := ⟨"benz-2025", "(32a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Beobachtung des Nachthimmels dauerte drei Stunden"
    glossedTokens := [("Die", "the"), ("Beobacht-ung", "observe-NMLZ"), ("des", "the.GEN"), ("Nachthimmels", "night.sky"), ("dauerte", "took"), ("drei", "three"), ("Stunden", "hours")]
    glossedWords := [⟨['D', 'i', 'e'], ['t', 'h', 'e'], [⟨['D', 'i', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['B', 'e', 'o', 'b', 'a', 'c', 'h', 't', '-', 'u', 'n', 'g'], ['o', 'b', 's', 'e', 'r', 'v', 'e', '-', 'N', 'M', 'L', 'Z'], [⟨['B', 'e', 'o', 'b', 'a', 'c', 'h', 't'], ['o', 'b', 's', 'e', 'r', 'v', 'e'], none⟩, ⟨['u', 'n', 'g'], ['N', 'M', 'L', 'Z'], some '-'⟩]⟩, ⟨['d', 'e', 's'], ['t', 'h', 'e', '.', 'G', 'E', 'N'], [⟨['d', 'e', 's'], ['t', 'h', 'e', '.', 'G', 'E', 'N'], none⟩]⟩, ⟨['N', 'a', 'c', 'h', 't', 'h', 'i', 'm', 'm', 'e', 'l', 's'], ['n', 'i', 'g', 'h', 't', '.', 's', 'k', 'y'], [⟨['N', 'a', 'c', 'h', 't', 'h', 'i', 'm', 'm', 'e', 'l', 's'], ['n', 'i', 'g', 'h', 't', '.', 's', 'k', 'y'], none⟩]⟩, ⟨['d', 'a', 'u', 'e', 'r', 't', 'e'], ['t', 'o', 'o', 'k'], [⟨['d', 'a', 'u', 'e', 'r', 't', 'e'], ['t', 'o', 'o', 'k'], none⟩]⟩, ⟨['d', 'r', 'e', 'i'], ['t', 'h', 'r', 'e', 'e'], [⟨['d', 'r', 'e', 'i'], ['t', 'h', 'r', 'e', 'e'], none⟩]⟩, ⟨['S', 't', 'u', 'n', 'd', 'e', 'n'], ['h', 'o', 'u', 'r', 's'], [⟨['S', 't', 'u', 'n', 'd', 'e', 'n'], ['h', 'o', 'u', 'r', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reading", "Event"), ("duration_predicate", "yes"), ("plural", "no"), ("cp_complement", "no")] }

def ex32b : Datum :=
  { id := "benz2025_ex32b"
    source := ⟨"benz-2025", "(32b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Beobachtungen der Astronomin sind für immer verloren"
    glossedTokens := [("Die", "the"), ("Beobacht-ung-en", "observe-NMLZ-PL"), ("der", "the.GEN"), ("Astronomin", "astronomer"), ("sind", "are"), ("für", "for"), ("immer", "ever"), ("verloren", "lost")]
    glossedWords := [⟨['D', 'i', 'e'], ['t', 'h', 'e'], [⟨['D', 'i', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['B', 'e', 'o', 'b', 'a', 'c', 'h', 't', '-', 'u', 'n', 'g', '-', 'e', 'n'], ['o', 'b', 's', 'e', 'r', 'v', 'e', '-', 'N', 'M', 'L', 'Z', '-', 'P', 'L'], [⟨['B', 'e', 'o', 'b', 'a', 'c', 'h', 't'], ['o', 'b', 's', 'e', 'r', 'v', 'e'], none⟩, ⟨['u', 'n', 'g'], ['N', 'M', 'L', 'Z'], some '-'⟩, ⟨['e', 'n'], ['P', 'L'], some '-'⟩]⟩, ⟨['d', 'e', 'r'], ['t', 'h', 'e', '.', 'G', 'E', 'N'], [⟨['d', 'e', 'r'], ['t', 'h', 'e', '.', 'G', 'E', 'N'], none⟩]⟩, ⟨['A', 's', 't', 'r', 'o', 'n', 'o', 'm', 'i', 'n'], ['a', 's', 't', 'r', 'o', 'n', 'o', 'm', 'e', 'r'], [⟨['A', 's', 't', 'r', 'o', 'n', 'o', 'm', 'i', 'n'], ['a', 's', 't', 'r', 'o', 'n', 'o', 'm', 'e', 'r'], none⟩]⟩, ⟨['s', 'i', 'n', 'd'], ['a', 'r', 'e'], [⟨['s', 'i', 'n', 'd'], ['a', 'r', 'e'], none⟩]⟩, ⟨['f', 'ü', 'r'], ['f', 'o', 'r'], [⟨['f', 'ü', 'r'], ['f', 'o', 'r'], none⟩]⟩, ⟨['i', 'm', 'm', 'e', 'r'], ['e', 'v', 'e', 'r'], [⟨['i', 'm', 'm', 'e', 'r'], ['e', 'v', 'e', 'r'], none⟩]⟩, ⟨['v', 'e', 'r', 'l', 'o', 'r', 'e', 'n'], ['l', 'o', 's', 't'], [⟨['v', 'e', 'r', 'l', 'o', 'r', 'e', 'n'], ['l', 'o', 's', 't'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("concrete object", .acceptable), ("result", .acceptable), ("content", .acceptable)]
    paperFeatures := [("reading", "RN"), ("duration_predicate", "no"), ("plural", "yes"), ("cp_complement", "no")] }

def ex32c : Datum :=
  { id := "benz2025_ex32c"
    source := ⟨"benz-2025", "(32c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Seine Beobachtung, dass Planeten sich bewegen, veränderte die Wissenschaft"
    glossedTokens := [("Seine", "his"), ("Beobacht-ung", "observe-NMLZ"), ("dass", "COMP"), ("Planeten", "planets"), ("sich", "REFL"), ("bewegen", "move"), ("veränderte", "changed"), ("die", "the"), ("Wissenschaft", "science")]
    glossedWords := [⟨['S', 'e', 'i', 'n', 'e'], ['h', 'i', 's'], [⟨['S', 'e', 'i', 'n', 'e'], ['h', 'i', 's'], none⟩]⟩, ⟨['B', 'e', 'o', 'b', 'a', 'c', 'h', 't', '-', 'u', 'n', 'g'], ['o', 'b', 's', 'e', 'r', 'v', 'e', '-', 'N', 'M', 'L', 'Z'], [⟨['B', 'e', 'o', 'b', 'a', 'c', 'h', 't'], ['o', 'b', 's', 'e', 'r', 'v', 'e'], none⟩, ⟨['u', 'n', 'g'], ['N', 'M', 'L', 'Z'], some '-'⟩]⟩, ⟨['d', 'a', 's', 's'], ['C', 'O', 'M', 'P'], [⟨['d', 'a', 's', 's'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['P', 'l', 'a', 'n', 'e', 't', 'e', 'n'], ['p', 'l', 'a', 'n', 'e', 't', 's'], [⟨['P', 'l', 'a', 'n', 'e', 't', 'e', 'n'], ['p', 'l', 'a', 'n', 'e', 't', 's'], none⟩]⟩, ⟨['s', 'i', 'c', 'h'], ['R', 'E', 'F', 'L'], [⟨['s', 'i', 'c', 'h'], ['R', 'E', 'F', 'L'], none⟩]⟩, ⟨['b', 'e', 'w', 'e', 'g', 'e', 'n'], ['m', 'o', 'v', 'e'], [⟨['b', 'e', 'w', 'e', 'g', 'e', 'n'], ['m', 'o', 'v', 'e'], none⟩]⟩, ⟨['v', 'e', 'r', 'ä', 'n', 'd', 'e', 'r', 't', 'e'], ['c', 'h', 'a', 'n', 'g', 'e', 'd'], [⟨['v', 'e', 'r', 'ä', 'n', 'd', 'e', 'r', 't', 'e'], ['c', 'h', 'a', 'n', 'g', 'e', 'd'], none⟩]⟩, ⟨['d', 'i', 'e'], ['t', 'h', 'e'], [⟨['d', 'i', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['W', 'i', 's', 's', 'e', 'n', 's', 'c', 'h', 'a', 'f', 't'], ['s', 'c', 'i', 'e', 'n', 'c', 'e'], [⟨['W', 'i', 's', 's', 'e', 'n', 's', 'c', 'h', 'a', 'f', 't'], ['s', 'c', 'i', 'e', 'n', 'c', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reading", "Content"), ("duration_predicate", "no"), ("plural", "no"), ("cp_complement", "yes")] }

def ex89a : Datum :=
  { id := "benz2025_ex89a"
    source := ⟨"benz-2025", "(89a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Er hämmerte das Metall platt"
    glossedTokens := [("Er", "he"), ("hämmerte", "hammered"), ("das", "the.ACC"), ("Metall", "metal"), ("platt", "flat")]
    glossedWords := [⟨['E', 'r'], ['h', 'e'], [⟨['E', 'r'], ['h', 'e'], none⟩]⟩, ⟨['h', 'ä', 'm', 'm', 'e', 'r', 't', 'e'], ['h', 'a', 'm', 'm', 'e', 'r', 'e', 'd'], [⟨['h', 'ä', 'm', 'm', 'e', 'r', 't', 'e'], ['h', 'a', 'm', 'm', 'e', 'r', 'e', 'd'], none⟩]⟩, ⟨['d', 'a', 's'], ['t', 'h', 'e', '.', 'A', 'C', 'C'], [⟨['d', 'a', 's'], ['t', 'h', 'e', '.', 'A', 'C', 'C'], none⟩]⟩, ⟨['M', 'e', 't', 'a', 'l', 'l'], ['m', 'e', 't', 'a', 'l'], [⟨['M', 'e', 't', 'a', 'l', 'l'], ['m', 'e', 't', 'a', 'l'], none⟩]⟩, ⟨['p', 'l', 'a', 't', 't'], ['f', 'l', 'a', 't'], [⟨['p', 'l', 'a', 't', 't'], ['f', 'l', 'a', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb_class", "transitive"), ("m_predicate", "hämmern"), ("r_predicate", "platt")] }

def ex89b : Datum :=
  { id := "benz2025_ex89b"
    source := ⟨"benz-2025", "(89b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Er schießt seinen Gegner tot"
    glossedTokens := [("Er", "he"), ("schießt", "shoots"), ("seinen", "his.ACC"), ("Gegner", "opponent"), ("tot", "dead")]
    glossedWords := [⟨['E', 'r'], ['h', 'e'], [⟨['E', 'r'], ['h', 'e'], none⟩]⟩, ⟨['s', 'c', 'h', 'i', 'e', 'ß', 't'], ['s', 'h', 'o', 'o', 't', 's'], [⟨['s', 'c', 'h', 'i', 'e', 'ß', 't'], ['s', 'h', 'o', 'o', 't', 's'], none⟩]⟩, ⟨['s', 'e', 'i', 'n', 'e', 'n'], ['h', 'i', 's', '.', 'A', 'C', 'C'], [⟨['s', 'e', 'i', 'n', 'e', 'n'], ['h', 'i', 's', '.', 'A', 'C', 'C'], none⟩]⟩, ⟨['G', 'e', 'g', 'n', 'e', 'r'], ['o', 'p', 'p', 'o', 'n', 'e', 'n', 't'], [⟨['G', 'e', 'g', 'n', 'e', 'r'], ['o', 'p', 'p', 'o', 'n', 'e', 'n', 't'], none⟩]⟩, ⟨['t', 'o', 't'], ['d', 'e', 'a', 'd'], [⟨['t', 'o', 't'], ['d', 'e', 'a', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb_class", "transitive"), ("m_predicate", "schießen"), ("r_predicate", "tot")] }

def ex115a : Datum :=
  { id := "benz2025_ex115a"
    source := ⟨"creemers-2020", ""⟩
    reportedIn := some ⟨"benz-2025", "(115a)"⟩
    language := "stan1295"
    primaryText := "Hans hat den Stock kaputt gebrochen"
    glossedTokens := [("Hans", "Hans"), ("hat", "has"), ("den", "the.ACC"), ("Stock", "stick"), ("kaputt", "broken"), ("gebrochen", "broken.PTCP")]
    glossedWords := [⟨['H', 'a', 'n', 's'], ['H', 'a', 'n', 's'], [⟨['H', 'a', 'n', 's'], ['H', 'a', 'n', 's'], none⟩]⟩, ⟨['h', 'a', 't'], ['h', 'a', 's'], [⟨['h', 'a', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['d', 'e', 'n'], ['t', 'h', 'e', '.', 'A', 'C', 'C'], [⟨['d', 'e', 'n'], ['t', 'h', 'e', '.', 'A', 'C', 'C'], none⟩]⟩, ⟨['S', 't', 'o', 'c', 'k'], ['s', 't', 'i', 'c', 'k'], [⟨['S', 't', 'o', 'c', 'k'], ['s', 't', 'i', 'c', 'k'], none⟩]⟩, ⟨['k', 'a', 'p', 'u', 't', 't'], ['b', 'r', 'o', 'k', 'e', 'n'], [⟨['k', 'a', 'p', 'u', 't', 't'], ['b', 'r', 'o', 'k', 'e', 'n'], none⟩]⟩, ⟨['g', 'e', 'b', 'r', 'o', 'c', 'h', 'e', 'n'], ['b', 'r', 'o', 'k', 'e', 'n', '.', 'P', 'T', 'C', 'P'], [⟨['g', 'e', 'b', 'r', 'o', 'c', 'h', 'e', 'n'], ['b', 'r', 'o', 'k', 'e', 'n', '.', 'P', 'T', 'C', 'P'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb_class", "obligatorily transitive"), ("m_predicate", "brechen"), ("r_predicate", "kaputt")] }

def ex115e : Datum :=
  { id := "benz2025_ex115e"
    source := ⟨"creemers-2020", ""⟩
    reportedIn := some ⟨"benz-2025", "(115e)"⟩
    language := "stan1295"
    primaryText := "Das Wasser fror fest"
    glossedTokens := [("Das", "the.NOM"), ("Wasser", "water"), ("fror", "froze"), ("fest", "solid")]
    glossedWords := [⟨['D', 'a', 's'], ['t', 'h', 'e', '.', 'N', 'O', 'M'], [⟨['D', 'a', 's'], ['t', 'h', 'e', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['W', 'a', 's', 's', 'e', 'r'], ['w', 'a', 't', 'e', 'r'], [⟨['W', 'a', 's', 's', 'e', 'r'], ['w', 'a', 't', 'e', 'r'], none⟩]⟩, ⟨['f', 'r', 'o', 'r'], ['f', 'r', 'o', 'z', 'e'], [⟨['f', 'r', 'o', 'r'], ['f', 'r', 'o', 'z', 'e'], none⟩]⟩, ⟨['f', 'e', 's', 't'], ['s', 'o', 'l', 'i', 'd'], [⟨['f', 'e', 's', 't'], ['s', 'o', 'l', 'i', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb_class", "unaccusative"), ("m_predicate", "frieren"), ("r_predicate", "fest")] }

def ex115f : Datum :=
  { id := "benz2025_ex115f"
    source := ⟨"creemers-2020", ""⟩
    reportedIn := some ⟨"benz-2025", "(115f)"⟩
    language := "stan1295"
    primaryText := "Sie haben sich krank/tot geschämt"
    glossedTokens := [("Sie", "they"), ("haben", "have"), ("sich", "REFL"), ("krank/tot", "sick/dead"), ("geschämt", "shamed.PTCP")]
    glossedWords := [⟨['S', 'i', 'e'], ['t', 'h', 'e', 'y'], [⟨['S', 'i', 'e'], ['t', 'h', 'e', 'y'], none⟩]⟩, ⟨['h', 'a', 'b', 'e', 'n'], ['h', 'a', 'v', 'e'], [⟨['h', 'a', 'b', 'e', 'n'], ['h', 'a', 'v', 'e'], none⟩]⟩, ⟨['s', 'i', 'c', 'h'], ['R', 'E', 'F', 'L'], [⟨['s', 'i', 'c', 'h'], ['R', 'E', 'F', 'L'], none⟩]⟩, ⟨['k', 'r', 'a', 'n', 'k', '/', 't', 'o', 't'], ['s', 'i', 'c', 'k', '/', 'd', 'e', 'a', 'd'], [⟨['k', 'r', 'a', 'n', 'k', '/', 't', 'o', 't'], ['s', 'i', 'c', 'k', '/', 'd', 'e', 'a', 'd'], none⟩]⟩, ⟨['g', 'e', 's', 'c', 'h', 'ä', 'm', 't'], ['s', 'h', 'a', 'm', 'e', 'd', '.', 'P', 'T', 'C', 'P'], [⟨['g', 'e', 's', 'c', 'h', 'ä', 'm', 't'], ['s', 'h', 'a', 'm', 'e', 'd', '.', 'P', 'T', 'C', 'P'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb_class", "inherently reflexive"), ("m_predicate", "schämen"), ("r_predicate", "krank/tot")] }

def ex87ab : Datum :=
  { id := "benz2025_ex87ab"
    source := ⟨"creemers-2020", ""⟩
    reportedIn := some ⟨"benz-2025", "(87a-b)"⟩
    language := "stan1295"
    primaryText := "Sie haben uns arm geraubt"
    glossedTokens := [("Sie", "they"), ("haben", "have"), ("uns", "us.ACC"), ("arm", "poor"), ("geraubt", "robbed.PTCP")]
    glossedWords := [⟨['S', 'i', 'e'], ['t', 'h', 'e', 'y'], [⟨['S', 'i', 'e'], ['t', 'h', 'e', 'y'], none⟩]⟩, ⟨['h', 'a', 'b', 'e', 'n'], ['h', 'a', 'v', 'e'], [⟨['h', 'a', 'b', 'e', 'n'], ['h', 'a', 'v', 'e'], none⟩]⟩, ⟨['u', 'n', 's'], ['u', 's', '.', 'A', 'C', 'C'], [⟨['u', 'n', 's'], ['u', 's', '.', 'A', 'C', 'C'], none⟩]⟩, ⟨['a', 'r', 'm'], ['p', 'o', 'o', 'r'], [⟨['a', 'r', 'm'], ['p', 'o', 'o', 'r'], none⟩]⟩, ⟨['g', 'e', 'r', 'a', 'u', 'b', 't'], ['r', 'o', 'b', 'b', 'e', 'd', '.', 'P', 'T', 'C', 'P'], [⟨['g', 'e', 'r', 'a', 'u', 'b', 't'], ['r', 'o', 'b', 'b', 'e', 'd', '.', 'P', 'T', 'C', 'P'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Sie haben uns arm be-raubt", .ungrammatical)]
    readings := []
    paperFeatures := [("blocker_type", "prefix"), ("blocker", "be-"), ("r_predicate", "arm"), ("outer", "rsp"), ("inner", "pfx")] }

def ex87cd : Datum :=
  { id := "benz2025_ex87cd"
    source := ⟨"creemers-2020", ""⟩
    reportedIn := some ⟨"benz-2025", "(87c-d)"⟩
    language := "stan1295"
    primaryText := "Sie haben ihn tot geschossen"
    glossedTokens := [("Sie", "they"), ("haben", "have"), ("ihn", "him.ACC"), ("tot", "dead"), ("geschossen", "shot.PTCP")]
    glossedWords := [⟨['S', 'i', 'e'], ['t', 'h', 'e', 'y'], [⟨['S', 'i', 'e'], ['t', 'h', 'e', 'y'], none⟩]⟩, ⟨['h', 'a', 'b', 'e', 'n'], ['h', 'a', 'v', 'e'], [⟨['h', 'a', 'b', 'e', 'n'], ['h', 'a', 'v', 'e'], none⟩]⟩, ⟨['i', 'h', 'n'], ['h', 'i', 'm', '.', 'A', 'C', 'C'], [⟨['i', 'h', 'n'], ['h', 'i', 'm', '.', 'A', 'C', 'C'], none⟩]⟩, ⟨['t', 'o', 't'], ['d', 'e', 'a', 'd'], [⟨['t', 'o', 't'], ['d', 'e', 'a', 'd'], none⟩]⟩, ⟨['g', 'e', 's', 'c', 'h', 'o', 's', 's', 'e', 'n'], ['s', 'h', 'o', 't', '.', 'P', 'T', 'C', 'P'], [⟨['g', 'e', 's', 'c', 'h', 'o', 's', 's', 'e', 'n'], ['s', 'h', 'o', 't', '.', 'P', 'T', 'C', 'P'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Sie haben ihn tot er-schossen", .ungrammatical)]
    readings := []
    paperFeatures := [("blocker_type", "prefix"), ("blocker", "er-"), ("r_predicate", "tot"), ("outer", "rsp"), ("inner", "pfx")] }

def ex87ef : Datum :=
  { id := "benz2025_ex87ef"
    source := ⟨"creemers-2020", ""⟩
    reportedIn := some ⟨"benz-2025", "(87e-f)"⟩
    language := "stan1295"
    primaryText := "Hans hat den Stock kaputt gebrochen"
    glossedTokens := [("Hans", "Hans"), ("hat", "has"), ("den", "the.ACC"), ("Stock", "stick"), ("kaputt", "broken.ADJ"), ("gebrochen", "broken.PTCP")]
    glossedWords := [⟨['H', 'a', 'n', 's'], ['H', 'a', 'n', 's'], [⟨['H', 'a', 'n', 's'], ['H', 'a', 'n', 's'], none⟩]⟩, ⟨['h', 'a', 't'], ['h', 'a', 's'], [⟨['h', 'a', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['d', 'e', 'n'], ['t', 'h', 'e', '.', 'A', 'C', 'C'], [⟨['d', 'e', 'n'], ['t', 'h', 'e', '.', 'A', 'C', 'C'], none⟩]⟩, ⟨['S', 't', 'o', 'c', 'k'], ['s', 't', 'i', 'c', 'k'], [⟨['S', 't', 'o', 'c', 'k'], ['s', 't', 'i', 'c', 'k'], none⟩]⟩, ⟨['k', 'a', 'p', 'u', 't', 't'], ['b', 'r', 'o', 'k', 'e', 'n', '.', 'A', 'D', 'J'], [⟨['k', 'a', 'p', 'u', 't', 't'], ['b', 'r', 'o', 'k', 'e', 'n', '.', 'A', 'D', 'J'], none⟩]⟩, ⟨['g', 'e', 'b', 'r', 'o', 'c', 'h', 'e', 'n'], ['b', 'r', 'o', 'k', 'e', 'n', '.', 'P', 'T', 'C', 'P'], [⟨['g', 'e', 'b', 'r', 'o', 'c', 'h', 'e', 'n'], ['b', 'r', 'o', 'k', 'e', 'n', '.', 'P', 'T', 'C', 'P'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Hans hat den Stock kaputt zer-brochen", .ungrammatical)]
    readings := []
    paperFeatures := [("blocker_type", "prefix"), ("blocker", "zer-"), ("r_predicate", "kaputt"), ("outer", "rsp"), ("inner", "pfx")] }

def ex88ab : Datum :=
  { id := "benz2025_ex88ab"
    source := ⟨"benz-2025", "(88a-b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Sie hat den Tisch trocken gewischt"
    glossedTokens := [("Sie", "she"), ("hat", "has"), ("den", "the.ACC"), ("Tisch", "table"), ("trocken", "dry"), ("gewischt", "wiped.PTCP")]
    glossedWords := [⟨['S', 'i', 'e'], ['s', 'h', 'e'], [⟨['S', 'i', 'e'], ['s', 'h', 'e'], none⟩]⟩, ⟨['h', 'a', 't'], ['h', 'a', 's'], [⟨['h', 'a', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['d', 'e', 'n'], ['t', 'h', 'e', '.', 'A', 'C', 'C'], [⟨['d', 'e', 'n'], ['t', 'h', 'e', '.', 'A', 'C', 'C'], none⟩]⟩, ⟨['T', 'i', 's', 'c', 'h'], ['t', 'a', 'b', 'l', 'e'], [⟨['T', 'i', 's', 'c', 'h'], ['t', 'a', 'b', 'l', 'e'], none⟩]⟩, ⟨['t', 'r', 'o', 'c', 'k', 'e', 'n'], ['d', 'r', 'y'], [⟨['t', 'r', 'o', 'c', 'k', 'e', 'n'], ['d', 'r', 'y'], none⟩]⟩, ⟨['g', 'e', 'w', 'i', 's', 'c', 'h', 't'], ['w', 'i', 'p', 'e', 'd', '.', 'P', 'T', 'C', 'P'], [⟨['g', 'e', 'w', 'i', 's', 'c', 'h', 't'], ['w', 'i', 'p', 'e', 'd', '.', 'P', 'T', 'C', 'P'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Sie hat den Tisch trocken ab-gewischt", .ungrammatical)]
    readings := []
    paperFeatures := [("blocker_type", "particle"), ("blocker", "ab-"), ("r_predicate", "trocken"), ("outer", "rsp"), ("inner", "prt")] }

def ex88cd : Datum :=
  { id := "benz2025_ex88cd"
    source := ⟨"benz-2025", "(88c-d)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Das Baby hat mich nass gespuckt"
    glossedTokens := [("Das", "the"), ("Baby", "baby"), ("hat", "has"), ("mich", "me.ACC"), ("nass", "wet"), ("gespuckt", "spit.PTCP")]
    glossedWords := [⟨['D', 'a', 's'], ['t', 'h', 'e'], [⟨['D', 'a', 's'], ['t', 'h', 'e'], none⟩]⟩, ⟨['B', 'a', 'b', 'y'], ['b', 'a', 'b', 'y'], [⟨['B', 'a', 'b', 'y'], ['b', 'a', 'b', 'y'], none⟩]⟩, ⟨['h', 'a', 't'], ['h', 'a', 's'], [⟨['h', 'a', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['m', 'i', 'c', 'h'], ['m', 'e', '.', 'A', 'C', 'C'], [⟨['m', 'i', 'c', 'h'], ['m', 'e', '.', 'A', 'C', 'C'], none⟩]⟩, ⟨['n', 'a', 's', 's'], ['w', 'e', 't'], [⟨['n', 'a', 's', 's'], ['w', 'e', 't'], none⟩]⟩, ⟨['g', 'e', 's', 'p', 'u', 'c', 'k', 't'], ['s', 'p', 'i', 't', '.', 'P', 'T', 'C', 'P'], [⟨['g', 'e', 's', 'p', 'u', 'c', 'k', 't'], ['s', 'p', 'i', 't', '.', 'P', 'T', 'C', 'P'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Das Baby hat mich nass an-gespuckt", .ungrammatical)]
    readings := []
    paperFeatures := [("blocker_type", "particle"), ("blocker", "an-"), ("r_predicate", "nass"), ("outer", "rsp"), ("inner", "prt")] }

def ex81a : Datum :=
  { id := "benz2025_ex81a"
    source := ⟨"benz-2025", "(81a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "ent-ver-trauen"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("outer", "pfx"), ("inner", "pfx")] }

def ex82a : Datum :=
  { id := "benz2025_ex82a"
    source := ⟨"benz-2025", "(82a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "rad-ein-fahren"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("outer", "prt"), ("inner", "prt")] }

def ex83a : Datum :=
  { id := "benz2025_ex83a"
    source := ⟨"benz-2025", "(83a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "zer-ab-schneiden"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("outer", "pfx"), ("inner", "prt")] }

def ex84a : Datum :=
  { id := "benz2025_ex84a"
    source := ⟨"benz-2025", "(84a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "aus-er-wählen"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("outer", "prt"), ("inner", "pfx")] }

def ex86b : Datum :=
  { id := "benz2025_ex86b"
    source := ⟨"benz-2025", "(86b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Sie hat sich kaputt müde gearbeitet"
    glossedTokens := [("Sie", "she"), ("hat", "has"), ("sich", "REFL"), ("kaputt", "broken"), ("müde", "tired"), ("gearbeitet", "worked.PTCP")]
    glossedWords := [⟨['S', 'i', 'e'], ['s', 'h', 'e'], [⟨['S', 'i', 'e'], ['s', 'h', 'e'], none⟩]⟩, ⟨['h', 'a', 't'], ['h', 'a', 's'], [⟨['h', 'a', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['s', 'i', 'c', 'h'], ['R', 'E', 'F', 'L'], [⟨['s', 'i', 'c', 'h'], ['R', 'E', 'F', 'L'], none⟩]⟩, ⟨['k', 'a', 'p', 'u', 't', 't'], ['b', 'r', 'o', 'k', 'e', 'n'], [⟨['k', 'a', 'p', 'u', 't', 't'], ['b', 'r', 'o', 'k', 'e', 'n'], none⟩]⟩, ⟨['m', 'ü', 'd', 'e'], ['t', 'i', 'r', 'e', 'd'], [⟨['m', 'ü', 'd', 'e'], ['t', 'i', 'r', 'e', 'd'], none⟩]⟩, ⟨['g', 'e', 'a', 'r', 'b', 'e', 'i', 't', 'e', 't'], ['w', 'o', 'r', 'k', 'e', 'd', '.', 'P', 'T', 'C', 'P'], [⟨['g', 'e', 'a', 'r', 'b', 'e', 'i', 't', 'e', 't'], ['w', 'o', 'r', 'k', 'e', 'd', '.', 'P', 'T', 'C', 'P'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("outer", "rsp"), ("inner", "rsp")] }

def ex193a : Datum :=
  { id := "benz2025_ex193a"
    source := ⟨"benz-2025", "(193a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "das Ver-kaufen"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("nominalization", "infinitive"), ("element", "pfx"), ("verb", "verkaufen")] }

def ex193b : Datum :=
  { id := "benz2025_ex193b"
    source := ⟨"benz-2025", "(193b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "das Ein-führen"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("nominalization", "infinitive"), ("element", "prt"), ("verb", "einführen")] }

def ex193c : Datum :=
  { id := "benz2025_ex193c"
    source := ⟨"benz-2025", "(193c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "das Wach-küssen"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("nominalization", "infinitive"), ("element", "rsp"), ("verb", "küssen")] }

def ex197a : Datum :=
  { id := "benz2025_ex197a"
    source := ⟨"benz-2025", "(197a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Ein-führ-ung"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("nominalization", "ung"), ("element", "prt"), ("verb", "einführen")] }

def ex198c : Datum :=
  { id := "benz2025_ex198c"
    source := ⟨"benz-2025", "(198c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Be-mal-ung"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("nominalization", "ung"), ("element", "pfx"), ("verb", "bemalen")] }

def ex198c_base : Datum :=
  { id := "benz2025_ex198c_base"
    source := ⟨"benz-2025", "(198c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Mal-ung"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("nominalization", "ung"), ("element", "none"), ("verb", "malen")] }

def ex204a : Datum :=
  { id := "benz2025_ex204a"
    source := ⟨"benz-2025", "(204a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Platt-hämmer-ung"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("nominalization", "ung"), ("element", "rsp"), ("verb", "hämmern")] }

def ex204c : Datum :=
  { id := "benz2025_ex204c"
    source := ⟨"benz-2025", "(204c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wach-küss-ung"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("nominalization", "ung"), ("element", "rsp"), ("verb", "küssen")] }

def ex212a : Datum :=
  { id := "benz2025_ex212a"
    source := ⟨"benz-2025", "(212a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "das Herum-ge-renn-e"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("nominalization", "geE"), ("element", "prt"), ("verb", "rennen")] }

def ex216a : Datum :=
  { id := "benz2025_ex216a"
    source := ⟨"benz-2025", "(216a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "das Wach-ge-küss-e"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("nominalization", "geE"), ("element", "rsp"), ("verb", "küssen")] }

def ex216b : Datum :=
  { id := "benz2025_ex216b"
    source := ⟨"benz-2025", "(216b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "das Platt-ge-hämmer-e"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("nominalization", "geE"), ("element", "rsp"), ("verb", "hämmern")] }

def ex218c : Datum :=
  { id := "benz2025_ex218c"
    source := ⟨"benz-2025", "(218c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Ge-be-mal-e"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("nominalization", "geE"), ("element", "pfx"), ("verb", "bemalen")] }

def all : List Datum := [ex32a, ex32b, ex32c, ex89a, ex89b, ex115a, ex115e, ex115f, ex87ab, ex87cd, ex87ef, ex88ab, ex88cd, ex81a, ex82a, ex83a, ex84a, ex86b, ex193a, ex193b, ex193c, ex197a, ex198c, ex198c_base, ex204a, ex204c, ex212a, ex216a, ex216b, ex218c]

end Benz2025.Examples
