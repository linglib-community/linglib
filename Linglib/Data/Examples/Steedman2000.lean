module

public import Linglib.Data.Examples.Schema

/-!
# `Steedman2000` — typed example data

Auto-generated from `Linglib/Data/Examples/Steedman2000.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Steedman2000.Examples`.
-/

@[expose] public section

namespace Steedman2000.Examples

def ex_96 : Datum :=
  { id := "steedman2000_96"
    source := ⟨"steedman-2000", "ch. 6 (96)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "(Weil) irgendjemand auf jeden gespannt ist."
    glossedTokens := [("(Weil)", "(since)"), ("irgendjemand", "someone"), ("auf", "on"), ("jeden", "everybody"), ("gespannt", "curious"), ("ist", "is")]
    glossedWords := [⟨['(', 'W', 'e', 'i', 'l', ')'], ['(', 's', 'i', 'n', 'c', 'e', ')'], [⟨['W', 'e', 'i', 'l'], ['(', 's', 'i', 'n', 'c', 'e', ')'], none⟩]⟩, ⟨['i', 'r', 'g', 'e', 'n', 'd', 'j', 'e', 'm', 'a', 'n', 'd'], ['s', 'o', 'm', 'e', 'o', 'n', 'e'], [⟨['i', 'r', 'g', 'e', 'n', 'd', 'j', 'e', 'm', 'a', 'n', 'd'], ['s', 'o', 'm', 'e', 'o', 'n', 'e'], none⟩]⟩, ⟨['a', 'u', 'f'], ['o', 'n'], [⟨['a', 'u', 'f'], ['o', 'n'], none⟩]⟩, ⟨['j', 'e', 'd', 'e', 'n'], ['e', 'v', 'e', 'r', 'y', 'b', 'o', 'd', 'y'], [⟨['j', 'e', 'd', 'e', 'n'], ['e', 'v', 'e', 'r', 'y', 'b', 'o', 'd', 'y'], none⟩]⟩, ⟨['g', 'e', 's', 'p', 'a', 'n', 'n', 't'], ['c', 'u', 'r', 'i', 'o', 'u', 's'], [⟨['g', 'e', 's', 'p', 'a', 'n', 'n', 't'], ['c', 'u', 'r', 'i', 'o', 'u', 's'], none⟩]⟩, ⟨['i', 's', 't'], ['i', 's'], [⟨['i', 's', 't'], ['i', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "German verb-final subordinate clause; the quantified PP precedes the predicate-tense cluster."
    judgment := .acceptable
    contrasts := []
    readings := [("surface", .acceptable), ("inverse", .acceptable)]
    paperFeatures := [("wordOrder", "verbRaising")] }

def ex_97 : Datum :=
  { id := "steedman2000_97"
    source := ⟨"steedman-2000", "ch. 6 (97)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "(Weil) jemand versucht hat jeden reinzulegen."
    glossedTokens := [("(Weil)", "(since)"), ("jemand", "someone"), ("versucht", "tried"), ("hat", "has"), ("jeden", "everyone"), ("reinzulegen", "cheat")]
    glossedWords := [⟨['(', 'W', 'e', 'i', 'l', ')'], ['(', 's', 'i', 'n', 'c', 'e', ')'], [⟨['W', 'e', 'i', 'l'], ['(', 's', 'i', 'n', 'c', 'e', ')'], none⟩]⟩, ⟨['j', 'e', 'm', 'a', 'n', 'd'], ['s', 'o', 'm', 'e', 'o', 'n', 'e'], [⟨['j', 'e', 'm', 'a', 'n', 'd'], ['s', 'o', 'm', 'e', 'o', 'n', 'e'], none⟩]⟩, ⟨['v', 'e', 'r', 's', 'u', 'c', 'h', 't'], ['t', 'r', 'i', 'e', 'd'], [⟨['v', 'e', 'r', 's', 'u', 'c', 'h', 't'], ['t', 'r', 'i', 'e', 'd'], none⟩]⟩, ⟨['h', 'a', 't'], ['h', 'a', 's'], [⟨['h', 'a', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['j', 'e', 'd', 'e', 'n'], ['e', 'v', 'e', 'r', 'y', 'o', 'n', 'e'], [⟨['j', 'e', 'd', 'e', 'n'], ['e', 'v', 'e', 'r', 'y', 'o', 'n', 'e'], none⟩]⟩, ⟨['r', 'e', 'i', 'n', 'z', 'u', 'l', 'e', 'g', 'e', 'n'], ['c', 'h', 'e', 'a', 't'], [⟨['r', 'e', 'i', 'n', 'z', 'u', 'l', 'e', 'g', 'e', 'n'], ['c', 'h', 'e', 'a', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "German verb-final subordinate clause; the quantified object follows the matrix verb cluster."
    judgment := .acceptable
    contrasts := []
    readings := [("surface", .acceptable), ("inverse", .unacceptable)]
    paperFeatures := [("wordOrder", "verbProjectionRaising")] }

def ex_98a : Datum :=
  { id := "steedman2000_98a"
    source := ⟨"steedman-2000", "ch. 6 (98a)"⟩
    reportedIn := none
    language := "vlaa1240"
    primaryText := "(da) Jan vee boeken hee willen lezen"
    glossedTokens := [("(da)", "(that)"), ("Jan", "Jan"), ("vee", "many"), ("boeken", "books"), ("hee", "has"), ("willen", "wanted"), ("lezen", "read")]
    glossedWords := [⟨['(', 'd', 'a', ')'], ['(', 't', 'h', 'a', 't', ')'], [⟨['d', 'a'], ['(', 't', 'h', 'a', 't', ')'], none⟩]⟩, ⟨['J', 'a', 'n'], ['J', 'a', 'n'], [⟨['J', 'a', 'n'], ['J', 'a', 'n'], none⟩]⟩, ⟨['v', 'e', 'e'], ['m', 'a', 'n', 'y'], [⟨['v', 'e', 'e'], ['m', 'a', 'n', 'y'], none⟩]⟩, ⟨['b', 'o', 'e', 'k', 'e', 'n'], ['b', 'o', 'o', 'k', 's'], [⟨['b', 'o', 'e', 'k', 'e', 'n'], ['b', 'o', 'o', 'k', 's'], none⟩]⟩, ⟨['h', 'e', 'e'], ['h', 'a', 's'], [⟨['h', 'e', 'e'], ['h', 'a', 's'], none⟩]⟩, ⟨['w', 'i', 'l', 'l', 'e', 'n'], ['w', 'a', 'n', 't', 'e', 'd'], [⟨['w', 'i', 'l', 'l', 'e', 'n'], ['w', 'a', 'n', 't', 'e', 'd'], none⟩]⟩, ⟨['l', 'e', 'z', 'e', 'n'], ['r', 'e', 'a', 'd'], [⟨['l', 'e', 'z', 'e', 'n'], ['r', 'e', 'a', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "West Flemish subordinate clause in the verb-raising word order."
    judgment := .acceptable
    contrasts := []
    readings := [("surface", .acceptable), ("inverse", .acceptable)]
    paperFeatures := [("wordOrder", "verbRaising")] }

def ex_98b : Datum :=
  { id := "steedman2000_98b"
    source := ⟨"steedman-2000", "ch. 6 (98b)"⟩
    reportedIn := none
    language := "vlaa1240"
    primaryText := "(da) Jan hee willen vee boeken lezen"
    glossedTokens := [("(da)", "(that)"), ("Jan", "Jan"), ("hee", "has"), ("willen", "wanted"), ("vee", "many"), ("boeken", "books"), ("lezen", "read")]
    glossedWords := [⟨['(', 'd', 'a', ')'], ['(', 't', 'h', 'a', 't', ')'], [⟨['d', 'a'], ['(', 't', 'h', 'a', 't', ')'], none⟩]⟩, ⟨['J', 'a', 'n'], ['J', 'a', 'n'], [⟨['J', 'a', 'n'], ['J', 'a', 'n'], none⟩]⟩, ⟨['h', 'e', 'e'], ['h', 'a', 's'], [⟨['h', 'e', 'e'], ['h', 'a', 's'], none⟩]⟩, ⟨['w', 'i', 'l', 'l', 'e', 'n'], ['w', 'a', 'n', 't', 'e', 'd'], [⟨['w', 'i', 'l', 'l', 'e', 'n'], ['w', 'a', 'n', 't', 'e', 'd'], none⟩]⟩, ⟨['v', 'e', 'e'], ['m', 'a', 'n', 'y'], [⟨['v', 'e', 'e'], ['m', 'a', 'n', 'y'], none⟩]⟩, ⟨['b', 'o', 'e', 'k', 'e', 'n'], ['b', 'o', 'o', 'k', 's'], [⟨['b', 'o', 'e', 'k', 'e', 'n'], ['b', 'o', 'o', 'k', 's'], none⟩]⟩, ⟨['l', 'e', 'z', 'e', 'n'], ['r', 'e', 'a', 'd'], [⟨['l', 'e', 'z', 'e', 'n'], ['r', 'e', 'a', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "West Flemish subordinate clause in the verb-projection-raising word order."
    judgment := .acceptable
    contrasts := []
    readings := [("surface", .acceptable), ("inverse", .unacceptable)]
    paperFeatures := [("wordOrder", "verbProjectionRaising")] }

def ex_99a : Datum :=
  { id := "steedman2000_99a"
    source := ⟨"steedman-2000", "ch. 6 (99a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "(omdat) Jan veel liederen probeert te zingen"
    glossedTokens := [("(omdat)", "(because)"), ("Jan", "Jan"), ("veel", "many"), ("liederen", "songs"), ("probeert", "tries"), ("te", "to"), ("zingen", "sing")]
    glossedWords := [⟨['(', 'o', 'm', 'd', 'a', 't', ')'], ['(', 'b', 'e', 'c', 'a', 'u', 's', 'e', ')'], [⟨['o', 'm', 'd', 'a', 't'], ['(', 'b', 'e', 'c', 'a', 'u', 's', 'e', ')'], none⟩]⟩, ⟨['J', 'a', 'n'], ['J', 'a', 'n'], [⟨['J', 'a', 'n'], ['J', 'a', 'n'], none⟩]⟩, ⟨['v', 'e', 'e', 'l'], ['m', 'a', 'n', 'y'], [⟨['v', 'e', 'e', 'l'], ['m', 'a', 'n', 'y'], none⟩]⟩, ⟨['l', 'i', 'e', 'd', 'e', 'r', 'e', 'n'], ['s', 'o', 'n', 'g', 's'], [⟨['l', 'i', 'e', 'd', 'e', 'r', 'e', 'n'], ['s', 'o', 'n', 'g', 's'], none⟩]⟩, ⟨['p', 'r', 'o', 'b', 'e', 'e', 'r', 't'], ['t', 'r', 'i', 'e', 's'], [⟨['p', 'r', 'o', 'b', 'e', 'e', 'r', 't'], ['t', 'r', 'i', 'e', 's'], none⟩]⟩, ⟨['t', 'e'], ['t', 'o'], [⟨['t', 'e'], ['t', 'o'], none⟩]⟩, ⟨['z', 'i', 'n', 'g', 'e', 'n'], ['s', 'i', 'n', 'g'], [⟨['z', 'i', 'n', 'g', 'e', 'n'], ['s', 'i', 'n', 'g'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Dutch subordinate clause with an equi verb, verb-raising word order."
    judgment := .acceptable
    contrasts := []
    readings := [("surface", .acceptable), ("inverse", .acceptable)]
    paperFeatures := [("wordOrder", "verbRaising")] }

def ex_99b : Datum :=
  { id := "steedman2000_99b"
    source := ⟨"steedman-2000", "ch. 6 (99b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "(omdat) Jan probeert veel liederen te zingen"
    glossedTokens := [("(omdat)", "(because)"), ("Jan", "Jan"), ("probeert", "tries"), ("veel", "many"), ("liederen", "songs"), ("te", "to"), ("zingen", "sing")]
    glossedWords := [⟨['(', 'o', 'm', 'd', 'a', 't', ')'], ['(', 'b', 'e', 'c', 'a', 'u', 's', 'e', ')'], [⟨['o', 'm', 'd', 'a', 't'], ['(', 'b', 'e', 'c', 'a', 'u', 's', 'e', ')'], none⟩]⟩, ⟨['J', 'a', 'n'], ['J', 'a', 'n'], [⟨['J', 'a', 'n'], ['J', 'a', 'n'], none⟩]⟩, ⟨['p', 'r', 'o', 'b', 'e', 'e', 'r', 't'], ['t', 'r', 'i', 'e', 's'], [⟨['p', 'r', 'o', 'b', 'e', 'e', 'r', 't'], ['t', 'r', 'i', 'e', 's'], none⟩]⟩, ⟨['v', 'e', 'e', 'l'], ['m', 'a', 'n', 'y'], [⟨['v', 'e', 'e', 'l'], ['m', 'a', 'n', 'y'], none⟩]⟩, ⟨['l', 'i', 'e', 'd', 'e', 'r', 'e', 'n'], ['s', 'o', 'n', 'g', 's'], [⟨['l', 'i', 'e', 'd', 'e', 'r', 'e', 'n'], ['s', 'o', 'n', 'g', 's'], none⟩]⟩, ⟨['t', 'e'], ['t', 'o'], [⟨['t', 'e'], ['t', 'o'], none⟩]⟩, ⟨['z', 'i', 'n', 'g', 'e', 'n'], ['s', 'i', 'n', 'g'], [⟨['z', 'i', 'n', 'g', 'e', 'n'], ['s', 'i', 'n', 'g'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Dutch subordinate clause with an equi verb, verb-projection-raising word order."
    judgment := .acceptable
    contrasts := []
    readings := [("surface", .acceptable), ("inverse", .unacceptable)]
    paperFeatures := [("wordOrder", "verbProjectionRaising")] }

def ex_100a : Datum :=
  { id := "steedman2000_100a"
    source := ⟨"steedman-2000", "ch. 6 (100a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "(omdat) iemand alle liederen probeert te zingen"
    glossedTokens := [("(omdat)", "(because)"), ("iemand", "someone"), ("alle", "every"), ("liederen", "song"), ("probeert", "tries"), ("te", "to"), ("zingen", "sing")]
    glossedWords := [⟨['(', 'o', 'm', 'd', 'a', 't', ')'], ['(', 'b', 'e', 'c', 'a', 'u', 's', 'e', ')'], [⟨['o', 'm', 'd', 'a', 't'], ['(', 'b', 'e', 'c', 'a', 'u', 's', 'e', ')'], none⟩]⟩, ⟨['i', 'e', 'm', 'a', 'n', 'd'], ['s', 'o', 'm', 'e', 'o', 'n', 'e'], [⟨['i', 'e', 'm', 'a', 'n', 'd'], ['s', 'o', 'm', 'e', 'o', 'n', 'e'], none⟩]⟩, ⟨['a', 'l', 'l', 'e'], ['e', 'v', 'e', 'r', 'y'], [⟨['a', 'l', 'l', 'e'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['l', 'i', 'e', 'd', 'e', 'r', 'e', 'n'], ['s', 'o', 'n', 'g'], [⟨['l', 'i', 'e', 'd', 'e', 'r', 'e', 'n'], ['s', 'o', 'n', 'g'], none⟩]⟩, ⟨['p', 'r', 'o', 'b', 'e', 'e', 'r', 't'], ['t', 'r', 'i', 'e', 's'], [⟨['p', 'r', 'o', 'b', 'e', 'e', 'r', 't'], ['t', 'r', 'i', 'e', 's'], none⟩]⟩, ⟨['t', 'e'], ['t', 'o'], [⟨['t', 'e'], ['t', 'o'], none⟩]⟩, ⟨['z', 'i', 'n', 'g', 'e', 'n'], ['s', 'i', 'n', 'g'], [⟨['z', 'i', 'n', 'g', 'e', 'n'], ['s', 'i', 'n', 'g'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Dutch subordinate clause, verb-raising word order, two quantified arguments."
    judgment := .acceptable
    contrasts := []
    readings := [("surface", .acceptable), ("inverse", .acceptable)]
    paperFeatures := [("wordOrder", "verbRaising")] }

def ex_100b : Datum :=
  { id := "steedman2000_100b"
    source := ⟨"steedman-2000", "ch. 6 (100b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "(omdat) iemand probeert alle liederen te zingen"
    glossedTokens := [("(omdat)", "(because)"), ("iemand", "someone"), ("probeert", "tries"), ("alle", "every"), ("liederen", "song"), ("te", "to"), ("zingen", "sing")]
    glossedWords := [⟨['(', 'o', 'm', 'd', 'a', 't', ')'], ['(', 'b', 'e', 'c', 'a', 'u', 's', 'e', ')'], [⟨['o', 'm', 'd', 'a', 't'], ['(', 'b', 'e', 'c', 'a', 'u', 's', 'e', ')'], none⟩]⟩, ⟨['i', 'e', 'm', 'a', 'n', 'd'], ['s', 'o', 'm', 'e', 'o', 'n', 'e'], [⟨['i', 'e', 'm', 'a', 'n', 'd'], ['s', 'o', 'm', 'e', 'o', 'n', 'e'], none⟩]⟩, ⟨['p', 'r', 'o', 'b', 'e', 'e', 'r', 't'], ['t', 'r', 'i', 'e', 's'], [⟨['p', 'r', 'o', 'b', 'e', 'e', 'r', 't'], ['t', 'r', 'i', 'e', 's'], none⟩]⟩, ⟨['a', 'l', 'l', 'e'], ['e', 'v', 'e', 'r', 'y'], [⟨['a', 'l', 'l', 'e'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['l', 'i', 'e', 'd', 'e', 'r', 'e', 'n'], ['s', 'o', 'n', 'g'], [⟨['l', 'i', 'e', 'd', 'e', 'r', 'e', 'n'], ['s', 'o', 'n', 'g'], none⟩]⟩, ⟨['t', 'e'], ['t', 'o'], [⟨['t', 'e'], ['t', 'o'], none⟩]⟩, ⟨['z', 'i', 'n', 'g', 'e', 'n'], ['s', 'i', 'n', 'g'], [⟨['z', 'i', 'n', 'g', 'e', 'n'], ['s', 'i', 'n', 'g'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Dutch subordinate clause, verb-projection-raising word order, two quantified arguments."
    judgment := .acceptable
    contrasts := []
    readings := [("surface", .acceptable), ("inverse", .unacceptable)]
    paperFeatures := [("wordOrder", "verbProjectionRaising")] }

def ch7_4 : Datum :=
  { id := "steedman2000_ch7_4"
    source := ⟨"steedman-2000", "ch. 7 (4)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "[Ken-ga Naomi-o], [Erika-ga Sara-o] tazuneta"
    glossedTokens := [("Ken-ga", "Ken-NOM"), ("Naomi-o", "Naomi-ACC"), ("Erika-ga", "Erika-NOM"), ("Sara-o", "Sara-ACC"), ("tazuneta", "visit-PST.CONCL")]
    glossedWords := [⟨['K', 'e', 'n', '-', 'g', 'a'], ['K', 'e', 'n', '-', 'N', 'O', 'M'], [⟨['K', 'e', 'n'], ['K', 'e', 'n'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['N', 'a', 'o', 'm', 'i', '-', 'o'], ['N', 'a', 'o', 'm', 'i', '-', 'A', 'C', 'C'], [⟨['N', 'a', 'o', 'm', 'i'], ['N', 'a', 'o', 'm', 'i'], none⟩, ⟨['o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['E', 'r', 'i', 'k', 'a', '-', 'g', 'a'], ['E', 'r', 'i', 'k', 'a', '-', 'N', 'O', 'M'], [⟨['E', 'r', 'i', 'k', 'a'], ['E', 'r', 'i', 'k', 'a'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['S', 'a', 'r', 'a', '-', 'o'], ['S', 'a', 'r', 'a', '-', 'A', 'C', 'C'], [⟨['S', 'a', 'r', 'a'], ['S', 'a', 'r', 'a'], none⟩, ⟨['o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['t', 'a', 'z', 'u', 'n', 'e', 't', 'a'], ['v', 'i', 's', 'i', 't', '-', 'P', 'S', 'T', '.', 'C', 'O', 'N', 'C', 'L'], []⟩]
    lgrConformance := some .wordAligned
    context := "Japanese (pure SOV): backward gapping — the nonstandard subject-object argument clusters conjoin and the verb surfaces only in the final conjunct."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "gapping"), ("wordOrder", "SOV"), ("gappingDirection", "backward")] }

def ch7_5 : Datum :=
  { id := "steedman2000_ch7_5"
    source := ⟨"steedman-2000", "ch. 7 (5)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Ken-ga Naomi-o tazunete, Erika-ga Sara-o"
    glossedTokens := [("Ken-ga", "Ken-NOM"), ("Naomi-o", "Naomi-ACC"), ("tazunete", "visit-PST.ADV"), ("Erika-ga", "Erika-NOM"), ("Sara-o", "Sara-ACC")]
    glossedWords := [⟨['K', 'e', 'n', '-', 'g', 'a'], ['K', 'e', 'n', '-', 'N', 'O', 'M'], [⟨['K', 'e', 'n'], ['K', 'e', 'n'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['N', 'a', 'o', 'm', 'i', '-', 'o'], ['N', 'a', 'o', 'm', 'i', '-', 'A', 'C', 'C'], [⟨['N', 'a', 'o', 'm', 'i'], ['N', 'a', 'o', 'm', 'i'], none⟩, ⟨['o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['t', 'a', 'z', 'u', 'n', 'e', 't', 'e'], ['v', 'i', 's', 'i', 't', '-', 'P', 'S', 'T', '.', 'A', 'D', 'V'], []⟩, ⟨['E', 'r', 'i', 'k', 'a', '-', 'g', 'a'], ['E', 'r', 'i', 'k', 'a', '-', 'N', 'O', 'M'], [⟨['E', 'r', 'i', 'k', 'a'], ['E', 'r', 'i', 'k', 'a'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['S', 'a', 'r', 'a', '-', 'o'], ['S', 'a', 'r', 'a', '-', 'A', 'C', 'C'], [⟨['S', 'a', 'r', 'a'], ['S', 'a', 'r', 'a'], none⟩, ⟨['o'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Japanese (pure SOV): forward gapping — the verb in the first conjunct with a verbless second conjunct — is excluded."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "gapping"), ("wordOrder", "SOV"), ("gappingDirection", "forward")] }

def ch7_11 : Datum :=
  { id := "steedman2000_ch7_11"
    source := ⟨"steedman-2000", "ch. 7 (11)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Ik geloof dat Jan Syntactic Structures en Piet Aspects gelezen heeft."
    glossedTokens := [("Ik", "I"), ("geloof", "believe"), ("dat", "that"), ("Jan", "Jan"), ("Syntactic Structures", "Syntactic Structures"), ("en", "and"), ("Piet", "Piet"), ("Aspects", "Aspects"), ("gelezen", "read"), ("heeft", "has")]
    glossedWords := [⟨['I', 'k'], ['I'], [⟨['I', 'k'], ['I'], none⟩]⟩, ⟨['g', 'e', 'l', 'o', 'o', 'f'], ['b', 'e', 'l', 'i', 'e', 'v', 'e'], [⟨['g', 'e', 'l', 'o', 'o', 'f'], ['b', 'e', 'l', 'i', 'e', 'v', 'e'], none⟩]⟩, ⟨['d', 'a', 't'], ['t', 'h', 'a', 't'], [⟨['d', 'a', 't'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['J', 'a', 'n'], ['J', 'a', 'n'], [⟨['J', 'a', 'n'], ['J', 'a', 'n'], none⟩]⟩, ⟨['S', 'y', 'n', 't', 'a', 'c', 't', 'i', 'c', ' ', 'S', 't', 'r', 'u', 'c', 't', 'u', 'r', 'e', 's'], ['S', 'y', 'n', 't', 'a', 'c', 't', 'i', 'c', ' ', 'S', 't', 'r', 'u', 'c', 't', 'u', 'r', 'e', 's'], [⟨['S', 'y', 'n', 't', 'a', 'c', 't', 'i', 'c', ' ', 'S', 't', 'r', 'u', 'c', 't', 'u', 'r', 'e', 's'], ['S', 'y', 'n', 't', 'a', 'c', 't', 'i', 'c', ' ', 'S', 't', 'r', 'u', 'c', 't', 'u', 'r', 'e', 's'], none⟩]⟩, ⟨['e', 'n'], ['a', 'n', 'd'], [⟨['e', 'n'], ['a', 'n', 'd'], none⟩]⟩, ⟨['P', 'i', 'e', 't'], ['P', 'i', 'e', 't'], [⟨['P', 'i', 'e', 't'], ['P', 'i', 'e', 't'], none⟩]⟩, ⟨['A', 's', 'p', 'e', 'c', 't', 's'], ['A', 's', 'p', 'e', 'c', 't', 's'], [⟨['A', 's', 'p', 'e', 'c', 't', 's'], ['A', 's', 'p', 'e', 'c', 't', 's'], none⟩]⟩, ⟨['g', 'e', 'l', 'e', 'z', 'e', 'n'], ['r', 'e', 'a', 'd'], [⟨['g', 'e', 'l', 'e', 'z', 'e', 'n'], ['r', 'e', 'a', 'd'], none⟩]⟩, ⟨['h', 'e', 'e', 'f', 't'], ['h', 'a', 's'], [⟨['h', 'e', 'e', 'f', 't'], ['h', 'a', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Dutch subordinate clause (SOV): backward gapping — conjoined subject-object clusters precede the shared verb cluster."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "gapping"), ("wordOrder", "SOV"), ("gappingDirection", "backward")] }

def ch7_19 : Datum :=
  { id := "steedman2000_ch7_19"
    source := ⟨"steedman-2000", "ch. 7 (19)"⟩
    reportedIn := none
    language := "iris1253"
    primaryText := "Chonaic [Eoghan Siobhán] agus [Eoghnaí Ciarán]"
    glossedTokens := [("Chonaic", "saw"), ("Eoghan", "Eoghan"), ("Siobhán", "Siobhán"), ("agus", "and"), ("Eoghnaí", "Eoghnaí"), ("Ciarán", "Ciarán")]
    glossedWords := [⟨['C', 'h', 'o', 'n', 'a', 'i', 'c'], ['s', 'a', 'w'], [⟨['C', 'h', 'o', 'n', 'a', 'i', 'c'], ['s', 'a', 'w'], none⟩]⟩, ⟨['E', 'o', 'g', 'h', 'a', 'n'], ['E', 'o', 'g', 'h', 'a', 'n'], [⟨['E', 'o', 'g', 'h', 'a', 'n'], ['E', 'o', 'g', 'h', 'a', 'n'], none⟩]⟩, ⟨['S', 'i', 'o', 'b', 'h', 'á', 'n'], ['S', 'i', 'o', 'b', 'h', 'á', 'n'], [⟨['S', 'i', 'o', 'b', 'h', 'á', 'n'], ['S', 'i', 'o', 'b', 'h', 'á', 'n'], none⟩]⟩, ⟨['a', 'g', 'u', 's'], ['a', 'n', 'd'], [⟨['a', 'g', 'u', 's'], ['a', 'n', 'd'], none⟩]⟩, ⟨['E', 'o', 'g', 'h', 'n', 'a', 'í'], ['E', 'o', 'g', 'h', 'n', 'a', 'í'], [⟨['E', 'o', 'g', 'h', 'n', 'a', 'í'], ['E', 'o', 'g', 'h', 'n', 'a', 'í'], none⟩]⟩, ⟨['C', 'i', 'a', 'r', 'á', 'n'], ['C', 'i', 'a', 'r', 'á', 'n'], [⟨['C', 'i', 'a', 'r', 'á', 'n'], ['C', 'i', 'a', 'r', 'á', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Irish (pure VSO): forward gapping — the initial verb is shared by conjoined subject-object argument clusters."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "gapping"), ("wordOrder", "VSO"), ("gappingDirection", "forward")] }

def ch7_20 : Datum :=
  { id := "steedman2000_ch7_20"
    source := ⟨"steedman-2000", "ch. 7 (20)"⟩
    reportedIn := none
    language := "iris1253"
    primaryText := "[Eoghan Siobhán] agus chonaic [Eoghnaí Ciarán]"
    glossedTokens := [("Eoghan", "Eoghan"), ("Siobhán", "Siobhán"), ("agus", "and"), ("chonaic", "saw"), ("Eoghnaí", "Eoghnaí"), ("Ciarán", "Ciarán")]
    glossedWords := [⟨['E', 'o', 'g', 'h', 'a', 'n'], ['E', 'o', 'g', 'h', 'a', 'n'], [⟨['E', 'o', 'g', 'h', 'a', 'n'], ['E', 'o', 'g', 'h', 'a', 'n'], none⟩]⟩, ⟨['S', 'i', 'o', 'b', 'h', 'á', 'n'], ['S', 'i', 'o', 'b', 'h', 'á', 'n'], [⟨['S', 'i', 'o', 'b', 'h', 'á', 'n'], ['S', 'i', 'o', 'b', 'h', 'á', 'n'], none⟩]⟩, ⟨['a', 'g', 'u', 's'], ['a', 'n', 'd'], [⟨['a', 'g', 'u', 's'], ['a', 'n', 'd'], none⟩]⟩, ⟨['c', 'h', 'o', 'n', 'a', 'i', 'c'], ['s', 'a', 'w'], [⟨['c', 'h', 'o', 'n', 'a', 'i', 'c'], ['s', 'a', 'w'], none⟩]⟩, ⟨['E', 'o', 'g', 'h', 'n', 'a', 'í'], ['E', 'o', 'g', 'h', 'n', 'a', 'í'], [⟨['E', 'o', 'g', 'h', 'n', 'a', 'í'], ['E', 'o', 'g', 'h', 'n', 'a', 'í'], none⟩]⟩, ⟨['C', 'i', 'a', 'r', 'á', 'n'], ['C', 'i', 'a', 'r', 'á', 'n'], [⟨['C', 'i', 'a', 'r', 'á', 'n'], ['C', 'i', 'a', 'r', 'á', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Irish (pure VSO): backward gapping — verbless first conjunct with the verb in the second conjunct — is excluded."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "gapping"), ("wordOrder", "VSO"), ("gappingDirection", "backward")] }

def ch7_21 : Datum :=
  { id := "steedman2000_ch7_21"
    source := ⟨"steedman-2000", "ch. 7 (21)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Wil jij een ijsje en Marietje limonade?"
    glossedTokens := [("Wil", "want"), ("jij", "you"), ("een", "an"), ("ijsje", "ice-cream"), ("en", "and"), ("Marietje", "Marietje"), ("limonade", "lemonade")]
    glossedWords := [⟨['W', 'i', 'l'], ['w', 'a', 'n', 't'], [⟨['W', 'i', 'l'], ['w', 'a', 'n', 't'], none⟩]⟩, ⟨['j', 'i', 'j'], ['y', 'o', 'u'], [⟨['j', 'i', 'j'], ['y', 'o', 'u'], none⟩]⟩, ⟨['e', 'e', 'n'], ['a', 'n'], [⟨['e', 'e', 'n'], ['a', 'n'], none⟩]⟩, ⟨['i', 'j', 's', 'j', 'e'], ['i', 'c', 'e', '-', 'c', 'r', 'e', 'a', 'm'], []⟩, ⟨['e', 'n'], ['a', 'n', 'd'], [⟨['e', 'n'], ['a', 'n', 'd'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'e', 't', 'j', 'e'], ['M', 'a', 'r', 'i', 'e', 't', 'j', 'e'], [⟨['M', 'a', 'r', 'i', 'e', 't', 'j', 'e'], ['M', 'a', 'r', 'i', 'e', 't', 'j', 'e'], none⟩]⟩, ⟨['l', 'i', 'm', 'o', 'n', 'a', 'd', 'e'], ['l', 'e', 'm', 'o', 'n', 'a', 'd', 'e'], [⟨['l', 'i', 'm', 'o', 'n', 'a', 'd', 'e'], ['l', 'e', 'm', 'o', 'n', 'a', 'd', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Dutch main clause (verb-initial yes/no question, conforming to the VSO pattern per Steedman): forward gapping, the mirror image of the backward-gapping subordinate clauses."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "gapping"), ("wordOrder", "VSO"), ("gappingDirection", "forward")] }

def ch7_62 : Datum :=
  { id := "steedman2000_ch7_62"
    source := ⟨"steedman-2000", "ch. 7 (62)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dexter eats bread, and Warren, potatoes"
    glossedTokens := []
    context := "English (SVO): forward gapping — the verb in the first conjunct is shared by the verbless right conjunct."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "gapping"), ("wordOrder", "SVO"), ("gappingDirection", "forward")] }

def ch7_63 : Datum :=
  { id := "steedman2000_ch7_63"
    source := ⟨"steedman-2000", "ch. 7 (63)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Warren, potatoes and Dexter bought bread"
    glossedTokens := []
    context := "English (SVO): backward gapping — verbless left conjunct with the verb in the right conjunct — is excluded by universal principles."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "gapping"), ("wordOrder", "SVO"), ("gappingDirection", "backward")] }

def all : List Datum := [ex_96, ex_97, ex_98a, ex_98b, ex_99a, ex_99b, ex_100a, ex_100b, ch7_4, ch7_5, ch7_11, ch7_19, ch7_20, ch7_21, ch7_62, ch7_63]

end Steedman2000.Examples
