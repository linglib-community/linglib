module

public import Linglib.Data.Examples.Schema

/-!
# `MartinezVera2026` — typed example data

Auto-generated from `Linglib/Data/Examples/MartinezVera2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace MartinezVera2026.Examples`.
-/

@[expose] public section

namespace MartinezVera2026.Examples

def ex_6 : Datum :=
  { id := "martinezvera2026_6"
    source := ⟨"martinez-vera-2026", "(6)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Maria-ka mana mayu-man ri-rka. Mana, Maria-ka mayu-man ri-rka=mi."
    glossedTokens := [("Maria-ka", "Maria-TOP"), ("mana", "no"), ("mayu-man", "river-DIR"), ("ri-rka", "go-PST1"), ("Mana", "no"), ("Maria-ka", "Maria-TOP"), ("mayu-man", "river-DIR"), ("ri-rka=mi", "go-PST1=mi")]
    glossedWords := [⟨['M', 'a', 'r', 'i', 'a', '-', 'k', 'a'], ['M', 'a', 'r', 'i', 'a', '-', 'T', 'O', 'P'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['m', 'a', 'n', 'a'], ['n', 'o'], [⟨['m', 'a', 'n', 'a'], ['n', 'o'], none⟩]⟩, ⟨['m', 'a', 'y', 'u', '-', 'm', 'a', 'n'], ['r', 'i', 'v', 'e', 'r', '-', 'D', 'I', 'R'], [⟨['m', 'a', 'y', 'u'], ['r', 'i', 'v', 'e', 'r'], none⟩, ⟨['m', 'a', 'n'], ['D', 'I', 'R'], some '-'⟩]⟩, ⟨['r', 'i', '-', 'r', 'k', 'a'], ['g', 'o', '-', 'P', 'S', 'T', '1'], [⟨['r', 'i'], ['g', 'o'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩]⟩, ⟨['M', 'a', 'n', 'a'], ['n', 'o'], [⟨['M', 'a', 'n', 'a'], ['n', 'o'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a', '-', 'k', 'a'], ['M', 'a', 'r', 'i', 'a', '-', 'T', 'O', 'P'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['m', 'a', 'y', 'u', '-', 'm', 'a', 'n'], ['r', 'i', 'v', 'e', 'r', '-', 'D', 'I', 'R'], [⟨['m', 'a', 'y', 'u'], ['r', 'i', 'v', 'e', 'r'], none⟩, ⟨['m', 'a', 'n'], ['D', 'I', 'R'], some '-'⟩]⟩, ⟨['r', 'i', '-', 'r', 'k', 'a', '=', 'm', 'i'], ['g', 'o', '-', 'P', 'S', 'T', '1', '=', 'm', 'i'], [⟨['r', 'i'], ['g', 'o'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩, ⟨['m', 'i'], ['m', 'i'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Two individuals are discussing Maria's whereabouts."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("prior", "assertedNegation"), ("focus", "clause")] }

def ex_7 : Datum :=
  { id := "martinezvera2026_7"
    source := ⟨"martinez-vera-2026", "(7)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Juanchu-ka oveja-ta ranti-rka=mi."
    glossedTokens := [("Juanchu-ka", "Juan-TOP"), ("oveja-ta", "sheep-ACC"), ("ranti-rka=mi", "buy-PST1=mi")]
    glossedWords := [⟨['J', 'u', 'a', 'n', 'c', 'h', 'u', '-', 'k', 'a'], ['J', 'u', 'a', 'n', '-', 'T', 'O', 'P'], [⟨['J', 'u', 'a', 'n', 'c', 'h', 'u'], ['J', 'u', 'a', 'n'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['o', 'v', 'e', 'j', 'a', '-', 't', 'a'], ['s', 'h', 'e', 'e', 'p', '-', 'A', 'C', 'C'], [⟨['o', 'v', 'e', 'j', 'a'], ['s', 'h', 'e', 'e', 'p'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['r', 'a', 'n', 't', 'i', '-', 'r', 'k', 'a', '=', 'm', 'i'], ['b', 'u', 'y', '-', 'P', 'S', 'T', '1', '=', 'm', 'i'], [⟨['r', 'a', 'n', 't', 'i'], ['b', 'u', 'y'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩, ⟨['m', 'i'], ['m', 'i'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "A couple is on its house entrance seeing people passing by. One individual says (7)."
    judgment := .unacceptable
    contrasts := [("Juanchu-ka oveja-ta ranti-rka.", .acceptable)]
    readings := []
    paperFeatures := [("prior", "none"), ("focus", "clause")] }

def ex_8b : Datum :=
  { id := "martinezvera2026_8b"
    source := ⟨"martinez-vera-2026", "(8b)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Maria-ka wakra-ta ranti-rka-chu? Ari, Maria-ka wakra-ta ranti-rka=mi."
    glossedTokens := [("Maria-ka", "Maria-TOP"), ("wakra-ta", "cow-ACC"), ("ranti-rka-chu", "buy-PST1-POL"), ("Ari", "yes"), ("Maria-ka", "Maria-TOP"), ("wakra-ta", "cow-ACC"), ("ranti-rka=mi", "buy-PST1=mi")]
    glossedWords := [⟨['M', 'a', 'r', 'i', 'a', '-', 'k', 'a'], ['M', 'a', 'r', 'i', 'a', '-', 'T', 'O', 'P'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['w', 'a', 'k', 'r', 'a', '-', 't', 'a'], ['c', 'o', 'w', '-', 'A', 'C', 'C'], [⟨['w', 'a', 'k', 'r', 'a'], ['c', 'o', 'w'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['r', 'a', 'n', 't', 'i', '-', 'r', 'k', 'a', '-', 'c', 'h', 'u'], ['b', 'u', 'y', '-', 'P', 'S', 'T', '1', '-', 'P', 'O', 'L'], [⟨['r', 'a', 'n', 't', 'i'], ['b', 'u', 'y'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩, ⟨['c', 'h', 'u'], ['P', 'O', 'L'], some '-'⟩]⟩, ⟨['A', 'r', 'i'], ['y', 'e', 's'], [⟨['A', 'r', 'i'], ['y', 'e', 's'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a', '-', 'k', 'a'], ['M', 'a', 'r', 'i', 'a', '-', 'T', 'O', 'P'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['w', 'a', 'k', 'r', 'a', '-', 't', 'a'], ['c', 'o', 'w', '-', 'A', 'C', 'C'], [⟨['w', 'a', 'k', 'r', 'a'], ['c', 'o', 'w'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['r', 'a', 'n', 't', 'i', '-', 'r', 'k', 'a', '=', 'm', 'i'], ['b', 'u', 'y', '-', 'P', 'S', 'T', '1', '=', 'm', 'i'], [⟨['r', 'a', 'n', 't', 'i'], ['b', 'u', 'y'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩, ⟨['m', 'i'], ['m', 'i'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "One individual asks a question about Maria's whereabouts and another individual replies. There is no bias or expectations as to what Maria would be doing."
    judgment := .unacceptable
    contrasts := [("Ari, Maria-ka wakra-ta ranti-rka.", .acceptable)]
    readings := []
    paperFeatures := [("prior", "none"), ("question", "polar"), ("focus", "clause")] }

def ex_8c : Datum :=
  { id := "martinezvera2026_8c"
    source := ⟨"martinez-vera-2026", "(8c)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Maria-ka wakra-ta ranti-rka-chu? Mana, Maria-ka mana wakra-ta ranti-rka=mi."
    glossedTokens := [("Maria-ka", "Maria-TOP"), ("wakra-ta", "cow-ACC"), ("ranti-rka-chu", "buy-PST1-POL"), ("Mana", "no"), ("Maria-ka", "Maria-TOP"), ("mana", "no"), ("wakra-ta", "cow-ACC"), ("ranti-rka=mi", "buy-PST1=mi")]
    glossedWords := [⟨['M', 'a', 'r', 'i', 'a', '-', 'k', 'a'], ['M', 'a', 'r', 'i', 'a', '-', 'T', 'O', 'P'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['w', 'a', 'k', 'r', 'a', '-', 't', 'a'], ['c', 'o', 'w', '-', 'A', 'C', 'C'], [⟨['w', 'a', 'k', 'r', 'a'], ['c', 'o', 'w'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['r', 'a', 'n', 't', 'i', '-', 'r', 'k', 'a', '-', 'c', 'h', 'u'], ['b', 'u', 'y', '-', 'P', 'S', 'T', '1', '-', 'P', 'O', 'L'], [⟨['r', 'a', 'n', 't', 'i'], ['b', 'u', 'y'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩, ⟨['c', 'h', 'u'], ['P', 'O', 'L'], some '-'⟩]⟩, ⟨['M', 'a', 'n', 'a'], ['n', 'o'], [⟨['M', 'a', 'n', 'a'], ['n', 'o'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a', '-', 'k', 'a'], ['M', 'a', 'r', 'i', 'a', '-', 'T', 'O', 'P'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['m', 'a', 'n', 'a'], ['n', 'o'], [⟨['m', 'a', 'n', 'a'], ['n', 'o'], none⟩]⟩, ⟨['w', 'a', 'k', 'r', 'a', '-', 't', 'a'], ['c', 'o', 'w', '-', 'A', 'C', 'C'], [⟨['w', 'a', 'k', 'r', 'a'], ['c', 'o', 'w'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['r', 'a', 'n', 't', 'i', '-', 'r', 'k', 'a', '=', 'm', 'i'], ['b', 'u', 'y', '-', 'P', 'S', 'T', '1', '=', 'm', 'i'], [⟨['r', 'a', 'n', 't', 'i'], ['b', 'u', 'y'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩, ⟨['m', 'i'], ['m', 'i'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "One individual asks a question about Maria's whereabouts and another individual replies. There is no bias or expectations as to what Maria would be doing."
    judgment := .unacceptable
    contrasts := [("Mana, Maria-ka mana wakra-ta ranti-rka.", .acceptable)]
    readings := []
    paperFeatures := [("prior", "none"), ("question", "polar"), ("focus", "clause"), ("polarity", "negative")] }

def fn5_i : Datum :=
  { id := "martinezvera2026_fn5_i"
    source := ⟨"martinez-vera-2026", "fn. 5 (i)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Maria-manta ima tuku-shka? Maria-ka wakra-ta ranti-rka=mi."
    glossedTokens := [("Maria-manta", "Maria-ABL"), ("ima", "what"), ("tuku-shka", "happen-PST2"), ("Maria-ka", "Maria-TOP"), ("wakra-ta", "cow-ACC"), ("ranti-rka=mi", "buy-PST1=mi")]
    glossedWords := [⟨['M', 'a', 'r', 'i', 'a', '-', 'm', 'a', 'n', 't', 'a'], ['M', 'a', 'r', 'i', 'a', '-', 'A', 'B', 'L'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩, ⟨['m', 'a', 'n', 't', 'a'], ['A', 'B', 'L'], some '-'⟩]⟩, ⟨['i', 'm', 'a'], ['w', 'h', 'a', 't'], [⟨['i', 'm', 'a'], ['w', 'h', 'a', 't'], none⟩]⟩, ⟨['t', 'u', 'k', 'u', '-', 's', 'h', 'k', 'a'], ['h', 'a', 'p', 'p', 'e', 'n', '-', 'P', 'S', 'T', '2'], [⟨['t', 'u', 'k', 'u'], ['h', 'a', 'p', 'p', 'e', 'n'], none⟩, ⟨['s', 'h', 'k', 'a'], ['P', 'S', 'T', '2'], some '-'⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a', '-', 'k', 'a'], ['M', 'a', 'r', 'i', 'a', '-', 'T', 'O', 'P'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['w', 'a', 'k', 'r', 'a', '-', 't', 'a'], ['c', 'o', 'w', '-', 'A', 'C', 'C'], [⟨['w', 'a', 'k', 'r', 'a'], ['c', 'o', 'w'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['r', 'a', 'n', 't', 'i', '-', 'r', 'k', 'a', '=', 'm', 'i'], ['b', 'u', 'y', '-', 'P', 'S', 'T', '1', '=', 'm', 'i'], [⟨['r', 'a', 'n', 't', 'i'], ['b', 'u', 'y'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩, ⟨['m', 'i'], ['m', 'i'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    contrasts := [("Maria-ka wakra-ta ranti-rka.", .acceptable)]
    readings := []
    paperFeatures := [("prior", "none"), ("question", "constituent"), ("focus", "clause")] }

def ex_9 : Datum :=
  { id := "martinezvera2026_9"
    source := ⟨"martinez-vera-2026", "(9)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Maria-ka wakra-ta ranti-rka-chu, na? Ari, Maria-ka wakra-ta ranti-rka=mi."
    glossedTokens := [("Maria-ka", "Maria-TOP"), ("wakra-ta", "cow-ACC"), ("ranti-rka-chu", "buy-PST1-POL"), ("na", "in.fact"), ("Ari", "yes"), ("Maria-ka", "Maria-TOP"), ("wakra-ta", "cow-ACC"), ("ranti-rka=mi", "buy-PST1=mi")]
    glossedWords := [⟨['M', 'a', 'r', 'i', 'a', '-', 'k', 'a'], ['M', 'a', 'r', 'i', 'a', '-', 'T', 'O', 'P'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['w', 'a', 'k', 'r', 'a', '-', 't', 'a'], ['c', 'o', 'w', '-', 'A', 'C', 'C'], [⟨['w', 'a', 'k', 'r', 'a'], ['c', 'o', 'w'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['r', 'a', 'n', 't', 'i', '-', 'r', 'k', 'a', '-', 'c', 'h', 'u'], ['b', 'u', 'y', '-', 'P', 'S', 'T', '1', '-', 'P', 'O', 'L'], [⟨['r', 'a', 'n', 't', 'i'], ['b', 'u', 'y'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩, ⟨['c', 'h', 'u'], ['P', 'O', 'L'], some '-'⟩]⟩, ⟨['n', 'a'], ['i', 'n', '.', 'f', 'a', 'c', 't'], [⟨['n', 'a'], ['i', 'n', '.', 'f', 'a', 'c', 't'], none⟩]⟩, ⟨['A', 'r', 'i'], ['y', 'e', 's'], [⟨['A', 'r', 'i'], ['y', 'e', 's'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a', '-', 'k', 'a'], ['M', 'a', 'r', 'i', 'a', '-', 'T', 'O', 'P'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['w', 'a', 'k', 'r', 'a', '-', 't', 'a'], ['c', 'o', 'w', '-', 'A', 'C', 'C'], [⟨['w', 'a', 'k', 'r', 'a'], ['c', 'o', 'w'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['r', 'a', 'n', 't', 'i', '-', 'r', 'k', 'a', '=', 'm', 'i'], ['b', 'u', 'y', '-', 'P', 'S', 'T', '1', '=', 'm', 'i'], [⟨['r', 'a', 'n', 't', 'i'], ['b', 'u', 'y'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩, ⟨['m', 'i'], ['m', 'i'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("prior", "debate"), ("question", "polar"), ("focus", "clause")] }

def ex_10 : Datum :=
  { id := "martinezvera2026_10"
    source := ⟨"martinez-vera-2026", "(10)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Maria-ka mana mayu-man ri-rka-chu? Ari, Maria-ka mayu-man ri-rka=mi."
    glossedTokens := [("Maria-ka", "Maria-TOP"), ("mana", "no"), ("mayu-man", "river-DIR"), ("ri-rka-chu", "go-PST1-POL"), ("Ari", "yes"), ("Maria-ka", "Maria-TOP"), ("mayu-man", "river-DIR"), ("ri-rka=mi", "go-PST1=mi")]
    glossedWords := [⟨['M', 'a', 'r', 'i', 'a', '-', 'k', 'a'], ['M', 'a', 'r', 'i', 'a', '-', 'T', 'O', 'P'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['m', 'a', 'n', 'a'], ['n', 'o'], [⟨['m', 'a', 'n', 'a'], ['n', 'o'], none⟩]⟩, ⟨['m', 'a', 'y', 'u', '-', 'm', 'a', 'n'], ['r', 'i', 'v', 'e', 'r', '-', 'D', 'I', 'R'], [⟨['m', 'a', 'y', 'u'], ['r', 'i', 'v', 'e', 'r'], none⟩, ⟨['m', 'a', 'n'], ['D', 'I', 'R'], some '-'⟩]⟩, ⟨['r', 'i', '-', 'r', 'k', 'a', '-', 'c', 'h', 'u'], ['g', 'o', '-', 'P', 'S', 'T', '1', '-', 'P', 'O', 'L'], [⟨['r', 'i'], ['g', 'o'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩, ⟨['c', 'h', 'u'], ['P', 'O', 'L'], some '-'⟩]⟩, ⟨['A', 'r', 'i'], ['y', 'e', 's'], [⟨['A', 'r', 'i'], ['y', 'e', 's'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a', '-', 'k', 'a'], ['M', 'a', 'r', 'i', 'a', '-', 'T', 'O', 'P'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['m', 'a', 'y', 'u', '-', 'm', 'a', 'n'], ['r', 'i', 'v', 'e', 'r', '-', 'D', 'I', 'R'], [⟨['m', 'a', 'y', 'u'], ['r', 'i', 'v', 'e', 'r'], none⟩, ⟨['m', 'a', 'n'], ['D', 'I', 'R'], some '-'⟩]⟩, ⟨['r', 'i', '-', 'r', 'k', 'a', '=', 'm', 'i'], ['g', 'o', '-', 'P', 'S', 'T', '1', '=', 'm', 'i'], [⟨['r', 'i'], ['g', 'o'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩, ⟨['m', 'i'], ['m', 'i'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("prior", "none"), ("question", "negativeBiased"), ("focus", "clause")] }

def ex_11 : Datum :=
  { id := "martinezvera2026_11"
    source := ⟨"martinez-vera-2026", "(11)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Ciertu-chu wakra-ta ranti-rka? Ari, Maria-ka wakra-ta ranti-rka=mi."
    glossedTokens := [("Ciertu-chu", "in.fact-POL"), ("wakra-ta", "cow-ACC"), ("ranti-rka", "buy-PST1"), ("Ari", "yes"), ("Maria-ka", "Maria-TOP"), ("wakra-ta", "cow-ACC"), ("ranti-rka=mi", "buy-PST1=mi")]
    glossedWords := [⟨['C', 'i', 'e', 'r', 't', 'u', '-', 'c', 'h', 'u'], ['i', 'n', '.', 'f', 'a', 'c', 't', '-', 'P', 'O', 'L'], [⟨['C', 'i', 'e', 'r', 't', 'u'], ['i', 'n', '.', 'f', 'a', 'c', 't'], none⟩, ⟨['c', 'h', 'u'], ['P', 'O', 'L'], some '-'⟩]⟩, ⟨['w', 'a', 'k', 'r', 'a', '-', 't', 'a'], ['c', 'o', 'w', '-', 'A', 'C', 'C'], [⟨['w', 'a', 'k', 'r', 'a'], ['c', 'o', 'w'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['r', 'a', 'n', 't', 'i', '-', 'r', 'k', 'a'], ['b', 'u', 'y', '-', 'P', 'S', 'T', '1'], [⟨['r', 'a', 'n', 't', 'i'], ['b', 'u', 'y'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩]⟩, ⟨['A', 'r', 'i'], ['y', 'e', 's'], [⟨['A', 'r', 'i'], ['y', 'e', 's'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a', '-', 'k', 'a'], ['M', 'a', 'r', 'i', 'a', '-', 'T', 'O', 'P'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['w', 'a', 'k', 'r', 'a', '-', 't', 'a'], ['c', 'o', 'w', '-', 'A', 'C', 'C'], [⟨['w', 'a', 'k', 'r', 'a'], ['c', 'o', 'w'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['r', 'a', 'n', 't', 'i', '-', 'r', 'k', 'a', '=', 'm', 'i'], ['b', 'u', 'y', '-', 'P', 'S', 'T', '1', '=', 'm', 'i'], [⟨['r', 'a', 'n', 't', 'i'], ['b', 'u', 'y'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩, ⟨['m', 'i'], ['m', 'i'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "One individual asks a question about Maria's whereabouts and another individual replies. There has been some discussion about Maria's whereabouts, with it being suggested that Maria didn't buy a cow in addition to it being suggested that she did buy one, but the discussion is still open. The individual wants to settle the matter, so they ask the second individual to do so."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("prior", "debate"), ("question", "positiveBiased"), ("focus", "clause")] }

def ex_18a : Datum :=
  { id := "martinezvera2026_18a"
    source := ⟨"martinez-vera-2026", "(18a)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Pedro-ka mayu-man ri-rka, chay-ka mana shina-chu."
    glossedTokens := [("Pedro-ka", "Pedro-TOP"), ("mayu-man", "river-DIR"), ("ri-rka", "go-PST1"), ("chay-ka", "that-TOP"), ("mana", "no"), ("shina-chu", "like.that-POL")]
    glossedWords := [⟨['P', 'e', 'd', 'r', 'o', '-', 'k', 'a'], ['P', 'e', 'd', 'r', 'o', '-', 'T', 'O', 'P'], [⟨['P', 'e', 'd', 'r', 'o'], ['P', 'e', 'd', 'r', 'o'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['m', 'a', 'y', 'u', '-', 'm', 'a', 'n'], ['r', 'i', 'v', 'e', 'r', '-', 'D', 'I', 'R'], [⟨['m', 'a', 'y', 'u'], ['r', 'i', 'v', 'e', 'r'], none⟩, ⟨['m', 'a', 'n'], ['D', 'I', 'R'], some '-'⟩]⟩, ⟨['r', 'i', '-', 'r', 'k', 'a'], ['g', 'o', '-', 'P', 'S', 'T', '1'], [⟨['r', 'i'], ['g', 'o'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩]⟩, ⟨['c', 'h', 'a', 'y', '-', 'k', 'a'], ['t', 'h', 'a', 't', '-', 'T', 'O', 'P'], [⟨['c', 'h', 'a', 'y'], ['t', 'h', 'a', 't'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['m', 'a', 'n', 'a'], ['n', 'o'], [⟨['m', 'a', 'n', 'a'], ['n', 'o'], none⟩]⟩, ⟨['s', 'h', 'i', 'n', 'a', '-', 'c', 'h', 'u'], ['l', 'i', 'k', 'e', '.', 't', 'h', 'a', 't', '-', 'P', 'O', 'L'], [⟨['s', 'h', 'i', 'n', 'a'], ['l', 'i', 'k', 'e', '.', 't', 'h', 'a', 't'], none⟩, ⟨['c', 'h', 'u'], ['P', 'O', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("evidential", "direct"), ("continuation", "deniesScope")] }

def ex_18b : Datum :=
  { id := "martinezvera2026_18b"
    source := ⟨"martinez-vera-2026", "(18b)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Pedro-ka mayu-man ri-rka, mana riku-rka-ni."
    glossedTokens := [("Pedro-ka", "Pedro-TOP"), ("mayu-man", "river-DIR"), ("ri-rka", "go-PST1"), ("mana", "no"), ("riku-rka-ni", "see-PST1-1SG")]
    glossedWords := [⟨['P', 'e', 'd', 'r', 'o', '-', 'k', 'a'], ['P', 'e', 'd', 'r', 'o', '-', 'T', 'O', 'P'], [⟨['P', 'e', 'd', 'r', 'o'], ['P', 'e', 'd', 'r', 'o'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['m', 'a', 'y', 'u', '-', 'm', 'a', 'n'], ['r', 'i', 'v', 'e', 'r', '-', 'D', 'I', 'R'], [⟨['m', 'a', 'y', 'u'], ['r', 'i', 'v', 'e', 'r'], none⟩, ⟨['m', 'a', 'n'], ['D', 'I', 'R'], some '-'⟩]⟩, ⟨['r', 'i', '-', 'r', 'k', 'a'], ['g', 'o', '-', 'P', 'S', 'T', '1'], [⟨['r', 'i'], ['g', 'o'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩]⟩, ⟨['m', 'a', 'n', 'a'], ['n', 'o'], [⟨['m', 'a', 'n', 'a'], ['n', 'o'], none⟩]⟩, ⟨['r', 'i', 'k', 'u', '-', 'r', 'k', 'a', '-', 'n', 'i'], ['s', 'e', 'e', '-', 'P', 'S', 'T', '1', '-', '1', 'S', 'G'], [⟨['r', 'i', 'k', 'u'], ['s', 'e', 'e'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩, ⟨['n', 'i'], ['1', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("evidential", "direct"), ("continuation", "deniesEvidence")] }

def ex_19a : Datum :=
  { id := "martinezvera2026_19a"
    source := ⟨"martinez-vera-2026", "(19a)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Pedro-ka mayu-man ri-shka, chay-ka mana shina-chu."
    glossedTokens := [("Pedro-ka", "Pedro-TOP"), ("mayu-man", "river-DIR"), ("ri-shka", "go-PST2"), ("chay-ka", "that-TOP"), ("mana", "no"), ("shina-chu", "like.that-POL")]
    glossedWords := [⟨['P', 'e', 'd', 'r', 'o', '-', 'k', 'a'], ['P', 'e', 'd', 'r', 'o', '-', 'T', 'O', 'P'], [⟨['P', 'e', 'd', 'r', 'o'], ['P', 'e', 'd', 'r', 'o'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['m', 'a', 'y', 'u', '-', 'm', 'a', 'n'], ['r', 'i', 'v', 'e', 'r', '-', 'D', 'I', 'R'], [⟨['m', 'a', 'y', 'u'], ['r', 'i', 'v', 'e', 'r'], none⟩, ⟨['m', 'a', 'n'], ['D', 'I', 'R'], some '-'⟩]⟩, ⟨['r', 'i', '-', 's', 'h', 'k', 'a'], ['g', 'o', '-', 'P', 'S', 'T', '2'], [⟨['r', 'i'], ['g', 'o'], none⟩, ⟨['s', 'h', 'k', 'a'], ['P', 'S', 'T', '2'], some '-'⟩]⟩, ⟨['c', 'h', 'a', 'y', '-', 'k', 'a'], ['t', 'h', 'a', 't', '-', 'T', 'O', 'P'], [⟨['c', 'h', 'a', 'y'], ['t', 'h', 'a', 't'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['m', 'a', 'n', 'a'], ['n', 'o'], [⟨['m', 'a', 'n', 'a'], ['n', 'o'], none⟩]⟩, ⟨['s', 'h', 'i', 'n', 'a', '-', 'c', 'h', 'u'], ['l', 'i', 'k', 'e', '.', 't', 'h', 'a', 't', '-', 'P', 'O', 'L'], [⟨['s', 'h', 'i', 'n', 'a'], ['l', 'i', 'k', 'e', '.', 't', 'h', 'a', 't'], none⟩, ⟨['c', 'h', 'u'], ['P', 'O', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("evidential", "reportative"), ("continuation", "deniesScope")] }

def ex_19b : Datum :=
  { id := "martinezvera2026_19b"
    source := ⟨"martinez-vera-2026", "(19b)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Pedro-ka mayu-man ri-shka, pi-pash chay-ta mana ni-rka-chu."
    glossedTokens := [("Pedro-ka", "Pedro-TOP"), ("mayu-man", "river-DIR"), ("ri-shka", "go-PST2"), ("pi-pash", "no-one"), ("chay-ta", "that-ACC"), ("mana", "no"), ("ni-rka-chu", "say-PST1-POL")]
    glossedWords := [⟨['P', 'e', 'd', 'r', 'o', '-', 'k', 'a'], ['P', 'e', 'd', 'r', 'o', '-', 'T', 'O', 'P'], [⟨['P', 'e', 'd', 'r', 'o'], ['P', 'e', 'd', 'r', 'o'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['m', 'a', 'y', 'u', '-', 'm', 'a', 'n'], ['r', 'i', 'v', 'e', 'r', '-', 'D', 'I', 'R'], [⟨['m', 'a', 'y', 'u'], ['r', 'i', 'v', 'e', 'r'], none⟩, ⟨['m', 'a', 'n'], ['D', 'I', 'R'], some '-'⟩]⟩, ⟨['r', 'i', '-', 's', 'h', 'k', 'a'], ['g', 'o', '-', 'P', 'S', 'T', '2'], [⟨['r', 'i'], ['g', 'o'], none⟩, ⟨['s', 'h', 'k', 'a'], ['P', 'S', 'T', '2'], some '-'⟩]⟩, ⟨['p', 'i', '-', 'p', 'a', 's', 'h'], ['n', 'o', '-', 'o', 'n', 'e'], [⟨['p', 'i'], ['n', 'o'], none⟩, ⟨['p', 'a', 's', 'h'], ['o', 'n', 'e'], some '-'⟩]⟩, ⟨['c', 'h', 'a', 'y', '-', 't', 'a'], ['t', 'h', 'a', 't', '-', 'A', 'C', 'C'], [⟨['c', 'h', 'a', 'y'], ['t', 'h', 'a', 't'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['m', 'a', 'n', 'a'], ['n', 'o'], [⟨['m', 'a', 'n', 'a'], ['n', 'o'], none⟩]⟩, ⟨['n', 'i', '-', 'r', 'k', 'a', '-', 'c', 'h', 'u'], ['s', 'a', 'y', '-', 'P', 'S', 'T', '1', '-', 'P', 'O', 'L'], [⟨['n', 'i'], ['s', 'a', 'y'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩, ⟨['c', 'h', 'u'], ['P', 'O', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("evidential", "reportative"), ("continuation", "deniesEvidence")] }

def ex_20 : Datum :=
  { id := "martinezvera2026_20"
    source := ⟨"martinez-vera-2026", "(20)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Juanchu-ka shuk wakra-ta shuwa-rka; chashna=mi."
    glossedTokens := [("Juanchu-ka", "Juan-TOP"), ("shuk", "one"), ("wakra-ta", "cow-ACC"), ("shuwa-rka", "steal-PST1"), ("chashna=mi", "like.this=mi")]
    glossedWords := [⟨['J', 'u', 'a', 'n', 'c', 'h', 'u', '-', 'k', 'a'], ['J', 'u', 'a', 'n', '-', 'T', 'O', 'P'], [⟨['J', 'u', 'a', 'n', 'c', 'h', 'u'], ['J', 'u', 'a', 'n'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['s', 'h', 'u', 'k'], ['o', 'n', 'e'], [⟨['s', 'h', 'u', 'k'], ['o', 'n', 'e'], none⟩]⟩, ⟨['w', 'a', 'k', 'r', 'a', '-', 't', 'a'], ['c', 'o', 'w', '-', 'A', 'C', 'C'], [⟨['w', 'a', 'k', 'r', 'a'], ['c', 'o', 'w'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['s', 'h', 'u', 'w', 'a', '-', 'r', 'k', 'a'], ['s', 't', 'e', 'a', 'l', '-', 'P', 'S', 'T', '1'], [⟨['s', 'h', 'u', 'w', 'a'], ['s', 't', 'e', 'a', 'l'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩]⟩, ⟨['c', 'h', 'a', 's', 'h', 'n', 'a', '=', 'm', 'i'], ['l', 'i', 'k', 'e', '.', 't', 'h', 'i', 's', '=', 'm', 'i'], [⟨['c', 'h', 'a', 's', 'h', 'n', 'a'], ['l', 'i', 'k', 'e', '.', 't', 'h', 'i', 's'], none⟩, ⟨['m', 'i'], ['m', 'i'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Two individuals are discussing Juan's whereabouts. One of them shares the news that Juan stole a cow. They saw Juan doing so, but could not intervene."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("prior", "directEvidential"), ("focus", "clause")] }

def ex_21 : Datum :=
  { id := "martinezvera2026_21"
    source := ⟨"martinez-vera-2026", "(21)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Juanchu-ka shuk wakra-ta shuwa-shka; chashna=mi."
    glossedTokens := [("Juanchu-ka", "Juan-TOP"), ("shuk", "one"), ("wakra-ta", "cow-ACC"), ("shuwa-shka", "steal-PST2"), ("chashna=mi", "like.this=mi")]
    glossedWords := [⟨['J', 'u', 'a', 'n', 'c', 'h', 'u', '-', 'k', 'a'], ['J', 'u', 'a', 'n', '-', 'T', 'O', 'P'], [⟨['J', 'u', 'a', 'n', 'c', 'h', 'u'], ['J', 'u', 'a', 'n'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['s', 'h', 'u', 'k'], ['o', 'n', 'e'], [⟨['s', 'h', 'u', 'k'], ['o', 'n', 'e'], none⟩]⟩, ⟨['w', 'a', 'k', 'r', 'a', '-', 't', 'a'], ['c', 'o', 'w', '-', 'A', 'C', 'C'], [⟨['w', 'a', 'k', 'r', 'a'], ['c', 'o', 'w'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['s', 'h', 'u', 'w', 'a', '-', 's', 'h', 'k', 'a'], ['s', 't', 'e', 'a', 'l', '-', 'P', 'S', 'T', '2'], [⟨['s', 'h', 'u', 'w', 'a'], ['s', 't', 'e', 'a', 'l'], none⟩, ⟨['s', 'h', 'k', 'a'], ['P', 'S', 'T', '2'], some '-'⟩]⟩, ⟨['c', 'h', 'a', 's', 'h', 'n', 'a', '=', 'm', 'i'], ['l', 'i', 'k', 'e', '.', 't', 'h', 'i', 's', '=', 'm', 'i'], [⟨['c', 'h', 'a', 's', 'h', 'n', 'a'], ['l', 'i', 'k', 'e', '.', 't', 'h', 'i', 's'], none⟩, ⟨['m', 'i'], ['m', 'i'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Two individuals are discussing Juan's whereabouts. One of them shares the news that Juan stole a cow. They were told that Juan did so, and they trust the source."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("prior", "reportativeEvidential"), ("focus", "clause")] }

def fn9_i : Datum :=
  { id := "martinezvera2026_fn9_i"
    source := ⟨"martinez-vera-2026", "fn. 9 (i)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Juanchu-ka mayu-man ri-shka; mana shina=mi ka-shka-nka."
    glossedTokens := [("Juanchu-ka", "Juan-TOP"), ("mayu-man", "river-DIR"), ("ri-shka", "go-PST2"), ("mana", "no"), ("shina=mi", "like.this=mi"), ("ka-shka-nka", "be-PST2-CONJ")]
    glossedWords := [⟨['J', 'u', 'a', 'n', 'c', 'h', 'u', '-', 'k', 'a'], ['J', 'u', 'a', 'n', '-', 'T', 'O', 'P'], [⟨['J', 'u', 'a', 'n', 'c', 'h', 'u'], ['J', 'u', 'a', 'n'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['m', 'a', 'y', 'u', '-', 'm', 'a', 'n'], ['r', 'i', 'v', 'e', 'r', '-', 'D', 'I', 'R'], [⟨['m', 'a', 'y', 'u'], ['r', 'i', 'v', 'e', 'r'], none⟩, ⟨['m', 'a', 'n'], ['D', 'I', 'R'], some '-'⟩]⟩, ⟨['r', 'i', '-', 's', 'h', 'k', 'a'], ['g', 'o', '-', 'P', 'S', 'T', '2'], [⟨['r', 'i'], ['g', 'o'], none⟩, ⟨['s', 'h', 'k', 'a'], ['P', 'S', 'T', '2'], some '-'⟩]⟩, ⟨['m', 'a', 'n', 'a'], ['n', 'o'], [⟨['m', 'a', 'n', 'a'], ['n', 'o'], none⟩]⟩, ⟨['s', 'h', 'i', 'n', 'a', '=', 'm', 'i'], ['l', 'i', 'k', 'e', '.', 't', 'h', 'i', 's', '=', 'm', 'i'], [⟨['s', 'h', 'i', 'n', 'a'], ['l', 'i', 'k', 'e', '.', 't', 'h', 'i', 's'], none⟩, ⟨['m', 'i'], ['m', 'i'], some '='⟩]⟩, ⟨['k', 'a', '-', 's', 'h', 'k', 'a', '-', 'n', 'k', 'a'], ['b', 'e', '-', 'P', 'S', 'T', '2', '-', 'C', 'O', 'N', 'J'], [⟨['k', 'a'], ['b', 'e'], none⟩, ⟨['s', 'h', 'k', 'a'], ['P', 'S', 'T', '2'], some '-'⟩, ⟨['n', 'k', 'a'], ['C', 'O', 'N', 'J'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Two individuals are discussing Juan's whereabouts. One of them shares the news that Juan went to the river. They were told that Juan did so, but they don't trust the source."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("prior", "reportativeEvidential"), ("focus", "clause"), ("polarity", "negative")] }

def fn10_i : Datum :=
  { id := "martinezvera2026_fn10_i"
    source := ⟨"martinez-vera-2026", "fn. 10 (i)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Juanchu-ka shuk wakra-ta shuwa-shka; chashna=mi, chay-ka mana shina-chu."
    glossedTokens := [("Juanchu-ka", "Juan-TOP"), ("shuk", "one"), ("wakra-ta", "cow-ACC"), ("shuwa-shka", "steal-PST2"), ("chashna=mi", "like.this=mi"), ("chay-ka", "that-TOP"), ("mana", "no"), ("shina-chu", "like.that-POL")]
    glossedWords := [⟨['J', 'u', 'a', 'n', 'c', 'h', 'u', '-', 'k', 'a'], ['J', 'u', 'a', 'n', '-', 'T', 'O', 'P'], [⟨['J', 'u', 'a', 'n', 'c', 'h', 'u'], ['J', 'u', 'a', 'n'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['s', 'h', 'u', 'k'], ['o', 'n', 'e'], [⟨['s', 'h', 'u', 'k'], ['o', 'n', 'e'], none⟩]⟩, ⟨['w', 'a', 'k', 'r', 'a', '-', 't', 'a'], ['c', 'o', 'w', '-', 'A', 'C', 'C'], [⟨['w', 'a', 'k', 'r', 'a'], ['c', 'o', 'w'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['s', 'h', 'u', 'w', 'a', '-', 's', 'h', 'k', 'a'], ['s', 't', 'e', 'a', 'l', '-', 'P', 'S', 'T', '2'], [⟨['s', 'h', 'u', 'w', 'a'], ['s', 't', 'e', 'a', 'l'], none⟩, ⟨['s', 'h', 'k', 'a'], ['P', 'S', 'T', '2'], some '-'⟩]⟩, ⟨['c', 'h', 'a', 's', 'h', 'n', 'a', '=', 'm', 'i'], ['l', 'i', 'k', 'e', '.', 't', 'h', 'i', 's', '=', 'm', 'i'], [⟨['c', 'h', 'a', 's', 'h', 'n', 'a'], ['l', 'i', 'k', 'e', '.', 't', 'h', 'i', 's'], none⟩, ⟨['m', 'i'], ['m', 'i'], some '='⟩]⟩, ⟨['c', 'h', 'a', 'y', '-', 'k', 'a'], ['t', 'h', 'a', 't', '-', 'T', 'O', 'P'], [⟨['c', 'h', 'a', 'y'], ['t', 'h', 'a', 't'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['m', 'a', 'n', 'a'], ['n', 'o'], [⟨['m', 'a', 'n', 'a'], ['n', 'o'], none⟩]⟩, ⟨['s', 'h', 'i', 'n', 'a', '-', 'c', 'h', 'u'], ['l', 'i', 'k', 'e', '.', 't', 'h', 'a', 't', '-', 'P', 'O', 'L'], [⟨['s', 'h', 'i', 'n', 'a'], ['l', 'i', 'k', 'e', '.', 't', 'h', 'a', 't'], none⟩, ⟨['c', 'h', 'u'], ['P', 'O', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("evidential", "reportative"), ("continuation", "confirmsThenDeniesScope")] }

def ex_22 : Datum :=
  { id := "martinezvera2026_22"
    source := ⟨"martinez-vera-2026", "(22)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Juanchu-ka wakra-ta ranti-rka. Mana, kuchi-ta=mi ranti-rka."
    glossedTokens := [("Juanchu-ka", "Juan-TOP"), ("wakra-ta", "cow-ACC"), ("ranti-rka", "buy-PST1"), ("Mana", "no"), ("kuchi-ta=mi", "pig-ACC=mi"), ("ranti-rka", "buy-PST1")]
    glossedWords := [⟨['J', 'u', 'a', 'n', 'c', 'h', 'u', '-', 'k', 'a'], ['J', 'u', 'a', 'n', '-', 'T', 'O', 'P'], [⟨['J', 'u', 'a', 'n', 'c', 'h', 'u'], ['J', 'u', 'a', 'n'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['w', 'a', 'k', 'r', 'a', '-', 't', 'a'], ['c', 'o', 'w', '-', 'A', 'C', 'C'], [⟨['w', 'a', 'k', 'r', 'a'], ['c', 'o', 'w'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['r', 'a', 'n', 't', 'i', '-', 'r', 'k', 'a'], ['b', 'u', 'y', '-', 'P', 'S', 'T', '1'], [⟨['r', 'a', 'n', 't', 'i'], ['b', 'u', 'y'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩]⟩, ⟨['M', 'a', 'n', 'a'], ['n', 'o'], [⟨['M', 'a', 'n', 'a'], ['n', 'o'], none⟩]⟩, ⟨['k', 'u', 'c', 'h', 'i', '-', 't', 'a', '=', 'm', 'i'], ['p', 'i', 'g', '-', 'A', 'C', 'C', '=', 'm', 'i'], [⟨['k', 'u', 'c', 'h', 'i'], ['p', 'i', 'g'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩, ⟨['m', 'i'], ['m', 'i'], some '='⟩]⟩, ⟨['r', 'a', 'n', 't', 'i', '-', 'r', 'k', 'a'], ['b', 'u', 'y', '-', 'P', 'S', 'T', '1'], [⟨['r', 'a', 'n', 't', 'i'], ['b', 'u', 'y'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Two discourse participants are discussing the issue of what it was (i.e., what farm animal) that Juan bought, e.g., at the Sunday market."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("prior", "correction"), ("focus", "object"), ("contrast", "object")] }

def ex_23 : Datum :=
  { id := "martinezvera2026_23"
    source := ⟨"martinez-vera-2026", "(23)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Juanchu oveja-ta ranti-rka. Mana, Maria=mi oveja-ta ranti-rka."
    glossedTokens := [("Juanchu", "Juan"), ("oveja-ta", "sheep-ACC"), ("ranti-rka", "buy-PST1"), ("Mana", "no"), ("Maria=mi", "Maria=mi"), ("oveja-ta", "sheep-ACC"), ("ranti-rka", "buy-PST1")]
    glossedWords := [⟨['J', 'u', 'a', 'n', 'c', 'h', 'u'], ['J', 'u', 'a', 'n'], [⟨['J', 'u', 'a', 'n', 'c', 'h', 'u'], ['J', 'u', 'a', 'n'], none⟩]⟩, ⟨['o', 'v', 'e', 'j', 'a', '-', 't', 'a'], ['s', 'h', 'e', 'e', 'p', '-', 'A', 'C', 'C'], [⟨['o', 'v', 'e', 'j', 'a'], ['s', 'h', 'e', 'e', 'p'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['r', 'a', 'n', 't', 'i', '-', 'r', 'k', 'a'], ['b', 'u', 'y', '-', 'P', 'S', 'T', '1'], [⟨['r', 'a', 'n', 't', 'i'], ['b', 'u', 'y'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩]⟩, ⟨['M', 'a', 'n', 'a'], ['n', 'o'], [⟨['M', 'a', 'n', 'a'], ['n', 'o'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a', '=', 'm', 'i'], ['M', 'a', 'r', 'i', 'a', '=', 'm', 'i'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩, ⟨['m', 'i'], ['m', 'i'], some '='⟩]⟩, ⟨['o', 'v', 'e', 'j', 'a', '-', 't', 'a'], ['s', 'h', 'e', 'e', 'p', '-', 'A', 'C', 'C'], [⟨['o', 'v', 'e', 'j', 'a'], ['s', 'h', 'e', 'e', 'p'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['r', 'a', 'n', 't', 'i', '-', 'r', 'k', 'a'], ['b', 'u', 'y', '-', 'P', 'S', 'T', '1'], [⟨['r', 'a', 'n', 't', 'i'], ['b', 'u', 'y'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Two discourse participants are discussing the issue of who bought a sheep at the Sunday market."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("prior", "correction"), ("focus", "subject"), ("contrast", "subject")] }

def ex_25 : Datum :=
  { id := "martinezvera2026_25"
    source := ⟨"martinez-vera-2026", "(25)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Pedro-ka mina-man ri-rka. Mana, Pedro-ka mayu-man=mi ri-rka."
    glossedTokens := [("Pedro-ka", "Pedro-TOP"), ("mina-man", "mine-DIR"), ("ri-rka", "go-PST1"), ("Mana", "no"), ("Pedro-ka", "Pedro-TOP"), ("mayu-man=mi", "river-DIR=mi"), ("ri-rka", "go-PST1")]
    glossedWords := [⟨['P', 'e', 'd', 'r', 'o', '-', 'k', 'a'], ['P', 'e', 'd', 'r', 'o', '-', 'T', 'O', 'P'], [⟨['P', 'e', 'd', 'r', 'o'], ['P', 'e', 'd', 'r', 'o'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['m', 'i', 'n', 'a', '-', 'm', 'a', 'n'], ['m', 'i', 'n', 'e', '-', 'D', 'I', 'R'], [⟨['m', 'i', 'n', 'a'], ['m', 'i', 'n', 'e'], none⟩, ⟨['m', 'a', 'n'], ['D', 'I', 'R'], some '-'⟩]⟩, ⟨['r', 'i', '-', 'r', 'k', 'a'], ['g', 'o', '-', 'P', 'S', 'T', '1'], [⟨['r', 'i'], ['g', 'o'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩]⟩, ⟨['M', 'a', 'n', 'a'], ['n', 'o'], [⟨['M', 'a', 'n', 'a'], ['n', 'o'], none⟩]⟩, ⟨['P', 'e', 'd', 'r', 'o', '-', 'k', 'a'], ['P', 'e', 'd', 'r', 'o', '-', 'T', 'O', 'P'], [⟨['P', 'e', 'd', 'r', 'o'], ['P', 'e', 'd', 'r', 'o'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['m', 'a', 'y', 'u', '-', 'm', 'a', 'n', '=', 'm', 'i'], ['r', 'i', 'v', 'e', 'r', '-', 'D', 'I', 'R', '=', 'm', 'i'], [⟨['m', 'a', 'y', 'u'], ['r', 'i', 'v', 'e', 'r'], none⟩, ⟨['m', 'a', 'n'], ['D', 'I', 'R'], some '-'⟩, ⟨['m', 'i'], ['m', 'i'], some '='⟩]⟩, ⟨['r', 'i', '-', 'r', 'k', 'a'], ['g', 'o', '-', 'P', 'S', 'T', '1'], [⟨['r', 'i'], ['g', 'o'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Two discourse participants are discussing Pedro's whereabouts, in particular, where he went for the day."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("prior", "correction"), ("focus", "goal"), ("contrast", "goal")] }

def ex_26 : Datum :=
  { id := "martinezvera2026_26"
    source := ⟨"martinez-vera-2026", "(26)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Pedro-ka mina-man ri-rka. Mana, Pedro-ka mikuna-kuna-ta mercado-pi ranti-chi-rka=mi."
    glossedTokens := [("Pedro-ka", "Pedro-TOP"), ("mina-man", "mine-DIR"), ("ri-rka", "go-PST1"), ("Mana", "no"), ("Pedro-ka", "Pedro-TOP"), ("mikuna-kuna-ta", "food-PL-ACC"), ("mercado-pi", "market-LOC"), ("ranti-chi-rka=mi", "buy-CAUS-PST1=mi")]
    glossedWords := [⟨['P', 'e', 'd', 'r', 'o', '-', 'k', 'a'], ['P', 'e', 'd', 'r', 'o', '-', 'T', 'O', 'P'], [⟨['P', 'e', 'd', 'r', 'o'], ['P', 'e', 'd', 'r', 'o'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['m', 'i', 'n', 'a', '-', 'm', 'a', 'n'], ['m', 'i', 'n', 'e', '-', 'D', 'I', 'R'], [⟨['m', 'i', 'n', 'a'], ['m', 'i', 'n', 'e'], none⟩, ⟨['m', 'a', 'n'], ['D', 'I', 'R'], some '-'⟩]⟩, ⟨['r', 'i', '-', 'r', 'k', 'a'], ['g', 'o', '-', 'P', 'S', 'T', '1'], [⟨['r', 'i'], ['g', 'o'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩]⟩, ⟨['M', 'a', 'n', 'a'], ['n', 'o'], [⟨['M', 'a', 'n', 'a'], ['n', 'o'], none⟩]⟩, ⟨['P', 'e', 'd', 'r', 'o', '-', 'k', 'a'], ['P', 'e', 'd', 'r', 'o', '-', 'T', 'O', 'P'], [⟨['P', 'e', 'd', 'r', 'o'], ['P', 'e', 'd', 'r', 'o'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['m', 'i', 'k', 'u', 'n', 'a', '-', 'k', 'u', 'n', 'a', '-', 't', 'a'], ['f', 'o', 'o', 'd', '-', 'P', 'L', '-', 'A', 'C', 'C'], [⟨['m', 'i', 'k', 'u', 'n', 'a'], ['f', 'o', 'o', 'd'], none⟩, ⟨['k', 'u', 'n', 'a'], ['P', 'L'], some '-'⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['m', 'e', 'r', 'c', 'a', 'd', 'o', '-', 'p', 'i'], ['m', 'a', 'r', 'k', 'e', 't', '-', 'L', 'O', 'C'], [⟨['m', 'e', 'r', 'c', 'a', 'd', 'o'], ['m', 'a', 'r', 'k', 'e', 't'], none⟩, ⟨['p', 'i'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['r', 'a', 'n', 't', 'i', '-', 'c', 'h', 'i', '-', 'r', 'k', 'a', '=', 'm', 'i'], ['b', 'u', 'y', '-', 'C', 'A', 'U', 'S', '-', 'P', 'S', 'T', '1', '=', 'm', 'i'], [⟨['r', 'a', 'n', 't', 'i'], ['b', 'u', 'y'], none⟩, ⟨['c', 'h', 'i'], ['C', 'A', 'U', 'S'], some '-'⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩, ⟨['m', 'i'], ['m', 'i'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Two individuals are discussing Pedro's whereabouts. Since heading to the mine is an activity that takes all day, it excludes any other activity."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("prior", "correction"), ("focus", "verbPhrase"), ("contrast", "verbPhrase")] }

def ex_27b : Datum :=
  { id := "martinezvera2026_27b"
    source := ⟨"martinez-vera-2026", "(27b)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Segundo kuchita-ta ranti-rka. Mana, Segundo wakra-ta=mi ranti-rka."
    glossedTokens := [("Segundo", "Segundo"), ("kuchita-ta", "pig-ACC"), ("ranti-rka", "buy-PST1"), ("Mana", "no"), ("Segundo", "Segundo"), ("wakra-ta=mi", "cow-ACC=mi"), ("ranti-rka", "buy-PST1")]
    glossedWords := [⟨['S', 'e', 'g', 'u', 'n', 'd', 'o'], ['S', 'e', 'g', 'u', 'n', 'd', 'o'], [⟨['S', 'e', 'g', 'u', 'n', 'd', 'o'], ['S', 'e', 'g', 'u', 'n', 'd', 'o'], none⟩]⟩, ⟨['k', 'u', 'c', 'h', 'i', 't', 'a', '-', 't', 'a'], ['p', 'i', 'g', '-', 'A', 'C', 'C'], [⟨['k', 'u', 'c', 'h', 'i', 't', 'a'], ['p', 'i', 'g'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['r', 'a', 'n', 't', 'i', '-', 'r', 'k', 'a'], ['b', 'u', 'y', '-', 'P', 'S', 'T', '1'], [⟨['r', 'a', 'n', 't', 'i'], ['b', 'u', 'y'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩]⟩, ⟨['M', 'a', 'n', 'a'], ['n', 'o'], [⟨['M', 'a', 'n', 'a'], ['n', 'o'], none⟩]⟩, ⟨['S', 'e', 'g', 'u', 'n', 'd', 'o'], ['S', 'e', 'g', 'u', 'n', 'd', 'o'], [⟨['S', 'e', 'g', 'u', 'n', 'd', 'o'], ['S', 'e', 'g', 'u', 'n', 'd', 'o'], none⟩]⟩, ⟨['w', 'a', 'k', 'r', 'a', '-', 't', 'a', '=', 'm', 'i'], ['c', 'o', 'w', '-', 'A', 'C', 'C', '=', 'm', 'i'], [⟨['w', 'a', 'k', 'r', 'a'], ['c', 'o', 'w'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩, ⟨['m', 'i'], ['m', 'i'], some '='⟩]⟩, ⟨['r', 'a', 'n', 't', 'i', '-', 'r', 'k', 'a'], ['b', 'u', 'y', '-', 'P', 'S', 'T', '1'], [⟨['r', 'a', 'n', 't', 'i'], ['b', 'u', 'y'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Two discourse participants are discussing the issue of what it was (i.e., what farm animal) that Juan bought, e.g., at the Sunday market."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("prior", "correction"), ("focus", "object"), ("contrast", "object")] }

def ex_27c : Datum :=
  { id := "martinezvera2026_27c"
    source := ⟨"martinez-vera-2026", "(27c)"⟩
    reportedIn := none
    method := some .elicitation
    language := "loja1235"
    primaryText := "Segundo kuchita-ta ranti-rka. Mana, Segundo=mi wakra-ta ranti-rka."
    glossedTokens := [("Segundo", "Segundo"), ("kuchita-ta", "pig-ACC"), ("ranti-rka", "buy-PST1"), ("Mana", "no"), ("Segundo=mi", "Segundo=mi"), ("wakra-ta", "cow-ACC"), ("ranti-rka", "buy-PST1")]
    glossedWords := [⟨['S', 'e', 'g', 'u', 'n', 'd', 'o'], ['S', 'e', 'g', 'u', 'n', 'd', 'o'], [⟨['S', 'e', 'g', 'u', 'n', 'd', 'o'], ['S', 'e', 'g', 'u', 'n', 'd', 'o'], none⟩]⟩, ⟨['k', 'u', 'c', 'h', 'i', 't', 'a', '-', 't', 'a'], ['p', 'i', 'g', '-', 'A', 'C', 'C'], [⟨['k', 'u', 'c', 'h', 'i', 't', 'a'], ['p', 'i', 'g'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['r', 'a', 'n', 't', 'i', '-', 'r', 'k', 'a'], ['b', 'u', 'y', '-', 'P', 'S', 'T', '1'], [⟨['r', 'a', 'n', 't', 'i'], ['b', 'u', 'y'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩]⟩, ⟨['M', 'a', 'n', 'a'], ['n', 'o'], [⟨['M', 'a', 'n', 'a'], ['n', 'o'], none⟩]⟩, ⟨['S', 'e', 'g', 'u', 'n', 'd', 'o', '=', 'm', 'i'], ['S', 'e', 'g', 'u', 'n', 'd', 'o', '=', 'm', 'i'], [⟨['S', 'e', 'g', 'u', 'n', 'd', 'o'], ['S', 'e', 'g', 'u', 'n', 'd', 'o'], none⟩, ⟨['m', 'i'], ['m', 'i'], some '='⟩]⟩, ⟨['w', 'a', 'k', 'r', 'a', '-', 't', 'a'], ['c', 'o', 'w', '-', 'A', 'C', 'C'], [⟨['w', 'a', 'k', 'r', 'a'], ['c', 'o', 'w'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['r', 'a', 'n', 't', 'i', '-', 'r', 'k', 'a'], ['b', 'u', 'y', '-', 'P', 'S', 'T', '1'], [⟨['r', 'a', 'n', 't', 'i'], ['b', 'u', 'y'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Two discourse participants are discussing the issue of what it was (i.e., what farm animal) that Juan bought, e.g., at the Sunday market."
    judgment := .unacceptable
    contrasts := [("Mana, Segundo wakra-ta ranti-rka.", .acceptable)]
    readings := []
    paperFeatures := [("prior", "correction"), ("focus", "subject"), ("contrast", "object")] }

def ex_27d : Datum :=
  { id := "martinezvera2026_27d"
    source := ⟨"martinez-vera-2026", "(27d)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Segundo kuchita-ta ranti-rka. Mana, Segundo wakra-ta ranti-rka=mi."
    glossedTokens := [("Segundo", "Segundo"), ("kuchita-ta", "pig-ACC"), ("ranti-rka", "buy-PST1"), ("Mana", "no"), ("Segundo", "Segundo"), ("wakra-ta", "cow-ACC"), ("ranti-rka=mi", "buy-PST1=mi")]
    glossedWords := [⟨['S', 'e', 'g', 'u', 'n', 'd', 'o'], ['S', 'e', 'g', 'u', 'n', 'd', 'o'], [⟨['S', 'e', 'g', 'u', 'n', 'd', 'o'], ['S', 'e', 'g', 'u', 'n', 'd', 'o'], none⟩]⟩, ⟨['k', 'u', 'c', 'h', 'i', 't', 'a', '-', 't', 'a'], ['p', 'i', 'g', '-', 'A', 'C', 'C'], [⟨['k', 'u', 'c', 'h', 'i', 't', 'a'], ['p', 'i', 'g'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['r', 'a', 'n', 't', 'i', '-', 'r', 'k', 'a'], ['b', 'u', 'y', '-', 'P', 'S', 'T', '1'], [⟨['r', 'a', 'n', 't', 'i'], ['b', 'u', 'y'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩]⟩, ⟨['M', 'a', 'n', 'a'], ['n', 'o'], [⟨['M', 'a', 'n', 'a'], ['n', 'o'], none⟩]⟩, ⟨['S', 'e', 'g', 'u', 'n', 'd', 'o'], ['S', 'e', 'g', 'u', 'n', 'd', 'o'], [⟨['S', 'e', 'g', 'u', 'n', 'd', 'o'], ['S', 'e', 'g', 'u', 'n', 'd', 'o'], none⟩]⟩, ⟨['w', 'a', 'k', 'r', 'a', '-', 't', 'a'], ['c', 'o', 'w', '-', 'A', 'C', 'C'], [⟨['w', 'a', 'k', 'r', 'a'], ['c', 'o', 'w'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['r', 'a', 'n', 't', 'i', '-', 'r', 'k', 'a', '=', 'm', 'i'], ['b', 'u', 'y', '-', 'P', 'S', 'T', '1', '=', 'm', 'i'], [⟨['r', 'a', 'n', 't', 'i'], ['b', 'u', 'y'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩, ⟨['m', 'i'], ['m', 'i'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Two discourse participants are discussing the issue of what it was (i.e., what farm animal) that Juan bought, e.g., at the Sunday market."
    judgment := .unacceptable
    contrasts := [("Mana, Segundo wakra-ta ranti-rka.", .acceptable)]
    readings := []
    paperFeatures := [("prior", "correction"), ("focus", "verb"), ("contrast", "object")] }

def ex_28_modifier : Datum :=
  { id := "martinezvera2026_28_modifier"
    source := ⟨"martinez-vera-2026", "(28)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Shuk Estados Unidos-manta ashpapi llankak Canada-manta=mi ashpapi llankak-wan tupanaku-n."
    glossedTokens := [("Shuk", "a"), ("Estados", "United"), ("Unidos-manta", "States-ABL"), ("ashpapi", "land.LOC"), ("llankak", "work.NMLZ"), ("Canada-manta=mi", "Canada-ABL=mi"), ("ashpapi", "land.LOC"), ("llankak-wan", "work.NMLZ-INST"), ("tupanaku-n", "meet-3")]
    glossedWords := [⟨['S', 'h', 'u', 'k'], ['a'], [⟨['S', 'h', 'u', 'k'], ['a'], none⟩]⟩, ⟨['E', 's', 't', 'a', 'd', 'o', 's'], ['U', 'n', 'i', 't', 'e', 'd'], [⟨['E', 's', 't', 'a', 'd', 'o', 's'], ['U', 'n', 'i', 't', 'e', 'd'], none⟩]⟩, ⟨['U', 'n', 'i', 'd', 'o', 's', '-', 'm', 'a', 'n', 't', 'a'], ['S', 't', 'a', 't', 'e', 's', '-', 'A', 'B', 'L'], [⟨['U', 'n', 'i', 'd', 'o', 's'], ['S', 't', 'a', 't', 'e', 's'], none⟩, ⟨['m', 'a', 'n', 't', 'a'], ['A', 'B', 'L'], some '-'⟩]⟩, ⟨['a', 's', 'h', 'p', 'a', 'p', 'i'], ['l', 'a', 'n', 'd', '.', 'L', 'O', 'C'], [⟨['a', 's', 'h', 'p', 'a', 'p', 'i'], ['l', 'a', 'n', 'd', '.', 'L', 'O', 'C'], none⟩]⟩, ⟨['l', 'l', 'a', 'n', 'k', 'a', 'k'], ['w', 'o', 'r', 'k', '.', 'N', 'M', 'L', 'Z'], [⟨['l', 'l', 'a', 'n', 'k', 'a', 'k'], ['w', 'o', 'r', 'k', '.', 'N', 'M', 'L', 'Z'], none⟩]⟩, ⟨['C', 'a', 'n', 'a', 'd', 'a', '-', 'm', 'a', 'n', 't', 'a', '=', 'm', 'i'], ['C', 'a', 'n', 'a', 'd', 'a', '-', 'A', 'B', 'L', '=', 'm', 'i'], [⟨['C', 'a', 'n', 'a', 'd', 'a'], ['C', 'a', 'n', 'a', 'd', 'a'], none⟩, ⟨['m', 'a', 'n', 't', 'a'], ['A', 'B', 'L'], some '-'⟩, ⟨['m', 'i'], ['m', 'i'], some '='⟩]⟩, ⟨['a', 's', 'h', 'p', 'a', 'p', 'i'], ['l', 'a', 'n', 'd', '.', 'L', 'O', 'C'], [⟨['a', 's', 'h', 'p', 'a', 'p', 'i'], ['l', 'a', 'n', 'd', '.', 'L', 'O', 'C'], none⟩]⟩, ⟨['l', 'l', 'a', 'n', 'k', 'a', 'k', '-', 'w', 'a', 'n'], ['w', 'o', 'r', 'k', '.', 'N', 'M', 'L', 'Z', '-', 'I', 'N', 'S', 'T'], [⟨['l', 'l', 'a', 'n', 'k', 'a', 'k'], ['w', 'o', 'r', 'k', '.', 'N', 'M', 'L', 'Z'], none⟩, ⟨['w', 'a', 'n'], ['I', 'N', 'S', 'T'], some '-'⟩]⟩, ⟨['t', 'u', 'p', 'a', 'n', 'a', 'k', 'u', '-', 'n'], ['m', 'e', 'e', 't', '-', '3'], [⟨['t', 'u', 'p', 'a', 'n', 'a', 'k', 'u'], ['m', 'e', 'e', 't'], none⟩, ⟨['n'], ['3'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    contrasts := [("Shuk Estados Unidos-manta ashpapi llankak Canada-manta ashpapi llankak-wan tupanaku-n.", .acceptable)]
    readings := []
    paperFeatures := [("prior", "none"), ("focus", "modifier")] }

def ex_28_object : Datum :=
  { id := "martinezvera2026_28_object"
    source := ⟨"martinez-vera-2026", "(28)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Shuk Estados Unidos-manta ashpapi llankak Canada-manta ashpapi llankak-wan=mi tupanaku-n."
    glossedTokens := [("Shuk", "a"), ("Estados", "United"), ("Unidos-manta", "States-ABL"), ("ashpapi", "land.LOC"), ("llankak", "work.NMLZ"), ("Canada-manta", "Canada-ABL"), ("ashpapi", "land.LOC"), ("llankak-wan=mi", "work.NMLZ-INST=mi"), ("tupanaku-n", "meet-3")]
    glossedWords := [⟨['S', 'h', 'u', 'k'], ['a'], [⟨['S', 'h', 'u', 'k'], ['a'], none⟩]⟩, ⟨['E', 's', 't', 'a', 'd', 'o', 's'], ['U', 'n', 'i', 't', 'e', 'd'], [⟨['E', 's', 't', 'a', 'd', 'o', 's'], ['U', 'n', 'i', 't', 'e', 'd'], none⟩]⟩, ⟨['U', 'n', 'i', 'd', 'o', 's', '-', 'm', 'a', 'n', 't', 'a'], ['S', 't', 'a', 't', 'e', 's', '-', 'A', 'B', 'L'], [⟨['U', 'n', 'i', 'd', 'o', 's'], ['S', 't', 'a', 't', 'e', 's'], none⟩, ⟨['m', 'a', 'n', 't', 'a'], ['A', 'B', 'L'], some '-'⟩]⟩, ⟨['a', 's', 'h', 'p', 'a', 'p', 'i'], ['l', 'a', 'n', 'd', '.', 'L', 'O', 'C'], [⟨['a', 's', 'h', 'p', 'a', 'p', 'i'], ['l', 'a', 'n', 'd', '.', 'L', 'O', 'C'], none⟩]⟩, ⟨['l', 'l', 'a', 'n', 'k', 'a', 'k'], ['w', 'o', 'r', 'k', '.', 'N', 'M', 'L', 'Z'], [⟨['l', 'l', 'a', 'n', 'k', 'a', 'k'], ['w', 'o', 'r', 'k', '.', 'N', 'M', 'L', 'Z'], none⟩]⟩, ⟨['C', 'a', 'n', 'a', 'd', 'a', '-', 'm', 'a', 'n', 't', 'a'], ['C', 'a', 'n', 'a', 'd', 'a', '-', 'A', 'B', 'L'], [⟨['C', 'a', 'n', 'a', 'd', 'a'], ['C', 'a', 'n', 'a', 'd', 'a'], none⟩, ⟨['m', 'a', 'n', 't', 'a'], ['A', 'B', 'L'], some '-'⟩]⟩, ⟨['a', 's', 'h', 'p', 'a', 'p', 'i'], ['l', 'a', 'n', 'd', '.', 'L', 'O', 'C'], [⟨['a', 's', 'h', 'p', 'a', 'p', 'i'], ['l', 'a', 'n', 'd', '.', 'L', 'O', 'C'], none⟩]⟩, ⟨['l', 'l', 'a', 'n', 'k', 'a', 'k', '-', 'w', 'a', 'n', '=', 'm', 'i'], ['w', 'o', 'r', 'k', '.', 'N', 'M', 'L', 'Z', '-', 'I', 'N', 'S', 'T', '=', 'm', 'i'], [⟨['l', 'l', 'a', 'n', 'k', 'a', 'k'], ['w', 'o', 'r', 'k', '.', 'N', 'M', 'L', 'Z'], none⟩, ⟨['w', 'a', 'n'], ['I', 'N', 'S', 'T'], some '-'⟩, ⟨['m', 'i'], ['m', 'i'], some '='⟩]⟩, ⟨['t', 'u', 'p', 'a', 'n', 'a', 'k', 'u', '-', 'n'], ['m', 'e', 'e', 't', '-', '3'], [⟨['t', 'u', 'p', 'a', 'n', 'a', 'k', 'u'], ['m', 'e', 'e', 't'], none⟩, ⟨['n'], ['3'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    contrasts := [("Shuk Estados Unidos-manta ashpapi llankak Canada-manta ashpapi llankak-wan tupanaku-n.", .acceptable)]
    readings := []
    paperFeatures := [("prior", "none"), ("focus", "object")] }

def ex_29b : Datum :=
  { id := "martinezvera2026_29b"
    source := ⟨"martinez-vera-2026", "(29b)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Pedro-ka ima-ta ranti-rka? Pedro-ka oveja-ta=mi ranti-rka."
    glossedTokens := [("Pedro-ka", "Pedro-TOP"), ("ima-ta", "what-ACC"), ("ranti-rka", "buy-PST1"), ("Pedro-ka", "Pedro-TOP"), ("oveja-ta=mi", "sheep-ACC=mi"), ("ranti-rka", "buy-PST1")]
    glossedWords := [⟨['P', 'e', 'd', 'r', 'o', '-', 'k', 'a'], ['P', 'e', 'd', 'r', 'o', '-', 'T', 'O', 'P'], [⟨['P', 'e', 'd', 'r', 'o'], ['P', 'e', 'd', 'r', 'o'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['i', 'm', 'a', '-', 't', 'a'], ['w', 'h', 'a', 't', '-', 'A', 'C', 'C'], [⟨['i', 'm', 'a'], ['w', 'h', 'a', 't'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['r', 'a', 'n', 't', 'i', '-', 'r', 'k', 'a'], ['b', 'u', 'y', '-', 'P', 'S', 'T', '1'], [⟨['r', 'a', 'n', 't', 'i'], ['b', 'u', 'y'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩]⟩, ⟨['P', 'e', 'd', 'r', 'o', '-', 'k', 'a'], ['P', 'e', 'd', 'r', 'o', '-', 'T', 'O', 'P'], [⟨['P', 'e', 'd', 'r', 'o'], ['P', 'e', 'd', 'r', 'o'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['o', 'v', 'e', 'j', 'a', '-', 't', 'a', '=', 'm', 'i'], ['s', 'h', 'e', 'e', 'p', '-', 'A', 'C', 'C', '=', 'm', 'i'], [⟨['o', 'v', 'e', 'j', 'a'], ['s', 'h', 'e', 'e', 'p'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩, ⟨['m', 'i'], ['m', 'i'], some '='⟩]⟩, ⟨['r', 'a', 'n', 't', 'i', '-', 'r', 'k', 'a'], ['b', 'u', 'y', '-', 'P', 'S', 'T', '1'], [⟨['r', 'a', 'n', 't', 'i'], ['b', 'u', 'y'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "An individual asks another one about the farm animal that Pedro bought at the Sunday market."
    judgment := .unacceptable
    contrasts := [("Pedro-ka oveja-ta ranti-rka.", .acceptable)]
    readings := []
    paperFeatures := [("prior", "none"), ("question", "constituent"), ("focus", "object")] }

def ex_29c : Datum :=
  { id := "martinezvera2026_29c"
    source := ⟨"martinez-vera-2026", "(29c)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Pedro-ka ima-ta ranti-rka? Oveja-ta=mi Pedro-ka ranti-rka."
    glossedTokens := [("Pedro-ka", "Pedro-TOP"), ("ima-ta", "what-ACC"), ("ranti-rka", "buy-PST1"), ("Oveja-ta=mi", "sheep-ACC=mi"), ("Pedro-ka", "Pedro-TOP"), ("ranti-rka", "buy-PST1")]
    glossedWords := [⟨['P', 'e', 'd', 'r', 'o', '-', 'k', 'a'], ['P', 'e', 'd', 'r', 'o', '-', 'T', 'O', 'P'], [⟨['P', 'e', 'd', 'r', 'o'], ['P', 'e', 'd', 'r', 'o'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['i', 'm', 'a', '-', 't', 'a'], ['w', 'h', 'a', 't', '-', 'A', 'C', 'C'], [⟨['i', 'm', 'a'], ['w', 'h', 'a', 't'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['r', 'a', 'n', 't', 'i', '-', 'r', 'k', 'a'], ['b', 'u', 'y', '-', 'P', 'S', 'T', '1'], [⟨['r', 'a', 'n', 't', 'i'], ['b', 'u', 'y'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩]⟩, ⟨['O', 'v', 'e', 'j', 'a', '-', 't', 'a', '=', 'm', 'i'], ['s', 'h', 'e', 'e', 'p', '-', 'A', 'C', 'C', '=', 'm', 'i'], [⟨['O', 'v', 'e', 'j', 'a'], ['s', 'h', 'e', 'e', 'p'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩, ⟨['m', 'i'], ['m', 'i'], some '='⟩]⟩, ⟨['P', 'e', 'd', 'r', 'o', '-', 'k', 'a'], ['P', 'e', 'd', 'r', 'o', '-', 'T', 'O', 'P'], [⟨['P', 'e', 'd', 'r', 'o'], ['P', 'e', 'd', 'r', 'o'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['r', 'a', 'n', 't', 'i', '-', 'r', 'k', 'a'], ['b', 'u', 'y', '-', 'P', 'S', 'T', '1'], [⟨['r', 'a', 'n', 't', 'i'], ['b', 'u', 'y'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "An individual asks another one about the farm animal that Pedro bought at the Sunday market."
    judgment := .unacceptable
    contrasts := [("Oveja-ta Pedro-ka ranti-rka.", .acceptable)]
    readings := []
    paperFeatures := [("prior", "none"), ("question", "constituent"), ("focus", "object")] }

def ex_30a : Datum :=
  { id := "martinezvera2026_30a"
    source := ⟨"martinez-vera-2026", "(30a)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Pedro-ka mana oveja-ta ranti-rka; Pedro-ka wakra-ta=mi ranti-rka."
    glossedTokens := [("Pedro-ka", "Pedro-TOP"), ("mana", "no"), ("oveja-ta", "sheep-ACC"), ("ranti-rka", "buy-PST1"), ("Pedro-ka", "Pedro-TOP"), ("wakra-ta=mi", "cow-ACC=mi"), ("ranti-rka", "buy-PST1")]
    glossedWords := [⟨['P', 'e', 'd', 'r', 'o', '-', 'k', 'a'], ['P', 'e', 'd', 'r', 'o', '-', 'T', 'O', 'P'], [⟨['P', 'e', 'd', 'r', 'o'], ['P', 'e', 'd', 'r', 'o'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['m', 'a', 'n', 'a'], ['n', 'o'], [⟨['m', 'a', 'n', 'a'], ['n', 'o'], none⟩]⟩, ⟨['o', 'v', 'e', 'j', 'a', '-', 't', 'a'], ['s', 'h', 'e', 'e', 'p', '-', 'A', 'C', 'C'], [⟨['o', 'v', 'e', 'j', 'a'], ['s', 'h', 'e', 'e', 'p'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['r', 'a', 'n', 't', 'i', '-', 'r', 'k', 'a'], ['b', 'u', 'y', '-', 'P', 'S', 'T', '1'], [⟨['r', 'a', 'n', 't', 'i'], ['b', 'u', 'y'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩]⟩, ⟨['P', 'e', 'd', 'r', 'o', '-', 'k', 'a'], ['P', 'e', 'd', 'r', 'o', '-', 'T', 'O', 'P'], [⟨['P', 'e', 'd', 'r', 'o'], ['P', 'e', 'd', 'r', 'o'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['w', 'a', 'k', 'r', 'a', '-', 't', 'a', '=', 'm', 'i'], ['c', 'o', 'w', '-', 'A', 'C', 'C', '=', 'm', 'i'], [⟨['w', 'a', 'k', 'r', 'a'], ['c', 'o', 'w'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩, ⟨['m', 'i'], ['m', 'i'], some '='⟩]⟩, ⟨['r', 'a', 'n', 't', 'i', '-', 'r', 'k', 'a'], ['b', 'u', 'y', '-', 'P', 'S', 'T', '1'], [⟨['r', 'a', 'n', 't', 'i'], ['b', 'u', 'y'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "An individual communicates that the farm animal that Pedro bought was a cow, contrary to what was first thought, namely, that he bought a sheep."
    judgment := .acceptable
    contrasts := [("Pedro-ka mana oveja-ta ranti-rka; Pedro-ka wakra-ta ranti-rka.", .acceptable)]
    readings := []
    paperFeatures := [("prior", "correction"), ("focus", "object"), ("contrast", "object")] }

def ex_30b : Datum :=
  { id := "martinezvera2026_30b"
    source := ⟨"martinez-vera-2026", "(30b)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Pedro-ka mana oveja-ta ranti-rka; wakra-ta=mi Pedro-ka ranti-rka."
    glossedTokens := [("Pedro-ka", "Pedro-TOP"), ("mana", "no"), ("oveja-ta", "sheep-ACC"), ("ranti-rka", "buy-PST1"), ("wakra-ta=mi", "cow-ACC=mi"), ("Pedro-ka", "Pedro-TOP"), ("ranti-rka", "buy-PST1")]
    glossedWords := [⟨['P', 'e', 'd', 'r', 'o', '-', 'k', 'a'], ['P', 'e', 'd', 'r', 'o', '-', 'T', 'O', 'P'], [⟨['P', 'e', 'd', 'r', 'o'], ['P', 'e', 'd', 'r', 'o'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['m', 'a', 'n', 'a'], ['n', 'o'], [⟨['m', 'a', 'n', 'a'], ['n', 'o'], none⟩]⟩, ⟨['o', 'v', 'e', 'j', 'a', '-', 't', 'a'], ['s', 'h', 'e', 'e', 'p', '-', 'A', 'C', 'C'], [⟨['o', 'v', 'e', 'j', 'a'], ['s', 'h', 'e', 'e', 'p'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['r', 'a', 'n', 't', 'i', '-', 'r', 'k', 'a'], ['b', 'u', 'y', '-', 'P', 'S', 'T', '1'], [⟨['r', 'a', 'n', 't', 'i'], ['b', 'u', 'y'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩]⟩, ⟨['w', 'a', 'k', 'r', 'a', '-', 't', 'a', '=', 'm', 'i'], ['c', 'o', 'w', '-', 'A', 'C', 'C', '=', 'm', 'i'], [⟨['w', 'a', 'k', 'r', 'a'], ['c', 'o', 'w'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩, ⟨['m', 'i'], ['m', 'i'], some '='⟩]⟩, ⟨['P', 'e', 'd', 'r', 'o', '-', 'k', 'a'], ['P', 'e', 'd', 'r', 'o', '-', 'T', 'O', 'P'], [⟨['P', 'e', 'd', 'r', 'o'], ['P', 'e', 'd', 'r', 'o'], none⟩, ⟨['k', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['r', 'a', 'n', 't', 'i', '-', 'r', 'k', 'a'], ['b', 'u', 'y', '-', 'P', 'S', 'T', '1'], [⟨['r', 'a', 'n', 't', 'i'], ['b', 'u', 'y'], none⟩, ⟨['r', 'k', 'a'], ['P', 'S', 'T', '1'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "An individual communicates that the farm animal that Pedro bought was a cow, contrary to what was first thought, namely, that he bought a sheep."
    judgment := .acceptable
    contrasts := [("Pedro-ka mana oveja-ta ranti-rka; wakra-ta Pedro-ka ranti-rka.", .acceptable)]
    readings := []
    paperFeatures := [("prior", "correction"), ("focus", "object"), ("contrast", "object")] }

def all : List Datum := [ex_6, ex_7, ex_8b, ex_8c, fn5_i, ex_9, ex_10, ex_11, ex_18a, ex_18b, ex_19a, ex_19b, ex_20, ex_21, fn9_i, fn10_i, ex_22, ex_23, ex_25, ex_26, ex_27b, ex_27c, ex_27d, ex_28_modifier, ex_28_object, ex_29b, ex_29c, ex_30a, ex_30b]

end MartinezVera2026.Examples
