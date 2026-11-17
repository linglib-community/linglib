module

public import Linglib.Data.Examples.Schema

/-!
# `Deal2020` — typed example data

Auto-generated from `Linglib/Data/Examples/Deal2020.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Deal2020.Examples`.
-/

@[expose] public section

namespace Deal2020.Examples

def ex_70 : Datum :=
  { id := "deal2020_70"
    source := ⟨"deal-2020", "(70)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "Ne-’níc-em pee-∅-n-e ’in-haama-na, ’iin-im ciq’aamqal hi-twehkey’k-∅-e ’iin-e."
    glossedTokens := [("Ne-’níc-em", "1SG-older.sister-ERG"), ("pee-∅-n-e", "3/3-say-P-REM.PAST"), ("’in-haama-na,", "1SG-husband-ACC"), ("’iin-im", "1SG-GEN"), ("ciq’aamqal", "dog(ERG)"), ("hi-twehkey’k-∅-e", "3SUBJ-chase-P-REM.PAST"), ("’iin-e", "1SG-ACC")]
    glossedWords := [⟨['N', 'e', '-', '’', 'n', 'í', 'c', '-', 'e', 'm'], ['1', 'S', 'G', '-', 'o', 'l', 'd', 'e', 'r', '.', 's', 'i', 's', 't', 'e', 'r', '-', 'E', 'R', 'G'], [⟨['N', 'e'], ['1', 'S', 'G'], none⟩, ⟨['’', 'n', 'í', 'c'], ['o', 'l', 'd', 'e', 'r', '.', 's', 'i', 's', 't', 'e', 'r'], some '-'⟩, ⟨['e', 'm'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['p', 'e', 'e', '-', '∅', '-', 'n', '-', 'e'], ['3', '/', '3', '-', 's', 'a', 'y', '-', 'P', '-', 'R', 'E', 'M', '.', 'P', 'A', 'S', 'T'], [⟨['p', 'e', 'e'], ['3', '/', '3'], none⟩, ⟨['∅'], ['s', 'a', 'y'], some '-'⟩, ⟨['n'], ['P'], some '-'⟩, ⟨['e'], ['R', 'E', 'M', '.', 'P', 'A', 'S', 'T'], some '-'⟩]⟩, ⟨['’', 'i', 'n', '-', 'h', 'a', 'a', 'm', 'a', '-', 'n', 'a', ','], ['1', 'S', 'G', '-', 'h', 'u', 's', 'b', 'a', 'n', 'd', '-', 'A', 'C', 'C'], [⟨['’', 'i', 'n'], ['1', 'S', 'G'], none⟩, ⟨['h', 'a', 'a', 'm', 'a'], ['h', 'u', 's', 'b', 'a', 'n', 'd'], some '-'⟩, ⟨['n', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['’', 'i', 'i', 'n', '-', 'i', 'm'], ['1', 'S', 'G', '-', 'G', 'E', 'N'], [⟨['’', 'i', 'i', 'n'], ['1', 'S', 'G'], none⟩, ⟨['i', 'm'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['c', 'i', 'q', '’', 'a', 'a', 'm', 'q', 'a', 'l'], ['d', 'o', 'g', '(', 'E', 'R', 'G', ')'], [⟨['c', 'i', 'q', '’', 'a', 'a', 'm', 'q', 'a', 'l'], ['d', 'o', 'g', '(', 'E', 'R', 'G', ')'], none⟩]⟩, ⟨['h', 'i', '-', 't', 'w', 'e', 'h', 'k', 'e', 'y', '’', 'k', '-', '∅', '-', 'e'], ['3', 'S', 'U', 'B', 'J', '-', 'c', 'h', 'a', 's', 'e', '-', 'P', '-', 'R', 'E', 'M', '.', 'P', 'A', 'S', 'T'], [⟨['h', 'i'], ['3', 'S', 'U', 'B', 'J'], none⟩, ⟨['t', 'w', 'e', 'h', 'k', 'e', 'y', '’', 'k'], ['c', 'h', 'a', 's', 'e'], some '-'⟩, ⟨['∅'], ['P'], some '-'⟩, ⟨['e'], ['R', 'E', 'M', '.', 'P', 'A', 'S', 'T'], some '-'⟩]⟩, ⟨['’', 'i', 'i', 'n', '-', 'e'], ['1', 'S', 'G', '-', 'A', 'C', 'C'], [⟨['’', 'i', 'i', 'n'], ['1', 'S', 'G'], none⟩, ⟨['e'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("both reported", .acceptable), ("both utterance", .marginal), ("second reported only", .unacceptable), ("first reported only", .unacceptable)]
    paperFeatures := [("verb", "nezperce_say"), ("indexical", "I"), ("indexical", "I"), ("test", "shift_together")] }

def ex_73 : Datum :=
  { id := "deal2020_73"
    source := ⟨"deal-2020", "(73)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "Ne-’níc-em pee-∅-n-e ’in-haama-na, ’im-im ciq’aamqal hi-twehkey’k-∅-e ’iin-e."
    glossedTokens := [("Ne-’níc-em", "1SG-older.sister-ERG"), ("pee-∅-n-e", "3/3-say-P-REM.PAST"), ("’in-haama-na,", "1SG-husband-ACC"), ("’im-im", "2SG-GEN"), ("ciq’aamqal", "dog(ERG)"), ("hi-twehkey’k-∅-e", "3SUBJ-chase-P-REM.PAST"), ("’iin-e", "1SG-ACC")]
    glossedWords := [⟨['N', 'e', '-', '’', 'n', 'í', 'c', '-', 'e', 'm'], ['1', 'S', 'G', '-', 'o', 'l', 'd', 'e', 'r', '.', 's', 'i', 's', 't', 'e', 'r', '-', 'E', 'R', 'G'], [⟨['N', 'e'], ['1', 'S', 'G'], none⟩, ⟨['’', 'n', 'í', 'c'], ['o', 'l', 'd', 'e', 'r', '.', 's', 'i', 's', 't', 'e', 'r'], some '-'⟩, ⟨['e', 'm'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['p', 'e', 'e', '-', '∅', '-', 'n', '-', 'e'], ['3', '/', '3', '-', 's', 'a', 'y', '-', 'P', '-', 'R', 'E', 'M', '.', 'P', 'A', 'S', 'T'], [⟨['p', 'e', 'e'], ['3', '/', '3'], none⟩, ⟨['∅'], ['s', 'a', 'y'], some '-'⟩, ⟨['n'], ['P'], some '-'⟩, ⟨['e'], ['R', 'E', 'M', '.', 'P', 'A', 'S', 'T'], some '-'⟩]⟩, ⟨['’', 'i', 'n', '-', 'h', 'a', 'a', 'm', 'a', '-', 'n', 'a', ','], ['1', 'S', 'G', '-', 'h', 'u', 's', 'b', 'a', 'n', 'd', '-', 'A', 'C', 'C'], [⟨['’', 'i', 'n'], ['1', 'S', 'G'], none⟩, ⟨['h', 'a', 'a', 'm', 'a'], ['h', 'u', 's', 'b', 'a', 'n', 'd'], some '-'⟩, ⟨['n', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['’', 'i', 'm', '-', 'i', 'm'], ['2', 'S', 'G', '-', 'G', 'E', 'N'], [⟨['’', 'i', 'm'], ['2', 'S', 'G'], none⟩, ⟨['i', 'm'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['c', 'i', 'q', '’', 'a', 'a', 'm', 'q', 'a', 'l'], ['d', 'o', 'g', '(', 'E', 'R', 'G', ')'], [⟨['c', 'i', 'q', '’', 'a', 'a', 'm', 'q', 'a', 'l'], ['d', 'o', 'g', '(', 'E', 'R', 'G', ')'], none⟩]⟩, ⟨['h', 'i', '-', 't', 'w', 'e', 'h', 'k', 'e', 'y', '’', 'k', '-', '∅', '-', 'e'], ['3', 'S', 'U', 'B', 'J', '-', 'c', 'h', 'a', 's', 'e', '-', 'P', '-', 'R', 'E', 'M', '.', 'P', 'A', 'S', 'T'], [⟨['h', 'i'], ['3', 'S', 'U', 'B', 'J'], none⟩, ⟨['t', 'w', 'e', 'h', 'k', 'e', 'y', '’', 'k'], ['c', 'h', 'a', 's', 'e'], some '-'⟩, ⟨['∅'], ['P'], some '-'⟩, ⟨['e'], ['R', 'E', 'M', '.', 'P', 'A', 'S', 'T'], some '-'⟩]⟩, ⟨['’', 'i', 'i', 'n', '-', 'e'], ['1', 'S', 'G', '-', 'A', 'C', 'C'], [⟨['’', 'i', 'i', 'n'], ['1', 'S', 'G'], none⟩, ⟨['e'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("both reported", .acceptable), ("both utterance", .marginal), ("second reported only", .unacceptable), ("first reported only", .unacceptable)]
    paperFeatures := [("verb", "nezperce_say"), ("indexical", "you"), ("indexical", "I"), ("test", "shift_together")] }

def ex_83 : Datum :=
  { id := "deal2020_83"
    source := ⟨"deal-2020", "(83)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "Katie hi-hi-ce-∅ pro neki-se-∅ ’iin-k’u wees kine."
    glossedTokens := [("Katie", "Katie.NOM"), ("hi-hi-ce-∅", "3SUBJ-say-IMPERF-PRES"), ("pro", "1SG.NOM"), ("neki-se-∅", "think-IMPERF-PRES"), ("’iin-k’u", "1SG.NOM-too"), ("wees", "be.PRES"), ("kine", "here")]
    glossedWords := [⟨['K', 'a', 't', 'i', 'e'], ['K', 'a', 't', 'i', 'e', '.', 'N', 'O', 'M'], [⟨['K', 'a', 't', 'i', 'e'], ['K', 'a', 't', 'i', 'e', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['h', 'i', '-', 'h', 'i', '-', 'c', 'e', '-', '∅'], ['3', 'S', 'U', 'B', 'J', '-', 's', 'a', 'y', '-', 'I', 'M', 'P', 'E', 'R', 'F', '-', 'P', 'R', 'E', 'S'], [⟨['h', 'i'], ['3', 'S', 'U', 'B', 'J'], none⟩, ⟨['h', 'i'], ['s', 'a', 'y'], some '-'⟩, ⟨['c', 'e'], ['I', 'M', 'P', 'E', 'R', 'F'], some '-'⟩, ⟨['∅'], ['P', 'R', 'E', 'S'], some '-'⟩]⟩, ⟨['p', 'r', 'o'], ['1', 'S', 'G', '.', 'N', 'O', 'M'], [⟨['p', 'r', 'o'], ['1', 'S', 'G', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['n', 'e', 'k', 'i', '-', 's', 'e', '-', '∅'], ['t', 'h', 'i', 'n', 'k', '-', 'I', 'M', 'P', 'E', 'R', 'F', '-', 'P', 'R', 'E', 'S'], [⟨['n', 'e', 'k', 'i'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['s', 'e'], ['I', 'M', 'P', 'E', 'R', 'F'], some '-'⟩, ⟨['∅'], ['P', 'R', 'E', 'S'], some '-'⟩]⟩, ⟨['’', 'i', 'i', 'n', '-', 'k', '’', 'u'], ['1', 'S', 'G', '.', 'N', 'O', 'M', '-', 't', 'o', 'o'], [⟨['’', 'i', 'i', 'n'], ['1', 'S', 'G', '.', 'N', 'O', 'M'], none⟩, ⟨['k', '’', 'u'], ['t', 'o', 'o'], some '-'⟩]⟩, ⟨['w', 'e', 'e', 's'], ['b', 'e', '.', 'P', 'R', 'E', 'S'], [⟨['w', 'e', 'e', 's'], ['b', 'e', '.', 'P', 'R', 'E', 'S'], none⟩]⟩, ⟨['k', 'i', 'n', 'e'], ['h', 'e', 'r', 'e'], [⟨['k', 'i', 'n', 'e'], ['h', 'e', 'r', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("both reported", .acceptable), ("both utterance", .acceptable), ("first reported only", .unacceptable), ("second reported only", .unacceptable)]
    paperFeatures := [("verb", "nezperce_say"), ("indexical", "I"), ("indexical", "I"), ("test", "local_determination")] }

def ex_87 : Datum :=
  { id := "deal2020_87"
    source := ⟨"deal-2020", "(87)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "Caan hi-neki-se-∅ Meeli-nm pee-∅-n-e Sue-ne ’ee wees qetu kuhet ’iin-im-kin’ix."
    glossedTokens := [("Caan", "John.NOM"), ("hi-neki-se-∅", "3SUBJ-think-IMPERF-PRES"), ("Meeli-nm", "Mary-ERG"), ("pee-∅-n-e", "3/3-say-P-REM.PAST"), ("Sue-ne", "Sue-ACC"), ("’ee", "2SG.CL"), ("wees", "be.PRES"), ("qetu", "more"), ("kuhet", "tall"), ("’iin-im-kin’ix", "1SG-OBL-from")]
    glossedWords := [⟨['C', 'a', 'a', 'n'], ['J', 'o', 'h', 'n', '.', 'N', 'O', 'M'], [⟨['C', 'a', 'a', 'n'], ['J', 'o', 'h', 'n', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['h', 'i', '-', 'n', 'e', 'k', 'i', '-', 's', 'e', '-', '∅'], ['3', 'S', 'U', 'B', 'J', '-', 't', 'h', 'i', 'n', 'k', '-', 'I', 'M', 'P', 'E', 'R', 'F', '-', 'P', 'R', 'E', 'S'], [⟨['h', 'i'], ['3', 'S', 'U', 'B', 'J'], none⟩, ⟨['n', 'e', 'k', 'i'], ['t', 'h', 'i', 'n', 'k'], some '-'⟩, ⟨['s', 'e'], ['I', 'M', 'P', 'E', 'R', 'F'], some '-'⟩, ⟨['∅'], ['P', 'R', 'E', 'S'], some '-'⟩]⟩, ⟨['M', 'e', 'e', 'l', 'i', '-', 'n', 'm'], ['M', 'a', 'r', 'y', '-', 'E', 'R', 'G'], [⟨['M', 'e', 'e', 'l', 'i'], ['M', 'a', 'r', 'y'], none⟩, ⟨['n', 'm'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['p', 'e', 'e', '-', '∅', '-', 'n', '-', 'e'], ['3', '/', '3', '-', 's', 'a', 'y', '-', 'P', '-', 'R', 'E', 'M', '.', 'P', 'A', 'S', 'T'], [⟨['p', 'e', 'e'], ['3', '/', '3'], none⟩, ⟨['∅'], ['s', 'a', 'y'], some '-'⟩, ⟨['n'], ['P'], some '-'⟩, ⟨['e'], ['R', 'E', 'M', '.', 'P', 'A', 'S', 'T'], some '-'⟩]⟩, ⟨['S', 'u', 'e', '-', 'n', 'e'], ['S', 'u', 'e', '-', 'A', 'C', 'C'], [⟨['S', 'u', 'e'], ['S', 'u', 'e'], none⟩, ⟨['n', 'e'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['’', 'e', 'e'], ['2', 'S', 'G', '.', 'C', 'L'], [⟨['’', 'e', 'e'], ['2', 'S', 'G', '.', 'C', 'L'], none⟩]⟩, ⟨['w', 'e', 'e', 's'], ['b', 'e', '.', 'P', 'R', 'E', 'S'], [⟨['w', 'e', 'e', 's'], ['b', 'e', '.', 'P', 'R', 'E', 'S'], none⟩]⟩, ⟨['q', 'e', 't', 'u'], ['m', 'o', 'r', 'e'], [⟨['q', 'e', 't', 'u'], ['m', 'o', 'r', 'e'], none⟩]⟩, ⟨['k', 'u', 'h', 'e', 't'], ['t', 'a', 'l', 'l'], [⟨['k', 'u', 'h', 'e', 't'], ['t', 'a', 'l', 'l'], none⟩]⟩, ⟨['’', 'i', 'i', 'n', '-', 'i', 'm', '-', 'k', 'i', 'n', '’', 'i', 'x'], ['1', 'S', 'G', '-', 'O', 'B', 'L', '-', 'f', 'r', 'o', 'm'], [⟨['’', 'i', 'i', 'n'], ['1', 'S', 'G'], none⟩, ⟨['i', 'm'], ['O', 'B', 'L'], some '-'⟩, ⟨['k', 'i', 'n', '’', 'i', 'x'], ['f', 'r', 'o', 'm'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("intermediate reported context", .unacceptable), ("lowest reported context", .acceptable)]
    paperFeatures := [("verb", "nezperce_think"), ("lower_verb", "nezperce_say"), ("indexical", "I"), ("test", "local_determination"), ("lowest_shift", "yes")] }

def ex_111 : Datum :=
  { id := "deal2020_111"
    source := ⟨"deal-2020", "(111)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "Talmaks-pa pro hi-pe-hi-n-e pro weet’u kíne wisiinu’ kii k’ay’x-pa."
    glossedTokens := [("Talmaks-pa", "Talmaks-LOC"), ("pro", "3PL"), ("hi-pe-hi-n-e", "3SUBJ-S.PL-say-P-REM.PAST"), ("pro", "1PL"), ("weet’u", "not"), ("kíne", "here"), ("wisiinu’", "be.PROSP.PL"), ("kii", "this"), ("k’ay’x-pa", "week-LOC")]
    glossedWords := [⟨['T', 'a', 'l', 'm', 'a', 'k', 's', '-', 'p', 'a'], ['T', 'a', 'l', 'm', 'a', 'k', 's', '-', 'L', 'O', 'C'], [⟨['T', 'a', 'l', 'm', 'a', 'k', 's'], ['T', 'a', 'l', 'm', 'a', 'k', 's'], none⟩, ⟨['p', 'a'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['p', 'r', 'o'], ['3', 'P', 'L'], [⟨['p', 'r', 'o'], ['3', 'P', 'L'], none⟩]⟩, ⟨['h', 'i', '-', 'p', 'e', '-', 'h', 'i', '-', 'n', '-', 'e'], ['3', 'S', 'U', 'B', 'J', '-', 'S', '.', 'P', 'L', '-', 's', 'a', 'y', '-', 'P', '-', 'R', 'E', 'M', '.', 'P', 'A', 'S', 'T'], [⟨['h', 'i'], ['3', 'S', 'U', 'B', 'J'], none⟩, ⟨['p', 'e'], ['S', '.', 'P', 'L'], some '-'⟩, ⟨['h', 'i'], ['s', 'a', 'y'], some '-'⟩, ⟨['n'], ['P'], some '-'⟩, ⟨['e'], ['R', 'E', 'M', '.', 'P', 'A', 'S', 'T'], some '-'⟩]⟩, ⟨['p', 'r', 'o'], ['1', 'P', 'L'], [⟨['p', 'r', 'o'], ['1', 'P', 'L'], none⟩]⟩, ⟨['w', 'e', 'e', 't', '’', 'u'], ['n', 'o', 't'], [⟨['w', 'e', 'e', 't', '’', 'u'], ['n', 'o', 't'], none⟩]⟩, ⟨['k', 'í', 'n', 'e'], ['h', 'e', 'r', 'e'], [⟨['k', 'í', 'n', 'e'], ['h', 'e', 'r', 'e'], none⟩]⟩, ⟨['w', 'i', 's', 'i', 'i', 'n', 'u', '’'], ['b', 'e', '.', 'P', 'R', 'O', 'S', 'P', '.', 'P', 'L'], [⟨['w', 'i', 's', 'i', 'i', 'n', 'u', '’'], ['b', 'e', '.', 'P', 'R', 'O', 'S', 'P', '.', 'P', 'L'], none⟩]⟩, ⟨['k', 'i', 'i'], ['t', 'h', 'i', 's'], [⟨['k', 'i', 'i'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['k', '’', 'a', 'y', '’', 'x', '-', 'p', 'a'], ['w', 'e', 'e', 'k', '-', 'L', 'O', 'C'], [⟨['k', '’', 'a', 'y', '’', 'x'], ['w', 'e', 'e', 'k'], none⟩, ⟨['p', 'a'], ['L', 'O', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("both reported", .acceptable), ("first reported only", .acceptable)]
    paperFeatures := [("verb", "nezperce_say"), ("indexical", "I"), ("indexical", "here")] }

def ex_113 : Datum :=
  { id := "deal2020_113"
    source := ⟨"deal-2020", "(113)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "’In-lawtiwaa-nm Boston-pa hi-nees-∅-n-e pro weet’u kine pro wees kii kaa."
    glossedTokens := [("’In-lawtiwaa-nm", "1SG-friend-ERG"), ("Boston-pa", "Boston-LOC"), ("hi-nees-∅-n-e", "3SUBJ-O.PL-say-P-REM.PAST"), ("pro", "3PL"), ("weet’u", "NEG"), ("kine", "here"), ("pro", "1SG"), ("wees", "be.PRES"), ("kii", "this"), ("kaa", "then")]
    glossedWords := [⟨['’', 'I', 'n', '-', 'l', 'a', 'w', 't', 'i', 'w', 'a', 'a', '-', 'n', 'm'], ['1', 'S', 'G', '-', 'f', 'r', 'i', 'e', 'n', 'd', '-', 'E', 'R', 'G'], [⟨['’', 'I', 'n'], ['1', 'S', 'G'], none⟩, ⟨['l', 'a', 'w', 't', 'i', 'w', 'a', 'a'], ['f', 'r', 'i', 'e', 'n', 'd'], some '-'⟩, ⟨['n', 'm'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['B', 'o', 's', 't', 'o', 'n', '-', 'p', 'a'], ['B', 'o', 's', 't', 'o', 'n', '-', 'L', 'O', 'C'], [⟨['B', 'o', 's', 't', 'o', 'n'], ['B', 'o', 's', 't', 'o', 'n'], none⟩, ⟨['p', 'a'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['h', 'i', '-', 'n', 'e', 'e', 's', '-', '∅', '-', 'n', '-', 'e'], ['3', 'S', 'U', 'B', 'J', '-', 'O', '.', 'P', 'L', '-', 's', 'a', 'y', '-', 'P', '-', 'R', 'E', 'M', '.', 'P', 'A', 'S', 'T'], [⟨['h', 'i'], ['3', 'S', 'U', 'B', 'J'], none⟩, ⟨['n', 'e', 'e', 's'], ['O', '.', 'P', 'L'], some '-'⟩, ⟨['∅'], ['s', 'a', 'y'], some '-'⟩, ⟨['n'], ['P'], some '-'⟩, ⟨['e'], ['R', 'E', 'M', '.', 'P', 'A', 'S', 'T'], some '-'⟩]⟩, ⟨['p', 'r', 'o'], ['3', 'P', 'L'], [⟨['p', 'r', 'o'], ['3', 'P', 'L'], none⟩]⟩, ⟨['w', 'e', 'e', 't', '’', 'u'], ['N', 'E', 'G'], [⟨['w', 'e', 'e', 't', '’', 'u'], ['N', 'E', 'G'], none⟩]⟩, ⟨['k', 'i', 'n', 'e'], ['h', 'e', 'r', 'e'], [⟨['k', 'i', 'n', 'e'], ['h', 'e', 'r', 'e'], none⟩]⟩, ⟨['p', 'r', 'o'], ['1', 'S', 'G'], [⟨['p', 'r', 'o'], ['1', 'S', 'G'], none⟩]⟩, ⟨['w', 'e', 'e', 's'], ['b', 'e', '.', 'P', 'R', 'E', 'S'], [⟨['w', 'e', 'e', 's'], ['b', 'e', '.', 'P', 'R', 'E', 'S'], none⟩]⟩, ⟨['k', 'i', 'i'], ['t', 'h', 'i', 's'], [⟨['k', 'i', 'i'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['k', 'a', 'a'], ['t', 'h', 'e', 'n'], [⟨['k', 'a', 'a'], ['t', 'h', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Taamsas is speaking."
    judgment := .acceptable
    contrasts := []
    readings := [("both reported", .acceptable), ("first reported only", .unacceptable)]
    paperFeatures := [("verb", "nezperce_say"), ("indexical", "here"), ("indexical", "I")] }

def ex_115 : Datum :=
  { id := "deal2020_115"
    source := ⟨"deal-2020", "(115)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nezp1238"
    primaryText := "Pay’s Harold hi-neki-se-∅ pro wees kine Clarkston-pa."
    glossedTokens := [("Pay’s", "maybe"), ("Harold", "Harold.NOM"), ("hi-neki-se-∅", "3SUBJ-think-IMPERF-PRES"), ("pro", "1SG"), ("wees", "be.PRES"), ("kine", "here"), ("Clarkston-pa", "Clarkston-LOC")]
    glossedWords := [⟨['P', 'a', 'y', '’', 's'], ['m', 'a', 'y', 'b', 'e'], [⟨['P', 'a', 'y', '’', 's'], ['m', 'a', 'y', 'b', 'e'], none⟩]⟩, ⟨['H', 'a', 'r', 'o', 'l', 'd'], ['H', 'a', 'r', 'o', 'l', 'd', '.', 'N', 'O', 'M'], [⟨['H', 'a', 'r', 'o', 'l', 'd'], ['H', 'a', 'r', 'o', 'l', 'd', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['h', 'i', '-', 'n', 'e', 'k', 'i', '-', 's', 'e', '-', '∅'], ['3', 'S', 'U', 'B', 'J', '-', 't', 'h', 'i', 'n', 'k', '-', 'I', 'M', 'P', 'E', 'R', 'F', '-', 'P', 'R', 'E', 'S'], [⟨['h', 'i'], ['3', 'S', 'U', 'B', 'J'], none⟩, ⟨['n', 'e', 'k', 'i'], ['t', 'h', 'i', 'n', 'k'], some '-'⟩, ⟨['s', 'e'], ['I', 'M', 'P', 'E', 'R', 'F'], some '-'⟩, ⟨['∅'], ['P', 'R', 'E', 'S'], some '-'⟩]⟩, ⟨['p', 'r', 'o'], ['1', 'S', 'G'], [⟨['p', 'r', 'o'], ['1', 'S', 'G'], none⟩]⟩, ⟨['w', 'e', 'e', 's'], ['b', 'e', '.', 'P', 'R', 'E', 'S'], [⟨['w', 'e', 'e', 's'], ['b', 'e', '.', 'P', 'R', 'E', 'S'], none⟩]⟩, ⟨['k', 'i', 'n', 'e'], ['h', 'e', 'r', 'e'], [⟨['k', 'i', 'n', 'e'], ['h', 'e', 'r', 'e'], none⟩]⟩, ⟨['C', 'l', 'a', 'r', 'k', 's', 't', 'o', 'n', '-', 'p', 'a'], ['C', 'l', 'a', 'r', 'k', 's', 't', 'o', 'n', '-', 'L', 'O', 'C'], [⟨['C', 'l', 'a', 'r', 'k', 's', 't', 'o', 'n'], ['C', 'l', 'a', 'r', 'k', 's', 't', 'o', 'n'], none⟩, ⟨['p', 'a'], ['L', 'O', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Harold is in Clarkston. I and my consultant are in Lapwai."
    judgment := .unacceptable
    contrasts := []
    readings := [("second reported only", .unacceptable)]
    paperFeatures := [("verb", "nezperce_think"), ("indexical", "I"), ("indexical", "here")] }

def ex_118 : Datum :=
  { id := "deal2020_118"
    source := ⟨"deal-2020", "(118)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "’Aayat hi-nek-saa-qa pro peeleey-ce-∅."
    glossedTokens := [("’Aayat", "woman.NOM"), ("hi-nek-saa-qa", "3SUBJ-think-IMPERF-REC.PAST"), ("pro", "1SG"), ("peeleey-ce-∅", "be.missing-IMPERF-PRES")]
    glossedWords := [⟨['’', 'A', 'a', 'y', 'a', 't'], ['w', 'o', 'm', 'a', 'n', '.', 'N', 'O', 'M'], [⟨['’', 'A', 'a', 'y', 'a', 't'], ['w', 'o', 'm', 'a', 'n', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['h', 'i', '-', 'n', 'e', 'k', '-', 's', 'a', 'a', '-', 'q', 'a'], ['3', 'S', 'U', 'B', 'J', '-', 't', 'h', 'i', 'n', 'k', '-', 'I', 'M', 'P', 'E', 'R', 'F', '-', 'R', 'E', 'C', '.', 'P', 'A', 'S', 'T'], [⟨['h', 'i'], ['3', 'S', 'U', 'B', 'J'], none⟩, ⟨['n', 'e', 'k'], ['t', 'h', 'i', 'n', 'k'], some '-'⟩, ⟨['s', 'a', 'a'], ['I', 'M', 'P', 'E', 'R', 'F'], some '-'⟩, ⟨['q', 'a'], ['R', 'E', 'C', '.', 'P', 'A', 'S', 'T'], some '-'⟩]⟩, ⟨['p', 'r', 'o'], ['1', 'S', 'G'], [⟨['p', 'r', 'o'], ['1', 'S', 'G'], none⟩]⟩, ⟨['p', 'e', 'e', 'l', 'e', 'e', 'y', '-', 'c', 'e', '-', '∅'], ['b', 'e', '.', 'm', 'i', 's', 's', 'i', 'n', 'g', '-', 'I', 'M', 'P', 'E', 'R', 'F', '-', 'P', 'R', 'E', 'S'], [⟨['p', 'e', 'e', 'l', 'e', 'e', 'y'], ['b', 'e', '.', 'm', 'i', 's', 's', 'i', 'n', 'g'], none⟩, ⟨['c', 'e'], ['I', 'M', 'P', 'E', 'R', 'F'], some '-'⟩, ⟨['∅'], ['P', 'R', 'E', 'S'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "A woman was on a group tour and she wandered off from the group and went back to the bus to take a nap. People noticed she was missing and started searching for her. She woke up, got back off the bus, and noticed everyone searching around. Of course, she didn’t know why they were searching. Someone said to her, “A woman is lost.” So she joined the search party to look for that woman, without knowing it was herself!"
    judgment := .unacceptable
    contrasts := []
    readings := [("non-de se", .unacceptable)]
    paperFeatures := [("verb", "nezperce_think"), ("indexical", "I"), ("test", "de_se")] }

def ex_121 : Datum :=
  { id := "deal2020_121"
    source := ⟨"deal-2020", "(121)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nezp1238"
    primaryText := "Meeli-nm pee-∅-n-e Caan-e, ’ee cikliitoq-o’qa."
    glossedTokens := [("Meeli-nm", "Mary-ERG"), ("pee-∅-n-e", "3/3-say-P-REM.PAST"), ("Caan-e,", "John-ACC"), ("’ee", "2SG.CL"), ("cikliitoq-o’qa", "go.home-MODAL")]
    glossedWords := [⟨['M', 'e', 'e', 'l', 'i', '-', 'n', 'm'], ['M', 'a', 'r', 'y', '-', 'E', 'R', 'G'], [⟨['M', 'e', 'e', 'l', 'i'], ['M', 'a', 'r', 'y'], none⟩, ⟨['n', 'm'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['p', 'e', 'e', '-', '∅', '-', 'n', '-', 'e'], ['3', '/', '3', '-', 's', 'a', 'y', '-', 'P', '-', 'R', 'E', 'M', '.', 'P', 'A', 'S', 'T'], [⟨['p', 'e', 'e'], ['3', '/', '3'], none⟩, ⟨['∅'], ['s', 'a', 'y'], some '-'⟩, ⟨['n'], ['P'], some '-'⟩, ⟨['e'], ['R', 'E', 'M', '.', 'P', 'A', 'S', 'T'], some '-'⟩]⟩, ⟨['C', 'a', 'a', 'n', '-', 'e', ','], ['J', 'o', 'h', 'n', '-', 'A', 'C', 'C'], [⟨['C', 'a', 'a', 'n'], ['J', 'o', 'h', 'n'], none⟩, ⟨['e'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['’', 'e', 'e'], ['2', 'S', 'G', '.', 'C', 'L'], [⟨['’', 'e', 'e'], ['2', 'S', 'G', '.', 'C', 'L'], none⟩]⟩, ⟨['c', 'i', 'k', 'l', 'i', 'i', 't', 'o', 'q', '-', 'o', '’', 'q', 'a'], ['g', 'o', '.', 'h', 'o', 'm', 'e', '-', 'M', 'O', 'D', 'A', 'L'], [⟨['c', 'i', 'k', 'l', 'i', 'i', 't', 'o', 'q'], ['g', 'o', '.', 'h', 'o', 'm', 'e'], none⟩, ⟨['o', '’', 'q', 'a'], ['M', 'O', 'D', 'A', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Mary is organizing a big dinner at a restaurant with waiters to help serve food. She hears that a certain waiter named John is being a nuisance. She tells the nearest waiter, “John should go home.\" Unbeknowst to her, she’s talking to John."
    judgment := .unacceptable
    contrasts := []
    readings := [("non-de se", .unacceptable)]
    paperFeatures := [("verb", "nezperce_say"), ("indexical", "you"), ("test", "de_se")] }

def ex_124 : Datum :=
  { id := "deal2020_124"
    source := ⟨"deal-2020", "(124)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "’Aayat hii-wes Clarkston-pa, met’u pro hi-neki-se-∅ Asootin-pa, kaa pro hi-neki-se-∅ Costco hii-wes kine."
    glossedTokens := [("’Aayat", "woman.NOM"), ("hii-wes", "3SUBJ-be.PRES"), ("Clarkston-pa,", "Clarkston-LOC"), ("met’u", "but"), ("pro", "3SG"), ("hi-neki-se-∅", "3SUBJ-think-IMPERF-PRES"), ("Asootin-pa,", "Asotin-LOC"), ("kaa", "and"), ("pro", "3SG"), ("hi-neki-se-∅", "3SUBJ-think-IMPERF-PRES"), ("Costco", "Costco"), ("hii-wes", "3SUBJ-be.PRES"), ("kine", "here")]
    glossedWords := [⟨['’', 'A', 'a', 'y', 'a', 't'], ['w', 'o', 'm', 'a', 'n', '.', 'N', 'O', 'M'], [⟨['’', 'A', 'a', 'y', 'a', 't'], ['w', 'o', 'm', 'a', 'n', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['h', 'i', 'i', '-', 'w', 'e', 's'], ['3', 'S', 'U', 'B', 'J', '-', 'b', 'e', '.', 'P', 'R', 'E', 'S'], [⟨['h', 'i', 'i'], ['3', 'S', 'U', 'B', 'J'], none⟩, ⟨['w', 'e', 's'], ['b', 'e', '.', 'P', 'R', 'E', 'S'], some '-'⟩]⟩, ⟨['C', 'l', 'a', 'r', 'k', 's', 't', 'o', 'n', '-', 'p', 'a', ','], ['C', 'l', 'a', 'r', 'k', 's', 't', 'o', 'n', '-', 'L', 'O', 'C'], [⟨['C', 'l', 'a', 'r', 'k', 's', 't', 'o', 'n'], ['C', 'l', 'a', 'r', 'k', 's', 't', 'o', 'n'], none⟩, ⟨['p', 'a'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['m', 'e', 't', '’', 'u'], ['b', 'u', 't'], [⟨['m', 'e', 't', '’', 'u'], ['b', 'u', 't'], none⟩]⟩, ⟨['p', 'r', 'o'], ['3', 'S', 'G'], [⟨['p', 'r', 'o'], ['3', 'S', 'G'], none⟩]⟩, ⟨['h', 'i', '-', 'n', 'e', 'k', 'i', '-', 's', 'e', '-', '∅'], ['3', 'S', 'U', 'B', 'J', '-', 't', 'h', 'i', 'n', 'k', '-', 'I', 'M', 'P', 'E', 'R', 'F', '-', 'P', 'R', 'E', 'S'], [⟨['h', 'i'], ['3', 'S', 'U', 'B', 'J'], none⟩, ⟨['n', 'e', 'k', 'i'], ['t', 'h', 'i', 'n', 'k'], some '-'⟩, ⟨['s', 'e'], ['I', 'M', 'P', 'E', 'R', 'F'], some '-'⟩, ⟨['∅'], ['P', 'R', 'E', 'S'], some '-'⟩]⟩, ⟨['A', 's', 'o', 'o', 't', 'i', 'n', '-', 'p', 'a', ','], ['A', 's', 'o', 't', 'i', 'n', '-', 'L', 'O', 'C'], [⟨['A', 's', 'o', 'o', 't', 'i', 'n'], ['A', 's', 'o', 't', 'i', 'n'], none⟩, ⟨['p', 'a'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['k', 'a', 'a'], ['a', 'n', 'd'], [⟨['k', 'a', 'a'], ['a', 'n', 'd'], none⟩]⟩, ⟨['p', 'r', 'o'], ['3', 'S', 'G'], [⟨['p', 'r', 'o'], ['3', 'S', 'G'], none⟩]⟩, ⟨['h', 'i', '-', 'n', 'e', 'k', 'i', '-', 's', 'e', '-', '∅'], ['3', 'S', 'U', 'B', 'J', '-', 't', 'h', 'i', 'n', 'k', '-', 'I', 'M', 'P', 'E', 'R', 'F', '-', 'P', 'R', 'E', 'S'], [⟨['h', 'i'], ['3', 'S', 'U', 'B', 'J'], none⟩, ⟨['n', 'e', 'k', 'i'], ['t', 'h', 'i', 'n', 'k'], some '-'⟩, ⟨['s', 'e'], ['I', 'M', 'P', 'E', 'R', 'F'], some '-'⟩, ⟨['∅'], ['P', 'R', 'E', 'S'], some '-'⟩]⟩, ⟨['C', 'o', 's', 't', 'c', 'o'], ['C', 'o', 's', 't', 'c', 'o'], [⟨['C', 'o', 's', 't', 'c', 'o'], ['C', 'o', 's', 't', 'c', 'o'], none⟩]⟩, ⟨['h', 'i', 'i', '-', 'w', 'e', 's'], ['3', 'S', 'U', 'B', 'J', '-', 'b', 'e', '.', 'P', 'R', 'E', 'S'], [⟨['h', 'i', 'i'], ['3', 'S', 'U', 'B', 'J'], none⟩, ⟨['w', 'e', 's'], ['b', 'e', '.', 'P', 'R', 'E', 'S'], some '-'⟩]⟩, ⟨['k', 'i', 'n', 'e'], ['h', 'e', 'r', 'e'], [⟨['k', 'i', 'n', 'e'], ['h', 'e', 'r', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Elicited in Lapwai: Costco is a prominent store in Clarkston. Everyone knows where it is."
    judgment := .acceptable
    contrasts := []
    readings := [("non-de se", .acceptable)]
    paperFeatures := [("verb", "nezperce_think"), ("indexical", "here"), ("test", "de_se")] }

def ex_117 : Datum :=
  { id := "deal2020_117"
    source := ⟨"anand-2006", "p. 79"⟩
    reportedIn := some ⟨"deal-2020", "(117)"⟩
    language := "diml1238"
    primaryText := "Heseni va kɛ ɛz newɛsha."
    glossedTokens := [("Heseni", "Hesen.OBL"), ("va", "said"), ("kɛ", "that"), ("ɛz", "I"), ("newɛsha", "be.sick.PRES")]
    glossedWords := [⟨['H', 'e', 's', 'e', 'n', 'i'], ['H', 'e', 's', 'e', 'n', '.', 'O', 'B', 'L'], [⟨['H', 'e', 's', 'e', 'n', 'i'], ['H', 'e', 's', 'e', 'n', '.', 'O', 'B', 'L'], none⟩]⟩, ⟨['v', 'a'], ['s', 'a', 'i', 'd'], [⟨['v', 'a'], ['s', 'a', 'i', 'd'], none⟩]⟩, ⟨['k', 'ɛ'], ['t', 'h', 'a', 't'], [⟨['k', 'ɛ'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['ɛ', 'z'], ['I'], [⟨['ɛ', 'z'], ['I'], none⟩]⟩, ⟨['n', 'e', 'w', 'ɛ', 's', 'h', 'a'], ['b', 'e', '.', 's', 'i', 'c', 'k', '.', 'P', 'R', 'E', 'S'], [⟨['n', 'e', 'w', 'ɛ', 's', 'h', 'a'], ['b', 'e', '.', 's', 'i', 'c', 'k', '.', 'P', 'R', 'E', 'S'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("de se", .acceptable), ("non-de se", .unacceptable)]
    paperFeatures := [("verb", "zazaki_say"), ("indexical", "I"), ("test", "de_se")] }

def ex_120 : Datum :=
  { id := "deal2020_120"
    source := ⟨"anand-2006", "p. 80"⟩
    reportedIn := some ⟨"deal-2020", "(120)"⟩
    language := "diml1238"
    primaryText := "Heseni va Ali-ra kɛ ti newɛsha."
    glossedTokens := [("Heseni", "Hesen.OBL"), ("va", "said"), ("Ali-ra", "Ali-to"), ("kɛ", "that"), ("ti", "you"), ("newɛsha", "be.sick.PRES")]
    glossedWords := [⟨['H', 'e', 's', 'e', 'n', 'i'], ['H', 'e', 's', 'e', 'n', '.', 'O', 'B', 'L'], [⟨['H', 'e', 's', 'e', 'n', 'i'], ['H', 'e', 's', 'e', 'n', '.', 'O', 'B', 'L'], none⟩]⟩, ⟨['v', 'a'], ['s', 'a', 'i', 'd'], [⟨['v', 'a'], ['s', 'a', 'i', 'd'], none⟩]⟩, ⟨['A', 'l', 'i', '-', 'r', 'a'], ['A', 'l', 'i', '-', 't', 'o'], [⟨['A', 'l', 'i'], ['A', 'l', 'i'], none⟩, ⟨['r', 'a'], ['t', 'o'], some '-'⟩]⟩, ⟨['k', 'ɛ'], ['t', 'h', 'a', 't'], [⟨['k', 'ɛ'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['t', 'i'], ['y', 'o', 'u'], [⟨['t', 'i'], ['y', 'o', 'u'], none⟩]⟩, ⟨['n', 'e', 'w', 'ɛ', 's', 'h', 'a'], ['b', 'e', '.', 's', 'i', 'c', 'k', '.', 'P', 'R', 'E', 'S'], [⟨['n', 'e', 'w', 'ɛ', 's', 'h', 'a'], ['b', 'e', '.', 's', 'i', 'c', 'k', '.', 'P', 'R', 'E', 'S'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("de se", .acceptable), ("non-de se", .unacceptable)]
    paperFeatures := [("verb", "zazaki_say"), ("indexical", "you"), ("test", "de_se")] }

def ex_123 : Datum :=
  { id := "deal2020_123"
    source := ⟨"anand-2006", "p. 80"⟩
    reportedIn := some ⟨"deal-2020", "(123)"⟩
    language := "diml1238"
    primaryText := "Waxto kɛ o London-de bime Pierri va kɛ o ita rindɛka."
    glossedTokens := [("Waxto", "when"), ("kɛ", "that"), ("o", "he"), ("London-de", "London-at"), ("bime", "be.PAST"), ("Pierri", "Pierre.OBL"), ("va", "said"), ("kɛ", "that"), ("o", "it"), ("ita", "here"), ("rindɛka", "be.pretty.PRES")]
    glossedWords := [⟨['W', 'a', 'x', 't', 'o'], ['w', 'h', 'e', 'n'], [⟨['W', 'a', 'x', 't', 'o'], ['w', 'h', 'e', 'n'], none⟩]⟩, ⟨['k', 'ɛ'], ['t', 'h', 'a', 't'], [⟨['k', 'ɛ'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['o'], ['h', 'e'], [⟨['o'], ['h', 'e'], none⟩]⟩, ⟨['L', 'o', 'n', 'd', 'o', 'n', '-', 'd', 'e'], ['L', 'o', 'n', 'd', 'o', 'n', '-', 'a', 't'], [⟨['L', 'o', 'n', 'd', 'o', 'n'], ['L', 'o', 'n', 'd', 'o', 'n'], none⟩, ⟨['d', 'e'], ['a', 't'], some '-'⟩]⟩, ⟨['b', 'i', 'm', 'e'], ['b', 'e', '.', 'P', 'A', 'S', 'T'], [⟨['b', 'i', 'm', 'e'], ['b', 'e', '.', 'P', 'A', 'S', 'T'], none⟩]⟩, ⟨['P', 'i', 'e', 'r', 'r', 'i'], ['P', 'i', 'e', 'r', 'r', 'e', '.', 'O', 'B', 'L'], [⟨['P', 'i', 'e', 'r', 'r', 'i'], ['P', 'i', 'e', 'r', 'r', 'e', '.', 'O', 'B', 'L'], none⟩]⟩, ⟨['v', 'a'], ['s', 'a', 'i', 'd'], [⟨['v', 'a'], ['s', 'a', 'i', 'd'], none⟩]⟩, ⟨['k', 'ɛ'], ['t', 'h', 'a', 't'], [⟨['k', 'ɛ'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['o'], ['i', 't'], [⟨['o'], ['i', 't'], none⟩]⟩, ⟨['i', 't', 'a'], ['h', 'e', 'r', 'e'], [⟨['i', 't', 'a'], ['h', 'e', 'r', 'e'], none⟩]⟩, ⟨['r', 'i', 'n', 'd', 'ɛ', 'k', 'a'], ['b', 'e', '.', 'p', 'r', 'e', 't', 't', 'y', '.', 'P', 'R', 'E', 'S'], [⟨['r', 'i', 'n', 'd', 'ɛ', 'k', 'a'], ['b', 'e', '.', 'p', 'r', 'e', 't', 't', 'y', '.', 'P', 'R', 'E', 'S'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("de se", .acceptable), ("non-de se", .unacceptable)]
    paperFeatures := [("verb", "zazaki_say"), ("indexical", "here"), ("test", "de_se")] }

def ex_103b : Datum :=
  { id := "deal2020_103b"
    source := ⟨"sudo-2012", "p. 244"⟩
    reportedIn := some ⟨"deal-2020", "(103b)"⟩
    language := "uigh1240"
    primaryText := "Muhemmet manga toqquzinji ay-din bašla-p (men) bu jer-de uqu-imen di-di."
    glossedTokens := [("Muhemmet", "Muhemmet"), ("manga", "1SG.DAT"), ("toqquzinji", "9th"), ("ay-din", "month-from"), ("bašla-p", "start-ing"), ("(men)", "1SG.NOM"), ("bu jer-de", "here-LOC"), ("uqu-imen", "study-IMPF.1SG"), ("di-di.", "say-PAST.3")]
    glossedWords := [⟨['M', 'u', 'h', 'e', 'm', 'm', 'e', 't'], ['M', 'u', 'h', 'e', 'm', 'm', 'e', 't'], [⟨['M', 'u', 'h', 'e', 'm', 'm', 'e', 't'], ['M', 'u', 'h', 'e', 'm', 'm', 'e', 't'], none⟩]⟩, ⟨['m', 'a', 'n', 'g', 'a'], ['1', 'S', 'G', '.', 'D', 'A', 'T'], [⟨['m', 'a', 'n', 'g', 'a'], ['1', 'S', 'G', '.', 'D', 'A', 'T'], none⟩]⟩, ⟨['t', 'o', 'q', 'q', 'u', 'z', 'i', 'n', 'j', 'i'], ['9', 't', 'h'], [⟨['t', 'o', 'q', 'q', 'u', 'z', 'i', 'n', 'j', 'i'], ['9', 't', 'h'], none⟩]⟩, ⟨['a', 'y', '-', 'd', 'i', 'n'], ['m', 'o', 'n', 't', 'h', '-', 'f', 'r', 'o', 'm'], [⟨['a', 'y'], ['m', 'o', 'n', 't', 'h'], none⟩, ⟨['d', 'i', 'n'], ['f', 'r', 'o', 'm'], some '-'⟩]⟩, ⟨['b', 'a', 'š', 'l', 'a', '-', 'p'], ['s', 't', 'a', 'r', 't', '-', 'i', 'n', 'g'], [⟨['b', 'a', 'š', 'l', 'a'], ['s', 't', 'a', 'r', 't'], none⟩, ⟨['p'], ['i', 'n', 'g'], some '-'⟩]⟩, ⟨['(', 'm', 'e', 'n', ')'], ['1', 'S', 'G', '.', 'N', 'O', 'M'], [⟨['m', 'e', 'n'], ['1', 'S', 'G', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['b', 'u', ' ', 'j', 'e', 'r', '-', 'd', 'e'], ['h', 'e', 'r', 'e', '-', 'L', 'O', 'C'], [⟨['b', 'u', ' ', 'j', 'e', 'r'], ['h', 'e', 'r', 'e'], none⟩, ⟨['d', 'e'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['u', 'q', 'u', '-', 'i', 'm', 'e', 'n'], ['s', 't', 'u', 'd', 'y', '-', 'I', 'M', 'P', 'F', '.', '1', 'S', 'G'], [⟨['u', 'q', 'u'], ['s', 't', 'u', 'd', 'y'], none⟩, ⟨['i', 'm', 'e', 'n'], ['I', 'M', 'P', 'F', '.', '1', 'S', 'G'], some '-'⟩]⟩, ⟨['d', 'i', '-', 'd', 'i', '.'], ['s', 'a', 'y', '-', 'P', 'A', 'S', 'T', '.', '3'], [⟨['d', 'i'], ['s', 'a', 'y'], none⟩, ⟨['d', 'i'], ['P', 'A', 'S', 'T', '.', '3'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "This summer, I went to UCLA and met Muhemmet there. He told me, “I’m going to study here from this September.” Now I’m back in Cambridge, MA, talking to Ahmet."
    judgment := .unacceptable
    contrasts := [("Muhemmet manga toqquzinji ay-din bašla-p (men) u jer-de uqu-imen di-di.", .acceptable)]
    readings := [("both reported", .unacceptable)]
    paperFeatures := [("verb", "uyghur_say"), ("indexical", "I"), ("indexical", "here")] }

def ex_122 : Datum :=
  { id := "deal2020_122"
    source := ⟨"sudo-2012", "p. 225"⟩
    reportedIn := some ⟨"deal-2020", "(122)"⟩
    language := "uigh1240"
    primaryText := "Muhemmet John-gha pro öy-ge kit-sh-ing kirek di-di."
    glossedTokens := [("Muhemmet", "Muhemmet"), ("John-gha", "John-DAT"), ("pro", "2SG"), ("öy-ge", "home-DAT"), ("kit-sh-ing", "leave-GER-2SG"), ("kirek", "should"), ("di-di.", "say-PAST.3")]
    glossedWords := [⟨['M', 'u', 'h', 'e', 'm', 'm', 'e', 't'], ['M', 'u', 'h', 'e', 'm', 'm', 'e', 't'], [⟨['M', 'u', 'h', 'e', 'm', 'm', 'e', 't'], ['M', 'u', 'h', 'e', 'm', 'm', 'e', 't'], none⟩]⟩, ⟨['J', 'o', 'h', 'n', '-', 'g', 'h', 'a'], ['J', 'o', 'h', 'n', '-', 'D', 'A', 'T'], [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], none⟩, ⟨['g', 'h', 'a'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['p', 'r', 'o'], ['2', 'S', 'G'], [⟨['p', 'r', 'o'], ['2', 'S', 'G'], none⟩]⟩, ⟨['ö', 'y', '-', 'g', 'e'], ['h', 'o', 'm', 'e', '-', 'D', 'A', 'T'], [⟨['ö', 'y'], ['h', 'o', 'm', 'e'], none⟩, ⟨['g', 'e'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['k', 'i', 't', '-', 's', 'h', '-', 'i', 'n', 'g'], ['l', 'e', 'a', 'v', 'e', '-', 'G', 'E', 'R', '-', '2', 'S', 'G'], [⟨['k', 'i', 't'], ['l', 'e', 'a', 'v', 'e'], none⟩, ⟨['s', 'h'], ['G', 'E', 'R'], some '-'⟩, ⟨['i', 'n', 'g'], ['2', 'S', 'G'], some '-'⟩]⟩, ⟨['k', 'i', 'r', 'e', 'k'], ['s', 'h', 'o', 'u', 'l', 'd'], [⟨['k', 'i', 'r', 'e', 'k'], ['s', 'h', 'o', 'u', 'l', 'd'], none⟩]⟩, ⟨['d', 'i', '-', 'd', 'i', '.'], ['s', 'a', 'y', '-', 'P', 'A', 'S', 'T', '.', '3'], [⟨['d', 'i'], ['s', 'a', 'y'], none⟩, ⟨['d', 'i'], ['P', 'A', 'S', 'T', '.', '3'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Muhemmet is hosting a party. He hears that a certain waiter named John is being a nuisance. Muhemmet tells the nearest waiter, “John should go home.” Unbeknownst to him, he’s talking to John."
    judgment := .acceptable
    contrasts := []
    readings := [("non-de se", .acceptable)]
    paperFeatures := [("verb", "uyghur_say"), ("indexical", "you"), ("test", "de_se")] }

def ex_106 : Datum :=
  { id := "deal2020_106"
    source := ⟨"rice-1986", "p. 53"⟩
    reportedIn := some ⟨"deal-2020", "(106)"⟩
    language := "slav1253"
    primaryText := "Simon rásereyineht’u hadi."
    glossedTokens := [("Simon", "Simon"), ("rásereyineht’u", "2SG.hit.1SG"), ("hadi.", "3SG.say")]
    glossedWords := [⟨['S', 'i', 'm', 'o', 'n'], ['S', 'i', 'm', 'o', 'n'], [⟨['S', 'i', 'm', 'o', 'n'], ['S', 'i', 'm', 'o', 'n'], none⟩]⟩, ⟨['r', 'á', 's', 'e', 'r', 'e', 'y', 'i', 'n', 'e', 'h', 't', '’', 'u'], ['2', 'S', 'G', '.', 'h', 'i', 't', '.', '1', 'S', 'G'], [⟨['r', 'á', 's', 'e', 'r', 'e', 'y', 'i', 'n', 'e', 'h', 't', '’', 'u'], ['2', 'S', 'G', '.', 'h', 'i', 't', '.', '1', 'S', 'G'], none⟩]⟩, ⟨['h', 'a', 'd', 'i', '.'], ['3', 'S', 'G', '.', 's', 'a', 'y'], [⟨['h', 'a', 'd', 'i'], ['3', 'S', 'G', '.', 's', 'a', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("second reported only", .acceptable)]
    paperFeatures := [("verb", "slave_say"), ("indexical", "you"), ("indexical", "I")] }

def ex_119 : Datum :=
  { id := "deal2020_119"
    source := ⟨"nishiguchi-2017", "p. 48"⟩
    reportedIn := some ⟨"deal-2020", "(119)"⟩
    language := "daas1238"
    primaryText := "Baali kiey-e sure-chu he jiet hi konye."
    glossedTokens := [("Baali", "Baali"), ("kiey-e", "say.3SG-PAST"), ("sure-chu", "1SG.GEN-pants"), ("he", "COPULA"), ("jiet", "fire"), ("hi", "RP"), ("konye.", "eat.3SG.PASS.PAST")]
    glossedWords := [⟨['B', 'a', 'a', 'l', 'i'], ['B', 'a', 'a', 'l', 'i'], [⟨['B', 'a', 'a', 'l', 'i'], ['B', 'a', 'a', 'l', 'i'], none⟩]⟩, ⟨['k', 'i', 'e', 'y', '-', 'e'], ['s', 'a', 'y', '.', '3', 'S', 'G', '-', 'P', 'A', 'S', 'T'], [⟨['k', 'i', 'e', 'y'], ['s', 'a', 'y', '.', '3', 'S', 'G'], none⟩, ⟨['e'], ['P', 'A', 'S', 'T'], some '-'⟩]⟩, ⟨['s', 'u', 'r', 'e', '-', 'c', 'h', 'u'], ['1', 'S', 'G', '.', 'G', 'E', 'N', '-', 'p', 'a', 'n', 't', 's'], [⟨['s', 'u', 'r', 'e'], ['1', 'S', 'G', '.', 'G', 'E', 'N'], none⟩, ⟨['c', 'h', 'u'], ['p', 'a', 'n', 't', 's'], some '-'⟩]⟩, ⟨['h', 'e'], ['C', 'O', 'P', 'U', 'L', 'A'], [⟨['h', 'e'], ['C', 'O', 'P', 'U', 'L', 'A'], none⟩]⟩, ⟨['j', 'i', 'e', 't'], ['f', 'i', 'r', 'e'], [⟨['j', 'i', 'e', 't'], ['f', 'i', 'r', 'e'], none⟩]⟩, ⟨['h', 'i'], ['R', 'P'], [⟨['h', 'i'], ['R', 'P'], none⟩]⟩, ⟨['k', 'o', 'n', 'y', 'e', '.'], ['e', 'a', 't', '.', '3', 'S', 'G', '.', 'P', 'A', 'S', 'S', '.', 'P', 'A', 'S', 'T'], [⟨['k', 'o', 'n', 'y', 'e'], ['e', 'a', 't', '.', '3', 'S', 'G', '.', 'P', 'A', 'S', 'S', '.', 'P', 'A', 'S', 'T'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("de se", .acceptable), ("non-de se", .acceptable)]
    paperFeatures := [("verb", "dhaasanac_say"), ("indexical", "I"), ("test", "de_se")] }

def ex_159 : Datum :=
  { id := "deal2020_159"
    source := ⟨"park-2016", "p. 29"⟩
    reportedIn := some ⟨"deal-2020", "(159)"⟩
    language := "kore1280"
    primaryText := "John-i cinancwu welyoil-ey Mary-ka onul ttenanta-ko malhayssta."
    glossedTokens := [("John-i", "John-NOM"), ("cinancwu", "last.week"), ("welyoil-ey", "Monday-on"), ("Mary-ka", "Mary-NOM"), ("onul", "today"), ("ttenanta-ko", "leave-C"), ("malhayssta.", "said")]
    glossedWords := [⟨['J', 'o', 'h', 'n', '-', 'i'], ['J', 'o', 'h', 'n', '-', 'N', 'O', 'M'], [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], none⟩, ⟨['i'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['c', 'i', 'n', 'a', 'n', 'c', 'w', 'u'], ['l', 'a', 's', 't', '.', 'w', 'e', 'e', 'k'], [⟨['c', 'i', 'n', 'a', 'n', 'c', 'w', 'u'], ['l', 'a', 's', 't', '.', 'w', 'e', 'e', 'k'], none⟩]⟩, ⟨['w', 'e', 'l', 'y', 'o', 'i', 'l', '-', 'e', 'y'], ['M', 'o', 'n', 'd', 'a', 'y', '-', 'o', 'n'], [⟨['w', 'e', 'l', 'y', 'o', 'i', 'l'], ['M', 'o', 'n', 'd', 'a', 'y'], none⟩, ⟨['e', 'y'], ['o', 'n'], some '-'⟩]⟩, ⟨['M', 'a', 'r', 'y', '-', 'k', 'a'], ['M', 'a', 'r', 'y', '-', 'N', 'O', 'M'], [⟨['M', 'a', 'r', 'y'], ['M', 'a', 'r', 'y'], none⟩, ⟨['k', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['o', 'n', 'u', 'l'], ['t', 'o', 'd', 'a', 'y'], [⟨['o', 'n', 'u', 'l'], ['t', 'o', 'd', 'a', 'y'], none⟩]⟩, ⟨['t', 't', 'e', 'n', 'a', 'n', 't', 'a', '-', 'k', 'o'], ['l', 'e', 'a', 'v', 'e', '-', 'C'], [⟨['t', 't', 'e', 'n', 'a', 'n', 't', 'a'], ['l', 'e', 'a', 'v', 'e'], none⟩, ⟨['k', 'o'], ['C'], some '-'⟩]⟩, ⟨['m', 'a', 'l', 'h', 'a', 'y', 's', 's', 't', 'a', '.'], ['s', 'a', 'i', 'd'], [⟨['m', 'a', 'l', 'h', 'a', 'y', 's', 's', 't', 'a'], ['s', 'a', 'i', 'd'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("de se", .acceptable), ("non-de se", .unacceptable)]
    paperFeatures := [("verb", "korean_say"), ("indexical", "today"), ("test", "de_se")] }

def ex_161 : Datum :=
  { id := "deal2020_161"
    source := ⟨"park-2016", "fn. 10"⟩
    reportedIn := some ⟨"deal-2020", "(161)"⟩
    language := "kore1280"
    primaryText := "Cinan cwu-ey Mary-ka nwuka nayil ttenanta-ko sayngkakayss-ni?"
    glossedTokens := [("Cinan", "Last"), ("cwu-ey", "week-in"), ("Mary-ka", "Mary-NOM"), ("nwuka", "who-NOM"), ("nayil", "tomorrow"), ("ttenanta-ko", "leave-C"), ("sayngkakayss-ni?", "thought-Q")]
    glossedWords := [⟨['C', 'i', 'n', 'a', 'n'], ['L', 'a', 's', 't'], [⟨['C', 'i', 'n', 'a', 'n'], ['L', 'a', 's', 't'], none⟩]⟩, ⟨['c', 'w', 'u', '-', 'e', 'y'], ['w', 'e', 'e', 'k', '-', 'i', 'n'], [⟨['c', 'w', 'u'], ['w', 'e', 'e', 'k'], none⟩, ⟨['e', 'y'], ['i', 'n'], some '-'⟩]⟩, ⟨['M', 'a', 'r', 'y', '-', 'k', 'a'], ['M', 'a', 'r', 'y', '-', 'N', 'O', 'M'], [⟨['M', 'a', 'r', 'y'], ['M', 'a', 'r', 'y'], none⟩, ⟨['k', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['n', 'w', 'u', 'k', 'a'], ['w', 'h', 'o', '-', 'N', 'O', 'M'], []⟩, ⟨['n', 'a', 'y', 'i', 'l'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['n', 'a', 'y', 'i', 'l'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩, ⟨['t', 't', 'e', 'n', 'a', 'n', 't', 'a', '-', 'k', 'o'], ['l', 'e', 'a', 'v', 'e', '-', 'C'], [⟨['t', 't', 'e', 'n', 'a', 'n', 't', 'a'], ['l', 'e', 'a', 'v', 'e'], none⟩, ⟨['k', 'o'], ['C'], some '-'⟩]⟩, ⟨['s', 'a', 'y', 'n', 'g', 'k', 'a', 'k', 'a', 'y', 's', 's', '-', 'n', 'i', '?'], ['t', 'h', 'o', 'u', 'g', 'h', 't', '-', 'Q'], [⟨['s', 'a', 'y', 'n', 'g', 'k', 'a', 'k', 'a', 'y', 's', 's'], ['t', 'h', 'o', 'u', 'g', 'h', 't'], none⟩, ⟨['n', 'i'], ['Q'], some '-'⟩]⟩]
    lgrConformance := some .wordAligned
    context := "It is January 8th."
    judgment := .acceptable
    contrasts := []
    readings := [("reported context", .acceptable), ("utterance context", .acceptable)]
    paperFeatures := [("verb", "korean_think"), ("indexical", "tomorrow")] }

def ex_162 : Datum :=
  { id := "deal2020_162"
    source := ⟨"park-2016", "(30b)"⟩
    reportedIn := some ⟨"deal-2020", "(162)"⟩
    language := "kore1280"
    primaryText := "Mary-ka nwuka na-lul coahanta-ko sayngkakayss-ni?"
    glossedTokens := [("Mary-ka", "Mary-NOM"), ("nwuka", "who"), ("na-lul", "I-ACC"), ("coahanta-ko", "like-C"), ("sayngkakayss-ni?", "thought-Q")]
    glossedWords := [⟨['M', 'a', 'r', 'y', '-', 'k', 'a'], ['M', 'a', 'r', 'y', '-', 'N', 'O', 'M'], [⟨['M', 'a', 'r', 'y'], ['M', 'a', 'r', 'y'], none⟩, ⟨['k', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['n', 'w', 'u', 'k', 'a'], ['w', 'h', 'o'], [⟨['n', 'w', 'u', 'k', 'a'], ['w', 'h', 'o'], none⟩]⟩, ⟨['n', 'a', '-', 'l', 'u', 'l'], ['I', '-', 'A', 'C', 'C'], [⟨['n', 'a'], ['I'], none⟩, ⟨['l', 'u', 'l'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['c', 'o', 'a', 'h', 'a', 'n', 't', 'a', '-', 'k', 'o'], ['l', 'i', 'k', 'e', '-', 'C'], [⟨['c', 'o', 'a', 'h', 'a', 'n', 't', 'a'], ['l', 'i', 'k', 'e'], none⟩, ⟨['k', 'o'], ['C'], some '-'⟩]⟩, ⟨['s', 'a', 'y', 'n', 'g', 'k', 'a', 'k', 'a', 'y', 's', 's', '-', 'n', 'i', '?'], ['t', 'h', 'o', 'u', 'g', 'h', 't', '-', 'Q'], [⟨['s', 'a', 'y', 'n', 'g', 'k', 'a', 'k', 'a', 'y', 's', 's'], ['t', 'h', 'o', 'u', 'g', 'h', 't'], none⟩, ⟨['n', 'i'], ['Q'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("utterance context", .acceptable), ("reported context", .unacceptable)]
    paperFeatures := [("verb", "korean_think"), ("indexical", "I")] }

def ex_175 : Datum :=
  { id := "deal2020_175"
    source := ⟨"park-2016", "(25)"⟩
    reportedIn := some ⟨"deal-2020", "(175)"⟩
    language := "kore1280"
    primaryText := "Tom-i ece cenyek New York-eyse Sue-ka ece yeki-ey wassta-ko malhayssta."
    glossedTokens := [("Tom-i", "Tom-NOM"), ("ece", "yesterday"), ("cenyek", "night"), ("New York-eyse", "New York-at"), ("Sue-ka", "Sue-NOM"), ("ece", "yesterday"), ("yeki-ey", "here-at"), ("wassta-ko", "came-C"), ("malhayssta.", "said")]
    glossedWords := [⟨['T', 'o', 'm', '-', 'i'], ['T', 'o', 'm', '-', 'N', 'O', 'M'], [⟨['T', 'o', 'm'], ['T', 'o', 'm'], none⟩, ⟨['i'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['e', 'c', 'e'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['e', 'c', 'e'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩, ⟨['c', 'e', 'n', 'y', 'e', 'k'], ['n', 'i', 'g', 'h', 't'], [⟨['c', 'e', 'n', 'y', 'e', 'k'], ['n', 'i', 'g', 'h', 't'], none⟩]⟩, ⟨['N', 'e', 'w', ' ', 'Y', 'o', 'r', 'k', '-', 'e', 'y', 's', 'e'], ['N', 'e', 'w', ' ', 'Y', 'o', 'r', 'k', '-', 'a', 't'], [⟨['N', 'e', 'w', ' ', 'Y', 'o', 'r', 'k'], ['N', 'e', 'w', ' ', 'Y', 'o', 'r', 'k'], none⟩, ⟨['e', 'y', 's', 'e'], ['a', 't'], some '-'⟩]⟩, ⟨['S', 'u', 'e', '-', 'k', 'a'], ['S', 'u', 'e', '-', 'N', 'O', 'M'], [⟨['S', 'u', 'e'], ['S', 'u', 'e'], none⟩, ⟨['k', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['e', 'c', 'e'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['e', 'c', 'e'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩, ⟨['y', 'e', 'k', 'i', '-', 'e', 'y'], ['h', 'e', 'r', 'e', '-', 'a', 't'], [⟨['y', 'e', 'k', 'i'], ['h', 'e', 'r', 'e'], none⟩, ⟨['e', 'y'], ['a', 't'], some '-'⟩]⟩, ⟨['w', 'a', 's', 's', 't', 'a', '-', 'k', 'o'], ['c', 'a', 'm', 'e', '-', 'C'], [⟨['w', 'a', 's', 's', 't', 'a'], ['c', 'a', 'm', 'e'], none⟩, ⟨['k', 'o'], ['C'], some '-'⟩]⟩, ⟨['m', 'a', 'l', 'h', 'a', 'y', 's', 's', 't', 'a', '.'], ['s', 'a', 'i', 'd'], [⟨['m', 'a', 'l', 'h', 'a', 'y', 's', 's', 't', 'a'], ['s', 'a', 'i', 'd'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "John and Mary are having a conversation in Boston on July 3rd. John says:"
    judgment := .acceptable
    contrasts := []
    readings := [("both utterance", .acceptable), ("both reported", .acceptable), ("second reported only", .unacceptable), ("first reported only", .unacceptable)]
    paperFeatures := [("verb", "korean_say"), ("indexical", "yesterday"), ("indexical", "here")] }

def ex_176 : Datum :=
  { id := "deal2020_176"
    source := ⟨"park-2016", "(32)"⟩
    reportedIn := some ⟨"deal-2020", "(176)"⟩
    language := "kore1280"
    primaryText := "Tom-i New York-eyse nay-ka yeki-eyse thayenassta-ko malhayssta."
    glossedTokens := [("Tom-i", "Tom-NOM"), ("New York-eyse", "New York-at"), ("nay-ka", "I-NOM"), ("yeki-eyse", "here-at"), ("thayenassta-ko", "be.born-C"), ("malhayssta.", "said")]
    glossedWords := [⟨['T', 'o', 'm', '-', 'i'], ['T', 'o', 'm', '-', 'N', 'O', 'M'], [⟨['T', 'o', 'm'], ['T', 'o', 'm'], none⟩, ⟨['i'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['N', 'e', 'w', ' ', 'Y', 'o', 'r', 'k', '-', 'e', 'y', 's', 'e'], ['N', 'e', 'w', ' ', 'Y', 'o', 'r', 'k', '-', 'a', 't'], [⟨['N', 'e', 'w', ' ', 'Y', 'o', 'r', 'k'], ['N', 'e', 'w', ' ', 'Y', 'o', 'r', 'k'], none⟩, ⟨['e', 'y', 's', 'e'], ['a', 't'], some '-'⟩]⟩, ⟨['n', 'a', 'y', '-', 'k', 'a'], ['I', '-', 'N', 'O', 'M'], [⟨['n', 'a', 'y'], ['I'], none⟩, ⟨['k', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['y', 'e', 'k', 'i', '-', 'e', 'y', 's', 'e'], ['h', 'e', 'r', 'e', '-', 'a', 't'], [⟨['y', 'e', 'k', 'i'], ['h', 'e', 'r', 'e'], none⟩, ⟨['e', 'y', 's', 'e'], ['a', 't'], some '-'⟩]⟩, ⟨['t', 'h', 'a', 'y', 'e', 'n', 'a', 's', 's', 't', 'a', '-', 'k', 'o'], ['b', 'e', '.', 'b', 'o', 'r', 'n', '-', 'C'], [⟨['t', 'h', 'a', 'y', 'e', 'n', 'a', 's', 's', 't', 'a'], ['b', 'e', '.', 'b', 'o', 'r', 'n'], none⟩, ⟨['k', 'o'], ['C'], some '-'⟩]⟩, ⟨['m', 'a', 'l', 'h', 'a', 'y', 's', 's', 't', 'a', '.'], ['s', 'a', 'i', 'd'], [⟨['m', 'a', 'l', 'h', 'a', 'y', 's', 's', 't', 'a'], ['s', 'a', 'i', 'd'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "John and Mary are having a conversation in Seoul. John says:"
    judgment := .acceptable
    contrasts := []
    readings := [("both utterance", .acceptable), ("second reported only", .acceptable), ("first reported only", .acceptable), ("both reported", .acceptable)]
    paperFeatures := [("verb", "korean_say"), ("indexical", "I"), ("indexical", "here")] }

def ex_165 : Datum :=
  { id := "deal2020_165"
    source := ⟨"deal-2020", "(165)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "When I saw Kate a week ago, she said that she’d seen Star Wars yesterday."
    glossedTokens := []
    context := ""
    judgment := .variable
    contrasts := []
    readings := [("reported context", .acceptable)]
    paperFeatures := [("verb", "anderson_say"), ("indexical", "yesterday"), ("variety", "Anderson English")] }

def ex_166 : Datum :=
  { id := "deal2020_166"
    source := ⟨"deal-2020", "(166)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Last Thursday, John said that he was going to come over tomorrow, but he showed up on Saturday instead!"
    glossedTokens := []
    context := "John is confused on Thursday and thinks the date is the 23rd, when it is really the 24th. On Thursday, John tells Sarah, “I’m coming on the 25th.” But he doesn’t show up until Saturday. A week later, Sarah is telling Bill what happened. She says:"
    judgment := .variable
    contrasts := []
    readings := [("non-de se", .acceptable)]
    paperFeatures := [("verb", "anderson_say"), ("indexical", "tomorrow"), ("variety", "Anderson English"), ("test", "de_se")] }

def all : List Datum := [ex_70, ex_73, ex_83, ex_87, ex_111, ex_113, ex_115, ex_118, ex_121, ex_124, ex_117, ex_120, ex_123, ex_103b, ex_122, ex_106, ex_119, ex_159, ex_161, ex_162, ex_175, ex_176, ex_165, ex_166]

end Deal2020.Examples
