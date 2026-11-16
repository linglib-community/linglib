module

public import Linglib.Data.Examples.Schema

/-!
# `Deal2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Deal2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Deal2026.Examples`.
-/

@[expose] public section

namespace Deal2026.Examples

def ex_28a : Datum :=
  { id := "deal2026_28a"
    source := ⟨"deal-2026", "(28a)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "’Aayat hi-llooy-ca-∅ yox̂ ke ma-may’ac hi-pa-paay-n-∅."
    glossedTokens := [("’Aayat", "woman.nom"), ("hi-llooy-ca-∅", "3subj-be.happy-imperf-pres"), ("yox̂", "rp.nom"), ("ke", "CĀ"), ("ma-may’ac", "pl-child"), ("hi-pa-paay-n-∅", "3subj-S.pl-arrive-p-pres")]
    glossedWords := [⟨[['’', 'A', 'a', 'y', 'a', 't']], [['w', 'o', 'm', 'a', 'n', '.', 'n', 'o', 'm']]⟩, ⟨[['h', 'i'], ['l', 'l', 'o', 'o', 'y'], ['c', 'a'], ['∅']], [['3', 's', 'u', 'b', 'j'], ['b', 'e', '.', 'h', 'a', 'p', 'p', 'y'], ['i', 'm', 'p', 'e', 'r', 'f'], ['p', 'r', 'e', 's']]⟩, ⟨[['y', 'o', 'x', '̂']], [['r', 'p', '.', 'n', 'o', 'm']]⟩, ⟨[['k', 'e']], [['C', 'Ā']]⟩, ⟨[['m', 'a'], ['m', 'a', 'y', '’', 'a', 'c']], [['p', 'l'], ['c', 'h', 'i', 'l', 'd']]⟩, ⟨[['h', 'i'], ['p', 'a'], ['p', 'a', 'a', 'y'], ['n'], ['∅']], [['3', 's', 'u', 'b', 'j'], ['S', '.', 'p', 'l'], ['a', 'r', 'r', 'i', 'v', 'e'], ['p'], ['p', 'r', 'e', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := [("’Aayat hi-llooy-ca-∅ ma-may’ac hi-pa-paay-n-∅.", .ungrammatical)]
    readings := []
    paperFeatures := [("verb", "lilooy"), ("edge", "yoxKe"), ("diagnostic", "edge")] }

def ex_28b : Datum :=
  { id := "deal2026_28b"
    source := ⟨"deal-2026", "(28b)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "pro cicwaay-ca-∅ yox̂ ke pro kuleewit-nix hi-paay-no’."
    glossedTokens := [("pro", "1sg"), ("cicwaay-ca-∅", "be.surprised-imperf-pres"), ("yox̂", "rp.nom"), ("ke", "CĀ"), ("pro", "3sg"), ("kuleewit-nix", "evening-emph"), ("hi-paay-no’", "3subj-arrive-prosp")]
    glossedWords := [⟨[['p', 'r', 'o']], [['1', 's', 'g']]⟩, ⟨[['c', 'i', 'c', 'w', 'a', 'a', 'y'], ['c', 'a'], ['∅']], [['b', 'e', '.', 's', 'u', 'r', 'p', 'r', 'i', 's', 'e', 'd'], ['i', 'm', 'p', 'e', 'r', 'f'], ['p', 'r', 'e', 's']]⟩, ⟨[['y', 'o', 'x', '̂']], [['r', 'p', '.', 'n', 'o', 'm']]⟩, ⟨[['k', 'e']], [['C', 'Ā']]⟩, ⟨[['p', 'r', 'o']], [['3', 's', 'g']]⟩, ⟨[['k', 'u', 'l', 'e', 'e', 'w', 'i', 't'], ['n', 'i', 'x']], [['e', 'v', 'e', 'n', 'i', 'n', 'g'], ['e', 'm', 'p', 'h']]⟩, ⟨[['h', 'i'], ['p', 'a', 'a', 'y'], ['n', 'o', '’']], [['3', 's', 'u', 'b', 'j'], ['a', 'r', 'r', 'i', 'v', 'e'], ['p', 'r', 'o', 's', 'p']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := [("pro cicwaay-ca-∅ pro kuleewit-nix hi-paay-no’.", .ungrammatical)]
    readings := []
    paperFeatures := [("verb", "cicwaay"), ("edge", "yoxKe"), ("diagnostic", "edge")] }

def ex_27b : Datum :=
  { id := "deal2026_27b"
    source := ⟨"deal-2026", "(27b)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "pro hi-’etqew-ce-∅ yox̂ ke-x ’iin wixne-tet’ee-se-∅."
    glossedTokens := [("pro", "3sg"), ("hi-’etqew-ce-∅", "3subj-be.sad-imperf-pres"), ("yox̂", "rp.nom"), ("ke-x", "CĀ-1"), ("’iin", "1sg.nom"), ("wixne-tet’ee-se-∅", "leave-gonna-imperf-pres")]
    glossedWords := [⟨[['p', 'r', 'o']], [['3', 's', 'g']]⟩, ⟨[['h', 'i'], ['’', 'e', 't', 'q', 'e', 'w'], ['c', 'e'], ['∅']], [['3', 's', 'u', 'b', 'j'], ['b', 'e', '.', 's', 'a', 'd'], ['i', 'm', 'p', 'e', 'r', 'f'], ['p', 'r', 'e', 's']]⟩, ⟨[['y', 'o', 'x', '̂']], [['r', 'p', '.', 'n', 'o', 'm']]⟩, ⟨[['k', 'e'], ['x']], [['C', 'Ā'], ['1']]⟩, ⟨[['’', 'i', 'i', 'n']], [['1', 's', 'g', '.', 'n', 'o', 'm']]⟩, ⟨[['w', 'i', 'x', 'n', 'e'], ['t', 'e', 't', '’', 'e', 'e'], ['s', 'e'], ['∅']], [['l', 'e', 'a', 'v', 'e'], ['g', 'o', 'n', 'n', 'a'], ['i', 'm', 'p', 'e', 'r', 'f'], ['p', 'r', 'e', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "’etqew"), ("edge", "yoxKe"), ("diagnostic", "edge")] }

def ex_27d : Datum :=
  { id := "deal2026_27d"
    source := ⟨"deal-2026", "(27d)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "’Aayat hi-tmiipni-se-∅ yox̂ ke pro hi-pa-paay-n-a."
    glossedTokens := [("’Aayat", "woman.nom"), ("hi-tmiipni-se-∅", "3subj-remember-imperf-pres"), ("yox̂", "rp.nom"), ("ke", "CĀ"), ("pro", "3pl"), ("hi-pa-paay-n-a", "3subj-S.pl-arrive-p-rem.past")]
    glossedWords := [⟨[['’', 'A', 'a', 'y', 'a', 't']], [['w', 'o', 'm', 'a', 'n', '.', 'n', 'o', 'm']]⟩, ⟨[['h', 'i'], ['t', 'm', 'i', 'i', 'p', 'n', 'i'], ['s', 'e'], ['∅']], [['3', 's', 'u', 'b', 'j'], ['r', 'e', 'm', 'e', 'm', 'b', 'e', 'r'], ['i', 'm', 'p', 'e', 'r', 'f'], ['p', 'r', 'e', 's']]⟩, ⟨[['y', 'o', 'x', '̂']], [['r', 'p', '.', 'n', 'o', 'm']]⟩, ⟨[['k', 'e']], [['C', 'Ā']]⟩, ⟨[['p', 'r', 'o']], [['3', 'p', 'l']]⟩, ⟨[['h', 'i'], ['p', 'a'], ['p', 'a', 'a', 'y'], ['n'], ['a']], [['3', 's', 'u', 'b', 'j'], ['S', '.', 'p', 'l'], ['a', 'r', 'r', 'i', 'v', 'e'], ['p'], ['r', 'e', 'm', '.', 'p', 'a', 's', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "timiipni"), ("edge", "yoxKe"), ("diagnostic", "edge")] }

def ex_27e_eeys : Datum :=
  { id := "deal2026_27e_eeys"
    source := ⟨"deal-2026", "(27e)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "pro he-’eey’s-ce-∅ yox̂ ke pro hi-pa-paay-n-∅."
    glossedTokens := [("pro", "3sg"), ("he-’eey’s-ce-∅", "3subj-be.joyful-imperf-pres"), ("yox̂", "rp.nom"), ("ke", "CĀ"), ("pro", "3pl"), ("hi-pa-paay-n-∅", "3subj-S.pl-arrive-p-pres")]
    glossedWords := [⟨[['p', 'r', 'o']], [['3', 's', 'g']]⟩, ⟨[['h', 'e'], ['’', 'e', 'e', 'y', '’', 's'], ['c', 'e'], ['∅']], [['3', 's', 'u', 'b', 'j'], ['b', 'e', '.', 'j', 'o', 'y', 'f', 'u', 'l'], ['i', 'm', 'p', 'e', 'r', 'f'], ['p', 'r', 'e', 's']]⟩, ⟨[['y', 'o', 'x', '̂']], [['r', 'p', '.', 'n', 'o', 'm']]⟩, ⟨[['k', 'e']], [['C', 'Ā']]⟩, ⟨[['p', 'r', 'o']], [['3', 'p', 'l']]⟩, ⟨[['h', 'i'], ['p', 'a'], ['p', 'a', 'a', 'y'], ['n'], ['∅']], [['3', 's', 'u', 'b', 'j'], ['S', '.', 'p', 'l'], ['a', 'r', 'r', 'i', 'v', 'e'], ['p'], ['p', 'r', 'e', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "’eey’s"), ("edge", "yoxKe"), ("diagnostic", "edge")] }

def ex_27e_qeese : Datum :=
  { id := "deal2026_27e_qeese"
    source := ⟨"deal-2026", "(27e)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "pro hi-q’eese’-ce-∅ yox̂ ke pro hi-pa-paay-n-∅."
    glossedTokens := [("pro", "3sg"), ("hi-q’eese’-ce-∅", "3subj-be.bothered-imperf-pres"), ("yox̂", "rp.nom"), ("ke", "CĀ"), ("pro", "3pl"), ("hi-pa-paay-n-∅", "3subj-S.pl-arrive-p-pres")]
    glossedWords := [⟨[['p', 'r', 'o']], [['3', 's', 'g']]⟩, ⟨[['h', 'i'], ['q', '’', 'e', 'e', 's', 'e', '’'], ['c', 'e'], ['∅']], [['3', 's', 'u', 'b', 'j'], ['b', 'e', '.', 'b', 'o', 't', 'h', 'e', 'r', 'e', 'd'], ['i', 'm', 'p', 'e', 'r', 'f'], ['p', 'r', 'e', 's']]⟩, ⟨[['y', 'o', 'x', '̂']], [['r', 'p', '.', 'n', 'o', 'm']]⟩, ⟨[['k', 'e']], [['C', 'Ā']]⟩, ⟨[['p', 'r', 'o']], [['3', 'p', 'l']]⟩, ⟨[['h', 'i'], ['p', 'a'], ['p', 'a', 'a', 'y'], ['n'], ['∅']], [['3', 's', 'u', 'b', 'j'], ['S', '.', 'p', 'l'], ['a', 'r', 'r', 'i', 'v', 'e'], ['p'], ['p', 'r', 'e', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "q’eese’"), ("edge", "yoxKe"), ("diagnostic", "edge")] }

def ex_27e_timneeneki : Datum :=
  { id := "deal2026_27e_timneeneki"
    source := ⟨"deal-2026", "(27e)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "pro hi-tim’neenek-se-∅ yox̂ ke pro hi-pa-paay-n-∅."
    glossedTokens := [("pro", "3sg"), ("hi-tim’neenek-se-∅", "3subj-be.worried-imperf-pres"), ("yox̂", "rp.nom"), ("ke", "CĀ"), ("pro", "3pl"), ("hi-pa-paay-n-∅", "3subj-S.pl-arrive-p-pres")]
    glossedWords := [⟨[['p', 'r', 'o']], [['3', 's', 'g']]⟩, ⟨[['h', 'i'], ['t', 'i', 'm', '’', 'n', 'e', 'e', 'n', 'e', 'k'], ['s', 'e'], ['∅']], [['3', 's', 'u', 'b', 'j'], ['b', 'e', '.', 'w', 'o', 'r', 'r', 'i', 'e', 'd'], ['i', 'm', 'p', 'e', 'r', 'f'], ['p', 'r', 'e', 's']]⟩, ⟨[['y', 'o', 'x', '̂']], [['r', 'p', '.', 'n', 'o', 'm']]⟩, ⟨[['k', 'e']], [['C', 'Ā']]⟩, ⟨[['p', 'r', 'o']], [['3', 'p', 'l']]⟩, ⟨[['h', 'i'], ['p', 'a'], ['p', 'a', 'a', 'y'], ['n'], ['∅']], [['3', 's', 'u', 'b', 'j'], ['S', '.', 'p', 'l'], ['a', 'r', 'r', 'i', 'v', 'e'], ['p'], ['p', 'r', 'e', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "tim’neeneki"), ("edge", "yoxKe"), ("diagnostic", "edge")] }

def ex_41a : Datum :=
  { id := "deal2026_41a"
    source := ⟨"deal-2026", "(41a)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "Naaqc-nim qiiwn-e pe-’eey’s-ce-∅."
    glossedTokens := [("Naaqc-nim", "one-erg"), ("qiiwn-e", "old.man-acc"), ("pe-’eey’s-ce-∅", "3/3-be.joyful-imperf-pres")]
    glossedWords := [⟨[['N', 'a', 'a', 'q', 'c'], ['n', 'i', 'm']], [['o', 'n', 'e'], ['e', 'r', 'g']]⟩, ⟨[['q', 'i', 'i', 'w', 'n'], ['e']], [['o', 'l', 'd', '.', 'm', 'a', 'n'], ['a', 'c', 'c']]⟩, ⟨[['p', 'e'], ['’', 'e', 'e', 'y', '’', 's'], ['c', 'e'], ['∅']], [['3', '/', '3'], ['b', 'e', '.', 'j', 'o', 'y', 'f', 'u', 'l'], ['i', 'm', 'p', 'e', 'r', 'f'], ['p', 'r', 'e', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "’eey’s"), ("diagnostic", "nominalComplement")] }

def ex_41b : Datum :=
  { id := "deal2026_41b"
    source := ⟨"deal-2026", "(41b)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "pro he-’eey’s-ce-∅ titwaatit."
    glossedTokens := [("pro", "3sg"), ("he-’eey’s-ce-∅", "3subj-be.joyful-imperf-pres"), ("titwaatit", "story.nom")]
    glossedWords := [⟨[['p', 'r', 'o']], [['3', 's', 'g']]⟩, ⟨[['h', 'e'], ['’', 'e', 'e', 'y', '’', 's'], ['c', 'e'], ['∅']], [['3', 's', 'u', 'b', 'j'], ['b', 'e', '.', 'j', 'o', 'y', 'f', 'u', 'l'], ['i', 'm', 'p', 'e', 'r', 'f'], ['p', 'r', 'e', 's']]⟩, ⟨[['t', 'i', 't', 'w', 'a', 'a', 't', 'i', 't']], [['s', 't', 'o', 'r', 'y', '.', 'n', 'o', 'm']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "’eey’s"), ("diagnostic", "nominalComplement")] }

def ex_42a : Datum :=
  { id := "deal2026_42a"
    source := ⟨"deal-2026", "(42a)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "Qe’ciyeew’yew’ yox̂ ke-m pro tamtaayn-im pro."
    glossedTokens := [("Qe’ciyeew’yew’", "thank.you"), ("yox̂", "rp.nom"), ("ke-m", "CĀ-2"), ("pro", "2sg"), ("tamtaayn-im", "tell.news-cisloc"), ("pro", "1sg")]
    glossedWords := [⟨[['Q', 'e', '’', 'c', 'i', 'y', 'e', 'e', 'w', '’', 'y', 'e', 'w', '’']], [['t', 'h', 'a', 'n', 'k', '.', 'y', 'o', 'u']]⟩, ⟨[['y', 'o', 'x', '̂']], [['r', 'p', '.', 'n', 'o', 'm']]⟩, ⟨[['k', 'e'], ['m']], [['C', 'Ā'], ['2']]⟩, ⟨[['p', 'r', 'o']], [['2', 's', 'g']]⟩, ⟨[['t', 'a', 'm', 't', 'a', 'a', 'y', 'n'], ['i', 'm']], [['t', 'e', 'l', 'l', '.', 'n', 'e', 'w', 's'], ['c', 'i', 's', 'l', 'o', 'c']]⟩, ⟨[['p', 'r', 'o']], [['1', 's', 'g']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "qe’ciyeew’yew’"), ("edge", "yoxKe"), ("diagnostic", "edge")] }

def ex_42b : Datum :=
  { id := "deal2026_42b"
    source := ⟨"deal-2026", "(42b)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "Qe’ciyeew’yew’ hipt."
    glossedTokens := [("Qe’ciyeew’yew’", "thank.you"), ("hipt", "food.nom")]
    glossedWords := [⟨[['Q', 'e', '’', 'c', 'i', 'y', 'e', 'e', 'w', '’', 'y', 'e', 'w', '’']], [['t', 'h', 'a', 'n', 'k', '.', 'y', 'o', 'u']]⟩, ⟨[['h', 'i', 'p', 't']], [['f', 'o', 'o', 'd', '.', 'n', 'o', 'm']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := [("Qe’ciyeew’yew’ tamtaayn.", .ungrammatical)]
    readings := []
    paperFeatures := [("verb", "qe’ciyeew’yew’"), ("diagnostic", "nominalComplement")] }

def ex_47a : Datum :=
  { id := "deal2026_47a"
    source := ⟨"deal-2026", "(47a)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "pro ’a-w-caa-qa ’in-lawtiwaa-na hi-weeqi-yu’."
    glossedTokens := [("pro", "1sg"), ("’a-w-caa-qa", "3obj-say-imperf-rec.past"), ("’in-lawtiwaa-na", "1sg-friend-acc"), ("hi-weeqi-yu’", "3subj-rain-prosp")]
    glossedWords := [⟨[['p', 'r', 'o']], [['1', 's', 'g']]⟩, ⟨[['’', 'a'], ['w'], ['c', 'a', 'a'], ['q', 'a']], [['3', 'o', 'b', 'j'], ['s', 'a', 'y'], ['i', 'm', 'p', 'e', 'r', 'f'], ['r', 'e', 'c', '.', 'p', 'a', 's', 't']]⟩, ⟨[['’', 'i', 'n'], ['l', 'a', 'w', 't', 'i', 'w', 'a', 'a'], ['n', 'a']], [['1', 's', 'g'], ['f', 'r', 'i', 'e', 'n', 'd'], ['a', 'c', 'c']]⟩, ⟨[['h', 'i'], ['w', 'e', 'e', 'q', 'i'], ['y', 'u', '’']], [['3', 's', 'u', 'b', 'j'], ['r', 'a', 'i', 'n'], ['p', 'r', 'o', 's', 'p']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := [("pro ’a-w-caa-qa ’in-lawtiwaa-na yox̂ ke hi-weeqi-yu’.", .ungrammatical)]
    readings := []
    paperFeatures := [("verb", "hi"), ("edge", "bare"), ("diagnostic", "edge")] }

def ex_47b : Datum :=
  { id := "deal2026_47b"
    source := ⟨"deal-2026", "(47b)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "pro ’ew-∅-ce-ne ’in-lawtiwaa-na tamtaay-ki."
    glossedTokens := [("pro", "1sg"), ("’ew-∅-ce-ne", "3obj-say-imperf-rem.past"), ("’in-lawtiwaa-na", "1sg-friend-acc"), ("tamtaay-ki", "news-inst")]
    glossedWords := [⟨[['p', 'r', 'o']], [['1', 's', 'g']]⟩, ⟨[['’', 'e', 'w'], ['∅'], ['c', 'e'], ['n', 'e']], [['3', 'o', 'b', 'j'], ['s', 'a', 'y'], ['i', 'm', 'p', 'e', 'r', 'f'], ['r', 'e', 'm', '.', 'p', 'a', 's', 't']]⟩, ⟨[['’', 'i', 'n'], ['l', 'a', 'w', 't', 'i', 'w', 'a', 'a'], ['n', 'a']], [['1', 's', 'g'], ['f', 'r', 'i', 'e', 'n', 'd'], ['a', 'c', 'c']]⟩, ⟨[['t', 'a', 'm', 't', 'a', 'a', 'y'], ['k', 'i']], [['n', 'e', 'w', 's'], ['i', 'n', 's', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "hi"), ("diagnostic", "aboutPP")] }

def ex_48a : Datum :=
  { id := "deal2026_48a"
    source := ⟨"deal-2026", "(48a)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "pro hi-neki-se-∅ hi-waaqi-sa-qa watiisx."
    glossedTokens := [("pro", "3sg"), ("hi-neki-se-∅", "3subj-think-pres"), ("hi-waaqi-sa-qa", "3subj-rain-imperf-rec.past"), ("watiisx", "one.day.away")]
    glossedWords := [⟨[['p', 'r', 'o']], [['3', 's', 'g']]⟩, ⟨[['h', 'i'], ['n', 'e', 'k', 'i'], ['s', 'e'], ['∅']], [['3', 's', 'u', 'b', 'j'], ['t', 'h', 'i', 'n', 'k'], ['p', 'r', 'e', 's']]⟩, ⟨[['h', 'i'], ['w', 'a', 'a', 'q', 'i'], ['s', 'a'], ['q', 'a']], [['3', 's', 'u', 'b', 'j'], ['r', 'a', 'i', 'n'], ['i', 'm', 'p', 'e', 'r', 'f'], ['r', 'e', 'c', '.', 'p', 'a', 's', 't']]⟩, ⟨[['w', 'a', 't', 'i', 'i', 's', 'x']], [['o', 'n', 'e', '.', 'd', 'a', 'y', '.', 'a', 'w', 'a', 'y']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("pro hi-neki-se-∅ yox̂ ke hi-waaqi-sa-qa watiisx.", .ungrammatical)]
    readings := []
    paperFeatures := [("verb", "neki"), ("edge", "bare"), ("diagnostic", "edge")] }

def ex_48b : Datum :=
  { id := "deal2026_48b"
    source := ⟨"deal-2026", "(48b)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "pro neki-se-∅ kimti tamtaay-ki. Weet’u ta’c pro hii-wes."
    glossedTokens := [("pro", "1sg"), ("neki-se-∅", "think-imperf-pres"), ("kimti", "new"), ("tamtaay-ki", "news-inst"), ("Weet’u", "neg"), ("ta’c", "good"), ("pro", "3sg"), ("hii-wes", "3subj-be.pres")]
    glossedWords := [⟨[['p', 'r', 'o']], [['1', 's', 'g']]⟩, ⟨[['n', 'e', 'k', 'i'], ['s', 'e'], ['∅']], [['t', 'h', 'i', 'n', 'k'], ['i', 'm', 'p', 'e', 'r', 'f'], ['p', 'r', 'e', 's']]⟩, ⟨[['k', 'i', 'm', 't', 'i']], [['n', 'e', 'w']]⟩, ⟨[['t', 'a', 'm', 't', 'a', 'a', 'y'], ['k', 'i']], [['n', 'e', 'w', 's'], ['i', 'n', 's', 't']]⟩, ⟨[['W', 'e', 'e', 't', '’', 'u']], [['n', 'e', 'g']]⟩, ⟨[['t', 'a', '’', 'c']], [['g', 'o', 'o', 'd']]⟩, ⟨[['p', 'r', 'o']], [['3', 's', 'g']]⟩, ⟨[['h', 'i', 'i'], ['w', 'e', 's']], [['3', 's', 'u', 'b', 'j'], ['b', 'e', '.', 'p', 'r', 'e', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "neki"), ("diagnostic", "aboutPP")] }

def ex_65b : Datum :=
  { id := "deal2026_65b"
    source := ⟨"deal-2026", "(65b)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "pro hi-i-caa-qa watiisx hi-weeqi-∅-ye."
    glossedTokens := [("pro", "3sg"), ("hi-i-caa-qa", "3subj-say-imperf-rec.past"), ("watiisx", "one.day.away"), ("hi-weeqi-∅-ye", "3subj-rain-p-rem.past")]
    glossedWords := [⟨[['p', 'r', 'o']], [['3', 's', 'g']]⟩, ⟨[['h', 'i'], ['i'], ['c', 'a', 'a'], ['q', 'a']], [['3', 's', 'u', 'b', 'j'], ['s', 'a', 'y'], ['i', 'm', 'p', 'e', 'r', 'f'], ['r', 'e', 'c', '.', 'p', 'a', 's', 't']]⟩, ⟨[['w', 'a', 't', 'i', 'i', 's', 'x']], [['o', 'n', 'e', '.', 'd', 'a', 'y', '.', 'a', 'w', 'a', 'y']]⟩, ⟨[['h', 'i'], ['w', 'e', 'e', 'q', 'i'], ['∅'], ['y', 'e']], [['3', 's', 'u', 'b', 'j'], ['r', 'a', 'i', 'n'], ['p'], ['r', 'e', 'm', '.', 'p', 'a', 's', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := [("pro hi-i-caa-qa yox̂ ke watiisx hi-weeqi-∅-ye.", .ungrammatical)]
    readings := []
    paperFeatures := [("verb", "hi"), ("edge", "bare"), ("diagnostic", "edge")] }

def ex_66a : Datum :=
  { id := "deal2026_66a"
    source := ⟨"deal-2026", "(66a)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "Waaqo’ pro hi-cuukwe-ce-∅ hi-weeqi-se-∅."
    glossedTokens := [("Waaqo’", "now"), ("pro", "3sg"), ("hi-cuukwe-ce-∅", "3subj-know-imperf-pres"), ("hi-weeqi-se-∅", "3subj-rain-imperf-pres")]
    glossedWords := [⟨[['W', 'a', 'a', 'q', 'o', '’']], [['n', 'o', 'w']]⟩, ⟨[['p', 'r', 'o']], [['3', 's', 'g']]⟩, ⟨[['h', 'i'], ['c', 'u', 'u', 'k', 'w', 'e'], ['c', 'e'], ['∅']], [['3', 's', 'u', 'b', 'j'], ['k', 'n', 'o', 'w'], ['i', 'm', 'p', 'e', 'r', 'f'], ['p', 'r', 'e', 's']]⟩, ⟨[['h', 'i'], ['w', 'e', 'e', 'q', 'i'], ['s', 'e'], ['∅']], [['3', 's', 'u', 'b', 'j'], ['r', 'a', 'i', 'n'], ['i', 'm', 'p', 'e', 'r', 'f'], ['p', 'r', 'e', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "cuukwe"), ("edge", "bare"), ("diagnostic", "edge")] }

def ex_66b : Datum :=
  { id := "deal2026_66b"
    source := ⟨"deal-2026", "(66b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nezp1238"
    primaryText := "Weet’u pro hi-cuukwe-ce-∅ yox̂ ke hi-weeqi-sa-qa watiisx."
    glossedTokens := [("Weet’u", "neg"), ("pro", "3sg"), ("hi-cuukwe-ce-∅", "3subj-know-imperf-pres"), ("yox̂", "rp.nom"), ("ke", "CĀ"), ("hi-weeqi-sa-qa", "3subj-rain-imperf-rec.past"), ("watiisx", "one.day.away")]
    glossedWords := [⟨[['W', 'e', 'e', 't', '’', 'u']], [['n', 'e', 'g']]⟩, ⟨[['p', 'r', 'o']], [['3', 's', 'g']]⟩, ⟨[['h', 'i'], ['c', 'u', 'u', 'k', 'w', 'e'], ['c', 'e'], ['∅']], [['3', 's', 'u', 'b', 'j'], ['k', 'n', 'o', 'w'], ['i', 'm', 'p', 'e', 'r', 'f'], ['p', 'r', 'e', 's']]⟩, ⟨[['y', 'o', 'x', '̂']], [['r', 'p', '.', 'n', 'o', 'm']]⟩, ⟨[['k', 'e']], [['C', 'Ā']]⟩, ⟨[['h', 'i'], ['w', 'e', 'e', 'q', 'i'], ['s', 'a'], ['q', 'a']], [['3', 's', 'u', 'b', 'j'], ['r', 'a', 'i', 'n'], ['i', 'm', 'p', 'e', 'r', 'f'], ['r', 'e', 'c', '.', 'p', 'a', 's', 't']]⟩, ⟨[['w', 'a', 't', 'i', 'i', 's', 'x']], [['o', 'n', 'e', '.', 'd', 'a', 'y', '.', 'a', 'w', 'a', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .variable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "cuukwe"), ("edge", "yoxKe"), ("diagnostic", "edge")] }

def ex_33 : Datum :=
  { id := "deal2026_33"
    source := ⟨"deal-2026", "(33)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "Weet’u ’in-haama hi-llooy-ca-∅ yox̂ ke Fido hi-ckiliitoq-∅-a."
    glossedTokens := [("Weet’u", "neg"), ("’in-haama", "1sg-husband.nom"), ("hi-llooy-ca-∅", "3subj-be.happy-imperf-pres"), ("yox̂", "rp.nom"), ("ke", "CĀ"), ("Fido", "Fido.nom"), ("hi-ckiliitoq-∅-a", "3subj-go.back-p-rem.past")]
    glossedWords := [⟨[['W', 'e', 'e', 't', '’', 'u']], [['n', 'e', 'g']]⟩, ⟨[['’', 'i', 'n'], ['h', 'a', 'a', 'm', 'a']], [['1', 's', 'g'], ['h', 'u', 's', 'b', 'a', 'n', 'd', '.', 'n', 'o', 'm']]⟩, ⟨[['h', 'i'], ['l', 'l', 'o', 'o', 'y'], ['c', 'a'], ['∅']], [['3', 's', 'u', 'b', 'j'], ['b', 'e', '.', 'h', 'a', 'p', 'p', 'y'], ['i', 'm', 'p', 'e', 'r', 'f'], ['p', 'r', 'e', 's']]⟩, ⟨[['y', 'o', 'x', '̂']], [['r', 'p', '.', 'n', 'o', 'm']]⟩, ⟨[['k', 'e']], [['C', 'Ā']]⟩, ⟨[['F', 'i', 'd', 'o']], [['F', 'i', 'd', 'o', '.', 'n', 'o', 'm']]⟩, ⟨[['h', 'i'], ['c', 'k', 'i', 'l', 'i', 'i', 't', 'o', 'q'], ['∅'], ['a']], [['3', 's', 'u', 'b', 'j'], ['g', 'o', '.', 'b', 'a', 'c', 'k'], ['p'], ['r', 'e', 'm', '.', 'p', 'a', 's', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Asked whether the dog went back, the consultant answers yes."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "lilooy"), ("diagnostic", "projection"), ("environment", "negation"), ("projective", "yes"), ("person", "3")] }

def ex_34 : Datum :=
  { id := "deal2026_34"
    source := ⟨"deal-2026", "(34)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "Weet’u ’in-haama hi-tim’neenek-se-∅ yox̂ ke kimti ciq’aamqal hi-wahoo-tato."
    glossedTokens := [("Weet’u", "neg"), ("’in-haama", "1sg-husband.nom"), ("hi-tim’neenek-se-∅", "3subj-be.worried-imperf-pres"), ("yox̂", "rp.nom"), ("ke", "CĀ"), ("kimti", "new"), ("ciq’aamqal", "dog.nom"), ("hi-wahoo-tato", "3subj-howl-hab.pres")]
    glossedWords := [⟨[['W', 'e', 'e', 't', '’', 'u']], [['n', 'e', 'g']]⟩, ⟨[['’', 'i', 'n'], ['h', 'a', 'a', 'm', 'a']], [['1', 's', 'g'], ['h', 'u', 's', 'b', 'a', 'n', 'd', '.', 'n', 'o', 'm']]⟩, ⟨[['h', 'i'], ['t', 'i', 'm', '’', 'n', 'e', 'e', 'n', 'e', 'k'], ['s', 'e'], ['∅']], [['3', 's', 'u', 'b', 'j'], ['b', 'e', '.', 'w', 'o', 'r', 'r', 'i', 'e', 'd'], ['i', 'm', 'p', 'e', 'r', 'f'], ['p', 'r', 'e', 's']]⟩, ⟨[['y', 'o', 'x', '̂']], [['r', 'p', '.', 'n', 'o', 'm']]⟩, ⟨[['k', 'e']], [['C', 'Ā']]⟩, ⟨[['k', 'i', 'm', 't', 'i']], [['n', 'e', 'w']]⟩, ⟨[['c', 'i', 'q', '’', 'a', 'a', 'm', 'q', 'a', 'l']], [['d', 'o', 'g', '.', 'n', 'o', 'm']]⟩, ⟨[['h', 'i'], ['w', 'a', 'h', 'o', 'o'], ['t', 'a', 't', 'o']], [['3', 's', 'u', 'b', 'j'], ['h', 'o', 'w', 'l'], ['h', 'a', 'b', '.', 'p', 'r', 'e', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Asked whether the dog is a howler, the consultant answers that it is."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "tim’neeneki"), ("diagnostic", "projection"), ("environment", "negation"), ("projective", "yes"), ("person", "3")] }

def ex_35 : Datum :=
  { id := "deal2026_35"
    source := ⟨"deal-2026", "(35)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "Weet’u pro hi-neki-se-∅ watiisx hi-weeqi-yu’."
    glossedTokens := [("Weet’u", "neg"), ("pro", "3sg"), ("hi-neki-se-∅", "3subj-think-imperf-pres"), ("watiisx", "one.day.away"), ("hi-weeqi-yu’", "3subj-rain-prosp")]
    glossedWords := [⟨[['W', 'e', 'e', 't', '’', 'u']], [['n', 'e', 'g']]⟩, ⟨[['p', 'r', 'o']], [['3', 's', 'g']]⟩, ⟨[['h', 'i'], ['n', 'e', 'k', 'i'], ['s', 'e'], ['∅']], [['3', 's', 'u', 'b', 'j'], ['t', 'h', 'i', 'n', 'k'], ['i', 'm', 'p', 'e', 'r', 'f'], ['p', 'r', 'e', 's']]⟩, ⟨[['w', 'a', 't', 'i', 'i', 's', 'x']], [['o', 'n', 'e', '.', 'd', 'a', 'y', '.', 'a', 'w', 'a', 'y']]⟩, ⟨[['h', 'i'], ['w', 'e', 'e', 'q', 'i'], ['y', 'u', '’']], [['3', 's', 'u', 'b', 'j'], ['r', 'a', 'i', 'n'], ['p', 'r', 'o', 's', 'p']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Asked whether it was going to rain the next day, the consultant answers no."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "neki"), ("diagnostic", "projection"), ("environment", "negation"), ("projective", "no"), ("person", "3")] }

def ex_36 : Datum :=
  { id := "deal2026_36"
    source := ⟨"deal-2026", "(36)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "Weet Angel hi-neki-se-∅ hiteemenew’eet hi-pe-kuu-∅-ye Siminikem-x?"
    glossedTokens := [("Weet", "y.n"), ("Angel", "Angel.nom"), ("hi-neki-se-∅", "3subj-think-imperf-pres"), ("hiteemenew’eet", "student.nom"), ("hi-pe-kuu-∅-ye", "3subj-S.pl-go-p-rem.past"), ("Siminikem-x", "Lewiston-to")]
    glossedWords := [⟨[['W', 'e', 'e', 't']], [['y', '.', 'n']]⟩, ⟨[['A', 'n', 'g', 'e', 'l']], [['A', 'n', 'g', 'e', 'l', '.', 'n', 'o', 'm']]⟩, ⟨[['h', 'i'], ['n', 'e', 'k', 'i'], ['s', 'e'], ['∅']], [['3', 's', 'u', 'b', 'j'], ['t', 'h', 'i', 'n', 'k'], ['i', 'm', 'p', 'e', 'r', 'f'], ['p', 'r', 'e', 's']]⟩, ⟨[['h', 'i', 't', 'e', 'e', 'm', 'e', 'n', 'e', 'w', '’', 'e', 'e', 't']], [['s', 't', 'u', 'd', 'e', 'n', 't', '.', 'n', 'o', 'm']]⟩, ⟨[['h', 'i'], ['p', 'e'], ['k', 'u', 'u'], ['∅'], ['y', 'e']], [['3', 's', 'u', 'b', 'j'], ['S', '.', 'p', 'l'], ['g', 'o'], ['p'], ['r', 'e', 'm', '.', 'p', 'a', 's', 't']]⟩, ⟨[['S', 'i', 'm', 'i', 'n', 'i', 'k', 'e', 'm'], ['x']], [['L', 'e', 'w', 'i', 's', 't', 'o', 'n'], ['t', 'o']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Asked about the students, the consultant does not know whether they went."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "neki"), ("diagnostic", "projection"), ("environment", "question"), ("projective", "no"), ("person", "3")] }

def ex_68 : Datum :=
  { id := "deal2026_68"
    source := ⟨"deal-2026", "(68)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "C’alawi sepehiteemenew’eet hi-cuukwe-ce-∅ ’iin k’oomay-ca-∅, weet’u pro hi-cewcew-nuu-yu’-kum pro."
    glossedTokens := [("C’alawi", "if"), ("sepehiteemenew’eet", "teacher.nom"), ("hi-cuukwe-ce-∅", "3subj-know-imperf-pres"), ("’iin", "1sg.nom"), ("k’oomay-ca-∅", "be.sick-imperf-pres"), ("weet’u", "neg"), ("pro", "3sg"), ("hi-cewcew-nuu-yu’-kum", "3subj-call-appl-prosp-cis"), ("pro", "1sg")]
    glossedWords := [⟨[['C', '’', 'a', 'l', 'a', 'w', 'i']], [['i', 'f']]⟩, ⟨[['s', 'e', 'p', 'e', 'h', 'i', 't', 'e', 'e', 'm', 'e', 'n', 'e', 'w', '’', 'e', 'e', 't']], [['t', 'e', 'a', 'c', 'h', 'e', 'r', '.', 'n', 'o', 'm']]⟩, ⟨[['h', 'i'], ['c', 'u', 'u', 'k', 'w', 'e'], ['c', 'e'], ['∅']], [['3', 's', 'u', 'b', 'j'], ['k', 'n', 'o', 'w'], ['i', 'm', 'p', 'e', 'r', 'f'], ['p', 'r', 'e', 's']]⟩, ⟨[['’', 'i', 'i', 'n']], [['1', 's', 'g', '.', 'n', 'o', 'm']]⟩, ⟨[['k', '’', 'o', 'o', 'm', 'a', 'y'], ['c', 'a'], ['∅']], [['b', 'e', '.', 's', 'i', 'c', 'k'], ['i', 'm', 'p', 'e', 'r', 'f'], ['p', 'r', 'e', 's']]⟩, ⟨[['w', 'e', 'e', 't', '’', 'u']], [['n', 'e', 'g']]⟩, ⟨[['p', 'r', 'o']], [['3', 's', 'g']]⟩, ⟨[['h', 'i'], ['c', 'e', 'w', 'c', 'e', 'w'], ['n', 'u', 'u'], ['y', 'u', '’'], ['k', 'u', 'm']], [['3', 's', 'u', 'b', 'j'], ['c', 'a', 'l', 'l'], ['a', 'p', 'p', 'l'], ['p', 'r', 'o', 's', 'p'], ['c', 'i', 's']]⟩, ⟨[['p', 'r', 'o']], [['1', 's', 'g']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Asked whether that person was ill, the consultant answers that they would think so."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "cuukwe"), ("diagnostic", "projection"), ("environment", "conditional antecedent"), ("projective", "yes"), ("person", "3")] }

def all : List Datum := [ex_28a, ex_28b, ex_27b, ex_27d, ex_27e_eeys, ex_27e_qeese, ex_27e_timneeneki, ex_41a, ex_41b, ex_42a, ex_42b, ex_47a, ex_47b, ex_48a, ex_48b, ex_65b, ex_66a, ex_66b, ex_33, ex_34, ex_35, ex_36, ex_68]

end Deal2026.Examples
