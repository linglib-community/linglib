module

public import Linglib.Data.Examples.Schema

/-!
# `BakayEtAl2026` — typed example data

Auto-generated from `Linglib/Data/Examples/BakayEtAl2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BakayEtAl2026.Examples`.
-/

@[expose] public section

namespace BakayEtAl2026.Examples

def ex_5a_match : Datum :=
  { id := "bakayetal2026_5a_match"
    source := ⟨"bakay-etal-2026", "(5a), Distractor Match"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ayşe yönetmenlerin yeni kameramanlarının sertçe birbirlerini eleştirdiklerini anlattı."
    glossedTokens := [("Ayşe", "Ayşe"), ("yönetmen-ler-in", "director-PL-GEN"), ("yeni", "new"), ("kameraman-ların-ın", "cameraman-3PL.POSS-GEN"), ("sertçe", "severely"), ("birbirlerin-i", "each.other-ACC"), ("eleştir-dik-lerin-i", "criticize-NMLZ-3PL.POSS-ACC"), ("anlat-tı", "say-PST")]
    glossedWords := [⟨[['A', 'y', 'ş', 'e']], [['A', 'y', 'ş', 'e']]⟩, ⟨[['y', 'ö', 'n', 'e', 't', 'm', 'e', 'n'], ['l', 'e', 'r'], ['i', 'n']], [['d', 'i', 'r', 'e', 'c', 't', 'o', 'r'], ['P', 'L'], ['G', 'E', 'N']]⟩, ⟨[['y', 'e', 'n', 'i']], [['n', 'e', 'w']]⟩, ⟨[['k', 'a', 'm', 'e', 'r', 'a', 'm', 'a', 'n'], ['l', 'a', 'r', 'ı', 'n'], ['ı', 'n']], [['c', 'a', 'm', 'e', 'r', 'a', 'm', 'a', 'n'], ['3', 'P', 'L', '.', 'P', 'O', 'S', 'S'], ['G', 'E', 'N']]⟩, ⟨[['s', 'e', 'r', 't', 'ç', 'e']], [['s', 'e', 'v', 'e', 'r', 'e', 'l', 'y']]⟩, ⟨[['b', 'i', 'r', 'b', 'i', 'r', 'l', 'e', 'r', 'i', 'n'], ['i']], [['e', 'a', 'c', 'h', '.', 'o', 't', 'h', 'e', 'r'], ['A', 'C', 'C']]⟩, ⟨[['e', 'l', 'e', 'ş', 't', 'i', 'r'], ['d', 'i', 'k'], ['l', 'e', 'r', 'i', 'n'], ['i']], [['c', 'r', 'i', 't', 'i', 'c', 'i', 'z', 'e'], ['N', 'M', 'L', 'Z'], ['3', 'P', 'L', '.', 'P', 'O', 'S', 'S'], ['A', 'C', 'C']]⟩, ⟨[['a', 'n', 'l', 'a', 't'], ['t', 'ı']], [['s', 'a', 'y'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("matrix subject", .unacceptable), ("distractor", .unacceptable), ("embedded subject", .acceptable)]
    paperFeatures := [("experiment", "1"), ("condition", "Recent Target, Distractor Match"), ("target", "subject"), ("distractor", "possessor in subject"), ("distractorNumber", "plural")] }

def ex_5a_mismatch : Datum :=
  { id := "bakayetal2026_5a_mismatch"
    source := ⟨"bakay-etal-2026", "(5a), Distractor Mismatch"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ayşe yönetmenin yeni kameramanlarının sertçe birbirlerini eleştirdiklerini anlattı."
    glossedTokens := [("Ayşe", "Ayşe"), ("yönetmen-in", "director-GEN"), ("yeni", "new"), ("kameraman-ların-ın", "cameraman-3PL.POSS-GEN"), ("sertçe", "severely"), ("birbirlerin-i", "each.other-ACC"), ("eleştir-dik-lerin-i", "criticize-NMLZ-3PL.POSS-ACC"), ("anlat-tı", "say-PST")]
    glossedWords := [⟨[['A', 'y', 'ş', 'e']], [['A', 'y', 'ş', 'e']]⟩, ⟨[['y', 'ö', 'n', 'e', 't', 'm', 'e', 'n'], ['i', 'n']], [['d', 'i', 'r', 'e', 'c', 't', 'o', 'r'], ['G', 'E', 'N']]⟩, ⟨[['y', 'e', 'n', 'i']], [['n', 'e', 'w']]⟩, ⟨[['k', 'a', 'm', 'e', 'r', 'a', 'm', 'a', 'n'], ['l', 'a', 'r', 'ı', 'n'], ['ı', 'n']], [['c', 'a', 'm', 'e', 'r', 'a', 'm', 'a', 'n'], ['3', 'P', 'L', '.', 'P', 'O', 'S', 'S'], ['G', 'E', 'N']]⟩, ⟨[['s', 'e', 'r', 't', 'ç', 'e']], [['s', 'e', 'v', 'e', 'r', 'e', 'l', 'y']]⟩, ⟨[['b', 'i', 'r', 'b', 'i', 'r', 'l', 'e', 'r', 'i', 'n'], ['i']], [['e', 'a', 'c', 'h', '.', 'o', 't', 'h', 'e', 'r'], ['A', 'C', 'C']]⟩, ⟨[['e', 'l', 'e', 'ş', 't', 'i', 'r'], ['d', 'i', 'k'], ['l', 'e', 'r', 'i', 'n'], ['i']], [['c', 'r', 'i', 't', 'i', 'c', 'i', 'z', 'e'], ['N', 'M', 'L', 'Z'], ['3', 'P', 'L', '.', 'P', 'O', 'S', 'S'], ['A', 'C', 'C']]⟩, ⟨[['a', 'n', 'l', 'a', 't'], ['t', 'ı']], [['s', 'a', 'y'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("matrix subject", .unacceptable), ("distractor", .unacceptable), ("embedded subject", .acceptable)]
    paperFeatures := [("experiment", "1"), ("condition", "Recent Target, Distractor Mismatch"), ("target", "subject"), ("distractor", "possessor in subject"), ("distractorNumber", "singular")] }

def ex_5b_match : Datum :=
  { id := "bakayetal2026_5b_match"
    source := ⟨"bakay-etal-2026", "(5b), Distractor Match"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ayşe kameramanların yönetmenlerin izniyle sertçe birbirlerini eleştirdiklerini anlattı."
    glossedTokens := [("Ayşe", "Ayşe"), ("kameraman-lar-ın", "cameraman-PL-GEN"), ("yönetmen-ler-in", "director-PL-GEN"), ("izn-i-yle", "permission-3SG.POSS-COM"), ("sertçe", "severely"), ("birbirlerin-i", "each.other-ACC"), ("eleştir-dik-lerin-i", "criticize-NMLZ-3PL.POSS-ACC"), ("anlat-tı", "say-PST")]
    glossedWords := [⟨[['A', 'y', 'ş', 'e']], [['A', 'y', 'ş', 'e']]⟩, ⟨[['k', 'a', 'm', 'e', 'r', 'a', 'm', 'a', 'n'], ['l', 'a', 'r'], ['ı', 'n']], [['c', 'a', 'm', 'e', 'r', 'a', 'm', 'a', 'n'], ['P', 'L'], ['G', 'E', 'N']]⟩, ⟨[['y', 'ö', 'n', 'e', 't', 'm', 'e', 'n'], ['l', 'e', 'r'], ['i', 'n']], [['d', 'i', 'r', 'e', 'c', 't', 'o', 'r'], ['P', 'L'], ['G', 'E', 'N']]⟩, ⟨[['i', 'z', 'n'], ['i'], ['y', 'l', 'e']], [['p', 'e', 'r', 'm', 'i', 's', 's', 'i', 'o', 'n'], ['3', 'S', 'G', '.', 'P', 'O', 'S', 'S'], ['C', 'O', 'M']]⟩, ⟨[['s', 'e', 'r', 't', 'ç', 'e']], [['s', 'e', 'v', 'e', 'r', 'e', 'l', 'y']]⟩, ⟨[['b', 'i', 'r', 'b', 'i', 'r', 'l', 'e', 'r', 'i', 'n'], ['i']], [['e', 'a', 'c', 'h', '.', 'o', 't', 'h', 'e', 'r'], ['A', 'C', 'C']]⟩, ⟨[['e', 'l', 'e', 'ş', 't', 'i', 'r'], ['d', 'i', 'k'], ['l', 'e', 'r', 'i', 'n'], ['i']], [['c', 'r', 'i', 't', 'i', 'c', 'i', 'z', 'e'], ['N', 'M', 'L', 'Z'], ['3', 'P', 'L', '.', 'P', 'O', 'S', 'S'], ['A', 'C', 'C']]⟩, ⟨[['a', 'n', 'l', 'a', 't'], ['t', 'ı']], [['s', 'a', 'y'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("matrix subject", .unacceptable), ("embedded subject", .acceptable), ("distractor", .unacceptable)]
    paperFeatures := [("experiment", "1"), ("condition", "Distant Target, Distractor Match"), ("target", "subject"), ("distractor", "possessor in adjunct"), ("distractorNumber", "plural")] }

def ex_5b_mismatch : Datum :=
  { id := "bakayetal2026_5b_mismatch"
    source := ⟨"bakay-etal-2026", "(5b), Distractor Mismatch"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ayşe kameramanların yönetmenin izniyle sertçe birbirlerini eleştirdiklerini anlattı."
    glossedTokens := [("Ayşe", "Ayşe"), ("kameraman-lar-ın", "cameraman-PL-GEN"), ("yönetmen-in", "director-GEN"), ("izn-i-yle", "permission-3SG.POSS-COM"), ("sertçe", "severely"), ("birbirlerin-i", "each.other-ACC"), ("eleştir-dik-lerin-i", "criticize-NMLZ-3PL.POSS-ACC"), ("anlat-tı", "say-PST")]
    glossedWords := [⟨[['A', 'y', 'ş', 'e']], [['A', 'y', 'ş', 'e']]⟩, ⟨[['k', 'a', 'm', 'e', 'r', 'a', 'm', 'a', 'n'], ['l', 'a', 'r'], ['ı', 'n']], [['c', 'a', 'm', 'e', 'r', 'a', 'm', 'a', 'n'], ['P', 'L'], ['G', 'E', 'N']]⟩, ⟨[['y', 'ö', 'n', 'e', 't', 'm', 'e', 'n'], ['i', 'n']], [['d', 'i', 'r', 'e', 'c', 't', 'o', 'r'], ['G', 'E', 'N']]⟩, ⟨[['i', 'z', 'n'], ['i'], ['y', 'l', 'e']], [['p', 'e', 'r', 'm', 'i', 's', 's', 'i', 'o', 'n'], ['3', 'S', 'G', '.', 'P', 'O', 'S', 'S'], ['C', 'O', 'M']]⟩, ⟨[['s', 'e', 'r', 't', 'ç', 'e']], [['s', 'e', 'v', 'e', 'r', 'e', 'l', 'y']]⟩, ⟨[['b', 'i', 'r', 'b', 'i', 'r', 'l', 'e', 'r', 'i', 'n'], ['i']], [['e', 'a', 'c', 'h', '.', 'o', 't', 'h', 'e', 'r'], ['A', 'C', 'C']]⟩, ⟨[['e', 'l', 'e', 'ş', 't', 'i', 'r'], ['d', 'i', 'k'], ['l', 'e', 'r', 'i', 'n'], ['i']], [['c', 'r', 'i', 't', 'i', 'c', 'i', 'z', 'e'], ['N', 'M', 'L', 'Z'], ['3', 'P', 'L', '.', 'P', 'O', 'S', 'S'], ['A', 'C', 'C']]⟩, ⟨[['a', 'n', 'l', 'a', 't'], ['t', 'ı']], [['s', 'a', 'y'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("matrix subject", .unacceptable), ("embedded subject", .acceptable), ("distractor", .unacceptable)]
    paperFeatures := [("experiment", "1"), ("condition", "Distant Target, Distractor Mismatch"), ("target", "subject"), ("distractor", "possessor in adjunct"), ("distractorNumber", "singular")] }

def ex_8a_match : Datum :=
  { id := "bakayetal2026_8a_match"
    source := ⟨"bakay-etal-2026", "(8a), IO Match"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ayşe kameramanların yönetmenlere açıkça birbirlerini sorduğunu anladı."
    glossedTokens := [("Ayşe", "Ayşe"), ("kameraman-lar-ın", "cameraman-PL-GEN"), ("yönetmen-ler-e", "director-PL-DAT"), ("açıkça", "openly"), ("birbirlerin-i", "each.other-ACC"), ("sor-duğ-un-u", "ask-NMLZ-3SG.POSS-ACC"), ("anla-dı", "notice-PST")]
    glossedWords := [⟨[['A', 'y', 'ş', 'e']], [['A', 'y', 'ş', 'e']]⟩, ⟨[['k', 'a', 'm', 'e', 'r', 'a', 'm', 'a', 'n'], ['l', 'a', 'r'], ['ı', 'n']], [['c', 'a', 'm', 'e', 'r', 'a', 'm', 'a', 'n'], ['P', 'L'], ['G', 'E', 'N']]⟩, ⟨[['y', 'ö', 'n', 'e', 't', 'm', 'e', 'n'], ['l', 'e', 'r'], ['e']], [['d', 'i', 'r', 'e', 'c', 't', 'o', 'r'], ['P', 'L'], ['D', 'A', 'T']]⟩, ⟨[['a', 'ç', 'ı', 'k', 'ç', 'a']], [['o', 'p', 'e', 'n', 'l', 'y']]⟩, ⟨[['b', 'i', 'r', 'b', 'i', 'r', 'l', 'e', 'r', 'i', 'n'], ['i']], [['e', 'a', 'c', 'h', '.', 'o', 't', 'h', 'e', 'r'], ['A', 'C', 'C']]⟩, ⟨[['s', 'o', 'r'], ['d', 'u', 'ğ'], ['u', 'n'], ['u']], [['a', 's', 'k'], ['N', 'M', 'L', 'Z'], ['3', 'S', 'G', '.', 'P', 'O', 'S', 'S'], ['A', 'C', 'C']]⟩, ⟨[['a', 'n', 'l', 'a'], ['d', 'ı']], [['n', 'o', 't', 'i', 'c', 'e'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("matrix subject", .unacceptable), ("embedded subject", .acceptable), ("indirect object", .acceptable)]
    paperFeatures := [("experiment", "2"), ("condition", "Plural Subject, IO Match"), ("target", "subject"), ("second", "indirect object"), ("secondNumber", "plural")] }

def ex_8a_mismatch : Datum :=
  { id := "bakayetal2026_8a_mismatch"
    source := ⟨"bakay-etal-2026", "(8a), IO Mismatch"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ayşe kameramanların yönetmene açıkça birbirlerini sorduğunu anladı."
    glossedTokens := [("Ayşe", "Ayşe"), ("kameraman-lar-ın", "cameraman-PL-GEN"), ("yönetmen-e", "director-DAT"), ("açıkça", "openly"), ("birbirlerin-i", "each.other-ACC"), ("sor-duğ-un-u", "ask-NMLZ-3SG.POSS-ACC"), ("anla-dı", "notice-PST")]
    glossedWords := [⟨[['A', 'y', 'ş', 'e']], [['A', 'y', 'ş', 'e']]⟩, ⟨[['k', 'a', 'm', 'e', 'r', 'a', 'm', 'a', 'n'], ['l', 'a', 'r'], ['ı', 'n']], [['c', 'a', 'm', 'e', 'r', 'a', 'm', 'a', 'n'], ['P', 'L'], ['G', 'E', 'N']]⟩, ⟨[['y', 'ö', 'n', 'e', 't', 'm', 'e', 'n'], ['e']], [['d', 'i', 'r', 'e', 'c', 't', 'o', 'r'], ['D', 'A', 'T']]⟩, ⟨[['a', 'ç', 'ı', 'k', 'ç', 'a']], [['o', 'p', 'e', 'n', 'l', 'y']]⟩, ⟨[['b', 'i', 'r', 'b', 'i', 'r', 'l', 'e', 'r', 'i', 'n'], ['i']], [['e', 'a', 'c', 'h', '.', 'o', 't', 'h', 'e', 'r'], ['A', 'C', 'C']]⟩, ⟨[['s', 'o', 'r'], ['d', 'u', 'ğ'], ['u', 'n'], ['u']], [['a', 's', 'k'], ['N', 'M', 'L', 'Z'], ['3', 'S', 'G', '.', 'P', 'O', 'S', 'S'], ['A', 'C', 'C']]⟩, ⟨[['a', 'n', 'l', 'a'], ['d', 'ı']], [['n', 'o', 't', 'i', 'c', 'e'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("matrix subject", .unacceptable), ("embedded subject", .acceptable), ("indirect object", .acceptable)]
    paperFeatures := [("experiment", "2"), ("condition", "Plural Subject, IO Mismatch"), ("target", "subject"), ("second", "indirect object"), ("secondNumber", "singular")] }

def ex_8b_match : Datum :=
  { id := "bakayetal2026_8b_match"
    source := ⟨"bakay-etal-2026", "(8b), Distractor Match"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ayşe kameramanların yönetmenlere göre açıkça birbirlerini sorduğunu anladı."
    glossedTokens := [("Ayşe", "Ayşe"), ("kameraman-lar-ın", "cameraman-PL-GEN"), ("yönetmen-ler-e", "director-PL-DAT"), ("göre", "according.to"), ("açıkça", "openly"), ("birbirlerin-i", "each.other-ACC"), ("sor-duğ-un-u", "ask-NMLZ-3SG.POSS-ACC"), ("anla-dı", "notice-PST")]
    glossedWords := [⟨[['A', 'y', 'ş', 'e']], [['A', 'y', 'ş', 'e']]⟩, ⟨[['k', 'a', 'm', 'e', 'r', 'a', 'm', 'a', 'n'], ['l', 'a', 'r'], ['ı', 'n']], [['c', 'a', 'm', 'e', 'r', 'a', 'm', 'a', 'n'], ['P', 'L'], ['G', 'E', 'N']]⟩, ⟨[['y', 'ö', 'n', 'e', 't', 'm', 'e', 'n'], ['l', 'e', 'r'], ['e']], [['d', 'i', 'r', 'e', 'c', 't', 'o', 'r'], ['P', 'L'], ['D', 'A', 'T']]⟩, ⟨[['g', 'ö', 'r', 'e']], [['a', 'c', 'c', 'o', 'r', 'd', 'i', 'n', 'g', '.', 't', 'o']]⟩, ⟨[['a', 'ç', 'ı', 'k', 'ç', 'a']], [['o', 'p', 'e', 'n', 'l', 'y']]⟩, ⟨[['b', 'i', 'r', 'b', 'i', 'r', 'l', 'e', 'r', 'i', 'n'], ['i']], [['e', 'a', 'c', 'h', '.', 'o', 't', 'h', 'e', 'r'], ['A', 'C', 'C']]⟩, ⟨[['s', 'o', 'r'], ['d', 'u', 'ğ'], ['u', 'n'], ['u']], [['a', 's', 'k'], ['N', 'M', 'L', 'Z'], ['3', 'S', 'G', '.', 'P', 'O', 'S', 'S'], ['A', 'C', 'C']]⟩, ⟨[['a', 'n', 'l', 'a'], ['d', 'ı']], [['n', 'o', 't', 'i', 'c', 'e'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("matrix subject", .unacceptable), ("embedded subject", .acceptable), ("distractor", .unacceptable)]
    paperFeatures := [("experiment", "2"), ("condition", "Plural Subject, Distractor Match"), ("target", "subject"), ("distractor", "postpositional adjunct"), ("distractorNumber", "plural")] }

def ex_8b_mismatch : Datum :=
  { id := "bakayetal2026_8b_mismatch"
    source := ⟨"bakay-etal-2026", "(8b), Distractor Mismatch"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ayşe kameramanların yönetmene göre açıkça birbirlerini sorduğunu anladı."
    glossedTokens := [("Ayşe", "Ayşe"), ("kameraman-lar-ın", "cameraman-PL-GEN"), ("yönetmen-e", "director-DAT"), ("göre", "according.to"), ("açıkça", "openly"), ("birbirlerin-i", "each.other-ACC"), ("sor-duğ-un-u", "ask-NMLZ-3SG.POSS-ACC"), ("anla-dı", "notice-PST")]
    glossedWords := [⟨[['A', 'y', 'ş', 'e']], [['A', 'y', 'ş', 'e']]⟩, ⟨[['k', 'a', 'm', 'e', 'r', 'a', 'm', 'a', 'n'], ['l', 'a', 'r'], ['ı', 'n']], [['c', 'a', 'm', 'e', 'r', 'a', 'm', 'a', 'n'], ['P', 'L'], ['G', 'E', 'N']]⟩, ⟨[['y', 'ö', 'n', 'e', 't', 'm', 'e', 'n'], ['e']], [['d', 'i', 'r', 'e', 'c', 't', 'o', 'r'], ['D', 'A', 'T']]⟩, ⟨[['g', 'ö', 'r', 'e']], [['a', 'c', 'c', 'o', 'r', 'd', 'i', 'n', 'g', '.', 't', 'o']]⟩, ⟨[['a', 'ç', 'ı', 'k', 'ç', 'a']], [['o', 'p', 'e', 'n', 'l', 'y']]⟩, ⟨[['b', 'i', 'r', 'b', 'i', 'r', 'l', 'e', 'r', 'i', 'n'], ['i']], [['e', 'a', 'c', 'h', '.', 'o', 't', 'h', 'e', 'r'], ['A', 'C', 'C']]⟩, ⟨[['s', 'o', 'r'], ['d', 'u', 'ğ'], ['u', 'n'], ['u']], [['a', 's', 'k'], ['N', 'M', 'L', 'Z'], ['3', 'S', 'G', '.', 'P', 'O', 'S', 'S'], ['A', 'C', 'C']]⟩, ⟨[['a', 'n', 'l', 'a'], ['d', 'ı']], [['n', 'o', 't', 'i', 'c', 'e'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("matrix subject", .unacceptable), ("embedded subject", .acceptable), ("distractor", .unacceptable)]
    paperFeatures := [("experiment", "2"), ("condition", "Plural Subject, Distractor Mismatch"), ("target", "subject"), ("distractor", "postpositional adjunct"), ("distractorNumber", "singular")] }

def ex_8c : Datum :=
  { id := "bakayetal2026_8c"
    source := ⟨"bakay-etal-2026", "(8c), Singular Subject, IO Match"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ayşe kameramanın yönetmenlere açıkça birbirlerini sorduğunu anladı."
    glossedTokens := [("Ayşe", "Ayşe"), ("kameraman-ın", "cameraman-GEN"), ("yönetmen-ler-e", "director-PL-DAT"), ("açıkça", "openly"), ("birbirlerin-i", "each.other-ACC"), ("sor-duğ-un-u", "ask-NMLZ-3SG.POSS-ACC"), ("anla-dı", "notice-PST")]
    glossedWords := [⟨[['A', 'y', 'ş', 'e']], [['A', 'y', 'ş', 'e']]⟩, ⟨[['k', 'a', 'm', 'e', 'r', 'a', 'm', 'a', 'n'], ['ı', 'n']], [['c', 'a', 'm', 'e', 'r', 'a', 'm', 'a', 'n'], ['G', 'E', 'N']]⟩, ⟨[['y', 'ö', 'n', 'e', 't', 'm', 'e', 'n'], ['l', 'e', 'r'], ['e']], [['d', 'i', 'r', 'e', 'c', 't', 'o', 'r'], ['P', 'L'], ['D', 'A', 'T']]⟩, ⟨[['a', 'ç', 'ı', 'k', 'ç', 'a']], [['o', 'p', 'e', 'n', 'l', 'y']]⟩, ⟨[['b', 'i', 'r', 'b', 'i', 'r', 'l', 'e', 'r', 'i', 'n'], ['i']], [['e', 'a', 'c', 'h', '.', 'o', 't', 'h', 'e', 'r'], ['A', 'C', 'C']]⟩, ⟨[['s', 'o', 'r'], ['d', 'u', 'ğ'], ['u', 'n'], ['u']], [['a', 's', 'k'], ['N', 'M', 'L', 'Z'], ['3', 'S', 'G', '.', 'P', 'O', 'S', 'S'], ['A', 'C', 'C']]⟩, ⟨[['a', 'n', 'l', 'a'], ['d', 'ı']], [['n', 'o', 't', 'i', 'c', 'e'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("matrix subject", .unacceptable), ("embedded subject", .acceptable), ("indirect object", .acceptable)]
    paperFeatures := [("experiment", "2"), ("condition", "Singular Subject, IO Match"), ("target", "subject"), ("targetNumber", "singular"), ("second", "indirect object"), ("secondNumber", "plural")] }

def ex_10a : Datum :=
  { id := "bakayetal2026_10a"
    source := ⟨"bakay-etal-2026", "(10a), IO, Dative"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ayşe aşçıların garsonlara sebepsizce birbirlerini kötülediklerini biliyor."
    glossedTokens := [("Ayşe", "Ayşe"), ("aşçı-lar-ın", "chef-PL-GEN"), ("garson-lar-a", "waiter-PL-DAT"), ("sebepsizce", "without.reason"), ("birbirlerin-i", "each.other-ACC"), ("kötüle-dik-lerin-i", "badmouth-NMLZ-3PL.POSS-ACC"), ("bil-iyor", "know-PROG")]
    glossedWords := [⟨[['A', 'y', 'ş', 'e']], [['A', 'y', 'ş', 'e']]⟩, ⟨[['a', 'ş', 'ç', 'ı'], ['l', 'a', 'r'], ['ı', 'n']], [['c', 'h', 'e', 'f'], ['P', 'L'], ['G', 'E', 'N']]⟩, ⟨[['g', 'a', 'r', 's', 'o', 'n'], ['l', 'a', 'r'], ['a']], [['w', 'a', 'i', 't', 'e', 'r'], ['P', 'L'], ['D', 'A', 'T']]⟩, ⟨[['s', 'e', 'b', 'e', 'p', 's', 'i', 'z', 'c', 'e']], [['w', 'i', 't', 'h', 'o', 'u', 't', '.', 'r', 'e', 'a', 's', 'o', 'n']]⟩, ⟨[['b', 'i', 'r', 'b', 'i', 'r', 'l', 'e', 'r', 'i', 'n'], ['i']], [['e', 'a', 'c', 'h', '.', 'o', 't', 'h', 'e', 'r'], ['A', 'C', 'C']]⟩, ⟨[['k', 'ö', 't', 'ü', 'l', 'e'], ['d', 'i', 'k'], ['l', 'e', 'r', 'i', 'n'], ['i']], [['b', 'a', 'd', 'm', 'o', 'u', 't', 'h'], ['N', 'M', 'L', 'Z'], ['3', 'P', 'L', '.', 'P', 'O', 'S', 'S'], ['A', 'C', 'C']]⟩, ⟨[['b', 'i', 'l'], ['i', 'y', 'o', 'r']], [['k', 'n', 'o', 'w'], ['P', 'R', 'O', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("matrix subject", .unacceptable), ("embedded subject", .acceptable), ("indirect object", .acceptable)]
    paperFeatures := [("experiment", "3"), ("condition", "IO, Dative"), ("target", "subject"), ("second", "indirect object"), ("secondNumber", "plural")] }

def ex_10b : Datum :=
  { id := "bakayetal2026_10b"
    source := ⟨"bakay-etal-2026", "(10b), Distractor, Dative"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ayşe aşçıların garsonlara rağmen sebepsizce birbirlerini kötülediklerini biliyor."
    glossedTokens := [("Ayşe", "Ayşe"), ("aşçı-lar-ın", "chef-PL-GEN"), ("garson-lar-a", "waiter-PL-DAT"), ("rağmen", "despite"), ("sebepsizce", "without.reason"), ("birbirlerin-i", "each.other-ACC"), ("kötüle-dik-lerin-i", "badmouth-NMLZ-3PL.POSS-ACC"), ("bil-iyor", "know-PROG")]
    glossedWords := [⟨[['A', 'y', 'ş', 'e']], [['A', 'y', 'ş', 'e']]⟩, ⟨[['a', 'ş', 'ç', 'ı'], ['l', 'a', 'r'], ['ı', 'n']], [['c', 'h', 'e', 'f'], ['P', 'L'], ['G', 'E', 'N']]⟩, ⟨[['g', 'a', 'r', 's', 'o', 'n'], ['l', 'a', 'r'], ['a']], [['w', 'a', 'i', 't', 'e', 'r'], ['P', 'L'], ['D', 'A', 'T']]⟩, ⟨[['r', 'a', 'ğ', 'm', 'e', 'n']], [['d', 'e', 's', 'p', 'i', 't', 'e']]⟩, ⟨[['s', 'e', 'b', 'e', 'p', 's', 'i', 'z', 'c', 'e']], [['w', 'i', 't', 'h', 'o', 'u', 't', '.', 'r', 'e', 'a', 's', 'o', 'n']]⟩, ⟨[['b', 'i', 'r', 'b', 'i', 'r', 'l', 'e', 'r', 'i', 'n'], ['i']], [['e', 'a', 'c', 'h', '.', 'o', 't', 'h', 'e', 'r'], ['A', 'C', 'C']]⟩, ⟨[['k', 'ö', 't', 'ü', 'l', 'e'], ['d', 'i', 'k'], ['l', 'e', 'r', 'i', 'n'], ['i']], [['b', 'a', 'd', 'm', 'o', 'u', 't', 'h'], ['N', 'M', 'L', 'Z'], ['3', 'P', 'L', '.', 'P', 'O', 'S', 'S'], ['A', 'C', 'C']]⟩, ⟨[['b', 'i', 'l'], ['i', 'y', 'o', 'r']], [['k', 'n', 'o', 'w'], ['P', 'R', 'O', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("matrix subject", .unacceptable), ("embedded subject", .acceptable), ("distractor", .unacceptable)]
    paperFeatures := [("experiment", "3"), ("condition", "Distractor, Dative"), ("target", "subject"), ("distractor", "postpositional adjunct"), ("distractorNumber", "plural")] }

def ex_10c : Datum :=
  { id := "bakayetal2026_10c"
    source := ⟨"bakay-etal-2026", "(10c), Distractor, Genitive"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ayşe aşçıların garsonların etkisiyle sebepsizce birbirlerini kötülediklerini biliyor."
    glossedTokens := [("Ayşe", "Ayşe"), ("aşçı-lar-ın", "chef-PL-GEN"), ("garson-lar-ın", "waiter-PL-GEN"), ("etki-si-yle", "influence-3SG.POSS-COM"), ("sebepsizce", "without.reason"), ("birbirlerin-i", "each.other-ACC"), ("kötüle-dik-lerin-i", "badmouth-NMLZ-3PL.POSS-ACC"), ("bil-iyor", "know-PROG")]
    glossedWords := [⟨[['A', 'y', 'ş', 'e']], [['A', 'y', 'ş', 'e']]⟩, ⟨[['a', 'ş', 'ç', 'ı'], ['l', 'a', 'r'], ['ı', 'n']], [['c', 'h', 'e', 'f'], ['P', 'L'], ['G', 'E', 'N']]⟩, ⟨[['g', 'a', 'r', 's', 'o', 'n'], ['l', 'a', 'r'], ['ı', 'n']], [['w', 'a', 'i', 't', 'e', 'r'], ['P', 'L'], ['G', 'E', 'N']]⟩, ⟨[['e', 't', 'k', 'i'], ['s', 'i'], ['y', 'l', 'e']], [['i', 'n', 'f', 'l', 'u', 'e', 'n', 'c', 'e'], ['3', 'S', 'G', '.', 'P', 'O', 'S', 'S'], ['C', 'O', 'M']]⟩, ⟨[['s', 'e', 'b', 'e', 'p', 's', 'i', 'z', 'c', 'e']], [['w', 'i', 't', 'h', 'o', 'u', 't', '.', 'r', 'e', 'a', 's', 'o', 'n']]⟩, ⟨[['b', 'i', 'r', 'b', 'i', 'r', 'l', 'e', 'r', 'i', 'n'], ['i']], [['e', 'a', 'c', 'h', '.', 'o', 't', 'h', 'e', 'r'], ['A', 'C', 'C']]⟩, ⟨[['k', 'ö', 't', 'ü', 'l', 'e'], ['d', 'i', 'k'], ['l', 'e', 'r', 'i', 'n'], ['i']], [['b', 'a', 'd', 'm', 'o', 'u', 't', 'h'], ['N', 'M', 'L', 'Z'], ['3', 'P', 'L', '.', 'P', 'O', 'S', 'S'], ['A', 'C', 'C']]⟩, ⟨[['b', 'i', 'l'], ['i', 'y', 'o', 'r']], [['k', 'n', 'o', 'w'], ['P', 'R', 'O', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("matrix subject", .unacceptable), ("embedded subject", .acceptable), ("distractor", .unacceptable)]
    paperFeatures := [("experiment", "3"), ("condition", "Distractor, Genitive"), ("target", "subject"), ("distractor", "possessor in adjunct"), ("distractorNumber", "plural")] }

def all : List Datum := [ex_5a_match, ex_5a_mismatch, ex_5b_match, ex_5b_mismatch, ex_8a_match, ex_8a_mismatch, ex_8b_match, ex_8b_mismatch, ex_8c, ex_10a, ex_10b, ex_10c]

end BakayEtAl2026.Examples
