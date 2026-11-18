module

public import Linglib.Data.Examples.Schema

/-!
# `Ostrove2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Ostrove2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Ostrove2026.Examples`.
-/

@[expose] public section

namespace Ostrove2026.Examples

def ex_9a_completive : Datum :=
  { id := "ostrove2026_9a_completive"
    source := ⟨"ostrove-2026", "(9a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ká'án =ì xìin Ana iin be'e"
    glossedTokens := [("Ká'án", "think:CONT"), ("=ì", "=I"), ("xìin", "buy:COMP"), ("Ana", "Ana"), ("iin", "one"), ("be'e", "house")]
    glossedWords := [⟨['K', 'á', '\'', 'á', 'n'], ['t', 'h', 'i', 'n', 'k', ':', 'C', 'O', 'N', 'T'], [⟨['K', 'á', '\'', 'á', 'n'], ['t', 'h', 'i', 'n', 'k', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['=', 'ì'], ['=', 'I'], [⟨['ì'], ['I'], some '='⟩]⟩, ⟨['x', 'ì', 'i', 'n'], ['b', 'u', 'y', ':', 'C', 'O', 'M', 'P'], [⟨['x', 'ì', 'i', 'n'], ['b', 'u', 'y', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['A', 'n', 'a'], ['A', 'n', 'a'], [⟨['A', 'n', 'a'], ['A', 'n', 'a'], none⟩]⟩, ⟨['i', 'i', 'n'], ['o', 'n', 'e'], [⟨['i', 'i', 'n'], ['o', 'n', 'e'], none⟩]⟩, ⟨['b', 'e', '\'', 'e'], ['h', 'o', 'u', 's', 'e'], [⟨['b', 'e', '\'', 'e'], ['h', 'o', 'u', 's', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ka'án"), ("clauseType", "finite"), ("diagnostic", "aspect"), ("aspect", "completive")] }

def ex_9a_continuous : Datum :=
  { id := "ostrove2026_9a_continuous"
    source := ⟨"ostrove-2026", "(9a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ká'án =ì xíin Ana iin be'e"
    glossedTokens := [("Ká'án", "think:CONT"), ("=ì", "=I"), ("xíin", "buy:CONT"), ("Ana", "Ana"), ("iin", "one"), ("be'e", "house")]
    glossedWords := [⟨['K', 'á', '\'', 'á', 'n'], ['t', 'h', 'i', 'n', 'k', ':', 'C', 'O', 'N', 'T'], [⟨['K', 'á', '\'', 'á', 'n'], ['t', 'h', 'i', 'n', 'k', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['=', 'ì'], ['=', 'I'], [⟨['ì'], ['I'], some '='⟩]⟩, ⟨['x', 'í', 'i', 'n'], ['b', 'u', 'y', ':', 'C', 'O', 'N', 'T'], [⟨['x', 'í', 'i', 'n'], ['b', 'u', 'y', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['A', 'n', 'a'], ['A', 'n', 'a'], [⟨['A', 'n', 'a'], ['A', 'n', 'a'], none⟩]⟩, ⟨['i', 'i', 'n'], ['o', 'n', 'e'], [⟨['i', 'i', 'n'], ['o', 'n', 'e'], none⟩]⟩, ⟨['b', 'e', '\'', 'e'], ['h', 'o', 'u', 's', 'e'], [⟨['b', 'e', '\'', 'e'], ['h', 'o', 'u', 's', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ka'án"), ("clauseType", "finite"), ("diagnostic", "aspect"), ("aspect", "continuous")] }

def ex_9a_irrealis : Datum :=
  { id := "ostrove2026_9a_irrealis"
    source := ⟨"ostrove-2026", "(9a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ká'án =ì kwiin Ana iin be'e"
    glossedTokens := [("Ká'án", "think:CONT"), ("=ì", "=I"), ("kwiin", "buy:IRR"), ("Ana", "Ana"), ("iin", "one"), ("be'e", "house")]
    glossedWords := [⟨['K', 'á', '\'', 'á', 'n'], ['t', 'h', 'i', 'n', 'k', ':', 'C', 'O', 'N', 'T'], [⟨['K', 'á', '\'', 'á', 'n'], ['t', 'h', 'i', 'n', 'k', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['=', 'ì'], ['=', 'I'], [⟨['ì'], ['I'], some '='⟩]⟩, ⟨['k', 'w', 'i', 'i', 'n'], ['b', 'u', 'y', ':', 'I', 'R', 'R'], [⟨['k', 'w', 'i', 'i', 'n'], ['b', 'u', 'y', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['A', 'n', 'a'], ['A', 'n', 'a'], [⟨['A', 'n', 'a'], ['A', 'n', 'a'], none⟩]⟩, ⟨['i', 'i', 'n'], ['o', 'n', 'e'], [⟨['i', 'i', 'n'], ['o', 'n', 'e'], none⟩]⟩, ⟨['b', 'e', '\'', 'e'], ['h', 'o', 'u', 's', 'e'], [⟨['b', 'e', '\'', 'e'], ['h', 'o', 'u', 's', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ka'án"), ("clauseType", "finite"), ("diagnostic", "aspect"), ("aspect", "irrealis")] }

def ex_9b_completive : Datum :=
  { id := "ostrove2026_9b_completive"
    source := ⟨"ostrove-2026", "(9b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Nì- kà'àn Maria kìxi kwé'e =ñá"
    glossedTokens := [("Nì-", "COMP-"), ("kà'àn", "say"), ("Maria", "Maria"), ("kìxi", "sleep:COMP"), ("kwé'e", "much"), ("=ñá", "=she")]
    glossedWords := [⟨['N', 'ì', '-'], ['C', 'O', 'M', 'P', '-'], [⟨['N', 'ì'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['k', 'à', '\'', 'à', 'n'], ['s', 'a', 'y'], [⟨['k', 'à', '\'', 'à', 'n'], ['s', 'a', 'y'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['k', 'ì', 'x', 'i'], ['s', 'l', 'e', 'e', 'p', ':', 'C', 'O', 'M', 'P'], [⟨['k', 'ì', 'x', 'i'], ['s', 'l', 'e', 'e', 'p', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['k', 'w', 'é', '\'', 'e'], ['m', 'u', 'c', 'h'], [⟨['k', 'w', 'é', '\'', 'e'], ['m', 'u', 'c', 'h'], none⟩]⟩, ⟨['=', 'ñ', 'á'], ['=', 's', 'h', 'e'], [⟨['ñ', 'á'], ['s', 'h', 'e'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "kà'àn"), ("clauseType", "finite"), ("diagnostic", "aspect"), ("aspect", "completive")] }

def ex_9b_continuous : Datum :=
  { id := "ostrove2026_9b_continuous"
    source := ⟨"ostrove-2026", "(9b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Nì- kà'àn Maria kíxi kwé'e =ñá"
    glossedTokens := [("Nì-", "COMP-"), ("kà'àn", "say"), ("Maria", "Maria"), ("kíxi", "sleep:CONT"), ("kwé'e", "much"), ("=ñá", "=she")]
    glossedWords := [⟨['N', 'ì', '-'], ['C', 'O', 'M', 'P', '-'], [⟨['N', 'ì'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['k', 'à', '\'', 'à', 'n'], ['s', 'a', 'y'], [⟨['k', 'à', '\'', 'à', 'n'], ['s', 'a', 'y'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['k', 'í', 'x', 'i'], ['s', 'l', 'e', 'e', 'p', ':', 'C', 'O', 'N', 'T'], [⟨['k', 'í', 'x', 'i'], ['s', 'l', 'e', 'e', 'p', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['k', 'w', 'é', '\'', 'e'], ['m', 'u', 'c', 'h'], [⟨['k', 'w', 'é', '\'', 'e'], ['m', 'u', 'c', 'h'], none⟩]⟩, ⟨['=', 'ñ', 'á'], ['=', 's', 'h', 'e'], [⟨['ñ', 'á'], ['s', 'h', 'e'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "kà'àn"), ("clauseType", "finite"), ("diagnostic", "aspect"), ("aspect", "continuous")] }

def ex_9b_irrealis : Datum :=
  { id := "ostrove2026_9b_irrealis"
    source := ⟨"ostrove-2026", "(9b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Nì- kà'àn Maria kusi kwé'e =ñá"
    glossedTokens := [("Nì-", "COMP-"), ("kà'àn", "say"), ("Maria", "Maria"), ("kusi", "sleep:IRR"), ("kwé'e", "much"), ("=ñá", "=she")]
    glossedWords := [⟨['N', 'ì', '-'], ['C', 'O', 'M', 'P', '-'], [⟨['N', 'ì'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['k', 'à', '\'', 'à', 'n'], ['s', 'a', 'y'], [⟨['k', 'à', '\'', 'à', 'n'], ['s', 'a', 'y'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['k', 'u', 's', 'i'], ['s', 'l', 'e', 'e', 'p', ':', 'I', 'R', 'R'], [⟨['k', 'u', 's', 'i'], ['s', 'l', 'e', 'e', 'p', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['k', 'w', 'é', '\'', 'e'], ['m', 'u', 'c', 'h'], [⟨['k', 'w', 'é', '\'', 'e'], ['m', 'u', 'c', 'h'], none⟩]⟩, ⟨['=', 'ñ', 'á'], ['=', 's', 'h', 'e'], [⟨['ñ', 'á'], ['s', 'h', 'e'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "kà'àn"), ("clauseType", "finite"), ("diagnostic", "aspect"), ("aspect", "irrealis")] }

def ex_9c_completive : Datum :=
  { id := "ostrove2026_9c_completive"
    source := ⟨"ostrove-2026", "(9c)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kùsijǐ ini =rà nì- nì'ǐ =rà ña'á"
    glossedTokens := [("Kùsijǐ", "be.happy:COMP"), ("ini", "in"), ("=rà", "=he"), ("nì-", "COMP-"), ("nì'ǐ", "get"), ("=rà", "=he"), ("ña'á", "thing")]
    glossedWords := [⟨['K', 'ù', 's', 'i', 'j', 'ǐ'], ['b', 'e', '.', 'h', 'a', 'p', 'p', 'y', ':', 'C', 'O', 'M', 'P'], [⟨['K', 'ù', 's', 'i', 'j', 'ǐ'], ['b', 'e', '.', 'h', 'a', 'p', 'p', 'y', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['i', 'n', 'i'], ['i', 'n'], [⟨['i', 'n', 'i'], ['i', 'n'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['n', 'ì', '-'], ['C', 'O', 'M', 'P', '-'], [⟨['n', 'ì'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['n', 'ì', '\'', 'ǐ'], ['g', 'e', 't'], [⟨['n', 'ì', '\'', 'ǐ'], ['g', 'e', 't'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['ñ', 'a', '\'', 'á'], ['t', 'h', 'i', 'n', 'g'], [⟨['ñ', 'a', '\'', 'á'], ['t', 'h', 'i', 'n', 'g'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "kusijǐ ini"), ("clauseType", "finite"), ("diagnostic", "aspect"), ("aspect", "completive")] }

def ex_9c_continuous : Datum :=
  { id := "ostrove2026_9c_continuous"
    source := ⟨"ostrove-2026", "(9c)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kùsijǐ ini =rà nî'ǐ =rà ña'á"
    glossedTokens := [("Kùsijǐ", "be.happy:COMP"), ("ini", "in"), ("=rà", "=he"), ("nî'ǐ", "get:CONT"), ("=rà", "=he"), ("ña'á", "thing")]
    glossedWords := [⟨['K', 'ù', 's', 'i', 'j', 'ǐ'], ['b', 'e', '.', 'h', 'a', 'p', 'p', 'y', ':', 'C', 'O', 'M', 'P'], [⟨['K', 'ù', 's', 'i', 'j', 'ǐ'], ['b', 'e', '.', 'h', 'a', 'p', 'p', 'y', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['i', 'n', 'i'], ['i', 'n'], [⟨['i', 'n', 'i'], ['i', 'n'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['n', 'î', '\'', 'ǐ'], ['g', 'e', 't', ':', 'C', 'O', 'N', 'T'], [⟨['n', 'î', '\'', 'ǐ'], ['g', 'e', 't', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['ñ', 'a', '\'', 'á'], ['t', 'h', 'i', 'n', 'g'], [⟨['ñ', 'a', '\'', 'á'], ['t', 'h', 'i', 'n', 'g'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "kusijǐ ini"), ("clauseType", "finite"), ("diagnostic", "aspect"), ("aspect", "continuous")] }

def ex_9c_irrealis : Datum :=
  { id := "ostrove2026_9c_irrealis"
    source := ⟨"ostrove-2026", "(9c)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kùsijǐ ini =rà ni'ǐ =rà ña'á"
    glossedTokens := [("Kùsijǐ", "be.happy:COMP"), ("ini", "in"), ("=rà", "=he"), ("ni'ǐ", "get:IRR"), ("=rà", "=he"), ("ña'á", "thing")]
    glossedWords := [⟨['K', 'ù', 's', 'i', 'j', 'ǐ'], ['b', 'e', '.', 'h', 'a', 'p', 'p', 'y', ':', 'C', 'O', 'M', 'P'], [⟨['K', 'ù', 's', 'i', 'j', 'ǐ'], ['b', 'e', '.', 'h', 'a', 'p', 'p', 'y', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['i', 'n', 'i'], ['i', 'n'], [⟨['i', 'n', 'i'], ['i', 'n'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['n', 'i', '\'', 'ǐ'], ['g', 'e', 't', ':', 'I', 'R', 'R'], [⟨['n', 'i', '\'', 'ǐ'], ['g', 'e', 't', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['ñ', 'a', '\'', 'á'], ['t', 'h', 'i', 'n', 'g'], [⟨['ñ', 'a', '\'', 'á'], ['t', 'h', 'i', 'n', 'g'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "kusijǐ ini"), ("clauseType", "finite"), ("diagnostic", "aspect"), ("aspect", "irrealis")] }

def ex_13a_completive : Datum :=
  { id := "ostrove2026_13a_completive"
    source := ⟨"ostrove-2026", "(13a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ntátu =rà xòná =rà ña'á"
    glossedTokens := [("Ntátu", "hope:CONT"), ("=rà", "=he"), ("xòná", "open:COMP"), ("=rà", "he"), ("ña'á", "thing")]
    glossedWords := [⟨['N', 't', 'á', 't', 'u'], ['h', 'o', 'p', 'e', ':', 'C', 'O', 'N', 'T'], [⟨['N', 't', 'á', 't', 'u'], ['h', 'o', 'p', 'e', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['x', 'ò', 'n', 'á'], ['o', 'p', 'e', 'n', ':', 'C', 'O', 'M', 'P'], [⟨['x', 'ò', 'n', 'á'], ['o', 'p', 'e', 'n', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['=', 'r', 'à'], ['h', 'e'], []⟩, ⟨['ñ', 'a', '\'', 'á'], ['t', 'h', 'i', 'n', 'g'], [⟨['ñ', 'a', '\'', 'á'], ['t', 'h', 'i', 'n', 'g'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ntatu"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "aspect"), ("aspect", "completive")] }

def ex_13a_continuous : Datum :=
  { id := "ostrove2026_13a_continuous"
    source := ⟨"ostrove-2026", "(13a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ntátu =rà xóná =rà ña'á"
    glossedTokens := [("Ntátu", "hope:CONT"), ("=rà", "=he"), ("xóná", "open:CONT"), ("=rà", "he"), ("ña'á", "thing")]
    glossedWords := [⟨['N', 't', 'á', 't', 'u'], ['h', 'o', 'p', 'e', ':', 'C', 'O', 'N', 'T'], [⟨['N', 't', 'á', 't', 'u'], ['h', 'o', 'p', 'e', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['x', 'ó', 'n', 'á'], ['o', 'p', 'e', 'n', ':', 'C', 'O', 'N', 'T'], [⟨['x', 'ó', 'n', 'á'], ['o', 'p', 'e', 'n', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['=', 'r', 'à'], ['h', 'e'], []⟩, ⟨['ñ', 'a', '\'', 'á'], ['t', 'h', 'i', 'n', 'g'], [⟨['ñ', 'a', '\'', 'á'], ['t', 'h', 'i', 'n', 'g'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ntatu"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "aspect"), ("aspect", "continuous")] }

def ex_13a_irrealis : Datum :=
  { id := "ostrove2026_13a_irrealis"
    source := ⟨"ostrove-2026", "(13a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ntátu =rà koná =rà ña'á"
    glossedTokens := [("Ntátu", "hope:CONT"), ("=rà", "=he"), ("koná", "open:IRR"), ("=rà", "he"), ("ña'á", "thing")]
    glossedWords := [⟨['N', 't', 'á', 't', 'u'], ['h', 'o', 'p', 'e', ':', 'C', 'O', 'N', 'T'], [⟨['N', 't', 'á', 't', 'u'], ['h', 'o', 'p', 'e', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['k', 'o', 'n', 'á'], ['o', 'p', 'e', 'n', ':', 'I', 'R', 'R'], [⟨['k', 'o', 'n', 'á'], ['o', 'p', 'e', 'n', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'r', 'à'], ['h', 'e'], []⟩, ⟨['ñ', 'a', '\'', 'á'], ['t', 'h', 'i', 'n', 'g'], [⟨['ñ', 'a', '\'', 'á'], ['t', 'h', 'i', 'n', 'g'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ntatu"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "aspect"), ("aspect", "irrealis")] }

def ex_13b_completive : Datum :=
  { id := "ostrove2026_13b_completive"
    source := ⟨"ostrove-2026", "(13b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kôni =ì xòná =ì mí yùye'e"
    glossedTokens := [("Kôni", "want:CONT"), ("=ì", "=I"), ("xòná", "open:COMP"), ("=ì", "=I"), ("mí", "the"), ("yùye'e", "door")]
    glossedWords := [⟨['K', 'ô', 'n', 'i'], ['w', 'a', 'n', 't', ':', 'C', 'O', 'N', 'T'], [⟨['K', 'ô', 'n', 'i'], ['w', 'a', 'n', 't', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['=', 'ì'], ['=', 'I'], [⟨['ì'], ['I'], some '='⟩]⟩, ⟨['x', 'ò', 'n', 'á'], ['o', 'p', 'e', 'n', ':', 'C', 'O', 'M', 'P'], [⟨['x', 'ò', 'n', 'á'], ['o', 'p', 'e', 'n', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['=', 'ì'], ['=', 'I'], [⟨['ì'], ['I'], some '='⟩]⟩, ⟨['m', 'í'], ['t', 'h', 'e'], [⟨['m', 'í'], ['t', 'h', 'e'], none⟩]⟩, ⟨['y', 'ù', 'y', 'e', '\'', 'e'], ['d', 'o', 'o', 'r'], [⟨['y', 'ù', 'y', 'e', '\'', 'e'], ['d', 'o', 'o', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "kòni"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "aspect"), ("aspect", "completive")] }

def ex_13b_continuous : Datum :=
  { id := "ostrove2026_13b_continuous"
    source := ⟨"ostrove-2026", "(13b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kôni =ì xóxá =ì mí yùye'e"
    glossedTokens := [("Kôni", "want:CONT"), ("=ì", "=I"), ("xóxá", "open:CONT"), ("=ì", "=I"), ("mí", "the"), ("yùye'e", "door")]
    glossedWords := [⟨['K', 'ô', 'n', 'i'], ['w', 'a', 'n', 't', ':', 'C', 'O', 'N', 'T'], [⟨['K', 'ô', 'n', 'i'], ['w', 'a', 'n', 't', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['=', 'ì'], ['=', 'I'], [⟨['ì'], ['I'], some '='⟩]⟩, ⟨['x', 'ó', 'x', 'á'], ['o', 'p', 'e', 'n', ':', 'C', 'O', 'N', 'T'], [⟨['x', 'ó', 'x', 'á'], ['o', 'p', 'e', 'n', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['=', 'ì'], ['=', 'I'], [⟨['ì'], ['I'], some '='⟩]⟩, ⟨['m', 'í'], ['t', 'h', 'e'], [⟨['m', 'í'], ['t', 'h', 'e'], none⟩]⟩, ⟨['y', 'ù', 'y', 'e', '\'', 'e'], ['d', 'o', 'o', 'r'], [⟨['y', 'ù', 'y', 'e', '\'', 'e'], ['d', 'o', 'o', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "kòni"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "aspect"), ("aspect", "continuous")] }

def ex_13b_irrealis : Datum :=
  { id := "ostrove2026_13b_irrealis"
    source := ⟨"ostrove-2026", "(13b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kôni =ì koná =ì mí yùye'e"
    glossedTokens := [("Kôni", "want:CONT"), ("=ì", "=I"), ("koná", "open:IRR"), ("=ì", "=I"), ("mí", "the"), ("yùye'e", "door")]
    glossedWords := [⟨['K', 'ô', 'n', 'i'], ['w', 'a', 'n', 't', ':', 'C', 'O', 'N', 'T'], [⟨['K', 'ô', 'n', 'i'], ['w', 'a', 'n', 't', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['=', 'ì'], ['=', 'I'], [⟨['ì'], ['I'], some '='⟩]⟩, ⟨['k', 'o', 'n', 'á'], ['o', 'p', 'e', 'n', ':', 'I', 'R', 'R'], [⟨['k', 'o', 'n', 'á'], ['o', 'p', 'e', 'n', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'ì'], ['=', 'I'], [⟨['ì'], ['I'], some '='⟩]⟩, ⟨['m', 'í'], ['t', 'h', 'e'], [⟨['m', 'í'], ['t', 'h', 'e'], none⟩]⟩, ⟨['y', 'ù', 'y', 'e', '\'', 'e'], ['d', 'o', 'o', 'r'], [⟨['y', 'ù', 'y', 'e', '\'', 'e'], ['d', 'o', 'o', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "kòni"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "aspect"), ("aspect", "irrealis")] }

def ex_13c_completive : Datum :=
  { id := "ostrove2026_13c_completive"
    source := ⟨"ostrove-2026", "(13c)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ntùkú Ana xìxi kwa'ǎ =ñá ntstika"
    glossedTokens := [("Ntùkú", "try:COMP"), ("Ana", "Ana"), ("xìxi", "eat:COMP"), ("kwa'ǎ", "more"), ("=ñá", "=she"), ("ntstika", "banana")]
    glossedWords := [⟨['N', 't', 'ù', 'k', 'ú'], ['t', 'r', 'y', ':', 'C', 'O', 'M', 'P'], [⟨['N', 't', 'ù', 'k', 'ú'], ['t', 'r', 'y', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['A', 'n', 'a'], ['A', 'n', 'a'], [⟨['A', 'n', 'a'], ['A', 'n', 'a'], none⟩]⟩, ⟨['x', 'ì', 'x', 'i'], ['e', 'a', 't', ':', 'C', 'O', 'M', 'P'], [⟨['x', 'ì', 'x', 'i'], ['e', 'a', 't', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['k', 'w', 'a', '\'', 'ǎ'], ['m', 'o', 'r', 'e'], [⟨['k', 'w', 'a', '\'', 'ǎ'], ['m', 'o', 'r', 'e'], none⟩]⟩, ⟨['=', 'ñ', 'á'], ['=', 's', 'h', 'e'], [⟨['ñ', 'á'], ['s', 'h', 'e'], some '='⟩]⟩, ⟨['n', 't', 's', 't', 'i', 'k', 'a'], ['b', 'a', 'n', 'a', 'n', 'a'], [⟨['n', 't', 's', 't', 'i', 'k', 'a'], ['b', 'a', 'n', 'a', 'n', 'a'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ntukú"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "aspect"), ("aspect", "completive")] }

def ex_13c_continuous : Datum :=
  { id := "ostrove2026_13c_continuous"
    source := ⟨"ostrove-2026", "(13c)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ntùkú Ana xíxi kwa'ǎ =ñá ntstika"
    glossedTokens := [("Ntùkú", "try:COMP"), ("Ana", "Ana"), ("xíxi", "eat:CONT"), ("kwa'ǎ", "more"), ("=ñá", "=she"), ("ntstika", "banana")]
    glossedWords := [⟨['N', 't', 'ù', 'k', 'ú'], ['t', 'r', 'y', ':', 'C', 'O', 'M', 'P'], [⟨['N', 't', 'ù', 'k', 'ú'], ['t', 'r', 'y', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['A', 'n', 'a'], ['A', 'n', 'a'], [⟨['A', 'n', 'a'], ['A', 'n', 'a'], none⟩]⟩, ⟨['x', 'í', 'x', 'i'], ['e', 'a', 't', ':', 'C', 'O', 'N', 'T'], [⟨['x', 'í', 'x', 'i'], ['e', 'a', 't', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['k', 'w', 'a', '\'', 'ǎ'], ['m', 'o', 'r', 'e'], [⟨['k', 'w', 'a', '\'', 'ǎ'], ['m', 'o', 'r', 'e'], none⟩]⟩, ⟨['=', 'ñ', 'á'], ['=', 's', 'h', 'e'], [⟨['ñ', 'á'], ['s', 'h', 'e'], some '='⟩]⟩, ⟨['n', 't', 's', 't', 'i', 'k', 'a'], ['b', 'a', 'n', 'a', 'n', 'a'], [⟨['n', 't', 's', 't', 'i', 'k', 'a'], ['b', 'a', 'n', 'a', 'n', 'a'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ntukú"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "aspect"), ("aspect", "continuous")] }

def ex_13c_irrealis : Datum :=
  { id := "ostrove2026_13c_irrealis"
    source := ⟨"ostrove-2026", "(13c)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ntùkú Ana kuxi kwa'ǎ =ñá ntstika"
    glossedTokens := [("Ntùkú", "try:COMP"), ("Ana", "Ana"), ("kuxi", "eat:IRR"), ("kwa'ǎ", "more"), ("=ñá", "=she"), ("ntstika", "banana")]
    glossedWords := [⟨['N', 't', 'ù', 'k', 'ú'], ['t', 'r', 'y', ':', 'C', 'O', 'M', 'P'], [⟨['N', 't', 'ù', 'k', 'ú'], ['t', 'r', 'y', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['A', 'n', 'a'], ['A', 'n', 'a'], [⟨['A', 'n', 'a'], ['A', 'n', 'a'], none⟩]⟩, ⟨['k', 'u', 'x', 'i'], ['e', 'a', 't', ':', 'I', 'R', 'R'], [⟨['k', 'u', 'x', 'i'], ['e', 'a', 't', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['k', 'w', 'a', '\'', 'ǎ'], ['m', 'o', 'r', 'e'], [⟨['k', 'w', 'a', '\'', 'ǎ'], ['m', 'o', 'r', 'e'], none⟩]⟩, ⟨['=', 'ñ', 'á'], ['=', 's', 'h', 'e'], [⟨['ñ', 'á'], ['s', 'h', 'e'], some '='⟩]⟩, ⟨['n', 't', 's', 't', 'i', 'k', 'a'], ['b', 'a', 'n', 'a', 'n', 'a'], [⟨['n', 't', 's', 't', 'i', 'k', 'a'], ['b', 'a', 'n', 'a', 'n', 'a'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ntukú"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "aspect"), ("aspect", "irrealis")] }

def ex_13d_completive : Datum :=
  { id := "ostrove2026_13d_completive"
    source := ⟨"ostrove-2026", "(13d)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Xíniñu'u =ì xì'i kwa'ǎ =ì tskwǐì"
    glossedTokens := [("Xíniñu'u", "need:COMP"), ("=ì", "=I"), ("xì'i", "drink:COMP"), ("kwa'ǎ", "more"), ("=ì", "=I"), ("tskwǐì", "water")]
    glossedWords := [⟨['X', 'í', 'n', 'i', 'ñ', 'u', '\'', 'u'], ['n', 'e', 'e', 'd', ':', 'C', 'O', 'M', 'P'], [⟨['X', 'í', 'n', 'i', 'ñ', 'u', '\'', 'u'], ['n', 'e', 'e', 'd', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['=', 'ì'], ['=', 'I'], [⟨['ì'], ['I'], some '='⟩]⟩, ⟨['x', 'ì', '\'', 'i'], ['d', 'r', 'i', 'n', 'k', ':', 'C', 'O', 'M', 'P'], [⟨['x', 'ì', '\'', 'i'], ['d', 'r', 'i', 'n', 'k', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['k', 'w', 'a', '\'', 'ǎ'], ['m', 'o', 'r', 'e'], [⟨['k', 'w', 'a', '\'', 'ǎ'], ['m', 'o', 'r', 'e'], none⟩]⟩, ⟨['=', 'ì'], ['=', 'I'], [⟨['ì'], ['I'], some '='⟩]⟩, ⟨['t', 's', 'k', 'w', 'ǐ', 'ì'], ['w', 'a', 't', 'e', 'r'], [⟨['t', 's', 'k', 'w', 'ǐ', 'ì'], ['w', 'a', 't', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "xiniñu'u"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "aspect"), ("aspect", "completive")] }

def ex_13d_continuous : Datum :=
  { id := "ostrove2026_13d_continuous"
    source := ⟨"ostrove-2026", "(13d)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Xíniñu'u =ì xí'ì kwa'ǎ =ì tskwǐì"
    glossedTokens := [("Xíniñu'u", "need:COMP"), ("=ì", "=I"), ("xí'ì", "drink:CONT"), ("kwa'ǎ", "more"), ("=ì", "=I"), ("tskwǐì", "water")]
    glossedWords := [⟨['X', 'í', 'n', 'i', 'ñ', 'u', '\'', 'u'], ['n', 'e', 'e', 'd', ':', 'C', 'O', 'M', 'P'], [⟨['X', 'í', 'n', 'i', 'ñ', 'u', '\'', 'u'], ['n', 'e', 'e', 'd', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['=', 'ì'], ['=', 'I'], [⟨['ì'], ['I'], some '='⟩]⟩, ⟨['x', 'í', '\'', 'ì'], ['d', 'r', 'i', 'n', 'k', ':', 'C', 'O', 'N', 'T'], [⟨['x', 'í', '\'', 'ì'], ['d', 'r', 'i', 'n', 'k', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['k', 'w', 'a', '\'', 'ǎ'], ['m', 'o', 'r', 'e'], [⟨['k', 'w', 'a', '\'', 'ǎ'], ['m', 'o', 'r', 'e'], none⟩]⟩, ⟨['=', 'ì'], ['=', 'I'], [⟨['ì'], ['I'], some '='⟩]⟩, ⟨['t', 's', 'k', 'w', 'ǐ', 'ì'], ['w', 'a', 't', 'e', 'r'], [⟨['t', 's', 'k', 'w', 'ǐ', 'ì'], ['w', 'a', 't', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "xiniñu'u"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "aspect"), ("aspect", "continuous")] }

def ex_13d_irrealis : Datum :=
  { id := "ostrove2026_13d_irrealis"
    source := ⟨"ostrove-2026", "(13d)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Xíniñu'u =ì ko'o kwa'ǎ =ì tskwǐì"
    glossedTokens := [("Xíniñu'u", "need:COMP"), ("=ì", "=I"), ("ko'o", "drink:IRR"), ("kwa'ǎ", "more"), ("=ì", "=I"), ("tskwǐì", "water")]
    glossedWords := [⟨['X', 'í', 'n', 'i', 'ñ', 'u', '\'', 'u'], ['n', 'e', 'e', 'd', ':', 'C', 'O', 'M', 'P'], [⟨['X', 'í', 'n', 'i', 'ñ', 'u', '\'', 'u'], ['n', 'e', 'e', 'd', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['=', 'ì'], ['=', 'I'], [⟨['ì'], ['I'], some '='⟩]⟩, ⟨['k', 'o', '\'', 'o'], ['d', 'r', 'i', 'n', 'k', ':', 'I', 'R', 'R'], [⟨['k', 'o', '\'', 'o'], ['d', 'r', 'i', 'n', 'k', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['k', 'w', 'a', '\'', 'ǎ'], ['m', 'o', 'r', 'e'], [⟨['k', 'w', 'a', '\'', 'ǎ'], ['m', 'o', 'r', 'e'], none⟩]⟩, ⟨['=', 'ì'], ['=', 'I'], [⟨['ì'], ['I'], some '='⟩]⟩, ⟨['t', 's', 'k', 'w', 'ǐ', 'ì'], ['w', 'a', 't', 'e', 'r'], [⟨['t', 's', 'k', 'w', 'ǐ', 'ì'], ['w', 'a', 't', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "xiniñu'u"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "aspect"), ("aspect", "irrealis")] }

def ex_10a : Datum :=
  { id := "ostrove2026_10a"
    source := ⟨"ostrove-2026", "(10a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Bitsìn kâ'àn Maria xìin =ñá iin be'e xàa koni"
    glossedTokens := [("Bitsìn", "now"), ("kâ'àn", "say:CONT"), ("Maria", "Maria"), ("xìin", "buy:COMP"), ("=ñá", "=she"), ("iin", "one"), ("be'e", "house"), ("xàa", "new"), ("koni", "yesterday")]
    glossedWords := [⟨['B', 'i', 't', 's', 'ì', 'n'], ['n', 'o', 'w'], [⟨['B', 'i', 't', 's', 'ì', 'n'], ['n', 'o', 'w'], none⟩]⟩, ⟨['k', 'â', '\'', 'à', 'n'], ['s', 'a', 'y', ':', 'C', 'O', 'N', 'T'], [⟨['k', 'â', '\'', 'à', 'n'], ['s', 'a', 'y', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['x', 'ì', 'i', 'n'], ['b', 'u', 'y', ':', 'C', 'O', 'M', 'P'], [⟨['x', 'ì', 'i', 'n'], ['b', 'u', 'y', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['=', 'ñ', 'á'], ['=', 's', 'h', 'e'], [⟨['ñ', 'á'], ['s', 'h', 'e'], some '='⟩]⟩, ⟨['i', 'i', 'n'], ['o', 'n', 'e'], [⟨['i', 'i', 'n'], ['o', 'n', 'e'], none⟩]⟩, ⟨['b', 'e', '\'', 'e'], ['h', 'o', 'u', 's', 'e'], [⟨['b', 'e', '\'', 'e'], ['h', 'o', 'u', 's', 'e'], none⟩]⟩, ⟨['x', 'à', 'a'], ['n', 'e', 'w'], [⟨['x', 'à', 'a'], ['n', 'e', 'w'], none⟩]⟩, ⟨['k', 'o', 'n', 'i'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['k', 'o', 'n', 'i'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "kà'àn"), ("clauseType", "finite"), ("diagnostic", "tense")] }

def ex_10b : Datum :=
  { id := "ostrove2026_10b"
    source := ⟨"ostrove-2026", "(10b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Itsyààn ka'án Raúl xí'i kwé'e =rà bitsìn"
    glossedTokens := [("Itsyààn", "tomorrow"), ("ka'án", "think:IRR"), ("Raúl", "Raul"), ("xí'i", "drink:CONT"), ("kwé'e", "a.lot"), ("=rà", "=he"), ("bitsìn", "now")]
    glossedWords := [⟨['I', 't', 's', 'y', 'à', 'à', 'n'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['I', 't', 's', 'y', 'à', 'à', 'n'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩, ⟨['k', 'a', '\'', 'á', 'n'], ['t', 'h', 'i', 'n', 'k', ':', 'I', 'R', 'R'], [⟨['k', 'a', '\'', 'á', 'n'], ['t', 'h', 'i', 'n', 'k', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['R', 'a', 'ú', 'l'], ['R', 'a', 'u', 'l'], [⟨['R', 'a', 'ú', 'l'], ['R', 'a', 'u', 'l'], none⟩]⟩, ⟨['x', 'í', '\'', 'i'], ['d', 'r', 'i', 'n', 'k', ':', 'C', 'O', 'N', 'T'], [⟨['x', 'í', '\'', 'i'], ['d', 'r', 'i', 'n', 'k', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['k', 'w', 'é', '\'', 'e'], ['a', '.', 'l', 'o', 't'], [⟨['k', 'w', 'é', '\'', 'e'], ['a', '.', 'l', 'o', 't'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['b', 'i', 't', 's', 'ì', 'n'], ['n', 'o', 'w'], [⟨['b', 'i', 't', 's', 'ì', 'n'], ['n', 'o', 'w'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ka'án"), ("clauseType", "finite"), ("diagnostic", "tense")] }

def ex_16a : Datum :=
  { id := "ostrove2026_16a"
    source := ⟨"ostrove-2026", "(16a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Bitsìn ntátu =ì kusi bà'a =ì itsyààn"
    glossedTokens := [("Bitsìn", "today"), ("ntátu", "hope:CONT"), ("=ì", "=I"), ("kusi", "sleep:IRR"), ("bà'a", "well"), ("=ì", "=I"), ("itsyààn", "tomorrow")]
    glossedWords := [⟨['B', 'i', 't', 's', 'ì', 'n'], ['t', 'o', 'd', 'a', 'y'], [⟨['B', 'i', 't', 's', 'ì', 'n'], ['t', 'o', 'd', 'a', 'y'], none⟩]⟩, ⟨['n', 't', 'á', 't', 'u'], ['h', 'o', 'p', 'e', ':', 'C', 'O', 'N', 'T'], [⟨['n', 't', 'á', 't', 'u'], ['h', 'o', 'p', 'e', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['=', 'ì'], ['=', 'I'], [⟨['ì'], ['I'], some '='⟩]⟩, ⟨['k', 'u', 's', 'i'], ['s', 'l', 'e', 'e', 'p', ':', 'I', 'R', 'R'], [⟨['k', 'u', 's', 'i'], ['s', 'l', 'e', 'e', 'p', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['b', 'à', '\'', 'a'], ['w', 'e', 'l', 'l'], [⟨['b', 'à', '\'', 'a'], ['w', 'e', 'l', 'l'], none⟩]⟩, ⟨['=', 'ì'], ['=', 'I'], [⟨['ì'], ['I'], some '='⟩]⟩, ⟨['i', 't', 's', 'y', 'à', 'à', 'n'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['i', 't', 's', 'y', 'à', 'à', 'n'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ntatu"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "tense")] }

def ex_16b : Datum :=
  { id := "ostrove2026_16b"
    source := ⟨"ostrove-2026", "(16b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Koni kò nì- kòni Maria ku'ún =ñá tienda bitsìn"
    glossedTokens := [("Koni", "yesterday"), ("kò", "NEG"), ("nì-", "COMP-"), ("kòni", "want"), ("Maria", "Maria"), ("ku'ún", "go:IRR"), ("=ñá", "=she"), ("tienda", "store"), ("bitsìn", "today")]
    glossedWords := [⟨['K', 'o', 'n', 'i'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['K', 'o', 'n', 'i'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩, ⟨['k', 'ò'], ['N', 'E', 'G'], [⟨['k', 'ò'], ['N', 'E', 'G'], none⟩]⟩, ⟨['n', 'ì', '-'], ['C', 'O', 'M', 'P', '-'], [⟨['n', 'ì'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['k', 'ò', 'n', 'i'], ['w', 'a', 'n', 't'], [⟨['k', 'ò', 'n', 'i'], ['w', 'a', 'n', 't'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['k', 'u', '\'', 'ú', 'n'], ['g', 'o', ':', 'I', 'R', 'R'], [⟨['k', 'u', '\'', 'ú', 'n'], ['g', 'o', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'ñ', 'á'], ['=', 's', 'h', 'e'], [⟨['ñ', 'á'], ['s', 'h', 'e'], some '='⟩]⟩, ⟨['t', 'i', 'e', 'n', 'd', 'a'], ['s', 't', 'o', 'r', 'e'], [⟨['t', 'i', 'e', 'n', 'd', 'a'], ['s', 't', 'o', 'r', 'e'], none⟩]⟩, ⟨['b', 'i', 't', 's', 'ì', 'n'], ['t', 'o', 'd', 'a', 'y'], [⟨['b', 'i', 't', 's', 'ì', 'n'], ['t', 'o', 'd', 'a', 'y'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "kòni"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "tense")] }

def ex_17a : Datum :=
  { id := "ostrove2026_17a"
    source := ⟨"ostrove-2026", "(17a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Bitsìn nákú'ún ini Maria ku'ún =ñá tienda itsyààn"
    glossedTokens := [("Bitsìn", "today"), ("nákú'ún", "remember:CONT"), ("ini", "in"), ("Maria", "Maria"), ("ku'ún", "go:IRR"), ("=ñá", "=she"), ("tienda", "market"), ("itsyààn", "tomorrow")]
    glossedWords := [⟨['B', 'i', 't', 's', 'ì', 'n'], ['t', 'o', 'd', 'a', 'y'], [⟨['B', 'i', 't', 's', 'ì', 'n'], ['t', 'o', 'd', 'a', 'y'], none⟩]⟩, ⟨['n', 'á', 'k', 'ú', '\'', 'ú', 'n'], ['r', 'e', 'm', 'e', 'm', 'b', 'e', 'r', ':', 'C', 'O', 'N', 'T'], [⟨['n', 'á', 'k', 'ú', '\'', 'ú', 'n'], ['r', 'e', 'm', 'e', 'm', 'b', 'e', 'r', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['i', 'n', 'i'], ['i', 'n'], [⟨['i', 'n', 'i'], ['i', 'n'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['k', 'u', '\'', 'ú', 'n'], ['g', 'o', ':', 'I', 'R', 'R'], [⟨['k', 'u', '\'', 'ú', 'n'], ['g', 'o', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'ñ', 'á'], ['=', 's', 'h', 'e'], [⟨['ñ', 'á'], ['s', 'h', 'e'], some '='⟩]⟩, ⟨['t', 'i', 'e', 'n', 'd', 'a'], ['m', 'a', 'r', 'k', 'e', 't'], [⟨['t', 'i', 'e', 'n', 'd', 'a'], ['m', 'a', 'r', 'k', 'e', 't'], none⟩]⟩, ⟨['i', 't', 's', 'y', 'à', 'à', 'n'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['i', 't', 's', 'y', 'à', 'à', 'n'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "nakú'ún ini"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "tense")] }

def ex_17b : Datum :=
  { id := "ostrove2026_17b"
    source := ⟨"ostrove-2026", "(17b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Koni ntùkú Juân ka'ani =rà iin ntsìbá'yi itsyààn"
    glossedTokens := [("Koni", "yesterday"), ("ntùkú", "try:COMP"), ("Juân", "Juan"), ("ka'ani", "kill:IRR"), ("=rà", "=he"), ("iin", "one"), ("ntsìbá'yi", "coyote"), ("itsyààn", "tomorrow")]
    glossedWords := [⟨['K', 'o', 'n', 'i'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['K', 'o', 'n', 'i'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩, ⟨['n', 't', 'ù', 'k', 'ú'], ['t', 'r', 'y', ':', 'C', 'O', 'M', 'P'], [⟨['n', 't', 'ù', 'k', 'ú'], ['t', 'r', 'y', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['J', 'u', 'â', 'n'], ['J', 'u', 'a', 'n'], [⟨['J', 'u', 'â', 'n'], ['J', 'u', 'a', 'n'], none⟩]⟩, ⟨['k', 'a', '\'', 'a', 'n', 'i'], ['k', 'i', 'l', 'l', ':', 'I', 'R', 'R'], [⟨['k', 'a', '\'', 'a', 'n', 'i'], ['k', 'i', 'l', 'l', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['i', 'i', 'n'], ['o', 'n', 'e'], [⟨['i', 'i', 'n'], ['o', 'n', 'e'], none⟩]⟩, ⟨['n', 't', 's', 'ì', 'b', 'á', '\'', 'y', 'i'], ['c', 'o', 'y', 'o', 't', 'e'], [⟨['n', 't', 's', 'ì', 'b', 'á', '\'', 'y', 'i'], ['c', 'o', 'y', 'o', 't', 'e'], none⟩]⟩, ⟨['i', 't', 's', 'y', 'à', 'à', 'n'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['i', 't', 's', 'y', 'à', 'à', 'n'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ntukú"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "tense")] }

def ex_12a : Datum :=
  { id := "ostrove2026_12a"
    source := ⟨"ostrove-2026", "(12a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Káchi Raúl xí'in Pablo xìxi kwé'e =rà ndùchì koni"
    glossedTokens := [("Káchi", "say:COMP"), ("Raúl", "Raul"), ("xí'in", "with"), ("Pablo", "Pablo"), ("xìxi", "eat:COMP"), ("kwé'e", "many"), ("=rà", "=he"), ("ndùchì", "bean"), ("koni", "yesterday")]
    glossedWords := [⟨['K', 'á', 'c', 'h', 'i'], ['s', 'a', 'y', ':', 'C', 'O', 'M', 'P'], [⟨['K', 'á', 'c', 'h', 'i'], ['s', 'a', 'y', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['R', 'a', 'ú', 'l'], ['R', 'a', 'u', 'l'], [⟨['R', 'a', 'ú', 'l'], ['R', 'a', 'u', 'l'], none⟩]⟩, ⟨['x', 'í', '\'', 'i', 'n'], ['w', 'i', 't', 'h'], [⟨['x', 'í', '\'', 'i', 'n'], ['w', 'i', 't', 'h'], none⟩]⟩, ⟨['P', 'a', 'b', 'l', 'o'], ['P', 'a', 'b', 'l', 'o'], [⟨['P', 'a', 'b', 'l', 'o'], ['P', 'a', 'b', 'l', 'o'], none⟩]⟩, ⟨['x', 'ì', 'x', 'i'], ['e', 'a', 't', ':', 'C', 'O', 'M', 'P'], [⟨['x', 'ì', 'x', 'i'], ['e', 'a', 't', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['k', 'w', 'é', '\'', 'e'], ['m', 'a', 'n', 'y'], [⟨['k', 'w', 'é', '\'', 'e'], ['m', 'a', 'n', 'y'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['n', 'd', 'ù', 'c', 'h', 'ì'], ['b', 'e', 'a', 'n'], [⟨['n', 'd', 'ù', 'c', 'h', 'ì'], ['b', 'e', 'a', 'n'], none⟩]⟩, ⟨['k', 'o', 'n', 'i'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['k', 'o', 'n', 'i'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("controlled", .acceptable), ("free", .acceptable)]
    paperFeatures := [("verb", "káchi"), ("clauseType", "finite"), ("diagnostic", "subject")] }

def ex_12b : Datum :=
  { id := "ostrove2026_12b"
    source := ⟨"ostrove-2026", "(12b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kúsijǐ ini Eva kèba'a =ñá carrera"
    glossedTokens := [("Kúsijǐ", "be.happy:CONT"), ("ini", "in"), ("Eva", "Eva"), ("kèba'a", "win:COMP"), ("=ñá", "=she"), ("carrera", "race")]
    glossedWords := [⟨['K', 'ú', 's', 'i', 'j', 'ǐ'], ['b', 'e', '.', 'h', 'a', 'p', 'p', 'y', ':', 'C', 'O', 'N', 'T'], [⟨['K', 'ú', 's', 'i', 'j', 'ǐ'], ['b', 'e', '.', 'h', 'a', 'p', 'p', 'y', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['i', 'n', 'i'], ['i', 'n'], [⟨['i', 'n', 'i'], ['i', 'n'], none⟩]⟩, ⟨['E', 'v', 'a'], ['E', 'v', 'a'], [⟨['E', 'v', 'a'], ['E', 'v', 'a'], none⟩]⟩, ⟨['k', 'è', 'b', 'a', '\'', 'a'], ['w', 'i', 'n', ':', 'C', 'O', 'M', 'P'], [⟨['k', 'è', 'b', 'a', '\'', 'a'], ['w', 'i', 'n', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['=', 'ñ', 'á'], ['=', 's', 'h', 'e'], [⟨['ñ', 'á'], ['s', 'h', 'e'], some '='⟩]⟩, ⟨['c', 'a', 'r', 'r', 'e', 'r', 'a'], ['r', 'a', 'c', 'e'], [⟨['c', 'a', 'r', 'r', 'e', 'r', 'a'], ['r', 'a', 'c', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("controlled", .acceptable), ("free", .acceptable)]
    paperFeatures := [("verb", "kusijǐ ini"), ("clauseType", "finite"), ("diagnostic", "subject")] }

def ex_18a : Datum :=
  { id := "ostrove2026_18a"
    source := ⟨"ostrove-2026", "(18a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kôni Maria kusi =ñá"
    glossedTokens := [("Kôni", "want:CONT"), ("Maria", "Maria"), ("kusi", "sleep:IRR"), ("=ñá", "=she")]
    glossedWords := [⟨['K', 'ô', 'n', 'i'], ['w', 'a', 'n', 't', ':', 'C', 'O', 'N', 'T'], [⟨['K', 'ô', 'n', 'i'], ['w', 'a', 'n', 't', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['k', 'u', 's', 'i'], ['s', 'l', 'e', 'e', 'p', ':', 'I', 'R', 'R'], [⟨['k', 'u', 's', 'i'], ['s', 'l', 'e', 'e', 'p', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'ñ', 'á'], ['=', 's', 'h', 'e'], [⟨['ñ', 'á'], ['s', 'h', 'e'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("controlled", .acceptable), ("free", .ungrammatical)]
    paperFeatures := [("verb", "kòni"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "subject")] }

def ex_18b : Datum :=
  { id := "ostrove2026_18b"
    source := ⟨"ostrove-2026", "(18b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kôni Maria ná kusi =ñá"
    glossedTokens := [("Kôni", "want:CONT"), ("Maria", "Maria"), ("ná", "NÁ"), ("kusi", "sleep:IRR"), ("=ñá", "=she")]
    glossedWords := [⟨['K', 'ô', 'n', 'i'], ['w', 'a', 'n', 't', ':', 'C', 'O', 'N', 'T'], [⟨['K', 'ô', 'n', 'i'], ['w', 'a', 'n', 't', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['n', 'á'], ['N', 'Á'], [⟨['n', 'á'], ['N', 'Á'], none⟩]⟩, ⟨['k', 'u', 's', 'i'], ['s', 'l', 'e', 'e', 'p', ':', 'I', 'R', 'R'], [⟨['k', 'u', 's', 'i'], ['s', 'l', 'e', 'e', 'p', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'ñ', 'á'], ['=', 's', 'h', 'e'], [⟨['ñ', 'á'], ['s', 'h', 'e'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("controlled", .ungrammatical), ("free", .acceptable)]
    paperFeatures := [("verb", "kòni"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "subject")] }

def ex_18c : Datum :=
  { id := "ostrove2026_18c"
    source := ⟨"ostrove-2026", "(18c)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kôni Maria kusi =rí"
    glossedTokens := [("Kôni", "want:CONT"), ("Maria", "Maria"), ("kusi", "sleep:IRR"), ("=rí", "=it.AML")]
    glossedWords := [⟨['K', 'ô', 'n', 'i'], ['w', 'a', 'n', 't', ':', 'C', 'O', 'N', 'T'], [⟨['K', 'ô', 'n', 'i'], ['w', 'a', 'n', 't', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['k', 'u', 's', 'i'], ['s', 'l', 'e', 'e', 'p', ':', 'I', 'R', 'R'], [⟨['k', 'u', 's', 'i'], ['s', 'l', 'e', 'e', 'p', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'r', 'í'], ['=', 'i', 't', '.', 'A', 'M', 'L'], [⟨['r', 'í'], ['i', 't', '.', 'A', 'M', 'L'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Kôni Maria ná kusi =rí", .acceptable)]
    readings := [("free", .acceptable)]
    paperFeatures := [("verb", "kòni"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "subject")] }

def ex_18d : Datum :=
  { id := "ostrove2026_18d"
    source := ⟨"ostrove-2026", "(18d)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kôni Maria kusi lěe =ñá"
    glossedTokens := [("Kôni", "want:CONT"), ("Maria", "Maria"), ("kusi", "sleep:IRR"), ("lěe", "baby"), ("=ñá", "=her")]
    glossedWords := [⟨['K', 'ô', 'n', 'i'], ['w', 'a', 'n', 't', ':', 'C', 'O', 'N', 'T'], [⟨['K', 'ô', 'n', 'i'], ['w', 'a', 'n', 't', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['k', 'u', 's', 'i'], ['s', 'l', 'e', 'e', 'p', ':', 'I', 'R', 'R'], [⟨['k', 'u', 's', 'i'], ['s', 'l', 'e', 'e', 'p', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['l', 'ě', 'e'], ['b', 'a', 'b', 'y'], [⟨['l', 'ě', 'e'], ['b', 'a', 'b', 'y'], none⟩]⟩, ⟨['=', 'ñ', 'á'], ['=', 'h', 'e', 'r'], [⟨['ñ', 'á'], ['h', 'e', 'r'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Kôni Maria ná kusi lěe =ñá", .acceptable)]
    readings := [("free", .acceptable)]
    paperFeatures := [("verb", "kòni"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "subject"), ("embeddedSubject", "lexical")] }

def ex_19a : Datum :=
  { id := "ostrove2026_19a"
    source := ⟨"ostrove-2026", "(19a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ntùkú Maria ku'un =rà tienda"
    glossedTokens := [("Ntùkú", "try:COMP"), ("Maria", "Maria"), ("ku'un", "go:IRR"), ("=rà", "=he"), ("tienda", "store")]
    glossedWords := [⟨['N', 't', 'ù', 'k', 'ú'], ['t', 'r', 'y', ':', 'C', 'O', 'M', 'P'], [⟨['N', 't', 'ù', 'k', 'ú'], ['t', 'r', 'y', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['k', 'u', '\'', 'u', 'n'], ['g', 'o', ':', 'I', 'R', 'R'], [⟨['k', 'u', '\'', 'u', 'n'], ['g', 'o', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['t', 'i', 'e', 'n', 'd', 'a'], ['s', 't', 'o', 'r', 'e'], [⟨['t', 'i', 'e', 'n', 'd', 'a'], ['s', 't', 'o', 'r', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := [("Ntùkú Maria ná ku'un =rà tienda", .ungrammatical), ("Ntùkú Maria ná ku'un =ñá tienda", .ungrammatical)]
    readings := [("free", .ungrammatical)]
    paperFeatures := [("verb", "ntukú"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "subject")] }

def ex_19b : Datum :=
  { id := "ostrove2026_19b"
    source := ⟨"ostrove-2026", "(19b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Nàkú'ún ini Maria kata bà'a =rà"
    glossedTokens := [("Nàkú'ún", "remember:CONT"), ("ini", "in"), ("Maria", "Maria"), ("kata", "sing:IRR"), ("bà'a", "well"), ("=rà", "=he")]
    glossedWords := [⟨['N', 'à', 'k', 'ú', '\'', 'ú', 'n'], ['r', 'e', 'm', 'e', 'm', 'b', 'e', 'r', ':', 'C', 'O', 'N', 'T'], [⟨['N', 'à', 'k', 'ú', '\'', 'ú', 'n'], ['r', 'e', 'm', 'e', 'm', 'b', 'e', 'r', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['i', 'n', 'i'], ['i', 'n'], [⟨['i', 'n', 'i'], ['i', 'n'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['k', 'a', 't', 'a'], ['s', 'i', 'n', 'g', ':', 'I', 'R', 'R'], [⟨['k', 'a', 't', 'a'], ['s', 'i', 'n', 'g', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['b', 'à', '\'', 'a'], ['w', 'e', 'l', 'l'], [⟨['b', 'à', '\'', 'a'], ['w', 'e', 'l', 'l'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := [("Nàkú'ún ini Maria ná kata bà'a =rà", .ungrammatical), ("Nàkú'ún ini Maria ná kata bà'a =ñá", .ungrammatical)]
    readings := [("free", .ungrammatical)]
    paperFeatures := [("verb", "nakú'ún ini"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "subject")] }

def ex_40a : Datum :=
  { id := "ostrove2026_40a"
    source := ⟨"ostrove-2026", "(40a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Xíniñu'u Maria kwiin =rà iin koto xàá"
    glossedTokens := [("Xíniñu'u", "need:CONT"), ("Maria", "Maria"), ("kwiin", "buy:IRR"), ("=rà", "=he"), ("iin", "one"), ("koto", "shirt"), ("xàá", "new")]
    glossedWords := [⟨['X', 'í', 'n', 'i', 'ñ', 'u', '\'', 'u'], ['n', 'e', 'e', 'd', ':', 'C', 'O', 'N', 'T'], [⟨['X', 'í', 'n', 'i', 'ñ', 'u', '\'', 'u'], ['n', 'e', 'e', 'd', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['k', 'w', 'i', 'i', 'n'], ['b', 'u', 'y', ':', 'I', 'R', 'R'], [⟨['k', 'w', 'i', 'i', 'n'], ['b', 'u', 'y', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['i', 'i', 'n'], ['o', 'n', 'e'], [⟨['i', 'i', 'n'], ['o', 'n', 'e'], none⟩]⟩, ⟨['k', 'o', 't', 'o'], ['s', 'h', 'i', 'r', 't'], [⟨['k', 'o', 't', 'o'], ['s', 'h', 'i', 'r', 't'], none⟩]⟩, ⟨['x', 'à', 'á'], ['n', 'e', 'w'], [⟨['x', 'à', 'á'], ['n', 'e', 'w'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := [("Xíniñu'u Maria ná kwiin =rà iin koto xàá", .ungrammatical), ("Xíniñu'u Maria ná kwiin =ñá iin koto xàá", .ungrammatical)]
    readings := [("free", .ungrammatical)]
    paperFeatures := [("verb", "xiniñu'u"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "subject")] }

def ex_40b : Datum :=
  { id := "ostrove2026_40b"
    source := ⟨"ostrove-2026", "(40b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kìxǎ Maria kata bà'a =rà"
    glossedTokens := [("Kìxǎ", "start:CONT"), ("Maria", "Maria"), ("kata", "sing:IRR"), ("bà'a", "well"), ("=rà", "=he")]
    glossedWords := [⟨['K', 'ì', 'x', 'ǎ'], ['s', 't', 'a', 'r', 't', ':', 'C', 'O', 'N', 'T'], [⟨['K', 'ì', 'x', 'ǎ'], ['s', 't', 'a', 'r', 't', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['k', 'a', 't', 'a'], ['s', 'i', 'n', 'g', ':', 'I', 'R', 'R'], [⟨['k', 'a', 't', 'a'], ['s', 'i', 'n', 'g', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['b', 'à', '\'', 'a'], ['w', 'e', 'l', 'l'], [⟨['b', 'à', '\'', 'a'], ['w', 'e', 'l', 'l'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := [("Kìxǎ Maria ná kata bà'a =rà", .ungrammatical), ("Kìxǎ Maria ná kata bà'a =ñá", .ungrammatical)]
    readings := [("free", .ungrammatical)]
    paperFeatures := [("verb", "kixǎ"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "subject")] }

def ex_41a : Datum :=
  { id := "ostrove2026_41a"
    source := ⟨"ostrove-2026", "(41a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ntátu Maria bà'a ná kusi ìjǐ =ñá"
    glossedTokens := [("Ntátu", "hope:CONT"), ("Maria", "Maria"), ("bà'a", "well"), ("ná", "NÁ"), ("kusi", "sleep:IRR"), ("ìjǐ", "husband"), ("=ñá", "=her")]
    glossedWords := [⟨['N', 't', 'á', 't', 'u'], ['h', 'o', 'p', 'e', ':', 'C', 'O', 'N', 'T'], [⟨['N', 't', 'á', 't', 'u'], ['h', 'o', 'p', 'e', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['b', 'à', '\'', 'a'], ['w', 'e', 'l', 'l'], [⟨['b', 'à', '\'', 'a'], ['w', 'e', 'l', 'l'], none⟩]⟩, ⟨['n', 'á'], ['N', 'Á'], [⟨['n', 'á'], ['N', 'Á'], none⟩]⟩, ⟨['k', 'u', 's', 'i'], ['s', 'l', 'e', 'e', 'p', ':', 'I', 'R', 'R'], [⟨['k', 'u', 's', 'i'], ['s', 'l', 'e', 'e', 'p', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['ì', 'j', 'ǐ'], ['h', 'u', 's', 'b', 'a', 'n', 'd'], [⟨['ì', 'j', 'ǐ'], ['h', 'u', 's', 'b', 'a', 'n', 'd'], none⟩]⟩, ⟨['=', 'ñ', 'á'], ['=', 'h', 'e', 'r'], [⟨['ñ', 'á'], ['h', 'e', 'r'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("free", .acceptable)]
    paperFeatures := [("verb", "ntatu"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "subject"), ("embeddedSubject", "lexical")] }

def ex_41b : Datum :=
  { id := "ostrove2026_41b"
    source := ⟨"ostrove-2026", "(41b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Xíniñu'u Maria kwiin Juân iin koto xàá"
    glossedTokens := [("Xíniñu'u", "need:CONT"), ("Maria", "Maria"), ("kwiin", "buy:IRR"), ("Juân", "Juan"), ("iin", "one"), ("koto", "shirt"), ("xàá", "new")]
    glossedWords := [⟨['X', 'í', 'n', 'i', 'ñ', 'u', '\'', 'u'], ['n', 'e', 'e', 'd', ':', 'C', 'O', 'N', 'T'], [⟨['X', 'í', 'n', 'i', 'ñ', 'u', '\'', 'u'], ['n', 'e', 'e', 'd', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['k', 'w', 'i', 'i', 'n'], ['b', 'u', 'y', ':', 'I', 'R', 'R'], [⟨['k', 'w', 'i', 'i', 'n'], ['b', 'u', 'y', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['J', 'u', 'â', 'n'], ['J', 'u', 'a', 'n'], [⟨['J', 'u', 'â', 'n'], ['J', 'u', 'a', 'n'], none⟩]⟩, ⟨['i', 'i', 'n'], ['o', 'n', 'e'], [⟨['i', 'i', 'n'], ['o', 'n', 'e'], none⟩]⟩, ⟨['k', 'o', 't', 'o'], ['s', 'h', 'i', 'r', 't'], [⟨['k', 'o', 't', 'o'], ['s', 'h', 'i', 'r', 't'], none⟩]⟩, ⟨['x', 'à', 'á'], ['n', 'e', 'w'], [⟨['x', 'à', 'á'], ['n', 'e', 'w'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := [("free", .ungrammatical)]
    paperFeatures := [("verb", "xiniñu'u"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "subject"), ("embeddedSubject", "lexical")] }

def ex_20a : Datum :=
  { id := "ostrove2026_20a"
    source := ⟨"ostrove-2026", "(20a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kwa'ǎ carro ndàtǔ'un Maria nàkatsya Pedro"
    glossedTokens := [("Kwa'ǎ", "many"), ("carro", "car"), ("ndàtǔ'un", "talk:COMP"), ("Maria", "Maria"), ("nàkatsya", "wash:COMP"), ("Pedro", "Pedro")]
    glossedWords := [⟨['K', 'w', 'a', '\'', 'ǎ'], ['m', 'a', 'n', 'y'], [⟨['K', 'w', 'a', '\'', 'ǎ'], ['m', 'a', 'n', 'y'], none⟩]⟩, ⟨['c', 'a', 'r', 'r', 'o'], ['c', 'a', 'r'], [⟨['c', 'a', 'r', 'r', 'o'], ['c', 'a', 'r'], none⟩]⟩, ⟨['n', 'd', 'à', 't', 'ǔ', '\'', 'u', 'n'], ['t', 'a', 'l', 'k', ':', 'C', 'O', 'M', 'P'], [⟨['n', 'd', 'à', 't', 'ǔ', '\'', 'u', 'n'], ['t', 'a', 'l', 'k', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['n', 'à', 'k', 'a', 't', 's', 'y', 'a'], ['w', 'a', 's', 'h', ':', 'C', 'O', 'M', 'P'], [⟨['n', 'à', 'k', 'a', 't', 's', 'y', 'a'], ['w', 'a', 's', 'h', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['P', 'e', 'd', 'r', 'o'], ['P', 'e', 'd', 'r', 'o'], [⟨['P', 'e', 'd', 'r', 'o'], ['P', 'e', 'd', 'r', 'o'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ntatǔ'un"), ("clauseType", "finite"), ("diagnostic", "fronting"), ("fronting", "out")] }

def ex_20b : Datum :=
  { id := "ostrove2026_20b"
    source := ⟨"ostrove-2026", "(20b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ni'iin =nà ká'á =rà doctor kò kú'u"
    glossedTokens := [("Ni'iin", "no"), ("=nà", "=they"), ("ká'á", "think:CONT"), ("=rà", "=he"), ("doctor", "doctor"), ("kò", "NEG"), ("kú'u", "be.sick:CONT")]
    glossedWords := [⟨['N', 'i', '\'', 'i', 'i', 'n'], ['n', 'o'], [⟨['N', 'i', '\'', 'i', 'i', 'n'], ['n', 'o'], none⟩]⟩, ⟨['=', 'n', 'à'], ['=', 't', 'h', 'e', 'y'], [⟨['n', 'à'], ['t', 'h', 'e', 'y'], some '='⟩]⟩, ⟨['k', 'á', '\'', 'á'], ['t', 'h', 'i', 'n', 'k', ':', 'C', 'O', 'N', 'T'], [⟨['k', 'á', '\'', 'á'], ['t', 'h', 'i', 'n', 'k', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['d', 'o', 'c', 't', 'o', 'r'], ['d', 'o', 'c', 't', 'o', 'r'], [⟨['d', 'o', 'c', 't', 'o', 'r'], ['d', 'o', 'c', 't', 'o', 'r'], none⟩]⟩, ⟨['k', 'ò'], ['N', 'E', 'G'], [⟨['k', 'ò'], ['N', 'E', 'G'], none⟩]⟩, ⟨['k', 'ú', '\'', 'u'], ['b', 'e', '.', 's', 'i', 'c', 'k', ':', 'C', 'O', 'N', 'T'], [⟨['k', 'ú', '\'', 'u'], ['b', 'e', '.', 's', 'i', 'c', 'k', ':', 'C', 'O', 'N', 'T'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ka'án"), ("clauseType", "finite"), ("diagnostic", "fronting"), ("fronting", "out")] }

def ex_21a : Datum :=
  { id := "ostrove2026_21a"
    source := ⟨"ostrove-2026", "(21a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Káchi Maria kòjmǐ xìta xìxi =ñá"
    glossedTokens := [("Káchi", "say:COMP"), ("Maria", "Maria"), ("kòjmǐ", "four"), ("xìta", "tortilla"), ("xìxi", "eat:COMP"), ("=ñá", "=she")]
    glossedWords := [⟨['K', 'á', 'c', 'h', 'i'], ['s', 'a', 'y', ':', 'C', 'O', 'M', 'P'], [⟨['K', 'á', 'c', 'h', 'i'], ['s', 'a', 'y', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['k', 'ò', 'j', 'm', 'ǐ'], ['f', 'o', 'u', 'r'], [⟨['k', 'ò', 'j', 'm', 'ǐ'], ['f', 'o', 'u', 'r'], none⟩]⟩, ⟨['x', 'ì', 't', 'a'], ['t', 'o', 'r', 't', 'i', 'l', 'l', 'a'], [⟨['x', 'ì', 't', 'a'], ['t', 'o', 'r', 't', 'i', 'l', 'l', 'a'], none⟩]⟩, ⟨['x', 'ì', 'x', 'i'], ['e', 'a', 't', ':', 'C', 'O', 'M', 'P'], [⟨['x', 'ì', 'x', 'i'], ['e', 'a', 't', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['=', 'ñ', 'á'], ['=', 's', 'h', 'e'], [⟨['ñ', 'á'], ['s', 'h', 'e'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "káchi"), ("clauseType", "finite"), ("diagnostic", "fronting"), ("fronting", "within")] }

def ex_21b : Datum :=
  { id := "ostrove2026_21b"
    source := ⟨"ostrove-2026", "(21b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kúntàà ini =ì ntsikû mí tsǐnà ntá'yi"
    glossedTokens := [("Kúntàà", "believe:CONT"), ("ini", "in"), ("=ì", "=I"), ("ntsikû", "all"), ("mí", "the"), ("tsǐnà", "dog"), ("ntá'yi", "cry:CONT")]
    glossedWords := [⟨['K', 'ú', 'n', 't', 'à', 'à'], ['b', 'e', 'l', 'i', 'e', 'v', 'e', ':', 'C', 'O', 'N', 'T'], [⟨['K', 'ú', 'n', 't', 'à', 'à'], ['b', 'e', 'l', 'i', 'e', 'v', 'e', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['i', 'n', 'i'], ['i', 'n'], [⟨['i', 'n', 'i'], ['i', 'n'], none⟩]⟩, ⟨['=', 'ì'], ['=', 'I'], [⟨['ì'], ['I'], some '='⟩]⟩, ⟨['n', 't', 's', 'i', 'k', 'û'], ['a', 'l', 'l'], [⟨['n', 't', 's', 'i', 'k', 'û'], ['a', 'l', 'l'], none⟩]⟩, ⟨['m', 'í'], ['t', 'h', 'e'], [⟨['m', 'í'], ['t', 'h', 'e'], none⟩]⟩, ⟨['t', 's', 'ǐ', 'n', 'à'], ['d', 'o', 'g'], [⟨['t', 's', 'ǐ', 'n', 'à'], ['d', 'o', 'g'], none⟩]⟩, ⟨['n', 't', 'á', '\'', 'y', 'i'], ['c', 'r', 'y', ':', 'C', 'O', 'N', 'T'], [⟨['n', 't', 'á', '\'', 'y', 'i'], ['c', 'r', 'y', ':', 'C', 'O', 'N', 'T'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "kuntàà ini"), ("clauseType", "finite"), ("diagnostic", "fronting"), ("fronting", "within")] }

def ex_22a : Datum :=
  { id := "ostrove2026_22a"
    source := ⟨"ostrove-2026", "(22a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ntsi'i carro ntátu Pedro nakatsya =rà"
    glossedTokens := [("Ntsi'i", "every"), ("carro", "car"), ("ntátu", "hope:CONT"), ("Pedro", "Pedro"), ("nakatsya", "wash:IRR"), ("=rà", "=he")]
    glossedWords := [⟨['N', 't', 's', 'i', '\'', 'i'], ['e', 'v', 'e', 'r', 'y'], [⟨['N', 't', 's', 'i', '\'', 'i'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['c', 'a', 'r', 'r', 'o'], ['c', 'a', 'r'], [⟨['c', 'a', 'r', 'r', 'o'], ['c', 'a', 'r'], none⟩]⟩, ⟨['n', 't', 'á', 't', 'u'], ['h', 'o', 'p', 'e', ':', 'C', 'O', 'N', 'T'], [⟨['n', 't', 'á', 't', 'u'], ['h', 'o', 'p', 'e', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['P', 'e', 'd', 'r', 'o'], ['P', 'e', 'd', 'r', 'o'], [⟨['P', 'e', 'd', 'r', 'o'], ['P', 'e', 'd', 'r', 'o'], none⟩]⟩, ⟨['n', 'a', 'k', 'a', 't', 's', 'y', 'a'], ['w', 'a', 's', 'h', ':', 'I', 'R', 'R'], [⟨['n', 'a', 'k', 'a', 't', 's', 'y', 'a'], ['w', 'a', 's', 'h', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ntatu"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "fronting"), ("fronting", "out")] }

def ex_22b : Datum :=
  { id := "ostrove2026_22b"
    source := ⟨"ostrove-2026", "(22b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kwa'ǎ yà'a í'ní chìkàà ini Juân kaxi =rà"
    glossedTokens := [("Kwa'ǎ", "many"), ("yà'a", "chili"), ("í'ní", "hot"), ("chìkàà", "put.in:COMP"), ("ini", "in"), ("Juân", "Juan"), ("kaxi", "eat:IRR"), ("=rà", "=he")]
    glossedWords := [⟨['K', 'w', 'a', '\'', 'ǎ'], ['m', 'a', 'n', 'y'], [⟨['K', 'w', 'a', '\'', 'ǎ'], ['m', 'a', 'n', 'y'], none⟩]⟩, ⟨['y', 'à', '\'', 'a'], ['c', 'h', 'i', 'l', 'i'], [⟨['y', 'à', '\'', 'a'], ['c', 'h', 'i', 'l', 'i'], none⟩]⟩, ⟨['í', '\'', 'n', 'í'], ['h', 'o', 't'], [⟨['í', '\'', 'n', 'í'], ['h', 'o', 't'], none⟩]⟩, ⟨['c', 'h', 'ì', 'k', 'à', 'à'], ['p', 'u', 't', '.', 'i', 'n', ':', 'C', 'O', 'M', 'P'], [⟨['c', 'h', 'ì', 'k', 'à', 'à'], ['p', 'u', 't', '.', 'i', 'n', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['i', 'n', 'i'], ['i', 'n'], [⟨['i', 'n', 'i'], ['i', 'n'], none⟩]⟩, ⟨['J', 'u', 'â', 'n'], ['J', 'u', 'a', 'n'], [⟨['J', 'u', 'â', 'n'], ['J', 'u', 'a', 'n'], none⟩]⟩, ⟨['k', 'a', 'x', 'i'], ['e', 'a', 't', ':', 'I', 'R', 'R'], [⟨['k', 'a', 'x', 'i'], ['e', 'a', 't', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "chikàà ini"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "fronting"), ("fronting", "out")] }

def ex_23a : Datum :=
  { id := "ostrove2026_23a"
    source := ⟨"ostrove-2026", "(23a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ntátu =rà lo'o ntsi'i ña'á koná =rà"
    glossedTokens := [("Ntátu", "hope:CONT"), ("=rà", "=he"), ("lo'o", "little"), ("ntsi'i", "every"), ("ña'á", "thing"), ("koná", "open:IRR"), ("=rà", "=he")]
    glossedWords := [⟨['N', 't', 'á', 't', 'u'], ['h', 'o', 'p', 'e', ':', 'C', 'O', 'N', 'T'], [⟨['N', 't', 'á', 't', 'u'], ['h', 'o', 'p', 'e', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['l', 'o', '\'', 'o'], ['l', 'i', 't', 't', 'l', 'e'], [⟨['l', 'o', '\'', 'o'], ['l', 'i', 't', 't', 'l', 'e'], none⟩]⟩, ⟨['n', 't', 's', 'i', '\'', 'i'], ['e', 'v', 'e', 'r', 'y'], [⟨['n', 't', 's', 'i', '\'', 'i'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['ñ', 'a', '\'', 'á'], ['t', 'h', 'i', 'n', 'g'], [⟨['ñ', 'a', '\'', 'á'], ['t', 'h', 'i', 'n', 'g'], none⟩]⟩, ⟨['k', 'o', 'n', 'á'], ['o', 'p', 'e', 'n', ':', 'I', 'R', 'R'], [⟨['k', 'o', 'n', 'á'], ['o', 'p', 'e', 'n', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ntatu"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "fronting"), ("fronting", "within")] }

def ex_23b : Datum :=
  { id := "ostrove2026_23b"
    source := ⟨"ostrove-2026", "(23b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Chìkàà ini Juân kwa'ǎ yà'ǎ í'ní kaxi =rà"
    glossedTokens := [("Chìkàà", "put.in:COMP"), ("ini", "in"), ("Juân", "Juan"), ("kwa'ǎ", "many"), ("yà'ǎ", "chili"), ("í'ní", "hot"), ("kaxi", "eat:IRR"), ("=rà", "=he")]
    glossedWords := [⟨['C', 'h', 'ì', 'k', 'à', 'à'], ['p', 'u', 't', '.', 'i', 'n', ':', 'C', 'O', 'M', 'P'], [⟨['C', 'h', 'ì', 'k', 'à', 'à'], ['p', 'u', 't', '.', 'i', 'n', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['i', 'n', 'i'], ['i', 'n'], [⟨['i', 'n', 'i'], ['i', 'n'], none⟩]⟩, ⟨['J', 'u', 'â', 'n'], ['J', 'u', 'a', 'n'], [⟨['J', 'u', 'â', 'n'], ['J', 'u', 'a', 'n'], none⟩]⟩, ⟨['k', 'w', 'a', '\'', 'ǎ'], ['m', 'a', 'n', 'y'], [⟨['k', 'w', 'a', '\'', 'ǎ'], ['m', 'a', 'n', 'y'], none⟩]⟩, ⟨['y', 'à', '\'', 'ǎ'], ['c', 'h', 'i', 'l', 'i'], [⟨['y', 'à', '\'', 'ǎ'], ['c', 'h', 'i', 'l', 'i'], none⟩]⟩, ⟨['í', '\'', 'n', 'í'], ['h', 'o', 't'], [⟨['í', '\'', 'n', 'í'], ['h', 'o', 't'], none⟩]⟩, ⟨['k', 'a', 'x', 'i'], ['e', 'a', 't', ':', 'I', 'R', 'R'], [⟨['k', 'a', 'x', 'i'], ['e', 'a', 't', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "chikàà ini"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "fronting"), ("fronting", "within")] }

def ex_24a : Datum :=
  { id := "ostrove2026_24a"
    source := ⟨"ostrove-2026", "(24a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kwa'ǎ ko'ǒ nàntǒso Mateo nakatsya =rà"
    glossedTokens := [("Kwa'ǎ", "many"), ("ko'ǒ", "plate"), ("nàntǒso", "forget:COMP"), ("Mateo", "Mateo"), ("nakatsya", "wash:IRR"), ("=rà", "=he")]
    glossedWords := [⟨['K', 'w', 'a', '\'', 'ǎ'], ['m', 'a', 'n', 'y'], [⟨['K', 'w', 'a', '\'', 'ǎ'], ['m', 'a', 'n', 'y'], none⟩]⟩, ⟨['k', 'o', '\'', 'ǒ'], ['p', 'l', 'a', 't', 'e'], [⟨['k', 'o', '\'', 'ǒ'], ['p', 'l', 'a', 't', 'e'], none⟩]⟩, ⟨['n', 'à', 'n', 't', 'ǒ', 's', 'o'], ['f', 'o', 'r', 'g', 'e', 't', ':', 'C', 'O', 'M', 'P'], [⟨['n', 'à', 'n', 't', 'ǒ', 's', 'o'], ['f', 'o', 'r', 'g', 'e', 't', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['M', 'a', 't', 'e', 'o'], ['M', 'a', 't', 'e', 'o'], [⟨['M', 'a', 't', 'e', 'o'], ['M', 'a', 't', 'e', 'o'], none⟩]⟩, ⟨['n', 'a', 'k', 'a', 't', 's', 'y', 'a'], ['w', 'a', 's', 'h', ':', 'I', 'R', 'R'], [⟨['n', 'a', 'k', 'a', 't', 's', 'y', 'a'], ['w', 'a', 's', 'h', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "nantǒso"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "fronting"), ("fronting", "out")] }

def ex_24b : Datum :=
  { id := "ostrove2026_24b"
    source := ⟨"ostrove-2026", "(24b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kòjmǐ yà'ǎ ntùkú Maria kaxi =ñá"
    glossedTokens := [("Kòjmǐ", "four"), ("yà'ǎ", "chili"), ("ntùkú", "try:COMP"), ("Maria", "Maria"), ("kaxi", "eat:IRR"), ("=ñá", "=she")]
    glossedWords := [⟨['K', 'ò', 'j', 'm', 'ǐ'], ['f', 'o', 'u', 'r'], [⟨['K', 'ò', 'j', 'm', 'ǐ'], ['f', 'o', 'u', 'r'], none⟩]⟩, ⟨['y', 'à', '\'', 'ǎ'], ['c', 'h', 'i', 'l', 'i'], [⟨['y', 'à', '\'', 'ǎ'], ['c', 'h', 'i', 'l', 'i'], none⟩]⟩, ⟨['n', 't', 'ù', 'k', 'ú'], ['t', 'r', 'y', ':', 'C', 'O', 'M', 'P'], [⟨['n', 't', 'ù', 'k', 'ú'], ['t', 'r', 'y', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['k', 'a', 'x', 'i'], ['e', 'a', 't', ':', 'I', 'R', 'R'], [⟨['k', 'a', 'x', 'i'], ['e', 'a', 't', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'ñ', 'á'], ['=', 's', 'h', 'e'], [⟨['ñ', 'á'], ['s', 'h', 'e'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ntukú"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "fronting"), ("fronting", "out")] }

def ex_25a : Datum :=
  { id := "ostrove2026_25a"
    source := ⟨"ostrove-2026", "(25a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Nàntǒso Mateo kwa'ǎ ko'ǒ nakatsya =rà"
    glossedTokens := [("Nàntǒso", "forget:COMP"), ("Mateo", "Mateo"), ("kwa'ǎ", "many"), ("ko'ǒ", "plate"), ("nakatsya", "wash:IRR"), ("=rà", "=he")]
    glossedWords := [⟨['N', 'à', 'n', 't', 'ǒ', 's', 'o'], ['f', 'o', 'r', 'g', 'e', 't', ':', 'C', 'O', 'M', 'P'], [⟨['N', 'à', 'n', 't', 'ǒ', 's', 'o'], ['f', 'o', 'r', 'g', 'e', 't', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['M', 'a', 't', 'e', 'o'], ['M', 'a', 't', 'e', 'o'], [⟨['M', 'a', 't', 'e', 'o'], ['M', 'a', 't', 'e', 'o'], none⟩]⟩, ⟨['k', 'w', 'a', '\'', 'ǎ'], ['m', 'a', 'n', 'y'], [⟨['k', 'w', 'a', '\'', 'ǎ'], ['m', 'a', 'n', 'y'], none⟩]⟩, ⟨['k', 'o', '\'', 'ǒ'], ['p', 'l', 'a', 't', 'e'], [⟨['k', 'o', '\'', 'ǒ'], ['p', 'l', 'a', 't', 'e'], none⟩]⟩, ⟨['n', 'a', 'k', 'a', 't', 's', 'y', 'a'], ['w', 'a', 's', 'h', ':', 'I', 'R', 'R'], [⟨['n', 'a', 'k', 'a', 't', 's', 'y', 'a'], ['w', 'a', 's', 'h', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "nantǒso"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "fronting"), ("fronting", "within")] }

def ex_25b : Datum :=
  { id := "ostrove2026_25b"
    source := ⟨"ostrove-2026", "(25b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ntùkú Maria kòjmǐ yà'ǎ kaxi =ñá"
    glossedTokens := [("Ntùkú", "try:COMP"), ("Maria", "Maria"), ("kòjmǐ", "four"), ("yà'ǎ", "chili"), ("kaxi", "eat:IRR"), ("=ñá", "=she")]
    glossedWords := [⟨['N', 't', 'ù', 'k', 'ú'], ['t', 'r', 'y', ':', 'C', 'O', 'M', 'P'], [⟨['N', 't', 'ù', 'k', 'ú'], ['t', 'r', 'y', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['k', 'ò', 'j', 'm', 'ǐ'], ['f', 'o', 'u', 'r'], [⟨['k', 'ò', 'j', 'm', 'ǐ'], ['f', 'o', 'u', 'r'], none⟩]⟩, ⟨['y', 'à', '\'', 'ǎ'], ['c', 'h', 'i', 'l', 'i'], [⟨['y', 'à', '\'', 'ǎ'], ['c', 'h', 'i', 'l', 'i'], none⟩]⟩, ⟨['k', 'a', 'x', 'i'], ['e', 'a', 't', ':', 'I', 'R', 'R'], [⟨['k', 'a', 'x', 'i'], ['e', 'a', 't', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'ñ', 'á'], ['=', 's', 'h', 'e'], [⟨['ñ', 'á'], ['s', 'h', 'e'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ntukú"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "fronting"), ("fronting", "within")] }

def ex_109 : Datum :=
  { id := "ostrove2026_109"
    source := ⟨"ostrove-2026", "(109)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Iin dragón kôni =rà tsyàja ka'ani =rà"
    glossedTokens := [("Iin", "one"), ("dragón", "dragon"), ("kôni", "want:CONT"), ("=rà", "=he"), ("tsyàja", "man"), ("ka'ani", "kill:IRR"), ("=rà", "=he")]
    glossedWords := [⟨['I', 'i', 'n'], ['o', 'n', 'e'], [⟨['I', 'i', 'n'], ['o', 'n', 'e'], none⟩]⟩, ⟨['d', 'r', 'a', 'g', 'ó', 'n'], ['d', 'r', 'a', 'g', 'o', 'n'], [⟨['d', 'r', 'a', 'g', 'ó', 'n'], ['d', 'r', 'a', 'g', 'o', 'n'], none⟩]⟩, ⟨['k', 'ô', 'n', 'i'], ['w', 'a', 'n', 't', ':', 'C', 'O', 'N', 'T'], [⟨['k', 'ô', 'n', 'i'], ['w', 'a', 'n', 't', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['t', 's', 'y', 'à', 'j', 'a'], ['m', 'a', 'n'], [⟨['t', 's', 'y', 'à', 'j', 'a'], ['m', 'a', 'n'], none⟩]⟩, ⟨['k', 'a', '\'', 'a', 'n', 'i'], ['k', 'i', 'l', 'l', ':', 'I', 'R', 'R'], [⟨['k', 'a', '\'', 'a', 'n', 'i'], ['k', 'i', 'l', 'l', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "kòni"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "fronting"), ("fronting", "out")] }

def ex_30a : Datum :=
  { id := "ostrove2026_30a"
    source := ⟨"ostrove-2026", "(30a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Káchi Julia bà'a kwé'e xìjnǐ =ñá, sǎ =ti Mateo =ba"
    glossedTokens := [("Káchi", "say:COMP"), ("Julia", "Julia"), ("bà'a", "good"), ("kwé'e", "very"), ("xìjnǐ", "head"), ("=ñá", "=she"), ("sǎ", "so"), ("=ti", "=too"), ("Mateo", "Mateo"), ("=ba", "=EMPH")]
    glossedWords := [⟨['K', 'á', 'c', 'h', 'i'], ['s', 'a', 'y', ':', 'C', 'O', 'M', 'P'], [⟨['K', 'á', 'c', 'h', 'i'], ['s', 'a', 'y', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['J', 'u', 'l', 'i', 'a'], ['J', 'u', 'l', 'i', 'a'], [⟨['J', 'u', 'l', 'i', 'a'], ['J', 'u', 'l', 'i', 'a'], none⟩]⟩, ⟨['b', 'à', '\'', 'a'], ['g', 'o', 'o', 'd'], [⟨['b', 'à', '\'', 'a'], ['g', 'o', 'o', 'd'], none⟩]⟩, ⟨['k', 'w', 'é', '\'', 'e'], ['v', 'e', 'r', 'y'], [⟨['k', 'w', 'é', '\'', 'e'], ['v', 'e', 'r', 'y'], none⟩]⟩, ⟨['x', 'ì', 'j', 'n', 'ǐ'], ['h', 'e', 'a', 'd'], [⟨['x', 'ì', 'j', 'n', 'ǐ'], ['h', 'e', 'a', 'd'], none⟩]⟩, ⟨['=', 'ñ', 'á'], ['=', 's', 'h', 'e'], [⟨['ñ', 'á'], ['s', 'h', 'e'], some '='⟩]⟩, ⟨['s', 'ǎ'], ['s', 'o'], [⟨['s', 'ǎ'], ['s', 'o'], none⟩]⟩, ⟨['=', 't', 'i'], ['=', 't', 'o', 'o'], [⟨['t', 'i'], ['t', 'o', 'o'], some '='⟩]⟩, ⟨['M', 'a', 't', 'e', 'o'], ['M', 'a', 't', 'e', 'o'], [⟨['M', 'a', 't', 'e', 'o'], ['M', 'a', 't', 'e', 'o'], none⟩]⟩, ⟨['=', 'b', 'a'], ['=', 'E', 'M', 'P', 'H'], [⟨['b', 'a'], ['E', 'M', 'P', 'H'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("sloppy", .acceptable), ("strict", .acceptable)]
    paperFeatures := [("verb", "káchi"), ("clauseType", "finite"), ("diagnostic", "ellipsis")] }

def ex_30b : Datum :=
  { id := "ostrove2026_30b"
    source := ⟨"ostrove-2026", "(30b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kà'án Juan ni'í xìnu =rà, sǎ =ti Sergio =ba"
    glossedTokens := [("Kà'án", "think:COMP"), ("Juan", "Juan"), ("ni'í", "fast"), ("xìnu", "run:COMP"), ("=rà", "=he"), ("sǎ", "so"), ("=ti", "=too"), ("Sergio", "Sergio"), ("=ba", "=EMPH")]
    glossedWords := [⟨['K', 'à', '\'', 'á', 'n'], ['t', 'h', 'i', 'n', 'k', ':', 'C', 'O', 'M', 'P'], [⟨['K', 'à', '\'', 'á', 'n'], ['t', 'h', 'i', 'n', 'k', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['J', 'u', 'a', 'n'], ['J', 'u', 'a', 'n'], [⟨['J', 'u', 'a', 'n'], ['J', 'u', 'a', 'n'], none⟩]⟩, ⟨['n', 'i', '\'', 'í'], ['f', 'a', 's', 't'], [⟨['n', 'i', '\'', 'í'], ['f', 'a', 's', 't'], none⟩]⟩, ⟨['x', 'ì', 'n', 'u'], ['r', 'u', 'n', ':', 'C', 'O', 'M', 'P'], [⟨['x', 'ì', 'n', 'u'], ['r', 'u', 'n', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['s', 'ǎ'], ['s', 'o'], [⟨['s', 'ǎ'], ['s', 'o'], none⟩]⟩, ⟨['=', 't', 'i'], ['=', 't', 'o', 'o'], [⟨['t', 'i'], ['t', 'o', 'o'], some '='⟩]⟩, ⟨['S', 'e', 'r', 'g', 'i', 'o'], ['S', 'e', 'r', 'g', 'i', 'o'], [⟨['S', 'e', 'r', 'g', 'i', 'o'], ['S', 'e', 'r', 'g', 'i', 'o'], none⟩]⟩, ⟨['=', 'b', 'a'], ['=', 'E', 'M', 'P', 'H'], [⟨['b', 'a'], ['E', 'M', 'P', 'H'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("sloppy", .acceptable), ("strict", .acceptable)]
    paperFeatures := [("verb", "ka'án"), ("clauseType", "finite"), ("diagnostic", "ellipsis")] }

def ex_32a : Datum :=
  { id := "ostrove2026_32a"
    source := ⟨"ostrove-2026", "(32a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kôni Marco keba'a =rà carrera, sǎ =ti Maria =ba"
    glossedTokens := [("Kôni", "want:CONT"), ("Marco", "Marco"), ("keba'a", "win:IRR"), ("=rà", "=he"), ("carrera", "race"), ("sǎ", "so"), ("=ti", "=too"), ("Maria", "Maria"), ("=ba", "=EMPH")]
    glossedWords := [⟨['K', 'ô', 'n', 'i'], ['w', 'a', 'n', 't', ':', 'C', 'O', 'N', 'T'], [⟨['K', 'ô', 'n', 'i'], ['w', 'a', 'n', 't', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['M', 'a', 'r', 'c', 'o'], ['M', 'a', 'r', 'c', 'o'], [⟨['M', 'a', 'r', 'c', 'o'], ['M', 'a', 'r', 'c', 'o'], none⟩]⟩, ⟨['k', 'e', 'b', 'a', '\'', 'a'], ['w', 'i', 'n', ':', 'I', 'R', 'R'], [⟨['k', 'e', 'b', 'a', '\'', 'a'], ['w', 'i', 'n', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['c', 'a', 'r', 'r', 'e', 'r', 'a'], ['r', 'a', 'c', 'e'], [⟨['c', 'a', 'r', 'r', 'e', 'r', 'a'], ['r', 'a', 'c', 'e'], none⟩]⟩, ⟨['s', 'ǎ'], ['s', 'o'], [⟨['s', 'ǎ'], ['s', 'o'], none⟩]⟩, ⟨['=', 't', 'i'], ['=', 't', 'o', 'o'], [⟨['t', 'i'], ['t', 'o', 'o'], some '='⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['=', 'b', 'a'], ['=', 'E', 'M', 'P', 'H'], [⟨['b', 'a'], ['E', 'M', 'P', 'H'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Maria is not in the race, but she wants Marco to win."
    judgment := .acceptable
    contrasts := []
    readings := [("sloppy", .acceptable), ("strict", .acceptable)]
    paperFeatures := [("verb", "kòni"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "ellipsis")] }

def ex_32b : Datum :=
  { id := "ostrove2026_32b"
    source := ⟨"ostrove-2026", "(32b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ntátu Raúl ku'ún =rà Olímpico, sǎ =ti nána =rà =ba"
    glossedTokens := [("Ntátu", "hope:CONT"), ("Raúl", "Raul"), ("ku'ún", "go:IRR"), ("=rà", "=he"), ("Olímpico", "Olympics"), ("sǎ", "so"), ("=ti", "=too"), ("nána", "mother"), ("=rà", "=his"), ("=ba", "=EMPH")]
    glossedWords := [⟨['N', 't', 'á', 't', 'u'], ['h', 'o', 'p', 'e', ':', 'C', 'O', 'N', 'T'], [⟨['N', 't', 'á', 't', 'u'], ['h', 'o', 'p', 'e', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['R', 'a', 'ú', 'l'], ['R', 'a', 'u', 'l'], [⟨['R', 'a', 'ú', 'l'], ['R', 'a', 'u', 'l'], none⟩]⟩, ⟨['k', 'u', '\'', 'ú', 'n'], ['g', 'o', ':', 'I', 'R', 'R'], [⟨['k', 'u', '\'', 'ú', 'n'], ['g', 'o', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['O', 'l', 'í', 'm', 'p', 'i', 'c', 'o'], ['O', 'l', 'y', 'm', 'p', 'i', 'c', 's'], [⟨['O', 'l', 'í', 'm', 'p', 'i', 'c', 'o'], ['O', 'l', 'y', 'm', 'p', 'i', 'c', 's'], none⟩]⟩, ⟨['s', 'ǎ'], ['s', 'o'], [⟨['s', 'ǎ'], ['s', 'o'], none⟩]⟩, ⟨['=', 't', 'i'], ['=', 't', 'o', 'o'], [⟨['t', 'i'], ['t', 'o', 'o'], some '='⟩]⟩, ⟨['n', 'á', 'n', 'a'], ['m', 'o', 't', 'h', 'e', 'r'], [⟨['n', 'á', 'n', 'a'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'i', 's'], [⟨['r', 'à'], ['h', 'i', 's'], some '='⟩]⟩, ⟨['=', 'b', 'a'], ['=', 'E', 'M', 'P', 'H'], [⟨['b', 'a'], ['E', 'M', 'P', 'H'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Raul's mother is not an athlete, but she hopes her son will go to the Olympics."
    judgment := .acceptable
    contrasts := []
    readings := [("sloppy", .acceptable), ("strict", .acceptable)]
    paperFeatures := [("verb", "ntatu"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "ellipsis")] }

def ex_33a : Datum :=
  { id := "ostrove2026_33a"
    source := ⟨"ostrove-2026", "(33a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Xînì Ana ixutsya =ñá, sǎ =ti Laura =ba"
    glossedTokens := [("Xînì", "know:CONT"), ("Ana", "Ana"), ("ixutsya", "swim:IRR"), ("=ñá", "=she"), ("sǎ", "so"), ("=ti", "=too"), ("Laura", "Laura"), ("=ba", "=EMPH")]
    glossedWords := [⟨['X', 'î', 'n', 'ì'], ['k', 'n', 'o', 'w', ':', 'C', 'O', 'N', 'T'], [⟨['X', 'î', 'n', 'ì'], ['k', 'n', 'o', 'w', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['A', 'n', 'a'], ['A', 'n', 'a'], [⟨['A', 'n', 'a'], ['A', 'n', 'a'], none⟩]⟩, ⟨['i', 'x', 'u', 't', 's', 'y', 'a'], ['s', 'w', 'i', 'm', ':', 'I', 'R', 'R'], [⟨['i', 'x', 'u', 't', 's', 'y', 'a'], ['s', 'w', 'i', 'm', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'ñ', 'á'], ['=', 's', 'h', 'e'], [⟨['ñ', 'á'], ['s', 'h', 'e'], some '='⟩]⟩, ⟨['s', 'ǎ'], ['s', 'o'], [⟨['s', 'ǎ'], ['s', 'o'], none⟩]⟩, ⟨['=', 't', 'i'], ['=', 't', 'o', 'o'], [⟨['t', 'i'], ['t', 'o', 'o'], some '='⟩]⟩, ⟨['L', 'a', 'u', 'r', 'a'], ['L', 'a', 'u', 'r', 'a'], [⟨['L', 'a', 'u', 'r', 'a'], ['L', 'a', 'u', 'r', 'a'], none⟩]⟩, ⟨['=', 'b', 'a'], ['=', 'E', 'M', 'P', 'H'], [⟨['b', 'a'], ['E', 'M', 'P', 'H'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Laura cannot swim, but she knows that Ana can."
    judgment := .acceptable
    contrasts := []
    readings := [("sloppy", .acceptable), ("strict", .ungrammatical)]
    paperFeatures := [("verb", "kònì"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "ellipsis")] }

def ex_33b : Datum :=
  { id := "ostrove2026_33b"
    source := ⟨"ostrove-2026", "(33b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Nàkú'ún ini Maria ku'ún =ñá tienda, sǎ =ti Juân =ba"
    glossedTokens := [("Nàkú'ún", "remember:COMP"), ("ini", "in"), ("Maria", "Maria"), ("ku'ún", "go:IRR"), ("=ñá", "=she"), ("tienda", "store"), ("sǎ", "so"), ("=ti", "=too"), ("Juân", "Juan"), ("=ba", "=EMPH")]
    glossedWords := [⟨['N', 'à', 'k', 'ú', '\'', 'ú', 'n'], ['r', 'e', 'm', 'e', 'm', 'b', 'e', 'r', ':', 'C', 'O', 'M', 'P'], [⟨['N', 'à', 'k', 'ú', '\'', 'ú', 'n'], ['r', 'e', 'm', 'e', 'm', 'b', 'e', 'r', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['i', 'n', 'i'], ['i', 'n'], [⟨['i', 'n', 'i'], ['i', 'n'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['k', 'u', '\'', 'ú', 'n'], ['g', 'o', ':', 'I', 'R', 'R'], [⟨['k', 'u', '\'', 'ú', 'n'], ['g', 'o', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'ñ', 'á'], ['=', 's', 'h', 'e'], [⟨['ñ', 'á'], ['s', 'h', 'e'], some '='⟩]⟩, ⟨['t', 'i', 'e', 'n', 'd', 'a'], ['s', 't', 'o', 'r', 'e'], [⟨['t', 'i', 'e', 'n', 'd', 'a'], ['s', 't', 'o', 'r', 'e'], none⟩]⟩, ⟨['s', 'ǎ'], ['s', 'o'], [⟨['s', 'ǎ'], ['s', 'o'], none⟩]⟩, ⟨['=', 't', 'i'], ['=', 't', 'o', 'o'], [⟨['t', 'i'], ['t', 'o', 'o'], some '='⟩]⟩, ⟨['J', 'u', 'â', 'n'], ['J', 'u', 'a', 'n'], [⟨['J', 'u', 'â', 'n'], ['J', 'u', 'a', 'n'], none⟩]⟩, ⟨['=', 'b', 'a'], ['=', 'E', 'M', 'P', 'H'], [⟨['b', 'a'], ['E', 'M', 'P', 'H'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Juan did not go to the store, but he remembers Maria did."
    judgment := .acceptable
    contrasts := []
    readings := [("sloppy", .acceptable), ("strict", .ungrammatical)]
    paperFeatures := [("verb", "nakú'ún ini"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "ellipsis")] }

def ex_37a : Datum :=
  { id := "ostrove2026_37a"
    source := ⟨"ostrove-2026", "(37a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Nàntǒso =rà patrón nakitá'àn =nà kâ uxi iin"
    glossedTokens := [("Nàntǒso", "forget:COMP"), ("=rà", "=he"), ("patrón", "boss"), ("nakitá'àn", "meet:IRR"), ("=nà", "=they"), ("kâ", "hour"), ("uxi", "ten"), ("iin", "one")]
    glossedWords := [⟨['N', 'à', 'n', 't', 'ǒ', 's', 'o'], ['f', 'o', 'r', 'g', 'e', 't', ':', 'C', 'O', 'M', 'P'], [⟨['N', 'à', 'n', 't', 'ǒ', 's', 'o'], ['f', 'o', 'r', 'g', 'e', 't', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['p', 'a', 't', 'r', 'ó', 'n'], ['b', 'o', 's', 's'], [⟨['p', 'a', 't', 'r', 'ó', 'n'], ['b', 'o', 's', 's'], none⟩]⟩, ⟨['n', 'a', 'k', 'i', 't', 'á', '\'', 'à', 'n'], ['m', 'e', 'e', 't', ':', 'I', 'R', 'R'], [⟨['n', 'a', 'k', 'i', 't', 'á', '\'', 'à', 'n'], ['m', 'e', 'e', 't', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'n', 'à'], ['=', 't', 'h', 'e', 'y'], [⟨['n', 'à'], ['t', 'h', 'e', 'y'], some '='⟩]⟩, ⟨['k', 'â'], ['h', 'o', 'u', 'r'], [⟨['k', 'â'], ['h', 'o', 'u', 'r'], none⟩]⟩, ⟨['u', 'x', 'i'], ['t', 'e', 'n'], [⟨['u', 'x', 'i'], ['t', 'e', 'n'], none⟩]⟩, ⟨['i', 'i', 'n'], ['o', 'n', 'e'], [⟨['i', 'i', 'n'], ['o', 'n', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "nantǒso"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "partialControl")] }

def ex_37b : Datum :=
  { id := "ostrove2026_37b"
    source := ⟨"ostrove-2026", "(37b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Xíniñu'u Maria ku'ún ntíbi =nà bìjkǒ"
    glossedTokens := [("Xíniñu'u", "need:CONT"), ("Maria", "Maria"), ("ku'ún", "go:IRR"), ("ntíbi", "together"), ("=nà", "=they"), ("bìjkǒ", "party")]
    glossedWords := [⟨['X', 'í', 'n', 'i', 'ñ', 'u', '\'', 'u'], ['n', 'e', 'e', 'd', ':', 'C', 'O', 'N', 'T'], [⟨['X', 'í', 'n', 'i', 'ñ', 'u', '\'', 'u'], ['n', 'e', 'e', 'd', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['k', 'u', '\'', 'ú', 'n'], ['g', 'o', ':', 'I', 'R', 'R'], [⟨['k', 'u', '\'', 'ú', 'n'], ['g', 'o', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['n', 't', 'í', 'b', 'i'], ['t', 'o', 'g', 'e', 't', 'h', 'e', 'r'], [⟨['n', 't', 'í', 'b', 'i'], ['t', 'o', 'g', 'e', 't', 'h', 'e', 'r'], none⟩]⟩, ⟨['=', 'n', 'à'], ['=', 't', 'h', 'e', 'y'], [⟨['n', 'à'], ['t', 'h', 'e', 'y'], some '='⟩]⟩, ⟨['b', 'ì', 'j', 'k', 'ǒ'], ['p', 'a', 'r', 't', 'y'], [⟨['b', 'ì', 'j', 'k', 'ǒ'], ['p', 'a', 'r', 't', 'y'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "xiniñu'u"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "partialControl")] }

def ex_43a : Datum :=
  { id := "ostrove2026_43a"
    source := ⟨"ostrove-2026", "(43a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kôni nána Julio ná keba'a =rà mí carrera"
    glossedTokens := [("Kôni", "want:CONT"), ("nána", "mother"), ("Julio", "Julio"), ("ná", "NÁ"), ("keba'a", "win:IRR"), ("=rà", "=he"), ("mí", "the"), ("carrera", "race")]
    glossedWords := [⟨['K', 'ô', 'n', 'i'], ['w', 'a', 'n', 't', ':', 'C', 'O', 'N', 'T'], [⟨['K', 'ô', 'n', 'i'], ['w', 'a', 'n', 't', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['n', 'á', 'n', 'a'], ['m', 'o', 't', 'h', 'e', 'r'], [⟨['n', 'á', 'n', 'a'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩]⟩, ⟨['J', 'u', 'l', 'i', 'o'], ['J', 'u', 'l', 'i', 'o'], [⟨['J', 'u', 'l', 'i', 'o'], ['J', 'u', 'l', 'i', 'o'], none⟩]⟩, ⟨['n', 'á'], ['N', 'Á'], [⟨['n', 'á'], ['N', 'Á'], none⟩]⟩, ⟨['k', 'e', 'b', 'a', '\'', 'a'], ['w', 'i', 'n', ':', 'I', 'R', 'R'], [⟨['k', 'e', 'b', 'a', '\'', 'a'], ['w', 'i', 'n', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['m', 'í'], ['t', 'h', 'e'], [⟨['m', 'í'], ['t', 'h', 'e'], none⟩]⟩, ⟨['c', 'a', 'r', 'r', 'e', 'r', 'a'], ['r', 'a', 'c', 'e'], [⟨['c', 'a', 'r', 'r', 'e', 'r', 'a'], ['r', 'a', 'c', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "kòni"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "cCommand"), ("antecedent", "nonCCommanding")] }

def ex_43b : Datum :=
  { id := "ostrove2026_43b"
    source := ⟨"ostrove-2026", "(43b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ntátu amiga ña'à Marco ná ku'u =rà mí Olimpico"
    glossedTokens := [("Ntátu", "hope:CONT"), ("amiga", "friend.FEM"), ("ña'à", "POSS"), ("Marco", "Marco"), ("ná", "NÁ"), ("ku'u", "go:IRR"), ("=rà", "=he"), ("mí", "the"), ("Olimpico", "Olympics")]
    glossedWords := [⟨['N', 't', 'á', 't', 'u'], ['h', 'o', 'p', 'e', ':', 'C', 'O', 'N', 'T'], [⟨['N', 't', 'á', 't', 'u'], ['h', 'o', 'p', 'e', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['a', 'm', 'i', 'g', 'a'], ['f', 'r', 'i', 'e', 'n', 'd', '.', 'F', 'E', 'M'], [⟨['a', 'm', 'i', 'g', 'a'], ['f', 'r', 'i', 'e', 'n', 'd', '.', 'F', 'E', 'M'], none⟩]⟩, ⟨['ñ', 'a', '\'', 'à'], ['P', 'O', 'S', 'S'], [⟨['ñ', 'a', '\'', 'à'], ['P', 'O', 'S', 'S'], none⟩]⟩, ⟨['M', 'a', 'r', 'c', 'o'], ['M', 'a', 'r', 'c', 'o'], [⟨['M', 'a', 'r', 'c', 'o'], ['M', 'a', 'r', 'c', 'o'], none⟩]⟩, ⟨['n', 'á'], ['N', 'Á'], [⟨['n', 'á'], ['N', 'Á'], none⟩]⟩, ⟨['k', 'u', '\'', 'u'], ['g', 'o', ':', 'I', 'R', 'R'], [⟨['k', 'u', '\'', 'u'], ['g', 'o', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['m', 'í'], ['t', 'h', 'e'], [⟨['m', 'í'], ['t', 'h', 'e'], none⟩]⟩, ⟨['O', 'l', 'i', 'm', 'p', 'i', 'c', 'o'], ['O', 'l', 'y', 'm', 'p', 'i', 'c', 's'], [⟨['O', 'l', 'i', 'm', 'p', 'i', 'c', 'o'], ['O', 'l', 'y', 'm', 'p', 'i', 'c', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ntatu"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "cCommand"), ("antecedent", "nonCCommanding")] }

def ex_44a : Datum :=
  { id := "ostrove2026_44a"
    source := ⟨"ostrove-2026", "(44a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Nàntǒso táta Maria ku'un =ñá tienda"
    glossedTokens := [("Nàntǒso", "forget:COMP"), ("táta", "father"), ("Maria", "Maria"), ("ku'un", "go:IRR"), ("=ñá", "=she"), ("tienda", "store")]
    glossedWords := [⟨['N', 'à', 'n', 't', 'ǒ', 's', 'o'], ['f', 'o', 'r', 'g', 'e', 't', ':', 'C', 'O', 'M', 'P'], [⟨['N', 'à', 'n', 't', 'ǒ', 's', 'o'], ['f', 'o', 'r', 'g', 'e', 't', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['t', 'á', 't', 'a'], ['f', 'a', 't', 'h', 'e', 'r'], [⟨['t', 'á', 't', 'a'], ['f', 'a', 't', 'h', 'e', 'r'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['k', 'u', '\'', 'u', 'n'], ['g', 'o', ':', 'I', 'R', 'R'], [⟨['k', 'u', '\'', 'u', 'n'], ['g', 'o', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'ñ', 'á'], ['=', 's', 'h', 'e'], [⟨['ñ', 'á'], ['s', 'h', 'e'], some '='⟩]⟩, ⟨['t', 'i', 'e', 'n', 'd', 'a'], ['s', 't', 'o', 'r', 'e'], [⟨['t', 'i', 'e', 'n', 'd', 'a'], ['s', 't', 'o', 'r', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "nantǒso"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "cCommand"), ("antecedent", "nonCCommanding")] }

def ex_44b : Datum :=
  { id := "ostrove2026_44b"
    source := ⟨"ostrove-2026", "(44b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Xíniñu'u nána Julio kwiin =rà iin koto xàá"
    glossedTokens := [("Xíniñu'u", "need:CONT"), ("nána", "mother"), ("Julio", "Julio"), ("kwiin", "buy:IRR"), ("=rà", "=he"), ("iin", "one"), ("koto", "shirt"), ("xàá", "new")]
    glossedWords := [⟨['X', 'í', 'n', 'i', 'ñ', 'u', '\'', 'u'], ['n', 'e', 'e', 'd', ':', 'C', 'O', 'N', 'T'], [⟨['X', 'í', 'n', 'i', 'ñ', 'u', '\'', 'u'], ['n', 'e', 'e', 'd', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['n', 'á', 'n', 'a'], ['m', 'o', 't', 'h', 'e', 'r'], [⟨['n', 'á', 'n', 'a'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩]⟩, ⟨['J', 'u', 'l', 'i', 'o'], ['J', 'u', 'l', 'i', 'o'], [⟨['J', 'u', 'l', 'i', 'o'], ['J', 'u', 'l', 'i', 'o'], none⟩]⟩, ⟨['k', 'w', 'i', 'i', 'n'], ['b', 'u', 'y', ':', 'I', 'R', 'R'], [⟨['k', 'w', 'i', 'i', 'n'], ['b', 'u', 'y', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['i', 'i', 'n'], ['o', 'n', 'e'], [⟨['i', 'i', 'n'], ['o', 'n', 'e'], none⟩]⟩, ⟨['k', 'o', 't', 'o'], ['s', 'h', 'i', 'r', 't'], [⟨['k', 'o', 't', 'o'], ['s', 'h', 'i', 'r', 't'], none⟩]⟩, ⟨['x', 'à', 'á'], ['n', 'e', 'w'], [⟨['x', 'à', 'á'], ['n', 'e', 'w'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "xiniñu'u"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "cCommand"), ("antecedent", "nonCCommanding")] }

def ex_45a : Datum :=
  { id := "ostrove2026_45a"
    source := ⟨"ostrove-2026", "(45a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Bìjkǒ ña'à Marco xìndatu Ana kaxi =rà yù'u =ñá"
    glossedTokens := [("Bìjkǒ", "party"), ("ña'à", "POSS"), ("Marco", "Marco"), ("xìndatu", "hope:IMP:COMP"), ("Ana", "Ana"), ("kaxi", "eat:IRR"), ("=rà", "=he"), ("yù'u", "mouth"), ("=ñá", "=her")]
    glossedWords := [⟨['B', 'ì', 'j', 'k', 'ǒ'], ['p', 'a', 'r', 't', 'y'], [⟨['B', 'ì', 'j', 'k', 'ǒ'], ['p', 'a', 'r', 't', 'y'], none⟩]⟩, ⟨['ñ', 'a', '\'', 'à'], ['P', 'O', 'S', 'S'], [⟨['ñ', 'a', '\'', 'à'], ['P', 'O', 'S', 'S'], none⟩]⟩, ⟨['M', 'a', 'r', 'c', 'o'], ['M', 'a', 'r', 'c', 'o'], [⟨['M', 'a', 'r', 'c', 'o'], ['M', 'a', 'r', 'c', 'o'], none⟩]⟩, ⟨['x', 'ì', 'n', 'd', 'a', 't', 'u'], ['h', 'o', 'p', 'e', ':', 'I', 'M', 'P', ':', 'C', 'O', 'M', 'P'], [⟨['x', 'ì', 'n', 'd', 'a', 't', 'u'], ['h', 'o', 'p', 'e', ':', 'I', 'M', 'P', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['A', 'n', 'a'], ['A', 'n', 'a'], [⟨['A', 'n', 'a'], ['A', 'n', 'a'], none⟩]⟩, ⟨['k', 'a', 'x', 'i'], ['e', 'a', 't', ':', 'I', 'R', 'R'], [⟨['k', 'a', 'x', 'i'], ['e', 'a', 't', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['y', 'ù', '\'', 'u'], ['m', 'o', 'u', 't', 'h'], [⟨['y', 'ù', '\'', 'u'], ['m', 'o', 'u', 't', 'h'], none⟩]⟩, ⟨['=', 'ñ', 'á'], ['=', 'h', 'e', 'r'], [⟨['ñ', 'á'], ['h', 'e', 'r'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ntatu"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "cCommand"), ("antecedent", "nonCCommanding")] }

def ex_45b : Datum :=
  { id := "ostrove2026_45b"
    source := ⟨"ostrove-2026", "(45b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Bìjkǒ ña'à Marco kòni Ana kaxi =rà yù'u =ñá"
    glossedTokens := [("Bìjkǒ", "party"), ("ña'à", "POSS"), ("Marco", "Marco"), ("kòni", "want:COMP"), ("Ana", "Ana"), ("kaxi", "eat:IRR"), ("=rà", "=he"), ("yù'u", "mouth"), ("=ñá", "=her")]
    glossedWords := [⟨['B', 'ì', 'j', 'k', 'ǒ'], ['p', 'a', 'r', 't', 'y'], [⟨['B', 'ì', 'j', 'k', 'ǒ'], ['p', 'a', 'r', 't', 'y'], none⟩]⟩, ⟨['ñ', 'a', '\'', 'à'], ['P', 'O', 'S', 'S'], [⟨['ñ', 'a', '\'', 'à'], ['P', 'O', 'S', 'S'], none⟩]⟩, ⟨['M', 'a', 'r', 'c', 'o'], ['M', 'a', 'r', 'c', 'o'], [⟨['M', 'a', 'r', 'c', 'o'], ['M', 'a', 'r', 'c', 'o'], none⟩]⟩, ⟨['k', 'ò', 'n', 'i'], ['w', 'a', 'n', 't', ':', 'C', 'O', 'M', 'P'], [⟨['k', 'ò', 'n', 'i'], ['w', 'a', 'n', 't', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['A', 'n', 'a'], ['A', 'n', 'a'], [⟨['A', 'n', 'a'], ['A', 'n', 'a'], none⟩]⟩, ⟨['k', 'a', 'x', 'i'], ['e', 'a', 't', ':', 'I', 'R', 'R'], [⟨['k', 'a', 'x', 'i'], ['e', 'a', 't', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['y', 'ù', '\'', 'u'], ['m', 'o', 'u', 't', 'h'], [⟨['y', 'ù', '\'', 'u'], ['m', 'o', 'u', 't', 'h'], none⟩]⟩, ⟨['=', 'ñ', 'á'], ['=', 'h', 'e', 'r'], [⟨['ñ', 'á'], ['h', 'e', 'r'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "kòni"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "cCommand"), ("antecedent", "nonCCommanding")] }

def ex_46a : Datum :=
  { id := "ostrove2026_46a"
    source := ⟨"ostrove-2026", "(46a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Bìjkǒ ña'à Marco xìniñu'u Ana kaxi =rà yù'u =ñá"
    glossedTokens := [("Bìjkǒ", "party"), ("ña'à", "POSS"), ("Marco", "Marco"), ("xìniñu'u", "need:COMP"), ("Ana", "Ana"), ("kaxi", "eat:IRR"), ("=rà", "=he"), ("yù'u", "mouth"), ("=ñá", "=her")]
    glossedWords := [⟨['B', 'ì', 'j', 'k', 'ǒ'], ['p', 'a', 'r', 't', 'y'], [⟨['B', 'ì', 'j', 'k', 'ǒ'], ['p', 'a', 'r', 't', 'y'], none⟩]⟩, ⟨['ñ', 'a', '\'', 'à'], ['P', 'O', 'S', 'S'], [⟨['ñ', 'a', '\'', 'à'], ['P', 'O', 'S', 'S'], none⟩]⟩, ⟨['M', 'a', 'r', 'c', 'o'], ['M', 'a', 'r', 'c', 'o'], [⟨['M', 'a', 'r', 'c', 'o'], ['M', 'a', 'r', 'c', 'o'], none⟩]⟩, ⟨['x', 'ì', 'n', 'i', 'ñ', 'u', '\'', 'u'], ['n', 'e', 'e', 'd', ':', 'C', 'O', 'M', 'P'], [⟨['x', 'ì', 'n', 'i', 'ñ', 'u', '\'', 'u'], ['n', 'e', 'e', 'd', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['A', 'n', 'a'], ['A', 'n', 'a'], [⟨['A', 'n', 'a'], ['A', 'n', 'a'], none⟩]⟩, ⟨['k', 'a', 'x', 'i'], ['e', 'a', 't', ':', 'I', 'R', 'R'], [⟨['k', 'a', 'x', 'i'], ['e', 'a', 't', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['y', 'ù', '\'', 'u'], ['m', 'o', 'u', 't', 'h'], [⟨['y', 'ù', '\'', 'u'], ['m', 'o', 'u', 't', 'h'], none⟩]⟩, ⟨['=', 'ñ', 'á'], ['=', 'h', 'e', 'r'], [⟨['ñ', 'á'], ['h', 'e', 'r'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "xiniñu'u"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "cCommand"), ("antecedent", "nonCCommanding")] }

def ex_46b : Datum :=
  { id := "ostrove2026_46b"
    source := ⟨"ostrove-2026", "(46b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Bìjkǒ ña'à Marco ntùkú Ana kaxi =rà yù'u =ñá"
    glossedTokens := [("Bìjkǒ", "party"), ("ña'à", "POSS"), ("Marco", "Marco"), ("ntùkú", "try:COMP"), ("Ana", "Ana"), ("kaxi", "eat:IRR"), ("=rà", "=he"), ("yù'u", "mouth"), ("=ñá", "=her")]
    glossedWords := [⟨['B', 'ì', 'j', 'k', 'ǒ'], ['p', 'a', 'r', 't', 'y'], [⟨['B', 'ì', 'j', 'k', 'ǒ'], ['p', 'a', 'r', 't', 'y'], none⟩]⟩, ⟨['ñ', 'a', '\'', 'à'], ['P', 'O', 'S', 'S'], [⟨['ñ', 'a', '\'', 'à'], ['P', 'O', 'S', 'S'], none⟩]⟩, ⟨['M', 'a', 'r', 'c', 'o'], ['M', 'a', 'r', 'c', 'o'], [⟨['M', 'a', 'r', 'c', 'o'], ['M', 'a', 'r', 'c', 'o'], none⟩]⟩, ⟨['n', 't', 'ù', 'k', 'ú'], ['t', 'r', 'y', ':', 'C', 'O', 'M', 'P'], [⟨['n', 't', 'ù', 'k', 'ú'], ['t', 'r', 'y', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['A', 'n', 'a'], ['A', 'n', 'a'], [⟨['A', 'n', 'a'], ['A', 'n', 'a'], none⟩]⟩, ⟨['k', 'a', 'x', 'i'], ['e', 'a', 't', ':', 'I', 'R', 'R'], [⟨['k', 'a', 'x', 'i'], ['e', 'a', 't', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['y', 'ù', '\'', 'u'], ['m', 'o', 'u', 't', 'h'], [⟨['y', 'ù', '\'', 'u'], ['m', 'o', 'u', 't', 'h'], none⟩]⟩, ⟨['=', 'ñ', 'á'], ['=', 'h', 'e', 'r'], [⟨['ñ', 'á'], ['h', 'e', 'r'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ntukú"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "cCommand"), ("antecedent", "nonCCommanding")] }

def ex_67a : Datum :=
  { id := "ostrove2026_67a"
    source := ⟨"ostrove-2026", "(67a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Saá nántǒso =ndó koná ndó'ó yùye'e"
    glossedTokens := [("Saá", "always"), ("nántǒso", "forget:CONT"), ("=ndó", "=you.PL"), ("koná", "open:IRR"), ("ndó'ó", "you"), ("yùye'e", "door")]
    glossedWords := [⟨['S', 'a', 'á'], ['a', 'l', 'w', 'a', 'y', 's'], [⟨['S', 'a', 'á'], ['a', 'l', 'w', 'a', 'y', 's'], none⟩]⟩, ⟨['n', 'á', 'n', 't', 'ǒ', 's', 'o'], ['f', 'o', 'r', 'g', 'e', 't', ':', 'C', 'O', 'N', 'T'], [⟨['n', 'á', 'n', 't', 'ǒ', 's', 'o'], ['f', 'o', 'r', 'g', 'e', 't', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['=', 'n', 'd', 'ó'], ['=', 'y', 'o', 'u', '.', 'P', 'L'], [⟨['n', 'd', 'ó'], ['y', 'o', 'u', '.', 'P', 'L'], some '='⟩]⟩, ⟨['k', 'o', 'n', 'á'], ['o', 'p', 'e', 'n', ':', 'I', 'R', 'R'], [⟨['k', 'o', 'n', 'á'], ['o', 'p', 'e', 'n', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['n', 'd', 'ó', '\'', 'ó'], ['y', 'o', 'u'], [⟨['n', 'd', 'ó', '\'', 'ó'], ['y', 'o', 'u'], none⟩]⟩, ⟨['y', 'ù', 'y', 'e', '\'', 'e'], ['d', 'o', 'o', 'r'], [⟨['y', 'ù', 'y', 'e', '\'', 'e'], ['d', 'o', 'o', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "nantǒso"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "clitic"), ("embeddedSubject", "nonclitic")] }

def ex_67b : Datum :=
  { id := "ostrove2026_67b"
    source := ⟨"ostrove-2026", "(67b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Xíni Marco ixutsya mí =rà"
    glossedTokens := [("Xíni", "know:CONT"), ("Marco", "Marco"), ("ixutsya", "swim:IRR"), ("mí", "the"), ("=rà", "=he")]
    glossedWords := [⟨['X', 'í', 'n', 'i'], ['k', 'n', 'o', 'w', ':', 'C', 'O', 'N', 'T'], [⟨['X', 'í', 'n', 'i'], ['k', 'n', 'o', 'w', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['M', 'a', 'r', 'c', 'o'], ['M', 'a', 'r', 'c', 'o'], [⟨['M', 'a', 'r', 'c', 'o'], ['M', 'a', 'r', 'c', 'o'], none⟩]⟩, ⟨['i', 'x', 'u', 't', 's', 'y', 'a'], ['s', 'w', 'i', 'm', ':', 'I', 'R', 'R'], [⟨['i', 'x', 'u', 't', 's', 'y', 'a'], ['s', 'w', 'i', 'm', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['m', 'í'], ['t', 'h', 'e'], [⟨['m', 'í'], ['t', 'h', 'e'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "kònì"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "clitic"), ("embeddedSubject", "nonclitic")] }

def ex_67c : Datum :=
  { id := "ostrove2026_67c"
    source := ⟨"ostrove-2026", "(67c)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kìxǎ mí leso taxá'á rí kan"
    glossedTokens := [("Kìxǎ", "start:COMP"), ("mí", "the"), ("leso", "rabbit"), ("taxá'á", "dance:IRR"), ("rí", "it.AML"), ("kan", "there")]
    glossedWords := [⟨['K', 'ì', 'x', 'ǎ'], ['s', 't', 'a', 'r', 't', ':', 'C', 'O', 'M', 'P'], [⟨['K', 'ì', 'x', 'ǎ'], ['s', 't', 'a', 'r', 't', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['m', 'í'], ['t', 'h', 'e'], [⟨['m', 'í'], ['t', 'h', 'e'], none⟩]⟩, ⟨['l', 'e', 's', 'o'], ['r', 'a', 'b', 'b', 'i', 't'], [⟨['l', 'e', 's', 'o'], ['r', 'a', 'b', 'b', 'i', 't'], none⟩]⟩, ⟨['t', 'a', 'x', 'á', '\'', 'á'], ['d', 'a', 'n', 'c', 'e', ':', 'I', 'R', 'R'], [⟨['t', 'a', 'x', 'á', '\'', 'á'], ['d', 'a', 'n', 'c', 'e', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['r', 'í'], ['i', 't', '.', 'A', 'M', 'L'], [⟨['r', 'í'], ['i', 't', '.', 'A', 'M', 'L'], none⟩]⟩, ⟨['k', 'a', 'n'], ['t', 'h', 'e', 'r', 'e'], [⟨['k', 'a', 'n'], ['t', 'h', 'e', 'r', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "kixǎ"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "clitic"), ("embeddedSubject", "nonclitic")] }

def ex_68a : Datum :=
  { id := "ostrove2026_68a"
    source := ⟨"ostrove-2026", "(68a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kôni Jûan keba'a mí =rà carrera"
    glossedTokens := [("Kôni", "want:CONT"), ("Jûan", "Juan"), ("keba'a", "win:IRR"), ("mí", "the"), ("=rà", "=he"), ("carrera", "race")]
    glossedWords := [⟨['K', 'ô', 'n', 'i'], ['w', 'a', 'n', 't', ':', 'C', 'O', 'N', 'T'], [⟨['K', 'ô', 'n', 'i'], ['w', 'a', 'n', 't', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['J', 'û', 'a', 'n'], ['J', 'u', 'a', 'n'], [⟨['J', 'û', 'a', 'n'], ['J', 'u', 'a', 'n'], none⟩]⟩, ⟨['k', 'e', 'b', 'a', '\'', 'a'], ['w', 'i', 'n', ':', 'I', 'R', 'R'], [⟨['k', 'e', 'b', 'a', '\'', 'a'], ['w', 'i', 'n', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['m', 'í'], ['t', 'h', 'e'], [⟨['m', 'í'], ['t', 'h', 'e'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['c', 'a', 'r', 'r', 'e', 'r', 'a'], ['r', 'a', 'c', 'e'], [⟨['c', 'a', 'r', 'r', 'e', 'r', 'a'], ['r', 'a', 'c', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "kòni"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "clitic"), ("embeddedSubject", "nonclitic")] }

def ex_68b : Datum :=
  { id := "ostrove2026_68b"
    source := ⟨"ostrove-2026", "(68b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ntátu Maria ku'ún mí =ñá yòjo"
    glossedTokens := [("Ntátu", "hope:CONT"), ("Maria", "Maria"), ("ku'ún", "go:IRR"), ("mí", "the"), ("=ñá", "=she"), ("yòjo", "moon")]
    glossedWords := [⟨['N', 't', 'á', 't', 'u'], ['h', 'o', 'p', 'e', ':', 'C', 'O', 'N', 'T'], [⟨['N', 't', 'á', 't', 'u'], ['h', 'o', 'p', 'e', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['k', 'u', '\'', 'ú', 'n'], ['g', 'o', ':', 'I', 'R', 'R'], [⟨['k', 'u', '\'', 'ú', 'n'], ['g', 'o', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['m', 'í'], ['t', 'h', 'e'], [⟨['m', 'í'], ['t', 'h', 'e'], none⟩]⟩, ⟨['=', 'ñ', 'á'], ['=', 's', 'h', 'e'], [⟨['ñ', 'á'], ['s', 'h', 'e'], some '='⟩]⟩, ⟨['y', 'ò', 'j', 'o'], ['m', 'o', 'o', 'n'], [⟨['y', 'ò', 'j', 'o'], ['m', 'o', 'o', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ntatu"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "clitic"), ("embeddedSubject", "nonclitic")] }

def ex_75a : Datum :=
  { id := "ostrove2026_75a"
    source := ⟨"ostrove-2026", "(75a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Tá'iin'iin tsǐnà tsìi ndò'ò mí =rí"
    glossedTokens := [("Tá'iin'iin", "each"), ("tsǐnà", "dog"), ("tsìi", "bite:COMP"), ("ndò'ò", "tail"), ("mí", "the"), ("=rí", "=its")]
    glossedWords := [⟨['T', 'á', '\'', 'i', 'i', 'n', '\'', 'i', 'i', 'n'], ['e', 'a', 'c', 'h'], [⟨['T', 'á', '\'', 'i', 'i', 'n', '\'', 'i', 'i', 'n'], ['e', 'a', 'c', 'h'], none⟩]⟩, ⟨['t', 's', 'ǐ', 'n', 'à'], ['d', 'o', 'g'], [⟨['t', 's', 'ǐ', 'n', 'à'], ['d', 'o', 'g'], none⟩]⟩, ⟨['t', 's', 'ì', 'i'], ['b', 'i', 't', 'e', ':', 'C', 'O', 'M', 'P'], [⟨['t', 's', 'ì', 'i'], ['b', 'i', 't', 'e', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['n', 'd', 'ò', '\'', 'ò'], ['t', 'a', 'i', 'l'], [⟨['n', 'd', 'ò', '\'', 'ò'], ['t', 'a', 'i', 'l'], none⟩]⟩, ⟨['m', 'í'], ['t', 'h', 'e'], [⟨['m', 'í'], ['t', 'h', 'e'], none⟩]⟩, ⟨['=', 'r', 'í'], ['=', 'i', 't', 's'], [⟨['r', 'í'], ['i', 't', 's'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "exemptAnaphor"), ("antecedent", "quantified")] }

def ex_75b : Datum :=
  { id := "ostrove2026_75b"
    source := ⟨"ostrove-2026", "(75b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ni'iin =ná báli nǐ- xini táta mí =ná"
    glossedTokens := [("Ni'iin", "no"), ("=ná", "=they.FEM"), ("báli", "little.PL"), ("nǐ-", "COMP.NEG"), ("xini", "see"), ("táta", "father"), ("mí", "the"), ("=ná", "=their.FEM")]
    glossedWords := [⟨['N', 'i', '\'', 'i', 'i', 'n'], ['n', 'o'], [⟨['N', 'i', '\'', 'i', 'i', 'n'], ['n', 'o'], none⟩]⟩, ⟨['=', 'n', 'á'], ['=', 't', 'h', 'e', 'y', '.', 'F', 'E', 'M'], [⟨['n', 'á'], ['t', 'h', 'e', 'y', '.', 'F', 'E', 'M'], some '='⟩]⟩, ⟨['b', 'á', 'l', 'i'], ['l', 'i', 't', 't', 'l', 'e', '.', 'P', 'L'], [⟨['b', 'á', 'l', 'i'], ['l', 'i', 't', 't', 'l', 'e', '.', 'P', 'L'], none⟩]⟩, ⟨['n', 'ǐ', '-'], ['C', 'O', 'M', 'P', '.', 'N', 'E', 'G'], []⟩, ⟨['x', 'i', 'n', 'i'], ['s', 'e', 'e'], [⟨['x', 'i', 'n', 'i'], ['s', 'e', 'e'], none⟩]⟩, ⟨['t', 'á', 't', 'a'], ['f', 'a', 't', 'h', 'e', 'r'], [⟨['t', 'á', 't', 'a'], ['f', 'a', 't', 'h', 'e', 'r'], none⟩]⟩, ⟨['m', 'í'], ['t', 'h', 'e'], [⟨['m', 'í'], ['t', 'h', 'e'], none⟩]⟩, ⟨['=', 'n', 'á'], ['=', 't', 'h', 'e', 'i', 'r', '.', 'F', 'E', 'M'], [⟨['n', 'á'], ['t', 'h', 'e', 'i', 'r', '.', 'F', 'E', 'M'], some '='⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "exemptAnaphor"), ("antecedent", "quantified")] }

def ex_86a : Datum :=
  { id := "ostrove2026_86a"
    source := ⟨"ostrove-2026", "(86a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Tá'iin'iin tsǐnà kìxǎ tsii =rí ndò'ò mí =rí"
    glossedTokens := [("Tá'iin'iin", "each"), ("tsǐnà", "dog"), ("kìxǎ", "start:COMP"), ("tsii", "bite:IRR"), ("=rí", "=it.AML"), ("ndò'ò", "tail"), ("mí", "the"), ("=rí", "=its.AML")]
    glossedWords := [⟨['T', 'á', '\'', 'i', 'i', 'n', '\'', 'i', 'i', 'n'], ['e', 'a', 'c', 'h'], [⟨['T', 'á', '\'', 'i', 'i', 'n', '\'', 'i', 'i', 'n'], ['e', 'a', 'c', 'h'], none⟩]⟩, ⟨['t', 's', 'ǐ', 'n', 'à'], ['d', 'o', 'g'], [⟨['t', 's', 'ǐ', 'n', 'à'], ['d', 'o', 'g'], none⟩]⟩, ⟨['k', 'ì', 'x', 'ǎ'], ['s', 't', 'a', 'r', 't', ':', 'C', 'O', 'M', 'P'], [⟨['k', 'ì', 'x', 'ǎ'], ['s', 't', 'a', 'r', 't', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['t', 's', 'i', 'i'], ['b', 'i', 't', 'e', ':', 'I', 'R', 'R'], [⟨['t', 's', 'i', 'i'], ['b', 'i', 't', 'e', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'r', 'í'], ['=', 'i', 't', '.', 'A', 'M', 'L'], [⟨['r', 'í'], ['i', 't', '.', 'A', 'M', 'L'], some '='⟩]⟩, ⟨['n', 'd', 'ò', '\'', 'ò'], ['t', 'a', 'i', 'l'], [⟨['n', 'd', 'ò', '\'', 'ò'], ['t', 'a', 'i', 'l'], none⟩]⟩, ⟨['m', 'í'], ['t', 'h', 'e'], [⟨['m', 'í'], ['t', 'h', 'e'], none⟩]⟩, ⟨['=', 'r', 'í'], ['=', 'i', 't', 's', '.', 'A', 'M', 'L'], [⟨['r', 'í'], ['i', 't', 's', '.', 'A', 'M', 'L'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "kixǎ"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "exemptAnaphor"), ("antecedent", "quantified")] }

def ex_86b : Datum :=
  { id := "ostrove2026_86b"
    source := ⟨"ostrove-2026", "(86b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ni'iin =rà bálí kò xíniñu'u kònì =rà táta mí =rà"
    glossedTokens := [("Ni'iin", "no"), ("=rà", "=he"), ("bálí", "little.PL"), ("kò", "NEG"), ("xíniñu'u", "need:CONT"), ("kònì", "see:IRR"), ("=rà", "=he"), ("táta", "father"), ("mí", "the"), ("=rà", "=his")]
    glossedWords := [⟨['N', 'i', '\'', 'i', 'i', 'n'], ['n', 'o'], [⟨['N', 'i', '\'', 'i', 'i', 'n'], ['n', 'o'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['b', 'á', 'l', 'í'], ['l', 'i', 't', 't', 'l', 'e', '.', 'P', 'L'], [⟨['b', 'á', 'l', 'í'], ['l', 'i', 't', 't', 'l', 'e', '.', 'P', 'L'], none⟩]⟩, ⟨['k', 'ò'], ['N', 'E', 'G'], [⟨['k', 'ò'], ['N', 'E', 'G'], none⟩]⟩, ⟨['x', 'í', 'n', 'i', 'ñ', 'u', '\'', 'u'], ['n', 'e', 'e', 'd', ':', 'C', 'O', 'N', 'T'], [⟨['x', 'í', 'n', 'i', 'ñ', 'u', '\'', 'u'], ['n', 'e', 'e', 'd', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['k', 'ò', 'n', 'ì'], ['s', 'e', 'e', ':', 'I', 'R', 'R'], [⟨['k', 'ò', 'n', 'ì'], ['s', 'e', 'e', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['t', 'á', 't', 'a'], ['f', 'a', 't', 'h', 'e', 'r'], [⟨['t', 'á', 't', 'a'], ['f', 'a', 't', 'h', 'e', 'r'], none⟩]⟩, ⟨['m', 'í'], ['t', 'h', 'e'], [⟨['m', 'í'], ['t', 'h', 'e'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'i', 's'], [⟨['r', 'à'], ['h', 'i', 's'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "xiniñu'u"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "exemptAnaphor"), ("antecedent", "quantified")] }

def ex_87a : Datum :=
  { id := "ostrove2026_87a"
    source := ⟨"ostrove-2026", "(87a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kìxǎ iin tsǐnà tsii =rí ndò'ò mí =rí"
    glossedTokens := [("Kìxǎ", "start:COMP"), ("iin", "one"), ("tsǐnà", "dog"), ("tsii", "bite:IRR"), ("=rí", "=it.AML"), ("ndò'ò", "tail"), ("mí", "the"), ("=rí", "=its.AML")]
    glossedWords := [⟨['K', 'ì', 'x', 'ǎ'], ['s', 't', 'a', 'r', 't', ':', 'C', 'O', 'M', 'P'], [⟨['K', 'ì', 'x', 'ǎ'], ['s', 't', 'a', 'r', 't', ':', 'C', 'O', 'M', 'P'], none⟩]⟩, ⟨['i', 'i', 'n'], ['o', 'n', 'e'], [⟨['i', 'i', 'n'], ['o', 'n', 'e'], none⟩]⟩, ⟨['t', 's', 'ǐ', 'n', 'à'], ['d', 'o', 'g'], [⟨['t', 's', 'ǐ', 'n', 'à'], ['d', 'o', 'g'], none⟩]⟩, ⟨['t', 's', 'i', 'i'], ['b', 'i', 't', 'e', ':', 'I', 'R', 'R'], [⟨['t', 's', 'i', 'i'], ['b', 'i', 't', 'e', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'r', 'í'], ['=', 'i', 't', '.', 'A', 'M', 'L'], [⟨['r', 'í'], ['i', 't', '.', 'A', 'M', 'L'], some '='⟩]⟩, ⟨['n', 'd', 'ò', '\'', 'ò'], ['t', 'a', 'i', 'l'], [⟨['n', 'd', 'ò', '\'', 'ò'], ['t', 'a', 'i', 'l'], none⟩]⟩, ⟨['m', 'í'], ['t', 'h', 'e'], [⟨['m', 'í'], ['t', 'h', 'e'], none⟩]⟩, ⟨['=', 'r', 'í'], ['=', 'i', 't', 's', '.', 'A', 'M', 'L'], [⟨['r', 'í'], ['i', 't', 's', '.', 'A', 'M', 'L'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "kixǎ"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "exemptAnaphor"), ("antecedent", "quantified")] }

def ex_87b : Datum :=
  { id := "ostrove2026_87b"
    source := ⟨"ostrove-2026", "(87b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kò xíniñu'u ni'iin =rà bálí kònì =rà táta mí =rà"
    glossedTokens := [("Kò", "NEG"), ("xíniñu'u", "need:CONT"), ("ni'iin", "no"), ("=rà", "=he"), ("bálí", "little.PL"), ("kònì", "see:IRR"), ("=rà", "=he"), ("táta", "father"), ("mí", "the"), ("=rà", "=his")]
    glossedWords := [⟨['K', 'ò'], ['N', 'E', 'G'], [⟨['K', 'ò'], ['N', 'E', 'G'], none⟩]⟩, ⟨['x', 'í', 'n', 'i', 'ñ', 'u', '\'', 'u'], ['n', 'e', 'e', 'd', ':', 'C', 'O', 'N', 'T'], [⟨['x', 'í', 'n', 'i', 'ñ', 'u', '\'', 'u'], ['n', 'e', 'e', 'd', ':', 'C', 'O', 'N', 'T'], none⟩]⟩, ⟨['n', 'i', '\'', 'i', 'i', 'n'], ['n', 'o'], [⟨['n', 'i', '\'', 'i', 'i', 'n'], ['n', 'o'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['b', 'á', 'l', 'í'], ['l', 'i', 't', 't', 'l', 'e', '.', 'P', 'L'], [⟨['b', 'á', 'l', 'í'], ['l', 'i', 't', 't', 'l', 'e', '.', 'P', 'L'], none⟩]⟩, ⟨['k', 'ò', 'n', 'ì'], ['s', 'e', 'e', ':', 'I', 'R', 'R'], [⟨['k', 'ò', 'n', 'ì'], ['s', 'e', 'e', ':', 'I', 'R', 'R'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'e'], [⟨['r', 'à'], ['h', 'e'], some '='⟩]⟩, ⟨['t', 'á', 't', 'a'], ['f', 'a', 't', 'h', 'e', 'r'], [⟨['t', 'á', 't', 'a'], ['f', 'a', 't', 'h', 'e', 'r'], none⟩]⟩, ⟨['m', 'í'], ['t', 'h', 'e'], [⟨['m', 'í'], ['t', 'h', 'e'], none⟩]⟩, ⟨['=', 'r', 'à'], ['=', 'h', 'i', 's'], [⟨['r', 'à'], ['h', 'i', 's'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "xiniñu'u"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "exemptAnaphor"), ("antecedent", "quantified")] }

def all : List Datum := [ex_9a_completive, ex_9a_continuous, ex_9a_irrealis, ex_9b_completive, ex_9b_continuous, ex_9b_irrealis, ex_9c_completive, ex_9c_continuous, ex_9c_irrealis, ex_13a_completive, ex_13a_continuous, ex_13a_irrealis, ex_13b_completive, ex_13b_continuous, ex_13b_irrealis, ex_13c_completive, ex_13c_continuous, ex_13c_irrealis, ex_13d_completive, ex_13d_continuous, ex_13d_irrealis, ex_10a, ex_10b, ex_16a, ex_16b, ex_17a, ex_17b, ex_12a, ex_12b, ex_18a, ex_18b, ex_18c, ex_18d, ex_19a, ex_19b, ex_40a, ex_40b, ex_41a, ex_41b, ex_20a, ex_20b, ex_21a, ex_21b, ex_22a, ex_22b, ex_23a, ex_23b, ex_24a, ex_24b, ex_25a, ex_25b, ex_109, ex_30a, ex_30b, ex_32a, ex_32b, ex_33a, ex_33b, ex_37a, ex_37b, ex_43a, ex_43b, ex_44a, ex_44b, ex_45a, ex_45b, ex_46a, ex_46b, ex_67a, ex_67b, ex_67c, ex_68a, ex_68b, ex_75a, ex_75b, ex_86a, ex_86b, ex_87a, ex_87b]

end Ostrove2026.Examples
