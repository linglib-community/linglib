module

public import Linglib.Data.Examples.Schema

/-!
# `Anderson2006a` — typed example data

Auto-generated from `Linglib/Data/Examples/Anderson2006a.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Anderson2006a.Examples`.
-/

@[expose] public section

namespace Anderson2006a.Examples

def komi_neg_pres : Datum :=
  { id := "anderson2006a_komi_neg_pres"
    source := ⟨"anderson-2006a", "ch. 1, (47a)"⟩
    reportedIn := none
    language := "komi1268"
    primaryText := "o-g mun"
    glossedTokens := [("o-g", "NEG:PRES-1"), ("mun", "go")]
    glossedWords := [⟨['o', '-', 'g'], ['N', 'E', 'G', ':', 'P', 'R', 'E', 'S', '-', '1'], [⟨['o'], ['N', 'E', 'G', ':', 'P', 'R', 'E', 'S'], none⟩, ⟨['g'], ['1'], some '-'⟩]⟩, ⟨['m', 'u', 'n'], ['g', 'o'], [⟨['m', 'u', 'n'], ['g', 'o'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "negVerb"), ("tense", "present"), ("on_aux", "negation"), ("on_aux", "tense"), ("on_aux", "subj")] }

def komi_neg_past : Datum :=
  { id := "anderson2006a_komi_neg_past"
    source := ⟨"anderson-2006a", "ch. 1, (47b)"⟩
    reportedIn := none
    language := "komi1268"
    primaryText := "e-g mun"
    glossedTokens := [("e-g", "NEG:PST-1"), ("mun", "go")]
    glossedWords := [⟨['e', '-', 'g'], ['N', 'E', 'G', ':', 'P', 'S', 'T', '-', '1'], [⟨['e'], ['N', 'E', 'G', ':', 'P', 'S', 'T'], none⟩, ⟨['g'], ['1'], some '-'⟩]⟩, ⟨['m', 'u', 'n'], ['g', 'o'], [⟨['m', 'u', 'n'], ['g', 'o'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "negVerb"), ("tense", "past"), ("on_aux", "negation"), ("on_aux", "tense"), ("on_aux", "subj")] }

def udihe_neg : Datum :=
  { id := "anderson2006a_udihe_neg"
    source := ⟨"anderson-2006a", "ch. 1, (49)"⟩
    reportedIn := none
    language := "udih1248"
    primaryText := "bi ei-mi sa:"
    glossedTokens := [("bi", "I"), ("ei-mi", "NEG-1"), ("sa:", "know")]
    glossedWords := [⟨['b', 'i'], ['I'], [⟨['b', 'i'], ['I'], none⟩]⟩, ⟨['e', 'i', '-', 'm', 'i'], ['N', 'E', 'G', '-', '1'], [⟨['e', 'i'], ['N', 'E', 'G'], none⟩, ⟨['m', 'i'], ['1'], some '-'⟩]⟩, ⟨['s', 'a', ':'], ['k', 'n', 'o', 'w'], [⟨['s', 'a'], ['k', 'n', 'o', 'w'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "negVerb"), ("infl_pattern", "auxHeaded"), ("on_aux", "negation"), ("on_aux", "subj")] }

def kokota_neg : Datum :=
  { id := "anderson2006a_kokota_neg"
    source := ⟨"anderson-2006a", "ch. 1, (50)"⟩
    reportedIn := none
    language := "koko1269"
    primaryText := "o-ti dupa-i manei si-ago"
    glossedTokens := [("o-ti", "2-NEG"), ("dupa-i", "punch-3"), ("manei", "s/he"), ("si-ago", "FOC-2")]
    glossedWords := [⟨['o', '-', 't', 'i'], ['2', '-', 'N', 'E', 'G'], [⟨['o'], ['2'], none⟩, ⟨['t', 'i'], ['N', 'E', 'G'], some '-'⟩]⟩, ⟨['d', 'u', 'p', 'a', '-', 'i'], ['p', 'u', 'n', 'c', 'h', '-', '3'], [⟨['d', 'u', 'p', 'a'], ['p', 'u', 'n', 'c', 'h'], none⟩, ⟨['i'], ['3'], some '-'⟩]⟩, ⟨['m', 'a', 'n', 'e', 'i'], ['s', '/', 'h', 'e'], [⟨['m', 'a', 'n', 'e', 'i'], ['s', '/', 'h', 'e'], none⟩]⟩, ⟨['s', 'i', '-', 'a', 'g', 'o'], ['F', 'O', 'C', '-', '2'], [⟨['s', 'i'], ['F', 'O', 'C'], none⟩, ⟨['a', 'g', 'o'], ['2'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "negVerb"), ("infl_pattern", "split"), ("on_aux", "negation"), ("on_aux", "subj"), ("on_lex", "obj")] }

def neyo_neg_past : Datum :=
  { id := "anderson2006a_neyo_neg_past"
    source := ⟨"anderson-2006a", "ch. 1, (51a)"⟩
    reportedIn := none
    language := "neyo1238"
    primaryText := "ma ne wa yo la"
    glossedTokens := [("ma", "but"), ("ne", "NEG.1"), ("wa", "PAST"), ("yo", "child"), ("la", "bring")]
    glossedWords := [⟨['m', 'a'], ['b', 'u', 't'], [⟨['m', 'a'], ['b', 'u', 't'], none⟩]⟩, ⟨['n', 'e'], ['N', 'E', 'G', '.', '1'], [⟨['n', 'e'], ['N', 'E', 'G', '.', '1'], none⟩]⟩, ⟨['w', 'a'], ['P', 'A', 'S', 'T'], [⟨['w', 'a'], ['P', 'A', 'S', 'T'], none⟩]⟩, ⟨['y', 'o'], ['c', 'h', 'i', 'l', 'd'], [⟨['y', 'o'], ['c', 'h', 'i', 'l', 'd'], none⟩]⟩, ⟨['l', 'a'], ['b', 'r', 'i', 'n', 'g'], [⟨['l', 'a'], ['b', 'r', 'i', 'n', 'g'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "negVerb"), ("infl_pattern", "auxHeaded"), ("on_aux", "negation"), ("on_aux", "subj")] }

def kwerba_neg_fut : Datum :=
  { id := "anderson2006a_kwerba_neg_fut"
    source := ⟨"anderson-2006a", "ch. 1, (52a)"⟩
    reportedIn := none
    language := "kwer1242"
    primaryText := "co kwai kot-ri-m"
    glossedTokens := [("co", "I"), ("kwai", "NEG:FUT"), ("kot-ri-m", "cut-AUG-IRR")]
    glossedWords := [⟨['c', 'o'], ['I'], [⟨['c', 'o'], ['I'], none⟩]⟩, ⟨['k', 'w', 'a', 'i'], ['N', 'E', 'G', ':', 'F', 'U', 'T'], [⟨['k', 'w', 'a', 'i'], ['N', 'E', 'G', ':', 'F', 'U', 'T'], none⟩]⟩, ⟨['k', 'o', 't', '-', 'r', 'i', '-', 'm'], ['c', 'u', 't', '-', 'A', 'U', 'G', '-', 'I', 'R', 'R'], [⟨['k', 'o', 't'], ['c', 'u', 't'], none⟩, ⟨['r', 'i'], ['A', 'U', 'G'], some '-'⟩, ⟨['m'], ['I', 'R', 'R'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "negVerb"), ("infl_pattern", "lexHeaded")] }

def kwerba_neg_past : Datum :=
  { id := "anderson2006a_kwerba_neg_past"
    source := ⟨"anderson-2006a", "ch. 1, (52b)"⟩
    reportedIn := none
    language := "kwer1242"
    primaryText := "co kot-ri-m-o baye"
    glossedTokens := [("co", "I"), ("kot-ri-m-o", "cut-AUG-IRR-NEG"), ("baye", "NEG:PST")]
    glossedWords := [⟨['c', 'o'], ['I'], [⟨['c', 'o'], ['I'], none⟩]⟩, ⟨['k', 'o', 't', '-', 'r', 'i', '-', 'm', '-', 'o'], ['c', 'u', 't', '-', 'A', 'U', 'G', '-', 'I', 'R', 'R', '-', 'N', 'E', 'G'], [⟨['k', 'o', 't'], ['c', 'u', 't'], none⟩, ⟨['r', 'i'], ['A', 'U', 'G'], some '-'⟩, ⟨['m'], ['I', 'R', 'R'], some '-'⟩, ⟨['o'], ['N', 'E', 'G'], some '-'⟩]⟩, ⟨['b', 'a', 'y', 'e'], ['N', 'E', 'G', ':', 'P', 'S', 'T'], [⟨['b', 'a', 'y', 'e'], ['N', 'E', 'G', ':', 'P', 'S', 'T'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "negVerb"), ("infl_pattern", "lexHeaded")] }

def doyayo_lexheaded : Datum :=
  { id := "anderson2006a_doyayo_lexheaded"
    source := ⟨"anderson-2006a", "ch. 3, (15a)"⟩
    reportedIn := none
    language := "doya1240"
    primaryText := "mi¹ (gi²) kpel¹-ko¹"
    glossedTokens := [("mi¹", "I"), ("(gi²)", "AUX"), ("kpel¹-ko¹", "pour-PROX")]
    glossedWords := [⟨['m', 'i', '¹'], ['I'], [⟨['m', 'i', '¹'], ['I'], none⟩]⟩, ⟨['(', 'g', 'i', '²', ')'], ['A', 'U', 'X'], [⟨['g', 'i', '²'], ['A', 'U', 'X'], none⟩]⟩, ⟨['k', 'p', 'e', 'l', '¹', '-', 'k', 'o', '¹'], ['p', 'o', 'u', 'r', '-', 'P', 'R', 'O', 'X'], [⟨['k', 'p', 'e', 'l', '¹'], ['p', 'o', 'u', 'r'], none⟩, ⟨['k', 'o', '¹'], ['P', 'R', 'O', 'X'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("infl_pattern", "lexHeaded"), ("on_aux", "subj"), ("on_lex", "tense"), ("aux_marking", "partial (tone)")] }

def doyayo_splitdoubled : Datum :=
  { id := "anderson2006a_doyayo_splitdoubled"
    source := ⟨"anderson-2006a", "ch. 5, (129)"⟩
    reportedIn := none
    language := "doya1240"
    primaryText := "hi¹-za¹ hi¹-zaa¹³ hi¹-lɔ-mɔ"
    glossedTokens := [("hi¹-za¹", "3PL-POT"), ("hi¹-zaa¹³", "3PL-come"), ("hi¹-lɔ-mɔ", "3PL-bite-2")]
    glossedWords := [⟨['h', 'i', '¹', '-', 'z', 'a', '¹'], ['3', 'P', 'L', '-', 'P', 'O', 'T'], [⟨['h', 'i', '¹'], ['3', 'P', 'L'], none⟩, ⟨['z', 'a', '¹'], ['P', 'O', 'T'], some '-'⟩]⟩, ⟨['h', 'i', '¹', '-', 'z', 'a', 'a', '¹', '³'], ['3', 'P', 'L', '-', 'c', 'o', 'm', 'e'], [⟨['h', 'i', '¹'], ['3', 'P', 'L'], none⟩, ⟨['z', 'a', 'a', '¹', '³'], ['c', 'o', 'm', 'e'], some '-'⟩]⟩, ⟨['h', 'i', '¹', '-', 'l', 'ɔ', '-', 'm', 'ɔ'], ['3', 'P', 'L', '-', 'b', 'i', 't', 'e', '-', '2'], [⟨['h', 'i', '¹'], ['3', 'P', 'L'], none⟩, ⟨['l', 'ɔ'], ['b', 'i', 't', 'e'], some '-'⟩, ⟨['m', 'ɔ'], ['2'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("infl_pattern", "splitDoubled"), ("on_aux", "subj"), ("on_lex", "subj"), ("on_lex", "obj")] }

def gorum_tiger : Datum :=
  { id := "anderson2006a_gorum_tiger"
    source := ⟨"anderson-2006a", "ch. 4, (63a)"⟩
    reportedIn := none
    language := "pare1266"
    primaryText := "kula ne-giʔ-sun miŋ ne-butoŋ-tuʔ ne-i-tuʔ"
    glossedTokens := [("kula", "tiger"), ("ne-giʔ-sun", "1-see-when"), ("miŋ", "I"), ("ne-butoŋ-tuʔ", "1-fear-NPST:AFF"), ("ne-i-tuʔ", "1-AUX-NPST:AFF")]
    glossedWords := [⟨['k', 'u', 'l', 'a'], ['t', 'i', 'g', 'e', 'r'], [⟨['k', 'u', 'l', 'a'], ['t', 'i', 'g', 'e', 'r'], none⟩]⟩, ⟨['n', 'e', '-', 'g', 'i', 'ʔ', '-', 's', 'u', 'n'], ['1', '-', 's', 'e', 'e', '-', 'w', 'h', 'e', 'n'], [⟨['n', 'e'], ['1'], none⟩, ⟨['g', 'i', 'ʔ'], ['s', 'e', 'e'], some '-'⟩, ⟨['s', 'u', 'n'], ['w', 'h', 'e', 'n'], some '-'⟩]⟩, ⟨['m', 'i', 'ŋ'], ['I'], [⟨['m', 'i', 'ŋ'], ['I'], none⟩]⟩, ⟨['n', 'e', '-', 'b', 'u', 't', 'o', 'ŋ', '-', 't', 'u', 'ʔ'], ['1', '-', 'f', 'e', 'a', 'r', '-', 'N', 'P', 'S', 'T', ':', 'A', 'F', 'F'], [⟨['n', 'e'], ['1'], none⟩, ⟨['b', 'u', 't', 'o', 'ŋ'], ['f', 'e', 'a', 'r'], some '-'⟩, ⟨['t', 'u', 'ʔ'], ['N', 'P', 'S', 'T', ':', 'A', 'F', 'F'], some '-'⟩]⟩, ⟨['n', 'e', '-', 'i', '-', 't', 'u', 'ʔ'], ['1', '-', 'A', 'U', 'X', '-', 'N', 'P', 'S', 'T', ':', 'A', 'F', 'F'], [⟨['n', 'e'], ['1'], none⟩, ⟨['i'], ['A', 'U', 'X'], some '-'⟩, ⟨['t', 'u', 'ʔ'], ['N', 'P', 'S', 'T', ':', 'A', 'F', 'F'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("infl_pattern", "doubled"), ("on_aux", "subj"), ("on_aux", "tense"), ("on_aux", "affectedness"), ("on_lex", "subj"), ("on_lex", "tense"), ("on_lex", "affectedness")] }

def gorum_vigorously : Datum :=
  { id := "anderson2006a_gorum_vigorously"
    source := ⟨"anderson-2006a", "ch. 4, (63b)"⟩
    reportedIn := none
    language := "pare1266"
    primaryText := "miŋ ne-gaʔ-ru ne-laʔ-ru"
    glossedTokens := [("miŋ", "I"), ("ne-gaʔ-ru", "1-eat-PST"), ("ne-laʔ-ru", "1-AUX-PST")]
    glossedWords := [⟨['m', 'i', 'ŋ'], ['I'], [⟨['m', 'i', 'ŋ'], ['I'], none⟩]⟩, ⟨['n', 'e', '-', 'g', 'a', 'ʔ', '-', 'r', 'u'], ['1', '-', 'e', 'a', 't', '-', 'P', 'S', 'T'], [⟨['n', 'e'], ['1'], none⟩, ⟨['g', 'a', 'ʔ'], ['e', 'a', 't'], some '-'⟩, ⟨['r', 'u'], ['P', 'S', 'T'], some '-'⟩]⟩, ⟨['n', 'e', '-', 'l', 'a', 'ʔ', '-', 'r', 'u'], ['1', '-', 'A', 'U', 'X', '-', 'P', 'S', 'T'], [⟨['n', 'e'], ['1'], none⟩, ⟨['l', 'a', 'ʔ'], ['A', 'U', 'X'], some '-'⟩, ⟨['r', 'u'], ['P', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("infl_pattern", "doubled"), ("on_aux", "subj"), ("on_aux", "tense"), ("on_lex", "subj"), ("on_lex", "tense")] }

def hemba_progressive : Datum :=
  { id := "anderson2006a_hemba_progressive"
    source := ⟨"anderson-2006a", "ch. 5, (105)"⟩
    reportedIn := none
    language := "hemb1242"
    primaryText := "tw-a-li tu-tib-a muti"
    glossedTokens := [("tw-a-li", "1PL-TNS-AUX"), ("tu-tib-a", "1PL-cut-FV/IND"), ("muti", "tree")]
    glossedWords := [⟨['t', 'w', '-', 'a', '-', 'l', 'i'], ['1', 'P', 'L', '-', 'T', 'N', 'S', '-', 'A', 'U', 'X'], [⟨['t', 'w'], ['1', 'P', 'L'], none⟩, ⟨['a'], ['T', 'N', 'S'], some '-'⟩, ⟨['l', 'i'], ['A', 'U', 'X'], some '-'⟩]⟩, ⟨['t', 'u', '-', 't', 'i', 'b', '-', 'a'], ['1', 'P', 'L', '-', 'c', 'u', 't', '-', 'F', 'V', '/', 'I', 'N', 'D'], [⟨['t', 'u'], ['1', 'P', 'L'], none⟩, ⟨['t', 'i', 'b'], ['c', 'u', 't'], some '-'⟩, ⟨['a'], ['F', 'V', '/', 'I', 'N', 'D'], some '-'⟩]⟩, ⟨['m', 'u', 't', 'i'], ['t', 'r', 'e', 'e'], [⟨['m', 'u', 't', 'i'], ['t', 'r', 'e', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("infl_pattern", "splitDoubled"), ("on_aux", "subj"), ("on_aux", "tense"), ("on_lex", "subj"), ("on_lex", "mood")] }

def pipil_capability : Datum :=
  { id := "anderson2006a_pipil_capability"
    source := ⟨"anderson-2006a", "ch. 3, (49)"⟩
    reportedIn := none
    language := "pipi1250"
    primaryText := "weli ni-nehnemi wehka"
    glossedTokens := [("weli", "CAP"), ("ni-nehnemi", "1-walk"), ("wehka", "far")]
    glossedWords := [⟨['w', 'e', 'l', 'i'], ['C', 'A', 'P'], [⟨['w', 'e', 'l', 'i'], ['C', 'A', 'P'], none⟩]⟩, ⟨['n', 'i', '-', 'n', 'e', 'h', 'n', 'e', 'm', 'i'], ['1', '-', 'w', 'a', 'l', 'k'], [⟨['n', 'i'], ['1'], none⟩, ⟨['n', 'e', 'h', 'n', 'e', 'm', 'i'], ['w', 'a', 'l', 'k'], some '-'⟩]⟩, ⟨['w', 'e', 'h', 'k', 'a'], ['f', 'a', 'r'], [⟨['w', 'e', 'h', 'k', 'a'], ['f', 'a', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("infl_pattern", "lexHeaded"), ("on_lex", "subj")] }

def pipil_progressive : Datum :=
  { id := "anderson2006a_pipil_progressive"
    source := ⟨"anderson-2006a", "ch. 5, (133b)"⟩
    reportedIn := none
    language := "pipi1250"
    primaryText := "n-yu ni-mitsin-ilwitia"
    glossedTokens := [("n-yu", "1-AUX"), ("ni-mitsin-ilwitia", "1-2PL-show")]
    glossedWords := [⟨['n', '-', 'y', 'u'], ['1', '-', 'A', 'U', 'X'], [⟨['n'], ['1'], none⟩, ⟨['y', 'u'], ['A', 'U', 'X'], some '-'⟩]⟩, ⟨['n', 'i', '-', 'm', 'i', 't', 's', 'i', 'n', '-', 'i', 'l', 'w', 'i', 't', 'i', 'a'], ['1', '-', '2', 'P', 'L', '-', 's', 'h', 'o', 'w'], [⟨['n', 'i'], ['1'], none⟩, ⟨['m', 'i', 't', 's', 'i', 'n'], ['2', 'P', 'L'], some '-'⟩, ⟨['i', 'l', 'w', 'i', 't', 'i', 'a'], ['s', 'h', 'o', 'w'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("infl_pattern", "splitDoubled"), ("on_aux", "subj"), ("on_lex", "subj"), ("on_lex", "obj")] }

def jakaltek_completive : Datum :=
  { id := "anderson2006a_jakaltek_completive"
    source := ⟨"anderson-2006a", "ch. 5, (87a)"⟩
    reportedIn := none
    language := "popt1235"
    primaryText := "šk-ach w-ila"
    glossedTokens := [("šk-ach", "COMPL-ABS2"), ("w-ila", "ERG1-see")]
    glossedWords := [⟨['š', 'k', '-', 'a', 'c', 'h'], ['C', 'O', 'M', 'P', 'L', '-', 'A', 'B', 'S', '2'], [⟨['š', 'k'], ['C', 'O', 'M', 'P', 'L'], none⟩, ⟨['a', 'c', 'h'], ['A', 'B', 'S', '2'], some '-'⟩]⟩, ⟨['w', '-', 'i', 'l', 'a'], ['E', 'R', 'G', '1', '-', 's', 'e', 'e'], [⟨['w'], ['E', 'R', 'G', '1'], none⟩, ⟨['i', 'l', 'a'], ['s', 'e', 'e'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("infl_pattern", "split"), ("on_aux", "aspect"), ("on_aux", "obj"), ("on_lex", "subj")] }

def all : List Datum := [komi_neg_pres, komi_neg_past, udihe_neg, kokota_neg, neyo_neg_past, kwerba_neg_fut, kwerba_neg_past, doyayo_lexheaded, doyayo_splitdoubled, gorum_tiger, gorum_vigorously, hemba_progressive, pipil_capability, pipil_progressive, jakaltek_completive]

end Anderson2006a.Examples
