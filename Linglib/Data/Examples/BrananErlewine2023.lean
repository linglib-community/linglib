module

public import Linglib.Data.Examples.Schema

/-!
# `BrananErlewine2023` — typed example data

Auto-generated from `Linglib/Data/Examples/BrananErlewine2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BrananErlewine2023.Examples`.
-/

@[expose] public section

namespace BrananErlewine2023.Examples

def ex_1 : Datum :=
  { id := "brananerlewine2023_1"
    source := ⟨"branan-erlewine-2023", "(1)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "A házigazda Katinak mutatta be Jánost."
    glossedTokens := [("A", "the"), ("házigazda", "host"), ("Katinak", "Cathy.DAT"), ("mutatta", "show"), ("be", "VM"), ("Jánost", "John.ACC")]
    glossedWords := [⟨[['A']], [['t', 'h', 'e']]⟩, ⟨[['h', 'á', 'z', 'i', 'g', 'a', 'z', 'd', 'a']], [['h', 'o', 's', 't']]⟩, ⟨[['K', 'a', 't', 'i', 'n', 'a', 'k']], [['C', 'a', 't', 'h', 'y', '.', 'D', 'A', 'T']]⟩, ⟨[['m', 'u', 't', 'a', 't', 't', 'a']], [['s', 'h', 'o', 'w']]⟩, ⟨[['b', 'e']], [['V', 'M']]⟩, ⟨[['J', 'á', 'n', 'o', 's', 't']], [['J', 'o', 'h', 'n', '.', 'A', 'C', 'C']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("goal", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "goal"), ("mismatch", "none")] }

def ex_2 : Datum :=
  { id := "brananerlewine2023_2"
    source := ⟨"branan-erlewine-2023", "(2)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Hanako-wa hon-mo kat-ta."
    glossedTokens := [("Hanako-wa", "Hanako-TOP"), ("hon-mo", "book-also"), ("kat-ta", "buy-PST")]
    glossedWords := [⟨[['H', 'a', 'n', 'a', 'k', 'o'], ['w', 'a']], [['H', 'a', 'n', 'a', 'k', 'o'], ['T', 'O', 'P']]⟩, ⟨[['h', 'o', 'n'], ['m', 'o']], [['b', 'o', 'o', 'k'], ['a', 'l', 's', 'o']]⟩, ⟨[['k', 'a', 't'], ['t', 'a']], [['b', 'u', 'y'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("object", .acceptable)]
    paperFeatures := [("process", "particle"), ("msf", "object"), ("mismatch", "none")] }

def ex_3 : Datum :=
  { id := "brananerlewine2023_3"
    source := ⟨"branan-erlewine-2023", "(3)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Anna a használt autót adta el."
    glossedTokens := [("Anna", "Anna"), ("a", "the"), ("használt", "used"), ("autót", "car.ACC"), ("adta", "sold"), ("el", "VM")]
    glossedWords := [⟨[['A', 'n', 'n', 'a']], [['A', 'n', 'n', 'a']]⟩, ⟨[['a']], [['t', 'h', 'e']]⟩, ⟨[['h', 'a', 's', 'z', 'n', 'á', 'l', 't']], [['u', 's', 'e', 'd']]⟩, ⟨[['a', 'u', 't', 'ó', 't']], [['c', 'a', 'r', '.', 'A', 'C', 'C']]⟩, ⟨[['a', 'd', 't', 'a']], [['s', 'o', 'l', 'd']]⟩, ⟨[['e', 'l']], [['V', 'M']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("adjective", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "object"), ("mismatch", "piedPiping")] }

def ex_4 : Datum :=
  { id := "brananerlewine2023_4"
    source := ⟨"branan-erlewine-2023", "(4)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Hanako-wa hon-o kai-mo shi, zasshi-o kai-mo shi-ta."
    glossedTokens := [("Hanako-wa", "Hanako-TOP"), ("hon-o", "book-ACC"), ("kai-mo", "buy-also"), ("shi", "do"), ("zasshi-o", "magazine-ACC"), ("kai-mo", "buy-also"), ("shi-ta", "do-PST")]
    glossedWords := [⟨[['H', 'a', 'n', 'a', 'k', 'o'], ['w', 'a']], [['H', 'a', 'n', 'a', 'k', 'o'], ['T', 'O', 'P']]⟩, ⟨[['h', 'o', 'n'], ['o']], [['b', 'o', 'o', 'k'], ['A', 'C', 'C']]⟩, ⟨[['k', 'a', 'i'], ['m', 'o']], [['b', 'u', 'y'], ['a', 'l', 's', 'o']]⟩, ⟨[['s', 'h', 'i']], [['d', 'o']]⟩, ⟨[['z', 'a', 's', 's', 'h', 'i'], ['o']], [['m', 'a', 'g', 'a', 'z', 'i', 'n', 'e'], ['A', 'C', 'C']]⟩, ⟨[['k', 'a', 'i'], ['m', 'o']], [['b', 'u', 'y'], ['a', 'l', 's', 'o']]⟩, ⟨[['s', 'h', 'i'], ['t', 'a']], [['d', 'o'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("object", .acceptable)]
    paperFeatures := [("process", "particle"), ("msf", "predicate"), ("mismatch", "piedPiping")] }

def ex_7 : Datum :=
  { id := "brananerlewine2023_7"
    source := ⟨"branan-erlewine-2023", "(7)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Péter a Hamletet olvasta fel a kertben, nem pedig úszott."
    glossedTokens := [("Péter", "Peter"), ("a", "the"), ("Hamletet", "Hamlet.ACC"), ("olvasta", "read"), ("fel", "VM"), ("a", "the"), ("kertben", "garden.INE"), ("nem", "not"), ("pedig", "rather"), ("úszott", "swim")]
    glossedWords := [⟨[['P', 'é', 't', 'e', 'r']], [['P', 'e', 't', 'e', 'r']]⟩, ⟨[['a']], [['t', 'h', 'e']]⟩, ⟨[['H', 'a', 'm', 'l', 'e', 't', 'e', 't']], [['H', 'a', 'm', 'l', 'e', 't', '.', 'A', 'C', 'C']]⟩, ⟨[['o', 'l', 'v', 'a', 's', 't', 'a']], [['r', 'e', 'a', 'd']]⟩, ⟨[['f', 'e', 'l']], [['V', 'M']]⟩, ⟨[['a']], [['t', 'h', 'e']]⟩, ⟨[['k', 'e', 'r', 't', 'b', 'e', 'n']], [['g', 'a', 'r', 'd', 'e', 'n', '.', 'I', 'N', 'E']]⟩, ⟨[['n', 'e', 'm']], [['n', 'o', 't']]⟩, ⟨[['p', 'e', 'd', 'i', 'g']], [['r', 'a', 't', 'h', 'e', 'r']]⟩, ⟨[['ú', 's', 'z', 'o', 't', 't']], [['s', 'w', 'i', 'm']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("predicate", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "object"), ("mismatch", "antiPiedPiping")] }

def ex_8 : Datum :=
  { id := "brananerlewine2023_8"
    source := ⟨"branan-erlewine-2023", "(8)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Ame-mo furu-shi, kaze-mo fuku."
    glossedTokens := [("Ame-mo", "rain-also"), ("furu-shi", "falls-CONJ"), ("kaze-mo", "wind-also"), ("fuku", "blows")]
    glossedWords := [⟨[['A', 'm', 'e'], ['m', 'o']], [['r', 'a', 'i', 'n'], ['a', 'l', 's', 'o']]⟩, ⟨[['f', 'u', 'r', 'u'], ['s', 'h', 'i']], [['f', 'a', 'l', 'l', 's'], ['C', 'O', 'N', 'J']]⟩, ⟨[['k', 'a', 'z', 'e'], ['m', 'o']], [['w', 'i', 'n', 'd'], ['a', 'l', 's', 'o']]⟩, ⟨[['f', 'u', 'k', 'u']], [['b', 'l', 'o', 'w', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("sentence", .acceptable)]
    paperFeatures := [("process", "particle"), ("msf", "subject"), ("mismatch", "antiPiedPiping")] }

def ex_17b : Datum :=
  { id := "brananerlewine2023_17b"
    source := ⟨"branan-erlewine-2023", "(17b)"⟩
    reportedIn := none
    language := "yaey1239"
    primaryText := "Hajasi-san-du ziroo-ba bari."
    glossedTokens := [("Hajasi-san-du", "Hayashi-san-PRT"), ("ziroo-ba", "Jiro-BA"), ("bari", "hit")]
    glossedWords := [⟨[['H', 'a', 'j', 'a', 's', 'i'], ['s', 'a', 'n'], ['d', 'u']], [['H', 'a', 'y', 'a', 's', 'h', 'i'], ['s', 'a', 'n'], ['P', 'R', 'T']]⟩, ⟨[['z', 'i', 'r', 'o', 'o'], ['b', 'a']], [['J', 'i', 'r', 'o'], ['B', 'A']]⟩, ⟨[['b', 'a', 'r', 'i']], [['h', 'i', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Answer to 'What happened?'"
    judgment := .acceptable
    alternatives := []
    readings := [("sentence", .acceptable)]
    paperFeatures := [("process", "particle"), ("msf", "subject"), ("leftmost", "strong"), ("mismatch", "antiPiedPiping")] }

def ex_18b : Datum :=
  { id := "brananerlewine2023_18b"
    source := ⟨"branan-erlewine-2023", "(18b)"⟩
    reportedIn := none
    language := "yaey1239"
    primaryText := "Kunu midunpïto-o izï-ba-du fai."
    glossedTokens := [("Kunu", "this"), ("midunpïto-o", "woman-TOP"), ("izï-ba-du", "fish-BA-PRT"), ("fai", "ate")]
    glossedWords := [⟨[['K', 'u', 'n', 'u']], [['t', 'h', 'i', 's']]⟩, ⟨[['m', 'i', 'd', 'u', 'n', 'p', 'ï', 't', 'o'], ['o']], [['w', 'o', 'm', 'a', 'n'], ['T', 'O', 'P']]⟩, ⟨[['i', 'z', 'ï'], ['b', 'a'], ['d', 'u']], [['f', 'i', 's', 'h'], ['B', 'A'], ['P', 'R', 'T']]⟩, ⟨[['f', 'a', 'i']], [['a', 't', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Answer to 'What did that woman do?'"
    judgment := .acceptable
    alternatives := []
    readings := [("predicate", .acceptable)]
    paperFeatures := [("process", "particle"), ("msf", "object"), ("leftmost", "strong"), ("mismatch", "antiPiedPiping")] }

def ex_21 : Datum :=
  { id := "brananerlewine2023_21"
    source := ⟨"branan-erlewine-2023", "(21)"⟩
    reportedIn := none
    language := "ishk1246"
    primaryText := "Salima kulča-məs pacu."
    glossedTokens := [("Salima", "Salima"), ("kulča-məs", "kulcha-also"), ("pacu", "bake")]
    glossedWords := [⟨[['S', 'a', 'l', 'i', 'm', 'a']], [['S', 'a', 'l', 'i', 'm', 'a']]⟩, ⟨[['k', 'u', 'l', 'č', 'a'], ['m', 'ə', 's']], [['k', 'u', 'l', 'c', 'h', 'a'], ['a', 'l', 's', 'o']]⟩, ⟨[['p', 'a', 'c', 'u']], [['b', 'a', 'k', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("object", .acceptable), ("predicate", .acceptable)]
    paperFeatures := [("process", "particle"), ("msf", "object"), ("leftmost", "strong")] }

def ex_30a : Datum :=
  { id := "brananerlewine2023_30a"
    source := ⟨"branan-erlewine-2023", "(30a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taro-ga tako-o tabe-mo shi-ta."
    glossedTokens := [("Taro-ga", "Taro-NOM"), ("tako-o", "octopus-ACC"), ("tabe-mo", "eat-also"), ("shi-ta", "do-PST")]
    glossedWords := [⟨[['T', 'a', 'r', 'o'], ['g', 'a']], [['T', 'a', 'r', 'o'], ['N', 'O', 'M']]⟩, ⟨[['t', 'a', 'k', 'o'], ['o']], [['o', 'c', 't', 'o', 'p', 'u', 's'], ['A', 'C', 'C']]⟩, ⟨[['t', 'a', 'b', 'e'], ['m', 'o']], [['e', 'a', 't'], ['a', 'l', 's', 'o']]⟩, ⟨[['s', 'h', 'i'], ['t', 'a']], [['d', 'o'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("predicate", .acceptable), ("object", .acceptable)]
    paperFeatures := [("process", "particle"), ("msf", "predicate"), ("leftmost", "weak")] }

def ex_30b : Datum :=
  { id := "brananerlewine2023_30b"
    source := ⟨"branan-erlewine-2023", "(30b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taro-ga tako-mo tabe-ta."
    glossedTokens := [("Taro-ga", "Taro-NOM"), ("tako-mo", "octopus-also"), ("tabe-ta", "eat-PST")]
    glossedWords := [⟨[['T', 'a', 'r', 'o'], ['g', 'a']], [['T', 'a', 'r', 'o'], ['N', 'O', 'M']]⟩, ⟨[['t', 'a', 'k', 'o'], ['m', 'o']], [['o', 'c', 't', 'o', 'p', 'u', 's'], ['a', 'l', 's', 'o']]⟩, ⟨[['t', 'a', 'b', 'e'], ['t', 'a']], [['e', 'a', 't'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("predicate", .acceptable), ("object", .acceptable)]
    paperFeatures := [("process", "particle"), ("msf", "object"), ("leftmost", "weak")] }

def ex_38 : Datum :=
  { id := "brananerlewine2023_38"
    source := ⟨"branan-erlewine-2023", "(38)"⟩
    reportedIn := none
    language := "ishk1246"
    primaryText := "Wai mol-məs xi dusto-i zənayu isu."
    glossedTokens := [("Wai", "DEM"), ("mol-məs", "husband-also"), ("xi", "REFL"), ("dusto-i", "hands-ACC"), ("zənayu", "wash"), ("isu", "come")]
    glossedWords := [⟨[['W', 'a', 'i']], [['D', 'E', 'M']]⟩, ⟨[['m', 'o', 'l'], ['m', 'ə', 's']], [['h', 'u', 's', 'b', 'a', 'n', 'd'], ['a', 'l', 's', 'o']]⟩, ⟨[['x', 'i']], [['R', 'E', 'F', 'L']]⟩, ⟨[['d', 'u', 's', 't', 'o'], ['i']], [['h', 'a', 'n', 'd', 's'], ['A', 'C', 'C']]⟩, ⟨[['z', 'ə', 'n', 'a', 'y', 'u']], [['w', 'a', 's', 'h']]⟩, ⟨[['i', 's', 'u']], [['c', 'o', 'm', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("subject", .acceptable), ("sentence", .acceptable)]
    paperFeatures := [("process", "particle"), ("msf", "subject"), ("leftmost", "strong")] }

def ex_65_goal : Datum :=
  { id := "brananerlewine2023_65_goal"
    source := ⟨"branan-erlewine-2023", "(65)"⟩
    reportedIn := none
    language := "tibe1272"
    primaryText := "Kun.dga’ khyi-la-yang kha.lag sprad.gi.’dug."
    glossedTokens := [("Kun.dga’", "Kunga"), ("khyi-la-yang", "dog-DAT-also"), ("kha.lag", "food"), ("sprad.gi.’dug", "gives")]
    glossedWords := [⟨[['K', 'u', 'n', 'd', 'g', 'a', '’']], [['K', 'u', 'n', 'g', 'a']]⟩, ⟨[['k', 'h', 'y', 'i'], ['l', 'a'], ['y', 'a', 'n', 'g']], [['d', 'o', 'g'], ['D', 'A', 'T'], ['a', 'l', 's', 'o']]⟩, ⟨[['k', 'h', 'a', 'l', 'a', 'g']], [['f', 'o', 'o', 'd']]⟩, ⟨[['s', 'p', 'r', 'a', 'd', 'g', 'i', '’', 'd', 'u', 'g']], [['g', 'i', 'v', 'e', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Kunga's a very good person. She prays at the temple every day."
    judgment := .acceptable
    alternatives := []
    readings := [("predicate", .acceptable)]
    paperFeatures := [("process", "particle"), ("msf", "goal"), ("leftmost", "weak")] }

def ex_65_theme : Datum :=
  { id := "brananerlewine2023_65_theme"
    source := ⟨"branan-erlewine-2023", "(65)"⟩
    reportedIn := none
    language := "tibe1272"
    primaryText := "Kun.dga’ khyi-la kha.lag-yang sprad.gi.’dug."
    glossedTokens := [("Kun.dga’", "Kunga"), ("khyi-la", "dog-DAT"), ("kha.lag-yang", "food-also"), ("sprad.gi.’dug", "gives")]
    glossedWords := [⟨[['K', 'u', 'n', 'd', 'g', 'a', '’']], [['K', 'u', 'n', 'g', 'a']]⟩, ⟨[['k', 'h', 'y', 'i'], ['l', 'a']], [['d', 'o', 'g'], ['D', 'A', 'T']]⟩, ⟨[['k', 'h', 'a', 'l', 'a', 'g'], ['y', 'a', 'n', 'g']], [['f', 'o', 'o', 'd'], ['a', 'l', 's', 'o']]⟩, ⟨[['s', 'p', 'r', 'a', 'd', 'g', 'i', '’', 'd', 'u', 'g']], [['g', 'i', 'v', 'e', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Kunga's a very good person. She prays at the temple every day."
    judgment := .marginal
    alternatives := []
    readings := [("predicate", .marginal)]
    paperFeatures := [("process", "particle"), ("msf", "theme"), ("leftmost", "weak")] }

def ex_66a : Datum :=
  { id := "brananerlewine2023_66a"
    source := ⟨"branan-erlewine-2023", "(66a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taro-mo piano-o hiita."
    glossedTokens := [("Taro-mo", "Taro-also"), ("piano-o", "piano-ACC"), ("hiita", "played")]
    glossedWords := [⟨[['T', 'a', 'r', 'o'], ['m', 'o']], [['T', 'a', 'r', 'o'], ['a', 'l', 's', 'o']]⟩, ⟨[['p', 'i', 'a', 'n', 'o'], ['o']], [['p', 'i', 'a', 'n', 'o'], ['A', 'C', 'C']]⟩, ⟨[['h', 'i', 'i', 't', 'a']], [['p', 'l', 'a', 'y', 'e', 'd']]⟩]
    lgrConformance := some .morphemeAligned
    context := "At yesterday's party, not only did Hanako dance, but ..."
    judgment := .acceptable
    alternatives := []
    readings := [("sentence", .acceptable)]
    paperFeatures := [("process", "particle"), ("msf", "subject"), ("leftmost", "weak")] }

def ex_66b : Datum :=
  { id := "brananerlewine2023_66b"
    source := ⟨"branan-erlewine-2023", "(66b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taro-ga piano-mo hiita."
    glossedTokens := [("Taro-ga", "Taro-NOM"), ("piano-mo", "piano-also"), ("hiita", "played")]
    glossedWords := [⟨[['T', 'a', 'r', 'o'], ['g', 'a']], [['T', 'a', 'r', 'o'], ['N', 'O', 'M']]⟩, ⟨[['p', 'i', 'a', 'n', 'o'], ['m', 'o']], [['p', 'i', 'a', 'n', 'o'], ['a', 'l', 's', 'o']]⟩, ⟨[['h', 'i', 'i', 't', 'a']], [['p', 'l', 'a', 'y', 'e', 'd']]⟩]
    lgrConformance := some .morphemeAligned
    context := "At yesterday's party, not only did Hanako dance, but ..."
    judgment := .marginal
    alternatives := []
    readings := [("sentence", .marginal)]
    paperFeatures := [("process", "particle"), ("msf", "object"), ("leftmost", "weak")] }

def ex_67_goal : Datum :=
  { id := "brananerlewine2023_67_goal"
    source := ⟨"branan-erlewine-2023", "(67)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "Vo sirf bachcho-ko hii tohfe de payaa hai."
    glossedTokens := [("Vo", "3SG"), ("sirf", "only"), ("bachcho-ko", "children-DAT"), ("hii", "PRT"), ("tohfe", "gifts"), ("de", "give"), ("payaa", "able"), ("hai", "AUX")]
    glossedWords := [⟨[['V', 'o']], [['3', 'S', 'G']]⟩, ⟨[['s', 'i', 'r', 'f']], [['o', 'n', 'l', 'y']]⟩, ⟨[['b', 'a', 'c', 'h', 'c', 'h', 'o'], ['k', 'o']], [['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n'], ['D', 'A', 'T']]⟩, ⟨[['h', 'i', 'i']], [['P', 'R', 'T']]⟩, ⟨[['t', 'o', 'h', 'f', 'e']], [['g', 'i', 'f', 't', 's']]⟩, ⟨[['d', 'e']], [['g', 'i', 'v', 'e']]⟩, ⟨[['p', 'a', 'y', 'a', 'a']], [['a', 'b', 'l', 'e']]⟩, ⟨[['h', 'a', 'i']], [['A', 'U', 'X']]⟩]
    lgrConformance := some .morphemeAligned
    context := "During Diwali, Pulkit plans to feed the poor and also distribute gifts to children. However, due to some emergency, he fails to be able to feed the poor."
    judgment := .acceptable
    alternatives := []
    readings := [("predicate", .acceptable)]
    paperFeatures := [("process", "particle"), ("msf", "goal"), ("leftmost", "weak")] }

def ex_67_theme : Datum :=
  { id := "brananerlewine2023_67_theme"
    source := ⟨"branan-erlewine-2023", "(67)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "Vo sirf bachcho-ko tohfe hii de payaa hai."
    glossedTokens := [("Vo", "3SG"), ("sirf", "only"), ("bachcho-ko", "children-DAT"), ("tohfe", "gifts"), ("hii", "PRT"), ("de", "give"), ("payaa", "able"), ("hai", "AUX")]
    glossedWords := [⟨[['V', 'o']], [['3', 'S', 'G']]⟩, ⟨[['s', 'i', 'r', 'f']], [['o', 'n', 'l', 'y']]⟩, ⟨[['b', 'a', 'c', 'h', 'c', 'h', 'o'], ['k', 'o']], [['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n'], ['D', 'A', 'T']]⟩, ⟨[['t', 'o', 'h', 'f', 'e']], [['g', 'i', 'f', 't', 's']]⟩, ⟨[['h', 'i', 'i']], [['P', 'R', 'T']]⟩, ⟨[['d', 'e']], [['g', 'i', 'v', 'e']]⟩, ⟨[['p', 'a', 'y', 'a', 'a']], [['a', 'b', 'l', 'e']]⟩, ⟨[['h', 'a', 'i']], [['A', 'U', 'X']]⟩]
    lgrConformance := some .morphemeAligned
    context := "During Diwali, Pulkit plans to feed the poor and also distribute gifts to children. However, due to some emergency, he fails to be able to feed the poor."
    judgment := .marginal
    alternatives := []
    readings := [("predicate", .marginal)]
    paperFeatures := [("process", "particle"), ("msf", "theme"), ("leftmost", "weak")] }

def ex_68a : Datum :=
  { id := "brananerlewine2023_68a"
    source := ⟨"branan-erlewine-2023", "(68a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Bücher hab ich ins Regal gestellt."
    glossedTokens := [("Die", "the"), ("Bücher", "books"), ("hab", "have"), ("ich", "1SG"), ("ins", "into.the"), ("Regal", "shelf"), ("gestellt", "placed")]
    glossedWords := [⟨[['D', 'i', 'e']], [['t', 'h', 'e']]⟩, ⟨[['B', 'ü', 'c', 'h', 'e', 'r']], [['b', 'o', 'o', 'k', 's']]⟩, ⟨[['h', 'a', 'b']], [['h', 'a', 'v', 'e']]⟩, ⟨[['i', 'c', 'h']], [['1', 'S', 'G']]⟩, ⟨[['i', 'n', 's']], [['i', 'n', 't', 'o', '.', 't', 'h', 'e']]⟩, ⟨[['R', 'e', 'g', 'a', 'l']], [['s', 'h', 'e', 'l', 'f']]⟩, ⟨[['g', 'e', 's', 't', 'e', 'l', 'l', 't']], [['p', 'l', 'a', 'c', 'e', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("theme", .acceptable), ("predicate", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "theme"), ("leftmost", "strong")] }

def ex_68b : Datum :=
  { id := "brananerlewine2023_68b"
    source := ⟨"branan-erlewine-2023", "(68b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Ins Regal hab ich die Bücher gestellt."
    glossedTokens := [("Ins", "into.the"), ("Regal", "shelf"), ("hab", "have"), ("ich", "1SG"), ("die", "the"), ("Bücher", "books"), ("gestellt", "placed")]
    glossedWords := [⟨[['I', 'n', 's']], [['i', 'n', 't', 'o', '.', 't', 'h', 'e']]⟩, ⟨[['R', 'e', 'g', 'a', 'l']], [['s', 'h', 'e', 'l', 'f']]⟩, ⟨[['h', 'a', 'b']], [['h', 'a', 'v', 'e']]⟩, ⟨[['i', 'c', 'h']], [['1', 'S', 'G']]⟩, ⟨[['d', 'i', 'e']], [['t', 'h', 'e']]⟩, ⟨[['B', 'ü', 'c', 'h', 'e', 'r']], [['b', 'o', 'o', 'k', 's']]⟩, ⟨[['g', 'e', 's', 't', 'e', 'l', 'l', 't']], [['p', 'l', 'a', 'c', 'e', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("goal", .acceptable), ("predicate", .ungrammatical)]
    paperFeatures := [("process", "movement"), ("msf", "goal"), ("leftmost", "strong")] }

def ex_69a : Datum :=
  { id := "brananerlewine2023_69a"
    source := ⟨"branan-erlewine-2023", "(69a)"⟩
    reportedIn := none
    language := "kiku1240"
    primaryText := "Ne-mwana Abdul aðomaɣera iβuku."
    glossedTokens := [("Ne-mwana", "PRT-1.child"), ("Abdul", "Abdul"), ("aðomaɣera", "read"), ("iβuku", "book")]
    glossedWords := [⟨[['N', 'e'], ['m', 'w', 'a', 'n', 'a']], [['P', 'R', 'T'], ['1', '.', 'c', 'h', 'i', 'l', 'd']]⟩, ⟨[['A', 'b', 'd', 'u', 'l']], [['A', 'b', 'd', 'u', 'l']]⟩, ⟨[['a', 'ð', 'o', 'm', 'a', 'ɣ', 'e', 'r', 'a']], [['r', 'e', 'a', 'd']]⟩, ⟨[['i', 'β', 'u', 'k', 'u']], [['b', 'o', 'o', 'k']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Q: What does Abdul do?"
    judgment := .acceptable
    alternatives := []
    readings := [("predicate", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "goal"), ("leftmost", "weak")] }

def ex_69b : Datum :=
  { id := "brananerlewine2023_69b"
    source := ⟨"branan-erlewine-2023", "(69b)"⟩
    reportedIn := none
    language := "kiku1240"
    primaryText := "Ne-iβuku Abdul aðomaɣera mwana."
    glossedTokens := [("Ne-iβuku", "PRT-book"), ("Abdul", "Abdul"), ("aðomaɣera", "read"), ("mwana", "child")]
    glossedWords := [⟨[['N', 'e'], ['i', 'β', 'u', 'k', 'u']], [['P', 'R', 'T'], ['b', 'o', 'o', 'k']]⟩, ⟨[['A', 'b', 'd', 'u', 'l']], [['A', 'b', 'd', 'u', 'l']]⟩, ⟨[['a', 'ð', 'o', 'm', 'a', 'ɣ', 'e', 'r', 'a']], [['r', 'e', 'a', 'd']]⟩, ⟨[['m', 'w', 'a', 'n', 'a']], [['c', 'h', 'i', 'l', 'd']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Q: What does Abdul do?"
    judgment := .marginal
    alternatives := []
    readings := [("predicate", .marginal)]
    paperFeatures := [("process", "movement"), ("msf", "theme"), ("leftmost", "weak")] }

def ex_70a : Datum :=
  { id := "brananerlewine2023_70a"
    source := ⟨"branan-erlewine-2023", "(70a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Tsìnà shàshi koñu."
    glossedTokens := [("Tsìnà", "dog"), ("shàshi", "ate"), ("koñu", "meat")]
    glossedWords := [⟨[['T', 's', 'ì', 'n', 'à']], [['d', 'o', 'g']]⟩, ⟨[['s', 'h', 'à', 's', 'h', 'i']], [['a', 't', 'e']]⟩, ⟨[['k', 'o', 'ñ', 'u']], [['m', 'e', 'a', 't']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("sentence", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "subject"), ("leftmost", "free")] }

def ex_70b : Datum :=
  { id := "brananerlewine2023_70b"
    source := ⟨"branan-erlewine-2023", "(70b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Koñu shàshi tsìnà."
    glossedTokens := [("Koñu", "meat"), ("shàshi", "ate"), ("tsìnà", "dog")]
    glossedWords := [⟨[['K', 'o', 'ñ', 'u']], [['m', 'e', 'a', 't']]⟩, ⟨[['s', 'h', 'à', 's', 'h', 'i']], [['a', 't', 'e']]⟩, ⟨[['t', 's', 'ì', 'n', 'à']], [['d', 'o', 'g']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("sentence", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "object"), ("leftmost", "free")] }

def ex_109a : Datum :=
  { id := "brananerlewine2023_109a"
    source := ⟨"branan-erlewine-2023", "(109a)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Janu Linda hledala."
    glossedTokens := [("Janu", "Jana.ACC"), ("Linda", "Linda.NOM"), ("hledala", "looked.for.SG.F")]
    glossedWords := [⟨[['J', 'a', 'n', 'u']], [['J', 'a', 'n', 'a', '.', 'A', 'C', 'C']]⟩, ⟨[['L', 'i', 'n', 'd', 'a']], [['L', 'i', 'n', 'd', 'a', '.', 'N', 'O', 'M']]⟩, ⟨[['h', 'l', 'e', 'd', 'a', 'l', 'a']], [['l', 'o', 'o', 'k', 'e', 'd', '.', 'f', 'o', 'r', '.', 'S', 'G', '.', 'F']]⟩]
    lgrConformance := some .wordAligned
    context := "Q: What's new?"
    judgment := .unacceptable
    alternatives := []
    readings := [("sentence", .unacceptable), ("object", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "object"), ("leftmost", "strong")] }

def ex_109b : Datum :=
  { id := "brananerlewine2023_109b"
    source := ⟨"branan-erlewine-2023", "(109b)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Janu někdo hledal."
    glossedTokens := [("Janu", "Jana.ACC"), ("někdo", "somebody.NOM"), ("hledal", "looked.for.SG.M")]
    glossedWords := [⟨[['J', 'a', 'n', 'u']], [['J', 'a', 'n', 'a', '.', 'A', 'C', 'C']]⟩, ⟨[['n', 'ě', 'k', 'd', 'o']], [['s', 'o', 'm', 'e', 'b', 'o', 'd', 'y', '.', 'N', 'O', 'M']]⟩, ⟨[['h', 'l', 'e', 'd', 'a', 'l']], [['l', 'o', 'o', 'k', 'e', 'd', '.', 'f', 'o', 'r', '.', 'S', 'G', '.', 'M']]⟩]
    lgrConformance := some .wordAligned
    context := "Q: What's new?"
    judgment := .acceptable
    alternatives := []
    readings := [("sentence", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "object"), ("leftmost", "strong"), ("skipped", "subject")] }

def ex_111a : Datum :=
  { id := "brananerlewine2023_111a"
    source := ⟨"branan-erlewine-2023", "(111a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "dareka-mo piano-o hiita."
    glossedTokens := [("dareka-mo", "someone-also"), ("piano-o", "piano-ACC"), ("hiita", "played")]
    glossedWords := [⟨[['d', 'a', 'r', 'e', 'k', 'a'], ['m', 'o']], [['s', 'o', 'm', 'e', 'o', 'n', 'e'], ['a', 'l', 's', 'o']]⟩, ⟨[['p', 'i', 'a', 'n', 'o'], ['o']], [['p', 'i', 'a', 'n', 'o'], ['A', 'C', 'C']]⟩, ⟨[['h', 'i', 'i', 't', 'a']], [['p', 'l', 'a', 'y', 'e', 'd']]⟩]
    lgrConformance := some .morphemeAligned
    context := "At yesterday's party, not only did Hanako dance a dance, but ..."
    judgment := .unacceptable
    alternatives := []
    readings := [("sentence", .unacceptable)]
    paperFeatures := [("process", "particle"), ("msf", "subject"), ("leftmost", "weak"), ("skipped", "subject")] }

def ex_111b : Datum :=
  { id := "brananerlewine2023_111b"
    source := ⟨"branan-erlewine-2023", "(111b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "dareka-ga piano-mo hiita."
    glossedTokens := [("dareka-ga", "someone-NOM"), ("piano-mo", "piano-also"), ("hiita", "played")]
    glossedWords := [⟨[['d', 'a', 'r', 'e', 'k', 'a'], ['g', 'a']], [['s', 'o', 'm', 'e', 'o', 'n', 'e'], ['N', 'O', 'M']]⟩, ⟨[['p', 'i', 'a', 'n', 'o'], ['m', 'o']], [['p', 'i', 'a', 'n', 'o'], ['a', 'l', 's', 'o']]⟩, ⟨[['h', 'i', 'i', 't', 'a']], [['p', 'l', 'a', 'y', 'e', 'd']]⟩]
    lgrConformance := some .morphemeAligned
    context := "At yesterday's party, not only did Hanako dance a dance, but ..."
    judgment := .acceptable
    alternatives := []
    readings := [("sentence", .acceptable)]
    paperFeatures := [("process", "particle"), ("msf", "object"), ("leftmost", "weak"), ("skipped", "subject")] }

def ex_114a : Datum :=
  { id := "brananerlewine2023_114a"
    source := ⟨"branan-erlewine-2023", "(114a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "B’àràayii nèe su-kà yi mîn saatàa!"
    glossedTokens := [("B’àràayii", "robbers"), ("nèe", "FM"), ("su-kà", "3PL-REL"), ("yi", "do"), ("mîn", "to.me"), ("saatàa", "theft")]
    glossedWords := [⟨[['B', '’', 'à', 'r', 'à', 'a', 'y', 'i', 'i']], [['r', 'o', 'b', 'b', 'e', 'r', 's']]⟩, ⟨[['n', 'è', 'e']], [['F', 'M']]⟩, ⟨[['s', 'u'], ['k', 'à']], [['3', 'P', 'L'], ['R', 'E', 'L']]⟩, ⟨[['y', 'i']], [['d', 'o']]⟩, ⟨[['m', 'î', 'n']], [['t', 'o', '.', 'm', 'e']]⟩, ⟨[['s', 'a', 'a', 't', 'à', 'a']], [['t', 'h', 'e', 'f', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("sentence", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "subject"), ("leftmost", "strong")] }

def ex_114b : Datum :=
  { id := "brananerlewine2023_114b"
    source := ⟨"branan-erlewine-2023", "(114b)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Dabboobi-n jeejìi nèe mutàanee su-kà kaamàa."
    glossedTokens := [("Dabboobi-n", "animals-of"), ("jeejìi", "wild"), ("nèe", "FM"), ("mutàanee", "men"), ("su-kà", "3PL-REL"), ("kaamàa", "catch")]
    glossedWords := [⟨[['D', 'a', 'b', 'b', 'o', 'o', 'b', 'i'], ['n']], [['a', 'n', 'i', 'm', 'a', 'l', 's'], ['o', 'f']]⟩, ⟨[['j', 'e', 'e', 'j', 'ì', 'i']], [['w', 'i', 'l', 'd']]⟩, ⟨[['n', 'è', 'e']], [['F', 'M']]⟩, ⟨[['m', 'u', 't', 'à', 'a', 'n', 'e', 'e']], [['m', 'e', 'n']]⟩, ⟨[['s', 'u'], ['k', 'à']], [['3', 'P', 'L'], ['R', 'E', 'L']]⟩, ⟨[['k', 'a', 'a', 'm', 'à', 'a']], [['c', 'a', 't', 'c', 'h']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("sentence", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "object"), ("leftmost", "strong"), ("skipped", "subject")] }

def ex_120a : Datum :=
  { id := "brananerlewine2023_120a"
    source := ⟨"branan-erlewine-2023", "(120a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Whose picture did you frame?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("wh", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "phrase"), ("leftmost", "strong")] }

def ex_120b : Datum :=
  { id := "brananerlewine2023_120b"
    source := ⟨"branan-erlewine-2023", "(120b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A picture of whom did you frame?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := [("wh", .ungrammatical)]
    paperFeatures := [("process", "movement"), ("msf", "phrase"), ("leftmost", "strong")] }

def ex_121a : Datum :=
  { id := "brananerlewine2023_121a"
    source := ⟨"branan-erlewine-2023", "(121a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Whose brother's friend's father did you see?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("wh", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "phrase"), ("leftmost", "strong")] }

def ex_121b : Datum :=
  { id := "brananerlewine2023_121b"
    source := ⟨"branan-erlewine-2023", "(121b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The father of whose brother's friend did you see?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := [("wh", .ungrammatical)]
    paperFeatures := [("process", "movement"), ("msf", "phrase"), ("leftmost", "strong")] }

def ex_123 : Datum :=
  { id := "brananerlewine2023_123"
    source := ⟨"branan-erlewine-2023", "(123)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "To which student's friend did you speak?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("wh", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "phrase"), ("leftmost", "strong"), ("skipped", "phrase")] }

def ex_124 : Datum :=
  { id := "brananerlewine2023_124"
    source := ⟨"branan-erlewine-2023", "(124)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "ob eās-que rēs"
    glossedTokens := [("ob", "because"), ("eās-que", "these-also"), ("rēs", "things")]
    glossedWords := [⟨[['o', 'b']], [['b', 'e', 'c', 'a', 'u', 's', 'e']]⟩, ⟨[['e', 'ā', 's'], ['q', 'u', 'e']], [['t', 'h', 'e', 's', 'e'], ['a', 'l', 's', 'o']]⟩, ⟨[['r', 'ē', 's']], [['t', 'h', 'i', 'n', 'g', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("phrase", .acceptable)]
    paperFeatures := [("process", "particle"), ("msf", "demonstrative"), ("leftmost", "strong"), ("skipped", "phrase")] }

def ex_125 : Datum :=
  { id := "brananerlewine2023_125"
    source := ⟨"branan-erlewine-2023", "(125)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Interesno na sestre druga č’ej materi on ženilsja."
    glossedTokens := [("Interesno", "interesting"), ("na", "on"), ("sestre", "sister"), ("druga", "friend"), ("č’ej", "whose"), ("materi", "mother"), ("on", "he"), ("ženilsja", "married")]
    glossedWords := [⟨[['I', 'n', 't', 'e', 'r', 'e', 's', 'n', 'o']], [['i', 'n', 't', 'e', 'r', 'e', 's', 't', 'i', 'n', 'g']]⟩, ⟨[['n', 'a']], [['o', 'n']]⟩, ⟨[['s', 'e', 's', 't', 'r', 'e']], [['s', 'i', 's', 't', 'e', 'r']]⟩, ⟨[['d', 'r', 'u', 'g', 'a']], [['f', 'r', 'i', 'e', 'n', 'd']]⟩, ⟨[['č', '’', 'e', 'j']], [['w', 'h', 'o', 's', 'e']]⟩, ⟨[['m', 'a', 't', 'e', 'r', 'i']], [['m', 'o', 't', 'h', 'e', 'r']]⟩, ⟨[['o', 'n']], [['h', 'e']]⟩, ⟨[['ž', 'e', 'n', 'i', 'l', 's', 'j', 'a']], [['m', 'a', 'r', 'r', 'i', 'e', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("wh", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "phrase"), ("leftmost", "free")] }

def ex_126 : Datum :=
  { id := "brananerlewine2023_126"
    source := ⟨"branan-erlewine-2023", "(126)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Reports the height of the lettering on the covers of which the government prescribes should be abolished."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("wh", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "phrase"), ("leftmost", "free")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_7, ex_8, ex_17b, ex_18b, ex_21, ex_30a, ex_30b, ex_38, ex_65_goal, ex_65_theme, ex_66a, ex_66b, ex_67_goal, ex_67_theme, ex_68a, ex_68b, ex_69a, ex_69b, ex_70a, ex_70b, ex_109a, ex_109b, ex_111a, ex_111b, ex_114a, ex_114b, ex_120a, ex_120b, ex_121a, ex_121b, ex_123, ex_124, ex_125, ex_126]

end BrananErlewine2023.Examples
