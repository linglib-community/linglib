module

public import Linglib.Data.Examples.Schema

/-!
# `Zimmermann2008` — typed example data

Auto-generated from `Linglib/Data/Examples/Zimmermann2008.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Zimmermann2008.Examples`.
-/

@[expose] public section

namespace Zimmermann2008.Examples

def ex_11a : Datum :=
  { id := "zimmermann2008_11a"
    source := ⟨"zimmermann-2008", "(11a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Audù bà-i sàyi hùulaa à kàasuwaa ba"
    glossedTokens := [("Audù", "Audu"), ("bà-i", "NEG-3SG"), ("sàyi", "buy"), ("hùulaa", "cap"), ("à", "at"), ("kàasuwaa", "market"), ("ba", "NEG")]
    glossedWords := [⟨[['A', 'u', 'd', 'ù']], [['A', 'u', 'd', 'u']]⟩, ⟨[['b', 'à'], ['i']], [['N', 'E', 'G'], ['3', 'S', 'G']]⟩, ⟨[['s', 'à', 'y', 'i']], [['b', 'u', 'y']]⟩, ⟨[['h', 'ù', 'u', 'l', 'a', 'a']], [['c', 'a', 'p']]⟩, ⟨[['à']], [['a', 't']]⟩, ⟨[['k', 'à', 'a', 's', 'u', 'w', 'a', 'a']], [['m', 'a', 'r', 'k', 'e', 't']]⟩, ⟨[['b', 'a']], [['N', 'E', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "bare"), ("scope", "NEG > ∃")] }

def ex_12a : Datum :=
  { id := "zimmermann2008_12a"
    source := ⟨"zimmermann-2008", "(12a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "manòomii bà-i zoo ba"
    glossedTokens := [("manòomii", "farmer"), ("bà-i", "NEG-3SG"), ("zoo", "come"), ("ba", "NEG")]
    glossedWords := [⟨[['m', 'a', 'n', 'ò', 'o', 'm', 'i', 'i']], [['f', 'a', 'r', 'm', 'e', 'r']]⟩, ⟨[['b', 'à'], ['i']], [['N', 'E', 'G'], ['3', 'S', 'G']]⟩, ⟨[['z', 'o', 'o']], [['c', 'o', 'm', 'e']]⟩, ⟨[['b', 'a']], [['N', 'E', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "bare"), ("scope", "NEG > ∃")] }

def ex_13a : Datum :=
  { id := "zimmermann2008_13a"
    source := ⟨"zimmermann-2008", "(13a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "mutàanee bà sù tàfi kàasuwaa ba"
    glossedTokens := [("mutàanee", "people"), ("bà", "NEG"), ("sù", "3PL"), ("tàfi", "go"), ("kàasuwaa", "market"), ("ba", "NEG")]
    glossedWords := [⟨[['m', 'u', 't', 'à', 'a', 'n', 'e', 'e']], [['p', 'e', 'o', 'p', 'l', 'e']]⟩, ⟨[['b', 'à']], [['N', 'E', 'G']]⟩, ⟨[['s', 'ù']], [['3', 'P', 'L']]⟩, ⟨[['t', 'à', 'f', 'i']], [['g', 'o']]⟩, ⟨[['k', 'à', 'a', 's', 'u', 'w', 'a', 'a']], [['m', 'a', 'r', 'k', 'e', 't']]⟩, ⟨[['b', 'a']], [['N', 'E', 'G']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "bare"), ("scope", "NEG > ∃")] }

def ex_63a : Datum :=
  { id := "zimmermann2008_63a"
    source := ⟨"zimmermann-2008", "(63a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "sai wani yaaròo yaa cêe"
    glossedTokens := [("sai", "then"), ("wani", "some"), ("yaaròo", "boy"), ("yaa", "3SG.PERF"), ("cêe", "say")]
    glossedWords := [⟨[['s', 'a', 'i']], [['t', 'h', 'e', 'n']]⟩, ⟨[['w', 'a', 'n', 'i']], [['s', 'o', 'm', 'e']]⟩, ⟨[['y', 'a', 'a', 'r', 'ò', 'o']], [['b', 'o', 'y']]⟩, ⟨[['y', 'a', 'a']], [['3', 'S', 'G', '.', 'P', 'E', 'R', 'F']]⟩, ⟨[['c', 'ê', 'e']], [['s', 'a', 'y']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "wani"), ("function", "discourse-introducing")] }

def ex_64 : Datum :=
  { id := "zimmermann2008_64"
    source := ⟨"zimmermann-2008", "(64)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "wasu sun zoo, wasu bà sù zoo ba"
    glossedTokens := [("wasu", "some"), ("sun", "3PL.PERF"), ("zoo", "come"), ("wasu", "some"), ("bà", "NEG"), ("sù", "3PL.SUBJ"), ("zoo", "come"), ("ba", "NEG")]
    glossedWords := [⟨[['w', 'a', 's', 'u']], [['s', 'o', 'm', 'e']]⟩, ⟨[['s', 'u', 'n']], [['3', 'P', 'L', '.', 'P', 'E', 'R', 'F']]⟩, ⟨[['z', 'o', 'o']], [['c', 'o', 'm', 'e']]⟩, ⟨[['w', 'a', 's', 'u']], [['s', 'o', 'm', 'e']]⟩, ⟨[['b', 'à']], [['N', 'E', 'G']]⟩, ⟨[['s', 'ù']], [['3', 'P', 'L', '.', 'S', 'U', 'B', 'J']]⟩, ⟨[['z', 'o', 'o']], [['c', 'o', 'm', 'e']]⟩, ⟨[['b', 'a']], [['N', 'E', 'G']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "wasu"), ("reading", "partitive")] }

def ex_65a : Datum :=
  { id := "zimmermann2008_65a"
    source := ⟨"zimmermann-2008", "(65a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Wani yaa zoo?"
    glossedTokens := [("Wani", "some/any"), ("yaa", "3SG.PERF"), ("zoo", "come")]
    glossedWords := [⟨[['W', 'a', 'n', 'i']], [['s', 'o', 'm', 'e', '/', 'a', 'n', 'y']]⟩, ⟨[['y', 'a', 'a']], [['3', 'S', 'G', '.', 'P', 'E', 'R', 'F']]⟩, ⟨[['z', 'o', 'o']], [['c', 'o', 'm', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "wani"), ("clause", "polar question")] }

def ex_69a : Datum :=
  { id := "zimmermann2008_69a"
    source := ⟨"zimmermann-2008", "(69a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "bà-n ga wani ba"
    glossedTokens := [("bà-n", "NEG-1SG.SUBJ"), ("ga", "see"), ("wani", "someone"), ("ba", "NEG")]
    glossedWords := [⟨[['b', 'à'], ['n']], [['N', 'E', 'G'], ['1', 'S', 'G', '.', 'S', 'U', 'B', 'J']]⟩, ⟨[['g', 'a']], [['s', 'e', 'e']]⟩, ⟨[['w', 'a', 'n', 'i']], [['s', 'o', 'm', 'e', 'o', 'n', 'e']]⟩, ⟨[['b', 'a']], [['N', 'E', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "wani"), ("position", "object"), ("scope", "ambiguous")] }

def ex_69b : Datum :=
  { id := "zimmermann2008_69b"
    source := ⟨"zimmermann-2008", "(69b)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Muusaa bà-i kiraa wani àbookii lìyaafaa ba"
    glossedTokens := [("Muusaa", "Musa"), ("bà-i", "NEG-3SG.SUBJ"), ("kiraa", "invite"), ("wani", "some"), ("àbookii", "friend"), ("lìyaafaa", "ceremony"), ("ba", "NEG")]
    glossedWords := [⟨[['M', 'u', 'u', 's', 'a', 'a']], [['M', 'u', 's', 'a']]⟩, ⟨[['b', 'à'], ['i']], [['N', 'E', 'G'], ['3', 'S', 'G', '.', 'S', 'U', 'B', 'J']]⟩, ⟨[['k', 'i', 'r', 'a', 'a']], [['i', 'n', 'v', 'i', 't', 'e']]⟩, ⟨[['w', 'a', 'n', 'i']], [['s', 'o', 'm', 'e']]⟩, ⟨[['à', 'b', 'o', 'o', 'k', 'i', 'i']], [['f', 'r', 'i', 'e', 'n', 'd']]⟩, ⟨[['l', 'ì', 'y', 'a', 'a', 'f', 'a', 'a']], [['c', 'e', 'r', 'e', 'm', 'o', 'n', 'y']]⟩, ⟨[['b', 'a']], [['N', 'E', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "wani"), ("position", "object"), ("scope", "ambiguous")] }

def ex_70 : Datum :=
  { id := "zimmermann2008_70"
    source := ⟨"zimmermann-2008", "(70)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "wasu bà sù zoo ba"
    glossedTokens := [("wasu", "some.PL"), ("bà", "NEG"), ("sù", "3PL"), ("zoo", "come"), ("ba", "NEG")]
    glossedWords := [⟨[['w', 'a', 's', 'u']], [['s', 'o', 'm', 'e', '.', 'P', 'L']]⟩, ⟨[['b', 'à']], [['N', 'E', 'G']]⟩, ⟨[['s', 'ù']], [['3', 'P', 'L']]⟩, ⟨[['z', 'o', 'o']], [['c', 'o', 'm', 'e']]⟩, ⟨[['b', 'a']], [['N', 'E', 'G']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "wasu"), ("position", "subject"), ("scope", "∃ > NEG only")] }

def ex_71 : Datum :=
  { id := "zimmermann2008_71"
    source := ⟨"zimmermann-2008", "(71)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "baabù wan dà ya zoo"
    glossedTokens := [("baabù", "not.exist"), ("wan", "someone"), ("dà", "REL"), ("ya", "3SG.PERF.REL"), ("zoo", "come")]
    glossedWords := [⟨[['b', 'a', 'a', 'b', 'ù']], [['n', 'o', 't', '.', 'e', 'x', 'i', 's', 't']]⟩, ⟨[['w', 'a', 'n']], [['s', 'o', 'm', 'e', 'o', 'n', 'e']]⟩, ⟨[['d', 'à']], [['R', 'E', 'L']]⟩, ⟨[['y', 'a']], [['3', 'S', 'G', '.', 'P', 'E', 'R', 'F', '.', 'R', 'E', 'L']]⟩, ⟨[['z', 'o', 'o']], [['c', 'o', 'm', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "negative existential relative")] }

def ex_73 : Datum :=
  { id := "zimmermann2008_73"
    source := ⟨"zimmermann-2008", "(73)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "bà-n ga koo-waa ba"
    glossedTokens := [("bà-n", "NEG-1SG.SUBJ"), ("ga", "see"), ("koo-waa", "DISJ-wh"), ("ba", "NEG")]
    glossedWords := [⟨[['b', 'à'], ['n']], [['N', 'E', 'G'], ['1', 'S', 'G', '.', 'S', 'U', 'B', 'J']]⟩, ⟨[['g', 'a']], [['s', 'e', 'e']]⟩, ⟨[['k', 'o', 'o'], ['w', 'a', 'a']], [['D', 'I', 'S', 'J'], ['w', 'h']]⟩, ⟨[['b', 'a']], [['N', 'E', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "koo+wh"), ("negation", "VP"), ("scope", "negative existential only")] }

def ex_74a : Datum :=
  { id := "zimmermann2008_74a"
    source := ⟨"zimmermann-2008", "(74a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "bàa koo-waa kèe sô-n wannàn jàr̃iidàa ba"
    glossedTokens := [("bàa", "NEG"), ("koo-waa", "DISJ-who"), ("kèe", "PROG.REL"), ("sô-n", "like-LINK"), ("wannàn", "this"), ("jàr̃iidàa", "newspaper"), ("ba", "NEG")]
    glossedWords := [⟨[['b', 'à', 'a']], [['N', 'E', 'G']]⟩, ⟨[['k', 'o', 'o'], ['w', 'a', 'a']], [['D', 'I', 'S', 'J'], ['w', 'h', 'o']]⟩, ⟨[['k', 'è', 'e']], [['P', 'R', 'O', 'G', '.', 'R', 'E', 'L']]⟩, ⟨[['s', 'ô'], ['n']], [['l', 'i', 'k', 'e'], ['L', 'I', 'N', 'K']]⟩, ⟨[['w', 'a', 'n', 'n', 'à', 'n']], [['t', 'h', 'i', 's']]⟩, ⟨[['j', 'à', 'r', '̃', 'i', 'i', 'd', 'à', 'a']], [['n', 'e', 'w', 's', 'p', 'a', 'p', 'e', 'r']]⟩, ⟨[['b', 'a']], [['N', 'E', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "koo+wh"), ("negation", "sentential"), ("scope", "negative universal only")] }

def ex_75 : Datum :=
  { id := "zimmermann2008_75"
    source := ⟨"zimmermann-2008", "(75)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "koo-waa bà-i ci jar̃r̃àbâawaa ba"
    glossedTokens := [("koo-waa", "DISJ-who"), ("bà-i", "NEG-3SG.SUBJ"), ("ci", "eat"), ("jar̃r̃àbâawaa", "exam"), ("ba", "NEG")]
    glossedWords := [⟨[['k', 'o', 'o'], ['w', 'a', 'a']], [['D', 'I', 'S', 'J'], ['w', 'h', 'o']]⟩, ⟨[['b', 'à'], ['i']], [['N', 'E', 'G'], ['3', 'S', 'G', '.', 'S', 'U', 'B', 'J']]⟩, ⟨[['c', 'i']], [['e', 'a', 't']]⟩, ⟨[['j', 'a', 'r', '̃', 'r', '̃', 'à', 'b', 'â', 'a', 'w', 'a', 'a']], [['e', 'x', 'a', 'm']]⟩, ⟨[['b', 'a']], [['N', 'E', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "koo+wh"), ("position", "subject")] }

def ex_78 : Datum :=
  { id := "zimmermann2008_78"
    source := ⟨"zimmermann-2008", "(78)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "koo-wànè ɗàalìbii nèe bà-i ci jar̃r̃àbâawaa ba"
    glossedTokens := [("koo-wànè", "DISJ-which"), ("ɗàalìbii", "student"), ("nèe", "PRT"), ("bà-i", "NEG-3SG"), ("ci", "eat"), ("jar̃r̃àbâawaa", "exam"), ("ba", "NEG")]
    glossedWords := [⟨[['k', 'o', 'o'], ['w', 'à', 'n', 'è']], [['D', 'I', 'S', 'J'], ['w', 'h', 'i', 'c', 'h']]⟩, ⟨[['ɗ', 'à', 'a', 'l', 'ì', 'b', 'i', 'i']], [['s', 't', 'u', 'd', 'e', 'n', 't']]⟩, ⟨[['n', 'è', 'e']], [['P', 'R', 'T']]⟩, ⟨[['b', 'à'], ['i']], [['N', 'E', 'G'], ['3', 'S', 'G']]⟩, ⟨[['c', 'i']], [['e', 'a', 't']]⟩, ⟨[['j', 'a', 'r', '̃', 'r', '̃', 'à', 'b', 'â', 'a', 'w', 'a', 'a']], [['e', 'x', 'a', 'm']]⟩, ⟨[['b', 'a']], [['N', 'E', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "koo+wh"), ("position", "subject"), ("focus", "yes")] }

def ex_85a : Datum :=
  { id := "zimmermann2008_85a"
    source := ⟨"zimmermann-2008", "(85a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "duk faasinjoojî-n"
    glossedTokens := [("duk", "all"), ("faasinjoojî-n", "passengers-DEF")]
    glossedWords := [⟨[['d', 'u', 'k']], [['a', 'l', 'l']]⟩, ⟨[['f', 'a', 'a', 's', 'i', 'n', 'j', 'o', 'o', 'j', 'î'], ['n']], [['p', 'a', 's', 's', 'e', 'n', 'g', 'e', 'r', 's'], ['D', 'E', 'F']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "duk"), ("order", "prenominal")] }

def ex_86 : Datum :=
  { id := "zimmermann2008_86"
    source := ⟨"zimmermann-2008", "(86)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "naa ga duk ɗàalìbii"
    glossedTokens := [("naa", "1SG.PERF"), ("ga", "see"), ("duk", "all"), ("ɗàalìbii", "student")]
    glossedWords := [⟨[['n', 'a', 'a']], [['1', 'S', 'G', '.', 'P', 'E', 'R', 'F']]⟩, ⟨[['g', 'a']], [['s', 'e', 'e']]⟩, ⟨[['d', 'u', 'k']], [['a', 'l', 'l']]⟩, ⟨[['ɗ', 'à', 'a', 'l', 'ì', 'b', 'i', 'i']], [['s', 't', 'u', 'd', 'e', 'n', 't']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "duk"), ("restrictor", "singular")] }

def ex_89a : Datum :=
  { id := "zimmermann2008_89a"
    source := ⟨"zimmermann-2008", "(89a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "koo-wànè ɗàalìbii yáa tàaru à gàba-n makar̃antaa"
    glossedTokens := [("koo-wànè", "DISJ-which"), ("ɗàalìbii", "student"), ("yáa", "3SG.PERF"), ("tàaru", "gather"), ("à", "at"), ("gàba-n", "front-LINK"), ("makar̃antaa", "school")]
    glossedWords := [⟨[['k', 'o', 'o'], ['w', 'à', 'n', 'è']], [['D', 'I', 'S', 'J'], ['w', 'h', 'i', 'c', 'h']]⟩, ⟨[['ɗ', 'à', 'a', 'l', 'ì', 'b', 'i', 'i']], [['s', 't', 'u', 'd', 'e', 'n', 't']]⟩, ⟨[['y', 'á', 'a']], [['3', 'S', 'G', '.', 'P', 'E', 'R', 'F']]⟩, ⟨[['t', 'à', 'a', 'r', 'u']], [['g', 'a', 't', 'h', 'e', 'r']]⟩, ⟨[['à']], [['a', 't']]⟩, ⟨[['g', 'à', 'b', 'a'], ['n']], [['f', 'r', 'o', 'n', 't'], ['L', 'I', 'N', 'K']]⟩, ⟨[['m', 'a', 'k', 'a', 'r', '̃', 'a', 'n', 't', 'a', 'a']], [['s', 'c', 'h', 'o', 'o', 'l']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "koo+wh"), ("predicate", "collective")] }

def ex_90a : Datum :=
  { id := "zimmermann2008_90a"
    source := ⟨"zimmermann-2008", "(90a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "duk ɗàalìbâ-n sun tàaru à gàba-n makar̃antaa"
    glossedTokens := [("duk", "all"), ("ɗàalìbâ-n", "students-DEF"), ("sun", "3PL.PERF"), ("tàaru", "gather"), ("à", "at"), ("gàba-n", "front-LINK"), ("makar̃antaa", "school")]
    glossedWords := [⟨[['d', 'u', 'k']], [['a', 'l', 'l']]⟩, ⟨[['ɗ', 'à', 'a', 'l', 'ì', 'b', 'â'], ['n']], [['s', 't', 'u', 'd', 'e', 'n', 't', 's'], ['D', 'E', 'F']]⟩, ⟨[['s', 'u', 'n']], [['3', 'P', 'L', '.', 'P', 'E', 'R', 'F']]⟩, ⟨[['t', 'à', 'a', 'r', 'u']], [['g', 'a', 't', 'h', 'e', 'r']]⟩, ⟨[['à']], [['a', 't']]⟩, ⟨[['g', 'à', 'b', 'a'], ['n']], [['f', 'r', 'o', 'n', 't'], ['L', 'I', 'N', 'K']]⟩, ⟨[['m', 'a', 'k', 'a', 'r', '̃', 'a', 'n', 't', 'a', 'a']], [['s', 'c', 'h', 'o', 'o', 'l']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "duk"), ("predicate", "collective")] }

def ex_91a : Datum :=
  { id := "zimmermann2008_91a"
    source := ⟨"zimmermann-2008", "(91a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "bà-n kar̃àntà duk lìttàttàafâ-n ba"
    glossedTokens := [("bà-n", "NEG-1SG"), ("kar̃àntà", "read"), ("duk", "all"), ("lìttàttàafâ-n", "books-DEF"), ("ba", "NEG")]
    glossedWords := [⟨[['b', 'à'], ['n']], [['N', 'E', 'G'], ['1', 'S', 'G']]⟩, ⟨[['k', 'a', 'r', '̃', 'à', 'n', 't', 'à']], [['r', 'e', 'a', 'd']]⟩, ⟨[['d', 'u', 'k']], [['a', 'l', 'l']]⟩, ⟨[['l', 'ì', 't', 't', 'à', 't', 't', 'à', 'a', 'f', 'â'], ['n']], [['b', 'o', 'o', 'k', 's'], ['D', 'E', 'F']]⟩, ⟨[['b', 'a']], [['N', 'E', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "duk"), ("negation", "VP"), ("scope", "negative universal")] }

def ex_91b : Datum :=
  { id := "zimmermann2008_91b"
    source := ⟨"zimmermann-2008", "(91b)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "bàa duk bàaƙii su-kà zoo ba"
    glossedTokens := [("bàa", "NEG"), ("duk", "all"), ("bàaƙii", "guests"), ("su-kà", "3PL-PERF.REL"), ("zoo", "come"), ("ba", "NEG")]
    glossedWords := [⟨[['b', 'à', 'a']], [['N', 'E', 'G']]⟩, ⟨[['d', 'u', 'k']], [['a', 'l', 'l']]⟩, ⟨[['b', 'à', 'a', 'ƙ', 'i', 'i']], [['g', 'u', 'e', 's', 't', 's']]⟩, ⟨[['s', 'u'], ['k', 'à']], [['3', 'P', 'L'], ['P', 'E', 'R', 'F', '.', 'R', 'E', 'L']]⟩, ⟨[['z', 'o', 'o']], [['c', 'o', 'm', 'e']]⟩, ⟨[['b', 'a']], [['N', 'E', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "duk"), ("negation", "sentential"), ("scope", "negative universal")] }

def all : List Datum := [ex_11a, ex_12a, ex_13a, ex_63a, ex_64, ex_65a, ex_69a, ex_69b, ex_70, ex_71, ex_73, ex_74a, ex_75, ex_78, ex_85a, ex_86, ex_89a, ex_90a, ex_91a, ex_91b]

end Zimmermann2008.Examples
