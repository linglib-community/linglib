module

public import Linglib.Data.Examples.Schema

/-!
# `BaleKhanjian2014` — typed example data

Auto-generated from `Linglib/Data/Examples/BaleKhanjian2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BaleKhanjian2014.Examples`.
-/

@[expose] public section

namespace BaleKhanjian2014.Examples

def ex_3 : Datum :=
  { id := "balekhanjian2014_3"
    source := ⟨"bale-khanjian-2014", "(3)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Dəgha vazets."
    glossedTokens := [("Dəgha", "boy(SG)"), ("vaze-ts", "run-PST")]
    glossedWords := [⟨[['D', 'ə', 'g', 'h', 'a']], [['b', 'o', 'y', '(', 'S', 'G', ')']]⟩, ⟨[['v', 'a', 'z', 'e'], ['t', 's']], [['r', 'u', 'n'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "existential"), ("number", "SG"), ("definite", "no"), ("reading", "general")] }

def ex_4a : Datum :=
  { id := "balekhanjian2014_4a"
    source := ⟨"bale-khanjian-2014", "(4a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Johnə dəgha e."
    glossedTokens := [("John-ə", "John-DEF"), ("dəgha", "boy(SG)"), ("e", "is")]
    glossedWords := [⟨[['J', 'o', 'h', 'n'], ['ə']], [['J', 'o', 'h', 'n'], ['D', 'E', 'F']]⟩, ⟨[['d', 'ə', 'g', 'h', 'a']], [['b', 'o', 'y', '(', 'S', 'G', ')']]⟩, ⟨[['e']], [['i', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "predicative"), ("subject", "atom"), ("number", "SG")] }

def ex_4b : Datum :=
  { id := "balekhanjian2014_4b"
    source := ⟨"bale-khanjian-2014", "(4b)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Johnə yev Bradə dəgha en."
    glossedTokens := [("John-ə", "John-DEF"), ("yev", "and"), ("Brad-ə", "Brad-DEF"), ("dəgha", "boy(SG)"), ("en", "are")]
    glossedWords := [⟨[['J', 'o', 'h', 'n'], ['ə']], [['J', 'o', 'h', 'n'], ['D', 'E', 'F']]⟩, ⟨[['y', 'e', 'v']], [['a', 'n', 'd']]⟩, ⟨[['B', 'r', 'a', 'd'], ['ə']], [['B', 'r', 'a', 'd'], ['D', 'E', 'F']]⟩, ⟨[['d', 'ə', 'g', 'h', 'a']], [['b', 'o', 'y', '(', 'S', 'G', ')']]⟩, ⟨[['e', 'n']], [['a', 'r', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "predicative"), ("subject", "group"), ("number", "SG")] }

def ex_5a : Datum :=
  { id := "balekhanjian2014_5a"
    source := ⟨"bale-khanjian-2014", "(5a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Johnə yev Bradə yergu dəghaner en."
    glossedTokens := [("John-ə", "John-DEF"), ("yev", "and"), ("Brad-ə", "Brad-DEF"), ("yergu", "two"), ("dəgha-ner", "boy-PL"), ("en", "are")]
    glossedWords := [⟨[['J', 'o', 'h', 'n'], ['ə']], [['J', 'o', 'h', 'n'], ['D', 'E', 'F']]⟩, ⟨[['y', 'e', 'v']], [['a', 'n', 'd']]⟩, ⟨[['B', 'r', 'a', 'd'], ['ə']], [['B', 'r', 'a', 'd'], ['D', 'E', 'F']]⟩, ⟨[['y', 'e', 'r', 'g', 'u']], [['t', 'w', 'o']]⟩, ⟨[['d', 'ə', 'g', 'h', 'a'], ['n', 'e', 'r']], [['b', 'o', 'y'], ['P', 'L']]⟩, ⟨[['e', 'n']], [['a', 'r', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "predicative"), ("subject", "group"), ("number", "PL"), ("numeral", "two")] }

def ex_5b : Datum :=
  { id := "balekhanjian2014_5b"
    source := ⟨"bale-khanjian-2014", "(5b)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Johnə yev Bradə meg dəgha en/e."
    glossedTokens := [("John-ə", "John-DEF"), ("yev", "and"), ("Brad-ə", "Brad-DEF"), ("meg", "one"), ("dəgha", "boy"), ("en/e", "are/is")]
    glossedWords := [⟨[['J', 'o', 'h', 'n'], ['ə']], [['J', 'o', 'h', 'n'], ['D', 'E', 'F']]⟩, ⟨[['y', 'e', 'v']], [['a', 'n', 'd']]⟩, ⟨[['B', 'r', 'a', 'd'], ['ə']], [['B', 'r', 'a', 'd'], ['D', 'E', 'F']]⟩, ⟨[['m', 'e', 'g']], [['o', 'n', 'e']]⟩, ⟨[['d', 'ə', 'g', 'h', 'a']], [['b', 'o', 'y']]⟩, ⟨[['e', 'n', '/', 'e']], [['a', 'r', 'e', '/', 'i', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "predicative"), ("subject", "group"), ("number", "SG"), ("numeral", "one")] }

def ex_5c : Datum :=
  { id := "balekhanjian2014_5c"
    source := ⟨"bale-khanjian-2014", "(5c)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Johnə yev Bradə dəgha mən e."
    glossedTokens := [("John-ə", "John-DEF"), ("yev", "and"), ("Brad-ə", "Brad-DEF"), ("dəgha", "boy"), ("mən", "INDEF(SG)"), ("e", "is")]
    glossedWords := [⟨[['J', 'o', 'h', 'n'], ['ə']], [['J', 'o', 'h', 'n'], ['D', 'E', 'F']]⟩, ⟨[['y', 'e', 'v']], [['a', 'n', 'd']]⟩, ⟨[['B', 'r', 'a', 'd'], ['ə']], [['B', 'r', 'a', 'd'], ['D', 'E', 'F']]⟩, ⟨[['d', 'ə', 'g', 'h', 'a']], [['b', 'o', 'y']]⟩, ⟨[['m', 'ə', 'n']], [['I', 'N', 'D', 'E', 'F', '(', 'S', 'G', ')']]⟩, ⟨[['e']], [['i', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "predicativeIndefinite"), ("subject", "group"), ("number", "SG")] }

def ex_6a : Datum :=
  { id := "balekhanjian2014_6a"
    source := ⟨"bale-khanjian-2014", "(6a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Johnə yev Bradə dəghaner en."
    glossedTokens := [("John-ə", "John-DEF"), ("yev", "and"), ("Brad-ə", "Brad-DEF"), ("dəgha-ner", "boy-PL"), ("en", "are")]
    glossedWords := [⟨[['J', 'o', 'h', 'n'], ['ə']], [['J', 'o', 'h', 'n'], ['D', 'E', 'F']]⟩, ⟨[['y', 'e', 'v']], [['a', 'n', 'd']]⟩, ⟨[['B', 'r', 'a', 'd'], ['ə']], [['B', 'r', 'a', 'd'], ['D', 'E', 'F']]⟩, ⟨[['d', 'ə', 'g', 'h', 'a'], ['n', 'e', 'r']], [['b', 'o', 'y'], ['P', 'L']]⟩, ⟨[['e', 'n']], [['a', 'r', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "predicative"), ("subject", "group"), ("number", "PL")] }

def ex_6b : Datum :=
  { id := "balekhanjian2014_6b"
    source := ⟨"bale-khanjian-2014", "(6b)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Johnə dəghaner e."
    glossedTokens := [("John-ə", "John-DEF"), ("dəgha-ner", "boy-PL"), ("e", "is")]
    glossedWords := [⟨[['J', 'o', 'h', 'n'], ['ə']], [['J', 'o', 'h', 'n'], ['D', 'E', 'F']]⟩, ⟨[['d', 'ə', 'g', 'h', 'a'], ['n', 'e', 'r']], [['b', 'o', 'y'], ['P', 'L']]⟩, ⟨[['e']], [['i', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "predicative"), ("subject", "atom"), ("number", "PL")] }

def ex_7 : Datum :=
  { id := "balekhanjian2014_7"
    source := ⟨"bale-khanjian-2014", "(7)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Dəghaner vazetsin."
    glossedTokens := [("Dəgha-ner", "boy-PL"), ("vaze-ts-in", "run-PST-3PL")]
    glossedWords := [⟨[['D', 'ə', 'g', 'h', 'a'], ['n', 'e', 'r']], [['b', 'o', 'y'], ['P', 'L']]⟩, ⟨[['v', 'a', 'z', 'e'], ['t', 's'], ['i', 'n']], [['r', 'u', 'n'], ['P', 'S', 'T'], ['3', 'P', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "existential"), ("number", "PL"), ("definite", "no"), ("reading", "strictPlural")] }

def ex_8a : Datum :=
  { id := "balekhanjian2014_8a"
    source := ⟨"bale-khanjian-2014", "(8a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Amen mart vor bəzdigner uner vodki gajnetsav."
    glossedTokens := [("Amen", "all"), ("mart", "person"), ("vor", "that"), ("bəzdig-ner", "child-PL"), ("uner", "had"), ("vodk-i", "foot-DAT"), ("gajne-tsav", "stand.up-PST")]
    glossedWords := [⟨[['A', 'm', 'e', 'n']], [['a', 'l', 'l']]⟩, ⟨[['m', 'a', 'r', 't']], [['p', 'e', 'r', 's', 'o', 'n']]⟩, ⟨[['v', 'o', 'r']], [['t', 'h', 'a', 't']]⟩, ⟨[['b', 'ə', 'z', 'd', 'i', 'g'], ['n', 'e', 'r']], [['c', 'h', 'i', 'l', 'd'], ['P', 'L']]⟩, ⟨[['u', 'n', 'e', 'r']], [['h', 'a', 'd']]⟩, ⟨[['v', 'o', 'd', 'k'], ['i']], [['f', 'o', 'o', 't'], ['D', 'A', 'T']]⟩, ⟨[['g', 'a', 'j', 'n', 'e'], ['t', 's', 'a', 'v']], [['s', 't', 'a', 'n', 'd', '.', 'u', 'p'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("construction", "restrictor"), ("number", "PL"), ("reading", "strictPlural")] }

def ex_8b : Datum :=
  { id := "balekhanjian2014_8b"
    source := ⟨"bale-khanjian-2014", "(8b)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Amen mart vor bəzdig uner vodki gajnetsav."
    glossedTokens := [("Amen", "all"), ("mart", "person"), ("vor", "that"), ("bəzdig", "child(SG)"), ("uner", "had"), ("vodk-i", "foot-DAT"), ("gajne-tsav", "stand.up-PST")]
    glossedWords := [⟨[['A', 'm', 'e', 'n']], [['a', 'l', 'l']]⟩, ⟨[['m', 'a', 'r', 't']], [['p', 'e', 'r', 's', 'o', 'n']]⟩, ⟨[['v', 'o', 'r']], [['t', 'h', 'a', 't']]⟩, ⟨[['b', 'ə', 'z', 'd', 'i', 'g']], [['c', 'h', 'i', 'l', 'd', '(', 'S', 'G', ')']]⟩, ⟨[['u', 'n', 'e', 'r']], [['h', 'a', 'd']]⟩, ⟨[['v', 'o', 'd', 'k'], ['i']], [['f', 'o', 'o', 't'], ['D', 'A', 'T']]⟩, ⟨[['g', 'a', 'j', 'n', 'e'], ['t', 's', 'a', 'v']], [['s', 't', 'a', 'n', 'd', '.', 'u', 'p'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "restrictor"), ("number", "SG"), ("reading", "general")] }

def ex_10a : Datum :=
  { id := "balekhanjian2014_10a"
    source := ⟨"bale-khanjian-2014", "(10a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Yergu dəgha vazets."
    glossedTokens := [("Yergu", "two"), ("dəgha", "boy(SG)"), ("vaze-ts", "run-PST")]
    glossedWords := [⟨[['Y', 'e', 'r', 'g', 'u']], [['t', 'w', 'o']]⟩, ⟨[['d', 'ə', 'g', 'h', 'a']], [['b', 'o', 'y', '(', 'S', 'G', ')']]⟩, ⟨[['v', 'a', 'z', 'e'], ['t', 's']], [['r', 'u', 'n'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "existential"), ("number", "SG"), ("numeral", "two"), ("definite", "no")] }

def ex_10b : Datum :=
  { id := "balekhanjian2014_10b"
    source := ⟨"bale-khanjian-2014", "(10b)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Yergu dəghaner vazetsin."
    glossedTokens := [("Yergu", "two"), ("dəgha-ner", "boy-PL"), ("vaze-ts-in", "run-PST-3PL")]
    glossedWords := [⟨[['Y', 'e', 'r', 'g', 'u']], [['t', 'w', 'o']]⟩, ⟨[['d', 'ə', 'g', 'h', 'a'], ['n', 'e', 'r']], [['b', 'o', 'y'], ['P', 'L']]⟩, ⟨[['v', 'a', 'z', 'e'], ['t', 's'], ['i', 'n']], [['r', 'u', 'n'], ['P', 'S', 'T'], ['3', 'P', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "existential"), ("number", "PL"), ("numeral", "two"), ("definite", "no")] }

def ex_11b : Datum :=
  { id := "balekhanjian2014_11b"
    source := ⟨"bale-khanjian-2014", "(11b)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Dəghan vazets."
    glossedTokens := [("Dəgha-n", "boy(SG)-DEF"), ("vaze-ts", "run-PST")]
    glossedWords := [⟨[['D', 'ə', 'g', 'h', 'a'], ['n']], [['b', 'o', 'y', '(', 'S', 'G', ')'], ['D', 'E', 'F']]⟩, ⟨[['v', 'a', 'z', 'e'], ['t', 's']], [['r', 'u', 'n'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "definite"), ("number", "SG"), ("definite", "yes"), ("reading", "strictSingular")] }

def ex_13a : Datum :=
  { id := "balekhanjian2014_13a"
    source := ⟨"bale-khanjian-2014", "(13a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Amen dəgha ir kirkerə kənadz e."
    glossedTokens := [("Amen", "every"), ("dəgha", "boy"), ("ir", "3SG.HUMAN.GEN"), ("kirk-er-ə", "book-PL-DEF"), ("kənadz", "buy.PRF"), ("e", "be.3SG")]
    glossedWords := [⟨[['A', 'm', 'e', 'n']], [['e', 'v', 'e', 'r', 'y']]⟩, ⟨[['d', 'ə', 'g', 'h', 'a']], [['b', 'o', 'y']]⟩, ⟨[['i', 'r']], [['3', 'S', 'G', '.', 'H', 'U', 'M', 'A', 'N', '.', 'G', 'E', 'N']]⟩, ⟨[['k', 'i', 'r', 'k'], ['e', 'r'], ['ə']], [['b', 'o', 'o', 'k'], ['P', 'L'], ['D', 'E', 'F']]⟩, ⟨[['k', 'ə', 'n', 'a', 'd', 'z']], [['b', 'u', 'y', '.', 'P', 'R', 'F']]⟩, ⟨[['e']], [['b', 'e', '.', '3', 'S', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "boundPossessive"), ("number", "PL"), ("definite", "yes"), ("reading", "strictPlural")] }

def ex_13b : Datum :=
  { id := "balekhanjian2014_13b"
    source := ⟨"bale-khanjian-2014", "(13b)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Amen dəgha ir kirkə kənadz e."
    glossedTokens := [("Amen", "every"), ("dəgha", "boy"), ("ir", "3SG.HUMAN.GEN"), ("kirk-ə", "book-DEF"), ("kənadz", "buy.PRF"), ("e", "be.3SG")]
    glossedWords := [⟨[['A', 'm', 'e', 'n']], [['e', 'v', 'e', 'r', 'y']]⟩, ⟨[['d', 'ə', 'g', 'h', 'a']], [['b', 'o', 'y']]⟩, ⟨[['i', 'r']], [['3', 'S', 'G', '.', 'H', 'U', 'M', 'A', 'N', '.', 'G', 'E', 'N']]⟩, ⟨[['k', 'i', 'r', 'k'], ['ə']], [['b', 'o', 'o', 'k'], ['D', 'E', 'F']]⟩, ⟨[['k', 'ə', 'n', 'a', 'd', 'z']], [['b', 'u', 'y', '.', 'P', 'R', 'F']]⟩, ⟨[['e']], [['b', 'e', '.', '3', 'S', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "boundPossessive"), ("number", "SG"), ("definite", "yes"), ("reading", "strictSingular")] }

def ex_14a : Datum :=
  { id := "balekhanjian2014_14a"
    source := ⟨"bale-khanjian-2014", "(14a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Yergu dəghan vazets."
    glossedTokens := [("Yergu", "two"), ("dəgha-n", "boy(SG)-DEF"), ("vaze-ts", "run-PST")]
    glossedWords := [⟨[['Y', 'e', 'r', 'g', 'u']], [['t', 'w', 'o']]⟩, ⟨[['d', 'ə', 'g', 'h', 'a'], ['n']], [['b', 'o', 'y', '(', 'S', 'G', ')'], ['D', 'E', 'F']]⟩, ⟨[['v', 'a', 'z', 'e'], ['t', 's']], [['r', 'u', 'n'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "definite"), ("number", "SG"), ("numeral", "two"), ("definite", "yes")] }

def ex_14b : Datum :=
  { id := "balekhanjian2014_14b"
    source := ⟨"bale-khanjian-2014", "(14b)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Yergu dəghanerə vazetsin."
    glossedTokens := [("Yergu", "two"), ("dəgha-ner-ə", "boy-PL-DEF"), ("vaze-ts-in", "run-PST-3PL")]
    glossedWords := [⟨[['Y', 'e', 'r', 'g', 'u']], [['t', 'w', 'o']]⟩, ⟨[['d', 'ə', 'g', 'h', 'a'], ['n', 'e', 'r'], ['ə']], [['b', 'o', 'y'], ['P', 'L'], ['D', 'E', 'F']]⟩, ⟨[['v', 'a', 'z', 'e'], ['t', 's'], ['i', 'n']], [['r', 'u', 'n'], ['P', 'S', 'T'], ['3', 'P', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "definite"), ("number", "PL"), ("numeral", "two"), ("definite", "yes")] }

def ex_24a : Datum :=
  { id := "balekhanjian2014_24a"
    source := ⟨"bale-khanjian-2014", "(24a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Dəgha chi vazets."
    glossedTokens := [("Dəgha", "boy(SG)"), ("chi", "not"), ("vaze-ts", "run-PST")]
    glossedWords := [⟨[['D', 'ə', 'g', 'h', 'a']], [['b', 'o', 'y', '(', 'S', 'G', ')']]⟩, ⟨[['c', 'h', 'i']], [['n', 'o', 't']]⟩, ⟨[['v', 'a', 'z', 'e'], ['t', 's']], [['r', 'u', 'n'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "negated"), ("number", "SG"), ("definite", "no"), ("scopeAmbiguous", "no")] }

def ex_25a : Datum :=
  { id := "balekhanjian2014_25a"
    source := ⟨"bale-khanjian-2014", "(25a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Dəghaner chi vazetsin."
    glossedTokens := [("Dəgha-ner", "boy-PL"), ("chi", "not"), ("vaze-ts-in", "run-PST-3PL")]
    glossedWords := [⟨[['D', 'ə', 'g', 'h', 'a'], ['n', 'e', 'r']], [['b', 'o', 'y'], ['P', 'L']]⟩, ⟨[['c', 'h', 'i']], [['n', 'o', 't']]⟩, ⟨[['v', 'a', 'z', 'e'], ['t', 's'], ['i', 'n']], [['r', 'u', 'n'], ['P', 'S', 'T'], ['3', 'P', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "negated"), ("number", "PL"), ("definite", "no"), ("scopeAmbiguous", "yes")] }

def ex_26a : Datum :=
  { id := "balekhanjian2014_26a"
    source := ⟨"bale-khanjian-2014", "(26a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Yergu dəgha chi vazets."
    glossedTokens := [("Yergu", "two"), ("dəgha", "boy(SG)"), ("chi", "not"), ("vaze-ts", "run-PST")]
    glossedWords := [⟨[['Y', 'e', 'r', 'g', 'u']], [['t', 'w', 'o']]⟩, ⟨[['d', 'ə', 'g', 'h', 'a']], [['b', 'o', 'y', '(', 'S', 'G', ')']]⟩, ⟨[['c', 'h', 'i']], [['n', 'o', 't']]⟩, ⟨[['v', 'a', 'z', 'e'], ['t', 's']], [['r', 'u', 'n'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "negated"), ("number", "SG"), ("numeral", "two"), ("definite", "no"), ("scopeAmbiguous", "yes")] }

def ex_27a : Datum :=
  { id := "balekhanjian2014_27a"
    source := ⟨"bale-khanjian-2014", "(27a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Yergu dəghaner chi vazetsin."
    glossedTokens := [("Yergu", "two"), ("dəgha-ner", "boy-PL"), ("chi", "not"), ("vaze-ts-in", "run-PST-3PL")]
    glossedWords := [⟨[['Y', 'e', 'r', 'g', 'u']], [['t', 'w', 'o']]⟩, ⟨[['d', 'ə', 'g', 'h', 'a'], ['n', 'e', 'r']], [['b', 'o', 'y'], ['P', 'L']]⟩, ⟨[['c', 'h', 'i']], [['n', 'o', 't']]⟩, ⟨[['v', 'a', 'z', 'e'], ['t', 's'], ['i', 'n']], [['r', 'u', 'n'], ['P', 'S', 'T'], ['3', 'P', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "negated"), ("number", "PL"), ("numeral", "two"), ("definite", "no"), ("scopeAmbiguous", "yes")] }

def all : List Datum := [ex_3, ex_4a, ex_4b, ex_5a, ex_5b, ex_5c, ex_6a, ex_6b, ex_7, ex_8a, ex_8b, ex_10a, ex_10b, ex_11b, ex_13a, ex_13b, ex_14a, ex_14b, ex_24a, ex_25a, ex_26a, ex_27a]

end BaleKhanjian2014.Examples
