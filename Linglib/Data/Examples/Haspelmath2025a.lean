module

public import Linglib.Data.Examples.Schema

/-!
# `Haspelmath2025a` — typed example data

Auto-generated from `Linglib/Data/Examples/Haspelmath2025a.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Haspelmath2025a.Examples`.
-/

@[expose] public section

namespace Haspelmath2025a.Examples

def ex1 : Datum :=
  { id := "haspelmath2025a_ex1"
    source := ⟨"haspelmath-2025a", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lee is a baker."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "classificational")] }

def ex2 : Datum :=
  { id := "haspelmath2025a_ex2"
    source := ⟨"haspelmath-2025a", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kim is my mother."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "equational")] }

def ex3 : Datum :=
  { id := "haspelmath2025a_ex3"
    source := ⟨"haspelmath-2025a", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The bird is small."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "attributional")] }

def ex4 : Datum :=
  { id := "haspelmath2025a_ex4"
    source := ⟨"haspelmath-2025a", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The bird is on the roof."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "predlocative")] }

def ex5 : Datum :=
  { id := "haspelmath2025a_ex5"
    source := ⟨"haspelmath-2025a", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is a bird on the roof."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "existential")] }

def ex6 : Datum :=
  { id := "haspelmath2025a_ex6"
    source := ⟨"haspelmath-2025a", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have a boat."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "predpossessive")] }

def ex7 : Datum :=
  { id := "haspelmath2025a_ex7"
    source := ⟨"haspelmath-2025a", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The boat belongs to me."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "appertentive")] }

def ex8a : Datum :=
  { id := "haspelmath2025a_ex8a"
    source := ⟨"haspelmath-2025a", "(8a)"⟩
    reportedIn := none
    method := some .description
    language := "lezg1247"
    primaryText := "Zi buba kešiš ja."
    glossedTokens := [("Zi", "my"), ("buba", "father"), ("kešiš", "priest"), ("ja", "COP")]
    glossedWords := [⟨[['Z', 'i']], [['m', 'y']]⟩, ⟨[['b', 'u', 'b', 'a']], [['f', 'a', 't', 'h', 'e', 'r']]⟩, ⟨[['k', 'e', 'š', 'i', 'š']], [['p', 'r', 'i', 'e', 's', 't']]⟩, ⟨[['j', 'a']], [['C', 'O', 'P']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "classificational"), ("bold", "ja"), ("boldGloss", "COP")] }

def ex8b : Datum :=
  { id := "haspelmath2025a_ex8b"
    source := ⟨"haspelmath-2025a", "(8b)"⟩
    reportedIn := none
    method := some .description
    language := "lezg1247"
    primaryText := "Wi ktab im ja."
    glossedTokens := [("Wi", "your"), ("ktab", "book"), ("im", "this.one"), ("ja", "COP")]
    glossedWords := [⟨[['W', 'i']], [['y', 'o', 'u', 'r']]⟩, ⟨[['k', 't', 'a', 'b']], [['b', 'o', 'o', 'k']]⟩, ⟨[['i', 'm']], [['t', 'h', 'i', 's', '.', 'o', 'n', 'e']]⟩, ⟨[['j', 'a']], [['C', 'O', 'P']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "equational"), ("bold", "ja"), ("boldGloss", "COP")] }

def ex9a : Datum :=
  { id := "haspelmath2025a_ex9a"
    source := ⟨"haspelmath-2025a", "(9a)"⟩
    reportedIn := none
    method := some .description
    language := "wels1247"
    primaryText := "Mae Caerdydd yn ddinas hardd."
    glossedTokens := [("Mae", "be.PRS.3SG"), ("Caerdydd", "Cardiff"), ("yn", "PRED"), ("ddinas", "city"), ("hardd", "beautiful")]
    glossedWords := [⟨[['M', 'a', 'e']], [['b', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G']]⟩, ⟨[['C', 'a', 'e', 'r', 'd', 'y', 'd', 'd']], [['C', 'a', 'r', 'd', 'i', 'f', 'f']]⟩, ⟨[['y', 'n']], [['P', 'R', 'E', 'D']]⟩, ⟨[['d', 'd', 'i', 'n', 'a', 's']], [['c', 'i', 't', 'y']]⟩, ⟨[['h', 'a', 'r', 'd', 'd']], [['b', 'e', 'a', 'u', 't', 'i', 'f', 'u', 'l']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "classificational"), ("bold", "Mae"), ("boldGloss", "be.PRS.3SG")] }

def ex9b : Datum :=
  { id := "haspelmath2025a_ex9b"
    source := ⟨"haspelmath-2025a", "(9b)"⟩
    reportedIn := none
    method := some .description
    language := "wels1247"
    primaryText := "Caerdydd yw prifddinas Cymru."
    glossedTokens := [("Caerdydd", "Cardiff"), ("yw", "be.PRS.3SG"), ("prifddinas", "capital"), ("Cymru", "Wales")]
    glossedWords := [⟨[['C', 'a', 'e', 'r', 'd', 'y', 'd', 'd']], [['C', 'a', 'r', 'd', 'i', 'f', 'f']]⟩, ⟨[['y', 'w']], [['b', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G']]⟩, ⟨[['p', 'r', 'i', 'f', 'd', 'd', 'i', 'n', 'a', 's']], [['c', 'a', 'p', 'i', 't', 'a', 'l']]⟩, ⟨[['C', 'y', 'm', 'r', 'u']], [['W', 'a', 'l', 'e', 's']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "equational"), ("bold", "yw"), ("boldGloss", "be.PRS.3SG")] }

def ex10a : Datum :=
  { id := "haspelmath2025a_ex10a"
    source := ⟨"haspelmath-2025a", "(10a)"⟩
    reportedIn := none
    method := some .description
    language := "egyp1253"
    primaryText := "ʕAli mudarris"
    glossedTokens := [("ʕAli", "Ali"), ("mudarris", "teacher")]
    glossedWords := [⟨[['ʕ', 'A', 'l', 'i']], [['A', 'l', 'i']]⟩, ⟨[['m', 'u', 'd', 'a', 'r', 'r', 'i', 's']], [['t', 'e', 'a', 'c', 'h', 'e', 'r']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "classificational")] }

def ex10b : Datum :=
  { id := "haspelmath2025a_ex10b"
    source := ⟨"haspelmath-2025a", "(10b)"⟩
    reportedIn := none
    method := some .description
    language := "egyp1253"
    primaryText := "Miħammad huwwa ʕAli."
    glossedTokens := [("Miħammad", "Mohammed"), ("huwwa", "COP"), ("ʕAli", "Ali")]
    glossedWords := [⟨[['M', 'i', 'ħ', 'a', 'm', 'm', 'a', 'd']], [['M', 'o', 'h', 'a', 'm', 'm', 'e', 'd']]⟩, ⟨[['h', 'u', 'w', 'w', 'a']], [['C', 'O', 'P']]⟩, ⟨[['ʕ', 'A', 'l', 'i']], [['A', 'l', 'i']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Miħammad ʕAli.", .ungrammatical)]
    readings := []
    paperFeatures := [("construction", "equational"), ("bold", "huwwa"), ("boldGloss", "COP")] }

def ex23 : Datum :=
  { id := "haspelmath2025a_ex23"
    source := ⟨"haspelmath-2025a", "(23)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Man pul ziyâde dâram."
    glossedTokens := [("Man", "I"), ("pul", "money"), ("ziyâde", "much"), ("dâram", "have")]
    glossedWords := [⟨[['M', 'a', 'n']], [['I']]⟩, ⟨[['p', 'u', 'l']], [['m', 'o', 'n', 'e', 'y']]⟩, ⟨[['z', 'i', 'y', 'â', 'd', 'e']], [['m', 'u', 'c', 'h']]⟩, ⟨[['d', 'â', 'r', 'a', 'm']], [['h', 'a', 'v', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "transpossessive"), ("bold", "dâram"), ("boldGloss", "have")] }

def ex24 : Datum :=
  { id := "haspelmath2025a_ex24"
    source := ⟨"haspelmath-2025a", "(24)"⟩
    reportedIn := none
    method := some .description
    language := "haus1257"
    primaryText := "Bàlki ta-nàa dà kùjèeruu màasu kyâu."
    glossedTokens := [("Bàlki", "Balki"), ("ta-nàa", "3F.SG-be"), ("dà", "with"), ("kùjèeruu", "chairs"), ("màasu", "having"), ("kyâu", "beauty")]
    glossedWords := [⟨[['B', 'à', 'l', 'k', 'i']], [['B', 'a', 'l', 'k', 'i']]⟩, ⟨[['t', 'a'], ['n', 'à', 'a']], [['3', 'F', '.', 'S', 'G'], ['b', 'e']]⟩, ⟨[['d', 'à']], [['w', 'i', 't', 'h']]⟩, ⟨[['k', 'ù', 'j', 'è', 'e', 'r', 'u', 'u']], [['c', 'h', 'a', 'i', 'r', 's']]⟩, ⟨[['m', 'à', 'a', 's', 'u']], [['h', 'a', 'v', 'i', 'n', 'g']]⟩, ⟨[['k', 'y', 'â', 'u']], [['b', 'e', 'a', 'u', 't', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "compossessive"), ("bold", "ta-nàa"), ("boldGloss", "3F.SG-be")] }

def ex25 : Datum :=
  { id := "haspelmath2025a_ex25"
    source := ⟨"haspelmath-2025a", "(25)"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "Peka-lla on auto."
    glossedTokens := [("Peka-lla", "Pekka-ADESS"), ("on", "is"), ("auto", "car.SG.NOM")]
    glossedWords := [⟨[['P', 'e', 'k', 'a'], ['l', 'l', 'a']], [['P', 'e', 'k', 'k', 'a'], ['A', 'D', 'E', 'S', 'S']]⟩, ⟨[['o', 'n']], [['i', 's']]⟩, ⟨[['a', 'u', 't', 'o']], [['c', 'a', 'r', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "locpossessive"), ("bold", "on"), ("boldGloss", "is")] }

def ex26 : Datum :=
  { id := "haspelmath2025a_ex26"
    source := ⟨"haspelmath-2025a", "(26)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Mašin-a prinadležit Miš-e."
    glossedTokens := [("Mašin-a", "car-NOM"), ("prinadležit", "belongs"), ("Miš-e", "Misha-DAT")]
    glossedWords := [⟨[['M', 'a', 'š', 'i', 'n'], ['a']], [['c', 'a', 'r'], ['N', 'O', 'M']]⟩, ⟨[['p', 'r', 'i', 'n', 'a', 'd', 'l', 'e', 'ž', 'i', 't']], [['b', 'e', 'l', 'o', 'n', 'g', 's']]⟩, ⟨[['M', 'i', 'š'], ['e']], [['M', 'i', 's', 'h', 'a'], ['D', 'A', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "oblique-possessor"), ("bold", "prinadležit"), ("boldGloss", "belongs")] }

def ex27 : Datum :=
  { id := "haspelmath2025a_ex27"
    source := ⟨"haspelmath-2025a", "(27)"⟩
    reportedIn := none
    method := some .description
    language := "stan1288"
    primaryText := "Esta canasta es mía."
    glossedTokens := [("Esta", "this"), ("canasta", "basket"), ("es", "is"), ("mía", "mine")]
    glossedWords := [⟨[['E', 's', 't', 'a']], [['t', 'h', 'i', 's']]⟩, ⟨[['c', 'a', 'n', 'a', 's', 't', 'a']], [['b', 'a', 's', 'k', 'e', 't']]⟩, ⟨[['e', 's']], [['i', 's']]⟩, ⟨[['m', 'í', 'a']], [['m', 'i', 'n', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "independent-possessor"), ("bold", "es"), ("boldGloss", "is")] }

def ex31 : Datum :=
  { id := "haspelmath2025a_ex31"
    source := ⟨"haspelmath-2025a", "(31)"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "Satıcı-y-dı-m."
    glossedTokens := [("Satıcı-y-dı-m", "seller-COP-PST-1SG")]
    glossedWords := [⟨[['S', 'a', 't', 'ı', 'c', 'ı'], ['y'], ['d', 'ı'], ['m']], [['s', 'e', 'l', 'l', 'e', 'r'], ['C', 'O', 'P'], ['P', 'S', 'T'], ['1', 'S', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("bold", "y"), ("boldGloss", "COP")] }

def ex33 : Datum :=
  { id := "haspelmath2025a_ex33"
    source := ⟨"haspelmath-2025a", "(33)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Hay mucha gente afuera."
    glossedTokens := [("Hay", "EXV"), ("mucha", "many"), ("gente", "people"), ("afuera", "outside")]
    glossedWords := [⟨[['H', 'a', 'y']], [['E', 'X', 'V']]⟩, ⟨[['m', 'u', 'c', 'h', 'a']], [['m', 'a', 'n', 'y']]⟩, ⟨[['g', 'e', 'n', 't', 'e']], [['p', 'e', 'o', 'p', 'l', 'e']]⟩, ⟨[['a', 'f', 'u', 'e', 'r', 'a']], [['o', 'u', 't', 's', 'i', 'd', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "existential"), ("bold", "Hay"), ("boldGloss", "EXV")] }

def ex50 : Datum :=
  { id := "haspelmath2025a_ex50"
    source := ⟨"haspelmath-2025a", "(50)"⟩
    reportedIn := none
    method := some .description
    language := "taga1270"
    primaryText := "May mga tao sa labas."
    glossedTokens := [("May", "EXV"), ("mga", "PL"), ("tao", "person"), ("sa", "LOC"), ("labas", "outside")]
    glossedWords := [⟨[['M', 'a', 'y']], [['E', 'X', 'V']]⟩, ⟨[['m', 'g', 'a']], [['P', 'L']]⟩, ⟨[['t', 'a', 'o']], [['p', 'e', 'r', 's', 'o', 'n']]⟩, ⟨[['s', 'a']], [['L', 'O', 'C']]⟩, ⟨[['l', 'a', 'b', 'a', 's']], [['o', 'u', 't', 's', 'i', 'd', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "existive-copula"), ("bold", "May"), ("boldGloss", "EXV")] }

def ex51 : Datum :=
  { id := "haspelmath2025a_ex51"
    source := ⟨"haspelmath-2025a", "(51)"⟩
    reportedIn := none
    method := some .description
    language := "sese1246"
    primaryText := "Ler i annan koudvan zot pa reste lo sa zil."
    glossedTokens := [("Ler", "when"), ("i", "3SG"), ("annan", "have"), ("koudvan", "hurricane"), ("zot", "they"), ("pa", "not"), ("reste", "stay"), ("lo", "on"), ("sa", "the"), ("zil", "island")]
    glossedWords := [⟨[['L', 'e', 'r']], [['w', 'h', 'e', 'n']]⟩, ⟨[['i']], [['3', 'S', 'G']]⟩, ⟨[['a', 'n', 'n', 'a', 'n']], [['h', 'a', 'v', 'e']]⟩, ⟨[['k', 'o', 'u', 'd', 'v', 'a', 'n']], [['h', 'u', 'r', 'r', 'i', 'c', 'a', 'n', 'e']]⟩, ⟨[['z', 'o', 't']], [['t', 'h', 'e', 'y']]⟩, ⟨[['p', 'a']], [['n', 'o', 't']]⟩, ⟨[['r', 'e', 's', 't', 'e']], [['s', 't', 'a', 'y']]⟩, ⟨[['l', 'o']], [['o', 'n']]⟩, ⟨[['s', 'a']], [['t', 'h', 'e']]⟩, ⟨[['z', 'i', 'l']], [['i', 's', 'l', 'a', 'n', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "transpossessive-existential"), ("bold", "annan"), ("boldGloss", "have")] }

def ex52 : Datum :=
  { id := "haspelmath2025a_ex52"
    source := ⟨"haspelmath-2025a", "(52)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ci sono molte montagne in Svizzera."
    glossedTokens := [("Ci", "PROLOC"), ("sono", "are"), ("molte", "many"), ("montagne", "mountains"), ("in", "in"), ("Svizzera", "Switzerland")]
    glossedWords := [⟨[['C', 'i']], [['P', 'R', 'O', 'L', 'O', 'C']]⟩, ⟨[['s', 'o', 'n', 'o']], [['a', 'r', 'e']]⟩, ⟨[['m', 'o', 'l', 't', 'e']], [['m', 'a', 'n', 'y']]⟩, ⟨[['m', 'o', 'n', 't', 'a', 'g', 'n', 'e']], [['m', 'o', 'u', 'n', 't', 'a', 'i', 'n', 's']]⟩, ⟨[['i', 'n']], [['i', 'n']]⟩, ⟨[['S', 'v', 'i', 'z', 'z', 'e', 'r', 'a']], [['S', 'w', 'i', 't', 'z', 'e', 'r', 'l', 'a', 'n', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "prolocative"), ("bold", "Ci"), ("boldGloss", "PROLOC"), ("bold", "sono"), ("boldGloss", "are")] }

def ex53 : Datum :=
  { id := "haspelmath2025a_ex53"
    source := ⟨"haspelmath-2025a", "(53)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Kato-lla on lintu."
    glossedTokens := [("Kato-lla", "roof-ADESS"), ("on", "is"), ("lintu", "bird")]
    glossedWords := [⟨[['K', 'a', 't', 'o'], ['l', 'l', 'a']], [['r', 'o', 'o', 'f'], ['A', 'D', 'E', 'S', 'S']]⟩, ⟨[['o', 'n']], [['i', 's']]⟩, ⟨[['l', 'i', 'n', 't', 'u']], [['b', 'i', 'r', 'd']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "existent-postposing"), ("bold", "on"), ("boldGloss", "is")] }

def ex53cf : Datum :=
  { id := "haspelmath2025a_ex53cf"
    source := ⟨"haspelmath-2025a", "(53)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Lintu on katolla."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "predlocative")] }

def ex57 : Datum :=
  { id := "haspelmath2025a_ex57"
    source := ⟨"haspelmath-2025a", "(57)"⟩
    reportedIn := none
    method := some .description
    language := "mand1436"
    primaryText := "Wùlôo bé yíròo kótò."
    glossedTokens := [("Wùlôo", "dog.DET"), ("bé", "LCOP"), ("yíròo", "tree.DET"), ("kótò", "under")]
    glossedWords := [⟨[['W', 'ù', 'l', 'ô', 'o']], [['d', 'o', 'g', '.', 'D', 'E', 'T']]⟩, ⟨[['b', 'é']], [['L', 'C', 'O', 'P']]⟩, ⟨[['y', 'í', 'r', 'ò', 'o']], [['t', 'r', 'e', 'e', '.', 'D', 'E', 'T']]⟩, ⟨[['k', 'ó', 't', 'ò']], [['u', 'n', 'd', 'e', 'r']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "predlocative"), ("construction", "existential"), ("bold", "bé"), ("boldGloss", "LCOP")] }

def ex61 : Datum :=
  { id := "haspelmath2025a_ex61"
    source := ⟨"haspelmath-2025a", "(61)"⟩
    reportedIn := none
    method := some .description
    language := "hame1242"
    primaryText := "Noqó dá-u?"
    glossedTokens := [("Noqó", "water"), ("dá-u", "EXV-Q")]
    glossedWords := [⟨[['N', 'o', 'q', 'ó']], [['w', 'a', 't', 'e', 'r']]⟩, ⟨[['d', 'á'], ['u']], [['E', 'X', 'V'], ['Q']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "existential"), ("bold", "dá-u"), ("boldGloss", "EXV-Q")] }

def ex64 : Datum :=
  { id := "haspelmath2025a_ex64"
    source := ⟨"haspelmath-2025a", "(64)"⟩
    reportedIn := none
    method := some .corpus
    language := "lati1261"
    primaryText := "Cogito, ergo sum."
    glossedTokens := [("Cogito,", "I.think"), ("ergo", "therefore"), ("sum", "I.exist")]
    glossedWords := [⟨[['C', 'o', 'g', 'i', 't', 'o']], [['I', '.', 't', 'h', 'i', 'n', 'k']]⟩, ⟨[['e', 'r', 'g', 'o']], [['t', 'h', 'e', 'r', 'e', 'f', 'o', 'r', 'e']]⟩, ⟨[['s', 'u', 'm']], [['I', '.', 'e', 'x', 'i', 's', 't']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "hyparctic"), ("bold", "sum"), ("boldGloss", "I.exist")] }

def ex65 : Datum :=
  { id := "haspelmath2025a_ex65"
    source := ⟨"haspelmath-2025a", "(65)"⟩
    reportedIn := none
    method := some .description
    language := "stan1290"
    primaryText := "Il est des situations dans lesquelles personne n'aimerait se trouver."
    glossedTokens := [("Il", "it"), ("est", "is"), ("des", "INDF"), ("situations", "situations"), ("dans", "in"), ("lesquelles", "which"), ("personne", "nobody"), ("n'aimerait", "would.like"), ("se", "self"), ("trouver", "to.find")]
    glossedWords := [⟨[['I', 'l']], [['i', 't']]⟩, ⟨[['e', 's', 't']], [['i', 's']]⟩, ⟨[['d', 'e', 's']], [['I', 'N', 'D', 'F']]⟩, ⟨[['s', 'i', 't', 'u', 'a', 't', 'i', 'o', 'n', 's']], [['s', 'i', 't', 'u', 'a', 't', 'i', 'o', 'n', 's']]⟩, ⟨[['d', 'a', 'n', 's']], [['i', 'n']]⟩, ⟨[['l', 'e', 's', 'q', 'u', 'e', 'l', 'l', 'e', 's']], [['w', 'h', 'i', 'c', 'h']]⟩, ⟨[['p', 'e', 'r', 's', 'o', 'n', 'n', 'e']], [['n', 'o', 'b', 'o', 'd', 'y']]⟩, ⟨[['n', '\'', 'a', 'i', 'm', 'e', 'r', 'a', 'i', 't']], [['w', 'o', 'u', 'l', 'd', '.', 'l', 'i', 'k', 'e']]⟩, ⟨[['s', 'e']], [['s', 'e', 'l', 'f']]⟩, ⟨[['t', 'r', 'o', 'u', 'v', 'e', 'r']], [['t', 'o', '.', 'f', 'i', 'n', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "hyparctic"), ("bold", "est"), ("boldGloss", "is")] }

def ex66 : Datum :=
  { id := "haspelmath2025a_ex66"
    source := ⟨"haspelmath-2025a", "(66)"⟩
    reportedIn := none
    method := some .description
    language := "hame1242"
    primaryText := "Bajó dáa."
    glossedTokens := [("Bajó", "fate"), ("dáa", "EXV")]
    glossedWords := [⟨[['B', 'a', 'j', 'ó']], [['f', 'a', 't', 'e']]⟩, ⟨[['d', 'á', 'a']], [['E', 'X', 'V']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "hyparctic"), ("bold", "dáa"), ("boldGloss", "EXV")] }

def all : List Datum := [ex1, ex2, ex3, ex4, ex5, ex6, ex7, ex8a, ex8b, ex9a, ex9b, ex10a, ex10b, ex23, ex24, ex25, ex26, ex27, ex31, ex33, ex50, ex51, ex52, ex53, ex53cf, ex57, ex61, ex64, ex65, ex66]

end Haspelmath2025a.Examples
