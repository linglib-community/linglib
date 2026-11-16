module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Deal2011` — typed example data

Auto-generated from `Linglib/Data/Examples/Deal2011.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Deal2011.Examples`.
-/

@[expose] public section

namespace Deal2011.Examples

def ex1 : Datum :=
  { id := "deal2011_ex1"
    source := ⟨"deal-2011", "(1)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nezp1238"
    primaryText := "'inéhne-no'qa 'ee kii lepít cíickan."
    glossedTokens := [("'inéhne-no'qa", "take-MOD"), ("'ee", "you"), ("kii", "DEM"), ("lepít", "two"), ("cíickan", "blanket")]
    glossedWords := [⟨[['\'', 'i', 'n', 'é', 'h', 'n', 'e'], ['n', 'o', '\'', 'q', 'a']], [['t', 'a', 'k', 'e'], ['M', 'O', 'D']]⟩, ⟨[['\'', 'e', 'e']], [['y', 'o', 'u']]⟩, ⟨[['k', 'i', 'i']], [['D', 'E', 'M']]⟩, ⟨[['l', 'e', 'p', 'í', 't']], [['t', 'w', 'o']]⟩, ⟨[['c', 'í', 'i', 'c', 'k', 'a', 'n']], [['b', 'l', 'a', 'n', 'k', 'e', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := "A friend is preparing for a camping trip. I am taking this person around my camping supplies and suggesting appropriate things. I hand them two blankets and say:"
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .acceptable)]
    paperFeatures := [("modal", "o'qa"), ("environment", "unembedded")] }

def ex5 : Datum :=
  { id := "deal2011_ex5"
    source := ⟨"deal-2011", "(5)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nezp1238"
    primaryText := "kíye pe-ckilíi-toq-o'qa kulaawit-'ásx."
    glossedTokens := [("kíye", "we"), ("pe-ckilíi-toq-o'qa", "S.PL-return-back-MOD"), ("kulaawit-'ásx", "dark-before")]
    glossedWords := [⟨[['k', 'í', 'y', 'e']], [['w', 'e']]⟩, ⟨[['p', 'e'], ['c', 'k', 'i', 'l', 'í', 'i'], ['t', 'o', 'q'], ['o', '\'', 'q', 'a']], [['S', '.', 'P', 'L'], ['r', 'e', 't', 'u', 'r', 'n'], ['b', 'a', 'c', 'k'], ['M', 'O', 'D']]⟩, ⟨[['k', 'u', 'l', 'a', 'a', 'w', 'i', 't'], ['\'', 'á', 's', 'x']], [['d', 'a', 'r', 'k'], ['b', 'e', 'f', 'o', 'r', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Prompt: We have to get home before it gets dark."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "o'qa"), ("environment", "unembedded"), ("force", "necessity")] }

def ex6 : Datum :=
  { id := "deal2011_ex6"
    source := ⟨"deal-2011", "(6)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nezp1238"
    primaryText := "c'alawí 'ee ta'c c'ix̂-n'ipéecwi-se-∅ niimiipuutímt, ilx̂níi-ne c'íiqin 'ee 'a-cóokwa-no'qa."
    glossedTokens := [("c'alawí", "if"), ("'ee", "you"), ("ta'c", "good"), ("c'ix̂-n'ipéecwi-se-∅", "speak-DES-IMPF-PRES"), ("niimiipuutímt", "Nez.Perce.language"), ("ilx̂níi-ne", "many-OBJ"), ("c'íiqin", "word"), ("'ee", "you"), ("'a-cóokwa-no'qa", "3OBJ-know-MOD")]
    glossedWords := [⟨[['c', '\'', 'a', 'l', 'a', 'w', 'í']], [['i', 'f']]⟩, ⟨[['\'', 'e', 'e']], [['y', 'o', 'u']]⟩, ⟨[['t', 'a', '\'', 'c']], [['g', 'o', 'o', 'd']]⟩, ⟨[['c', '\'', 'i', 'x', '̂'], ['n', '\'', 'i', 'p', 'é', 'e', 'c', 'w', 'i'], ['s', 'e'], ['∅']], [['s', 'p', 'e', 'a', 'k'], ['D', 'E', 'S'], ['I', 'M', 'P', 'F'], ['P', 'R', 'E', 'S']]⟩, ⟨[['n', 'i', 'i', 'm', 'i', 'i', 'p', 'u', 'u', 't', 'í', 'm', 't']], [['N', 'e', 'z', '.', 'P', 'e', 'r', 'c', 'e', '.', 'l', 'a', 'n', 'g', 'u', 'a', 'g', 'e']]⟩, ⟨[['i', 'l', 'x', '̂', 'n', 'í', 'i'], ['n', 'e']], [['m', 'a', 'n', 'y'], ['O', 'B', 'J']]⟩, ⟨[['c', '\'', 'í', 'i', 'q', 'i', 'n']], [['w', 'o', 'r', 'd']]⟩, ⟨[['\'', 'e', 'e']], [['y', 'o', 'u']]⟩, ⟨[['\'', 'a'], ['c', 'ó', 'o', 'k', 'w', 'a'], ['n', 'o', '\'', 'q', 'a']], [['3', 'O', 'B', 'J'], ['k', 'n', 'o', 'w'], ['M', 'O', 'D']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Prompt: To speak well, you have to know a lot of words."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "o'qa"), ("environment", "conditional consequent"), ("force", "necessity")] }

def ex10 : Datum :=
  { id := "deal2011_ex10"
    source := ⟨"deal-2011", "(10)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "'i'yéwki hi-pa-c'íix̂-no'qa."
    glossedTokens := [("'i'yéwki", "slowly"), ("hi-pa-c'íix̂-no'qa", "3SUBJ-S.PL-speak-MOD")]
    glossedWords := [⟨[['\'', 'i', '\'', 'y', 'é', 'w', 'k', 'i']], [['s', 'l', 'o', 'w', 'l', 'y']]⟩, ⟨[['h', 'i'], ['p', 'a'], ['c', '\'', 'í', 'i', 'x', '̂'], ['n', 'o', '\'', 'q', 'a']], [['3', 'S', 'U', 'B', 'J'], ['S', '.', 'P', 'L'], ['s', 'p', 'e', 'a', 'k'], ['M', 'O', 'D']]⟩]
    lgrConformance := some .morphemeAligned
    context := "A discussion of how young people speak quickly, making them hard to understand."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "o'qa"), ("environment", "unembedded"), ("force", "necessity")] }

def ex46 : Datum :=
  { id := "deal2011_ex46"
    source := ⟨"deal-2011", "(46)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nezp1238"
    primaryText := "tamáalwit-wecet wéet'u 'ee x̂eeleewi-yo'qa 'étke k'omáy'c 'ee wee-s-∅ 'áatim."
    glossedTokens := [("tamáalwit-wecet", "rule-reason"), ("wéet'u", "not"), ("'ee", "you"), ("x̂eeleewi-yo'qa", "play-MOD"), ("'étke", "because"), ("k'omáy'c", "hurt"), ("'ee", "you"), ("wee-s-∅", "be-P-PRES"), ("'áatim", "arm")]
    glossedWords := [⟨[['t', 'a', 'm', 'á', 'a', 'l', 'w', 'i', 't'], ['w', 'e', 'c', 'e', 't']], [['r', 'u', 'l', 'e'], ['r', 'e', 'a', 's', 'o', 'n']]⟩, ⟨[['w', 'é', 'e', 't', '\'', 'u']], [['n', 'o', 't']]⟩, ⟨[['\'', 'e', 'e']], [['y', 'o', 'u']]⟩, ⟨[['x', '̂', 'e', 'e', 'l', 'e', 'e', 'w', 'i'], ['y', 'o', '\'', 'q', 'a']], [['p', 'l', 'a', 'y'], ['M', 'O', 'D']]⟩, ⟨[['\'', 'é', 't', 'k', 'e']], [['b', 'e', 'c', 'a', 'u', 's', 'e']]⟩, ⟨[['k', '\'', 'o', 'm', 'á', 'y', '\'', 'c']], [['h', 'u', 'r', 't']]⟩, ⟨[['\'', 'e', 'e']], [['y', 'o', 'u']]⟩, ⟨[['w', 'e', 'e'], ['s'], ['∅']], [['b', 'e'], ['P'], ['P', 'R', 'E', 'S']]⟩, ⟨[['\'', 'á', 'a', 't', 'i', 'm']], [['a', 'r', 'm']]⟩]
    lgrConformance := some .morphemeAligned
    context := "The referee is talking to an injured player."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "o'qa"), ("environment", "negation"), ("force", "possibility")] }

def ex47 : Datum :=
  { id := "deal2011_ex47"
    source := ⟨"deal-2011", "(47)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nezp1238"
    primaryText := "wéet'u kíye kíne pa-w'cáa-yo'qa, kíye ciklíi-six-∅."
    glossedTokens := [("wéet'u", "not"), ("kíye", "we"), ("kíne", "here"), ("pa-w'cáa-yo'qa", "S.PL-stay-MOD"), ("kíye", "we"), ("ciklíi-six-∅", "go.home-IMPF.PL-PRES")]
    glossedWords := [⟨[['w', 'é', 'e', 't', '\'', 'u']], [['n', 'o', 't']]⟩, ⟨[['k', 'í', 'y', 'e']], [['w', 'e']]⟩, ⟨[['k', 'í', 'n', 'e']], [['h', 'e', 'r', 'e']]⟩, ⟨[['p', 'a'], ['w', '\'', 'c', 'á', 'a'], ['y', 'o', '\'', 'q', 'a']], [['S', '.', 'P', 'L'], ['s', 't', 'a', 'y'], ['M', 'O', 'D']]⟩, ⟨[['k', 'í', 'y', 'e']], [['w', 'e']]⟩, ⟨[['c', 'i', 'k', 'l', 'í', 'i'], ['s', 'i', 'x'], ['∅']], [['g', 'o', '.', 'h', 'o', 'm', 'e'], ['I', 'M', 'P', 'F', '.', 'P', 'L'], ['P', 'R', 'E', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "o'qa"), ("environment", "negation"), ("force", "possibility")] }

def ex48 : Datum :=
  { id := "deal2011_ex48"
    source := ⟨"deal-2011", "(48)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nezp1238"
    primaryText := "Wéet'u máwa hi-pa-'yáax̂-no'qa 'inpeew'etúu-nm."
    glossedTokens := [("Wéet'u", "not"), ("máwa", "when"), ("hi-pa-'yáax̂-no'qa", "3SUBJ-S.PL-find-MOD"), ("'inpeew'etúu-nm", "police-ERG")]
    glossedWords := [⟨[['W', 'é', 'e', 't', '\'', 'u']], [['n', 'o', 't']]⟩, ⟨[['m', 'á', 'w', 'a']], [['w', 'h', 'e', 'n']]⟩, ⟨[['h', 'i'], ['p', 'a'], ['\'', 'y', 'á', 'a', 'x', '̂'], ['n', 'o', '\'', 'q', 'a']], [['3', 'S', 'U', 'B', 'J'], ['S', '.', 'P', 'L'], ['f', 'i', 'n', 'd'], ['M', 'O', 'D']]⟩, ⟨[['\'', 'i', 'n', 'p', 'e', 'e', 'w', '\'', 'e', 't', 'ú', 'u'], ['n', 'm']], [['p', 'o', 'l', 'i', 'c', 'e'], ['E', 'R', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .unacceptable)]
    paperFeatures := [("modal", "o'qa"), ("environment", "negation")] }

def ex49 : Datum :=
  { id := "deal2011_ex49"
    source := ⟨"deal-2011", "(49)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nezp1238"
    primaryText := "wéet'u 'ee kiy-ó'qa."
    glossedTokens := [("wéet'u", "not"), ("'ee", "you"), ("kiy-ó'qa", "go-MOD")]
    glossedWords := [⟨[['w', 'é', 'e', 't', '\'', 'u']], [['n', 'o', 't']]⟩, ⟨[['\'', 'e', 'e']], [['y', 'o', 'u']]⟩, ⟨[['k', 'i', 'y'], ['ó', '\'', 'q', 'a']], [['g', 'o'], ['M', 'O', 'D']]⟩]
    lgrConformance := some .morphemeAligned
    context := "You are explaining to someone who thinks they have to leave that they are not in fact required to do so. It's not necessary for them to leave."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "o'qa"), ("environment", "negation"), ("force", "necessity")] }

def ex50 : Datum :=
  { id := "deal2011_ex50"
    source := ⟨"deal-2011", "(50)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nezp1238"
    primaryText := "wéet'u 'ee timiipni-yo'qa."
    glossedTokens := [("wéet'u", "not"), ("'ee", "you"), ("timiipni-yo'qa", "remember-MOD")]
    glossedWords := [⟨[['w', 'é', 'e', 't', '\'', 'u']], [['n', 'o', 't']]⟩, ⟨[['\'', 'e', 'e']], [['y', 'o', 'u']]⟩, ⟨[['t', 'i', 'm', 'i', 'i', 'p', 'n', 'i'], ['y', 'o', '\'', 'q', 'a']], [['r', 'e', 'm', 'e', 'm', 'b', 'e', 'r'], ['M', 'O', 'D']]⟩]
    lgrConformance := some .morphemeAligned
    context := "I tell someone my number and I see that they are trying to remember it. I say, 'You don't have to remember it; here's my card.'"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "o'qa"), ("environment", "negation"), ("force", "necessity")] }

def ex51 : Datum :=
  { id := "deal2011_ex51"
    source := ⟨"deal-2011", "(51)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nezp1238"
    primaryText := "hi-wqíi-cix-∅ 'iléx̂ni hipt ke yox̂ hi-pá-ap-o'qa."
    glossedTokens := [("hi-wqíi-cix-∅", "3SUBJ-throw.away-IMPF.PL-PRES"), ("'iléx̂ni", "a.lot"), ("hipt", "food"), ("ke", "REL"), ("yox̂", "DEM"), ("hi-pá-ap-o'qa", "3SUBJ-S.PL-eat-MOD")]
    glossedWords := [⟨[['h', 'i'], ['w', 'q', 'í', 'i'], ['c', 'i', 'x'], ['∅']], [['3', 'S', 'U', 'B', 'J'], ['t', 'h', 'r', 'o', 'w', '.', 'a', 'w', 'a', 'y'], ['I', 'M', 'P', 'F', '.', 'P', 'L'], ['P', 'R', 'E', 'S']]⟩, ⟨[['\'', 'i', 'l', 'é', 'x', '̂', 'n', 'i']], [['a', '.', 'l', 'o', 't']]⟩, ⟨[['h', 'i', 'p', 't']], [['f', 'o', 'o', 'd']]⟩, ⟨[['k', 'e']], [['R', 'E', 'L']]⟩, ⟨[['y', 'o', 'x', '̂']], [['D', 'E', 'M']]⟩, ⟨[['h', 'i'], ['p', 'á'], ['a', 'p'], ['o', '\'', 'q', 'a']], [['3', 'S', 'U', 'B', 'J'], ['S', '.', 'P', 'L'], ['e', 'a', 't'], ['M', 'O', 'D']]⟩]
    lgrConformance := some .morphemeAligned
    context := "I am watching people clean out a cooler and throw away various things."
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .acceptable)]
    paperFeatures := [("modal", "o'qa"), ("environment", "existential restriction")] }

def ex52 : Datum :=
  { id := "deal2011_ex52"
    source := ⟨"deal-2011", "(52)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nezp1238"
    primaryText := "hi-wqíi-cix-∅ 'óykala hipt ke yox̂ hi-pá-ap-o'qa."
    glossedTokens := [("hi-wqíi-cix-∅", "3SUBJ-throw.away-IMPF.PL-PRES"), ("'óykala", "all"), ("hipt", "food"), ("ke", "REL"), ("yox̂", "DEM"), ("hi-pá-ap-o'qa", "3SUBJ-S.PL-eat-MOD")]
    glossedWords := [⟨[['h', 'i'], ['w', 'q', 'í', 'i'], ['c', 'i', 'x'], ['∅']], [['3', 'S', 'U', 'B', 'J'], ['t', 'h', 'r', 'o', 'w', '.', 'a', 'w', 'a', 'y'], ['I', 'M', 'P', 'F', '.', 'P', 'L'], ['P', 'R', 'E', 'S']]⟩, ⟨[['\'', 'ó', 'y', 'k', 'a', 'l', 'a']], [['a', 'l', 'l']]⟩, ⟨[['h', 'i', 'p', 't']], [['f', 'o', 'o', 'd']]⟩, ⟨[['k', 'e']], [['R', 'E', 'L']]⟩, ⟨[['y', 'o', 'x', '̂']], [['D', 'E', 'M']]⟩, ⟨[['h', 'i'], ['p', 'á'], ['a', 'p'], ['o', '\'', 'q', 'a']], [['3', 'S', 'U', 'B', 'J'], ['S', '.', 'P', 'L'], ['e', 'a', 't'], ['M', 'O', 'D']]⟩]
    lgrConformance := some .morphemeAligned
    context := "I am watching people clean out a cooler and throw away various things."
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .unacceptable)]
    paperFeatures := [("modal", "o'qa"), ("environment", "universal restriction")] }

def ex53 : Datum :=
  { id := "deal2011_ex53"
    source := ⟨"deal-2011", "(53)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nezp1238"
    primaryText := "'e-hitéeme-∅ 'óykala-na ke-m 'a-hitáama-no'qa!"
    glossedTokens := [("'e-hitéeme-∅", "3OBJ-read-IMPV"), ("'óykala-na", "everything-OBJ"), ("ke-m", "REL-2SG"), ("'a-hitáama-no'qa", "3OBJ-read-MOD")]
    glossedWords := [⟨[['\'', 'e'], ['h', 'i', 't', 'é', 'e', 'm', 'e'], ['∅']], [['3', 'O', 'B', 'J'], ['r', 'e', 'a', 'd'], ['I', 'M', 'P', 'V']]⟩, ⟨[['\'', 'ó', 'y', 'k', 'a', 'l', 'a'], ['n', 'a']], [['e', 'v', 'e', 'r', 'y', 't', 'h', 'i', 'n', 'g'], ['O', 'B', 'J']]⟩, ⟨[['k', 'e'], ['m']], [['R', 'E', 'L'], ['2', 'S', 'G']]⟩, ⟨[['\'', 'a'], ['h', 'i', 't', 'á', 'a', 'm', 'a'], ['n', 'o', '\'', 'q', 'a']], [['3', 'O', 'B', 'J'], ['r', 'e', 'a', 'd'], ['M', 'O', 'D']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .unacceptable)]
    paperFeatures := [("modal", "o'qa"), ("environment", "universal restriction")] }

def ex54 : Datum :=
  { id := "deal2011_ex54"
    source := ⟨"deal-2011", "(54)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nezp1238"
    primaryText := "ke-m itúu 'iim kiy-ó'qa 'iin wáaqo' kúu-∅-ye."
    glossedTokens := [("ke-m", "REL-2SG"), ("itúu", "what"), ("'iim", "you"), ("kiy-ó'qa", "do-MOD"), ("'iin", "I"), ("wáaqo'", "already"), ("kúu-∅-ye", "do-P-REM.PST")]
    glossedWords := [⟨[['k', 'e'], ['m']], [['R', 'E', 'L'], ['2', 'S', 'G']]⟩, ⟨[['i', 't', 'ú', 'u']], [['w', 'h', 'a', 't']]⟩, ⟨[['\'', 'i', 'i', 'm']], [['y', 'o', 'u']]⟩, ⟨[['k', 'i', 'y'], ['ó', '\'', 'q', 'a']], [['d', 'o'], ['M', 'O', 'D']]⟩, ⟨[['\'', 'i', 'i', 'n']], [['I']]⟩, ⟨[['w', 'á', 'a', 'q', 'o', '\'']], [['a', 'l', 'r', 'e', 'a', 'd', 'y']]⟩, ⟨[['k', 'ú', 'u'], ['∅'], ['y', 'e']], [['d', 'o'], ['P'], ['R', 'E', 'M', '.', 'P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .unacceptable)]
    paperFeatures := [("modal", "o'qa"), ("environment", "universal restriction")] }

def ex57 : Datum :=
  { id := "deal2011_ex57"
    source := ⟨"deal-2011", "(57)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nezp1238"
    primaryText := "c'alawí wéeyux̂ 'u-u-s-∅ k'omáy'c, saykiptaw'atóo-nm háamti'c páa-x-no'qa."
    glossedTokens := [("c'alawí", "if"), ("wéeyux̂", "leg"), ("'u-u-s-∅", "3GEN-be-P-PRES"), ("k'omáy'c", "injured"), ("saykiptaw'atóo-nm", "doctor-ERG"), ("háamti'c", "quickly"), ("páa-x-no'qa", "3/3-see-MOD")]
    glossedWords := [⟨[['c', '\'', 'a', 'l', 'a', 'w', 'í']], [['i', 'f']]⟩, ⟨[['w', 'é', 'e', 'y', 'u', 'x', '̂']], [['l', 'e', 'g']]⟩, ⟨[['\'', 'u'], ['u'], ['s'], ['∅']], [['3', 'G', 'E', 'N'], ['b', 'e'], ['P'], ['P', 'R', 'E', 'S']]⟩, ⟨[['k', '\'', 'o', 'm', 'á', 'y', '\'', 'c']], [['i', 'n', 'j', 'u', 'r', 'e', 'd']]⟩, ⟨[['s', 'a', 'y', 'k', 'i', 'p', 't', 'a', 'w', '\'', 'a', 't', 'ó', 'o'], ['n', 'm']], [['d', 'o', 'c', 't', 'o', 'r'], ['E', 'R', 'G']]⟩, ⟨[['h', 'á', 'a', 'm', 't', 'i', '\'', 'c']], [['q', 'u', 'i', 'c', 'k', 'l', 'y']]⟩, ⟨[['p', 'á', 'a'], ['x'], ['n', 'o', '\'', 'q', 'a']], [['3', '/', '3'], ['s', 'e', 'e'], ['M', 'O', 'D']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "o'qa"), ("environment", "conditional consequent"), ("force", "necessity")] }

def ex58 : Datum :=
  { id := "deal2011_ex58"
    source := ⟨"deal-2011", "(58)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nezp1238"
    primaryText := "c'alawí saykiptaw'atóo-nm háamti'c páa-x-no'qa, simíinikem-x hi-kiy-ó'qa."
    glossedTokens := [("c'alawí", "if"), ("saykiptaw'atóo-nm", "doctor-ERG"), ("háamti'c", "quickly"), ("páa-x-no'qa", "3/3-see-MOD"), ("simíinikem-x", "Lewiston-to"), ("hi-kiy-ó'qa", "3SUBJ-go-MOD")]
    glossedWords := [⟨[['c', '\'', 'a', 'l', 'a', 'w', 'í']], [['i', 'f']]⟩, ⟨[['s', 'a', 'y', 'k', 'i', 'p', 't', 'a', 'w', '\'', 'a', 't', 'ó', 'o'], ['n', 'm']], [['d', 'o', 'c', 't', 'o', 'r'], ['E', 'R', 'G']]⟩, ⟨[['h', 'á', 'a', 'm', 't', 'i', '\'', 'c']], [['q', 'u', 'i', 'c', 'k', 'l', 'y']]⟩, ⟨[['p', 'á', 'a'], ['x'], ['n', 'o', '\'', 'q', 'a']], [['3', '/', '3'], ['s', 'e', 'e'], ['M', 'O', 'D']]⟩, ⟨[['s', 'i', 'm', 'í', 'i', 'n', 'i', 'k', 'e', 'm'], ['x']], [['L', 'e', 'w', 'i', 's', 't', 'o', 'n'], ['t', 'o']]⟩, ⟨[['h', 'i'], ['k', 'i', 'y'], ['ó', '\'', 'q', 'a']], [['3', 'S', 'U', 'B', 'J'], ['g', 'o'], ['M', 'O', 'D']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .unacceptable)]
    paperFeatures := [("modal", "o'qa"), ("environment", "conditional antecedent")] }

def ex59 : Datum :=
  { id := "deal2011_ex59"
    source := ⟨"deal-2011", "(59)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nezp1238"
    primaryText := "c'alawí 'aac-o'qa, kaa 'aac-o'."
    glossedTokens := [("c'alawí", "if"), ("'aac-o'qa", "enter-MOD"), ("kaa", "then"), ("'aac-o'", "enter-PROSP")]
    glossedWords := [⟨[['c', '\'', 'a', 'l', 'a', 'w', 'í']], [['i', 'f']]⟩, ⟨[['\'', 'a', 'a', 'c'], ['o', '\'', 'q', 'a']], [['e', 'n', 't', 'e', 'r'], ['M', 'O', 'D']]⟩, ⟨[['k', 'a', 'a']], [['t', 'h', 'e', 'n']]⟩, ⟨[['\'', 'a', 'a', 'c'], ['o', '\'']], [['e', 'n', 't', 'e', 'r'], ['P', 'R', 'O', 'S', 'P']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .unacceptable)]
    paperFeatures := [("modal", "o'qa"), ("environment", "conditional antecedent")] }

def ex60 : Datum :=
  { id := "deal2011_ex60"
    source := ⟨"deal-2011", "(60)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nezp1238"
    primaryText := "c'alawí 'a-múu-no'qa saykiptaw'atóo-na, kaa 'e-múu-nu'."
    glossedTokens := [("c'alawí", "if"), ("'a-múu-no'qa", "3OBJ-call-MOD"), ("saykiptaw'atóo-na", "doctor-OBJ"), ("kaa", "then"), ("'e-múu-nu'", "3OBJ-call-PROSP")]
    glossedWords := [⟨[['c', '\'', 'a', 'l', 'a', 'w', 'í']], [['i', 'f']]⟩, ⟨[['\'', 'a'], ['m', 'ú', 'u'], ['n', 'o', '\'', 'q', 'a']], [['3', 'O', 'B', 'J'], ['c', 'a', 'l', 'l'], ['M', 'O', 'D']]⟩, ⟨[['s', 'a', 'y', 'k', 'i', 'p', 't', 'a', 'w', '\'', 'a', 't', 'ó', 'o'], ['n', 'a']], [['d', 'o', 'c', 't', 'o', 'r'], ['O', 'B', 'J']]⟩, ⟨[['k', 'a', 'a']], [['t', 'h', 'e', 'n']]⟩, ⟨[['\'', 'e'], ['m', 'ú', 'u'], ['n', 'u', '\'']], [['3', 'O', 'B', 'J'], ['c', 'a', 'l', 'l'], ['P', 'R', 'O', 'S', 'P']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Prompt: If I have to call the doctor, I will."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "o'qa"), ("environment", "conditional antecedent"), ("force", "necessity")] }

def all : List Datum := [ex1, ex5, ex6, ex10, ex46, ex47, ex48, ex49, ex50, ex51, ex52, ex53, ex54, ex57, ex58, ex59, ex60]

/-- The environment of the modal in the sentence. -/
inductive Environment where
  /-- unembedded: an unembedded clause -/
  | unembedded
  /-- existential restriction: the restriction of an existential quantifier -/
  | existentialRestriction
  /-- conditional consequent: the consequent of a conditional -/
  | conditionalConsequent
  /-- negation: the scope of negation -/
  | negation
  /-- universal restriction: the restriction of a universal quantifier -/
  | universalRestriction
  /-- conditional antecedent: the antecedent of a conditional -/
  | conditionalAntecedent
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `environment`. -/
def environment (e : Datum) : Option Environment :=
  e.parse? "environment" [("unembedded", .unembedded), ("existential restriction", .existentialRestriction),
    ("conditional consequent", .conditionalConsequent), ("negation", .negation),
    ("universal restriction", .universalRestriction),
    ("conditional antecedent", .conditionalAntecedent)]

end Deal2011.Examples
