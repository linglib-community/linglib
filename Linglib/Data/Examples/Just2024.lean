module

public import Linglib.Data.Examples.Schema

/-!
# `Just2024` — typed example data

Auto-generated from `Linglib/Data/Examples/Just2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Just2024.Examples`.
-/

@[expose] public section

namespace Just2024.Examples

def ex_2a : Datum :=
  { id := "just2024_2a"
    source := ⟨"just-2024", "(2a)"⟩
    reportedIn := none
    language := "east2879"
    primaryText := "äj-nø=tee-nø wöär-s-øt"
    glossedTokens := [("äj-nø=tee-nø", "drink-GER=eat-GER"), ("wöär-s-øt", "make-PST-3PL")]
    glossedWords := [⟨[['ä', 'j'], ['n', 'ø'], ['t', 'e', 'e'], ['n', 'ø']], [['d', 'r', 'i', 'n', 'k'], ['G', 'E', 'R'], ['e', 'a', 't'], ['G', 'E', 'R']]⟩, ⟨[['w', 'ö', 'ä', 'r'], ['s'], ['ø', 't']], [['m', 'a', 'k', 'e'], ['P', 'S', 'T'], ['3', 'P', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "P"), ("indexed", "false"), ("condition", "indefinite")] }

def ex_2b : Datum :=
  { id := "just2024_2b"
    source := ⟨"just-2024", "(2b)"⟩
    reportedIn := none
    language := "east2879"
    primaryText := "õõw-øm öät kont-iitø"
    glossedTokens := [("õõw-øm", "door-ACC"), ("öät", "NEG"), ("kont-iitø", "find-3SG>SG")]
    glossedWords := [⟨[['õ', 'õ', 'w'], ['ø', 'm']], [['d', 'o', 'o', 'r'], ['A', 'C', 'C']]⟩, ⟨[['ö', 'ä', 't']], [['N', 'E', 'G']]⟩, ⟨[['k', 'o', 'n', 't'], ['i', 'i', 't', 'ø']], [['f', 'i', 'n', 'd'], ['3', 'S', 'G', '>', 'S', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "P"), ("indexed", "true"), ("condition", "topical")] }

def ex_3 : Datum :=
  { id := "just2024_3"
    source := ⟨"just-2024", "(3)"⟩
    reportedIn := none
    language := "mace1250"
    primaryText := "Jana *(go)=bara režiser-ot"
    glossedTokens := [("Jana", "Jana"), ("*(go)=bara", "3SG.M.ACC=look.for.3SG"), ("režiser-ot", "movie.director-DEF.M")]
    glossedWords := [⟨[['J', 'a', 'n', 'a']], [['J', 'a', 'n', 'a']]⟩, ⟨[['*', 'g', 'o'], ['b', 'a', 'r', 'a']], [['3', 'S', 'G', '.', 'M', '.', 'A', 'C', 'C'], ['l', 'o', 'o', 'k', '.', 'f', 'o', 'r', '.', '3', 'S', 'G']]⟩, ⟨[['r', 'e', 'ž', 'i', 's', 'e', 'r'], ['o', 't']], [['m', 'o', 'v', 'i', 'e', '.', 'd', 'i', 'r', 'e', 'c', 't', 'o', 'r'], ['D', 'E', 'F', '.', 'M']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "P"), ("indexed", "true"), ("condition", "definite")] }

def ex_4a : Datum :=
  { id := "just2024_4a"
    source := ⟨"just-2024", "(4a)"⟩
    reportedIn := none
    language := "kagu1239"
    primaryText := "Awafele ha-wa-koma dijoka"
    glossedTokens := [("Awafele", "C2.woman"), ("ha-wa-koma", "PST-C2.A-kill"), ("dijoka", "C5.snake")]
    glossedWords := [⟨[['A', 'w', 'a', 'f', 'e', 'l', 'e']], [['C', '2', '.', 'w', 'o', 'm', 'a', 'n']]⟩, ⟨[['h', 'a'], ['w', 'a'], ['k', 'o', 'm', 'a']], [['P', 'S', 'T'], ['C', '2', '.', 'A'], ['k', 'i', 'l', 'l']]⟩, ⟨[['d', 'i', 'j', 'o', 'k', 'a']], [['C', '5', '.', 's', 'n', 'a', 'k', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "P"), ("indexed", "false")] }

def ex_4b : Datum :=
  { id := "just2024_4b"
    source := ⟨"just-2024", "(4b)"⟩
    reportedIn := none
    language := "kagu1239"
    primaryText := "Ka-mu-on-aga imukulu akwe"
    glossedTokens := [("Ka-mu-on-aga", "PST.3SG.A-C1.P-see-IPFV"), ("imukulu", "C1.big"), ("akwe", "3SG.POSS")]
    glossedWords := [⟨[['K', 'a'], ['m', 'u'], ['o', 'n'], ['a', 'g', 'a']], [['P', 'S', 'T', '.', '3', 'S', 'G', '.', 'A'], ['C', '1', '.', 'P'], ['s', 'e', 'e'], ['I', 'P', 'F', 'V']]⟩, ⟨[['i', 'm', 'u', 'k', 'u', 'l', 'u']], [['C', '1', '.', 'b', 'i', 'g']]⟩, ⟨[['a', 'k', 'w', 'e']], [['3', 'S', 'G', '.', 'P', 'O', 'S', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "P"), ("indexed", "true"), ("condition", "animate")] }

def ex_4c : Datum :=
  { id := "just2024_4c"
    source := ⟨"just-2024", "(4c)"⟩
    reportedIn := none
    language := "kagu1239"
    primaryText := "Mheho i-ku-mu-ogoh-es-a"
    glossedTokens := [("Mheho", "C9.cold"), ("i-ku-mu-ogoh-es-a", "C9.A-PRS-3SG.P-fear-CAUS-FV")]
    glossedWords := [⟨[['M', 'h', 'e', 'h', 'o']], [['C', '9', '.', 'c', 'o', 'l', 'd']]⟩, ⟨[['i'], ['k', 'u'], ['m', 'u'], ['o', 'g', 'o', 'h'], ['e', 's'], ['a']], [['C', '9', '.', 'A'], ['P', 'R', 'S'], ['3', 'S', 'G', '.', 'P'], ['f', 'e', 'a', 'r'], ['C', 'A', 'U', 'S'], ['F', 'V']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "P"), ("indexed", "true"), ("condition", "animate")] }

def ex_5a : Datum :=
  { id := "just2024_5a"
    source := ⟨"just-2024", "(5a)"⟩
    reportedIn := none
    language := "teiw1235"
    primaryText := "Miaag yivar ga-sii"
    glossedTokens := [("Miaag", "yesterday"), ("yivar", "dog"), ("ga-sii", "3SG.P-bite")]
    glossedWords := [⟨[['M', 'i', 'a', 'a', 'g']], [['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y']]⟩, ⟨[['y', 'i', 'v', 'a', 'r']], [['d', 'o', 'g']]⟩, ⟨[['g', 'a'], ['s', 'i', 'i']], [['3', 'S', 'G', '.', 'P'], ['b', 'i', 't', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "P"), ("indexed", "true"), ("condition", "animate")] }

def ex_5b : Datum :=
  { id := "just2024_5b"
    source := ⟨"just-2024", "(5b)"⟩
    reportedIn := none
    language := "teiw1235"
    primaryText := "Miaag yivar ga'an sii"
    glossedTokens := [("Miaag", "yesterday"), ("yivar", "dog"), ("ga'an", "3SG"), ("sii", "bite")]
    glossedWords := [⟨[['M', 'i', 'a', 'a', 'g']], [['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y']]⟩, ⟨[['y', 'i', 'v', 'a', 'r']], [['d', 'o', 'g']]⟩, ⟨[['g', 'a', '\'', 'a', 'n']], [['3', 'S', 'G']]⟩, ⟨[['s', 'i', 'i']], [['b', 'i', 't', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "P"), ("indexed", "false"), ("condition", "focus")] }

def ex_6a : Datum :=
  { id := "just2024_6a"
    source := ⟨"just-2024", "(6a)"⟩
    reportedIn := none
    language := "rund1242"
    primaryText := "Abâna ba-ára-nyôye amatá"
    glossedTokens := [("Abâna", "C2.children"), ("ba-ára-nyôye", "C2-PST-drink:PFV"), ("amatá", "C1.milk")]
    glossedWords := [⟨[['A', 'b', 'â', 'n', 'a']], [['C', '2', '.', 'c', 'h', 'i', 'l', 'd', 'r', 'e', 'n']]⟩, ⟨[['b', 'a'], ['á', 'r', 'a'], ['n', 'y', 'ô', 'y', 'e']], [['C', '2'], ['P', 'S', 'T'], ['d', 'r', 'i', 'n', 'k', ':', 'P', 'F', 'V']]⟩, ⟨[['a', 'm', 'a', 't', 'á']], [['C', '1', '.', 'm', 'i', 'l', 'k']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "true"), ("condition", "topical")] }

def ex_6b : Datum :=
  { id := "just2024_6b"
    source := ⟨"just-2024", "(6b)"⟩
    reportedIn := none
    language := "rund1242"
    primaryText := "Amatá y-á-nyôye abâna"
    glossedTokens := [("Amatá", "C1.milk"), ("y-á-nyôye", "C1.PST-drink:PFV"), ("abâna", "C2.children")]
    glossedWords := [⟨[['A', 'm', 'a', 't', 'á']], [['C', '1', '.', 'm', 'i', 'l', 'k']]⟩, ⟨[['y'], ['á'], ['n', 'y', 'ô', 'y', 'e']], [['C', '1', '.', 'P', 'S', 'T'], ['d', 'r', 'i', 'n', 'k', ':', 'P', 'F', 'V']]⟩, ⟨[['a', 'b', 'â', 'n', 'a']], [['C', '2', '.', 'c', 'h', 'i', 'l', 'd', 'r', 'e', 'n']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "false"), ("condition", "focus")] }

def ex_6c : Datum :=
  { id := "just2024_6c"
    source := ⟨"just-2024", "(6c)"⟩
    reportedIn := none
    language := "rund1242"
    primaryText := "ha-á-nyôye amatá abâna"
    glossedTokens := [("ha-á-nyôye", "C10.LOC-PST-drink:PFV"), ("amatá", "C1.milk"), ("abâna", "C2.children")]
    glossedWords := [⟨[['h', 'a'], ['á'], ['n', 'y', 'ô', 'y', 'e']], [['C', '1', '0', '.', 'L', 'O', 'C'], ['P', 'S', 'T'], ['d', 'r', 'i', 'n', 'k', ':', 'P', 'F', 'V']]⟩, ⟨[['a', 'm', 'a', 't', 'á']], [['C', '1', '.', 'm', 'i', 'l', 'k']]⟩, ⟨[['a', 'b', 'â', 'n', 'a']], [['C', '2', '.', 'c', 'h', 'i', 'l', 'd', 'r', 'e', 'n']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "false"), ("condition", "focus")] }

def ex_7a : Datum :=
  { id := "just2024_7a"
    source := ⟨"just-2024", "(7a)"⟩
    reportedIn := none
    language := "wels1247"
    primaryText := "Gwel-on nhw ddraig"
    glossedTokens := [("Gwel-on", "see-3PL.PST"), ("nhw", "they"), ("ddraig", "dragon")]
    glossedWords := [⟨[['G', 'w', 'e', 'l'], ['o', 'n']], [['s', 'e', 'e'], ['3', 'P', 'L', '.', 'P', 'S', 'T']]⟩, ⟨[['n', 'h', 'w']], [['t', 'h', 'e', 'y']]⟩, ⟨[['d', 'd', 'r', 'a', 'i', 'g']], [['d', 'r', 'a', 'g', 'o', 'n']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "true"), ("condition", "pronominal")] }

def ex_7b : Datum :=
  { id := "just2024_7b"
    source := ⟨"just-2024", "(7b)"⟩
    reportedIn := none
    language := "wels1247"
    primaryText := "Gwel-odd y bechgyn ddraig"
    glossedTokens := [("Gwel-odd", "see-3SG.PST"), ("y", "DEF"), ("bechgyn", "boy.PL"), ("ddraig", "dragon")]
    glossedWords := [⟨[['G', 'w', 'e', 'l'], ['o', 'd', 'd']], [['s', 'e', 'e'], ['3', 'S', 'G', '.', 'P', 'S', 'T']]⟩, ⟨[['y']], [['D', 'E', 'F']]⟩, ⟨[['b', 'e', 'c', 'h', 'g', 'y', 'n']], [['b', 'o', 'y', '.', 'P', 'L']]⟩, ⟨[['d', 'd', 'r', 'a', 'i', 'g']], [['d', 'r', 'a', 'g', 'o', 'n']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "false"), ("condition", "lexical")] }

def ex_7c : Datum :=
  { id := "just2024_7c"
    source := ⟨"just-2024", "(7c)"⟩
    reportedIn := none
    language := "wels1247"
    primaryText := "Gwel-on y bechgyn ddraig"
    glossedTokens := [("Gwel-on", "see-3PL.PST"), ("y", "DEF"), ("bechgyn", "boy.PL"), ("ddraig", "dragon")]
    glossedWords := [⟨[['G', 'w', 'e', 'l'], ['o', 'n']], [['s', 'e', 'e'], ['3', 'P', 'L', '.', 'P', 'S', 'T']]⟩, ⟨[['y']], [['D', 'E', 'F']]⟩, ⟨[['b', 'e', 'c', 'h', 'g', 'y', 'n']], [['b', 'o', 'y', '.', 'P', 'L']]⟩, ⟨[['d', 'd', 'r', 'a', 'i', 'g']], [['d', 'r', 'a', 'g', 'o', 'n']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "true"), ("condition", "lexical")] }

def ex_8a : Datum :=
  { id := "just2024_8a"
    source := ⟨"just-2024", "(8a)"⟩
    reportedIn := none
    language := "koor1239"
    primaryText := "nun-i doro woon-d-uu-ns'i-ko"
    glossedTokens := [("nun-i", "we-NOM"), ("doro", "sheep"), ("woon-d-uu-ns'i-ko", "buy-PFV-PST-1PL-FOC")]
    glossedWords := [⟨[['n', 'u', 'n'], ['i']], [['w', 'e'], ['N', 'O', 'M']]⟩, ⟨[['d', 'o', 'r', 'o']], [['s', 'h', 'e', 'e', 'p']]⟩, ⟨[['w', 'o', 'o', 'n'], ['d'], ['u', 'u'], ['n', 's', '\'', 'i'], ['k', 'o']], [['b', 'u', 'y'], ['P', 'F', 'V'], ['P', 'S', 'T'], ['1', 'P', 'L'], ['F', 'O', 'C']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "true"), ("condition", "predicateFocus")] }

def ex_8b : Datum :=
  { id := "just2024_8b"
    source := ⟨"just-2024", "(8b)"⟩
    reportedIn := none
    language := "koor1239"
    primaryText := "nun-i doro-ko woon-d-o"
    glossedTokens := [("nun-i", "we-NOM"), ("doro-ko", "sheep-FOC"), ("woon-d-o", "buy-PFV-PST")]
    glossedWords := [⟨[['n', 'u', 'n'], ['i']], [['w', 'e'], ['N', 'O', 'M']]⟩, ⟨[['d', 'o', 'r', 'o'], ['k', 'o']], [['s', 'h', 'e', 'e', 'p'], ['F', 'O', 'C']]⟩, ⟨[['w', 'o', 'o', 'n'], ['d'], ['o']], [['b', 'u', 'y'], ['P', 'F', 'V'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "false"), ("condition", "otherFocus")] }

def ex_8c : Datum :=
  { id := "just2024_8c"
    source := ⟨"just-2024", "(8c)"⟩
    reportedIn := none
    language := "koor1239"
    primaryText := "tamba-ko doro woon-d-a"
    glossedTokens := [("tamba-ko", "me-FOC"), ("doro", "sheep"), ("woon-d-a", "buy-PFV-REL")]
    glossedWords := [⟨[['t', 'a', 'm', 'b', 'a'], ['k', 'o']], [['m', 'e'], ['F', 'O', 'C']]⟩, ⟨[['d', 'o', 'r', 'o']], [['s', 'h', 'e', 'e', 'p']]⟩, ⟨[['w', 'o', 'o', 'n'], ['d'], ['a']], [['b', 'u', 'y'], ['P', 'F', 'V'], ['R', 'E', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "false"), ("condition", "focus")] }

def ex_8d : Datum :=
  { id := "just2024_8d"
    source := ⟨"just-2024", "(8d)"⟩
    reportedIn := none
    language := "koor1239"
    primaryText := "nun-i doro-ko woon-d-uu-ns'i"
    glossedTokens := [("nun-i", "we-NOM"), ("doro-ko", "sheep-FOC"), ("woon-d-uu-ns'i", "buy-PFV-PST-1PL")]
    glossedWords := [⟨[['n', 'u', 'n'], ['i']], [['w', 'e'], ['N', 'O', 'M']]⟩, ⟨[['d', 'o', 'r', 'o'], ['k', 'o']], [['s', 'h', 'e', 'e', 'p'], ['F', 'O', 'C']]⟩, ⟨[['w', 'o', 'o', 'n'], ['d'], ['u', 'u'], ['n', 's', '\'', 'i']], [['b', 'u', 'y'], ['P', 'F', 'V'], ['P', 'S', 'T'], ['1', 'P', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "true"), ("condition", "otherFocus")] }

def ex_9a : Datum :=
  { id := "just2024_9a"
    source := ⟨"just-2024", "(9a)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "toofan-ha-ya peyapey dehkæde ra viran kærd"
    glossedTokens := [("toofan-ha-ya", "storm-PL-EZ"), ("peyapey", "constant"), ("dehkæde", "village"), ("ra", "ACC"), ("viran", "destroy"), ("kærd", "did.3SG")]
    glossedWords := [⟨[['t', 'o', 'o', 'f', 'a', 'n'], ['h', 'a'], ['y', 'a']], [['s', 't', 'o', 'r', 'm'], ['P', 'L'], ['E', 'Z']]⟩, ⟨[['p', 'e', 'y', 'a', 'p', 'e', 'y']], [['c', 'o', 'n', 's', 't', 'a', 'n', 't']]⟩, ⟨[['d', 'e', 'h', 'k', 'æ', 'd', 'e']], [['v', 'i', 'l', 'l', 'a', 'g', 'e']]⟩, ⟨[['r', 'a']], [['A', 'C', 'C']]⟩, ⟨[['v', 'i', 'r', 'a', 'n']], [['d', 'e', 's', 't', 'r', 'o', 'y']]⟩, ⟨[['k', 'æ', 'r', 'd']], [['d', 'i', 'd', '.', '3', 'S', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "false"), ("condition", "inanimate")] }

def ex_9b : Datum :=
  { id := "just2024_9b"
    source := ⟨"just-2024", "(9b)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "dozd-an-e gharætgar dehkæde ra viran kærd-ænd"
    glossedTokens := [("dozd-an-e", "thief-PL-EZ"), ("gharætgar", "marauder"), ("dehkæde", "village"), ("ra", "ACC"), ("viran", "destroy"), ("kærd-ænd", "did-3PL")]
    glossedWords := [⟨[['d', 'o', 'z', 'd'], ['a', 'n'], ['e']], [['t', 'h', 'i', 'e', 'f'], ['P', 'L'], ['E', 'Z']]⟩, ⟨[['g', 'h', 'a', 'r', 'æ', 't', 'g', 'a', 'r']], [['m', 'a', 'r', 'a', 'u', 'd', 'e', 'r']]⟩, ⟨[['d', 'e', 'h', 'k', 'æ', 'd', 'e']], [['v', 'i', 'l', 'l', 'a', 'g', 'e']]⟩, ⟨[['r', 'a']], [['A', 'C', 'C']]⟩, ⟨[['v', 'i', 'r', 'a', 'n']], [['d', 'e', 's', 't', 'r', 'o', 'y']]⟩, ⟨[['k', 'æ', 'r', 'd'], ['æ', 'n', 'd']], [['d', 'i', 'd'], ['3', 'P', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "true"), ("condition", "animate")] }

def ex_10a : Datum :=
  { id := "just2024_10a"
    source := ⟨"just-2024", "(10a)"⟩
    reportedIn := none
    language := "anua1242"
    primaryText := "kwʌ̌n ā-cám ɲìlàal(-lì)"
    glossedTokens := [("kwʌ̌n", "porridge"), ("ā-cám", "PST-eat"), ("ɲìlàal(-lì)", "child(-DEF)")]
    glossedWords := [⟨[['k', 'w', 'ʌ', '̌', 'n']], [['p', 'o', 'r', 'r', 'i', 'd', 'g', 'e']]⟩, ⟨[['ā'], ['c', 'á', 'm']], [['P', 'S', 'T'], ['e', 'a', 't']]⟩, ⟨[['ɲ', 'ì', 'l', 'à', 'a', 'l'], ['l', 'ì']], [['c', 'h', 'i', 'l', 'd', '('], ['D', 'E', 'F', ')']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "false")] }

def ex_10b : Datum :=
  { id := "just2024_10b"
    source := ⟨"just-2024", "(10b)"⟩
    reportedIn := none
    language := "anua1242"
    primaryText := "ɲìlàal kwʌ̌n ā-cám-ɛ̄"
    glossedTokens := [("ɲìlàal", "child"), ("kwʌ̌n", "porridge"), ("ā-cám-ɛ̄", "PST-eat-3SG.A")]
    glossedWords := [⟨[['ɲ', 'ì', 'l', 'à', 'a', 'l']], [['c', 'h', 'i', 'l', 'd']]⟩, ⟨[['k', 'w', 'ʌ', '̌', 'n']], [['p', 'o', 'r', 'r', 'i', 'd', 'g', 'e']]⟩, ⟨[['ā'], ['c', 'á', 'm'], ['ɛ', '̄']], [['P', 'S', 'T'], ['e', 'a', 't'], ['3', 'S', 'G', '.', 'A']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "true"), ("condition", "topical")] }

def ex_10c : Datum :=
  { id := "just2024_10c"
    source := ⟨"just-2024", "(10c)"⟩
    reportedIn := none
    language := "anua1242"
    primaryText := "ɲìlàal cám-á kwʌ̌n"
    glossedTokens := [("ɲìlàal", "child"), ("cám-á", "eat-FOC"), ("kwʌ̌n", "porridge")]
    glossedWords := [⟨[['ɲ', 'ì', 'l', 'à', 'a', 'l']], [['c', 'h', 'i', 'l', 'd']]⟩, ⟨[['c', 'á', 'm'], ['á']], [['e', 'a', 't'], ['F', 'O', 'C']]⟩, ⟨[['k', 'w', 'ʌ', '̌', 'n']], [['p', 'o', 'r', 'r', 'i', 'd', 'g', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "false"), ("condition", "otherFocus")] }

def ex_10d : Datum :=
  { id := "just2024_10d"
    source := ⟨"just-2024", "(10d)"⟩
    reportedIn := none
    language := "anua1242"
    primaryText := "kwʌ̌n cám-á ɲìlàal(-li)"
    glossedTokens := [("kwʌ̌n", "porridge"), ("cám-á", "eat-FOC"), ("ɲìlàal(-li)", "child(-DEF)")]
    glossedWords := [⟨[['k', 'w', 'ʌ', '̌', 'n']], [['p', 'o', 'r', 'r', 'i', 'd', 'g', 'e']]⟩, ⟨[['c', 'á', 'm'], ['á']], [['e', 'a', 't'], ['F', 'O', 'C']]⟩, ⟨[['ɲ', 'ì', 'l', 'à', 'a', 'l'], ['l', 'i']], [['c', 'h', 'i', 'l', 'd', '('], ['D', 'E', 'F', ')']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "false"), ("condition", "focus")] }

def ex_12a : Datum :=
  { id := "just2024_12a"
    source := ⟨"just-2024", "(12a)"⟩
    reportedIn := none
    language := "shek1245"
    primaryText := "gébèn bây dàdù nyààs=í-k"
    glossedTokens := [("gébèn", "Geben"), ("bây", "female"), ("dàdù", "child"), ("nyààs=í-k", "give.birth=3SG.F.A-REAL")]
    glossedWords := [⟨[['g', 'é', 'b', 'è', 'n']], [['G', 'e', 'b', 'e', 'n']]⟩, ⟨[['b', 'â', 'y']], [['f', 'e', 'm', 'a', 'l', 'e']]⟩, ⟨[['d', 'à', 'd', 'ù']], [['c', 'h', 'i', 'l', 'd']]⟩, ⟨[['n', 'y', 'à', 'à', 's'], ['í'], ['k']], [['g', 'i', 'v', 'e', '.', 'b', 'i', 'r', 't', 'h'], ['3', 'S', 'G', '.', 'F', '.', 'A'], ['R', 'E', 'A', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "true"), ("condition", "predicateFocus")] }

def ex_12b : Datum :=
  { id := "just2024_12b"
    source := ⟨"just-2024", "(12b)"⟩
    reportedIn := none
    language := "shek1245"
    primaryText := "m-bāyǹ nata gasku-k-ə"
    glossedTokens := [("m-bāyǹ", "1SG.POSS-wife"), ("nata", "1SG"), ("gasku-k-ə", "insult-REAL-IND")]
    glossedWords := [⟨[['m'], ['b', 'ā', 'y', 'ǹ']], [['1', 'S', 'G', '.', 'P', 'O', 'S', 'S'], ['w', 'i', 'f', 'e']]⟩, ⟨[['n', 'a', 't', 'a']], [['1', 'S', 'G']]⟩, ⟨[['g', 'a', 's', 'k', 'u'], ['k'], ['ə']], [['i', 'n', 's', 'u', 'l', 't'], ['R', 'E', 'A', 'L'], ['I', 'N', 'D']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "false"), ("condition", "focus")] }

def ex_13a_A : Datum :=
  { id := "just2024_13a_A"
    source := ⟨"just-2024", "(13a)"⟩
    reportedIn := none
    language := "maka1311"
    primaryText := "Na=cini'=i tedong-ku i Ali"
    glossedTokens := [("Na=cini'=i", "3SG.A=see=3SG.P"), ("tedong-ku", "buffalo-1SG.POSS"), ("i", "PERS"), ("Ali", "Ali")]
    glossedWords := [⟨[['N', 'a'], ['c', 'i', 'n', 'i', '\''], ['i']], [['3', 'S', 'G', '.', 'A'], ['s', 'e', 'e'], ['3', 'S', 'G', '.', 'P']]⟩, ⟨[['t', 'e', 'd', 'o', 'n', 'g'], ['k', 'u']], [['b', 'u', 'f', 'f', 'a', 'l', 'o'], ['1', 'S', 'G', '.', 'P', 'O', 'S', 'S']]⟩, ⟨[['i']], [['P', 'E', 'R', 'S']]⟩, ⟨[['A', 'l', 'i']], [['A', 'l', 'i']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "true"), ("condition", "topical")] }

def ex_13a_P : Datum :=
  { id := "just2024_13a_P"
    source := ⟨"just-2024", "(13a)"⟩
    reportedIn := none
    language := "maka1311"
    primaryText := "Na=cini'=i tedong-ku i Ali"
    glossedTokens := [("Na=cini'=i", "3SG.A=see=3SG.P"), ("tedong-ku", "buffalo-1SG.POSS"), ("i", "PERS"), ("Ali", "Ali")]
    glossedWords := [⟨[['N', 'a'], ['c', 'i', 'n', 'i', '\''], ['i']], [['3', 'S', 'G', '.', 'A'], ['s', 'e', 'e'], ['3', 'S', 'G', '.', 'P']]⟩, ⟨[['t', 'e', 'd', 'o', 'n', 'g'], ['k', 'u']], [['b', 'u', 'f', 'f', 'a', 'l', 'o'], ['1', 'S', 'G', '.', 'P', 'O', 'S', 'S']]⟩, ⟨[['i']], [['P', 'E', 'R', 'S']]⟩, ⟨[['A', 'l', 'i']], [['A', 'l', 'i']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "P"), ("indexed", "true"), ("condition", "definite")] }

def ex_13b_A : Datum :=
  { id := "just2024_13b_A"
    source := ⟨"just-2024", "(13b)"⟩
    reportedIn := none
    language := "maka1311"
    primaryText := "kongkong=a a-buno=i miong=a"
    glossedTokens := [("kongkong=a", "dog=DEF"), ("a-buno=i", "AF-kill=3SG.P"), ("miong=a", "cat=DEF")]
    glossedWords := [⟨[['k', 'o', 'n', 'g', 'k', 'o', 'n', 'g'], ['a']], [['d', 'o', 'g'], ['D', 'E', 'F']]⟩, ⟨[['a'], ['b', 'u', 'n', 'o'], ['i']], [['A', 'F'], ['k', 'i', 'l', 'l'], ['3', 'S', 'G', '.', 'P']]⟩, ⟨[['m', 'i', 'o', 'n', 'g'], ['a']], [['c', 'a', 't'], ['D', 'E', 'F']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "false"), ("condition", "focus")] }

def ex_13b_P : Datum :=
  { id := "just2024_13b_P"
    source := ⟨"just-2024", "(13b)"⟩
    reportedIn := none
    language := "maka1311"
    primaryText := "kongkong=a a-buno=i miong=a"
    glossedTokens := [("kongkong=a", "dog=DEF"), ("a-buno=i", "AF-kill=3SG.P"), ("miong=a", "cat=DEF")]
    glossedWords := [⟨[['k', 'o', 'n', 'g', 'k', 'o', 'n', 'g'], ['a']], [['d', 'o', 'g'], ['D', 'E', 'F']]⟩, ⟨[['a'], ['b', 'u', 'n', 'o'], ['i']], [['A', 'F'], ['k', 'i', 'l', 'l'], ['3', 'S', 'G', '.', 'P']]⟩, ⟨[['m', 'i', 'o', 'n', 'g'], ['a']], [['c', 'a', 't'], ['D', 'E', 'F']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "P"), ("indexed", "true"), ("condition", "definite")] }

def ex_13c_P : Datum :=
  { id := "just2024_13c_P"
    source := ⟨"just-2024", "(13c)"⟩
    reportedIn := none
    language := "maka1311"
    primaryText := "miong=a na=buno kongkong=a"
    glossedTokens := [("miong=a", "cat=DEF"), ("na=buno", "3SG.A=kill"), ("kongkong=a", "dog=DEF")]
    glossedWords := [⟨[['m', 'i', 'o', 'n', 'g'], ['a']], [['c', 'a', 't'], ['D', 'E', 'F']]⟩, ⟨[['n', 'a'], ['b', 'u', 'n', 'o']], [['3', 'S', 'G', '.', 'A'], ['k', 'i', 'l', 'l']]⟩, ⟨[['k', 'o', 'n', 'g', 'k', 'o', 'n', 'g'], ['a']], [['d', 'o', 'g'], ['D', 'E', 'F']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "P"), ("indexed", "false"), ("condition", "focus")] }

def ex_13c_A : Datum :=
  { id := "just2024_13c_A"
    source := ⟨"just-2024", "(13c)"⟩
    reportedIn := none
    language := "maka1311"
    primaryText := "miong=a na=buno kongkong=a"
    glossedTokens := [("miong=a", "cat=DEF"), ("na=buno", "3SG.A=kill"), ("kongkong=a", "dog=DEF")]
    glossedWords := [⟨[['m', 'i', 'o', 'n', 'g'], ['a']], [['c', 'a', 't'], ['D', 'E', 'F']]⟩, ⟨[['n', 'a'], ['b', 'u', 'n', 'o']], [['3', 'S', 'G', '.', 'A'], ['k', 'i', 'l', 'l']]⟩, ⟨[['k', 'o', 'n', 'g', 'k', 'o', 'n', 'g'], ['a']], [['d', 'o', 'g'], ['D', 'E', 'F']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "true"), ("condition", "topical")] }

def t1_a1_p2 : Datum :=
  { id := "just2024_t1_a1_p2"
    source := ⟨"just-2024", "Table 1"⟩
    reportedIn := none
    language := "reye1240"
    primaryText := "A 1 with P 2"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aPerson", "1"), ("pPerson", "2"), ("indexed", "P")] }

def t1_a1_p3 : Datum :=
  { id := "just2024_t1_a1_p3"
    source := ⟨"just-2024", "Table 1"⟩
    reportedIn := none
    language := "reye1240"
    primaryText := "A 1 with P 3"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aPerson", "1"), ("pPerson", "3"), ("indexed", "A")] }

def t1_a2_p1 : Datum :=
  { id := "just2024_t1_a2_p1"
    source := ⟨"just-2024", "Table 1"⟩
    reportedIn := none
    language := "reye1240"
    primaryText := "A 2 with P 1"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aPerson", "2"), ("pPerson", "1"), ("indexed", "A")] }

def t1_a2_p3 : Datum :=
  { id := "just2024_t1_a2_p3"
    source := ⟨"just-2024", "Table 1"⟩
    reportedIn := none
    language := "reye1240"
    primaryText := "A 2 with P 3"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aPerson", "2"), ("pPerson", "3"), ("indexed", "A")] }

def t1_a3_p1 : Datum :=
  { id := "just2024_t1_a3_p1"
    source := ⟨"just-2024", "Table 1"⟩
    reportedIn := none
    language := "reye1240"
    primaryText := "A 3 with P 1"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aPerson", "3"), ("pPerson", "1"), ("indexed", "AP")] }

def t1_a3_p2 : Datum :=
  { id := "just2024_t1_a3_p2"
    source := ⟨"just-2024", "Table 1"⟩
    reportedIn := none
    language := "reye1240"
    primaryText := "A 3 with P 2"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aPerson", "3"), ("pPerson", "2"), ("indexed", "AP")] }

def t1_a3_p3 : Datum :=
  { id := "just2024_t1_a3_p3"
    source := ⟨"just-2024", "Table 1"⟩
    reportedIn := none
    language := "reye1240"
    primaryText := "A 3 with P 3"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aPerson", "3"), ("pPerson", "3"), ("indexed", "A")] }

def all : List Datum := [ex_2a, ex_2b, ex_3, ex_4a, ex_4b, ex_4c, ex_5a, ex_5b, ex_6a, ex_6b, ex_6c, ex_7a, ex_7b, ex_7c, ex_8a, ex_8b, ex_8c, ex_8d, ex_9a, ex_9b, ex_10a, ex_10b, ex_10c, ex_10d, ex_12a, ex_12b, ex_13a_A, ex_13a_P, ex_13b_A, ex_13b_P, ex_13c_P, ex_13c_A, t1_a1_p2, t1_a1_p3, t1_a2_p1, t1_a2_p3, t1_a3_p1, t1_a3_p2, t1_a3_p3]

end Just2024.Examples
