module

public import Linglib.Data.Examples.Schema

/-!
# `AssmannEtAl2023` — typed example data

Auto-generated from `Linglib/Data/Examples/AssmannEtAl2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AssmannEtAl2023.Examples`.
-/

@[expose] public section

namespace AssmannEtAl2023.Examples

def ex_1 : Datum :=
  { id := "assmannetal2023_1"
    source := ⟨"assmann-etal-2023", "(1)"⟩
    reportedIn := none
    method := some .description
    language := "guru1271"
    primaryText := "Á fúrmáyò bà wúm kwálíngálá."
    glossedTokens := [("Á", "FOC"), ("fúrmáyò", "Fulani"), ("bà", "PROG"), ("wúm", "chew"), ("kwálíngálá", "colanut")]
    glossedWords := [⟨['Á'], ['F', 'O', 'C'], [⟨['Á'], ['F', 'O', 'C'], none⟩]⟩, ⟨['f', 'ú', 'r', 'm', 'á', 'y', 'ò'], ['F', 'u', 'l', 'a', 'n', 'i'], [⟨['f', 'ú', 'r', 'm', 'á', 'y', 'ò'], ['F', 'u', 'l', 'a', 'n', 'i'], none⟩]⟩, ⟨['b', 'à'], ['P', 'R', 'O', 'G'], [⟨['b', 'à'], ['P', 'R', 'O', 'G'], none⟩]⟩, ⟨['w', 'ú', 'm'], ['c', 'h', 'e', 'w'], [⟨['w', 'ú', 'm'], ['c', 'h', 'e', 'w'], none⟩]⟩, ⟨['k', 'w', 'á', 'l', 'í', 'n', 'g', 'á', 'l', 'á'], ['c', 'o', 'l', 'a', 'n', 'u', 't'], [⟨['k', 'w', 'á', 'l', 'í', 'n', 'g', 'á', 'l', 'á'], ['c', 'o', 'l', 'a', 'n', 'u', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Who is chewing colanut?"
    judgment := .acceptable
    contrasts := []
    readings := [("subject", .acceptable)]
    paperFeatures := [("marking", "a before subject")] }

def ex_2 : Datum :=
  { id := "assmannetal2023_2"
    source := ⟨"assmann-etal-2023", "(2)"⟩
    reportedIn := none
    method := some .description
    language := "guru1271"
    primaryText := "Tí bà ròmb-á gʷéì."
    glossedTokens := [("Tí", "3SG"), ("bà", "PROG"), ("ròmb-á", "gather-FOC"), ("gʷéì", "seeds")]
    glossedWords := [⟨['T', 'í'], ['3', 'S', 'G'], [⟨['T', 'í'], ['3', 'S', 'G'], none⟩]⟩, ⟨['b', 'à'], ['P', 'R', 'O', 'G'], [⟨['b', 'à'], ['P', 'R', 'O', 'G'], none⟩]⟩, ⟨['r', 'ò', 'm', 'b', '-', 'á'], ['g', 'a', 't', 'h', 'e', 'r', '-', 'F', 'O', 'C'], [⟨['r', 'ò', 'm', 'b'], ['g', 'a', 't', 'h', 'e', 'r'], none⟩, ⟨['á'], ['F', 'O', 'C'], some '-'⟩]⟩, ⟨['g', 'ʷ', 'é', 'ì'], ['s', 'e', 'e', 'd', 's'], [⟨['g', 'ʷ', 'é', 'ì'], ['s', 'e', 'e', 'd', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("object", .acceptable), ("verb", .acceptable), ("VP", .acceptable)]
    paperFeatures := [("marking", "a between verb and object")] }

def ex_3 : Datum :=
  { id := "assmannetal2023_3"
    source := ⟨"assmann-etal-2023", "(3)"⟩
    reportedIn := none
    method := some .description
    language := "guru1271"
    primaryText := "Kóo vùr mɘ́ kãa Mài Dáwà sái tí shí gànyáhú-à."
    glossedTokens := [("Kóo", "every"), ("vùr", "when"), ("mɘ́", ""), ("kãa", ""), ("Mài Dáwà", "Mai Dawa"), ("sái", "then"), ("tí", "3SG"), ("shí", "eat"), ("gànyáhú-à", "rice-FOC")]
    glossedWords := [⟨['K', 'ó', 'o'], ['e', 'v', 'e', 'r', 'y'], [⟨['K', 'ó', 'o'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['v', 'ù', 'r'], ['w', 'h', 'e', 'n'], [⟨['v', 'ù', 'r'], ['w', 'h', 'e', 'n'], none⟩]⟩, ⟨['m', 'ɘ', '́'], [], []⟩, ⟨['k', 'ã', 'a'], [], []⟩, ⟨['M', 'à', 'i', ' ', 'D', 'á', 'w', 'à'], ['M', 'a', 'i', ' ', 'D', 'a', 'w', 'a'], [⟨['M', 'à', 'i', ' ', 'D', 'á', 'w', 'à'], ['M', 'a', 'i', ' ', 'D', 'a', 'w', 'a'], none⟩]⟩, ⟨['s', 'á', 'i'], ['t', 'h', 'e', 'n'], [⟨['s', 'á', 'i'], ['t', 'h', 'e', 'n'], none⟩]⟩, ⟨['t', 'í'], ['3', 'S', 'G'], [⟨['t', 'í'], ['3', 'S', 'G'], none⟩]⟩, ⟨['s', 'h', 'í'], ['e', 'a', 't'], [⟨['s', 'h', 'í'], ['e', 'a', 't'], none⟩]⟩, ⟨['g', 'à', 'n', 'y', 'á', 'h', 'ú', '-', 'à'], ['r', 'i', 'c', 'e', '-', 'F', 'O', 'C'], [⟨['g', 'à', 'n', 'y', 'á', 'h', 'ú'], ['r', 'i', 'c', 'e'], none⟩, ⟨['à'], ['F', 'O', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "discourse-initial"
    judgment := .acceptable
    contrasts := []
    readings := [("clause", .acceptable)]
    paperFeatures := [("marking", "a clause-final")] }

def ex_5 : Datum :=
  { id := "assmannetal2023_5"
    source := ⟨"assmann-etal-2023", "(5)"⟩
    reportedIn := none
    method := some .description
    language := "guru1271"
    primaryText := "Tí vún lúurìn nvùrì-à."
    glossedTokens := [("Tí", "3SG"), ("vún", "wash"), ("lúurìn", "clothes"), ("nvùrì-à", "yesterday-FOC")]
    glossedWords := [⟨['T', 'í'], ['3', 'S', 'G'], [⟨['T', 'í'], ['3', 'S', 'G'], none⟩]⟩, ⟨['v', 'ú', 'n'], ['w', 'a', 's', 'h'], [⟨['v', 'ú', 'n'], ['w', 'a', 's', 'h'], none⟩]⟩, ⟨['l', 'ú', 'u', 'r', 'ì', 'n'], ['c', 'l', 'o', 't', 'h', 'e', 's'], [⟨['l', 'ú', 'u', 'r', 'ì', 'n'], ['c', 'l', 'o', 't', 'h', 'e', 's'], none⟩]⟩, ⟨['n', 'v', 'ù', 'r', 'ì', '-', 'à'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y', '-', 'F', 'O', 'C'], [⟨['n', 'v', 'ù', 'r', 'ì'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩, ⟨['à'], ['F', 'O', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("clause", .acceptable)]
    paperFeatures := [("marking", "a clause-final")] }

def fn4_i : Datum :=
  { id := "assmannetal2023_fn4_i"
    source := ⟨"assmann-etal-2023", "fn. 4 (i)"⟩
    reportedIn := none
    method := some .description
    language := "guru1271"
    primaryText := "Tí bà wúr má-ì à báa-sì."
    glossedTokens := [("Tí", "3SG"), ("bà", "PROG"), ("wúr", "bring"), ("má-ì", "water-DEF"), ("à", "FOC"), ("báa-sì", "father-his")]
    glossedWords := [⟨['T', 'í'], ['3', 'S', 'G'], [⟨['T', 'í'], ['3', 'S', 'G'], none⟩]⟩, ⟨['b', 'à'], ['P', 'R', 'O', 'G'], [⟨['b', 'à'], ['P', 'R', 'O', 'G'], none⟩]⟩, ⟨['w', 'ú', 'r'], ['b', 'r', 'i', 'n', 'g'], [⟨['w', 'ú', 'r'], ['b', 'r', 'i', 'n', 'g'], none⟩]⟩, ⟨['m', 'á', '-', 'ì'], ['w', 'a', 't', 'e', 'r', '-', 'D', 'E', 'F'], [⟨['m', 'á'], ['w', 'a', 't', 'e', 'r'], none⟩, ⟨['ì'], ['D', 'E', 'F'], some '-'⟩]⟩, ⟨['à'], ['F', 'O', 'C'], [⟨['à'], ['F', 'O', 'C'], none⟩]⟩, ⟨['b', 'á', 'a', '-', 's', 'ì'], ['f', 'a', 't', 'h', 'e', 'r', '-', 'h', 'i', 's'], [⟨['b', 'á', 'a'], ['f', 'a', 't', 'h', 'e', 'r'], none⟩, ⟨['s', 'ì'], ['h', 'i', 's'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("phrase within VP", .acceptable)]
    paperFeatures := [("marking", "a before phrase within VP")] }

def ex_6a : Datum :=
  { id := "assmannetal2023_6a"
    source := ⟨"assmann-etal-2023", "(6a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "buli1254"
    primaryText := "(ká) Àtìm alè dè mángó."
    glossedTokens := [("(ká)", "FOC"), ("Àtìm", "Atim"), ("alè", "FOC"), ("dè", "ate"), ("mángó", "mango")]
    glossedWords := [⟨['(', 'k', 'á', ')'], ['F', 'O', 'C'], [⟨['k', 'á'], ['F', 'O', 'C'], none⟩]⟩, ⟨['À', 't', 'ì', 'm'], ['A', 't', 'i', 'm'], [⟨['À', 't', 'ì', 'm'], ['A', 't', 'i', 'm'], none⟩]⟩, ⟨['a', 'l', 'è'], ['F', 'O', 'C'], [⟨['a', 'l', 'è'], ['F', 'O', 'C'], none⟩]⟩, ⟨['d', 'è'], ['a', 't', 'e'], [⟨['d', 'è'], ['a', 't', 'e'], none⟩]⟩, ⟨['m', 'á', 'n', 'g', 'ó'], ['m', 'a', 'n', 'g', 'o'], [⟨['m', 'á', 'n', 'g', 'ó'], ['m', 'a', 'n', 'g', 'o'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Who ate a mango?"
    judgment := .acceptable
    contrasts := []
    readings := [("subject", .acceptable)]
    paperFeatures := [("marking", "le after subject")] }

def ex_6b : Datum :=
  { id := "assmannetal2023_6b"
    source := ⟨"assmann-etal-2023", "(6b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "buli1254"
    primaryText := "(ká) Àtìm alè dè n mangó."
    glossedTokens := [("(ká)", "FOC"), ("Àtìm", "Atim"), ("alè", "FOC"), ("dè", "ate"), ("n", "1SG.POSS"), ("mangó", "mango")]
    glossedWords := [⟨['(', 'k', 'á', ')'], ['F', 'O', 'C'], [⟨['k', 'á'], ['F', 'O', 'C'], none⟩]⟩, ⟨['À', 't', 'ì', 'm'], ['A', 't', 'i', 'm'], [⟨['À', 't', 'ì', 'm'], ['A', 't', 'i', 'm'], none⟩]⟩, ⟨['a', 'l', 'è'], ['F', 'O', 'C'], [⟨['a', 'l', 'è'], ['F', 'O', 'C'], none⟩]⟩, ⟨['d', 'è'], ['a', 't', 'e'], [⟨['d', 'è'], ['a', 't', 'e'], none⟩]⟩, ⟨['n'], ['1', 'S', 'G', '.', 'P', 'O', 'S', 'S'], [⟨['n'], ['1', 'S', 'G', '.', 'P', 'O', 'S', 'S'], none⟩]⟩, ⟨['m', 'a', 'n', 'g', 'ó'], ['m', 'a', 'n', 'g', 'o'], [⟨['m', 'a', 'n', 'g', 'ó'], ['m', 'a', 'n', 'g', 'o'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Why are you angry?"
    judgment := .acceptable
    contrasts := []
    readings := [("clause", .acceptable)]
    paperFeatures := [("marking", "le after subject")] }

def ex_7 : Datum :=
  { id := "assmannetal2023_7"
    source := ⟨"assmann-etal-2023", "(7)"⟩
    reportedIn := none
    method := some .elicitation
    language := "buli1254"
    primaryText := "wá dè ká mángó."
    glossedTokens := [("wá", "3SG"), ("dè", "ate"), ("ká", "FOC"), ("mángó", "mango")]
    glossedWords := [⟨['w', 'á'], ['3', 'S', 'G'], [⟨['w', 'á'], ['3', 'S', 'G'], none⟩]⟩, ⟨['d', 'è'], ['a', 't', 'e'], [⟨['d', 'è'], ['a', 't', 'e'], none⟩]⟩, ⟨['k', 'á'], ['F', 'O', 'C'], [⟨['k', 'á'], ['F', 'O', 'C'], none⟩]⟩, ⟨['m', 'á', 'n', 'g', 'ó'], ['m', 'a', 'n', 'g', 'o'], [⟨['m', 'á', 'n', 'g', 'ó'], ['m', 'a', 'n', 'g', 'o'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "What did Atim do? / What did Atim eat?"
    judgment := .acceptable
    contrasts := []
    readings := [("VP", .acceptable), ("object", .acceptable)]
    paperFeatures := [("marking", "ka before object")] }

def ex_8 : Datum :=
  { id := "assmannetal2023_8"
    source := ⟨"assmann-etal-2023", "(8)"⟩
    reportedIn := none
    method := some .elicitation
    language := "buli1254"
    primaryText := "Aáya, Atim a lɛ Amoak kámā."
    glossedTokens := [("Aáya", "no"), ("Atim", "Atim"), ("a", "IPFV"), ("lɛ", "insult"), ("Amoak", "Amoak"), ("kámā", "FOC")]
    glossedWords := [⟨['A', 'á', 'y', 'a'], ['n', 'o'], [⟨['A', 'á', 'y', 'a'], ['n', 'o'], none⟩]⟩, ⟨['A', 't', 'i', 'm'], ['A', 't', 'i', 'm'], [⟨['A', 't', 'i', 'm'], ['A', 't', 'i', 'm'], none⟩]⟩, ⟨['a'], ['I', 'P', 'F', 'V'], [⟨['a'], ['I', 'P', 'F', 'V'], none⟩]⟩, ⟨['l', 'ɛ'], ['i', 'n', 's', 'u', 'l', 't'], [⟨['l', 'ɛ'], ['i', 'n', 's', 'u', 'l', 't'], none⟩]⟩, ⟨['A', 'm', 'o', 'a', 'k'], ['A', 'm', 'o', 'a', 'k'], [⟨['A', 'm', 'o', 'a', 'k'], ['A', 'm', 'o', 'a', 'k'], none⟩]⟩, ⟨['k', 'á', 'm', 'ā'], ['F', 'O', 'C'], [⟨['k', 'á', 'm', 'ā'], ['F', 'O', 'C'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Atim hit Amoak."
    judgment := .acceptable
    contrasts := []
    readings := [("verb", .acceptable)]
    paperFeatures := [("marking", "kama after VP")] }

def ex_10 : Datum :=
  { id := "assmannetal2023_10"
    source := ⟨"assmann-etal-2023", "(10)"⟩
    reportedIn := none
    method := some .description
    language := "haus1257"
    primaryText := "Kandè ta-kèe dafà kiifii."
    glossedTokens := [("Kandè", "Kande"), ("ta-kèe", "3SG.F-REL.IPFV"), ("dafà", "cooking"), ("kiifii", "fish")]
    glossedWords := [⟨['K', 'a', 'n', 'd', 'è'], ['K', 'a', 'n', 'd', 'e'], [⟨['K', 'a', 'n', 'd', 'è'], ['K', 'a', 'n', 'd', 'e'], none⟩]⟩, ⟨['t', 'a', '-', 'k', 'è', 'e'], ['3', 'S', 'G', '.', 'F', '-', 'R', 'E', 'L', '.', 'I', 'P', 'F', 'V'], [⟨['t', 'a'], ['3', 'S', 'G', '.', 'F'], none⟩, ⟨['k', 'è', 'e'], ['R', 'E', 'L', '.', 'I', 'P', 'F', 'V'], some '-'⟩]⟩, ⟨['d', 'a', 'f', 'à'], ['c', 'o', 'o', 'k', 'i', 'n', 'g'], [⟨['d', 'a', 'f', 'à'], ['c', 'o', 'o', 'k', 'i', 'n', 'g'], none⟩]⟩, ⟨['k', 'i', 'i', 'f', 'i', 'i'], ['f', 'i', 's', 'h'], [⟨['k', 'i', 'i', 'f', 'i', 'i'], ['f', 'i', 's', 'h'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("subject", .acceptable)]
    paperFeatures := [("marking", "relative form")] }

def ex_11 : Datum :=
  { id := "assmannetal2023_11"
    source := ⟨"assmann-etal-2023", "(11)"⟩
    reportedIn := none
    method := some .elicitation
    language := "haus1257"
    primaryText := "Kànde ta-nàa dafà kiifii."
    glossedTokens := [("Kànde", "Kande"), ("ta-nàa", "3SG.F-IPFV"), ("dafà", "cook"), ("kiifii", "fish")]
    glossedWords := [⟨['K', 'à', 'n', 'd', 'e'], ['K', 'a', 'n', 'd', 'e'], [⟨['K', 'à', 'n', 'd', 'e'], ['K', 'a', 'n', 'd', 'e'], none⟩]⟩, ⟨['t', 'a', '-', 'n', 'à', 'a'], ['3', 'S', 'G', '.', 'F', '-', 'I', 'P', 'F', 'V'], [⟨['t', 'a'], ['3', 'S', 'G', '.', 'F'], none⟩, ⟨['n', 'à', 'a'], ['I', 'P', 'F', 'V'], some '-'⟩]⟩, ⟨['d', 'a', 'f', 'à'], ['c', 'o', 'o', 'k'], [⟨['d', 'a', 'f', 'à'], ['c', 'o', 'o', 'k'], none⟩]⟩, ⟨['k', 'i', 'i', 'f', 'i', 'i'], ['f', 'i', 's', 'h'], [⟨['k', 'i', 'i', 'f', 'i', 'i'], ['f', 'i', 's', 'h'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "What is Kande cooking? / What is Kande doing with the fish? / What is Kande doing? / What is happening?"
    judgment := .acceptable
    contrasts := []
    readings := [("object", .acceptable), ("verb", .acceptable), ("VP", .acceptable), ("clause", .acceptable)]
    paperFeatures := [("marking", "absolute form")] }

def ex_12 : Datum :=
  { id := "assmannetal2023_12"
    source := ⟨"assmann-etal-2023", "(12)"⟩
    reportedIn := none
    method := some .description
    language := "haus1257"
    primaryText := "Kandè (cee) ta-kèe dafà kiifii."
    glossedTokens := [("Kandè", "Kande"), ("(cee)", "FOC"), ("ta-kèe", "3SG.F-REL.IPFV"), ("dafà", "cooking"), ("kiifii", "fish")]
    glossedWords := [⟨['K', 'a', 'n', 'd', 'è'], ['K', 'a', 'n', 'd', 'e'], [⟨['K', 'a', 'n', 'd', 'è'], ['K', 'a', 'n', 'd', 'e'], none⟩]⟩, ⟨['(', 'c', 'e', 'e', ')'], ['F', 'O', 'C'], [⟨['c', 'e', 'e'], ['F', 'O', 'C'], none⟩]⟩, ⟨['t', 'a', '-', 'k', 'è', 'e'], ['3', 'S', 'G', '.', 'F', '-', 'R', 'E', 'L', '.', 'I', 'P', 'F', 'V'], [⟨['t', 'a'], ['3', 'S', 'G', '.', 'F'], none⟩, ⟨['k', 'è', 'e'], ['R', 'E', 'L', '.', 'I', 'P', 'F', 'V'], some '-'⟩]⟩, ⟨['d', 'a', 'f', 'à'], ['c', 'o', 'o', 'k', 'i', 'n', 'g'], [⟨['d', 'a', 'f', 'à'], ['c', 'o', 'o', 'k', 'i', 'n', 'g'], none⟩]⟩, ⟨['k', 'i', 'i', 'f', 'i', 'i'], ['f', 'i', 's', 'h'], [⟨['k', 'i', 'i', 'f', 'i', 'i'], ['f', 'i', 's', 'h'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("subject", .acceptable)]
    paperFeatures := [("marking", "relative form"), ("particle", "cee after subject")] }

def ex_13 : Datum :=
  { id := "assmannetal2023_13"
    source := ⟨"assmann-etal-2023", "(13)"⟩
    reportedIn := none
    method := some .elicitation
    language := "haus1257"
    primaryText := "Kànde ta-nàa dafà kiifii (nèe)."
    glossedTokens := [("Kànde", "Kande"), ("ta-nàa", "3SG.F-IPFV"), ("dafà", "cook"), ("kiifii", "fish"), ("(nèe)", "FOC")]
    glossedWords := [⟨['K', 'à', 'n', 'd', 'e'], ['K', 'a', 'n', 'd', 'e'], [⟨['K', 'à', 'n', 'd', 'e'], ['K', 'a', 'n', 'd', 'e'], none⟩]⟩, ⟨['t', 'a', '-', 'n', 'à', 'a'], ['3', 'S', 'G', '.', 'F', '-', 'I', 'P', 'F', 'V'], [⟨['t', 'a'], ['3', 'S', 'G', '.', 'F'], none⟩, ⟨['n', 'à', 'a'], ['I', 'P', 'F', 'V'], some '-'⟩]⟩, ⟨['d', 'a', 'f', 'à'], ['c', 'o', 'o', 'k'], [⟨['d', 'a', 'f', 'à'], ['c', 'o', 'o', 'k'], none⟩]⟩, ⟨['k', 'i', 'i', 'f', 'i', 'i'], ['f', 'i', 's', 'h'], [⟨['k', 'i', 'i', 'f', 'i', 'i'], ['f', 'i', 's', 'h'], none⟩]⟩, ⟨['(', 'n', 'è', 'e', ')'], ['F', 'O', 'C'], [⟨['n', 'è', 'e'], ['F', 'O', 'C'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "What is Kande cooking? / What is Kande doing with the fish? / What is Kande doing? / What is happening?"
    judgment := .acceptable
    contrasts := []
    readings := [("object", .acceptable), ("verb", .acceptable), ("VP", .acceptable), ("clause", .acceptable)]
    paperFeatures := [("marking", "absolute form"), ("particle", "nee clause-final")] }

def ex_14 : Datum :=
  { id := "assmannetal2023_14"
    source := ⟨"assmann-etal-2023", "(14)"⟩
    reportedIn := none
    method := some .elicitation
    language := "haus1257"
    primaryText := "Kànde ta-nàa dafà àyàbà nee."
    glossedTokens := [("Kànde", "K."), ("ta-nàa", "3SG.F-IPFV"), ("dafà", "cook"), ("àyàbà", "banana"), ("nee", "FOC")]
    glossedWords := [⟨['K', 'à', 'n', 'd', 'e'], ['K', '.'], [⟨['K', 'à', 'n', 'd', 'e'], ['K', '.'], none⟩]⟩, ⟨['t', 'a', '-', 'n', 'à', 'a'], ['3', 'S', 'G', '.', 'F', '-', 'I', 'P', 'F', 'V'], [⟨['t', 'a'], ['3', 'S', 'G', '.', 'F'], none⟩, ⟨['n', 'à', 'a'], ['I', 'P', 'F', 'V'], some '-'⟩]⟩, ⟨['d', 'a', 'f', 'à'], ['c', 'o', 'o', 'k'], [⟨['d', 'a', 'f', 'à'], ['c', 'o', 'o', 'k'], none⟩]⟩, ⟨['à', 'y', 'à', 'b', 'à'], ['b', 'a', 'n', 'a', 'n', 'a'], [⟨['à', 'y', 'à', 'b', 'à'], ['b', 'a', 'n', 'a', 'n', 'a'], none⟩]⟩, ⟨['n', 'e', 'e'], ['F', 'O', 'C'], [⟨['n', 'e', 'e'], ['F', 'O', 'C'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "What is Kande cooking?"
    judgment := .acceptable
    contrasts := [("Kànde ta-nàa dafà àyàbà cee.", .ungrammatical)]
    readings := [("object", .acceptable)]
    paperFeatures := [("marking", "absolute form"), ("particle", "nee clause-final"), ("agreement", "masculine despite feminine object")] }

def ex_15 : Datum :=
  { id := "assmannetal2023_15"
    source := ⟨"assmann-etal-2023", "(15)"⟩
    reportedIn := none
    method := some .elicitation
    language := "haus1257"
    primaryText := "A'a, farii-n dookìi na nèe ya halbi yaarò na."
    glossedTokens := [("A'a", "no"), ("farii-n", "white-LINK"), ("dookìi", "horse"), ("na", "DEF.PROX"), ("nèe", "FOC"), ("ya", "3SG.M-PFV.REL"), ("halbi", "kick"), ("yaarò", "child"), ("na", "DEF.PROX")]
    glossedWords := [⟨['A', '\'', 'a'], ['n', 'o'], [⟨['A', '\'', 'a'], ['n', 'o'], none⟩]⟩, ⟨['f', 'a', 'r', 'i', 'i', '-', 'n'], ['w', 'h', 'i', 't', 'e', '-', 'L', 'I', 'N', 'K'], [⟨['f', 'a', 'r', 'i', 'i'], ['w', 'h', 'i', 't', 'e'], none⟩, ⟨['n'], ['L', 'I', 'N', 'K'], some '-'⟩]⟩, ⟨['d', 'o', 'o', 'k', 'ì', 'i'], ['h', 'o', 'r', 's', 'e'], [⟨['d', 'o', 'o', 'k', 'ì', 'i'], ['h', 'o', 'r', 's', 'e'], none⟩]⟩, ⟨['n', 'a'], ['D', 'E', 'F', '.', 'P', 'R', 'O', 'X'], [⟨['n', 'a'], ['D', 'E', 'F', '.', 'P', 'R', 'O', 'X'], none⟩]⟩, ⟨['n', 'è', 'e'], ['F', 'O', 'C'], [⟨['n', 'è', 'e'], ['F', 'O', 'C'], none⟩]⟩, ⟨['y', 'a'], ['3', 'S', 'G', '.', 'M', '-', 'P', 'F', 'V', '.', 'R', 'E', 'L'], []⟩, ⟨['h', 'a', 'l', 'b', 'i'], ['k', 'i', 'c', 'k'], [⟨['h', 'a', 'l', 'b', 'i'], ['k', 'i', 'c', 'k'], none⟩]⟩, ⟨['y', 'a', 'a', 'r', 'ò'], ['c', 'h', 'i', 'l', 'd'], [⟨['y', 'a', 'a', 'r', 'ò'], ['c', 'h', 'i', 'l', 'd'], none⟩]⟩, ⟨['n', 'a'], ['D', 'E', 'F', '.', 'P', 'R', 'O', 'X'], [⟨['n', 'a'], ['D', 'E', 'F', '.', 'P', 'R', 'O', 'X'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "A black horse kicked the boy."
    judgment := .acceptable
    contrasts := []
    readings := [("part of subject", .acceptable)]
    paperFeatures := [("marking", "relative form"), ("particle", "nee after subject")] }

def ex_17 : Datum :=
  { id := "assmannetal2023_17"
    source := ⟨"assmann-etal-2023", "(17)"⟩
    reportedIn := none
    method := some .description
    language := "haus1257"
    primaryText := "Tankò yaa sàyi kàazaa nèe à kàasuwaa."
    glossedTokens := [("Tankò", "T."), ("yaa", "3SG.M.PFV"), ("sàyi", "buy"), ("kàazaa", "chicken"), ("nèe", "FOC"), ("à", "at"), ("kàasuwaa", "market")]
    glossedWords := [⟨['T', 'a', 'n', 'k', 'ò'], ['T', '.'], [⟨['T', 'a', 'n', 'k', 'ò'], ['T', '.'], none⟩]⟩, ⟨['y', 'a', 'a'], ['3', 'S', 'G', '.', 'M', '.', 'P', 'F', 'V'], [⟨['y', 'a', 'a'], ['3', 'S', 'G', '.', 'M', '.', 'P', 'F', 'V'], none⟩]⟩, ⟨['s', 'à', 'y', 'i'], ['b', 'u', 'y'], [⟨['s', 'à', 'y', 'i'], ['b', 'u', 'y'], none⟩]⟩, ⟨['k', 'à', 'a', 'z', 'a', 'a'], ['c', 'h', 'i', 'c', 'k', 'e', 'n'], [⟨['k', 'à', 'a', 'z', 'a', 'a'], ['c', 'h', 'i', 'c', 'k', 'e', 'n'], none⟩]⟩, ⟨['n', 'è', 'e'], ['F', 'O', 'C'], [⟨['n', 'è', 'e'], ['F', 'O', 'C'], none⟩]⟩, ⟨['à'], ['a', 't'], [⟨['à'], ['a', 't'], none⟩]⟩, ⟨['k', 'à', 'a', 's', 'u', 'w', 'a', 'a'], ['m', 'a', 'r', 'k', 'e', 't'], [⟨['k', 'à', 'a', 's', 'u', 'w', 'a', 'a'], ['m', 'a', 'r', 'k', 'e', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("object", .acceptable)]
    paperFeatures := [("marking", "absolute form"), ("particle", "nee after object")] }

def ex_18a : Datum :=
  { id := "assmannetal2023_18a"
    source := ⟨"assmann-etal-2023", "(18a)"⟩
    reportedIn := none
    method := some .description
    language := "nucl1347"
    primaryText := "Maa-y lekk jën."
    glossedTokens := [("Maa-y", "FOC.1SG-IPFV"), ("lekk", "eat"), ("jën", "fish")]
    glossedWords := [⟨['M', 'a', 'a', '-', 'y'], ['F', 'O', 'C', '.', '1', 'S', 'G', '-', 'I', 'P', 'F', 'V'], [⟨['M', 'a', 'a'], ['F', 'O', 'C', '.', '1', 'S', 'G'], none⟩, ⟨['y'], ['I', 'P', 'F', 'V'], some '-'⟩]⟩, ⟨['l', 'e', 'k', 'k'], ['e', 'a', 't'], [⟨['l', 'e', 'k', 'k'], ['e', 'a', 't'], none⟩]⟩, ⟨['j', 'ë', 'n'], ['f', 'i', 's', 'h'], [⟨['j', 'ë', 'n'], ['f', 'i', 's', 'h'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("subject", .acceptable)]
    paperFeatures := [("marking", "a")] }

def ex_18b : Datum :=
  { id := "assmannetal2023_18b"
    source := ⟨"assmann-etal-2023", "(18b)"⟩
    reportedIn := none
    method := some .description
    language := "nucl1347"
    primaryText := "Jën laa-y lekk."
    glossedTokens := [("Jën", "fish"), ("laa-y", "FOC.1SG-IPFV"), ("lekk", "eat")]
    glossedWords := [⟨['J', 'ë', 'n'], ['f', 'i', 's', 'h'], [⟨['J', 'ë', 'n'], ['f', 'i', 's', 'h'], none⟩]⟩, ⟨['l', 'a', 'a', '-', 'y'], ['F', 'O', 'C', '.', '1', 'S', 'G', '-', 'I', 'P', 'F', 'V'], [⟨['l', 'a', 'a'], ['F', 'O', 'C', '.', '1', 'S', 'G'], none⟩, ⟨['y'], ['I', 'P', 'F', 'V'], some '-'⟩]⟩, ⟨['l', 'e', 'k', 'k'], ['e', 'a', 't'], [⟨['l', 'e', 'k', 'k'], ['e', 'a', 't'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("object", .acceptable)]
    paperFeatures := [("marking", "la"), ("movement", "object fronted")] }

def ex_18c : Datum :=
  { id := "assmannetal2023_18c"
    source := ⟨"assmann-etal-2023", "(18c)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nucl1347"
    primaryText := "Dafa-y lekk jën."
    glossedTokens := [("Dafa-y", "FOC.3SG-IPFV"), ("lekk", "eat"), ("jën", "fish")]
    glossedWords := [⟨['D', 'a', 'f', 'a', '-', 'y'], ['F', 'O', 'C', '.', '3', 'S', 'G', '-', 'I', 'P', 'F', 'V'], [⟨['D', 'a', 'f', 'a'], ['F', 'O', 'C', '.', '3', 'S', 'G'], none⟩, ⟨['y'], ['I', 'P', 'F', 'V'], some '-'⟩]⟩, ⟨['l', 'e', 'k', 'k'], ['e', 'a', 't'], [⟨['l', 'e', 'k', 'k'], ['e', 'a', 't'], none⟩]⟩, ⟨['j', 'ë', 'n'], ['f', 'i', 's', 'h'], [⟨['j', 'ë', 'n'], ['f', 'i', 's', 'h'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "What is Omar doing? / Is he buying fish?"
    judgment := .acceptable
    contrasts := []
    readings := [("verb", .acceptable), ("VP", .acceptable)]
    paperFeatures := [("marking", "dafa")] }

def ex_19 : Datum :=
  { id := "assmannetal2023_19"
    source := ⟨"assmann-etal-2023", "(19)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nucl1347"
    primaryText := "Mu-ngi naan ndox."
    glossedTokens := [("Mu-ngi", "3SG-PROG"), ("naan", "drink"), ("ndox", "water")]
    glossedWords := [⟨['M', 'u', '-', 'n', 'g', 'i'], ['3', 'S', 'G', '-', 'P', 'R', 'O', 'G'], [⟨['M', 'u'], ['3', 'S', 'G'], none⟩, ⟨['n', 'g', 'i'], ['P', 'R', 'O', 'G'], some '-'⟩]⟩, ⟨['n', 'a', 'a', 'n'], ['d', 'r', 'i', 'n', 'k'], [⟨['n', 'a', 'a', 'n'], ['d', 'r', 'i', 'n', 'k'], none⟩]⟩, ⟨['n', 'd', 'o', 'x'], ['w', 'a', 't', 'e', 'r'], [⟨['n', 'd', 'o', 'x'], ['w', 'a', 't', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "What is happening?"
    judgment := .acceptable
    contrasts := []
    readings := [("clause", .acceptable)]
    paperFeatures := [("marking", "ngi"), ("aspect", "imperfective")] }

def ex_20 : Datum :=
  { id := "assmannetal2023_20"
    source := ⟨"assmann-etal-2023", "(20)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nucl1347"
    primaryText := "Fatou bind na téére."
    glossedTokens := [("Fatou", "F."), ("bind", "write"), ("na", "FOC.3SG"), ("téére", "book")]
    glossedWords := [⟨['F', 'a', 't', 'o', 'u'], ['F', '.'], [⟨['F', 'a', 't', 'o', 'u'], ['F', '.'], none⟩]⟩, ⟨['b', 'i', 'n', 'd'], ['w', 'r', 'i', 't', 'e'], [⟨['b', 'i', 'n', 'd'], ['w', 'r', 'i', 't', 'e'], none⟩]⟩, ⟨['n', 'a'], ['F', 'O', 'C', '.', '3', 'S', 'G'], [⟨['n', 'a'], ['F', 'O', 'C', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['t', 'é', 'é', 'r', 'e'], ['b', 'o', 'o', 'k'], [⟨['t', 'é', 'é', 'r', 'e'], ['b', 'o', 'o', 'k'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "What happened?"
    judgment := .acceptable
    contrasts := []
    readings := [("clause", .acceptable)]
    paperFeatures := [("marking", "na"), ("aspect", "perfective")] }

def ex_37 : Datum :=
  { id := "assmannetal2023_37"
    source := ⟨"assmann-etal-2023", "(37)"⟩
    reportedIn := none
    method := some .description
    language := "cent2142"
    primaryText := "Maria-x wawa-r t'ant' chur-i-wa."
    glossedTokens := [("Maria-x", "Maria-TOP"), ("wawa-r", "baby-ALL"), ("t'ant'", "bread"), ("chur-i-wa", "give-3-FOC")]
    glossedWords := [⟨['M', 'a', 'r', 'i', 'a', '-', 'x'], ['M', 'a', 'r', 'i', 'a', '-', 'T', 'O', 'P'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩, ⟨['x'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['w', 'a', 'w', 'a', '-', 'r'], ['b', 'a', 'b', 'y', '-', 'A', 'L', 'L'], [⟨['w', 'a', 'w', 'a'], ['b', 'a', 'b', 'y'], none⟩, ⟨['r'], ['A', 'L', 'L'], some '-'⟩]⟩, ⟨['t', '\'', 'a', 'n', 't', '\''], ['b', 'r', 'e', 'a', 'd'], [⟨['t', '\'', 'a', 'n', 't', '\''], ['b', 'r', 'e', 'a', 'd'], none⟩]⟩, ⟨['c', 'h', 'u', 'r', '-', 'i', '-', 'w', 'a'], ['g', 'i', 'v', 'e', '-', '3', '-', 'F', 'O', 'C'], [⟨['c', 'h', 'u', 'r'], ['g', 'i', 'v', 'e'], none⟩, ⟨['i'], ['3'], some '-'⟩, ⟨['w', 'a'], ['F', 'O', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "What happened?"
    judgment := .acceptable
    contrasts := []
    readings := [("clause", .acceptable)]
    paperFeatures := [("marking", "wa on verb")] }

def ex_38 : Datum :=
  { id := "assmannetal2023_38"
    source := ⟨"assmann-etal-2023", "(38)"⟩
    reportedIn := none
    method := some .description
    language := "cent2142"
    primaryText := "Manq'a-k-i-wa."
    glossedTokens := [("Manq'a-k-i-wa", "eat-EXCL-3-FOC")]
    glossedWords := [⟨['M', 'a', 'n', 'q', '\'', 'a', '-', 'k', '-', 'i', '-', 'w', 'a'], ['e', 'a', 't', '-', 'E', 'X', 'C', 'L', '-', '3', '-', 'F', 'O', 'C'], [⟨['M', 'a', 'n', 'q', '\'', 'a'], ['e', 'a', 't'], none⟩, ⟨['k'], ['E', 'X', 'C', 'L'], some '-'⟩, ⟨['i'], ['3'], some '-'⟩, ⟨['w', 'a'], ['F', 'O', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("verb", .acceptable)]
    paperFeatures := [("marking", "wa on verb")] }

def ex_39 : Datum :=
  { id := "assmannetal2023_39"
    source := ⟨"assmann-etal-2023", "(39)"⟩
    reportedIn := none
    method := some .description
    language := "cent2142"
    primaryText := "Jani-wa futbola-ki-t gust-k-i-ti, challwa katu-ña gusta-raki-wa."
    glossedTokens := [("Jani-wa", "no-WA"), ("futbola-ki-t", "futbol-EXCL-ABL"), ("gust-k-i-ti", "like-NCOMPL-3-TI"), ("challwa", "fish"), ("katu-ña", "fish-INF"), ("gusta-raki-wa", "like-ADD-FOC")]
    glossedWords := [⟨['J', 'a', 'n', 'i', '-', 'w', 'a'], ['n', 'o', '-', 'W', 'A'], [⟨['J', 'a', 'n', 'i'], ['n', 'o'], none⟩, ⟨['w', 'a'], ['W', 'A'], some '-'⟩]⟩, ⟨['f', 'u', 't', 'b', 'o', 'l', 'a', '-', 'k', 'i', '-', 't'], ['f', 'u', 't', 'b', 'o', 'l', '-', 'E', 'X', 'C', 'L', '-', 'A', 'B', 'L'], [⟨['f', 'u', 't', 'b', 'o', 'l', 'a'], ['f', 'u', 't', 'b', 'o', 'l'], none⟩, ⟨['k', 'i'], ['E', 'X', 'C', 'L'], some '-'⟩, ⟨['t'], ['A', 'B', 'L'], some '-'⟩]⟩, ⟨['g', 'u', 's', 't', '-', 'k', '-', 'i', '-', 't', 'i'], ['l', 'i', 'k', 'e', '-', 'N', 'C', 'O', 'M', 'P', 'L', '-', '3', '-', 'T', 'I'], [⟨['g', 'u', 's', 't'], ['l', 'i', 'k', 'e'], none⟩, ⟨['k'], ['N', 'C', 'O', 'M', 'P', 'L'], some '-'⟩, ⟨['i'], ['3'], some '-'⟩, ⟨['t', 'i'], ['T', 'I'], some '-'⟩]⟩, ⟨['c', 'h', 'a', 'l', 'l', 'w', 'a'], ['f', 'i', 's', 'h'], [⟨['c', 'h', 'a', 'l', 'l', 'w', 'a'], ['f', 'i', 's', 'h'], none⟩]⟩, ⟨['k', 'a', 't', 'u', '-', 'ñ', 'a'], ['f', 'i', 's', 'h', '-', 'I', 'N', 'F'], [⟨['k', 'a', 't', 'u'], ['f', 'i', 's', 'h'], none⟩, ⟨['ñ', 'a'], ['I', 'N', 'F'], some '-'⟩]⟩, ⟨['g', 'u', 's', 't', 'a', '-', 'r', 'a', 'k', 'i', '-', 'w', 'a'], ['l', 'i', 'k', 'e', '-', 'A', 'D', 'D', '-', 'F', 'O', 'C'], [⟨['g', 'u', 's', 't', 'a'], ['l', 'i', 'k', 'e'], none⟩, ⟨['r', 'a', 'k', 'i'], ['A', 'D', 'D'], some '-'⟩, ⟨['w', 'a'], ['F', 'O', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("VP", .acceptable)]
    paperFeatures := [("marking", "wa on verb")] }

def ex_41 : Datum :=
  { id := "assmannetal2023_41"
    source := ⟨"assmann-etal-2023", "(41)"⟩
    reportedIn := none
    method := some .description
    language := "awin1248"
    primaryText := "Alombah a-pe'-náŋnə ŋgəsáŋə̀."
    glossedTokens := [("Alombah", "A."), ("a-pe'-náŋnə", "SM-PST-cook"), ("ŋgəsáŋə̀", "maize")]
    glossedWords := [⟨['A', 'l', 'o', 'm', 'b', 'a', 'h'], ['A', '.'], [⟨['A', 'l', 'o', 'm', 'b', 'a', 'h'], ['A', '.'], none⟩]⟩, ⟨['a', '-', 'p', 'e', '\'', '-', 'n', 'á', 'ŋ', 'n', 'ə'], ['S', 'M', '-', 'P', 'S', 'T', '-', 'c', 'o', 'o', 'k'], [⟨['a'], ['S', 'M'], none⟩, ⟨['p', 'e', '\''], ['P', 'S', 'T'], some '-'⟩, ⟨['n', 'á', 'ŋ', 'n', 'ə'], ['c', 'o', 'o', 'k'], some '-'⟩]⟩, ⟨['ŋ', 'g', 'ə', 's', 'á', 'ŋ', 'ə', '̀'], ['m', 'a', 'i', 'z', 'e'], [⟨['ŋ', 'g', 'ə', 's', 'á', 'ŋ', 'ə', '̀'], ['m', 'a', 'i', 'z', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "What did Alombah cook? / What did Alombah do with the maize? / What did Alombah do? / Who cooked the maize? / What happened?"
    judgment := .acceptable
    contrasts := []
    readings := [("object", .acceptable), ("verb", .acceptable), ("VP", .acceptable), ("subject", .acceptable), ("clause", .acceptable)]
    paperFeatures := [("marking", "none")] }

def ex_53 : Datum :=
  { id := "assmannetal2023_53"
    source := ⟨"assmann-etal-2023", "(53)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kim ATE the yogurt."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("verb", .acceptable), ("object", .unacceptable), ("VP", .unacceptable), ("clause", .unacceptable), ("subject", .unacceptable), ("subject and verb", .acceptable)]
    paperFeatures := [("marking", "nuclear stress on verb")] }

def ex_56 : Datum :=
  { id := "assmannetal2023_56"
    source := ⟨"assmann-etal-2023", "(56)"⟩
    reportedIn := none
    method := some .elicitation
    language := "haus1257"
    primaryText := "A'a, wasu yaara sun saata ta."
    glossedTokens := [("A'a", "no"), ("wasu", "some"), ("yaara", "children"), ("sun", "3PL.PFV"), ("saata", "steal"), ("ta", "3SG.F.O")]
    glossedWords := [⟨['A', '\'', 'a'], ['n', 'o'], [⟨['A', '\'', 'a'], ['n', 'o'], none⟩]⟩, ⟨['w', 'a', 's', 'u'], ['s', 'o', 'm', 'e'], [⟨['w', 'a', 's', 'u'], ['s', 'o', 'm', 'e'], none⟩]⟩, ⟨['y', 'a', 'a', 'r', 'a'], ['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n'], [⟨['y', 'a', 'a', 'r', 'a'], ['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n'], none⟩]⟩, ⟨['s', 'u', 'n'], ['3', 'P', 'L', '.', 'P', 'F', 'V'], [⟨['s', 'u', 'n'], ['3', 'P', 'L', '.', 'P', 'F', 'V'], none⟩]⟩, ⟨['s', 'a', 'a', 't', 'a'], ['s', 't', 'e', 'a', 'l'], [⟨['s', 'a', 'a', 't', 'a'], ['s', 't', 'e', 'a', 'l'], none⟩]⟩, ⟨['t', 'a'], ['3', 'S', 'G', '.', 'F', '.', 'O'], [⟨['t', 'a'], ['3', 'S', 'G', '.', 'F', '.', 'O'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Can I borrow your car?"
    judgment := .acceptable
    contrasts := []
    readings := [("subject and verb", .acceptable)]
    paperFeatures := [("marking", "absolute form")] }

def ex_57a : Datum :=
  { id := "assmannetal2023_57a"
    source := ⟨"assmann-etal-2023", "(57a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nucl1347"
    primaryText := "Alkaati bi jàpp na ko/Jean."
    glossedTokens := [("Alkaati", "police.officer"), ("bi", "DET"), ("jàpp", "catch"), ("na", "PFV.3SG"), ("ko/Jean", "3SG.O/J.")]
    glossedWords := [⟨['A', 'l', 'k', 'a', 'a', 't', 'i'], ['p', 'o', 'l', 'i', 'c', 'e', '.', 'o', 'f', 'f', 'i', 'c', 'e', 'r'], [⟨['A', 'l', 'k', 'a', 'a', 't', 'i'], ['p', 'o', 'l', 'i', 'c', 'e', '.', 'o', 'f', 'f', 'i', 'c', 'e', 'r'], none⟩]⟩, ⟨['b', 'i'], ['D', 'E', 'T'], [⟨['b', 'i'], ['D', 'E', 'T'], none⟩]⟩, ⟨['j', 'à', 'p', 'p'], ['c', 'a', 't', 'c', 'h'], [⟨['j', 'à', 'p', 'p'], ['c', 'a', 't', 'c', 'h'], none⟩]⟩, ⟨['n', 'a'], ['P', 'F', 'V', '.', '3', 'S', 'G'], [⟨['n', 'a'], ['P', 'F', 'V', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['k', 'o', '/', 'J', 'e', 'a', 'n'], ['3', 'S', 'G', '.', 'O', '/', 'J', '.'], [⟨['k', 'o', '/', 'J', 'e', 'a', 'n'], ['3', 'S', 'G', '.', 'O', '/', 'J', '.'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "What happened to Jean?"
    judgment := .acceptable
    contrasts := []
    readings := [("subject and verb", .acceptable)]
    paperFeatures := [("marking", "na")] }

def ex_59 : Datum :=
  { id := "assmannetal2023_59"
    source := ⟨"assmann-etal-2023", "(59)"⟩
    reportedIn := none
    method := some .elicitation
    language := "buli1254"
    primaryText := "Aayá, (ká) Amoak alé pa dá!"
    glossedTokens := [("Aayá", "no"), ("(ká)", "FOC"), ("Amoak", "Amoak"), ("alé", "FOC"), ("pa", "take"), ("dá", "sell")]
    glossedWords := [⟨['A', 'a', 'y', 'á'], ['n', 'o'], [⟨['A', 'a', 'y', 'á'], ['n', 'o'], none⟩]⟩, ⟨['(', 'k', 'á', ')'], ['F', 'O', 'C'], [⟨['k', 'á'], ['F', 'O', 'C'], none⟩]⟩, ⟨['A', 'm', 'o', 'a', 'k'], ['A', 'm', 'o', 'a', 'k'], [⟨['A', 'm', 'o', 'a', 'k'], ['A', 'm', 'o', 'a', 'k'], none⟩]⟩, ⟨['a', 'l', 'é'], ['F', 'O', 'C'], [⟨['a', 'l', 'é'], ['F', 'O', 'C'], none⟩]⟩, ⟨['p', 'a'], ['t', 'a', 'k', 'e'], [⟨['p', 'a'], ['t', 'a', 'k', 'e'], none⟩]⟩, ⟨['d', 'á'], ['s', 'e', 'l', 'l'], [⟨['d', 'á'], ['s', 'e', 'l', 'l'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Did Atim eat the mango?"
    judgment := .acceptable
    contrasts := []
    readings := [("subject and verb", .acceptable)]
    paperFeatures := [("marking", "le after subject")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_5, fn4_i, ex_6a, ex_6b, ex_7, ex_8, ex_10, ex_11, ex_12, ex_13, ex_14, ex_15, ex_17, ex_18a, ex_18b, ex_18c, ex_19, ex_20, ex_37, ex_38, ex_39, ex_41, ex_53, ex_56, ex_57a, ex_59]

end AssmannEtAl2023.Examples
