module

public import Linglib.Data.Examples.Schema

/-!
# `HendersonCoon2018` — typed example data

Auto-generated from `Linglib/Data/Examples/HendersonCoon2018.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HendersonCoon2018.Examples`.
-/

@[expose] public section

namespace HendersonCoon2018.Examples

def ex_1 : Datum :=
  { id := "hendersoncoon2018_1"
    source := ⟨"henderson-coon-2018", "(1)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike x-Ø-u-löq' ri äk'?"
    glossedTokens := [("Achike", "who"), ("x-Ø-u-löq'", "CPL-ABS3S-ERG3S-buy"), ("ri", "the"), ("äk'", "chicken")]
    glossedWords := [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o'], [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o'], none⟩]⟩, ⟨['x', '-', 'Ø', '-', 'u', '-', 'l', 'ö', 'q', '\''], ['C', 'P', 'L', '-', 'A', 'B', 'S', '3', 'S', '-', 'E', 'R', 'G', '3', 'S', '-', 'b', 'u', 'y'], [⟨['x'], ['C', 'P', 'L'], none⟩, ⟨['Ø'], ['A', 'B', 'S', '3', 'S'], some '-'⟩, ⟨['u'], ['E', 'R', 'G', '3', 'S'], some '-'⟩, ⟨['l', 'ö', 'q', '\''], ['b', 'u', 'y'], some '-'⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['ä', 'k', '\''], ['c', 'h', 'i', 'c', 'k', 'e', 'n'], [⟨['ä', 'k', '\''], ['c', 'h', 'i', 'c', 'k', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "dp"), ("subject", "3"), ("object", "3")] }

def ex_2 : Datum :=
  { id := "hendersoncoon2018_2"
    source := ⟨"henderson-coon-2018", "(2)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike x-Ø-loq'-o ri äk'?"
    glossedTokens := [("Achike", "who"), ("x-Ø-loq'-o", "CPL-ABS3S-buy-AF"), ("ri", "the"), ("äk'", "chicken")]
    glossedWords := [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o'], [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o'], none⟩]⟩, ⟨['x', '-', 'Ø', '-', 'l', 'o', 'q', '\'', '-', 'o'], ['C', 'P', 'L', '-', 'A', 'B', 'S', '3', 'S', '-', 'b', 'u', 'y', '-', 'A', 'F'], [⟨['x'], ['C', 'P', 'L'], none⟩, ⟨['Ø'], ['A', 'B', 'S', '3', 'S'], some '-'⟩, ⟨['l', 'o', 'q', '\''], ['b', 'u', 'y'], some '-'⟩, ⟨['o'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['ä', 'k', '\''], ['c', 'h', 'i', 'c', 'k', 'e', 'n'], [⟨['ä', 'k', '\''], ['c', 'h', 'i', 'c', 'k', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "AF"), ("objectKind", "dp"), ("subject", "3"), ("object", "3")] }

def ex_12a : Datum :=
  { id := "hendersoncoon2018_12a"
    source := ⟨"henderson-coon-2018", "(12a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike x-Ø-u-löq' ri tijonel?"
    glossedTokens := [("Achike", "what"), ("x-Ø-u-löq'", "CPL-ABS3S-ERG3S-buy"), ("ri", "the"), ("tijonel", "teacher")]
    glossedWords := [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'a', 't'], [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'a', 't'], none⟩]⟩, ⟨['x', '-', 'Ø', '-', 'u', '-', 'l', 'ö', 'q', '\''], ['C', 'P', 'L', '-', 'A', 'B', 'S', '3', 'S', '-', 'E', 'R', 'G', '3', 'S', '-', 'b', 'u', 'y'], [⟨['x'], ['C', 'P', 'L'], none⟩, ⟨['Ø'], ['A', 'B', 'S', '3', 'S'], some '-'⟩, ⟨['u'], ['E', 'R', 'G', '3', 'S'], some '-'⟩, ⟨['l', 'ö', 'q', '\''], ['b', 'u', 'y'], some '-'⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['t', 'i', 'j', 'o', 'n', 'e', 'l'], ['t', 'e', 'a', 'c', 'h', 'e', 'r'], [⟨['t', 'i', 'j', 'o', 'n', 'e', 'l'], ['t', 'e', 'a', 'c', 'h', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "object"), ("verb", "TV"), ("objectKind", "dp"), ("subject", "3"), ("object", "3")] }

def ex_18a : Datum :=
  { id := "hendersoncoon2018_18a"
    source := ⟨"henderson-coon-2018", "(18a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Ja ri ixoq x-Ø-u-ch'ëy r-i'."
    glossedTokens := [("Ja", "FOC"), ("ri", "the"), ("ixoq", "woman"), ("x-Ø-u-ch'ëy", "CPL-ABS3S-ERG3S-hit"), ("r-i'", "ERG3S-self")]
    glossedWords := [⟨['J', 'a'], ['F', 'O', 'C'], [⟨['J', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['i', 'x', 'o', 'q'], ['w', 'o', 'm', 'a', 'n'], [⟨['i', 'x', 'o', 'q'], ['w', 'o', 'm', 'a', 'n'], none⟩]⟩, ⟨['x', '-', 'Ø', '-', 'u', '-', 'c', 'h', '\'', 'ë', 'y'], ['C', 'P', 'L', '-', 'A', 'B', 'S', '3', 'S', '-', 'E', 'R', 'G', '3', 'S', '-', 'h', 'i', 't'], [⟨['x'], ['C', 'P', 'L'], none⟩, ⟨['Ø'], ['A', 'B', 'S', '3', 'S'], some '-'⟩, ⟨['u'], ['E', 'R', 'G', '3', 'S'], some '-'⟩, ⟨['c', 'h', '\'', 'ë', 'y'], ['h', 'i', 't'], some '-'⟩]⟩, ⟨['r', '-', 'i', '\''], ['E', 'R', 'G', '3', 'S', '-', 's', 'e', 'l', 'f'], [⟨['r'], ['E', 'R', 'G', '3', 'S'], none⟩, ⟨['i', '\''], ['s', 'e', 'l', 'f'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "reflexive"), ("subject", "3"), ("object", "3")] }

def ex_18b : Datum :=
  { id := "hendersoncoon2018_18b"
    source := ⟨"henderson-coon-2018", "(18b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike x-Ø-u-k'äm pe r-ixayil pa nimaq'ij"
    glossedTokens := [("Achike", "who"), ("x-Ø-u-k'äm", "CPL-ABS3S-ERG3S-bring"), ("pe", "DIR"), ("r-ixayil", "ERG3S-wife"), ("pa", "PREP"), ("nimaq'ij", "party")]
    glossedWords := [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o'], [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o'], none⟩]⟩, ⟨['x', '-', 'Ø', '-', 'u', '-', 'k', '\'', 'ä', 'm'], ['C', 'P', 'L', '-', 'A', 'B', 'S', '3', 'S', '-', 'E', 'R', 'G', '3', 'S', '-', 'b', 'r', 'i', 'n', 'g'], [⟨['x'], ['C', 'P', 'L'], none⟩, ⟨['Ø'], ['A', 'B', 'S', '3', 'S'], some '-'⟩, ⟨['u'], ['E', 'R', 'G', '3', 'S'], some '-'⟩, ⟨['k', '\'', 'ä', 'm'], ['b', 'r', 'i', 'n', 'g'], some '-'⟩]⟩, ⟨['p', 'e'], ['D', 'I', 'R'], [⟨['p', 'e'], ['D', 'I', 'R'], none⟩]⟩, ⟨['r', '-', 'i', 'x', 'a', 'y', 'i', 'l'], ['E', 'R', 'G', '3', 'S', '-', 'w', 'i', 'f', 'e'], [⟨['r'], ['E', 'R', 'G', '3', 'S'], none⟩, ⟨['i', 'x', 'a', 'y', 'i', 'l'], ['w', 'i', 'f', 'e'], some '-'⟩]⟩, ⟨['p', 'a'], ['P', 'R', 'E', 'P'], [⟨['p', 'a'], ['P', 'R', 'E', 'P'], none⟩]⟩, ⟨['n', 'i', 'm', 'a', 'q', '\'', 'i', 'j'], ['p', 'a', 'r', 't', 'y'], [⟨['n', 'i', 'm', 'a', 'q', '\'', 'i', 'j'], ['p', 'a', 'r', 't', 'y'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "extendedReflexive"), ("subject", "3"), ("object", "3")] }

def ex_19 : Datum :=
  { id := "hendersoncoon2018_19"
    source := ⟨"henderson-coon-2018", "(19)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "... ri nik'aj chïk winäq ri ni-Ø-ki-b'ij chi ni-Ø-ki-b'än jun kosa y..."
    glossedTokens := [("ri", "the"), ("nik'aj", "half"), ("chïk", "again"), ("winäq", "people"), ("ri", "REL"), ("ni-Ø-ki-b'ij", "ICPL-ABS3S-ERG3P-say"), ("chi", "that"), ("ni-Ø-ki-b'än", "ICPL-ABS3S-ERG3P-do"), ("jun", "one"), ("kosa", "thing"), ("y", "and")]
    glossedWords := [⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['n', 'i', 'k', '\'', 'a', 'j'], ['h', 'a', 'l', 'f'], [⟨['n', 'i', 'k', '\'', 'a', 'j'], ['h', 'a', 'l', 'f'], none⟩]⟩, ⟨['c', 'h', 'ï', 'k'], ['a', 'g', 'a', 'i', 'n'], [⟨['c', 'h', 'ï', 'k'], ['a', 'g', 'a', 'i', 'n'], none⟩]⟩, ⟨['w', 'i', 'n', 'ä', 'q'], ['p', 'e', 'o', 'p', 'l', 'e'], [⟨['w', 'i', 'n', 'ä', 'q'], ['p', 'e', 'o', 'p', 'l', 'e'], none⟩]⟩, ⟨['r', 'i'], ['R', 'E', 'L'], [⟨['r', 'i'], ['R', 'E', 'L'], none⟩]⟩, ⟨['n', 'i', '-', 'Ø', '-', 'k', 'i', '-', 'b', '\'', 'i', 'j'], ['I', 'C', 'P', 'L', '-', 'A', 'B', 'S', '3', 'S', '-', 'E', 'R', 'G', '3', 'P', '-', 's', 'a', 'y'], [⟨['n', 'i'], ['I', 'C', 'P', 'L'], none⟩, ⟨['Ø'], ['A', 'B', 'S', '3', 'S'], some '-'⟩, ⟨['k', 'i'], ['E', 'R', 'G', '3', 'P'], some '-'⟩, ⟨['b', '\'', 'i', 'j'], ['s', 'a', 'y'], some '-'⟩]⟩, ⟨['c', 'h', 'i'], ['t', 'h', 'a', 't'], [⟨['c', 'h', 'i'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['n', 'i', '-', 'Ø', '-', 'k', 'i', '-', 'b', '\'', 'ä', 'n'], ['I', 'C', 'P', 'L', '-', 'A', 'B', 'S', '3', 'S', '-', 'E', 'R', 'G', '3', 'P', '-', 'd', 'o'], [⟨['n', 'i'], ['I', 'C', 'P', 'L'], none⟩, ⟨['Ø'], ['A', 'B', 'S', '3', 'S'], some '-'⟩, ⟨['k', 'i'], ['E', 'R', 'G', '3', 'P'], some '-'⟩, ⟨['b', '\'', 'ä', 'n'], ['d', 'o'], some '-'⟩]⟩, ⟨['j', 'u', 'n'], ['o', 'n', 'e'], [⟨['j', 'u', 'n'], ['o', 'n', 'e'], none⟩]⟩, ⟨['k', 'o', 's', 'a'], ['t', 'h', 'i', 'n', 'g'], [⟨['k', 'o', 's', 'a'], ['t', 'h', 'i', 'n', 'g'], none⟩]⟩, ⟨['y'], ['a', 'n', 'd'], [⟨['y'], ['a', 'n', 'd'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "clause"), ("subject", "3"), ("object", "3")] }

def ex_20 : Datum :=
  { id := "hendersoncoon2018_20"
    source := ⟨"henderson-coon-2018", "(20)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike x-Ø-u-b'än manifestar pa b'ey?"
    glossedTokens := [("Achike", "who"), ("x-Ø-u-b'än", "CPL-ABS3S-ERG3S-do"), ("manifestar", "protest"), ("pa", "in"), ("b'ey", "street")]
    glossedWords := [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o'], [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o'], none⟩]⟩, ⟨['x', '-', 'Ø', '-', 'u', '-', 'b', '\'', 'ä', 'n'], ['C', 'P', 'L', '-', 'A', 'B', 'S', '3', 'S', '-', 'E', 'R', 'G', '3', 'S', '-', 'd', 'o'], [⟨['x'], ['C', 'P', 'L'], none⟩, ⟨['Ø'], ['A', 'B', 'S', '3', 'S'], some '-'⟩, ⟨['u'], ['E', 'R', 'G', '3', 'S'], some '-'⟩, ⟨['b', '\'', 'ä', 'n'], ['d', 'o'], some '-'⟩]⟩, ⟨['m', 'a', 'n', 'i', 'f', 'e', 's', 't', 'a', 'r'], ['p', 'r', 'o', 't', 'e', 's', 't'], [⟨['m', 'a', 'n', 'i', 'f', 'e', 's', 't', 'a', 'r'], ['p', 'r', 'o', 't', 'e', 's', 't'], none⟩]⟩, ⟨['p', 'a'], ['i', 'n'], [⟨['p', 'a'], ['i', 'n'], none⟩]⟩, ⟨['b', '\'', 'e', 'y'], ['s', 't', 'r', 'e', 'e', 't'], [⟨['b', '\'', 'e', 'y'], ['s', 't', 'r', 'e', 'e', 't'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "lightVerb"), ("subject", "3"), ("object", "3")] }

def ex_4 : Datum :=
  { id := "hendersoncoon2018_4"
    source := ⟨"henderson-coon-2018", "(4)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike kan qitzij x-Ø-u-tij ri wäy?"
    glossedTokens := [("Achike", "who"), ("kan", "truly"), ("qitzij", "truth"), ("x-Ø-u-tij", "CPL-ABS3S-ERG3S-eat"), ("ri", "the"), ("wäy", "tortilla")]
    glossedWords := [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o'], [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o'], none⟩]⟩, ⟨['k', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], [⟨['k', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], none⟩]⟩, ⟨['q', 'i', 't', 'z', 'i', 'j'], ['t', 'r', 'u', 't', 'h'], [⟨['q', 'i', 't', 'z', 'i', 'j'], ['t', 'r', 'u', 't', 'h'], none⟩]⟩, ⟨['x', '-', 'Ø', '-', 'u', '-', 't', 'i', 'j'], ['C', 'P', 'L', '-', 'A', 'B', 'S', '3', 'S', '-', 'E', 'R', 'G', '3', 'S', '-', 'e', 'a', 't'], [⟨['x'], ['C', 'P', 'L'], none⟩, ⟨['Ø'], ['A', 'B', 'S', '3', 'S'], some '-'⟩, ⟨['u'], ['E', 'R', 'G', '3', 'S'], some '-'⟩, ⟨['t', 'i', 'j'], ['e', 'a', 't'], some '-'⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['w', 'ä', 'y'], ['t', 'o', 'r', 't', 'i', 'l', 'l', 'a'], [⟨['w', 'ä', 'y'], ['t', 'o', 'r', 't', 'i', 'l', 'l', 'a'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "kan qitzij")] }

def ex_5 : Datum :=
  { id := "hendersoncoon2018_5"
    source := ⟨"henderson-coon-2018", "(5)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Ri kan qitzij y-e-ya'-on ru-q'ij k'o chi e ütz chuqa'."
    glossedTokens := [("Ri", "REL"), ("kan", "truly"), ("qitzij", "truth"), ("y-e-ya'-on", "ICPL-ABS3P-give-AF"), ("ru-q'ij", "ERG3S-day"), ("k'o chi", "must"), ("e", "ABS3P"), ("ütz", "good"), ("chuqa'", "also")]
    glossedWords := [⟨['R', 'i'], ['R', 'E', 'L'], [⟨['R', 'i'], ['R', 'E', 'L'], none⟩]⟩, ⟨['k', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], [⟨['k', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], none⟩]⟩, ⟨['q', 'i', 't', 'z', 'i', 'j'], ['t', 'r', 'u', 't', 'h'], [⟨['q', 'i', 't', 'z', 'i', 'j'], ['t', 'r', 'u', 't', 'h'], none⟩]⟩, ⟨['y', '-', 'e', '-', 'y', 'a', '\'', '-', 'o', 'n'], ['I', 'C', 'P', 'L', '-', 'A', 'B', 'S', '3', 'P', '-', 'g', 'i', 'v', 'e', '-', 'A', 'F'], [⟨['y'], ['I', 'C', 'P', 'L'], none⟩, ⟨['e'], ['A', 'B', 'S', '3', 'P'], some '-'⟩, ⟨['y', 'a', '\''], ['g', 'i', 'v', 'e'], some '-'⟩, ⟨['o', 'n'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'u', '-', 'q', '\'', 'i', 'j'], ['E', 'R', 'G', '3', 'S', '-', 'd', 'a', 'y'], [⟨['r', 'u'], ['E', 'R', 'G', '3', 'S'], none⟩, ⟨['q', '\'', 'i', 'j'], ['d', 'a', 'y'], some '-'⟩]⟩, ⟨['k', '\'', 'o', ' ', 'c', 'h', 'i'], ['m', 'u', 's', 't'], [⟨['k', '\'', 'o', ' ', 'c', 'h', 'i'], ['m', 'u', 's', 't'], none⟩]⟩, ⟨['e'], ['A', 'B', 'S', '3', 'P'], [⟨['e'], ['A', 'B', 'S', '3', 'P'], none⟩]⟩, ⟨['ü', 't', 'z'], ['g', 'o', 'o', 'd'], [⟨['ü', 't', 'z'], ['g', 'o', 'o', 'd'], none⟩]⟩, ⟨['c', 'h', 'u', 'q', 'a', '\''], ['a', 'l', 's', 'o'], [⟨['c', 'h', 'u', 'q', 'a', '\''], ['a', 'l', 's', 'o'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "AF"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "kan qitzij")] }

def ex_6 : Datum :=
  { id := "hendersoncoon2018_6"
    source := ⟨"henderson-coon-2018", "(6)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "... roma ri winäq ri kan qitzij n-Ø-u-ya' ru-q'ij ri Dios..."
    glossedTokens := [("roma", "because"), ("ri", "the"), ("winäq", "person"), ("ri", "REL"), ("kan", "truly"), ("qitzij", "truth"), ("n-Ø-u-ya'", "ICPL-ABS3S-ERG3S-give"), ("ru-q'ij", "ERG3S-day"), ("ri", "the"), ("Dios", "God")]
    glossedWords := [⟨['r', 'o', 'm', 'a'], ['b', 'e', 'c', 'a', 'u', 's', 'e'], [⟨['r', 'o', 'm', 'a'], ['b', 'e', 'c', 'a', 'u', 's', 'e'], none⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['w', 'i', 'n', 'ä', 'q'], ['p', 'e', 'r', 's', 'o', 'n'], [⟨['w', 'i', 'n', 'ä', 'q'], ['p', 'e', 'r', 's', 'o', 'n'], none⟩]⟩, ⟨['r', 'i'], ['R', 'E', 'L'], [⟨['r', 'i'], ['R', 'E', 'L'], none⟩]⟩, ⟨['k', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], [⟨['k', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], none⟩]⟩, ⟨['q', 'i', 't', 'z', 'i', 'j'], ['t', 'r', 'u', 't', 'h'], [⟨['q', 'i', 't', 'z', 'i', 'j'], ['t', 'r', 'u', 't', 'h'], none⟩]⟩, ⟨['n', '-', 'Ø', '-', 'u', '-', 'y', 'a', '\''], ['I', 'C', 'P', 'L', '-', 'A', 'B', 'S', '3', 'S', '-', 'E', 'R', 'G', '3', 'S', '-', 'g', 'i', 'v', 'e'], [⟨['n'], ['I', 'C', 'P', 'L'], none⟩, ⟨['Ø'], ['A', 'B', 'S', '3', 'S'], some '-'⟩, ⟨['u'], ['E', 'R', 'G', '3', 'S'], some '-'⟩, ⟨['y', 'a', '\''], ['g', 'i', 'v', 'e'], some '-'⟩]⟩, ⟨['r', 'u', '-', 'q', '\'', 'i', 'j'], ['E', 'R', 'G', '3', 'S', '-', 'd', 'a', 'y'], [⟨['r', 'u'], ['E', 'R', 'G', '3', 'S'], none⟩, ⟨['q', '\'', 'i', 'j'], ['d', 'a', 'y'], some '-'⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['D', 'i', 'o', 's'], ['G', 'o', 'd'], [⟨['D', 'i', 'o', 's'], ['G', 'o', 'd'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "kan qitzij")] }

def ex_24 : Datum :=
  { id := "hendersoncoon2018_24"
    source := ⟨"henderson-coon-2018", "(24)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "... ri pastores ri kan x-Ø-ki-tzijoj ri ru-ch'ab'äl ri Dios ch-iw-e."
    glossedTokens := [("ri", "the"), ("pastores", "pastors"), ("ri", "REL"), ("kan", "truly"), ("x-Ø-ki-tzijoj", "CPL-ABS3S-ERG3P-preach"), ("ri", "the"), ("ru-ch'ab'äl", "ERG3S-word"), ("ri", "the"), ("Dios", "God"), ("ch-iw-e", "PREP-ERG2P-RN.to")]
    glossedWords := [⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['p', 'a', 's', 't', 'o', 'r', 'e', 's'], ['p', 'a', 's', 't', 'o', 'r', 's'], [⟨['p', 'a', 's', 't', 'o', 'r', 'e', 's'], ['p', 'a', 's', 't', 'o', 'r', 's'], none⟩]⟩, ⟨['r', 'i'], ['R', 'E', 'L'], [⟨['r', 'i'], ['R', 'E', 'L'], none⟩]⟩, ⟨['k', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], [⟨['k', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], none⟩]⟩, ⟨['x', '-', 'Ø', '-', 'k', 'i', '-', 't', 'z', 'i', 'j', 'o', 'j'], ['C', 'P', 'L', '-', 'A', 'B', 'S', '3', 'S', '-', 'E', 'R', 'G', '3', 'P', '-', 'p', 'r', 'e', 'a', 'c', 'h'], [⟨['x'], ['C', 'P', 'L'], none⟩, ⟨['Ø'], ['A', 'B', 'S', '3', 'S'], some '-'⟩, ⟨['k', 'i'], ['E', 'R', 'G', '3', 'P'], some '-'⟩, ⟨['t', 'z', 'i', 'j', 'o', 'j'], ['p', 'r', 'e', 'a', 'c', 'h'], some '-'⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['r', 'u', '-', 'c', 'h', '\'', 'a', 'b', '\'', 'ä', 'l'], ['E', 'R', 'G', '3', 'S', '-', 'w', 'o', 'r', 'd'], [⟨['r', 'u'], ['E', 'R', 'G', '3', 'S'], none⟩, ⟨['c', 'h', '\'', 'a', 'b', '\'', 'ä', 'l'], ['w', 'o', 'r', 'd'], some '-'⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['D', 'i', 'o', 's'], ['G', 'o', 'd'], [⟨['D', 'i', 'o', 's'], ['G', 'o', 'd'], none⟩]⟩, ⟨['c', 'h', '-', 'i', 'w', '-', 'e'], ['P', 'R', 'E', 'P', '-', 'E', 'R', 'G', '2', 'P', '-', 'R', 'N', '.', 't', 'o'], [⟨['c', 'h'], ['P', 'R', 'E', 'P'], none⟩, ⟨['i', 'w'], ['E', 'R', 'G', '2', 'P'], some '-'⟩, ⟨['e'], ['R', 'N', '.', 't', 'o'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "kan")] }

def ex_25 : Datum :=
  { id := "hendersoncoon2018_25"
    source := ⟨"henderson-coon-2018", "(25)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Rija' kan jun achi ri kan x-Ø-u-q'alaj-saj ri nu-ch'ab'äl."
    glossedTokens := [("Rija'", "He"), ("kan", "truly"), ("jun", "a"), ("achi", "man"), ("ri", "REL"), ("kan", "truly"), ("x-Ø-u-q'alaj-saj", "CPL-ABS3S-ERG3S-visible-CAUS"), ("ri", "the"), ("nu-ch'ab'äl", "ERG1S-word")]
    glossedWords := [⟨['R', 'i', 'j', 'a', '\''], ['H', 'e'], [⟨['R', 'i', 'j', 'a', '\''], ['H', 'e'], none⟩]⟩, ⟨['k', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], [⟨['k', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], none⟩]⟩, ⟨['j', 'u', 'n'], ['a'], [⟨['j', 'u', 'n'], ['a'], none⟩]⟩, ⟨['a', 'c', 'h', 'i'], ['m', 'a', 'n'], [⟨['a', 'c', 'h', 'i'], ['m', 'a', 'n'], none⟩]⟩, ⟨['r', 'i'], ['R', 'E', 'L'], [⟨['r', 'i'], ['R', 'E', 'L'], none⟩]⟩, ⟨['k', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], [⟨['k', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], none⟩]⟩, ⟨['x', '-', 'Ø', '-', 'u', '-', 'q', '\'', 'a', 'l', 'a', 'j', '-', 's', 'a', 'j'], ['C', 'P', 'L', '-', 'A', 'B', 'S', '3', 'S', '-', 'E', 'R', 'G', '3', 'S', '-', 'v', 'i', 's', 'i', 'b', 'l', 'e', '-', 'C', 'A', 'U', 'S'], [⟨['x'], ['C', 'P', 'L'], none⟩, ⟨['Ø'], ['A', 'B', 'S', '3', 'S'], some '-'⟩, ⟨['u'], ['E', 'R', 'G', '3', 'S'], some '-'⟩, ⟨['q', '\'', 'a', 'l', 'a', 'j'], ['v', 'i', 's', 'i', 'b', 'l', 'e'], some '-'⟩, ⟨['s', 'a', 'j'], ['C', 'A', 'U', 'S'], some '-'⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['n', 'u', '-', 'c', 'h', '\'', 'a', 'b', '\'', 'ä', 'l'], ['E', 'R', 'G', '1', 'S', '-', 'w', 'o', 'r', 'd'], [⟨['n', 'u'], ['E', 'R', 'G', '1', 'S'], none⟩, ⟨['c', 'h', '\'', 'a', 'b', '\'', 'ä', 'l'], ['w', 'o', 'r', 'd'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "kan")] }

def ex_27 : Datum :=
  { id := "hendersoncoon2018_27"
    source := ⟨"henderson-coon-2018", "(27)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Ri kan xti-Ø-b'an-o k'a ri nu-samäj, xti-Ø-ya'-ox k'a ru-q'ij r-oma ri Nata'."
    glossedTokens := [("Ri", "REL"), ("kan", "truly"), ("xti-Ø-b'an-o", "POT-ABS3S-do-AF"), ("k'a ri", "then"), ("nu-samäj", "ERG1S-work"), ("xti-Ø-ya'-ox", "POT-ABS3S-give-PASS"), ("k'a", "then"), ("ru-q'ij", "ERG3S-day"), ("r-oma", "ERG3S-by"), ("ri", "the"), ("Nata'", "Father")]
    glossedWords := [⟨['R', 'i'], ['R', 'E', 'L'], [⟨['R', 'i'], ['R', 'E', 'L'], none⟩]⟩, ⟨['k', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], [⟨['k', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], none⟩]⟩, ⟨['x', 't', 'i', '-', 'Ø', '-', 'b', '\'', 'a', 'n', '-', 'o'], ['P', 'O', 'T', '-', 'A', 'B', 'S', '3', 'S', '-', 'd', 'o', '-', 'A', 'F'], [⟨['x', 't', 'i'], ['P', 'O', 'T'], none⟩, ⟨['Ø'], ['A', 'B', 'S', '3', 'S'], some '-'⟩, ⟨['b', '\'', 'a', 'n'], ['d', 'o'], some '-'⟩, ⟨['o'], ['A', 'F'], some '-'⟩]⟩, ⟨['k', '\'', 'a', ' ', 'r', 'i'], ['t', 'h', 'e', 'n'], [⟨['k', '\'', 'a', ' ', 'r', 'i'], ['t', 'h', 'e', 'n'], none⟩]⟩, ⟨['n', 'u', '-', 's', 'a', 'm', 'ä', 'j'], ['E', 'R', 'G', '1', 'S', '-', 'w', 'o', 'r', 'k'], [⟨['n', 'u'], ['E', 'R', 'G', '1', 'S'], none⟩, ⟨['s', 'a', 'm', 'ä', 'j'], ['w', 'o', 'r', 'k'], some '-'⟩]⟩, ⟨['x', 't', 'i', '-', 'Ø', '-', 'y', 'a', '\'', '-', 'o', 'x'], ['P', 'O', 'T', '-', 'A', 'B', 'S', '3', 'S', '-', 'g', 'i', 'v', 'e', '-', 'P', 'A', 'S', 'S'], [⟨['x', 't', 'i'], ['P', 'O', 'T'], none⟩, ⟨['Ø'], ['A', 'B', 'S', '3', 'S'], some '-'⟩, ⟨['y', 'a', '\''], ['g', 'i', 'v', 'e'], some '-'⟩, ⟨['o', 'x'], ['P', 'A', 'S', 'S'], some '-'⟩]⟩, ⟨['k', '\'', 'a'], ['t', 'h', 'e', 'n'], [⟨['k', '\'', 'a'], ['t', 'h', 'e', 'n'], none⟩]⟩, ⟨['r', 'u', '-', 'q', '\'', 'i', 'j'], ['E', 'R', 'G', '3', 'S', '-', 'd', 'a', 'y'], [⟨['r', 'u'], ['E', 'R', 'G', '3', 'S'], none⟩, ⟨['q', '\'', 'i', 'j'], ['d', 'a', 'y'], some '-'⟩]⟩, ⟨['r', '-', 'o', 'm', 'a'], ['E', 'R', 'G', '3', 'S', '-', 'b', 'y'], [⟨['r'], ['E', 'R', 'G', '3', 'S'], none⟩, ⟨['o', 'm', 'a'], ['b', 'y'], some '-'⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['N', 'a', 't', 'a', '\''], ['F', 'a', 't', 'h', 'e', 'r'], [⟨['N', 'a', 't', 'a', '\''], ['F', 'a', 't', 'h', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "AF"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "kan")] }

def ex_28 : Datum :=
  { id := "hendersoncoon2018_28"
    source := ⟨"henderson-coon-2018", "(28)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike k'a ri n-Ø-u-k'üt re tzij re' ch-qa-wäch?"
    glossedTokens := [("Achike", "who"), ("k'a ri", "then"), ("n-Ø-u-k'üt", "ICPL-ABS3S-ERG3S-show"), ("re", "this"), ("tzij", "word"), ("re'", "DEIC"), ("ch-qa-wäch", "PREP-ERG1P-RN.front")]
    glossedWords := [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o'], [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o'], none⟩]⟩, ⟨['k', '\'', 'a', ' ', 'r', 'i'], ['t', 'h', 'e', 'n'], [⟨['k', '\'', 'a', ' ', 'r', 'i'], ['t', 'h', 'e', 'n'], none⟩]⟩, ⟨['n', '-', 'Ø', '-', 'u', '-', 'k', '\'', 'ü', 't'], ['I', 'C', 'P', 'L', '-', 'A', 'B', 'S', '3', 'S', '-', 'E', 'R', 'G', '3', 'S', '-', 's', 'h', 'o', 'w'], [⟨['n'], ['I', 'C', 'P', 'L'], none⟩, ⟨['Ø'], ['A', 'B', 'S', '3', 'S'], some '-'⟩, ⟨['u'], ['E', 'R', 'G', '3', 'S'], some '-'⟩, ⟨['k', '\'', 'ü', 't'], ['s', 'h', 'o', 'w'], some '-'⟩]⟩, ⟨['r', 'e'], ['t', 'h', 'i', 's'], [⟨['r', 'e'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['t', 'z', 'i', 'j'], ['w', 'o', 'r', 'd'], [⟨['t', 'z', 'i', 'j'], ['w', 'o', 'r', 'd'], none⟩]⟩, ⟨['r', 'e', '\''], ['D', 'E', 'I', 'C'], [⟨['r', 'e', '\''], ['D', 'E', 'I', 'C'], none⟩]⟩, ⟨['c', 'h', '-', 'q', 'a', '-', 'w', 'ä', 'c', 'h'], ['P', 'R', 'E', 'P', '-', 'E', 'R', 'G', '1', 'P', '-', 'R', 'N', '.', 'f', 'r', 'o', 'n', 't'], [⟨['c', 'h'], ['P', 'R', 'E', 'P'], none⟩, ⟨['q', 'a'], ['E', 'R', 'G', '1', 'P'], some '-'⟩, ⟨['w', 'ä', 'c', 'h'], ['R', 'N', '.', 'f', 'r', 'o', 'n', 't'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "k'a ri")] }

def ex_29 : Datum :=
  { id := "hendersoncoon2018_29"
    source := ⟨"henderson-coon-2018", "(29)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Ri achike k'a ri n-Ø-r-ak'axaj ri ru-ch'ab'äl ri Nata' Dios y n-Ø-r-etamaj..."
    glossedTokens := [("Ri", "REL"), ("achike", "who"), ("k'a ri", "then"), ("n-Ø-r-ak'axaj", "ICPL-ABS3S-ERG3S-hear"), ("ri", "the"), ("ru-ch'ab'äl", "ERG3S-word"), ("ri", "the"), ("Nata'", "father"), ("Dios", "god"), ("y", "and"), ("n-Ø-r-etamaj", "ICPL-ABS3S-ERG3S-learn")]
    glossedWords := [⟨['R', 'i'], ['R', 'E', 'L'], [⟨['R', 'i'], ['R', 'E', 'L'], none⟩]⟩, ⟨['a', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o'], [⟨['a', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o'], none⟩]⟩, ⟨['k', '\'', 'a', ' ', 'r', 'i'], ['t', 'h', 'e', 'n'], [⟨['k', '\'', 'a', ' ', 'r', 'i'], ['t', 'h', 'e', 'n'], none⟩]⟩, ⟨['n', '-', 'Ø', '-', 'r', '-', 'a', 'k', '\'', 'a', 'x', 'a', 'j'], ['I', 'C', 'P', 'L', '-', 'A', 'B', 'S', '3', 'S', '-', 'E', 'R', 'G', '3', 'S', '-', 'h', 'e', 'a', 'r'], [⟨['n'], ['I', 'C', 'P', 'L'], none⟩, ⟨['Ø'], ['A', 'B', 'S', '3', 'S'], some '-'⟩, ⟨['r'], ['E', 'R', 'G', '3', 'S'], some '-'⟩, ⟨['a', 'k', '\'', 'a', 'x', 'a', 'j'], ['h', 'e', 'a', 'r'], some '-'⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['r', 'u', '-', 'c', 'h', '\'', 'a', 'b', '\'', 'ä', 'l'], ['E', 'R', 'G', '3', 'S', '-', 'w', 'o', 'r', 'd'], [⟨['r', 'u'], ['E', 'R', 'G', '3', 'S'], none⟩, ⟨['c', 'h', '\'', 'a', 'b', '\'', 'ä', 'l'], ['w', 'o', 'r', 'd'], some '-'⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['N', 'a', 't', 'a', '\''], ['f', 'a', 't', 'h', 'e', 'r'], [⟨['N', 'a', 't', 'a', '\''], ['f', 'a', 't', 'h', 'e', 'r'], none⟩]⟩, ⟨['D', 'i', 'o', 's'], ['g', 'o', 'd'], [⟨['D', 'i', 'o', 's'], ['g', 'o', 'd'], none⟩]⟩, ⟨['y'], ['a', 'n', 'd'], [⟨['y'], ['a', 'n', 'd'], none⟩]⟩, ⟨['n', '-', 'Ø', '-', 'r', '-', 'e', 't', 'a', 'm', 'a', 'j'], ['I', 'C', 'P', 'L', '-', 'A', 'B', 'S', '3', 'S', '-', 'E', 'R', 'G', '3', 'S', '-', 'l', 'e', 'a', 'r', 'n'], [⟨['n'], ['I', 'C', 'P', 'L'], none⟩, ⟨['Ø'], ['A', 'B', 'S', '3', 'S'], some '-'⟩, ⟨['r'], ['E', 'R', 'G', '3', 'S'], some '-'⟩, ⟨['e', 't', 'a', 'm', 'a', 'j'], ['l', 'e', 'a', 'r', 'n'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "k'a ri")] }

def ex_30 : Datum :=
  { id := "hendersoncoon2018_30"
    source := ⟨"henderson-coon-2018", "(30)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike k'a ri x-a-ch'ey-o?"
    glossedTokens := [("Achike", "who"), ("k'a ri", "then"), ("x-a-ch'ey-o", "CPL-ABS2S-fight-AF")]
    glossedWords := [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o'], [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o'], none⟩]⟩, ⟨['k', '\'', 'a', ' ', 'r', 'i'], ['t', 'h', 'e', 'n'], [⟨['k', '\'', 'a', ' ', 'r', 'i'], ['t', 'h', 'e', 'n'], none⟩]⟩, ⟨['x', '-', 'a', '-', 'c', 'h', '\'', 'e', 'y', '-', 'o'], ['C', 'P', 'L', '-', 'A', 'B', 'S', '2', 'S', '-', 'f', 'i', 'g', 'h', 't', '-', 'A', 'F'], [⟨['x'], ['C', 'P', 'L'], none⟩, ⟨['a'], ['A', 'B', 'S', '2', 'S'], some '-'⟩, ⟨['c', 'h', '\'', 'e', 'y'], ['f', 'i', 'g', 'h', 't'], some '-'⟩, ⟨['o'], ['A', 'F'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "AF"), ("objectKind", "dp"), ("subject", "3"), ("object", "2"), ("intervener", "k'a ri")] }

def ex_31 : Datum :=
  { id := "hendersoncoon2018_31"
    source := ⟨"henderson-coon-2018", "(31)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Xab'achike k'a ri xti-Ø-nima-n ri Jesús kan xt-Ø-r-il wi k'a jun k'aslen ri..."
    glossedTokens := [("Xab'achike", "whoever"), ("k'a ri", "then"), ("xti-Ø-nima-n", "POT-ABS3S-believe-AF"), ("ri", "the"), ("Jesús", "Jesus"), ("kan", "truly"), ("xt-Ø-r-il", "POT-ABS3S-ERG3S-find"), ("wi", "FOC"), ("k'a", "then"), ("jun", "a"), ("k'aslen", "life"), ("ri", "REL")]
    glossedWords := [⟨['X', 'a', 'b', '\'', 'a', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o', 'e', 'v', 'e', 'r'], [⟨['X', 'a', 'b', '\'', 'a', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o', 'e', 'v', 'e', 'r'], none⟩]⟩, ⟨['k', '\'', 'a', ' ', 'r', 'i'], ['t', 'h', 'e', 'n'], [⟨['k', '\'', 'a', ' ', 'r', 'i'], ['t', 'h', 'e', 'n'], none⟩]⟩, ⟨['x', 't', 'i', '-', 'Ø', '-', 'n', 'i', 'm', 'a', '-', 'n'], ['P', 'O', 'T', '-', 'A', 'B', 'S', '3', 'S', '-', 'b', 'e', 'l', 'i', 'e', 'v', 'e', '-', 'A', 'F'], [⟨['x', 't', 'i'], ['P', 'O', 'T'], none⟩, ⟨['Ø'], ['A', 'B', 'S', '3', 'S'], some '-'⟩, ⟨['n', 'i', 'm', 'a'], ['b', 'e', 'l', 'i', 'e', 'v', 'e'], some '-'⟩, ⟨['n'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['J', 'e', 's', 'ú', 's'], ['J', 'e', 's', 'u', 's'], [⟨['J', 'e', 's', 'ú', 's'], ['J', 'e', 's', 'u', 's'], none⟩]⟩, ⟨['k', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], [⟨['k', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], none⟩]⟩, ⟨['x', 't', '-', 'Ø', '-', 'r', '-', 'i', 'l'], ['P', 'O', 'T', '-', 'A', 'B', 'S', '3', 'S', '-', 'E', 'R', 'G', '3', 'S', '-', 'f', 'i', 'n', 'd'], [⟨['x', 't'], ['P', 'O', 'T'], none⟩, ⟨['Ø'], ['A', 'B', 'S', '3', 'S'], some '-'⟩, ⟨['r'], ['E', 'R', 'G', '3', 'S'], some '-'⟩, ⟨['i', 'l'], ['f', 'i', 'n', 'd'], some '-'⟩]⟩, ⟨['w', 'i'], ['F', 'O', 'C'], [⟨['w', 'i'], ['F', 'O', 'C'], none⟩]⟩, ⟨['k', '\'', 'a'], ['t', 'h', 'e', 'n'], [⟨['k', '\'', 'a'], ['t', 'h', 'e', 'n'], none⟩]⟩, ⟨['j', 'u', 'n'], ['a'], [⟨['j', 'u', 'n'], ['a'], none⟩]⟩, ⟨['k', '\'', 'a', 's', 'l', 'e', 'n'], ['l', 'i', 'f', 'e'], [⟨['k', '\'', 'a', 's', 'l', 'e', 'n'], ['l', 'i', 'f', 'e'], none⟩]⟩, ⟨['r', 'i'], ['R', 'E', 'L'], [⟨['r', 'i'], ['R', 'E', 'L'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "AF"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "k'a ri")] }

def ex_32 : Datum :=
  { id := "hendersoncoon2018_32"
    source := ⟨"henderson-coon-2018", "(32)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike chi-k-e man x-Ø-tij-o ta ri takamal"
    glossedTokens := [("Achike", "who"), ("chi-k-e", "PREP-ERG3P-RN"), ("man", "NEG"), ("x-Ø-tij-o", "CPL-ABS3S-eat-AF"), ("ta", "IRR"), ("ri", "the"), ("takamal", "tamale")]
    glossedWords := [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o'], [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o'], none⟩]⟩, ⟨['c', 'h', 'i', '-', 'k', '-', 'e'], ['P', 'R', 'E', 'P', '-', 'E', 'R', 'G', '3', 'P', '-', 'R', 'N'], [⟨['c', 'h', 'i'], ['P', 'R', 'E', 'P'], none⟩, ⟨['k'], ['E', 'R', 'G', '3', 'P'], some '-'⟩, ⟨['e'], ['R', 'N'], some '-'⟩]⟩, ⟨['m', 'a', 'n'], ['N', 'E', 'G'], [⟨['m', 'a', 'n'], ['N', 'E', 'G'], none⟩]⟩, ⟨['x', '-', 'Ø', '-', 't', 'i', 'j', '-', 'o'], ['C', 'P', 'L', '-', 'A', 'B', 'S', '3', 'S', '-', 'e', 'a', 't', '-', 'A', 'F'], [⟨['x'], ['C', 'P', 'L'], none⟩, ⟨['Ø'], ['A', 'B', 'S', '3', 'S'], some '-'⟩, ⟨['t', 'i', 'j'], ['e', 'a', 't'], some '-'⟩, ⟨['o'], ['A', 'F'], some '-'⟩]⟩, ⟨['t', 'a'], ['I', 'R', 'R'], [⟨['t', 'a'], ['I', 'R', 'R'], none⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['t', 'a', 'k', 'a', 'm', 'a', 'l'], ['t', 'a', 'm', 'a', 'l', 'e'], [⟨['t', 'a', 'k', 'a', 'm', 'a', 'l'], ['t', 'a', 'm', 'a', 'l', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "AF"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "man")] }

def ex_33 : Datum :=
  { id := "hendersoncoon2018_33"
    source := ⟨"henderson-coon-2018", "(33)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike chi-k-e man x-Ø-u-tij ta ri takamal"
    glossedTokens := [("Achike", "who"), ("chi-k-e", "PREP-ERG3P-RN"), ("man", "NEG"), ("x-Ø-u-tij", "CPL-ABS3S-ERG3S-eat"), ("ta", "IRR"), ("ri", "the"), ("takamal", "tamale")]
    glossedWords := [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o'], [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o'], none⟩]⟩, ⟨['c', 'h', 'i', '-', 'k', '-', 'e'], ['P', 'R', 'E', 'P', '-', 'E', 'R', 'G', '3', 'P', '-', 'R', 'N'], [⟨['c', 'h', 'i'], ['P', 'R', 'E', 'P'], none⟩, ⟨['k'], ['E', 'R', 'G', '3', 'P'], some '-'⟩, ⟨['e'], ['R', 'N'], some '-'⟩]⟩, ⟨['m', 'a', 'n'], ['N', 'E', 'G'], [⟨['m', 'a', 'n'], ['N', 'E', 'G'], none⟩]⟩, ⟨['x', '-', 'Ø', '-', 'u', '-', 't', 'i', 'j'], ['C', 'P', 'L', '-', 'A', 'B', 'S', '3', 'S', '-', 'E', 'R', 'G', '3', 'S', '-', 'e', 'a', 't'], [⟨['x'], ['C', 'P', 'L'], none⟩, ⟨['Ø'], ['A', 'B', 'S', '3', 'S'], some '-'⟩, ⟨['u'], ['E', 'R', 'G', '3', 'S'], some '-'⟩, ⟨['t', 'i', 'j'], ['e', 'a', 't'], some '-'⟩]⟩, ⟨['t', 'a'], ['I', 'R', 'R'], [⟨['t', 'a'], ['I', 'R', 'R'], none⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['t', 'a', 'k', 'a', 'm', 'a', 'l'], ['t', 'a', 'm', 'a', 'l', 'e'], [⟨['t', 'a', 'k', 'a', 'm', 'a', 'l'], ['t', 'a', 'm', 'a', 'l', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "man")] }

def ex_45 : Datum :=
  { id := "hendersoncoon2018_45"
    source := ⟨"henderson-coon-2018", "(45)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "K'o q-ach'alal ri kan qitzij chi rije' y-e-ya'-o ru-q'ij."
    glossedTokens := [("K'o", "EXST"), ("q-ach'alal", "ERG1P-family"), ("ri", "REL"), ("kan", "truly"), ("qitzij", "truth"), ("chi", "COMP"), ("rije'", "PRON3P"), ("y-e-ya'-o", "ICPL-ABS3P-give-AF"), ("ru-q'ij", "ERG3S-day")]
    glossedWords := [⟨['K', '\'', 'o'], ['E', 'X', 'S', 'T'], [⟨['K', '\'', 'o'], ['E', 'X', 'S', 'T'], none⟩]⟩, ⟨['q', '-', 'a', 'c', 'h', '\'', 'a', 'l', 'a', 'l'], ['E', 'R', 'G', '1', 'P', '-', 'f', 'a', 'm', 'i', 'l', 'y'], [⟨['q'], ['E', 'R', 'G', '1', 'P'], none⟩, ⟨['a', 'c', 'h', '\'', 'a', 'l', 'a', 'l'], ['f', 'a', 'm', 'i', 'l', 'y'], some '-'⟩]⟩, ⟨['r', 'i'], ['R', 'E', 'L'], [⟨['r', 'i'], ['R', 'E', 'L'], none⟩]⟩, ⟨['k', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], [⟨['k', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], none⟩]⟩, ⟨['q', 'i', 't', 'z', 'i', 'j'], ['t', 'r', 'u', 't', 'h'], [⟨['q', 'i', 't', 'z', 'i', 'j'], ['t', 'r', 'u', 't', 'h'], none⟩]⟩, ⟨['c', 'h', 'i'], ['C', 'O', 'M', 'P'], [⟨['c', 'h', 'i'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['r', 'i', 'j', 'e', '\''], ['P', 'R', 'O', 'N', '3', 'P'], [⟨['r', 'i', 'j', 'e', '\''], ['P', 'R', 'O', 'N', '3', 'P'], none⟩]⟩, ⟨['y', '-', 'e', '-', 'y', 'a', '\'', '-', 'o'], ['I', 'C', 'P', 'L', '-', 'A', 'B', 'S', '3', 'P', '-', 'g', 'i', 'v', 'e', '-', 'A', 'F'], [⟨['y'], ['I', 'C', 'P', 'L'], none⟩, ⟨['e'], ['A', 'B', 'S', '3', 'P'], some '-'⟩, ⟨['y', 'a', '\''], ['g', 'i', 'v', 'e'], some '-'⟩, ⟨['o'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'u', '-', 'q', '\'', 'i', 'j'], ['E', 'R', 'G', '3', 'S', '-', 'd', 'a', 'y'], [⟨['r', 'u'], ['E', 'R', 'G', '3', 'S'], none⟩, ⟨['q', '\'', 'i', 'j'], ['d', 'a', 'y'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "AF"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "kan qitzij"), ("complementizer", "chi"), ("resumptive", "overt")] }

def ex_46 : Datum :=
  { id := "hendersoncoon2018_46"
    source := ⟨"henderson-coon-2018", "(46)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "K'o q-ach'alal ri kan qitzij chi rije' y-e-loq'-o ru-wäy."
    glossedTokens := [("K'o", "EXST"), ("q-ach'alal", "ERG1P-family"), ("ri", "REL"), ("kan", "truly"), ("qitzij", "truth"), ("chi", "COMP"), ("rije'", "PRON3P"), ("y-e-loq'-o", "ICPL-ABS3P-buy-AF"), ("ru-wäy", "ERG3S-food")]
    glossedWords := [⟨['K', '\'', 'o'], ['E', 'X', 'S', 'T'], [⟨['K', '\'', 'o'], ['E', 'X', 'S', 'T'], none⟩]⟩, ⟨['q', '-', 'a', 'c', 'h', '\'', 'a', 'l', 'a', 'l'], ['E', 'R', 'G', '1', 'P', '-', 'f', 'a', 'm', 'i', 'l', 'y'], [⟨['q'], ['E', 'R', 'G', '1', 'P'], none⟩, ⟨['a', 'c', 'h', '\'', 'a', 'l', 'a', 'l'], ['f', 'a', 'm', 'i', 'l', 'y'], some '-'⟩]⟩, ⟨['r', 'i'], ['R', 'E', 'L'], [⟨['r', 'i'], ['R', 'E', 'L'], none⟩]⟩, ⟨['k', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], [⟨['k', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], none⟩]⟩, ⟨['q', 'i', 't', 'z', 'i', 'j'], ['t', 'r', 'u', 't', 'h'], [⟨['q', 'i', 't', 'z', 'i', 'j'], ['t', 'r', 'u', 't', 'h'], none⟩]⟩, ⟨['c', 'h', 'i'], ['C', 'O', 'M', 'P'], [⟨['c', 'h', 'i'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['r', 'i', 'j', 'e', '\''], ['P', 'R', 'O', 'N', '3', 'P'], [⟨['r', 'i', 'j', 'e', '\''], ['P', 'R', 'O', 'N', '3', 'P'], none⟩]⟩, ⟨['y', '-', 'e', '-', 'l', 'o', 'q', '\'', '-', 'o'], ['I', 'C', 'P', 'L', '-', 'A', 'B', 'S', '3', 'P', '-', 'b', 'u', 'y', '-', 'A', 'F'], [⟨['y'], ['I', 'C', 'P', 'L'], none⟩, ⟨['e'], ['A', 'B', 'S', '3', 'P'], some '-'⟩, ⟨['l', 'o', 'q', '\''], ['b', 'u', 'y'], some '-'⟩, ⟨['o'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'u', '-', 'w', 'ä', 'y'], ['E', 'R', 'G', '3', 'S', '-', 'f', 'o', 'o', 'd'], [⟨['r', 'u'], ['E', 'R', 'G', '3', 'S'], none⟩, ⟨['w', 'ä', 'y'], ['f', 'o', 'o', 'd'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "AF"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "kan qitzij"), ("complementizer", "chi"), ("resumptive", "overt")] }

def ex_49 : Datum :=
  { id := "hendersoncoon2018_49"
    source := ⟨"henderson-coon-2018", "(49)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "K'o q-ach'alal ri kan qitzij chi rije' n-Ø-ki-ya' ru-q'ij."
    glossedTokens := [("K'o", "EXST"), ("q-ach'alal", "ERG1P-family"), ("ri", "REL"), ("kan", "truly"), ("qitzij", "truth"), ("chi", "COMP"), ("rije'", "PRON3P"), ("n-Ø-ki-ya'", "ICPL-ABS3S-ERG3P-give"), ("ru-q'ij", "ERG3S-day")]
    glossedWords := [⟨['K', '\'', 'o'], ['E', 'X', 'S', 'T'], [⟨['K', '\'', 'o'], ['E', 'X', 'S', 'T'], none⟩]⟩, ⟨['q', '-', 'a', 'c', 'h', '\'', 'a', 'l', 'a', 'l'], ['E', 'R', 'G', '1', 'P', '-', 'f', 'a', 'm', 'i', 'l', 'y'], [⟨['q'], ['E', 'R', 'G', '1', 'P'], none⟩, ⟨['a', 'c', 'h', '\'', 'a', 'l', 'a', 'l'], ['f', 'a', 'm', 'i', 'l', 'y'], some '-'⟩]⟩, ⟨['r', 'i'], ['R', 'E', 'L'], [⟨['r', 'i'], ['R', 'E', 'L'], none⟩]⟩, ⟨['k', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], [⟨['k', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], none⟩]⟩, ⟨['q', 'i', 't', 'z', 'i', 'j'], ['t', 'r', 'u', 't', 'h'], [⟨['q', 'i', 't', 'z', 'i', 'j'], ['t', 'r', 'u', 't', 'h'], none⟩]⟩, ⟨['c', 'h', 'i'], ['C', 'O', 'M', 'P'], [⟨['c', 'h', 'i'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['r', 'i', 'j', 'e', '\''], ['P', 'R', 'O', 'N', '3', 'P'], [⟨['r', 'i', 'j', 'e', '\''], ['P', 'R', 'O', 'N', '3', 'P'], none⟩]⟩, ⟨['n', '-', 'Ø', '-', 'k', 'i', '-', 'y', 'a', '\''], ['I', 'C', 'P', 'L', '-', 'A', 'B', 'S', '3', 'S', '-', 'E', 'R', 'G', '3', 'P', '-', 'g', 'i', 'v', 'e'], [⟨['n'], ['I', 'C', 'P', 'L'], none⟩, ⟨['Ø'], ['A', 'B', 'S', '3', 'S'], some '-'⟩, ⟨['k', 'i'], ['E', 'R', 'G', '3', 'P'], some '-'⟩, ⟨['y', 'a', '\''], ['g', 'i', 'v', 'e'], some '-'⟩]⟩, ⟨['r', 'u', '-', 'q', '\'', 'i', 'j'], ['E', 'R', 'G', '3', 'S', '-', 'd', 'a', 'y'], [⟨['r', 'u'], ['E', 'R', 'G', '3', 'S'], none⟩, ⟨['q', '\'', 'i', 'j'], ['d', 'a', 'y'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "kan qitzij"), ("complementizer", "chi"), ("resumptive", "overt")] }

def ex_50 : Datum :=
  { id := "hendersoncoon2018_50"
    source := ⟨"henderson-coon-2018", "(50)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "K'o q-ach'alal ri kan qitzij chi rije' n-Ø-ki-loq' ru-wäy."
    glossedTokens := [("K'o", "EXST"), ("q-ach'alal", "ERG1P-family"), ("ri", "REL"), ("kan", "truly"), ("qitzij", "truth"), ("chi", "COMP"), ("rije'", "PRON3P"), ("n-Ø-ki-loq'", "ICPL-ABS3S-ERG3P-buy"), ("ru-wäy", "ERG3S-food")]
    glossedWords := [⟨['K', '\'', 'o'], ['E', 'X', 'S', 'T'], [⟨['K', '\'', 'o'], ['E', 'X', 'S', 'T'], none⟩]⟩, ⟨['q', '-', 'a', 'c', 'h', '\'', 'a', 'l', 'a', 'l'], ['E', 'R', 'G', '1', 'P', '-', 'f', 'a', 'm', 'i', 'l', 'y'], [⟨['q'], ['E', 'R', 'G', '1', 'P'], none⟩, ⟨['a', 'c', 'h', '\'', 'a', 'l', 'a', 'l'], ['f', 'a', 'm', 'i', 'l', 'y'], some '-'⟩]⟩, ⟨['r', 'i'], ['R', 'E', 'L'], [⟨['r', 'i'], ['R', 'E', 'L'], none⟩]⟩, ⟨['k', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], [⟨['k', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], none⟩]⟩, ⟨['q', 'i', 't', 'z', 'i', 'j'], ['t', 'r', 'u', 't', 'h'], [⟨['q', 'i', 't', 'z', 'i', 'j'], ['t', 'r', 'u', 't', 'h'], none⟩]⟩, ⟨['c', 'h', 'i'], ['C', 'O', 'M', 'P'], [⟨['c', 'h', 'i'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['r', 'i', 'j', 'e', '\''], ['P', 'R', 'O', 'N', '3', 'P'], [⟨['r', 'i', 'j', 'e', '\''], ['P', 'R', 'O', 'N', '3', 'P'], none⟩]⟩, ⟨['n', '-', 'Ø', '-', 'k', 'i', '-', 'l', 'o', 'q', '\''], ['I', 'C', 'P', 'L', '-', 'A', 'B', 'S', '3', 'S', '-', 'E', 'R', 'G', '3', 'P', '-', 'b', 'u', 'y'], [⟨['n'], ['I', 'C', 'P', 'L'], none⟩, ⟨['Ø'], ['A', 'B', 'S', '3', 'S'], some '-'⟩, ⟨['k', 'i'], ['E', 'R', 'G', '3', 'P'], some '-'⟩, ⟨['l', 'o', 'q', '\''], ['b', 'u', 'y'], some '-'⟩]⟩, ⟨['r', 'u', '-', 'w', 'ä', 'y'], ['E', 'R', 'G', '3', 'S', '-', 'f', 'o', 'o', 'd'], [⟨['r', 'u'], ['E', 'R', 'G', '3', 'S'], none⟩, ⟨['w', 'ä', 'y'], ['f', 'o', 'o', 'd'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "kan qitzij"), ("complementizer", "chi"), ("resumptive", "overt")] }

def ex_51 : Datum :=
  { id := "hendersoncoon2018_51"
    source := ⟨"henderson-coon-2018", "(51)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "K'o q-ach'alal ri kan qitzij chi ja rije' y-e-ya-o ru-q'ij."
    glossedTokens := [("K'o", "EXST"), ("q-ach'alal", "ERG1P-family"), ("ri", "REL"), ("kan", "truly"), ("qitzij", "truth"), ("chi", "COMP"), ("ja", "FOC"), ("rije'", "PRON3P"), ("y-e-ya-o", "CPL-ABS3P-give-AF"), ("ru-q'ij", "ERG3S-day")]
    glossedWords := [⟨['K', '\'', 'o'], ['E', 'X', 'S', 'T'], [⟨['K', '\'', 'o'], ['E', 'X', 'S', 'T'], none⟩]⟩, ⟨['q', '-', 'a', 'c', 'h', '\'', 'a', 'l', 'a', 'l'], ['E', 'R', 'G', '1', 'P', '-', 'f', 'a', 'm', 'i', 'l', 'y'], [⟨['q'], ['E', 'R', 'G', '1', 'P'], none⟩, ⟨['a', 'c', 'h', '\'', 'a', 'l', 'a', 'l'], ['f', 'a', 'm', 'i', 'l', 'y'], some '-'⟩]⟩, ⟨['r', 'i'], ['R', 'E', 'L'], [⟨['r', 'i'], ['R', 'E', 'L'], none⟩]⟩, ⟨['k', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], [⟨['k', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], none⟩]⟩, ⟨['q', 'i', 't', 'z', 'i', 'j'], ['t', 'r', 'u', 't', 'h'], [⟨['q', 'i', 't', 'z', 'i', 'j'], ['t', 'r', 'u', 't', 'h'], none⟩]⟩, ⟨['c', 'h', 'i'], ['C', 'O', 'M', 'P'], [⟨['c', 'h', 'i'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'i', 'j', 'e', '\''], ['P', 'R', 'O', 'N', '3', 'P'], [⟨['r', 'i', 'j', 'e', '\''], ['P', 'R', 'O', 'N', '3', 'P'], none⟩]⟩, ⟨['y', '-', 'e', '-', 'y', 'a', '-', 'o'], ['C', 'P', 'L', '-', 'A', 'B', 'S', '3', 'P', '-', 'g', 'i', 'v', 'e', '-', 'A', 'F'], [⟨['y'], ['C', 'P', 'L'], none⟩, ⟨['e'], ['A', 'B', 'S', '3', 'P'], some '-'⟩, ⟨['y', 'a'], ['g', 'i', 'v', 'e'], some '-'⟩, ⟨['o'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'u', '-', 'q', '\'', 'i', 'j'], ['E', 'R', 'G', '3', 'S', '-', 'd', 'a', 'y'], [⟨['r', 'u'], ['E', 'R', 'G', '3', 'S'], none⟩, ⟨['q', '\'', 'i', 'j'], ['d', 'a', 'y'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "AF"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "kan qitzij"), ("complementizer", "chi"), ("resumptive", "focused")] }

def ex_56 : Datum :=
  { id := "hendersoncoon2018_56"
    source := ⟨"henderson-coon-2018", "(56)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike kan qitzij x-Ø-tij-o ri wäy?"
    glossedTokens := [("Achike", "who"), ("kan", "truly"), ("qitzij", "truth"), ("x-Ø-tij-o", "CPL-ABS3S-eat-AF"), ("ri", "the"), ("wäy", "tortilla")]
    glossedWords := [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o'], [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o'], none⟩]⟩, ⟨['k', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], [⟨['k', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], none⟩]⟩, ⟨['q', 'i', 't', 'z', 'i', 'j'], ['t', 'r', 'u', 't', 'h'], [⟨['q', 'i', 't', 'z', 'i', 'j'], ['t', 'r', 'u', 't', 'h'], none⟩]⟩, ⟨['x', '-', 'Ø', '-', 't', 'i', 'j', '-', 'o'], ['C', 'P', 'L', '-', 'A', 'B', 'S', '3', 'S', '-', 'e', 'a', 't', '-', 'A', 'F'], [⟨['x'], ['C', 'P', 'L'], none⟩, ⟨['Ø'], ['A', 'B', 'S', '3', 'S'], some '-'⟩, ⟨['t', 'i', 'j'], ['e', 'a', 't'], some '-'⟩, ⟨['o'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['w', 'ä', 'y'], ['t', 'o', 'r', 't', 'i', 'l', 'l', 'a'], [⟨['w', 'ä', 'y'], ['t', 'o', 'r', 't', 'i', 'l', 'l', 'a'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "AF"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "kan qitzij")] }

def ex_60a : Datum :=
  { id := "hendersoncoon2018_60a"
    source := ⟨"henderson-coon-2018", "(60a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike jantäq n-Ø-tij-o ri äk'."
    glossedTokens := [("Achike", "who/what"), ("jantäq", "sometimes"), ("n-Ø-tij-o", "ICPL-ABS3S-eat-AF"), ("ri", "the"), ("äk'", "chicken")]
    glossedWords := [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o', '/', 'w', 'h', 'a', 't'], [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o', '/', 'w', 'h', 'a', 't'], none⟩]⟩, ⟨['j', 'a', 'n', 't', 'ä', 'q'], ['s', 'o', 'm', 'e', 't', 'i', 'm', 'e', 's'], [⟨['j', 'a', 'n', 't', 'ä', 'q'], ['s', 'o', 'm', 'e', 't', 'i', 'm', 'e', 's'], none⟩]⟩, ⟨['n', '-', 'Ø', '-', 't', 'i', 'j', '-', 'o'], ['I', 'C', 'P', 'L', '-', 'A', 'B', 'S', '3', 'S', '-', 'e', 'a', 't', '-', 'A', 'F'], [⟨['n'], ['I', 'C', 'P', 'L'], none⟩, ⟨['Ø'], ['A', 'B', 'S', '3', 'S'], some '-'⟩, ⟨['t', 'i', 'j'], ['e', 'a', 't'], some '-'⟩, ⟨['o'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['ä', 'k', '\''], ['c', 'h', 'i', 'c', 'k', 'e', 'n'], [⟨['ä', 'k', '\''], ['c', 'h', 'i', 'c', 'k', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "AF"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "jantäq")] }

def ex_60b : Datum :=
  { id := "hendersoncoon2018_60b"
    source := ⟨"henderson-coon-2018", "(60b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike jantäq n-Ø-u-tij ri äk'."
    glossedTokens := [("Achike", "who/what"), ("jantäq", "sometimes"), ("n-Ø-u-tij", "ICPL-ABS3S-ERG3S-eat"), ("ri", "the"), ("äk'", "chicken")]
    glossedWords := [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o', '/', 'w', 'h', 'a', 't'], [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o', '/', 'w', 'h', 'a', 't'], none⟩]⟩, ⟨['j', 'a', 'n', 't', 'ä', 'q'], ['s', 'o', 'm', 'e', 't', 'i', 'm', 'e', 's'], [⟨['j', 'a', 'n', 't', 'ä', 'q'], ['s', 'o', 'm', 'e', 't', 'i', 'm', 'e', 's'], none⟩]⟩, ⟨['n', '-', 'Ø', '-', 'u', '-', 't', 'i', 'j'], ['I', 'C', 'P', 'L', '-', 'A', 'B', 'S', '3', 'S', '-', 'E', 'R', 'G', '3', 'S', '-', 'e', 'a', 't'], [⟨['n'], ['I', 'C', 'P', 'L'], none⟩, ⟨['Ø'], ['A', 'B', 'S', '3', 'S'], some '-'⟩, ⟨['u'], ['E', 'R', 'G', '3', 'S'], some '-'⟩, ⟨['t', 'i', 'j'], ['e', 'a', 't'], some '-'⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['ä', 'k', '\''], ['c', 'h', 'i', 'c', 'k', 'e', 'n'], [⟨['ä', 'k', '\''], ['c', 'h', 'i', 'c', 'k', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := [("subject extraction", .ungrammatical), ("object extraction", .acceptable)]
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "jantäq")] }

def ex_61a : Datum :=
  { id := "hendersoncoon2018_61a"
    source := ⟨"henderson-coon-2018", "(61a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike jumul n-Ø-tij-o ri äk'."
    glossedTokens := [("Achike", "who/what"), ("jumul", "always"), ("n-Ø-tij-o", "ICPL-ABS3S-eat-AF"), ("ri", "the"), ("äk'", "chicken")]
    glossedWords := [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o', '/', 'w', 'h', 'a', 't'], [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o', '/', 'w', 'h', 'a', 't'], none⟩]⟩, ⟨['j', 'u', 'm', 'u', 'l'], ['a', 'l', 'w', 'a', 'y', 's'], [⟨['j', 'u', 'm', 'u', 'l'], ['a', 'l', 'w', 'a', 'y', 's'], none⟩]⟩, ⟨['n', '-', 'Ø', '-', 't', 'i', 'j', '-', 'o'], ['I', 'C', 'P', 'L', '-', 'A', 'B', 'S', '3', 'S', '-', 'e', 'a', 't', '-', 'A', 'F'], [⟨['n'], ['I', 'C', 'P', 'L'], none⟩, ⟨['Ø'], ['A', 'B', 'S', '3', 'S'], some '-'⟩, ⟨['t', 'i', 'j'], ['e', 'a', 't'], some '-'⟩, ⟨['o'], ['A', 'F'], some '-'⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['ä', 'k', '\''], ['c', 'h', 'i', 'c', 'k', 'e', 'n'], [⟨['ä', 'k', '\''], ['c', 'h', 'i', 'c', 'k', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "AF"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "jumul")] }

def ex_61b : Datum :=
  { id := "hendersoncoon2018_61b"
    source := ⟨"henderson-coon-2018", "(61b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike jumul n-Ø-u-tij ri äk'."
    glossedTokens := [("Achike", "who/what"), ("jumul", "always"), ("n-Ø-u-tij", "ICPL-ABS3S-ERG3S-eat"), ("ri", "the"), ("äk'", "chicken")]
    glossedWords := [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o', '/', 'w', 'h', 'a', 't'], [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o', '/', 'w', 'h', 'a', 't'], none⟩]⟩, ⟨['j', 'u', 'm', 'u', 'l'], ['a', 'l', 'w', 'a', 'y', 's'], [⟨['j', 'u', 'm', 'u', 'l'], ['a', 'l', 'w', 'a', 'y', 's'], none⟩]⟩, ⟨['n', '-', 'Ø', '-', 'u', '-', 't', 'i', 'j'], ['I', 'C', 'P', 'L', '-', 'A', 'B', 'S', '3', 'S', '-', 'E', 'R', 'G', '3', 'S', '-', 'e', 'a', 't'], [⟨['n'], ['I', 'C', 'P', 'L'], none⟩, ⟨['Ø'], ['A', 'B', 'S', '3', 'S'], some '-'⟩, ⟨['u'], ['E', 'R', 'G', '3', 'S'], some '-'⟩, ⟨['t', 'i', 'j'], ['e', 'a', 't'], some '-'⟩]⟩, ⟨['r', 'i'], ['t', 'h', 'e'], [⟨['r', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['ä', 'k', '\''], ['c', 'h', 'i', 'c', 'k', 'e', 'n'], [⟨['ä', 'k', '\''], ['c', 'h', 'i', 'c', 'k', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := [("subject extraction", .ungrammatical), ("object extraction", .acceptable)]
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "jumul")] }

def ex_38 : Datum :=
  { id := "hendersoncoon2018_38"
    source := ⟨"henderson-coon-2018", "(38)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "K'a ri chi xi-Ø-k'achoj r-uma."
    glossedTokens := [("K'a ri", "then"), ("chi", "COMP"), ("xi-Ø-k'achoj", "CPL-ABS3S-cure"), ("r-uma", "ERG3S-RN.by")]
    glossedWords := [⟨['K', '\'', 'a', ' ', 'r', 'i'], ['t', 'h', 'e', 'n'], [⟨['K', '\'', 'a', ' ', 'r', 'i'], ['t', 'h', 'e', 'n'], none⟩]⟩, ⟨['c', 'h', 'i'], ['C', 'O', 'M', 'P'], [⟨['c', 'h', 'i'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['x', 'i', '-', 'Ø', '-', 'k', '\'', 'a', 'c', 'h', 'o', 'j'], ['C', 'P', 'L', '-', 'A', 'B', 'S', '3', 'S', '-', 'c', 'u', 'r', 'e'], [⟨['x', 'i'], ['C', 'P', 'L'], none⟩, ⟨['Ø'], ['A', 'B', 'S', '3', 'S'], some '-'⟩, ⟨['k', '\'', 'a', 'c', 'h', 'o', 'j'], ['c', 'u', 'r', 'e'], some '-'⟩]⟩, ⟨['r', '-', 'u', 'm', 'a'], ['E', 'R', 'G', '3', 'S', '-', 'R', 'N', '.', 'b', 'y'], [⟨['r'], ['E', 'R', 'G', '3', 'S'], none⟩, ⟨['u', 'm', 'a'], ['R', 'N', '.', 'b', 'y'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "embedding"), ("adverb", "k'a ri"), ("complement", "chi")] }

def ex_40 : Datum :=
  { id := "hendersoncoon2018_40"
    source := ⟨"henderson-coon-2018", "(40)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "... ma x-Ø-in-kusaj ta chuqa' ch'ab'el ri kan janipe' na ru-b'an-ik..."
    glossedTokens := [("ma", "NEG"), ("x-Ø-in-kusaj", "CPL-ABS3S-ERG1S-use"), ("ta", "IRR"), ("chuqa'", "also"), ("ch'ab'el", "speech"), ("ri", "REL"), ("kan", "truly"), ("janipe'", "how.much"), ("na", "PART"), ("ru-b'an-ik", "ERG3S-do-NML")]
    glossedWords := [⟨['m', 'a'], ['N', 'E', 'G'], [⟨['m', 'a'], ['N', 'E', 'G'], none⟩]⟩, ⟨['x', '-', 'Ø', '-', 'i', 'n', '-', 'k', 'u', 's', 'a', 'j'], ['C', 'P', 'L', '-', 'A', 'B', 'S', '3', 'S', '-', 'E', 'R', 'G', '1', 'S', '-', 'u', 's', 'e'], [⟨['x'], ['C', 'P', 'L'], none⟩, ⟨['Ø'], ['A', 'B', 'S', '3', 'S'], some '-'⟩, ⟨['i', 'n'], ['E', 'R', 'G', '1', 'S'], some '-'⟩, ⟨['k', 'u', 's', 'a', 'j'], ['u', 's', 'e'], some '-'⟩]⟩, ⟨['t', 'a'], ['I', 'R', 'R'], [⟨['t', 'a'], ['I', 'R', 'R'], none⟩]⟩, ⟨['c', 'h', 'u', 'q', 'a', '\''], ['a', 'l', 's', 'o'], [⟨['c', 'h', 'u', 'q', 'a', '\''], ['a', 'l', 's', 'o'], none⟩]⟩, ⟨['c', 'h', '\'', 'a', 'b', '\'', 'e', 'l'], ['s', 'p', 'e', 'e', 'c', 'h'], [⟨['c', 'h', '\'', 'a', 'b', '\'', 'e', 'l'], ['s', 'p', 'e', 'e', 'c', 'h'], none⟩]⟩, ⟨['r', 'i'], ['R', 'E', 'L'], [⟨['r', 'i'], ['R', 'E', 'L'], none⟩]⟩, ⟨['k', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], [⟨['k', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], none⟩]⟩, ⟨['j', 'a', 'n', 'i', 'p', 'e', '\''], ['h', 'o', 'w', '.', 'm', 'u', 'c', 'h'], [⟨['j', 'a', 'n', 'i', 'p', 'e', '\''], ['h', 'o', 'w', '.', 'm', 'u', 'c', 'h'], none⟩]⟩, ⟨['n', 'a'], ['P', 'A', 'R', 'T'], [⟨['n', 'a'], ['P', 'A', 'R', 'T'], none⟩]⟩, ⟨['r', 'u', '-', 'b', '\'', 'a', 'n', '-', 'i', 'k'], ['E', 'R', 'G', '3', 'S', '-', 'd', 'o', '-', 'N', 'M', 'L'], [⟨['r', 'u'], ['E', 'R', 'G', '3', 'S'], none⟩, ⟨['b', '\'', 'a', 'n'], ['d', 'o'], some '-'⟩, ⟨['i', 'k'], ['N', 'M', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "embedding"), ("adverb", "kan"), ("complement", "wh")] }

def ex_57 : Datum :=
  { id := "hendersoncoon2018_57"
    source := ⟨"henderson-coon-2018", "(57)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Kan qitzij chi x-a-samäj."
    glossedTokens := [("Kan", "truly"), ("qitzij", "truth"), ("chi", "COMP"), ("x-a-samäj", "CPL-ABS2S-work")]
    glossedWords := [⟨['K', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], [⟨['K', 'a', 'n'], ['t', 'r', 'u', 'l', 'y'], none⟩]⟩, ⟨['q', 'i', 't', 'z', 'i', 'j'], ['t', 'r', 'u', 't', 'h'], [⟨['q', 'i', 't', 'z', 'i', 'j'], ['t', 'r', 'u', 't', 'h'], none⟩]⟩, ⟨['c', 'h', 'i'], ['C', 'O', 'M', 'P'], [⟨['c', 'h', 'i'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['x', '-', 'a', '-', 's', 'a', 'm', 'ä', 'j'], ['C', 'P', 'L', '-', 'A', 'B', 'S', '2', 'S', '-', 'w', 'o', 'r', 'k'], [⟨['x'], ['C', 'P', 'L'], none⟩, ⟨['a'], ['A', 'B', 'S', '2', 'S'], some '-'⟩, ⟨['s', 'a', 'm', 'ä', 'j'], ['w', 'o', 'r', 'k'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "embedding"), ("adverb", "kan qitzij"), ("complement", "chi")] }

def ex_58 : Datum :=
  { id := "hendersoncoon2018_58"
    source := ⟨"henderson-coon-2018", "(58)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Jantäq chi x-a-samäj."
    glossedTokens := [("Jantäq", "sometimes"), ("chi", "COMP"), ("x-a-samäj", "CPL-ABS2S-work")]
    glossedWords := [⟨['J', 'a', 'n', 't', 'ä', 'q'], ['s', 'o', 'm', 'e', 't', 'i', 'm', 'e', 's'], [⟨['J', 'a', 'n', 't', 'ä', 'q'], ['s', 'o', 'm', 'e', 't', 'i', 'm', 'e', 's'], none⟩]⟩, ⟨['c', 'h', 'i'], ['C', 'O', 'M', 'P'], [⟨['c', 'h', 'i'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['x', '-', 'a', '-', 's', 'a', 'm', 'ä', 'j'], ['C', 'P', 'L', '-', 'A', 'B', 'S', '2', 'S', '-', 'w', 'o', 'r', 'k'], [⟨['x'], ['C', 'P', 'L'], none⟩, ⟨['a'], ['A', 'B', 'S', '2', 'S'], some '-'⟩, ⟨['s', 'a', 'm', 'ä', 'j'], ['w', 'o', 'r', 'k'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "embedding"), ("adverb", "jantäq"), ("complement", "chi")] }

def ex_59 : Datum :=
  { id := "hendersoncoon2018_59"
    source := ⟨"henderson-coon-2018", "(59)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Jumul chi x-a-samäj."
    glossedTokens := [("Jumul", "always"), ("chi", "COMP"), ("x-a-samäj", "CPL-ABS2S-work")]
    glossedWords := [⟨['J', 'u', 'm', 'u', 'l'], ['a', 'l', 'w', 'a', 'y', 's'], [⟨['J', 'u', 'm', 'u', 'l'], ['a', 'l', 'w', 'a', 'y', 's'], none⟩]⟩, ⟨['c', 'h', 'i'], ['C', 'O', 'M', 'P'], [⟨['c', 'h', 'i'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['x', '-', 'a', '-', 's', 'a', 'm', 'ä', 'j'], ['C', 'P', 'L', '-', 'A', 'B', 'S', '2', 'S', '-', 'w', 'o', 'r', 'k'], [⟨['x'], ['C', 'P', 'L'], none⟩, ⟨['a'], ['A', 'B', 'S', '2', 'S'], some '-'⟩, ⟨['s', 'a', 'm', 'ä', 'j'], ['w', 'o', 'r', 'k'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "embedding"), ("adverb", "jumul"), ("complement", "chi")] }

def all : List Datum := [ex_1, ex_2, ex_12a, ex_18a, ex_18b, ex_19, ex_20, ex_4, ex_5, ex_6, ex_24, ex_25, ex_27, ex_28, ex_29, ex_30, ex_31, ex_32, ex_33, ex_45, ex_46, ex_49, ex_50, ex_51, ex_56, ex_60a, ex_60b, ex_61a, ex_61b, ex_38, ex_40, ex_57, ex_58, ex_59]

end HendersonCoon2018.Examples
