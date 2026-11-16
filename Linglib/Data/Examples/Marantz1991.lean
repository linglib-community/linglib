module

public import Linglib.Data.Examples.Schema

/-!
# `Marantz1991` — typed example data

Auto-generated from `Linglib/Data/Examples/Marantz1991.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Marantz1991.Examples`.
-/

@[expose] public section

namespace Marantz1991.Examples

def m1991_1a : Datum :=
  { id := "m1991_1a"
    source := ⟨"marantz-1991", "(1a)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "vano pikr-ob-s mariḳaze."
    glossedTokens := [("vano", "Vano.NOM"), ("pikr-ob-s", "think-INFL.I"), ("mariḳaze", "Marika.on")]
    glossedWords := [⟨[['v', 'a', 'n', 'o']], [['V', 'a', 'n', 'o', '.', 'N', 'O', 'M']]⟩, ⟨[['p', 'i', 'k', 'r'], ['o', 'b'], ['s']], [['t', 'h', 'i', 'n', 'k'], ['I', 'N', 'F', 'L', '.', 'I']]⟩, ⟨[['m', 'a', 'r', 'i', 'ḳ', 'a', 'z', 'e']], [['M', 'a', 'r', 'i', 'k', 'a', '.', 'o', 'n']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unergative"), ("inflection", "I"), ("subject", "NOM")] }

def m1991_1b : Datum :=
  { id := "m1991_1b"
    source := ⟨"marantz-1991", "(1b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "vano-m i-pikr-a mariḳaze."
    glossedTokens := [("vano-m", "Vano-ERG"), ("i-pikr-a", "think-INFL.II"), ("mariḳaze", "Marika.on")]
    glossedWords := [⟨[['v', 'a', 'n', 'o'], ['m']], [['V', 'a', 'n', 'o'], ['E', 'R', 'G']]⟩, ⟨[['i'], ['p', 'i', 'k', 'r'], ['a']], [['t', 'h', 'i', 'n', 'k'], ['I', 'N', 'F', 'L', '.', 'I', 'I']]⟩, ⟨[['m', 'a', 'r', 'i', 'ḳ', 'a', 'z', 'e']], [['M', 'a', 'r', 'i', 'k', 'a', '.', 'o', 'n']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unergative"), ("inflection", "II"), ("subject", "ERG")] }

def m1991_1c : Datum :=
  { id := "m1991_1c"
    source := ⟨"marantz-1991", "(1c)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "nino gia-s surateb-s a-čven-eb-s."
    glossedTokens := [("nino", "Nino.NOM"), ("gia-s", "Gia-DAT"), ("surateb-s", "pictures-DAT"), ("a-čven-eb-s", "show-INFL.I")]
    glossedWords := [⟨[['n', 'i', 'n', 'o']], [['N', 'i', 'n', 'o', '.', 'N', 'O', 'M']]⟩, ⟨[['g', 'i', 'a'], ['s']], [['G', 'i', 'a'], ['D', 'A', 'T']]⟩, ⟨[['s', 'u', 'r', 'a', 't', 'e', 'b'], ['s']], [['p', 'i', 'c', 't', 'u', 'r', 'e', 's'], ['D', 'A', 'T']]⟩, ⟨[['a'], ['č', 'v', 'e', 'n'], ['e', 'b'], ['s']], [['s', 'h', 'o', 'w'], ['I', 'N', 'F', 'L', '.', 'I']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("inflection", "I"), ("subject", "NOM"), ("object", "DAT")] }

def m1991_1d : Datum :=
  { id := "m1991_1d"
    source := ⟨"marantz-1991", "(1d)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "nino-m gia-s surateb-i a-čven-a"
    glossedTokens := [("nino-m", "Nino-ERG"), ("gia-s", "Gia-DAT"), ("surateb-i", "pictures-NOM"), ("a-čven-a", "show-INFL.II")]
    glossedWords := [⟨[['n', 'i', 'n', 'o'], ['m']], [['N', 'i', 'n', 'o'], ['E', 'R', 'G']]⟩, ⟨[['g', 'i', 'a'], ['s']], [['G', 'i', 'a'], ['D', 'A', 'T']]⟩, ⟨[['s', 'u', 'r', 'a', 't', 'e', 'b'], ['i']], [['p', 'i', 'c', 't', 'u', 'r', 'e', 's'], ['N', 'O', 'M']]⟩, ⟨[['a'], ['č', 'v', 'e', 'n'], ['a']], [['s', 'h', 'o', 'w'], ['I', 'N', 'F', 'L', '.', 'I', 'I']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("inflection", "II"), ("subject", "ERG"), ("object", "NOM")] }

def m1991_2a : Datum :=
  { id := "m1991_2a"
    source := ⟨"marantz-1991", "(2a)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "es saxl-i ivane-s a=u-šendeb-a."
    glossedTokens := [("es", "this"), ("saxl-i", "house-NOM"), ("ivane-s", "Ivan-DAT"), ("a=u-šendeb-a", "PreV=built-INFL.I.3SG")]
    glossedWords := [⟨[['e', 's']], [['t', 'h', 'i', 's']]⟩, ⟨[['s', 'a', 'x', 'l'], ['i']], [['h', 'o', 'u', 's', 'e'], ['N', 'O', 'M']]⟩, ⟨[['i', 'v', 'a', 'n', 'e'], ['s']], [['I', 'v', 'a', 'n'], ['D', 'A', 'T']]⟩, ⟨[['a'], ['u'], ['š', 'e', 'n', 'd', 'e', 'b'], ['a']], [['P', 'r', 'e', 'V'], ['b', 'u', 'i', 'l', 't'], ['I', 'N', 'F', 'L', '.', 'I', '.', '3', 'S', 'G']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("inflection", "I"), ("subject", "NOM")] }

def m1991_2b : Datum :=
  { id := "m1991_2b"
    source := ⟨"marantz-1991", "(2b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "es saxl-i ivane-s a=u-šend-a."
    glossedTokens := [("es", "this"), ("saxl-i", "house-NOM"), ("ivane-s", "Ivan-DAT"), ("a=u-šend-a", "PreV=built-INFL.II.3SG")]
    glossedWords := [⟨[['e', 's']], [['t', 'h', 'i', 's']]⟩, ⟨[['s', 'a', 'x', 'l'], ['i']], [['h', 'o', 'u', 's', 'e'], ['N', 'O', 'M']]⟩, ⟨[['i', 'v', 'a', 'n', 'e'], ['s']], [['I', 'v', 'a', 'n'], ['D', 'A', 'T']]⟩, ⟨[['a'], ['u'], ['š', 'e', 'n', 'd'], ['a']], [['P', 'r', 'e', 'V'], ['b', 'u', 'i', 'l', 't'], ['I', 'N', 'F', 'L', '.', 'I', 'I', '.', '3', 'S', 'G']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("inflection", "II"), ("subject", "NOM")] }

def m1991_3a : Datum :=
  { id := "m1991_3a"
    source := ⟨"marantz-1991", "(3a)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "šen pelamuš-i g-i-qvar-s."
    glossedTokens := [("šen", "you.DAT"), ("pelamuš-i", "pelamusi-NOM"), ("g-i-qvar-s", "AGR-like-INFL.I")]
    glossedWords := [⟨[['š', 'e', 'n']], [['y', 'o', 'u', '.', 'D', 'A', 'T']]⟩, ⟨[['p', 'e', 'l', 'a', 'm', 'u', 'š'], ['i']], [['p', 'e', 'l', 'a', 'm', 'u', 's', 'i'], ['N', 'O', 'M']]⟩, ⟨[['g'], ['i'], ['q', 'v', 'a', 'r'], ['s']], [['A', 'G', 'R'], ['l', 'i', 'k', 'e'], ['I', 'N', 'F', 'L', '.', 'I']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "psych"), ("inflection", "I"), ("subject", "DAT"), ("object", "NOM")] }

def m1991_3b : Datum :=
  { id := "m1991_3b"
    source := ⟨"marantz-1991", "(3b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "šen pelamuš-i g-e-qvar-e."
    glossedTokens := [("šen", "you.DAT"), ("pelamuš-i", "pelamusi-NOM"), ("g-e-qvar-e", "AGR-like-INFL.II")]
    glossedWords := [⟨[['š', 'e', 'n']], [['y', 'o', 'u', '.', 'D', 'A', 'T']]⟩, ⟨[['p', 'e', 'l', 'a', 'm', 'u', 'š'], ['i']], [['p', 'e', 'l', 'a', 'm', 'u', 's', 'i'], ['N', 'O', 'M']]⟩, ⟨[['g'], ['e'], ['q', 'v', 'a', 'r'], ['e']], [['A', 'G', 'R'], ['l', 'i', 'k', 'e'], ['I', 'N', 'F', 'L', '.', 'I', 'I']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "psych"), ("inflection", "II"), ("subject", "DAT"), ("object", "NOM")] }

def m1991_4a : Datum :=
  { id := "m1991_4a"
    source := ⟨"marantz-1991", "(4a)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "siita aayii."
    glossedTokens := [("siita", "Sita.FEM"), ("aayii", "arrived/came-FEM")]
    glossedWords := [⟨[['s', 'i', 'i', 't', 'a']], [['S', 'i', 't', 'a', '.', 'F', 'E', 'M']]⟩, ⟨[['a', 'a', 'y', 'i', 'i']], [['a', 'r', 'r', 'i', 'v', 'e', 'd', '/', 'c', 'a', 'm', 'e'], ['F', 'E', 'M']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("inflection", "perfect"), ("subject", "NOM")] }

def m1991_4a_erg : Datum :=
  { id := "m1991_4a_erg"
    source := ⟨"marantz-1991", "(4a)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "siita ne aayii."
    glossedTokens := [("siita", "Sita.FEM"), ("ne", "ERG"), ("aayii", "arrived/came-FEM")]
    glossedWords := [⟨[['s', 'i', 'i', 't', 'a']], [['S', 'i', 't', 'a', '.', 'F', 'E', 'M']]⟩, ⟨[['n', 'e']], [['E', 'R', 'G']]⟩, ⟨[['a', 'a', 'y', 'i', 'i']], [['a', 'r', 'r', 'i', 'v', 'e', 'd', '/', 'c', 'a', 'm', 'e'], ['F', 'E', 'M']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("inflection", "perfect"), ("subject", "ERG")] }

def m1991_4b : Datum :=
  { id := "m1991_4b"
    source := ⟨"marantz-1991", "(4b)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "kutte bhoNke."
    glossedTokens := [("kutte", "dogs.MASC.PL"), ("bhoNke", "barked.MASC.PL")]
    glossedWords := [⟨[['k', 'u', 't', 't', 'e']], [['d', 'o', 'g', 's', '.', 'M', 'A', 'S', 'C', '.', 'P', 'L']]⟩, ⟨[['b', 'h', 'o', 'N', 'k', 'e']], [['b', 'a', 'r', 'k', 'e', 'd', '.', 'M', 'A', 'S', 'C', '.', 'P', 'L']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unergative"), ("inflection", "perfect"), ("subject", "NOM")] }

def m1991_4c : Datum :=
  { id := "m1991_4c"
    source := ⟨"marantz-1991", "(4c)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "kuttoN ne bhoNkaa."
    glossedTokens := [("kuttoN", "dogs.PL"), ("ne", "ERG"), ("bhoNkaa", "barked.MASC.SG")]
    glossedWords := [⟨[['k', 'u', 't', 't', 'o', 'N']], [['d', 'o', 'g', 's', '.', 'P', 'L']]⟩, ⟨[['n', 'e']], [['E', 'R', 'G']]⟩, ⟨[['b', 'h', 'o', 'N', 'k', 'a', 'a']], [['b', 'a', 'r', 'k', 'e', 'd', '.', 'M', 'A', 'S', 'C', '.', 'S', 'G']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unergative"), ("inflection", "perfect"), ("subject", "ERG")] }

def m1991_4d : Datum :=
  { id := "m1991_4d"
    source := ⟨"marantz-1991", "(4d)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "raam ne roTii khaayii thii."
    glossedTokens := [("raam", "Ram.MASC"), ("ne", "ERG"), ("roTii", "bread.FEM"), ("khaayii", "eat.FEM"), ("thii", "be.PAST.FEM")]
    glossedWords := [⟨[['r', 'a', 'a', 'm']], [['R', 'a', 'm', '.', 'M', 'A', 'S', 'C']]⟩, ⟨[['n', 'e']], [['E', 'R', 'G']]⟩, ⟨[['r', 'o', 'T', 'i', 'i']], [['b', 'r', 'e', 'a', 'd', '.', 'F', 'E', 'M']]⟩, ⟨[['k', 'h', 'a', 'a', 'y', 'i', 'i']], [['e', 'a', 't', '.', 'F', 'E', 'M']]⟩, ⟨[['t', 'h', 'i', 'i']], [['b', 'e', '.', 'P', 'A', 'S', 'T', '.', 'F', 'E', 'M']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("inflection", "perfect"), ("subject", "ERG"), ("object", "NOM")] }

def m1991_5a : Datum :=
  { id := "m1991_5a"
    source := ⟨"marantz-1991", "(5a)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "Ni etorri naiz."
    glossedTokens := [("Ni", "I.ABS"), ("etorri", "come"), ("naiz", "1SG.be")]
    glossedWords := [⟨[['N', 'i']], [['I', '.', 'A', 'B', 'S']]⟩, ⟨[['e', 't', 'o', 'r', 'r', 'i']], [['c', 'o', 'm', 'e']]⟩, ⟨[['n', 'a', 'i', 'z']], [['1', 'S', 'G', '.', 'b', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("subject", "ABS")] }

def m1991_5b : Datum :=
  { id := "m1991_5b"
    source := ⟨"marantz-1991", "(5b)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "Nik lan egin dut."
    glossedTokens := [("Nik", "I.ERG"), ("lan", "work"), ("egin", "do"), ("dut", "have.1SG")]
    glossedWords := [⟨[['N', 'i', 'k']], [['I', '.', 'E', 'R', 'G']]⟩, ⟨[['l', 'a', 'n']], [['w', 'o', 'r', 'k']]⟩, ⟨[['e', 'g', 'i', 'n']], [['d', 'o']]⟩, ⟨[['d', 'u', 't']], [['h', 'a', 'v', 'e', '.', '1', 'S', 'G']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unergative"), ("subject", "ERG")] }

def m1991_5c : Datum :=
  { id := "m1991_5c"
    source := ⟨"marantz-1991", "(5c)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "Nik libura ekarri dut."
    glossedTokens := [("Nik", "I.ERG"), ("libura", "book.ABS"), ("ekarri", "bought"), ("dut", "have.1SG")]
    glossedWords := [⟨[['N', 'i', 'k']], [['I', '.', 'E', 'R', 'G']]⟩, ⟨[['l', 'i', 'b', 'u', 'r', 'a']], [['b', 'o', 'o', 'k', '.', 'A', 'B', 'S']]⟩, ⟨[['e', 'k', 'a', 'r', 'r', 'i']], [['b', 'o', 'u', 'g', 'h', 't']]⟩, ⟨[['d', 'u', 't']], [['h', 'a', 'v', 'e', '.', '1', 'S', 'G']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("subject", "ERG"), ("object", "ABS")] }

def all : List Datum := [m1991_1a, m1991_1b, m1991_1c, m1991_1d, m1991_2a, m1991_2b, m1991_3a, m1991_3b, m1991_4a, m1991_4a_erg, m1991_4b, m1991_4c, m1991_4d, m1991_5a, m1991_5b, m1991_5c]

end Marantz1991.Examples
