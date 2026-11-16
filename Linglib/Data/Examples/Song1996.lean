module

public import Linglib.Data.Examples.Schema

/-!
# `Song1996` — typed example data

Auto-generated from `Linglib/Data/Examples/Song1996.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Song1996.Examples`.
-/

@[expose] public section

namespace Song1996.Examples

def ex_1b : Datum :=
  { id := "song1996_1b"
    source := ⟨"song-1996", "(1.b), p. 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The policewoman killed the terrorist."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauses", "one"), ("vcause", "fused")] }

def ex_6 : Datum :=
  { id := "song1996_6"
    source := ⟨"song-1996", "(6), p. 12"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The policewoman killed the terrorist, but he didn't die."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clauses", "one"), ("vcause", "fused"), ("effect", "negated")] }

def ex_2b : Datum :=
  { id := "song1996_2b"
    source := ⟨"song-1996", "(2.b), p. 3"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ali Hasan-ı öl-dür-dü"
    glossedTokens := [("Ali", "Ali"), ("Hasan-ı", "Hasan-DO"), ("öl-dür-dü", "die-CS-PST")]
    glossedWords := [⟨[['A', 'l', 'i']], [['A', 'l', 'i']]⟩, ⟨[['H', 'a', 's', 'a', 'n'], ['ı']], [['H', 'a', 's', 'a', 'n'], ['D', 'O']]⟩, ⟨[['ö', 'l'], ['d', 'ü', 'r'], ['d', 'ü']], [['d', 'i', 'e'], ['C', 'S'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauses", "one"), ("vcause", "bound")] }

def ex_3b : Datum :=
  { id := "song1996_3b"
    source := ⟨"song-1996", "(3.b), p. 3"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "kiho-ka cini-ka wus-ke ha-əss-ta"
    glossedTokens := [("kiho-ka", "Keeho-NOM"), ("cini-ka", "Jinee-NOM"), ("wus-ke", "smile-COMP"), ("ha-əss-ta", "cause-PST-IND")]
    glossedWords := [⟨[['k', 'i', 'h', 'o'], ['k', 'a']], [['K', 'e', 'e', 'h', 'o'], ['N', 'O', 'M']]⟩, ⟨[['c', 'i', 'n', 'i'], ['k', 'a']], [['J', 'i', 'n', 'e', 'e'], ['N', 'O', 'M']]⟩, ⟨[['w', 'u', 's'], ['k', 'e']], [['s', 'm', 'i', 'l', 'e'], ['C', 'O', 'M', 'P']]⟩, ⟨[['h', 'a'], ['ə', 's', 's'], ['t', 'a']], [['c', 'a', 'u', 's', 'e'], ['P', 'S', 'T'], ['I', 'N', 'D']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauses", "two"), ("link", "PURP"), ("order", "effect-cause")] }

def ex_4a : Datum :=
  { id := "song1996_4a"
    source := ⟨"song-1996", "(4.a), p. 5"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Hanako ga Ziroo o ik-ase-ta"
    glossedTokens := [("Hanako", "Hanako"), ("ga", "NOM"), ("Ziroo", "Ziroo"), ("o", "ACC"), ("ik-ase-ta", "go-CS-PST")]
    glossedWords := [⟨[['H', 'a', 'n', 'a', 'k', 'o']], [['H', 'a', 'n', 'a', 'k', 'o']]⟩, ⟨[['g', 'a']], [['N', 'O', 'M']]⟩, ⟨[['Z', 'i', 'r', 'o', 'o']], [['Z', 'i', 'r', 'o', 'o']]⟩, ⟨[['o']], [['A', 'C', 'C']]⟩, ⟨[['i', 'k'], ['a', 's', 'e'], ['t', 'a']], [['g', 'o'], ['C', 'S'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauses", "one"), ("vcause", "bound")] }

def ex_5 : Datum :=
  { id := "song1996_5"
    source := ⟨"song-1996", "(5), p. 10"⟩
    reportedIn := none
    language := "lako1244"
    primaryText := "ǹ gbā le yÒ-Ò lī"
    glossedTokens := [("ǹ", "I"), ("gbā", "speak"), ("le", "CONJ"), ("yÒ-Ò", "child-DEF"), ("lī", "eat")]
    glossedWords := [⟨[['ǹ']], [['I']]⟩, ⟨[['g', 'b', 'ā']], [['s', 'p', 'e', 'a', 'k']]⟩, ⟨[['l', 'e']], [['C', 'O', 'N', 'J']]⟩, ⟨[['y', 'Ò'], ['Ò']], [['c', 'h', 'i', 'l', 'd'], ['D', 'E', 'F']]⟩, ⟨[['l', 'ī']], [['e', 'a', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauses", "two"), ("link", "AND"), ("order", "cause-effect")] }

def ex_7 : Datum :=
  { id := "song1996_7"
    source := ⟨"song-1996", "(7), p. 13"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "kiho-ka cini-ka wus-ke ha-əss-ɨna cini-ka wus-ci=an-əss-ta"
    glossedTokens := [("kiho-ka", "Keeho-NOM"), ("cini-ka", "Jinee-NOM"), ("wus-ke", "smile-PURP"), ("ha-əss-ɨna", "cause-PST-but"), ("cini-ka", "Jinee-NOM"), ("wus-ci=an-əss-ta", "smile-NEG-PST-IND")]
    glossedWords := [⟨[['k', 'i', 'h', 'o'], ['k', 'a']], [['K', 'e', 'e', 'h', 'o'], ['N', 'O', 'M']]⟩, ⟨[['c', 'i', 'n', 'i'], ['k', 'a']], [['J', 'i', 'n', 'e', 'e'], ['N', 'O', 'M']]⟩, ⟨[['w', 'u', 's'], ['k', 'e']], [['s', 'm', 'i', 'l', 'e'], ['P', 'U', 'R', 'P']]⟩, ⟨[['h', 'a'], ['ə', 's', 's'], ['ɨ', 'n', 'a']], [['c', 'a', 'u', 's', 'e'], ['P', 'S', 'T'], ['b', 'u', 't']]⟩, ⟨[['c', 'i', 'n', 'i'], ['k', 'a']], [['J', 'i', 'n', 'e', 'e'], ['N', 'O', 'M']]⟩, ⟨[['w', 'u', 's'], ['c', 'i'], ['a', 'n'], ['ə', 's', 's'], ['t', 'a']], [['s', 'm', 'i', 'l', 'e'], ['N', 'E', 'G'], ['P', 'S', 'T'], ['I', 'N', 'D']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauses", "two"), ("link", "PURP"), ("order", "effect-cause"), ("effect", "negated")] }

def ex_24 : Datum :=
  { id := "song1996_24"
    source := ⟨"song-1996", "(24), p. 33"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Je ferai lire le livre à Nicole"
    glossedTokens := [("Je", "I"), ("ferai", "make + FUT"), ("lire", "read"), ("le", "the"), ("livre", "book (ACC)"), ("à", "DAT"), ("Nicole", "Nicole")]
    glossedWords := [⟨[['J', 'e']], [['I']]⟩, ⟨[['f', 'e', 'r', 'a', 'i']], [['m', 'a', 'k', 'e', ' ', '+', ' ', 'F', 'U', 'T']]⟩, ⟨[['l', 'i', 'r', 'e']], [['r', 'e', 'a', 'd']]⟩, ⟨[['l', 'e']], [['t', 'h', 'e']]⟩, ⟨[['l', 'i', 'v', 'r', 'e']], [['b', 'o', 'o', 'k', ' ', '(', 'A', 'C', 'C', ')']]⟩, ⟨[['à']], [['D', 'A', 'T']]⟩, ⟨[['N', 'i', 'c', 'o', 'l', 'e']], [['N', 'i', 'c', 'o', 'l', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauses", "one"), ("vcause", "free")] }

def ex_104 : Datum :=
  { id := "song1996_104"
    source := ⟨"song-1996", "(104), p. 68"⟩
    reportedIn := none
    language := "khmu1256"
    primaryText := "kə̀ə p-ŋ̀mɔ́ɔŋ nàa, nàa pə́ə mɔ́ɔŋ"
    glossedTokens := [("kə̀ə", "he"), ("p-ŋ̀mɔ́ɔŋ", "CP-sad"), ("nàa,", "she"), ("nàa", "she"), ("pə́ə", "not"), ("mɔ́ɔŋ", "sad")]
    glossedWords := [⟨[['k', 'ə', '̀', 'ə']], [['h', 'e']]⟩, ⟨[['p'], ['ŋ', '̀', 'm', 'ɔ', '́', 'ɔ', 'ŋ']], [['C', 'P'], ['s', 'a', 'd']]⟩, ⟨[['n', 'à', 'a']], [['s', 'h', 'e']]⟩, ⟨[['n', 'à', 'a']], [['s', 'h', 'e']]⟩, ⟨[['p', 'ə', '́', 'ə']], [['n', 'o', 't']]⟩, ⟨[['m', 'ɔ', '́', 'ɔ', 'ŋ']], [['s', 'a', 'd']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauses", "one"), ("vcause", "bound"), ("effect", "negated")] }

def ch4_1a : Datum :=
  { id := "song1996_ch4_1a"
    source := ⟨"song-1996", "ch. 4 (1.a)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "kiho-ka ka-əss-ta"
    glossedTokens := [("kiho-ka", "Keeho-NOM"), ("ka-əss-ta", "go-PST-IND")]
    glossedWords := [⟨[['k', 'i', 'h', 'o'], ['k', 'a']], [['K', 'e', 'e', 'h', 'o'], ['N', 'O', 'M']]⟩, ⟨[['k', 'a'], ['ə', 's', 's'], ['t', 'a']], [['g', 'o'], ['P', 'S', 'T'], ['I', 'N', 'D']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "basic")] }

def ch4_1b : Datum :=
  { id := "song1996_ch4_1b"
    source := ⟨"song-1996", "ch. 4 (1.b)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "əməni-ka kiho-lɨl ponɛ-əss-ta"
    glossedTokens := [("əməni-ka", "mother-NOM"), ("kiho-lɨl", "Keeho-ACC"), ("ponɛ-əss-ta", "send-PST-IND")]
    glossedWords := [⟨[['ə', 'm', 'ə', 'n', 'i'], ['k', 'a']], [['m', 'o', 't', 'h', 'e', 'r'], ['N', 'O', 'M']]⟩, ⟨[['k', 'i', 'h', 'o'], ['l', 'ɨ', 'l']], [['K', 'e', 'e', 'h', 'o'], ['A', 'C', 'C']]⟩, ⟨[['p', 'o', 'n', 'ɛ'], ['ə', 's', 's'], ['t', 'a']], [['s', 'e', 'n', 'd'], ['P', 'S', 'T'], ['I', 'N', 'D']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "lexical causative"), ("clauses", "one"), ("vcause", "fused")] }

def ch4_2a : Datum :=
  { id := "song1996_ch4_2a"
    source := ⟨"song-1996", "ch. 4 (2.a)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "cini-ka wus-əss-ta"
    glossedTokens := [("cini-ka", "Jinee-NOM"), ("wus-əss-ta", "smile-PST-IND")]
    glossedWords := [⟨[['c', 'i', 'n', 'i'], ['k', 'a']], [['J', 'i', 'n', 'e', 'e'], ['N', 'O', 'M']]⟩, ⟨[['w', 'u', 's'], ['ə', 's', 's'], ['t', 'a']], [['s', 'm', 'i', 'l', 'e'], ['P', 'S', 'T'], ['I', 'N', 'D']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "basic")] }

def ch4_2b : Datum :=
  { id := "song1996_ch4_2b"
    source := ⟨"song-1996", "ch. 4 (2.b)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "kiho-ka cini-lɨl wus-I-əss-ta"
    glossedTokens := [("kiho-ka", "Keeho-NOM"), ("cini-lɨl", "Jinee-ACC"), ("wus-I-əss-ta", "smile-CS-PST-IND")]
    glossedWords := [⟨[['k', 'i', 'h', 'o'], ['k', 'a']], [['K', 'e', 'e', 'h', 'o'], ['N', 'O', 'M']]⟩, ⟨[['c', 'i', 'n', 'i'], ['l', 'ɨ', 'l']], [['J', 'i', 'n', 'e', 'e'], ['A', 'C', 'C']]⟩, ⟨[['w', 'u', 's'], ['I'], ['ə', 's', 's'], ['t', 'a']], [['s', 'm', 'i', 'l', 'e'], ['C', 'S'], ['P', 'S', 'T'], ['I', 'N', 'D']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "morphological causative"), ("clauses", "one"), ("vcause", "bound"), ("causee", "ACC")] }

def ch4_3 : Datum :=
  { id := "song1996_ch4_3"
    source := ⟨"song-1996", "ch. 4 (3)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "kiho-ka cini-eke kwail cɨp-ɨl masi-ke ha-əss-ta"
    glossedTokens := [("kiho-ka", "Keeho-NOM"), ("cini-eke", "Jinee-DAT"), ("kwail", "fruit"), ("cɨp-ɨl", "juice-ACC"), ("masi-ke", "drink-PURP"), ("ha-əss-ta", "do-PST-IND")]
    glossedWords := [⟨[['k', 'i', 'h', 'o'], ['k', 'a']], [['K', 'e', 'e', 'h', 'o'], ['N', 'O', 'M']]⟩, ⟨[['c', 'i', 'n', 'i'], ['e', 'k', 'e']], [['J', 'i', 'n', 'e', 'e'], ['D', 'A', 'T']]⟩, ⟨[['k', 'w', 'a', 'i', 'l']], [['f', 'r', 'u', 'i', 't']]⟩, ⟨[['c', 'ɨ', 'p'], ['ɨ', 'l']], [['j', 'u', 'i', 'c', 'e'], ['A', 'C', 'C']]⟩, ⟨[['m', 'a', 's', 'i'], ['k', 'e']], [['d', 'r', 'i', 'n', 'k'], ['P', 'U', 'R', 'P']]⟩, ⟨[['h', 'a'], ['ə', 's', 's'], ['t', 'a']], [['d', 'o'], ['P', 'S', 'T'], ['I', 'N', 'D']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "PURP causative"), ("clauses", "two"), ("link", "PURP"), ("order", "effect-cause"), ("causee", "DAT")] }

def ch4_4 : Datum :=
  { id := "song1996_ch4_4"
    source := ⟨"song-1996", "ch. 4 (4)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "kiho-ka cini-ka pathi-e o-ke kɨnyə-ɨi cip-e cənhwa-lɨl kəl-əss-ta"
    glossedTokens := [("kiho-ka", "Keeho-NOM"), ("cini-ka", "Jinee-NOM"), ("pathi-e", "party-LOC"), ("o-ke", "come-PURP"), ("kɨnyə-ɨi", "she-GEN"), ("cip-e", "home-LOC"), ("cənhwa-lɨl", "phone-ACC"), ("kəl-əss-ta", "dial-PST-IND")]
    glossedWords := [⟨[['k', 'i', 'h', 'o'], ['k', 'a']], [['K', 'e', 'e', 'h', 'o'], ['N', 'O', 'M']]⟩, ⟨[['c', 'i', 'n', 'i'], ['k', 'a']], [['J', 'i', 'n', 'e', 'e'], ['N', 'O', 'M']]⟩, ⟨[['p', 'a', 't', 'h', 'i'], ['e']], [['p', 'a', 'r', 't', 'y'], ['L', 'O', 'C']]⟩, ⟨[['o'], ['k', 'e']], [['c', 'o', 'm', 'e'], ['P', 'U', 'R', 'P']]⟩, ⟨[['k', 'ɨ', 'n', 'y', 'ə'], ['ɨ', 'i']], [['s', 'h', 'e'], ['G', 'E', 'N']]⟩, ⟨[['c', 'i', 'p'], ['e']], [['h', 'o', 'm', 'e'], ['L', 'O', 'C']]⟩, ⟨[['c', 'ə', 'n', 'h', 'w', 'a'], ['l', 'ɨ', 'l']], [['p', 'h', 'o', 'n', 'e'], ['A', 'C', 'C']]⟩, ⟨[['k', 'ə', 'l'], ['ə', 's', 's'], ['t', 'a']], [['d', 'i', 'a', 'l'], ['P', 'S', 'T'], ['I', 'N', 'D']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "purposive"), ("subject", "NOM")] }

def ch4_5 : Datum :=
  { id := "song1996_ch4_5"
    source := ⟨"song-1996", "ch. 4 (5)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "kiho-ka cini-ka kwail cɨp-ɨl masi-ke ha-əss-ta"
    glossedTokens := [("kiho-ka", "Keeho-NOM"), ("cini-ka", "Jinee-NOM"), ("kwail", "fruit"), ("cɨp-ɨl", "juice-ACC"), ("masi-ke", "drink-PURP"), ("ha-əss-ta", "do-PST-IND")]
    glossedWords := [⟨[['k', 'i', 'h', 'o'], ['k', 'a']], [['K', 'e', 'e', 'h', 'o'], ['N', 'O', 'M']]⟩, ⟨[['c', 'i', 'n', 'i'], ['k', 'a']], [['J', 'i', 'n', 'e', 'e'], ['N', 'O', 'M']]⟩, ⟨[['k', 'w', 'a', 'i', 'l']], [['f', 'r', 'u', 'i', 't']]⟩, ⟨[['c', 'ɨ', 'p'], ['ɨ', 'l']], [['j', 'u', 'i', 'c', 'e'], ['A', 'C', 'C']]⟩, ⟨[['m', 'a', 's', 'i'], ['k', 'e']], [['d', 'r', 'i', 'n', 'k'], ['P', 'U', 'R', 'P']]⟩, ⟨[['h', 'a'], ['ə', 's', 's'], ['t', 'a']], [['d', 'o'], ['P', 'S', 'T'], ['I', 'N', 'D']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := [("kiho-ka cini-ka kwail cɨp-ɨl masi-ke-lɨl ha-əss-ta", .acceptable)]
    readings := []
    paperFeatures := [("construction", "complement causative"), ("clauses", "two"), ("link", "PURP"), ("order", "effect-cause"), ("causee", "NOM")] }

def ch4_6 : Datum :=
  { id := "song1996_ch4_6"
    source := ⟨"song-1996", "ch. 4 (6)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "kiho-ka ha-əss-ta"
    glossedTokens := [("kiho-ka", "Keeho-NOM"), ("ha-əss-ta", "do-PST-IND")]
    glossedWords := [⟨[['k', 'i', 'h', 'o'], ['k', 'a']], [['K', 'e', 'e', 'h', 'o'], ['N', 'O', 'M']]⟩, ⟨[['h', 'a'], ['ə', 's', 's'], ['t', 'a']], [['d', 'o'], ['P', 'S', 'T'], ['I', 'N', 'D']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "PURP causative"), ("clause", "omitted")] }

def ch4_7 : Datum :=
  { id := "song1996_ch4_7"
    source := ⟨"song-1996", "ch. 4 (7)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "kiho-ka kɨnyə-ɨi cip-e cənhwa-lɨl kəl-əss-ta"
    glossedTokens := [("kiho-ka", "Keeho-NOM"), ("kɨnyə-ɨi", "she-GEN"), ("cip-e", "home-LOC"), ("cənhwa-lɨl", "phone-ACC"), ("kəl-əss-ta", "dial-PST-IND")]
    glossedWords := [⟨[['k', 'i', 'h', 'o'], ['k', 'a']], [['K', 'e', 'e', 'h', 'o'], ['N', 'O', 'M']]⟩, ⟨[['k', 'ɨ', 'n', 'y', 'ə'], ['ɨ', 'i']], [['s', 'h', 'e'], ['G', 'E', 'N']]⟩, ⟨[['c', 'i', 'p'], ['e']], [['h', 'o', 'm', 'e'], ['L', 'O', 'C']]⟩, ⟨[['c', 'ə', 'n', 'h', 'w', 'a'], ['l', 'ɨ', 'l']], [['p', 'h', 'o', 'n', 'e'], ['A', 'C', 'C']]⟩, ⟨[['k', 'ə', 'l'], ['ə', 's', 's'], ['t', 'a']], [['d', 'i', 'a', 'l'], ['P', 'S', 'T'], ['I', 'N', 'D']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "purposive"), ("clause", "omitted")] }

def ch4_8 : Datum :=
  { id := "song1996_ch4_8"
    source := ⟨"song-1996", "ch. 4 (8)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "kiho-ka cini-lɨl kwail cɨp-ɨl masi-ke ha-əss-ta"
    glossedTokens := [("kiho-ka", "Keeho-NOM"), ("cini-lɨl", "Jinee-ACC"), ("kwail", "fruit"), ("cɨp-ɨl", "juice-ACC"), ("masi-ke", "drink-PURP"), ("ha-əss-ta", "do-PST-IND")]
    glossedWords := [⟨[['k', 'i', 'h', 'o'], ['k', 'a']], [['K', 'e', 'e', 'h', 'o'], ['N', 'O', 'M']]⟩, ⟨[['c', 'i', 'n', 'i'], ['l', 'ɨ', 'l']], [['J', 'i', 'n', 'e', 'e'], ['A', 'C', 'C']]⟩, ⟨[['k', 'w', 'a', 'i', 'l']], [['f', 'r', 'u', 'i', 't']]⟩, ⟨[['c', 'ɨ', 'p'], ['ɨ', 'l']], [['j', 'u', 'i', 'c', 'e'], ['A', 'C', 'C']]⟩, ⟨[['m', 'a', 's', 'i'], ['k', 'e']], [['d', 'r', 'i', 'n', 'k'], ['P', 'U', 'R', 'P']]⟩, ⟨[['h', 'a'], ['ə', 's', 's'], ['t', 'a']], [['d', 'o'], ['P', 'S', 'T'], ['I', 'N', 'D']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "PURP causative"), ("clauses", "two"), ("link", "PURP"), ("order", "effect-cause"), ("causee", "ACC")] }

def ch4_9_acc : Datum :=
  { id := "song1996_ch4_9_acc"
    source := ⟨"song-1996", "ch. 4 (9)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "kiho-ka cini-lɨl pathi-e o-ke kɨnyə-ɨi cip-e cənhwa-lɨl kəl-əss-ta"
    glossedTokens := [("kiho-ka", "Keeho-NOM"), ("cini-lɨl", "Jinee-ACC"), ("pathi-e", "party-LOC"), ("o-ke", "come-PURP"), ("kɨnyə-ɨi", "she-GEN"), ("cip-e", "home-LOC"), ("cənhwa-lɨl", "phone-ACC"), ("kəl-əss-ta", "dial-PST-IND")]
    glossedWords := [⟨[['k', 'i', 'h', 'o'], ['k', 'a']], [['K', 'e', 'e', 'h', 'o'], ['N', 'O', 'M']]⟩, ⟨[['c', 'i', 'n', 'i'], ['l', 'ɨ', 'l']], [['J', 'i', 'n', 'e', 'e'], ['A', 'C', 'C']]⟩, ⟨[['p', 'a', 't', 'h', 'i'], ['e']], [['p', 'a', 'r', 't', 'y'], ['L', 'O', 'C']]⟩, ⟨[['o'], ['k', 'e']], [['c', 'o', 'm', 'e'], ['P', 'U', 'R', 'P']]⟩, ⟨[['k', 'ɨ', 'n', 'y', 'ə'], ['ɨ', 'i']], [['s', 'h', 'e'], ['G', 'E', 'N']]⟩, ⟨[['c', 'i', 'p'], ['e']], [['h', 'o', 'm', 'e'], ['L', 'O', 'C']]⟩, ⟨[['c', 'ə', 'n', 'h', 'w', 'a'], ['l', 'ɨ', 'l']], [['p', 'h', 'o', 'n', 'e'], ['A', 'C', 'C']]⟩, ⟨[['k', 'ə', 'l'], ['ə', 's', 's'], ['t', 'a']], [['d', 'i', 'a', 'l'], ['P', 'S', 'T'], ['I', 'N', 'D']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "purposive"), ("subject", "ACC")] }

def ch4_9_dat : Datum :=
  { id := "song1996_ch4_9_dat"
    source := ⟨"song-1996", "ch. 4 (9)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "kiho-ka cini-eke pathi-e o-ke kɨnyə-ɨi cip-e cənhwa-lɨl kəl-əss-ta"
    glossedTokens := [("kiho-ka", "Keeho-NOM"), ("cini-eke", "Jinee-DAT"), ("pathi-e", "party-LOC"), ("o-ke", "come-PURP"), ("kɨnyə-ɨi", "she-GEN"), ("cip-e", "home-LOC"), ("cənhwa-lɨl", "phone-ACC"), ("kəl-əss-ta", "dial-PST-IND")]
    glossedWords := [⟨[['k', 'i', 'h', 'o'], ['k', 'a']], [['K', 'e', 'e', 'h', 'o'], ['N', 'O', 'M']]⟩, ⟨[['c', 'i', 'n', 'i'], ['e', 'k', 'e']], [['J', 'i', 'n', 'e', 'e'], ['D', 'A', 'T']]⟩, ⟨[['p', 'a', 't', 'h', 'i'], ['e']], [['p', 'a', 'r', 't', 'y'], ['L', 'O', 'C']]⟩, ⟨[['o'], ['k', 'e']], [['c', 'o', 'm', 'e'], ['P', 'U', 'R', 'P']]⟩, ⟨[['k', 'ɨ', 'n', 'y', 'ə'], ['ɨ', 'i']], [['s', 'h', 'e'], ['G', 'E', 'N']]⟩, ⟨[['c', 'i', 'p'], ['e']], [['h', 'o', 'm', 'e'], ['L', 'O', 'C']]⟩, ⟨[['c', 'ə', 'n', 'h', 'w', 'a'], ['l', 'ɨ', 'l']], [['p', 'h', 'o', 'n', 'e'], ['A', 'C', 'C']]⟩, ⟨[['k', 'ə', 'l'], ['ə', 's', 's'], ['t', 'a']], [['d', 'i', 'a', 'l'], ['P', 'S', 'T'], ['I', 'N', 'D']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "purposive"), ("subject", "DAT")] }

def ch4_10 : Datum :=
  { id := "song1996_ch4_10"
    source := ⟨"song-1996", "ch. 4 (10)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "kiho-ka cini-ka kwail cɨp-ɨl masi-ke kəcismal-ɨl ha-əss-ta"
    glossedTokens := [("kiho-ka", "Keeho-NOM"), ("cini-ka", "Jinee-NOM"), ("kwail", "fruit"), ("cɨp-ɨl", "juice-ACC"), ("masi-ke", "drink-PURP"), ("kəcismal-ɨl", "lie-ACC"), ("ha-əss-ta", "do-PST-IND")]
    glossedWords := [⟨[['k', 'i', 'h', 'o'], ['k', 'a']], [['K', 'e', 'e', 'h', 'o'], ['N', 'O', 'M']]⟩, ⟨[['c', 'i', 'n', 'i'], ['k', 'a']], [['J', 'i', 'n', 'e', 'e'], ['N', 'O', 'M']]⟩, ⟨[['k', 'w', 'a', 'i', 'l']], [['f', 'r', 'u', 'i', 't']]⟩, ⟨[['c', 'ɨ', 'p'], ['ɨ', 'l']], [['j', 'u', 'i', 'c', 'e'], ['A', 'C', 'C']]⟩, ⟨[['m', 'a', 's', 'i'], ['k', 'e']], [['d', 'r', 'i', 'n', 'k'], ['P', 'U', 'R', 'P']]⟩, ⟨[['k', 'ə', 'c', 'i', 's', 'm', 'a', 'l'], ['ɨ', 'l']], [['l', 'i', 'e'], ['A', 'C', 'C']]⟩, ⟨[['h', 'a'], ['ə', 's', 's'], ['t', 'a']], [['d', 'o'], ['P', 'S', 'T'], ['I', 'N', 'D']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "purposive"), ("subject", "NOM")] }

def ch4_11_acc : Datum :=
  { id := "song1996_ch4_11_acc"
    source := ⟨"song-1996", "ch. 4 (11)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "kɨ-ka na-lɨl kimchi-lɨl mək-ke ha-əss-ɨna nɛ-ka ani mək-əss-ta"
    glossedTokens := [("kɨ-ka", "he-NOM"), ("na-lɨl", "I-ACC"), ("kimchi-lɨl", "pickle-ACC"), ("mək-ke", "eat-PURP"), ("ha-əss-ɨna", "do-PST-but"), ("nɛ-ka", "I-NOM"), ("ani", "NEG"), ("mək-əss-ta", "eat-PST-IND")]
    glossedWords := [⟨[['k', 'ɨ'], ['k', 'a']], [['h', 'e'], ['N', 'O', 'M']]⟩, ⟨[['n', 'a'], ['l', 'ɨ', 'l']], [['I'], ['A', 'C', 'C']]⟩, ⟨[['k', 'i', 'm', 'c', 'h', 'i'], ['l', 'ɨ', 'l']], [['p', 'i', 'c', 'k', 'l', 'e'], ['A', 'C', 'C']]⟩, ⟨[['m', 'ə', 'k'], ['k', 'e']], [['e', 'a', 't'], ['P', 'U', 'R', 'P']]⟩, ⟨[['h', 'a'], ['ə', 's', 's'], ['ɨ', 'n', 'a']], [['d', 'o'], ['P', 'S', 'T'], ['b', 'u', 't']]⟩, ⟨[['n', 'ɛ'], ['k', 'a']], [['I'], ['N', 'O', 'M']]⟩, ⟨[['a', 'n', 'i']], [['N', 'E', 'G']]⟩, ⟨[['m', 'ə', 'k'], ['ə', 's', 's'], ['t', 'a']], [['e', 'a', 't'], ['P', 'S', 'T'], ['I', 'N', 'D']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := [("kɨ-ka na-lɨl kimchi-lɨl mək-ke ha-əss-ɨna nɛ-ka kimchi-lɨl ani mək-əss-ta", .acceptable)]
    readings := []
    paperFeatures := [("construction", "PURP causative"), ("clauses", "two"), ("link", "PURP"), ("order", "effect-cause"), ("effect", "negated"), ("causee", "ACC")] }

def ch4_11_dat : Datum :=
  { id := "song1996_ch4_11_dat"
    source := ⟨"song-1996", "ch. 4 (11)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "kɨ-ka na-eke kimchi-lɨl mək-ke ha-əss-ɨna nɛ-ka ani mək-əss-ta"
    glossedTokens := [("kɨ-ka", "he-NOM"), ("na-eke", "I-DAT"), ("kimchi-lɨl", "pickle-ACC"), ("mək-ke", "eat-PURP"), ("ha-əss-ɨna", "do-PST-but"), ("nɛ-ka", "I-NOM"), ("ani", "NEG"), ("mək-əss-ta", "eat-PST-IND")]
    glossedWords := [⟨[['k', 'ɨ'], ['k', 'a']], [['h', 'e'], ['N', 'O', 'M']]⟩, ⟨[['n', 'a'], ['e', 'k', 'e']], [['I'], ['D', 'A', 'T']]⟩, ⟨[['k', 'i', 'm', 'c', 'h', 'i'], ['l', 'ɨ', 'l']], [['p', 'i', 'c', 'k', 'l', 'e'], ['A', 'C', 'C']]⟩, ⟨[['m', 'ə', 'k'], ['k', 'e']], [['e', 'a', 't'], ['P', 'U', 'R', 'P']]⟩, ⟨[['h', 'a'], ['ə', 's', 's'], ['ɨ', 'n', 'a']], [['d', 'o'], ['P', 'S', 'T'], ['b', 'u', 't']]⟩, ⟨[['n', 'ɛ'], ['k', 'a']], [['I'], ['N', 'O', 'M']]⟩, ⟨[['a', 'n', 'i']], [['N', 'E', 'G']]⟩, ⟨[['m', 'ə', 'k'], ['ə', 's', 's'], ['t', 'a']], [['e', 'a', 't'], ['P', 'S', 'T'], ['I', 'N', 'D']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := [("kɨ-ka na-eke kimchi-lɨl mək-ke ha-əss-ɨna nɛ-ka kimchi-lɨl ani mək-əss-ta", .acceptable)]
    readings := []
    paperFeatures := [("construction", "PURP causative"), ("clauses", "two"), ("link", "PURP"), ("order", "effect-cause"), ("effect", "negated"), ("causee", "DAT")] }

def all : List Datum := [ex_1b, ex_6, ex_2b, ex_3b, ex_4a, ex_5, ex_7, ex_24, ex_104, ch4_1a, ch4_1b, ch4_2a, ch4_2b, ch4_3, ch4_4, ch4_5, ch4_6, ch4_7, ch4_8, ch4_9_acc, ch4_9_dat, ch4_10, ch4_11_acc, ch4_11_dat]

end Song1996.Examples
