module

public import Linglib.Data.Examples.Schema

/-!
# `Gong2022` — typed example data

Auto-generated from `Linglib/Data/Examples/Gong2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Gong2022.Examples`.
-/

@[expose] public section

namespace Gong2022.Examples

def ex_18b : Datum :=
  { id := "gong2022_18b"
    source := ⟨"gong-2022", "(18b)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "Bagš [Čemeg-in nom-ig] tüün-d ög-sön."
    glossedTokens := [("Bagš", "teacher.NOM"), ("Čemeg-in", "Čemeg-GEN"), ("nom-ig", "book-ACC"), ("tüün-d", "3SG-DAT"), ("ög-sön", "give-PST")]
    glossedWords := [⟨[['B', 'a', 'g', 'š']], [['t', 'e', 'a', 'c', 'h', 'e', 'r', '.', 'N', 'O', 'M']]⟩, ⟨[['Č', 'e', 'm', 'e', 'g'], ['i', 'n']], [['Č', 'e', 'm', 'e', 'g'], ['G', 'E', 'N']]⟩, ⟨[['n', 'o', 'm'], ['i', 'g']], [['b', 'o', 'o', 'k'], ['A', 'C', 'C']]⟩, ⟨[['t', 'ü', 'ü', 'n'], ['d']], [['3', 'S', 'G'], ['D', 'A', 'T']]⟩, ⟨[['ö', 'g'], ['s', 'ö', 'n']], [['g', 'i', 'v', 'e'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "SS"), ("binder", "IO"), ("mover", "DP")] }

def ex_19b : Datum :=
  { id := "gong2022_19b"
    source := ⟨"gong-2022", "(19b)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "[Čemeg-in nom-ig] bagš tüün-d ög-sön."
    glossedTokens := [("Čemeg-in", "Čemeg-GEN"), ("nom-ig", "book-ACC"), ("bagš", "teacher.NOM"), ("tüün-d", "3SG-DAT"), ("ög-sön", "give-PST")]
    glossedWords := [⟨[['Č', 'e', 'm', 'e', 'g'], ['i', 'n']], [['Č', 'e', 'm', 'e', 'g'], ['G', 'E', 'N']]⟩, ⟨[['n', 'o', 'm'], ['i', 'g']], [['b', 'o', 'o', 'k'], ['A', 'C', 'C']]⟩, ⟨[['b', 'a', 'g', 'š']], [['t', 'e', 'a', 'c', 'h', 'e', 'r', '.', 'N', 'O', 'M']]⟩, ⟨[['t', 'ü', 'ü', 'n'], ['d']], [['3', 'S', 'G'], ['D', 'A', 'T']]⟩, ⟨[['ö', 'g'], ['s', 'ö', 'n']], [['g', 'i', 'v', 'e'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "IS"), ("binder", "IO"), ("mover", "DP")] }

def ex_20b : Datum :=
  { id := "gong2022_20b"
    source := ⟨"gong-2022", "(20b)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "[Čemeg-in nom-ig] ter ura-san."
    glossedTokens := [("Čemeg-in", "Čemeg-GEN"), ("nom-ig", "book-ACC"), ("ter", "3SG.NOM"), ("ura-san", "tear-PST")]
    glossedWords := [⟨[['Č', 'e', 'm', 'e', 'g'], ['i', 'n']], [['Č', 'e', 'm', 'e', 'g'], ['G', 'E', 'N']]⟩, ⟨[['n', 'o', 'm'], ['i', 'g']], [['b', 'o', 'o', 'k'], ['A', 'C', 'C']]⟩, ⟨[['t', 'e', 'r']], [['3', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['u', 'r', 'a'], ['s', 'a', 'n']], [['t', 'e', 'a', 'r'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "IS"), ("binder", "subject"), ("mover", "DP")] }

def ex_21b : Datum :=
  { id := "gong2022_21b"
    source := ⟨"gong-2022", "(21b)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "[Čemeg-in nom-ig] ter Bat-ad ög-sön."
    glossedTokens := [("Čemeg-in", "Čemeg-GEN"), ("nom-ig", "book-ACC"), ("ter", "3SG.NOM"), ("Bat-ad", "Bat-DAT"), ("ög-sön", "give-PST")]
    glossedWords := [⟨[['Č', 'e', 'm', 'e', 'g'], ['i', 'n']], [['Č', 'e', 'm', 'e', 'g'], ['G', 'E', 'N']]⟩, ⟨[['n', 'o', 'm'], ['i', 'g']], [['b', 'o', 'o', 'k'], ['A', 'C', 'C']]⟩, ⟨[['t', 'e', 'r']], [['3', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['B', 'a', 't'], ['a', 'd']], [['B', 'a', 't'], ['D', 'A', 'T']]⟩, ⟨[['ö', 'g'], ['s', 'ö', 'n']], [['g', 'i', 'v', 'e'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "IS"), ("binder", "subject"), ("mover", "DP")] }

def ex_32b : Datum :=
  { id := "gong2022_32b"
    source := ⟨"gong-2022", "(32b)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "[Bat-in eej-iig] bi tüün-d [sain khün gej] khel-sen."
    glossedTokens := [("Bat-in", "Bat-GEN"), ("eej-iig", "mother-ACC"), ("bi", "1SG.NOM"), ("tüün-d", "3SG-DAT"), ("sain", "good"), ("khün", "person"), ("gej", "C"), ("khel-sen", "say-PST")]
    glossedWords := [⟨[['B', 'a', 't'], ['i', 'n']], [['B', 'a', 't'], ['G', 'E', 'N']]⟩, ⟨[['e', 'e', 'j'], ['i', 'i', 'g']], [['m', 'o', 't', 'h', 'e', 'r'], ['A', 'C', 'C']]⟩, ⟨[['b', 'i']], [['1', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['t', 'ü', 'ü', 'n'], ['d']], [['3', 'S', 'G'], ['D', 'A', 'T']]⟩, ⟨[['s', 'a', 'i', 'n']], [['g', 'o', 'o', 'd']]⟩, ⟨[['k', 'h', 'ü', 'n']], [['p', 'e', 'r', 's', 'o', 'n']]⟩, ⟨[['g', 'e', 'j']], [['C']]⟩, ⟨[['k', 'h', 'e', 'l'], ['s', 'e', 'n']], [['s', 'a', 'y'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "ACC-SUBJ"), ("binder", "matrix DAT"), ("mover", "DP")] }

def ex_33 : Datum :=
  { id := "gong2022_33"
    source := ⟨"gong-2022", "(33)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "[Baatar-in zokhiol-iig] ter [maš sain gej] khel-sen."
    glossedTokens := [("Baatar-in", "Baatar-GEN"), ("zokhiol-iig", "article-ACC"), ("ter", "3SG.NOM"), ("maš", "very"), ("sain", "good"), ("gej", "C"), ("khel-sen", "say-PST")]
    glossedWords := [⟨[['B', 'a', 'a', 't', 'a', 'r'], ['i', 'n']], [['B', 'a', 'a', 't', 'a', 'r'], ['G', 'E', 'N']]⟩, ⟨[['z', 'o', 'k', 'h', 'i', 'o', 'l'], ['i', 'i', 'g']], [['a', 'r', 't', 'i', 'c', 'l', 'e'], ['A', 'C', 'C']]⟩, ⟨[['t', 'e', 'r']], [['3', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['m', 'a', 'š']], [['v', 'e', 'r', 'y']]⟩, ⟨[['s', 'a', 'i', 'n']], [['g', 'o', 'o', 'd']]⟩, ⟨[['g', 'e', 'j']], [['C']]⟩, ⟨[['k', 'h', 'e', 'l'], ['s', 'e', 'n']], [['s', 'a', 'y'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "ACC-SUBJ"), ("binder", "matrix subject"), ("mover", "DP")] }

def ex_40 : Datum :=
  { id := "gong2022_40"
    source := ⟨"gong-2022", "(40)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "[Bat-in esee-g] ter [bagš-iig unš-san gej] khel-sen."
    glossedTokens := [("Bat-in", "Bat-GEN"), ("esee-g", "essay-ACC"), ("ter", "3SG.NOM"), ("bagš-iig", "teacher-ACC"), ("unš-san", "read-PST"), ("gej", "C"), ("khel-sen", "say-PST")]
    glossedWords := [⟨[['B', 'a', 't'], ['i', 'n']], [['B', 'a', 't'], ['G', 'E', 'N']]⟩, ⟨[['e', 's', 'e', 'e'], ['g']], [['e', 's', 's', 'a', 'y'], ['A', 'C', 'C']]⟩, ⟨[['t', 'e', 'r']], [['3', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['b', 'a', 'g', 'š'], ['i', 'i', 'g']], [['t', 'e', 'a', 'c', 'h', 'e', 'r'], ['A', 'C', 'C']]⟩, ⟨[['u', 'n', 'š'], ['s', 'a', 'n']], [['r', 'e', 'a', 'd'], ['P', 'S', 'T']]⟩, ⟨[['g', 'e', 'j']], [['C']]⟩, ⟨[['k', 'h', 'e', 'l'], ['s', 'e', 'n']], [['s', 'a', 'y'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "LDS"), ("binder", "matrix subject"), ("mover", "DP")] }

def ex_41 : Datum :=
  { id := "gong2022_41"
    source := ⟨"gong-2022", "(41)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "[Bat-in esee-g] Zaya tüün-d [bagš-iig unš-san gej] khel-sen."
    glossedTokens := [("Bat-in", "Bat-GEN"), ("esee-g", "essay-ACC"), ("Zaya", "Zaya.NOM"), ("tüün-d", "3SG-DAT"), ("bagš-iig", "teacher-ACC"), ("unš-san", "read-PST"), ("gej", "C"), ("khel-sen", "say-PST")]
    glossedWords := [⟨[['B', 'a', 't'], ['i', 'n']], [['B', 'a', 't'], ['G', 'E', 'N']]⟩, ⟨[['e', 's', 'e', 'e'], ['g']], [['e', 's', 's', 'a', 'y'], ['A', 'C', 'C']]⟩, ⟨[['Z', 'a', 'y', 'a']], [['Z', 'a', 'y', 'a', '.', 'N', 'O', 'M']]⟩, ⟨[['t', 'ü', 'ü', 'n'], ['d']], [['3', 'S', 'G'], ['D', 'A', 'T']]⟩, ⟨[['b', 'a', 'g', 'š'], ['i', 'i', 'g']], [['t', 'e', 'a', 'c', 'h', 'e', 'r'], ['A', 'C', 'C']]⟩, ⟨[['u', 'n', 'š'], ['s', 'a', 'n']], [['r', 'e', 'a', 'd'], ['P', 'S', 'T']]⟩, ⟨[['g', 'e', 'j']], [['C']]⟩, ⟨[['k', 'h', 'e', 'l'], ['s', 'e', 'n']], [['s', 'a', 'y'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "LDS"), ("binder", "matrix DAT"), ("mover", "DP")] }

def ex_58a : Datum :=
  { id := "gong2022_58a"
    source := ⟨"gong-2022", "(58a)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "Bi [Bat-in eej-iig] tüün-d [sain khün gej] khel-sen."
    glossedTokens := [("Bi", "1SG.NOM"), ("Bat-in", "Bat-GEN"), ("eej-iig", "mother-ACC"), ("tüün-d", "3SG-DAT"), ("sain", "good"), ("khün", "person"), ("gej", "C"), ("khel-sen", "say-PST")]
    glossedWords := [⟨[['B', 'i']], [['1', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['B', 'a', 't'], ['i', 'n']], [['B', 'a', 't'], ['G', 'E', 'N']]⟩, ⟨[['e', 'e', 'j'], ['i', 'i', 'g']], [['m', 'o', 't', 'h', 'e', 'r'], ['A', 'C', 'C']]⟩, ⟨[['t', 'ü', 'ü', 'n'], ['d']], [['3', 'S', 'G'], ['D', 'A', 'T']]⟩, ⟨[['s', 'a', 'i', 'n']], [['g', 'o', 'o', 'd']]⟩, ⟨[['k', 'h', 'ü', 'n']], [['p', 'e', 'r', 's', 'o', 'n']]⟩, ⟨[['g', 'e', 'j']], [['C']]⟩, ⟨[['k', 'h', 'e', 'l'], ['s', 'e', 'n']], [['s', 'a', 'y'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "ACC-SUBJ intermediate"), ("binder", "matrix DAT"), ("mover", "DP")] }

def ex_58b : Datum :=
  { id := "gong2022_58b"
    source := ⟨"gong-2022", "(58b)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "Zaya [Bat-in esee-g] tüün-d [bagš-iig-aa unš-san gej] khel-sen."
    glossedTokens := [("Zaya", "Zaya.NOM"), ("Bat-in", "Bat-GEN"), ("esee-g", "essay-ACC"), ("tüün-d", "3SG-DAT"), ("bagš-iig-aa", "teacher-ACC-REFL.POSS"), ("unš-san", "read-PST"), ("gej", "C"), ("khel-sen", "say-PST")]
    glossedWords := [⟨[['Z', 'a', 'y', 'a']], [['Z', 'a', 'y', 'a', '.', 'N', 'O', 'M']]⟩, ⟨[['B', 'a', 't'], ['i', 'n']], [['B', 'a', 't'], ['G', 'E', 'N']]⟩, ⟨[['e', 's', 'e', 'e'], ['g']], [['e', 's', 's', 'a', 'y'], ['A', 'C', 'C']]⟩, ⟨[['t', 'ü', 'ü', 'n'], ['d']], [['3', 'S', 'G'], ['D', 'A', 'T']]⟩, ⟨[['b', 'a', 'g', 'š'], ['i', 'i', 'g'], ['a', 'a']], [['t', 'e', 'a', 'c', 'h', 'e', 'r'], ['A', 'C', 'C'], ['R', 'E', 'F', 'L', '.', 'P', 'O', 'S', 'S']]⟩, ⟨[['u', 'n', 'š'], ['s', 'a', 'n']], [['r', 'e', 'a', 'd'], ['P', 'S', 'T']]⟩, ⟨[['g', 'e', 'j']], [['C']]⟩, ⟨[['k', 'h', 'e', 'l'], ['s', 'e', 'n']], [['s', 'a', 'y'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "LDS intermediate"), ("binder", "matrix DAT"), ("mover", "DP")] }

def ex_61 : Datum :=
  { id := "gong2022_61"
    source := ⟨"gong-2022", "(61)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "[Bat-in em-iig] emč [tüün-iig uu-gaagüi gej] uurla-san."
    glossedTokens := [("Bat-in", "Bat-GEN"), ("em-iig", "medicine-ACC"), ("emč", "doctor.NOM"), ("tüün-iig", "3SG-ACC"), ("uu-gaagüi", "drink-PST.NEG"), ("gej", "C"), ("uurla-san", "become.angry-PST")]
    glossedWords := [⟨[['B', 'a', 't'], ['i', 'n']], [['B', 'a', 't'], ['G', 'E', 'N']]⟩, ⟨[['e', 'm'], ['i', 'i', 'g']], [['m', 'e', 'd', 'i', 'c', 'i', 'n', 'e'], ['A', 'C', 'C']]⟩, ⟨[['e', 'm', 'č']], [['d', 'o', 'c', 't', 'o', 'r', '.', 'N', 'O', 'M']]⟩, ⟨[['t', 'ü', 'ü', 'n'], ['i', 'i', 'g']], [['3', 'S', 'G'], ['A', 'C', 'C']]⟩, ⟨[['u', 'u'], ['g', 'a', 'a', 'g', 'ü', 'i']], [['d', 'r', 'i', 'n', 'k'], ['P', 'S', 'T', '.', 'N', 'E', 'G']]⟩, ⟨[['g', 'e', 'j']], [['C']]⟩, ⟨[['u', 'u', 'r', 'l', 'a'], ['s', 'a', 'n']], [['b', 'e', 'c', 'o', 'm', 'e', '.', 'a', 'n', 'g', 'r', 'y'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "LDS"), ("binder", "embedded subject"), ("mover", "DP")] }

def ex_79 : Datum :=
  { id := "gong2022_79"
    source := ⟨"gong-2022", "(79)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "[Čemeg-in eej-id] ter nom ög-sön."
    glossedTokens := [("Čemeg-in", "Čemeg-GEN"), ("eej-id", "mother-DAT"), ("ter", "3SG.NOM"), ("nom", "book"), ("ög-sön", "give-PST")]
    glossedWords := [⟨[['Č', 'e', 'm', 'e', 'g'], ['i', 'n']], [['Č', 'e', 'm', 'e', 'g'], ['G', 'E', 'N']]⟩, ⟨[['e', 'e', 'j'], ['i', 'd']], [['m', 'o', 't', 'h', 'e', 'r'], ['D', 'A', 'T']]⟩, ⟨[['t', 'e', 'r']], [['3', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['n', 'o', 'm']], [['b', 'o', 'o', 'k']]⟩, ⟨[['ö', 'g'], ['s', 'ö', 'n']], [['g', 'i', 'v', 'e'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "IO"), ("binder", "subject"), ("mover", "DP-lexical")] }

def ex_85b : Datum :=
  { id := "gong2022_85b"
    source := ⟨"gong-2022", "(85b)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "[Bat-in nom] bagš-aar tüün-d ögö-gd-sön."
    glossedTokens := [("Bat-in", "Bat-GEN"), ("nom", "book.NOM"), ("bagš-aar", "teacher-INST"), ("tüün-d", "3SG-DAT"), ("ögö-gd-sön", "give-PASS-PST")]
    glossedWords := [⟨[['B', 'a', 't'], ['i', 'n']], [['B', 'a', 't'], ['G', 'E', 'N']]⟩, ⟨[['n', 'o', 'm']], [['b', 'o', 'o', 'k', '.', 'N', 'O', 'M']]⟩, ⟨[['b', 'a', 'g', 'š'], ['a', 'a', 'r']], [['t', 'e', 'a', 'c', 'h', 'e', 'r'], ['I', 'N', 'S', 'T']]⟩, ⟨[['t', 'ü', 'ü', 'n'], ['d']], [['3', 'S', 'G'], ['D', 'A', 'T']]⟩, ⟨[['ö', 'g', 'ö'], ['g', 'd'], ['s', 'ö', 'n']], [['g', 'i', 'v', 'e'], ['P', 'A', 'S', 'S'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "passive"), ("binder", "IO"), ("mover", "DP")] }

def ex_86 : Datum :=
  { id := "gong2022_86"
    source := ⟨"gong-2022", "(86)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "[Zorig-iin emee-d] bi [tüün-iig tusal-dag bai-san gej] bodo-j bai-na."
    glossedTokens := [("Zorig-iin", "Zorig-GEN"), ("emee-d", "grandmother-DAT"), ("bi", "1SG.NOM"), ("tüün-iig", "3SG-ACC"), ("tusal-dag", "help-HABIT"), ("bai-san", "COP-PST"), ("gej", "C"), ("bodo-j", "think-CVB"), ("bai-na", "COP-NPST")]
    glossedWords := [⟨[['Z', 'o', 'r', 'i', 'g'], ['i', 'i', 'n']], [['Z', 'o', 'r', 'i', 'g'], ['G', 'E', 'N']]⟩, ⟨[['e', 'm', 'e', 'e'], ['d']], [['g', 'r', 'a', 'n', 'd', 'm', 'o', 't', 'h', 'e', 'r'], ['D', 'A', 'T']]⟩, ⟨[['b', 'i']], [['1', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['t', 'ü', 'ü', 'n'], ['i', 'i', 'g']], [['3', 'S', 'G'], ['A', 'C', 'C']]⟩, ⟨[['t', 'u', 's', 'a', 'l'], ['d', 'a', 'g']], [['h', 'e', 'l', 'p'], ['H', 'A', 'B', 'I', 'T']]⟩, ⟨[['b', 'a', 'i'], ['s', 'a', 'n']], [['C', 'O', 'P'], ['P', 'S', 'T']]⟩, ⟨[['g', 'e', 'j']], [['C']]⟩, ⟨[['b', 'o', 'd', 'o'], ['j']], [['t', 'h', 'i', 'n', 'k'], ['C', 'V', 'B']]⟩, ⟨[['b', 'a', 'i'], ['n', 'a']], [['C', 'O', 'P'], ['N', 'P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "LDS"), ("binder", "embedded subject"), ("mover", "DP-lexical"), ("alsoJudged", "ungrammatical")] }

def ex_93b : Datum :=
  { id := "gong2022_93b"
    source := ⟨"gong-2022", "(93b)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "[Bat-in dontolt-in esreg] emč [tüün-iig kheden jil-iin turš temtse-j bai-san gej] nadad khel-sen."
    glossedTokens := [("Bat-in", "Bat-GEN"), ("dontolt-in", "addiction-GEN"), ("esreg", "against"), ("emč", "doctor"), ("tüün-iig", "3SG-ACC"), ("kheden", "some"), ("jil-iin", "year-GEN"), ("turš", "during"), ("temtse-j", "fight-CVB"), ("bai-san", "COP-PST"), ("gej", "C"), ("nadad", "1SG.DAT"), ("khel-sen", "say-PST")]
    glossedWords := [⟨[['B', 'a', 't'], ['i', 'n']], [['B', 'a', 't'], ['G', 'E', 'N']]⟩, ⟨[['d', 'o', 'n', 't', 'o', 'l', 't'], ['i', 'n']], [['a', 'd', 'd', 'i', 'c', 't', 'i', 'o', 'n'], ['G', 'E', 'N']]⟩, ⟨[['e', 's', 'r', 'e', 'g']], [['a', 'g', 'a', 'i', 'n', 's', 't']]⟩, ⟨[['e', 'm', 'č']], [['d', 'o', 'c', 't', 'o', 'r']]⟩, ⟨[['t', 'ü', 'ü', 'n'], ['i', 'i', 'g']], [['3', 'S', 'G'], ['A', 'C', 'C']]⟩, ⟨[['k', 'h', 'e', 'd', 'e', 'n']], [['s', 'o', 'm', 'e']]⟩, ⟨[['j', 'i', 'l'], ['i', 'i', 'n']], [['y', 'e', 'a', 'r'], ['G', 'E', 'N']]⟩, ⟨[['t', 'u', 'r', 'š']], [['d', 'u', 'r', 'i', 'n', 'g']]⟩, ⟨[['t', 'e', 'm', 't', 's', 'e'], ['j']], [['f', 'i', 'g', 'h', 't'], ['C', 'V', 'B']]⟩, ⟨[['b', 'a', 'i'], ['s', 'a', 'n']], [['C', 'O', 'P'], ['P', 'S', 'T']]⟩, ⟨[['g', 'e', 'j']], [['C']]⟩, ⟨[['n', 'a', 'd', 'a', 'd']], [['1', 'S', 'G', '.', 'D', 'A', 'T']]⟩, ⟨[['k', 'h', 'e', 'l'], ['s', 'e', 'n']], [['s', 'a', 'y'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "PP-LDS"), ("binder", "embedded subject"), ("mover", "PP")] }

def ex_94b : Datum :=
  { id := "gong2022_94b"
    source := ⟨"gong-2022", "(94b)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "[Zorig-iin öwčin-ii esreg] Zaya tüün-d [emč nar-ig čadakh bükhn-eer-ee temtse-j bol-no gej] khel-sen."
    glossedTokens := [("Zorig-iin", "Zorig-GEN"), ("öwčin-ii", "disease-GEN"), ("esreg", "against"), ("Zaya", "Zaya.NOM"), ("tüün-d", "3SG-DAT"), ("emč", "doctor"), ("nar-ig", "PL-ACC"), ("čadakh", "ability"), ("bükhn-eer-ee", "all-INST-REFL.POSS"), ("temtse-j", "fight-CVB"), ("bol-no", "be-NPST"), ("gej", "C"), ("khel-sen", "say-PST")]
    glossedWords := [⟨[['Z', 'o', 'r', 'i', 'g'], ['i', 'i', 'n']], [['Z', 'o', 'r', 'i', 'g'], ['G', 'E', 'N']]⟩, ⟨[['ö', 'w', 'č', 'i', 'n'], ['i', 'i']], [['d', 'i', 's', 'e', 'a', 's', 'e'], ['G', 'E', 'N']]⟩, ⟨[['e', 's', 'r', 'e', 'g']], [['a', 'g', 'a', 'i', 'n', 's', 't']]⟩, ⟨[['Z', 'a', 'y', 'a']], [['Z', 'a', 'y', 'a', '.', 'N', 'O', 'M']]⟩, ⟨[['t', 'ü', 'ü', 'n'], ['d']], [['3', 'S', 'G'], ['D', 'A', 'T']]⟩, ⟨[['e', 'm', 'č']], [['d', 'o', 'c', 't', 'o', 'r']]⟩, ⟨[['n', 'a', 'r'], ['i', 'g']], [['P', 'L'], ['A', 'C', 'C']]⟩, ⟨[['č', 'a', 'd', 'a', 'k', 'h']], [['a', 'b', 'i', 'l', 'i', 't', 'y']]⟩, ⟨[['b', 'ü', 'k', 'h', 'n'], ['e', 'e', 'r'], ['e', 'e']], [['a', 'l', 'l'], ['I', 'N', 'S', 'T'], ['R', 'E', 'F', 'L', '.', 'P', 'O', 'S', 'S']]⟩, ⟨[['t', 'e', 'm', 't', 's', 'e'], ['j']], [['f', 'i', 'g', 'h', 't'], ['C', 'V', 'B']]⟩, ⟨[['b', 'o', 'l'], ['n', 'o']], [['b', 'e'], ['N', 'P', 'S', 'T']]⟩, ⟨[['g', 'e', 'j']], [['C']]⟩, ⟨[['k', 'h', 'e', 'l'], ['s', 'e', 'n']], [['s', 'a', 'y'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "PP-LDS"), ("binder", "matrix DAT"), ("mover", "PP")] }

def ex_47 : Datum :=
  { id := "gong2022_47"
    source := ⟨"gong-2022", "(47)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "Emč [Bat-ig em-ee uu-gaagüi gej] uurla-san."
    glossedTokens := [("Emč", "doctor.NOM"), ("Bat-ig", "Bat-ACC"), ("em-ee", "medicine-REFL.POSS"), ("uu-gaagüi", "drink-PST.NEG"), ("gej", "C"), ("uurla-san", "become.angry-PST")]
    glossedWords := [⟨[['E', 'm', 'č']], [['d', 'o', 'c', 't', 'o', 'r', '.', 'N', 'O', 'M']]⟩, ⟨[['B', 'a', 't'], ['i', 'g']], [['B', 'a', 't'], ['A', 'C', 'C']]⟩, ⟨[['e', 'm'], ['e', 'e']], [['m', 'e', 'd', 'i', 'c', 'i', 'n', 'e'], ['R', 'E', 'F', 'L', '.', 'P', 'O', 'S', 'S']]⟩, ⟨[['u', 'u'], ['g', 'a', 'a', 'g', 'ü', 'i']], [['d', 'r', 'i', 'n', 'k'], ['P', 'S', 'T', '.', 'N', 'E', 'G']]⟩, ⟨[['g', 'e', 'j']], [['C']]⟩, ⟨[['u', 'u', 'r', 'l', 'a'], ['s', 'a', 'n']], [['b', 'e', 'c', 'o', 'm', 'e', '.', 'a', 'n', 'g', 'r', 'y'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "accusative subject"), ("competitor", "NOM")] }

def ex_48 : Datum :=
  { id := "gong2022_48"
    source := ⟨"gong-2022", "(48)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "Bi [Čang-iig amid bai-gaa gedeg]-t itgeltei bai-na."
    glossedTokens := [("Bi", "1SG.NOM"), ("Čang-iig", "Čang-ACC"), ("amid", "alive"), ("bai-gaa", "COP-NPST.PTCP"), ("gedeg-t", "C-DAT"), ("itgeltei", "believe"), ("bai-na", "COP-NPST")]
    glossedWords := [⟨[['B', 'i']], [['1', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['Č', 'a', 'n', 'g'], ['i', 'i', 'g']], [['Č', 'a', 'n', 'g'], ['A', 'C', 'C']]⟩, ⟨[['a', 'm', 'i', 'd']], [['a', 'l', 'i', 'v', 'e']]⟩, ⟨[['b', 'a', 'i'], ['g', 'a', 'a']], [['C', 'O', 'P'], ['N', 'P', 'S', 'T', '.', 'P', 'T', 'C', 'P']]⟩, ⟨[['g', 'e', 'd', 'e', 'g'], ['t']], [['C'], ['D', 'A', 'T']]⟩, ⟨[['i', 't', 'g', 'e', 'l', 't', 'e', 'i']], [['b', 'e', 'l', 'i', 'e', 'v', 'e']]⟩, ⟨[['b', 'a', 'i'], ['n', 'a']], [['C', 'O', 'P'], ['N', 'P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "accusative subject"), ("competitor", "NOM")] }

def ex_63 : Datum :=
  { id := "gong2022_63"
    source := ⟨"gong-2022", "(63)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "[Bat-ig ger-iin daalgawr-aa khiikh ni] čukhal."
    glossedTokens := [("Bat-ig", "Bat-ACC"), ("ger-iin", "home-GEN"), ("daalgawr-aa", "assignment-REFL.POSS"), ("khiikh", "do.INF"), ("ni", "3SG.POSS"), ("čukhal", "important")]
    glossedWords := [⟨[['B', 'a', 't'], ['i', 'g']], [['B', 'a', 't'], ['A', 'C', 'C']]⟩, ⟨[['g', 'e', 'r'], ['i', 'i', 'n']], [['h', 'o', 'm', 'e'], ['G', 'E', 'N']]⟩, ⟨[['d', 'a', 'a', 'l', 'g', 'a', 'w', 'r'], ['a', 'a']], [['a', 's', 's', 'i', 'g', 'n', 'm', 'e', 'n', 't'], ['R', 'E', 'F', 'L', '.', 'P', 'O', 'S', 'S']]⟩, ⟨[['k', 'h', 'i', 'i', 'k', 'h']], [['d', 'o', '.', 'I', 'N', 'F']]⟩, ⟨[['n', 'i']], [['3', 'S', 'G', '.', 'P', 'O', 'S', 'S']]⟩, ⟨[['č', 'u', 'k', 'h', 'a', 'l']], [['i', 'm', 'p', 'o', 'r', 't', 'a', 'n', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("kind", "accusative subject"), ("competitor", "none")] }

def ex_64 : Datum :=
  { id := "gong2022_64"
    source := ⟨"gong-2022", "(64)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "Saruul [Jon-ig šine mašin aw-san gej] uurla-san."
    glossedTokens := [("Saruul", "Saruul.NOM"), ("Jon-ig", "Jon-ACC"), ("šine", "new"), ("mašin", "car"), ("aw-san", "buy-PST"), ("gej", "C"), ("uurla-san", "become.angry-PST")]
    glossedWords := [⟨[['S', 'a', 'r', 'u', 'u', 'l']], [['S', 'a', 'r', 'u', 'u', 'l', '.', 'N', 'O', 'M']]⟩, ⟨[['J', 'o', 'n'], ['i', 'g']], [['J', 'o', 'n'], ['A', 'C', 'C']]⟩, ⟨[['š', 'i', 'n', 'e']], [['n', 'e', 'w']]⟩, ⟨[['m', 'a', 'š', 'i', 'n']], [['c', 'a', 'r']]⟩, ⟨[['a', 'w'], ['s', 'a', 'n']], [['b', 'u', 'y'], ['P', 'S', 'T']]⟩, ⟨[['g', 'e', 'j']], [['C']]⟩, ⟨[['u', 'u', 'r', 'l', 'a'], ['s', 'a', 'n']], [['b', 'e', 'c', 'o', 'm', 'e', '.', 'a', 'n', 'g', 'r', 'y'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "accusative subject"), ("competitor", "NOM")] }

def ex_65 : Datum :=
  { id := "gong2022_65"
    source := ⟨"gong-2022", "(65)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "Saruul-d [Jon-ig šine mašin aw-san gej] sanagda-j bai-san."
    glossedTokens := [("Saruul-d", "Saruul-DAT"), ("Jon-ig", "Jon-ACC"), ("šine", "new"), ("mašin", "car"), ("aw-san", "buy-PST"), ("gej", "C"), ("sanagda-j", "seem-CVB"), ("bai-san", "COP-PST")]
    glossedWords := [⟨[['S', 'a', 'r', 'u', 'u', 'l'], ['d']], [['S', 'a', 'r', 'u', 'u', 'l'], ['D', 'A', 'T']]⟩, ⟨[['J', 'o', 'n'], ['i', 'g']], [['J', 'o', 'n'], ['A', 'C', 'C']]⟩, ⟨[['š', 'i', 'n', 'e']], [['n', 'e', 'w']]⟩, ⟨[['m', 'a', 'š', 'i', 'n']], [['c', 'a', 'r']]⟩, ⟨[['a', 'w'], ['s', 'a', 'n']], [['b', 'u', 'y'], ['P', 'S', 'T']]⟩, ⟨[['g', 'e', 'j']], [['C']]⟩, ⟨[['s', 'a', 'n', 'a', 'g', 'd', 'a'], ['j']], [['s', 'e', 'e', 'm'], ['C', 'V', 'B']]⟩, ⟨[['b', 'a', 'i'], ['s', 'a', 'n']], [['C', 'O', 'P'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("kind", "accusative subject"), ("competitor", "DAT")] }

def all : List Datum := [ex_18b, ex_19b, ex_20b, ex_21b, ex_32b, ex_33, ex_40, ex_41, ex_58a, ex_58b, ex_61, ex_79, ex_85b, ex_86, ex_93b, ex_94b, ex_47, ex_48, ex_63, ex_64, ex_65]

end Gong2022.Examples
