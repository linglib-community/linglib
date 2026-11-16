module

public import Linglib.Data.Examples.Schema

/-!
# `Pylkkanen2008` — typed example data

Auto-generated from `Linglib/Data/Examples/Pylkkanen2008.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Pylkkanen2008.Examples`.
-/

@[expose] public section

namespace Pylkkanen2008.Examples

def ex19a : Datum :=
  { id := "pylkkanen2008_ex19a"
    source := ⟨"pylkkanen-2008", "ch. 2, (19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I baked him a cake."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "baseline"), ("relation", "recipient")] }

def ex19b : Datum :=
  { id := "pylkkanen2008_ex19b"
    source := ⟨"pylkkanen-2008", "ch. 2, (19b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-ga Hanako-ni tegami-o kaita."
    glossedTokens := [("Taroo-ga", "Taro-NOM"), ("Hanako-ni", "Hanako-DAT"), ("tegami-o", "letter-ACC"), ("kaita", "wrote")]
    glossedWords := [⟨[['T', 'a', 'r', 'o', 'o'], ['g', 'a']], [['T', 'a', 'r', 'o'], ['N', 'O', 'M']]⟩, ⟨[['H', 'a', 'n', 'a', 'k', 'o'], ['n', 'i']], [['H', 'a', 'n', 'a', 'k', 'o'], ['D', 'A', 'T']]⟩, ⟨[['t', 'e', 'g', 'a', 'm', 'i'], ['o']], [['l', 'e', 't', 't', 'e', 'r'], ['A', 'C', 'C']]⟩, ⟨[['k', 'a', 'i', 't', 'a']], [['w', 'r', 'o', 't', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "baseline"), ("relation", "recipient")] }

def ex19c : Datum :=
  { id := "pylkkanen2008_ex19c"
    source := ⟨"pylkkanen-2008", "ch. 2, (19c)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "John-i Mary-hanthey pyunci-lul sse-ess-ta."
    glossedTokens := [("John-i", "John-NOM"), ("Mary-hanthey", "Mary-DAT"), ("pyunci-lul", "letter-ACC"), ("sse-ess-ta", "wrote-PAST-PLAIN")]
    glossedWords := [⟨[['J', 'o', 'h', 'n'], ['i']], [['J', 'o', 'h', 'n'], ['N', 'O', 'M']]⟩, ⟨[['M', 'a', 'r', 'y'], ['h', 'a', 'n', 't', 'h', 'e', 'y']], [['M', 'a', 'r', 'y'], ['D', 'A', 'T']]⟩, ⟨[['p', 'y', 'u', 'n', 'c', 'i'], ['l', 'u', 'l']], [['l', 'e', 't', 't', 'e', 'r'], ['A', 'C', 'C']]⟩, ⟨[['s', 's', 'e'], ['e', 's', 's'], ['t', 'a']], [['w', 'r', 'o', 't', 'e'], ['P', 'A', 'S', 'T'], ['P', 'L', 'A', 'I', 'N']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "baseline"), ("relation", "recipient")] }

def ex19d : Datum :=
  { id := "pylkkanen2008_ex19d"
    source := ⟨"pylkkanen-2008", "ch. 2, (19d)"⟩
    reportedIn := none
    language := "gand1255"
    primaryText := "Mukasa ya-som-e-dde Katonga ekitabo."
    glossedTokens := [("Mukasa", "Mukasa"), ("ya-som-e-dde", "3SG.PAST-read-APPL-PAST"), ("Katonga", "Katonga"), ("ekitabo", "book")]
    glossedWords := [⟨[['M', 'u', 'k', 'a', 's', 'a']], [['M', 'u', 'k', 'a', 's', 'a']]⟩, ⟨[['y', 'a'], ['s', 'o', 'm'], ['e'], ['d', 'd', 'e']], [['3', 'S', 'G', '.', 'P', 'A', 'S', 'T'], ['r', 'e', 'a', 'd'], ['A', 'P', 'P', 'L'], ['P', 'A', 'S', 'T']]⟩, ⟨[['K', 'a', 't', 'o', 'n', 'g', 'a']], [['K', 'a', 't', 'o', 'n', 'g', 'a']]⟩, ⟨[['e', 'k', 'i', 't', 'a', 'b', 'o']], [['b', 'o', 'o', 'k']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "baseline"), ("relation", "benefactive")] }

def ex19e : Datum :=
  { id := "pylkkanen2008_ex19e"
    source := ⟨"pylkkanen-2008", "ch. 2, (19e)"⟩
    reportedIn := none
    language := "vend1245"
    primaryText := "Nd-o-tandulela tshimu ya mukegulu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "baseline"), ("relation", "benefactive")] }

def ex19f : Datum :=
  { id := "pylkkanen2008_ex19f"
    source := ⟨"pylkkanen-2008", "ch. 2, (19f)"⟩
    reportedIn := none
    language := "alba1267"
    primaryText := "Drita i poqi Agimit kek."
    glossedTokens := [("Drita", "Drita.NOM"), ("i", "CL"), ("poqi", "baked"), ("Agimit", "Agim.DAT"), ("kek", "cake")]
    glossedWords := [⟨[['D', 'r', 'i', 't', 'a']], [['D', 'r', 'i', 't', 'a', '.', 'N', 'O', 'M']]⟩, ⟨[['i']], [['C', 'L']]⟩, ⟨[['p', 'o', 'q', 'i']], [['b', 'a', 'k', 'e', 'd']]⟩, ⟨[['A', 'g', 'i', 'm', 'i', 't']], [['A', 'g', 'i', 'm', '.', 'D', 'A', 'T']]⟩, ⟨[['k', 'e', 'k']], [['c', 'a', 'k', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "baseline"), ("relation", "benefactive")] }

def ex20a : Datum :=
  { id := "pylkkanen2008_ex20a"
    source := ⟨"pylkkanen-2008", "ch. 2, (20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I ran him."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("test", "unergative")] }

def ex20b : Datum :=
  { id := "pylkkanen2008_ex20b"
    source := ⟨"pylkkanen-2008", "ch. 2, (20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I held him the bag."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("test", "static")] }

def ex21a : Datum :=
  { id := "pylkkanen2008_ex21a"
    source := ⟨"pylkkanen-2008", "ch. 2, (21a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-ga Hanako-ni hasit-ta."
    glossedTokens := [("Taroo-ga", "Taro-NOM"), ("Hanako-ni", "Hanako-DAT"), ("hasit-ta", "run-PAST")]
    glossedWords := [⟨[['T', 'a', 'r', 'o', 'o'], ['g', 'a']], [['T', 'a', 'r', 'o'], ['N', 'O', 'M']]⟩, ⟨[['H', 'a', 'n', 'a', 'k', 'o'], ['n', 'i']], [['H', 'a', 'n', 'a', 'k', 'o'], ['D', 'A', 'T']]⟩, ⟨[['h', 'a', 's', 'i', 't'], ['t', 'a']], [['r', 'u', 'n'], ['P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("test", "unergative")] }

def ex21b : Datum :=
  { id := "pylkkanen2008_ex21b"
    source := ⟨"pylkkanen-2008", "ch. 2, (21b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-ga Hanako-ni kanojo-no kaban-o mot-ta."
    glossedTokens := [("Taroo-ga", "Taro-NOM"), ("Hanako-ni", "Hanako-DAT"), ("kanojo-no", "she-GEN"), ("kaban-o", "bag-ACC"), ("mot-ta", "hold-PAST")]
    glossedWords := [⟨[['T', 'a', 'r', 'o', 'o'], ['g', 'a']], [['T', 'a', 'r', 'o'], ['N', 'O', 'M']]⟩, ⟨[['H', 'a', 'n', 'a', 'k', 'o'], ['n', 'i']], [['H', 'a', 'n', 'a', 'k', 'o'], ['D', 'A', 'T']]⟩, ⟨[['k', 'a', 'n', 'o', 'j', 'o'], ['n', 'o']], [['s', 'h', 'e'], ['G', 'E', 'N']]⟩, ⟨[['k', 'a', 'b', 'a', 'n'], ['o']], [['b', 'a', 'g'], ['A', 'C', 'C']]⟩, ⟨[['m', 'o', 't'], ['t', 'a']], [['h', 'o', 'l', 'd'], ['P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("test", "static")] }

def ex22a : Datum :=
  { id := "pylkkanen2008_ex22a"
    source := ⟨"pylkkanen-2008", "ch. 2, (22a)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Mary-ka John-hanthey talli-ess-ta."
    glossedTokens := [("Mary-ka", "Mary-NOM"), ("John-hanthey", "John-DAT"), ("talli-ess-ta", "run-PAST-PLAIN")]
    glossedWords := [⟨[['M', 'a', 'r', 'y'], ['k', 'a']], [['M', 'a', 'r', 'y'], ['N', 'O', 'M']]⟩, ⟨[['J', 'o', 'h', 'n'], ['h', 'a', 'n', 't', 'h', 'e', 'y']], [['J', 'o', 'h', 'n'], ['D', 'A', 'T']]⟩, ⟨[['t', 'a', 'l', 'l', 'i'], ['e', 's', 's'], ['t', 'a']], [['r', 'u', 'n'], ['P', 'A', 'S', 'T'], ['P', 'L', 'A', 'I', 'N']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("test", "unergative")] }

def ex22b : Datum :=
  { id := "pylkkanen2008_ex22b"
    source := ⟨"pylkkanen-2008", "ch. 2, (22b)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "John-i Mary-hanthey kabang-ul cap-ass-ta."
    glossedTokens := [("John-i", "John-NOM"), ("Mary-hanthey", "Mary-DAT"), ("kabang-ul", "bag-ACC"), ("cap-ass-ta", "hold-PAST-PLAIN")]
    glossedWords := [⟨[['J', 'o', 'h', 'n'], ['i']], [['J', 'o', 'h', 'n'], ['N', 'O', 'M']]⟩, ⟨[['M', 'a', 'r', 'y'], ['h', 'a', 'n', 't', 'h', 'e', 'y']], [['M', 'a', 'r', 'y'], ['D', 'A', 'T']]⟩, ⟨[['k', 'a', 'b', 'a', 'n', 'g'], ['u', 'l']], [['b', 'a', 'g'], ['A', 'C', 'C']]⟩, ⟨[['c', 'a', 'p'], ['a', 's', 's'], ['t', 'a']], [['h', 'o', 'l', 'd'], ['P', 'A', 'S', 'T'], ['P', 'L', 'A', 'I', 'N']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("test", "static")] }

def ex23a : Datum :=
  { id := "pylkkanen2008_ex23a"
    source := ⟨"pylkkanen-2008", "ch. 2, (23a)"⟩
    reportedIn := none
    language := "gand1255"
    primaryText := "Mukasa ya-tambu-le-dde Katonga."
    glossedTokens := [("Mukasa", "Mukasa"), ("ya-tambu-le-dde", "3SG.PAST-walk-APPL-PAST"), ("Katonga", "Katonga")]
    glossedWords := [⟨[['M', 'u', 'k', 'a', 's', 'a']], [['M', 'u', 'k', 'a', 's', 'a']]⟩, ⟨[['y', 'a'], ['t', 'a', 'm', 'b', 'u'], ['l', 'e'], ['d', 'd', 'e']], [['3', 'S', 'G', '.', 'P', 'A', 'S', 'T'], ['w', 'a', 'l', 'k'], ['A', 'P', 'P', 'L'], ['P', 'A', 'S', 'T']]⟩, ⟨[['K', 'a', 't', 'o', 'n', 'g', 'a']], [['K', 'a', 't', 'o', 'n', 'g', 'a']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "unergative")] }

def ex23b : Datum :=
  { id := "pylkkanen2008_ex23b"
    source := ⟨"pylkkanen-2008", "ch. 2, (23b)"⟩
    reportedIn := none
    language := "gand1255"
    primaryText := "Katonga ya-kwaant-i-dde Mukasa ensawo."
    glossedTokens := [("Katonga", "Katonga"), ("ya-kwaant-i-dde", "3SG.PAST-hold-APPL-PAST"), ("Mukasa", "Mukasa"), ("ensawo", "bag")]
    glossedWords := [⟨[['K', 'a', 't', 'o', 'n', 'g', 'a']], [['K', 'a', 't', 'o', 'n', 'g', 'a']]⟩, ⟨[['y', 'a'], ['k', 'w', 'a', 'a', 'n', 't'], ['i'], ['d', 'd', 'e']], [['3', 'S', 'G', '.', 'P', 'A', 'S', 'T'], ['h', 'o', 'l', 'd'], ['A', 'P', 'P', 'L'], ['P', 'A', 'S', 'T']]⟩, ⟨[['M', 'u', 'k', 'a', 's', 'a']], [['M', 'u', 'k', 'a', 's', 'a']]⟩, ⟨[['e', 'n', 's', 'a', 'w', 'o']], [['b', 'a', 'g']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "static")] }

def ex24a : Datum :=
  { id := "pylkkanen2008_ex24a"
    source := ⟨"pylkkanen-2008", "ch. 2, (24a)"⟩
    reportedIn := none
    language := "vend1245"
    primaryText := "Ndi-do-shum-el-a musadzi."
    glossedTokens := [("Ndi-do-shum-el-a", "1SG-FUT-work-APPL-FV"), ("musadzi", "lady")]
    glossedWords := [⟨[['N', 'd', 'i'], ['d', 'o'], ['s', 'h', 'u', 'm'], ['e', 'l'], ['a']], [['1', 'S', 'G'], ['F', 'U', 'T'], ['w', 'o', 'r', 'k'], ['A', 'P', 'P', 'L'], ['F', 'V']]⟩, ⟨[['m', 'u', 's', 'a', 'd', 'z', 'i']], [['l', 'a', 'd', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "unergative")] }

def ex24b : Datum :=
  { id := "pylkkanen2008_ex24b"
    source := ⟨"pylkkanen-2008", "ch. 2, (24b)"⟩
    reportedIn := none
    language := "vend1245"
    primaryText := "Nd-o-far-el-a Mukasa khali."
    glossedTokens := [("Nd-o-far-el-a", "1SG-PAST-hold-APPL-FV"), ("Mukasa", "Mukasa"), ("khali", "pot")]
    glossedWords := [⟨[['N', 'd'], ['o'], ['f', 'a', 'r'], ['e', 'l'], ['a']], [['1', 'S', 'G'], ['P', 'A', 'S', 'T'], ['h', 'o', 'l', 'd'], ['A', 'P', 'P', 'L'], ['F', 'V']]⟩, ⟨[['M', 'u', 'k', 'a', 's', 'a']], [['M', 'u', 'k', 'a', 's', 'a']]⟩, ⟨[['k', 'h', 'a', 'l', 'i']], [['p', 'o', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "static")] }

def ex25a : Datum :=
  { id := "pylkkanen2008_ex25a"
    source := ⟨"pylkkanen-2008", "ch. 2, (25a)"⟩
    reportedIn := none
    language := "alba1267"
    primaryText := "I vrapova."
    glossedTokens := [("I", "him.DAT.CL"), ("vrapova", "ran.1SG")]
    glossedWords := [⟨[['I']], [['h', 'i', 'm', '.', 'D', 'A', 'T', '.', 'C', 'L']]⟩, ⟨[['v', 'r', 'a', 'p', 'o', 'v', 'a']], [['r', 'a', 'n', '.', '1', 'S', 'G']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "unergative")] }

def ex25b : Datum :=
  { id := "pylkkanen2008_ex25b"
    source := ⟨"pylkkanen-2008", "ch. 2, (25b)"⟩
    reportedIn := none
    language := "alba1267"
    primaryText := "Agimi i mban Drites çanten time."
    glossedTokens := [("Agimi", "Agim.NOM"), ("i", "CL"), ("mban", "holds"), ("Drites", "Drita.DAT"), ("çanten", "bag.ACC"), ("time", "my")]
    glossedWords := [⟨[['A', 'g', 'i', 'm', 'i']], [['A', 'g', 'i', 'm', '.', 'N', 'O', 'M']]⟩, ⟨[['i']], [['C', 'L']]⟩, ⟨[['m', 'b', 'a', 'n']], [['h', 'o', 'l', 'd', 's']]⟩, ⟨[['D', 'r', 'i', 't', 'e', 's']], [['D', 'r', 'i', 't', 'a', '.', 'D', 'A', 'T']]⟩, ⟨[['ç', 'a', 'n', 't', 'e', 'n']], [['b', 'a', 'g', '.', 'A', 'C', 'C']]⟩, ⟨[['t', 'i', 'm', 'e']], [['m', 'y']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "static")] }

def ex26a : Datum :=
  { id := "pylkkanen2008_ex26a"
    source := ⟨"pylkkanen-2008", "ch. 2, (26a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I gave Mary the meat raw."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "depictiveObject")] }

def ex26b : Datum :=
  { id := "pylkkanen2008_ex26b"
    source := ⟨"pylkkanen-2008", "ch. 2, (26b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I gave Mary the meat hungry."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("test", "depictiveApplied")] }

def ex40a : Datum :=
  { id := "pylkkanen2008_ex40a"
    source := ⟨"pylkkanen-2008", "ch. 2, (40a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-ga hadaka-de Hanako-ni hon-o yonda."
    glossedTokens := [("Taroo-ga", "Taro-NOM"), ("hadaka-de", "naked"), ("Hanako-ni", "Hanako-DAT"), ("hon-o", "book-ACC"), ("yonda", "read.PAST")]
    glossedWords := [⟨[['T', 'a', 'r', 'o', 'o'], ['g', 'a']], [['T', 'a', 'r', 'o'], ['N', 'O', 'M']]⟩, ⟨[['h', 'a', 'd', 'a', 'k', 'a'], ['d', 'e']], [['n', 'a', 'k', 'e', 'd']]⟩, ⟨[['H', 'a', 'n', 'a', 'k', 'o'], ['n', 'i']], [['H', 'a', 'n', 'a', 'k', 'o'], ['D', 'A', 'T']]⟩, ⟨[['h', 'o', 'n'], ['o']], [['b', 'o', 'o', 'k'], ['A', 'C', 'C']]⟩, ⟨[['y', 'o', 'n', 'd', 'a']], [['r', 'e', 'a', 'd', '.', 'P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("test", "depictiveApplied")] }

def ex43a : Datum :=
  { id := "pylkkanen2008_ex43a"
    source := ⟨"pylkkanen-2008", "ch. 2, (43a)"⟩
    reportedIn := none
    language := "gand1255"
    primaryText := "Mustafa ya-ko-le-dde Katonga nga mulwadde."
    glossedTokens := [("Mustafa", "Mustafa"), ("ya-ko-le-dde", "3SG.PAST-work-APPL-PAST"), ("Katonga", "Katonga"), ("nga", ""), ("mulwadde", "sick")]
    glossedWords := [⟨[['M', 'u', 's', 't', 'a', 'f', 'a']], [['M', 'u', 's', 't', 'a', 'f', 'a']]⟩, ⟨[['y', 'a'], ['k', 'o'], ['l', 'e'], ['d', 'd', 'e']], [['3', 'S', 'G', '.', 'P', 'A', 'S', 'T'], ['w', 'o', 'r', 'k'], ['A', 'P', 'P', 'L'], ['P', 'A', 'S', 'T']]⟩, ⟨[['K', 'a', 't', 'o', 'n', 'g', 'a']], [['K', 'a', 't', 'o', 'n', 'g', 'a']]⟩, ⟨[['n', 'g', 'a']], [[]]⟩, ⟨[['m', 'u', 'l', 'w', 'a', 'd', 'd', 'e']], [['s', 'i', 'c', 'k']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Mustafa is healthy and Katonga is sick."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "depictiveApplied")] }

def ex12 : Datum :=
  { id := "pylkkanen2008_ex12"
    source := ⟨"pylkkanen-2008", "ch. 2, (12)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Totuk-i Mary-hanthey panci-lul humchi-ess-ta."
    glossedTokens := [("Totuk-i", "thief-NOM"), ("Mary-hanthey", "Mary-DAT"), ("panci-lul", "ring-ACC"), ("humchi-ess-ta", "steal-PAST-PLAIN")]
    glossedWords := [⟨[['T', 'o', 't', 'u', 'k'], ['i']], [['t', 'h', 'i', 'e', 'f'], ['N', 'O', 'M']]⟩, ⟨[['M', 'a', 'r', 'y'], ['h', 'a', 'n', 't', 'h', 'e', 'y']], [['M', 'a', 'r', 'y'], ['D', 'A', 'T']]⟩, ⟨[['p', 'a', 'n', 'c', 'i'], ['l', 'u', 'l']], [['r', 'i', 'n', 'g'], ['A', 'C', 'C']]⟩, ⟨[['h', 'u', 'm', 'c', 'h', 'i'], ['e', 's', 's'], ['t', 'a']], [['s', 't', 'e', 'a', 'l'], ['P', 'A', 'S', 'T'], ['P', 'L', 'A', 'I', 'N']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "baseline"), ("relation", "source")] }

def ex82a : Datum :=
  { id := "pylkkanen2008_ex82a"
    source := ⟨"pylkkanen-2008", "ch. 2, (82a)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "Ha-yalda kilkela le-Dan et ha-radio."
    glossedTokens := [("Ha-yalda", "the-girl"), ("kilkela", "spoiled"), ("le-Dan", "to-Dan"), ("et", "ACC"), ("ha-radio", "the-radio")]
    glossedWords := [⟨[['H', 'a'], ['y', 'a', 'l', 'd', 'a']], [['t', 'h', 'e'], ['g', 'i', 'r', 'l']]⟩, ⟨[['k', 'i', 'l', 'k', 'e', 'l', 'a']], [['s', 'p', 'o', 'i', 'l', 'e', 'd']]⟩, ⟨[['l', 'e'], ['D', 'a', 'n']], [['t', 'o'], ['D', 'a', 'n']]⟩, ⟨[['e', 't']], [['A', 'C', 'C']]⟩, ⟨[['h', 'a'], ['r', 'a', 'd', 'i', 'o']], [['t', 'h', 'e'], ['r', 'a', 'd', 'i', 'o']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "baseline"), ("relation", "source"), ("construction", "possessorDative")] }

def ex120a : Datum :=
  { id := "pylkkanen2008_ex120a"
    source := ⟨"pylkkanen-2008", "ch. 2, (120a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Hanako-ga dorobou-ni yubiwa-o to-rare-ta."
    glossedTokens := [("Hanako-ga", "Hanako-NOM"), ("dorobou-ni", "thief-DAT"), ("yubiwa-o", "ring-ACC"), ("to-rare-ta", "steal-PASS-PAST")]
    glossedWords := [⟨[['H', 'a', 'n', 'a', 'k', 'o'], ['g', 'a']], [['H', 'a', 'n', 'a', 'k', 'o'], ['N', 'O', 'M']]⟩, ⟨[['d', 'o', 'r', 'o', 'b', 'o', 'u'], ['n', 'i']], [['t', 'h', 'i', 'e', 'f'], ['D', 'A', 'T']]⟩, ⟨[['y', 'u', 'b', 'i', 'w', 'a'], ['o']], [['r', 'i', 'n', 'g'], ['A', 'C', 'C']]⟩, ⟨[['t', 'o'], ['r', 'a', 'r', 'e'], ['t', 'a']], [['s', 't', 'e', 'a', 'l'], ['P', 'A', 'S', 'S'], ['P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "baseline"), ("relation", "source"), ("construction", "adversityGapped")] }

def ex121a : Datum :=
  { id := "pylkkanen2008_ex121a"
    source := ⟨"pylkkanen-2008", "ch. 2, (121a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-ga Hanako-ni shinkoushukyoo-o hajime-rare-ta."
    glossedTokens := [("Taroo-ga", "Taro-NOM"), ("Hanako-ni", "Hanako-DAT"), ("shinkoushukyoo-o", "new.religion-ACC"), ("hajime-rare-ta", "begin-PASS-PAST")]
    glossedWords := [⟨[['T', 'a', 'r', 'o', 'o'], ['g', 'a']], [['T', 'a', 'r', 'o'], ['N', 'O', 'M']]⟩, ⟨[['H', 'a', 'n', 'a', 'k', 'o'], ['n', 'i']], [['H', 'a', 'n', 'a', 'k', 'o'], ['D', 'A', 'T']]⟩, ⟨[['s', 'h', 'i', 'n', 'k', 'o', 'u', 's', 'h', 'u', 'k', 'y', 'o', 'o'], ['o']], [['n', 'e', 'w', '.', 'r', 'e', 'l', 'i', 'g', 'i', 'o', 'n'], ['A', 'C', 'C']]⟩, ⟨[['h', 'a', 'j', 'i', 'm', 'e'], ['r', 'a', 'r', 'e'], ['t', 'a']], [['b', 'e', 'g', 'i', 'n'], ['P', 'A', 'S', 'S'], ['P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "baseline"), ("relation", "malefactive"), ("construction", "adversityGapless")] }

def ex95 : Datum :=
  { id := "pylkkanen2008_ex95"
    source := ⟨"pylkkanen-2008", "ch. 3, (95)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John cried the child."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("test", "rootCausativeUnergative")] }

def ex96 : Datum :=
  { id := "pylkkanen2008_ex96"
    source := ⟨"pylkkanen-2008", "ch. 3, (96)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "John-ga kodomo-o nak-asi-ta."
    glossedTokens := [("John-ga", "John-NOM"), ("kodomo-o", "child-ACC"), ("nak-asi-ta", "cry-CAUSE-PAST")]
    glossedWords := [⟨[['J', 'o', 'h', 'n'], ['g', 'a']], [['J', 'o', 'h', 'n'], ['N', 'O', 'M']]⟩, ⟨[['k', 'o', 'd', 'o', 'm', 'o'], ['o']], [['c', 'h', 'i', 'l', 'd'], ['A', 'C', 'C']]⟩, ⟨[['n', 'a', 'k'], ['a', 's', 'i'], ['t', 'a']], [['c', 'r', 'y'], ['C', 'A', 'U', 'S', 'E'], ['P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "rootCausativeUnergative")] }

def all : List Datum := [ex19a, ex19b, ex19c, ex19d, ex19e, ex19f, ex20a, ex20b, ex21a, ex21b, ex22a, ex22b, ex23a, ex23b, ex24a, ex24b, ex25a, ex25b, ex26a, ex26b, ex40a, ex43a, ex12, ex82a, ex120a, ex121a, ex95, ex96]

end Pylkkanen2008.Examples
