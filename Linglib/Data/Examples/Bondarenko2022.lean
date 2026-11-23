module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Bondarenko2022` — typed example data

Auto-generated from `Linglib/Data/Examples/Bondarenko2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Bondarenko2022.Examples`.
-/

@[expose] public section

namespace Bondarenko2022.Examples

def ch2_105 : Datum :=
  { id := "bondarenko2022_ch2_105"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (105)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Ideja čto grjadut reformy javljaetsja vernoj."
    glossedTokens := [("Ideja", "idea"), ("čto", "COMP"), ("grjadut", "are.coming"), ("reformy", "reforms"), ("javljaetsja", "is"), ("vernoj", "true")]
    glossedWords := [⟨['I', 'd', 'e', 'j', 'a'], ['i', 'd', 'e', 'a'], [⟨['I', 'd', 'e', 'j', 'a'], ['i', 'd', 'e', 'a'], none⟩]⟩, ⟨['č', 't', 'o'], ['C', 'O', 'M', 'P'], [⟨['č', 't', 'o'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['g', 'r', 'j', 'a', 'd', 'u', 't'], ['a', 'r', 'e', '.', 'c', 'o', 'm', 'i', 'n', 'g'], [⟨['g', 'r', 'j', 'a', 'd', 'u', 't'], ['a', 'r', 'e', '.', 'c', 'o', 'm', 'i', 'n', 'g'], none⟩]⟩, ⟨['r', 'e', 'f', 'o', 'r', 'm', 'y'], ['r', 'e', 'f', 'o', 'r', 'm', 's'], [⟨['r', 'e', 'f', 'o', 'r', 'm', 'y'], ['r', 'e', 'f', 'o', 'r', 'm', 's'], none⟩]⟩, ⟨['j', 'a', 'v', 'l', 'j', 'a', 'e', 't', 's', 'j', 'a'], ['i', 's'], [⟨['j', 'a', 'v', 'l', 'j', 'a', 'e', 't', 's', 'j', 'a'], ['i', 's'], none⟩]⟩, ⟨['v', 'e', 'r', 'n', 'o', 'j'], ['t', 'r', 'u', 'e'], [⟨['v', 'e', 'r', 'n', 'o', 'j'], ['t', 'r', 'u', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Situacija čto grjadut reformy javljaetsja vernoj.", .ungrammatical), ("Ideja čto grjadut reformy javljaetsja ošibočnoj.", .acceptable)]
    readings := []
    paperFeatures := [("diagnostic", "truth-predicates"), ("nounSort", "content")] }

def ch2_106 : Datum :=
  { id := "bondarenko2022_ch2_106"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (106)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Swuna-ka mwuncey-lul phwul-ess-ta-nun cwucang-i kecis-i-ta."
    glossedTokens := [("Swuna-ka", "Swuna-NOM"), ("mwuncey-lul", "problem-ACC"), ("phwul-ess-ta-nun", "solve-PST-DECL-ADN"), ("cwucang-i", "claim-NOM"), ("kecis-i-ta", "falsehood-COP-DECL")]
    glossedWords := [⟨['S', 'w', 'u', 'n', 'a', '-', 'k', 'a'], ['S', 'w', 'u', 'n', 'a', '-', 'N', 'O', 'M'], [⟨['S', 'w', 'u', 'n', 'a'], ['S', 'w', 'u', 'n', 'a'], none⟩, ⟨['k', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['m', 'w', 'u', 'n', 'c', 'e', 'y', '-', 'l', 'u', 'l'], ['p', 'r', 'o', 'b', 'l', 'e', 'm', '-', 'A', 'C', 'C'], [⟨['m', 'w', 'u', 'n', 'c', 'e', 'y'], ['p', 'r', 'o', 'b', 'l', 'e', 'm'], none⟩, ⟨['l', 'u', 'l'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['p', 'h', 'w', 'u', 'l', '-', 'e', 's', 's', '-', 't', 'a', '-', 'n', 'u', 'n'], ['s', 'o', 'l', 'v', 'e', '-', 'P', 'S', 'T', '-', 'D', 'E', 'C', 'L', '-', 'A', 'D', 'N'], [⟨['p', 'h', 'w', 'u', 'l'], ['s', 'o', 'l', 'v', 'e'], none⟩, ⟨['e', 's', 's'], ['P', 'S', 'T'], some '-'⟩, ⟨['t', 'a'], ['D', 'E', 'C', 'L'], some '-'⟩, ⟨['n', 'u', 'n'], ['A', 'D', 'N'], some '-'⟩]⟩, ⟨['c', 'w', 'u', 'c', 'a', 'n', 'g', '-', 'i'], ['c', 'l', 'a', 'i', 'm', '-', 'N', 'O', 'M'], [⟨['c', 'w', 'u', 'c', 'a', 'n', 'g'], ['c', 'l', 'a', 'i', 'm'], none⟩, ⟨['i'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['k', 'e', 'c', 'i', 's', '-', 'i', '-', 't', 'a'], ['f', 'a', 'l', 's', 'e', 'h', 'o', 'o', 'd', '-', 'C', 'O', 'P', '-', 'D', 'E', 'C', 'L'], [⟨['k', 'e', 'c', 'i', 's'], ['f', 'a', 'l', 's', 'e', 'h', 'o', 'o', 'd'], none⟩, ⟨['i'], ['C', 'O', 'P'], some '-'⟩, ⟨['t', 'a'], ['D', 'E', 'C', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Swuna-ka mwuncey-lul phwul-ess-ta-nun cwucang-i cham-i-ta.", .acceptable)]
    readings := []
    paperFeatures := [("diagnostic", "truth-predicates"), ("nounSort", "content")] }

def ch2_107 : Datum :=
  { id := "bondarenko2022_ch2_107"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (107)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Swuna-ka mwuncey-lul phwul-un sanghwang-i kecis-i-ta."
    glossedTokens := [("Swuna-ka", "Swuna-NOM"), ("mwuncey-lul", "problem-ACC"), ("phwul-un", "solve-ADN"), ("sanghwang-i", "situation-NOM"), ("kecis-i-ta", "falsehood-COP-DECL")]
    glossedWords := [⟨['S', 'w', 'u', 'n', 'a', '-', 'k', 'a'], ['S', 'w', 'u', 'n', 'a', '-', 'N', 'O', 'M'], [⟨['S', 'w', 'u', 'n', 'a'], ['S', 'w', 'u', 'n', 'a'], none⟩, ⟨['k', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['m', 'w', 'u', 'n', 'c', 'e', 'y', '-', 'l', 'u', 'l'], ['p', 'r', 'o', 'b', 'l', 'e', 'm', '-', 'A', 'C', 'C'], [⟨['m', 'w', 'u', 'n', 'c', 'e', 'y'], ['p', 'r', 'o', 'b', 'l', 'e', 'm'], none⟩, ⟨['l', 'u', 'l'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['p', 'h', 'w', 'u', 'l', '-', 'u', 'n'], ['s', 'o', 'l', 'v', 'e', '-', 'A', 'D', 'N'], [⟨['p', 'h', 'w', 'u', 'l'], ['s', 'o', 'l', 'v', 'e'], none⟩, ⟨['u', 'n'], ['A', 'D', 'N'], some '-'⟩]⟩, ⟨['s', 'a', 'n', 'g', 'h', 'w', 'a', 'n', 'g', '-', 'i'], ['s', 'i', 't', 'u', 'a', 't', 'i', 'o', 'n', '-', 'N', 'O', 'M'], [⟨['s', 'a', 'n', 'g', 'h', 'w', 'a', 'n', 'g'], ['s', 'i', 't', 'u', 'a', 't', 'i', 'o', 'n'], none⟩, ⟨['i'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['k', 'e', 'c', 'i', 's', '-', 'i', '-', 't', 'a'], ['f', 'a', 'l', 's', 'e', 'h', 'o', 'o', 'd', '-', 'C', 'O', 'P', '-', 'D', 'E', 'C', 'L'], [⟨['k', 'e', 'c', 'i', 's'], ['f', 'a', 'l', 's', 'e', 'h', 'o', 'o', 'd'], none⟩, ⟨['i'], ['C', 'O', 'P'], some '-'⟩, ⟨['t', 'a'], ['D', 'E', 'C', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := [("Swuna-ka mwuncey-lul phwul-un sanghwang-i cham-i-ta.", .ungrammatical)]
    readings := []
    paperFeatures := [("diagnostic", "truth-predicates"), ("nounSort", "situation")] }

def ch2_108 : Datum :=
  { id := "bondarenko2022_ch2_108"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (108)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Včera proizošla situacija čto moj zakaz zaderžali."
    glossedTokens := [("Včera", "yesterday"), ("proizošla", "occured"), ("situacija", "situation"), ("čto", "COMP"), ("moj", "my"), ("zakaz", "order"), ("zaderžali", "delayed")]
    glossedWords := [⟨['V', 'č', 'e', 'r', 'a'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['V', 'č', 'e', 'r', 'a'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩, ⟨['p', 'r', 'o', 'i', 'z', 'o', 'š', 'l', 'a'], ['o', 'c', 'c', 'u', 'r', 'e', 'd'], [⟨['p', 'r', 'o', 'i', 'z', 'o', 'š', 'l', 'a'], ['o', 'c', 'c', 'u', 'r', 'e', 'd'], none⟩]⟩, ⟨['s', 'i', 't', 'u', 'a', 'c', 'i', 'j', 'a'], ['s', 'i', 't', 'u', 'a', 't', 'i', 'o', 'n'], [⟨['s', 'i', 't', 'u', 'a', 'c', 'i', 'j', 'a'], ['s', 'i', 't', 'u', 'a', 't', 'i', 'o', 'n'], none⟩]⟩, ⟨['č', 't', 'o'], ['C', 'O', 'M', 'P'], [⟨['č', 't', 'o'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['m', 'o', 'j'], ['m', 'y'], [⟨['m', 'o', 'j'], ['m', 'y'], none⟩]⟩, ⟨['z', 'a', 'k', 'a', 'z'], ['o', 'r', 'd', 'e', 'r'], [⟨['z', 'a', 'k', 'a', 'z'], ['o', 'r', 'd', 'e', 'r'], none⟩]⟩, ⟨['z', 'a', 'd', 'e', 'r', 'ž', 'a', 'l', 'i'], ['d', 'e', 'l', 'a', 'y', 'e', 'd'], [⟨['z', 'a', 'd', 'e', 'r', 'ž', 'a', 'l', 'i'], ['d', 'e', 'l', 'a', 'y', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Včera proizošla ideja čto moj zakaz zaderžali.", .ungrammatical), ("Včera slučilas’ situacija čto moj zakaz zaderžali.", .acceptable)]
    readings := []
    paperFeatures := [("diagnostic", "occurrence-predicates"), ("nounSort", "situation")] }

def ch2_109 : Datum :=
  { id := "bondarenko2022_ch2_109"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (109)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Swuna-ka mwuncey-lul phwul-ess-ta-nun cwucang-i ilena-ss-ta"
    glossedTokens := [("Swuna-ka", "Swuna-NOM"), ("mwuncey-lul", "problem-ACC"), ("phwul-ess-ta-nun", "solve-PST-DECL-ADN"), ("cwucang-i", "claim-NOM"), ("ilena-ss-ta", "occur-PST-DECL")]
    glossedWords := [⟨['S', 'w', 'u', 'n', 'a', '-', 'k', 'a'], ['S', 'w', 'u', 'n', 'a', '-', 'N', 'O', 'M'], [⟨['S', 'w', 'u', 'n', 'a'], ['S', 'w', 'u', 'n', 'a'], none⟩, ⟨['k', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['m', 'w', 'u', 'n', 'c', 'e', 'y', '-', 'l', 'u', 'l'], ['p', 'r', 'o', 'b', 'l', 'e', 'm', '-', 'A', 'C', 'C'], [⟨['m', 'w', 'u', 'n', 'c', 'e', 'y'], ['p', 'r', 'o', 'b', 'l', 'e', 'm'], none⟩, ⟨['l', 'u', 'l'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['p', 'h', 'w', 'u', 'l', '-', 'e', 's', 's', '-', 't', 'a', '-', 'n', 'u', 'n'], ['s', 'o', 'l', 'v', 'e', '-', 'P', 'S', 'T', '-', 'D', 'E', 'C', 'L', '-', 'A', 'D', 'N'], [⟨['p', 'h', 'w', 'u', 'l'], ['s', 'o', 'l', 'v', 'e'], none⟩, ⟨['e', 's', 's'], ['P', 'S', 'T'], some '-'⟩, ⟨['t', 'a'], ['D', 'E', 'C', 'L'], some '-'⟩, ⟨['n', 'u', 'n'], ['A', 'D', 'N'], some '-'⟩]⟩, ⟨['c', 'w', 'u', 'c', 'a', 'n', 'g', '-', 'i'], ['c', 'l', 'a', 'i', 'm', '-', 'N', 'O', 'M'], [⟨['c', 'w', 'u', 'c', 'a', 'n', 'g'], ['c', 'l', 'a', 'i', 'm'], none⟩, ⟨['i'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['i', 'l', 'e', 'n', 'a', '-', 's', 's', '-', 't', 'a'], ['o', 'c', 'c', 'u', 'r', '-', 'P', 'S', 'T', '-', 'D', 'E', 'C', 'L'], [⟨['i', 'l', 'e', 'n', 'a'], ['o', 'c', 'c', 'u', 'r'], none⟩, ⟨['s', 's'], ['P', 'S', 'T'], some '-'⟩, ⟨['t', 'a'], ['D', 'E', 'C', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "occurrence-predicates"), ("nounSort", "content")] }

def ch2_110 : Datum :=
  { id := "bondarenko2022_ch2_110"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (110)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Swuna-ka mwuncey-lul phwul-un sanghwang-i ilena-ss-ta"
    glossedTokens := [("Swuna-ka", "Swuna-NOM"), ("mwuncey-lul", "problem-ACC"), ("phwul-un", "solve-ADN"), ("sanghwang-i", "situation-NOM"), ("ilena-ss-ta", "occur-PST-DECL")]
    glossedWords := [⟨['S', 'w', 'u', 'n', 'a', '-', 'k', 'a'], ['S', 'w', 'u', 'n', 'a', '-', 'N', 'O', 'M'], [⟨['S', 'w', 'u', 'n', 'a'], ['S', 'w', 'u', 'n', 'a'], none⟩, ⟨['k', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['m', 'w', 'u', 'n', 'c', 'e', 'y', '-', 'l', 'u', 'l'], ['p', 'r', 'o', 'b', 'l', 'e', 'm', '-', 'A', 'C', 'C'], [⟨['m', 'w', 'u', 'n', 'c', 'e', 'y'], ['p', 'r', 'o', 'b', 'l', 'e', 'm'], none⟩, ⟨['l', 'u', 'l'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['p', 'h', 'w', 'u', 'l', '-', 'u', 'n'], ['s', 'o', 'l', 'v', 'e', '-', 'A', 'D', 'N'], [⟨['p', 'h', 'w', 'u', 'l'], ['s', 'o', 'l', 'v', 'e'], none⟩, ⟨['u', 'n'], ['A', 'D', 'N'], some '-'⟩]⟩, ⟨['s', 'a', 'n', 'g', 'h', 'w', 'a', 'n', 'g', '-', 'i'], ['s', 'i', 't', 'u', 'a', 't', 'i', 'o', 'n', '-', 'N', 'O', 'M'], [⟨['s', 'a', 'n', 'g', 'h', 'w', 'a', 'n', 'g'], ['s', 'i', 't', 'u', 'a', 't', 'i', 'o', 'n'], none⟩, ⟨['i'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['i', 'l', 'e', 'n', 'a', '-', 's', 's', '-', 't', 'a'], ['o', 'c', 'c', 'u', 'r', '-', 'P', 'S', 'T', '-', 'D', 'E', 'C', 'L'], [⟨['i', 'l', 'e', 'n', 'a'], ['o', 'c', 'c', 'u', 'r'], none⟩, ⟨['s', 's'], ['P', 'S', 'T'], some '-'⟩, ⟨['t', 'a'], ['D', 'E', 'C', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "occurrence-predicates"), ("nounSort", "situation")] }

def ch2_111 : Datum :=
  { id := "bondarenko2022_ch2_111"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (111)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kore1280"
    primaryText := "Mina-ka Swuna-ka mwuncey-lul phwul-ess-ta-nun cwucang-ul alachay-ss-ta"
    glossedTokens := [("Mina-ka", "Mina-NOM"), ("Swuna-ka", "Swuna-NOM"), ("mwuncey-lul", "problem-ACC"), ("phwul-ess-ta-nun", "solve-PST-DECL-ADN"), ("cwucang-ul", "claim-ACC"), ("alachay-ss-ta", "notice-PST-DECL")]
    glossedWords := [⟨['M', 'i', 'n', 'a', '-', 'k', 'a'], ['M', 'i', 'n', 'a', '-', 'N', 'O', 'M'], [⟨['M', 'i', 'n', 'a'], ['M', 'i', 'n', 'a'], none⟩, ⟨['k', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['S', 'w', 'u', 'n', 'a', '-', 'k', 'a'], ['S', 'w', 'u', 'n', 'a', '-', 'N', 'O', 'M'], [⟨['S', 'w', 'u', 'n', 'a'], ['S', 'w', 'u', 'n', 'a'], none⟩, ⟨['k', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['m', 'w', 'u', 'n', 'c', 'e', 'y', '-', 'l', 'u', 'l'], ['p', 'r', 'o', 'b', 'l', 'e', 'm', '-', 'A', 'C', 'C'], [⟨['m', 'w', 'u', 'n', 'c', 'e', 'y'], ['p', 'r', 'o', 'b', 'l', 'e', 'm'], none⟩, ⟨['l', 'u', 'l'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['p', 'h', 'w', 'u', 'l', '-', 'e', 's', 's', '-', 't', 'a', '-', 'n', 'u', 'n'], ['s', 'o', 'l', 'v', 'e', '-', 'P', 'S', 'T', '-', 'D', 'E', 'C', 'L', '-', 'A', 'D', 'N'], [⟨['p', 'h', 'w', 'u', 'l'], ['s', 'o', 'l', 'v', 'e'], none⟩, ⟨['e', 's', 's'], ['P', 'S', 'T'], some '-'⟩, ⟨['t', 'a'], ['D', 'E', 'C', 'L'], some '-'⟩, ⟨['n', 'u', 'n'], ['A', 'D', 'N'], some '-'⟩]⟩, ⟨['c', 'w', 'u', 'c', 'a', 'n', 'g', '-', 'u', 'l'], ['c', 'l', 'a', 'i', 'm', '-', 'A', 'C', 'C'], [⟨['c', 'w', 'u', 'c', 'a', 'n', 'g'], ['c', 'l', 'a', 'i', 'm'], none⟩, ⟨['u', 'l'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['a', 'l', 'a', 'c', 'h', 'a', 'y', '-', 's', 's', '-', 't', 'a'], ['n', 'o', 't', 'i', 'c', 'e', '-', 'P', 'S', 'T', '-', 'D', 'E', 'C', 'L'], [⟨['a', 'l', 'a', 'c', 'h', 'a', 'y'], ['n', 'o', 't', 'i', 'c', 'e'], none⟩, ⟨['s', 's'], ['P', 'S', 'T'], some '-'⟩, ⟨['t', 'a'], ['D', 'E', 'C', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "situation-only-predicate-notice"), ("nounSort", "content")] }

def ch2_112 : Datum :=
  { id := "bondarenko2022_ch2_112"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (112)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Mina-ka Swuna-ka mwuncey-lul phwul-un sanghwang-ul alachay-ss-ta"
    glossedTokens := [("Mina-ka", "Mina-NOM"), ("Swuna-ka", "Swuna-NOM"), ("mwuncey-lul", "problem-ACC"), ("phwul-un", "solve-ADN"), ("sanghwang-ul", "situation-ACC"), ("alachay-ss-ta", "notice-PST-DECL")]
    glossedWords := [⟨['M', 'i', 'n', 'a', '-', 'k', 'a'], ['M', 'i', 'n', 'a', '-', 'N', 'O', 'M'], [⟨['M', 'i', 'n', 'a'], ['M', 'i', 'n', 'a'], none⟩, ⟨['k', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['S', 'w', 'u', 'n', 'a', '-', 'k', 'a'], ['S', 'w', 'u', 'n', 'a', '-', 'N', 'O', 'M'], [⟨['S', 'w', 'u', 'n', 'a'], ['S', 'w', 'u', 'n', 'a'], none⟩, ⟨['k', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['m', 'w', 'u', 'n', 'c', 'e', 'y', '-', 'l', 'u', 'l'], ['p', 'r', 'o', 'b', 'l', 'e', 'm', '-', 'A', 'C', 'C'], [⟨['m', 'w', 'u', 'n', 'c', 'e', 'y'], ['p', 'r', 'o', 'b', 'l', 'e', 'm'], none⟩, ⟨['l', 'u', 'l'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['p', 'h', 'w', 'u', 'l', '-', 'u', 'n'], ['s', 'o', 'l', 'v', 'e', '-', 'A', 'D', 'N'], [⟨['p', 'h', 'w', 'u', 'l'], ['s', 'o', 'l', 'v', 'e'], none⟩, ⟨['u', 'n'], ['A', 'D', 'N'], some '-'⟩]⟩, ⟨['s', 'a', 'n', 'g', 'h', 'w', 'a', 'n', 'g', '-', 'u', 'l'], ['s', 'i', 't', 'u', 'a', 't', 'i', 'o', 'n', '-', 'A', 'C', 'C'], [⟨['s', 'a', 'n', 'g', 'h', 'w', 'a', 'n', 'g'], ['s', 'i', 't', 'u', 'a', 't', 'i', 'o', 'n'], none⟩, ⟨['u', 'l'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['a', 'l', 'a', 'c', 'h', 'a', 'y', '-', 's', 's', '-', 't', 'a'], ['n', 'o', 't', 'i', 'c', 'e', '-', 'P', 'S', 'T', '-', 'D', 'E', 'C', 'L'], [⟨['a', 'l', 'a', 'c', 'h', 'a', 'y'], ['n', 'o', 't', 'i', 'c', 'e'], none⟩, ⟨['s', 's'], ['P', 'S', 'T'], some '-'⟩, ⟨['t', 'a'], ['D', 'E', 'C', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "situation-only-predicate-notice"), ("nounSort", "situation")] }

def ch2_120a : Datum :=
  { id := "bondarenko2022_ch2_120a"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (120a)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Lena zametila slux čto èta ženščina priexala na kone."
    glossedTokens := [("Lena", "Lena"), ("zametila", "noticed"), ("slux", "rumor"), ("čto", "COMP"), ("èta", "this"), ("ženščina", "woman"), ("priexala", "arrived"), ("na", "on"), ("kone", "horse")]
    glossedWords := [⟨['L', 'e', 'n', 'a'], ['L', 'e', 'n', 'a'], [⟨['L', 'e', 'n', 'a'], ['L', 'e', 'n', 'a'], none⟩]⟩, ⟨['z', 'a', 'm', 'e', 't', 'i', 'l', 'a'], ['n', 'o', 't', 'i', 'c', 'e', 'd'], [⟨['z', 'a', 'm', 'e', 't', 'i', 'l', 'a'], ['n', 'o', 't', 'i', 'c', 'e', 'd'], none⟩]⟩, ⟨['s', 'l', 'u', 'x'], ['r', 'u', 'm', 'o', 'r'], [⟨['s', 'l', 'u', 'x'], ['r', 'u', 'm', 'o', 'r'], none⟩]⟩, ⟨['č', 't', 'o'], ['C', 'O', 'M', 'P'], [⟨['č', 't', 'o'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['è', 't', 'a'], ['t', 'h', 'i', 's'], [⟨['è', 't', 'a'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['ž', 'e', 'n', 'š', 'č', 'i', 'n', 'a'], ['w', 'o', 'm', 'a', 'n'], [⟨['ž', 'e', 'n', 'š', 'č', 'i', 'n', 'a'], ['w', 'o', 'm', 'a', 'n'], none⟩]⟩, ⟨['p', 'r', 'i', 'e', 'x', 'a', 'l', 'a'], ['a', 'r', 'r', 'i', 'v', 'e', 'd'], [⟨['p', 'r', 'i', 'e', 'x', 'a', 'l', 'a'], ['a', 'r', 'r', 'i', 'v', 'e', 'd'], none⟩]⟩, ⟨['n', 'a'], ['o', 'n'], [⟨['n', 'a'], ['o', 'n'], none⟩]⟩, ⟨['k', 'o', 'n', 'e'], ['h', 'o', 'r', 's', 'e'], [⟨['k', 'o', 'n', 'e'], ['h', 'o', 'r', 's', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Lena zametila slučaj čto èta ženščina priexala na kone.", .acceptable)]
    readings := []
    paperFeatures := [("diagnostic", "substitution"), ("role", "premise-a")] }

def ch2_120b : Datum :=
  { id := "bondarenko2022_ch2_120b"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (120b)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "èta ženščina — koroleva Velikobritanii."
    glossedTokens := [("èta", "this"), ("ženščina", "woman"), ("koroleva", "queen"), ("Velikobritanii", "Great.Britain")]
    glossedWords := [⟨['è', 't', 'a'], ['t', 'h', 'i', 's'], [⟨['è', 't', 'a'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['ž', 'e', 'n', 'š', 'č', 'i', 'n', 'a'], ['w', 'o', 'm', 'a', 'n'], [⟨['ž', 'e', 'n', 'š', 'č', 'i', 'n', 'a'], ['w', 'o', 'm', 'a', 'n'], none⟩]⟩, ⟨['k', 'o', 'r', 'o', 'l', 'e', 'v', 'a'], ['q', 'u', 'e', 'e', 'n'], [⟨['k', 'o', 'r', 'o', 'l', 'e', 'v', 'a'], ['q', 'u', 'e', 'e', 'n'], none⟩]⟩, ⟨['V', 'e', 'l', 'i', 'k', 'o', 'b', 'r', 'i', 't', 'a', 'n', 'i', 'i'], ['G', 'r', 'e', 'a', 't', '.', 'B', 'r', 'i', 't', 'a', 'i', 'n'], [⟨['V', 'e', 'l', 'i', 'k', 'o', 'b', 'r', 'i', 't', 'a', 'n', 'i', 'i'], ['G', 'r', 'e', 'a', 't', '.', 'B', 'r', 'i', 't', 'a', 'i', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "substitution"), ("role", "premise-b")] }

def ch2_120c : Datum :=
  { id := "bondarenko2022_ch2_120c"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (120c)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Lena zametila slux čto koroleva Velikobritanii priexala na kone."
    glossedTokens := [("Lena", "Lena"), ("zametila", "noticed"), ("slux", "rumor"), ("čto", "COMP"), ("koroleva", "queen"), ("Velikobritanii", "Great.Britain"), ("priexala", "arrived"), ("na", "on"), ("kone", "horse")]
    glossedWords := [⟨['L', 'e', 'n', 'a'], ['L', 'e', 'n', 'a'], [⟨['L', 'e', 'n', 'a'], ['L', 'e', 'n', 'a'], none⟩]⟩, ⟨['z', 'a', 'm', 'e', 't', 'i', 'l', 'a'], ['n', 'o', 't', 'i', 'c', 'e', 'd'], [⟨['z', 'a', 'm', 'e', 't', 'i', 'l', 'a'], ['n', 'o', 't', 'i', 'c', 'e', 'd'], none⟩]⟩, ⟨['s', 'l', 'u', 'x'], ['r', 'u', 'm', 'o', 'r'], [⟨['s', 'l', 'u', 'x'], ['r', 'u', 'm', 'o', 'r'], none⟩]⟩, ⟨['č', 't', 'o'], ['C', 'O', 'M', 'P'], [⟨['č', 't', 'o'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['k', 'o', 'r', 'o', 'l', 'e', 'v', 'a'], ['q', 'u', 'e', 'e', 'n'], [⟨['k', 'o', 'r', 'o', 'l', 'e', 'v', 'a'], ['q', 'u', 'e', 'e', 'n'], none⟩]⟩, ⟨['V', 'e', 'l', 'i', 'k', 'o', 'b', 'r', 'i', 't', 'a', 'n', 'i', 'i'], ['G', 'r', 'e', 'a', 't', '.', 'B', 'r', 'i', 't', 'a', 'i', 'n'], [⟨['V', 'e', 'l', 'i', 'k', 'o', 'b', 'r', 'i', 't', 'a', 'n', 'i', 'i'], ['G', 'r', 'e', 'a', 't', '.', 'B', 'r', 'i', 't', 'a', 'i', 'n'], none⟩]⟩, ⟨['p', 'r', 'i', 'e', 'x', 'a', 'l', 'a'], ['a', 'r', 'r', 'i', 'v', 'e', 'd'], [⟨['p', 'r', 'i', 'e', 'x', 'a', 'l', 'a'], ['a', 'r', 'r', 'i', 'v', 'e', 'd'], none⟩]⟩, ⟨['n', 'a'], ['o', 'n'], [⟨['n', 'a'], ['o', 'n'], none⟩]⟩, ⟨['k', 'o', 'n', 'e'], ['h', 'o', 'r', 's', 'e'], [⟨['k', 'o', 'n', 'e'], ['h', 'o', 'r', 's', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Lena zametila slučaj čto koroleva Velikobritanii priexala na kone.", .acceptable)]
    readings := []
    paperFeatures := [("diagnostic", "substitution"), ("role", "conclusion")] }

def ch2_121a : Datum :=
  { id := "bondarenko2022_ch2_121a"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (121a)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Mina-ka Swuna-ka mwuncey-lul phwul-ess-ta-nun cwucang-ul kiekhay-ss-ta."
    glossedTokens := [("Mina-ka", "Mina-NOM"), ("Swuna-ka", "Swuna-NOM"), ("mwuncey-lul", "problem-ACC"), ("phwul-ess-ta-nun", "solve-PST-DECL-ADN"), ("cwucang-ul", "claim-ACC"), ("kiekhay-ss-ta", "remember-PST-DECL")]
    glossedWords := [⟨['M', 'i', 'n', 'a', '-', 'k', 'a'], ['M', 'i', 'n', 'a', '-', 'N', 'O', 'M'], [⟨['M', 'i', 'n', 'a'], ['M', 'i', 'n', 'a'], none⟩, ⟨['k', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['S', 'w', 'u', 'n', 'a', '-', 'k', 'a'], ['S', 'w', 'u', 'n', 'a', '-', 'N', 'O', 'M'], [⟨['S', 'w', 'u', 'n', 'a'], ['S', 'w', 'u', 'n', 'a'], none⟩, ⟨['k', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['m', 'w', 'u', 'n', 'c', 'e', 'y', '-', 'l', 'u', 'l'], ['p', 'r', 'o', 'b', 'l', 'e', 'm', '-', 'A', 'C', 'C'], [⟨['m', 'w', 'u', 'n', 'c', 'e', 'y'], ['p', 'r', 'o', 'b', 'l', 'e', 'm'], none⟩, ⟨['l', 'u', 'l'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['p', 'h', 'w', 'u', 'l', '-', 'e', 's', 's', '-', 't', 'a', '-', 'n', 'u', 'n'], ['s', 'o', 'l', 'v', 'e', '-', 'P', 'S', 'T', '-', 'D', 'E', 'C', 'L', '-', 'A', 'D', 'N'], [⟨['p', 'h', 'w', 'u', 'l'], ['s', 'o', 'l', 'v', 'e'], none⟩, ⟨['e', 's', 's'], ['P', 'S', 'T'], some '-'⟩, ⟨['t', 'a'], ['D', 'E', 'C', 'L'], some '-'⟩, ⟨['n', 'u', 'n'], ['A', 'D', 'N'], some '-'⟩]⟩, ⟨['c', 'w', 'u', 'c', 'a', 'n', 'g', '-', 'u', 'l'], ['c', 'l', 'a', 'i', 'm', '-', 'A', 'C', 'C'], [⟨['c', 'w', 'u', 'c', 'a', 'n', 'g'], ['c', 'l', 'a', 'i', 'm'], none⟩, ⟨['u', 'l'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['k', 'i', 'e', 'k', 'h', 'a', 'y', '-', 's', 's', '-', 't', 'a'], ['r', 'e', 'm', 'e', 'm', 'b', 'e', 'r', '-', 'P', 'S', 'T', '-', 'D', 'E', 'C', 'L'], [⟨['k', 'i', 'e', 'k', 'h', 'a', 'y'], ['r', 'e', 'm', 'e', 'm', 'b', 'e', 'r'], none⟩, ⟨['s', 's'], ['P', 'S', 'T'], some '-'⟩, ⟨['t', 'a'], ['D', 'E', 'C', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "substitution"), ("nounSort", "content"), ("role", "premise-a")] }

def ch2_121b : Datum :=
  { id := "bondarenko2022_ch2_121b"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (121b)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Swuna-ka pan-eyse kacang khi-ga khu-ta."
    glossedTokens := [("Swuna-ka", "Swuna-NOM"), ("pan-eyse", "class-LOC"), ("kacang", "most"), ("khi-ga", "height-NOM"), ("khu-ta", "large-DECL")]
    glossedWords := [⟨['S', 'w', 'u', 'n', 'a', '-', 'k', 'a'], ['S', 'w', 'u', 'n', 'a', '-', 'N', 'O', 'M'], [⟨['S', 'w', 'u', 'n', 'a'], ['S', 'w', 'u', 'n', 'a'], none⟩, ⟨['k', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['p', 'a', 'n', '-', 'e', 'y', 's', 'e'], ['c', 'l', 'a', 's', 's', '-', 'L', 'O', 'C'], [⟨['p', 'a', 'n'], ['c', 'l', 'a', 's', 's'], none⟩, ⟨['e', 'y', 's', 'e'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['k', 'a', 'c', 'a', 'n', 'g'], ['m', 'o', 's', 't'], [⟨['k', 'a', 'c', 'a', 'n', 'g'], ['m', 'o', 's', 't'], none⟩]⟩, ⟨['k', 'h', 'i', '-', 'g', 'a'], ['h', 'e', 'i', 'g', 'h', 't', '-', 'N', 'O', 'M'], [⟨['k', 'h', 'i'], ['h', 'e', 'i', 'g', 'h', 't'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['k', 'h', 'u', '-', 't', 'a'], ['l', 'a', 'r', 'g', 'e', '-', 'D', 'E', 'C', 'L'], [⟨['k', 'h', 'u'], ['l', 'a', 'r', 'g', 'e'], none⟩, ⟨['t', 'a'], ['D', 'E', 'C', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "substitution"), ("role", "premise-b")] }

def ch2_121c : Datum :=
  { id := "bondarenko2022_ch2_121c"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (121c)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Mina-ka pan-eyse kacang khi-ga khun sonye-ka mwuncey-lul phwul-ess-ta-nun cwucang-ul kiekhay-ss-ta."
    glossedTokens := [("Mina-ka", "Mina-NOM"), ("pan-eyse", "class-LOC"), ("kacang", "most"), ("khi-ga", "height-NOM"), ("khun", "large"), ("sonye-ka", "girl-NOM"), ("mwuncey-lul", "problem-ACC"), ("phwul-ess-ta-nun", "solve-PST-DECL-ADN"), ("cwucang-ul", "claim-ACC"), ("kiekhay-ss-ta", "remember-PST-DECL")]
    glossedWords := [⟨['M', 'i', 'n', 'a', '-', 'k', 'a'], ['M', 'i', 'n', 'a', '-', 'N', 'O', 'M'], [⟨['M', 'i', 'n', 'a'], ['M', 'i', 'n', 'a'], none⟩, ⟨['k', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['p', 'a', 'n', '-', 'e', 'y', 's', 'e'], ['c', 'l', 'a', 's', 's', '-', 'L', 'O', 'C'], [⟨['p', 'a', 'n'], ['c', 'l', 'a', 's', 's'], none⟩, ⟨['e', 'y', 's', 'e'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['k', 'a', 'c', 'a', 'n', 'g'], ['m', 'o', 's', 't'], [⟨['k', 'a', 'c', 'a', 'n', 'g'], ['m', 'o', 's', 't'], none⟩]⟩, ⟨['k', 'h', 'i', '-', 'g', 'a'], ['h', 'e', 'i', 'g', 'h', 't', '-', 'N', 'O', 'M'], [⟨['k', 'h', 'i'], ['h', 'e', 'i', 'g', 'h', 't'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['k', 'h', 'u', 'n'], ['l', 'a', 'r', 'g', 'e'], [⟨['k', 'h', 'u', 'n'], ['l', 'a', 'r', 'g', 'e'], none⟩]⟩, ⟨['s', 'o', 'n', 'y', 'e', '-', 'k', 'a'], ['g', 'i', 'r', 'l', '-', 'N', 'O', 'M'], [⟨['s', 'o', 'n', 'y', 'e'], ['g', 'i', 'r', 'l'], none⟩, ⟨['k', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['m', 'w', 'u', 'n', 'c', 'e', 'y', '-', 'l', 'u', 'l'], ['p', 'r', 'o', 'b', 'l', 'e', 'm', '-', 'A', 'C', 'C'], [⟨['m', 'w', 'u', 'n', 'c', 'e', 'y'], ['p', 'r', 'o', 'b', 'l', 'e', 'm'], none⟩, ⟨['l', 'u', 'l'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['p', 'h', 'w', 'u', 'l', '-', 'e', 's', 's', '-', 't', 'a', '-', 'n', 'u', 'n'], ['s', 'o', 'l', 'v', 'e', '-', 'P', 'S', 'T', '-', 'D', 'E', 'C', 'L', '-', 'A', 'D', 'N'], [⟨['p', 'h', 'w', 'u', 'l'], ['s', 'o', 'l', 'v', 'e'], none⟩, ⟨['e', 's', 's'], ['P', 'S', 'T'], some '-'⟩, ⟨['t', 'a'], ['D', 'E', 'C', 'L'], some '-'⟩, ⟨['n', 'u', 'n'], ['A', 'D', 'N'], some '-'⟩]⟩, ⟨['c', 'w', 'u', 'c', 'a', 'n', 'g', '-', 'u', 'l'], ['c', 'l', 'a', 'i', 'm', '-', 'A', 'C', 'C'], [⟨['c', 'w', 'u', 'c', 'a', 'n', 'g'], ['c', 'l', 'a', 'i', 'm'], none⟩, ⟨['u', 'l'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['k', 'i', 'e', 'k', 'h', 'a', 'y', '-', 's', 's', '-', 't', 'a'], ['r', 'e', 'm', 'e', 'm', 'b', 'e', 'r', '-', 'P', 'S', 'T', '-', 'D', 'E', 'C', 'L'], [⟨['k', 'i', 'e', 'k', 'h', 'a', 'y'], ['r', 'e', 'm', 'e', 'm', 'b', 'e', 'r'], none⟩, ⟨['s', 's'], ['P', 'S', 'T'], some '-'⟩, ⟨['t', 'a'], ['D', 'E', 'C', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "substitution"), ("nounSort", "content"), ("role", "conclusion"), ("inference", "invalid")] }

def ch2_122a : Datum :=
  { id := "bondarenko2022_ch2_122a"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (122a)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Mina-ka Swuna-ka mwuncey-lul phwul-un sanghwang-ul kiekhay-ss-ta."
    glossedTokens := [("Mina-ka", "Mina-NOM"), ("Swuna-ka", "Swuna-NOM"), ("mwuncey-lul", "problem-ACC"), ("phwul-un", "solve-ADN"), ("sanghwang-ul", "situation-ACC"), ("kiekhay-ss-ta", "remember-PST-DECL")]
    glossedWords := [⟨['M', 'i', 'n', 'a', '-', 'k', 'a'], ['M', 'i', 'n', 'a', '-', 'N', 'O', 'M'], [⟨['M', 'i', 'n', 'a'], ['M', 'i', 'n', 'a'], none⟩, ⟨['k', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['S', 'w', 'u', 'n', 'a', '-', 'k', 'a'], ['S', 'w', 'u', 'n', 'a', '-', 'N', 'O', 'M'], [⟨['S', 'w', 'u', 'n', 'a'], ['S', 'w', 'u', 'n', 'a'], none⟩, ⟨['k', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['m', 'w', 'u', 'n', 'c', 'e', 'y', '-', 'l', 'u', 'l'], ['p', 'r', 'o', 'b', 'l', 'e', 'm', '-', 'A', 'C', 'C'], [⟨['m', 'w', 'u', 'n', 'c', 'e', 'y'], ['p', 'r', 'o', 'b', 'l', 'e', 'm'], none⟩, ⟨['l', 'u', 'l'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['p', 'h', 'w', 'u', 'l', '-', 'u', 'n'], ['s', 'o', 'l', 'v', 'e', '-', 'A', 'D', 'N'], [⟨['p', 'h', 'w', 'u', 'l'], ['s', 'o', 'l', 'v', 'e'], none⟩, ⟨['u', 'n'], ['A', 'D', 'N'], some '-'⟩]⟩, ⟨['s', 'a', 'n', 'g', 'h', 'w', 'a', 'n', 'g', '-', 'u', 'l'], ['s', 'i', 't', 'u', 'a', 't', 'i', 'o', 'n', '-', 'A', 'C', 'C'], [⟨['s', 'a', 'n', 'g', 'h', 'w', 'a', 'n', 'g'], ['s', 'i', 't', 'u', 'a', 't', 'i', 'o', 'n'], none⟩, ⟨['u', 'l'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['k', 'i', 'e', 'k', 'h', 'a', 'y', '-', 's', 's', '-', 't', 'a'], ['r', 'e', 'm', 'e', 'm', 'b', 'e', 'r', '-', 'P', 'S', 'T', '-', 'D', 'E', 'C', 'L'], [⟨['k', 'i', 'e', 'k', 'h', 'a', 'y'], ['r', 'e', 'm', 'e', 'm', 'b', 'e', 'r'], none⟩, ⟨['s', 's'], ['P', 'S', 'T'], some '-'⟩, ⟨['t', 'a'], ['D', 'E', 'C', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "substitution"), ("nounSort", "situation"), ("role", "premise-a")] }

def ch2_122b : Datum :=
  { id := "bondarenko2022_ch2_122b"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (122b)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Swuna-ka pan-eyse kacang khi-ga khu-ta."
    glossedTokens := [("Swuna-ka", "Swuna-NOM"), ("pan-eyse", "class-LOC"), ("kacang", "most"), ("khi-ga", "height-NOM"), ("khu-ta", "large-DECL")]
    glossedWords := [⟨['S', 'w', 'u', 'n', 'a', '-', 'k', 'a'], ['S', 'w', 'u', 'n', 'a', '-', 'N', 'O', 'M'], [⟨['S', 'w', 'u', 'n', 'a'], ['S', 'w', 'u', 'n', 'a'], none⟩, ⟨['k', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['p', 'a', 'n', '-', 'e', 'y', 's', 'e'], ['c', 'l', 'a', 's', 's', '-', 'L', 'O', 'C'], [⟨['p', 'a', 'n'], ['c', 'l', 'a', 's', 's'], none⟩, ⟨['e', 'y', 's', 'e'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['k', 'a', 'c', 'a', 'n', 'g'], ['m', 'o', 's', 't'], [⟨['k', 'a', 'c', 'a', 'n', 'g'], ['m', 'o', 's', 't'], none⟩]⟩, ⟨['k', 'h', 'i', '-', 'g', 'a'], ['h', 'e', 'i', 'g', 'h', 't', '-', 'N', 'O', 'M'], [⟨['k', 'h', 'i'], ['h', 'e', 'i', 'g', 'h', 't'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['k', 'h', 'u', '-', 't', 'a'], ['l', 'a', 'r', 'g', 'e', '-', 'D', 'E', 'C', 'L'], [⟨['k', 'h', 'u'], ['l', 'a', 'r', 'g', 'e'], none⟩, ⟨['t', 'a'], ['D', 'E', 'C', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "substitution"), ("role", "premise-b")] }

def ch2_122c : Datum :=
  { id := "bondarenko2022_ch2_122c"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (122c)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Mina-ka pan-eyse kacang khi-ga khun sonye-ka mwuncey-lul phwul-un sanghwang-ul kiekhay-ss-ta."
    glossedTokens := [("Mina-ka", "Mina-NOM"), ("pan-eyse", "class-LOC"), ("kacang", "most"), ("khi-ga", "height-NOM"), ("khun", "large"), ("sonye-ka", "girl-NOM"), ("mwuncey-lul", "problem-ACC"), ("phwul-un", "solve-ADN"), ("sanghwang-ul", "situation-ACC"), ("kiekhay-ss-ta", "remember-PST-DECL")]
    glossedWords := [⟨['M', 'i', 'n', 'a', '-', 'k', 'a'], ['M', 'i', 'n', 'a', '-', 'N', 'O', 'M'], [⟨['M', 'i', 'n', 'a'], ['M', 'i', 'n', 'a'], none⟩, ⟨['k', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['p', 'a', 'n', '-', 'e', 'y', 's', 'e'], ['c', 'l', 'a', 's', 's', '-', 'L', 'O', 'C'], [⟨['p', 'a', 'n'], ['c', 'l', 'a', 's', 's'], none⟩, ⟨['e', 'y', 's', 'e'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['k', 'a', 'c', 'a', 'n', 'g'], ['m', 'o', 's', 't'], [⟨['k', 'a', 'c', 'a', 'n', 'g'], ['m', 'o', 's', 't'], none⟩]⟩, ⟨['k', 'h', 'i', '-', 'g', 'a'], ['h', 'e', 'i', 'g', 'h', 't', '-', 'N', 'O', 'M'], [⟨['k', 'h', 'i'], ['h', 'e', 'i', 'g', 'h', 't'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['k', 'h', 'u', 'n'], ['l', 'a', 'r', 'g', 'e'], [⟨['k', 'h', 'u', 'n'], ['l', 'a', 'r', 'g', 'e'], none⟩]⟩, ⟨['s', 'o', 'n', 'y', 'e', '-', 'k', 'a'], ['g', 'i', 'r', 'l', '-', 'N', 'O', 'M'], [⟨['s', 'o', 'n', 'y', 'e'], ['g', 'i', 'r', 'l'], none⟩, ⟨['k', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['m', 'w', 'u', 'n', 'c', 'e', 'y', '-', 'l', 'u', 'l'], ['p', 'r', 'o', 'b', 'l', 'e', 'm', '-', 'A', 'C', 'C'], [⟨['m', 'w', 'u', 'n', 'c', 'e', 'y'], ['p', 'r', 'o', 'b', 'l', 'e', 'm'], none⟩, ⟨['l', 'u', 'l'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['p', 'h', 'w', 'u', 'l', '-', 'u', 'n'], ['s', 'o', 'l', 'v', 'e', '-', 'A', 'D', 'N'], [⟨['p', 'h', 'w', 'u', 'l'], ['s', 'o', 'l', 'v', 'e'], none⟩, ⟨['u', 'n'], ['A', 'D', 'N'], some '-'⟩]⟩, ⟨['s', 'a', 'n', 'g', 'h', 'w', 'a', 'n', 'g', '-', 'u', 'l'], ['s', 'i', 't', 'u', 'a', 't', 'i', 'o', 'n', '-', 'A', 'C', 'C'], [⟨['s', 'a', 'n', 'g', 'h', 'w', 'a', 'n', 'g'], ['s', 'i', 't', 'u', 'a', 't', 'i', 'o', 'n'], none⟩, ⟨['u', 'l'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['k', 'i', 'e', 'k', 'h', 'a', 'y', '-', 's', 's', '-', 't', 'a'], ['r', 'e', 'm', 'e', 'm', 'b', 'e', 'r', '-', 'P', 'S', 'T', '-', 'D', 'E', 'C', 'L'], [⟨['k', 'i', 'e', 'k', 'h', 'a', 'y'], ['r', 'e', 'm', 'e', 'm', 'b', 'e', 'r'], none⟩, ⟨['s', 's'], ['P', 'S', 'T'], some '-'⟩, ⟨['t', 'a'], ['D', 'E', 'C', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "substitution"), ("nounSort", "situation"), ("role", "conclusion"), ("inference", "valid")] }

def ch4_30 : Datum :=
  { id := "bondarenko2022_ch4_30"
    source := ⟨"bondarenko-2022", "§4.3.1 ex. (30)"⟩
    reportedIn := none
    language := "russ1264"
    primaryText := "Dugar mi:sgɘi zagaha ɘdj-ɘ: gɘ-žɘ han-a:"
    glossedTokens := [("Dugar", "Dugar.NOM"), ("mi:sgɘi", "cat.NOM"), ("zagaha", "fish"), ("ɘdj-ɘ:", "eat-PST"), ("gɘ-žɘ", "say-CVB"), ("han-a:", "think-PST")]
    glossedWords := [⟨['D', 'u', 'g', 'a', 'r'], ['D', 'u', 'g', 'a', 'r', '.', 'N', 'O', 'M'], [⟨['D', 'u', 'g', 'a', 'r'], ['D', 'u', 'g', 'a', 'r', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['m', 'i', ':', 's', 'g', 'ɘ', 'i'], ['c', 'a', 't', '.', 'N', 'O', 'M'], [⟨['m', 'i', 's', 'g', 'ɘ', 'i'], ['c', 'a', 't', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['z', 'a', 'g', 'a', 'h', 'a'], ['f', 'i', 's', 'h'], [⟨['z', 'a', 'g', 'a', 'h', 'a'], ['f', 'i', 's', 'h'], none⟩]⟩, ⟨['ɘ', 'd', 'j', '-', 'ɘ', ':'], ['e', 'a', 't', '-', 'P', 'S', 'T'], [⟨['ɘ', 'd', 'j'], ['e', 'a', 't'], none⟩, ⟨['ɘ'], ['P', 'S', 'T'], some '-'⟩]⟩, ⟨['g', 'ɘ', '-', 'ž', 'ɘ'], ['s', 'a', 'y', '-', 'C', 'V', 'B'], [⟨['g', 'ɘ'], ['s', 'a', 'y'], none⟩, ⟨['ž', 'ɘ'], ['C', 'V', 'B'], some '-'⟩]⟩, ⟨['h', 'a', 'n', '-', 'a', ':'], ['t', 'h', 'i', 'n', 'k', '-', 'P', 'S', 'T'], [⟨['h', 'a', 'n'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['a'], ['P', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clauseType", "Cont-CP"), ("shape", "bare gɘ-žɘ clause")] }

def ch4_31 : Datum :=
  { id := "bondarenko2022_ch4_31"
    source := ⟨"bondarenko-2022", "§4.3.1 ex. (31)"⟩
    reportedIn := none
    language := "russ1264"
    primaryText := "Dugar mi:sgɘi-n zagaha ɘdj-ɘ:š-i:jɘ-(n’) han-a:"
    glossedTokens := [("Dugar", "Dugar.NOM"), ("mi:sgɘi-n", "cat-GEN"), ("zagaha", "fish"), ("ɘdj-ɘ:š-i:jɘ-(n’)", "eat-PART-ACC-(3)"), ("han-a:", "think-PST")]
    glossedWords := [⟨['D', 'u', 'g', 'a', 'r'], ['D', 'u', 'g', 'a', 'r', '.', 'N', 'O', 'M'], [⟨['D', 'u', 'g', 'a', 'r'], ['D', 'u', 'g', 'a', 'r', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['m', 'i', ':', 's', 'g', 'ɘ', 'i', '-', 'n'], ['c', 'a', 't', '-', 'G', 'E', 'N'], [⟨['m', 'i', 's', 'g', 'ɘ', 'i'], ['c', 'a', 't'], none⟩, ⟨['n'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['z', 'a', 'g', 'a', 'h', 'a'], ['f', 'i', 's', 'h'], [⟨['z', 'a', 'g', 'a', 'h', 'a'], ['f', 'i', 's', 'h'], none⟩]⟩, ⟨['ɘ', 'd', 'j', '-', 'ɘ', ':', 'š', '-', 'i', ':', 'j', 'ɘ', '-', '(', 'n', '’', ')'], ['e', 'a', 't', '-', 'P', 'A', 'R', 'T', '-', 'A', 'C', 'C', '-', '(', '3', ')'], [⟨['ɘ', 'd', 'j'], ['e', 'a', 't'], none⟩, ⟨['ɘ', 'š'], ['P', 'A', 'R', 'T'], some '-'⟩, ⟨['i', 'j', 'ɘ'], ['A', 'C', 'C'], some '-'⟩, ⟨['n', '’'], ['(', '3', ')'], some '-'⟩]⟩, ⟨['h', 'a', 'n', '-', 'a', ':'], ['t', 'h', 'i', 'n', 'k', '-', 'P', 'S', 'T'], [⟨['h', 'a', 'n'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['a'], ['P', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clauseType", "Sit-CP"), ("shape", "nominalized participial clause")] }

def ch4_32 : Datum :=
  { id := "bondarenko2022_ch4_32"
    source := ⟨"bondarenko-2022", "§4.3.1 ex. (32)"⟩
    reportedIn := none
    language := "russ1264"
    primaryText := "Dugar mi:sgɘi-n zagaha ɘdj-ɘ: g-ɘ:š-i:jɘ-(n’) han-a:"
    glossedTokens := [("Dugar", "Dugar.NOM"), ("mi:sgɘi-n", "cat-GEN"), ("zagaha", "fish"), ("ɘdj-ɘ:", "eat-PST"), ("g-ɘ:š-i:jɘ-(n’)", "say-PART-ACC-(3)"), ("han-a:", "think-PST")]
    glossedWords := [⟨['D', 'u', 'g', 'a', 'r'], ['D', 'u', 'g', 'a', 'r', '.', 'N', 'O', 'M'], [⟨['D', 'u', 'g', 'a', 'r'], ['D', 'u', 'g', 'a', 'r', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['m', 'i', ':', 's', 'g', 'ɘ', 'i', '-', 'n'], ['c', 'a', 't', '-', 'G', 'E', 'N'], [⟨['m', 'i', 's', 'g', 'ɘ', 'i'], ['c', 'a', 't'], none⟩, ⟨['n'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['z', 'a', 'g', 'a', 'h', 'a'], ['f', 'i', 's', 'h'], [⟨['z', 'a', 'g', 'a', 'h', 'a'], ['f', 'i', 's', 'h'], none⟩]⟩, ⟨['ɘ', 'd', 'j', '-', 'ɘ', ':'], ['e', 'a', 't', '-', 'P', 'S', 'T'], [⟨['ɘ', 'd', 'j'], ['e', 'a', 't'], none⟩, ⟨['ɘ'], ['P', 'S', 'T'], some '-'⟩]⟩, ⟨['g', '-', 'ɘ', ':', 'š', '-', 'i', ':', 'j', 'ɘ', '-', '(', 'n', '’', ')'], ['s', 'a', 'y', '-', 'P', 'A', 'R', 'T', '-', 'A', 'C', 'C', '-', '(', '3', ')'], [⟨['g'], ['s', 'a', 'y'], none⟩, ⟨['ɘ', 'š'], ['P', 'A', 'R', 'T'], some '-'⟩, ⟨['i', 'j', 'ɘ'], ['A', 'C', 'C'], some '-'⟩, ⟨['n', '’'], ['(', '3', ')'], some '-'⟩]⟩, ⟨['h', 'a', 'n', '-', 'a', ':'], ['t', 'h', 'i', 'n', 'k', '-', 'P', 'S', 'T'], [⟨['h', 'a', 'n'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['a'], ['P', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clauseType", "Cont-CP"), ("shape", "nominalized gɘ-participial clause")] }

def all : List Datum := [ch2_105, ch2_106, ch2_107, ch2_108, ch2_109, ch2_110, ch2_111, ch2_112, ch2_120a, ch2_120b, ch2_120c, ch2_121a, ch2_121b, ch2_121c, ch2_122a, ch2_122b, ch2_122c, ch4_30, ch4_31, ch4_32]

/-- The diagnostic the example applies. -/
inductive Diagnostic where
  /-- truth-predicates: predicates of truth and falsity, *true*, *false*, *mistaken* -/
  | truthPredicates
  /-- occurrence-predicates: predicates of occurrence, *occur*, *happen* -/
  | occurrencePredicates
  /-- situation-only-predicate-notice: *notice*, which takes situation nouns only -/
  | notice
  /-- substitution: substitution of a clause true at the same situations -/
  | substitution
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `diagnostic`. -/
def diagnostic (e : Datum) : Option Diagnostic :=
  e.parse? "diagnostic" [("truth-predicates", .truthPredicates), ("occurrence-predicates", .occurrencePredicates),
    ("situation-only-predicate-notice", .notice), ("substitution", .substitution)]

/-- The sort of the noun the clause combines with. -/
inductive NounSort where
  /-- content: a content noun, *idea*, *claim*, *rumor* -/
  | content
  /-- situation: a situation noun, *situation*, *event*, *case* -/
  | situation
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `nounSort`. -/
def nounSort (e : Datum) : Option NounSort :=
  e.parse? "nounSort" [("content", .content), ("situation", .situation)]

/-- The place of the sentence in a substitution triple. -/
inductive Role where
  /-- premise-a: the first premise -/
  | premiseA
  /-- premise-b: the second premise -/
  | premiseB
  /-- conclusion: the conclusion -/
  | conclusion
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `role`. -/
def role (e : Datum) : Option Role :=
  e.parse? "role" [("premise-a", .premiseA), ("premise-b", .premiseB), ("conclusion", .conclusion)]

/-- Whether the conclusion follows from the premises. -/
inductive Inference where
  /-- valid: the conclusion follows -/
  | valid
  /-- invalid: the conclusion does not follow -/
  | invalid
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `inference`. -/
def inference (e : Datum) : Option Inference :=
  e.parse? "inference" [("valid", .valid), ("invalid", .invalid)]

/-- The meaning of the embedded clause. -/
inductive ClauseType where
  /-- Cont-CP: a clause that describes propositional content -/
  | contCP
  /-- Sit-CP: a clause that describes a situation -/
  | sitCP
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `clauseType`. -/
def clauseType (e : Datum) : Option ClauseType :=
  e.parse? "clauseType" [("Cont-CP", .contCP), ("Sit-CP", .sitCP)]

/-- The form of the Buryat embedded clause. -/
inductive Shape where
  /-- bare gɘ-žɘ clause: a bare clause with *gɘ* and the converb *-žɘ* -/
  | bareGeZhe
  /-- nominalized participial clause: a nominalized clause with the participle alone -/
  | nominalizedParticipial
  /-- nominalized gɘ-participial clause: a nominalized clause with *gɘ* and the participle -/
  | nominalizedGeParticipial
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `shape`. -/
def shape (e : Datum) : Option Shape :=
  e.parse? "shape" [("bare gɘ-žɘ clause", .bareGeZhe),
    ("nominalized participial clause", .nominalizedParticipial),
    ("nominalized gɘ-participial clause", .nominalizedGeParticipial)]

end Bondarenko2022.Examples
