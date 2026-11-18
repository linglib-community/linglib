module

public import Linglib.Data.Examples.Schema

/-!
# `Rett2020a` — typed example data

Auto-generated from `Linglib/Data/Examples/Rett2020a.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Rett2020a.Examples`.
-/

@[expose] public section

namespace Rett2020a.Examples

def ex_9 : Datum :=
  { id := "rett2020a_9"
    source := ⟨"rett-2020a", "(9)"⟩
    reportedIn := none
    language := "taga1270"
    primaryText := "Nakilala ni-Mary si-John bago siya um-akyat sa bundok."
    glossedTokens := [("Nakilala", "PFV.TV-meet"), ("ni-Mary", "GEN-Mary"), ("si-John", "SUBJ-John"), ("bago", "before"), ("siya", "SUBJ.3SG"), ("um-akyat", "PFV.AV-climb"), ("sa", "OBL"), ("bundok", "mountain")]
    glossedWords := [⟨['N', 'a', 'k', 'i', 'l', 'a', 'l', 'a'], ['P', 'F', 'V', '.', 'T', 'V', '-', 'm', 'e', 'e', 't'], []⟩, ⟨['n', 'i', '-', 'M', 'a', 'r', 'y'], ['G', 'E', 'N', '-', 'M', 'a', 'r', 'y'], [⟨['n', 'i'], ['G', 'E', 'N'], none⟩, ⟨['M', 'a', 'r', 'y'], ['M', 'a', 'r', 'y'], some '-'⟩]⟩, ⟨['s', 'i', '-', 'J', 'o', 'h', 'n'], ['S', 'U', 'B', 'J', '-', 'J', 'o', 'h', 'n'], [⟨['s', 'i'], ['S', 'U', 'B', 'J'], none⟩, ⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], some '-'⟩]⟩, ⟨['b', 'a', 'g', 'o'], ['b', 'e', 'f', 'o', 'r', 'e'], [⟨['b', 'a', 'g', 'o'], ['b', 'e', 'f', 'o', 'r', 'e'], none⟩]⟩, ⟨['s', 'i', 'y', 'a'], ['S', 'U', 'B', 'J', '.', '3', 'S', 'G'], [⟨['s', 'i', 'y', 'a'], ['S', 'U', 'B', 'J', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['u', 'm', '-', 'a', 'k', 'y', 'a', 't'], ['P', 'F', 'V', '.', 'A', 'V', '-', 'c', 'l', 'i', 'm', 'b'], [⟨['u', 'm'], ['P', 'F', 'V', '.', 'A', 'V'], none⟩, ⟨['a', 'k', 'y', 'a', 't'], ['c', 'l', 'i', 'm', 'b'], some '-'⟩]⟩, ⟨['s', 'a'], ['O', 'B', 'L'], [⟨['s', 'a'], ['O', 'B', 'L'], none⟩]⟩, ⟨['b', 'u', 'n', 'd', 'o', 'k'], ['m', 'o', 'u', 'n', 't', 'a', 'i', 'n'], [⟨['b', 'u', 'n', 'd', 'o', 'k'], ['m', 'o', 'u', 'n', 't', 'a', 'i', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("before-start", .acceptable), ("before-finish", .unacceptable)]
    paperFeatures := [("construction", "before"), ("embedded", "culmination")] }

def ex_10 : Datum :=
  { id := "rett2020a_10"
    source := ⟨"rett-2020a", "(10)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Mary hat John getroffen, nachdem er Single war."
    glossedTokens := [("Mary", "Mary"), ("hat", "had-3SG"), ("John", "John"), ("getroffen,", "met"), ("nachdem", "after"), ("er", "he"), ("Single", "single"), ("war.", "was-3SG")]
    glossedWords := [⟨['M', 'a', 'r', 'y'], ['M', 'a', 'r', 'y'], [⟨['M', 'a', 'r', 'y'], ['M', 'a', 'r', 'y'], none⟩]⟩, ⟨['h', 'a', 't'], ['h', 'a', 'd', '-', '3', 'S', 'G'], []⟩, ⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], none⟩]⟩, ⟨['g', 'e', 't', 'r', 'o', 'f', 'f', 'e', 'n', ','], ['m', 'e', 't'], [⟨['g', 'e', 't', 'r', 'o', 'f', 'f', 'e', 'n'], ['m', 'e', 't'], none⟩]⟩, ⟨['n', 'a', 'c', 'h', 'd', 'e', 'm'], ['a', 'f', 't', 'e', 'r'], [⟨['n', 'a', 'c', 'h', 'd', 'e', 'm'], ['a', 'f', 't', 'e', 'r'], none⟩]⟩, ⟨['e', 'r'], ['h', 'e'], [⟨['e', 'r'], ['h', 'e'], none⟩]⟩, ⟨['S', 'i', 'n', 'g', 'l', 'e'], ['s', 'i', 'n', 'g', 'l', 'e'], [⟨['S', 'i', 'n', 'g', 'l', 'e'], ['s', 'i', 'n', 'g', 'l', 'e'], none⟩]⟩, ⟨['w', 'a', 'r', '.'], ['w', 'a', 's', '-', '3', 'S', 'G'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("after-finish", .acceptable), ("after-start", .unacceptable)]
    paperFeatures := [("construction", "after"), ("embedded", "process")] }

def ex_11a : Datum :=
  { id := "rett2020a_11a"
    source := ⟨"rett-2020a", "(11a)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Mary je srela Johna pre nego što se peo na vrh planine."
    glossedTokens := [("Mary", "Mary-NOM"), ("je", "is-PRES-3FS"), ("srela", "met-PP-3FS"), ("Johna", "John-ACC"), ("pre", "before"), ("nego", "than"), ("što", "PTCL"), ("se", "REFL"), ("peo", "climb-IMP-3MS"), ("na", "on"), ("vrh", "top-ACC"), ("planine.", "mountain-GEN")]
    glossedWords := [⟨['M', 'a', 'r', 'y'], ['M', 'a', 'r', 'y', '-', 'N', 'O', 'M'], []⟩, ⟨['j', 'e'], ['i', 's', '-', 'P', 'R', 'E', 'S', '-', '3', 'F', 'S'], []⟩, ⟨['s', 'r', 'e', 'l', 'a'], ['m', 'e', 't', '-', 'P', 'P', '-', '3', 'F', 'S'], []⟩, ⟨['J', 'o', 'h', 'n', 'a'], ['J', 'o', 'h', 'n', '-', 'A', 'C', 'C'], []⟩, ⟨['p', 'r', 'e'], ['b', 'e', 'f', 'o', 'r', 'e'], [⟨['p', 'r', 'e'], ['b', 'e', 'f', 'o', 'r', 'e'], none⟩]⟩, ⟨['n', 'e', 'g', 'o'], ['t', 'h', 'a', 'n'], [⟨['n', 'e', 'g', 'o'], ['t', 'h', 'a', 'n'], none⟩]⟩, ⟨['š', 't', 'o'], ['P', 'T', 'C', 'L'], [⟨['š', 't', 'o'], ['P', 'T', 'C', 'L'], none⟩]⟩, ⟨['s', 'e'], ['R', 'E', 'F', 'L'], [⟨['s', 'e'], ['R', 'E', 'F', 'L'], none⟩]⟩, ⟨['p', 'e', 'o'], ['c', 'l', 'i', 'm', 'b', '-', 'I', 'M', 'P', '-', '3', 'M', 'S'], []⟩, ⟨['n', 'a'], ['o', 'n'], [⟨['n', 'a'], ['o', 'n'], none⟩]⟩, ⟨['v', 'r', 'h'], ['t', 'o', 'p', '-', 'A', 'C', 'C'], []⟩, ⟨['p', 'l', 'a', 'n', 'i', 'n', 'e', '.'], ['m', 'o', 'u', 'n', 't', 'a', 'i', 'n', '-', 'G', 'E', 'N'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("before-start", .acceptable)]
    paperFeatures := [("construction", "before"), ("embedded", "culmination"), ("aspect", "imperfective")] }

def ex_11b : Datum :=
  { id := "rett2020a_11b"
    source := ⟨"rett-2020a", "(11b)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Mary je srela Johna pre nego što se popeo na vrh planine."
    glossedTokens := [("Mary", "Mary-NOM"), ("je", "is-PRES-3FS"), ("srela", "met-PP-3FS"), ("Johna", "John-ACC"), ("pre", "before"), ("nego", "than"), ("što", "PTCL"), ("se", "REFL"), ("popeo", "climb-PP-3MS"), ("na", "on"), ("vrh", "top-ACC"), ("planine.", "mountain-GEN")]
    glossedWords := [⟨['M', 'a', 'r', 'y'], ['M', 'a', 'r', 'y', '-', 'N', 'O', 'M'], []⟩, ⟨['j', 'e'], ['i', 's', '-', 'P', 'R', 'E', 'S', '-', '3', 'F', 'S'], []⟩, ⟨['s', 'r', 'e', 'l', 'a'], ['m', 'e', 't', '-', 'P', 'P', '-', '3', 'F', 'S'], []⟩, ⟨['J', 'o', 'h', 'n', 'a'], ['J', 'o', 'h', 'n', '-', 'A', 'C', 'C'], []⟩, ⟨['p', 'r', 'e'], ['b', 'e', 'f', 'o', 'r', 'e'], [⟨['p', 'r', 'e'], ['b', 'e', 'f', 'o', 'r', 'e'], none⟩]⟩, ⟨['n', 'e', 'g', 'o'], ['t', 'h', 'a', 'n'], [⟨['n', 'e', 'g', 'o'], ['t', 'h', 'a', 'n'], none⟩]⟩, ⟨['š', 't', 'o'], ['P', 'T', 'C', 'L'], [⟨['š', 't', 'o'], ['P', 'T', 'C', 'L'], none⟩]⟩, ⟨['s', 'e'], ['R', 'E', 'F', 'L'], [⟨['s', 'e'], ['R', 'E', 'F', 'L'], none⟩]⟩, ⟨['p', 'o', 'p', 'e', 'o'], ['c', 'l', 'i', 'm', 'b', '-', 'P', 'P', '-', '3', 'M', 'S'], []⟩, ⟨['n', 'a'], ['o', 'n'], [⟨['n', 'a'], ['o', 'n'], none⟩]⟩, ⟨['v', 'r', 'h'], ['t', 'o', 'p', '-', 'A', 'C', 'C'], []⟩, ⟨['p', 'l', 'a', 'n', 'i', 'n', 'e', '.'], ['m', 'o', 'u', 'n', 't', 'a', 'i', 'n', '-', 'G', 'E', 'N'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("before-finish", .acceptable)]
    paperFeatures := [("construction", "before"), ("embedded", "culmination"), ("aspect", "perfective")] }

def ex_12a : Datum :=
  { id := "rett2020a_12a"
    source := ⟨"rett-2020a", "(12a)"⟩
    reportedIn := none
    language := "taga1270"
    primaryText := "Um-alis siya bago niya w<in>alis-an ang-sahig."
    glossedTokens := [("Um-alis", "AV.PFV.NEUT-leave"), ("siya", "SUBJ.3SG"), ("bago", "before"), ("niya", "NON.SUBJ.3SG"), ("w<in>alis-an", "PFV.NEUT-sweep-LV"), ("ang-sahig.", "SUBJ-floor")]
    glossedWords := [⟨['U', 'm', '-', 'a', 'l', 'i', 's'], ['A', 'V', '.', 'P', 'F', 'V', '.', 'N', 'E', 'U', 'T', '-', 'l', 'e', 'a', 'v', 'e'], [⟨['U', 'm'], ['A', 'V', '.', 'P', 'F', 'V', '.', 'N', 'E', 'U', 'T'], none⟩, ⟨['a', 'l', 'i', 's'], ['l', 'e', 'a', 'v', 'e'], some '-'⟩]⟩, ⟨['s', 'i', 'y', 'a'], ['S', 'U', 'B', 'J', '.', '3', 'S', 'G'], [⟨['s', 'i', 'y', 'a'], ['S', 'U', 'B', 'J', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['b', 'a', 'g', 'o'], ['b', 'e', 'f', 'o', 'r', 'e'], [⟨['b', 'a', 'g', 'o'], ['b', 'e', 'f', 'o', 'r', 'e'], none⟩]⟩, ⟨['n', 'i', 'y', 'a'], ['N', 'O', 'N', '.', 'S', 'U', 'B', 'J', '.', '3', 'S', 'G'], [⟨['n', 'i', 'y', 'a'], ['N', 'O', 'N', '.', 'S', 'U', 'B', 'J', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['w', '<', 'i', 'n', '>', 'a', 'l', 'i', 's', '-', 'a', 'n'], ['P', 'F', 'V', '.', 'N', 'E', 'U', 'T', '-', 's', 'w', 'e', 'e', 'p', '-', 'L', 'V'], []⟩, ⟨['a', 'n', 'g', '-', 's', 'a', 'h', 'i', 'g', '.'], ['S', 'U', 'B', 'J', '-', 'f', 'l', 'o', 'o', 'r'], [⟨['a', 'n', 'g'], ['S', 'U', 'B', 'J'], none⟩, ⟨['s', 'a', 'h', 'i', 'g'], ['f', 'l', 'o', 'o', 'r'], some '-'⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("before-start", .acceptable)]
    paperFeatures := [("construction", "before"), ("embedded", "culmination"), ("aspect", "pfv.neut")] }

def ex_12b : Datum :=
  { id := "rett2020a_12b"
    source := ⟨"rett-2020a", "(12b)"⟩
    reportedIn := none
    language := "taga1270"
    primaryText := "Um-alis siya bago niya na-walis-an ang-sahig."
    glossedTokens := [("Um-alis", "AV.PFV.NEUT-leave"), ("siya", "SUBJ.3SG"), ("bago", "before"), ("niya", "NON.SUBJ.3SG"), ("na-walis-an", "PFV.AIA-sweep-LV"), ("ang-sahig.", "SUBJ-floor")]
    glossedWords := [⟨['U', 'm', '-', 'a', 'l', 'i', 's'], ['A', 'V', '.', 'P', 'F', 'V', '.', 'N', 'E', 'U', 'T', '-', 'l', 'e', 'a', 'v', 'e'], [⟨['U', 'm'], ['A', 'V', '.', 'P', 'F', 'V', '.', 'N', 'E', 'U', 'T'], none⟩, ⟨['a', 'l', 'i', 's'], ['l', 'e', 'a', 'v', 'e'], some '-'⟩]⟩, ⟨['s', 'i', 'y', 'a'], ['S', 'U', 'B', 'J', '.', '3', 'S', 'G'], [⟨['s', 'i', 'y', 'a'], ['S', 'U', 'B', 'J', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['b', 'a', 'g', 'o'], ['b', 'e', 'f', 'o', 'r', 'e'], [⟨['b', 'a', 'g', 'o'], ['b', 'e', 'f', 'o', 'r', 'e'], none⟩]⟩, ⟨['n', 'i', 'y', 'a'], ['N', 'O', 'N', '.', 'S', 'U', 'B', 'J', '.', '3', 'S', 'G'], [⟨['n', 'i', 'y', 'a'], ['N', 'O', 'N', '.', 'S', 'U', 'B', 'J', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['n', 'a', '-', 'w', 'a', 'l', 'i', 's', '-', 'a', 'n'], ['P', 'F', 'V', '.', 'A', 'I', 'A', '-', 's', 'w', 'e', 'e', 'p', '-', 'L', 'V'], [⟨['n', 'a'], ['P', 'F', 'V', '.', 'A', 'I', 'A'], none⟩, ⟨['w', 'a', 'l', 'i', 's'], ['s', 'w', 'e', 'e', 'p'], some '-'⟩, ⟨['a', 'n'], ['L', 'V'], some '-'⟩]⟩, ⟨['a', 'n', 'g', '-', 's', 'a', 'h', 'i', 'g', '.'], ['S', 'U', 'B', 'J', '-', 'f', 'l', 'o', 'o', 'r'], [⟨['a', 'n', 'g'], ['S', 'U', 'B', 'J'], none⟩, ⟨['s', 'a', 'h', 'i', 'g'], ['f', 'l', 'o', 'o', 'r'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("before-finish", .acceptable)]
    paperFeatures := [("construction", "before"), ("embedded", "culmination"), ("aspect", "aia")] }

def all : List Datum := [ex_9, ex_10, ex_11a, ex_11b, ex_12a, ex_12b]

end Rett2020a.Examples
