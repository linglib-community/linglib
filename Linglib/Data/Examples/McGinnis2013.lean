module

public import Linglib.Data.Examples.Schema

/-!
# `McGinnis2013` — typed example data

Auto-generated from `Linglib/Data/Examples/McGinnis2013.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace McGinnis2013.Examples`.
-/

@[expose] public section

namespace McGinnis2013.Examples

def ex_17a : Datum :=
  { id := "mcginnis2013_17a"
    source := ⟨"mcginnis-2013", "(2), (17a)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "g-nax-a-t"
    glossedTokens := [("g-nax-a-t", "2.dat-see-aor-pl")]
    glossedWords := [⟨['g', '-', 'n', 'a', 'x', '-', 'a', '-', 't'], ['2', '.', 'd', 'a', 't', '-', 's', 'e', 'e', '-', 'a', 'o', 'r', '-', 'p', 'l'], [⟨['g'], ['2', '.', 'd', 'a', 't'], none⟩, ⟨['n', 'a', 'x'], ['s', 'e', 'e'], some '-'⟩, ⟨['a'], ['a', 'o', 'r'], some '-'⟩, ⟨['t'], ['p', 'l'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subjPerson", "3"), ("subjNumber", "sg"), ("objPerson", "2"), ("objNumber", "pl"), ("objCase", "dat"), ("screeve", "aorist"), ("prefix", "g"), ("suffix1", "a"), ("suffix2", "t")] }

def ex_17b : Datum :=
  { id := "mcginnis2013_17b"
    source := ⟨"mcginnis-2013", "(3a), (17b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "g-nax-es"
    glossedTokens := [("g-nax-es", "2.dat-see-aor.3pl")]
    glossedWords := [⟨['g', '-', 'n', 'a', 'x', '-', 'e', 's'], ['2', '.', 'd', 'a', 't', '-', 's', 'e', 'e', '-', 'a', 'o', 'r', '.', '3', 'p', 'l'], [⟨['g'], ['2', '.', 'd', 'a', 't'], none⟩, ⟨['n', 'a', 'x'], ['s', 'e', 'e'], some '-'⟩, ⟨['e', 's'], ['a', 'o', 'r', '.', '3', 'p', 'l'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subjPerson", "3"), ("subjNumber", "pl"), ("objPerson", "2"), ("objNumber", "sg"), ("objCase", "dat"), ("screeve", "aorist"), ("prefix", "g"), ("suffix1", "es")] }

def ex_3a_pl : Datum :=
  { id := "mcginnis2013_3a_pl"
    source := ⟨"mcginnis-2013", "(3a), (5a), (11a), (17b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "g-nax-es"
    glossedTokens := [("g-nax-es", "2.dat-see-aor.3pl")]
    glossedWords := [⟨['g', '-', 'n', 'a', 'x', '-', 'e', 's'], ['2', '.', 'd', 'a', 't', '-', 's', 'e', 'e', '-', 'a', 'o', 'r', '.', '3', 'p', 'l'], [⟨['g'], ['2', '.', 'd', 'a', 't'], none⟩, ⟨['n', 'a', 'x'], ['s', 'e', 'e'], some '-'⟩, ⟨['e', 's'], ['a', 'o', 'r', '.', '3', 'p', 'l'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subjPerson", "3"), ("subjNumber", "pl"), ("objPerson", "2"), ("objNumber", "pl"), ("objCase", "dat"), ("screeve", "aorist"), ("prefix", "g"), ("suffix1", "es")] }

def ex_3b : Datum :=
  { id := "mcginnis2013_3b"
    source := ⟨"mcginnis-2013", "(3b), (17b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "g-nax-es-t"
    glossedTokens := [("g-nax-es-t", "2.dat-see-aor.3pl-pl")]
    glossedWords := [⟨['g', '-', 'n', 'a', 'x', '-', 'e', 's', '-', 't'], ['2', '.', 'd', 'a', 't', '-', 's', 'e', 'e', '-', 'a', 'o', 'r', '.', '3', 'p', 'l', '-', 'p', 'l'], [⟨['g'], ['2', '.', 'd', 'a', 't'], none⟩, ⟨['n', 'a', 'x'], ['s', 'e', 'e'], some '-'⟩, ⟨['e', 's'], ['a', 'o', 'r', '.', '3', 'p', 'l'], some '-'⟩, ⟨['t'], ['p', 'l'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("subjPerson", "3"), ("subjNumber", "pl"), ("objPerson", "2"), ("objNumber", "pl"), ("objCase", "dat"), ("screeve", "aorist"), ("prefix", "g"), ("suffix1", "es"), ("suffix2", "t")] }

def ex_5c : Datum :=
  { id := "mcginnis2013_5c"
    source := ⟨"mcginnis-2013", "(5c)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "g-nax-a"
    glossedTokens := [("g-nax-a", "2.dat-see-aor")]
    glossedWords := [⟨['g', '-', 'n', 'a', 'x', '-', 'a'], ['2', '.', 'd', 'a', 't', '-', 's', 'e', 'e', '-', 'a', 'o', 'r'], [⟨['g'], ['2', '.', 'd', 'a', 't'], none⟩, ⟨['n', 'a', 'x'], ['s', 'e', 'e'], some '-'⟩, ⟨['a'], ['a', 'o', 'r'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subjPerson", "3"), ("subjNumber", "sg"), ("objPerson", "2"), ("objNumber", "sg"), ("objCase", "dat"), ("screeve", "aorist"), ("prefix", "g"), ("suffix1", "a")] }

def ex_6a : Datum :=
  { id := "mcginnis2013_6a"
    source := ⟨"mcginnis-2013", "(6a)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "v-nax-es"
    glossedTokens := [("v-nax-es", "1-see-aor.3pl")]
    glossedWords := [⟨['v', '-', 'n', 'a', 'x', '-', 'e', 's'], ['1', '-', 's', 'e', 'e', '-', 'a', 'o', 'r', '.', '3', 'p', 'l'], [⟨['v'], ['1'], none⟩, ⟨['n', 'a', 'x'], ['s', 'e', 'e'], some '-'⟩, ⟨['e', 's'], ['a', 'o', 'r', '.', '3', 'p', 'l'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("subjPerson", "1"), ("subjNumber", "sg"), ("objPerson", "3"), ("objNumber", "pl"), ("objCase", "dat"), ("screeve", "aorist"), ("prefix", "v"), ("suffix1", "es")] }

def ex_6b_we : Datum :=
  { id := "mcginnis2013_6b_we"
    source := ⟨"mcginnis-2013", "(6b), (11b), (22b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "v-nax-e-t"
    glossedTokens := [("v-nax-e-t", "1-see-aor.part-pl")]
    glossedWords := [⟨['v', '-', 'n', 'a', 'x', '-', 'e', '-', 't'], ['1', '-', 's', 'e', 'e', '-', 'a', 'o', 'r', '.', 'p', 'a', 'r', 't', '-', 'p', 'l'], [⟨['v'], ['1'], none⟩, ⟨['n', 'a', 'x'], ['s', 'e', 'e'], some '-'⟩, ⟨['e'], ['a', 'o', 'r', '.', 'p', 'a', 'r', 't'], some '-'⟩, ⟨['t'], ['p', 'l'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subjPerson", "1"), ("subjNumber", "pl"), ("objPerson", "3"), ("objNumber", "sg"), ("objCase", "dat"), ("screeve", "aorist"), ("prefix", "v"), ("suffix1", "e"), ("suffix2", "t")] }

def ex_6b_i : Datum :=
  { id := "mcginnis2013_6b_i"
    source := ⟨"mcginnis-2013", "(6b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "v-nax-e-t"
    glossedTokens := [("v-nax-e-t", "1-see-aor.part-pl")]
    glossedWords := [⟨['v', '-', 'n', 'a', 'x', '-', 'e', '-', 't'], ['1', '-', 's', 'e', 'e', '-', 'a', 'o', 'r', '.', 'p', 'a', 'r', 't', '-', 'p', 'l'], [⟨['v'], ['1'], none⟩, ⟨['n', 'a', 'x'], ['s', 'e', 'e'], some '-'⟩, ⟨['e'], ['a', 'o', 'r', '.', 'p', 'a', 'r', 't'], some '-'⟩, ⟨['t'], ['p', 'l'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("subjPerson", "1"), ("subjNumber", "sg"), ("objPerson", "3"), ("objNumber", "pl"), ("objCase", "dat"), ("screeve", "aorist"), ("prefix", "v"), ("suffix1", "e"), ("suffix2", "t")] }

def ex_6c : Datum :=
  { id := "mcginnis2013_6c"
    source := ⟨"mcginnis-2013", "(6c), (22a)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "v-nax-e"
    glossedTokens := [("v-nax-e", "1-see-aor.part")]
    glossedWords := [⟨['v', '-', 'n', 'a', 'x', '-', 'e'], ['1', '-', 's', 'e', 'e', '-', 'a', 'o', 'r', '.', 'p', 'a', 'r', 't'], [⟨['v'], ['1'], none⟩, ⟨['n', 'a', 'x'], ['s', 'e', 'e'], some '-'⟩, ⟨['e'], ['a', 'o', 'r', '.', 'p', 'a', 'r', 't'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subjPerson", "1"), ("subjNumber", "sg"), ("objPerson", "3"), ("objNumber", "sg"), ("objCase", "dat"), ("screeve", "aorist"), ("prefix", "v"), ("suffix1", "e")] }

def ex_18a : Datum :=
  { id := "mcginnis2013_18a"
    source := ⟨"mcginnis-2013", "(12), (18a)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "g-nax-o-s"
    glossedTokens := [("g-nax-o-s", "2.dat-see-opt-#")]
    glossedWords := [⟨['g', '-', 'n', 'a', 'x', '-', 'o', '-', 's'], ['2', '.', 'd', 'a', 't', '-', 's', 'e', 'e', '-', 'o', 'p', 't', '-', '#'], [⟨['g'], ['2', '.', 'd', 'a', 't'], none⟩, ⟨['n', 'a', 'x'], ['s', 'e', 'e'], some '-'⟩, ⟨['o'], ['o', 'p', 't'], some '-'⟩, ⟨['s'], ['#'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subjPerson", "3"), ("subjNumber", "sg"), ("objPerson", "2"), ("objNumber", "sg"), ("objCase", "dat"), ("screeve", "optative"), ("prefix", "g"), ("suffix1", "o"), ("suffix2", "s")] }

def ex_18b : Datum :=
  { id := "mcginnis2013_18b"
    source := ⟨"mcginnis-2013", "(15), (18b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "g-nax-o-t"
    glossedTokens := [("g-nax-o-t", "2.dat-see-opt-pl")]
    glossedWords := [⟨['g', '-', 'n', 'a', 'x', '-', 'o', '-', 't'], ['2', '.', 'd', 'a', 't', '-', 's', 'e', 'e', '-', 'o', 'p', 't', '-', 'p', 'l'], [⟨['g'], ['2', '.', 'd', 'a', 't'], none⟩, ⟨['n', 'a', 'x'], ['s', 'e', 'e'], some '-'⟩, ⟨['o'], ['o', 'p', 't'], some '-'⟩, ⟨['t'], ['p', 'l'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subjPerson", "3"), ("subjNumber", "sg"), ("objPerson", "2"), ("objNumber", "pl"), ("objCase", "dat"), ("screeve", "optative"), ("prefix", "g"), ("suffix1", "o"), ("suffix2", "t")] }

def ex_18b_st : Datum :=
  { id := "mcginnis2013_18b_st"
    source := ⟨"mcginnis-2013", "(15), (18b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "g-nax-o-s-t"
    glossedTokens := [("g-nax-o-s-t", "2.dat-see-opt-#-pl")]
    glossedWords := [⟨['g', '-', 'n', 'a', 'x', '-', 'o', '-', 's', '-', 't'], ['2', '.', 'd', 'a', 't', '-', 's', 'e', 'e', '-', 'o', 'p', 't', '-', '#', '-', 'p', 'l'], [⟨['g'], ['2', '.', 'd', 'a', 't'], none⟩, ⟨['n', 'a', 'x'], ['s', 'e', 'e'], some '-'⟩, ⟨['o'], ['o', 'p', 't'], some '-'⟩, ⟨['s'], ['#'], some '-'⟩, ⟨['t'], ['p', 'l'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("subjPerson", "3"), ("subjNumber", "sg"), ("objPerson", "2"), ("objNumber", "pl"), ("objCase", "dat"), ("screeve", "optative"), ("prefix", "g"), ("suffix1", "o"), ("suffix2", "s"), ("suffix3", "t")] }

def ex_18b_ts : Datum :=
  { id := "mcginnis2013_18b_ts"
    source := ⟨"mcginnis-2013", "(15), (18b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "g-nax-o-t-s"
    glossedTokens := [("g-nax-o-t-s", "2.dat-see-opt-pl-#")]
    glossedWords := [⟨['g', '-', 'n', 'a', 'x', '-', 'o', '-', 't', '-', 's'], ['2', '.', 'd', 'a', 't', '-', 's', 'e', 'e', '-', 'o', 'p', 't', '-', 'p', 'l', '-', '#'], [⟨['g'], ['2', '.', 'd', 'a', 't'], none⟩, ⟨['n', 'a', 'x'], ['s', 'e', 'e'], some '-'⟩, ⟨['o'], ['o', 'p', 't'], some '-'⟩, ⟨['t'], ['p', 'l'], some '-'⟩, ⟨['s'], ['#'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("subjPerson", "3"), ("subjNumber", "sg"), ("objPerson", "2"), ("objNumber", "pl"), ("objCase", "dat"), ("screeve", "optative"), ("prefix", "g"), ("suffix1", "o"), ("suffix2", "t"), ("suffix3", "s")] }

def ex_21 : Datum :=
  { id := "mcginnis2013_21"
    source := ⟨"mcginnis-2013", "(21)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "gv-nax-e-t"
    glossedTokens := [("gv-nax-e-t", "multisp.dat-see-aor.part-pl")]
    glossedWords := [⟨['g', 'v', '-', 'n', 'a', 'x', '-', 'e', '-', 't'], ['m', 'u', 'l', 't', 'i', 's', 'p', '.', 'd', 'a', 't', '-', 's', 'e', 'e', '-', 'a', 'o', 'r', '.', 'p', 'a', 'r', 't', '-', 'p', 'l'], [⟨['g', 'v'], ['m', 'u', 'l', 't', 'i', 's', 'p', '.', 'd', 'a', 't'], none⟩, ⟨['n', 'a', 'x'], ['s', 'e', 'e'], some '-'⟩, ⟨['e'], ['a', 'o', 'r', '.', 'p', 'a', 'r', 't'], some '-'⟩, ⟨['t'], ['p', 'l'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subjPerson", "2"), ("subjNumber", "pl"), ("objPerson", "1"), ("objNumber", "pl"), ("objCase", "dat"), ("screeve", "aorist"), ("prefix", "gv"), ("suffix1", "e"), ("suffix2", "t")] }

def ex_23a : Datum :=
  { id := "mcginnis2013_23a"
    source := ⟨"mcginnis-2013", "(23a)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "m-nax-a"
    glossedTokens := [("m-nax-a", "1.dat-see-aor")]
    glossedWords := [⟨['m', '-', 'n', 'a', 'x', '-', 'a'], ['1', '.', 'd', 'a', 't', '-', 's', 'e', 'e', '-', 'a', 'o', 'r'], [⟨['m'], ['1', '.', 'd', 'a', 't'], none⟩, ⟨['n', 'a', 'x'], ['s', 'e', 'e'], some '-'⟩, ⟨['a'], ['a', 'o', 'r'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subjPerson", "3"), ("subjNumber", "sg"), ("objPerson", "1"), ("objNumber", "sg"), ("objCase", "dat"), ("screeve", "aorist"), ("prefix", "m"), ("suffix1", "a")] }

def ex_23b : Datum :=
  { id := "mcginnis2013_23b"
    source := ⟨"mcginnis-2013", "(23b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "gv-nax-a"
    glossedTokens := [("gv-nax-a", "multisp.dat-see-aor")]
    glossedWords := [⟨['g', 'v', '-', 'n', 'a', 'x', '-', 'a'], ['m', 'u', 'l', 't', 'i', 's', 'p', '.', 'd', 'a', 't', '-', 's', 'e', 'e', '-', 'a', 'o', 'r'], [⟨['g', 'v'], ['m', 'u', 'l', 't', 'i', 's', 'p', '.', 'd', 'a', 't'], none⟩, ⟨['n', 'a', 'x'], ['s', 'e', 'e'], some '-'⟩, ⟨['a'], ['a', 'o', 'r'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subjPerson", "3"), ("subjNumber", "sg"), ("objPerson", "1"), ("objNumber", "pl"), ("objCase", "dat"), ("screeve", "aorist"), ("prefix", "gv"), ("suffix1", "a")] }

def ex_23b_t : Datum :=
  { id := "mcginnis2013_23b_t"
    source := ⟨"mcginnis-2013", "(23b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "gv-nax-a-t"
    glossedTokens := [("gv-nax-a-t", "multisp.dat-see-aor-pl")]
    glossedWords := [⟨['g', 'v', '-', 'n', 'a', 'x', '-', 'a', '-', 't'], ['m', 'u', 'l', 't', 'i', 's', 'p', '.', 'd', 'a', 't', '-', 's', 'e', 'e', '-', 'a', 'o', 'r', '-', 'p', 'l'], [⟨['g', 'v'], ['m', 'u', 'l', 't', 'i', 's', 'p', '.', 'd', 'a', 't'], none⟩, ⟨['n', 'a', 'x'], ['s', 'e', 'e'], some '-'⟩, ⟨['a'], ['a', 'o', 'r'], some '-'⟩, ⟨['t'], ['p', 'l'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("subjPerson", "3"), ("subjNumber", "sg"), ("objPerson", "1"), ("objNumber", "pl"), ("objCase", "dat"), ("screeve", "aorist"), ("prefix", "gv"), ("suffix1", "a"), ("suffix2", "t")] }

def ex_26 : Datum :=
  { id := "mcginnis2013_26"
    source := ⟨"mcginnis-2013", "(26)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "gv-nax-es"
    glossedTokens := [("gv-nax-es", "multisp.dat-see-aor.3pl")]
    glossedWords := [⟨['g', 'v', '-', 'n', 'a', 'x', '-', 'e', 's'], ['m', 'u', 'l', 't', 'i', 's', 'p', '.', 'd', 'a', 't', '-', 's', 'e', 'e', '-', 'a', 'o', 'r', '.', '3', 'p', 'l'], [⟨['g', 'v'], ['m', 'u', 'l', 't', 'i', 's', 'p', '.', 'd', 'a', 't'], none⟩, ⟨['n', 'a', 'x'], ['s', 'e', 'e'], some '-'⟩, ⟨['e', 's'], ['a', 'o', 'r', '.', '3', 'p', 'l'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subjPerson", "3"), ("subjNumber", "pl"), ("objPerson", "1"), ("objNumber", "pl"), ("objCase", "dat"), ("screeve", "aorist"), ("prefix", "gv"), ("suffix1", "es")] }

def all : List Datum := [ex_17a, ex_17b, ex_3a_pl, ex_3b, ex_5c, ex_6a, ex_6b_we, ex_6b_i, ex_6c, ex_18a, ex_18b, ex_18b_st, ex_18b_ts, ex_21, ex_23a, ex_23b, ex_23b_t, ex_26]

end McGinnis2013.Examples
