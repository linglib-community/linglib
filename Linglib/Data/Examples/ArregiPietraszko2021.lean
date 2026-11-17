module

public import Linglib.Data.Examples.Schema

/-!
# `ArregiPietraszko2021` — typed example data

Auto-generated from `Linglib/Data/Examples/ArregiPietraszko2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ArregiPietraszko2021.Examples`.
-/

@[expose] public section

namespace ArregiPietraszko2021.Examples

def ex_6 : Datum :=
  { id := "arregipietraszko2021_6"
    source := ⟨"pollock-1989", "(4b)"⟩
    reportedIn := some ⟨"arregi-pietraszko-2021", "(6)"⟩
    language := "stan1290"
    primaryText := "Jean embrasse souvent Marie."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Jean souvent embrasse Marie.", .ungrammatical)]
    readings := []
    paperFeatures := [("context", "declarative"), ("verbType", "lexical"), ("finitePosition", "T")] }

def ex_7 : Datum :=
  { id := "arregipietraszko2021_7"
    source := ⟨"arregi-pietraszko-2021", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue often eats fish."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Sue eats often fish.", .ungrammatical)]
    readings := []
    paperFeatures := [("context", "declarative"), ("verbType", "lexical"), ("finitePosition", "V")] }

def ex_10a : Datum :=
  { id := "arregipietraszko2021_10a"
    source := ⟨"arregi-pietraszko-2021", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He has not understood."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "negation"), ("verbType", "auxiliary"), ("finitePosition", "T"), ("doSupport", "false")] }

def ex_10b : Datum :=
  { id := "arregipietraszko2021_10b"
    source := ⟨"pollock-1989", "(11b)"⟩
    reportedIn := some ⟨"arregi-pietraszko-2021", "(10b)"⟩
    language := "stan1290"
    primaryText := "Il a pas compris."
    glossedTokens := [("Il", "he"), ("a", "has"), ("pas", "not"), ("compris", "understood")]
    glossedWords := [⟨['I', 'l'], ['h', 'e'], [⟨['I', 'l'], ['h', 'e'], none⟩]⟩, ⟨['a'], ['h', 'a', 's'], [⟨['a'], ['h', 'a', 's'], none⟩]⟩, ⟨['p', 'a', 's'], ['n', 'o', 't'], [⟨['p', 'a', 's'], ['n', 'o', 't'], none⟩]⟩, ⟨['c', 'o', 'm', 'p', 'r', 'i', 's'], ['u', 'n', 'd', 'e', 'r', 's', 't', 'o', 'o', 'd'], [⟨['c', 'o', 'm', 'p', 'r', 'i', 's'], ['u', 'n', 'd', 'e', 'r', 's', 't', 'o', 'o', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "negation"), ("verbType", "auxiliary"), ("finitePosition", "T"), ("doSupport", "false")] }

def ex_12 : Datum :=
  { id := "arregipietraszko2021_12"
    source := ⟨"arregi-pietraszko-2021", "(12)"⟩
    reportedIn := none
    language := "nort2795"
    primaryText := "Isi-lwane si-za-gijima."
    glossedTokens := [("Isi-lwane", "7-lion"), ("si-za-gijima", "7SBJ-FUT-run")]
    glossedWords := [⟨['I', 's', 'i', '-', 'l', 'w', 'a', 'n', 'e'], ['7', '-', 'l', 'i', 'o', 'n'], [⟨['I', 's', 'i'], ['7'], none⟩, ⟨['l', 'w', 'a', 'n', 'e'], ['l', 'i', 'o', 'n'], some '-'⟩]⟩, ⟨['s', 'i', '-', 'z', 'a', '-', 'g', 'i', 'j', 'i', 'm', 'a'], ['7', 'S', 'B', 'J', '-', 'F', 'U', 'T', '-', 'r', 'u', 'n'], [⟨['s', 'i'], ['7', 'S', 'B', 'J'], none⟩, ⟨['z', 'a'], ['F', 'U', 'T'], some '-'⟩, ⟨['g', 'i', 'j', 'i', 'm', 'a'], ['r', 'u', 'n'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "declarative")] }

def ex_13 : Datum :=
  { id := "arregipietraszko2021_13"
    source := ⟨"arregi-pietraszko-2021", "(13)"⟩
    reportedIn := none
    language := "nort2795"
    primaryText := "isi-lwane esi-za-gijima"
    glossedTokens := [("isi-lwane", "7-lion"), ("esi-za-gijima", "7REL-FUT-run")]
    glossedWords := [⟨['i', 's', 'i', '-', 'l', 'w', 'a', 'n', 'e'], ['7', '-', 'l', 'i', 'o', 'n'], [⟨['i', 's', 'i'], ['7'], none⟩, ⟨['l', 'w', 'a', 'n', 'e'], ['l', 'i', 'o', 'n'], some '-'⟩]⟩, ⟨['e', 's', 'i', '-', 'z', 'a', '-', 'g', 'i', 'j', 'i', 'm', 'a'], ['7', 'R', 'E', 'L', '-', 'F', 'U', 'T', '-', 'r', 'u', 'n'], [⟨['e', 's', 'i'], ['7', 'R', 'E', 'L'], none⟩, ⟨['z', 'a'], ['F', 'U', 'T'], some '-'⟩, ⟨['g', 'i', 'j', 'i', 'm', 'a'], ['r', 'u', 'n'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "relative")] }

def ex_16 : Datum :=
  { id := "arregipietraszko2021_16"
    source := ⟨"arregi-pietraszko-2021", "(16)"⟩
    reportedIn := none
    language := "nort2795"
    primaryText := "i-nyama isi-lwane esi-yi-dlileyo"
    glossedTokens := [("i-nyama", "9-meat"), ("isi-lwane", "7-lion"), ("esi-yi-dlileyo", "7REL-9OBJ-ate.DSJ")]
    glossedWords := [⟨['i', '-', 'n', 'y', 'a', 'm', 'a'], ['9', '-', 'm', 'e', 'a', 't'], [⟨['i'], ['9'], none⟩, ⟨['n', 'y', 'a', 'm', 'a'], ['m', 'e', 'a', 't'], some '-'⟩]⟩, ⟨['i', 's', 'i', '-', 'l', 'w', 'a', 'n', 'e'], ['7', '-', 'l', 'i', 'o', 'n'], [⟨['i', 's', 'i'], ['7'], none⟩, ⟨['l', 'w', 'a', 'n', 'e'], ['l', 'i', 'o', 'n'], some '-'⟩]⟩, ⟨['e', 's', 'i', '-', 'y', 'i', '-', 'd', 'l', 'i', 'l', 'e', 'y', 'o'], ['7', 'R', 'E', 'L', '-', '9', 'O', 'B', 'J', '-', 'a', 't', 'e', '.', 'D', 'S', 'J'], [⟨['e', 's', 'i'], ['7', 'R', 'E', 'L'], none⟩, ⟨['y', 'i'], ['9', 'O', 'B', 'J'], some '-'⟩, ⟨['d', 'l', 'i', 'l', 'e', 'y', 'o'], ['a', 't', 'e', '.', 'D', 'S', 'J'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "relative"), ("relPrefixPosition", "T")] }

def ex_26 : Datum :=
  { id := "arregipietraszko2021_26"
    source := ⟨"vikner-1995", "p. 47"⟩
    reportedIn := some ⟨"arregi-pietraszko-2021", "(26)"⟩
    language := "dani1285"
    primaryText := "Om morgenen drikker Peter ofte kaffe."
    glossedTokens := [("Om", "in"), ("morgenen", "the.morning"), ("drikker", "drinks"), ("Peter", "Peter"), ("ofte", "often"), ("kaffe", "coffee")]
    glossedWords := [⟨['O', 'm'], ['i', 'n'], [⟨['O', 'm'], ['i', 'n'], none⟩]⟩, ⟨['m', 'o', 'r', 'g', 'e', 'n', 'e', 'n'], ['t', 'h', 'e', '.', 'm', 'o', 'r', 'n', 'i', 'n', 'g'], [⟨['m', 'o', 'r', 'g', 'e', 'n', 'e', 'n'], ['t', 'h', 'e', '.', 'm', 'o', 'r', 'n', 'i', 'n', 'g'], none⟩]⟩, ⟨['d', 'r', 'i', 'k', 'k', 'e', 'r'], ['d', 'r', 'i', 'n', 'k', 's'], [⟨['d', 'r', 'i', 'k', 'k', 'e', 'r'], ['d', 'r', 'i', 'n', 'k', 's'], none⟩]⟩, ⟨['P', 'e', 't', 'e', 'r'], ['P', 'e', 't', 'e', 'r'], [⟨['P', 'e', 't', 'e', 'r'], ['P', 'e', 't', 'e', 'r'], none⟩]⟩, ⟨['o', 'f', 't', 'e'], ['o', 'f', 't', 'e', 'n'], [⟨['o', 'f', 't', 'e'], ['o', 'f', 't', 'e', 'n'], none⟩]⟩, ⟨['k', 'a', 'f', 'f', 'e'], ['c', 'o', 'f', 'f', 'e', 'e'], [⟨['k', 'a', 'f', 'f', 'e'], ['c', 'o', 'f', 'f', 'e', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "v2"), ("verbType", "lexical"), ("finitePosition", "C"), ("doSupport", "false")] }

def ex_27 : Datum :=
  { id := "arregipietraszko2021_27"
    source := ⟨"vikner-1995", "p. 47"⟩
    reportedIn := some ⟨"arregi-pietraszko-2021", "(27)"⟩
    language := "dani1285"
    primaryText := "Vi ved at Peter ofte drikker kaffe om morgenen."
    glossedTokens := [("Vi", "we"), ("ved", "know"), ("at", "that"), ("Peter", "Peter"), ("ofte", "often"), ("drikker", "drinks"), ("kaffe", "coffee"), ("om", "in"), ("morgenen", "the.morning")]
    glossedWords := [⟨['V', 'i'], ['w', 'e'], [⟨['V', 'i'], ['w', 'e'], none⟩]⟩, ⟨['v', 'e', 'd'], ['k', 'n', 'o', 'w'], [⟨['v', 'e', 'd'], ['k', 'n', 'o', 'w'], none⟩]⟩, ⟨['a', 't'], ['t', 'h', 'a', 't'], [⟨['a', 't'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['P', 'e', 't', 'e', 'r'], ['P', 'e', 't', 'e', 'r'], [⟨['P', 'e', 't', 'e', 'r'], ['P', 'e', 't', 'e', 'r'], none⟩]⟩, ⟨['o', 'f', 't', 'e'], ['o', 'f', 't', 'e', 'n'], [⟨['o', 'f', 't', 'e'], ['o', 'f', 't', 'e', 'n'], none⟩]⟩, ⟨['d', 'r', 'i', 'k', 'k', 'e', 'r'], ['d', 'r', 'i', 'n', 'k', 's'], [⟨['d', 'r', 'i', 'k', 'k', 'e', 'r'], ['d', 'r', 'i', 'n', 'k', 's'], none⟩]⟩, ⟨['k', 'a', 'f', 'f', 'e'], ['c', 'o', 'f', 'f', 'e', 'e'], [⟨['k', 'a', 'f', 'f', 'e'], ['c', 'o', 'f', 'f', 'e', 'e'], none⟩]⟩, ⟨['o', 'm'], ['i', 'n'], [⟨['o', 'm'], ['i', 'n'], none⟩]⟩, ⟨['m', 'o', 'r', 'g', 'e', 'n', 'e', 'n'], ['t', 'h', 'e', '.', 'm', 'o', 'r', 'n', 'i', 'n', 'g'], [⟨['m', 'o', 'r', 'g', 'e', 'n', 'e', 'n'], ['t', 'h', 'e', '.', 'm', 'o', 'r', 'n', 'i', 'n', 'g'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "declarative"), ("verbType", "lexical"), ("finitePosition", "V")] }

def ex_30 : Datum :=
  { id := "arregipietraszko2021_30"
    source := ⟨"arregi-pietraszko-2021", "(30)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Llamad nos!"
    glossedTokens := [("Llamad", "call.IMP.2PL"), ("nos", "us")]
    glossedWords := [⟨['L', 'l', 'a', 'm', 'a', 'd'], ['c', 'a', 'l', 'l', '.', 'I', 'M', 'P', '.', '2', 'P', 'L'], [⟨['L', 'l', 'a', 'm', 'a', 'd'], ['c', 'a', 'l', 'l', '.', 'I', 'M', 'P', '.', '2', 'P', 'L'], none⟩]⟩, ⟨['n', 'o', 's'], ['u', 's'], [⟨['n', 'o', 's'], ['u', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "imperativeAff"), ("verbType", "lexical"), ("finitePosition", "C"), ("imperativeForm", "true")] }

def ex_31 : Datum :=
  { id := "arregipietraszko2021_31"
    source := ⟨"arregi-pietraszko-2021", "(31)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "No nos llaméis!"
    glossedTokens := [("No", "not"), ("nos", "us"), ("llaméis", "call.IMP/PRS.SBJV.2PL")]
    glossedWords := [⟨['N', 'o'], ['n', 'o', 't'], [⟨['N', 'o'], ['n', 'o', 't'], none⟩]⟩, ⟨['n', 'o', 's'], ['u', 's'], [⟨['n', 'o', 's'], ['u', 's'], none⟩]⟩, ⟨['l', 'l', 'a', 'm', 'é', 'i', 's'], ['c', 'a', 'l', 'l', '.', 'I', 'M', 'P', '/', 'P', 'R', 'S', '.', 'S', 'B', 'J', 'V', '.', '2', 'P', 'L'], [⟨['l', 'l', 'a', 'm', 'é', 'i', 's'], ['c', 'a', 'l', 'l', '.', 'I', 'M', 'P', '/', 'P', 'R', 'S', '.', 'S', 'B', 'J', 'V', '.', '2', 'P', 'L'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "imperativeNeg"), ("verbType", "lexical"), ("finitePosition", "T"), ("imperativeForm", "false")] }

def ex_33 : Datum :=
  { id := "arregipietraszko2021_33"
    source := ⟨"manzini-savoia-2005", "p. 424"⟩
    reportedIn := some ⟨"arregi-pietraszko-2021", "(33)"⟩
    language := "lowe1386"
    primaryText := "ans klɔˈmai"
    glossedTokens := [("ans", "us"), ("klɔˈmai", "call.IMP.2PL")]
    glossedWords := [⟨['a', 'n', 's'], ['u', 's'], [⟨['a', 'n', 's'], ['u', 's'], none⟩]⟩, ⟨['k', 'l', 'ɔ', 'ˈ', 'm', 'a', 'i'], ['c', 'a', 'l', 'l', '.', 'I', 'M', 'P', '.', '2', 'P', 'L'], [⟨['k', 'l', 'ɔ', 'ˈ', 'm', 'a', 'i'], ['c', 'a', 'l', 'l', '.', 'I', 'M', 'P', '.', '2', 'P', 'L'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "imperativeAff"), ("verbType", "lexical"), ("finitePosition", "T"), ("imperativeForm", "true")] }

def ex_34 : Datum :=
  { id := "arregipietraszko2021_34"
    source := ⟨"manzini-savoia-2005", "p. 424"⟩
    reportedIn := some ⟨"arregi-pietraszko-2021", "(34)"⟩
    language := "lowe1386"
    primaryText := "nu ns klɔmaˈrai"
    glossedTokens := [("nu", "not"), ("ns", "us"), ("klɔmaˈrai", "call.IMP/INF.2PL")]
    glossedWords := [⟨['n', 'u'], ['n', 'o', 't'], [⟨['n', 'u'], ['n', 'o', 't'], none⟩]⟩, ⟨['n', 's'], ['u', 's'], [⟨['n', 's'], ['u', 's'], none⟩]⟩, ⟨['k', 'l', 'ɔ', 'm', 'a', 'ˈ', 'r', 'a', 'i'], ['c', 'a', 'l', 'l', '.', 'I', 'M', 'P', '/', 'I', 'N', 'F', '.', '2', 'P', 'L'], [⟨['k', 'l', 'ɔ', 'm', 'a', 'ˈ', 'r', 'a', 'i'], ['c', 'a', 'l', 'l', '.', 'I', 'M', 'P', '/', 'I', 'N', 'F', '.', '2', 'P', 'L'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "imperativeNeg"), ("verbType", "lexical"), ("finitePosition", "T"), ("imperativeForm", "false")] }

def ex_36a : Datum :=
  { id := "arregipietraszko2021_36a"
    source := ⟨"arregi-pietraszko-2021", "(36a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue does not eat fish."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Sue doesn't eat fish.", .acceptable), ("Sue not eats fish.", .ungrammatical), ("Sue eats not fish.", .ungrammatical)]
    readings := []
    paperFeatures := [("context", "negation"), ("verbType", "lexical"), ("finitePosition", "T"), ("doSupport", "true"), ("verbForm", "bare")] }

def ex_36b : Datum :=
  { id := "arregipietraszko2021_36b"
    source := ⟨"arregi-pietraszko-2021", "(36b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue DOES (so) eat fish."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Sue so eats fish.", .ungrammatical), ("Sue eats so fish.", .ungrammatical)]
    readings := []
    paperFeatures := [("context", "verum"), ("verbType", "lexical"), ("finitePosition", "T"), ("doSupport", "true"), ("verbForm", "bare")] }

def ex_36c : Datum :=
  { id := "arregipietraszko2021_36c"
    source := ⟨"arregi-pietraszko-2021", "(36c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Where does Sue eat fish?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Where Sue eats fish?", .ungrammatical), ("Where eats Sue fish?", .ungrammatical)]
    readings := []
    paperFeatures := [("context", "inversion"), ("verbType", "lexical"), ("finitePosition", "C"), ("doSupport", "true"), ("verbForm", "bare")] }

def ex_37a : Datum :=
  { id := "arregipietraszko2021_37a"
    source := ⟨"arregi-pietraszko-2021", "(37a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue is not eating fish."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Sue isn't eating fish.", .acceptable), ("Sue does not be eating fish.", .ungrammatical), ("Sue doesn't be eating fish.", .ungrammatical)]
    readings := []
    paperFeatures := [("context", "negation"), ("verbType", "auxiliary"), ("finitePosition", "T"), ("doSupport", "false")] }

def ex_37b : Datum :=
  { id := "arregipietraszko2021_37b"
    source := ⟨"arregi-pietraszko-2021", "(37b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue IS (so) eating fish."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Sue DOES (so) be eating fish.", .ungrammatical)]
    readings := []
    paperFeatures := [("context", "verum"), ("verbType", "auxiliary"), ("finitePosition", "T"), ("doSupport", "false")] }

def ex_37c : Datum :=
  { id := "arregipietraszko2021_37c"
    source := ⟨"arregi-pietraszko-2021", "(37c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Where is Sue eating fish?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Where does Sue be eating fish?", .ungrammatical)]
    readings := []
    paperFeatures := [("context", "inversion"), ("verbType", "auxiliary"), ("finitePosition", "C"), ("doSupport", "false")] }

def fn38 : Datum :=
  { id := "arregipietraszko2021_fn38"
    source := ⟨"arregi-pietraszko-2021", "fn. 38"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who eats fish?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "subjectWh"), ("verbType", "lexical"), ("finitePosition", "V"), ("doSupport", "false")] }

def ex_51 : Datum :=
  { id := "arregipietraszko2021_51"
    source := ⟨"vikner-1995", "p. 144"⟩
    reportedIn := some ⟨"arregi-pietraszko-2021", "(51)"⟩
    language := "dani1285"
    primaryText := "Jeg tror at Johan ikke købte bogen."
    glossedTokens := [("Jeg", "I"), ("tror", "believe"), ("at", "that"), ("Johan", "Johan"), ("ikke", "not"), ("købte", "bought"), ("bogen", "the.book")]
    glossedWords := [⟨['J', 'e', 'g'], ['I'], [⟨['J', 'e', 'g'], ['I'], none⟩]⟩, ⟨['t', 'r', 'o', 'r'], ['b', 'e', 'l', 'i', 'e', 'v', 'e'], [⟨['t', 'r', 'o', 'r'], ['b', 'e', 'l', 'i', 'e', 'v', 'e'], none⟩]⟩, ⟨['a', 't'], ['t', 'h', 'a', 't'], [⟨['a', 't'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['J', 'o', 'h', 'a', 'n'], ['J', 'o', 'h', 'a', 'n'], [⟨['J', 'o', 'h', 'a', 'n'], ['J', 'o', 'h', 'a', 'n'], none⟩]⟩, ⟨['i', 'k', 'k', 'e'], ['n', 'o', 't'], [⟨['i', 'k', 'k', 'e'], ['n', 'o', 't'], none⟩]⟩, ⟨['k', 'ø', 'b', 't', 'e'], ['b', 'o', 'u', 'g', 'h', 't'], [⟨['k', 'ø', 'b', 't', 'e'], ['b', 'o', 'u', 'g', 'h', 't'], none⟩]⟩, ⟨['b', 'o', 'g', 'e', 'n'], ['t', 'h', 'e', '.', 'b', 'o', 'o', 'k'], [⟨['b', 'o', 'g', 'e', 'n'], ['t', 'h', 'e', '.', 'b', 'o', 'o', 'k'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "negation"), ("verbType", "lexical"), ("finitePosition", "V"), ("doSupport", "false")] }

def ex_52 : Datum :=
  { id := "arregipietraszko2021_52"
    source := ⟨"vikner-1995", "p. 47"⟩
    reportedIn := some ⟨"arregi-pietraszko-2021", "(52)"⟩
    language := "dani1285"
    primaryText := "Om morgenen drikker Peter ofte kaffe."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "v2"), ("verbType", "lexical"), ("finitePosition", "C"), ("doSupport", "false")] }

def ex_53a : Datum :=
  { id := "arregipietraszko2021_53a"
    source := ⟨"beninca-poletto-2004", "pp. 59–60"⟩
    reportedIn := some ⟨"arregi-pietraszko-2021", "(53a)"⟩
    language := "lomb1257"
    primaryText := "l tʃàkola semper"
    glossedTokens := [("l", "he"), ("tʃàkola", "speak.PRS.IND.3SG"), ("semper", "always")]
    glossedWords := [⟨['l'], ['h', 'e'], [⟨['l'], ['h', 'e'], none⟩]⟩, ⟨['t', 'ʃ', 'à', 'k', 'o', 'l', 'a'], ['s', 'p', 'e', 'a', 'k', '.', 'P', 'R', 'S', '.', 'I', 'N', 'D', '.', '3', 'S', 'G'], [⟨['t', 'ʃ', 'à', 'k', 'o', 'l', 'a'], ['s', 'p', 'e', 'a', 'k', '.', 'P', 'R', 'S', '.', 'I', 'N', 'D', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['s', 'e', 'm', 'p', 'e', 'r'], ['a', 'l', 'w', 'a', 'y', 's'], [⟨['s', 'e', 'm', 'p', 'e', 'r'], ['a', 'l', 'w', 'a', 'y', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "declarative"), ("verbType", "lexical"), ("finitePosition", "T")] }

def ex_53b : Datum :=
  { id := "arregipietraszko2021_53b"
    source := ⟨"beninca-poletto-2004", "pp. 59–60"⟩
    reportedIn := some ⟨"arregi-pietraszko-2021", "(53b)"⟩
    language := "lomb1257"
    primaryText := "l tʃàkola mìa"
    glossedTokens := [("l", "he"), ("tʃàkola", "speak.PRS.IND.3SG"), ("mìa", "not")]
    glossedWords := [⟨['l'], ['h', 'e'], [⟨['l'], ['h', 'e'], none⟩]⟩, ⟨['t', 'ʃ', 'à', 'k', 'o', 'l', 'a'], ['s', 'p', 'e', 'a', 'k', '.', 'P', 'R', 'S', '.', 'I', 'N', 'D', '.', '3', 'S', 'G'], [⟨['t', 'ʃ', 'à', 'k', 'o', 'l', 'a'], ['s', 'p', 'e', 'a', 'k', '.', 'P', 'R', 'S', '.', 'I', 'N', 'D', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['m', 'ì', 'a'], ['n', 'o', 't'], [⟨['m', 'ì', 'a'], ['n', 'o', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "negation"), ("verbType", "lexical"), ("finitePosition", "T"), ("doSupport", "false")] }

def ex_54 : Datum :=
  { id := "arregipietraszko2021_54"
    source := ⟨"beninca-poletto-2004", "p. 59"⟩
    reportedIn := some ⟨"arregi-pietraszko-2021", "(54)"⟩
    language := "lomb1257"
    primaryText := "l à semper tʃakolà"
    glossedTokens := [("l", "he"), ("à", "have.PRS.IND.3SG"), ("semper", "always"), ("tʃakolà", "spoken")]
    glossedWords := [⟨['l'], ['h', 'e'], [⟨['l'], ['h', 'e'], none⟩]⟩, ⟨['à'], ['h', 'a', 'v', 'e', '.', 'P', 'R', 'S', '.', 'I', 'N', 'D', '.', '3', 'S', 'G'], [⟨['à'], ['h', 'a', 'v', 'e', '.', 'P', 'R', 'S', '.', 'I', 'N', 'D', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['s', 'e', 'm', 'p', 'e', 'r'], ['a', 'l', 'w', 'a', 'y', 's'], [⟨['s', 'e', 'm', 'p', 'e', 'r'], ['a', 'l', 'w', 'a', 'y', 's'], none⟩]⟩, ⟨['t', 'ʃ', 'a', 'k', 'o', 'l', 'à'], ['s', 'p', 'o', 'k', 'e', 'n'], [⟨['t', 'ʃ', 'a', 'k', 'o', 'l', 'à'], ['s', 'p', 'o', 'k', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "declarative"), ("verbType", "auxiliary"), ("finitePosition", "T")] }

def ex_55 : Datum :=
  { id := "arregipietraszko2021_55"
    source := ⟨"beninca-poletto-2004", "p. 52"⟩
    reportedIn := some ⟨"arregi-pietraszko-2021", "(55)"⟩
    language := "lomb1257"
    primaryText := "à-l majà"
    glossedTokens := [("à-l", "have.PRS.IND.3SG-he"), ("majà", "eaten")]
    glossedWords := [⟨['à', '-', 'l'], ['h', 'a', 'v', 'e', '.', 'P', 'R', 'S', '.', 'I', 'N', 'D', '.', '3', 'S', 'G', '-', 'h', 'e'], [⟨['à'], ['h', 'a', 'v', 'e', '.', 'P', 'R', 'S', '.', 'I', 'N', 'D', '.', '3', 'S', 'G'], none⟩, ⟨['l'], ['h', 'e'], some '-'⟩]⟩, ⟨['m', 'a', 'j', 'à'], ['e', 'a', 't', 'e', 'n'], [⟨['m', 'a', 'j', 'à'], ['e', 'a', 't', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "inversion"), ("verbType", "auxiliary"), ("finitePosition", "C"), ("doSupport", "false")] }

def ex_56b : Datum :=
  { id := "arregipietraszko2021_56b"
    source := ⟨"beninca-poletto-2004", "p. 52"⟩
    reportedIn := some ⟨"arregi-pietraszko-2021", "(56b)"⟩
    language := "lomb1257"
    primaryText := "fa-l majà"
    glossedTokens := [("fa-l", "do.PRS.IND.3SG-he"), ("majà", "eat.INF")]
    glossedWords := [⟨['f', 'a', '-', 'l'], ['d', 'o', '.', 'P', 'R', 'S', '.', 'I', 'N', 'D', '.', '3', 'S', 'G', '-', 'h', 'e'], [⟨['f', 'a'], ['d', 'o', '.', 'P', 'R', 'S', '.', 'I', 'N', 'D', '.', '3', 'S', 'G'], none⟩, ⟨['l'], ['h', 'e'], some '-'⟩]⟩, ⟨['m', 'a', 'j', 'à'], ['e', 'a', 't', '.', 'I', 'N', 'F'], [⟨['m', 'a', 'j', 'à'], ['e', 'a', 't', '.', 'I', 'N', 'F'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("maja-l", .ungrammatical)]
    readings := []
    paperFeatures := [("context", "inversion"), ("verbType", "lexical"), ("finitePosition", "C"), ("doSupport", "true"), ("verbForm", "infinitive")] }

def ex_57 : Datum :=
  { id := "arregipietraszko2021_57"
    source := ⟨"bjorkman-2011", "pp. 190–191"⟩
    reportedIn := some ⟨"arregi-pietraszko-2021", "(57)"⟩
    language := "lomb1257"
    primaryText := "fe-t mia majal 'l pom"
    glossedTokens := [("fe-t", "do.PRS.IND.2SG-you"), ("mia", "not"), ("majal", "eat.INF"), ("'l", "the"), ("pom", "apple")]
    glossedWords := [⟨['f', 'e', '-', 't'], ['d', 'o', '.', 'P', 'R', 'S', '.', 'I', 'N', 'D', '.', '2', 'S', 'G', '-', 'y', 'o', 'u'], [⟨['f', 'e'], ['d', 'o', '.', 'P', 'R', 'S', '.', 'I', 'N', 'D', '.', '2', 'S', 'G'], none⟩, ⟨['t'], ['y', 'o', 'u'], some '-'⟩]⟩, ⟨['m', 'i', 'a'], ['n', 'o', 't'], [⟨['m', 'i', 'a'], ['n', 'o', 't'], none⟩]⟩, ⟨['m', 'a', 'j', 'a', 'l'], ['e', 'a', 't', '.', 'I', 'N', 'F'], [⟨['m', 'a', 'j', 'a', 'l'], ['e', 'a', 't', '.', 'I', 'N', 'F'], none⟩]⟩, ⟨['\'', 'l'], ['t', 'h', 'e'], [⟨['\'', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['p', 'o', 'm'], ['a', 'p', 'p', 'l', 'e'], [⟨['p', 'o', 'm'], ['a', 'p', 'p', 'l', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "inversion"), ("verbType", "lexical"), ("finitePosition", "C"), ("doSupport", "true"), ("verbForm", "infinitive")] }

def ex_61 : Datum :=
  { id := "arregipietraszko2021_61"
    source := ⟨"arregi-pietraszko-2021", "(61)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I wanted to give him a book and I did."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "ellipsis"), ("verbType", "lexical"), ("finitePosition", "T"), ("doSupport", "true")] }

def ex_62 : Datum :=
  { id := "arregipietraszko2021_62"
    source := ⟨"arregi-pietraszko-2021", "(62)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Chciałam mu dać książkę i dałam."
    glossedTokens := [("Chciałam", "wanted.1SG"), ("mu", "him"), ("dać", "give.INF"), ("książkę", "book"), ("i", "and"), ("dałam", "gave.1SG")]
    glossedWords := [⟨['C', 'h', 'c', 'i', 'a', 'ł', 'a', 'm'], ['w', 'a', 'n', 't', 'e', 'd', '.', '1', 'S', 'G'], [⟨['C', 'h', 'c', 'i', 'a', 'ł', 'a', 'm'], ['w', 'a', 'n', 't', 'e', 'd', '.', '1', 'S', 'G'], none⟩]⟩, ⟨['m', 'u'], ['h', 'i', 'm'], [⟨['m', 'u'], ['h', 'i', 'm'], none⟩]⟩, ⟨['d', 'a', 'ć'], ['g', 'i', 'v', 'e', '.', 'I', 'N', 'F'], [⟨['d', 'a', 'ć'], ['g', 'i', 'v', 'e', '.', 'I', 'N', 'F'], none⟩]⟩, ⟨['k', 's', 'i', 'ą', 'ż', 'k', 'ę'], ['b', 'o', 'o', 'k'], [⟨['k', 's', 'i', 'ą', 'ż', 'k', 'ę'], ['b', 'o', 'o', 'k'], none⟩]⟩, ⟨['i'], ['a', 'n', 'd'], [⟨['i'], ['a', 'n', 'd'], none⟩]⟩, ⟨['d', 'a', 'ł', 'a', 'm'], ['g', 'a', 'v', 'e', '.', '1', 'S', 'G'], [⟨['d', 'a', 'ł', 'a', 'm'], ['g', 'a', 'v', 'e', '.', '1', 'S', 'G'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Chciałam mu dać książkę i ją dałam.", .ungrammatical)]
    readings := []
    paperFeatures := [("context", "ellipsis"), ("verbType", "lexical"), ("finitePosition", "T"), ("doSupport", "false")] }

def ex_67 : Datum :=
  { id := "arregipietraszko2021_67"
    source := ⟨"sailor-2018", "pp. 855–856"⟩
    reportedIn := some ⟨"arregi-pietraszko-2021", "(67)"⟩
    language := "dani1285"
    primaryText := "Mona og Jasper vaskede bilen, eller rettere Mona gjorde."
    glossedTokens := [("Mona", "Mona"), ("og", "and"), ("Jasper", "Jasper"), ("vaskede", "washed"), ("bilen", "the.car"), ("eller", "or"), ("rettere", "rather"), ("Mona", "Mona"), ("gjorde", "did")]
    glossedWords := [⟨['M', 'o', 'n', 'a'], ['M', 'o', 'n', 'a'], [⟨['M', 'o', 'n', 'a'], ['M', 'o', 'n', 'a'], none⟩]⟩, ⟨['o', 'g'], ['a', 'n', 'd'], [⟨['o', 'g'], ['a', 'n', 'd'], none⟩]⟩, ⟨['J', 'a', 's', 'p', 'e', 'r'], ['J', 'a', 's', 'p', 'e', 'r'], [⟨['J', 'a', 's', 'p', 'e', 'r'], ['J', 'a', 's', 'p', 'e', 'r'], none⟩]⟩, ⟨['v', 'a', 's', 'k', 'e', 'd', 'e'], ['w', 'a', 's', 'h', 'e', 'd'], [⟨['v', 'a', 's', 'k', 'e', 'd', 'e'], ['w', 'a', 's', 'h', 'e', 'd'], none⟩]⟩, ⟨['b', 'i', 'l', 'e', 'n'], ['t', 'h', 'e', '.', 'c', 'a', 'r'], [⟨['b', 'i', 'l', 'e', 'n'], ['t', 'h', 'e', '.', 'c', 'a', 'r'], none⟩]⟩, ⟨['e', 'l', 'l', 'e', 'r'], ['o', 'r'], [⟨['e', 'l', 'l', 'e', 'r'], ['o', 'r'], none⟩]⟩, ⟨['r', 'e', 't', 't', 'e', 'r', 'e'], ['r', 'a', 't', 'h', 'e', 'r'], [⟨['r', 'e', 't', 't', 'e', 'r', 'e'], ['r', 'a', 't', 'h', 'e', 'r'], none⟩]⟩, ⟨['M', 'o', 'n', 'a'], ['M', 'o', 'n', 'a'], [⟨['M', 'o', 'n', 'a'], ['M', 'o', 'n', 'a'], none⟩]⟩, ⟨['g', 'j', 'o', 'r', 'd', 'e'], ['d', 'i', 'd'], [⟨['g', 'j', 'o', 'r', 'd', 'e'], ['d', 'i', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Mona og Jasper vaskede bilen, eller rettere Mona vaskede.", .ungrammatical)]
    readings := []
    paperFeatures := [("context", "ellipsisV2"), ("verbType", "lexical"), ("finitePosition", "C"), ("doSupport", "true")] }

def ex_70 : Datum :=
  { id := "arregipietraszko2021_70"
    source := ⟨"arregi-pietraszko-2021", "(70)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Oglądać mecz oglądałam."
    glossedTokens := [("Oglądać", "watch.INF"), ("mecz", "game"), ("oglądałam", "watched.1SG")]
    glossedWords := [⟨['O', 'g', 'l', 'ą', 'd', 'a', 'ć'], ['w', 'a', 't', 'c', 'h', '.', 'I', 'N', 'F'], [⟨['O', 'g', 'l', 'ą', 'd', 'a', 'ć'], ['w', 'a', 't', 'c', 'h', '.', 'I', 'N', 'F'], none⟩]⟩, ⟨['m', 'e', 'c', 'z'], ['g', 'a', 'm', 'e'], [⟨['m', 'e', 'c', 'z'], ['g', 'a', 'm', 'e'], none⟩]⟩, ⟨['o', 'g', 'l', 'ą', 'd', 'a', 'ł', 'a', 'm'], ['w', 'a', 't', 'c', 'h', 'e', 'd', '.', '1', 'S', 'G'], [⟨['o', 'g', 'l', 'ą', 'd', 'a', 'ł', 'a', 'm'], ['w', 'a', 't', 'c', 'h', 'e', 'd', '.', '1', 'S', 'G'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "fronting"), ("verbType", "lexical"), ("doSupport", "false"), ("frontedForm", "infinitive")] }

def ex_71 : Datum :=
  { id := "arregipietraszko2021_71"
    source := ⟨"arregi-pietraszko-2021", "(71)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Watch the game I did."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "fronting"), ("verbType", "lexical"), ("doSupport", "true"), ("frontedForm", "bare")] }

def ex_74a : Datum :=
  { id := "arregipietraszko2021_74a"
    source := ⟨"arregi-pietraszko-2021", "(74a)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Zaśpiewać, może zaśpiewam."
    glossedTokens := [("Zaśpiewać", "sing.INF"), ("może", "maybe"), ("zaśpiewam", "sing.FUT.1SG")]
    glossedWords := [⟨['Z', 'a', 'ś', 'p', 'i', 'e', 'w', 'a', 'ć'], ['s', 'i', 'n', 'g', '.', 'I', 'N', 'F'], [⟨['Z', 'a', 'ś', 'p', 'i', 'e', 'w', 'a', 'ć'], ['s', 'i', 'n', 'g', '.', 'I', 'N', 'F'], none⟩]⟩, ⟨['m', 'o', 'ż', 'e'], ['m', 'a', 'y', 'b', 'e'], [⟨['m', 'o', 'ż', 'e'], ['m', 'a', 'y', 'b', 'e'], none⟩]⟩, ⟨['z', 'a', 'ś', 'p', 'i', 'e', 'w', 'a', 'm'], ['s', 'i', 'n', 'g', '.', 'F', 'U', 'T', '.', '1', 'S', 'G'], [⟨['z', 'a', 'ś', 'p', 'i', 'e', 'w', 'a', 'm'], ['s', 'i', 'n', 'g', '.', 'F', 'U', 'T', '.', '1', 'S', 'G'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "fronting"), ("verbType", "lexical"), ("doSupport", "false"), ("frontedForm", "infinitive")] }

def ex_74b : Datum :=
  { id := "arregipietraszko2021_74b"
    source := ⟨"landau-2006", "p. 32"⟩
    reportedIn := some ⟨"arregi-pietraszko-2021", "(74b)"⟩
    language := "hebr1245"
    primaryText := "Lirkod, Gil lo yirkod ba-xayim."
    glossedTokens := [("Lirkod", "dance.INF"), ("Gil", "Gil"), ("lo", "not"), ("yirkod", "dance.FUT"), ("ba-xayim", "in.the-life")]
    glossedWords := [⟨['L', 'i', 'r', 'k', 'o', 'd'], ['d', 'a', 'n', 'c', 'e', '.', 'I', 'N', 'F'], [⟨['L', 'i', 'r', 'k', 'o', 'd'], ['d', 'a', 'n', 'c', 'e', '.', 'I', 'N', 'F'], none⟩]⟩, ⟨['G', 'i', 'l'], ['G', 'i', 'l'], [⟨['G', 'i', 'l'], ['G', 'i', 'l'], none⟩]⟩, ⟨['l', 'o'], ['n', 'o', 't'], [⟨['l', 'o'], ['n', 'o', 't'], none⟩]⟩, ⟨['y', 'i', 'r', 'k', 'o', 'd'], ['d', 'a', 'n', 'c', 'e', '.', 'F', 'U', 'T'], [⟨['y', 'i', 'r', 'k', 'o', 'd'], ['d', 'a', 'n', 'c', 'e', '.', 'F', 'U', 'T'], none⟩]⟩, ⟨['b', 'a', '-', 'x', 'a', 'y', 'i', 'm'], ['i', 'n', '.', 't', 'h', 'e', '-', 'l', 'i', 'f', 'e'], [⟨['b', 'a'], ['i', 'n', '.', 't', 'h', 'e'], none⟩, ⟨['x', 'a', 'y', 'i', 'm'], ['l', 'i', 'f', 'e'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "fronting"), ("verbType", "lexical"), ("doSupport", "false"), ("frontedForm", "infinitive")] }

def ex_77 : Datum :=
  { id := "arregipietraszko2021_77"
    source := ⟨"platzack-2012", "p. 281"⟩
    reportedIn := some ⟨"arregi-pietraszko-2021", "(77)"⟩
    language := "swed1254"
    primaryText := "… och körde bilen gjorde han."
    glossedTokens := [("och", "and"), ("körde", "drive.PST"), ("bilen", "the.car"), ("gjorde", "do.PST"), ("han", "he")]
    glossedWords := [⟨['o', 'c', 'h'], ['a', 'n', 'd'], [⟨['o', 'c', 'h'], ['a', 'n', 'd'], none⟩]⟩, ⟨['k', 'ö', 'r', 'd', 'e'], ['d', 'r', 'i', 'v', 'e', '.', 'P', 'S', 'T'], [⟨['k', 'ö', 'r', 'd', 'e'], ['d', 'r', 'i', 'v', 'e', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['b', 'i', 'l', 'e', 'n'], ['t', 'h', 'e', '.', 'c', 'a', 'r'], [⟨['b', 'i', 'l', 'e', 'n'], ['t', 'h', 'e', '.', 'c', 'a', 'r'], none⟩]⟩, ⟨['g', 'j', 'o', 'r', 'd', 'e'], ['d', 'o', '.', 'P', 'S', 'T'], [⟨['g', 'j', 'o', 'r', 'd', 'e'], ['d', 'o', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['h', 'a', 'n'], ['h', 'e'], [⟨['h', 'a', 'n'], ['h', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("… och köra bilen gjorde han.", .ungrammatical)]
    readings := []
    paperFeatures := [("context", "frontingV2"), ("verbType", "lexical"), ("doSupport", "true"), ("frontedForm", "finite")] }

def ex_80a : Datum :=
  { id := "arregipietraszko2021_80a"
    source := ⟨"travis-2003", "p. 244"⟩
    reportedIn := some ⟨"arregi-pietraszko-2021", "(80a)"⟩
    language := "east2295"
    primaryText := "Veys-n, veys ix."
    glossedTokens := [("Veys-n", "know.PRS.1SG-INF"), ("veys", "know.PRS.1SG"), ("ix", "I")]
    glossedWords := [⟨['V', 'e', 'y', 's', '-', 'n'], ['k', 'n', 'o', 'w', '.', 'P', 'R', 'S', '.', '1', 'S', 'G', '-', 'I', 'N', 'F'], [⟨['V', 'e', 'y', 's'], ['k', 'n', 'o', 'w', '.', 'P', 'R', 'S', '.', '1', 'S', 'G'], none⟩, ⟨['n'], ['I', 'N', 'F'], some '-'⟩]⟩, ⟨['v', 'e', 'y', 's'], ['k', 'n', 'o', 'w', '.', 'P', 'R', 'S', '.', '1', 'S', 'G'], [⟨['v', 'e', 'y', 's'], ['k', 'n', 'o', 'w', '.', 'P', 'R', 'S', '.', '1', 'S', 'G'], none⟩]⟩, ⟨['i', 'x'], ['I'], [⟨['i', 'x'], ['I'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "frontingV2"), ("verbType", "lexical"), ("doSupport", "false"), ("frontedForm", "pseudoInfinitive")] }

def ex_80b : Datum :=
  { id := "arregipietraszko2021_80b"
    source := ⟨"travis-2003", "p. 244"⟩
    reportedIn := some ⟨"arregi-pietraszko-2021", "(80b)"⟩
    language := "east2295"
    primaryText := "Iz-n, iz es reb yixezkl gombiners shtub."
    glossedTokens := [("Iz-n", "be.PRS.3SG-INF"), ("iz", "be.PRS.3SG"), ("es", "it"), ("reb", "Mr."), ("yixezkl", "Yikhezkl's"), ("gombiners", ""), ("shtub", "home")]
    glossedWords := [⟨['I', 'z', '-', 'n'], ['b', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G', '-', 'I', 'N', 'F'], [⟨['I', 'z'], ['b', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], none⟩, ⟨['n'], ['I', 'N', 'F'], some '-'⟩]⟩, ⟨['i', 'z'], ['b', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], [⟨['i', 'z'], ['b', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['e', 's'], ['i', 't'], [⟨['e', 's'], ['i', 't'], none⟩]⟩, ⟨['r', 'e', 'b'], ['M', 'r', '.'], [⟨['r', 'e', 'b'], ['M', 'r', '.'], none⟩]⟩, ⟨['y', 'i', 'x', 'e', 'z', 'k', 'l'], ['Y', 'i', 'k', 'h', 'e', 'z', 'k', 'l', '\'', 's'], [⟨['y', 'i', 'x', 'e', 'z', 'k', 'l'], ['Y', 'i', 'k', 'h', 'e', 'z', 'k', 'l', '\'', 's'], none⟩]⟩, ⟨['g', 'o', 'm', 'b', 'i', 'n', 'e', 'r', 's'], [], []⟩, ⟨['s', 'h', 't', 'u', 'b'], ['h', 'o', 'm', 'e'], [⟨['s', 'h', 't', 'u', 'b'], ['h', 'o', 'm', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "frontingV2"), ("verbType", "lexical"), ("doSupport", "false"), ("frontedForm", "pseudoInfinitive")] }

def ex_80c : Datum :=
  { id := "arregipietraszko2021_80c"
    source := ⟨"davis-prince-1986", "p. 95"⟩
    reportedIn := some ⟨"arregi-pietraszko-2021", "(80c)"⟩
    language := "east2295"
    primaryText := "Bin-en, bin ikh in amerike."
    glossedTokens := [("Bin-en", "be.PRS.1SG-INF"), ("bin", "be.PRS.1SG"), ("ikh", "I"), ("in", "in"), ("amerike", "America")]
    glossedWords := [⟨['B', 'i', 'n', '-', 'e', 'n'], ['b', 'e', '.', 'P', 'R', 'S', '.', '1', 'S', 'G', '-', 'I', 'N', 'F'], [⟨['B', 'i', 'n'], ['b', 'e', '.', 'P', 'R', 'S', '.', '1', 'S', 'G'], none⟩, ⟨['e', 'n'], ['I', 'N', 'F'], some '-'⟩]⟩, ⟨['b', 'i', 'n'], ['b', 'e', '.', 'P', 'R', 'S', '.', '1', 'S', 'G'], [⟨['b', 'i', 'n'], ['b', 'e', '.', 'P', 'R', 'S', '.', '1', 'S', 'G'], none⟩]⟩, ⟨['i', 'k', 'h'], ['I'], [⟨['i', 'k', 'h'], ['I'], none⟩]⟩, ⟨['i', 'n'], ['i', 'n'], [⟨['i', 'n'], ['i', 'n'], none⟩]⟩, ⟨['a', 'm', 'e', 'r', 'i', 'k', 'e'], ['A', 'm', 'e', 'r', 'i', 'c', 'a'], [⟨['a', 'm', 'e', 'r', 'i', 'k', 'e'], ['A', 'm', 'e', 'r', 'i', 'c', 'a'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "frontingV2"), ("verbType", "lexical"), ("doSupport", "false"), ("frontedForm", "pseudoInfinitive")] }

def ex_82 : Datum :=
  { id := "arregipietraszko2021_82"
    source := ⟨"arregi-pietraszko-2021", "(82)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Być w domu, jesteśmy."
    glossedTokens := [("Być", "be-INF"), ("w", "in"), ("domu", "house"), ("jesteśmy", "be.PRS-1PL")]
    glossedWords := [⟨['B', 'y', 'ć'], ['b', 'e', '-', 'I', 'N', 'F'], []⟩, ⟨['w'], ['i', 'n'], [⟨['w'], ['i', 'n'], none⟩]⟩, ⟨['d', 'o', 'm', 'u'], ['h', 'o', 'u', 's', 'e'], [⟨['d', 'o', 'm', 'u'], ['h', 'o', 'u', 's', 'e'], none⟩]⟩, ⟨['j', 'e', 's', 't', 'e', 'ś', 'm', 'y'], ['b', 'e', '.', 'P', 'R', 'S', '-', '1', 'P', 'L'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .marginal
    contrasts := [("Jesteć w domu, jesteśmy.", .ungrammatical)]
    readings := []
    paperFeatures := [("context", "fronting"), ("verbType", "lexical"), ("doSupport", "false"), ("frontedForm", "infinitive")] }

def ex_84 : Datum :=
  { id := "arregipietraszko2021_84"
    source := ⟨"arregi-pietraszko-2021", "(84)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Go, he did."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Went, he did.", .ungrammatical)]
    readings := []
    paperFeatures := [("context", "fronting"), ("verbType", "lexical"), ("doSupport", "true"), ("frontedForm", "bare")] }

def all : List Datum := [ex_6, ex_7, ex_10a, ex_10b, ex_12, ex_13, ex_16, ex_26, ex_27, ex_30, ex_31, ex_33, ex_34, ex_36a, ex_36b, ex_36c, ex_37a, ex_37b, ex_37c, fn38, ex_51, ex_52, ex_53a, ex_53b, ex_54, ex_55, ex_56b, ex_57, ex_61, ex_62, ex_67, ex_70, ex_71, ex_74a, ex_74b, ex_77, ex_80a, ex_80b, ex_80c, ex_82, ex_84]

end ArregiPietraszko2021.Examples
