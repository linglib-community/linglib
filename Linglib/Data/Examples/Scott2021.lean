module

public import Linglib.Data.Examples.Schema

/-!
# `Scott2021` — typed example data

Auto-generated from `Linglib/Data/Examples/Scott2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Scott2021.Examples`.
-/

@[expose] public section

namespace Scott2021.Examples

def cleft_24_mi : Datum :=
  { id := "scott2021_cleft_24_mi"
    source := ⟨"scott-2021", "(24)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "Mimi ndi-ye amba-ye Bahati a-li-pika na-mi."
    glossedTokens := [("Mimi", "1SG"), ("ndi-ye", "COP-1"), ("amba-ye", "AMBA-1"), ("Bahati", "Bahati"), ("a-li-pika", "1-PST-cook"), ("na-mi", "with-1SG")]
    glossedWords := [⟨['M', 'i', 'm', 'i'], ['1', 'S', 'G'], [⟨['M', 'i', 'm', 'i'], ['1', 'S', 'G'], none⟩]⟩, ⟨['n', 'd', 'i', '-', 'y', 'e'], ['C', 'O', 'P', '-', '1'], [⟨['n', 'd', 'i'], ['C', 'O', 'P'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['a', 'm', 'b', 'a', '-', 'y', 'e'], ['A', 'M', 'B', 'A', '-', '1'], [⟨['a', 'm', 'b', 'a'], ['A', 'M', 'B', 'A'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['B', 'a', 'h', 'a', 't', 'i'], ['B', 'a', 'h', 'a', 't', 'i'], [⟨['B', 'a', 'h', 'a', 't', 'i'], ['B', 'a', 'h', 'a', 't', 'i'], none⟩]⟩, ⟨['a', '-', 'l', 'i', '-', 'p', 'i', 'k', 'a'], ['1', '-', 'P', 'S', 'T', '-', 'c', 'o', 'o', 'k'], [⟨['a'], ['1'], none⟩, ⟨['l', 'i'], ['P', 'S', 'T'], some '-'⟩, ⟨['p', 'i', 'k', 'a'], ['c', 'o', 'o', 'k'], some '-'⟩]⟩, ⟨['n', 'a', '-', 'm', 'i'], ['w', 'i', 't', 'h', '-', '1', 'S', 'G'], [⟨['n', 'a'], ['w', 'i', 't', 'h'], none⟩, ⟨['m', 'i'], ['1', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "cleft"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("form", "mi")] }

def cleft_24_ye : Datum :=
  { id := "scott2021_cleft_24_ye"
    source := ⟨"scott-2021", "(24)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "Mimi ndi-ye amba-ye Bahati a-li-pika na-ye."
    glossedTokens := [("Mimi", "1SG"), ("ndi-ye", "COP-1"), ("amba-ye", "AMBA-1"), ("Bahati", "Bahati"), ("a-li-pika", "1-PST-cook"), ("na-ye", "with-1")]
    glossedWords := [⟨['M', 'i', 'm', 'i'], ['1', 'S', 'G'], [⟨['M', 'i', 'm', 'i'], ['1', 'S', 'G'], none⟩]⟩, ⟨['n', 'd', 'i', '-', 'y', 'e'], ['C', 'O', 'P', '-', '1'], [⟨['n', 'd', 'i'], ['C', 'O', 'P'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['a', 'm', 'b', 'a', '-', 'y', 'e'], ['A', 'M', 'B', 'A', '-', '1'], [⟨['a', 'm', 'b', 'a'], ['A', 'M', 'B', 'A'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['B', 'a', 'h', 'a', 't', 'i'], ['B', 'a', 'h', 'a', 't', 'i'], [⟨['B', 'a', 'h', 'a', 't', 'i'], ['B', 'a', 'h', 'a', 't', 'i'], none⟩]⟩, ⟨['a', '-', 'l', 'i', '-', 'p', 'i', 'k', 'a'], ['1', '-', 'P', 'S', 'T', '-', 'c', 'o', 'o', 'k'], [⟨['a'], ['1'], none⟩, ⟨['l', 'i'], ['P', 'S', 'T'], some '-'⟩, ⟨['p', 'i', 'k', 'a'], ['c', 'o', 'o', 'k'], some '-'⟩]⟩, ⟨['n', 'a', '-', 'y', 'e'], ['w', 'i', 't', 'h', '-', '1'], [⟨['n', 'a'], ['w', 'i', 't', 'h'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "cleft"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("form", "ye")] }

def cleft_25_we : Datum :=
  { id := "scott2021_cleft_25_we"
    source := ⟨"scott-2021", "(25)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "Wewe ndi-ye amba-ye Bahati a-li-pika na-we."
    glossedTokens := [("Wewe", "2SG"), ("ndi-ye", "COP-1"), ("amba-ye", "AMBA-1"), ("Bahati", "Bahati"), ("a-li-pika", "1-PST-cook"), ("na-we", "with-2SG")]
    glossedWords := [⟨['W', 'e', 'w', 'e'], ['2', 'S', 'G'], [⟨['W', 'e', 'w', 'e'], ['2', 'S', 'G'], none⟩]⟩, ⟨['n', 'd', 'i', '-', 'y', 'e'], ['C', 'O', 'P', '-', '1'], [⟨['n', 'd', 'i'], ['C', 'O', 'P'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['a', 'm', 'b', 'a', '-', 'y', 'e'], ['A', 'M', 'B', 'A', '-', '1'], [⟨['a', 'm', 'b', 'a'], ['A', 'M', 'B', 'A'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['B', 'a', 'h', 'a', 't', 'i'], ['B', 'a', 'h', 'a', 't', 'i'], [⟨['B', 'a', 'h', 'a', 't', 'i'], ['B', 'a', 'h', 'a', 't', 'i'], none⟩]⟩, ⟨['a', '-', 'l', 'i', '-', 'p', 'i', 'k', 'a'], ['1', '-', 'P', 'S', 'T', '-', 'c', 'o', 'o', 'k'], [⟨['a'], ['1'], none⟩, ⟨['l', 'i'], ['P', 'S', 'T'], some '-'⟩, ⟨['p', 'i', 'k', 'a'], ['c', 'o', 'o', 'k'], some '-'⟩]⟩, ⟨['n', 'a', '-', 'w', 'e'], ['w', 'i', 't', 'h', '-', '2', 'S', 'G'], [⟨['n', 'a'], ['w', 'i', 't', 'h'], none⟩, ⟨['w', 'e'], ['2', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "cleft"), ("antecedentPerson", "2"), ("antecedentNumber", "sg"), ("form", "we")] }

def cleft_25_ye : Datum :=
  { id := "scott2021_cleft_25_ye"
    source := ⟨"scott-2021", "(25)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "Wewe ndi-ye amba-ye Bahati a-li-pika na-ye."
    glossedTokens := [("Wewe", "2SG"), ("ndi-ye", "COP-1"), ("amba-ye", "AMBA-1"), ("Bahati", "Bahati"), ("a-li-pika", "1-PST-cook"), ("na-ye", "with-1")]
    glossedWords := [⟨['W', 'e', 'w', 'e'], ['2', 'S', 'G'], [⟨['W', 'e', 'w', 'e'], ['2', 'S', 'G'], none⟩]⟩, ⟨['n', 'd', 'i', '-', 'y', 'e'], ['C', 'O', 'P', '-', '1'], [⟨['n', 'd', 'i'], ['C', 'O', 'P'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['a', 'm', 'b', 'a', '-', 'y', 'e'], ['A', 'M', 'B', 'A', '-', '1'], [⟨['a', 'm', 'b', 'a'], ['A', 'M', 'B', 'A'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['B', 'a', 'h', 'a', 't', 'i'], ['B', 'a', 'h', 'a', 't', 'i'], [⟨['B', 'a', 'h', 'a', 't', 'i'], ['B', 'a', 'h', 'a', 't', 'i'], none⟩]⟩, ⟨['a', '-', 'l', 'i', '-', 'p', 'i', 'k', 'a'], ['1', '-', 'P', 'S', 'T', '-', 'c', 'o', 'o', 'k'], [⟨['a'], ['1'], none⟩, ⟨['l', 'i'], ['P', 'S', 'T'], some '-'⟩, ⟨['p', 'i', 'k', 'a'], ['c', 'o', 'o', 'k'], some '-'⟩]⟩, ⟨['n', 'a', '-', 'y', 'e'], ['w', 'i', 't', 'h', '-', '1'], [⟨['n', 'a'], ['w', 'i', 't', 'h'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "cleft"), ("antecedentPerson", "2"), ("antecedentNumber", "sg"), ("form", "ye")] }

def cleft_29a_si : Datum :=
  { id := "scott2021_cleft_29a_si"
    source := ⟨"scott-2021", "(29a)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "Mimi ndi-ye amba-ye Hadija a-li-kutana na-si."
    glossedTokens := [("Mimi", "1SG"), ("ndi-ye", "COP-1"), ("amba-ye", "AMBA-1"), ("Hadija", "Hadija"), ("a-li-kutana", "1-PST-meet"), ("na-si", "with-1PL")]
    glossedWords := [⟨['M', 'i', 'm', 'i'], ['1', 'S', 'G'], [⟨['M', 'i', 'm', 'i'], ['1', 'S', 'G'], none⟩]⟩, ⟨['n', 'd', 'i', '-', 'y', 'e'], ['C', 'O', 'P', '-', '1'], [⟨['n', 'd', 'i'], ['C', 'O', 'P'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['a', 'm', 'b', 'a', '-', 'y', 'e'], ['A', 'M', 'B', 'A', '-', '1'], [⟨['a', 'm', 'b', 'a'], ['A', 'M', 'B', 'A'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['H', 'a', 'd', 'i', 'j', 'a'], ['H', 'a', 'd', 'i', 'j', 'a'], [⟨['H', 'a', 'd', 'i', 'j', 'a'], ['H', 'a', 'd', 'i', 'j', 'a'], none⟩]⟩, ⟨['a', '-', 'l', 'i', '-', 'k', 'u', 't', 'a', 'n', 'a'], ['1', '-', 'P', 'S', 'T', '-', 'm', 'e', 'e', 't'], [⟨['a'], ['1'], none⟩, ⟨['l', 'i'], ['P', 'S', 'T'], some '-'⟩, ⟨['k', 'u', 't', 'a', 'n', 'a'], ['m', 'e', 'e', 't'], some '-'⟩]⟩, ⟨['n', 'a', '-', 's', 'i'], ['w', 'i', 't', 'h', '-', '1', 'P', 'L'], [⟨['n', 'a'], ['w', 'i', 't', 'h'], none⟩, ⟨['s', 'i'], ['1', 'P', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("construction", "cleft"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("form", "si")] }

def cleft_29a_o : Datum :=
  { id := "scott2021_cleft_29a_o"
    source := ⟨"scott-2021", "(29a)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "Mimi ndi-ye amba-ye Hadija a-li-kutana na-o."
    glossedTokens := [("Mimi", "1SG"), ("ndi-ye", "COP-1"), ("amba-ye", "AMBA-1"), ("Hadija", "Hadija"), ("a-li-kutana", "1-PST-meet"), ("na-o", "with-2")]
    glossedWords := [⟨['M', 'i', 'm', 'i'], ['1', 'S', 'G'], [⟨['M', 'i', 'm', 'i'], ['1', 'S', 'G'], none⟩]⟩, ⟨['n', 'd', 'i', '-', 'y', 'e'], ['C', 'O', 'P', '-', '1'], [⟨['n', 'd', 'i'], ['C', 'O', 'P'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['a', 'm', 'b', 'a', '-', 'y', 'e'], ['A', 'M', 'B', 'A', '-', '1'], [⟨['a', 'm', 'b', 'a'], ['A', 'M', 'B', 'A'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['H', 'a', 'd', 'i', 'j', 'a'], ['H', 'a', 'd', 'i', 'j', 'a'], [⟨['H', 'a', 'd', 'i', 'j', 'a'], ['H', 'a', 'd', 'i', 'j', 'a'], none⟩]⟩, ⟨['a', '-', 'l', 'i', '-', 'k', 'u', 't', 'a', 'n', 'a'], ['1', '-', 'P', 'S', 'T', '-', 'm', 'e', 'e', 't'], [⟨['a'], ['1'], none⟩, ⟨['l', 'i'], ['P', 'S', 'T'], some '-'⟩, ⟨['k', 'u', 't', 'a', 'n', 'a'], ['m', 'e', 'e', 't'], some '-'⟩]⟩, ⟨['n', 'a', '-', 'o'], ['w', 'i', 't', 'h', '-', '2'], [⟨['n', 'a'], ['w', 'i', 't', 'h'], none⟩, ⟨['o'], ['2'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("construction", "cleft"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("form", "o")] }

def cleft_29b_nyi : Datum :=
  { id := "scott2021_cleft_29b_nyi"
    source := ⟨"scott-2021", "(29b)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "Wewe ndi-ye amba-ye Hadija a-li-kutana na-nyi."
    glossedTokens := [("Wewe", "2SG"), ("ndi-ye", "COP-1"), ("amba-ye", "AMBA-1"), ("Hadija", "Hadija"), ("a-li-kutana", "1-PST-meet"), ("na-nyi", "with-2PL")]
    glossedWords := [⟨['W', 'e', 'w', 'e'], ['2', 'S', 'G'], [⟨['W', 'e', 'w', 'e'], ['2', 'S', 'G'], none⟩]⟩, ⟨['n', 'd', 'i', '-', 'y', 'e'], ['C', 'O', 'P', '-', '1'], [⟨['n', 'd', 'i'], ['C', 'O', 'P'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['a', 'm', 'b', 'a', '-', 'y', 'e'], ['A', 'M', 'B', 'A', '-', '1'], [⟨['a', 'm', 'b', 'a'], ['A', 'M', 'B', 'A'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['H', 'a', 'd', 'i', 'j', 'a'], ['H', 'a', 'd', 'i', 'j', 'a'], [⟨['H', 'a', 'd', 'i', 'j', 'a'], ['H', 'a', 'd', 'i', 'j', 'a'], none⟩]⟩, ⟨['a', '-', 'l', 'i', '-', 'k', 'u', 't', 'a', 'n', 'a'], ['1', '-', 'P', 'S', 'T', '-', 'm', 'e', 'e', 't'], [⟨['a'], ['1'], none⟩, ⟨['l', 'i'], ['P', 'S', 'T'], some '-'⟩, ⟨['k', 'u', 't', 'a', 'n', 'a'], ['m', 'e', 'e', 't'], some '-'⟩]⟩, ⟨['n', 'a', '-', 'n', 'y', 'i'], ['w', 'i', 't', 'h', '-', '2', 'P', 'L'], [⟨['n', 'a'], ['w', 'i', 't', 'h'], none⟩, ⟨['n', 'y', 'i'], ['2', 'P', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("construction", "cleft"), ("antecedentPerson", "2"), ("antecedentNumber", "sg"), ("form", "nyi")] }

def cleft_29b_o : Datum :=
  { id := "scott2021_cleft_29b_o"
    source := ⟨"scott-2021", "(29b)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "Wewe ndi-ye amba-ye Hadija a-li-kutana na-o."
    glossedTokens := [("Wewe", "2SG"), ("ndi-ye", "COP-1"), ("amba-ye", "AMBA-1"), ("Hadija", "Hadija"), ("a-li-kutana", "1-PST-meet"), ("na-o", "with-2")]
    glossedWords := [⟨['W', 'e', 'w', 'e'], ['2', 'S', 'G'], [⟨['W', 'e', 'w', 'e'], ['2', 'S', 'G'], none⟩]⟩, ⟨['n', 'd', 'i', '-', 'y', 'e'], ['C', 'O', 'P', '-', '1'], [⟨['n', 'd', 'i'], ['C', 'O', 'P'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['a', 'm', 'b', 'a', '-', 'y', 'e'], ['A', 'M', 'B', 'A', '-', '1'], [⟨['a', 'm', 'b', 'a'], ['A', 'M', 'B', 'A'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['H', 'a', 'd', 'i', 'j', 'a'], ['H', 'a', 'd', 'i', 'j', 'a'], [⟨['H', 'a', 'd', 'i', 'j', 'a'], ['H', 'a', 'd', 'i', 'j', 'a'], none⟩]⟩, ⟨['a', '-', 'l', 'i', '-', 'k', 'u', 't', 'a', 'n', 'a'], ['1', '-', 'P', 'S', 'T', '-', 'm', 'e', 'e', 't'], [⟨['a'], ['1'], none⟩, ⟨['l', 'i'], ['P', 'S', 'T'], some '-'⟩, ⟨['k', 'u', 't', 'a', 'n', 'a'], ['m', 'e', 'e', 't'], some '-'⟩]⟩, ⟨['n', 'a', '-', 'o'], ['w', 'i', 't', 'h', '-', '2'], [⟨['n', 'a'], ['w', 'i', 't', 'h'], none⟩, ⟨['o'], ['2'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("construction", "cleft"), ("antecedentPerson", "2"), ("antecedentNumber", "sg"), ("form", "o")] }

def island_31_we : Datum :=
  { id := "scott2021_island_31_we"
    source := ⟨"scott-2021", "(31)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "Wewe ndi-ye amba-ye ni-li-hama kwa sababu ni-li-ach-ana na-we."
    glossedTokens := [("Wewe", "2SG"), ("ndi-ye", "COP-1"), ("amba-ye", "AMBA-1"), ("ni-li-hama", "1SG-PST-move"), ("kwa", "for"), ("sababu", "reason"), ("ni-li-ach-ana", "1SG-PST-leave-RECP"), ("na-we", "with-2SG")]
    glossedWords := [⟨['W', 'e', 'w', 'e'], ['2', 'S', 'G'], [⟨['W', 'e', 'w', 'e'], ['2', 'S', 'G'], none⟩]⟩, ⟨['n', 'd', 'i', '-', 'y', 'e'], ['C', 'O', 'P', '-', '1'], [⟨['n', 'd', 'i'], ['C', 'O', 'P'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['a', 'm', 'b', 'a', '-', 'y', 'e'], ['A', 'M', 'B', 'A', '-', '1'], [⟨['a', 'm', 'b', 'a'], ['A', 'M', 'B', 'A'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['n', 'i', '-', 'l', 'i', '-', 'h', 'a', 'm', 'a'], ['1', 'S', 'G', '-', 'P', 'S', 'T', '-', 'm', 'o', 'v', 'e'], [⟨['n', 'i'], ['1', 'S', 'G'], none⟩, ⟨['l', 'i'], ['P', 'S', 'T'], some '-'⟩, ⟨['h', 'a', 'm', 'a'], ['m', 'o', 'v', 'e'], some '-'⟩]⟩, ⟨['k', 'w', 'a'], ['f', 'o', 'r'], [⟨['k', 'w', 'a'], ['f', 'o', 'r'], none⟩]⟩, ⟨['s', 'a', 'b', 'a', 'b', 'u'], ['r', 'e', 'a', 's', 'o', 'n'], [⟨['s', 'a', 'b', 'a', 'b', 'u'], ['r', 'e', 'a', 's', 'o', 'n'], none⟩]⟩, ⟨['n', 'i', '-', 'l', 'i', '-', 'a', 'c', 'h', '-', 'a', 'n', 'a'], ['1', 'S', 'G', '-', 'P', 'S', 'T', '-', 'l', 'e', 'a', 'v', 'e', '-', 'R', 'E', 'C', 'P'], [⟨['n', 'i'], ['1', 'S', 'G'], none⟩, ⟨['l', 'i'], ['P', 'S', 'T'], some '-'⟩, ⟨['a', 'c', 'h'], ['l', 'e', 'a', 'v', 'e'], some '-'⟩, ⟨['a', 'n', 'a'], ['R', 'E', 'C', 'P'], some '-'⟩]⟩, ⟨['n', 'a', '-', 'w', 'e'], ['w', 'i', 't', 'h', '-', '2', 'S', 'G'], [⟨['n', 'a'], ['w', 'i', 't', 'h'], none⟩, ⟨['w', 'e'], ['2', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "island"), ("antecedentPerson", "2"), ("antecedentNumber", "sg"), ("form", "we")] }

def island_31_ye : Datum :=
  { id := "scott2021_island_31_ye"
    source := ⟨"scott-2021", "(31)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "Wewe ndi-ye amba-ye ni-li-hama kwa sababu ni-li-ach-ana na-ye."
    glossedTokens := [("Wewe", "2SG"), ("ndi-ye", "COP-1"), ("amba-ye", "AMBA-1"), ("ni-li-hama", "1SG-PST-move"), ("kwa", "for"), ("sababu", "reason"), ("ni-li-ach-ana", "1SG-PST-leave-RECP"), ("na-ye", "with-1")]
    glossedWords := [⟨['W', 'e', 'w', 'e'], ['2', 'S', 'G'], [⟨['W', 'e', 'w', 'e'], ['2', 'S', 'G'], none⟩]⟩, ⟨['n', 'd', 'i', '-', 'y', 'e'], ['C', 'O', 'P', '-', '1'], [⟨['n', 'd', 'i'], ['C', 'O', 'P'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['a', 'm', 'b', 'a', '-', 'y', 'e'], ['A', 'M', 'B', 'A', '-', '1'], [⟨['a', 'm', 'b', 'a'], ['A', 'M', 'B', 'A'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['n', 'i', '-', 'l', 'i', '-', 'h', 'a', 'm', 'a'], ['1', 'S', 'G', '-', 'P', 'S', 'T', '-', 'm', 'o', 'v', 'e'], [⟨['n', 'i'], ['1', 'S', 'G'], none⟩, ⟨['l', 'i'], ['P', 'S', 'T'], some '-'⟩, ⟨['h', 'a', 'm', 'a'], ['m', 'o', 'v', 'e'], some '-'⟩]⟩, ⟨['k', 'w', 'a'], ['f', 'o', 'r'], [⟨['k', 'w', 'a'], ['f', 'o', 'r'], none⟩]⟩, ⟨['s', 'a', 'b', 'a', 'b', 'u'], ['r', 'e', 'a', 's', 'o', 'n'], [⟨['s', 'a', 'b', 'a', 'b', 'u'], ['r', 'e', 'a', 's', 'o', 'n'], none⟩]⟩, ⟨['n', 'i', '-', 'l', 'i', '-', 'a', 'c', 'h', '-', 'a', 'n', 'a'], ['1', 'S', 'G', '-', 'P', 'S', 'T', '-', 'l', 'e', 'a', 'v', 'e', '-', 'R', 'E', 'C', 'P'], [⟨['n', 'i'], ['1', 'S', 'G'], none⟩, ⟨['l', 'i'], ['P', 'S', 'T'], some '-'⟩, ⟨['a', 'c', 'h'], ['l', 'e', 'a', 'v', 'e'], some '-'⟩, ⟨['a', 'n', 'a'], ['R', 'E', 'C', 'P'], some '-'⟩]⟩, ⟨['n', 'a', '-', 'y', 'e'], ['w', 'i', 't', 'h', '-', '1'], [⟨['n', 'a'], ['w', 'i', 't', 'h'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("construction", "island"), ("antecedentPerson", "2"), ("antecedentNumber", "sg"), ("form", "ye")] }

def island_32_mi : Datum :=
  { id := "scott2021_island_32_mi"
    source := ⟨"scott-2021", "(32)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "Mimi ndi-ye amba-ye Nadya a-li-anguka a-li-po-cheza na-mi."
    glossedTokens := [("Mimi", "1SG"), ("ndi-ye", "COP-1"), ("amba-ye", "AMBA-1"), ("Nadya", "Nadya"), ("a-li-anguka", "1-PST-fall"), ("a-li-po-cheza", "1-PST-16-play"), ("na-mi", "with-1SG")]
    glossedWords := [⟨['M', 'i', 'm', 'i'], ['1', 'S', 'G'], [⟨['M', 'i', 'm', 'i'], ['1', 'S', 'G'], none⟩]⟩, ⟨['n', 'd', 'i', '-', 'y', 'e'], ['C', 'O', 'P', '-', '1'], [⟨['n', 'd', 'i'], ['C', 'O', 'P'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['a', 'm', 'b', 'a', '-', 'y', 'e'], ['A', 'M', 'B', 'A', '-', '1'], [⟨['a', 'm', 'b', 'a'], ['A', 'M', 'B', 'A'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['N', 'a', 'd', 'y', 'a'], ['N', 'a', 'd', 'y', 'a'], [⟨['N', 'a', 'd', 'y', 'a'], ['N', 'a', 'd', 'y', 'a'], none⟩]⟩, ⟨['a', '-', 'l', 'i', '-', 'a', 'n', 'g', 'u', 'k', 'a'], ['1', '-', 'P', 'S', 'T', '-', 'f', 'a', 'l', 'l'], [⟨['a'], ['1'], none⟩, ⟨['l', 'i'], ['P', 'S', 'T'], some '-'⟩, ⟨['a', 'n', 'g', 'u', 'k', 'a'], ['f', 'a', 'l', 'l'], some '-'⟩]⟩, ⟨['a', '-', 'l', 'i', '-', 'p', 'o', '-', 'c', 'h', 'e', 'z', 'a'], ['1', '-', 'P', 'S', 'T', '-', '1', '6', '-', 'p', 'l', 'a', 'y'], [⟨['a'], ['1'], none⟩, ⟨['l', 'i'], ['P', 'S', 'T'], some '-'⟩, ⟨['p', 'o'], ['1', '6'], some '-'⟩, ⟨['c', 'h', 'e', 'z', 'a'], ['p', 'l', 'a', 'y'], some '-'⟩]⟩, ⟨['n', 'a', '-', 'm', 'i'], ['w', 'i', 't', 'h', '-', '1', 'S', 'G'], [⟨['n', 'a'], ['w', 'i', 't', 'h'], none⟩, ⟨['m', 'i'], ['1', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "island"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("form", "mi")] }

def island_32_ye : Datum :=
  { id := "scott2021_island_32_ye"
    source := ⟨"scott-2021", "(32)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "Mimi ndi-ye amba-ye Nadya a-li-anguka a-li-po-cheza na-ye."
    glossedTokens := [("Mimi", "1SG"), ("ndi-ye", "COP-1"), ("amba-ye", "AMBA-1"), ("Nadya", "Nadya"), ("a-li-anguka", "1-PST-fall"), ("a-li-po-cheza", "1-PST-16-play"), ("na-ye", "with-1")]
    glossedWords := [⟨['M', 'i', 'm', 'i'], ['1', 'S', 'G'], [⟨['M', 'i', 'm', 'i'], ['1', 'S', 'G'], none⟩]⟩, ⟨['n', 'd', 'i', '-', 'y', 'e'], ['C', 'O', 'P', '-', '1'], [⟨['n', 'd', 'i'], ['C', 'O', 'P'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['a', 'm', 'b', 'a', '-', 'y', 'e'], ['A', 'M', 'B', 'A', '-', '1'], [⟨['a', 'm', 'b', 'a'], ['A', 'M', 'B', 'A'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['N', 'a', 'd', 'y', 'a'], ['N', 'a', 'd', 'y', 'a'], [⟨['N', 'a', 'd', 'y', 'a'], ['N', 'a', 'd', 'y', 'a'], none⟩]⟩, ⟨['a', '-', 'l', 'i', '-', 'a', 'n', 'g', 'u', 'k', 'a'], ['1', '-', 'P', 'S', 'T', '-', 'f', 'a', 'l', 'l'], [⟨['a'], ['1'], none⟩, ⟨['l', 'i'], ['P', 'S', 'T'], some '-'⟩, ⟨['a', 'n', 'g', 'u', 'k', 'a'], ['f', 'a', 'l', 'l'], some '-'⟩]⟩, ⟨['a', '-', 'l', 'i', '-', 'p', 'o', '-', 'c', 'h', 'e', 'z', 'a'], ['1', '-', 'P', 'S', 'T', '-', '1', '6', '-', 'p', 'l', 'a', 'y'], [⟨['a'], ['1'], none⟩, ⟨['l', 'i'], ['P', 'S', 'T'], some '-'⟩, ⟨['p', 'o'], ['1', '6'], some '-'⟩, ⟨['c', 'h', 'e', 'z', 'a'], ['p', 'l', 'a', 'y'], some '-'⟩]⟩, ⟨['n', 'a', '-', 'y', 'e'], ['w', 'i', 't', 'h', '-', '1'], [⟨['n', 'a'], ['w', 'i', 't', 'h'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("construction", "island"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("form", "ye")] }

def island_33_mi : Datum :=
  { id := "scott2021_island_33_mi"
    source := ⟨"scott-2021", "(33)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "Mimi ndi-ye amba-ye u-li-tabasamu wakati u-na-fanya kazi na-mi."
    glossedTokens := [("Mimi", "1SG"), ("ndi-ye", "COP-1"), ("amba-ye", "AMBA-1"), ("u-li-tabasamu", "2SG-PST-smile"), ("wakati", "while"), ("u-na-fanya", "2SG-PST-do"), ("kazi", "work"), ("na-mi", "with-1SG")]
    glossedWords := [⟨['M', 'i', 'm', 'i'], ['1', 'S', 'G'], [⟨['M', 'i', 'm', 'i'], ['1', 'S', 'G'], none⟩]⟩, ⟨['n', 'd', 'i', '-', 'y', 'e'], ['C', 'O', 'P', '-', '1'], [⟨['n', 'd', 'i'], ['C', 'O', 'P'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['a', 'm', 'b', 'a', '-', 'y', 'e'], ['A', 'M', 'B', 'A', '-', '1'], [⟨['a', 'm', 'b', 'a'], ['A', 'M', 'B', 'A'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['u', '-', 'l', 'i', '-', 't', 'a', 'b', 'a', 's', 'a', 'm', 'u'], ['2', 'S', 'G', '-', 'P', 'S', 'T', '-', 's', 'm', 'i', 'l', 'e'], [⟨['u'], ['2', 'S', 'G'], none⟩, ⟨['l', 'i'], ['P', 'S', 'T'], some '-'⟩, ⟨['t', 'a', 'b', 'a', 's', 'a', 'm', 'u'], ['s', 'm', 'i', 'l', 'e'], some '-'⟩]⟩, ⟨['w', 'a', 'k', 'a', 't', 'i'], ['w', 'h', 'i', 'l', 'e'], [⟨['w', 'a', 'k', 'a', 't', 'i'], ['w', 'h', 'i', 'l', 'e'], none⟩]⟩, ⟨['u', '-', 'n', 'a', '-', 'f', 'a', 'n', 'y', 'a'], ['2', 'S', 'G', '-', 'P', 'S', 'T', '-', 'd', 'o'], [⟨['u'], ['2', 'S', 'G'], none⟩, ⟨['n', 'a'], ['P', 'S', 'T'], some '-'⟩, ⟨['f', 'a', 'n', 'y', 'a'], ['d', 'o'], some '-'⟩]⟩, ⟨['k', 'a', 'z', 'i'], ['w', 'o', 'r', 'k'], [⟨['k', 'a', 'z', 'i'], ['w', 'o', 'r', 'k'], none⟩]⟩, ⟨['n', 'a', '-', 'm', 'i'], ['w', 'i', 't', 'h', '-', '1', 'S', 'G'], [⟨['n', 'a'], ['w', 'i', 't', 'h'], none⟩, ⟨['m', 'i'], ['1', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "island"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("form", "mi")] }

def island_33_ye : Datum :=
  { id := "scott2021_island_33_ye"
    source := ⟨"scott-2021", "(33)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "Mimi ndi-ye amba-ye u-li-tabasamu wakati u-na-fanya kazi na-ye."
    glossedTokens := [("Mimi", "1SG"), ("ndi-ye", "COP-1"), ("amba-ye", "AMBA-1"), ("u-li-tabasamu", "2SG-PST-smile"), ("wakati", "while"), ("u-na-fanya", "2SG-PST-do"), ("kazi", "work"), ("na-ye", "with-1")]
    glossedWords := [⟨['M', 'i', 'm', 'i'], ['1', 'S', 'G'], [⟨['M', 'i', 'm', 'i'], ['1', 'S', 'G'], none⟩]⟩, ⟨['n', 'd', 'i', '-', 'y', 'e'], ['C', 'O', 'P', '-', '1'], [⟨['n', 'd', 'i'], ['C', 'O', 'P'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['a', 'm', 'b', 'a', '-', 'y', 'e'], ['A', 'M', 'B', 'A', '-', '1'], [⟨['a', 'm', 'b', 'a'], ['A', 'M', 'B', 'A'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['u', '-', 'l', 'i', '-', 't', 'a', 'b', 'a', 's', 'a', 'm', 'u'], ['2', 'S', 'G', '-', 'P', 'S', 'T', '-', 's', 'm', 'i', 'l', 'e'], [⟨['u'], ['2', 'S', 'G'], none⟩, ⟨['l', 'i'], ['P', 'S', 'T'], some '-'⟩, ⟨['t', 'a', 'b', 'a', 's', 'a', 'm', 'u'], ['s', 'm', 'i', 'l', 'e'], some '-'⟩]⟩, ⟨['w', 'a', 'k', 'a', 't', 'i'], ['w', 'h', 'i', 'l', 'e'], [⟨['w', 'a', 'k', 'a', 't', 'i'], ['w', 'h', 'i', 'l', 'e'], none⟩]⟩, ⟨['u', '-', 'n', 'a', '-', 'f', 'a', 'n', 'y', 'a'], ['2', 'S', 'G', '-', 'P', 'S', 'T', '-', 'd', 'o'], [⟨['u'], ['2', 'S', 'G'], none⟩, ⟨['n', 'a'], ['P', 'S', 'T'], some '-'⟩, ⟨['f', 'a', 'n', 'y', 'a'], ['d', 'o'], some '-'⟩]⟩, ⟨['k', 'a', 'z', 'i'], ['w', 'o', 'r', 'k'], [⟨['k', 'a', 'z', 'i'], ['w', 'o', 'r', 'k'], none⟩]⟩, ⟨['n', 'a', '-', 'y', 'e'], ['w', 'i', 't', 'h', '-', '1'], [⟨['n', 'a'], ['w', 'i', 't', 'h'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("construction", "island"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("form", "ye")] }

def pg_36 : Datum :=
  { id := "scott2021_pg_36"
    source := ⟨"scott-2021", "(36)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "Mimi ndi-ye amba-ye u-li-pika na-ye kabla ya ku-ondoka na-ye."
    glossedTokens := [("Mimi", "1SG"), ("ndi-ye", "COP-1"), ("amba-ye", "AMBA-1"), ("u-li-pika", "2SG-PST-cook"), ("na-ye", "with-1"), ("kabla", "before"), ("ya", "of"), ("ku-ondoka", "15-leave"), ("na-ye", "with-1")]
    glossedWords := [⟨['M', 'i', 'm', 'i'], ['1', 'S', 'G'], [⟨['M', 'i', 'm', 'i'], ['1', 'S', 'G'], none⟩]⟩, ⟨['n', 'd', 'i', '-', 'y', 'e'], ['C', 'O', 'P', '-', '1'], [⟨['n', 'd', 'i'], ['C', 'O', 'P'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['a', 'm', 'b', 'a', '-', 'y', 'e'], ['A', 'M', 'B', 'A', '-', '1'], [⟨['a', 'm', 'b', 'a'], ['A', 'M', 'B', 'A'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['u', '-', 'l', 'i', '-', 'p', 'i', 'k', 'a'], ['2', 'S', 'G', '-', 'P', 'S', 'T', '-', 'c', 'o', 'o', 'k'], [⟨['u'], ['2', 'S', 'G'], none⟩, ⟨['l', 'i'], ['P', 'S', 'T'], some '-'⟩, ⟨['p', 'i', 'k', 'a'], ['c', 'o', 'o', 'k'], some '-'⟩]⟩, ⟨['n', 'a', '-', 'y', 'e'], ['w', 'i', 't', 'h', '-', '1'], [⟨['n', 'a'], ['w', 'i', 't', 'h'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['k', 'a', 'b', 'l', 'a'], ['b', 'e', 'f', 'o', 'r', 'e'], [⟨['k', 'a', 'b', 'l', 'a'], ['b', 'e', 'f', 'o', 'r', 'e'], none⟩]⟩, ⟨['y', 'a'], ['o', 'f'], [⟨['y', 'a'], ['o', 'f'], none⟩]⟩, ⟨['k', 'u', '-', 'o', 'n', 'd', 'o', 'k', 'a'], ['1', '5', '-', 'l', 'e', 'a', 'v', 'e'], [⟨['k', 'u'], ['1', '5'], none⟩, ⟨['o', 'n', 'd', 'o', 'k', 'a'], ['l', 'e', 'a', 'v', 'e'], some '-'⟩]⟩, ⟨['n', 'a', '-', 'y', 'e'], ['w', 'i', 't', 'h', '-', '1'], [⟨['n', 'a'], ['w', 'i', 't', 'h'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "parasiticGap"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("trueGap", "ye"), ("parasitic", "ye")] }

def pg_37 : Datum :=
  { id := "scott2021_pg_37"
    source := ⟨"scott-2021", "(37)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "Mimi ndi-ye amba-ye u-li-pika na-mi kabla ya ku-cheza na-ye."
    glossedTokens := [("Mimi", "1SG"), ("ndi-ye", "COP-1"), ("amba-ye", "AMBA-1"), ("u-li-pika", "2SG-PST-cook"), ("na-mi", "with-1SG"), ("kabla", "before"), ("ya", "of"), ("ku-cheza", "15-dance"), ("na-ye", "with-1")]
    glossedWords := [⟨['M', 'i', 'm', 'i'], ['1', 'S', 'G'], [⟨['M', 'i', 'm', 'i'], ['1', 'S', 'G'], none⟩]⟩, ⟨['n', 'd', 'i', '-', 'y', 'e'], ['C', 'O', 'P', '-', '1'], [⟨['n', 'd', 'i'], ['C', 'O', 'P'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['a', 'm', 'b', 'a', '-', 'y', 'e'], ['A', 'M', 'B', 'A', '-', '1'], [⟨['a', 'm', 'b', 'a'], ['A', 'M', 'B', 'A'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩, ⟨['u', '-', 'l', 'i', '-', 'p', 'i', 'k', 'a'], ['2', 'S', 'G', '-', 'P', 'S', 'T', '-', 'c', 'o', 'o', 'k'], [⟨['u'], ['2', 'S', 'G'], none⟩, ⟨['l', 'i'], ['P', 'S', 'T'], some '-'⟩, ⟨['p', 'i', 'k', 'a'], ['c', 'o', 'o', 'k'], some '-'⟩]⟩, ⟨['n', 'a', '-', 'm', 'i'], ['w', 'i', 't', 'h', '-', '1', 'S', 'G'], [⟨['n', 'a'], ['w', 'i', 't', 'h'], none⟩, ⟨['m', 'i'], ['1', 'S', 'G'], some '-'⟩]⟩, ⟨['k', 'a', 'b', 'l', 'a'], ['b', 'e', 'f', 'o', 'r', 'e'], [⟨['k', 'a', 'b', 'l', 'a'], ['b', 'e', 'f', 'o', 'r', 'e'], none⟩]⟩, ⟨['y', 'a'], ['o', 'f'], [⟨['y', 'a'], ['o', 'f'], none⟩]⟩, ⟨['k', 'u', '-', 'c', 'h', 'e', 'z', 'a'], ['1', '5', '-', 'd', 'a', 'n', 'c', 'e'], [⟨['k', 'u'], ['1', '5'], none⟩, ⟨['c', 'h', 'e', 'z', 'a'], ['d', 'a', 'n', 'c', 'e'], some '-'⟩]⟩, ⟨['n', 'a', '-', 'y', 'e'], ['w', 'i', 't', 'h', '-', '1'], [⟨['n', 'a'], ['w', 'i', 't', 'h'], none⟩, ⟨['y', 'e'], ['1'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "parasiticGap"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("trueGap", "mi"), ("parasitic", "ye")] }

def table4_sp1_ye_ye : Datum :=
  { id := "scott2021_table4_sp1_ye_ye"
    source := ⟨"scott-2021", "Table 4"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "… na-ye … na-ye"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "parasiticGap"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("trueGap", "ye"), ("parasitic", "ye"), ("speaker", "1")] }

def table4_sp1_mi_ye : Datum :=
  { id := "scott2021_table4_sp1_mi_ye"
    source := ⟨"scott-2021", "Table 4"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "… na-mi … na-ye"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("construction", "parasiticGap"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("trueGap", "mi"), ("parasitic", "ye"), ("speaker", "1")] }

def table4_sp1_mi_mi : Datum :=
  { id := "scott2021_table4_sp1_mi_mi"
    source := ⟨"scott-2021", "Table 4"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "… na-mi … na-mi"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("construction", "parasiticGap"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("trueGap", "mi"), ("parasitic", "mi"), ("speaker", "1")] }

def table4_sp1_ye_mi : Datum :=
  { id := "scott2021_table4_sp1_ye_mi"
    source := ⟨"scott-2021", "Table 4"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "… na-ye … na-mi"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("construction", "parasiticGap"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("trueGap", "ye"), ("parasitic", "mi"), ("speaker", "1")] }

def table4_sp2_ye_ye : Datum :=
  { id := "scott2021_table4_sp2_ye_ye"
    source := ⟨"scott-2021", "Table 4"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "… na-ye … na-ye"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "parasiticGap"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("trueGap", "ye"), ("parasitic", "ye"), ("speaker", "2")] }

def table4_sp2_mi_ye : Datum :=
  { id := "scott2021_table4_sp2_mi_ye"
    source := ⟨"scott-2021", "Table 4"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "… na-mi … na-ye"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("construction", "parasiticGap"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("trueGap", "mi"), ("parasitic", "ye"), ("speaker", "2")] }

def table4_sp2_mi_mi : Datum :=
  { id := "scott2021_table4_sp2_mi_mi"
    source := ⟨"scott-2021", "Table 4"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "… na-mi … na-mi"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "parasiticGap"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("trueGap", "mi"), ("parasitic", "mi"), ("speaker", "2")] }

def table4_sp2_ye_mi : Datum :=
  { id := "scott2021_table4_sp2_ye_mi"
    source := ⟨"scott-2021", "Table 4"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "… na-ye … na-mi"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "parasiticGap"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("trueGap", "ye"), ("parasitic", "mi"), ("speaker", "2")] }

def table4_sp3_ye_ye : Datum :=
  { id := "scott2021_table4_sp3_ye_ye"
    source := ⟨"scott-2021", "Table 4"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "… na-ye … na-ye"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "parasiticGap"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("trueGap", "ye"), ("parasitic", "ye"), ("speaker", "3")] }

def table4_sp3_mi_ye : Datum :=
  { id := "scott2021_table4_sp3_mi_ye"
    source := ⟨"scott-2021", "Table 4"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "… na-mi … na-ye"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("construction", "parasiticGap"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("trueGap", "mi"), ("parasitic", "ye"), ("speaker", "3")] }

def table4_sp3_mi_mi : Datum :=
  { id := "scott2021_table4_sp3_mi_mi"
    source := ⟨"scott-2021", "Table 4"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "… na-mi … na-mi"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "parasiticGap"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("trueGap", "mi"), ("parasitic", "mi"), ("speaker", "3")] }

def table4_sp3_ye_mi : Datum :=
  { id := "scott2021_table4_sp3_ye_mi"
    source := ⟨"scott-2021", "Table 4"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "… na-ye … na-mi"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("construction", "parasiticGap"), ("antecedentPerson", "1"), ("antecedentNumber", "sg"), ("trueGap", "ye"), ("parasitic", "mi"), ("speaker", "3")] }

def all : List Datum := [cleft_24_mi, cleft_24_ye, cleft_25_we, cleft_25_ye, cleft_29a_si, cleft_29a_o, cleft_29b_nyi, cleft_29b_o, island_31_we, island_31_ye, island_32_mi, island_32_ye, island_33_mi, island_33_ye, pg_36, pg_37, table4_sp1_ye_ye, table4_sp1_mi_ye, table4_sp1_mi_mi, table4_sp1_ye_mi, table4_sp2_ye_ye, table4_sp2_mi_ye, table4_sp2_mi_mi, table4_sp2_ye_mi, table4_sp3_ye_ye, table4_sp3_mi_ye, table4_sp3_mi_mi, table4_sp3_ye_mi]

end Scott2021.Examples
