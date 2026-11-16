module

public import Linglib.Data.Examples.Schema

/-!
# `Myler2016` — typed example data

Auto-generated from `Linglib/Data/Examples/Myler2016.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Myler2016.Examples`.
-/

@[expose] public section

namespace Myler2016.Examples

def concrete_hafa : Datum :=
  { id := "myler2016_concrete_hafa"
    source := ⟨"myler-2016", "(91)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Þeir hafa stóra bók."
    glossedTokens := [("Þeir", "they.NOM"), ("hafa", "have1"), ("stóra", "big"), ("bók", "book.ACC")]
    glossedWords := [⟨['Þ', 'e', 'i', 'r'], ['t', 'h', 'e', 'y', '.', 'N', 'O', 'M'], [⟨['Þ', 'e', 'i', 'r'], ['t', 'h', 'e', 'y', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['h', 'a', 'f', 'a'], ['h', 'a', 'v', 'e', '1'], [⟨['h', 'a', 'f', 'a'], ['h', 'a', 'v', 'e', '1'], none⟩]⟩, ⟨['s', 't', 'ó', 'r', 'a'], ['b', 'i', 'g'], [⟨['s', 't', 'ó', 'r', 'a'], ['b', 'i', 'g'], none⟩]⟩, ⟨['b', 'ó', 'k'], ['b', 'o', 'o', 'k', '.', 'A', 'C', 'C'], [⟨['b', 'ó', 'k'], ['b', 'o', 'o', 'k', '.', 'A', 'C', 'C'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("relation", "concrete"), ("construction", "clausal"), ("verb", "hafa")] }

def concrete_eiga : Datum :=
  { id := "myler2016_concrete_eiga"
    source := ⟨"myler-2016", "(91)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Þeir eiga stóra bók."
    glossedTokens := [("Þeir", "they.NOM"), ("eiga", "have2"), ("stóra", "big"), ("bók", "book.ACC")]
    glossedWords := [⟨['Þ', 'e', 'i', 'r'], ['t', 'h', 'e', 'y', '.', 'N', 'O', 'M'], [⟨['Þ', 'e', 'i', 'r'], ['t', 'h', 'e', 'y', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['e', 'i', 'g', 'a'], ['h', 'a', 'v', 'e', '2'], [⟨['e', 'i', 'g', 'a'], ['h', 'a', 'v', 'e', '2'], none⟩]⟩, ⟨['s', 't', 'ó', 'r', 'a'], ['b', 'i', 'g'], [⟨['s', 't', 'ó', 'r', 'a'], ['b', 'i', 'g'], none⟩]⟩, ⟨['b', 'ó', 'k'], ['b', 'o', 'o', 'k', '.', 'A', 'C', 'C'], [⟨['b', 'ó', 'k'], ['b', 'o', 'o', 'k', '.', 'A', 'C', 'C'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("relation", "concrete"), ("construction", "clausal"), ("verb", "eiga")] }

def kinship_hafa : Datum :=
  { id := "myler2016_kinship_hafa"
    source := ⟨"myler-2016", "(91)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Þeir hafa systur."
    glossedTokens := [("Þeir", "they.NOM"), ("hafa", "have1"), ("systur", "sister.ACC")]
    glossedWords := [⟨['Þ', 'e', 'i', 'r'], ['t', 'h', 'e', 'y', '.', 'N', 'O', 'M'], [⟨['Þ', 'e', 'i', 'r'], ['t', 'h', 'e', 'y', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['h', 'a', 'f', 'a'], ['h', 'a', 'v', 'e', '1'], [⟨['h', 'a', 'f', 'a'], ['h', 'a', 'v', 'e', '1'], none⟩]⟩, ⟨['s', 'y', 's', 't', 'u', 'r'], ['s', 'i', 's', 't', 'e', 'r', '.', 'A', 'C', 'C'], [⟨['s', 'y', 's', 't', 'u', 'r'], ['s', 'i', 's', 't', 'e', 'r', '.', 'A', 'C', 'C'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("relation", "kinship"), ("construction", "clausal"), ("verb", "hafa")] }

def kinship_eiga : Datum :=
  { id := "myler2016_kinship_eiga"
    source := ⟨"myler-2016", "(91)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Þeir eiga systur."
    glossedTokens := [("Þeir", "they.NOM"), ("eiga", "have2"), ("systur", "sister.ACC")]
    glossedWords := [⟨['Þ', 'e', 'i', 'r'], ['t', 'h', 'e', 'y', '.', 'N', 'O', 'M'], [⟨['Þ', 'e', 'i', 'r'], ['t', 'h', 'e', 'y', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['e', 'i', 'g', 'a'], ['h', 'a', 'v', 'e', '2'], [⟨['e', 'i', 'g', 'a'], ['h', 'a', 'v', 'e', '2'], none⟩]⟩, ⟨['s', 'y', 's', 't', 'u', 'r'], ['s', 'i', 's', 't', 'e', 'r', '.', 'A', 'C', 'C'], [⟨['s', 'y', 's', 't', 'u', 'r'], ['s', 'i', 's', 't', 'e', 'r', '.', 'A', 'C', 'C'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("relation", "kinship"), ("construction", "clausal"), ("verb", "eiga")] }

def bodyPart_hafa : Datum :=
  { id := "myler2016_bodyPart_hafa"
    source := ⟨"myler-2016", "(91)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Þeir hafa augu."
    glossedTokens := [("Þeir", "they.NOM"), ("hafa", "have1"), ("augu", "eyes.ACC")]
    glossedWords := [⟨['Þ', 'e', 'i', 'r'], ['t', 'h', 'e', 'y', '.', 'N', 'O', 'M'], [⟨['Þ', 'e', 'i', 'r'], ['t', 'h', 'e', 'y', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['h', 'a', 'f', 'a'], ['h', 'a', 'v', 'e', '1'], [⟨['h', 'a', 'f', 'a'], ['h', 'a', 'v', 'e', '1'], none⟩]⟩, ⟨['a', 'u', 'g', 'u'], ['e', 'y', 'e', 's', '.', 'A', 'C', 'C'], [⟨['a', 'u', 'g', 'u'], ['e', 'y', 'e', 's', '.', 'A', 'C', 'C'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("relation", "bodyPart"), ("construction", "clausal"), ("verb", "hafa")] }

def bodyPart_eiga : Datum :=
  { id := "myler2016_bodyPart_eiga"
    source := ⟨"myler-2016", "(91)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Þeir eiga augu."
    glossedTokens := [("Þeir", "they.NOM"), ("eiga", "have2"), ("augu", "eyes.ACC")]
    glossedWords := [⟨['Þ', 'e', 'i', 'r'], ['t', 'h', 'e', 'y', '.', 'N', 'O', 'M'], [⟨['Þ', 'e', 'i', 'r'], ['t', 'h', 'e', 'y', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['e', 'i', 'g', 'a'], ['h', 'a', 'v', 'e', '2'], [⟨['e', 'i', 'g', 'a'], ['h', 'a', 'v', 'e', '2'], none⟩]⟩, ⟨['a', 'u', 'g', 'u'], ['e', 'y', 'e', 's', '.', 'A', 'C', 'C'], [⟨['a', 'u', 'g', 'u'], ['e', 'y', 'e', 's', '.', 'A', 'C', 'C'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("relation", "bodyPart"), ("construction", "clausal"), ("verb", "eiga")] }

def abstract_hafa : Datum :=
  { id := "myler2016_abstract_hafa"
    source := ⟨"myler-2016", "(91)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Þeir hafa ekki hugmynd."
    glossedTokens := [("Þeir", "they.NOM"), ("hafa", "have1"), ("ekki", "not"), ("hugmynd", "idea.ACC")]
    glossedWords := [⟨['Þ', 'e', 'i', 'r'], ['t', 'h', 'e', 'y', '.', 'N', 'O', 'M'], [⟨['Þ', 'e', 'i', 'r'], ['t', 'h', 'e', 'y', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['h', 'a', 'f', 'a'], ['h', 'a', 'v', 'e', '1'], [⟨['h', 'a', 'f', 'a'], ['h', 'a', 'v', 'e', '1'], none⟩]⟩, ⟨['e', 'k', 'k', 'i'], ['n', 'o', 't'], [⟨['e', 'k', 'k', 'i'], ['n', 'o', 't'], none⟩]⟩, ⟨['h', 'u', 'g', 'm', 'y', 'n', 'd'], ['i', 'd', 'e', 'a', '.', 'A', 'C', 'C'], [⟨['h', 'u', 'g', 'm', 'y', 'n', 'd'], ['i', 'd', 'e', 'a', '.', 'A', 'C', 'C'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("relation", "abstract"), ("construction", "clausal"), ("verb", "hafa")] }

def abstract_eiga : Datum :=
  { id := "myler2016_abstract_eiga"
    source := ⟨"myler-2016", "(91)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Þeir eiga ekki hugmynd."
    glossedTokens := [("Þeir", "they.NOM"), ("eiga", "have2"), ("ekki", "not"), ("hugmynd", "idea.ACC")]
    glossedWords := [⟨['Þ', 'e', 'i', 'r'], ['t', 'h', 'e', 'y', '.', 'N', 'O', 'M'], [⟨['Þ', 'e', 'i', 'r'], ['t', 'h', 'e', 'y', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['e', 'i', 'g', 'a'], ['h', 'a', 'v', 'e', '2'], [⟨['e', 'i', 'g', 'a'], ['h', 'a', 'v', 'e', '2'], none⟩]⟩, ⟨['e', 'k', 'k', 'i'], ['n', 'o', 't'], [⟨['e', 'k', 'k', 'i'], ['n', 'o', 't'], none⟩]⟩, ⟨['h', 'u', 'g', 'm', 'y', 'n', 'd'], ['i', 'd', 'e', 'a', '.', 'A', 'C', 'C'], [⟨['h', 'u', 'g', 'm', 'y', 'n', 'd'], ['i', 'd', 'e', 'a', '.', 'A', 'C', 'C'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("relation", "abstract"), ("construction", "clausal"), ("verb", "eiga")] }

def concrete_attrA : Datum :=
  { id := "myler2016_concrete_attrA"
    source := ⟨"myler-2016", "(92)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "bók mín"
    glossedTokens := [("bók", "book"), ("mín", "my")]
    glossedWords := [⟨['b', 'ó', 'k'], ['b', 'o', 'o', 'k'], [⟨['b', 'ó', 'k'], ['b', 'o', 'o', 'k'], none⟩]⟩, ⟨['m', 'í', 'n'], ['m', 'y'], [⟨['m', 'í', 'n'], ['m', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("relation", "concrete"), ("construction", "attributiveA")] }

def concrete_attrB : Datum :=
  { id := "myler2016_concrete_attrB"
    source := ⟨"myler-2016", "(92)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "bók-in mín"
    glossedTokens := [("bók-in", "book-DEF"), ("mín", "my")]
    glossedWords := [⟨['b', 'ó', 'k', '-', 'i', 'n'], ['b', 'o', 'o', 'k', '-', 'D', 'E', 'F'], [⟨['b', 'ó', 'k'], ['b', 'o', 'o', 'k'], none⟩, ⟨['i', 'n'], ['D', 'E', 'F'], some '-'⟩]⟩, ⟨['m', 'í', 'n'], ['m', 'y'], [⟨['m', 'í', 'n'], ['m', 'y'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("relation", "concrete"), ("construction", "attributiveB")] }

def concrete_attrC : Datum :=
  { id := "myler2016_concrete_attrC"
    source := ⟨"myler-2016", "(92)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "bók-in hjá mér"
    glossedTokens := [("bók-in", "book-DEF"), ("hjá", "at"), ("mér", "me")]
    glossedWords := [⟨['b', 'ó', 'k', '-', 'i', 'n'], ['b', 'o', 'o', 'k', '-', 'D', 'E', 'F'], [⟨['b', 'ó', 'k'], ['b', 'o', 'o', 'k'], none⟩, ⟨['i', 'n'], ['D', 'E', 'F'], some '-'⟩]⟩, ⟨['h', 'j', 'á'], ['a', 't'], [⟨['h', 'j', 'á'], ['a', 't'], none⟩]⟩, ⟨['m', 'é', 'r'], ['m', 'e'], [⟨['m', 'é', 'r'], ['m', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("relation", "concrete"), ("construction", "attributiveC")] }

def kinship_attrA : Datum :=
  { id := "myler2016_kinship_attrA"
    source := ⟨"myler-2016", "(92)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "systir mín"
    glossedTokens := [("systir", "sister"), ("mín", "my")]
    glossedWords := [⟨['s', 'y', 's', 't', 'i', 'r'], ['s', 'i', 's', 't', 'e', 'r'], [⟨['s', 'y', 's', 't', 'i', 'r'], ['s', 'i', 's', 't', 'e', 'r'], none⟩]⟩, ⟨['m', 'í', 'n'], ['m', 'y'], [⟨['m', 'í', 'n'], ['m', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("relation", "kinship"), ("construction", "attributiveA")] }

def kinship_attrB : Datum :=
  { id := "myler2016_kinship_attrB"
    source := ⟨"myler-2016", "(92)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "systir-in mín"
    glossedTokens := [("systir-in", "sister-DEF"), ("mín", "my")]
    glossedWords := [⟨['s', 'y', 's', 't', 'i', 'r', '-', 'i', 'n'], ['s', 'i', 's', 't', 'e', 'r', '-', 'D', 'E', 'F'], [⟨['s', 'y', 's', 't', 'i', 'r'], ['s', 'i', 's', 't', 'e', 'r'], none⟩, ⟨['i', 'n'], ['D', 'E', 'F'], some '-'⟩]⟩, ⟨['m', 'í', 'n'], ['m', 'y'], [⟨['m', 'í', 'n'], ['m', 'y'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("relation", "kinship"), ("construction", "attributiveB")] }

def kinship_attrC : Datum :=
  { id := "myler2016_kinship_attrC"
    source := ⟨"myler-2016", "(92)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "systir-in hjá mér"
    glossedTokens := [("systir-in", "sister-DEF"), ("hjá", "at"), ("mér", "me")]
    glossedWords := [⟨['s', 'y', 's', 't', 'i', 'r', '-', 'i', 'n'], ['s', 'i', 's', 't', 'e', 'r', '-', 'D', 'E', 'F'], [⟨['s', 'y', 's', 't', 'i', 'r'], ['s', 'i', 's', 't', 'e', 'r'], none⟩, ⟨['i', 'n'], ['D', 'E', 'F'], some '-'⟩]⟩, ⟨['h', 'j', 'á'], ['a', 't'], [⟨['h', 'j', 'á'], ['a', 't'], none⟩]⟩, ⟨['m', 'é', 'r'], ['m', 'e'], [⟨['m', 'é', 'r'], ['m', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("relation", "kinship"), ("construction", "attributiveC")] }

def bodyPart_attrA : Datum :=
  { id := "myler2016_bodyPart_attrA"
    source := ⟨"myler-2016", "(92)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "augu mín"
    glossedTokens := [("augu", "eyes"), ("mín", "my")]
    glossedWords := [⟨['a', 'u', 'g', 'u'], ['e', 'y', 'e', 's'], [⟨['a', 'u', 'g', 'u'], ['e', 'y', 'e', 's'], none⟩]⟩, ⟨['m', 'í', 'n'], ['m', 'y'], [⟨['m', 'í', 'n'], ['m', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("relation", "bodyPart"), ("construction", "attributiveA")] }

def bodyPart_attrB : Datum :=
  { id := "myler2016_bodyPart_attrB"
    source := ⟨"myler-2016", "(92)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "augu-n mín"
    glossedTokens := [("augu-n", "eyes-DEF"), ("mín", "my")]
    glossedWords := [⟨['a', 'u', 'g', 'u', '-', 'n'], ['e', 'y', 'e', 's', '-', 'D', 'E', 'F'], [⟨['a', 'u', 'g', 'u'], ['e', 'y', 'e', 's'], none⟩, ⟨['n'], ['D', 'E', 'F'], some '-'⟩]⟩, ⟨['m', 'í', 'n'], ['m', 'y'], [⟨['m', 'í', 'n'], ['m', 'y'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("relation", "bodyPart"), ("construction", "attributiveB")] }

def bodyPart_attrC : Datum :=
  { id := "myler2016_bodyPart_attrC"
    source := ⟨"myler-2016", "(92)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "augu-n í mér"
    glossedTokens := [("augu-n", "eyes-DEF"), ("í", "in"), ("mér", "me")]
    glossedWords := [⟨['a', 'u', 'g', 'u', '-', 'n'], ['e', 'y', 'e', 's', '-', 'D', 'E', 'F'], [⟨['a', 'u', 'g', 'u'], ['e', 'y', 'e', 's'], none⟩, ⟨['n'], ['D', 'E', 'F'], some '-'⟩]⟩, ⟨['í'], ['i', 'n'], [⟨['í'], ['i', 'n'], none⟩]⟩, ⟨['m', 'é', 'r'], ['m', 'e'], [⟨['m', 'é', 'r'], ['m', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("relation", "bodyPart"), ("construction", "attributiveC")] }

def abstract_attrA : Datum :=
  { id := "myler2016_abstract_attrA"
    source := ⟨"myler-2016", "(92)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "hugmynd mín"
    glossedTokens := [("hugmynd", "idea"), ("mín", "my")]
    glossedWords := [⟨['h', 'u', 'g', 'm', 'y', 'n', 'd'], ['i', 'd', 'e', 'a'], [⟨['h', 'u', 'g', 'm', 'y', 'n', 'd'], ['i', 'd', 'e', 'a'], none⟩]⟩, ⟨['m', 'í', 'n'], ['m', 'y'], [⟨['m', 'í', 'n'], ['m', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("relation", "abstract"), ("construction", "attributiveA")] }

def abstract_attrB : Datum :=
  { id := "myler2016_abstract_attrB"
    source := ⟨"myler-2016", "(92)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "hugmynd-in mín"
    glossedTokens := [("hugmynd-in", "idea-DEF"), ("mín", "my")]
    glossedWords := [⟨['h', 'u', 'g', 'm', 'y', 'n', 'd', '-', 'i', 'n'], ['i', 'd', 'e', 'a', '-', 'D', 'E', 'F'], [⟨['h', 'u', 'g', 'm', 'y', 'n', 'd'], ['i', 'd', 'e', 'a'], none⟩, ⟨['i', 'n'], ['D', 'E', 'F'], some '-'⟩]⟩, ⟨['m', 'í', 'n'], ['m', 'y'], [⟨['m', 'í', 'n'], ['m', 'y'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("relation", "abstract"), ("construction", "attributiveB")] }

def abstract_attrC : Datum :=
  { id := "myler2016_abstract_attrC"
    source := ⟨"myler-2016", "(92)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "hugmynd-in hjá mér"
    glossedTokens := [("hugmynd-in", "idea-DEF"), ("hjá", "at"), ("mér", "me")]
    glossedWords := [⟨['h', 'u', 'g', 'm', 'y', 'n', 'd', '-', 'i', 'n'], ['i', 'd', 'e', 'a', '-', 'D', 'E', 'F'], [⟨['h', 'u', 'g', 'm', 'y', 'n', 'd'], ['i', 'd', 'e', 'a'], none⟩, ⟨['i', 'n'], ['D', 'E', 'F'], some '-'⟩]⟩, ⟨['h', 'j', 'á'], ['a', 't'], [⟨['h', 'j', 'á'], ['a', 't'], none⟩]⟩, ⟨['m', 'é', 'r'], ['m', 'e'], [⟨['m', 'é', 'r'], ['m', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("relation", "abstract"), ("construction", "attributiveC")] }

def all : List Datum := [concrete_hafa, concrete_eiga, kinship_hafa, kinship_eiga, bodyPart_hafa, bodyPart_eiga, abstract_hafa, abstract_eiga, concrete_attrA, concrete_attrB, concrete_attrC, kinship_attrA, kinship_attrB, kinship_attrC, bodyPart_attrA, bodyPart_attrB, bodyPart_attrC, abstract_attrA, abstract_attrB, abstract_attrC]

end Myler2016.Examples
