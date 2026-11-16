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
    glossedWords := [⟨[['Þ', 'e', 'i', 'r']], [['t', 'h', 'e', 'y', '.', 'N', 'O', 'M']]⟩, ⟨[['h', 'a', 'f', 'a']], [['h', 'a', 'v', 'e', '1']]⟩, ⟨[['s', 't', 'ó', 'r', 'a']], [['b', 'i', 'g']]⟩, ⟨[['b', 'ó', 'k']], [['b', 'o', 'o', 'k', '.', 'A', 'C', 'C']]⟩]
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
    glossedWords := [⟨[['Þ', 'e', 'i', 'r']], [['t', 'h', 'e', 'y', '.', 'N', 'O', 'M']]⟩, ⟨[['e', 'i', 'g', 'a']], [['h', 'a', 'v', 'e', '2']]⟩, ⟨[['s', 't', 'ó', 'r', 'a']], [['b', 'i', 'g']]⟩, ⟨[['b', 'ó', 'k']], [['b', 'o', 'o', 'k', '.', 'A', 'C', 'C']]⟩]
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
    glossedWords := [⟨[['Þ', 'e', 'i', 'r']], [['t', 'h', 'e', 'y', '.', 'N', 'O', 'M']]⟩, ⟨[['h', 'a', 'f', 'a']], [['h', 'a', 'v', 'e', '1']]⟩, ⟨[['s', 'y', 's', 't', 'u', 'r']], [['s', 'i', 's', 't', 'e', 'r', '.', 'A', 'C', 'C']]⟩]
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
    glossedWords := [⟨[['Þ', 'e', 'i', 'r']], [['t', 'h', 'e', 'y', '.', 'N', 'O', 'M']]⟩, ⟨[['e', 'i', 'g', 'a']], [['h', 'a', 'v', 'e', '2']]⟩, ⟨[['s', 'y', 's', 't', 'u', 'r']], [['s', 'i', 's', 't', 'e', 'r', '.', 'A', 'C', 'C']]⟩]
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
    glossedWords := [⟨[['Þ', 'e', 'i', 'r']], [['t', 'h', 'e', 'y', '.', 'N', 'O', 'M']]⟩, ⟨[['h', 'a', 'f', 'a']], [['h', 'a', 'v', 'e', '1']]⟩, ⟨[['a', 'u', 'g', 'u']], [['e', 'y', 'e', 's', '.', 'A', 'C', 'C']]⟩]
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
    glossedWords := [⟨[['Þ', 'e', 'i', 'r']], [['t', 'h', 'e', 'y', '.', 'N', 'O', 'M']]⟩, ⟨[['e', 'i', 'g', 'a']], [['h', 'a', 'v', 'e', '2']]⟩, ⟨[['a', 'u', 'g', 'u']], [['e', 'y', 'e', 's', '.', 'A', 'C', 'C']]⟩]
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
    glossedWords := [⟨[['Þ', 'e', 'i', 'r']], [['t', 'h', 'e', 'y', '.', 'N', 'O', 'M']]⟩, ⟨[['h', 'a', 'f', 'a']], [['h', 'a', 'v', 'e', '1']]⟩, ⟨[['e', 'k', 'k', 'i']], [['n', 'o', 't']]⟩, ⟨[['h', 'u', 'g', 'm', 'y', 'n', 'd']], [['i', 'd', 'e', 'a', '.', 'A', 'C', 'C']]⟩]
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
    glossedWords := [⟨[['Þ', 'e', 'i', 'r']], [['t', 'h', 'e', 'y', '.', 'N', 'O', 'M']]⟩, ⟨[['e', 'i', 'g', 'a']], [['h', 'a', 'v', 'e', '2']]⟩, ⟨[['e', 'k', 'k', 'i']], [['n', 'o', 't']]⟩, ⟨[['h', 'u', 'g', 'm', 'y', 'n', 'd']], [['i', 'd', 'e', 'a', '.', 'A', 'C', 'C']]⟩]
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
    glossedWords := [⟨[['b', 'ó', 'k']], [['b', 'o', 'o', 'k']]⟩, ⟨[['m', 'í', 'n']], [['m', 'y']]⟩]
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
    glossedWords := [⟨[['b', 'ó', 'k'], ['i', 'n']], [['b', 'o', 'o', 'k'], ['D', 'E', 'F']]⟩, ⟨[['m', 'í', 'n']], [['m', 'y']]⟩]
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
    glossedWords := [⟨[['b', 'ó', 'k'], ['i', 'n']], [['b', 'o', 'o', 'k'], ['D', 'E', 'F']]⟩, ⟨[['h', 'j', 'á']], [['a', 't']]⟩, ⟨[['m', 'é', 'r']], [['m', 'e']]⟩]
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
    glossedWords := [⟨[['s', 'y', 's', 't', 'i', 'r']], [['s', 'i', 's', 't', 'e', 'r']]⟩, ⟨[['m', 'í', 'n']], [['m', 'y']]⟩]
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
    glossedWords := [⟨[['s', 'y', 's', 't', 'i', 'r'], ['i', 'n']], [['s', 'i', 's', 't', 'e', 'r'], ['D', 'E', 'F']]⟩, ⟨[['m', 'í', 'n']], [['m', 'y']]⟩]
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
    glossedWords := [⟨[['s', 'y', 's', 't', 'i', 'r'], ['i', 'n']], [['s', 'i', 's', 't', 'e', 'r'], ['D', 'E', 'F']]⟩, ⟨[['h', 'j', 'á']], [['a', 't']]⟩, ⟨[['m', 'é', 'r']], [['m', 'e']]⟩]
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
    glossedWords := [⟨[['a', 'u', 'g', 'u']], [['e', 'y', 'e', 's']]⟩, ⟨[['m', 'í', 'n']], [['m', 'y']]⟩]
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
    glossedWords := [⟨[['a', 'u', 'g', 'u'], ['n']], [['e', 'y', 'e', 's'], ['D', 'E', 'F']]⟩, ⟨[['m', 'í', 'n']], [['m', 'y']]⟩]
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
    glossedWords := [⟨[['a', 'u', 'g', 'u'], ['n']], [['e', 'y', 'e', 's'], ['D', 'E', 'F']]⟩, ⟨[['í']], [['i', 'n']]⟩, ⟨[['m', 'é', 'r']], [['m', 'e']]⟩]
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
    glossedWords := [⟨[['h', 'u', 'g', 'm', 'y', 'n', 'd']], [['i', 'd', 'e', 'a']]⟩, ⟨[['m', 'í', 'n']], [['m', 'y']]⟩]
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
    glossedWords := [⟨[['h', 'u', 'g', 'm', 'y', 'n', 'd'], ['i', 'n']], [['i', 'd', 'e', 'a'], ['D', 'E', 'F']]⟩, ⟨[['m', 'í', 'n']], [['m', 'y']]⟩]
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
    glossedWords := [⟨[['h', 'u', 'g', 'm', 'y', 'n', 'd'], ['i', 'n']], [['i', 'd', 'e', 'a'], ['D', 'E', 'F']]⟩, ⟨[['h', 'j', 'á']], [['a', 't']]⟩, ⟨[['m', 'é', 'r']], [['m', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("relation", "abstract"), ("construction", "attributiveC")] }

def all : List Datum := [concrete_hafa, concrete_eiga, kinship_hafa, kinship_eiga, bodyPart_hafa, bodyPart_eiga, abstract_hafa, abstract_eiga, concrete_attrA, concrete_attrB, concrete_attrC, kinship_attrA, kinship_attrB, kinship_attrC, bodyPart_attrA, bodyPart_attrB, bodyPart_attrC, abstract_attrA, abstract_attrB, abstract_attrC]

end Myler2016.Examples
