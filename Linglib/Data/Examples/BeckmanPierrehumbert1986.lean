module

public import Linglib.Data.Examples.Schema

/-!
# `BeckmanPierrehumbert1986` — typed example data

Auto-generated from `Linglib/Data/Examples/BeckmanPierrehumbert1986.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BeckmanPierrehumbert1986.Examples`.
-/

@[expose] public section

namespace BeckmanPierrehumbert1986.Examples

def bp1986_fig3 : Datum :=
  { id := "bp1986_fig3"
    source := ⟨"beckman-pierrehumbert-1986", "Fig. 3"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Kore-wa toriya-no mawari-no oma'warisan-no hanasi desu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("accentual phrase", "unaccented"), ("tonal pattern", "phrasal H ... boundary L")] }

def bp1986_fig5 : Datum :=
  { id := "bp1986_fig5"
    source := ⟨"beckman-pierrehumbert-1986", "Fig. 5"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Kore-wa mo'riya-no mawari-no oma'warisan-no hanasi desu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("accentual phrase", "accented"), ("process", "catathesis")] }

def bp1986_fig6a : Datum :=
  { id := "bp1986_fig6a"
    source := ⟨"beckman-pierrehumbert-1986", "Fig. 6a"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Uma'i mame'-wa arimasen."
    glossedTokens := []
    context := "Adjective and noun grouped in one accentual phrase."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("process", "accent deletion"), ("constraint", "one accent per AP")] }

def bp1986_fig6b : Datum :=
  { id := "bp1986_fig6b"
    source := ⟨"beckman-pierrehumbert-1986", "Fig. 6b"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Uma'i ame-wa arimasen."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("accentual phrase", "one accent"), ("noun", "unaccented")] }

def bp1986_fig8 : Datum :=
  { id := "bp1986_fig8"
    source := ⟨"beckman-pierrehumbert-1986", "Fig. 8"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Amai mame'-wa arimasen."
    glossedTokens := []
    context := "Contrastive emphasis on amai."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("focus", "initial"), ("process", "subordination or dephrasing")] }

def bp1986_ex2 : Datum :=
  { id := "bp1986_ex2"
    source := ⟨"beckman-pierrehumbert-1986", "(2)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Kono arai ayaori-no obizi ga."
    glossedTokens := [("Kono", "this"), ("arai", "rough"), ("ayaori-no", "twill"), ("obizi", "obi.cloth"), ("ga", "")]
    glossedWords := [⟨['K', 'o', 'n', 'o'], ['t', 'h', 'i', 's'], [⟨['K', 'o', 'n', 'o'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['a', 'r', 'a', 'i'], ['r', 'o', 'u', 'g', 'h'], [⟨['a', 'r', 'a', 'i'], ['r', 'o', 'u', 'g', 'h'], none⟩]⟩, ⟨['a', 'y', 'a', 'o', 'r', 'i', '-', 'n', 'o'], ['t', 'w', 'i', 'l', 'l'], []⟩, ⟨['o', 'b', 'i', 'z', 'i'], ['o', 'b', 'i', '.', 'c', 'l', 'o', 't', 'h'], [⟨['o', 'b', 'i', 'z', 'i'], ['o', 'b', 'i', '.', 'c', 'l', 'o', 't', 'h'], none⟩]⟩, ⟨['g', 'a'], [], [⟨['g', 'a'], [], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("intermediate phrase", "break after first modifier")] }

def bp1986_ex3 : Datum :=
  { id := "bp1986_ex3"
    source := ⟨"beckman-pierrehumbert-1986", "(3)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "be'ika neage hantai u'ndoo"
    glossedTokens := [("be'ika", "rice.price"), ("neage", "price.raise"), ("hantai", "protest"), ("u'ndoo", "movement")]
    glossedWords := [⟨['b', 'e', '\'', 'i', 'k', 'a'], ['r', 'i', 'c', 'e', '.', 'p', 'r', 'i', 'c', 'e'], [⟨['b', 'e', '\'', 'i', 'k', 'a'], ['r', 'i', 'c', 'e', '.', 'p', 'r', 'i', 'c', 'e'], none⟩]⟩, ⟨['n', 'e', 'a', 'g', 'e'], ['p', 'r', 'i', 'c', 'e', '.', 'r', 'a', 'i', 's', 'e'], [⟨['n', 'e', 'a', 'g', 'e'], ['p', 'r', 'i', 'c', 'e', '.', 'r', 'a', 'i', 's', 'e'], none⟩]⟩, ⟨['h', 'a', 'n', 't', 'a', 'i'], ['p', 'r', 'o', 't', 'e', 's', 't'], [⟨['h', 'a', 'n', 't', 'a', 'i'], ['p', 'r', 'o', 't', 'e', 's', 't'], none⟩]⟩, ⟨['u', '\'', 'n', 'd', 'o', 'o'], ['m', 'o', 'v', 'e', 'm', 'e', 'n', 't'], [⟨['u', '\'', 'n', 'd', 'o', 'o'], ['m', 'o', 'v', 'e', 'm', 'e', 'n', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("intermediate phrase", "break inside compound")] }

def bp1986_fig36 : Datum :=
  { id := "bp1986_fig36"
    source := ⟨"beckman-pierrehumbert-1986", "Fig. 36"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Moo tyo'tto migigawa-ga sagerare'ru."
    glossedTokens := []
    context := "Declarative vs yes/no question renditions."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("process", "final lowering"), ("domain", "declaratives only")] }

def bp1986_fig1 : Datum :=
  { id := "bp1986_fig1"
    source := ⟨"beckman-pierrehumbert-1986", "Fig. 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "an orange ballgown"
    glossedTokens := []
    context := "Answers to the question: What's that?"
    judgment := .acceptable
    contrasts := []
    readings := [("H* H* L L%: neutral declarative", .acceptable), ("H*+L H* L L%: downstepping, feigned judiciousness", .acceptable), ("L* H* L L%: surprise-redundancy", .acceptable)]
    paperFeatures := [("accent inventory", "postlexical shape choice")] }

def bp1986_fig2 : Datum :=
  { id := "bp1986_fig2"
    source := ⟨"beckman-pierrehumbert-1986", "Fig. 2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I really won't allow Mary."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("H* on Mary: peak near end of stressed syllable, impatient reassertion", .acceptable), ("H+L* on Mary: peak just before the stressed syllable, peevish", .acceptable)]
    paperFeatures := [("diagnostic", "peak alignment"), ("claim", "bitonal accents are units")] }

def bp1986_fig11 : Datum :=
  { id := "bp1986_fig11"
    source := ⟨"beckman-pierrehumbert-1986", "Fig. 11"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "blueberries, bayberries, raspberries, mulberries and brambleberries"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("process", "catathesis chain"), ("contour", "descending staircase")] }

def bp1986_ex4 : Datum :=
  { id := "bp1986_ex4"
    source := ⟨"beckman-pierrehumbert-1986", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "'I' means insert."
    glossedTokens := []
    context := "A text-editor tutor defining a key."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("intermediate phrase", "medial L phrase accent")] }

def bp1986_ex7 : Datum :=
  { id := "bp1986_ex7"
    source := ⟨"beckman-pierrehumbert-1986", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They gave orange marmalade, lemon-oil marmalade, and watermelon-rind marmalade?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("intermediate phrase", "H phrase accent per list item"), ("boundary tone", "one final H%")] }

def bp1986_ex9 : Datum :=
  { id := "bp1986_ex9"
    source := ⟨"beckman-pierrehumbert-1986", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A pale orange and yellow ballgown."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("pale | orange and yellow: both conjuncts pale", .acceptable), ("pale orange | and yellow: only the orange pale", .acceptable)]
    paperFeatures := [("intermediate phrase", "scope disambiguation")] }

def bp1986_fig34 : Datum :=
  { id := "bp1986_fig34"
    source := ⟨"beckman-pierrehumbert-1986", "Fig. 34"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "it's eleven and nine and one and EIGHTY"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("process", "catathesis blocked at focus"), ("intermediate phrase", "break before focus")] }

def all : List Datum := [bp1986_fig3, bp1986_fig5, bp1986_fig6a, bp1986_fig6b, bp1986_fig8, bp1986_ex2, bp1986_ex3, bp1986_fig36, bp1986_fig1, bp1986_fig2, bp1986_fig11, bp1986_ex4, bp1986_ex7, bp1986_ex9, bp1986_fig34]

end BeckmanPierrehumbert1986.Examples
