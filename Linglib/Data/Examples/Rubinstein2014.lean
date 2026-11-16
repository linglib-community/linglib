module

public import Linglib.Data.Examples.Schema

/-!
# `Rubinstein2014` — typed example data

Auto-generated from `Linglib/Data/Examples/Rubinstein2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Rubinstein2014.Examples`.
-/

@[expose] public section

namespace Rubinstein2014.Examples

def nr_should : Datum :=
  { id := "rubinstein2014_nr_should"
    source := ⟨"horn-1978", "p. 198"⟩
    reportedIn := some ⟨"rubinstein-2014", "(31a)"⟩
    language := "stan1293"
    primaryText := "I don't think you should leave."
    glossedTokens := []
    context := "Embedded under 'I don't think', testing the lower-negation (neg-raising) reading."
    judgment := .acceptable
    alternatives := []
    readings := [("lowerNeg", .acceptable)]
    paperFeatures := [("modal", "should"), ("category", "modalVerb"), ("diagnostic", "negRaising")] }

def nr_ought : Datum :=
  { id := "rubinstein2014_nr_ought"
    source := ⟨"horn-1978", "p. 198"⟩
    reportedIn := some ⟨"rubinstein-2014", "(31a)"⟩
    language := "stan1293"
    primaryText := "I don't think you ought to leave."
    glossedTokens := []
    context := "Embedded under 'I don't think', testing the lower-negation (neg-raising) reading."
    judgment := .acceptable
    alternatives := []
    readings := [("lowerNeg", .acceptable)]
    paperFeatures := [("modal", "ought"), ("category", "modalVerb"), ("diagnostic", "negRaising")] }

def nr_better : Datum :=
  { id := "rubinstein2014_nr_better"
    source := ⟨"horn-1978", "p. 198"⟩
    reportedIn := some ⟨"rubinstein-2014", "(31a)"⟩
    language := "stan1293"
    primaryText := "I don't think you better leave."
    glossedTokens := []
    context := "Embedded under 'I don't think', testing the lower-negation (neg-raising) reading."
    judgment := .acceptable
    alternatives := []
    readings := [("lowerNeg", .acceptable)]
    paperFeatures := [("modal", "better"), ("category", "evaluativeComparative"), ("diagnostic", "negRaising")] }

def nr_good : Datum :=
  { id := "rubinstein2014_nr_good"
    source := ⟨"horn-1978", "p. 211"⟩
    reportedIn := some ⟨"rubinstein-2014", "(30)"⟩
    language := "stan1293"
    primaryText := "It wouldn't be good for you to cheat on your taxes."
    glossedTokens := []
    context := "Negated evaluative; tests the excluded-middle (neg-raising) inference under higher negation."
    judgment := .acceptable
    alternatives := []
    readings := [("lowerNeg", .acceptable)]
    paperFeatures := [("modal", "good"), ("category", "evaluativeComparative"), ("diagnostic", "negRaising")] }

def nr_must : Datum :=
  { id := "rubinstein2014_nr_must"
    source := ⟨"horn-1978", "p. 198"⟩
    reportedIn := some ⟨"rubinstein-2014", "(31b)"⟩
    language := "stan1293"
    primaryText := "I don't think you must leave."
    glossedTokens := []
    context := "Embedded under 'I don't think', testing whether the lower-negation reading is available for a strong necessity modal."
    judgment := .marginal
    alternatives := []
    readings := [("lowerNeg", .unacceptable)]
    paperFeatures := [("modal", "must"), ("category", "modalVerb"), ("diagnostic", "negRaising")] }

def nr_haveTo : Datum :=
  { id := "rubinstein2014_nr_haveTo"
    source := ⟨"horn-1978", "p. 198"⟩
    reportedIn := some ⟨"rubinstein-2014", "(31b)"⟩
    language := "stan1293"
    primaryText := "I don't think you have to leave."
    glossedTokens := []
    context := "Embedded under 'I don't think', testing whether the lower-negation reading is available for a strong necessity modal."
    judgment := .acceptable
    alternatives := []
    readings := [("lowerNeg", .unacceptable)]
    paperFeatures := [("modal", "have to"), ("category", "modalVerb"), ("diagnostic", "negRaising")] }

def nr_adif : Datum :=
  { id := "rubinstein2014_nr_adif"
    source := ⟨"rubinstein-2014", "(33)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "ce'irim sinim kayom lo xošvim še-'adif axeret."
    glossedTokens := [("ce'irim", "young"), ("sinim", "Chinese"), ("kayom", "these days"), ("lo", "NEG"), ("xošvim", "think"), ("še-'adif", "that-preferable"), ("axeret", "differently")]
    glossedWords := [⟨[['c', 'e', '\'', 'i', 'r', 'i', 'm']], [['y', 'o', 'u', 'n', 'g']]⟩, ⟨[['s', 'i', 'n', 'i', 'm']], [['C', 'h', 'i', 'n', 'e', 's', 'e']]⟩, ⟨[['k', 'a', 'y', 'o', 'm']], [['t', 'h', 'e', 's', 'e', ' ', 'd', 'a', 'y', 's']]⟩, ⟨[['l', 'o']], [['N', 'E', 'G']]⟩, ⟨[['x', 'o', 'š', 'v', 'i', 'm']], [['t', 'h', 'i', 'n', 'k']]⟩, ⟨[['š', 'e'], ['\'', 'a', 'd', 'i', 'f']], [['t', 'h', 'a', 't'], ['p', 'r', 'e', 'f', 'e', 'r', 'a', 'b', 'l', 'e']]⟩, ⟨[['a', 'x', 'e', 'r', 'e', 't']], [['d', 'i', 'f', 'f', 'e', 'r', 'e', 'n', 't', 'l', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Blog discussion of attitudes; tests neg-raising (cyclicity) of 'adif 'preferable' in Hebrew."
    judgment := .acceptable
    alternatives := []
    readings := [("lowerNeg", .acceptable)]
    paperFeatures := [("modal", "adif"), ("category", "evaluativeComparative"), ("diagnostic", "negRaising")] }

def ought_lexical : Datum :=
  { id := "rubinstein2014_ought_lexical"
    source := ⟨"rubinstein-2014", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I ought to do the dishes but I don't have to."
    glossedTokens := []
    context := "Test 1 (x E q, but doesn't have to q) with lexical weak-necessity 'ought'."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "ought"), ("category", "modalVerb"), ("strategy", "lexical"), ("diagnostic", "test1")] }

def compositional_deberia : Datum :=
  { id := "rubinstein2014_compositional_deberia"
    source := ⟨"von-fintel-iatridou-2008", "p. 122"⟩
    reportedIn := some ⟨"rubinstein-2014", "(8b)"⟩
    language := "stan1288"
    primaryText := "Debería limpiar los platos, pero no estoy obligado."
    glossedTokens := [("Debería", "must.COND"), ("limpiar", "clean"), ("los", "the"), ("platos", "dishes"), ("pero", "but"), ("no", "not"), ("estoy", "am"), ("obligado", "obliged")]
    glossedWords := [⟨[['D', 'e', 'b', 'e', 'r', 'í', 'a']], [['m', 'u', 's', 't', '.', 'C', 'O', 'N', 'D']]⟩, ⟨[['l', 'i', 'm', 'p', 'i', 'a', 'r']], [['c', 'l', 'e', 'a', 'n']]⟩, ⟨[['l', 'o', 's']], [['t', 'h', 'e']]⟩, ⟨[['p', 'l', 'a', 't', 'o', 's']], [['d', 'i', 's', 'h', 'e', 's']]⟩, ⟨[['p', 'e', 'r', 'o']], [['b', 'u', 't']]⟩, ⟨[['n', 'o']], [['n', 'o', 't']]⟩, ⟨[['e', 's', 't', 'o', 'y']], [['a', 'm']]⟩, ⟨[['o', 'b', 'l', 'i', 'g', 'a', 'd', 'o']], [['o', 'b', 'l', 'i', 'g', 'e', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := "Spanish derives weak necessity compositionally: strong modal deber + conditional morphology."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "deberia"), ("category", "compositional"), ("strategy", "compositional"), ("diagnostic", "test1")] }

def test1_carix : Datum :=
  { id := "rubinstein2014_test1_carix"
    source := ⟨"rubinstein-2014", "(16a)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "hu carix lištof et ha-kelim, aval hu lo xayav."
    glossedTokens := [("hu", "he"), ("carix", "need.MSG"), ("lištof", "wash"), ("et", "ACC"), ("ha-kelim", "the-dishes"), ("aval", "but"), ("hu", "he"), ("lo", "NEG"), ("xayav", "must.MSG")]
    glossedWords := [⟨[['h', 'u']], [['h', 'e']]⟩, ⟨[['c', 'a', 'r', 'i', 'x']], [['n', 'e', 'e', 'd', '.', 'M', 'S', 'G']]⟩, ⟨[['l', 'i', 'š', 't', 'o', 'f']], [['w', 'a', 's', 'h']]⟩, ⟨[['e', 't']], [['A', 'C', 'C']]⟩, ⟨[['h', 'a'], ['k', 'e', 'l', 'i', 'm']], [['t', 'h', 'e'], ['d', 'i', 's', 'h', 'e', 's']]⟩, ⟨[['a', 'v', 'a', 'l']], [['b', 'u', 't']]⟩, ⟨[['h', 'u']], [['h', 'e']]⟩, ⟨[['l', 'o']], [['N', 'E', 'G']]⟩, ⟨[['x', 'a', 'y', 'a', 'v']], [['m', 'u', 's', 't', '.', 'M', 'S', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Given the rules of the house. Test 1 (x ought to q, but doesn't have to) with carix 'need' substituted for ought."
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("modal", "carix"), ("category", "modalVerb"), ("diagnostic", "test1")] }

def test2_carix : Datum :=
  { id := "rubinstein2014_test2_carix"
    source := ⟨"rubinstein-2014", "(19)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "melcarim xayavim lištof yadayim, aval orxim raq crxim."
    glossedTokens := [("melcarim", "waiters"), ("xayavim", "must.MPL"), ("lištof", "wash"), ("yadayim", "hands"), ("aval", "but"), ("orxim", "guests"), ("raq", "only"), ("crxim", "need.MPL")]
    glossedWords := [⟨[['m', 'e', 'l', 'c', 'a', 'r', 'i', 'm']], [['w', 'a', 'i', 't', 'e', 'r', 's']]⟩, ⟨[['x', 'a', 'y', 'a', 'v', 'i', 'm']], [['m', 'u', 's', 't', '.', 'M', 'P', 'L']]⟩, ⟨[['l', 'i', 'š', 't', 'o', 'f']], [['w', 'a', 's', 'h']]⟩, ⟨[['y', 'a', 'd', 'a', 'y', 'i', 'm']], [['h', 'a', 'n', 'd', 's']]⟩, ⟨[['a', 'v', 'a', 'l']], [['b', 'u', 't']]⟩, ⟨[['o', 'r', 'x', 'i', 'm']], [['g', 'u', 'e', 's', 't', 's']]⟩, ⟨[['r', 'a', 'q']], [['o', 'n', 'l', 'y']]⟩, ⟨[['c', 'r', 'x', 'i', 'm']], [['n', 'e', 'e', 'd', '.', 'M', 'P', 'L']]⟩]
    lgrConformance := some .wordAligned
    context := "Test 2 with the exclusive 'only' (raq): y has to q, x only need-to q."
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("modal", "carix"), ("category", "modalVerb"), ("diagnostic", "test2")] }

def heb_yoter_tov : Datum :=
  { id := "rubinstein2014_heb_yoter_tov"
    source := ⟨"rubinstein-2014", "(21a)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "yoter tov še-hu yitpater, aval hu lo xayav lehitpater."
    glossedTokens := [("yoter", "more"), ("tov", "good"), ("še-hu", "that-he"), ("yitpater", "will resign"), ("aval", "but"), ("hu", "he"), ("lo", "NEG"), ("xayav", "must"), ("lehitpater", "resign")]
    glossedWords := [⟨[['y', 'o', 't', 'e', 'r']], [['m', 'o', 'r', 'e']]⟩, ⟨[['t', 'o', 'v']], [['g', 'o', 'o', 'd']]⟩, ⟨[['š', 'e'], ['h', 'u']], [['t', 'h', 'a', 't'], ['h', 'e']]⟩, ⟨[['y', 'i', 't', 'p', 'a', 't', 'e', 'r']], [['w', 'i', 'l', 'l', ' ', 'r', 'e', 's', 'i', 'g', 'n']]⟩, ⟨[['a', 'v', 'a', 'l']], [['b', 'u', 't']]⟩, ⟨[['h', 'u']], [['h', 'e']]⟩, ⟨[['l', 'o']], [['N', 'E', 'G']]⟩, ⟨[['x', 'a', 'y', 'a', 'v']], [['m', 'u', 's', 't']]⟩, ⟨[['l', 'e', 'h', 'i', 't', 'p', 'a', 't', 'e', 'r']], [['r', 'e', 's', 'i', 'g', 'n']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Bribe scenario: a convicted politician ought to resign though no law requires it. Hebrew renders weak-necessity 'ought' via morphological comparison (yoter tov 'more good')."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "tov"), ("category", "evaluativeComparative"), ("strategy", "evaluativeComparative"), ("diagnostic", "test1")] }

def heb_adif : Datum :=
  { id := "rubinstein2014_heb_adif"
    source := ⟨"rubinstein-2014", "(21b)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "'adif še-hu yitpater, aval hu lo xayav lehitpater."
    glossedTokens := [("'adif", "preferable"), ("še-hu", "that-he"), ("yitpater", "will resign"), ("aval", "but"), ("hu", "he"), ("lo", "NEG"), ("xayav", "must"), ("lehitpater", "resign")]
    glossedWords := [⟨[['\'', 'a', 'd', 'i', 'f']], [['p', 'r', 'e', 'f', 'e', 'r', 'a', 'b', 'l', 'e']]⟩, ⟨[['š', 'e'], ['h', 'u']], [['t', 'h', 'a', 't'], ['h', 'e']]⟩, ⟨[['y', 'i', 't', 'p', 'a', 't', 'e', 'r']], [['w', 'i', 'l', 'l', ' ', 'r', 'e', 's', 'i', 'g', 'n']]⟩, ⟨[['a', 'v', 'a', 'l']], [['b', 'u', 't']]⟩, ⟨[['h', 'u']], [['h', 'e']]⟩, ⟨[['l', 'o']], [['N', 'E', 'G']]⟩, ⟨[['x', 'a', 'y', 'a', 'v']], [['m', 'u', 's', 't']]⟩, ⟨[['l', 'e', 'h', 'i', 't', 'p', 'a', 't', 'e', 'r']], [['r', 'e', 's', 'i', 'g', 'n']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Bribe scenario; lexical comparison with a predicate of preference, 'adif 'preferable'."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "adif"), ("category", "evaluativeComparative"), ("strategy", "evaluativeComparative"), ("diagnostic", "test1")] }

def heb_kday : Datum :=
  { id := "rubinstein2014_heb_kday"
    source := ⟨"rubinstein-2014", "(21c)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "kday še-hu yitpater, aval hu lo xayav lehitpater."
    glossedTokens := [("kday", "worthwhile"), ("še-hu", "that-he"), ("yitpater", "will resign"), ("aval", "but"), ("hu", "he"), ("lo", "NEG"), ("xayav", "must"), ("lehitpater", "resign")]
    glossedWords := [⟨[['k', 'd', 'a', 'y']], [['w', 'o', 'r', 't', 'h', 'w', 'h', 'i', 'l', 'e']]⟩, ⟨[['š', 'e'], ['h', 'u']], [['t', 'h', 'a', 't'], ['h', 'e']]⟩, ⟨[['y', 'i', 't', 'p', 'a', 't', 'e', 'r']], [['w', 'i', 'l', 'l', ' ', 'r', 'e', 's', 'i', 'g', 'n']]⟩, ⟨[['a', 'v', 'a', 'l']], [['b', 'u', 't']]⟩, ⟨[['h', 'u']], [['h', 'e']]⟩, ⟨[['l', 'o']], [['N', 'E', 'G']]⟩, ⟨[['x', 'a', 'y', 'a', 'v']], [['m', 'u', 's', 't']]⟩, ⟨[['l', 'e', 'h', 'i', 't', 'p', 'a', 't', 'e', 'r']], [['r', 'e', 's', 'i', 'g', 'n']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Bribe scenario; implicit comparison with evaluative predicates kday 'worthwhile' / ra'uy 'fitting'."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "kday"), ("category", "evaluativeComparative"), ("strategy", "evaluativeComparative"), ("diagnostic", "test1")] }

def comp_better : Datum :=
  { id := "rubinstein2014_comp_better"
    source := ⟨"rubinstein-2014", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It would be better that the politician gets himself fired than that he keep working, but he really ought to quit voluntarily."
    glossedTokens := []
    context := "Three salient alternatives (get fired / keep working / resign). The morphological comparative pairwise-compares two of them."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "better"), ("category", "evaluativeComparative"), ("pairwise", "true")] }

def nr_carix : Datum :=
  { id := "rubinstein2014_nr_carix"
    source := ⟨"rubinstein-2014", "(57)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "ani lo xoševet še-ata carix lihyot po"
    glossedTokens := [("ani", "I"), ("lo", "NEG"), ("xoševet", "think.FSG"), ("še-ata", "that-you.MSG"), ("carix", "need.MSG"), ("lihyot", "be"), ("po", "here")]
    glossedWords := [⟨[['a', 'n', 'i']], [['I']]⟩, ⟨[['l', 'o']], [['N', 'E', 'G']]⟩, ⟨[['x', 'o', 'š', 'e', 'v', 'e', 't']], [['t', 'h', 'i', 'n', 'k', '.', 'F', 'S', 'G']]⟩, ⟨[['š', 'e'], ['a', 't', 'a']], [['t', 'h', 'a', 't'], ['y', 'o', 'u', '.', 'M', 'S', 'G']]⟩, ⟨[['c', 'a', 'r', 'i', 'x']], [['n', 'e', 'e', 'd', '.', 'M', 'S', 'G']]⟩, ⟨[['l', 'i', 'h', 'y', 'o', 't']], [['b', 'e']]⟩, ⟨[['p', 'o']], [['h', 'e', 'r', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := "The speaker tries to prevent someone from entering a meeting they are not invited to."
    judgment := .acceptable
    alternatives := []
    readings := [("lowerNeg", .acceptable)]
    paperFeatures := [("modal", "carix"), ("category", "modalVerb"), ("diagnostic", "negRaising"), ("hybrid", "true")] }

def all : List Datum := [nr_should, nr_ought, nr_better, nr_good, nr_must, nr_haveTo, nr_adif, ought_lexical, compositional_deberia, test1_carix, test2_carix, heb_yoter_tov, heb_adif, heb_kday, comp_better, nr_carix]

end Rubinstein2014.Examples
