module

public import Linglib.Data.Examples.Schema

/-!
# `Imanishi2014` — typed example data

Auto-generated from `Linglib/Data/Examples/Imanishi2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Imanishi2014.Examples`.
-/

@[expose] public section

namespace Imanishi2014.Examples

def s89 : Datum :=
  { id := "imanishi2014_s89"
    source := ⟨"imanishi-2014", "(89)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "i katastrofi tis polis apo tus varvarus mesa se tris meres"
    glossedTokens := [("i", "the"), ("katastrofi", "destruction"), ("tis", "the"), ("polis", "city-GEN"), ("apo", "by"), ("tus", "the"), ("varvarus", "barbarians"), ("mesa se", "within"), ("tris", "three"), ("meres", "days")]
    glossedWords := [⟨[['i']], [['t', 'h', 'e']]⟩, ⟨[['k', 'a', 't', 'a', 's', 't', 'r', 'o', 'f', 'i']], [['d', 'e', 's', 't', 'r', 'u', 'c', 't', 'i', 'o', 'n']]⟩, ⟨[['t', 'i', 's']], [['t', 'h', 'e']]⟩, ⟨[['p', 'o', 'l', 'i', 's']], [['c', 'i', 't', 'y'], ['G', 'E', 'N']]⟩, ⟨[['a', 'p', 'o']], [['b', 'y']]⟩, ⟨[['t', 'u', 's']], [['t', 'h', 'e']]⟩, ⟨[['v', 'a', 'r', 'v', 'a', 'r', 'u', 's']], [['b', 'a', 'r', 'b', 'a', 'r', 'i', 'a', 'n', 's']]⟩, ⟨[['m', 'e', 's', 'a', ' ', 's', 'e']], [['w', 'i', 't', 'h', 'i', 'n']]⟩, ⟨[['t', 'r', 'i', 's']], [['t', 'h', 'r', 'e', 'e']]⟩, ⟨[['m', 'e', 'r', 'e', 's']], [['d', 'a', 'y', 's']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.1"), ("source", "Alexiadou 2001:76"), ("nominalization", "external argument introduced by a preposition")] }

def s91 : Datum :=
  { id := "imanishi2014_s91"
    source := ⟨"imanishi-2014", "(91)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ri ru-k'at-ïk ri tinamït [ri x-ø-b'en ri a Juan] x-ø-xib'i-n."
    glossedTokens := [("ri", "DET"), ("ru-k'at-ïk", "ERG3S-burn-NOML"), ("ri", "DET"), ("tinamït", "city"), ("ri", "DET"), ("x-ø-b'en", "PRFV-ABS3S-do"), ("ri", "DET"), ("a", "CL"), ("Juan", "Juan"), ("x-ø-xib'i-n", "PRFV-ABS3S-scare-AP")]
    glossedWords := [⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['r', 'u'], ['k', '\'', 'a', 't'], ['ï', 'k']], [['E', 'R', 'G', '3', 'S'], ['b', 'u', 'r', 'n'], ['N', 'O', 'M', 'L']]⟩, ⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['t', 'i', 'n', 'a', 'm', 'ï', 't']], [['c', 'i', 't', 'y']]⟩, ⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['x'], ['ø'], ['b', '\'', 'e', 'n']], [['P', 'R', 'F', 'V'], ['A', 'B', 'S', '3', 'S'], ['d', 'o']]⟩, ⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['a']], [['C', 'L']]⟩, ⟨[['J', 'u', 'a', 'n']], [['J', 'u', 'a', 'n']]⟩, ⟨[['x'], ['ø'], ['x', 'i', 'b', '\'', 'i'], ['n']], [['P', 'R', 'F', 'V'], ['A', 'B', 'S', '3', 'S'], ['s', 'c', 'a', 'r', 'e'], ['A', 'P']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.1"), ("nominalization", "only the internal argument inside; the agent in a relative clause")] }

def s92 : Datum :=
  { id := "imanishi2014_s92"
    source := ⟨"imanishi-2014", "(92)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ru-k'at-ïk ri a Juan x-ø-xib'i-n."
    glossedTokens := [("ru-k'at-ïk", "ERG3S-burn-NOML"), ("ri", "DET"), ("a", "CL"), ("Juan", "Juan"), ("x-ø-xib'i-n", "PRFV-ABS3S-scare-AP")]
    glossedWords := [⟨[['r', 'u'], ['k', '\'', 'a', 't'], ['ï', 'k']], [['E', 'R', 'G', '3', 'S'], ['b', 'u', 'r', 'n'], ['N', 'O', 'M', 'L']]⟩, ⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['a']], [['C', 'L']]⟩, ⟨[['J', 'u', 'a', 'n']], [['J', 'u', 'a', 'n']]⟩, ⟨[['x'], ['ø'], ['x', 'i', 'b', '\'', 'i'], ['n']], [['P', 'R', 'F', 'V'], ['A', 'B', 'S', '3', 'S'], ['s', 'c', 'a', 'r', 'e'], ['A', 'P']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.1"), ("nominalization", "a sole argument is the internal argument")] }

def s93a : Datum :=
  { id := "imanishi2014_s93a"
    source := ⟨"imanishi-2014", "(93a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "y-in-ajin che [ki-k'ul-ïk ak'wal-a']."
    glossedTokens := [("y-in-ajin", "IMPF-ABS1S-PROG"), ("che", "PREP"), ("ki-k'ul-ïk", "ERG3P-meet.PAS-NOML"), ("ak'wal-a'", "child-PL")]
    glossedWords := [⟨[['y'], ['i', 'n'], ['a', 'j', 'i', 'n']], [['I', 'M', 'P', 'F'], ['A', 'B', 'S', '1', 'S'], ['P', 'R', 'O', 'G']]⟩, ⟨[['c', 'h', 'e']], [['P', 'R', 'E', 'P']]⟩, ⟨[['k', 'i'], ['k', '\'', 'u', 'l'], ['ï', 'k']], [['E', 'R', 'G', '3', 'P'], ['m', 'e', 'e', 't', '.', 'P', 'A', 'S'], ['N', 'O', 'M', 'L']]⟩, ⟨[['a', 'k', '\'', 'w', 'a', 'l'], ['a', '\'']], [['c', 'h', 'i', 'l', 'd'], ['P', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.1"), ("alignment", "S/A=ABS on ajin, O=ERG on the nominalized verb")] }

def s93b : Datum :=
  { id := "imanishi2014_s93b"
    source := ⟨"imanishi-2014", "(93b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "y-in-ajin che [atin-ïk]."
    glossedTokens := [("y-in-ajin", "IMPF-ABS1S-PROG"), ("che", "PREP"), ("atin-ïk", "bathe-NOML")]
    glossedWords := [⟨[['y'], ['i', 'n'], ['a', 'j', 'i', 'n']], [['I', 'M', 'P', 'F'], ['A', 'B', 'S', '1', 'S'], ['P', 'R', 'O', 'G']]⟩, ⟨[['c', 'h', 'e']], [['P', 'R', 'E', 'P']]⟩, ⟨[['a', 't', 'i', 'n'], ['ï', 'k']], [['b', 'a', 't', 'h', 'e'], ['N', 'O', 'M', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.1"), ("alignment", "S=ABS on ajin")] }

def s94a : Datum :=
  { id := "imanishi2014_s94a"
    source := ⟨"imanishi-2014", "(94a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "röj x-ø-qa-chäp [ki-k'ul-ïk rje']."
    glossedTokens := [("röj", "we"), ("x-ø-qa-chäp", "PRFV-ABS3S-ERG1P-begin"), ("ki-k'ul-ïk", "ERG3P-meet.PAS-NOML"), ("rje'", "they")]
    glossedWords := [⟨[['r', 'ö', 'j']], [['w', 'e']]⟩, ⟨[['x'], ['ø'], ['q', 'a'], ['c', 'h', 'ä', 'p']], [['P', 'R', 'F', 'V'], ['A', 'B', 'S', '3', 'S'], ['E', 'R', 'G', '1', 'P'], ['b', 'e', 'g', 'i', 'n']]⟩, ⟨[['k', 'i'], ['k', '\'', 'u', 'l'], ['ï', 'k']], [['E', 'R', 'G', '3', 'P'], ['m', 'e', 'e', 't', '.', 'P', 'A', 'S'], ['N', 'O', 'M', 'L']]⟩, ⟨[['r', 'j', 'e', '\'']], [['t', 'h', 'e', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.1"), ("construction", "embedding verb chäp 'begin'")] }

def s99b : Datum :=
  { id := "imanishi2014_s99b"
    source := ⟨"imanishi-2014", "(99b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "y-oj-ajin che ru-tik-ïk jun k'otz'i'j."
    glossedTokens := [("y-oj-ajin", "IMPF-ABS1P-PROG"), ("che", "PREP"), ("ru-tik-ïk", "ERG3S-plant.PAS-NOML"), ("jun", "one"), ("k'otz'i'j", "flower")]
    glossedWords := [⟨[['y'], ['o', 'j'], ['a', 'j', 'i', 'n']], [['I', 'M', 'P', 'F'], ['A', 'B', 'S', '1', 'P'], ['P', 'R', 'O', 'G']]⟩, ⟨[['c', 'h', 'e']], [['P', 'R', 'E', 'P']]⟩, ⟨[['r', 'u'], ['t', 'i', 'k'], ['ï', 'k']], [['E', 'R', 'G', '3', 'S'], ['p', 'l', 'a', 'n', 't', '.', 'P', 'A', 'S'], ['N', 'O', 'M', 'L']]⟩, ⟨[['j', 'u', 'n']], [['o', 'n', 'e']]⟩, ⟨[['k', '\'', 'o', 't', 'z', '\'', 'i', '\'', 'j']], [['f', 'l', 'o', 'w', 'e', 'r']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.1"), ("passivization", "tensed vowel of the root transitive under nominalization")] }

def s100b : Datum :=
  { id := "imanishi2014_s100b"
    source := ⟨"imanishi-2014", "(100b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "rje' y-e-ajin che ru-tuk-ïk sopa."
    glossedTokens := [("rje'", "they"), ("y-e-ajin", "IMPF-ABS3P-PROG"), ("che", "PREP"), ("ru-tuk-ïk", "ERG3S-stir.PAS-NOML"), ("sopa", "soup")]
    glossedWords := [⟨[['r', 'j', 'e', '\'']], [['t', 'h', 'e', 'y']]⟩, ⟨[['y'], ['e'], ['a', 'j', 'i', 'n']], [['I', 'M', 'P', 'F'], ['A', 'B', 'S', '3', 'P'], ['P', 'R', 'O', 'G']]⟩, ⟨[['c', 'h', 'e']], [['P', 'R', 'E', 'P']]⟩, ⟨[['r', 'u'], ['t', 'u', 'k'], ['ï', 'k']], [['E', 'R', 'G', '3', 'S'], ['s', 't', 'i', 'r', '.', 'P', 'A', 'S'], ['N', 'O', 'M', 'L']]⟩, ⟨[['s', 'o', 'p', 'a']], [['s', 'o', 'u', 'p']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.1"), ("passivization", "tensed vowel of the root transitive under nominalization")] }

def s102b : Datum :=
  { id := "imanishi2014_s102b"
    source := ⟨"imanishi-2014", "(102b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "röj y-oj-ajin che ki-q'ete-x-ïk ri ak'wal-a'."
    glossedTokens := [("röj", "we"), ("y-oj-ajin", "IMPF-ABS1P-PROG"), ("che", "PREP"), ("ki-q'ete-x-ïk", "ERG3P-hug-PAS-NOML"), ("ri", "DET"), ("ak'wal-a'", "child-PL")]
    glossedWords := [⟨[['r', 'ö', 'j']], [['w', 'e']]⟩, ⟨[['y'], ['o', 'j'], ['a', 'j', 'i', 'n']], [['I', 'M', 'P', 'F'], ['A', 'B', 'S', '1', 'P'], ['P', 'R', 'O', 'G']]⟩, ⟨[['c', 'h', 'e']], [['P', 'R', 'E', 'P']]⟩, ⟨[['k', 'i'], ['q', '\'', 'e', 't', 'e'], ['x'], ['ï', 'k']], [['E', 'R', 'G', '3', 'P'], ['h', 'u', 'g'], ['P', 'A', 'S'], ['N', 'O', 'M', 'L']]⟩, ⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['a', 'k', '\'', 'w', 'a', 'l'], ['a', '\'']], [['c', 'h', 'i', 'l', 'd'], ['P', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.1"), ("passivization", "the passive suffix -x on the derived transitive under nominalization")] }

def s137a : Datum :=
  { id := "imanishi2014_s137a"
    source := ⟨"imanishi-2014", "(137a)"⟩
    reportedIn := none
    language := "chol1282"
    primaryText := "Choñkol-ø [i-jats'-oñ]."
    glossedTokens := [("Choñkol-ø", "PROG-ABS3S"), ("i-jats'-oñ", "ERG3S-hit-ABS1S")]
    glossedWords := [⟨[['C', 'h', 'o', 'ñ', 'k', 'o', 'l'], ['ø']], [['P', 'R', 'O', 'G'], ['A', 'B', 'S', '3', 'S']]⟩, ⟨[['i'], ['j', 'a', 't', 's', '\''], ['o', 'ñ']], [['E', 'R', 'G', '3', 'S'], ['h', 'i', 't'], ['A', 'B', 'S', '1', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.3"), ("source", "Coon 2013a:11"), ("alignment", "A=ERG, O=ABS inside the nominalized clause")] }

def s137b : Datum :=
  { id := "imanishi2014_s137b"
    source := ⟨"imanishi-2014", "(137b)"⟩
    reportedIn := none
    language := "chol1282"
    primaryText := "Choñkol-ø [i-majl-el]."
    glossedTokens := [("Choñkol-ø", "PROG-ABS3S"), ("i-majl-el", "ERG3S-go-NOML")]
    glossedWords := [⟨[['C', 'h', 'o', 'ñ', 'k', 'o', 'l'], ['ø']], [['P', 'R', 'O', 'G'], ['A', 'B', 'S', '3', 'S']]⟩, ⟨[['i'], ['m', 'a', 'j', 'l'], ['e', 'l']], [['E', 'R', 'G', '3', 'S'], ['g', 'o'], ['N', 'O', 'M', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.3"), ("source", "Coon 2013a:11"), ("alignment", "S=ERG")] }

def s138a : Datum :=
  { id := "imanishi2014_s138a"
    source := ⟨"imanishi-2014", "(138a)"⟩
    reportedIn := none
    language := "qanj1241"
    primaryText := "lanan-ø [hach w-il-on-i]."
    glossedTokens := [("lanan-ø", "PROG-ABS3S"), ("hach", "ABS2S"), ("w-il-on-i", "ERG1S-see-DM-ITV")]
    glossedWords := [⟨[['l', 'a', 'n', 'a', 'n'], ['ø']], [['P', 'R', 'O', 'G'], ['A', 'B', 'S', '3', 'S']]⟩, ⟨[['h', 'a', 'c', 'h']], [['A', 'B', 'S', '2', 'S']]⟩, ⟨[['w'], ['i', 'l'], ['o', 'n'], ['i']], [['E', 'R', 'G', '1', 'S'], ['s', 'e', 'e'], ['D', 'M'], ['I', 'T', 'V']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.3"), ("source", "Mateo Pedro 2009"), ("alignment", "A=ERG, O=ABS, the suffix -on supplying object Case")] }

def s138b : Datum :=
  { id := "imanishi2014_s138b"
    source := ⟨"imanishi-2014", "(138b)"⟩
    reportedIn := none
    language := "qanj1241"
    primaryText := "lanan-ø [ha-way-i]."
    glossedTokens := [("lanan-ø", "PROG-ABS3S"), ("ha-way-i", "ERG2S-sleep-ITV")]
    glossedWords := [⟨[['l', 'a', 'n', 'a', 'n'], ['ø']], [['P', 'R', 'O', 'G'], ['A', 'B', 'S', '3', 'S']]⟩, ⟨[['h', 'a'], ['w', 'a', 'y'], ['i']], [['E', 'R', 'G', '2', 'S'], ['s', 'l', 'e', 'e', 'p'], ['I', 'T', 'V']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.3"), ("source", "Mateo Pedro 2009"), ("alignment", "S=ERG")] }

def s181 : Datum :=
  { id := "imanishi2014_s181"
    source := ⟨"imanishi-2014", "(181)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "at-ø txab'an siich' ok q-ook-a juu7n priim."
    glossedTokens := [("at-ø", "LOC-ABS3S"), ("txab'an", "bit"), ("siich'", "cigarette"), ("ok", "when"), ("q-ook-a", "ERG1P-enter-1P"), ("juu7n", "each"), ("priim", "early")]
    glossedWords := [⟨[['a', 't'], ['ø']], [['L', 'O', 'C'], ['A', 'B', 'S', '3', 'S']]⟩, ⟨[['t', 'x', 'a', 'b', '\'', 'a', 'n']], [['b', 'i', 't']]⟩, ⟨[['s', 'i', 'i', 'c', 'h', '\'']], [['c', 'i', 'g', 'a', 'r', 'e', 't', 't', 'e']]⟩, ⟨[['o', 'k']], [['w', 'h', 'e', 'n']]⟩, ⟨[['q'], ['o', 'o', 'k'], ['a']], [['E', 'R', 'G', '1', 'P'], ['e', 'n', 't', 'e', 'r'], ['1', 'P']]⟩, ⟨[['j', 'u', 'u', '7', 'n']], [['e', 'a', 'c', 'h']]⟩, ⟨[['p', 'r', 'i', 'i', 'm']], [['e', 'a', 'r', 'l', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.4"), ("source", "England 1983b:265"), ("alignment", "S=ERG in an aspectless temporal clause")] }

def s182 : Datum :=
  { id := "imanishi2014_s182"
    source := ⟨"imanishi-2014", "(182)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "ok qo tzaalaj-al ok t-q-il u7j t-e yool t-e l7tzal"
    glossedTokens := [("ok", "POT"), ("qo", "ABS1P"), ("tzaalaj-al", "be.happy-POT"), ("ok", "when"), ("t-q-il", "ERG3S-ERG1P-see"), ("u7j", "book"), ("t-e", "ERG3S-RN"), ("yool", "word"), ("t-e", "ERG3S-RN"), ("l7tzal", "Ixtahuacán")]
    glossedWords := [⟨[['o', 'k']], [['P', 'O', 'T']]⟩, ⟨[['q', 'o']], [['A', 'B', 'S', '1', 'P']]⟩, ⟨[['t', 'z', 'a', 'a', 'l', 'a', 'j'], ['a', 'l']], [['b', 'e', '.', 'h', 'a', 'p', 'p', 'y'], ['P', 'O', 'T']]⟩, ⟨[['o', 'k']], [['w', 'h', 'e', 'n']]⟩, ⟨[['t'], ['q'], ['i', 'l']], [['E', 'R', 'G', '3', 'S'], ['E', 'R', 'G', '1', 'P'], ['s', 'e', 'e']]⟩, ⟨[['u', '7', 'j']], [['b', 'o', 'o', 'k']]⟩, ⟨[['t'], ['e']], [['E', 'R', 'G', '3', 'S'], ['R', 'N']]⟩, ⟨[['y', 'o', 'o', 'l']], [['w', 'o', 'r', 'd']]⟩, ⟨[['t'], ['e']], [['E', 'R', 'G', '3', 'S'], ['R', 'N']]⟩, ⟨[['l', '7', 't', 'z', 'a', 'l']], [['I', 'x', 't', 'a', 'h', 'u', 'a', 'c', 'á', 'n']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.4"), ("source", "England 1983b:260"), ("alignment", "double ergative: A and O both ERG")] }

def t178_kaqchikel : Datum :=
  { id := "imanishi2014_t178_kaqchikel"
    source := ⟨"imanishi-2014", "(178)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Kaqchikel: non-perfective alignment S/A=ABS, O=ERG"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.3"), ("absolutive", "high"), ("urn", "+"), ("alignment", "S/A=ABS, O=ERG")] }

def t178_tojolabal : Datum :=
  { id := "imanishi2014_t178_tojolabal"
    source := ⟨"imanishi-2014", "(178)"⟩
    reportedIn := none
    language := "tojo1241"
    primaryText := "Tojolabal: non-perfective alignment S/A=ABS, O=ERG"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.3"), ("absolutive", "low"), ("urn", "+"), ("alignment", "S/A=ABS, O=ERG")] }

def t178_chol : Datum :=
  { id := "imanishi2014_t178_chol"
    source := ⟨"imanishi-2014", "(178)"⟩
    reportedIn := none
    language := "chol1282"
    primaryText := "Chol: non-perfective alignment S/A=ERG, O=ABS"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.3"), ("absolutive", "low"), ("urn", "-"), ("alignment", "S/A=ERG, O=ABS")] }

def t178_qanjobal : Datum :=
  { id := "imanishi2014_t178_qanjobal"
    source := ⟨"imanishi-2014", "(178)"⟩
    reportedIn := none
    language := "qanj1241"
    primaryText := "Q'anjob'al: non-perfective alignment S/A=ERG, O=ABS"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.3"), ("absolutive", "high"), ("urn", "-"), ("alignment", "S/A=ERG, O=ABS")] }

def t178_chuj : Datum :=
  { id := "imanishi2014_t178_chuj"
    source := ⟨"imanishi-2014", "(178)"⟩
    reportedIn := none
    language := "chuj1250"
    primaryText := "Chuj: non-perfective alignment S/A=ERG, O=ABS"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.3"), ("absolutive", "high"), ("urn", "-"), ("alignment", "S/A=ERG, O=ABS")] }

def t178_ixil : Datum :=
  { id := "imanishi2014_t178_ixil"
    source := ⟨"imanishi-2014", "(178)"⟩
    reportedIn := none
    language := "ixil1251"
    primaryText := "Ixil: non-perfective alignment S/A=ERG, O=ABS"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.3"), ("absolutive", "low"), ("urn", "-"), ("alignment", "S/A=ERG, O=ABS")] }

def t178_yucatec : Datum :=
  { id := "imanishi2014_t178_yucatec"
    source := ⟨"imanishi-2014", "(178)"⟩
    reportedIn := none
    language := "yuca1254"
    primaryText := "Yucatec: non-perfective alignment S/A=ERG, O=ABS"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.3"), ("absolutive", "low"), ("urn", "-"), ("alignment", "S/A=ERG, O=ABS")] }

def all : List Datum := [s89, s91, s92, s93a, s93b, s94a, s99b, s100b, s102b, s137a, s137b, s138a, s138b, s181, s182, t178_kaqchikel, t178_tojolabal, t178_chol, t178_qanjobal, t178_chuj, t178_ixil, t178_yucatec]

end Imanishi2014.Examples
