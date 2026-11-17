module

public import Linglib.Data.Examples.Schema

/-!
# `IoninMatushansky2006` — typed example data

Auto-generated from `Linglib/Data/Examples/IoninMatushansky2006.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace IoninMatushansky2006.Examples`.
-/

@[expose] public section

namespace IoninMatushansky2006.Examples

def s1a : Datum :=
  { id := "ioninmatushansky2006_s1a"
    source := ⟨"ionin-matushansky-2006", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "five hundred thousand"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("operation", "multiplication")] }

def s1b : Datum :=
  { id := "ioninmatushansky2006_s1b"
    source := ⟨"ionin-matushansky-2006", "(1b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "quatre vingt"
    glossedTokens := [("quatre", "four"), ("vingt", "twenty")]
    glossedWords := [⟨['q', 'u', 'a', 't', 'r', 'e'], ['f', 'o', 'u', 'r'], [⟨['q', 'u', 'a', 't', 'r', 'e'], ['f', 'o', 'u', 'r'], none⟩]⟩, ⟨['v', 'i', 'n', 'g', 't'], ['t', 'w', 'e', 'n', 't', 'y'], [⟨['v', 'i', 'n', 'g', 't'], ['t', 'w', 'e', 'n', 't', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("operation", "multiplication")] }

def s2a : Datum :=
  { id := "ioninmatushansky2006_s2a"
    source := ⟨"ionin-matushansky-2006", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "three hundred and five"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("operation", "addition")] }

def s2b : Datum :=
  { id := "ioninmatushansky2006_s2b"
    source := ⟨"ionin-matushansky-2006", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "twenty-seven"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("operation", "addition")] }

def s2c : Datum :=
  { id := "ioninmatushansky2006_s2c"
    source := ⟨"ionin-matushansky-2006", "(2c)"⟩
    reportedIn := none
    language := "wels1247"
    primaryText := "tri ar ddeg"
    glossedTokens := [("tri", "three"), ("ar", "on"), ("ddeg", "ten")]
    glossedWords := [⟨['t', 'r', 'i'], ['t', 'h', 'r', 'e', 'e'], [⟨['t', 'r', 'i'], ['t', 'h', 'r', 'e', 'e'], none⟩]⟩, ⟨['a', 'r'], ['o', 'n'], [⟨['a', 'r'], ['o', 'n'], none⟩]⟩, ⟨['d', 'd', 'e', 'g'], ['t', 'e', 'n'], [⟨['d', 'd', 'e', 'g'], ['t', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("source", "Hurford 2003"), ("operation", "addition")] }

def s3a : Datum :=
  { id := "ioninmatushansky2006_s3a"
    source := ⟨"ionin-matushansky-2006", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "four hundred books"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2"), ("claim", "the same four as in four books")] }

def s3b : Datum :=
  { id := "ioninmatushansky2006_s3b"
    source := ⟨"ionin-matushansky-2006", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "four books"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2"), ("claim", "the same four as in four hundred books")] }

def s14 : Datum :=
  { id := "ioninmatushansky2006_s14"
    source := ⟨"ionin-matushansky-2006", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the two birds / every two birds / those two birds"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.3"), ("claim", "cardinals combine with determiners, so are not determiners")] }

def s20 : Datum :=
  { id := "ioninmatushansky2006_s20"
    source := ⟨"ionin-matushansky-2006", "(20)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Yhdeksän omena-a puto-si maa-han."
    glossedTokens := [("Yhdeksän", "nine-NOM"), ("omena-a", "apple-PART.SG"), ("puto-si", "fall-PAST.3SG"), ("maa-han", "earth-ILL")]
    glossedWords := [⟨['Y', 'h', 'd', 'e', 'k', 's', 'ä', 'n'], ['n', 'i', 'n', 'e', '-', 'N', 'O', 'M'], []⟩, ⟨['o', 'm', 'e', 'n', 'a', '-', 'a'], ['a', 'p', 'p', 'l', 'e', '-', 'P', 'A', 'R', 'T', '.', 'S', 'G'], [⟨['o', 'm', 'e', 'n', 'a'], ['a', 'p', 'p', 'l', 'e'], none⟩, ⟨['a'], ['P', 'A', 'R', 'T', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['p', 'u', 't', 'o', '-', 's', 'i'], ['f', 'a', 'l', 'l', '-', 'P', 'A', 'S', 'T', '.', '3', 'S', 'G'], [⟨['p', 'u', 't', 'o'], ['f', 'a', 'l', 'l'], none⟩, ⟨['s', 'i'], ['P', 'A', 'S', 'T', '.', '3', 'S', 'G'], some '-'⟩]⟩, ⟨['m', 'a', 'a', '-', 'h', 'a', 'n'], ['e', 'a', 'r', 't', 'h', '-', 'I', 'L', 'L'], [⟨['m', 'a', 'a'], ['e', 'a', 'r', 't', 'h'], none⟩, ⟨['h', 'a', 'n'], ['I', 'L', 'L'], some '-'⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("source", "Nelson and Toivonen 2000"), ("claim", "the lexical xNP is morphologically singular")] }

def s21 : Datum :=
  { id := "ioninmatushansky2006_s21"
    source := ⟨"ionin-matushansky-2006", "(21)"⟩
    reportedIn := none
    language := "wels1247"
    primaryText := "y tair cath ddu hynny"
    glossedTokens := [("y", "the.PL"), ("tair", "three.F"), ("cath", "cat.F.SG"), ("ddu", "black.SG"), ("hynny", "that.PL")]
    glossedWords := [⟨['y'], ['t', 'h', 'e', '.', 'P', 'L'], [⟨['y'], ['t', 'h', 'e', '.', 'P', 'L'], none⟩]⟩, ⟨['t', 'a', 'i', 'r'], ['t', 'h', 'r', 'e', 'e', '.', 'F'], [⟨['t', 'a', 'i', 'r'], ['t', 'h', 'r', 'e', 'e', '.', 'F'], none⟩]⟩, ⟨['c', 'a', 't', 'h'], ['c', 'a', 't', '.', 'F', '.', 'S', 'G'], [⟨['c', 'a', 't', 'h'], ['c', 'a', 't', '.', 'F', '.', 'S', 'G'], none⟩]⟩, ⟨['d', 'd', 'u'], ['b', 'l', 'a', 'c', 'k', '.', 'S', 'G'], [⟨['d', 'd', 'u'], ['b', 'l', 'a', 'c', 'k', '.', 'S', 'G'], none⟩]⟩, ⟨['h', 'y', 'n', 'n', 'y'], ['t', 'h', 'a', 't', '.', 'P', 'L'], [⟨['h', 'y', 'n', 'n', 'y'], ['t', 'h', 'a', 't', '.', 'P', 'L'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("source", "Mittendorf and Sadler 2005"), ("claim", "the lexical xNP is morphologically singular")] }

def s24a : Datum :=
  { id := "ioninmatushansky2006_s24a"
    source := ⟨"ionin-matushansky-2006", "(24a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There are 17 people and chairs in this room."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("claim", "counting dissimilar entities is odd")] }

def s24b : Datum :=
  { id := "ioninmatushansky2006_s24b"
    source := ⟨"ionin-matushansky-2006", "(24b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There are 17 women and children in this room."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("claim", "rescued by the shared property of being human")] }

def s26a : Datum :=
  { id := "ioninmatushansky2006_s26a"
    source := ⟨"ionin-matushansky-2006", "(26a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "two dozen(*s) books"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("claim", "plural marking on a multiple")] }

def s26b : Datum :=
  { id := "ioninmatushansky2006_s26b"
    source := ⟨"ionin-matushansky-2006", "(26b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "three hundred(*s) people"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("claim", "plural marking on a multiple")] }

def s26c : Datum :=
  { id := "ioninmatushansky2006_s26c"
    source := ⟨"ionin-matushansky-2006", "(26c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "four score(*s) and seven years ago"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("claim", "plural marking on a multiple")] }

def s27a : Datum :=
  { id := "ioninmatushansky2006_s27a"
    source := ⟨"ionin-matushansky-2006", "(27a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "drie liter water"
    glossedTokens := [("drie", "three"), ("liter", "liter"), ("water", "water")]
    glossedWords := [⟨['d', 'r', 'i', 'e'], ['t', 'h', 'r', 'e', 'e'], [⟨['d', 'r', 'i', 'e'], ['t', 'h', 'r', 'e', 'e'], none⟩]⟩, ⟨['l', 'i', 't', 'e', 'r'], ['l', 'i', 't', 'e', 'r'], [⟨['l', 'i', 't', 'e', 'r'], ['l', 'i', 't', 'e', 'r'], none⟩]⟩, ⟨['w', 'a', 't', 'e', 'r'], ['w', 'a', 't', 'e', 'r'], [⟨['w', 'a', 't', 'e', 'r'], ['w', 'a', 't', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("claim", "measure noun singular")] }

def s27b : Datum :=
  { id := "ioninmatushansky2006_s27b"
    source := ⟨"ionin-matushansky-2006", "(27b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "driehonderd meisjes"
    glossedTokens := [("driehonderd", "three.hundred"), ("meisjes", "girls")]
    glossedWords := [⟨['d', 'r', 'i', 'e', 'h', 'o', 'n', 'd', 'e', 'r', 'd'], ['t', 'h', 'r', 'e', 'e', '.', 'h', 'u', 'n', 'd', 'r', 'e', 'd'], [⟨['d', 'r', 'i', 'e', 'h', 'o', 'n', 'd', 'e', 'r', 'd'], ['t', 'h', 'r', 'e', 'e', '.', 'h', 'u', 'n', 'd', 'r', 'e', 'd'], none⟩]⟩, ⟨['m', 'e', 'i', 's', 'j', 'e', 's'], ['g', 'i', 'r', 'l', 's'], [⟨['m', 'e', 'i', 's', 'j', 'e', 's'], ['g', 'i', 'r', 'l', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("claim", "cardinal singular")] }

def s28 : Datum :=
  { id := "ioninmatushansky2006_s28"
    source := ⟨"ionin-matushansky-2006", "(28)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "dvadcat' millionov knig"
    glossedTokens := [("dvadcat'", "twenty-NOM"), ("millionov", "million-GEN.PL"), ("knig", "book-GEN.PL")]
    glossedWords := [⟨['d', 'v', 'a', 'd', 'c', 'a', 't', '\''], ['t', 'w', 'e', 'n', 't', 'y', '-', 'N', 'O', 'M'], []⟩, ⟨['m', 'i', 'l', 'l', 'i', 'o', 'n', 'o', 'v'], ['m', 'i', 'l', 'l', 'i', 'o', 'n', '-', 'G', 'E', 'N', '.', 'P', 'L'], []⟩, ⟨['k', 'n', 'i', 'g'], ['b', 'o', 'o', 'k', '-', 'G', 'E', 'N', '.', 'P', 'L'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("claim", "semantic concord throughout in Russian")] }

def s37a : Datum :=
  { id := "ioninmatushansky2006_s37a"
    source := ⟨"ionin-matushansky-2006", "(37a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "two twenty"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.4"), ("claim", "overgeneration: only multiples serve as complements")] }

def s37b : Datum :=
  { id := "ioninmatushansky2006_s37b"
    source := ⟨"ionin-matushansky-2006", "(37b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "two [seventy five]"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.4"), ("claim", "overgeneration: only multiples serve as complements")] }

def s38a : Datum :=
  { id := "ioninmatushansky2006_s38a"
    source := ⟨"ionin-matushansky-2006", "(38a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "one hundred and two"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4"), ("operation", "coordination as addition")] }

def s38b : Datum :=
  { id := "ioninmatushansky2006_s38b"
    source := ⟨"ionin-matushansky-2006", "(38b)"⟩
    reportedIn := none
    language := "soma1255"
    primaryText := "laba iyo toban"
    glossedTokens := [("laba", "two"), ("iyo", "CONJ"), ("toban", "ten")]
    glossedWords := [⟨['l', 'a', 'b', 'a'], ['t', 'w', 'o'], [⟨['l', 'a', 'b', 'a'], ['t', 'w', 'o'], none⟩]⟩, ⟨['i', 'y', 'o'], ['C', 'O', 'N', 'J'], [⟨['i', 'y', 'o'], ['C', 'O', 'N', 'J'], none⟩]⟩, ⟨['t', 'o', 'b', 'a', 'n'], ['t', 'e', 'n'], [⟨['t', 'o', 'b', 'a', 'n'], ['t', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4"), ("source", "Saeed 1999"), ("operation", "coordination as addition")] }

def s38c : Datum :=
  { id := "ioninmatushansky2006_s38c"
    source := ⟨"ionin-matushansky-2006", "(38c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "seven and two thirds"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4"), ("operation", "coordination as addition")] }

def s45 : Datum :=
  { id := "ioninmatushansky2006_s45"
    source := ⟨"ionin-matushansky-2006", "(45)"⟩
    reportedIn := none
    language := "wels1247"
    primaryText := "onid un mlwydd cant"
    glossedTokens := [("onid", "but"), ("un", "one"), ("mlwydd", "years"), ("cant", "hundred")]
    glossedWords := [⟨['o', 'n', 'i', 'd'], ['b', 'u', 't'], [⟨['o', 'n', 'i', 'd'], ['b', 'u', 't'], none⟩]⟩, ⟨['u', 'n'], ['o', 'n', 'e'], [⟨['u', 'n'], ['o', 'n', 'e'], none⟩]⟩, ⟨['m', 'l', 'w', 'y', 'd', 'd'], ['y', 'e', 'a', 'r', 's'], [⟨['m', 'l', 'w', 'y', 'd', 'd'], ['y', 'e', 'a', 'r', 's'], none⟩]⟩, ⟨['c', 'a', 'n', 't'], ['h', 'u', 'n', 'd', 'r', 'e', 'd'], [⟨['c', 'a', 'n', 't'], ['h', 'u', 'n', 'd', 'r', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.1"), ("source", "Hurford 1975:198"), ("claim", "the lexical xNP inside the complex cardinal; subtraction by a preposition")] }

def s53a : Datum :=
  { id := "ioninmatushansky2006_s53a"
    source := ⟨"ionin-matushansky-2006", "(53a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The books are old and new."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.2"), ("claim", "split reading of coordinated plural predicates")] }

def s53b : Datum :=
  { id := "ioninmatushansky2006_s53b"
    source := ⟨"ionin-matushansky-2006", "(53b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "These men and women met in the park."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.2"), ("claim", "full split reading")] }

def s54 : Datum :=
  { id := "ioninmatushansky2006_s54"
    source := ⟨"ionin-matushansky-2006", "(54)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "His friends and colleagues came to the party."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.2"), ("readings", "joint: each a friend and a colleague; split: each a friend or a colleague")] }

def s56 : Datum :=
  { id := "ioninmatushansky2006_s56"
    source := ⟨"ionin-matushansky-2006", "(56)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Twenty-two people came to the party."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.2.1"), ("readings", "joint (56a) absent; split (56b) must be a full split")] }

def s57a : Datum :=
  { id := "ioninmatushansky2006_s57a"
    source := ⟨"ionin-matushansky-2006", "(57a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Twenty people and two people came to the party."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.2.1"), ("claim", "no overlap in the overt coordination")] }

def s57b : Datum :=
  { id := "ioninmatushansky2006_s57b"
    source := ⟨"ionin-matushansky-2006", "(57b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Twenty professors and seven deans came to the party."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.2.1"), ("claim", "no overlap with different lexical xNPs")] }

def s57c : Datum :=
  { id := "ioninmatushansky2006_s57c"
    source := ⟨"ionin-matushansky-2006", "(57c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All professors and several deans came to the party."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.2.1"), ("claim", "no overlap without cardinals")] }

def s58a : Datum :=
  { id := "ioninmatushansky2006_s58a"
    source := ⟨"ionin-matushansky-2006", "(58a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I bought six feet (and) six inches of finest silk."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.2.1"), ("claim", "no overlap in measurements")] }

def s58b : Datum :=
  { id := "ioninmatushansky2006_s58b"
    source := ⟨"ionin-matushansky-2006", "(58b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This cost five dollars (and) seventy-five cents."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.2.1"), ("claim", "no overlap in money")] }

def s59 : Datum :=
  { id := "ioninmatushansky2006_s59"
    source := ⟨"ionin-matushansky-2006", "(59)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She only had an apple and dessert."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.2.1"), ("source", "Hofweber 2005"), ("claim", "and as 'in addition to' outside cardinals")] }

def s61a : Datum :=
  { id := "ioninmatushansky2006_s61a"
    source := ⟨"ionin-matushansky-2006", "(61a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Each applicant is required to meet with three professors from linguistics and two professors from psychology."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.2.2"), ("claim", "overlap available: joint appointments may count twice")] }

def s61b : Datum :=
  { id := "ioninmatushansky2006_s61b"
    source := ⟨"ionin-matushansky-2006", "(61b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We need ten professors and five deans for a quorum."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.2.2"), ("claim", "overlap available: five deans may be among the ten professors")] }

def s63 : Datum :=
  { id := "ioninmatushansky2006_s63"
    source := ⟨"ionin-matushansky-2006", "(63)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We need twenty books and two books."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.2.2"), ("claim", "marginal overlap under different implicit restrictions, with stress on the conjunction")] }

def s72a : Datum :=
  { id := "ioninmatushansky2006_s72a"
    source := ⟨"ionin-matushansky-2006", "(72a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Two and two is four."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "Appendix 2"), ("claim", "cardinals as arguments in arithmetic")] }

def s74a : Datum :=
  { id := "ioninmatushansky2006_s74a"
    source := ⟨"ionin-matushansky-2006", "(74a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The number of moons of Jupiter is four."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "Appendix 2"), ("claim", "cardinal as singular term")] }

def s74b : Datum :=
  { id := "ioninmatushansky2006_s74b"
    source := ⟨"ionin-matushansky-2006", "(74b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jupiter has four moons."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "Appendix 2"), ("claim", "xNP-internal cardinal, the basic use")] }

def s75c : Datum :=
  { id := "ioninmatushansky2006_s75c"
    source := ⟨"ionin-matushansky-2006", "(75c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Two and two are four."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "Appendix 2"), ("source", "Hofweber 2005"), ("claim", "plural agreement: implicit quantification over an elided xNP")] }

def all : List Datum := [s1a, s1b, s2a, s2b, s2c, s3a, s3b, s14, s20, s21, s24a, s24b, s26a, s26b, s26c, s27a, s27b, s28, s37a, s37b, s38a, s38b, s38c, s45, s53a, s53b, s54, s56, s57a, s57b, s57c, s58a, s58b, s59, s61a, s61b, s63, s72a, s74a, s74b, s75c]

end IoninMatushansky2006.Examples
