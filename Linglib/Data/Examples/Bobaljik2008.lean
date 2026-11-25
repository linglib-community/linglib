module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Bobaljik2008` — typed example data

Auto-generated from `Linglib/Data/Examples/Bobaljik2008.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Bobaljik2008.Examples`.
-/

@[expose] public section

namespace Bobaljik2008.Examples

def ex_24a : Datum :=
  { id := "bobaljik2008_24a"
    source := ⟨"bickel-yadava-2000", "(5a)"⟩
    reportedIn := some ⟨"bobaljik-2008", "(24a)"⟩
    language := "nepa1254"
    primaryText := "ma yas pasal-mā patrikā kin-ch-u."
    glossedTokens := [("ma", "1sNOM"), ("yas", "DEM:OBL"), ("pasal-mā", "store-LOC"), ("patrikā", "newspaper:NOM"), ("kin-ch-u.", "buy-NPT-1s")]
    glossedWords := [⟨['m', 'a'], ['1', 's', 'N', 'O', 'M'], [⟨['m', 'a'], ['1', 's', 'N', 'O', 'M'], none⟩]⟩, ⟨['y', 'a', 's'], ['D', 'E', 'M', ':', 'O', 'B', 'L'], [⟨['y', 'a', 's'], ['D', 'E', 'M', ':', 'O', 'B', 'L'], none⟩]⟩, ⟨['p', 'a', 's', 'a', 'l', '-', 'm', 'ā'], ['s', 't', 'o', 'r', 'e', '-', 'L', 'O', 'C'], [⟨['p', 'a', 's', 'a', 'l'], ['s', 't', 'o', 'r', 'e'], none⟩, ⟨['m', 'ā'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['p', 'a', 't', 'r', 'i', 'k', 'ā'], ['n', 'e', 'w', 's', 'p', 'a', 'p', 'e', 'r', ':', 'N', 'O', 'M'], [⟨['p', 'a', 't', 'r', 'i', 'k', 'ā'], ['n', 'e', 'w', 's', 'p', 'a', 'p', 'e', 'r', ':', 'N', 'O', 'M'], none⟩]⟩, ⟨['k', 'i', 'n', '-', 'c', 'h', '-', 'u', '.'], ['b', 'u', 'y', '-', 'N', 'P', 'T', '-', '1', 's'], [⟨['k', 'i', 'n'], ['b', 'u', 'y'], none⟩, ⟨['c', 'h'], ['N', 'P', 'T'], some '-'⟩, ⟨['u'], ['1', 's'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "nominativeSubject"), ("controller", "subject")] }

def ex_24b : Datum :=
  { id := "bobaljik2008_24b"
    source := ⟨"bickel-yadava-2000", "(5b)"⟩
    reportedIn := some ⟨"bobaljik-2008", "(24b)"⟩
    language := "nepa1254"
    primaryText := "maile yas pasal-mā patrikā kin-ẽ."
    glossedTokens := [("maile", "1sERG"), ("yas", "DEM:OBL"), ("pasal-mā", "store-LOC"), ("patrikā", "newspaper:NOM"), ("kin-ẽ.", "buy-PT1s")]
    glossedWords := [⟨['m', 'a', 'i', 'l', 'e'], ['1', 's', 'E', 'R', 'G'], [⟨['m', 'a', 'i', 'l', 'e'], ['1', 's', 'E', 'R', 'G'], none⟩]⟩, ⟨['y', 'a', 's'], ['D', 'E', 'M', ':', 'O', 'B', 'L'], [⟨['y', 'a', 's'], ['D', 'E', 'M', ':', 'O', 'B', 'L'], none⟩]⟩, ⟨['p', 'a', 's', 'a', 'l', '-', 'm', 'ā'], ['s', 't', 'o', 'r', 'e', '-', 'L', 'O', 'C'], [⟨['p', 'a', 's', 'a', 'l'], ['s', 't', 'o', 'r', 'e'], none⟩, ⟨['m', 'ā'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['p', 'a', 't', 'r', 'i', 'k', 'ā'], ['n', 'e', 'w', 's', 'p', 'a', 'p', 'e', 'r', ':', 'N', 'O', 'M'], [⟨['p', 'a', 't', 'r', 'i', 'k', 'ā'], ['n', 'e', 'w', 's', 'p', 'a', 'p', 'e', 'r', ':', 'N', 'O', 'M'], none⟩]⟩, ⟨['k', 'i', 'n', '-', 'ẽ', '.'], ['b', 'u', 'y', '-', 'P', 'T', '1', 's'], [⟨['k', 'i', 'n'], ['b', 'u', 'y'], none⟩, ⟨['ẽ'], ['P', 'T', '1', 's'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "ergativeSubject"), ("controller", "subject")] }

def ex_24b_object : Datum :=
  { id := "bobaljik2008_24b_object"
    source := ⟨"bickel-yadava-2000", "(5b)"⟩
    reportedIn := some ⟨"bobaljik-2008", "(24b)"⟩
    language := "nepa1254"
    primaryText := "maile yas pasal-mā patrikā kin-yo."
    glossedTokens := [("maile", "1sERG"), ("yas", "DEM:OBL"), ("pasal-mā", "store-LOC"), ("patrikā", "newspaper:NOM"), ("kin-yo.", "buy-PT3sM")]
    glossedWords := [⟨['m', 'a', 'i', 'l', 'e'], ['1', 's', 'E', 'R', 'G'], [⟨['m', 'a', 'i', 'l', 'e'], ['1', 's', 'E', 'R', 'G'], none⟩]⟩, ⟨['y', 'a', 's'], ['D', 'E', 'M', ':', 'O', 'B', 'L'], [⟨['y', 'a', 's'], ['D', 'E', 'M', ':', 'O', 'B', 'L'], none⟩]⟩, ⟨['p', 'a', 's', 'a', 'l', '-', 'm', 'ā'], ['s', 't', 'o', 'r', 'e', '-', 'L', 'O', 'C'], [⟨['p', 'a', 's', 'a', 'l'], ['s', 't', 'o', 'r', 'e'], none⟩, ⟨['m', 'ā'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['p', 'a', 't', 'r', 'i', 'k', 'ā'], ['n', 'e', 'w', 's', 'p', 'a', 'p', 'e', 'r', ':', 'N', 'O', 'M'], [⟨['p', 'a', 't', 'r', 'i', 'k', 'ā'], ['n', 'e', 'w', 's', 'p', 'a', 'p', 'e', 'r', ':', 'N', 'O', 'M'], none⟩]⟩, ⟨['k', 'i', 'n', '-', 'y', 'o', '.'], ['b', 'u', 'y', '-', 'P', 'T', '3', 's', 'M'], [⟨['k', 'i', 'n'], ['b', 'u', 'y'], none⟩, ⟨['y', 'o'], ['P', 'T', '3', 's', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("clause", "ergativeSubject"), ("controller", "object")] }

def ex_26 : Datum :=
  { id := "bobaljik2008_26"
    source := ⟨"bickel-yadava-2000", "(7a)"⟩
    reportedIn := some ⟨"bobaljik-2008", "(26)"⟩
    language := "nepa1254"
    primaryText := "malāī timī man par-ch-au."
    glossedTokens := [("malāī", "1sDAT"), ("timī", "2mhNOM"), ("man", "liking"), ("par-ch-au.", "occur-NPT-2mh")]
    glossedWords := [⟨['m', 'a', 'l', 'ā', 'ī'], ['1', 's', 'D', 'A', 'T'], [⟨['m', 'a', 'l', 'ā', 'ī'], ['1', 's', 'D', 'A', 'T'], none⟩]⟩, ⟨['t', 'i', 'm', 'ī'], ['2', 'm', 'h', 'N', 'O', 'M'], [⟨['t', 'i', 'm', 'ī'], ['2', 'm', 'h', 'N', 'O', 'M'], none⟩]⟩, ⟨['m', 'a', 'n'], ['l', 'i', 'k', 'i', 'n', 'g'], [⟨['m', 'a', 'n'], ['l', 'i', 'k', 'i', 'n', 'g'], none⟩]⟩, ⟨['p', 'a', 'r', '-', 'c', 'h', '-', 'a', 'u', '.'], ['o', 'c', 'c', 'u', 'r', '-', 'N', 'P', 'T', '-', '2', 'm', 'h'], [⟨['p', 'a', 'r'], ['o', 'c', 'c', 'u', 'r'], none⟩, ⟨['c', 'h'], ['N', 'P', 'T'], some '-'⟩, ⟨['a', 'u'], ['2', 'm', 'h'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clause", "dativeSubject"), ("controller", "object")] }

def ex_26_subject : Datum :=
  { id := "bobaljik2008_26_subject"
    source := ⟨"bickel-yadava-2000", "(7a)"⟩
    reportedIn := some ⟨"bobaljik-2008", "(26)"⟩
    language := "nepa1254"
    primaryText := "malāī timī man par-ch-u."
    glossedTokens := [("malāī", "1sDAT"), ("timī", "2mhNOM"), ("man", "liking"), ("par-ch-u.", "occur-NPT-1s")]
    glossedWords := [⟨['m', 'a', 'l', 'ā', 'ī'], ['1', 's', 'D', 'A', 'T'], [⟨['m', 'a', 'l', 'ā', 'ī'], ['1', 's', 'D', 'A', 'T'], none⟩]⟩, ⟨['t', 'i', 'm', 'ī'], ['2', 'm', 'h', 'N', 'O', 'M'], [⟨['t', 'i', 'm', 'ī'], ['2', 'm', 'h', 'N', 'O', 'M'], none⟩]⟩, ⟨['m', 'a', 'n'], ['l', 'i', 'k', 'i', 'n', 'g'], [⟨['m', 'a', 'n'], ['l', 'i', 'k', 'i', 'n', 'g'], none⟩]⟩, ⟨['p', 'a', 'r', '-', 'c', 'h', '-', 'u', '.'], ['o', 'c', 'c', 'u', 'r', '-', 'N', 'P', 'T', '-', '1', 's'], [⟨['p', 'a', 'r'], ['o', 'c', 'c', 'u', 'r'], none⟩, ⟨['c', 'h'], ['N', 'P', 'T'], some '-'⟩, ⟨['u'], ['1', 's'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("clause", "dativeSubject"), ("controller", "subject")] }

def ex_22a : Datum :=
  { id := "bobaljik2008_22a"
    source := ⟨"woolford-1999", "(10a)"⟩
    reportedIn := some ⟨"bobaljik-2008", "(22a)"⟩
    language := "hind1269"
    primaryText := "Raam-ne roTii khaayii thii."
    glossedTokens := [("Raam-ne", "Ram-erg"), ("roTii", "bread(nom,fem)"), ("khaayii", "eat(perf,fem)"), ("thii.", "be(past,fem)")]
    glossedWords := [⟨['R', 'a', 'a', 'm', '-', 'n', 'e'], ['R', 'a', 'm', '-', 'e', 'r', 'g'], [⟨['R', 'a', 'a', 'm'], ['R', 'a', 'm'], none⟩, ⟨['n', 'e'], ['e', 'r', 'g'], some '-'⟩]⟩, ⟨['r', 'o', 'T', 'i', 'i'], ['b', 'r', 'e', 'a', 'd', '(', 'n', 'o', 'm', ',', 'f', 'e', 'm', ')'], [⟨['r', 'o', 'T', 'i', 'i'], ['b', 'r', 'e', 'a', 'd', '(', 'n', 'o', 'm', ',', 'f', 'e', 'm', ')'], none⟩]⟩, ⟨['k', 'h', 'a', 'a', 'y', 'i', 'i'], ['e', 'a', 't', '(', 'p', 'e', 'r', 'f', ',', 'f', 'e', 'm', ')'], [⟨['k', 'h', 'a', 'a', 'y', 'i', 'i'], ['e', 'a', 't', '(', 'p', 'e', 'r', 'f', ',', 'f', 'e', 'm', ')'], none⟩]⟩, ⟨['t', 'h', 'i', 'i', '.'], ['b', 'e', '(', 'p', 'a', 's', 't', ',', 'f', 'e', 'm', ')'], [⟨['t', 'h', 'i', 'i'], ['b', 'e', '(', 'p', 'a', 's', 't', ',', 'f', 'e', 'm', ')'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("pattern", "ergativeSubject"), ("controller", "object")] }

def ex_22b : Datum :=
  { id := "bobaljik2008_22b"
    source := ⟨"woolford-1999", "(10c)"⟩
    reportedIn := some ⟨"bobaljik-2008", "(22b)"⟩
    language := "hind1269"
    primaryText := "siitaa-ne laRkii-ko dekhaa"
    glossedTokens := [("siitaa-ne", "Sita(fem)-erg"), ("laRkii-ko", "girl-dat"), ("dekhaa", "see(perf,3sg.masc.)")]
    glossedWords := [⟨['s', 'i', 'i', 't', 'a', 'a', '-', 'n', 'e'], ['S', 'i', 't', 'a', '(', 'f', 'e', 'm', ')', '-', 'e', 'r', 'g'], [⟨['s', 'i', 'i', 't', 'a', 'a'], ['S', 'i', 't', 'a', '(', 'f', 'e', 'm', ')'], none⟩, ⟨['n', 'e'], ['e', 'r', 'g'], some '-'⟩]⟩, ⟨['l', 'a', 'R', 'k', 'i', 'i', '-', 'k', 'o'], ['g', 'i', 'r', 'l', '-', 'd', 'a', 't'], [⟨['l', 'a', 'R', 'k', 'i', 'i'], ['g', 'i', 'r', 'l'], none⟩, ⟨['k', 'o'], ['d', 'a', 't'], some '-'⟩]⟩, ⟨['d', 'e', 'k', 'h', 'a', 'a'], ['s', 'e', 'e', '(', 'p', 'e', 'r', 'f', ',', '3', 's', 'g', '.', 'm', 'a', 's', 'c', '.', ')'], [⟨['d', 'e', 'k', 'h', 'a', 'a'], ['s', 'e', 'e', '(', 'p', 'e', 'r', 'f', ',', '3', 's', 'g', '.', 'm', 'a', 's', 'c', '.', ')'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("pattern", "ergativeSubjectMarkedObject"), ("controller", "default")] }

def ex_22c : Datum :=
  { id := "bobaljik2008_22c"
    source := ⟨"woolford-1999", "(10d)"⟩
    reportedIn := some ⟨"bobaljik-2008", "(22c)"⟩
    language := "hind1269"
    primaryText := "siitaa kelaa khaatii thii"
    glossedTokens := [("siitaa", "Sita(nom,fem)"), ("kelaa", "banana(masc.)"), ("khaatii", "eat(imp,fem)"), ("thii", "be(past,fem)")]
    glossedWords := [⟨['s', 'i', 'i', 't', 'a', 'a'], ['S', 'i', 't', 'a', '(', 'n', 'o', 'm', ',', 'f', 'e', 'm', ')'], [⟨['s', 'i', 'i', 't', 'a', 'a'], ['S', 'i', 't', 'a', '(', 'n', 'o', 'm', ',', 'f', 'e', 'm', ')'], none⟩]⟩, ⟨['k', 'e', 'l', 'a', 'a'], ['b', 'a', 'n', 'a', 'n', 'a', '(', 'm', 'a', 's', 'c', '.', ')'], [⟨['k', 'e', 'l', 'a', 'a'], ['b', 'a', 'n', 'a', 'n', 'a', '(', 'm', 'a', 's', 'c', '.', ')'], none⟩]⟩, ⟨['k', 'h', 'a', 'a', 't', 'i', 'i'], ['e', 'a', 't', '(', 'i', 'm', 'p', ',', 'f', 'e', 'm', ')'], [⟨['k', 'h', 'a', 'a', 't', 'i', 'i'], ['e', 'a', 't', '(', 'i', 'm', 'p', ',', 'f', 'e', 'm', ')'], none⟩]⟩, ⟨['t', 'h', 'i', 'i'], ['b', 'e', '(', 'p', 'a', 's', 't', ',', 'f', 'e', 'm', ')'], [⟨['t', 'h', 'i', 'i'], ['b', 'e', '(', 'p', 'a', 's', 't', ',', 'f', 'e', 'm', ')'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("pattern", "unmarkedArguments"), ("controller", "subject")] }

def ex_22d : Datum :=
  { id := "bobaljik2008_22d"
    source := ⟨"woolford-1999", "(10e)"⟩
    reportedIn := some ⟨"bobaljik-2008", "(22d)"⟩
    language := "hind1269"
    primaryText := "niinaa bacce-ko uThaayegii"
    glossedTokens := [("niinaa", "Nina(nom)"), ("bacce-ko", "child-dat"), ("uThaayegii", "lift(fut,fem)")]
    glossedWords := [⟨['n', 'i', 'i', 'n', 'a', 'a'], ['N', 'i', 'n', 'a', '(', 'n', 'o', 'm', ')'], [⟨['n', 'i', 'i', 'n', 'a', 'a'], ['N', 'i', 'n', 'a', '(', 'n', 'o', 'm', ')'], none⟩]⟩, ⟨['b', 'a', 'c', 'c', 'e', '-', 'k', 'o'], ['c', 'h', 'i', 'l', 'd', '-', 'd', 'a', 't'], [⟨['b', 'a', 'c', 'c', 'e'], ['c', 'h', 'i', 'l', 'd'], none⟩, ⟨['k', 'o'], ['d', 'a', 't'], some '-'⟩]⟩, ⟨['u', 'T', 'h', 'a', 'a', 'y', 'e', 'g', 'i', 'i'], ['l', 'i', 'f', 't', '(', 'f', 'u', 't', ',', 'f', 'e', 'm', ')'], [⟨['u', 'T', 'h', 'a', 'a', 'y', 'e', 'g', 'i', 'i'], ['l', 'i', 'f', 't', '(', 'f', 'u', 't', ',', 'f', 'e', 'm', ')'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("pattern", "markedObject"), ("controller", "subject")] }

def ex_22e : Datum :=
  { id := "bobaljik2008_22e"
    source := ⟨"woolford-1999", "(10b)"⟩
    reportedIn := some ⟨"bobaljik-2008", "(22e)"⟩
    language := "hind1269"
    primaryText := "siitaa-ko larke pasand the."
    glossedTokens := [("siitaa-ko", "Sita-dat"), ("larke", "boys(nom)"), ("pasand", "like"), ("the.", "be(past,masc.pl)")]
    glossedWords := [⟨['s', 'i', 'i', 't', 'a', 'a', '-', 'k', 'o'], ['S', 'i', 't', 'a', '-', 'd', 'a', 't'], [⟨['s', 'i', 'i', 't', 'a', 'a'], ['S', 'i', 't', 'a'], none⟩, ⟨['k', 'o'], ['d', 'a', 't'], some '-'⟩]⟩, ⟨['l', 'a', 'r', 'k', 'e'], ['b', 'o', 'y', 's', '(', 'n', 'o', 'm', ')'], [⟨['l', 'a', 'r', 'k', 'e'], ['b', 'o', 'y', 's', '(', 'n', 'o', 'm', ')'], none⟩]⟩, ⟨['p', 'a', 's', 'a', 'n', 'd'], ['l', 'i', 'k', 'e'], [⟨['p', 'a', 's', 'a', 'n', 'd'], ['l', 'i', 'k', 'e'], none⟩]⟩, ⟨['t', 'h', 'e', '.'], ['b', 'e', '(', 'p', 'a', 's', 't', ',', 'm', 'a', 's', 'c', '.', 'p', 'l', ')'], [⟨['t', 'h', 'e'], ['b', 'e', '(', 'p', 'a', 's', 't', ',', 'm', 'a', 's', 'c', '.', 'p', 'l', ')'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("pattern", "dativeSubject"), ("controller", "object")] }

def all : List Datum := [ex_24a, ex_24b, ex_24b_object, ex_26, ex_26_subject, ex_22a, ex_22b, ex_22c, ex_22d, ex_22e]

/-- The Nepali clauses, by the case of the subject. -/
inductive Clause where
  /-- nominativeSubject: a nonpast transitive clause, with a nominative subject and a nominative object -/
  | nominativeSubject
  /-- ergativeSubject: a past transitive clause, with an ergative subject and a nominative object -/
  | ergativeSubject
  /-- dativeSubject: a clause with a dative subject and a nominative object -/
  | dativeSubject
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `clause`. -/
def clause (e : Datum) : Option Clause :=
  e.parse? "clause" [("nominativeSubject", .nominativeSubject), ("ergativeSubject", .ergativeSubject),
    ("dativeSubject", .dativeSubject)]

/-- The argument whose features the form of the verb shows. -/
inductive Controller where
  /-- subject: the subject -/
  | subject
  /-- object: the object -/
  | object
  /-- default: neither: the verb is in its default form -/
  | default
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `controller`. -/
def controller (e : Datum) : Option Controller :=
  e.parse? "controller" [("subject", .subject), ("object", .object), ("default", .default)]

/-- The Hindi-Urdu transitive patterns of (21), by the marking of the subject and the object. -/
inductive Pattern where
  /-- ergativeSubject: perfective, the subject with ne and the object unmarked -/
  | ergativeSubject
  /-- ergativeSubjectMarkedObject: perfective, the subject with ne and the object with ko -/
  | ergativeSubjectMarkedObject
  /-- unmarkedArguments: not perfective, the subject and the object unmarked -/
  | unmarkedArguments
  /-- markedObject: not perfective, the subject unmarked and the object with ko -/
  | markedObject
  /-- dativeSubject: the subject with ko and the object unmarked -/
  | dativeSubject
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `pattern`. -/
def pattern (e : Datum) : Option Pattern :=
  e.parse? "pattern" [("ergativeSubject", .ergativeSubject),
    ("ergativeSubjectMarkedObject", .ergativeSubjectMarkedObject),
    ("unmarkedArguments", .unmarkedArguments), ("markedObject", .markedObject),
    ("dativeSubject", .dativeSubject)]

/-- The examples of the file. -/
inductive Example where
  | ex_24a
  | ex_24b
  | ex_24b_object
  | ex_26
  | ex_26_subject
  | ex_22a
  | ex_22b
  | ex_22c
  | ex_22d
  | ex_22e
  deriving DecidableEq, Repr, Fintype

/-- Every example of the file, in its order. -/
def Example.all : List Example :=
  [.ex_24a, .ex_24b, .ex_24b_object, .ex_26, .ex_26_subject, .ex_22a, .ex_22b, .ex_22c, .ex_22d,
    .ex_22e]

/-- The row of an example. -/
def Example.datum : Example → Datum
  | .ex_24a => _root_.Bobaljik2008.Examples.ex_24a
  | .ex_24b => _root_.Bobaljik2008.Examples.ex_24b
  | .ex_24b_object => _root_.Bobaljik2008.Examples.ex_24b_object
  | .ex_26 => _root_.Bobaljik2008.Examples.ex_26
  | .ex_26_subject => _root_.Bobaljik2008.Examples.ex_26_subject
  | .ex_22a => _root_.Bobaljik2008.Examples.ex_22a
  | .ex_22b => _root_.Bobaljik2008.Examples.ex_22b
  | .ex_22c => _root_.Bobaljik2008.Examples.ex_22c
  | .ex_22d => _root_.Bobaljik2008.Examples.ex_22d
  | .ex_22e => _root_.Bobaljik2008.Examples.ex_22e

theorem Example.map_datum_all :
    Example.all.map Example.datum = _root_.Bobaljik2008.Examples.all := rfl

/-- The value the example records under `clause`. -/
def Example.clause : Example → Option Clause
  | .ex_24a => some .nominativeSubject
  | .ex_24b => some .ergativeSubject
  | .ex_24b_object => some .ergativeSubject
  | .ex_26 => some .dativeSubject
  | .ex_26_subject => some .dativeSubject
  | .ex_22a => none
  | .ex_22b => none
  | .ex_22c => none
  | .ex_22d => none
  | .ex_22e => none

theorem Example.clause_datum :
    ∀ x : Example, _root_.Bobaljik2008.Examples.clause x.datum = x.clause := by
  decide +kernel

/-- The value the example records under `controller`. -/
def Example.controller : Example → Option Controller
  | .ex_24a => some .subject
  | .ex_24b => some .subject
  | .ex_24b_object => some .object
  | .ex_26 => some .object
  | .ex_26_subject => some .subject
  | .ex_22a => some .object
  | .ex_22b => some .default
  | .ex_22c => some .subject
  | .ex_22d => some .subject
  | .ex_22e => some .object

theorem Example.controller_datum :
    ∀ x : Example, _root_.Bobaljik2008.Examples.controller x.datum = x.controller := by
  decide +kernel

/-- The value the example records under `pattern`. -/
def Example.pattern : Example → Option Pattern
  | .ex_24a => none
  | .ex_24b => none
  | .ex_24b_object => none
  | .ex_26 => none
  | .ex_26_subject => none
  | .ex_22a => some .ergativeSubject
  | .ex_22b => some .ergativeSubjectMarkedObject
  | .ex_22c => some .unmarkedArguments
  | .ex_22d => some .markedObject
  | .ex_22e => some .dativeSubject

theorem Example.pattern_datum :
    ∀ x : Example, _root_.Bobaljik2008.Examples.pattern x.datum = x.pattern := by
  decide +kernel

end Bobaljik2008.Examples
