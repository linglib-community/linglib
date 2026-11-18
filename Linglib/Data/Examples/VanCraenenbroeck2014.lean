module

public import Linglib.Data.Examples.Schema

/-!
# `VanCraenenbroeck2014` — typed example data

Auto-generated from `Linglib/Data/Examples/VanCraenenbroeck2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace VanCraenenbroeck2014.Examples`.
-/

@[expose] public section

namespace VanCraenenbroeck2014.Examples

def ex_10a : Datum :=
  { id := "vancraenenbroeck2014_10a"
    source := ⟨"van-craenenbroeck-2014", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kyle criticized my paper."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("construction", "selection"), ("category", "verb")] }

def ex_10b : Datum :=
  { id := "vancraenenbroeck2014_10b"
    source := ⟨"van-craenenbroeck-2014", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kyle's criticism of my paper."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("construction", "selection"), ("category", "noun")] }

def ex_11 : Datum :=
  { id := "vancraenenbroeck2014_11"
    source := ⟨"van-craenenbroeck-2014", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kyle criticized my paper and Rajesh did {the same/likewise} to my book."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("construction", "pronominalization"), ("category", "verb"), ("proform", "the same/likewise"), ("argument", "stranded")] }

def ex_13 : Datum :=
  { id := "vancraenenbroeck2014_13"
    source := ⟨"van-craenenbroeck-2014", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kyle criticized my paper and Rajesh did {the same/likewise}."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("construction", "pronominalization"), ("category", "verb"), ("proform", "the same/likewise"), ("argument", "included")] }

def ex_15a : Datum :=
  { id := "vancraenenbroeck2014_15a"
    source := ⟨"van-craenenbroeck-2014", "(15a)"⟩
    reportedIn := none
    language := "west2354"
    primaryText := "Jitske besprekt syn roman."
    glossedTokens := [("Jitske", "Jitske"), ("besprekt", "reviews"), ("syn", "his"), ("roman.", "novel")]
    glossedWords := [⟨['J', 'i', 't', 's', 'k', 'e'], ['J', 'i', 't', 's', 'k', 'e'], [⟨['J', 'i', 't', 's', 'k', 'e'], ['J', 'i', 't', 's', 'k', 'e'], none⟩]⟩, ⟨['b', 'e', 's', 'p', 'r', 'e', 'k', 't'], ['r', 'e', 'v', 'i', 'e', 'w', 's'], [⟨['b', 'e', 's', 'p', 'r', 'e', 'k', 't'], ['r', 'e', 'v', 'i', 'e', 'w', 's'], none⟩]⟩, ⟨['s', 'y', 'n'], ['h', 'i', 's'], [⟨['s', 'y', 'n'], ['h', 'i', 's'], none⟩]⟩, ⟨['r', 'o', 'm', 'a', 'n', '.'], ['n', 'o', 'v', 'e', 'l'], [⟨['r', 'o', 'm', 'a', 'n'], ['n', 'o', 'v', 'e', 'l'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("construction", "selection"), ("category", "verb")] }

def ex_15b : Datum :=
  { id := "vancraenenbroeck2014_15b"
    source := ⟨"van-craenenbroeck-2014", "(15b)"⟩
    reportedIn := none
    language := "west2354"
    primaryText := "in besprek fan syn roman"
    glossedTokens := [("in", "a"), ("besprek", "review"), ("fan", "of"), ("syn", "his"), ("roman", "novel")]
    glossedWords := [⟨['i', 'n'], ['a'], [⟨['i', 'n'], ['a'], none⟩]⟩, ⟨['b', 'e', 's', 'p', 'r', 'e', 'k'], ['r', 'e', 'v', 'i', 'e', 'w'], [⟨['b', 'e', 's', 'p', 'r', 'e', 'k'], ['r', 'e', 'v', 'i', 'e', 'w'], none⟩]⟩, ⟨['f', 'a', 'n'], ['o', 'f'], [⟨['f', 'a', 'n'], ['o', 'f'], none⟩]⟩, ⟨['s', 'y', 'n'], ['h', 'i', 's'], [⟨['s', 'y', 'n'], ['h', 'i', 's'], none⟩]⟩, ⟨['r', 'o', 'm', 'a', 'n'], ['n', 'o', 'v', 'e', 'l'], [⟨['r', 'o', 'm', 'a', 'n'], ['n', 'o', 'v', 'e', 'l'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("construction", "selection"), ("category", "noun")] }

def ex_16 : Datum :=
  { id := "vancraenenbroeck2014_16"
    source := ⟨"van-craenenbroeck-2014", "(16)"⟩
    reportedIn := none
    language := "west2354"
    primaryText := "Jan hie in witte auto en Geart in swarten ien."
    glossedTokens := [("Jan", "Jan"), ("hie", "has"), ("in", "a"), ("witte", "white"), ("auto", "car"), ("en", "and"), ("Geart", "Geart"), ("in", "a"), ("swarten", "black"), ("ien.", "one")]
    glossedWords := [⟨['J', 'a', 'n'], ['J', 'a', 'n'], [⟨['J', 'a', 'n'], ['J', 'a', 'n'], none⟩]⟩, ⟨['h', 'i', 'e'], ['h', 'a', 's'], [⟨['h', 'i', 'e'], ['h', 'a', 's'], none⟩]⟩, ⟨['i', 'n'], ['a'], [⟨['i', 'n'], ['a'], none⟩]⟩, ⟨['w', 'i', 't', 't', 'e'], ['w', 'h', 'i', 't', 'e'], [⟨['w', 'i', 't', 't', 'e'], ['w', 'h', 'i', 't', 'e'], none⟩]⟩, ⟨['a', 'u', 't', 'o'], ['c', 'a', 'r'], [⟨['a', 'u', 't', 'o'], ['c', 'a', 'r'], none⟩]⟩, ⟨['e', 'n'], ['a', 'n', 'd'], [⟨['e', 'n'], ['a', 'n', 'd'], none⟩]⟩, ⟨['G', 'e', 'a', 'r', 't'], ['G', 'e', 'a', 'r', 't'], [⟨['G', 'e', 'a', 'r', 't'], ['G', 'e', 'a', 'r', 't'], none⟩]⟩, ⟨['i', 'n'], ['a'], [⟨['i', 'n'], ['a'], none⟩]⟩, ⟨['s', 'w', 'a', 'r', 't', 'e', 'n'], ['b', 'l', 'a', 'c', 'k'], [⟨['s', 'w', 'a', 'r', 't', 'e', 'n'], ['b', 'l', 'a', 'c', 'k'], none⟩]⟩, ⟨['i', 'e', 'n', '.'], ['o', 'n', 'e'], [⟨['i', 'e', 'n'], ['o', 'n', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("construction", "npEllipsis"), ("proform", "ien")] }

def ex_17a : Datum :=
  { id := "vancraenenbroeck2014_17a"
    source := ⟨"van-craenenbroeck-2014", "(17a)"⟩
    reportedIn := none
    language := "west2354"
    primaryText := "Jitse wiisde him op in posityf besprek fan syn roman en Jitske op in negativen ien fan syn samle fersen."
    glossedTokens := [("Jitse", "Jitse"), ("wiisde", "pointed"), ("him", "him"), ("op", "on"), ("in", "a"), ("posityf", "positive"), ("besprek", "review"), ("fan", "of"), ("syn", "his"), ("roman", "novel"), ("en", "and"), ("Jitske", "Jitske"), ("op", "on"), ("in", "a"), ("negativen", "negative"), ("ien", "one"), ("fan", "of"), ("syn", "his"), ("samle", "collected"), ("fersen.", "poems")]
    glossedWords := [⟨['J', 'i', 't', 's', 'e'], ['J', 'i', 't', 's', 'e'], [⟨['J', 'i', 't', 's', 'e'], ['J', 'i', 't', 's', 'e'], none⟩]⟩, ⟨['w', 'i', 'i', 's', 'd', 'e'], ['p', 'o', 'i', 'n', 't', 'e', 'd'], [⟨['w', 'i', 'i', 's', 'd', 'e'], ['p', 'o', 'i', 'n', 't', 'e', 'd'], none⟩]⟩, ⟨['h', 'i', 'm'], ['h', 'i', 'm'], [⟨['h', 'i', 'm'], ['h', 'i', 'm'], none⟩]⟩, ⟨['o', 'p'], ['o', 'n'], [⟨['o', 'p'], ['o', 'n'], none⟩]⟩, ⟨['i', 'n'], ['a'], [⟨['i', 'n'], ['a'], none⟩]⟩, ⟨['p', 'o', 's', 'i', 't', 'y', 'f'], ['p', 'o', 's', 'i', 't', 'i', 'v', 'e'], [⟨['p', 'o', 's', 'i', 't', 'y', 'f'], ['p', 'o', 's', 'i', 't', 'i', 'v', 'e'], none⟩]⟩, ⟨['b', 'e', 's', 'p', 'r', 'e', 'k'], ['r', 'e', 'v', 'i', 'e', 'w'], [⟨['b', 'e', 's', 'p', 'r', 'e', 'k'], ['r', 'e', 'v', 'i', 'e', 'w'], none⟩]⟩, ⟨['f', 'a', 'n'], ['o', 'f'], [⟨['f', 'a', 'n'], ['o', 'f'], none⟩]⟩, ⟨['s', 'y', 'n'], ['h', 'i', 's'], [⟨['s', 'y', 'n'], ['h', 'i', 's'], none⟩]⟩, ⟨['r', 'o', 'm', 'a', 'n'], ['n', 'o', 'v', 'e', 'l'], [⟨['r', 'o', 'm', 'a', 'n'], ['n', 'o', 'v', 'e', 'l'], none⟩]⟩, ⟨['e', 'n'], ['a', 'n', 'd'], [⟨['e', 'n'], ['a', 'n', 'd'], none⟩]⟩, ⟨['J', 'i', 't', 's', 'k', 'e'], ['J', 'i', 't', 's', 'k', 'e'], [⟨['J', 'i', 't', 's', 'k', 'e'], ['J', 'i', 't', 's', 'k', 'e'], none⟩]⟩, ⟨['o', 'p'], ['o', 'n'], [⟨['o', 'p'], ['o', 'n'], none⟩]⟩, ⟨['i', 'n'], ['a'], [⟨['i', 'n'], ['a'], none⟩]⟩, ⟨['n', 'e', 'g', 'a', 't', 'i', 'v', 'e', 'n'], ['n', 'e', 'g', 'a', 't', 'i', 'v', 'e'], [⟨['n', 'e', 'g', 'a', 't', 'i', 'v', 'e', 'n'], ['n', 'e', 'g', 'a', 't', 'i', 'v', 'e'], none⟩]⟩, ⟨['i', 'e', 'n'], ['o', 'n', 'e'], [⟨['i', 'e', 'n'], ['o', 'n', 'e'], none⟩]⟩, ⟨['f', 'a', 'n'], ['o', 'f'], [⟨['f', 'a', 'n'], ['o', 'f'], none⟩]⟩, ⟨['s', 'y', 'n'], ['h', 'i', 's'], [⟨['s', 'y', 'n'], ['h', 'i', 's'], none⟩]⟩, ⟨['s', 'a', 'm', 'l', 'e'], ['c', 'o', 'l', 'l', 'e', 'c', 't', 'e', 'd'], [⟨['s', 'a', 'm', 'l', 'e'], ['c', 'o', 'l', 'l', 'e', 'c', 't', 'e', 'd'], none⟩]⟩, ⟨['f', 'e', 'r', 's', 'e', 'n', '.'], ['p', 'o', 'e', 'm', 's'], [⟨['f', 'e', 'r', 's', 'e', 'n'], ['p', 'o', 'e', 'm', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("construction", "pronominalization"), ("category", "noun"), ("proform", "ien"), ("argument", "stranded")] }

def ex_17b : Datum :=
  { id := "vancraenenbroeck2014_17b"
    source := ⟨"van-craenenbroeck-2014", "(17b)"⟩
    reportedIn := none
    language := "west2354"
    primaryText := "Jitse wiisde him op in posityf besprek fan syn roman en Jitske op in negativen ien."
    glossedTokens := [("Jitse", "Jitse"), ("wiisde", "pointed"), ("him", "him"), ("op", "on"), ("in", "a"), ("posityf", "positive"), ("besprek", "review"), ("fan", "of"), ("syn", "his"), ("roman", "novel"), ("en", "and"), ("Jitske", "Jitske"), ("op", "on"), ("in", "a"), ("negativen", "negative"), ("ien.", "one")]
    glossedWords := [⟨['J', 'i', 't', 's', 'e'], ['J', 'i', 't', 's', 'e'], [⟨['J', 'i', 't', 's', 'e'], ['J', 'i', 't', 's', 'e'], none⟩]⟩, ⟨['w', 'i', 'i', 's', 'd', 'e'], ['p', 'o', 'i', 'n', 't', 'e', 'd'], [⟨['w', 'i', 'i', 's', 'd', 'e'], ['p', 'o', 'i', 'n', 't', 'e', 'd'], none⟩]⟩, ⟨['h', 'i', 'm'], ['h', 'i', 'm'], [⟨['h', 'i', 'm'], ['h', 'i', 'm'], none⟩]⟩, ⟨['o', 'p'], ['o', 'n'], [⟨['o', 'p'], ['o', 'n'], none⟩]⟩, ⟨['i', 'n'], ['a'], [⟨['i', 'n'], ['a'], none⟩]⟩, ⟨['p', 'o', 's', 'i', 't', 'y', 'f'], ['p', 'o', 's', 'i', 't', 'i', 'v', 'e'], [⟨['p', 'o', 's', 'i', 't', 'y', 'f'], ['p', 'o', 's', 'i', 't', 'i', 'v', 'e'], none⟩]⟩, ⟨['b', 'e', 's', 'p', 'r', 'e', 'k'], ['r', 'e', 'v', 'i', 'e', 'w'], [⟨['b', 'e', 's', 'p', 'r', 'e', 'k'], ['r', 'e', 'v', 'i', 'e', 'w'], none⟩]⟩, ⟨['f', 'a', 'n'], ['o', 'f'], [⟨['f', 'a', 'n'], ['o', 'f'], none⟩]⟩, ⟨['s', 'y', 'n'], ['h', 'i', 's'], [⟨['s', 'y', 'n'], ['h', 'i', 's'], none⟩]⟩, ⟨['r', 'o', 'm', 'a', 'n'], ['n', 'o', 'v', 'e', 'l'], [⟨['r', 'o', 'm', 'a', 'n'], ['n', 'o', 'v', 'e', 'l'], none⟩]⟩, ⟨['e', 'n'], ['a', 'n', 'd'], [⟨['e', 'n'], ['a', 'n', 'd'], none⟩]⟩, ⟨['J', 'i', 't', 's', 'k', 'e'], ['J', 'i', 't', 's', 'k', 'e'], [⟨['J', 'i', 't', 's', 'k', 'e'], ['J', 'i', 't', 's', 'k', 'e'], none⟩]⟩, ⟨['o', 'p'], ['o', 'n'], [⟨['o', 'p'], ['o', 'n'], none⟩]⟩, ⟨['i', 'n'], ['a'], [⟨['i', 'n'], ['a'], none⟩]⟩, ⟨['n', 'e', 'g', 'a', 't', 'i', 'v', 'e', 'n'], ['n', 'e', 'g', 'a', 't', 'i', 'v', 'e'], [⟨['n', 'e', 'g', 'a', 't', 'i', 'v', 'e', 'n'], ['n', 'e', 'g', 'a', 't', 'i', 'v', 'e'], none⟩]⟩, ⟨['i', 'e', 'n', '.'], ['o', 'n', 'e'], [⟨['i', 'e', 'n'], ['o', 'n', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("construction", "pronominalization"), ("category", "noun"), ("proform", "ien"), ("argument", "included")] }

def ex_18a : Datum :=
  { id := "vancraenenbroeck2014_18a"
    source := ⟨"van-craenenbroeck-2014", "(18a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Ze geeft hem de bons."
    glossedTokens := [("Ze", "she"), ("geeft", "gives"), ("hem", "him"), ("de", "the"), ("bons.", "knock")]
    glossedWords := [⟨['Z', 'e'], ['s', 'h', 'e'], [⟨['Z', 'e'], ['s', 'h', 'e'], none⟩]⟩, ⟨['g', 'e', 'e', 'f', 't'], ['g', 'i', 'v', 'e', 's'], [⟨['g', 'e', 'e', 'f', 't'], ['g', 'i', 'v', 'e', 's'], none⟩]⟩, ⟨['h', 'e', 'm'], ['h', 'i', 'm'], [⟨['h', 'e', 'm'], ['h', 'i', 'm'], none⟩]⟩, ⟨['d', 'e'], ['t', 'h', 'e'], [⟨['d', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['b', 'o', 'n', 's', '.'], ['k', 'n', 'o', 'c', 'k'], [⟨['b', 'o', 'n', 's'], ['k', 'n', 'o', 'c', 'k'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3"), ("construction", "idiom"), ("idiom", "bons"), ("form", "active")] }

def ex_18b : Datum :=
  { id := "vancraenenbroeck2014_18b"
    source := ⟨"van-craenenbroeck-2014", "(18b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "het geven van de bons (aan hem)"
    glossedTokens := [("het", "the"), ("geven", "give.INF"), ("van", "of"), ("de", "the"), ("bons", "knock"), ("(aan", "to"), ("hem)", "him")]
    glossedWords := [⟨['h', 'e', 't'], ['t', 'h', 'e'], [⟨['h', 'e', 't'], ['t', 'h', 'e'], none⟩]⟩, ⟨['g', 'e', 'v', 'e', 'n'], ['g', 'i', 'v', 'e', '.', 'I', 'N', 'F'], [⟨['g', 'e', 'v', 'e', 'n'], ['g', 'i', 'v', 'e', '.', 'I', 'N', 'F'], none⟩]⟩, ⟨['v', 'a', 'n'], ['o', 'f'], [⟨['v', 'a', 'n'], ['o', 'f'], none⟩]⟩, ⟨['d', 'e'], ['t', 'h', 'e'], [⟨['d', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['b', 'o', 'n', 's'], ['k', 'n', 'o', 'c', 'k'], [⟨['b', 'o', 'n', 's'], ['k', 'n', 'o', 'c', 'k'], none⟩]⟩, ⟨['(', 'a', 'a', 'n'], ['t', 'o'], [⟨['a', 'a', 'n'], ['t', 'o'], none⟩]⟩, ⟨['h', 'e', 'm', ')'], ['h', 'i', 'm'], [⟨['h', 'e', 'm'], ['h', 'i', 'm'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3"), ("construction", "idiom"), ("idiom", "bons"), ("form", "nominalizedInfinitive")] }

def ex_18c : Datum :=
  { id := "vancraenenbroeck2014_18c"
    source := ⟨"van-craenenbroeck-2014", "(18c)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "De bons wordt hem door haar gegeven."
    glossedTokens := [("De", "the"), ("bons", "knock"), ("wordt", "becomes"), ("hem", "him"), ("door", "by"), ("haar", "her"), ("gegeven.", "given")]
    glossedWords := [⟨['D', 'e'], ['t', 'h', 'e'], [⟨['D', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['b', 'o', 'n', 's'], ['k', 'n', 'o', 'c', 'k'], [⟨['b', 'o', 'n', 's'], ['k', 'n', 'o', 'c', 'k'], none⟩]⟩, ⟨['w', 'o', 'r', 'd', 't'], ['b', 'e', 'c', 'o', 'm', 'e', 's'], [⟨['w', 'o', 'r', 'd', 't'], ['b', 'e', 'c', 'o', 'm', 'e', 's'], none⟩]⟩, ⟨['h', 'e', 'm'], ['h', 'i', 'm'], [⟨['h', 'e', 'm'], ['h', 'i', 'm'], none⟩]⟩, ⟨['d', 'o', 'o', 'r'], ['b', 'y'], [⟨['d', 'o', 'o', 'r'], ['b', 'y'], none⟩]⟩, ⟨['h', 'a', 'a', 'r'], ['h', 'e', 'r'], [⟨['h', 'a', 'a', 'r'], ['h', 'e', 'r'], none⟩]⟩, ⟨['g', 'e', 'g', 'e', 'v', 'e', 'n', '.'], ['g', 'i', 'v', 'e', 'n'], [⟨['g', 'e', 'g', 'e', 'v', 'e', 'n'], ['g', 'i', 'v', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3"), ("construction", "idiom"), ("idiom", "bons"), ("form", "passive")] }

def ex_19a : Datum :=
  { id := "vancraenenbroeck2014_19a"
    source := ⟨"van-craenenbroeck-2014", "(19a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Dat doet hem de das om."
    glossedTokens := [("Dat", "that"), ("doet", "puts"), ("hem", "him"), ("de", "the"), ("das", "tie"), ("om.", "on")]
    glossedWords := [⟨['D', 'a', 't'], ['t', 'h', 'a', 't'], [⟨['D', 'a', 't'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['d', 'o', 'e', 't'], ['p', 'u', 't', 's'], [⟨['d', 'o', 'e', 't'], ['p', 'u', 't', 's'], none⟩]⟩, ⟨['h', 'e', 'm'], ['h', 'i', 'm'], [⟨['h', 'e', 'm'], ['h', 'i', 'm'], none⟩]⟩, ⟨['d', 'e'], ['t', 'h', 'e'], [⟨['d', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['d', 'a', 's'], ['t', 'i', 'e'], [⟨['d', 'a', 's'], ['t', 'i', 'e'], none⟩]⟩, ⟨['o', 'm', '.'], ['o', 'n'], [⟨['o', 'm'], ['o', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3"), ("construction", "idiom"), ("idiom", "das"), ("form", "active")] }

def ex_19b : Datum :=
  { id := "vancraenenbroeck2014_19b"
    source := ⟨"van-craenenbroeck-2014", "(19b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Hem wordt de das omgedaan."
    glossedTokens := [("Hem", "him"), ("wordt", "becomes"), ("de", "the"), ("das", "tie"), ("omgedaan.", "put.on")]
    glossedWords := [⟨['H', 'e', 'm'], ['h', 'i', 'm'], [⟨['H', 'e', 'm'], ['h', 'i', 'm'], none⟩]⟩, ⟨['w', 'o', 'r', 'd', 't'], ['b', 'e', 'c', 'o', 'm', 'e', 's'], [⟨['w', 'o', 'r', 'd', 't'], ['b', 'e', 'c', 'o', 'm', 'e', 's'], none⟩]⟩, ⟨['d', 'e'], ['t', 'h', 'e'], [⟨['d', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['d', 'a', 's'], ['t', 'i', 'e'], [⟨['d', 'a', 's'], ['t', 'i', 'e'], none⟩]⟩, ⟨['o', 'm', 'g', 'e', 'd', 'a', 'a', 'n', '.'], ['p', 'u', 't', '.', 'o', 'n'], [⟨['o', 'm', 'g', 'e', 'd', 'a', 'a', 'n'], ['p', 'u', 't', '.', 'o', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3"), ("construction", "idiom"), ("idiom", "das"), ("form", "passive")] }

def ex_19c : Datum :=
  { id := "vancraenenbroeck2014_19c"
    source := ⟨"van-craenenbroeck-2014", "(19c)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "het hem omdoen van de das"
    glossedTokens := [("het", "the"), ("hem", "him"), ("omdoen", "on.put.INF"), ("van", "of"), ("de", "the"), ("das", "tie")]
    glossedWords := [⟨['h', 'e', 't'], ['t', 'h', 'e'], [⟨['h', 'e', 't'], ['t', 'h', 'e'], none⟩]⟩, ⟨['h', 'e', 'm'], ['h', 'i', 'm'], [⟨['h', 'e', 'm'], ['h', 'i', 'm'], none⟩]⟩, ⟨['o', 'm', 'd', 'o', 'e', 'n'], ['o', 'n', '.', 'p', 'u', 't', '.', 'I', 'N', 'F'], [⟨['o', 'm', 'd', 'o', 'e', 'n'], ['o', 'n', '.', 'p', 'u', 't', '.', 'I', 'N', 'F'], none⟩]⟩, ⟨['v', 'a', 'n'], ['o', 'f'], [⟨['v', 'a', 'n'], ['o', 'f'], none⟩]⟩, ⟨['d', 'e'], ['t', 'h', 'e'], [⟨['d', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['d', 'a', 's'], ['t', 'i', 'e'], [⟨['d', 'a', 's'], ['t', 'i', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3"), ("construction", "idiom"), ("idiom", "das"), ("form", "nominalizedInfinitive")] }

def ex_20a : Datum :=
  { id := "vancraenenbroeck2014_20a"
    source := ⟨"van-craenenbroeck-2014", "(20a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Hij begraaft de strijdbijl."
    glossedTokens := [("Hij", "he"), ("begraaft", "buries"), ("de", "the"), ("strijdbijl.", "hatchet")]
    glossedWords := [⟨['H', 'i', 'j'], ['h', 'e'], [⟨['H', 'i', 'j'], ['h', 'e'], none⟩]⟩, ⟨['b', 'e', 'g', 'r', 'a', 'a', 'f', 't'], ['b', 'u', 'r', 'i', 'e', 's'], [⟨['b', 'e', 'g', 'r', 'a', 'a', 'f', 't'], ['b', 'u', 'r', 'i', 'e', 's'], none⟩]⟩, ⟨['d', 'e'], ['t', 'h', 'e'], [⟨['d', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['s', 't', 'r', 'i', 'j', 'd', 'b', 'i', 'j', 'l', '.'], ['h', 'a', 't', 'c', 'h', 'e', 't'], [⟨['s', 't', 'r', 'i', 'j', 'd', 'b', 'i', 'j', 'l'], ['h', 'a', 't', 'c', 'h', 'e', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3"), ("construction", "idiom"), ("idiom", "strijdbijl"), ("form", "active")] }

def ex_20b : Datum :=
  { id := "vancraenenbroeck2014_20b"
    source := ⟨"van-craenenbroeck-2014", "(20b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "het begraven van de strijdbijl"
    glossedTokens := [("het", "the"), ("begraven", "bury.INF"), ("van", "of"), ("de", "the"), ("strijdbijl", "hatchet")]
    glossedWords := [⟨['h', 'e', 't'], ['t', 'h', 'e'], [⟨['h', 'e', 't'], ['t', 'h', 'e'], none⟩]⟩, ⟨['b', 'e', 'g', 'r', 'a', 'v', 'e', 'n'], ['b', 'u', 'r', 'y', '.', 'I', 'N', 'F'], [⟨['b', 'e', 'g', 'r', 'a', 'v', 'e', 'n'], ['b', 'u', 'r', 'y', '.', 'I', 'N', 'F'], none⟩]⟩, ⟨['v', 'a', 'n'], ['o', 'f'], [⟨['v', 'a', 'n'], ['o', 'f'], none⟩]⟩, ⟨['d', 'e'], ['t', 'h', 'e'], [⟨['d', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['s', 't', 'r', 'i', 'j', 'd', 'b', 'i', 'j', 'l'], ['h', 'a', 't', 'c', 'h', 'e', 't'], [⟨['s', 't', 'r', 'i', 'j', 'd', 'b', 'i', 'j', 'l'], ['h', 'a', 't', 'c', 'h', 'e', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3"), ("construction", "idiom"), ("idiom", "strijdbijl"), ("form", "nominalizedInfinitive")] }

def ex_20c : Datum :=
  { id := "vancraenenbroeck2014_20c"
    source := ⟨"van-craenenbroeck-2014", "(20c)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "De strijdbijl wordt begraven."
    glossedTokens := [("De", "the"), ("strijdbijl", "hatchet"), ("wordt", "becomes"), ("begraven.", "buried")]
    glossedWords := [⟨['D', 'e'], ['t', 'h', 'e'], [⟨['D', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['s', 't', 'r', 'i', 'j', 'd', 'b', 'i', 'j', 'l'], ['h', 'a', 't', 'c', 'h', 'e', 't'], [⟨['s', 't', 'r', 'i', 'j', 'd', 'b', 'i', 'j', 'l'], ['h', 'a', 't', 'c', 'h', 'e', 't'], none⟩]⟩, ⟨['w', 'o', 'r', 'd', 't'], ['b', 'e', 'c', 'o', 'm', 'e', 's'], [⟨['w', 'o', 'r', 'd', 't'], ['b', 'e', 'c', 'o', 'm', 'e', 's'], none⟩]⟩, ⟨['b', 'e', 'g', 'r', 'a', 'v', 'e', 'n', '.'], ['b', 'u', 'r', 'i', 'e', 'd'], [⟨['b', 'e', 'g', 'r', 'a', 'v', 'e', 'n'], ['b', 'u', 'r', 'i', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3"), ("construction", "idiom"), ("idiom", "strijdbijl"), ("form", "passive")] }

def ex_21a : Datum :=
  { id := "vancraenenbroeck2014_21a"
    source := ⟨"van-craenenbroeck-2014", "(21a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Hij breekt het ijs."
    glossedTokens := [("Hij", "he"), ("breekt", "breaks"), ("het", "the"), ("ijs.", "ice")]
    glossedWords := [⟨['H', 'i', 'j'], ['h', 'e'], [⟨['H', 'i', 'j'], ['h', 'e'], none⟩]⟩, ⟨['b', 'r', 'e', 'e', 'k', 't'], ['b', 'r', 'e', 'a', 'k', 's'], [⟨['b', 'r', 'e', 'e', 'k', 't'], ['b', 'r', 'e', 'a', 'k', 's'], none⟩]⟩, ⟨['h', 'e', 't'], ['t', 'h', 'e'], [⟨['h', 'e', 't'], ['t', 'h', 'e'], none⟩]⟩, ⟨['i', 'j', 's', '.'], ['i', 'c', 'e'], [⟨['i', 'j', 's'], ['i', 'c', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3"), ("construction", "idiom"), ("idiom", "ijs"), ("form", "active")] }

def ex_21b : Datum :=
  { id := "vancraenenbroeck2014_21b"
    source := ⟨"van-craenenbroeck-2014", "(21b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "het breken van het ijs"
    glossedTokens := [("het", "the"), ("breken", "break.INF"), ("van", "of"), ("het", "the"), ("ijs", "ice")]
    glossedWords := [⟨['h', 'e', 't'], ['t', 'h', 'e'], [⟨['h', 'e', 't'], ['t', 'h', 'e'], none⟩]⟩, ⟨['b', 'r', 'e', 'k', 'e', 'n'], ['b', 'r', 'e', 'a', 'k', '.', 'I', 'N', 'F'], [⟨['b', 'r', 'e', 'k', 'e', 'n'], ['b', 'r', 'e', 'a', 'k', '.', 'I', 'N', 'F'], none⟩]⟩, ⟨['v', 'a', 'n'], ['o', 'f'], [⟨['v', 'a', 'n'], ['o', 'f'], none⟩]⟩, ⟨['h', 'e', 't'], ['t', 'h', 'e'], [⟨['h', 'e', 't'], ['t', 'h', 'e'], none⟩]⟩, ⟨['i', 'j', 's'], ['i', 'c', 'e'], [⟨['i', 'j', 's'], ['i', 'c', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3"), ("construction", "idiom"), ("idiom", "ijs"), ("form", "nominalizedInfinitive")] }

def ex_21c : Datum :=
  { id := "vancraenenbroeck2014_21c"
    source := ⟨"van-craenenbroeck-2014", "(21c)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Het ijs is gebroken."
    glossedTokens := [("Het", "the"), ("ijs", "ice"), ("is", "is"), ("gebroken.", "broken")]
    glossedWords := [⟨['H', 'e', 't'], ['t', 'h', 'e'], [⟨['H', 'e', 't'], ['t', 'h', 'e'], none⟩]⟩, ⟨['i', 'j', 's'], ['i', 'c', 'e'], [⟨['i', 'j', 's'], ['i', 'c', 'e'], none⟩]⟩, ⟨['i', 's'], ['i', 's'], [⟨['i', 's'], ['i', 's'], none⟩]⟩, ⟨['g', 'e', 'b', 'r', 'o', 'k', 'e', 'n', '.'], ['b', 'r', 'o', 'k', 'e', 'n'], [⟨['g', 'e', 'b', 'r', 'o', 'k', 'e', 'n'], ['b', 'r', 'o', 'k', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3"), ("construction", "idiom"), ("idiom", "ijs"), ("form", "passive")] }

def ex_22a : Datum :=
  { id := "vancraenenbroeck2014_22a"
    source := ⟨"van-craenenbroeck-2014", "(22a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "de begraving van de strijdbijl"
    glossedTokens := [("de", "the"), ("begraving", "bury.NOMINALIZER"), ("van", "of"), ("de", "the"), ("strijdbijl", "hatchet")]
    glossedWords := [⟨['d', 'e'], ['t', 'h', 'e'], [⟨['d', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['b', 'e', 'g', 'r', 'a', 'v', 'i', 'n', 'g'], ['b', 'u', 'r', 'y', '.', 'N', 'O', 'M', 'I', 'N', 'A', 'L', 'I', 'Z', 'E', 'R'], [⟨['b', 'e', 'g', 'r', 'a', 'v', 'i', 'n', 'g'], ['b', 'u', 'r', 'y', '.', 'N', 'O', 'M', 'I', 'N', 'A', 'L', 'I', 'Z', 'E', 'R'], none⟩]⟩, ⟨['v', 'a', 'n'], ['o', 'f'], [⟨['v', 'a', 'n'], ['o', 'f'], none⟩]⟩, ⟨['d', 'e'], ['t', 'h', 'e'], [⟨['d', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['s', 't', 'r', 'i', 'j', 'd', 'b', 'i', 'j', 'l'], ['h', 'a', 't', 'c', 'h', 'e', 't'], [⟨['s', 't', 'r', 'i', 'j', 'd', 'b', 'i', 'j', 'l'], ['h', 'a', 't', 'c', 'h', 'e', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3"), ("construction", "idiom"), ("idiom", "strijdbijl"), ("form", "nominalization")] }

def ex_22b : Datum :=
  { id := "vancraenenbroeck2014_22b"
    source := ⟨"van-craenenbroeck-2014", "(22b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "de breking van het ijs"
    glossedTokens := [("de", "the"), ("breking", "break.NOMINALIZER"), ("van", "of"), ("het", "the"), ("ijs", "ice")]
    glossedWords := [⟨['d', 'e'], ['t', 'h', 'e'], [⟨['d', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['b', 'r', 'e', 'k', 'i', 'n', 'g'], ['b', 'r', 'e', 'a', 'k', '.', 'N', 'O', 'M', 'I', 'N', 'A', 'L', 'I', 'Z', 'E', 'R'], [⟨['b', 'r', 'e', 'k', 'i', 'n', 'g'], ['b', 'r', 'e', 'a', 'k', '.', 'N', 'O', 'M', 'I', 'N', 'A', 'L', 'I', 'Z', 'E', 'R'], none⟩]⟩, ⟨['v', 'a', 'n'], ['o', 'f'], [⟨['v', 'a', 'n'], ['o', 'f'], none⟩]⟩, ⟨['h', 'e', 't'], ['t', 'h', 'e'], [⟨['h', 'e', 't'], ['t', 'h', 'e'], none⟩]⟩, ⟨['i', 'j', 's'], ['i', 'c', 'e'], [⟨['i', 'j', 's'], ['i', 'c', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3"), ("construction", "idiom"), ("idiom", "ijs"), ("form", "nominalization")] }

def all : List Datum := [ex_10a, ex_10b, ex_11, ex_13, ex_15a, ex_15b, ex_16, ex_17a, ex_17b, ex_18a, ex_18b, ex_18c, ex_19a, ex_19b, ex_19c, ex_20a, ex_20b, ex_20c, ex_21a, ex_21b, ex_21c, ex_22a, ex_22b]

end VanCraenenbroeck2014.Examples
