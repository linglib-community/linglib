module

public import Linglib.Data.Examples.Schema

/-!
# `Sharvit2003` — typed example data

Auto-generated from `Linglib/Data/Examples/Sharvit2003.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Sharvit2003.Examples`.
-/

@[expose] public section

namespace Sharvit2003.Examples

def ex1 : Datum :=
  { id := "sharvit2003_ex1"
    source := ⟨"sharvit-2003", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A week ago, John decided that in ten days, at breakfast, he would tell his mother that he missed her."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("nonpast: the telling overlaps the missing", .acceptable), ("anteriority: the missing precedes the telling", .acceptable)]
    paperFeatures := [("language", "english"), ("matrix", "past"), ("embedded", "past"), ("nonpast", "yes")] }

def ex2 : Datum :=
  { id := "sharvit2003_ex2"
    source := ⟨"sharvit-2003", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John believed that Mary was pregnant."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("nonpast: the pregnancy overlaps John's now", .acceptable), ("anteriority: the pregnancy precedes John's now", .acceptable)]
    paperFeatures := [("language", "english"), ("matrix", "past"), ("embedded", "past"), ("nonpast", "yes")] }

def ex3 : Datum :=
  { id := "sharvit2003_ex3"
    source := ⟨"sharvit-2003", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John believed that Mary is pregnant."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("double access: the pregnancy contains the believing time and the utterance time", .acceptable), ("nonpast: the pregnancy overlaps John's now only", .ungrammatical)]
    paperFeatures := [("language", "english"), ("matrix", "past"), ("embedded", "present"), ("nonpast", "no")] }

def ex4a : Datum :=
  { id := "sharvit2003_ex4a"
    source := ⟨"sharvit-2003", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Two years ago, Sally found out that Mary was pregnant."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("nonpast: the pregnancy overlaps the finding out", .acceptable)]
    paperFeatures := [("language", "english"), ("matrix", "past"), ("embedded", "past"), ("nonpast", "yes")] }

def ex4b : Datum :=
  { id := "sharvit2003_ex4b"
    source := ⟨"sharvit-2003", "(4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Two years ago, Sally found out that Mary is pregnant."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := [("double access: the pregnancy contains the finding out and the utterance time", .unacceptable)]
    paperFeatures := [("language", "english"), ("matrix", "past"), ("embedded", "present"), ("nonpast", "no")] }

def ex5 : Datum :=
  { id := "sharvit2003_ex5"
    source := ⟨"sharvit-2003", "(5)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "Lifney šavua, Dan hexlit še be'od asara yamim, bizman aruxat ha-boker, hu yomar le-imo še hu mitga'agea ele-ha."
    glossedTokens := [("Lifney", "before"), ("šavua", "week"), ("Dan", "Dan"), ("hexlit", "decide-PAST"), ("še", "that"), ("be'od", "in"), ("asara", "ten"), ("yamim", "days"), ("bizman", "at-time"), ("aruxat ha-boker", "the-breakfast"), ("hu", "he"), ("yomar", "will-tell"), ("le-imo", "to-his-mother"), ("še", "that"), ("hu", "he"), ("mitga'agea", "miss-PRES"), ("ele-ha", "to-her")]
    glossedWords := [⟨[['L', 'i', 'f', 'n', 'e', 'y']], [['b', 'e', 'f', 'o', 'r', 'e']]⟩, ⟨[['š', 'a', 'v', 'u', 'a']], [['w', 'e', 'e', 'k']]⟩, ⟨[['D', 'a', 'n']], [['D', 'a', 'n']]⟩, ⟨[['h', 'e', 'x', 'l', 'i', 't']], [['d', 'e', 'c', 'i', 'd', 'e'], ['P', 'A', 'S', 'T']]⟩, ⟨[['š', 'e']], [['t', 'h', 'a', 't']]⟩, ⟨[['b', 'e', '\'', 'o', 'd']], [['i', 'n']]⟩, ⟨[['a', 's', 'a', 'r', 'a']], [['t', 'e', 'n']]⟩, ⟨[['y', 'a', 'm', 'i', 'm']], [['d', 'a', 'y', 's']]⟩, ⟨[['b', 'i', 'z', 'm', 'a', 'n']], [['a', 't'], ['t', 'i', 'm', 'e']]⟩, ⟨[['a', 'r', 'u', 'x', 'a', 't', ' ', 'h', 'a'], ['b', 'o', 'k', 'e', 'r']], [['t', 'h', 'e'], ['b', 'r', 'e', 'a', 'k', 'f', 'a', 's', 't']]⟩, ⟨[['h', 'u']], [['h', 'e']]⟩, ⟨[['y', 'o', 'm', 'a', 'r']], [['w', 'i', 'l', 'l'], ['t', 'e', 'l', 'l']]⟩, ⟨[['l', 'e'], ['i', 'm', 'o']], [['t', 'o'], ['h', 'i', 's'], ['m', 'o', 't', 'h', 'e', 'r']]⟩, ⟨[['š', 'e']], [['t', 'h', 'a', 't']]⟩, ⟨[['h', 'u']], [['h', 'e']]⟩, ⟨[['m', 'i', 't', 'g', 'a', '\'', 'a', 'g', 'e', 'a']], [['m', 'i', 's', 's'], ['P', 'R', 'E', 'S']]⟩, ⟨[['e', 'l', 'e'], ['h', 'a']], [['t', 'o'], ['h', 'e', 'r']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("nonpast: the telling overlaps the missing", .acceptable)]
    paperFeatures := [("language", "hebrew"), ("matrix", "past"), ("embedded", "present"), ("nonpast", "yes")] }

def ex6 : Datum :=
  { id := "sharvit2003_ex6"
    source := ⟨"sharvit-2003", "(6)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "Lifney šavua, Dan hexlit še be'od asara yamim, bizman aruxat ha-boker, hu yomar le-imo še hu hitga'agea ele-ha."
    glossedTokens := [("Lifney", "before"), ("šavua", "week"), ("Dan", "Dan"), ("hexlit", "decide-PAST"), ("še", "that"), ("be'od", "in"), ("asara", "ten"), ("yamim", "days"), ("bizman", "at-time"), ("aruxat ha-boker", "the-breakfast"), ("hu", "he"), ("yomar", "will-tell"), ("le-imo", "to-his-mother"), ("še", "that"), ("hu", "he"), ("hitga'agea", "miss-PAST"), ("ele-ha", "to-her")]
    glossedWords := [⟨[['L', 'i', 'f', 'n', 'e', 'y']], [['b', 'e', 'f', 'o', 'r', 'e']]⟩, ⟨[['š', 'a', 'v', 'u', 'a']], [['w', 'e', 'e', 'k']]⟩, ⟨[['D', 'a', 'n']], [['D', 'a', 'n']]⟩, ⟨[['h', 'e', 'x', 'l', 'i', 't']], [['d', 'e', 'c', 'i', 'd', 'e'], ['P', 'A', 'S', 'T']]⟩, ⟨[['š', 'e']], [['t', 'h', 'a', 't']]⟩, ⟨[['b', 'e', '\'', 'o', 'd']], [['i', 'n']]⟩, ⟨[['a', 's', 'a', 'r', 'a']], [['t', 'e', 'n']]⟩, ⟨[['y', 'a', 'm', 'i', 'm']], [['d', 'a', 'y', 's']]⟩, ⟨[['b', 'i', 'z', 'm', 'a', 'n']], [['a', 't'], ['t', 'i', 'm', 'e']]⟩, ⟨[['a', 'r', 'u', 'x', 'a', 't', ' ', 'h', 'a'], ['b', 'o', 'k', 'e', 'r']], [['t', 'h', 'e'], ['b', 'r', 'e', 'a', 'k', 'f', 'a', 's', 't']]⟩, ⟨[['h', 'u']], [['h', 'e']]⟩, ⟨[['y', 'o', 'm', 'a', 'r']], [['w', 'i', 'l', 'l'], ['t', 'e', 'l', 'l']]⟩, ⟨[['l', 'e'], ['i', 'm', 'o']], [['t', 'o'], ['h', 'i', 's'], ['m', 'o', 't', 'h', 'e', 'r']]⟩, ⟨[['š', 'e']], [['t', 'h', 'a', 't']]⟩, ⟨[['h', 'u']], [['h', 'e']]⟩, ⟨[['h', 'i', 't', 'g', 'a', '\'', 'a', 'g', 'e', 'a']], [['m', 'i', 's', 's'], ['P', 'A', 'S', 'T']]⟩, ⟨[['e', 'l', 'e'], ['h', 'a']], [['t', 'o'], ['h', 'e', 'r']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("anteriority: the missing precedes the telling", .acceptable), ("nonpast: the telling overlaps the missing", .ungrammatical)]
    paperFeatures := [("language", "hebrew"), ("matrix", "past"), ("embedded", "past"), ("nonpast", "no")] }

def ex12a : Datum :=
  { id := "sharvit2003_ex12a"
    source := ⟨"sharvit-2003", "(12a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "To 1963 o Kostas mas ipe oti i Maria ine eggios."
    glossedTokens := [("To", "the"), ("1963", "1963"), ("o", "the"), ("Kostas", "Kostas"), ("mas", "us"), ("ipe", "told"), ("oti", "that"), ("i", "the"), ("Maria", "Maria"), ("ine", "is"), ("eggios", "pregnant")]
    glossedWords := [⟨[['T', 'o']], [['t', 'h', 'e']]⟩, ⟨[['1', '9', '6', '3']], [['1', '9', '6', '3']]⟩, ⟨[['o']], [['t', 'h', 'e']]⟩, ⟨[['K', 'o', 's', 't', 'a', 's']], [['K', 'o', 's', 't', 'a', 's']]⟩, ⟨[['m', 'a', 's']], [['u', 's']]⟩, ⟨[['i', 'p', 'e']], [['t', 'o', 'l', 'd']]⟩, ⟨[['o', 't', 'i']], [['t', 'h', 'a', 't']]⟩, ⟨[['i']], [['t', 'h', 'e']]⟩, ⟨[['M', 'a', 'r', 'i', 'a']], [['M', 'a', 'r', 'i', 'a']]⟩, ⟨[['i', 'n', 'e']], [['i', 's']]⟩, ⟨[['e', 'g', 'g', 'i', 'o', 's']], [['p', 'r', 'e', 'g', 'n', 'a', 'n', 't']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("nonpast: the pregnancy overlaps the telling", .acceptable)]
    paperFeatures := [("language", "greek"), ("matrix", "past"), ("embedded", "present"), ("nonpast", "yes")] }

def ex12b : Datum :=
  { id := "sharvit2003_ex12b"
    source := ⟨"sharvit-2003", "(12b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "To 1963 o Kostas mas ipe oti i Maria itan eggios."
    glossedTokens := [("To", "the"), ("1963", "1963"), ("o", "the"), ("Kostas", "Kostas"), ("mas", "us"), ("ipe", "told"), ("oti", "that"), ("i", "the"), ("Maria", "Maria"), ("itan", "was"), ("eggios", "pregnant")]
    glossedWords := [⟨[['T', 'o']], [['t', 'h', 'e']]⟩, ⟨[['1', '9', '6', '3']], [['1', '9', '6', '3']]⟩, ⟨[['o']], [['t', 'h', 'e']]⟩, ⟨[['K', 'o', 's', 't', 'a', 's']], [['K', 'o', 's', 't', 'a', 's']]⟩, ⟨[['m', 'a', 's']], [['u', 's']]⟩, ⟨[['i', 'p', 'e']], [['t', 'o', 'l', 'd']]⟩, ⟨[['o', 't', 'i']], [['t', 'h', 'a', 't']]⟩, ⟨[['i']], [['t', 'h', 'e']]⟩, ⟨[['M', 'a', 'r', 'i', 'a']], [['M', 'a', 'r', 'i', 'a']]⟩, ⟨[['i', 't', 'a', 'n']], [['w', 'a', 's']]⟩, ⟨[['e', 'g', 'g', 'i', 'o', 's']], [['p', 'r', 'e', 'g', 'n', 'a', 'n', 't']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("nonpast: the pregnancy overlaps the telling", .acceptable)]
    paperFeatures := [("language", "greek"), ("matrix", "past"), ("embedded", "past"), ("nonpast", "yes")] }

def all : List Datum := [ex1, ex2, ex3, ex4a, ex4b, ex5, ex6, ex12a, ex12b]

end Sharvit2003.Examples
