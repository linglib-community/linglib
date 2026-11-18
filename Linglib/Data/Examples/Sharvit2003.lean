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
    contrasts := []
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
    contrasts := []
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
    contrasts := []
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
    contrasts := []
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
    contrasts := []
    readings := [("double access: the pregnancy contains the finding out and the utterance time", .unacceptable)]
    paperFeatures := [("language", "english"), ("matrix", "past"), ("embedded", "present"), ("nonpast", "no")] }

def ex5 : Datum :=
  { id := "sharvit2003_ex5"
    source := ⟨"sharvit-2003", "(5)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "Lifney šavua, Dan hexlit še be'od asara yamim, bizman aruxat ha-boker, hu yomar le-imo še hu mitga'agea ele-ha."
    glossedTokens := [("Lifney", "before"), ("šavua", "week"), ("Dan", "Dan"), ("hexlit", "decide-PAST"), ("še", "that"), ("be'od", "in"), ("asara", "ten"), ("yamim", "days"), ("bizman", "at-time"), ("aruxat ha-boker", "the-breakfast"), ("hu", "he"), ("yomar", "will-tell"), ("le-imo", "to-his-mother"), ("še", "that"), ("hu", "he"), ("mitga'agea", "miss-PRES"), ("ele-ha", "to-her")]
    glossedWords := [⟨['L', 'i', 'f', 'n', 'e', 'y'], ['b', 'e', 'f', 'o', 'r', 'e'], [⟨['L', 'i', 'f', 'n', 'e', 'y'], ['b', 'e', 'f', 'o', 'r', 'e'], none⟩]⟩, ⟨['š', 'a', 'v', 'u', 'a'], ['w', 'e', 'e', 'k'], [⟨['š', 'a', 'v', 'u', 'a'], ['w', 'e', 'e', 'k'], none⟩]⟩, ⟨['D', 'a', 'n'], ['D', 'a', 'n'], [⟨['D', 'a', 'n'], ['D', 'a', 'n'], none⟩]⟩, ⟨['h', 'e', 'x', 'l', 'i', 't'], ['d', 'e', 'c', 'i', 'd', 'e', '-', 'P', 'A', 'S', 'T'], []⟩, ⟨['š', 'e'], ['t', 'h', 'a', 't'], [⟨['š', 'e'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['b', 'e', '\'', 'o', 'd'], ['i', 'n'], [⟨['b', 'e', '\'', 'o', 'd'], ['i', 'n'], none⟩]⟩, ⟨['a', 's', 'a', 'r', 'a'], ['t', 'e', 'n'], [⟨['a', 's', 'a', 'r', 'a'], ['t', 'e', 'n'], none⟩]⟩, ⟨['y', 'a', 'm', 'i', 'm'], ['d', 'a', 'y', 's'], [⟨['y', 'a', 'm', 'i', 'm'], ['d', 'a', 'y', 's'], none⟩]⟩, ⟨['b', 'i', 'z', 'm', 'a', 'n'], ['a', 't', '-', 't', 'i', 'm', 'e'], []⟩, ⟨['a', 'r', 'u', 'x', 'a', 't', ' ', 'h', 'a', '-', 'b', 'o', 'k', 'e', 'r'], ['t', 'h', 'e', '-', 'b', 'r', 'e', 'a', 'k', 'f', 'a', 's', 't'], [⟨['a', 'r', 'u', 'x', 'a', 't', ' ', 'h', 'a'], ['t', 'h', 'e'], none⟩, ⟨['b', 'o', 'k', 'e', 'r'], ['b', 'r', 'e', 'a', 'k', 'f', 'a', 's', 't'], some '-'⟩]⟩, ⟨['h', 'u'], ['h', 'e'], [⟨['h', 'u'], ['h', 'e'], none⟩]⟩, ⟨['y', 'o', 'm', 'a', 'r'], ['w', 'i', 'l', 'l', '-', 't', 'e', 'l', 'l'], []⟩, ⟨['l', 'e', '-', 'i', 'm', 'o'], ['t', 'o', '-', 'h', 'i', 's', '-', 'm', 'o', 't', 'h', 'e', 'r'], []⟩, ⟨['š', 'e'], ['t', 'h', 'a', 't'], [⟨['š', 'e'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['h', 'u'], ['h', 'e'], [⟨['h', 'u'], ['h', 'e'], none⟩]⟩, ⟨['m', 'i', 't', 'g', 'a', '\'', 'a', 'g', 'e', 'a'], ['m', 'i', 's', 's', '-', 'P', 'R', 'E', 'S'], []⟩, ⟨['e', 'l', 'e', '-', 'h', 'a'], ['t', 'o', '-', 'h', 'e', 'r'], [⟨['e', 'l', 'e'], ['t', 'o'], none⟩, ⟨['h', 'a'], ['h', 'e', 'r'], some '-'⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("nonpast: the telling overlaps the missing", .acceptable)]
    paperFeatures := [("language", "hebrew"), ("matrix", "past"), ("embedded", "present"), ("nonpast", "yes")] }

def ex6 : Datum :=
  { id := "sharvit2003_ex6"
    source := ⟨"sharvit-2003", "(6)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "Lifney šavua, Dan hexlit še be'od asara yamim, bizman aruxat ha-boker, hu yomar le-imo še hu hitga'agea ele-ha."
    glossedTokens := [("Lifney", "before"), ("šavua", "week"), ("Dan", "Dan"), ("hexlit", "decide-PAST"), ("še", "that"), ("be'od", "in"), ("asara", "ten"), ("yamim", "days"), ("bizman", "at-time"), ("aruxat ha-boker", "the-breakfast"), ("hu", "he"), ("yomar", "will-tell"), ("le-imo", "to-his-mother"), ("še", "that"), ("hu", "he"), ("hitga'agea", "miss-PAST"), ("ele-ha", "to-her")]
    glossedWords := [⟨['L', 'i', 'f', 'n', 'e', 'y'], ['b', 'e', 'f', 'o', 'r', 'e'], [⟨['L', 'i', 'f', 'n', 'e', 'y'], ['b', 'e', 'f', 'o', 'r', 'e'], none⟩]⟩, ⟨['š', 'a', 'v', 'u', 'a'], ['w', 'e', 'e', 'k'], [⟨['š', 'a', 'v', 'u', 'a'], ['w', 'e', 'e', 'k'], none⟩]⟩, ⟨['D', 'a', 'n'], ['D', 'a', 'n'], [⟨['D', 'a', 'n'], ['D', 'a', 'n'], none⟩]⟩, ⟨['h', 'e', 'x', 'l', 'i', 't'], ['d', 'e', 'c', 'i', 'd', 'e', '-', 'P', 'A', 'S', 'T'], []⟩, ⟨['š', 'e'], ['t', 'h', 'a', 't'], [⟨['š', 'e'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['b', 'e', '\'', 'o', 'd'], ['i', 'n'], [⟨['b', 'e', '\'', 'o', 'd'], ['i', 'n'], none⟩]⟩, ⟨['a', 's', 'a', 'r', 'a'], ['t', 'e', 'n'], [⟨['a', 's', 'a', 'r', 'a'], ['t', 'e', 'n'], none⟩]⟩, ⟨['y', 'a', 'm', 'i', 'm'], ['d', 'a', 'y', 's'], [⟨['y', 'a', 'm', 'i', 'm'], ['d', 'a', 'y', 's'], none⟩]⟩, ⟨['b', 'i', 'z', 'm', 'a', 'n'], ['a', 't', '-', 't', 'i', 'm', 'e'], []⟩, ⟨['a', 'r', 'u', 'x', 'a', 't', ' ', 'h', 'a', '-', 'b', 'o', 'k', 'e', 'r'], ['t', 'h', 'e', '-', 'b', 'r', 'e', 'a', 'k', 'f', 'a', 's', 't'], [⟨['a', 'r', 'u', 'x', 'a', 't', ' ', 'h', 'a'], ['t', 'h', 'e'], none⟩, ⟨['b', 'o', 'k', 'e', 'r'], ['b', 'r', 'e', 'a', 'k', 'f', 'a', 's', 't'], some '-'⟩]⟩, ⟨['h', 'u'], ['h', 'e'], [⟨['h', 'u'], ['h', 'e'], none⟩]⟩, ⟨['y', 'o', 'm', 'a', 'r'], ['w', 'i', 'l', 'l', '-', 't', 'e', 'l', 'l'], []⟩, ⟨['l', 'e', '-', 'i', 'm', 'o'], ['t', 'o', '-', 'h', 'i', 's', '-', 'm', 'o', 't', 'h', 'e', 'r'], []⟩, ⟨['š', 'e'], ['t', 'h', 'a', 't'], [⟨['š', 'e'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['h', 'u'], ['h', 'e'], [⟨['h', 'u'], ['h', 'e'], none⟩]⟩, ⟨['h', 'i', 't', 'g', 'a', '\'', 'a', 'g', 'e', 'a'], ['m', 'i', 's', 's', '-', 'P', 'A', 'S', 'T'], []⟩, ⟨['e', 'l', 'e', '-', 'h', 'a'], ['t', 'o', '-', 'h', 'e', 'r'], [⟨['e', 'l', 'e'], ['t', 'o'], none⟩, ⟨['h', 'a'], ['h', 'e', 'r'], some '-'⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("anteriority: the missing precedes the telling", .acceptable), ("nonpast: the telling overlaps the missing", .ungrammatical)]
    paperFeatures := [("language", "hebrew"), ("matrix", "past"), ("embedded", "past"), ("nonpast", "no")] }

def ex12a : Datum :=
  { id := "sharvit2003_ex12a"
    source := ⟨"sharvit-2003", "(12a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "To 1963 o Kostas mas ipe oti i Maria ine eggios."
    glossedTokens := [("To", "the"), ("1963", "1963"), ("o", "the"), ("Kostas", "Kostas"), ("mas", "us"), ("ipe", "told"), ("oti", "that"), ("i", "the"), ("Maria", "Maria"), ("ine", "is"), ("eggios", "pregnant")]
    glossedWords := [⟨['T', 'o'], ['t', 'h', 'e'], [⟨['T', 'o'], ['t', 'h', 'e'], none⟩]⟩, ⟨['1', '9', '6', '3'], ['1', '9', '6', '3'], [⟨['1', '9', '6', '3'], ['1', '9', '6', '3'], none⟩]⟩, ⟨['o'], ['t', 'h', 'e'], [⟨['o'], ['t', 'h', 'e'], none⟩]⟩, ⟨['K', 'o', 's', 't', 'a', 's'], ['K', 'o', 's', 't', 'a', 's'], [⟨['K', 'o', 's', 't', 'a', 's'], ['K', 'o', 's', 't', 'a', 's'], none⟩]⟩, ⟨['m', 'a', 's'], ['u', 's'], [⟨['m', 'a', 's'], ['u', 's'], none⟩]⟩, ⟨['i', 'p', 'e'], ['t', 'o', 'l', 'd'], [⟨['i', 'p', 'e'], ['t', 'o', 'l', 'd'], none⟩]⟩, ⟨['o', 't', 'i'], ['t', 'h', 'a', 't'], [⟨['o', 't', 'i'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['i'], ['t', 'h', 'e'], [⟨['i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['i', 'n', 'e'], ['i', 's'], [⟨['i', 'n', 'e'], ['i', 's'], none⟩]⟩, ⟨['e', 'g', 'g', 'i', 'o', 's'], ['p', 'r', 'e', 'g', 'n', 'a', 'n', 't'], [⟨['e', 'g', 'g', 'i', 'o', 's'], ['p', 'r', 'e', 'g', 'n', 'a', 'n', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("nonpast: the pregnancy overlaps the telling", .acceptable)]
    paperFeatures := [("language", "greek"), ("matrix", "past"), ("embedded", "present"), ("nonpast", "yes")] }

def ex12b : Datum :=
  { id := "sharvit2003_ex12b"
    source := ⟨"sharvit-2003", "(12b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "To 1963 o Kostas mas ipe oti i Maria itan eggios."
    glossedTokens := [("To", "the"), ("1963", "1963"), ("o", "the"), ("Kostas", "Kostas"), ("mas", "us"), ("ipe", "told"), ("oti", "that"), ("i", "the"), ("Maria", "Maria"), ("itan", "was"), ("eggios", "pregnant")]
    glossedWords := [⟨['T', 'o'], ['t', 'h', 'e'], [⟨['T', 'o'], ['t', 'h', 'e'], none⟩]⟩, ⟨['1', '9', '6', '3'], ['1', '9', '6', '3'], [⟨['1', '9', '6', '3'], ['1', '9', '6', '3'], none⟩]⟩, ⟨['o'], ['t', 'h', 'e'], [⟨['o'], ['t', 'h', 'e'], none⟩]⟩, ⟨['K', 'o', 's', 't', 'a', 's'], ['K', 'o', 's', 't', 'a', 's'], [⟨['K', 'o', 's', 't', 'a', 's'], ['K', 'o', 's', 't', 'a', 's'], none⟩]⟩, ⟨['m', 'a', 's'], ['u', 's'], [⟨['m', 'a', 's'], ['u', 's'], none⟩]⟩, ⟨['i', 'p', 'e'], ['t', 'o', 'l', 'd'], [⟨['i', 'p', 'e'], ['t', 'o', 'l', 'd'], none⟩]⟩, ⟨['o', 't', 'i'], ['t', 'h', 'a', 't'], [⟨['o', 't', 'i'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['i'], ['t', 'h', 'e'], [⟨['i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['i', 't', 'a', 'n'], ['w', 'a', 's'], [⟨['i', 't', 'a', 'n'], ['w', 'a', 's'], none⟩]⟩, ⟨['e', 'g', 'g', 'i', 'o', 's'], ['p', 'r', 'e', 'g', 'n', 'a', 'n', 't'], [⟨['e', 'g', 'g', 'i', 'o', 's'], ['p', 'r', 'e', 'g', 'n', 'a', 'n', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("nonpast: the pregnancy overlaps the telling", .acceptable)]
    paperFeatures := [("language", "greek"), ("matrix", "past"), ("embedded", "past"), ("nonpast", "yes")] }

def all : List Datum := [ex1, ex2, ex3, ex4a, ex4b, ex5, ex6, ex12a, ex12b]

end Sharvit2003.Examples
