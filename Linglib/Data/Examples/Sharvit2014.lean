module

public import Linglib.Data.Examples.Schema

/-!
# `Sharvit2014` — typed example data

Auto-generated from `Linglib/Data/Examples/Sharvit2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Sharvit2014.Examples`.
-/

@[expose] public section

namespace Sharvit2014.Examples

def ex_1 : Datum :=
  { id := "sharvit2014_1"
    source := ⟨"sharvit-2014", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John left the meeting before Mary arrived."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "before"), ("embedded", "past")] }

def ex_2 : Datum :=
  { id := "sharvit2014_2"
    source := ⟨"sharvit-2014", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John left the meeting before Mary arrives."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "before"), ("embedded", "present")] }

def ex_3 : Datum :=
  { id := "sharvit2014_3"
    source := ⟨"sharvit-2014", "(3)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-wa Hanako-ni at-ta mae-ni denwa-o si-ta."
    glossedTokens := [("Taroo-wa", "Taro-TOP"), ("Hanako-ni", "Hanako-DAT"), ("at-ta", "meet-PAST"), ("mae-ni", "before"), ("denwa-o", "phone-ACC"), ("si-ta", "do-PAST")]
    glossedWords := [⟨[['T', 'a', 'r', 'o', 'o'], ['w', 'a']], [['T', 'a', 'r', 'o'], ['T', 'O', 'P']]⟩, ⟨[['H', 'a', 'n', 'a', 'k', 'o'], ['n', 'i']], [['H', 'a', 'n', 'a', 'k', 'o'], ['D', 'A', 'T']]⟩, ⟨[['a', 't'], ['t', 'a']], [['m', 'e', 'e', 't'], ['P', 'A', 'S', 'T']]⟩, ⟨[['m', 'a', 'e'], ['n', 'i']], [['b', 'e', 'f', 'o', 'r', 'e']]⟩, ⟨[['d', 'e', 'n', 'w', 'a'], ['o']], [['p', 'h', 'o', 'n', 'e'], ['A', 'C', 'C']]⟩, ⟨[['s', 'i'], ['t', 'a']], [['d', 'o'], ['P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "before"), ("embedded", "past")] }

def ex_4 : Datum :=
  { id := "sharvit2014_4"
    source := ⟨"sharvit-2014", "(4)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-wa Hanako-ni au mae-ni denwa-o si-ta."
    glossedTokens := [("Taroo-wa", "Taro-TOP"), ("Hanako-ni", "Hanako-DAT"), ("au", "meet-PRES"), ("mae-ni", "before"), ("denwa-o", "phone-ACC"), ("si-ta", "do-PAST")]
    glossedWords := [⟨[['T', 'a', 'r', 'o', 'o'], ['w', 'a']], [['T', 'a', 'r', 'o'], ['T', 'O', 'P']]⟩, ⟨[['H', 'a', 'n', 'a', 'k', 'o'], ['n', 'i']], [['H', 'a', 'n', 'a', 'k', 'o'], ['D', 'A', 'T']]⟩, ⟨[['a', 'u']], [['m', 'e', 'e', 't'], ['P', 'R', 'E', 'S']]⟩, ⟨[['m', 'a', 'e'], ['n', 'i']], [['b', 'e', 'f', 'o', 'r', 'e']]⟩, ⟨[['d', 'e', 'n', 'w', 'a'], ['o']], [['p', 'h', 'o', 'n', 'e'], ['A', 'C', 'C']]⟩, ⟨[['s', 'i'], ['t', 'a']], [['d', 'o'], ['P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "before"), ("embedded", "present")] }

def ex_5 : Datum :=
  { id := "sharvit2014_5"
    source := ⟨"sharvit-2014", "(5)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Ania przyszła na przyjęcie zanim Marcin przyszedł."
    glossedTokens := [("Ania", "Ania"), ("przyszła", "PRF-come-PAST"), ("na", "to"), ("przyjęcie", "party"), ("zanim", "before"), ("Marcin", "Marcin"), ("przyszedł", "PRF-come PAST")]
    glossedWords := [⟨[['A', 'n', 'i', 'a']], [['A', 'n', 'i', 'a']]⟩, ⟨[['p', 'r', 'z', 'y', 's', 'z', 'ł', 'a']], [['P', 'R', 'F'], ['c', 'o', 'm', 'e'], ['P', 'A', 'S', 'T']]⟩, ⟨[['n', 'a']], [['t', 'o']]⟩, ⟨[['p', 'r', 'z', 'y', 'j', 'ę', 'c', 'i', 'e']], [['p', 'a', 'r', 't', 'y']]⟩, ⟨[['z', 'a', 'n', 'i', 'm']], [['b', 'e', 'f', 'o', 'r', 'e']]⟩, ⟨[['M', 'a', 'r', 'c', 'i', 'n']], [['M', 'a', 'r', 'c', 'i', 'n']]⟩, ⟨[['p', 'r', 'z', 'y', 's', 'z', 'e', 'd', 'ł']], [['P', 'R', 'F'], ['c', 'o', 'm', 'e', ' ', 'P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "before"), ("embedded", "past")] }

def ex_6 : Datum :=
  { id := "sharvit2014_6"
    source := ⟨"sharvit-2014", "(6)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Ania przyszła na przyjęcie zanim Marcin przychodzi."
    glossedTokens := [("Ania", "Ania"), ("przyszła", "PRF-come-PAST"), ("na", "to"), ("przyjęcie", "party"), ("zanim", "before"), ("Marcin", "Marcin"), ("przychodzi", "PRF-come PRES")]
    glossedWords := [⟨[['A', 'n', 'i', 'a']], [['A', 'n', 'i', 'a']]⟩, ⟨[['p', 'r', 'z', 'y', 's', 'z', 'ł', 'a']], [['P', 'R', 'F'], ['c', 'o', 'm', 'e'], ['P', 'A', 'S', 'T']]⟩, ⟨[['n', 'a']], [['t', 'o']]⟩, ⟨[['p', 'r', 'z', 'y', 'j', 'ę', 'c', 'i', 'e']], [['p', 'a', 'r', 't', 'y']]⟩, ⟨[['z', 'a', 'n', 'i', 'm']], [['b', 'e', 'f', 'o', 'r', 'e']]⟩, ⟨[['M', 'a', 'r', 'c', 'i', 'n']], [['M', 'a', 'r', 'c', 'i', 'n']]⟩, ⟨[['p', 'r', 'z', 'y', 'c', 'h', 'o', 'd', 'z', 'i']], [['P', 'R', 'F'], ['c', 'o', 'm', 'e', ' ', 'P', 'R', 'E', 'S']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "before"), ("embedded", "present")] }

def ex_7 : Datum :=
  { id := "sharvit2014_7"
    source := ⟨"sharvit-2014", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John said that Mary was sick."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .acceptable), ("back-shifted", .acceptable)]
    paperFeatures := [("construction", "attitude"), ("embedded", "past")] }

def ex_8a : Datum :=
  { id := "sharvit2014_8a"
    source := ⟨"sharvit-2014", "(8a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-wa Hanako-ga byooki-da-to it-ta."
    glossedTokens := [("Taroo-wa", "Taro-TOP"), ("Hanako-ga", "Hanako-NOM"), ("byooki-da", "be-sick-PRES"), ("-to", "that"), ("it-ta", "say-PAST")]
    glossedWords := [⟨[['T', 'a', 'r', 'o', 'o'], ['w', 'a']], [['T', 'a', 'r', 'o'], ['T', 'O', 'P']]⟩, ⟨[['H', 'a', 'n', 'a', 'k', 'o'], ['g', 'a']], [['H', 'a', 'n', 'a', 'k', 'o'], ['N', 'O', 'M']]⟩, ⟨[['b', 'y', 'o', 'o', 'k', 'i'], ['d', 'a']], [['b', 'e'], ['s', 'i', 'c', 'k'], ['P', 'R', 'E', 'S']]⟩, ⟨[[], ['t', 'o']], [['t', 'h', 'a', 't']]⟩, ⟨[['i', 't'], ['t', 'a']], [['s', 'a', 'y'], ['P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .acceptable)]
    paperFeatures := [("construction", "attitude"), ("embedded", "present")] }

def ex_8b : Datum :=
  { id := "sharvit2014_8b"
    source := ⟨"sharvit-2014", "(8b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-wa Hanako-ga byooki-datta-to it-ta."
    glossedTokens := [("Taroo-wa", "Taro-TOP"), ("Hanako-ga", "Hanako-NOM"), ("byooki-datta", "be-sick-PAST"), ("-to", "that"), ("it-ta", "say-PAST")]
    glossedWords := [⟨[['T', 'a', 'r', 'o', 'o'], ['w', 'a']], [['T', 'a', 'r', 'o'], ['T', 'O', 'P']]⟩, ⟨[['H', 'a', 'n', 'a', 'k', 'o'], ['g', 'a']], [['H', 'a', 'n', 'a', 'k', 'o'], ['N', 'O', 'M']]⟩, ⟨[['b', 'y', 'o', 'o', 'k', 'i'], ['d', 'a', 't', 't', 'a']], [['b', 'e'], ['s', 'i', 'c', 'k'], ['P', 'A', 'S', 'T']]⟩, ⟨[[], ['t', 'o']], [['t', 'h', 'a', 't']]⟩, ⟨[['i', 't'], ['t', 'a']], [['s', 'a', 'y'], ['P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .unacceptable), ("back-shifted", .acceptable)]
    paperFeatures := [("construction", "attitude"), ("embedded", "past")] }

def ex_9a : Datum :=
  { id := "sharvit2014_9a"
    source := ⟨"sharvit-2014", "(9a)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Ania powiedziała że Marcin jest chory."
    glossedTokens := [("Ania", "Ania"), ("powiedziała", "say-PRF-PAST"), ("że", "that"), ("Marcin", "Marcin"), ("jest", "be-PRES"), ("chory", "sick")]
    glossedWords := [⟨[['A', 'n', 'i', 'a']], [['A', 'n', 'i', 'a']]⟩, ⟨[['p', 'o', 'w', 'i', 'e', 'd', 'z', 'i', 'a', 'ł', 'a']], [['s', 'a', 'y'], ['P', 'R', 'F'], ['P', 'A', 'S', 'T']]⟩, ⟨[['ż', 'e']], [['t', 'h', 'a', 't']]⟩, ⟨[['M', 'a', 'r', 'c', 'i', 'n']], [['M', 'a', 'r', 'c', 'i', 'n']]⟩, ⟨[['j', 'e', 's', 't']], [['b', 'e'], ['P', 'R', 'E', 'S']]⟩, ⟨[['c', 'h', 'o', 'r', 'y']], [['s', 'i', 'c', 'k']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .acceptable)]
    paperFeatures := [("construction", "attitude"), ("embedded", "present")] }

def ex_9b : Datum :=
  { id := "sharvit2014_9b"
    source := ⟨"sharvit-2014", "(9b)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Ania powiedziała że Marcin był chory."
    glossedTokens := [("Ania", "Ania"), ("powiedziała", "say-PRF-PAST"), ("że", "that"), ("Marcin", "Marcin"), ("był", "be-PAST"), ("chory", "sick")]
    glossedWords := [⟨[['A', 'n', 'i', 'a']], [['A', 'n', 'i', 'a']]⟩, ⟨[['p', 'o', 'w', 'i', 'e', 'd', 'z', 'i', 'a', 'ł', 'a']], [['s', 'a', 'y'], ['P', 'R', 'F'], ['P', 'A', 'S', 'T']]⟩, ⟨[['ż', 'e']], [['t', 'h', 'a', 't']]⟩, ⟨[['M', 'a', 'r', 'c', 'i', 'n']], [['M', 'a', 'r', 'c', 'i', 'n']]⟩, ⟨[['b', 'y', 'ł']], [['b', 'e'], ['P', 'A', 'S', 'T']]⟩, ⟨[['c', 'h', 'o', 'r', 'y']], [['s', 'i', 'c', 'k']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .unacceptable), ("back-shifted", .acceptable)]
    paperFeatures := [("construction", "attitude"), ("embedded", "past")] }

def ex_46 : Datum :=
  { id := "sharvit2014_46"
    source := ⟨"sharvit-2014", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John found out that Mary is sick."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .unacceptable), ("double access", .acceptable)]
    paperFeatures := [("construction", "attitude"), ("embedded", "present")] }

def ex_50b_did : Datum :=
  { id := "sharvit2014_50b_did"
    source := ⟨"sharvit-2014", "(50b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John left before Sally arrived, which she did this morning."
    glossedTokens := []
    context := "John's leaving and Sally's arrival are independent of each other."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "before"), ("embedded", "past"), ("clauseTime", "before speech")] }

def ex_50b_will : Datum :=
  { id := "sharvit2014_50b_will"
    source := ⟨"sharvit-2014", "(50b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John left before Sally arrived, which she will tomorrow."
    glossedTokens := []
    context := "John's leaving and Sally's arrival are independent of each other."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "before"), ("embedded", "past"), ("clauseTime", "after speech")] }

def ex_51 : Datum :=
  { id := "sharvit2014_51"
    source := ⟨"sharvit-2014", "(51)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Mary-wa asu toochakusu-ru koto-ni nat-te i-ru. dakara, John-ga Mary-ga toochakusu-ru maeni syuppatsusi-ta to iu koto-wa hontoo-da."
    glossedTokens := [("Mary-wa", "Mary-TOP"), ("asu", "tomorrow"), ("toochakusu-ru", "arrive-PRES"), ("koto-ni", "fact-DAT"), ("nat-te", "become-GER"), ("i-ru", "be-PRES"), ("dakara,", "So"), ("John-ga", "John-NOM"), ("Mary-ga", "Mary-NOM"), ("toochakusu-ru", "arrive-PRES"), ("maeni", "before"), ("syuppatsusi-ta", "depart-PAST"), ("to iu", "say"), ("koto-wa", "fact-TOP"), ("hontoo-da", "true")]
    glossedWords := [⟨[['M', 'a', 'r', 'y'], ['w', 'a']], [['M', 'a', 'r', 'y'], ['T', 'O', 'P']]⟩, ⟨[['a', 's', 'u']], [['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w']]⟩, ⟨[['t', 'o', 'o', 'c', 'h', 'a', 'k', 'u', 's', 'u'], ['r', 'u']], [['a', 'r', 'r', 'i', 'v', 'e'], ['P', 'R', 'E', 'S']]⟩, ⟨[['k', 'o', 't', 'o'], ['n', 'i']], [['f', 'a', 'c', 't'], ['D', 'A', 'T']]⟩, ⟨[['n', 'a', 't'], ['t', 'e']], [['b', 'e', 'c', 'o', 'm', 'e'], ['G', 'E', 'R']]⟩, ⟨[['i'], ['r', 'u']], [['b', 'e'], ['P', 'R', 'E', 'S']]⟩, ⟨[['d', 'a', 'k', 'a', 'r', 'a']], [['S', 'o']]⟩, ⟨[['J', 'o', 'h', 'n'], ['g', 'a']], [['J', 'o', 'h', 'n'], ['N', 'O', 'M']]⟩, ⟨[['M', 'a', 'r', 'y'], ['g', 'a']], [['M', 'a', 'r', 'y'], ['N', 'O', 'M']]⟩, ⟨[['t', 'o', 'o', 'c', 'h', 'a', 'k', 'u', 's', 'u'], ['r', 'u']], [['a', 'r', 'r', 'i', 'v', 'e'], ['P', 'R', 'E', 'S']]⟩, ⟨[['m', 'a', 'e', 'n', 'i']], [['b', 'e', 'f', 'o', 'r', 'e']]⟩, ⟨[['s', 'y', 'u', 'p', 'p', 'a', 't', 's', 'u', 's', 'i'], ['t', 'a']], [['d', 'e', 'p', 'a', 'r', 't'], ['P', 'A', 'S', 'T']]⟩, ⟨[['t', 'o', ' ', 'i', 'u']], [['s', 'a', 'y']]⟩, ⟨[['k', 'o', 't', 'o'], ['w', 'a']], [['f', 'a', 'c', 't'], ['T', 'O', 'P']]⟩, ⟨[['h', 'o', 'n', 't', 'o', 'o'], ['d', 'a']], [['t', 'r', 'u', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "before"), ("embedded", "present"), ("clauseTime", "after speech")] }

def ex_103 : Datum :=
  { id := "sharvit2014_103"
    source := ⟨"sharvit-2014", "(103)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "O Janis efige prin efige i Maria."
    glossedTokens := [("O", "the"), ("Janis", "John"), ("efige", "leave-PAST-PERF"), ("prin", "before"), ("efige", "leave-PAST-PERF"), ("i", "the"), ("Maria", "Mary")]
    glossedWords := [⟨[['O']], [['t', 'h', 'e']]⟩, ⟨[['J', 'a', 'n', 'i', 's']], [['J', 'o', 'h', 'n']]⟩, ⟨[['e', 'f', 'i', 'g', 'e']], [['l', 'e', 'a', 'v', 'e'], ['P', 'A', 'S', 'T'], ['P', 'E', 'R', 'F']]⟩, ⟨[['p', 'r', 'i', 'n']], [['b', 'e', 'f', 'o', 'r', 'e']]⟩, ⟨[['e', 'f', 'i', 'g', 'e']], [['l', 'e', 'a', 'v', 'e'], ['P', 'A', 'S', 'T'], ['P', 'E', 'R', 'F']]⟩, ⟨[['i']], [['t', 'h', 'e']]⟩, ⟨[['M', 'a', 'r', 'i', 'a']], [['M', 'a', 'r', 'y']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := [("O Janis efige prin na efige i Maria.", .ungrammatical), ("O Janis efige prin efevge i Maria.", .ungrammatical), ("O Janis efige prin na efevge i Maria.", .ungrammatical)]
    readings := []
    paperFeatures := [("construction", "before"), ("embedded", "past")] }

def ex_104 : Datum :=
  { id := "sharvit2014_104"
    source := ⟨"sharvit-2014", "(104)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "To 1963 o Kostas mas ipe oti i Maria itan eggios."
    glossedTokens := [("To", "the"), ("1963", "1963"), ("o", "the"), ("Kostas", "Kostas"), ("mas", "us"), ("ipe", "tell-PAST"), ("oti", "that"), ("i", "the"), ("Maria", "Maria"), ("itan", "be-PAST"), ("eggios", "pregnant")]
    glossedWords := [⟨[['T', 'o']], [['t', 'h', 'e']]⟩, ⟨[['1', '9', '6', '3']], [['1', '9', '6', '3']]⟩, ⟨[['o']], [['t', 'h', 'e']]⟩, ⟨[['K', 'o', 's', 't', 'a', 's']], [['K', 'o', 's', 't', 'a', 's']]⟩, ⟨[['m', 'a', 's']], [['u', 's']]⟩, ⟨[['i', 'p', 'e']], [['t', 'e', 'l', 'l'], ['P', 'A', 'S', 'T']]⟩, ⟨[['o', 't', 'i']], [['t', 'h', 'a', 't']]⟩, ⟨[['i']], [['t', 'h', 'e']]⟩, ⟨[['M', 'a', 'r', 'i', 'a']], [['M', 'a', 'r', 'i', 'a']]⟩, ⟨[['i', 't', 'a', 'n']], [['b', 'e'], ['P', 'A', 'S', 'T']]⟩, ⟨[['e', 'g', 'g', 'i', 'o', 's']], [['p', 'r', 'e', 'g', 'n', 'a', 'n', 't']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .acceptable)]
    paperFeatures := [("construction", "attitude"), ("embedded", "past")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8a, ex_8b, ex_9a, ex_9b, ex_46, ex_50b_did, ex_50b_will, ex_51, ex_103, ex_104]

end Sharvit2014.Examples
