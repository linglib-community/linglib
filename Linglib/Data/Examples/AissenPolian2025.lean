module

public import Linglib.Data.Examples.Schema

/-!
# `AissenPolian2025` — typed example data

Auto-generated from `Linglib/Data/Examples/AissenPolian2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AissenPolian2025.Examples`.
-/

@[expose] public section

namespace AissenPolian2025.Examples

def ex1 : Datum :=
  { id := "aissenpolian2025_ex1"
    source := ⟨"aissen-polian-2025", "(1)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Bejk'aj x-nich'an te Xun=e."
    glossedTokens := [("Bejk'aj", "CP.be.born"), ("x-nich'an", "A3-child.of.male"), ("te", "DET"), ("Xun=e", "Juan=ENC")]
    glossedWords := [⟨[['B', 'e', 'j', 'k', '\'', 'a', 'j']], [['C', 'P', '.', 'b', 'e', '.', 'b', 'o', 'r', 'n']]⟩, ⟨[['x'], ['n', 'i', 'c', 'h', '\'', 'a', 'n']], [['A', '3'], ['c', 'h', 'i', 'l', 'd', '.', 'o', 'f', '.', 'm', 'a', 'l', 'e']]⟩, ⟨[['t', 'e']], [['D', 'E', 'T']]⟩, ⟨[['X', 'u', 'n'], ['e']], [['J', 'u', 'a', 'n'], ['E', 'N', 'C']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Declarative with a possessed theme, Oxchuc Tseltal."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("construction", "lexicalUnaccusative")] }

def ex2a : Datum :=
  { id := "aissenpolian2025_ex2a"
    source := ⟨"aissen-polian-2025", "(2a)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "[Mach'a x-nich'an] bejk'aj?"
    glossedTokens := [("Mach'a", "who"), ("x-nich'an", "A3-child.of.male"), ("bejk'aj", "CP.be.born")]
    glossedWords := [⟨[['M', 'a', 'c', 'h', '\'', 'a']], [['w', 'h', 'o']]⟩, ⟨[['x'], ['n', 'i', 'c', 'h', '\'', 'a', 'n']], [['A', '3'], ['c', 'h', 'i', 'l', 'd', '.', 'o', 'f', '.', 'm', 'a', 'l', 'e']]⟩, ⟨[['b', 'e', 'j', 'k', '\'', 'a', 'j']], [['C', 'P', '.', 'b', 'e', '.', 'b', 'o', 'r', 'n']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Pied-piping: the question is about a particular child whose existence is presupposed."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "piedPiping"), ("possessorOf", "S_O"), ("possessum", "specific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "lexicalUnaccusative")] }

def ex2b : Datum :=
  { id := "aissenpolian2025_ex2b"
    source := ⟨"aissen-polian-2025", "(2b)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Mach'a bejk'aj x-nich'an?"
    glossedTokens := [("Mach'a", "who"), ("bejk'aj", "CP.be.born"), ("x-nich'an", "A3-child.of.male")]
    glossedWords := [⟨[['M', 'a', 'c', 'h', '\'', 'a']], [['w', 'h', 'o']]⟩, ⟨[['b', 'e', 'j', 'k', '\'', 'a', 'j']], [['C', 'P', '.', 'b', 'e', '.', 'b', 'o', 'r', 'n']]⟩, ⟨[['x'], ['n', 'i', 'c', 'h', '\'', 'a', 'n']], [['A', '3'], ['c', 'h', 'i', 'l', 'd', '.', 'o', 'f', '.', 'm', 'a', 'l', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Stranding: no child is presupposed to exist."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "S_O"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "lexicalUnaccusative"), ("table4", "T-none-unaccusative")] }

def ex4 : Datum :=
  { id := "aissenpolian2025_ex4"
    source := ⟨"aissen-polian-2025", "(4)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Mach'a x-bajt s-karo?"
    glossedTokens := [("Mach'a", "who"), ("x-bajt", "ICP-go"), ("s-karo", "A3-car")]
    glossedWords := [⟨[['M', 'a', 'c', 'h', '\'', 'a']], [['w', 'h', 'o']]⟩, ⟨[['x'], ['b', 'a', 'j', 't']], [['I', 'C', 'P'], ['g', 'o']]⟩, ⟨[['s'], ['k', 'a', 'r', 'o']], [['A', '3'], ['c', 'a', 'r']]⟩]
    lgrConformance := some .morphemeAligned
    context := "A group of men planning a community work project ask how they will get to the site; no particular car is presupposed, and 'nobody' is a felicitous answer."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "S_O"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "none"), ("table4", "T-none-unaccusative")] }

def ex5 : Datum :=
  { id := "aissenpolian2025_ex5"
    source := ⟨"aissen-polian-2025", "(5)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "[Mach'a x-wakax] la s-mil-ik?"
    glossedTokens := [("Mach'a", "who"), ("x-wakax", "A3-cow"), ("la", "CP"), ("s-mil-ik", "A3-kill-PL")]
    glossedWords := [⟨[['M', 'a', 'c', 'h', '\'', 'a']], [['w', 'h', 'o']]⟩, ⟨[['x'], ['w', 'a', 'k', 'a', 'x']], [['A', '3'], ['c', 'o', 'w']]⟩, ⟨[['l', 'a']], [['C', 'P']]⟩, ⟨[['s'], ['m', 'i', 'l'], ['i', 'k']], [['A', '3'], ['k', 'i', 'l', 'l'], ['P', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := "In a kitchen where meat that was obviously not purchased is being cooked; the cow is contextually salient and a 'nobody' answer is nonsensical."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "piedPiping"), ("possessorOf", "O"), ("possessum", "specific"), ("clause", "transitive"), ("intervener", "none")] }

def ex20a : Datum :=
  { id := "aissenpolian2025_ex20a"
    source := ⟨"little-2020b", "p. 11"⟩
    reportedIn := some ⟨"aissen-polian-2025", "(20a)"⟩
    language := "chol1282"
    primaryText := "[Majki i-wakax] ta' yajl-i?"
    glossedTokens := [("Majki", "who"), ("i-wakax", "A3-cow"), ("ta'", "PFV"), ("yajl-i", "fall-INTR")]
    glossedWords := [⟨[['M', 'a', 'j', 'k', 'i']], [['w', 'h', 'o']]⟩, ⟨[['i'], ['w', 'a', 'k', 'a', 'x']], [['A', '3'], ['c', 'o', 'w']]⟩, ⟨[['t', 'a', '\'']], [['P', 'F', 'V']]⟩, ⟨[['y', 'a', 'j', 'l'], ['i']], [['f', 'a', 'l', 'l'], ['I', 'N', 'T', 'R']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Ch'ol possessive S_O."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "piedPiping"), ("possessorOf", "S_O"), ("possessum", "specific"), ("clause", "unaccusative"), ("intervener", "none")] }

def ex20b : Datum :=
  { id := "aissenpolian2025_ex20b"
    source := ⟨"little-2020b", "p. 11"⟩
    reportedIn := some ⟨"aissen-polian-2025", "(20b)"⟩
    language := "chol1282"
    primaryText := "Majki ta' yajl-i [i-wakax]?"
    glossedTokens := [("Majki", "who"), ("ta'", "PFV"), ("yajl-i", "fall-INTR"), ("i-wakax", "A3-cow")]
    glossedWords := [⟨[['M', 'a', 'j', 'k', 'i']], [['w', 'h', 'o']]⟩, ⟨[['t', 'a', '\'']], [['P', 'F', 'V']]⟩, ⟨[['y', 'a', 'j', 'l'], ['i']], [['f', 'a', 'l', 'l'], ['I', 'N', 'T', 'R']]⟩, ⟨[['i'], ['w', 'a', 'k', 'a', 'x']], [['A', '3'], ['c', 'o', 'w']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Ch'ol possessive S_O, stranded."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "S_O"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "none"), ("table4", "T-none-unaccusative")] }

def ex22a : Datum :=
  { id := "aissenpolian2025_ex22a"
    source := ⟨"little-2020b", "p. 13"⟩
    reportedIn := some ⟨"aissen-polian-2025", "(22a)"⟩
    language := "chol1282"
    primaryText := "[Majki i-chich] ta' a-k'el-e?"
    glossedTokens := [("Majki", "who"), ("i-chich", "A3-sister"), ("ta'", "PFV"), ("a-k'el-e", "A2-see-TR")]
    glossedWords := [⟨[['M', 'a', 'j', 'k', 'i']], [['w', 'h', 'o']]⟩, ⟨[['i'], ['c', 'h', 'i', 'c', 'h']], [['A', '3'], ['s', 'i', 's', 't', 'e', 'r']]⟩, ⟨[['t', 'a', '\'']], [['P', 'F', 'V']]⟩, ⟨[['a'], ['k', '\'', 'e', 'l'], ['e']], [['A', '2'], ['s', 'e', 'e'], ['T', 'R']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Ch'ol possessive O in a monotransitive clause."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "piedPiping"), ("possessorOf", "O"), ("possessum", "specific"), ("clause", "transitive"), ("intervener", "none")] }

def ex22b : Datum :=
  { id := "aissenpolian2025_ex22b"
    source := ⟨"little-2020b", "p. 13"⟩
    reportedIn := some ⟨"aissen-polian-2025", "(22b)"⟩
    language := "chol1282"
    primaryText := "Majki ta' a-k'el-e [i-chich]?"
    glossedTokens := [("Majki", "who"), ("ta'", "PFV"), ("a-k'el-e", "A2-see-TR"), ("i-chich", "A3-sister")]
    glossedWords := [⟨[['M', 'a', 'j', 'k', 'i']], [['w', 'h', 'o']]⟩, ⟨[['t', 'a', '\'']], [['P', 'F', 'V']]⟩, ⟨[['a'], ['k', '\'', 'e', 'l'], ['e']], [['A', '2'], ['s', 'e', 'e'], ['T', 'R']]⟩, ⟨[['i'], ['c', 'h', 'i', 'c', 'h']], [['A', '3'], ['s', 'i', 's', 't', 'e', 'r']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Ch'ol possessive O, stranded."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "O"), ("possessum", "specific"), ("clause", "transitive"), ("intervener", "A"), ("table4", "T-A-transitive")] }

def ex26b : Datum :=
  { id := "aissenpolian2025_ex26b"
    source := ⟨"little-2020b", "fn. 10"⟩
    reportedIn := some ⟨"aissen-polian-2025", "(26b)"⟩
    language := "chol1282"
    primaryText := "Majki ta' a-k'el-be [i-chich]?"
    glossedTokens := [("Majki", "who"), ("ta'", "PFV"), ("a-k'el-be", "A2-see-APPL"), ("i-chich", "A3-sister")]
    glossedWords := [⟨[['M', 'a', 'j', 'k', 'i']], [['w', 'h', 'o']]⟩, ⟨[['t', 'a', '\'']], [['P', 'F', 'V']]⟩, ⟨[['a'], ['k', '\'', 'e', 'l'], ['b', 'e']], [['A', '2'], ['s', 'e', 'e'], ['A', 'P', 'P', 'L']]⟩, ⟨[['i'], ['c', 'h', 'i', 'c', 'h']], [['A', '3'], ['s', 'i', 's', 't', 'e', 'r']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Ch'ol ditransitive applicative with the possessor as applied object."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "O"), ("possessum", "nonSpecific"), ("clause", "ditransitiveRaising"), ("intervener", "none"), ("probe", "Appl"), ("table4", "Appl-none-ditransitive")] }

def ex23a : Datum :=
  { id := "aissenpolian2025_ex23a"
    source := ⟨"aissen-polian-2025", "(23a)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "[Much'u s-tseb] av-il ta ch'ivit?"
    glossedTokens := [("Much'u", "who"), ("s-tseb", "A3-girl"), ("av-il", "A2-see"), ("ta", "P"), ("ch'ivit", "market")]
    glossedWords := [⟨[['M', 'u', 'c', 'h', '\'', 'u']], [['w', 'h', 'o']]⟩, ⟨[['s'], ['t', 's', 'e', 'b']], [['A', '3'], ['g', 'i', 'r', 'l']]⟩, ⟨[['a', 'v'], ['i', 'l']], [['A', '2'], ['s', 'e', 'e']]⟩, ⟨[['t', 'a']], [['P']]⟩, ⟨[['c', 'h', '\'', 'i', 'v', 'i', 't']], [['m', 'a', 'r', 'k', 'e', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Possessive O in a monotransitive clause."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "piedPiping"), ("possessorOf", "O"), ("possessum", "specific"), ("clause", "transitive"), ("intervener", "none")] }

def ex23b : Datum :=
  { id := "aissenpolian2025_ex23b"
    source := ⟨"aissen-polian-2025", "(23b)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Much'u av-il [s-tseb] ta ch'ivit?"
    glossedTokens := [("Much'u", "who"), ("av-il", "A2-see"), ("s-tseb", "A3-girl"), ("ta", "P"), ("ch'ivit", "market")]
    glossedWords := [⟨[['M', 'u', 'c', 'h', '\'', 'u']], [['w', 'h', 'o']]⟩, ⟨[['a', 'v'], ['i', 'l']], [['A', '2'], ['s', 'e', 'e']]⟩, ⟨[['s'], ['t', 's', 'e', 'b']], [['A', '3'], ['g', 'i', 'r', 'l']]⟩, ⟨[['t', 'a']], [['P']]⟩, ⟨[['c', 'h', '\'', 'i', 'v', 'i', 't']], [['m', 'a', 'r', 'k', 'e', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Possessive O, stranded."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "O"), ("possessum", "specific"), ("clause", "transitive"), ("intervener", "A"), ("table4", "T-A-transitive")] }

def ex24 : Datum :=
  { id := "aissenpolian2025_ex24"
    source := ⟨"aissen-polian-2025", "(24)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "I-j-man tal [s-lok'obbail [li Nwéva York xchi'uk li k'elob osil=e]]."
    glossedTokens := [("I-j-man", "CP-A1-buy"), ("tal", "DIR"), ("s-lok'obbail", "A3-representation"), ("li", "DET"), ("Nwéva", "New"), ("York", "York"), ("xchi'uk", "and"), ("li", "DET"), ("k'elob", "lookout"), ("osil=e", "ground=ENC")]
    glossedWords := [⟨[['I'], ['j'], ['m', 'a', 'n']], [['C', 'P'], ['A', '1'], ['b', 'u', 'y']]⟩, ⟨[['t', 'a', 'l']], [['D', 'I', 'R']]⟩, ⟨[['s'], ['l', 'o', 'k', '\'', 'o', 'b', 'b', 'a', 'i', 'l']], [['A', '3'], ['r', 'e', 'p', 'r', 'e', 's', 'e', 'n', 't', 'a', 't', 'i', 'o', 'n']]⟩, ⟨[['l', 'i']], [['D', 'E', 'T']]⟩, ⟨[['N', 'w', 'é', 'v', 'a']], [['N', 'e', 'w']]⟩, ⟨[['Y', 'o', 'r', 'k']], [['Y', 'o', 'r', 'k']]⟩, ⟨[['x', 'c', 'h', 'i', '\'', 'u', 'k']], [['a', 'n', 'd']]⟩, ⟨[['l', 'i']], [['D', 'E', 'T']]⟩, ⟨[['k', '\'', 'e', 'l', 'o', 'b']], [['l', 'o', 'o', 'k', 'o', 'u', 't']]⟩, ⟨[['o', 's', 'i', 'l'], ['e']], [['g', 'r', 'o', 'u', 'n', 'd'], ['E', 'N', 'C']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Text description of a visit to the Empire State Building; nothing in the context implies the existence of pictures."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("construction", "lexicalTransitive"), ("possessum", "nonSpecific")] }

def ex25 : Datum :=
  { id := "aissenpolian2025_ex25"
    source := ⟨"aissen-polian-2025", "(25)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "K'usi a-man tal [s-lok'obbail]?"
    glossedTokens := [("K'usi", "what"), ("a-man", "A2-buy"), ("tal", "DIR"), ("s-lok'obbail", "A3-representation")]
    glossedWords := [⟨[['K', '\'', 'u', 's', 'i']], [['w', 'h', 'a', 't']]⟩, ⟨[['a'], ['m', 'a', 'n']], [['A', '2'], ['b', 'u', 'y']]⟩, ⟨[['t', 'a', 'l']], [['D', 'I', 'R']]⟩, ⟨[['s'], ['l', 'o', 'k', '\'', 'o', 'b', 'b', 'a', 'i', 'l']], [['A', '3'], ['r', 'e', 'p', 'r', 'e', 's', 'e', 'n', 't', 'a', 't', 'i', 'o', 'n']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Stranding from a non-specific possessive O."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "O"), ("possessum", "nonSpecific"), ("clause", "transitive"), ("intervener", "A"), ("table4", "T-A-transitive")] }

def ex27 : Datum :=
  { id := "aissenpolian2025_ex27"
    source := ⟨"aissen-polian-2025", "(27)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "K'usi a-man-be tal [s-lok'obbail]?"
    glossedTokens := [("K'usi", "what"), ("a-man-be", "A2-buy-APPL"), ("tal", "DIR"), ("s-lok'obbail", "A3-representation")]
    glossedWords := [⟨[['K', '\'', 'u', 's', 'i']], [['w', 'h', 'a', 't']]⟩, ⟨[['a'], ['m', 'a', 'n'], ['b', 'e']], [['A', '2'], ['b', 'u', 'y'], ['A', 'P', 'P', 'L']]⟩, ⟨[['t', 'a', 'l']], [['D', 'I', 'R']]⟩, ⟨[['s'], ['l', 'o', 'k', '\'', 'o', 'b', 'b', 'a', 'i', 'l']], [['A', '3'], ['r', 'e', 'p', 'r', 'e', 's', 'e', 'n', 't', 'a', 't', 'i', 'o', 'n']]⟩]
    lgrConformance := some .morphemeAligned
    context := "The applicative suffix makes (25) grammatical."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "O"), ("possessum", "nonSpecific"), ("clause", "ditransitiveRaising"), ("intervener", "none"), ("probe", "Appl"), ("table4", "Appl-none-ditransitive")] }

def ex28b : Datum :=
  { id := "aissenpolian2025_ex28b"
    source := ⟨"aissen-polian-2025", "(28b)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Mach'a la a-man-bey tal [s-lok'ombail]?"
    glossedTokens := [("Mach'a", "who"), ("la", "CP"), ("a-man-bey", "A2-buy-APPL"), ("tal", "DIR"), ("s-lok'ombail", "A3-representation")]
    glossedWords := [⟨[['M', 'a', 'c', 'h', '\'', 'a']], [['w', 'h', 'o']]⟩, ⟨[['l', 'a']], [['C', 'P']]⟩, ⟨[['a'], ['m', 'a', 'n'], ['b', 'e', 'y']], [['A', '2'], ['b', 'u', 'y'], ['A', 'P', 'P', 'L']]⟩, ⟨[['t', 'a', 'l']], [['D', 'I', 'R']]⟩, ⟨[['s'], ['l', 'o', 'k', '\'', 'o', 'm', 'b', 'a', 'i', 'l']], [['A', '3'], ['r', 'e', 'p', 'r', 'e', 's', 'e', 'n', 't', 'a', 't', 'i', 'o', 'n']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Tenango Tseltal applicative."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "O"), ("possessum", "nonSpecific"), ("clause", "ditransitiveRaising"), ("intervener", "none"), ("probe", "Appl"), ("table4", "Appl-none-ditransitive")] }

def ex28c : Datum :=
  { id := "aissenpolian2025_ex28c"
    source := ⟨"aissen-polian-2025", "(28c)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Mach'a la a-man tal [s-lok'ombail]?"
    glossedTokens := [("Mach'a", "who"), ("la", "CP"), ("a-man", "A2-buy"), ("tal", "DIR"), ("s-lok'ombail", "A3-representation")]
    glossedWords := [⟨[['M', 'a', 'c', 'h', '\'', 'a']], [['w', 'h', 'o']]⟩, ⟨[['l', 'a']], [['C', 'P']]⟩, ⟨[['a'], ['m', 'a', 'n']], [['A', '2'], ['b', 'u', 'y']]⟩, ⟨[['t', 'a', 'l']], [['D', 'I', 'R']]⟩, ⟨[['s'], ['l', 'o', 'k', '\'', 'o', 'm', 'b', 'a', 'i', 'l']], [['A', '3'], ['r', 'e', 'p', 'r', 'e', 's', 'e', 'n', 't', 'a', 't', 'i', 'o', 'n']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Tenango Tseltal monotransitive."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "O"), ("possessum", "nonSpecific"), ("clause", "transitive"), ("intervener", "A"), ("table4", "T-A-transitive")] }

def ex30 : Datum :=
  { id := "aissenpolian2025_ex30"
    source := ⟨"aissen-polian-2025", "(30)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Much'u ch-av-al-b-on [s-lo'iltael]?"
    glossedTokens := [("Much'u", "who"), ("ch-av-al-b-on", "ICP-A2-say-APPL-B1SG"), ("s-lo'iltael", "A3-talk")]
    glossedWords := [⟨[['M', 'u', 'c', 'h', '\'', 'u']], [['w', 'h', 'o']]⟩, ⟨[['c', 'h'], ['a', 'v'], ['a', 'l'], ['b'], ['o', 'n']], [['I', 'C', 'P'], ['A', '2'], ['s', 'a', 'y'], ['A', 'P', 'P', 'L'], ['B', '1', 'S', 'G']]⟩, ⟨[['s'], ['l', 'o', '\'', 'i', 'l', 't', 'a', 'e', 'l']], [['A', '3'], ['t', 'a', 'l', 'k']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Ditransitive with a first-person thematic applied object filling Spec,ApplP."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "O"), ("possessum", "nonSpecific"), ("clause", "ditransitiveThematic"), ("intervener", "goal"), ("probe", "Appl"), ("table4", "Appl-goal-ditransitive")] }

def ex31 : Datum :=
  { id := "aissenpolian2025_ex31"
    source := ⟨"aissen-polian-2025", "(31)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Bin ya aw-ak'-b-on [s-tojol]?"
    glossedTokens := [("Bin", "what"), ("ya", "ICP"), ("aw-ak'-b-on", "A2-give-APPL-B1SG"), ("s-tojol", "A3-payment")]
    glossedWords := [⟨[['B', 'i', 'n']], [['w', 'h', 'a', 't']]⟩, ⟨[['y', 'a']], [['I', 'C', 'P']]⟩, ⟨[['a', 'w'], ['a', 'k', '\''], ['b'], ['o', 'n']], [['A', '2'], ['g', 'i', 'v', 'e'], ['A', 'P', 'P', 'L'], ['B', '1', 'S', 'G']]⟩, ⟨[['s'], ['t', 'o', 'j', 'o', 'l']], [['A', '3'], ['p', 'a', 'y', 'm', 'e', 'n', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Tenango Tseltal ditransitive with a thematic applied object."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "O"), ("possessum", "nonSpecific"), ("clause", "ditransitiveThematic"), ("intervener", "goal"), ("probe", "Appl"), ("table4", "Appl-goal-ditransitive")] }

def ex32 : Datum :=
  { id := "aissenpolian2025_ex32"
    source := ⟨"aissen-polian-2025", "(32)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "I te l-i-k'elan-b-otikotik [s-lok'obbail li jch'ulme'tik=e]."
    glossedTokens := [("I", "and"), ("te", "then"), ("l-i-k'elan-b-otikotik", "CP-B1-present-APPL.PASS-B1EXCL"), ("s-lok'obbail", "A3-representation"), ("li", "DET"), ("jch'ulme'tik=e", "our.holy.mother=ENC")]
    glossedWords := [⟨[['I']], [['a', 'n', 'd']]⟩, ⟨[['t', 'e']], [['t', 'h', 'e', 'n']]⟩, ⟨[['l'], ['i'], ['k', '\'', 'e', 'l', 'a', 'n'], ['b'], ['o', 't', 'i', 'k', 'o', 't', 'i', 'k']], [['C', 'P'], ['B', '1'], ['p', 'r', 'e', 's', 'e', 'n', 't'], ['A', 'P', 'P', 'L', '.', 'P', 'A', 'S', 'S'], ['B', '1', 'E', 'X', 'C', 'L']]⟩, ⟨[['s'], ['l', 'o', 'k', '\'', 'o', 'b', 'b', 'a', 'i', 'l']], [['A', '3'], ['r', 'e', 'p', 'r', 'e', 's', 'e', 'n', 't', 'a', 't', 'i', 'o', 'n']]⟩, ⟨[['l', 'i']], [['D', 'E', 'T']]⟩, ⟨[['j', 'c', 'h', '\'', 'u', 'l', 'm', 'e', '\'', 't', 'i', 'k'], ['e']], [['o', 'u', 'r', '.', 'h', 'o', 'l', 'y', '.', 'm', 'o', 't', 'h', 'e', 'r'], ['E', 'N', 'C']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Text: initial mention of the picture; Spec,ApplP is filled by the first-person goal."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "ditransitiveThematic"), ("construction", "lexicalTransitive"), ("possessum", "nonSpecific")] }

def ex35 : Datum :=
  { id := "aissenpolian2025_ex35"
    source := ⟨"aissen-polian-2025", "(35)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Oy j-librotak."
    glossedTokens := [("Oy", "EXIS"), ("j-librotak", "A1-books")]
    glossedWords := [⟨[['O', 'y']], [['E', 'X', 'I', 'S']]⟩, ⟨[['j'], ['l', 'i', 'b', 'r', 'o', 't', 'a', 'k']], [['A', '1'], ['b', 'o', 'o', 'k', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Predicative possession on the existential construction."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("construction", "predicativePossession")] }

def ex36 : Datum :=
  { id := "aissenpolian2025_ex36"
    source := ⟨"aissen-polian-2025", "(36)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Kap-em j-jol."
    glossedTokens := [("Kap-em", "mixed.up.INTR-PRF"), ("j-jol", "A1-head")]
    glossedWords := [⟨[['K', 'a', 'p'], ['e', 'm']], [['m', 'i', 'x', 'e', 'd', '.', 'u', 'p', '.', 'I', 'N', 'T', 'R'], ['P', 'R', 'F']]⟩, ⟨[['j'], ['j', 'o', 'l']], [['A', '1'], ['h', 'e', 'a', 'd']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Experiential collocation."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("construction", "experientialCollocation")] }

def ex37 : Datum :=
  { id := "aissenpolian2025_ex37"
    source := ⟨"aissen-polian-2025", "(37)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Ch'ay j-tak'in."
    glossedTokens := [("Ch'ay", "lost.INTR"), ("j-tak'in", "A1-money")]
    glossedWords := [⟨[['C', 'h', '\'', 'a', 'y']], [['l', 'o', 's', 't', '.', 'I', 'N', 'T', 'R']]⟩, ⟨[['j'], ['t', 'a', 'k', '\'', 'i', 'n']], [['A', '1'], ['m', 'o', 'n', 'e', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Lexical unaccusative with a non-specific possessive S_O."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("construction", "lexicalUnaccusative"), ("possessum", "nonSpecific")] }

def ex43 : Datum :=
  { id := "aissenpolian2025_ex43"
    source := ⟨"aissen-polian-2025", "(43)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "May-uk j-kerem."
    glossedTokens := [("May-uk", "NEG+EXIS-IRR"), ("j-kerem", "A1-boy")]
    glossedWords := [⟨[['M', 'a', 'y'], ['u', 'k']], [['N', 'E', 'G', '+', 'E', 'X', 'I', 'S'], ['I', 'R', 'R']]⟩, ⟨[['j'], ['k', 'e', 'r', 'e', 'm']], [['A', '1'], ['b', 'o', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Predicative possession under negation: the possessum takes narrow scope."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("construction", "predicativePossession"), ("possessum", "nonSpecific")] }

def ex45a : Datum :=
  { id := "aissenpolian2025_ex45a"
    source := ⟨"aissen-polian-2025", "(45a)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Oy [s-na] ta Jobel li Xun=e."
    glossedTokens := [("Oy", "EXIS"), ("s-na", "A3-house"), ("ta", "in"), ("Jobel", "SC"), ("li", "DET"), ("Xun=e", "Juan=ENC")]
    glossedWords := [⟨[['O', 'y']], [['E', 'X', 'I', 'S']]⟩, ⟨[['s'], ['n', 'a']], [['A', '3'], ['h', 'o', 'u', 's', 'e']]⟩, ⟨[['t', 'a']], [['i', 'n']]⟩, ⟨[['J', 'o', 'b', 'e', 'l']], [['S', 'C']]⟩, ⟨[['l', 'i']], [['D', 'E', 'T']]⟩, ⟨[['X', 'u', 'n'], ['e']], [['J', 'u', 'a', 'n'], ['E', 'N', 'C']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Preferred order: the locative separates possessum and possessor."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("construction", "predicativePossession")] }

def ex45b : Datum :=
  { id := "aissenpolian2025_ex45b"
    source := ⟨"aissen-polian-2025", "(45b)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Oy [s-na] li Xun ta Jobel=e."
    glossedTokens := [("Oy", "EXIS"), ("s-na", "A3-house"), ("li", "DET"), ("Xun", "Juan"), ("ta", "in"), ("Jobel=e", "SC=ENC")]
    glossedWords := [⟨[['O', 'y']], [['E', 'X', 'I', 'S']]⟩, ⟨[['s'], ['n', 'a']], [['A', '3'], ['h', 'o', 'u', 's', 'e']]⟩, ⟨[['l', 'i']], [['D', 'E', 'T']]⟩, ⟨[['X', 'u', 'n']], [['J', 'u', 'a', 'n']]⟩, ⟨[['t', 'a']], [['i', 'n']]⟩, ⟨[['J', 'o', 'b', 'e', 'l'], ['e']], [['S', 'C'], ['E', 'N', 'C']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Locative after the possessor."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("construction", "predicativePossession")] }

def ex46 : Datum :=
  { id := "aissenpolian2025_ex46"
    source := ⟨"aissen-polian-2025", "(46)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Te oy ta Jobel [s-na li Xun=e]."
    glossedTokens := [("Te", "there"), ("oy", "EXIS"), ("ta", "in"), ("Jobel", "SC"), ("s-na", "A3-house"), ("li", "DET"), ("Xun=e", "Juan=ENC")]
    glossedWords := [⟨[['T', 'e']], [['t', 'h', 'e', 'r', 'e']]⟩, ⟨[['o', 'y']], [['E', 'X', 'I', 'S']]⟩, ⟨[['t', 'a']], [['i', 'n']]⟩, ⟨[['J', 'o', 'b', 'e', 'l']], [['S', 'C']]⟩, ⟨[['s'], ['n', 'a']], [['A', '3'], ['h', 'o', 'u', 's', 'e']]⟩, ⟨[['l', 'i']], [['D', 'E', 'T']]⟩, ⟨[['X', 'u', 'n'], ['e']], [['J', 'u', 'a', 'n'], ['E', 'N', 'C']]⟩]
    lgrConformance := some .morphemeAligned
    context := "The whole possessive follows the PP and is definite."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("construction", "locativeCopula"), ("possessum", "specific")] }

def ex47 : Datum :=
  { id := "aissenpolian2025_ex47"
    source := ⟨"aissen-polian-2025", "(47)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "[Oy s-vix] [oy y-ixlel] ti vinik un=e."
    glossedTokens := [("Oy", "EXIS"), ("s-vix", "A3-older.sis"), ("oy", "EXIS"), ("y-ixlel", "A3-younger.sis"), ("ti", "DET"), ("vinik", "man"), ("un=e", "PAR=ENC")]
    glossedWords := [⟨[['O', 'y']], [['E', 'X', 'I', 'S']]⟩, ⟨[['s'], ['v', 'i', 'x']], [['A', '3'], ['o', 'l', 'd', 'e', 'r', '.', 's', 'i', 's']]⟩, ⟨[['o', 'y']], [['E', 'X', 'I', 'S']]⟩, ⟨[['y'], ['i', 'x', 'l', 'e', 'l']], [['A', '3'], ['y', 'o', 'u', 'n', 'g', 'e', 'r', '.', 's', 'i', 's']]⟩, ⟨[['t', 'i']], [['D', 'E', 'T']]⟩, ⟨[['v', 'i', 'n', 'i', 'k']], [['m', 'a', 'n']]⟩, ⟨[['u', 'n'], ['e']], [['P', 'A', 'R'], ['E', 'N', 'C']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Coordinated existentials with one sentence-final possessor and no prosodic break."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("construction", "predicativePossession")] }

def ex48a : Datum :=
  { id := "aissenpolian2025_ex48a"
    source := ⟨"aissen-polian-2025", "(48a)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Much'u oy [x-chitom]?"
    glossedTokens := [("Much'u", "who"), ("oy", "EXIS"), ("x-chitom", "A3-pig")]
    glossedWords := [⟨[['M', 'u', 'c', 'h', '\'', 'u']], [['w', 'h', 'o']]⟩, ⟨[['o', 'y']], [['E', 'X', 'I', 'S']]⟩, ⟨[['x'], ['c', 'h', 'i', 't', 'o', 'm']], [['A', '3'], ['p', 'i', 'g']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Predicative possession."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "S_O"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "predicativePossession"), ("table4", "T-none-unaccusative")] }

def ex48b : Datum :=
  { id := "aissenpolian2025_ex48b"
    source := ⟨"aissen-polian-2025", "(48b)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "[Much'u x-chitom] oy?"
    glossedTokens := [("Much'u", "who"), ("x-chitom", "A3-pig"), ("oy", "EXIS")]
    glossedWords := [⟨[['M', 'u', 'c', 'h', '\'', 'u']], [['w', 'h', 'o']]⟩, ⟨[['x'], ['c', 'h', 'i', 't', 'o', 'm']], [['A', '3'], ['p', 'i', 'g']]⟩, ⟨[['o', 'y']], [['E', 'X', 'I', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Predicative possession, pied-piped."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "piedPiping"), ("possessorOf", "S_O"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "predicativePossession")] }

def ex49a : Datum :=
  { id := "aissenpolian2025_ex49a"
    source := ⟨"aissen-polian-2025", "(49a)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Mach'a ay [s-tak'in]?"
    glossedTokens := [("Mach'a", "who"), ("ay", "EXIS"), ("s-tak'in", "A3-money")]
    glossedWords := [⟨[['M', 'a', 'c', 'h', '\'', 'a']], [['w', 'h', 'o']]⟩, ⟨[['a', 'y']], [['E', 'X', 'I', 'S']]⟩, ⟨[['s'], ['t', 'a', 'k', '\'', 'i', 'n']], [['A', '3'], ['m', 'o', 'n', 'e', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Tenejapa Tseltal predicative possession."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "S_O"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "predicativePossession"), ("table4", "T-none-unaccusative")] }

def ex49b : Datum :=
  { id := "aissenpolian2025_ex49b"
    source := ⟨"aissen-polian-2025", "(49b)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "[Mach'a s-tak'in] ay?"
    glossedTokens := [("Mach'a", "who"), ("s-tak'in", "A3-money"), ("ay", "EXIS")]
    glossedWords := [⟨[['M', 'a', 'c', 'h', '\'', 'a']], [['w', 'h', 'o']]⟩, ⟨[['s'], ['t', 'a', 'k', '\'', 'i', 'n']], [['A', '3'], ['m', 'o', 'n', 'e', 'y']]⟩, ⟨[['a', 'y']], [['E', 'X', 'I', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Tenejapa Tseltal, pied-piped."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "piedPiping"), ("possessorOf", "S_O"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "predicativePossession")] }

def ex50a : Datum :=
  { id := "aissenpolian2025_ex50a"
    source := ⟨"aissen-polian-2025", "(50a)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Kap-em s-jol li ants=e."
    glossedTokens := [("Kap-em", "mixed.up-PRF"), ("s-jol", "A3-head"), ("li", "DET"), ("ants=e", "woman=ENC")]
    glossedWords := [⟨[['K', 'a', 'p'], ['e', 'm']], [['m', 'i', 'x', 'e', 'd', '.', 'u', 'p'], ['P', 'R', 'F']]⟩, ⟨[['s'], ['j', 'o', 'l']], [['A', '3'], ['h', 'e', 'a', 'd']]⟩, ⟨[['l', 'i']], [['D', 'E', 'T']]⟩, ⟨[['a', 'n', 't', 's'], ['e']], [['w', 'o', 'm', 'a', 'n'], ['E', 'N', 'C']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Experiential collocation kap -jol."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("construction", "experientialCollocation")] }

def ex51 : Datum :=
  { id := "aissenpolian2025_ex51"
    source := ⟨"aissen-polian-2025", "(51)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Kap-em-on j-jol."
    glossedTokens := [("Kap-em-on", "mixed.up-PRF-B1SG"), ("j-jol", "A1-head")]
    glossedWords := [⟨[['K', 'a', 'p'], ['e', 'm'], ['o', 'n']], [['m', 'i', 'x', 'e', 'd', '.', 'u', 'p'], ['P', 'R', 'F'], ['B', '1', 'S', 'G']]⟩, ⟨[['j'], ['j', 'o', 'l']], [['A', '1'], ['h', 'e', 'a', 'd']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Experiencer indexed on the verb."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("construction", "experientialCollocation")] }

def ex55a : Datum :=
  { id := "aissenpolian2025_ex55a"
    source := ⟨"aissen-polian-2025", "(55a)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Much'u kap-em [s-jol]?"
    glossedTokens := [("Much'u", "who"), ("kap-em", "mix.up-PRF"), ("s-jol", "A3-head")]
    glossedWords := [⟨[['M', 'u', 'c', 'h', '\'', 'u']], [['w', 'h', 'o']]⟩, ⟨[['k', 'a', 'p'], ['e', 'm']], [['m', 'i', 'x', '.', 'u', 'p'], ['P', 'R', 'F']]⟩, ⟨[['s'], ['j', 'o', 'l']], [['A', '3'], ['h', 'e', 'a', 'd']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Experiential collocation."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "S_O"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "experientialCollocation"), ("table4", "T-none-unaccusative")] }

def ex55b : Datum :=
  { id := "aissenpolian2025_ex55b"
    source := ⟨"aissen-polian-2025", "(55b)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "[Much'u s-jol] kap-em?"
    glossedTokens := [("Much'u", "who"), ("s-jol", "A3-head"), ("kap-em", "mix.up-PRF")]
    glossedWords := [⟨[['M', 'u', 'c', 'h', '\'', 'u']], [['w', 'h', 'o']]⟩, ⟨[['s'], ['j', 'o', 'l']], [['A', '3'], ['h', 'e', 'a', 'd']]⟩, ⟨[['k', 'a', 'p'], ['e', 'm']], [['m', 'i', 'x', '.', 'u', 'p'], ['P', 'R', 'F']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Experiential collocation, pied-piped."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "piedPiping"), ("possessorOf", "S_O"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "experientialCollocation")] }

def ex57b : Datum :=
  { id := "aissenpolian2025_ex57b"
    source := ⟨"aissen-polian-2025", "(57b)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Much'u i-yul [x-ch'ulel] ta ak'ubaltik?"
    glossedTokens := [("Much'u", "who"), ("i-yul", "CP-arrive"), ("x-ch'ulel", "A3-soul"), ("ta", "P"), ("ak'ubaltik", "night")]
    glossedWords := [⟨[['M', 'u', 'c', 'h', '\'', 'u']], [['w', 'h', 'o']]⟩, ⟨[['i'], ['y', 'u', 'l']], [['C', 'P'], ['a', 'r', 'r', 'i', 'v', 'e']]⟩, ⟨[['x'], ['c', 'h', '\'', 'u', 'l', 'e', 'l']], [['A', '3'], ['s', 'o', 'u', 'l']]⟩, ⟨[['t', 'a']], [['P']]⟩, ⟨[['a', 'k', '\'', 'u', 'b', 'a', 'l', 't', 'i', 'k']], [['n', 'i', 'g', 'h', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := "yul -ch'ulel is ambiguous between the idiom 'x awakes' and the literal 'x's soul arrives'."
    judgment := .acceptable
    alternatives := []
    readings := [("x woke up", .acceptable), ("x's soul arrived", .unacceptable)]
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "S_O"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "experientialCollocation"), ("table4", "T-none-unaccusative")] }

def ex58b : Datum :=
  { id := "aissenpolian2025_ex58b"
    source := ⟨"aissen-polian-2025", "(58b)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "[Much'u x-ch'ulel] i-yul ta ak'ubaltik?"
    glossedTokens := [("Much'u", "who"), ("x-ch'ulel", "A3-soul"), ("i-yul", "CP-arrive"), ("ta", "P"), ("ak'ubaltik", "night")]
    glossedWords := [⟨[['M', 'u', 'c', 'h', '\'', 'u']], [['w', 'h', 'o']]⟩, ⟨[['x'], ['c', 'h', '\'', 'u', 'l', 'e', 'l']], [['A', '3'], ['s', 'o', 'u', 'l']]⟩, ⟨[['i'], ['y', 'u', 'l']], [['C', 'P'], ['a', 'r', 'r', 'i', 'v', 'e']]⟩, ⟨[['t', 'a']], [['P']]⟩, ⟨[['a', 'k', '\'', 'u', 'b', 'a', 'l', 't', 'i', 'k']], [['n', 'i', 'g', 'h', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := "The same string with pied-piping."
    judgment := .acceptable
    alternatives := []
    readings := [("whose soul arrived", .acceptable), ("who woke up", .unacceptable)]
    paperFeatures := [("strategy", "piedPiping"), ("possessorOf", "S_O"), ("possessum", "specific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "lexicalUnaccusative")] }

def ex59 : Datum :=
  { id := "aissenpolian2025_ex59"
    source := ⟨"aissen-polian-2025", "(59)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Ch'ay s-tak'in te x-Mal=e."
    glossedTokens := [("Ch'ay", "lost.INTR"), ("s-tak'in", "A3-money"), ("te", "DET"), ("x-Mal=e", "CLF-Maria=ENC")]
    glossedWords := [⟨[['C', 'h', '\'', 'a', 'y']], [['l', 'o', 's', 't', '.', 'I', 'N', 'T', 'R']]⟩, ⟨[['s'], ['t', 'a', 'k', '\'', 'i', 'n']], [['A', '3'], ['m', 'o', 'n', 'e', 'y']]⟩, ⟨[['t', 'e']], [['D', 'E', 'T']]⟩, ⟨[['x'], ['M', 'a', 'l'], ['e']], [['C', 'L', 'F'], ['M', 'a', 'r', 'i', 'a'], ['E', 'N', 'C']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Ambiguous between a definite and a non-specific possessum; intransitive under both."
    judgment := .acceptable
    alternatives := []
    readings := [("Maria's money was lost", .acceptable), ("Maria lost some money", .acceptable)]
    paperFeatures := [("clause", "unaccusative"), ("construction", "lexicalUnaccusative")] }

def ex60 : Datum :=
  { id := "aissenpolian2025_ex60"
    source := ⟨"aissen-polian-2025", "(60)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Ch'ay ajk'ube s-tak'in te x-Mal=e."
    glossedTokens := [("Ch'ay", "lost.INTR"), ("ajk'ube", "yesterday"), ("s-tak'in", "A3-money"), ("te", "DET"), ("x-Mal=e", "CLF-Maria=ENC")]
    glossedWords := [⟨[['C', 'h', '\'', 'a', 'y']], [['l', 'o', 's', 't', '.', 'I', 'N', 'T', 'R']]⟩, ⟨[['a', 'j', 'k', '\'', 'u', 'b', 'e']], [['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y']]⟩, ⟨[['s'], ['t', 'a', 'k', '\'', 'i', 'n']], [['A', '3'], ['m', 'o', 'n', 'e', 'y']]⟩, ⟨[['t', 'e']], [['D', 'E', 'T']]⟩, ⟨[['x'], ['M', 'a', 'l'], ['e']], [['C', 'L', 'F'], ['M', 'a', 'r', 'i', 'a'], ['E', 'N', 'C']]⟩]
    lgrConformance := some .morphemeAligned
    context := "The whole possessive follows the adverb."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("construction", "lexicalUnaccusative"), ("possessum", "specific")] }

def ex61 : Datum :=
  { id := "aissenpolian2025_ex61"
    source := ⟨"aissen-polian-2025", "(61)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Ch'ay s-tak'in ajk'ube te x-Mal=e."
    glossedTokens := [("Ch'ay", "lost.INTR"), ("s-tak'in", "A3-money"), ("ajk'ube", "yesterday"), ("te", "DET"), ("x-Mal=e", "CLF-Maria=ENC")]
    glossedWords := [⟨[['C', 'h', '\'', 'a', 'y']], [['l', 'o', 's', 't', '.', 'I', 'N', 'T', 'R']]⟩, ⟨[['s'], ['t', 'a', 'k', '\'', 'i', 'n']], [['A', '3'], ['m', 'o', 'n', 'e', 'y']]⟩, ⟨[['a', 'j', 'k', '\'', 'u', 'b', 'e']], [['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y']]⟩, ⟨[['t', 'e']], [['D', 'E', 'T']]⟩, ⟨[['x'], ['M', 'a', 'l'], ['e']], [['C', 'L', 'F'], ['M', 'a', 'r', 'i', 'a'], ['E', 'N', 'C']]⟩]
    lgrConformance := some .morphemeAligned
    context := "The adverb separates possessum and possessor."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("construction", "lexicalUnaccusative"), ("possessum", "nonSpecific")] }

def ex62a : Datum :=
  { id := "aissenpolian2025_ex62a"
    source := ⟨"aissen-polian-2025", "(62a)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "[Mach'a s-tak'in] ch'ay?"
    glossedTokens := [("Mach'a", "who"), ("s-tak'in", "A3-money"), ("ch'ay", "lost.INTR")]
    glossedWords := [⟨[['M', 'a', 'c', 'h', '\'', 'a']], [['w', 'h', 'o']]⟩, ⟨[['s'], ['t', 'a', 'k', '\'', 'i', 'n']], [['A', '3'], ['m', 'o', 'n', 'e', 'y']]⟩, ⟨[['c', 'h', '\'', 'a', 'y']], [['l', 'o', 's', 't', '.', 'I', 'N', 'T', 'R']]⟩]
    lgrConformance := some .morphemeAligned
    context := "About some specific money known to have been lost."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "piedPiping"), ("possessorOf", "S_O"), ("possessum", "specific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "lexicalUnaccusative")] }

def ex62b : Datum :=
  { id := "aissenpolian2025_ex62b"
    source := ⟨"aissen-polian-2025", "(62b)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Mach'a ch'ay [s-tak'in]?"
    glossedTokens := [("Mach'a", "who"), ("ch'ay", "lost.INTR"), ("s-tak'in", "A3-money")]
    glossedWords := [⟨[['M', 'a', 'c', 'h', '\'', 'a']], [['w', 'h', 'o']]⟩, ⟨[['c', 'h', '\'', 'a', 'y']], [['l', 'o', 's', 't', '.', 'I', 'N', 'T', 'R']]⟩, ⟨[['s'], ['t', 'a', 'k', '\'', 'i', 'n']], [['A', '3'], ['m', 'o', 'n', 'e', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Who lost some non-specific money."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "S_O"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "lexicalUnaccusative"), ("table4", "T-none-unaccusative")] }

def ex65 : Datum :=
  { id := "aissenpolian2025_ex65"
    source := ⟨"aissen-polian-2025", "(65)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "[Much'u ta s-na] ch-av-ikta komel a-bolsa?"
    glossedTokens := [("Much'u", "who"), ("ta", "P"), ("s-na", "A3-house"), ("ch-av-ikta", "ICP-A2-leave"), ("komel", "DIR"), ("a-bolsa", "A2-bag")]
    glossedWords := [⟨[['M', 'u', 'c', 'h', '\'', 'u']], [['w', 'h', 'o']]⟩, ⟨[['t', 'a']], [['P']]⟩, ⟨[['s'], ['n', 'a']], [['A', '3'], ['h', 'o', 'u', 's', 'e']]⟩, ⟨[['c', 'h'], ['a', 'v'], ['i', 'k', 't', 'a']], [['I', 'C', 'P'], ['A', '2'], ['l', 'e', 'a', 'v', 'e']]⟩, ⟨[['k', 'o', 'm', 'e', 'l']], [['D', 'I', 'R']]⟩, ⟨[['a'], ['b', 'o', 'l', 's', 'a']], [['A', '2'], ['b', 'a', 'g']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Psr-OP pied-piped with the PP."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "piedPiping"), ("possessorOf", "OP"), ("possessum", "specific"), ("clause", "transitive"), ("intervener", "none")] }

def ex66 : Datum :=
  { id := "aissenpolian2025_ex66"
    source := ⟨"aissen-polian-2025", "(66)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "[Mach'a (ta) s-nah] ya x-'a'tej-at?"
    glossedTokens := [("Mach'a", "who"), ("ta", "P"), ("s-nah", "A3-house"), ("ya", "ICP"), ("x-'a'tej-at", "ICP-work-B2")]
    glossedWords := [⟨[['M', 'a', 'c', 'h', '\'', 'a']], [['w', 'h', 'o']]⟩, ⟨[['t', 'a']], [['P']]⟩, ⟨[['s'], ['n', 'a', 'h']], [['A', '3'], ['h', 'o', 'u', 's', 'e']]⟩, ⟨[['y', 'a']], [['I', 'C', 'P']]⟩, ⟨[['x'], ['\'', 'a', '\'', 't', 'e', 'j'], ['a', 't']], [['I', 'C', 'P'], ['w', 'o', 'r', 'k'], ['B', '2']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Petalcingo Tseltal unergative with a locative PP."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "piedPiping"), ("possessorOf", "OP"), ("possessum", "specific"), ("clause", "unergative"), ("intervener", "none")] }

def ex67 : Datum :=
  { id := "aissenpolian2025_ex67"
    source := ⟨"aissen-polian-2025", "(67)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Much'u ch-av-ikta komel a-bolsa [ta s-na]?"
    glossedTokens := [("Much'u", "who"), ("ch-av-ikta", "ICP-A2-leave"), ("komel", "DIR"), ("a-bolsa", "A2-bag"), ("ta", "P"), ("s-na", "A3-house")]
    glossedWords := [⟨[['M', 'u', 'c', 'h', '\'', 'u']], [['w', 'h', 'o']]⟩, ⟨[['c', 'h'], ['a', 'v'], ['i', 'k', 't', 'a']], [['I', 'C', 'P'], ['A', '2'], ['l', 'e', 'a', 'v', 'e']]⟩, ⟨[['k', 'o', 'm', 'e', 'l']], [['D', 'I', 'R']]⟩, ⟨[['a'], ['b', 'o', 'l', 's', 'a']], [['A', '2'], ['b', 'a', 'g']]⟩, ⟨[['t', 'a']], [['P']]⟩, ⟨[['s'], ['n', 'a']], [['A', '3'], ['h', 'o', 'u', 's', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Transitive clause with a specific external argument."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "OP"), ("possessum", "nonSpecific"), ("clause", "transitive"), ("intervener", "A"), ("table4", "T-A-transitive-OP")] }

def ex68 : Datum :=
  { id := "aissenpolian2025_ex68"
    source := ⟨"aissen-polian-2025", "(68)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Mach'a ya x-'a'tej-at [ta s-nah]?"
    glossedTokens := [("Mach'a", "who"), ("ya", "ICP"), ("x-'a'tej-at", "ICP-work-B2"), ("ta", "P"), ("s-nah", "A3-house")]
    glossedWords := [⟨[['M', 'a', 'c', 'h', '\'', 'a']], [['w', 'h', 'o']]⟩, ⟨[['y', 'a']], [['I', 'C', 'P']]⟩, ⟨[['x'], ['\'', 'a', '\'', 't', 'e', 'j'], ['a', 't']], [['I', 'C', 'P'], ['w', 'o', 'r', 'k'], ['B', '2']]⟩, ⟨[['t', 'a']], [['P']]⟩, ⟨[['s'], ['n', 'a', 'h']], [['A', '3'], ['h', 'o', 'u', 's', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Unergative with a specific (second-person) S_A."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "OP"), ("possessum", "nonSpecific"), ("clause", "unergative"), ("intervener", "S_A"), ("table4", "T-SA-unergative")] }

def ex69 : Datum :=
  { id := "aissenpolian2025_ex69"
    source := ⟨"aissen-polian-2025", "(69)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Mach'a x-'a'tej alaletik ta s-nah?"
    glossedTokens := [("Mach'a", "who"), ("x-'a'tej", "ICP-work"), ("alaletik", "children"), ("ta", "P"), ("s-nah", "A3-house")]
    glossedWords := [⟨[['M', 'a', 'c', 'h', '\'', 'a']], [['w', 'h', 'o']]⟩, ⟨[['x'], ['\'', 'a', '\'', 't', 'e', 'j']], [['I', 'C', 'P'], ['w', 'o', 'r', 'k']]⟩, ⟨[['a', 'l', 'a', 'l', 'e', 't', 'i', 'k']], [['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n']]⟩, ⟨[['t', 'a']], [['P']]⟩, ⟨[['s'], ['n', 'a', 'h']], [['A', '3'], ['h', 'o', 'u', 's', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Unergative with a non-specific S_A."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "OP"), ("possessum", "nonSpecific"), ("clause", "unergative"), ("intervener", "none"), ("table4", "T-SA-unergative")] }

def ex70 : Datum :=
  { id := "aissenpolian2025_ex70"
    source := ⟨"aissen-polian-2025", "(70)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Buch'i i-s-mil li Xun=e?"
    glossedTokens := [("Buch'i", "who"), ("i-s-mil", "CP-A3-kill"), ("li", "DET"), ("Xun=e", "Juan=ENC")]
    glossedWords := [⟨[['B', 'u', 'c', 'h', '\'', 'i']], [['w', 'h', 'o']]⟩, ⟨[['i'], ['s'], ['m', 'i', 'l']], [['C', 'P'], ['A', '3'], ['k', 'i', 'l', 'l']]⟩, ⟨[['l', 'i']], [['D', 'E', 'T']]⟩, ⟨[['X', 'u', 'n'], ['e']], [['J', 'u', 'a', 'n'], ['E', 'N', 'C']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Ambiguous transitive question."
    judgment := .acceptable
    alternatives := []
    readings := [("who killed Juan", .acceptable), ("who did Juan kill", .acceptable)]
    paperFeatures := [("clause", "transitive")] }

def ex74 : Datum :=
  { id := "aissenpolian2025_ex74"
    source := ⟨"aissen-polian-2025", "(74)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Och wakax ta s-na te j-Xun=e."
    glossedTokens := [("Och", "CP.enter"), ("wakax", "cow"), ("ta", "in"), ("s-na", "A3-house"), ("te", "DET"), ("j-Xun=e", "M-Juan=ENC")]
    glossedWords := [⟨[['O', 'c', 'h']], [['C', 'P', '.', 'e', 'n', 't', 'e', 'r']]⟩, ⟨[['w', 'a', 'k', 'a', 'x']], [['c', 'o', 'w']]⟩, ⟨[['t', 'a']], [['i', 'n']]⟩, ⟨[['s'], ['n', 'a']], [['A', '3'], ['h', 'o', 'u', 's', 'e']]⟩, ⟨[['t', 'e']], [['D', 'E', 'T']]⟩, ⟨[['j'], ['X', 'u', 'n'], ['e']], [['M'], ['J', 'u', 'a', 'n'], ['E', 'N', 'C']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Path verb with a non-specific theme and a locative PP."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("construction", "pathVerb")] }

def ex75a : Datum :=
  { id := "aissenpolian2025_ex75a"
    source := ⟨"aissen-polian-2025", "(75a)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Mach'a och wakax [ta s-na]?"
    glossedTokens := [("Mach'a", "who"), ("och", "CP.enter"), ("wakax", "cow"), ("ta", "P"), ("s-na", "A3-house")]
    glossedWords := [⟨[['M', 'a', 'c', 'h', '\'', 'a']], [['w', 'h', 'o']]⟩, ⟨[['o', 'c', 'h']], [['C', 'P', '.', 'e', 'n', 't', 'e', 'r']]⟩, ⟨[['w', 'a', 'k', 'a', 'x']], [['c', 'o', 'w']]⟩, ⟨[['t', 'a']], [['P']]⟩, ⟨[['s'], ['n', 'a']], [['A', '3'], ['h', 'o', 'u', 's', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Path verb, non-specific theme."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "OP"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "pathVerb"), ("table4", "T-SO-unaccusative")] }

def ex75b : Datum :=
  { id := "aissenpolian2025_ex75b"
    source := ⟨"aissen-polian-2025", "(75b)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Mach'a och-at [ta s-na]?"
    glossedTokens := [("Mach'a", "who"), ("och-at", "CP.enter-B2SG"), ("ta", "P"), ("s-na", "A3-house")]
    glossedWords := [⟨[['M', 'a', 'c', 'h', '\'', 'a']], [['w', 'h', 'o']]⟩, ⟨[['o', 'c', 'h'], ['a', 't']], [['C', 'P', '.', 'e', 'n', 't', 'e', 'r'], ['B', '2', 'S', 'G']]⟩, ⟨[['t', 'a']], [['P']]⟩, ⟨[['s'], ['n', 'a']], [['A', '3'], ['h', 'o', 'u', 's', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Path verb, specific (second-person) theme."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "OP"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "S_O"), ("construction", "pathVerb"), ("table4", "T-SO-unaccusative")] }

def ex77b : Datum :=
  { id := "aissenpolian2025_ex77b"
    source := ⟨"aissen-polian-2025", "(77b)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Much'u oy ixim [ta s-na]?"
    glossedTokens := [("Much'u", "who"), ("oy", "EXIS"), ("ixim", "corn"), ("ta", "P"), ("s-na", "A3-house")]
    glossedWords := [⟨[['M', 'u', 'c', 'h', '\'', 'u']], [['w', 'h', 'o']]⟩, ⟨[['o', 'y']], [['E', 'X', 'I', 'S']]⟩, ⟨[['i', 'x', 'i', 'm']], [['c', 'o', 'r', 'n']]⟩, ⟨[['t', 'a']], [['P']]⟩, ⟨[['s'], ['n', 'a']], [['A', '3'], ['h', 'o', 'u', 's', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Locative existential with a non-specific theme."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "OP"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "locativeExistential"), ("table4", "T-none-locativeExistential")] }

def ex78a : Datum :=
  { id := "aissenpolian2025_ex78a"
    source := ⟨"aissen-polian-2025", "(78a)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Mach'a ay-at [ta s-nah]?"
    glossedTokens := [("Mach'a", "who"), ("ay-at", "EXIS-B2"), ("ta", "P"), ("s-nah", "A3-house")]
    glossedWords := [⟨[['M', 'a', 'c', 'h', '\'', 'a']], [['w', 'h', 'o']]⟩, ⟨[['a', 'y'], ['a', 't']], [['E', 'X', 'I', 'S'], ['B', '2']]⟩, ⟨[['t', 'a']], [['P']]⟩, ⟨[['s'], ['n', 'a', 'h']], [['A', '3'], ['h', 'o', 'u', 's', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Locative copula with a specific theme, Petalcingo Tseltal."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "OP"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "S_O"), ("construction", "locativeCopula"), ("table4", "T-SO-locativeCopula")] }

def ex78b : Datum :=
  { id := "aissenpolian2025_ex78b"
    source := ⟨"aissen-polian-2025", "(78b)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Much'u oy-ot [ta s-na]?"
    glossedTokens := [("Much'u", "who"), ("oy-ot", "EXIS-B2"), ("ta", "P"), ("s-na", "A3-house")]
    glossedWords := [⟨[['M', 'u', 'c', 'h', '\'', 'u']], [['w', 'h', 'o']]⟩, ⟨[['o', 'y'], ['o', 't']], [['E', 'X', 'I', 'S'], ['B', '2']]⟩, ⟨[['t', 'a']], [['P']]⟩, ⟨[['s'], ['n', 'a']], [['A', '3'], ['h', 'o', 'u', 's', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Locative copula with a specific theme."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "OP"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "S_O"), ("construction", "locativeCopula"), ("table4", "T-SO-locativeCopula")] }

def ex81 : Datum :=
  { id := "aissenpolian2025_ex81"
    source := ⟨"aissen-polian-2025", "(81)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Mach'a k'ux-at [ta y-o'tan]?"
    glossedTokens := [("Mach'a", "who"), ("k'ux-at", "painful-B2"), ("ta", "P"), ("y-o'tan", "A3-heart")]
    glossedWords := [⟨[['M', 'a', 'c', 'h', '\'', 'a']], [['w', 'h', 'o']]⟩, ⟨[['k', '\'', 'u', 'x'], ['a', 't']], [['p', 'a', 'i', 'n', 'f', 'u', 'l'], ['B', '2']]⟩, ⟨[['t', 'a']], [['P']]⟩, ⟨[['y'], ['o', '\'', 't', 'a', 'n']], [['A', '3'], ['h', 'e', 'a', 'r', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Two-argument experiential collocation with a specific (second-person) theme."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "OP"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "twoArgExperiential"), ("table4", "T-none-experiential")] }

def ex82 : Datum :=
  { id := "aissenpolian2025_ex82"
    source := ⟨"aissen-polian-2025", "(82)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Much'u i-yul [ta s-jol] [(ta) s-man-el kantela]?"
    glossedTokens := [("Much'u", "who"), ("i-yul", "CP-arrive"), ("ta", "P"), ("s-jol", "A3-head"), ("ta", "P"), ("s-man-el", "A3-buy-NMLZ"), ("kantela", "candle")]
    glossedWords := [⟨[['M', 'u', 'c', 'h', '\'', 'u']], [['w', 'h', 'o']]⟩, ⟨[['i'], ['y', 'u', 'l']], [['C', 'P'], ['a', 'r', 'r', 'i', 'v', 'e']]⟩, ⟨[['t', 'a']], [['P']]⟩, ⟨[['s'], ['j', 'o', 'l']], [['A', '3'], ['h', 'e', 'a', 'd']]⟩, ⟨[['t', 'a']], [['P']]⟩, ⟨[['s'], ['m', 'a', 'n'], ['e', 'l']], [['A', '3'], ['b', 'u', 'y'], ['N', 'M', 'L', 'Z']]⟩, ⟨[['k', 'a', 'n', 't', 'e', 'l', 'a']], [['c', 'a', 'n', 'd', 'l', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Two-argument experiential collocation yul ta -jol."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "OP"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "twoArgExperiential"), ("table4", "T-none-experiential")] }

def ex85a : Datum :=
  { id := "aissenpolian2025_ex85a"
    source := ⟨"aissen-polian-2025", "(85a)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "[Much'u x-ch'amal] i-y-elk'an chij?"
    glossedTokens := [("Much'u", "who"), ("x-ch'amal", "A3-child.of.male"), ("i-y-elk'an", "CP-A3-steal"), ("chij", "sheep")]
    glossedWords := [⟨[['M', 'u', 'c', 'h', '\'', 'u']], [['w', 'h', 'o']]⟩, ⟨[['x'], ['c', 'h', '\'', 'a', 'm', 'a', 'l']], [['A', '3'], ['c', 'h', 'i', 'l', 'd', '.', 'o', 'f', '.', 'm', 'a', 'l', 'e']]⟩, ⟨[['i'], ['y'], ['e', 'l', 'k', '\'', 'a', 'n']], [['C', 'P'], ['A', '3'], ['s', 't', 'e', 'a', 'l']]⟩, ⟨[['c', 'h', 'i', 'j']], [['s', 'h', 'e', 'e', 'p']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Possessive A."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "piedPiping"), ("possessorOf", "A"), ("possessum", "specific"), ("clause", "transitive"), ("intervener", "none")] }

def ex85b : Datum :=
  { id := "aissenpolian2025_ex85b"
    source := ⟨"aissen-polian-2025", "(85b)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Much'u i-y-elk'an chij x-ch'amal?"
    glossedTokens := [("Much'u", "who"), ("i-y-elk'an", "CP-A3-steal"), ("chij", "sheep"), ("x-ch'amal", "A3-child.of.male")]
    glossedWords := [⟨[['M', 'u', 'c', 'h', '\'', 'u']], [['w', 'h', 'o']]⟩, ⟨[['i'], ['y'], ['e', 'l', 'k', '\'', 'a', 'n']], [['C', 'P'], ['A', '3'], ['s', 't', 'e', 'a', 'l']]⟩, ⟨[['c', 'h', 'i', 'j']], [['s', 'h', 'e', 'e', 'p']]⟩, ⟨[['x'], ['c', 'h', '\'', 'a', 'm', 'a', 'l']], [['A', '3'], ['c', 'h', 'i', 'l', 'd', '.', 'o', 'f', '.', 'm', 'a', 'l', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Possessive A, stranded; the A is specific."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "A"), ("possessum", "specific"), ("clause", "transitive"), ("intervener", "none")] }

def ex86 : Datum :=
  { id := "aissenpolian2025_ex86"
    source := ⟨"aissen-polian-2025", "(86)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Mach'a la s-wilunta-on [x-ch'akul]?"
    glossedTokens := [("Mach'a", "who"), ("la", "CP"), ("s-wilunta-on", "A3-fly.onto-B1"), ("x-ch'akul", "A3-flea")]
    glossedWords := [⟨[['M', 'a', 'c', 'h', '\'', 'a']], [['w', 'h', 'o']]⟩, ⟨[['l', 'a']], [['C', 'P']]⟩, ⟨[['s'], ['w', 'i', 'l', 'u', 'n', 't', 'a'], ['o', 'n']], [['A', '3'], ['f', 'l', 'y', '.', 'o', 'n', 't', 'o'], ['B', '1']]⟩, ⟨[['x'], ['c', 'h', '\'', 'a', 'k', 'u', 'l']], [['A', '3'], ['f', 'l', 'e', 'a']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Transitive with a non-specific possessive A whose possessor is a plausible ψ-subject."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "A"), ("possessum", "nonSpecific"), ("clause", "transitive"), ("intervener", "none")] }

def ex87 : Datum :=
  { id := "aissenpolian2025_ex87"
    source := ⟨"aissen-polian-2025", "(87)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "La s-wilunta-on [x-ch'akul] ajk'ube [te ts'i'=e]."
    glossedTokens := [("La", "CP"), ("s-wilunta-on", "A3-fly.onto-B1"), ("x-ch'akul", "A3-flea"), ("ajk'ube", "last.night"), ("te", "DET"), ("ts'i'=e", "dog=ENC")]
    glossedWords := [⟨[['L', 'a']], [['C', 'P']]⟩, ⟨[['s'], ['w', 'i', 'l', 'u', 'n', 't', 'a'], ['o', 'n']], [['A', '3'], ['f', 'l', 'y', '.', 'o', 'n', 't', 'o'], ['B', '1']]⟩, ⟨[['x'], ['c', 'h', '\'', 'a', 'k', 'u', 'l']], [['A', '3'], ['f', 'l', 'e', 'a']]⟩, ⟨[['a', 'j', 'k', '\'', 'u', 'b', 'e']], [['l', 'a', 's', 't', '.', 'n', 'i', 'g', 'h', 't']]⟩, ⟨[['t', 'e']], [['D', 'E', 'T']]⟩, ⟨[['t', 's', '\'', 'i', '\''], ['e']], [['d', 'o', 'g'], ['E', 'N', 'C']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Possessor and possessum separated by an adverb."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("construction", "lexicalTransitive"), ("possessum", "nonSpecific")] }

def all : List Datum := [ex1, ex2a, ex2b, ex4, ex5, ex20a, ex20b, ex22a, ex22b, ex26b, ex23a, ex23b, ex24, ex25, ex27, ex28b, ex28c, ex30, ex31, ex32, ex35, ex36, ex37, ex43, ex45a, ex45b, ex46, ex47, ex48a, ex48b, ex49a, ex49b, ex50a, ex51, ex55a, ex55b, ex57b, ex58b, ex59, ex60, ex61, ex62a, ex62b, ex65, ex66, ex67, ex68, ex69, ex70, ex74, ex75a, ex75b, ex77b, ex78a, ex78b, ex81, ex82, ex85a, ex85b, ex86, ex87]

end AissenPolian2025.Examples
