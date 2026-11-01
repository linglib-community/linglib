module

public import Linglib.Data.Examples.Schema

/-!
# `DalrympleKaplan2000` — typed example data

Auto-generated from `Linglib/Data/Examples/DalrympleKaplan2000.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace DalrympleKaplan2000.Examples`.
-/

@[expose] public section

namespace DalrympleKaplan2000.Examples

def ex_17 : Datum :=
  { id := "dalrymplekaplan2000_17"
    source := ⟨"dalrymple-kaplan-2000", "(17)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Ich habe gegessen was übrig war."
    glossedTokens := [("Ich", "I"), ("habe", "have"), ("gegessen", "eaten"), ("was", "what"), ("übrig", "left"), ("war", "was")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("requirements", "ACC by gegessen, NOM by übrig war")] }

def ex_32 : Datum :=
  { id := "dalrymplekaplan2000_32"
    source := ⟨"dalrymple-kaplan-2000", "(32)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wem du vertraust muss klug sein."
    glossedTokens := [("Wem", "who"), ("du", "you"), ("vertraust", "trust"), ("muss", "must"), ("klug", "clever"), ("sein", "be")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("requirements", "DAT by vertraust, NOM by muss")] }

def ex_40 : Datum :=
  { id := "dalrymplekaplan2000_40"
    source := ⟨"dyla-1984", "p. 701"⟩
    reportedIn := some ⟨"dalrymple-kaplan-2000", "(40)"⟩
    language := "poli1260"
    primaryText := "Kogo Janek lubi a Jerzy nienawidzi?"
    glossedTokens := [("Kogo", "who"), ("Janek", "Janek"), ("lubi", "likes"), ("a", "and"), ("Jerzy", "Jerzy"), ("nienawidzi", "hates")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("requirements", "ACC by lubi, GEN by nienawidzi")] }

def ex_41 : Datum :=
  { id := "dalrymplekaplan2000_41"
    source := ⟨"dalrymple-kaplan-2000", "(41)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Co Janek lubi a Jerzy nienawidzi?"
    glossedTokens := [("Co", "what"), ("Janek", "Janek"), ("lubi", "likes"), ("a", "and"), ("Jerzy", "Jerzy"), ("nienawidzi", "hates")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("requirements", "ACC by lubi, GEN by nienawidzi")] }

def ex_47 : Datum :=
  { id := "dalrymplekaplan2000_47"
    source := ⟨"pullum-zwicky-1986", "p. 761"⟩
    reportedIn := some ⟨"dalrymple-kaplan-2000", "(47)"⟩
    language := "stan1293"
    primaryText := "I certainly will, and you already have, clarify the situation with respect to the budget."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("requirements", "BASE by will, PPART by have")] }

def ex_48 : Datum :=
  { id := "dalrymplekaplan2000_48"
    source := ⟨"pullum-zwicky-1986", "p. 761"⟩
    reportedIn := some ⟨"dalrymple-kaplan-2000", "(48)"⟩
    language := "stan1293"
    primaryText := "I certainly will, and you already have, clarified the situation with respect to the budget."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("requirements", "BASE by will, PPART by have")] }

def ex_49 : Datum :=
  { id := "dalrymplekaplan2000_49"
    source := ⟨"dalrymple-kaplan-2000", "(49)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I certainly will, and you already have, set the record straight with respect to the budget."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("requirements", "BASE by will, PPART by have")] }

def ex_53a : Datum :=
  { id := "dalrymplekaplan2000_53a"
    source := ⟨"voeltz-1971", "Xhosa coordination"⟩
    reportedIn := some ⟨"dalrymple-kaplan-2000", "(53a)"⟩
    language := "xhos1239"
    primaryText := "Igqira nesanuse ayagoduka."
    glossedTokens := [("Igqira", "doctor"), ("nesanuse", "and.diviner"), ("ayagoduka", "go.home")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.4"), ("classes", "5/6 and 7/8"), ("requirement", "class 5/6")] }

def ex_53b : Datum :=
  { id := "dalrymplekaplan2000_53b"
    source := ⟨"voeltz-1971", "Xhosa coordination"⟩
    reportedIn := some ⟨"dalrymple-kaplan-2000", "(53b)"⟩
    language := "xhos1239"
    primaryText := "Igqira nesanuse ziyagoduka."
    glossedTokens := [("Igqira", "doctor"), ("nesanuse", "and.diviner"), ("ziyagoduka", "go.home")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.4"), ("classes", "5/6 and 7/8"), ("requirement", "class 7/8")] }

def ex_54 : Datum :=
  { id := "dalrymplekaplan2000_54"
    source := ⟨"voeltz-1971", "Xhosa coordination"⟩
    reportedIn := some ⟨"dalrymple-kaplan-2000", "(54)"⟩
    language := "xhos1239"
    primaryText := "Izandla neendlebe zibomvu."
    glossedTokens := [("Izandla", "hands"), ("neendlebe", "and.ears"), ("zibomvu", "are.red")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.4"), ("classes", "7/8 and 9/10"), ("requirement", "class in {7/8, 9/10}")] }

def ex_57 : Datum :=
  { id := "dalrymplekaplan2000_57"
    source := ⟨"corbett-1991", "pp. 276ff."⟩
    reportedIn := some ⟨"dalrymple-kaplan-2000", "(57)"⟩
    language := "nyan1308"
    primaryText := "ma-lalanje ndi ma-samba a-kubvunda."
    glossedTokens := [("ma-lalanje", "orange"), ("ndi", "and"), ("ma-samba", "leaf"), ("a-kubvunda", "are.rotting")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.4"), ("classes", "6 and 6"), ("requirement", "class in {2, 6}")] }

def ex_58 : Datum :=
  { id := "dalrymplekaplan2000_58"
    source := ⟨"corbett-1991", "pp. 276ff."⟩
    reportedIn := some ⟨"dalrymple-kaplan-2000", "(58)"⟩
    language := "nyan1308"
    primaryText := "a-mphaka ndi a-galu a-kuthamanga."
    glossedTokens := [("a-mphaka", "cat"), ("ndi", "and"), ("a-galu", "dog"), ("a-kuthamanga", "are.running")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.4"), ("classes", "2 and 2"), ("requirement", "class in {2, 6}")] }

def ex_59 : Datum :=
  { id := "dalrymplekaplan2000_59"
    source := ⟨"corbett-1991", "pp. 276ff."⟩
    reportedIn := some ⟨"dalrymple-kaplan-2000", "(59)"⟩
    language := "nyan1308"
    primaryText := "a-mphaka ndi ma-lalanje a-li uko."
    glossedTokens := [("a-mphaka", "cat"), ("ndi", "and"), ("ma-lalanje", "orange"), ("a-li", "be"), ("uko", "there")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.4"), ("classes", "2 and 6"), ("requirement", "class in {2, 6}")] }

def ex_61 : Datum :=
  { id := "dalrymplekaplan2000_61"
    source := ⟨"eisenberg-1973", "right node raising"⟩
    reportedIn := some ⟨"dalrymple-kaplan-2000", "(61)"⟩
    language := "stan1295"
    primaryText := "weil wir das Haus und die Müllers den Garten kaufen"
    glossedTokens := [("weil", "because"), ("wir", "we"), ("das", "the"), ("Haus", "house"), ("und", "and"), ("die", "the"), ("Müllers", "Müllers"), ("den", "the"), ("Garten", "garden"), ("kaufen", "buy")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.4"), ("subjects", "1PL and 3PL"), ("requirement", "person in {1, 3}")] }

def ex_64 : Datum :=
  { id := "dalrymplekaplan2000_64"
    source := ⟨"pullum-zwicky-1986", "p. 771"⟩
    reportedIn := some ⟨"dalrymple-kaplan-2000", "(64)"⟩
    method := some .elicitation
    language := "stan1295"
    primaryText := "weil ihr das Haus und Franz den Garten kauft"
    glossedTokens := [("weil", "because"), ("ihr", "you"), ("das", "the"), ("Haus", "house"), ("und", "and"), ("Franz", "Franz"), ("den", "the"), ("Garten", "garden"), ("kauft", "buy")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.4"), ("subjects", "2PL and 3SG"), ("requirement", "cell in {2PL, 3SG}")] }

def ex_71 : Datum :=
  { id := "dalrymplekaplan2000_71"
    source := ⟨"dalrymple-kaplan-2000", "(71)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "José y yo hablamos."
    glossedTokens := [("José", "José"), ("y", "and"), ("yo", "I"), ("hablamos", "speak.1PL")]
    context := ""
    judgment := .acceptable
    alternatives := [("José y yo habláis.", .ungrammatical), ("José y yo hablan.", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "5"), ("conjuncts", "3SG and 1SG"), ("agreement", "1PL")] }

def ex_76 : Datum :=
  { id := "dalrymplekaplan2000_76"
    source := ⟨"corbett-1983", "p. 178"⟩
    reportedIn := some ⟨"dalrymple-kaplan-2000", "(76)"⟩
    language := "slov1269"
    primaryText := "Ja a ty sme bratia."
    glossedTokens := [("Ja", "I"), ("a", "and"), ("ty", "you"), ("sme", "are.1PL"), ("bratia", "brothers")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6"), ("conjuncts", "1SG and 2SG"), ("agreement", "1PL")] }

def ex_81 : Datum :=
  { id := "dalrymplekaplan2000_81"
    source := ⟨"dalrymple-kaplan-2000", "(81)"⟩
    reportedIn := none
    language := "pula1262"
    primaryText := "an e Bill kö Afriki djodu-don."
    glossedTokens := [("an", "you"), ("e", "and"), ("Bill", "Bill"), ("kö", "in"), ("Afriki", "Africa"), ("djodu-don", "live.2PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1"), ("conjuncts", "2 and 3"), ("agreement", "2")] }

def ex_82 : Datum :=
  { id := "dalrymplekaplan2000_82"
    source := ⟨"dalrymple-kaplan-2000", "(82)"⟩
    reportedIn := none
    language := "pula1262"
    primaryText := "Bill e George kö Afriki bè-djodi."
    glossedTokens := [("Bill", "Bill"), ("e", "and"), ("George", "George"), ("kö", "in"), ("Afriki", "Africa"), ("bè-djodi", "live.3PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1"), ("conjuncts", "3 and 3"), ("agreement", "3")] }

def ex_83 : Datum :=
  { id := "dalrymplekaplan2000_83"
    source := ⟨"dalrymple-kaplan-2000", "(83)"⟩
    reportedIn := none
    language := "pula1262"
    primaryText := "an e min kö Afriki djodu-dèn."
    glossedTokens := [("an", "you"), ("e", "and"), ("min", "I"), ("kö", "in"), ("Afriki", "Africa"), ("djodu-dèn", "live.1INCL.PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1"), ("conjuncts", "2 and 1"), ("agreement", "1INCL.PL")] }

def ex_84 : Datum :=
  { id := "dalrymplekaplan2000_84"
    source := ⟨"dalrymple-kaplan-2000", "(84)"⟩
    reportedIn := none
    language := "pula1262"
    primaryText := "an e Bill e min kö Afriki djodu-dèn."
    glossedTokens := [("an", "you"), ("e", "and"), ("Bill", "Bill"), ("e", "and"), ("min", "I"), ("kö", "in"), ("Afriki", "Africa"), ("djodu-dèn", "live.1INCL.PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1"), ("conjuncts", "2, 3 and 1"), ("agreement", "1INCL.PL")] }

def ex_85 : Datum :=
  { id := "dalrymplekaplan2000_85"
    source := ⟨"dalrymple-kaplan-2000", "(85)"⟩
    reportedIn := none
    language := "pula1262"
    primaryText := "Bill e min kö Afriki mèn-djodi."
    glossedTokens := [("Bill", "Bill"), ("e", "and"), ("min", "I"), ("kö", "in"), ("Afriki", "Africa"), ("mèn-djodi", "live.1EXCL.PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1"), ("conjuncts", "3 and 1"), ("agreement", "1EXCL.PL")] }

def ex_86 : Datum :=
  { id := "dalrymplekaplan2000_86"
    source := ⟨"dalrymple-kaplan-2000", "(86)"⟩
    reportedIn := none
    language := "pula1262"
    primaryText := "Bill e mènèn kö Afriki mèn-djodi."
    glossedTokens := [("Bill", "Bill"), ("e", "and"), ("mènèn", "we.EXCL"), ("kö", "in"), ("Afriki", "Africa"), ("mèn-djodi", "live.1EXCL.PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1"), ("conjuncts", "3 and 1EXCL"), ("agreement", "1EXCL.PL")] }

def ex_95 : Datum :=
  { id := "dalrymplekaplan2000_95"
    source := ⟨"dalrymple-kaplan-2000", "(95)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "José y tú habláis."
    glossedTokens := [("José", "José"), ("y", "and"), ("tú", "you"), ("habláis", "speak.2PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.4"), ("conjuncts", "3SG and 2SG"), ("agreement", "2PL")] }

def ex_107 : Datum :=
  { id := "dalrymplekaplan2000_107"
    source := ⟨"dalrymple-kaplan-2000", "(107)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "meraa kuttaa aur merii billii mere saath gʰar mẽ rahte hãĩ."
    glossedTokens := [("meraa", "my"), ("kuttaa", "dog"), ("aur", "and"), ("merii", "my"), ("billii", "cat"), ("mere saath", "with me"), ("gʰar", "house"), ("mẽ", "LOC"), ("rahte hãĩ", "live.MASC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.1"), ("conjuncts", "MASC and FEM"), ("agreement", "MASC")] }

def ex_108 : Datum :=
  { id := "dalrymplekaplan2000_108"
    source := ⟨"dalrymple-kaplan-2000", "(108)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "yah laṛki aur uski mãã dilli mẽ rahtii hãĩ."
    glossedTokens := [("yah", "this"), ("laṛki", "girl"), ("aur", "and"), ("uski", "her"), ("mãã", "mother"), ("dilli", "Delhi"), ("mẽ", "LOC"), ("rahtii hãĩ", "live.FEM")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.1"), ("conjuncts", "FEM and FEM"), ("agreement", "FEM")] }

def ex_115 : Datum :=
  { id := "dalrymplekaplan2000_115"
    source := ⟨"dalrymple-kaplan-2000", "(115)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "drengurinn og telpan eru þreytt."
    glossedTokens := [("drengurinn", "the.boy"), ("og", "and"), ("telpan", "the.girl"), ("eru", "are"), ("þreytt", "tired.NEUT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.2"), ("conjuncts", "MASC and FEM"), ("agreement", "NEUT")] }

def ex_116 : Datum :=
  { id := "dalrymplekaplan2000_116"
    source := ⟨"dalrymple-kaplan-2000", "(116)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "maðurinn og barnið eru þreytt."
    glossedTokens := [("maðurinn", "the.man"), ("og", "and"), ("barnið", "the.baby"), ("eru", "are"), ("þreytt", "tired.NEUT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.2"), ("conjuncts", "MASC and NEUT"), ("agreement", "NEUT")] }

def ex_117 : Datum :=
  { id := "dalrymplekaplan2000_117"
    source := ⟨"dalrymple-kaplan-2000", "(117)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "ég sá á og lamb bæði svört."
    glossedTokens := [("ég", "I"), ("sá", "saw"), ("á", "a.ewe"), ("og", "and"), ("lamb", "a.lamb"), ("bæði", "both"), ("svört", "black.NEUT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.2"), ("conjuncts", "FEM and NEUT"), ("agreement", "NEUT")] }

def ex_123 : Datum :=
  { id := "dalrymplekaplan2000_123"
    source := ⟨"dalrymple-kaplan-2000", "(123)"⟩
    reportedIn := none
    language := "slov1268"
    primaryText := "To drevo in gnezdo na njem mi bosta ostala v spominu."
    glossedTokens := [("To", "that"), ("drevo", "tree"), ("in", "and"), ("gnezdo", "the.nest"), ("na", "on"), ("njem", "it"), ("mi", "to.me"), ("bosta", "will"), ("ostala", "remain.MASC"), ("v", "in"), ("spominu", "memory")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.3"), ("conjuncts", "NEUT and NEUT"), ("agreement", "MASC")] }

def ex_128 : Datum :=
  { id := "dalrymplekaplan2000_128"
    source := ⟨"dalrymple-kaplan-2000", "(128)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "wah pahũcaa aur pahũcii."
    glossedTokens := [("wah", "he/she"), ("pahũcaa", "arrived.MASC"), ("aur", "and"), ("pahũcii", "arrived.FEM")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "8"), ("requirements", "GENDER =c MASC and GENDER =c FEM")] }

def ex_141a : Datum :=
  { id := "dalrymplekaplan2000_141a"
    source := ⟨"dalrymple-kaplan-2000", "(141a)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "wah pahũcaa."
    glossedTokens := [("wah", "he/she"), ("pahũcaa", "arrived.MASC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "8"), ("requirements", "GENDER =c MASC")] }

def ex_141b : Datum :=
  { id := "dalrymplekaplan2000_141b"
    source := ⟨"dalrymple-kaplan-2000", "(141b)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "wah pahũcii."
    glossedTokens := [("wah", "he/she"), ("pahũcii", "arrived.FEM")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "8"), ("requirements", "GENDER =c FEM")] }

def all : List Datum := [ex_17, ex_32, ex_40, ex_41, ex_47, ex_48, ex_49, ex_53a, ex_53b, ex_54, ex_57, ex_58, ex_59, ex_61, ex_64, ex_71, ex_76, ex_81, ex_82, ex_83, ex_84, ex_85, ex_86, ex_95, ex_107, ex_108, ex_115, ex_116, ex_117, ex_123, ex_128, ex_141a, ex_141b]

end DalrympleKaplan2000.Examples
