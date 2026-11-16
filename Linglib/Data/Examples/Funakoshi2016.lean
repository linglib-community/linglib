module

public import Linglib.Data.Examples.Schema

/-!
# `Funakoshi2016` — typed example data

Auto-generated from `Linglib/Data/Examples/Funakoshi2016.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Funakoshi2016.Examples`.
-/

@[expose] public section

namespace Funakoshi2016.Examples

def ex15b : Datum :=
  { id := "funakoshi2016_ex15b"
    source := ⟨"funakoshi-2016", "(15b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "John-mo Δ araw-anak-atta"
    glossedTokens := [("John-mo", "John-also"), ("araw-anak-atta", "wash-NEG-PAST")]
    glossedWords := [⟨[['J', 'o', 'h', 'n'], ['m', 'o']], [['J', 'o', 'h', 'n'], ['a', 'l', 's', 'o']]⟩, ⟨[['a', 'r', 'a', 'w'], ['a', 'n', 'a', 'k'], ['a', 't', 't', 'a']], [['w', 'a', 's', 'h'], ['N', 'E', 'G'], ['P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Antecedent: Bill-wa teineini kuruma-o araw-anak-atta 'Bill didn't wash the car carefully'."
    judgment := .acceptable
    alternatives := []
    readings := [("null adjunct", .acceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "null"), ("subjectNull", "no"), ("available", "yes")] }

def ex16 : Datum :=
  { id := "funakoshi2016_ex16"
    source := ⟨"funakoshi-2016", "(16)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Bill-wa teineini kuruma-o arat-ta kedo, John-wa Δ araw-anak-atta"
    glossedTokens := [("Bill-wa", "Bill-TOP"), ("teineini", "carefully"), ("kuruma-o", "car-ACC"), ("arat-ta", "wash-PAST"), ("kedo,", "but"), ("John-wa", "John-TOP"), ("araw-anak-atta", "wash-NEG-PAST")]
    glossedWords := [⟨[['B', 'i', 'l', 'l'], ['w', 'a']], [['B', 'i', 'l', 'l'], ['T', 'O', 'P']]⟩, ⟨[['t', 'e', 'i', 'n', 'e', 'i', 'n', 'i']], [['c', 'a', 'r', 'e', 'f', 'u', 'l', 'l', 'y']]⟩, ⟨[['k', 'u', 'r', 'u', 'm', 'a'], ['o']], [['c', 'a', 'r'], ['A', 'C', 'C']]⟩, ⟨[['a', 'r', 'a', 't'], ['t', 'a']], [['w', 'a', 's', 'h'], ['P', 'A', 'S', 'T']]⟩, ⟨[['k', 'e', 'd', 'o']], [['b', 'u', 't']]⟩, ⟨[['J', 'o', 'h', 'n'], ['w', 'a']], [['J', 'o', 'h', 'n'], ['T', 'O', 'P']]⟩, ⟨[['a', 'r', 'a', 'w'], ['a', 'n', 'a', 'k'], ['a', 't', 't', 'a']], [['w', 'a', 's', 'h'], ['N', 'E', 'G'], ['P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("null adjunct", .acceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "null"), ("subjectNull", "no"), ("available", "yes")] }

def ex17b : Datum :=
  { id := "funakoshi2016_ex17b"
    source := ⟨"funakoshi-2016", "(17b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Hanako-wa Δ araw-anak-atta"
    glossedTokens := [("Hanako-wa", "Hanako-TOP"), ("araw-anak-atta", "wash-NEG-PAST")]
    glossedWords := [⟨[['H', 'a', 'n', 'a', 'k', 'o'], ['w', 'a']], [['H', 'a', 'n', 'a', 'k', 'o'], ['T', 'O', 'P']]⟩, ⟨[['a', 'r', 'a', 'w'], ['a', 'n', 'a', 'k'], ['a', 't', 't', 'a']], [['w', 'a', 's', 'h'], ['N', 'E', 'G'], ['P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Taroo and Hanako washed their parents' cars to get allowance. Taroo was thorough in his work while Hanako was not. Antecedent: Taroo-wa teineini kuruma-o arat-ta 'Taroo washed the car carefully'."
    judgment := .acceptable
    alternatives := []
    readings := [("null adjunct", .acceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "null"), ("subjectNull", "no"), ("available", "yes")] }

def ex18b : Datum :=
  { id := "funakoshi2016_ex18b"
    source := ⟨"funakoshi-2016", "(18b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Hanako-wa Δ kak-ana-i."
    glossedTokens := [("Hanako-wa", "Hanako-TOP"), ("kak-ana-i.", "write-NEG-PRES")]
    glossedWords := [⟨[['H', 'a', 'n', 'a', 'k', 'o'], ['w', 'a']], [['H', 'a', 'n', 'a', 'k', 'o'], ['T', 'O', 'P']]⟩, ⟨[['k', 'a', 'k'], ['a', 'n', 'a'], ['i']], [['w', 'r', 'i', 't', 'e'], ['N', 'E', 'G'], ['P', 'R', 'E', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Taroo and Hanako are graduate students who often write papers. Taroo likes Microsoft Office while Hanako does not. Antecedent: Taroo-wa Word-de ronbun-o kak-u 'Taroo writes papers with Word'."
    judgment := .acceptable
    alternatives := []
    readings := [("null adjunct", .acceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "null"), ("subjectNull", "no"), ("available", "yes")] }

def ex19b : Datum :=
  { id := "funakoshi2016_ex19b"
    source := ⟨"funakoshi-2016", "(19b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Motiron Hanako-wa Δ kaw-ana-i."
    glossedTokens := [("Motiron", "of.course"), ("Hanako-wa", "Hanako-TOP"), ("kaw-ana-i.", "buy-NEG-PRES")]
    glossedWords := [⟨[['M', 'o', 't', 'i', 'r', 'o', 'n']], [['o', 'f', '.', 'c', 'o', 'u', 'r', 's', 'e']]⟩, ⟨[['H', 'a', 'n', 'a', 'k', 'o'], ['w', 'a']], [['H', 'a', 'n', 'a', 'k', 'o'], ['T', 'O', 'P']]⟩, ⟨[['k', 'a', 'w'], ['a', 'n', 'a'], ['i']], [['b', 'u', 'y'], ['N', 'E', 'G'], ['P', 'R', 'E', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Taroo and Hanako are faculty of a linguistics department and like comic books. Antecedent: Odoroitakotoni Taroo-wa kenkyuuhi-de manga-o ka-u 'Surprisingly enough, Taroo buys comic books with his research fund'."
    judgment := .acceptable
    alternatives := []
    readings := [("null adjunct", .acceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "null"), ("subjectNull", "no"), ("available", "yes")] }

def ex20b : Datum :=
  { id := "funakoshi2016_ex20b"
    source := ⟨"funakoshi-2016", "(20b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Hanako-wa Δ kuruma-o araw-anak-atta"
    glossedTokens := [("Hanako-wa", "Hanako-TOP"), ("kuruma-o", "car-ACC"), ("araw-anak-atta", "wash-NEG-PAST")]
    glossedWords := [⟨[['H', 'a', 'n', 'a', 'k', 'o'], ['w', 'a']], [['H', 'a', 'n', 'a', 'k', 'o'], ['T', 'O', 'P']]⟩, ⟨[['k', 'u', 'r', 'u', 'm', 'a'], ['o']], [['c', 'a', 'r'], ['A', 'C', 'C']]⟩, ⟨[['a', 'r', 'a', 'w'], ['a', 'n', 'a', 'k'], ['a', 't', 't', 'a']], [['w', 'a', 's', 'h'], ['N', 'E', 'G'], ['P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Taroo and Hanako washed their parents' cars to get allowance. Taroo was thorough in his work while Hanako was not. Antecedent: Taroo-wa teineini kuruma-o arat-ta 'Taroo washed the car carefully'."
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def ex21b : Datum :=
  { id := "funakoshi2016_ex21b"
    source := ⟨"funakoshi-2016", "(21b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Hanako-wa Δ ronbun-o kak-ana-i."
    glossedTokens := [("Hanako-wa", "Hanako-TOP"), ("ronbun-o", "paper-ACC"), ("kak-ana-i.", "write-NEG-PRES")]
    glossedWords := [⟨[['H', 'a', 'n', 'a', 'k', 'o'], ['w', 'a']], [['H', 'a', 'n', 'a', 'k', 'o'], ['T', 'O', 'P']]⟩, ⟨[['r', 'o', 'n', 'b', 'u', 'n'], ['o']], [['p', 'a', 'p', 'e', 'r'], ['A', 'C', 'C']]⟩, ⟨[['k', 'a', 'k'], ['a', 'n', 'a'], ['i']], [['w', 'r', 'i', 't', 'e'], ['N', 'E', 'G'], ['P', 'R', 'E', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Taroo and Hanako are graduate students who often write papers. Taroo likes Microsoft Office while Hanako does not. Antecedent: Taroo-wa Word-de ronbun-o kak-u 'Taroo writes papers with Word'."
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def ex22b : Datum :=
  { id := "funakoshi2016_ex22b"
    source := ⟨"funakoshi-2016", "(22b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Motiron Hanako-wa Δ manga-o kaw-ana-i."
    glossedTokens := [("Motiron", "of.course"), ("Hanako-wa", "Hanako-TOP"), ("manga-o", "comic.books-ACC"), ("kaw-ana-i.", "buy-NEG-PRES")]
    glossedWords := [⟨[['M', 'o', 't', 'i', 'r', 'o', 'n']], [['o', 'f', '.', 'c', 'o', 'u', 'r', 's', 'e']]⟩, ⟨[['H', 'a', 'n', 'a', 'k', 'o'], ['w', 'a']], [['H', 'a', 'n', 'a', 'k', 'o'], ['T', 'O', 'P']]⟩, ⟨[['m', 'a', 'n', 'g', 'a'], ['o']], [['c', 'o', 'm', 'i', 'c', '.', 'b', 'o', 'o', 'k', 's'], ['A', 'C', 'C']]⟩, ⟨[['k', 'a', 'w'], ['a', 'n', 'a'], ['i']], [['b', 'u', 'y'], ['N', 'E', 'G'], ['P', 'R', 'E', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Taroo and Hanako are faculty of a linguistics department and like comic books. Antecedent: Odoroitakotoni Taroo-wa kenkyuuhi-de manga-o ka-u 'Surprisingly enough, Taroo buys comic books with his research fund'."
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def ex23b : Datum :=
  { id := "funakoshi2016_ex23b"
    source := ⟨"funakoshi-2016", "(23b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Hanako-mo Δ kuruma-o araw-anak-atta"
    glossedTokens := [("Hanako-mo", "Hanako-also"), ("kuruma-o", "car-ACC"), ("araw-anak-atta", "wash-NEG-PAST")]
    glossedWords := [⟨[['H', 'a', 'n', 'a', 'k', 'o'], ['m', 'o']], [['H', 'a', 'n', 'a', 'k', 'o'], ['a', 'l', 's', 'o']]⟩, ⟨[['k', 'u', 'r', 'u', 'm', 'a'], ['o']], [['c', 'a', 'r'], ['A', 'C', 'C']]⟩, ⟨[['a', 'r', 'a', 'w'], ['a', 'n', 'a', 'k'], ['a', 't', 't', 'a']], [['w', 'a', 's', 'h'], ['N', 'E', 'G'], ['P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Taroo and Hanako both did careless work. Antecedent: Taroo-wa teineini kuruma-o araw-anak-atta 'Taroo did not wash the car carefully'."
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def ex24b : Datum :=
  { id := "funakoshi2016_ex24b"
    source := ⟨"funakoshi-2016", "(24b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Hanako-mo Δ ronbun-o kak-ana-i."
    glossedTokens := [("Hanako-mo", "Hanako-also"), ("ronbun-o", "paper-ACC"), ("kak-ana-i.", "write-NEG-PRES")]
    glossedWords := [⟨[['H', 'a', 'n', 'a', 'k', 'o'], ['m', 'o']], [['H', 'a', 'n', 'a', 'k', 'o'], ['a', 'l', 's', 'o']]⟩, ⟨[['r', 'o', 'n', 'b', 'u', 'n'], ['o']], [['p', 'a', 'p', 'e', 'r'], ['A', 'C', 'C']]⟩, ⟨[['k', 'a', 'k'], ['a', 'n', 'a'], ['i']], [['w', 'r', 'i', 't', 'e'], ['N', 'E', 'G'], ['P', 'R', 'E', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Taroo and Hanako do not like Microsoft Office. Antecedent: Taroo-wa Word-de ronbun-o kak-ana-i 'Taroo does not write papers with Word'."
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def ex25b : Datum :=
  { id := "funakoshi2016_ex25b"
    source := ⟨"funakoshi-2016", "(25b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Motiron Hanako-mo Δ manga-o kaw-ana-i."
    glossedTokens := [("Motiron", "of.course"), ("Hanako-mo", "Hanako-also"), ("manga-o", "comic.books-ACC"), ("kaw-ana-i.", "buy-NEG-PRES")]
    glossedWords := [⟨[['M', 'o', 't', 'i', 'r', 'o', 'n']], [['o', 'f', '.', 'c', 'o', 'u', 'r', 's', 'e']]⟩, ⟨[['H', 'a', 'n', 'a', 'k', 'o'], ['m', 'o']], [['H', 'a', 'n', 'a', 'k', 'o'], ['a', 'l', 's', 'o']]⟩, ⟨[['m', 'a', 'n', 'g', 'a'], ['o']], [['c', 'o', 'm', 'i', 'c', '.', 'b', 'o', 'o', 'k', 's'], ['A', 'C', 'C']]⟩, ⟨[['k', 'a', 'w'], ['a', 'n', 'a'], ['i']], [['b', 'u', 'y'], ['N', 'E', 'G'], ['P', 'R', 'E', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Antecedent: Taroo-wa kenkyuuhi-de manga-o kaw-ana-i 'Taroo does not buy comic books with his research fund'."
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def ex26b : Datum :=
  { id := "funakoshi2016_ex26b"
    source := ⟨"funakoshi-2016", "(26b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Demo Hanako-wa Δ madogarasu-o huk-anak-atta."
    glossedTokens := [("Demo", "but"), ("Hanako-wa", "Hanako-TOP"), ("madogarasu-o", "window-ACC"), ("huk-anak-atta.", "wipe-NEG-PAST")]
    glossedWords := [⟨[['D', 'e', 'm', 'o']], [['b', 'u', 't']]⟩, ⟨[['H', 'a', 'n', 'a', 'k', 'o'], ['w', 'a']], [['H', 'a', 'n', 'a', 'k', 'o'], ['T', 'O', 'P']]⟩, ⟨[['m', 'a', 'd', 'o', 'g', 'a', 'r', 'a', 's', 'u'], ['o']], [['w', 'i', 'n', 'd', 'o', 'w'], ['A', 'C', 'C']]⟩, ⟨[['h', 'u', 'k'], ['a', 'n', 'a', 'k'], ['a', 't', 't', 'a']], [['w', 'i', 'p', 'e'], ['N', 'E', 'G'], ['P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Taroo and Hanako washed a car together: Taroo the body, then Hanako the windows. Taroo was thorough, Hanako not. Antecedent: Taroo-wa teineini syatai-o arat-ta 'Taroo washed the body of the car carefully'."
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def ex27b : Datum :=
  { id := "funakoshi2016_ex27b"
    source := ⟨"funakoshi-2016", "(27b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Demo sensei-wa Δ komento-o irete-kure-nanak-atta."
    glossedTokens := [("Demo", "but"), ("sensei-wa", "teacher-TOP"), ("komento-o", "comment-ACC"), ("irete-kure-nanak-atta.", "put-BEN-NEG-PAST")]
    glossedWords := [⟨[['D', 'e', 'm', 'o']], [['b', 'u', 't']]⟩, ⟨[['s', 'e', 'n', 's', 'e', 'i'], ['w', 'a']], [['t', 'e', 'a', 'c', 'h', 'e', 'r'], ['T', 'O', 'P']]⟩, ⟨[['k', 'o', 'm', 'e', 'n', 't', 'o'], ['o']], [['c', 'o', 'm', 'm', 'e', 'n', 't'], ['A', 'C', 'C']]⟩, ⟨[['i', 'r', 'e', 't', 'e'], ['k', 'u', 'r', 'e'], ['n', 'a', 'n', 'a', 'k'], ['a', 't', 't', 'a']], [['p', 'u', 't'], ['B', 'E', 'N'], ['N', 'E', 'G'], ['P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Taroo gave his paper to his advisor expecting comments with the Comments feature of Word, but the advisor does not like Microsoft Office. Antecedent: Taroo-wa Word-de ronbun-o kai-ta 'Taroo wrote the paper with Word'."
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def ex32b : Datum :=
  { id := "funakoshi2016_ex32b"
    source := ⟨"funakoshi-2016", "(32b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Ippou pro [Hanako-wa Δ yame-ta to] omottei-na-i."
    glossedTokens := [("Ippou", "on.the.other.hand"), ("pro", "pro"), ("[Hanako-wa", "Hanako-TOP"), ("yame-ta", "quit-PAST"), ("to]", "C"), ("omottei-na-i.", "think-NEG-PRES")]
    glossedWords := [⟨[['I', 'p', 'p', 'o', 'u']], [['o', 'n', '.', 't', 'h', 'e', '.', 'o', 't', 'h', 'e', 'r', '.', 'h', 'a', 'n', 'd']]⟩, ⟨[['p', 'r', 'o']], [['p', 'r', 'o']]⟩, ⟨[['H', 'a', 'n', 'a', 'k', 'o'], ['w', 'a']], [['H', 'a', 'n', 'a', 'k', 'o'], ['T', 'O', 'P']]⟩, ⟨[['y', 'a', 'm', 'e'], ['t', 'a']], [['q', 'u', 'i', 't'], ['P', 'A', 'S', 'T']]⟩, ⟨[['t', 'o']], [['C']]⟩, ⟨[['o', 'm', 'o', 't', 't', 'e', 'i'], ['n', 'a'], ['i']], [['t', 'h', 'i', 'n', 'k'], ['N', 'E', 'G'], ['P', 'R', 'E', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Antecedent: Boku-wa [Taroo-wa [pro baka-da kara] kaisya-o yame-ta to] omottei-ru 'I think that Taroo quit the company because he was a fool'."
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "reason"), ("object", "null"), ("subjectNull", "no"), ("available", "no")] }

def ex39b : Datum :=
  { id := "funakoshi2016_ex39b"
    source := ⟨"funakoshi-2016", "(39b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Basu-wa Δ ko-nak-atta."
    glossedTokens := [("Basu-wa", "bus-TOP"), ("ko-nak-atta.", "come-NEG-PAST")]
    glossedWords := [⟨[['B', 'a', 's', 'u'], ['w', 'a']], [['b', 'u', 's'], ['T', 'O', 'P']]⟩, ⟨[['k', 'o'], ['n', 'a', 'k'], ['a', 't', 't', 'a']], [['c', 'o', 'm', 'e'], ['N', 'E', 'G'], ['P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Antecedent: Densya-wa zikandoorini ki-ta 'The train came on time'."
    judgment := .acceptable
    alternatives := []
    readings := [("null adjunct", .acceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "absent"), ("subjectNull", "no"), ("available", "yes")] }

def ex41b : Datum :=
  { id := "funakoshi2016_ex41b"
    source := ⟨"funakoshi-2016", "(41b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Hanako-wa Δ syukudai-o das-anak-atta."
    glossedTokens := [("Hanako-wa", "Hanako-TOP"), ("syukudai-o", "homework-ACC"), ("das-anak-atta.", "submit-NEG-PAST")]
    glossedWords := [⟨[['H', 'a', 'n', 'a', 'k', 'o'], ['w', 'a']], [['H', 'a', 'n', 'a', 'k', 'o'], ['T', 'O', 'P']]⟩, ⟨[['s', 'y', 'u', 'k', 'u', 'd', 'a', 'i'], ['o']], [['h', 'o', 'm', 'e', 'w', 'o', 'r', 'k'], ['A', 'C', 'C']]⟩, ⟨[['d', 'a', 's'], ['a', 'n', 'a', 'k'], ['a', 't', 't', 'a']], [['s', 'u', 'b', 'm', 'i', 't'], ['N', 'E', 'G'], ['P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Antecedent: Taroo-wa {zikandoorini / okurete} syukudai-o dasi-ta 'Taroo submitted the homework on time / late'."
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def ex43b : Datum :=
  { id := "funakoshi2016_ex43b"
    source := ⟨"funakoshi-2016", "(43b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Demo Δ madogarasu-o huk-anak-atta."
    glossedTokens := [("Demo", "but"), ("madogarasu-o", "window-ACC"), ("huk-anak-atta.", "wipe-NEG-PAST")]
    glossedWords := [⟨[['D', 'e', 'm', 'o']], [['b', 'u', 't']]⟩, ⟨[['m', 'a', 'd', 'o', 'g', 'a', 'r', 'a', 's', 'u'], ['o']], [['w', 'i', 'n', 'd', 'o', 'w'], ['A', 'C', 'C']]⟩, ⟨[['h', 'u', 'k'], ['a', 'n', 'a', 'k'], ['a', 't', 't', 'a']], [['w', 'i', 'p', 'e'], ['N', 'E', 'G'], ['P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Taroo washed his car, meaning to wipe the windows after the body, but felt tired. Antecedent: Taroo-wa teineini syatai-o arat-ta 'Taroo washed the body of the car carefully'."
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "yes"), ("available", "no")] }

def ex44b : Datum :=
  { id := "funakoshi2016_ex44b"
    source := ⟨"funakoshi-2016", "(44b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Demo Δ gakusei-no ronbun-o naos-ana-i."
    glossedTokens := [("Demo", "but"), ("gakusei-no", "student-GEN"), ("ronbun-o", "paper-ACC"), ("naos-ana-i.", "revise-NEG-PRES")]
    glossedWords := [⟨[['D', 'e', 'm', 'o']], [['b', 'u', 't']]⟩, ⟨[['g', 'a', 'k', 'u', 's', 'e', 'i'], ['n', 'o']], [['s', 't', 'u', 'd', 'e', 'n', 't'], ['G', 'E', 'N']]⟩, ⟨[['r', 'o', 'n', 'b', 'u', 'n'], ['o']], [['p', 'a', 'p', 'e', 'r'], ['A', 'C', 'C']]⟩, ⟨[['n', 'a', 'o', 's'], ['a', 'n', 'a'], ['i']], [['r', 'e', 'v', 'i', 's', 'e'], ['N', 'E', 'G'], ['P', 'R', 'E', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Taroo writes his own papers and looks at his students' papers every day. Antecedent: Taroo-wa Word-de zibun-no ronbun-o kak-u 'Taroo writes his own papers with Word'."
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "yes"), ("available", "no")] }

def ex51b : Datum :=
  { id := "funakoshi2016_ex51b"
    source := ⟨"funakoshi-2016", "(51b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Kuruma-o Hanako-wa Δ araw-anak-atta"
    glossedTokens := [("Kuruma-o", "car-ACC"), ("Hanako-wa", "Hanako-TOP"), ("araw-anak-atta", "wash-NEG-PAST")]
    glossedWords := [⟨[['K', 'u', 'r', 'u', 'm', 'a'], ['o']], [['c', 'a', 'r'], ['A', 'C', 'C']]⟩, ⟨[['H', 'a', 'n', 'a', 'k', 'o'], ['w', 'a']], [['H', 'a', 'n', 'a', 'k', 'o'], ['T', 'O', 'P']]⟩, ⟨[['a', 'r', 'a', 'w'], ['a', 'n', 'a', 'k'], ['a', 't', 't', 'a']], [['w', 'a', 's', 'h'], ['N', 'E', 'G'], ['P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Taroo and Hanako washed their parents' cars to get an allowance. But Taroo was thorough in his work while Hanako was not. Antecedent: Kuruma-o Taroo-wa teineini arat-ta 'Taroo washed the car carefully'."
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def ex52b : Datum :=
  { id := "funakoshi2016_ex52b"
    source := ⟨"funakoshi-2016", "(52b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Kuruma-o Hanako-mo Δ araw-anak-atta"
    glossedTokens := [("Kuruma-o", "car-ACC"), ("Hanako-mo", "Hanako-also"), ("araw-anak-atta", "wash-NEG-PAST")]
    glossedWords := [⟨[['K', 'u', 'r', 'u', 'm', 'a'], ['o']], [['c', 'a', 'r'], ['A', 'C', 'C']]⟩, ⟨[['H', 'a', 'n', 'a', 'k', 'o'], ['m', 'o']], [['H', 'a', 'n', 'a', 'k', 'o'], ['a', 'l', 's', 'o']]⟩, ⟨[['a', 'r', 'a', 'w'], ['a', 'n', 'a', 'k'], ['a', 't', 't', 'a']], [['w', 'a', 's', 'h'], ['N', 'E', 'G'], ['P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Both did careless work. Antecedent: Kuruma-o Taroo-wa teineini araw-anak-atta."
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def ex53b : Datum :=
  { id := "funakoshi2016_ex53b"
    source := ⟨"funakoshi-2016", "(53b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Demo madogarasu-o Hanako-wa Δ huk-anak-atta."
    glossedTokens := [("Demo", "but"), ("madogarasu-o", "window-ACC"), ("Hanako-wa", "Hanako-TOP"), ("huk-anak-atta.", "wipe-NEG-PAST")]
    glossedWords := [⟨[['D', 'e', 'm', 'o']], [['b', 'u', 't']]⟩, ⟨[['m', 'a', 'd', 'o', 'g', 'a', 'r', 'a', 's', 'u'], ['o']], [['w', 'i', 'n', 'd', 'o', 'w'], ['A', 'C', 'C']]⟩, ⟨[['H', 'a', 'n', 'a', 'k', 'o'], ['w', 'a']], [['H', 'a', 'n', 'a', 'k', 'o'], ['T', 'O', 'P']]⟩, ⟨[['h', 'u', 'k'], ['a', 'n', 'a', 'k'], ['a', 't', 't', 'a']], [['w', 'i', 'p', 'e'], ['N', 'E', 'G'], ['P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Antecedent: Syatai-o Taroo-wa teineini arat-ta 'Taroo washed the body of the car carefully'."
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def ex55b : Datum :=
  { id := "funakoshi2016_ex55b"
    source := ⟨"funakoshi-2016", "(55b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Iya, boku-wa Δ ATTI-NO kuruma-o araw-anak-attanda."
    glossedTokens := [("Iya,", "no"), ("boku-wa", "I-TOP"), ("ATTI-NO", "that-GEN"), ("kuruma-o", "car-ACC"), ("araw-anak-attanda.", "wash-NEG-PAST")]
    glossedWords := [⟨[['I', 'y', 'a']], [['n', 'o']]⟩, ⟨[['b', 'o', 'k', 'u'], ['w', 'a']], [['I'], ['T', 'O', 'P']]⟩, ⟨[['A', 'T', 'T', 'I'], ['N', 'O']], [['t', 'h', 'a', 't'], ['G', 'E', 'N']]⟩, ⟨[['k', 'u', 'r', 'u', 'm', 'a'], ['o']], [['c', 'a', 'r'], ['A', 'C', 'C']]⟩, ⟨[['a', 'r', 'a', 'w'], ['a', 'n', 'a', 'k'], ['a', 't', 't', 'a', 'n', 'd', 'a']], [['w', 'a', 's', 'h'], ['N', 'E', 'G'], ['P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Taroo ordered Ziroo to wash his two cars clean; Ziroo washed one sloppily and the other carefully. Taroo: Kimi-wa teineini kotti-no kuruma-o araw-anak-atta daro? 'You didn't wash this car carefully, did you?'"
    judgment := .acceptable
    alternatives := []
    readings := [("null adjunct", .acceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "focused"), ("subjectNull", "no"), ("available", "yes")] }

def ex55b2 : Datum :=
  { id := "funakoshi2016_ex55b2"
    source := ⟨"funakoshi-2016", "(55b')"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Iya, ATTI-NO kuruma-o boku-wa Δ araw-anak-attanda."
    glossedTokens := [("Iya,", "no"), ("ATTI-NO", "that-GEN"), ("kuruma-o", "car-ACC"), ("boku-wa", "I-TOP"), ("araw-anak-attanda.", "wash-NEG-PAST")]
    glossedWords := [⟨[['I', 'y', 'a']], [['n', 'o']]⟩, ⟨[['A', 'T', 'T', 'I'], ['N', 'O']], [['t', 'h', 'a', 't'], ['G', 'E', 'N']]⟩, ⟨[['k', 'u', 'r', 'u', 'm', 'a'], ['o']], [['c', 'a', 'r'], ['A', 'C', 'C']]⟩, ⟨[['b', 'o', 'k', 'u'], ['w', 'a']], [['I'], ['T', 'O', 'P']]⟩, ⟨[['a', 'r', 'a', 'w'], ['a', 'n', 'a', 'k'], ['a', 't', 't', 'a', 'n', 'd', 'a']], [['w', 'a', 's', 'h'], ['N', 'E', 'G'], ['P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Taroo ordered Ziroo to wash his two cars clean; Ziroo washed one sloppily and the other carefully. Taroo: Kimi-wa teineini kotti-no kuruma-o araw-anak-atta daro? 'You didn't wash this car carefully, did you?'"
    judgment := .acceptable
    alternatives := []
    readings := [("null adjunct", .acceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "focused"), ("subjectNull", "no"), ("available", "yes")] }

def ex56b : Datum :=
  { id := "funakoshi2016_ex56b"
    source := ⟨"funakoshi-2016", "(56b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Iya, boku-wa kono kuruma-WA araw-anak-attayo."
    glossedTokens := [("Iya,", "no"), ("boku-wa", "I-TOP"), ("kono", "this"), ("kuruma-WA", "car-CONT"), ("araw-anak-attayo.", "wash-NEG-PAST")]
    glossedWords := [⟨[['I', 'y', 'a']], [['n', 'o']]⟩, ⟨[['b', 'o', 'k', 'u'], ['w', 'a']], [['I'], ['T', 'O', 'P']]⟩, ⟨[['k', 'o', 'n', 'o']], [['t', 'h', 'i', 's']]⟩, ⟨[['k', 'u', 'r', 'u', 'm', 'a'], ['W', 'A']], [['c', 'a', 'r'], ['C', 'O', 'N', 'T']]⟩, ⟨[['a', 'r', 'a', 'w'], ['a', 'n', 'a', 'k'], ['a', 't', 't', 'a', 'y', 'o']], [['w', 'a', 's', 'h'], ['N', 'E', 'G'], ['P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Same scenario. Taroo: Kimi-wa teineini kono kuruma-o arat-ta no? 'Did you wash this car carefully?'"
    judgment := .acceptable
    alternatives := []
    readings := [("null adjunct", .acceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "focused"), ("subjectNull", "no"), ("available", "yes")] }

def ex56b2 : Datum :=
  { id := "funakoshi2016_ex56b2"
    source := ⟨"funakoshi-2016", "(56b')"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Iya, kono kuruma-WA boku-wa araw-anak-attayo."
    glossedTokens := [("Iya,", "no"), ("kono", "this"), ("kuruma-WA", "car-CONT"), ("boku-wa", "I-TOP"), ("araw-anak-attayo.", "wash-NEG-PAST")]
    glossedWords := [⟨[['I', 'y', 'a']], [['n', 'o']]⟩, ⟨[['k', 'o', 'n', 'o']], [['t', 'h', 'i', 's']]⟩, ⟨[['k', 'u', 'r', 'u', 'm', 'a'], ['W', 'A']], [['c', 'a', 'r'], ['C', 'O', 'N', 'T']]⟩, ⟨[['b', 'o', 'k', 'u'], ['w', 'a']], [['I'], ['T', 'O', 'P']]⟩, ⟨[['a', 'r', 'a', 'w'], ['a', 'n', 'a', 'k'], ['a', 't', 't', 'a', 'y', 'o']], [['w', 'a', 's', 'h'], ['N', 'E', 'G'], ['P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Same scenario. Taroo: Kimi-wa teineini kono kuruma-o arat-ta no?"
    judgment := .acceptable
    alternatives := []
    readings := [("null adjunct", .acceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "focused"), ("subjectNull", "no"), ("available", "yes")] }

def ex57b : Datum :=
  { id := "funakoshi2016_ex57b"
    source := ⟨"funakoshi-2016", "(57b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Un, boku-wa Δ kotti-no kuruma-o araw-anak-attayo."
    glossedTokens := [("Un,", "yes"), ("boku-wa", "I-TOP"), ("kotti-no", "this-GEN"), ("kuruma-o", "car-ACC"), ("araw-anak-attayo.", "wash-NEG-PAST")]
    glossedWords := [⟨[['U', 'n']], [['y', 'e', 's']]⟩, ⟨[['b', 'o', 'k', 'u'], ['w', 'a']], [['I'], ['T', 'O', 'P']]⟩, ⟨[['k', 'o', 't', 't', 'i'], ['n', 'o']], [['t', 'h', 'i', 's'], ['G', 'E', 'N']]⟩, ⟨[['k', 'u', 'r', 'u', 'm', 'a'], ['o']], [['c', 'a', 'r'], ['A', 'C', 'C']]⟩, ⟨[['a', 'r', 'a', 'w'], ['a', 'n', 'a', 'k'], ['a', 't', 't', 'a', 'y', 'o']], [['w', 'a', 's', 'h'], ['N', 'E', 'G'], ['P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Taroo ordered Ziroo to wash his two cars clean; Ziroo washed one sloppily and the other carefully. Taroo: Kimi-wa teineini kotti-no kuruma-o araw-anak-atta daro? 'You didn't wash this car carefully, did you?'"
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def ex57b2 : Datum :=
  { id := "funakoshi2016_ex57b2"
    source := ⟨"funakoshi-2016", "(57b')"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Un, kotti-no kuruma-o boku-wa Δ araw-anak-attayo."
    glossedTokens := [("Un,", "yes"), ("kotti-no", "this-GEN"), ("kuruma-o", "car-ACC"), ("boku-wa", "I-TOP"), ("araw-anak-attayo.", "wash-NEG-PAST")]
    glossedWords := [⟨[['U', 'n']], [['y', 'e', 's']]⟩, ⟨[['k', 'o', 't', 't', 'i'], ['n', 'o']], [['t', 'h', 'i', 's'], ['G', 'E', 'N']]⟩, ⟨[['k', 'u', 'r', 'u', 'm', 'a'], ['o']], [['c', 'a', 'r'], ['A', 'C', 'C']]⟩, ⟨[['b', 'o', 'k', 'u'], ['w', 'a']], [['I'], ['T', 'O', 'P']]⟩, ⟨[['a', 'r', 'a', 'w'], ['a', 'n', 'a', 'k'], ['a', 't', 't', 'a', 'y', 'o']], [['w', 'a', 's', 'h'], ['N', 'E', 'G'], ['P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Taroo ordered Ziroo to wash his two cars clean; Ziroo washed one sloppily and the other carefully. Taroo: Kimi-wa teineini kotti-no kuruma-o araw-anak-atta daro? 'You didn't wash this car carefully, did you?'"
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def ex58b : Datum :=
  { id := "funakoshi2016_ex58b"
    source := ⟨"funakoshi-2016", "(58b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Iya, boku-wa kono kuruma-o araw-anak-attayo."
    glossedTokens := [("Iya,", "no"), ("boku-wa", "I-TOP"), ("kono", "this"), ("kuruma-o", "car-ACC"), ("araw-anak-attayo.", "wash-NEG-PAST")]
    glossedWords := [⟨[['I', 'y', 'a']], [['n', 'o']]⟩, ⟨[['b', 'o', 'k', 'u'], ['w', 'a']], [['I'], ['T', 'O', 'P']]⟩, ⟨[['k', 'o', 'n', 'o']], [['t', 'h', 'i', 's']]⟩, ⟨[['k', 'u', 'r', 'u', 'm', 'a'], ['o']], [['c', 'a', 'r'], ['A', 'C', 'C']]⟩, ⟨[['a', 'r', 'a', 'w'], ['a', 'n', 'a', 'k'], ['a', 't', 't', 'a', 'y', 'o']], [['w', 'a', 's', 'h'], ['N', 'E', 'G'], ['P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Same scenario. Taroo: Kimi-wa teineini kono kuruma-o arat-ta no?"
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def ex58b2 : Datum :=
  { id := "funakoshi2016_ex58b2"
    source := ⟨"funakoshi-2016", "(58b')"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Iya, kono kuruma-o boku-wa araw-anak-attayo."
    glossedTokens := [("Iya,", "no"), ("kono", "this"), ("kuruma-o", "car-ACC"), ("boku-wa", "I-TOP"), ("araw-anak-attayo.", "wash-NEG-PAST")]
    glossedWords := [⟨[['I', 'y', 'a']], [['n', 'o']]⟩, ⟨[['k', 'o', 'n', 'o']], [['t', 'h', 'i', 's']]⟩, ⟨[['k', 'u', 'r', 'u', 'm', 'a'], ['o']], [['c', 'a', 'r'], ['A', 'C', 'C']]⟩, ⟨[['b', 'o', 'k', 'u'], ['w', 'a']], [['I'], ['T', 'O', 'P']]⟩, ⟨[['a', 'r', 'a', 'w'], ['a', 'n', 'a', 'k'], ['a', 't', 't', 'a', 'y', 'o']], [['w', 'a', 's', 'h'], ['N', 'E', 'G'], ['P', 'A', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Same scenario. Taroo: Kimi-wa teineini kono kuruma-o arat-ta no?"
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def all : List Datum := [ex15b, ex16, ex17b, ex18b, ex19b, ex20b, ex21b, ex22b, ex23b, ex24b, ex25b, ex26b, ex27b, ex32b, ex39b, ex41b, ex43b, ex44b, ex51b, ex52b, ex53b, ex55b, ex55b2, ex56b, ex56b2, ex57b, ex57b2, ex58b, ex58b2]

end Funakoshi2016.Examples
