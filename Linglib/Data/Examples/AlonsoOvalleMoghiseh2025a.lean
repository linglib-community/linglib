module

public import Linglib.Data.Examples.Schema

/-!
# `AlonsoOvalleMoghiseh2025a` — typed example data

Auto-generated from `Linglib/Data/Examples/AlonsoOvalleMoghiseh2025a.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AlonsoOvalleMoghiseh2025a.Examples`.
-/

@[expose] public section

namespace AlonsoOvalleMoghiseh2025a.Examples

def ex_1 : Datum :=
  { id := "alonsoovallemoghiseh2025a_1"
    source := ⟨"aloni-port-2015", "p. 121"⟩
    reportedIn := some ⟨"alonso-ovalle-moghiseh-2025a", "(1)"⟩
    language := "stan1295"
    primaryText := "Niemand hat irgendeine Frage beantwortet."
    glossedTokens := [("Niemand", "nobody"), ("hat", "has"), ("irgendeine", "irgendeine"), ("Frage", "question"), ("beantwortet", "answered")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "irgendein"), ("environment", "downward entailing")] }

def ex_3b : Datum :=
  { id := "alonsoovallemoghiseh2025a_3b"
    source := ⟨"kratzer-shimoyama-2002", "p. 11"⟩
    reportedIn := some ⟨"alonso-ovalle-moghiseh-2025a", "(3b)"⟩
    language := "stan1295"
    primaryText := "Mary muss irgendeinen Arzt heiraten."
    glossedTokens := [("Mary", "Mary"), ("muss", "has-to"), ("irgendeinen", "irgendein"), ("Arzt", "doctor"), ("heiraten", "marry")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "irgendein"), ("modal", "deontic necessity"), ("inference", "free choice")] }

def ex_4 : Datum :=
  { id := "alonsoovallemoghiseh2025a_4"
    source := ⟨"falaus-2014", "p. 122"⟩
    reportedIn := some ⟨"alonso-ovalle-moghiseh-2025a", "(4)"⟩
    language := "roma1327"
    primaryText := "Monica s-a întâlnit cu vreun prieten."
    glossedTokens := [("Monica", "Monica"), ("s-a", "refl-have.3sg"), ("întâlnit", "met"), ("cu", "with"), ("vreun", "vreun"), ("prieten", "friend.masc")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("item", "vreun"), ("environment", "unembedded"), ("modalInsertion", "no"), ("partialExhaustification", "no")] }

def ex_5 : Datum :=
  { id := "alonsoovallemoghiseh2025a_5"
    source := ⟨"alonso-ovalle-menendez-benito-2015b", "p. 2"⟩
    reportedIn := some ⟨"alonso-ovalle-moghiseh-2025a", "(5)"⟩
    language := "stan1288"
    primaryText := "María se casó con algún médico."
    glossedTokens := [("María", "María"), ("se", "se"), ("casó", "married"), ("con", "with"), ("algún", "algún"), ("médico", "doctor")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "algún"), ("environment", "unembedded"), ("inference", "speaker ignorance")] }

def ex_6 : Datum :=
  { id := "alonsoovallemoghiseh2025a_6"
    source := ⟨"alonso-ovalle-menendez-benito-2015b", "p. 2"⟩
    reportedIn := some ⟨"alonso-ovalle-moghiseh-2025a", "(6)"⟩
    language := "stan1288"
    primaryText := "María se casó con algún médico, en concreto con el Dr. Smith."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "algún"), ("environment", "unembedded"), ("continuation", "namely")] }

def ex_7 : Datum :=
  { id := "alonsoovallemoghiseh2025a_7"
    source := ⟨"alonso-ovalle-menendez-benito-2018", "p. 2"⟩
    reportedIn := some ⟨"alonso-ovalle-moghiseh-2025a", "(7)"⟩
    language := "stan1288"
    primaryText := "Juan compró un libro cualquiera."
    glossedTokens := [("Juan", "Juan"), ("compró", "bought"), ("un", "un"), ("libro", "book"), ("cualquiera", "cualquiera")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "un NP cualquiera"), ("environment", "unembedded"), ("inference", "agent indifference")] }

def ex_8 : Datum :=
  { id := "alonsoovallemoghiseh2025a_8"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(8)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Ye ketab-i xarid-am."
    glossedTokens := [("Ye", "one"), ("ketab-i", "book-ind"), ("xarid-am", "bought-1sg")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "yek-i"), ("environment", "unembedded")] }

def ex_9 : Datum :=
  { id := "alonsoovallemoghiseh2025a_9"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(9)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Forood dirooz ye ketab-i xarid be esm-e Iliad."
    glossedTokens := [("Forood", "Forood"), ("dirooz", "yesterday"), ("ye", "one"), ("ketab-i", "book-ind"), ("xarid", "bought-3sg"), ("be", "to"), ("esm-e", "name-ez"), ("Iliad", "Iliad")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "yek-i"), ("environment", "unembedded"), ("continuation", "namely")] }

def ex_10a : Datum :=
  { id := "alonsoovallemoghiseh2025a_10a"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(10a)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Forood dirooz ye ketab-i xarid: ye roman va ye ketab-e sher."
    glossedTokens := [("Forood", "Forood"), ("dirooz", "yesterday"), ("ye", "one"), ("ketab-i", "book-ind"), ("xarid", "bought-3sg"), ("ye", "one"), ("roman", "novel"), ("va", "and"), ("ye", "one"), ("ketab-e", "book-ez"), ("sher", "poetry")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "yek-i"), ("environment", "unembedded"), ("inference", "uniqueness")] }

def ex_10b : Datum :=
  { id := "alonsoovallemoghiseh2025a_10b"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(10b)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Forood compró algún libro ayer: una novela y un libro de poesía."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "algún"), ("environment", "unembedded")] }

def ex_11 : Datum :=
  { id := "alonsoovallemoghiseh2025a_11"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(11)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Ye ketab xarid-am."
    glossedTokens := [("Ye", "one"), ("ketab", "book"), ("xarid-am", "bought-1sg")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "yek"), ("environment", "unembedded")] }

def ex_12a : Datum :=
  { id := "alonsoovallemoghiseh2025a_12a"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(12a)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Do ta ketab-i xarid-am."
    glossedTokens := [("Do", "two"), ("ta", "cl"), ("ketab-i", "book-ind"), ("xarid-am", "bought-1sg")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "numeral -i"), ("environment", "unembedded")] }

def ex_12b : Datum :=
  { id := "alonsoovallemoghiseh2025a_12b"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(12b)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Do ta ketab xarid-am."
    glossedTokens := [("Do", "two"), ("ta", "cl"), ("ketab", "book"), ("xarid-am", "bought-1sg")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "numeral"), ("environment", "unembedded")] }

def ex_13 : Datum :=
  { id := "alonsoovallemoghiseh2025a_13"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(13)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Forood ye ketab-a-i xarid."
    glossedTokens := [("Forood", "Forood"), ("ye", "one"), ("ketab-a-i", "book-pl-ind"), ("xarid", "bought-3sg")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "yek-i plural"), ("environment", "unembedded")] }

def ex_14 : Datum :=
  { id := "alonsoovallemoghiseh2025a_14"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(14)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Ketab-i xarid-am."
    glossedTokens := [("Ketab-i", "book-ind"), ("xarid-am", "bought-1sg")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "bare -i"), ("environment", "unembedded")] }

def ex_15 : Datum :=
  { id := "alonsoovallemoghiseh2025a_15"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(15)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "shak dar-am Forood ye film-i dide bash-e."
    glossedTokens := [("shak", "doubt"), ("dar-am", "have-1sg"), ("Forood", "Forood"), ("ye", "one"), ("film-i", "film-ind"), ("dide", "seen"), ("bash-e", "be-3sg")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "yek-i"), ("environment", "downward entailing"), ("scope", "doubt > ∃")] }

def ex_16 : Datum :=
  { id := "alonsoovallemoghiseh2025a_16"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(16)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "age Forood ye ketab-i bexun-e, ye jaize migir-e."
    glossedTokens := [("age", "if"), ("Forood", "Forood"), ("ye", "one"), ("ketab-i", "book-ind"), ("bexun-e", "read-3sg"), ("ye", "one"), ("jaize", "gift"), ("migir-e", "take-3sg")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "yek-i"), ("environment", "downward entailing"), ("scope", "if > ∃")] }

def ex_17 : Datum :=
  { id := "alonsoovallemoghiseh2025a_17"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(17)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Forood ye ketab-i na-xarid."
    glossedTokens := [("Forood", "Forood"), ("ye", "one"), ("ketab-i", "book-ind"), ("na-xarid", "neg-bought-3sg")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("item", "yek-i"), ("environment", "sentential negation")] }

def ex_18 : Datum :=
  { id := "alonsoovallemoghiseh2025a_18"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(18)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "No he leído algún libro."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("item", "algún"), ("environment", "sentential negation")] }

def ex_19 : Datum :=
  { id := "alonsoovallemoghiseh2025a_19"
    source := ⟨"chierchia-2013", "p. 250"⟩
    reportedIn := some ⟨"alonso-ovalle-moghiseh-2025a", "(19)"⟩
    language := "stan1295"
    primaryText := "Ich habe nicht irgendein Buch gelesen."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("item", "irgendein"), ("environment", "sentential negation")] }

def ex_20a : Datum :=
  { id := "alonsoovallemoghiseh2025a_20a"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(20a)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Forood mitun-e ye ketab-i bexar-e."
    glossedTokens := [("Forood", "Forood"), ("mitun-e", "can-3sg"), ("ye", "one"), ("ketab-i", "book-ind"), ("bexar-e", "buy-3sg")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "yek-i"), ("modal", "deontic possibility"), ("inference", "free choice")] }

def ex_20b : Datum :=
  { id := "alonsoovallemoghiseh2025a_20b"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(20b)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Forood bayad ye ketab-i bexar-e."
    glossedTokens := [("Forood", "Forood"), ("bayad", "must"), ("ye", "one"), ("ketab-i", "book-ind"), ("bexar-e", "buy-3sg")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "yek-i"), ("modal", "deontic necessity"), ("inference", "free choice")] }

def ex_21a : Datum :=
  { id := "alonsoovallemoghiseh2025a_21a"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(21a)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Forood mitun-e ye ketab-i xaride bash-e."
    glossedTokens := [("Forood", "Forood"), ("mitun-e", "can-3sg"), ("ye", "ye"), ("ketab-i", "book-ind"), ("xaride", "bought"), ("bash-e", "be-3sg")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "yek-i"), ("modal", "epistemic possibility"), ("inference", "modal variation")] }

def ex_21b : Datum :=
  { id := "alonsoovallemoghiseh2025a_21b"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(21b)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Forood bayad ye ketab-i xaride bash-e."
    glossedTokens := [("Forood", "Forood"), ("bayad", "must"), ("ye", "one"), ("ketab-i", "book-ind"), ("xaride", "bought"), ("bash-e", "be-3sg")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "yek-i"), ("modal", "epistemic necessity"), ("inference", "modal variation")] }

def ex_23 : Datum :=
  { id := "alonsoovallemoghiseh2025a_23"
    source := ⟨"alonso-ovalle-menendez-benito-2015b", "p. 10"⟩
    reportedIn := some ⟨"alonso-ovalle-moghiseh-2025a", "(23)"⟩
    language := "stan1288"
    primaryText := "María tiene que casarse con algún médico."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "algún"), ("modal", "deontic necessity"), ("inference", "modal variation")] }

def ex_25 : Datum :=
  { id := "alonsoovallemoghiseh2025a_25"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(25)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Forood mitun-e ye ketab bexar-e."
    glossedTokens := [("Forood", "Forood"), ("mitun-e", "can-3sg"), ("ye", "one"), ("ketab", "book"), ("bexar-e", "buy-3sg")]
    context := "There are only five books (b1–b5). Forood is allowed to buy b1, b2, and b3, but not b4 or b5."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [("item", "yek"), ("modal", "deontic possibility"), ("scenario", "permitted24")] }

def ex_26 : Datum :=
  { id := "alonsoovallemoghiseh2025a_26"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(26)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Forood mitun-e ye ketab-i bexar-e."
    glossedTokens := [("Forood", "Forood"), ("mitun-e", "can-3sg"), ("ye", "one"), ("ketab-i", "book-ind"), ("bexar-e", "buy-3sg")]
    context := "There are only five books (b1–b5). Forood is allowed to buy b1, b2, and b3, but not b4 or b5."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("item", "yek-i"), ("modal", "deontic possibility"), ("scenario", "permitted24")] }

def ex_27 : Datum :=
  { id := "alonsoovallemoghiseh2025a_27"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(27)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "amma ne-mitun-e ketab-e b1 o bexar-e."
    glossedTokens := [("amma", "but"), ("ne-mitun-e", "neg-can-3sg"), ("ketab-e", "book-ez"), ("b1", "b1"), ("o", "acc"), ("bexar-e", "buy-3sg")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "continuation incompatible with free choice")] }

def ex_29 : Datum :=
  { id := "alonsoovallemoghiseh2025a_29"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(29)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Forood bayad ye ketab bexar-e."
    glossedTokens := [("Forood", "Forood"), ("bayad", "must"), ("ye", "one"), ("ketab", "book"), ("bexar-e", "buy-3sg")]
    context := "There are only five books (b1–b5). Forood is required to buy a book and is allowed to buy b1, b2, and b3, but not b4 or b5."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [("item", "yek"), ("modal", "deontic necessity"), ("scenario", "required28")] }

def ex_30 : Datum :=
  { id := "alonsoovallemoghiseh2025a_30"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(30)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Forood bayad ye ketab-i bexar-e."
    glossedTokens := [("Forood", "Forood"), ("bayad", "must"), ("ye", "one"), ("ketab-i", "book-ind"), ("bexar-e", "buy-3sg")]
    context := "There are only five books (b1–b5). Forood is required to buy a book and is allowed to buy b1, b2, and b3, but not b4 or b5."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("item", "yek-i"), ("modal", "deontic necessity"), ("scenario", "required28")] }

def ex_32 : Datum :=
  { id := "alonsoovallemoghiseh2025a_32"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(32)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Forood mitun-e ye ketab-i xaride bash-e."
    glossedTokens := [("Forood", "Forood"), ("mitun-e", "can-3sg"), ("ye", "ye"), ("ketab-i", "book-ind"), ("xaride", "bought"), ("bash-e", "be-3sg")]
    context := "There are only five books (b1–b5). The speaker is convinced that Forood hasn't bought b4 or b5, but for all he knows Forood could have bought any of the other books, or even none."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [("item", "yek-i"), ("modal", "epistemic possibility"), ("scenario", "known31")] }

def ex_33 : Datum :=
  { id := "alonsoovallemoghiseh2025a_33"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(33)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "amma ketab-e b1 o na-xarid-e."
    glossedTokens := [("amma", "but"), ("ketab-e", "book-ez"), ("b1", "b1"), ("o", "acc"), ("na-xarid-e", "neg-bought-3sg")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "continuation incompatible with free choice")] }

def ex_35 : Datum :=
  { id := "alonsoovallemoghiseh2025a_35"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(35)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Forood bayad ye ketab-i xaride bash-e."
    glossedTokens := [("Forood", "Forood"), ("bayad", "must"), ("ye", "one"), ("ketab-i", "book-ind"), ("xaride", "bought"), ("bash-e", "be-3sg")]
    context := "There are only five books (b1–b5). The speaker is convinced that Forood has bought a book, but knows that he hasn't bought b4 or b5."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [("item", "yek-i"), ("modal", "epistemic necessity"), ("scenario", "known34")] }

def ex_36 : Datum :=
  { id := "alonsoovallemoghiseh2025a_36"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(36)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Forood dirooz ye ketab-i xarid."
    glossedTokens := [("Forood", "Forood"), ("dirooz", "yesterday"), ("ye", "one"), ("ketab-i", "book-ind"), ("xarid", "bought-3sg")]
    context := "Forood wanted to buy The Iliad and did so. He wouldn't have bought any other book."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "yek-i"), ("environment", "unembedded"), ("modalInsertion", "no"), ("partialExhaustification", "yes")] }

def ex_40 : Datum :=
  { id := "alonsoovallemoghiseh2025a_40"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(40)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "A: Forood dirooz ye ketab-i xarid. B: Kodum o?"
    glossedTokens := [("Forood", "Forood"), ("dirooz", "yesterday"), ("ye", "one"), ("ketab-i", "book-ind"), ("xarid", "bought-3sg"), ("Kodum", "which"), ("o", "acc")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "yek-i"), ("environment", "unembedded"), ("continuation", "which-question")] }

def ex_41 : Datum :=
  { id := "alonsoovallemoghiseh2025a_41"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(41)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A: Forood compró algún libro ayer. B: ¿Cuál?"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "algún"), ("environment", "unembedded"), ("continuation", "which-question")] }

def ex_42 : Datum :=
  { id := "alonsoovallemoghiseh2025a_42"
    source := ⟨"aloni-port-2015", "p. 119"⟩
    reportedIn := some ⟨"alonso-ovalle-moghiseh-2025a", "(42)"⟩
    language := "stan1295"
    primaryText := "Irgendein Student hat angerufen. Rat mal wer?"
    glossedTokens := [("Irgendein", "some"), ("Student", "student"), ("hat", "has"), ("angerufen", "called"), ("Rat", "guess"), ("mal", "prt"), ("wer", "who")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "irgendein"), ("environment", "unembedded"), ("continuation", "guess who")] }

def ex_43 : Datum :=
  { id := "alonsoovallemoghiseh2025a_43"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(43)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Forood dirooz ye ketab-i xarid. Hads bezan chi?"
    glossedTokens := [("Forood", "Forood"), ("dirooz", "yesterday"), ("ye", "one"), ("ketab-i", "book-ind"), ("xarid", "bought-3sg"), ("Hads", "guess"), ("bezan", "hit"), ("chi", "what")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "yek-i"), ("environment", "unembedded"), ("continuation", "guess what")] }

def ex_44 : Datum :=
  { id := "alonsoovallemoghiseh2025a_44"
    source := ⟨"chierchia-2013", "p. 251"⟩
    reportedIn := some ⟨"alonso-ovalle-moghiseh-2025a", "(44)"⟩
    language := "stan1295"
    primaryText := "John hat geschummelt. Deshalb ist irgendein Student aus deiner Klasse ein Betrueger."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "irgendein"), ("environment", "unembedded"), ("continuation", "previously mentioned witness")] }

def ex_45 : Datum :=
  { id := "alonsoovallemoghiseh2025a_45"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(45)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Forood ketab-e Iliad-o xarid. Bana-bar-in Forood ye ketab-i xarid-e."
    glossedTokens := [("Forood", "Forood"), ("ketab-e", "book-ez"), ("Iliad-o", "Iliad-acc"), ("xarid", "bought-3sg"), ("Bana-bar-in", "therefore"), ("Forood", "Forood"), ("ye", "ye"), ("ketab-i", "book-ind"), ("xarid-e", "bought-3sg")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "yek-i"), ("environment", "unembedded"), ("continuation", "previously mentioned witness")] }

def ex_47 : Datum :=
  { id := "alonsoovallemoghiseh2025a_47"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(47)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "A: Forood dirooz ye ketab-i xarid. B: Chand ta?"
    glossedTokens := [("Forood", "Forood"), ("dirooz", "yesterday"), ("ye", "one"), ("ketab-i", "book-ind"), ("xarid", "bought-3sg"), ("Chand", "how-many"), ("ta", "cl")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "yek-i"), ("environment", "unembedded"), ("continuation", "how-many question"), ("inference", "uniqueness")] }

def ex_48 : Datum :=
  { id := "alonsoovallemoghiseh2025a_48"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(48)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A: Ayer, Forood compró algún libro. B: ¿Cuántos?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "algún"), ("environment", "unembedded"), ("continuation", "how-many question")] }

def ex_49 : Datum :=
  { id := "alonsoovallemoghiseh2025a_49"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(49)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Age Forood ye ketab-i bexar-e, $10 mid-e, amma age do ta bexar-e, $15 mid-e."
    glossedTokens := [("Age", "if"), ("Forood", "Forood"), ("ye", "one"), ("ketab-i", "book-ind"), ("bexar-e", "buy-3sg"), ("$10", "$10"), ("mid-e", "give-3sg"), ("amma", "but"), ("age", "if"), ("do", "two"), ("ta", "cl"), ("bexar-e", "buy-3sg"), ("$15", "$15"), ("mid-e", "give-3sg")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "yek-i"), ("environment", "downward entailing"), ("inference", "uniqueness absent")] }

def ex_50 : Datum :=
  { id := "alonsoovallemoghiseh2025a_50"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(50)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Shak dar-am Forood bayad ye ketab-i bexar-e, bayad Oblomov ro bexar-e."
    glossedTokens := [("Shak", "doubt"), ("dar-am", "have-1sg"), ("Forood", "Forood"), ("bayad", "must"), ("ye", "one"), ("ketab-i", "book-ind"), ("bexar-e", "buy-3sg"), ("bayad", "must"), ("Oblomov", "Oblomov"), ("ro", "acc"), ("bexar-e", "buy-3sg")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "yek-i"), ("environment", "downward entailing"), ("inference", "free choice absent")] }

def ex_62 : Datum :=
  { id := "alonsoovallemoghiseh2025a_62"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(62)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "va inke mitun-e hadaksar se ta ketab bexar-e."
    glossedTokens := [("va", "and"), ("inke", "that"), ("mitun-e", "can-3sg"), ("hadaksar", "maximum"), ("se", "three"), ("ta", "cl"), ("ketab", "book"), ("bexar-e", "buy-3sg")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "continuation"), ("inference", "no anti-plurality under possibility")] }

def ex_73a : Datum :=
  { id := "alonsoovallemoghiseh2025a_73a"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(73a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Forood puede comprar algún libro."
    glossedTokens := [("Forood", "Forood"), ("puede", "can"), ("comprar", "buy-inf"), ("algún", "algún"), ("libro", "book")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "algún"), ("modal", "deontic possibility"), ("inference", "modal variation")] }

def ex_81a : Datum :=
  { id := "alonsoovallemoghiseh2025a_81a"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(81a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Maria hat irgendein Buch gekauft."
    glossedTokens := [("Maria", "Maria"), ("hat", "has"), ("irgendein", "irgendein"), ("Buch", "book"), ("gekauft", "bought")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "irgendein"), ("environment", "unembedded"), ("modalInsertion", "yes"), ("partialExhaustification", "no")] }

def ex_105a : Datum :=
  { id := "alonsoovallemoghiseh2025a_105a"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(105a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Forood tiene que comprar algún libro."
    glossedTokens := [("Forood", "Forood"), ("tiene", "has"), ("que", "that"), ("comprar", "buy"), ("algún", "algún"), ("libro", "book")]
    context := "There are only five books (b1–b5). Forood is required to buy a book, and any book is a permissible option. He is allowed to buy one or more than one book."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [("item", "algún"), ("modal", "deontic necessity"), ("scenario", "anyNumber104")] }

def ex_105b : Datum :=
  { id := "alonsoovallemoghiseh2025a_105b"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(105b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Forood muss irgendein Buch kaufen."
    glossedTokens := [("Forood", "Forood"), ("muss", "must"), ("irgendein", "irgendein"), ("Buch", "book"), ("kaufen", "buy")]
    context := "There are only five books (b1–b5). Forood is required to buy a book, and any book is a permissible option. He is allowed to buy one or more than one book."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [("item", "irgendein"), ("modal", "deontic necessity"), ("scenario", "anyNumber104")] }

def ex_106 : Datum :=
  { id := "alonsoovallemoghiseh2025a_106"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(106)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Forood bayad ye ketab-i bexar-e."
    glossedTokens := [("Forood", "Forood"), ("bayad", "must"), ("ye", "one"), ("ketab-i", "book-ind"), ("bexar-e", "buy-3sg")]
    context := "There are only five books (b1–b5). Forood is required to buy a book, and any book is a permissible option. He is allowed to buy one or more than one book."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("item", "yek-i"), ("modal", "deontic necessity"), ("scenario", "anyNumber104")] }

def ex_109 : Datum :=
  { id := "alonsoovallemoghiseh2025a_109"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(109)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Forood mitun-e ye ketab-i bexar-e."
    glossedTokens := [("Forood", "Forood"), ("mitun-e", "can-3sg"), ("ye", "one"), ("ketab-i", "book-ind"), ("bexar-e", "buy-3sg")]
    context := "There are only five books (b1–b5). Forood is required to buy two books, and any book is a permissible option."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("item", "yek-i"), ("modal", "deontic possibility"), ("scenario", "twoBooks108")] }

def ex_110 : Datum :=
  { id := "alonsoovallemoghiseh2025a_110"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(110)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "va inke ne-mitun-e bishtar az ye doone ketab bexar-e."
    glossedTokens := [("va", "and"), ("inke", "that"), ("ne-mitun-e", "neg-can-3sg"), ("bishtar", "more"), ("az", "from"), ("ye", "one"), ("doone", "cl"), ("ketab", "book"), ("bexar-e", "buy-3sg")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "continuation")] }

def ex_111 : Datum :=
  { id := "alonsoovallemoghiseh2025a_111"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(111)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "shak dar-am Forood bayad ye ketab-i bexar-e, bayad do ta bexar-e."
    glossedTokens := [("shak", "doubt"), ("dar-am", "have-1sg"), ("Forood", "Forood"), ("bayad", "must"), ("ye", "one"), ("ketab-i", "book-ind"), ("bexar-e", "buy-3sg"), ("bayad", "must"), ("do", "two"), ("ta", "cl"), ("bexar-e", "buy-3sg")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "yek-i"), ("environment", "downward entailing"), ("inference", "embedded uniqueness absent")] }

def ex_121 : Datum :=
  { id := "alonsoovallemoghiseh2025a_121"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(121)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Forood mitun-e ye ketab-i xaride bash-e, va inke ne-mitun-e daghighan ye doone xarid-e bash-e."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "yek-i"), ("modal", "epistemic possibility"), ("inference", "embedded uniqueness")] }

def ex_125 : Datum :=
  { id := "alonsoovallemoghiseh2025a_125"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(125)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Bayad ye ketab-i too jabe bash-e."
    glossedTokens := [("Bayad", "must"), ("ye", "one"), ("ketab-i", "book-ind"), ("too", "in"), ("jabe", "box"), ("bash-e", "be-3sg")]
    context := "There is a box on the desk. Forood doesn't know what the box contains."
    judgment := .acceptable
    alternatives := []
    readings := [("You see! There is one book", .acceptable), ("You see! There are three books", .unacceptable)]
    paperFeatures := [("item", "yek-i"), ("modal", "epistemic necessity"), ("inference", "embedded uniqueness")] }

def ex_128 : Datum :=
  { id := "alonsoovallemoghiseh2025a_128"
    source := ⟨"alonso-ovalle-moghiseh-2025a", "(128)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Forood bayad ye ketab-i xaride bash-e, va inke momkene ye doone ya do ta xaride bash-e."
    glossedTokens := [("Forood", "Forood"), ("bayad", "must"), ("ye", "one"), ("ketab-i", "book-ind"), ("xaride", "bought"), ("bash-e", "be-3sg"), ("va", "and"), ("inke", "that"), ("momkene", "possible"), ("ye", "one"), ("doone", "cl"), ("ya", "or"), ("do", "two"), ("ta", "cl"), ("xaride", "bought"), ("bash-e", "be-3sg")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "yek-i"), ("modal", "epistemic necessity"), ("inference", "apparent counterexample")] }

def all : List Datum := [ex_1, ex_3b, ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, ex_10a, ex_10b, ex_11, ex_12a, ex_12b, ex_13, ex_14, ex_15, ex_16, ex_17, ex_18, ex_19, ex_20a, ex_20b, ex_21a, ex_21b, ex_23, ex_25, ex_26, ex_27, ex_29, ex_30, ex_32, ex_33, ex_35, ex_36, ex_40, ex_41, ex_42, ex_43, ex_44, ex_45, ex_47, ex_48, ex_49, ex_50, ex_62, ex_73a, ex_81a, ex_105a, ex_105b, ex_106, ex_109, ex_110, ex_111, ex_121, ex_125, ex_128]

end AlonsoOvalleMoghiseh2025a.Examples
