module

public import Linglib.Data.Examples.Schema

/-!
# `HaslingerEtAl2025` — typed example data

Auto-generated from `Linglib/Data/Examples/HaslingerEtAl2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HaslingerEtAl2025.Examples`.
-/

@[expose] public section

namespace HaslingerEtAl2025.Examples

def ex1 : Datum :=
  { id := "haslingeretal2025_ex1"
    source := ⟨"haslinger-etal-2025", "(1)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Jeder Hund hat gerade insgesamt drei Würste gegessen."
    glossedTokens := [("Jeder", "each"), ("Hund", "dog"), ("hat", "AUX"), ("gerade", "just"), ("insgesamt", "in.total"), ("drei", "three"), ("Würste", "sausages"), ("gegessen.", "eaten")]
    context := "Three dogs: Abe, Bert, Carl. (3a) Abe ate three sausages, Bert ate three sausages, Carl ate three sausages. (3b) Abe ate one sausage, Bert ate one sausage, Carl ate one sausage. (3c) Abe ate three sausages, Bert ate three sausages, Carl didn't eat any sausages."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("item", "jederDP"), ("trueIn3a", "yes"), ("trueIn3b", "no"), ("trueIn3c", "no")] }

def ex2 : Datum :=
  { id := "haslingeretal2025_ex2"
    source := ⟨"haslinger-etal-2025", "(2)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Hunde haben gerade jeder insgesamt drei Würste gegessen."
    glossedTokens := [("Die", "the"), ("Hunde", "dogs"), ("haben", "AUX"), ("gerade", "just"), ("jeder", "each"), ("insgesamt", "in.total"), ("drei", "three"), ("Würste", "sausages"), ("gegessen.", "eaten")]
    context := "Three dogs: Abe, Bert, Carl. (3a) Abe ate three sausages, Bert ate three sausages, Carl ate three sausages. (3b) Abe ate one sausage, Bert ate one sausage, Carl ate one sausage. (3c) Abe ate three sausages, Bert ate three sausages, Carl didn't eat any sausages."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("item", "jederDistance"), ("trueIn3a", "yes"), ("trueIn3b", "no"), ("trueIn3c", "no")] }

def ex4a : Datum :=
  { id := "haslingeretal2025_ex4a"
    source := ⟨"haslinger-etal-2025", "(4a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Alle Hunde haben gerade insgesamt drei Würste gegessen."
    glossedTokens := [("Alle", "all"), ("Hunde", "dogs"), ("haben", "AUX"), ("gerade", "just"), ("insgesamt", "in.total"), ("drei", "three"), ("Würste", "sausages"), ("gegessen.", "eaten")]
    context := "Three dogs: Abe, Bert, Carl. (3a) Abe ate three sausages, Bert ate three sausages, Carl ate three sausages. (3b) Abe ate one sausage, Bert ate one sausage, Carl ate one sausage. (3c) Abe ate three sausages, Bert ate three sausages, Carl didn't eat any sausages."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("item", "alle"), ("trueIn3a", "yes"), ("trueIn3b", "yes"), ("trueIn3c", "no")] }

def ex4b : Datum :=
  { id := "haslingeretal2025_ex4b"
    source := ⟨"haslinger-etal-2025", "(4b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Drei Hunde haben gerade insgesamt drei Würste gegessen."
    glossedTokens := [("Drei", "three"), ("Hunde", "dogs"), ("haben", "AUX"), ("gerade", "just"), ("insgesamt", "in.total"), ("drei", "three"), ("Würste", "sausages"), ("gegessen.", "eaten")]
    context := "Three dogs: Abe, Bert, Carl. (3a) Abe ate three sausages, Bert ate three sausages, Carl ate three sausages. (3b) Abe ate one sausage, Bert ate one sausage, Carl ate one sausage. (3c) Abe ate three sausages, Bert ate three sausages, Carl didn't eat any sausages."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("item", "numeralIndefinite"), ("trueIn3a", "yes"), ("trueIn3b", "yes"), ("trueIn3c", "no")] }

def ex4c : Datum :=
  { id := "haslingeretal2025_ex4c"
    source := ⟨"haslinger-etal-2025", "(4c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Hunde haben gerade insgesamt drei Würste gegessen."
    glossedTokens := [("Die", "the"), ("Hunde", "dogs"), ("haben", "AUX"), ("gerade", "just"), ("insgesamt", "in.total"), ("drei", "three"), ("Würste", "sausages"), ("gegessen.", "eaten")]
    context := "Three dogs: Abe, Bert, Carl. (3a) Abe ate three sausages, Bert ate three sausages, Carl ate three sausages. (3b) Abe ate one sausage, Bert ate one sausage, Carl ate one sausage. (3c) Abe ate three sausages, Bert ate three sausages, Carl didn't eat any sausages."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("item", "definitePlural"), ("trueIn3a", "yes"), ("trueIn3b", "yes"), ("trueIn3c", "yes")] }

def ex22a : Datum :=
  { id := "haslingeretal2025_ex22a"
    source := ⟨"haslinger-etal-2025", "(22a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Hunde haben gerade jeweils drei Würste gegessen."
    glossedTokens := [("Die", "the"), ("Hunde", "dogs"), ("haben", "AUX"), ("gerade", "just"), ("jeweils", "each"), ("drei", "three"), ("Würste", "sausages"), ("gegessen.", "eaten")]
    context := "Three dogs: Abe, Bert, Carl. (3a) Abe ate three sausages, Bert ate three sausages, Carl ate three sausages. (3b) Abe ate one sausage, Bert ate one sausage, Carl ate one sausage. (3c) Abe ate three sausages, Bert ate three sausages, Carl didn't eat any sausages."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("item", "jeweils"), ("trueIn3a", "yes"), ("trueIn3b", "no"), ("trueIn3c", "no")] }

def ex22b : Datum :=
  { id := "haslingeretal2025_ex22b"
    source := ⟨"haslinger-etal-2025", "(22b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Jeder Hund hat gerade drei Würste gegessen."
    glossedTokens := [("Jeder", "each"), ("Hund", "dog"), ("hat", "AUX"), ("gerade", "just"), ("drei", "three"), ("Würste", "sausages"), ("gegessen.", "eaten")]
    context := "Three dogs: Abe, Bert, Carl. (3a) Abe ate three sausages, Bert ate three sausages, Carl ate three sausages. (3b) Abe ate one sausage, Bert ate one sausage, Carl ate one sausage. (3c) Abe ate three sausages, Bert ate three sausages, Carl didn't eat any sausages."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("item", "jederDP"), ("trueIn3a", "yes"), ("trueIn3b", "no"), ("trueIn3c", "no")] }

def ex22c : Datum :=
  { id := "haslingeretal2025_ex22c"
    source := ⟨"haslinger-etal-2025", "(22c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Hunde haben gerade jeder drei Würste gegessen."
    glossedTokens := [("Die", "the"), ("Hunde", "dogs"), ("haben", "AUX"), ("gerade", "just"), ("jeder", "each"), ("drei", "three"), ("Würste", "sausages"), ("gegessen.", "eaten")]
    context := "Three dogs: Abe, Bert, Carl. (3a) Abe ate three sausages, Bert ate three sausages, Carl ate three sausages. (3b) Abe ate one sausage, Bert ate one sausage, Carl ate one sausage. (3c) Abe ate three sausages, Bert ate three sausages, Carl didn't eat any sausages."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("item", "jederDistance"), ("trueIn3a", "yes"), ("trueIn3b", "no"), ("trueIn3c", "no")] }

def ex23b : Datum :=
  { id := "haslingeretal2025_ex23b"
    source := ⟨"haslinger-etal-2025", "(23b)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1295"
    primaryText := "In den Boxen sind jeweils zwei Magnete!"
    glossedTokens := [("In", "in"), ("den", "the"), ("Boxen", "boxes"), ("sind", "are"), ("jeweils", "each"), ("zwei", "two"), ("Magnete!", "magnets")]
    context := "Anna distributed 9 strong magnets, which should not be stored together, in 5 boxes. Four boxes contain two magnets, the fifth contains one. On the way home, Anna's co-driver reads the instructions to her. They say: ‘Each magnet absolutely needs to be stored separately, even just two magnets in the same box can trigger a horrible explosion.’ Anna exclaims: Oh no, we have to turn around ..."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("item", "jeweils"), ("scenario", "nonMaximal"), ("questionnaire", "yes")] }

def ex23c : Datum :=
  { id := "haslingeretal2025_ex23c"
    source := ⟨"haslinger-etal-2025", "(23c)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1295"
    primaryText := "In jeder Box sind zwei Magnete!"
    glossedTokens := [("In", "in"), ("jeder", "every"), ("Box", "box"), ("sind", "are"), ("zwei", "two"), ("Magnete!", "magnets")]
    context := "Anna distributed 9 strong magnets, which should not be stored together, in 5 boxes. Four boxes contain two magnets, the fifth contains one. On the way home, Anna's co-driver reads the instructions to her. They say: ‘Each magnet absolutely needs to be stored separately, even just two magnets in the same box can trigger a horrible explosion.’ Anna exclaims: Oh no, we have to turn around ..."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("item", "jederDP"), ("scenario", "nonMaximal"), ("questionnaire", "yes")] }

def ex24b : Datum :=
  { id := "haslingeretal2025_ex24b"
    source := ⟨"haslinger-etal-2025", "(24b)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1295"
    primaryText := "Die Freiwilligen haben jeweils zwei Hunde an der Leine!"
    glossedTokens := [("Die", "the"), ("Freiwilligen", "volunteers"), ("haben", "have"), ("jeweils", "each"), ("zwei", "two"), ("Hunde", "dogs"), ("an", "on"), ("der", "the"), ("Leine!", "leash")]
    context := "At the animal shelter, there is a section for attack dogs with 9 dogs. Today, 5 volunteers showed up to walk the dogs. Billie gives the first four volunteers two dogs each; the fifth gets just one dog. Afterwards, Billie learns that one should under no circumstances let someone walk more than one of the dogs, because the dogs will have terrible fights. Billie: Good heavens ..."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("item", "jeweils"), ("scenario", "nonMaximal"), ("questionnaire", "yes")] }

def ex24c : Datum :=
  { id := "haslingeretal2025_ex24c"
    source := ⟨"haslinger-etal-2025", "(24c)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1295"
    primaryText := "Die Freiwilligen haben jeder zwei Hunde an der Leine!"
    glossedTokens := [("Die", "the"), ("Freiwilligen", "volunteers"), ("haben", "have"), ("jeder", "every"), ("zwei", "two"), ("Hunde", "dogs"), ("an", "on"), ("der", "the"), ("Leine!", "leash")]
    context := "At the animal shelter, there is a section for attack dogs with 9 dogs. Today, 5 volunteers showed up to walk the dogs. Billie gives the first four volunteers two dogs each; the fifth gets just one dog. Afterwards, Billie learns that one should under no circumstances let someone walk more than one of the dogs, because the dogs will have terrible fights. Billie: Good heavens ..."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("item", "jederDistance"), ("scenario", "nonMaximal"), ("questionnaire", "yes")] }

def ex24d : Datum :=
  { id := "haslingeretal2025_ex24d"
    source := ⟨"haslinger-etal-2025", "(24d)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1295"
    primaryText := "Jeder Freiwillige hat zwei Hunde an der Leine!"
    glossedTokens := [("Jeder", "every"), ("Freiwillige", "volunteer"), ("hat", "has"), ("zwei", "two"), ("Hunde", "dogs"), ("an", "on"), ("der", "the"), ("Leine!", "leash")]
    context := "At the animal shelter, there is a section for attack dogs with 9 dogs. Today, 5 volunteers showed up to walk the dogs. Billie gives the first four volunteers two dogs each; the fifth gets just one dog. Afterwards, Billie learns that one should under no circumstances let someone walk more than one of the dogs, because the dogs will have terrible fights. Billie: Good heavens ..."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("item", "jederDP"), ("scenario", "nonMaximal"), ("questionnaire", "yes")] }

def ex26 : Datum :=
  { id := "haslingeretal2025_ex26"
    source := ⟨"haslinger-etal-2025", "(26)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Fünf Freiwillige haben (jeweils) zwei Hunde an der Leine!"
    glossedTokens := [("Fünf", "five"), ("Freiwillige", "volunteers"), ("haben", "have"), ("(jeweils)", "(each)"), ("zwei", "two"), ("Hunde", "dogs"), ("an", "on"), ("der", "the"), ("Leine!", "leash")]
    context := "At the animal shelter, there is a section for attack dogs with 9 dogs. Today, 5 volunteers showed up to walk the dogs. Billie gives the first four volunteers two dogs each; the fifth gets just one dog. Afterwards, Billie learns that one should under no circumstances let someone walk more than one of the dogs, because the dogs will have terrible fights. Billie: Good heavens ..."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("item", "numeralIndefinite"), ("scenario", "nonMaximal")] }

def all : List Datum := [ex1, ex2, ex4a, ex4b, ex4c, ex22a, ex22b, ex22c, ex23b, ex23c, ex24b, ex24c, ex24d, ex26]

end HaslingerEtAl2025.Examples
