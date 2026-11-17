module

public import Linglib.Data.Examples.Schema

/-!
# `Chierchia2006` — typed example data

Auto-generated from `Linglib/Data/Examples/Chierchia2006.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Chierchia2006.Examples`.
-/

@[expose] public section

namespace Chierchia2006.Examples

def ex2a : Datum :=
  { id := "chierchia2006_ex2a"
    source := ⟨"chierchia-2006", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is any student (in that building)."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("item", "npiFci"), ("environment", "episodic")] }

def ex2b : Datum :=
  { id := "chierchia2006_ex2b"
    source := ⟨"chierchia-2006", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There isn't any student (in that building)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "npiFci"), ("environment", "negation")] }

def ex3 : Datum :=
  { id := "chierchia2006_ex3"
    source := ⟨"chierchia-2006", "(3)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Ich werde irgendeinen Doktor heiraten."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("existential", .acceptable)]
    paperFeatures := [("item", "existentialNpiFci"), ("environment", "future")] }

def ex4 : Datum :=
  { id := "chierchia2006_ex4"
    source := ⟨"chierchia-2006", "(4)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Gestern hat irgendein Student für dich angerufen."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("existential", .acceptable)]
    paperFeatures := [("item", "existentialNpiFci"), ("environment", "episodic"), ("device", "covertModal")] }

def ex5 : Datum :=
  { id := "chierchia2006_ex5"
    source := ⟨"chierchia-2006", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yesterday Mary saw any student that wanted to see her."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("universal", .acceptable)]
    paperFeatures := [("item", "npiFci"), ("environment", "episodicSubtrigged")] }

def ex6 : Datum :=
  { id := "chierchia2006_ex6"
    source := ⟨"chierchia-2006", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "To continue, push any key."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("existential", .acceptable)]
    paperFeatures := [("item", "npiFci"), ("environment", "imperative")] }

def ex8a : Datum :=
  { id := "chierchia2006_ex8a"
    source := ⟨"chierchia-2006", "(8a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Sono uscito in strada e mi sono messo a bussare come un matto ad una porta qualsiasi con i battenti in legno."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := [("existential", .acceptable)]
    paperFeatures := [("item", "existentialPureFci"), ("environment", "episodic"), ("device", "covertModal")] }

def ex8b : Datum :=
  { id := "chierchia2006_ex8b"
    source := ⟨"chierchia-2006", "(8b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Sono uscito in strada e mi son messo a bussare come un matto a qualsiasi porta con i battenti in legno."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("universal", .acceptable)]
    paperFeatures := [("item", "pureFci"), ("environment", "episodicSubtrigged")] }

def ex10a : Datum :=
  { id := "chierchia2006_ex10a"
    source := ⟨"chierchia-2006", "(10a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Domani interrogherò qualsiasi studente che mi capiterà a tiro."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("universal", .acceptable), ("existential", .acceptable)]
    paperFeatures := [("item", "pureFci"), ("environment", "future")] }

def ex10b : Datum :=
  { id := "chierchia2006_ex10b"
    source := ⟨"chierchia-2006", "(10b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Domani interrogherò uno studente qualsiasi."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("existential", .acceptable)]
    paperFeatures := [("item", "existentialPureFci"), ("environment", "future")] }

def ex10c : Datum :=
  { id := "chierchia2006_ex10c"
    source := ⟨"chierchia-2006", "(10c)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Prendi qualunque dolce."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("universal", .acceptable), ("existential", .acceptable)]
    paperFeatures := [("item", "pureFci"), ("environment", "imperative")] }

def ex10d : Datum :=
  { id := "chierchia2006_ex10d"
    source := ⟨"chierchia-2006", "(10d)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Prendi un dolce qualunque."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("existential", .acceptable)]
    paperFeatures := [("item", "existentialPureFci"), ("environment", "imperative")] }

def ex10e : Datum :=
  { id := "chierchia2006_ex10e"
    source := ⟨"chierchia-2006", "(10e)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Puoi prendere qualunque dolce."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("universal", .acceptable), ("existential", .marginal)]
    paperFeatures := [("item", "pureFci"), ("environment", "possibility")] }

def ex10f : Datum :=
  { id := "chierchia2006_ex10f"
    source := ⟨"chierchia-2006", "(10f)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Puoi prendere un dolce qualunque."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("existential", .acceptable)]
    paperFeatures := [("item", "existentialPureFci"), ("environment", "possibility")] }

def ex10g : Datum :=
  { id := "chierchia2006_ex10g"
    source := ⟨"chierchia-2006", "(10g)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Devi prendere qualunque dolce con il liquore."
    glossedTokens := []
    context := "If you go to Naples, you must go to Scaturchio."
    judgment := .acceptable
    contrasts := []
    readings := [("universal", .acceptable), ("existential", .marginal)]
    paperFeatures := [("item", "pureFci"), ("environment", "necessity")] }

def ex10h : Datum :=
  { id := "chierchia2006_ex10h"
    source := ⟨"chierchia-2006", "(10h)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Devi prendere un dolce qualunque con il liquore."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("existential", .acceptable)]
    paperFeatures := [("item", "existentialPureFci"), ("environment", "necessity")] }

def ex11a : Datum :=
  { id := "chierchia2006_ex11a"
    source := ⟨"chierchia-2006", "(11a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ieri ho parlato con un qualsiasi filosofo."
    glossedTokens := []
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    paperFeatures := [("item", "existentialPureFci"), ("environment", "episodic")] }

def ex11b : Datum :=
  { id := "chierchia2006_ex11b"
    source := ⟨"chierchia-2006", "(11b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ieri ho parlato con un qualsiasi filosofo che fosse interessato a parlarmi."
    glossedTokens := []
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    paperFeatures := [("item", "existentialPureFci"), ("environment", "episodicSubtrigged")] }

def ex11c : Datum :=
  { id := "chierchia2006_ex11c"
    source := ⟨"chierchia-2006", "(11c)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ieri ho parlato con qualsiasi filosofo."
    glossedTokens := []
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    paperFeatures := [("item", "pureFci"), ("environment", "episodic")] }

def ex11d : Datum :=
  { id := "chierchia2006_ex11d"
    source := ⟨"chierchia-2006", "(11d)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ieri ho parlato con qualsiasi filosofo che fosse interessato a parlarmi."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("universal", .acceptable)]
    paperFeatures := [("item", "pureFci"), ("environment", "episodicSubtrigged")] }

def ex12 : Datum :=
  { id := "chierchia2006_ex12"
    source := ⟨"chierchia-2006", "(12)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Non leggerò qualunque libro."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("rhetorical", .acceptable), ("negativePolarity", .unacceptable)]
    paperFeatures := [("item", "pureFci"), ("environment", "negation")] }

def ex13 : Datum :=
  { id := "chierchia2006_ex13"
    source := ⟨"chierchia-2006", "(13)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Non leggerò qualunque libro che mi consiglierà Gianni."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("rhetorical", .acceptable), ("negativePolarity", .acceptable)]
    paperFeatures := [("item", "pureFci"), ("environment", "negationSubtrigged")] }

def ex14 : Datum :=
  { id := "chierchia2006_ex14"
    source := ⟨"chierchia-2006", "(14)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Non leggerò un libro qualunque (che mi consiglierà Gianni)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("rhetorical", .acceptable), ("negativePolarity", .unacceptable)]
    paperFeatures := [("item", "existentialPureFci"), ("environment", "negation")] }

def ex47a : Datum :=
  { id := "chierchia2006_ex47a"
    source := ⟨"chierchia-2006", "(47a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I saw any boy."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("item", "npiFci"), ("environment", "episodic")] }

def ex49a : Datum :=
  { id := "chierchia2006_ex49a"
    source := ⟨"chierchia-2006", "(49a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I didn't see any boy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "npiFci"), ("environment", "negation")] }

def ex55a : Datum :=
  { id := "chierchia2006_ex55a"
    source := ⟨"chierchia-2006", "(55a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Any cat meows."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("universal", .acceptable)]
    paperFeatures := [("item", "npiFci"), ("environment", "generic")] }

def ex55b : Datum :=
  { id := "chierchia2006_ex55b"
    source := ⟨"chierchia-2006", "(55b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yesterday, any student that was around dropped by."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("universal", .acceptable)]
    paperFeatures := [("item", "npiFci"), ("environment", "episodicSubtrigged")] }

def ex64a : Datum :=
  { id := "chierchia2006_ex64a"
    source := ⟨"chierchia-2006", "(64a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I didn't see any student (that wanted to see me)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("rhetorical", .acceptable), ("negativePolarity", .acceptable)]
    paperFeatures := [("item", "npiFci"), ("environment", "negation")] }

def ex67a : Datum :=
  { id := "chierchia2006_ex67a"
    source := ⟨"chierchia-2006", "(67a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I saw any student."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("item", "npiFci"), ("environment", "episodic")] }

def ex68a : Datum :=
  { id := "chierchia2006_ex68a"
    source := ⟨"chierchia-2006", "(68a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I saw any student that wanted to see me."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("universal", .acceptable)]
    paperFeatures := [("item", "npiFci"), ("environment", "episodicSubtrigged")] }

def ex69a : Datum :=
  { id := "chierchia2006_ex69a"
    source := ⟨"chierchia-2006", "(69a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Non ho visto qualunque studente."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := [("rhetorical", .acceptable), ("negativePolarity", .unacceptable)]
    paperFeatures := [("item", "pureFci"), ("environment", "negation")] }

def ex71a : Datum :=
  { id := "chierchia2006_ex71a"
    source := ⟨"chierchia-2006", "(71a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Vedrò qualunque studente."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("universal", .acceptable)]
    paperFeatures := [("item", "pureFci"), ("environment", "future")] }

def ex77c : Datum :=
  { id := "chierchia2006_ex77c"
    source := ⟨"chierchia-2006", "(77c)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Avrei dovuto discuterne con un qualunque filosofo."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("existential", .acceptable)]
    paperFeatures := [("item", "existentialPureFci"), ("environment", "necessity")] }

def ex79a : Datum :=
  { id := "chierchia2006_ex79a"
    source := ⟨"chierchia-2006", "(79a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ho sposato un qualsiasi dottore."
    glossedTokens := []
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    paperFeatures := [("item", "existentialPureFci"), ("environment", "episodic")] }

def ex83a : Datum :=
  { id := "chierchia2006_ex83a"
    source := ⟨"chierchia-2006", "(83a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Posso sposare un qualsiasi dottore."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("existential", .acceptable)]
    paperFeatures := [("item", "existentialPureFci"), ("environment", "possibility")] }

def ex86a : Datum :=
  { id := "chierchia2006_ex86a"
    source := ⟨"chierchia-2006", "(86a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Un linguista ha sposato un qualunque dottore."
    glossedTokens := []
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    paperFeatures := [("item", "existentialPureFci"), ("environment", "episodic"), ("device", "intervention")] }

def ex88a : Datum :=
  { id := "chierchia2006_ex88a"
    source := ⟨"chierchia-2006", "(88a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Un qualsiasi cittadino può sollevare una qualsiasi questione."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("existential", .acceptable)]
    paperFeatures := [("item", "existentialPureFci"), ("environment", "possibility")] }

def ex90a : Datum :=
  { id := "chierchia2006_ex90a"
    source := ⟨"chierchia-2006", "(90a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Niemand musste irgendjemand einladen."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("negativePolarity", .acceptable), ("rhetorical", .acceptable)]
    paperFeatures := [("item", "existentialNpiFci"), ("environment", "negationNecessity")] }

def ex90b : Datum :=
  { id := "chierchia2006_ex90b"
    source := ⟨"chierchia-2006", "(90b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Nessuno è costretto ad invitare una persona qualsiasi."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("rhetorical", .acceptable), ("negativePolarity", .unacceptable)]
    paperFeatures := [("item", "existentialPureFci"), ("environment", "negationNecessity")] }

def ex92a : Datum :=
  { id := "chierchia2006_ex92a"
    source := ⟨"chierchia-2006", "(92a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Taste any doughnut."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("existential", .acceptable), ("universal", .marginal)]
    paperFeatures := [("item", "npiFci"), ("environment", "imperative")] }

def ex92b : Datum :=
  { id := "chierchia2006_ex92b"
    source := ⟨"chierchia-2006", "(92b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Assaggia qualsiasi doughnut."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("existential", .acceptable), ("universal", .marginal)]
    paperFeatures := [("item", "pureFci"), ("environment", "imperative")] }

def ex115 : Datum :=
  { id := "chierchia2006_ex115"
    source := ⟨"chierchia-2006", "(115)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Devo sposare un dottore qualunque."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("existential", .acceptable)]
    paperFeatures := [("item", "existentialPureFci"), ("environment", "necessity")] }

def fn42i : Datum :=
  { id := "chierchia2006_fn42i"
    source := ⟨"chierchia-2006", "fn. 42 (i)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Er könnte irgendwas tun."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("existential", .acceptable), ("universal", .unacceptable)]
    paperFeatures := [("item", "existentialNpiFci"), ("environment", "possibility")] }

def all : List Datum := [ex2a, ex2b, ex3, ex4, ex5, ex6, ex8a, ex8b, ex10a, ex10b, ex10c, ex10d, ex10e, ex10f, ex10g, ex10h, ex11a, ex11b, ex11c, ex11d, ex12, ex13, ex14, ex47a, ex49a, ex55a, ex55b, ex64a, ex67a, ex68a, ex69a, ex71a, ex77c, ex79a, ex83a, ex86a, ex88a, ex90a, ex90b, ex92a, ex92b, ex115, fn42i]

end Chierchia2006.Examples
