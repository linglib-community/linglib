module

public import Linglib.Data.Examples.Schema

/-!
# `AlonsoOvalleRouillard2023` — typed example data

Auto-generated from `Linglib/Data/Examples/AlonsoOvalleRouillard2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AlonsoOvalleRouillard2023.Examples`.
-/

@[expose] public section

namespace AlonsoOvalleRouillard2023.Examples

def ex_1 : Datum :=
  { id := "alonsoovallerouillard2023_1"
    source := ⟨"alonso-ovalle-rouillard-2023", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which student is leaving?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .acceptable), ("plural answer", .unacceptable)]
    paperFeatures := [("type", "SCI")] }

def ex_2 : Datum :=
  { id := "alonsoovallerouillard2023_2"
    source := ⟨"alonso-ovalle-rouillard-2023", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which students are leaving?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .unacceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "PCI")] }

def ex_3 : Datum :=
  { id := "alonsoovallerouillard2023_3"
    source := ⟨"alonso-ovalle-rouillard-2023", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who is leaving?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Who are leaving?", .ungrammatical)]
    readings := [("singular answer", .acceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "BI")] }

def ex_4 : Datum :=
  { id := "alonsoovallerouillard2023_4"
    source := ⟨"alonso-ovalle-rouillard-2023", "(4)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Quiénes marcharon?"
    glossedTokens := [("Quiénes", "who.PL"), ("marcharon", "left.PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .unacceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "PBI")] }

def ex_5 : Datum :=
  { id := "alonsoovallerouillard2023_5"
    source := ⟨"alonso-ovalle-rouillard-2023", "(5)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Quién marchó?"
    glossedTokens := [("Quién", "who.SG"), ("marchó", "left.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .acceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "SBI")] }

def ex_22a : Datum :=
  { id := "alonsoovallerouillard2023_22a"
    source := ⟨"alonso-ovalle-rouillard-2023", "(22a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Quiénes forman un comité?"
    glossedTokens := [("Quiénes", "who.PL"), ("forman", "form.PL"), ("un", "a"), ("comité", "committee")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("two-group answer", .acceptable)]
    paperFeatures := [("type", "PBI")] }

def ex_27a : Datum :=
  { id := "alonsoovallerouillard2023_27a"
    source := ⟨"alonso-ovalle-rouillard-2023", "(27a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Con quién tienes que hablar?"
    glossedTokens := [("Con", "with"), ("quién", "whom.SG"), ("tienes", "have-to.2SG"), ("que", "que"), ("hablar", "talk")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("disjunction of an atom and a plurality", .acceptable)]
    paperFeatures := [("type", "SBI")] }

def ex_28a : Datum :=
  { id := "alonsoovallerouillard2023_28a"
    source := ⟨"alonso-ovalle-rouillard-2023", "(28a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Con quiénes tienes que hablar?"
    glossedTokens := [("Con", "with"), ("quiénes", "whom.PL"), ("tienes", "have-to.2SG"), ("que", "que"), ("hablar", "talk")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("disjunction of pluralities", .acceptable)]
    paperFeatures := [("type", "PBI")] }

def ex_53a : Datum :=
  { id := "alonsoovallerouillard2023_53a"
    source := ⟨"alonso-ovalle-rouillard-2023", "(53a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Quién levantó ese piano?"
    glossedTokens := [("Quién", "who.SG"), ("levantó", "lifted"), ("ese", "that"), ("piano", "piano")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("collective answer", .acceptable)]
    paperFeatures := [("type", "SBI")] }

def ex_58a : Datum :=
  { id := "alonsoovallerouillard2023_58a"
    source := ⟨"alonso-ovalle-rouillard-2023", "(58a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Quién es grande?"
    glossedTokens := [("Quién", "who.SG"), ("es", "is"), ("grande", "tall/big")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("distributive answer", .acceptable), ("group answer", .unacceptable)]
    paperFeatures := [("type", "SBI")] }

def ex_59a : Datum :=
  { id := "alonsoovallerouillard2023_59a"
    source := ⟨"alonso-ovalle-rouillard-2023", "(59a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Quién habló con esos diez profesores?"
    glossedTokens := [("Quién", "who.SG"), ("habló", "talked"), ("con", "to"), ("esos", "these"), ("diez", "ten"), ("profesores", "professors")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("cumulative answer", .acceptable)]
    paperFeatures := [("type", "SBI")] }

def ex_66a : Datum :=
  { id := "alonsoovallerouillard2023_66a"
    source := ⟨"alonso-ovalle-rouillard-2023", "(66a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Con quiénes tiene que hablar Juan?"
    glossedTokens := [("Con", "with"), ("quiénes", "who.PL"), ("tiene", "must"), ("que", "that"), ("hablar", "talk-to"), ("Juan", "Juan")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("disjunction of pluralities", .acceptable), ("disjunction of atoms", .unacceptable), ("disjunction of an atom and a plurality", .unacceptable)]
    paperFeatures := [("type", "PBI")] }

def ex_78 : Datum :=
  { id := "alonsoovallerouillard2023_78"
    source := ⟨"alonso-ovalle-rouillard-2023", "(78)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Quiénes se juntaron ayer a la noche?"
    glossedTokens := [("Quiénes", "who.PL"), ("se", "REFLX"), ("juntaron", "gathered"), ("ayer", "yesterday"), ("a", "at"), ("la", "the"), ("noche", "night")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "PBI")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_22a, ex_27a, ex_28a, ex_53a, ex_58a, ex_59a, ex_66a, ex_78]

end AlonsoOvalleRouillard2023.Examples
