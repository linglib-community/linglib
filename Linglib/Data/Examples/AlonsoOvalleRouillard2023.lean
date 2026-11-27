module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

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
    contrasts := []
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
    contrasts := []
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
    contrasts := [("Who are leaving?", .ungrammatical)]
    readings := [("singular answer", .acceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "BI")] }

def ex_4 : Datum :=
  { id := "alonsoovallerouillard2023_4"
    source := ⟨"alonso-ovalle-rouillard-2023", "(4)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Quiénes marcharon?"
    glossedTokens := [("Quiénes", "who.PL"), ("marcharon", "left.PL")]
    glossedWords := [⟨['Q', 'u', 'i', 'é', 'n', 'e', 's'], ['w', 'h', 'o', '.', 'P', 'L'], [⟨['Q', 'u', 'i', 'é', 'n', 'e', 's'], ['w', 'h', 'o', '.', 'P', 'L'], none⟩]⟩, ⟨['m', 'a', 'r', 'c', 'h', 'a', 'r', 'o', 'n'], ['l', 'e', 'f', 't', '.', 'P', 'L'], [⟨['m', 'a', 'r', 'c', 'h', 'a', 'r', 'o', 'n'], ['l', 'e', 'f', 't', '.', 'P', 'L'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("singular answer", .unacceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "PBI")] }

def ex_5 : Datum :=
  { id := "alonsoovallerouillard2023_5"
    source := ⟨"alonso-ovalle-rouillard-2023", "(5)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Quién marchó?"
    glossedTokens := [("Quién", "who.SG"), ("marchó", "left.SG")]
    glossedWords := [⟨['Q', 'u', 'i', 'é', 'n'], ['w', 'h', 'o', '.', 'S', 'G'], [⟨['Q', 'u', 'i', 'é', 'n'], ['w', 'h', 'o', '.', 'S', 'G'], none⟩]⟩, ⟨['m', 'a', 'r', 'c', 'h', 'ó'], ['l', 'e', 'f', 't', '.', 'S', 'G'], [⟨['m', 'a', 'r', 'c', 'h', 'ó'], ['l', 'e', 'f', 't', '.', 'S', 'G'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("singular answer", .acceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "SBI")] }

def ex_22a : Datum :=
  { id := "alonsoovallerouillard2023_22a"
    source := ⟨"alonso-ovalle-rouillard-2023", "(22a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Quiénes forman un comité?"
    glossedTokens := [("Quiénes", "who.PL"), ("forman", "form.PL"), ("un", "a"), ("comité", "committee")]
    glossedWords := [⟨['Q', 'u', 'i', 'é', 'n', 'e', 's'], ['w', 'h', 'o', '.', 'P', 'L'], [⟨['Q', 'u', 'i', 'é', 'n', 'e', 's'], ['w', 'h', 'o', '.', 'P', 'L'], none⟩]⟩, ⟨['f', 'o', 'r', 'm', 'a', 'n'], ['f', 'o', 'r', 'm', '.', 'P', 'L'], [⟨['f', 'o', 'r', 'm', 'a', 'n'], ['f', 'o', 'r', 'm', '.', 'P', 'L'], none⟩]⟩, ⟨['u', 'n'], ['a'], [⟨['u', 'n'], ['a'], none⟩]⟩, ⟨['c', 'o', 'm', 'i', 't', 'é'], ['c', 'o', 'm', 'm', 'i', 't', 't', 'e', 'e'], [⟨['c', 'o', 'm', 'i', 't', 'é'], ['c', 'o', 'm', 'm', 'i', 't', 't', 'e', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("two-group answer", .acceptable)]
    paperFeatures := [("type", "PBI")] }

def ex_27a : Datum :=
  { id := "alonsoovallerouillard2023_27a"
    source := ⟨"alonso-ovalle-rouillard-2023", "(27a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Con quién tienes que hablar?"
    glossedTokens := [("Con", "with"), ("quién", "whom.SG"), ("tienes", "have-to.2SG"), ("que", "que"), ("hablar", "talk")]
    glossedWords := [⟨['C', 'o', 'n'], ['w', 'i', 't', 'h'], [⟨['C', 'o', 'n'], ['w', 'i', 't', 'h'], none⟩]⟩, ⟨['q', 'u', 'i', 'é', 'n'], ['w', 'h', 'o', 'm', '.', 'S', 'G'], [⟨['q', 'u', 'i', 'é', 'n'], ['w', 'h', 'o', 'm', '.', 'S', 'G'], none⟩]⟩, ⟨['t', 'i', 'e', 'n', 'e', 's'], ['h', 'a', 'v', 'e', '-', 't', 'o', '.', '2', 'S', 'G'], []⟩, ⟨['q', 'u', 'e'], ['q', 'u', 'e'], [⟨['q', 'u', 'e'], ['q', 'u', 'e'], none⟩]⟩, ⟨['h', 'a', 'b', 'l', 'a', 'r'], ['t', 'a', 'l', 'k'], [⟨['h', 'a', 'b', 'l', 'a', 'r'], ['t', 'a', 'l', 'k'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("disjunction of an atom and a plurality", .acceptable)]
    paperFeatures := [("type", "SBI")] }

def ex_28a : Datum :=
  { id := "alonsoovallerouillard2023_28a"
    source := ⟨"alonso-ovalle-rouillard-2023", "(28a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Con quiénes tienes que hablar?"
    glossedTokens := [("Con", "with"), ("quiénes", "whom.PL"), ("tienes", "have-to.2SG"), ("que", "que"), ("hablar", "talk")]
    glossedWords := [⟨['C', 'o', 'n'], ['w', 'i', 't', 'h'], [⟨['C', 'o', 'n'], ['w', 'i', 't', 'h'], none⟩]⟩, ⟨['q', 'u', 'i', 'é', 'n', 'e', 's'], ['w', 'h', 'o', 'm', '.', 'P', 'L'], [⟨['q', 'u', 'i', 'é', 'n', 'e', 's'], ['w', 'h', 'o', 'm', '.', 'P', 'L'], none⟩]⟩, ⟨['t', 'i', 'e', 'n', 'e', 's'], ['h', 'a', 'v', 'e', '-', 't', 'o', '.', '2', 'S', 'G'], []⟩, ⟨['q', 'u', 'e'], ['q', 'u', 'e'], [⟨['q', 'u', 'e'], ['q', 'u', 'e'], none⟩]⟩, ⟨['h', 'a', 'b', 'l', 'a', 'r'], ['t', 'a', 'l', 'k'], [⟨['h', 'a', 'b', 'l', 'a', 'r'], ['t', 'a', 'l', 'k'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("disjunction of pluralities", .acceptable)]
    paperFeatures := [("type", "PBI")] }

def ex_53a : Datum :=
  { id := "alonsoovallerouillard2023_53a"
    source := ⟨"alonso-ovalle-rouillard-2023", "(53a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Quién levantó ese piano?"
    glossedTokens := [("Quién", "who.SG"), ("levantó", "lifted"), ("ese", "that"), ("piano", "piano")]
    glossedWords := [⟨['Q', 'u', 'i', 'é', 'n'], ['w', 'h', 'o', '.', 'S', 'G'], [⟨['Q', 'u', 'i', 'é', 'n'], ['w', 'h', 'o', '.', 'S', 'G'], none⟩]⟩, ⟨['l', 'e', 'v', 'a', 'n', 't', 'ó'], ['l', 'i', 'f', 't', 'e', 'd'], [⟨['l', 'e', 'v', 'a', 'n', 't', 'ó'], ['l', 'i', 'f', 't', 'e', 'd'], none⟩]⟩, ⟨['e', 's', 'e'], ['t', 'h', 'a', 't'], [⟨['e', 's', 'e'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['p', 'i', 'a', 'n', 'o'], ['p', 'i', 'a', 'n', 'o'], [⟨['p', 'i', 'a', 'n', 'o'], ['p', 'i', 'a', 'n', 'o'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("collective answer", .acceptable)]
    paperFeatures := [("type", "SBI")] }

def ex_58a : Datum :=
  { id := "alonsoovallerouillard2023_58a"
    source := ⟨"alonso-ovalle-rouillard-2023", "(58a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Quién es grande?"
    glossedTokens := [("Quién", "who.SG"), ("es", "is"), ("grande", "tall/big")]
    glossedWords := [⟨['Q', 'u', 'i', 'é', 'n'], ['w', 'h', 'o', '.', 'S', 'G'], [⟨['Q', 'u', 'i', 'é', 'n'], ['w', 'h', 'o', '.', 'S', 'G'], none⟩]⟩, ⟨['e', 's'], ['i', 's'], [⟨['e', 's'], ['i', 's'], none⟩]⟩, ⟨['g', 'r', 'a', 'n', 'd', 'e'], ['t', 'a', 'l', 'l', '/', 'b', 'i', 'g'], [⟨['g', 'r', 'a', 'n', 'd', 'e'], ['t', 'a', 'l', 'l', '/', 'b', 'i', 'g'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("distributive answer", .acceptable), ("group answer", .unacceptable)]
    paperFeatures := [("type", "SBI")] }

def ex_59a : Datum :=
  { id := "alonsoovallerouillard2023_59a"
    source := ⟨"alonso-ovalle-rouillard-2023", "(59a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Quién habló con esos diez profesores?"
    glossedTokens := [("Quién", "who.SG"), ("habló", "talked"), ("con", "to"), ("esos", "these"), ("diez", "ten"), ("profesores", "professors")]
    glossedWords := [⟨['Q', 'u', 'i', 'é', 'n'], ['w', 'h', 'o', '.', 'S', 'G'], [⟨['Q', 'u', 'i', 'é', 'n'], ['w', 'h', 'o', '.', 'S', 'G'], none⟩]⟩, ⟨['h', 'a', 'b', 'l', 'ó'], ['t', 'a', 'l', 'k', 'e', 'd'], [⟨['h', 'a', 'b', 'l', 'ó'], ['t', 'a', 'l', 'k', 'e', 'd'], none⟩]⟩, ⟨['c', 'o', 'n'], ['t', 'o'], [⟨['c', 'o', 'n'], ['t', 'o'], none⟩]⟩, ⟨['e', 's', 'o', 's'], ['t', 'h', 'e', 's', 'e'], [⟨['e', 's', 'o', 's'], ['t', 'h', 'e', 's', 'e'], none⟩]⟩, ⟨['d', 'i', 'e', 'z'], ['t', 'e', 'n'], [⟨['d', 'i', 'e', 'z'], ['t', 'e', 'n'], none⟩]⟩, ⟨['p', 'r', 'o', 'f', 'e', 's', 'o', 'r', 'e', 's'], ['p', 'r', 'o', 'f', 'e', 's', 's', 'o', 'r', 's'], [⟨['p', 'r', 'o', 'f', 'e', 's', 'o', 'r', 'e', 's'], ['p', 'r', 'o', 'f', 'e', 's', 's', 'o', 'r', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("cumulative answer", .acceptable)]
    paperFeatures := [("type", "SBI")] }

def ex_66a : Datum :=
  { id := "alonsoovallerouillard2023_66a"
    source := ⟨"alonso-ovalle-rouillard-2023", "(66a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Con quiénes tiene que hablar Juan?"
    glossedTokens := [("Con", "with"), ("quiénes", "who.PL"), ("tiene", "must"), ("que", "that"), ("hablar", "talk-to"), ("Juan", "Juan")]
    glossedWords := [⟨['C', 'o', 'n'], ['w', 'i', 't', 'h'], [⟨['C', 'o', 'n'], ['w', 'i', 't', 'h'], none⟩]⟩, ⟨['q', 'u', 'i', 'é', 'n', 'e', 's'], ['w', 'h', 'o', '.', 'P', 'L'], [⟨['q', 'u', 'i', 'é', 'n', 'e', 's'], ['w', 'h', 'o', '.', 'P', 'L'], none⟩]⟩, ⟨['t', 'i', 'e', 'n', 'e'], ['m', 'u', 's', 't'], [⟨['t', 'i', 'e', 'n', 'e'], ['m', 'u', 's', 't'], none⟩]⟩, ⟨['q', 'u', 'e'], ['t', 'h', 'a', 't'], [⟨['q', 'u', 'e'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['h', 'a', 'b', 'l', 'a', 'r'], ['t', 'a', 'l', 'k', '-', 't', 'o'], []⟩, ⟨['J', 'u', 'a', 'n'], ['J', 'u', 'a', 'n'], [⟨['J', 'u', 'a', 'n'], ['J', 'u', 'a', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("disjunction of pluralities", .acceptable), ("disjunction of atoms", .unacceptable), ("disjunction of an atom and a plurality", .unacceptable)]
    paperFeatures := [("type", "PBI")] }

def ex_78 : Datum :=
  { id := "alonsoovallerouillard2023_78"
    source := ⟨"alonso-ovalle-rouillard-2023", "(78)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Quiénes se juntaron ayer a la noche?"
    glossedTokens := [("Quiénes", "who.PL"), ("se", "REFLX"), ("juntaron", "gathered"), ("ayer", "yesterday"), ("a", "at"), ("la", "the"), ("noche", "night")]
    glossedWords := [⟨['Q', 'u', 'i', 'é', 'n', 'e', 's'], ['w', 'h', 'o', '.', 'P', 'L'], [⟨['Q', 'u', 'i', 'é', 'n', 'e', 's'], ['w', 'h', 'o', '.', 'P', 'L'], none⟩]⟩, ⟨['s', 'e'], ['R', 'E', 'F', 'L', 'X'], [⟨['s', 'e'], ['R', 'E', 'F', 'L', 'X'], none⟩]⟩, ⟨['j', 'u', 'n', 't', 'a', 'r', 'o', 'n'], ['g', 'a', 't', 'h', 'e', 'r', 'e', 'd'], [⟨['j', 'u', 'n', 't', 'a', 'r', 'o', 'n'], ['g', 'a', 't', 'h', 'e', 'r', 'e', 'd'], none⟩]⟩, ⟨['a', 'y', 'e', 'r'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['a', 'y', 'e', 'r'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩, ⟨['a'], ['a', 't'], [⟨['a'], ['a', 't'], none⟩]⟩, ⟨['l', 'a'], ['t', 'h', 'e'], [⟨['l', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['n', 'o', 'c', 'h', 'e'], ['n', 'i', 'g', 'h', 't'], [⟨['n', 'o', 'c', 'h', 'e'], ['n', 'i', 'g', 'h', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("type", "PBI")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_22a, ex_27a, ex_28a, ex_53a, ex_58a, ex_59a, ex_66a, ex_78]

/-- An interrogative phrase, by the paper's taxonomy of its rows. -/
inductive Phrase where
  /-- SCI: A singular complex phrase, *which student* -/
  | sci
  /-- PCI: A plural complex phrase, *which students* -/
  | pci
  /-- BI: an English bare phrase, *who* -/
  | bi
  /-- SBI: A singular bare phrase, *quién* -/
  | sbi
  /-- PBI: A plural bare phrase, *quiénes* -/
  | pbi
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `type`. -/
def phrase (e : Datum) : Option Phrase :=
  e.parse? "type" [("SCI", .sci), ("PCI", .pci), ("BI", .bi), ("SBI", .sbi), ("PBI", .pbi)]

end AlonsoOvalleRouillard2023.Examples
