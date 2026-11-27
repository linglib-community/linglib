module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Tsiakmakis2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Tsiakmakis2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Tsiakmakis2025.Examples`.
-/

@[expose] public section

namespace Tsiakmakis2025.Examples

def ex_6 : Datum :=
  { id := "tsiakmakis2025_6"
    source := ⟨"tsiakmakis-2025", "(6)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Dhen vrexi sti Lisavona."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negator", "dhen"), ("use", "negative"), ("mood", "indicative")] }

def ex_8 : Datum :=
  { id := "tsiakmakis2025_8"
    source := ⟨"tsiakmakis-2025", "(8)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Min pas sti Lisavona."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negator", "min"), ("use", "negative"), ("host", "imperative")] }

def ex_14 : Datum :=
  { id := "tsiakmakis2025_14"
    source := ⟨"tsiakmakis-2025", "(14)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Posus anthropus dhen kseyelase sta niata tu!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negator", "dhen"), ("use", "expletive"), ("host", "negative exclamative"), ("class", "apparent")] }

def ex_15 : Datum :=
  { id := "tsiakmakis2025_15"
    source := ⟨"tsiakmakis-2025", "(15)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Dhen ipie o Yanis kafe?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negator", "dhen"), ("use", "expletive"), ("host", "preposed negation question"), ("class", "apparent")] }

def ex_16 : Datum :=
  { id := "tsiakmakis2025_16"
    source := ⟨"tsiakmakis-2025", "(16)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Sto kato kato, dhen ine xrisimi ke i vroxi?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negator", "dhen"), ("use", "expletive"), ("host", "rhetorical question"), ("class", "apparent")] }

def ex_28 : Datum :=
  { id := "tsiakmakis2025_28"
    source := ⟨"tsiakmakis-2025", "(28)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Q: Pxios dhen efaye to fayito tu? A: Se pxion dhen aresun ta yuvarlakia?"
    glossedTokens := []
    context := "It is shared knowledge that dad does not like meatball soup."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negator", "dhen"), ("use", "negative"), ("host", "rhetorical question")] }

def ex_38 : Datum :=
  { id := "tsiakmakis2025_38"
    source := ⟨"tsiakmakis-2025", "(38)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Fovame min efaye ta yuvarlakia o babas."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negator", "min"), ("use", "expletive"), ("host", "fear-predicate complement"), ("class", "proper")] }

def ex_39 : Datum :=
  { id := "tsiakmakis2025_39"
    source := ⟨"tsiakmakis-2025", "(39)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Fovame min dhen efaye ta yuvarlakia o babas."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negator", "min dhen"), ("use", "expletive with canonical negation"), ("host", "fear-predicate complement"), ("class", "proper")] }

def ex_40 : Datum :=
  { id := "tsiakmakis2025_40"
    source := ⟨"tsiakmakis-2025", "(40)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Fovame min efaye TIPOTA o babas."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("negator", "min"), ("use", "expletive"), ("host", "fear-predicate complement"), ("diagnostic", "NCI licensing")] }

def ex_44a : Datum :=
  { id := "tsiakmakis2025_44a"
    source := ⟨"tsiakmakis-2025", "(44a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Fovame o babas min efaye yuvarlakia."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("negator", "min"), ("use", "expletive"), ("host", "fear-predicate complement"), ("diagnostic", "left-periphery merge")] }

def ex_45 : Datum :=
  { id := "tsiakmakis2025_45"
    source := ⟨"tsiakmakis-2025", "(45)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Min ksexaso kati, amesos na koroidepsis."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negator", "min"), ("use", "expletive"), ("host", "conditional"), ("class", "proper")] }

def ex_49b : Datum :=
  { id := "tsiakmakis2025_49b"
    source := ⟨"tsiakmakis-2025", "(49b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "An akusis kutsobolio, amesos tha erthis."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("host", "conditional"), ("conjunction", "an")] }

def ex_51a : Datum :=
  { id := "tsiakmakis2025_51a"
    source := ⟨"tsiakmakis-2025", "(51a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Min efaye ta yuvarlakia o babas?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negator", "min"), ("use", "expletive"), ("host", "polar question"), ("class", "proper")] }

def ex_53a : Datum :=
  { id := "tsiakmakis2025_53a"
    source := ⟨"tsiakmakis-2025", "(53a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Min dhen efaye ta yuvarlakia o babas?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negator", "min dhen"), ("use", "expletive with canonical negation"), ("host", "polar question"), ("class", "proper")] }

def ex_59 : Datum :=
  { id := "tsiakmakis2025_59"
    source := ⟨"tsiakmakis-2025", "(59)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "J'ai peur que vous ne vous fassiez piquer par une méduse."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negator", "ne"), ("use", "expletive"), ("host", "fear-predicate complement"), ("class", "proper")] }

def ex_61 : Datum :=
  { id := "tsiakmakis2025_61"
    source := ⟨"tsiakmakis-2025", "(61)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "paxadeti še-lo lo yiša'er klum."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negator", "lo"), ("use", "expletive with canonical negation"), ("host", "fear-predicate complement"), ("class", "proper")] }

def ex_62 : Datum :=
  { id := "tsiakmakis2025_62"
    source := ⟨"tsiakmakis-2025", "(62)"⟩
    reportedIn := none
    language := "oldf1239"
    primaryText := "Mais tul defent ne seit gabeth Quant dit que set e fait que peot."
    glossedTokens := []
    context := "Benedeit, Le voyage de Saint Brendan, 1121."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negator", "ne"), ("use", "expletive"), ("host", "negative predicate"), ("class", "proper")] }

def ex_65 : Datum :=
  { id := "tsiakmakis2025_65"
    source := ⟨"tsiakmakis-2025", "(65)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Hay quien dude que no son falsas las tales historias?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negator", "no"), ("use", "expletive"), ("host", "dubitative predicate"), ("class", "proper")] }

def ex_67 : Datum :=
  { id := "tsiakmakis2025_67"
    source := ⟨"tsiakmakis-2025", "(67)"⟩
    reportedIn := none
    language := "anci1242"
    primaryText := "apisteis me: ouk episte:me: e:i he: arete:"
    glossedTokens := []
    context := "Plato, Meno, 89d."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negator", "me: ouk"), ("use", "expletive with canonical negation"), ("host", "dubitative predicate"), ("class", "proper")] }

def ex_69a : Datum :=
  { id := "tsiakmakis2025_69a"
    source := ⟨"tsiakmakis-2025", "(69a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Resto qui finché non parli."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negator", "non"), ("use", "negative"), ("host", "temporal expression"), ("class", "apparent")] }

def ex_71 : Datum :=
  { id := "tsiakmakis2025_71"
    source := ⟨"tsiakmakis-2025", "(71)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Je l'ai fait sans qu'il ne me voie."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negator", "ne"), ("use", "expletive"), ("host", "negative adverbial"), ("class", "apparent")] }

def ex_75 : Datum :=
  { id := "tsiakmakis2025_75"
    source := ⟨"tsiakmakis-2025", "(75)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Me ne andrò a meno che tu non mangi."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negator", "non"), ("use", "expletive"), ("host", "unless-conditional"), ("class", "apparent")] }

def ex_77 : Datum :=
  { id := "tsiakmakis2025_77"
    source := ⟨"tsiakmakis-2025", "(77)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni è più alto di quanto non sia Pietro."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negator", "non"), ("use", "expletive"), ("host", "comparative"), ("class", "apparent")] }

def ex_84 : Datum :=
  { id := "tsiakmakis2025_84"
    source := ⟨"tsiakmakis-2025", "(84)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "non -ne animadvertis?"
    glossedTokens := []
    context := "Cicero, De Natura Deorum, 3,89."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negator", "non -ne"), ("use", "expletive with canonical negation"), ("host", "polar question"), ("class", "proper")] }

def ex_87 : Datum :=
  { id := "tsiakmakis2025_87"
    source := ⟨"tsiakmakis-2025", "(87)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Can I trust you? B: Have I ever hurt your feelings?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("host", "rhetorical question"), ("polarity", "positive")] }

def ex_90 : Datum :=
  { id := "tsiakmakis2025_90"
    source := ⟨"tsiakmakis-2025", "(90)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Che cosa non ha fatto Gianni!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negator", "non"), ("use", "expletive"), ("host", "negative exclamative"), ("class", "apparent")] }

def ex_92b : Datum :=
  { id := "tsiakmakis2025_92b"
    source := ⟨"tsiakmakis-2025", "(92b)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "ma še-dani lo katav hitparsem ba-iton."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negator", "lo"), ("use", "expletive"), ("host", "free relative"), ("class", "proper, tentative")] }

def all : List Datum := [ex_6, ex_8, ex_14, ex_15, ex_16, ex_28, ex_38, ex_39, ex_40, ex_44a, ex_45, ex_49b, ex_51a, ex_53a, ex_59, ex_61, ex_62, ex_65, ex_67, ex_69a, ex_71, ex_75, ex_77, ex_84, ex_87, ex_90, ex_92b]

/-- The environment hosting the negation. -/
inductive Host where
  /-- imperative: an imperative -/
  | imperative
  /-- negative exclamative: a negative exclamative -/
  | negativeExclamative
  /-- preposed negation question: a question with preposed negation -/
  | preposedNegationQuestion
  /-- rhetorical question: a rhetorical question -/
  | rhetoricalQuestion
  /-- fear-predicate complement: the complement of a predicate of fearing -/
  | fearPredicateComplement
  /-- conditional: a conditional -/
  | conditional
  /-- polar question: a polar question -/
  | polarQuestion
  /-- negative predicate: the complement of a negative predicate -/
  | negativePredicate
  /-- dubitative predicate: the complement of a predicate of doubt -/
  | dubitativePredicate
  /-- temporal expression: a temporal clause -/
  | temporalExpression
  /-- negative adverbial: a negative adverbial clause -/
  | negativeAdverbial
  /-- unless-conditional: an *unless* conditional -/
  | unlessConditional
  /-- comparative: a comparative clause -/
  | comparative
  /-- free relative: a free relative -/
  | freeRelative
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `host`. -/
def host (e : Datum) : Option Host :=
  e.parse? "host" [("imperative", .imperative), ("negative exclamative", .negativeExclamative),
    ("preposed negation question", .preposedNegationQuestion),
    ("rhetorical question", .rhetoricalQuestion),
    ("fear-predicate complement", .fearPredicateComplement), ("conditional", .conditional),
    ("polar question", .polarQuestion), ("negative predicate", .negativePredicate),
    ("dubitative predicate", .dubitativePredicate),
    ("temporal expression", .temporalExpression), ("negative adverbial", .negativeAdverbial),
    ("unless-conditional", .unlessConditional), ("comparative", .comparative),
    ("free relative", .freeRelative)]

/-- The use of the negation. -/
inductive Use where
  /-- negative: canonical negation -/
  | negative
  /-- expletive: expletive negation -/
  | expletive
  /-- expletive with canonical negation: expletive negation beside canonical negation -/
  | expletiveWithCanonical
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `use`. -/
def use (e : Datum) : Option Use :=
  e.parse? "use" [("negative", .negative), ("expletive", .expletive),
    ("expletive with canonical negation", .expletiveWithCanonical)]

end Tsiakmakis2025.Examples
