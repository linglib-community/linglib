module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Borer2005` — typed example data

Auto-generated from `Linglib/Data/Examples/Borer2005.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Borer2005.Examples`.
-/

@[expose] public section

namespace Borer2005.Examples

def ex_28 : Datum :=
  { id := "borer2005_28"
    source := ⟨"borer-2005", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "much salt"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "much"), ("stem", "bare")] }

def ex_29a_meat : Datum :=
  { id := "borer2005_29a_meat"
    source := ⟨"borer-2005", "(29a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "two meat"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "two"), ("stem", "bare")] }

def ex_29a_boy : Datum :=
  { id := "borer2005_29a_boy"
    source := ⟨"borer-2005", "(29a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "two boy"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "two"), ("stem", "bare")] }

def ex_29b_meat : Datum :=
  { id := "borer2005_29b_meat"
    source := ⟨"borer-2005", "(29b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "several meat"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "several"), ("stem", "bare")] }

def ex_29b_boy : Datum :=
  { id := "borer2005_29b_boy"
    source := ⟨"borer-2005", "(29b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "several boy"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "several"), ("stem", "bare")] }

def ex_29c_meat : Datum :=
  { id := "borer2005_29c_meat"
    source := ⟨"borer-2005", "(29c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "many meat"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "many"), ("stem", "bare")] }

def ex_29c_boy : Datum :=
  { id := "borer2005_29c_boy"
    source := ⟨"borer-2005", "(29c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "many boy"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "many"), ("stem", "bare")] }

def ex_29d_meat : Datum :=
  { id := "borer2005_29d_meat"
    source := ⟨"borer-2005", "(29d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "a few meat"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "a few"), ("stem", "bare")] }

def ex_29d_boy : Datum :=
  { id := "borer2005_29d_boy"
    source := ⟨"borer-2005", "(29d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "a few boy"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "a few"), ("stem", "bare")] }

def ex_29e_meat : Datum :=
  { id := "borer2005_29e_meat"
    source := ⟨"borer-2005", "(29e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "both meat"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "both"), ("stem", "bare")] }

def ex_29e_boy : Datum :=
  { id := "borer2005_29e_boy"
    source := ⟨"borer-2005", "(29e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "both boy"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "both"), ("stem", "bare")] }

def ex_30a_boy : Datum :=
  { id := "borer2005_30a_boy"
    source := ⟨"borer-2005", "(30a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "a boy"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "a"), ("stem", "bare")] }

def ex_30a_meat : Datum :=
  { id := "borer2005_30a_meat"
    source := ⟨"borer-2005", "(30a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "one meat"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "one"), ("stem", "bare")] }

def ex_30b_boys : Datum :=
  { id := "borer2005_30b_boys"
    source := ⟨"borer-2005", "(30b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "three boys"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "three"), ("stem", "plural")] }

def ex_30b_meats : Datum :=
  { id := "borer2005_30b_meats"
    source := ⟨"borer-2005", "(30b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "several meats"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "several"), ("stem", "plural")] }

def ex_30c_boy : Datum :=
  { id := "borer2005_30c_boy"
    source := ⟨"borer-2005", "(30c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "every boy"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "every"), ("stem", "bare")] }

def ex_30c_meat : Datum :=
  { id := "borer2005_30c_meat"
    source := ⟨"borer-2005", "(30c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "each meat"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "each"), ("stem", "bare")] }

def ex_31a : Datum :=
  { id := "borer2005_31a"
    source := ⟨"borer-2005", "(31a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "zero boy"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "zero"), ("stem", "bare"), ("reading", "singular")] }

def ex_31b : Datum :=
  { id := "borer2005_31b"
    source := ⟨"borer-2005", "(31b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "zero boys"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "zero"), ("stem", "plural")] }

def ex_31c : Datum :=
  { id := "borer2005_31c"
    source := ⟨"borer-2005", "(31c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "zero meat"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "zero"), ("stem", "bare")] }

def ex_33a_apples : Datum :=
  { id := "borer2005_33a_apples"
    source := ⟨"borer-2005", "(33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "0.2 apples"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "decimal"), ("stem", "plural")] }

def ex_33a_apple : Datum :=
  { id := "borer2005_33a_apple"
    source := ⟨"borer-2005", "(33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "0.2 apple"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "decimal"), ("stem", "bare")] }

def ex_33d_apples : Datum :=
  { id := "borer2005_33d_apples"
    source := ⟨"borer-2005", "(33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "1.0 apples"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "decimal"), ("stem", "plural")] }

def ex_33d_apple : Datum :=
  { id := "borer2005_33d_apple"
    source := ⟨"borer-2005", "(33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "1.0 apple"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "decimal"), ("stem", "bare")] }

def ex_34 : Datum :=
  { id := "borer2005_34"
    source := ⟨"borer-2005", "(34)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "zero a cat"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "zero"), ("determiner", "a"), ("stem", "bare")] }

def ex_35a : Datum :=
  { id := "borer2005_35a"
    source := ⟨"borer-2005", "(35a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "all meat"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "all"), ("stem", "bare")] }

def ex_35b : Datum :=
  { id := "borer2005_35b"
    source := ⟨"borer-2005", "(35b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "all boys"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "all"), ("stem", "plural")] }

def ex_35c : Datum :=
  { id := "borer2005_35c"
    source := ⟨"borer-2005", "(35c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "all boy"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "all"), ("stem", "bare"), ("reading", "singular")] }

def p112 : Datum :=
  { id := "borer2005_p112"
    source := ⟨"borer-2005", "p. 112"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "several a boy"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "several"), ("determiner", "a"), ("stem", "bare")] }

def ex_36b : Datum :=
  { id := "borer2005_36b"
    source := ⟨"borer-2005", "(36b)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "egy kalap"
    glossedTokens := [("egy", "a"), ("kalap", "hat")]
    glossedWords := [⟨['e', 'g', 'y'], ['a'], [⟨['e', 'g', 'y'], ['a'], none⟩]⟩, ⟨['k', 'a', 'l', 'a', 'p'], ['h', 'a', 't'], [⟨['k', 'a', 'l', 'a', 'p'], ['h', 'a', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "egy"), ("stem", "bare")] }

def ex_36c : Datum :=
  { id := "borer2005_36c"
    source := ⟨"borer-2005", "(36c)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "kalap-ok"
    glossedTokens := [("kalap-ok", "hat-PL")]
    glossedWords := [⟨['k', 'a', 'l', 'a', 'p', '-', 'o', 'k'], ['h', 'a', 't', '-', 'P', 'L'], [⟨['k', 'a', 'l', 'a', 'p'], ['h', 'a', 't'], none⟩, ⟨['o', 'k'], ['P', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("stem", "plural")] }

def ex_37a : Datum :=
  { id := "borer2005_37a"
    source := ⟨"borer-2005", "(37a)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "a két fekete kalap"
    glossedTokens := [("a", "the"), ("két", "two"), ("fekete", "black"), ("kalap", "hat")]
    glossedWords := [⟨['a'], ['t', 'h', 'e'], [⟨['a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['k', 'é', 't'], ['t', 'w', 'o'], [⟨['k', 'é', 't'], ['t', 'w', 'o'], none⟩]⟩, ⟨['f', 'e', 'k', 'e', 't', 'e'], ['b', 'l', 'a', 'c', 'k'], [⟨['f', 'e', 'k', 'e', 't', 'e'], ['b', 'l', 'a', 'c', 'k'], none⟩]⟩, ⟨['k', 'a', 'l', 'a', 'p'], ['h', 'a', 't'], [⟨['k', 'a', 'l', 'a', 'p'], ['h', 'a', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "két"), ("stem", "bare")] }

def ex_37b : Datum :=
  { id := "borer2005_37b"
    source := ⟨"borer-2005", "(37b)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "minden kalap"
    glossedTokens := [("minden", "every"), ("kalap", "hat")]
    glossedWords := [⟨['m', 'i', 'n', 'd', 'e', 'n'], ['e', 'v', 'e', 'r', 'y'], [⟨['m', 'i', 'n', 'd', 'e', 'n'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['k', 'a', 'l', 'a', 'p'], ['h', 'a', 't'], [⟨['k', 'a', 'l', 'a', 'p'], ['h', 'a', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "minden"), ("stem", "bare")] }

def all : List Datum := [ex_28, ex_29a_meat, ex_29a_boy, ex_29b_meat, ex_29b_boy, ex_29c_meat, ex_29c_boy, ex_29d_meat, ex_29d_boy, ex_29e_meat, ex_29e_boy, ex_30a_boy, ex_30a_meat, ex_30b_boys, ex_30b_meats, ex_30c_boy, ex_30c_meat, ex_31a, ex_31b, ex_31c, ex_33a_apples, ex_33a_apple, ex_33d_apples, ex_33d_apple, ex_34, ex_35a, ex_35b, ex_35c, p112, ex_36b, ex_36c, ex_37a, ex_37b]

/-- The determiners, cardinals and quantifiers of the nominal, the definite article apart. -/
inductive Determiner where
  /-- much: (40a) -/
  | much
  /-- two: a cardinal other than one (40d) -/
  | two
  /-- three: a cardinal other than one (40d) -/
  | three
  /-- zero: the cardinal zero (31) -/
  | zero
  /-- decimal: a decimalized number such as 0.2 or 1.0 (33) -/
  | decimal
  /-- several: (40d) -/
  | several
  /-- many: (40d) -/
  | many
  /-- a few: (40d) -/
  | aFew
  /-- both: (40d) -/
  | both
  /-- a: the indefinite article (40c) -/
  | a
  /-- one: the cardinal one (40c) -/
  | one
  /-- every: (40b) -/
  | every
  /-- each: (40b) -/
  | each
  /-- all: (40e) -/
  | all
  /-- egy: Hungarian 'a, one' (36) -/
  | egy
  /-- két: Hungarian 'two' (37) -/
  | ket
  /-- minden: Hungarian 'every' (37) -/
  | minden
  deriving DecidableEq, Repr, Fintype

/-- The values a row records under `determiner`. -/
def determiners (e : Datum) : List Determiner :=
  (e.features "determiner").filterMap (List.lookup · [("much", .much), ("two", .two), ("three", .three), ("zero", .zero), ("decimal", .decimal),
    ("several", .several), ("many", .many), ("a few", .aFew), ("both", .both), ("a", .a),
    ("one", .one), ("every", .every), ("each", .each), ("all", .all), ("egy", .egy),
    ("két", .ket), ("minden", .minden)])

/-- The inflection of the noun stem. -/
inductive Stem where
  /-- bare: an uninflected stem -/
  | bare
  /-- plural: a stem with plural inflection -/
  | plural
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `stem`. -/
def stem (e : Datum) : Option Stem :=
  e.parse? "stem" [("bare", .bare), ("plural", .plural)]

/-- The reading of the stem the judgment is restricted to. -/
inductive Construal where
  /-- singular: the stem read as a singular count noun -/
  | singular
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `reading`. -/
def construal (e : Datum) : Option Construal :=
  e.parse? "reading" [("singular", .singular)]

end Borer2005.Examples
