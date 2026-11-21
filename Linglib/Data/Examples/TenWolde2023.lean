module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `TenWolde2023` — typed example data

Auto-generated from `Linglib/Data/Examples/TenWolde2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace TenWolde2023.Examples`.
-/

@[expose] public section

namespace TenWolde2023.Examples

def ex_5_1d : Datum :=
  { id := "tenwolde2023_5_1d"
    source := ⟨"ten-wolde-2023", "(5.1d)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "a cake of spices"
    glossedTokens := []
    context := "ante 1325, OED: the gloss of Kakenole in W. de Bibbesworth."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("noun", "cake"), ("construction", "N+PP"), ("year", "1325")] }

def ex_5_7a : Datum :=
  { id := "tenwolde2023_5_7a"
    source := ⟨"ten-wolde-2023", "(5.7a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "That . . . he offre a silueren peny, and a round kaak of breed."
    glossedTokens := []
    context := "1382, OED."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("noun", "cake"), ("construction", "pseudo-partitive"), ("year", "1382")] }

def ex_5_4 : Datum :=
  { id := "tenwolde2023_5_4"
    source := ⟨"ten-wolde-2023", "(5.4)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "for he accustomed, to feade him selfe with a cake of rye, the whiche he grounde, and baked vppon the coles . . ."
    glossedTokens := []
    context := "1556, EEBO."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("noun", "cake"), ("construction", "head-classifier"), ("year", "1556")] }

def ex_5_10a : Datum :=
  { id := "tenwolde2023_5_10a"
    source := ⟨"ten-wolde-2023", "(5.10a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "as much as the industrial exhibit now housed in the former palace of Soviet-Chinese Friendship in Shanghai differs from what was originally intended when that towering wedding cake of a building was gratefully received as a present from the Soviet Union"
    glossedTokens := []
    context := "1973, COHA."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("noun", "cake"), ("construction", "EBNP"), ("year", "1973")] }

def ex_5_11 : Datum :=
  { id := "tenwolde2023_5_11"
    source := ⟨"ten-wolde-2023", "(5.11)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "The JLA would have a cake of a time getting this done"
    glossedTokens := []
    context := "2016, a forum post; the corpora have no clear example of cake in the evaluative modifier."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("noun", "cake"), ("construction", "EM"), ("year", "2016")] }

def ex_5_12 : Datum :=
  { id := "tenwolde2023_5_12"
    source := ⟨"ten-wolde-2023", "(5.12)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "þet te beast of helle, hwen he snakereð toward ow forte biten on ow . . ."
    glossedTokens := []
    context := "ca 1200, PPCME."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("noun", "beast"), ("construction", "N+PP"), ("year", "1200")] }

def ex_5_14b : Datum :=
  { id := "tenwolde2023_5_14b"
    source := ⟨"ten-wolde-2023", "(5.14b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "and in that pastyme hauyng to euery beast of venery but two dogges at the moste"
    glossedTokens := []
    context := "1541, EEBO."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("noun", "beast"), ("construction", "head-classifier"), ("year", "1541")] }

def ex_5_17b : Datum :=
  { id := "tenwolde2023_5_17b"
    source := ⟨"ten-wolde-2023", "(5.17b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "how great a beast of a man (a cruell thyng to be spoken) shal he be made then?"
    glossedTokens := []
    context := "1555, EEBO; the close of a longer sentence."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("noun", "beast"), ("construction", "EBNP"), ("year", "1555")] }

def ex_5_19a : Datum :=
  { id := "tenwolde2023_5_19a"
    source := ⟨"ten-wolde-2023", "(5.19a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "aye, I lost the finest beast of a mare in all Devonshire"
    glossedTokens := []
    context := "1678, EEBO."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("noun", "beast"), ("construction", "EM"), ("year", "1678")] }

def ex_5_20a : Datum :=
  { id := "tenwolde2023_5_20a"
    source := ⟨"ten-wolde-2023", "(5.20a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "what Americans face – or rather refuse to face – on their doorstep is a beast of a frightening new order: A Clockwork Orange set to ranchera music."
    glossedTokens := []
    context := "2010, COCA."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("noun", "beast"), ("construction", "BI"), ("year", "2010")] }

def ex_5_23d : Datum :=
  { id := "tenwolde2023_5_23d"
    source := ⟨"ten-wolde-2023", "(5.23d)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "it should also cause the vtter losse and dampnacion in hell of many thousand souls"
    glossedTokens := []
    context := "1530, EEBO."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("noun", "hell"), ("construction", "N+PP"), ("year", "1530")] }

def ex_5_25b : Datum :=
  { id := "tenwolde2023_5_25b"
    source := ⟨"ten-wolde-2023", "(5.25b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "She made no reckoning of his importunate and dilligent seruice, which drewe a Hell of tormentinge thoughts vppon Tarisius."
    glossedTokens := []
    context := "1588, OED."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("noun", "hell"), ("construction", "head-classifier"), ("year", "1588")] }

def ex_5_28 : Datum :=
  { id := "tenwolde2023_5_28"
    source := ⟨"ten-wolde-2023", "(5.28)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "heere woe and there woe, and a very hell of woes is heaped vppon mee"
    glossedTokens := []
    context := "1601, EEBO."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("noun", "hell"), ("construction", "pseudo-partitive"), ("year", "1601")] }

def ex_5_27b : Datum :=
  { id := "tenwolde2023_5_27b"
    source := ⟨"ten-wolde-2023", "(5.27b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "With the click of a mouse he could fire a hell of microwaves up at the ionosphere"
    glossedTokens := []
    context := "2006, COCA."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("noun", "hell"), ("construction", "pseudo-partitive"), ("year", "2006")] }

def ex_5_29a : Datum :=
  { id := "tenwolde2023_5_29a"
    source := ⟨"ten-wolde-2023", "(5.29a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "For if you were by my unkindness shaken, As I by yours, y' haue past a hell of time"
    glossedTokens := []
    context := "1609, OED: Shakespeare, Sonnet 120."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("noun", "hell"), ("construction", "EBNP"), ("year", "1609")] }

def ex_5_30 : Datum :=
  { id := "tenwolde2023_5_30"
    source := ⟨"ten-wolde-2023", "(5.30)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "This is a hell of a council of war."
    glossedTokens := []
    context := "1776, OED."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("noun", "hell"), ("construction", "EM"), ("year", "1776")] }

def ex_5_31a : Datum :=
  { id := "tenwolde2023_5_31a"
    source := ⟨"ten-wolde-2023", "(5.31a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "an' tell de boys he in a hell of a hurry, sah!"
    glossedTokens := []
    context := "1867, COHA."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("noun", "hell"), ("construction", "EM"), ("year", "1867")] }

def ex_5_33a : Datum :=
  { id := "tenwolde2023_5_33a"
    source := ⟨"ten-wolde-2023", "(5.33a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Thomas Burchard, testified that several nights since he had been fleeced at the same hell of a large sum"
    glossedTokens := []
    context := "1839, COHA."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("noun", "hell"), ("construction", "BI"), ("year", "1839")] }

def all : List Datum := [ex_5_1d, ex_5_7a, ex_5_4, ex_5_10a, ex_5_11, ex_5_12, ex_5_14b, ex_5_17b, ex_5_19a, ex_5_20a, ex_5_23d, ex_5_25b, ex_5_28, ex_5_27b, ex_5_29a, ex_5_30, ex_5_31a, ex_5_33a]

/-- The first nouns of the three case studies. -/
inductive Noun where
  /-- cake: an inanimate first noun -/
  | cake
  /-- beast: an animate first noun -/
  | beast
  /-- hell: an abstract first noun -/
  | hell
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `noun`. -/
def noun (e : Datum) : Option Noun :=
  e.parse? "noun" [("cake", .cake), ("beast", .beast), ("hell", .hell)]

/-- The of-binominal constructions. -/
inductive Construction where
  /-- N+PP: the prototypical N+PP -/
  | nPP
  /-- head-classifier: the head-classifier -/
  | headClassifier
  /-- pseudo-partitive: the pseudo-partitive -/
  | pseudoPartitive
  /-- EBNP: the evaluative binominal noun phrase -/
  | ebnp
  /-- EM: the evaluative modifier -/
  | em
  /-- BI: the binominal intensifier -/
  | bi
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `construction`. -/
def construction (e : Datum) : Option Construction :=
  e.parse? "construction" [("N+PP", .nPP), ("head-classifier", .headClassifier),
    ("pseudo-partitive", .pseudoPartitive), ("EBNP", .ebnp), ("EM", .em), ("BI", .bi)]

/-- The dated examples of the three case studies. -/
inductive Example where
  | ex_5_1d
  | ex_5_7a
  | ex_5_4
  | ex_5_10a
  | ex_5_11
  | ex_5_12
  | ex_5_14b
  | ex_5_17b
  | ex_5_19a
  | ex_5_20a
  | ex_5_23d
  | ex_5_25b
  | ex_5_28
  | ex_5_27b
  | ex_5_29a
  | ex_5_30
  | ex_5_31a
  | ex_5_33a
  deriving DecidableEq, Repr, Fintype

/-- Every example of the file, in its order. -/
def Example.all : List Example :=
  [.ex_5_1d, .ex_5_7a, .ex_5_4, .ex_5_10a, .ex_5_11, .ex_5_12, .ex_5_14b, .ex_5_17b, .ex_5_19a,
    .ex_5_20a, .ex_5_23d, .ex_5_25b, .ex_5_28, .ex_5_27b, .ex_5_29a, .ex_5_30, .ex_5_31a,
    .ex_5_33a]

/-- The row of an example. -/
def Example.datum : Example → Datum
  | .ex_5_1d => _root_.TenWolde2023.Examples.ex_5_1d
  | .ex_5_7a => _root_.TenWolde2023.Examples.ex_5_7a
  | .ex_5_4 => _root_.TenWolde2023.Examples.ex_5_4
  | .ex_5_10a => _root_.TenWolde2023.Examples.ex_5_10a
  | .ex_5_11 => _root_.TenWolde2023.Examples.ex_5_11
  | .ex_5_12 => _root_.TenWolde2023.Examples.ex_5_12
  | .ex_5_14b => _root_.TenWolde2023.Examples.ex_5_14b
  | .ex_5_17b => _root_.TenWolde2023.Examples.ex_5_17b
  | .ex_5_19a => _root_.TenWolde2023.Examples.ex_5_19a
  | .ex_5_20a => _root_.TenWolde2023.Examples.ex_5_20a
  | .ex_5_23d => _root_.TenWolde2023.Examples.ex_5_23d
  | .ex_5_25b => _root_.TenWolde2023.Examples.ex_5_25b
  | .ex_5_28 => _root_.TenWolde2023.Examples.ex_5_28
  | .ex_5_27b => _root_.TenWolde2023.Examples.ex_5_27b
  | .ex_5_29a => _root_.TenWolde2023.Examples.ex_5_29a
  | .ex_5_30 => _root_.TenWolde2023.Examples.ex_5_30
  | .ex_5_31a => _root_.TenWolde2023.Examples.ex_5_31a
  | .ex_5_33a => _root_.TenWolde2023.Examples.ex_5_33a

theorem Example.map_datum_all :
    Example.all.map Example.datum = _root_.TenWolde2023.Examples.all := rfl

/-- The value the example records under `noun`. -/
def Example.noun : Example → Option Noun
  | .ex_5_1d => some .cake
  | .ex_5_7a => some .cake
  | .ex_5_4 => some .cake
  | .ex_5_10a => some .cake
  | .ex_5_11 => some .cake
  | .ex_5_12 => some .beast
  | .ex_5_14b => some .beast
  | .ex_5_17b => some .beast
  | .ex_5_19a => some .beast
  | .ex_5_20a => some .beast
  | .ex_5_23d => some .hell
  | .ex_5_25b => some .hell
  | .ex_5_28 => some .hell
  | .ex_5_27b => some .hell
  | .ex_5_29a => some .hell
  | .ex_5_30 => some .hell
  | .ex_5_31a => some .hell
  | .ex_5_33a => some .hell

theorem Example.noun_datum :
    ∀ x : Example, _root_.TenWolde2023.Examples.noun x.datum = x.noun := by
  decide +kernel

/-- The value the example records under `construction`. -/
def Example.construction : Example → Option Construction
  | .ex_5_1d => some .nPP
  | .ex_5_7a => some .pseudoPartitive
  | .ex_5_4 => some .headClassifier
  | .ex_5_10a => some .ebnp
  | .ex_5_11 => some .em
  | .ex_5_12 => some .nPP
  | .ex_5_14b => some .headClassifier
  | .ex_5_17b => some .ebnp
  | .ex_5_19a => some .em
  | .ex_5_20a => some .bi
  | .ex_5_23d => some .nPP
  | .ex_5_25b => some .headClassifier
  | .ex_5_28 => some .pseudoPartitive
  | .ex_5_27b => some .pseudoPartitive
  | .ex_5_29a => some .ebnp
  | .ex_5_30 => some .em
  | .ex_5_31a => some .em
  | .ex_5_33a => some .bi

theorem Example.construction_datum :
    ∀ x : Example, _root_.TenWolde2023.Examples.construction x.datum = x.construction := by
  decide +kernel

end TenWolde2023.Examples
