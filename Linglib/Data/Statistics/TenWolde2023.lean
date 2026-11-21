module

public import Linglib.Data.Statistics.Schema

/-!
# TenWolde2023: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/TenWolde2023.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

The raw frequencies of six first nouns in the of-binominal constructions, by decade, in the Corpus
of Historical American English and the Corpus of Contemporary American English (Tables 6.3 to 6.8),
and the semantic class of each first noun the study names (Table 2.1). The tables also print
normalized frequencies and percentages, and all but Table 6.3 a row of totals, which are not
recorded. The book prints no frequency table for cake, beast and hell.

## References

* [ten-wolde-2023]
-/

@[expose] public section

namespace TenWolde2023

open Data.Statistics

/-- The first nouns of the case studies and of the corpus study. -/
inductive Noun where
  /-- cake: *cake* -/
  | cake
  /-- beast: *beast* -/
  | beast
  /-- hell: *hell* -/
  | hell
  /-- nub: *nub* -/
  | nub
  /-- breeze: *breeze* -/
  | breeze
  /-- husk: *husk* -/
  | husk
  /-- snake: *snake* -/
  | snake
  /-- whale: *whale* -/
  | whale
  /-- bitch: *bitch* -/
  | bitch
  deriving DecidableEq, Repr, Fintype

/-- The semantic classes of first nouns. -/
inductive SemanticClass where
  /-- abstract: third-order entities, among them mythical beings and expletives -/
  | abstract
  /-- animate: animate first-order entities -/
  | animate
  /-- inanimate: plants and lifeless objects -/
  | inanimate
  deriving DecidableEq, Repr, Fintype

/-- The rows of the frequency tables. -/
inductive Category where
  /-- N+PP: the prototypical N+PP -/
  | nPP
  /-- Head-Cl: the head-classifier, printed Head-Cl or Head-Q -/
  | headClassifier
  /-- Pseudo-P: the pseudo-partitive -/
  | pseudoPartitive
  /-- EBNP: the evaluative binominal noun phrase -/
  | ebnp
  /-- EM: the evaluative modifier -/
  | em
  /-- BI: the binominal intensifier -/
  | bi
  /-- unclear: tokens the book leaves unclassified -/
  | unclear
  deriving DecidableEq, Repr, Fintype

/-- A row of Table 2.1: the semantic class of a first noun. -/
structure NounClass where
  /-- Its class. -/
  semanticClass : SemanticClass
  deriving DecidableEq, Repr

/-- The cells of Table 2.1, by noun; counted in a corpus; checked against the PDF text layer
only. -/
def nouns : Noun → NounClass
  | .cake => ⟨.inanimate⟩
  | .beast => ⟨.animate⟩
  | .hell => ⟨.abstract⟩
  | .nub => ⟨.inanimate⟩
  | .breeze => ⟨.inanimate⟩
  | .husk => ⟨.inanimate⟩
  | .snake => ⟨.animate⟩
  | .whale => ⟨.animate⟩
  | .bitch => ⟨.abstract⟩

/-- A row of Tables 6.3 to 6.8: the decade with which the frequency table of a first noun begins;
every table ends with the period 2010 to 2015. -/
structure Period where
  /-- The first year of the first decade, where the book prints a table for the noun. -/
  start : Option ℕ
  deriving DecidableEq, Repr

/-- The cells of Tables 6.3 to 6.8, by noun; counted in a corpus; checked against the page
images. -/
def periods : Noun → Period
  | .cake => ⟨none⟩
  | .beast => ⟨none⟩
  | .hell => ⟨none⟩
  | .nub => ⟨some 1810⟩
  | .breeze => ⟨some 1810⟩
  | .husk => ⟨some 1810⟩
  | .snake => ⟨some 1810⟩
  | .whale => ⟨some 1810⟩
  | .bitch => ⟨some 1920⟩

/-- A row of Tables 6.3 to 6.8: the raw number of tokens of a first noun in a construction in
each period, from the first decade of its table to 2010 to 2015. -/
structure Frequency where
  /-- The raw figures by period, where the table of the noun has a row for the construction. -/
  counts : Option (List ℕ)
  deriving DecidableEq, Repr

/-- The cells of Tables 6.3 to 6.8, by noun and category; counted in a corpus; checked against
the page images. -/
def frequencies : Noun → Category → Frequency
  | .cake, .nPP => ⟨none⟩
  | .cake, .headClassifier => ⟨none⟩
  | .cake, .pseudoPartitive => ⟨none⟩
  | .cake, .ebnp => ⟨none⟩
  | .cake, .em => ⟨none⟩
  | .cake, .bi => ⟨none⟩
  | .cake, .unclear => ⟨none⟩
  | .beast, .nPP => ⟨none⟩
  | .beast, .headClassifier => ⟨none⟩
  | .beast, .pseudoPartitive => ⟨none⟩
  | .beast, .ebnp => ⟨none⟩
  | .beast, .em => ⟨none⟩
  | .beast, .bi => ⟨none⟩
  | .beast, .unclear => ⟨none⟩
  | .hell, .nPP => ⟨none⟩
  | .hell, .headClassifier => ⟨none⟩
  | .hell, .pseudoPartitive => ⟨none⟩
  | .hell, .ebnp => ⟨none⟩
  | .hell, .em => ⟨none⟩
  | .hell, .bi => ⟨none⟩
  | .hell, .unclear => ⟨none⟩
  | .nub, .nPP => ⟨some [0, 0, 2, 0, 0, 2, 0, 1, 1, 0, 2, 9, 7, 15, 14, 10, 13, 9, 49, 36, 17]⟩
  | .nub, .headClassifier => ⟨some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 1, 0, 13, 9, 6]⟩
  | .nub, .pseudoPartitive => ⟨some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 0]⟩
  | .nub, .ebnp => ⟨some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 5, 4, 2]⟩
  | .nub, .em => ⟨none⟩
  | .nub, .bi => ⟨none⟩
  | .nub, .unclear => ⟨none⟩
  | .breeze, .nPP =>
    ⟨some [2, 6, 17, 33, 23, 13, 12, 17, 16, 8, 12, 5, 8, 4, 4, 6, 3, 4, 30, 31, 13]⟩
  | .breeze, .headClassifier =>
    ⟨some [4, 8, 17, 10, 22, 9, 14, 13, 9, 7, 10, 3, 4, 3, 1, 9, 2, 3, 22, 12, 4]⟩
  | .breeze, .pseudoPartitive =>
    ⟨some [1, 0, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 0, 2, 0, 2, 4, 5, 1]⟩
  | .breeze, .ebnp => ⟨some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0]⟩
  | .breeze, .em => ⟨none⟩
  | .breeze, .bi => ⟨none⟩
  | .breeze, .unclear => ⟨some [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]⟩
  | .husk, .nPP => ⟨some [0, 1, 0, 5, 6, 2, 2, 1, 3, 3, 6, 4, 3, 1, 0, 2, 3, 6, 8, 20, 21]⟩
  | .husk, .headClassifier =>
    ⟨some [0, 1, 1, 2, 5, 3, 6, 6, 5, 6, 5, 4, 4, 4, 2, 1, 4, 0, 34, 23, 18]⟩
  | .husk, .pseudoPartitive =>
    ⟨some [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩
  | .husk, .ebnp => ⟨some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1, 1, 1, 5, 9, 5]⟩
  | .husk, .em => ⟨none⟩
  | .husk, .bi => ⟨none⟩
  | .husk, .unclear => ⟨some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]⟩
  | .snake, .nPP => ⟨some [0, 2, 2, 8, 1, 2, 1, 2, 11, 3, 4, 6, 2, 8, 4, 5, 1, 2, 17, 14, 10]⟩
  | .snake, .headClassifier =>
    ⟨some [2, 0, 0, 1, 0, 1, 3, 3, 1, 0, 0, 0, 1, 0, 4, 4, 1, 2, 7, 3, 3]⟩
  | .snake, .pseudoPartitive =>
    ⟨some [0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 2, 1, 2, 2, 1, 0, 1, 1, 14, 11, 7]⟩
  | .snake, .ebnp => ⟨some [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 1, 2, 0, 2, 2, 5, 3]⟩
  | .snake, .em => ⟨none⟩
  | .snake, .bi => ⟨none⟩
  | .snake, .unclear => ⟨some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1]⟩
  | .whale, .nPP => ⟨some [0, 0, 1, 0, 18, 3, 0, 1, 0, 1, 2, 4, 0, 3, 0, 0, 4, 2, 6, 18, 9]⟩
  | .whale, .headClassifier =>
    ⟨some [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0]⟩
  | .whale, .pseudoPartitive => ⟨none⟩
  | .whale, .ebnp => ⟨some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 11, 10, 5, 2, 5, 3, 0, 9, 3, 4]⟩
  | .whale, .em => ⟨some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 21, 6, 2, 8, 5, 2, 1, 19, 17, 10]⟩
  | .whale, .bi => ⟨some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 2, 4, 8, 4, 1, 2, 4, 5, 0]⟩
  | .whale, .unclear => ⟨some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 2, 0]⟩
  | .bitch, .nPP => ⟨some [1, 0, 1, 4, 0, 3, 0, 6, 2, 6]⟩
  | .bitch, .headClassifier => ⟨some [0, 0, 0, 0, 0, 0, 0, 2, 0, 1]⟩
  | .bitch, .pseudoPartitive => ⟨none⟩
  | .bitch, .ebnp => ⟨some [0, 2, 2, 2, 1, 2, 4, 9, 9, 9]⟩
  | .bitch, .em => ⟨some [0, 0, 0, 1, 2, 3, 4, 3, 12, 6]⟩
  | .bitch, .bi => ⟨some [0, 0, 0, 0, 0, 0, 0, 0, 1, 0]⟩
  | .bitch, .unclear => ⟨some [0, 3, 0, 0, 0, 0, 0, 0, 1, 2]⟩

end TenWolde2023
