module

public import Linglib.Data.Examples.Schema

/-!
# `Horn1972` — typed example data

Auto-generated from `Linglib/Data/Examples/Horn1972.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Horn1972.Examples`.
-/

@[expose] public section

namespace Horn1972.Examples

def ex1_58b_more : Datum :=
  { id := "horn1972_ex1_58b_more"
    source := ⟨"horn-1972", "(1.58b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John has 3 children, and indeed he may have more."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.21"), ("scale", "cardinal"), ("construction", "suspension of the upper bound"), ("base", "3")] }

def ex1_58b_fewer : Datum :=
  { id := "horn1972_ex1_58b_fewer"
    source := ⟨"horn-1972", "(1.58b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John has 3 children, and indeed he may have fewer."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.21"), ("scale", "cardinal"), ("construction", "suspension of the lower bound"), ("base", "3")] }

def ex1_59a : Datum :=
  { id := "horn1972_ex1_59a"
    source := ⟨"horn-1972", "(1.59a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John has 3 children."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.21"), ("scale", "cardinal"), ("asserts", "at least 3"), ("implicates", "at most 3")] }

def ex1_59b : Datum :=
  { id := "horn1972_ex1_59b"
    source := ⟨"horn-1972", "(1.59b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John doesn't have 3 children."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.21"), ("scale", "cardinal"), ("negation", "of the lower bound")] }

def ex1_60a : Datum :=
  { id := "horn1972_ex1_60a"
    source := ⟨"horn-1972", "(1.60a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have 3 children: in fact I have (even) more."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.21"), ("scale", "cardinal"), ("construction", "cancelling the upper bound"), ("base", "3")] }

def ex1_60b : Datum :=
  { id := "horn1972_ex1_60b"
    source := ⟨"horn-1972", "(1.60b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have only 3 children: in fact I don't (even) have that many."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.21"), ("scale", "cardinal"), ("construction", "contradicting the assertion of only"), ("base", "3")] }

def ex1_63b : Datum :=
  { id := "horn1972_ex1_63b"
    source := ⟨"horn-1972", "(1.63)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Does John have three children? — Yes, (in fact) he has four."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.21"), ("scale", "cardinal"), ("reading", "at least")] }

def ex1_63c : Datum :=
  { id := "horn1972_ex1_63c"
    source := ⟨"horn-1972", "(1.63)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Does John have three children? — No, he has four."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.21"), ("scale", "cardinal"), ("reading", "exact")] }

def ex1_72a_fact : Datum :=
  { id := "horn1972_ex1_72a_fact"
    source := ⟨"horn-1972", "(1.72a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's warm; in fact, it's hot."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.22"), ("scale", "warm–hot"), ("construction", "contradicting the implicature")] }

def ex1_72a_susp : Datum :=
  { id := "horn1972_ex1_72a_susp"
    source := ⟨"horn-1972", "(1.72a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's warm, if not hot."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.22"), ("scale", "warm–hot"), ("construction", "suspension")] }

def ex1_72b_cold : Datum :=
  { id := "horn1972_ex1_72b_cold"
    source := ⟨"horn-1972", "(1.72b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's cool, if not cold."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.22"), ("scale", "cool–cold"), ("construction", "suspension")] }

def ex1_72b_warm : Datum :=
  { id := "horn1972_ex1_72b_warm"
    source := ⟨"horn-1972", "(1.72b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's cool, if not warm."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.22"), ("scale", "cool–cold"), ("construction", "suspension across scales")] }

def ex1_73c_hot_warm : Datum :=
  { id := "horn1972_ex1_73c_hot_warm"
    source := ⟨"horn-1972", "(1.73c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "hot if not warm"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.22"), ("scale", "warm–hot"), ("construction", "suspension by a weaker member")] }

def ex1_82a : Datum :=
  { id := "horn1972_ex1_82a"
    source := ⟨"horn-1972", "(1.82a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dolores is pretty, if not beautiful."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.22"), ("scale", "pretty–beautiful"), ("construction", "suspension"), ("intonation", "rising")] }

def ex1_82b : Datum :=
  { id := "horn1972_ex1_82b"
    source := ⟨"horn-1972", "(1.82b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dolores is pretty, if not intelligent."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.22"), ("construction", "concession"), ("intonation", "falling")] }

def ex1_85a : Datum :=
  { id := "horn1972_ex1_85a"
    source := ⟨"horn-1972", "(1.85a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dolores is pretty if not downright beautiful."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.22"), ("construction", "suspension"), ("polarity item", "positive")] }

def ex1_85b : Datum :=
  { id := "horn1972_ex1_85b"
    source := ⟨"horn-1972", "(1.85b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dolores is pretty if not exactly beautiful."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.22"), ("construction", "concession"), ("polarity item", "negative")] }

def ex1_93_ok : Datum :=
  { id := "horn1972_ex1_93_ok"
    source := ⟨"horn-1972", "(1.93)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "seriously if not critically wounded"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.23"), ("scale", "seriously–critically–fatally wounded"), ("construction", "suspension")] }

def ex1_93_bad : Datum :=
  { id := "horn1972_ex1_93_bad"
    source := ⟨"horn-1972", "(1.93)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "critically if not seriously wounded"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.23"), ("scale", "seriously–critically–fatally wounded"), ("construction", "suspension by a weaker member")] }

def ex2_1a_some_all : Datum :=
  { id := "horn1972_ex2_1a_some_all"
    source := ⟨"horn-1972", "(2.1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "some if not all"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.11"), ("scale", "quantifier"), ("construction", "suspension")] }

def ex2_1a_all_some : Datum :=
  { id := "horn1972_ex2_1a_all_some"
    source := ⟨"horn-1972", "(2.1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "all if not some"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.11"), ("scale", "quantifier"), ("construction", "suspension by a weaker member")] }

def ex2_1a_many_most : Datum :=
  { id := "horn1972_ex2_1a_many_most"
    source := ⟨"horn-1972", "(2.1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "many if not most"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.11"), ("scale", "quantifier"), ("construction", "suspension")] }

def ex2_1b : Datum :=
  { id := "horn1972_ex2_1b"
    source := ⟨"horn-1972", "(2.1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "sometimes if not often / usually / always"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.11"), ("scale", "quantificational adverb"), ("construction", "suspension")] }

def ex2_1e_few : Datum :=
  { id := "horn1972_ex2_1e_few"
    source := ⟨"horn-1972", "(2.1e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "few if any"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.11"), ("scale", "negative quantifier"), ("construction", "suspension")] }

def ex2_3c : Datum :=
  { id := "horn1972_ex2_3c"
    source := ⟨"horn-1972", "(2.3c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Desdemona is pretty or (even) beautiful, or both."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.11"), ("construction", "or both after a suspender disjunction")] }

def ex2_3a : Datum :=
  { id := "horn1972_ex2_3a"
    source := ⟨"horn-1972", "(2.3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Desdemona loves Othello or Cassio, or both."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.11"), ("construction", "or both after a true disjunction")] }

def ex2_24a_somebody : Datum :=
  { id := "horn1972_ex2_24a_somebody"
    source := ⟨"horn-1972", "(2.24a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Somebody left, in fact everyone did."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.11"), ("scale", "quantifier"), ("construction", "cancelling the implicature")] }

def ex2_24b_some_not_all : Datum :=
  { id := "horn1972_ex2_24b_some_not_all"
    source := ⟨"horn-1972", "(2.24b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some but not all of my best friends are women."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.11"), ("scale", "quantifier"), ("construction", "asserting the implicature")] }

def ex2_25a : Datum :=
  { id := "horn1972_ex2_25a"
    source := ⟨"horn-1972", "(2.25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Few of the arrows hit the target, but some did."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.11"), ("scale", "negative quantifier"), ("construction", "asserting the implicature")] }

def ex2_28a : Datum :=
  { id := "horn1972_ex2_28a"
    source := ⟨"horn-1972", "(2.28a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't have three friends."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.11"), ("scale", "cardinal"), ("negation", "of the lower bound")] }

def ex2_28b : Datum :=
  { id := "horn1972_ex2_28b"
    source := ⟨"horn-1972", "(2.28b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't have three friends (...but four)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.11"), ("scale", "cardinal"), ("negation", "external")] }

def ex2_40a : Datum :=
  { id := "horn1972_ex2_40a"
    source := ⟨"horn-1972", "(2.40a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All (of) the boys didn't go."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.13"), ("ambiguity", "NEG-V vs NEG-Q")] }

def ex2_43a : Datum :=
  { id := "horn1972_ex2_43a"
    source := ⟨"horn-1972", "(2.43a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some of the boys didn't go."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.13"), ("reading", "NEG-V only")] }

def ex2_46 : Datum :=
  { id := "horn1972_ex2_46"
    source := ⟨"horn-1972", "(2.46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John left and Bill left. / John left or Bill left."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.13"), ("scale", "connective"), ("entails", "and entails or"), ("implicates", "or implicates not and")] }

def ex2_47 : Datum :=
  { id := "horn1972_ex2_47"
    source := ⟨"horn-1972", "(2.47)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you see John or Bill, let me know. — I saw both John and Bill."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.13"), ("scale", "connective"), ("context", "conditional")] }

def ex2_49b : Datum :=
  { id := "horn1972_ex2_49b"
    source := ⟨"horn-1972", "(2.49b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Claude will major in linguistics or necromancy, if not both."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.13"), ("scale", "connective"), ("construction", "suspension of exclusivity")] }

def ex2_51a : Datum :=
  { id := "horn1972_ex2_51a"
    source := ⟨"horn-1972", "(2.51a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some Americans smoke cigars."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.14"), ("scale", "quantifier"), ("status", "understatement")] }

def ex2_51d : Datum :=
  { id := "horn1972_ex2_51d"
    source := ⟨"horn-1972", "(2.51d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some Americans are earthlings."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.14"), ("scale", "quantifier"), ("status", "anomaly")] }

def ex2_52a : Datum :=
  { id := "horn1972_ex2_52a"
    source := ⟨"horn-1972", "(2.52a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some men are mortal."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.14"), ("scale", "quantifier"), ("status", "anomaly")] }

def ex2_55c : Datum :=
  { id := "horn1972_ex2_55c"
    source := ⟨"horn-1972", "(2.55c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some natural numbers are integers."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.14"), ("scale", "quantifier"), ("status", "anomaly")] }

def ex2_58a : Datum :=
  { id := "horn1972_ex2_58a"
    source := ⟨"horn-1972", "(2.58a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Almost all men are mammals."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.14"), ("scale", "quantifier"), ("status", "anomaly")] }

def ex2_58c : Datum :=
  { id := "horn1972_ex2_58c"
    source := ⟨"horn-1972", "(2.58c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some Austrians speak German."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.14"), ("scale", "quantifier"), ("status", "understatement")] }

def ex4_49a : Datum :=
  { id := "horn1972_ex4_49a"
    source := ⟨"horn-1972", "(4.49a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John isn't tall and he isn't handsome. / John isn't tall nor is he handsome."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.23"), ("connective", "and"), ("lexicalization", "nor = and~"), ("route", "inner")] }

def ex4_49a_prime : Datum :=
  { id := "horn1972_ex4_49a_prime"
    source := ⟨"horn-1972", "(4.49a')"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John isn't tall or he isn't handsome. / *John isn't tall nand is he handsome."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.23"), ("connective", "or"), ("lexicalization", "*nand = or~"), ("route", "inner")] }

def ex4_50a : Datum :=
  { id := "horn1972_ex4_50a"
    source := ⟨"horn-1972", "(4.50a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John and Mary came in, but neither of them stayed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.23"), ("connective", "both"), ("lexicalization", "neither = both~"), ("route", "inner")] }

def ex4_50a_prime : Datum :=
  { id := "horn1972_ex4_50a_prime"
    source := ⟨"horn-1972", "(4.50a')"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John and Mary came in, but *noth of them stayed."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.23"), ("connective", "either"), ("lexicalization", "*noth = not both"), ("route", "inner")] }

def ex4_56a : Datum :=
  { id := "horn1972_ex4_56a"
    source := ⟨"horn-1972", "(4.56a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All the eggs broke, and all of them didn't."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.24"), ("quantifier", "all"), ("compatibility", "incompatible with a lower negation")] }

def ex4_56b : Datum :=
  { id := "horn1972_ex4_56b"
    source := ⟨"horn-1972", "(4.56b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most of the eggs broke, and most of them didn't."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.24"), ("quantifier", "most"), ("compatibility", "incompatible with a lower negation")] }

def ex4_56c : Datum :=
  { id := "horn1972_ex4_56c"
    source := ⟨"horn-1972", "(4.56c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Half of the eggs broke, and half of them didn't."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.24"), ("quantifier", "half"), ("compatibility", "compatible with a lower negation")] }

def ex4_56e : Datum :=
  { id := "horn1972_ex4_56e"
    source := ⟨"horn-1972", "(4.56e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some of the eggs broke, and some of them didn't."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.24"), ("quantifier", "some"), ("compatibility", "compatible with a lower negation")] }

def ex4_57a : Datum :=
  { id := "horn1972_ex4_57a"
    source := ⟨"horn-1972", "(4.57a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Many of the eggs broke and many didn't."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.24"), ("quantifier", "many"), ("compatibility", "compatible with a lower negation")] }

def ex4_57a_prime : Datum :=
  { id := "horn1972_ex4_57a_prime"
    source := ⟨"horn-1972", "(4.57a')"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not many of the eggs broke and not many didn't."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.24"), ("quantifier", "not many"), ("compatibility", "incompatible with a lower negation")] }

def ex4_60a : Datum :=
  { id := "horn1972_ex4_60a"
    source := ⟨"horn-1972", "(4.60a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some have greatness thrust upon them."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("quantifier", "some"), ("implicates", "not all"), ("lexicalization", "~some = none; some~ unlexicalized")] }

def ex4_60b : Datum :=
  { id := "horn1972_ex4_60b"
    source := ⟨"horn-1972", "(4.60b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's possible for aardvarks to eat spiders."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("modal", "possible"), ("implicates", "not necessary"), ("lexicalization", "~possible = impossible; possible~ unlexicalized")] }

def ex4_60f : Datum :=
  { id := "horn1972_ex4_60f"
    source := ⟨"horn-1972", "(4.60f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either Yvonne or Yvette will marry Sam."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("connective", "either...or"), ("implicates", "not both"), ("lexicalization", "~(either...or) = neither...nor"), ("route", "outer")] }

def ex4_66a : Datum :=
  { id := "horn1972_ex4_66a"
    source := ⟨"horn-1972", "(4.66a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I allow you to leave and I allow you to stay."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("predicate", "allow"), ("compatibility", "compatible"), ("lexicalization", "~allow = disallow")] }

def ex4_66b : Datum :=
  { id := "horn1972_ex4_66b"
    source := ⟨"horn-1972", "(4.66b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I proved that you left and I proved that you stayed."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("predicate", "prove"), ("compatibility", "incompatible"), ("lexicalization", "prove~ = disprove")] }

def ex4_75 : Datum :=
  { id := "horn1972_ex4_75"
    source := ⟨"horn-1972", "(4.75)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's true that this is the last example, and it's true that it isn't."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("predicate", "true"), ("compatibility", "incompatible"), ("lexicalization", "true~ = false; ~true = untrue")] }

def all : List Datum := [ex1_58b_more, ex1_58b_fewer, ex1_59a, ex1_59b, ex1_60a, ex1_60b, ex1_63b, ex1_63c, ex1_72a_fact, ex1_72a_susp, ex1_72b_cold, ex1_72b_warm, ex1_73c_hot_warm, ex1_82a, ex1_82b, ex1_85a, ex1_85b, ex1_93_ok, ex1_93_bad, ex2_1a_some_all, ex2_1a_all_some, ex2_1a_many_most, ex2_1b, ex2_1e_few, ex2_3c, ex2_3a, ex2_24a_somebody, ex2_24b_some_not_all, ex2_25a, ex2_28a, ex2_28b, ex2_40a, ex2_43a, ex2_46, ex2_47, ex2_49b, ex2_51a, ex2_51d, ex2_52a, ex2_55c, ex2_58a, ex2_58c, ex4_49a, ex4_49a_prime, ex4_50a, ex4_50a_prime, ex4_56a, ex4_56b, ex4_56c, ex4_56e, ex4_57a, ex4_57a_prime, ex4_60a, ex4_60b, ex4_60f, ex4_66a, ex4_66b, ex4_75]

end Horn1972.Examples
