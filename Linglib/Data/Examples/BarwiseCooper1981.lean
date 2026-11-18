module

public import Linglib.Data.Examples.Schema

/-!
# `BarwiseCooper1981` — typed example data

Auto-generated from `Linglib/Data/Examples/BarwiseCooper1981.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BarwiseCooper1981.Examples`.
-/

@[expose] public section

namespace BarwiseCooper1981.Examples

def ex_6a : Datum :=
  { id := "barwisecooper1981_6a"
    source := ⟨"barwise-cooper-1981", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Harry sneezed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("np", "proper name")] }

def ex_6b : Datum :=
  { id := "barwisecooper1981_6b"
    source := ⟨"barwise-cooper-1981", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some person sneezed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "some")] }

def ex_6c : Datum :=
  { id := "barwisecooper1981_6c"
    source := ⟨"barwise-cooper-1981", "(6c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every man sneezed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "every")] }

def ex_6d : Datum :=
  { id := "barwisecooper1981_6d"
    source := ⟨"barwise-cooper-1981", "(6d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most babies sneeze."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "most")] }

def ex_21 : Datum :=
  { id := "barwisecooper1981_21"
    source := ⟨"barwise-cooper-1981", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No boy at the party kissed Mary."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "no"), ("class", "weak")] }

def ex_22 : Datum :=
  { id := "barwisecooper1981_22"
    source := ⟨"barwise-cooper-1981", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There were boys at the party."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "there-sentence")] }

def ex_23 : Datum :=
  { id := "barwisecooper1981_23"
    source := ⟨"barwise-cooper-1981", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No boy at the party kissed Mary since there weren't any boys at the party."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "no"), ("class", "weak")] }

def ex_24a : Datum :=
  { id := "barwisecooper1981_24a"
    source := ⟨"barwise-cooper-1981", "(24a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every man at the party kissed Mary."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "every"), ("class", "strong")] }

def ex_24c : Datum :=
  { id := "barwisecooper1981_24c"
    source := ⟨"barwise-cooper-1981", "(24c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every man at the party kissed Mary, but only because there weren't any men at the party."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "every"), ("class", "strong")] }

def ex_30 : Datum :=
  { id := "barwisecooper1981_30"
    source := ⟨"barwise-cooper-1981", "(30)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If some Republican entered the race early, then some Republican entered the race."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "some"), ("monotonicity", "increasing")] }

def ex_31 : Datum :=
  { id := "barwisecooper1981_31"
    source := ⟨"barwise-cooper-1981", "(31)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If no plumber entered the race, then no plumber entered the race early."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "no"), ("monotonicity", "decreasing")] }

def ex_32 : Datum :=
  { id := "barwisecooper1981_32"
    source := ⟨"barwise-cooper-1981", "(32)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most men that love Mary, love Mary."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "most"), ("class", "positive strong")] }

def ex_33 : Datum :=
  { id := "barwisecooper1981_33"
    source := ⟨"barwise-cooper-1981", "(33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every man that loves Mary, loves Mary."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "every"), ("class", "positive strong")] }

def ex_34 : Datum :=
  { id := "barwisecooper1981_34"
    source := ⟨"barwise-cooper-1981", "(34)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Neither man that loves Mary, loves Mary."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "neither"), ("class", "negative strong")] }

def ex_35a : Datum :=
  { id := "barwisecooper1981_35a"
    source := ⟨"barwise-cooper-1981", "(35a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No man that loves Mary, loves Mary."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "no"), ("class", "weak"), ("felicity", "infelicitous")] }

def ex_35b : Datum :=
  { id := "barwisecooper1981_35b"
    source := ⟨"barwise-cooper-1981", "(35b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some man that loves Mary, loves Mary."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "some"), ("class", "weak"), ("felicity", "infelicitous")] }

def ex_36b : Datum :=
  { id := "barwisecooper1981_36b"
    source := ⟨"barwise-cooper-1981", "(36b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Few men that love Mary, love Mary."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "few"), ("class", "weak"), ("felicity", "infelicitous")] }

def ex_37a : Datum :=
  { id := "barwisecooper1981_37a"
    source := ⟨"barwise-cooper-1981", "(37a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No man loves Mary."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "no")] }

def ex_37_prime_a : Datum :=
  { id := "barwisecooper1981_37_prime_a"
    source := ⟨"barwise-cooper-1981", "(37'a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is no man that loves Mary."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "no"), ("construction", "there-sentence")] }

def ex_37_prime_prime_a : Datum :=
  { id := "barwisecooper1981_37_prime_prime_a"
    source := ⟨"barwise-cooper-1981", "(37''a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No one that loves Mary is a man."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "no")] }

def ex_4_10_32a : Datum :=
  { id := "barwisecooper1981_4_10-32a"
    source := ⟨"barwise-cooper-1981", "§4.10 (32a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A man and three women could lift this piano."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("conjunction", "increasing + increasing")] }

def ex_4_10_32b : Datum :=
  { id := "barwisecooper1981_4_10-32b"
    source := ⟨"barwise-cooper-1981", "§4.10 (32b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No man and few women could lift this piano."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("conjunction", "decreasing + decreasing")] }

def ex_4_10_32c : Datum :=
  { id := "barwisecooper1981_4_10-32c"
    source := ⟨"barwise-cooper-1981", "§4.10 (32c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John and no woman could lift this piano."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("conjunction", "mixed")] }

def ex_4_10_33a : Datum :=
  { id := "barwisecooper1981_4_10-33a"
    source := ⟨"barwise-cooper-1981", "§4.10 (33a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John was invited and no woman was, so he went home alone again."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("conjunction", "sentential")] }

def ex_4_10_33a_prime : Datum :=
  { id := "barwisecooper1981_4_10-33a_prime"
    source := ⟨"barwise-cooper-1981", "§4.10 (33a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John and no woman was invited, so he went home alone again."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("conjunction", "mixed")] }

def ex_4_10_35a : Datum :=
  { id := "barwisecooper1981_4_10-35a"
    source := ⟨"barwise-cooper-1981", "§4.10 (35a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John but no woman was invited."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("conjunction", "but, mixed")] }

def ex_4_10_36a : Datum :=
  { id := "barwisecooper1981_4_10-36a"
    source := ⟨"barwise-cooper-1981", "§4.10 (36a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John but a woman was invited."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("conjunction", "but, increasing + increasing")] }

def ex_4_10_37a : Datum :=
  { id := "barwisecooper1981_4_10-37a"
    source := ⟨"barwise-cooper-1981", "§4.10 (37a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John and a woman and three children were invited."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("conjunction", "iterated and")] }

def ex_4_10_37b : Datum :=
  { id := "barwisecooper1981_4_10-37b"
    source := ⟨"barwise-cooper-1981", "§4.10 (37b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John but no woman but three children were invited."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("conjunction", "iterated but")] }

def ex_40a : Datum :=
  { id := "barwisecooper1981_40a"
    source := ⟨"barwise-cooper-1981", "(40a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not every man left."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "every"), ("negation", "NP")] }

def ex_40b : Datum :=
  { id := "barwisecooper1981_40b"
    source := ⟨"barwise-cooper-1981", "(40b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not all men left."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "all"), ("negation", "NP")] }

def ex_40c : Datum :=
  { id := "barwisecooper1981_40c"
    source := ⟨"barwise-cooper-1981", "(40c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not a (single) man left."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "a"), ("negation", "NP")] }

def ex_40d : Datum :=
  { id := "barwisecooper1981_40d"
    source := ⟨"barwise-cooper-1981", "(40d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not one man left."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "one"), ("negation", "NP")] }

def ex_40e : Datum :=
  { id := "barwisecooper1981_40e"
    source := ⟨"barwise-cooper-1981", "(40e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not many men left."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "many"), ("negation", "NP")] }

def ex_41a : Datum :=
  { id := "barwisecooper1981_41a"
    source := ⟨"barwise-cooper-1981", "(41a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not each man left."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "each"), ("negation", "NP")] }

def ex_41b : Datum :=
  { id := "barwisecooper1981_41b"
    source := ⟨"barwise-cooper-1981", "(41b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not some man left."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "some"), ("negation", "NP")] }

def ex_41c : Datum :=
  { id := "barwisecooper1981_41c"
    source := ⟨"barwise-cooper-1981", "(41c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not John left."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("np", "proper name"), ("negation", "NP")] }

def ex_41d : Datum :=
  { id := "barwisecooper1981_41d"
    source := ⟨"barwise-cooper-1981", "(41d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not the man left."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "the"), ("negation", "NP")] }

def ex_41e : Datum :=
  { id := "barwisecooper1981_41e"
    source := ⟨"barwise-cooper-1981", "(41e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not few men left."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "few"), ("negation", "NP"), ("monotonicity", "decreasing")] }

def ex_41f : Datum :=
  { id := "barwisecooper1981_41f"
    source := ⟨"barwise-cooper-1981", "(41f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not no man left."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "no"), ("negation", "NP"), ("monotonicity", "decreasing")] }

def ex_41g : Datum :=
  { id := "barwisecooper1981_41g"
    source := ⟨"barwise-cooper-1981", "(41g)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not most men left."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "most"), ("negation", "NP")] }

def ex_42 : Datum :=
  { id := "barwisecooper1981_42"
    source := ⟨"barwise-cooper-1981", "(42)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is not true that most men left."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "most"), ("negation", "sentential")] }

def ex_43 : Datum :=
  { id := "barwisecooper1981_43"
    source := ⟨"barwise-cooper-1981", "(43)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "At least half the men didn't leave."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "at least half")] }

def ex_44a : Datum :=
  { id := "barwisecooper1981_44a"
    source := ⟨"barwise-cooper-1981", "(44a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is not true that some man didn't leave."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("every man left", .acceptable)]
    paperFeatures := [("determiner", "some")] }

def ex_44b : Datum :=
  { id := "barwisecooper1981_44b"
    source := ⟨"barwise-cooper-1981", "(44b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is not true that every man didn't leave."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("some man left", .acceptable)]
    paperFeatures := [("determiner", "every")] }

def ex_44c : Datum :=
  { id := "barwisecooper1981_44c"
    source := ⟨"barwise-cooper-1981", "(44c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is not true that most men didn't leave."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "most")] }

def ex_46 : Datum :=
  { id := "barwisecooper1981_46"
    source := ⟨"barwise-cooper-1981", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not many men left."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "many")] }

def ex_47 : Datum :=
  { id := "barwisecooper1981_47"
    source := ⟨"barwise-cooper-1981", "(47)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Quite a few men didn't leave."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "quite a few")] }

def all : List Datum := [ex_6a, ex_6b, ex_6c, ex_6d, ex_21, ex_22, ex_23, ex_24a, ex_24c, ex_30, ex_31, ex_32, ex_33, ex_34, ex_35a, ex_35b, ex_36b, ex_37a, ex_37_prime_a, ex_37_prime_prime_a, ex_4_10_32a, ex_4_10_32b, ex_4_10_32c, ex_4_10_33a, ex_4_10_33a_prime, ex_4_10_35a, ex_4_10_36a, ex_4_10_37a, ex_4_10_37b, ex_40a, ex_40b, ex_40c, ex_40d, ex_40e, ex_41a, ex_41b, ex_41c, ex_41d, ex_41e, ex_41f, ex_41g, ex_42, ex_43, ex_44a, ex_44b, ex_44c, ex_46, ex_47]

end BarwiseCooper1981.Examples
