module

public import Linglib.Data.Examples.Schema

/-!
# `BarLevFox2020` — typed example data

Auto-generated from `Linglib/Data/Examples/BarLevFox2020.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BarLevFox2020.Examples`.
-/

@[expose] public section

namespace BarLevFox2020.Examples

def ex_1 : Datum :=
  { id := "barlevfox2020_1"
    source := ⟨"bar-lev-fox-2020", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is allowed to eat ice cream or cake."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("Mary is allowed to eat ice cream", .acceptable), ("Mary is allowed to eat cake", .acceptable)]
    paperFeatures := [("form", "◇(a ∨ b)"), ("inference", "free choice")] }

def ex_6 : Datum :=
  { id := "barlevfox2020_6"
    source := ⟨"bar-lev-fox-2020", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John isn't allowed to eat ice cream or cake."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("John is allowed to eat neither", .acceptable)]
    paperFeatures := [("form", "¬◇(a ∨ b)")] }

def ex_7 : Datum :=
  { id := "barlevfox2020_7"
    source := ⟨"bar-lev-fox-2020", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is allowed to eat ice cream or cake, and John isn't allowed to eat ice cream or cake."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("Mary is allowed to eat ice cream and allowed to eat cake", .acceptable), ("John isn't allowed to eat ice cream and he isn't allowed to eat cake", .acceptable)]
    paperFeatures := [("construction", "VP-ellipsis")] }

def ex_8 : Datum :=
  { id := "barlevfox2020_8"
    source := ⟨"bar-lev-fox-2020", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary solved some of the problems, and John didn't solve some of the problems."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("Mary solved some but not all of the problems", .acceptable), ("John didn't solve any of the problems", .acceptable)]
    paperFeatures := [("construction", "VP-ellipsis")] }

def ex_9 : Datum :=
  { id := "barlevfox2020_9"
    source := ⟨"bar-lev-fox-2020", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary ate ice cream or cake."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("Mary didn't eat both ice cream and cake", .acceptable)]
    paperFeatures := [("form", "a ∨ b"), ("alternatives", "{a ∨ b, a, b, a ∧ b}")] }

def ex_10 : Datum :=
  { id := "barlevfox2020_10"
    source := ⟨"bar-lev-fox-2020", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is allowed to eat ice cream or cake."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("Mary is allowed to eat ice cream and allowed to eat cake", .acceptable)]
    paperFeatures := [("form", "◇(a ∨ b)"), ("alternatives", "{◇(a ∨ b), ◇a, ◇b, ◇(a ∧ b)}")] }

def ex_33 : Datum :=
  { id := "barlevfox2020_33"
    source := ⟨"bar-lev-fox-2020", "(33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We are only allowed to eat [ice cream or cake]F."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("We are allowed to eat ice cream", .acceptable), ("We are allowed to eat cake", .acceptable)]
    paperFeatures := [("construction", "only"), ("inference", "presupposition")] }

def ex_34 : Datum :=
  { id := "barlevfox2020_34"
    source := ⟨"bar-lev-fox-2020", "(34)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Are we only allowed to eat [ice cream or cake]F?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("We are allowed to eat ice cream", .acceptable), ("We are allowed to eat cake", .acceptable)]
    paperFeatures := [("construction", "only"), ("construction", "polar question")] }

def ex_35 : Datum :=
  { id := "barlevfox2020_35"
    source := ⟨"bar-lev-fox-2020", "(35)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Are we allowed to eat ice cream or cake?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("We are allowed to eat ice cream", .unacceptable), ("We are allowed to eat cake", .unacceptable)]
    paperFeatures := [("construction", "polar question")] }

def ex_36 : Datum :=
  { id := "barlevfox2020_36"
    source := ⟨"bar-lev-fox-2020", "(36)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every boy is allowed to eat ice cream or cake."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("Every boy is allowed to eat ice cream", .acceptable), ("Every boy is allowed to eat cake", .acceptable)]
    paperFeatures := [("form", "∀x ◇(Px ∨ Qx)"), ("inference", "universal free choice")] }

def ex_37 : Datum :=
  { id := "barlevfox2020_37"
    source := ⟨"bar-lev-fox-2020", "(37)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No student is required to solve both problem A and problem B."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("No student is required to solve problem A", .acceptable), ("No student is required to solve problem B", .acceptable)]
    paperFeatures := [("form", "¬∃x □(Px ∧ Qx)"), ("inference", "universal free choice")] }

def ex_38 : Datum :=
  { id := "barlevfox2020_38"
    source := ⟨"bar-lev-fox-2020", "(38)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every girl is allowed to eat ice cream or cake on her birthday. Interestingly, no boy is allowed to eat ice cream or cake on his birthday."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("Every girl is allowed to eat ice cream and allowed to eat cake on her birthday", .acceptable), ("No boy is allowed to eat ice cream and no boy is allowed to eat cake on his birthday", .acceptable), ("No boy is both allowed to eat ice cream and allowed to eat cake on his birthday", .unacceptable)]
    paperFeatures := [("construction", "VP-ellipsis")] }

def ex_48 : Datum :=
  { id := "barlevfox2020_48"
    source := ⟨"bar-lev-fox-2020", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every one of these people is singing or dancing."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("At least one of these people is singing", .acceptable), ("At least one of these people is dancing", .acceptable)]
    paperFeatures := [("form", "∀x(Px ∨ Qx)"), ("inference", "distributive")] }

def ex_49 : Datum :=
  { id := "barlevfox2020_49"
    source := ⟨"bar-lev-fox-2020", "(49)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You are required to solve problem A or problem B."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("You are not required to solve problem A", .acceptable), ("You are not required to solve problem B", .acceptable)]
    paperFeatures := [("form", "□(p ∨ q)")] }

def ex_53 : Datum :=
  { id := "barlevfox2020_53"
    source := ⟨"bar-lev-fox-2020", "(53)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The teacher is OK with every student either talking to Mary or to Sue."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("The teacher is OK with every student talking to Mary", .acceptable), ("The teacher is OK with every student talking to Sue", .acceptable)]
    paperFeatures := [("form", "◇∀x(Px ∨ Qx)")] }

def ex_54 : Datum :=
  { id := "barlevfox2020_54"
    source := ⟨"bar-lev-fox-2020", "(54)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every kid ate ice cream or cake."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("Every kid ate ice cream", .unacceptable), ("Every kid ate cake", .unacceptable)]
    paperFeatures := [("form", "∀x(Px ∨ Qx)")] }

def ex_59 : Datum :=
  { id := "barlevfox2020_59"
    source := ⟨"bar-lev-fox-2020", "(59)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Betty can balance a fishing rod on her nose or on her chin."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("Betty can balance a fishing rod on her nose", .acceptable), ("Betty can balance a fishing rod on her chin", .acceptable)]
    paperFeatures := [("form", "∃p ∀w∈p (Pw ∨ Qw)"), ("modal", "ability")] }

def ex_61 : Datum :=
  { id := "barlevfox2020_61"
    source := ⟨"bar-lev-fox-2020", "(61)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you eat ice cream or cake, you will feel guilty."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("If you eat ice cream, you will feel guilty", .acceptable), ("If you eat cake, you will feel guilty", .acceptable)]
    paperFeatures := [("form", "(p ∨ q) □→ r"), ("inference", "simplification of disjunctive antecedents")] }

def ex_68 : Datum :=
  { id := "barlevfox2020_68"
    source := ⟨"bar-lev-fox-2020", "(68)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you eat an apple, an orange, or a pear, you will be healthy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("If you eat an apple you will be healthy", .acceptable), ("If you eat an orange you will be healthy", .acceptable), ("If you eat a pear you will be healthy", .acceptable)]
    paperFeatures := [("form", "(p ∨ q ∨ r) □→ s")] }

def ex_69 : Datum :=
  { id := "barlevfox2020_69"
    source := ⟨"bar-lev-fox-2020", "(69)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone will feel guilty if they eat ice cream or cake."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("Everyone will feel guilty if they eat ice cream", .acceptable), ("Everyone will feel guilty if they eat cake", .acceptable)]
    paperFeatures := [("form", "∀x((Px ∨ Qx) □→ Rx)")] }

def ex_70 : Datum :=
  { id := "barlevfox2020_70"
    source := ⟨"bar-lev-fox-2020", "(70)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not true that you will feel guilty if you eat ice cream or cake."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("It's not true that you will feel guilty if you eat ice cream", .acceptable), ("It's not true that you will feel guilty if you eat cake", .acceptable)]
    paperFeatures := [("form", "¬((p ∨ q) □→ r)")] }

def ex_71 : Datum :=
  { id := "barlevfox2020_71"
    source := ⟨"bar-lev-fox-2020", "(71)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Spain had fought with the Axis or with the Allies, it would have been with the Axis."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("If Spain had fought with the Axis it would have been with the Axis", .acceptable), ("If Spain had fought with the Allies it would have been with the Axis", .unacceptable)]
    paperFeatures := [("form", "(p ∨ q) □→ p")] }

def ex_72 : Datum :=
  { id := "barlevfox2020_72"
    source := ⟨"bar-lev-fox-2020", "(72)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Spain had fought with the Axis or with the Allies, Hitler would have been pleased."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := [("If Spain had fought with the Axis, Hitler would have been pleased", .acceptable), ("If Spain had fought with the Allies, Hitler would have been pleased", .unacceptable)]
    paperFeatures := [("form", "(p ∨ q) □→ r")] }

def ex_76 : Datum :=
  { id := "barlevfox2020_76"
    source := ⟨"bar-lev-fox-2020", "(76)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If switch A or switch B were down, the light would be off."
    glossedTokens := []
    context := "Both switches are up and the light is on; with exactly one switch down the light would be off; with both down it would be on."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("form", "(p̄ ∨ q̄) □→ r")] }

def ex_77 : Datum :=
  { id := "barlevfox2020_77"
    source := ⟨"bar-lev-fox-2020", "(77)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If switch A and switch B were not both up, the light would be off."
    glossedTokens := []
    context := "Both switches are up and the light is on; with exactly one switch down the light would be off; with both down it would be on."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("form", "(¬(p ∧ q)) □→ r")] }

def ex_78 : Datum :=
  { id := "barlevfox2020_78"
    source := ⟨"bar-lev-fox-2020", "(78)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If switch A or switch B or both were down, the light would be off."
    glossedTokens := []
    context := "Both switches are up and the light is on; with exactly one switch down the light would be off; with both down it would be on."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("form", "(Exh(p̄ ∨ q̄) ∨ (p̄ ∧ q̄)) □→ r")] }

def ex_85 : Datum :=
  { id := "barlevfox2020_85"
    source := ⟨"bar-lev-fox-2020", "(85)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most students in linguistics or philosophy took Advanced Syntax."
    glossedTokens := []
    context := "35 of the 40 linguistics students and 2 of the 30 philosophy students took Advanced Syntax; no student is in both."
    judgment := .acceptable
    contrasts := []
    readings := [("Most students in linguistics took Advanced Syntax", .acceptable), ("Most students in philosophy took Advanced Syntax", .acceptable)]
    paperFeatures := [("form", "Most(P ∪ Q)(R)")] }

def ex_91 : Datum :=
  { id := "barlevfox2020_91"
    source := ⟨"bar-lev-fox-2020", "(91)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some boys are allowed to eat ice cream or cake."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("Some boys are both allowed to eat ice cream and allowed to eat cake", .acceptable)]
    paperFeatures := [("form", "∃x ◇(Px ∨ Qx)")] }

def ex_92 : Datum :=
  { id := "barlevfox2020_92"
    source := ⟨"bar-lev-fox-2020", "(92)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not every student is required to solve both problem A and problem B."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("Not every student is required to solve problem A", .acceptable), ("Not every student is required to solve problem B", .acceptable), ("Some student is allowed to avoid solving problem A and allowed to avoid solving problem B", .unacceptable)]
    paperFeatures := [("form", "¬∀x □(Px ∧ Qx)")] }

def ex_93 : Datum :=
  { id := "barlevfox2020_93"
    source := ⟨"bar-lev-fox-2020", "(93)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some girls are allowed to eat ice cream or cake on their birthday. Interestingly, no boys are allowed to eat ice cream or cake on their birthday."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("Some girls are both allowed to eat ice cream and allowed to eat cake on their birthday", .acceptable), ("No boys are allowed to eat ice cream and no boys are allowed to eat cake on their birthday", .acceptable)]
    paperFeatures := [("construction", "VP-ellipsis")] }

def all : List Datum := [ex_1, ex_6, ex_7, ex_8, ex_9, ex_10, ex_33, ex_34, ex_35, ex_36, ex_37, ex_38, ex_48, ex_49, ex_53, ex_54, ex_59, ex_61, ex_68, ex_69, ex_70, ex_71, ex_72, ex_76, ex_77, ex_78, ex_85, ex_91, ex_92, ex_93]

end BarLevFox2020.Examples
