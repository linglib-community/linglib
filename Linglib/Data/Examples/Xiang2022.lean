module

public import Linglib.Data.Examples.Schema

/-!
# `Xiang2022` — typed example data

Auto-generated from `Linglib/Data/Examples/Xiang2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Xiang2022.Examples`.
-/

@[expose] public section

namespace Xiang2022.Examples

def ex_1 : Datum :=
  { id := "xiang2022_1"
    source := ⟨"xiang-2022", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who went to the party? John and Mary."
    glossedTokens := []
    context := "A believes that among the relevant individuals only John and Mary went to the party."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("answer", "complete")] }

def ex_2 : Datum :=
  { id := "xiang2022_2"
    source := ⟨"xiang-2022", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who went to the party? Antonio did ..."
    glossedTokens := []
    context := "A believes Antonio went to the party and it is unclear who else did."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("answer", "partial"), ("contour", "rise-fall-rise")] }

def ex_3 : Datum :=
  { id := "xiang2022_3"
    source := ⟨"xiang-2022", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who went to the party? Antonio did."
    glossedTokens := []
    context := "A believes Antonio went to the party and it is unclear who else did."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("answer", "partial"), ("contour", "falling")] }

def ex_4 : Datum :=
  { id := "xiang2022_4"
    source := ⟨"xiang-2022", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Where can we go to get coffee?"
    glossedTokens := []
    context := "There are three coffee places nearby: Starbucks, Peet's, and J.P. Licks."
    judgment := .acceptable
    contrasts := [("Starbucks.", .acceptable), ("Starbucks, Peet's, and J.P. Licks.", .acceptable), ("Starbucks, Peet's, or J.P. Licks.", .acceptable)]
    readings := [("mention-some", .acceptable), ("conjunctive mention-all", .acceptable), ("disjunctive mention-all", .acceptable)]
    paperFeatures := [("modal", "can"), ("flavor", "teleological")] }

def ex_5 : Datum :=
  { id := "xiang2022_5"
    source := ⟨"xiang-2022", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John left for coffee 15 mins ago. Where could he have gone?"
    glossedTokens := []
    context := "A believes there are two coffee places nearby, Starbucks and Peet's, and that John frequents both."
    judgment := .acceptable
    contrasts := [("Starbucks.", .marginal), ("Starbucks or Peet's.", .acceptable)]
    readings := []
    paperFeatures := [("modal", "could"), ("flavor", "epistemic")] }

def ex_6 : Datum :=
  { id := "xiang2022_6"
    source := ⟨"xiang-2022", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Where should I get coffee?"
    glossedTokens := []
    context := "A believes there are two coffee places nearby, Starbucks and Peet's."
    judgment := .acceptable
    contrasts := [("Starbucks.", .marginal), ("Starbucks or Peet's. (Either is good.)", .acceptable)]
    readings := []
    paperFeatures := [("modal", "should"), ("force", "universal")] }

def ex_7 : Datum :=
  { id := "xiang2022_7"
    source := ⟨"xiang-2022", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who can teach Psycholinguistics? Judy can."
    glossedTokens := []
    context := "The hiring committee wants to prioritize the candidates on the long-list who can teach Psycholinguistics."
    judgment := .acceptable
    contrasts := []
    readings := [("mention-all", .acceptable)]
    paperFeatures := [("modal", "can"), ("goal", "exhaustive")] }

def ex_8 : Datum :=
  { id := "xiang2022_8"
    source := ⟨"xiang-2022", "(58)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which child came?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("only one of the children came", .acceptable)]
    paperFeatures := [("wh", "singular"), ("inference", "uniqueness")] }

def ex_9 : Datum :=
  { id := "xiang2022_9"
    source := ⟨"xiang-2022", "(60a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which children came?"
    glossedTokens := []
    context := "Among the children under consideration only Andy and Billy came; the speaker knows multiple children came but not who."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("wh", "plural")] }

def ex_10 : Datum :=
  { id := "xiang2022_10"
    source := ⟨"xiang-2022", "(60b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which child came?"
    glossedTokens := []
    context := "Among the children under consideration only Andy and Billy came; the speaker knows multiple children came but not who."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("wh", "singular")] }

def ex_11 : Datum :=
  { id := "xiang2022_11"
    source := ⟨"xiang-2022", "(61)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which textbook should I use for this class? Heim & Kratzer or Meaning & Grammar. (The choice is up to you.)"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("narrow-scope disjunction", .acceptable)]
    paperFeatures := [("wh", "singular"), ("answer", "higher-order disjunction")] }

def ex_12 : Datum :=
  { id := "xiang2022_12"
    source := ⟨"xiang-2022", "(62)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which textbook can I use for this class?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Heim & Kratzer or Meaning & Grammar.", .acceptable), ("Heim & Kratzer and Meaning & Grammar.", .unacceptable)]
    readings := []
    paperFeatures := [("wh", "singular"), ("asymmetry", "disjunction-conjunction")] }

def ex_13 : Datum :=
  { id := "xiang2022_13"
    source := ⟨"xiang-2022", "(68a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which letter could we add to fo_m (to form a word)? A or r."
    glossedTokens := []
    context := "A multiple-choice context in which each choice involves a single letter, either a or r."
    judgment := .acceptable
    contrasts := []
    readings := [("local uniqueness", .acceptable)]
    paperFeatures := [("modal", "could"), ("inference", "local uniqueness")] }

def ex_14 : Datum :=
  { id := "xiang2022_14"
    source := ⟨"xiang-2022", "(69)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which chapter do we have to assign (to the students)?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("we are not allowed to assign more than one chapter", .acceptable)]
    paperFeatures := [("modal", "have to"), ("inference", "local uniqueness")] }

def ex_15 : Datum :=
  { id := "xiang2022_15"
    source := ⟨"xiang-2022", "(83)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I know which chapter we can assign (to the students next week) ..., Chap. 3."
    glossedTokens := []
    context := "The book has three chapters. The instructor has told the speaker, a TA, that they could assign either Chap. 1, or Chap. 2, or both Chaps. 2 and 3 next week."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "can"), ("inference", "local uniqueness")] }

def ex_16 : Datum :=
  { id := "xiang2022_16"
    source := ⟨"xiang-2022", "(84b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I know which SINgle chapter we can assign ..., Chap. 1."
    glossedTokens := []
    context := "As in (83)."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "can"), ("exhaustification", "local")] }

def ex_17 : Datum :=
  { id := "xiang2022_17"
    source := ⟨"xiang-2022", "(85)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We should assign one or two papers. Got it. Which paper could we assign?"
    glossedTokens := []
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "could"), ("inference", "local uniqueness")] }

def ex_18 : Datum :=
  { id := "xiang2022_18"
    source := ⟨"xiang-2022", "(86)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We should assign a journal article or a book chapter. Got it. Which journal article could we assign?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "could")] }

def ex_19 : Datum :=
  { id := "xiang2022_19"
    source := ⟨"xiang-2022", "(102)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which chapter do we have to assign? Chap. 1."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("global uniqueness", .acceptable)]
    paperFeatures := [("modal", "have to"), ("interpretation", "first-order")] }

def ex_20 : Datum :=
  { id := "xiang2022_20"
    source := ⟨"xiang-2022", "(103)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which chapter do we have to assign? Chap. 1 or Chap. 2, either is good."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("local uniqueness", .acceptable)]
    paperFeatures := [("modal", "have to"), ("interpretation", "narrow-scope higher-order")] }

def ex_21 : Datum :=
  { id := "xiang2022_21"
    source := ⟨"xiang-2022", "(105b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which chapter can we assign?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("universal local uniqueness", .acceptable)]
    paperFeatures := [("modal", "can"), ("interpretation", "mention-some")] }

def ex_22 : Datum :=
  { id := "xiang2022_22"
    source := ⟨"xiang-2022", "(106)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which SINgle chapter can we assign?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("existential local uniqueness", .acceptable)]
    paperFeatures := [("modal", "can"), ("exhaustification", "local")] }

def ex_23 : Datum :=
  { id := "xiang2022_23"
    source := ⟨"xiang-2022", "(107)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which chapter can we assign?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Chap. 1 or Chap. 2.", .acceptable), ("Chap. 1 and Chap. 2.", .unacceptable)]
    readings := [("disjunctive mention-all", .acceptable)]
    paperFeatures := [("modal", "can"), ("wh", "singular")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, ex_10, ex_11, ex_12, ex_13, ex_14, ex_15, ex_16, ex_17, ex_18, ex_19, ex_20, ex_21, ex_22, ex_23]

end Xiang2022.Examples
