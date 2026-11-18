module

public import Linglib.Data.Examples.Schema

/-!
# `Enguehard2024` — typed example data

Auto-generated from `Linglib/Data/Examples/Enguehard2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Enguehard2024.Examples`.
-/

@[expose] public section

namespace Enguehard2024.Examples

def ex_1a : Datum :=
  { id := "enguehard2024_1a"
    source := ⟨"enguehard-2024", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is a blue circle on the card."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("number", "sg"), ("polarity", "positive"), ("inference", "one")] }

def ex_1b : Datum :=
  { id := "enguehard2024_1b"
    source := ⟨"enguehard-2024", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There are blue circles on the card."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("number", "pl"), ("polarity", "positive"), ("inference", "atLeastTwo")] }

def ex_2a : Datum :=
  { id := "enguehard2024_2a"
    source := ⟨"enguehard-2024", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There isn't any blue circle on the card."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("number", "sg"), ("polarity", "negated"), ("inference", "zero")] }

def ex_2b : Datum :=
  { id := "enguehard2024_2b"
    source := ⟨"enguehard-2024", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There aren't any blue circles on the card."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("number", "pl"), ("polarity", "negated"), ("inference", "zero")] }

def ex_3a : Datum :=
  { id := "enguehard2024_3a"
    source := ⟨"enguehard-2024", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is no blue circle on the card."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("number", "sg"), ("polarity", "negative"), ("inference", "zero")] }

def ex_3b : Datum :=
  { id := "enguehard2024_3b"
    source := ⟨"enguehard-2024", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There are no blue circles on the card."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("number", "pl"), ("polarity", "negative"), ("inference", "zero")] }

def ex_4 : Datum :=
  { id := "enguehard2024_4"
    source := ⟨"enguehard-2024", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There are two blue circles on the card."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_5a : Datum :=
  { id := "enguehard2024_5a"
    source := ⟨"enguehard-2024", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This book has no table of contents."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("noun", "tableOfContents"), ("number", "sg")] }

def ex_5b : Datum :=
  { id := "enguehard2024_5b"
    source := ⟨"enguehard-2024", "(5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This book has no tables of contents."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("noun", "tableOfContents"), ("number", "pl")] }

def ex_6a : Datum :=
  { id := "enguehard2024_6a"
    source := ⟨"enguehard-2024", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This book has no chapter."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("noun", "chapters"), ("number", "sg")] }

def ex_6b : Datum :=
  { id := "enguehard2024_6b"
    source := ⟨"enguehard-2024", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This book has no chapters."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("noun", "chapters"), ("number", "pl")] }

def ex_9ai : Datum :=
  { id := "enguehard2024_9ai"
    source := ⟨"enguehard-2024", "(9a.i)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Do you have children?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_9aii : Datum :=
  { id := "enguehard2024_9aii"
    source := ⟨"enguehard-2024", "(9a.ii)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Do you have a child?"
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_9bi : Datum :=
  { id := "enguehard2024_9bi"
    source := ⟨"enguehard-2024", "(9b.i)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Do you have a child on our baseball team?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_9bii : Datum :=
  { id := "enguehard2024_9bii"
    source := ⟨"enguehard-2024", "(9b.ii)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Do you have children on our baseball team?"
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_12a : Datum :=
  { id := "enguehard2024_12a"
    source := ⟨"enguehard-2024", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I arrived late at the seminar and all the seats were taken, so I went to have a look in the surrounding rooms, but there was no chair anywhere."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_12b : Datum :=
  { id := "enguehard2024_12b"
    source := ⟨"enguehard-2024", "(12b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I arrived late at the seminar and all the seats were taken, so I went to have a look in the surrounding rooms, but there were no chairs anywhere."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_13 : Datum :=
  { id := "enguehard2024_13"
    source := ⟨"enguehard-2024", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is no bathroom here. It's upstairs."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_14 : Datum :=
  { id := "enguehard2024_14"
    source := ⟨"enguehard-2024", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is no bathroom here, or it is upstairs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_15 : Datum :=
  { id := "enguehard2024_15"
    source := ⟨"enguehard-2024", "(15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is false that there is no bathroom here. It is upstairs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_16 : Datum :=
  { id := "enguehard2024_16"
    source := ⟨"enguehard-2024", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is no bathroom here. It would be downstairs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_17 : Datum :=
  { id := "enguehard2024_17"
    source := ⟨"enguehard-2024", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "— There is no bathroom here. — Yes there is! It is upstairs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_18a : Datum :=
  { id := "enguehard2024_18a"
    source := ⟨"enguehard-2024", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not true that the card doesn't have a circle. It's just hard to see."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("antecedent", "sg"), ("pronoun", "it")] }

def ex_18b : Datum :=
  { id := "enguehard2024_18b"
    source := ⟨"enguehard-2024", "(18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not true that the card doesn't have a circle. They're just hard to see."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("antecedent", "sg"), ("pronoun", "they")] }

def ex_19a : Datum :=
  { id := "enguehard2024_19a"
    source := ⟨"enguehard-2024", "(19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not true that the card doesn't have any circles. It's just hard to see."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("antecedent", "pl"), ("pronoun", "it")] }

def ex_19b : Datum :=
  { id := "enguehard2024_19b"
    source := ⟨"enguehard-2024", "(19b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not true that the card doesn't have any circles. They're just hard to see."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("antecedent", "pl"), ("pronoun", "they")] }

def ex_20a : Datum :=
  { id := "enguehard2024_20a"
    source := ⟨"enguehard-2024", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not true that the card doesn't have a circle. It has several but they're hard to see."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_20b : Datum :=
  { id := "enguehard2024_20b"
    source := ⟨"enguehard-2024", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not true that the card doesn't have any circles. It has one but it's hard to see."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_21 : Datum :=
  { id := "enguehard2024_21"
    source := ⟨"enguehard-2024", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is no blue circle on the card."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_22a : Datum :=
  { id := "enguehard2024_22a"
    source := ⟨"enguehard-2024", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yes there is! It's just hard to see."
    glossedTokens := []
    context := "There are several, hard to see blue circles on the card."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_22b : Datum :=
  { id := "enguehard2024_22b"
    source := ⟨"enguehard-2024", "(22b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yes there is! They're just hard to see."
    glossedTokens := []
    context := "There are several, hard to see blue circles on the card."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_22c : Datum :=
  { id := "enguehard2024_22c"
    source := ⟨"enguehard-2024", "(22c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yes there is! There are several, they're just hard to see."
    glossedTokens := []
    context := "There are several, hard to see blue circles on the card."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_24a : Datum :=
  { id := "enguehard2024_24a"
    source := ⟨"enguehard-2024", "(24a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yes, there are several, but they're hard to see."
    glossedTokens := []
    context := "There are several blue circles on the card. Q: Is there a blue circle on the card?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_24b : Datum :=
  { id := "enguehard2024_24b"
    source := ⟨"enguehard-2024", "(24b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yes, but it's hard to see."
    glossedTokens := []
    context := "There are several blue circles on the card. Q: Is there a blue circle on the card?"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex_1a, ex_1b, ex_2a, ex_2b, ex_3a, ex_3b, ex_4, ex_5a, ex_5b, ex_6a, ex_6b, ex_9ai, ex_9aii, ex_9bi, ex_9bii, ex_12a, ex_12b, ex_13, ex_14, ex_15, ex_16, ex_17, ex_18a, ex_18b, ex_19a, ex_19b, ex_20a, ex_20b, ex_21, ex_22a, ex_22b, ex_22c, ex_24a, ex_24b]

end Enguehard2024.Examples
