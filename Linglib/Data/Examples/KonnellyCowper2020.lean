module

public import Linglib.Data.Examples.Schema

/-!
# `KonnellyCowper2020` — typed example data

Auto-generated from `Linglib/Data/Examples/KonnellyCowper2020.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace KonnellyCowper2020.Examples`.
-/

@[expose] public section

namespace KonnellyCowper2020.Examples

def ex1a : Datum :=
  { id := "konnellycowper2020_ex1a"
    source := ⟨"konnelly-cowper-2020", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No professor told me they wouldn't be holding office hours this week."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "quantified"), ("noun", "ungendered"), ("referent", "unknown"), ("pronoun", "they"), ("stage", "1"), ("firstStage", "1")] }

def ex1b : Datum :=
  { id := "konnellycowper2020_ex1b"
    source := ⟨"konnelly-cowper-2020", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The right candidate knows they should bring a copy of their resumé."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "referential"), ("noun", "ungendered"), ("referent", "unknown"), ("pronoun", "they"), ("stage", "1"), ("firstStage", "1")] }

def ex1c : Datum :=
  { id := "konnellycowper2020_ex1c"
    source := ⟨"konnelly-cowper-2020", "(1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every author knows they should get an early start in the morning."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "quantified"), ("noun", "ungendered"), ("referent", "unknown"), ("pronoun", "they"), ("stage", "1"), ("firstStage", "1")] }

def ex3a : Datum :=
  { id := "konnellycowper2020_ex3a"
    source := ⟨"konnelly-cowper-2020", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The professor said they cancelled the exam."
    glossedTokens := []
    context := ""
    judgment := .variable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "referential"), ("noun", "ungendered"), ("referent", "known"), ("pronoun", "they"), ("firstStage", "2")] }

def ex3b : Datum :=
  { id := "konnellycowper2020_ex3b"
    source := ⟨"konnelly-cowper-2020", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Our eldest child broke their leg."
    glossedTokens := []
    context := ""
    judgment := .variable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "referential"), ("noun", "ungendered"), ("referent", "known"), ("pronoun", "they"), ("firstStage", "2")] }

def ex3c : Datum :=
  { id := "konnellycowper2020_ex3c"
    source := ⟨"konnelly-cowper-2020", "(3c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I'll let my cousin introduce themselves."
    glossedTokens := []
    context := ""
    judgment := .variable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "referential"), ("noun", "ungendered"), ("referent", "known"), ("pronoun", "they"), ("firstStage", "2")] }

def ex4a : Datum :=
  { id := "konnellycowper2020_ex4a"
    source := ⟨"konnelly-cowper-2020", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Janet said they cancelled the exam."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "referential"), ("noun", "fem"), ("referent", "known"), ("pronoun", "they"), ("stage", "2"), ("firstStage", "3")] }

def ex4b : Datum :=
  { id := "konnellycowper2020_ex4b"
    source := ⟨"konnelly-cowper-2020", "(4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Thomas broke their leg."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "referential"), ("noun", "masc"), ("referent", "known"), ("pronoun", "they"), ("stage", "2"), ("firstStage", "3")] }

def ex4c : Datum :=
  { id := "konnellycowper2020_ex4c"
    source := ⟨"konnelly-cowper-2020", "(4c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I'll let my sister introduce themselves."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("father", .ungrammatical), ("aunt", .ungrammatical)]
    readings := []
    paperFeatures := [("antecedent", "referential"), ("noun", "fem"), ("referent", "known"), ("pronoun", "they"), ("stage", "2"), ("firstStage", "3")] }

def ex5a : Datum :=
  { id := "konnellycowper2020_ex5a"
    source := ⟨"konnelly-cowper-2020", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Anyone who thinks they need more time should ask for an extension."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "quantified"), ("noun", "ungendered"), ("referent", "unknown"), ("pronoun", "they"), ("stage", "3"), ("firstStage", "1")] }

def ex5b : Datum :=
  { id := "konnellycowper2020_ex5b"
    source := ⟨"konnelly-cowper-2020", "(5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The person at the door left before I could see who they were."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "referential"), ("noun", "ungendered"), ("referent", "unknown"), ("pronoun", "they"), ("stage", "3"), ("firstStage", "1")] }

def ex6a : Datum :=
  { id := "konnellycowper2020_ex6a"
    source := ⟨"konnelly-cowper-2020", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kelly said they were leaving early."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "referential"), ("noun", "ungendered"), ("referent", "known"), ("pronoun", "they"), ("stage", "3"), ("firstStage", "2")] }

def ex6b : Datum :=
  { id := "konnellycowper2020_ex6b"
    source := ⟨"konnelly-cowper-2020", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The strongest student will present their paper next."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "referential"), ("noun", "ungendered"), ("referent", "known"), ("pronoun", "they"), ("stage", "3"), ("firstStage", "2")] }

def ex7a : Datum :=
  { id := "konnellycowper2020_ex7a"
    source := ⟨"konnelly-cowper-2020", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Maria wants to send their students on the field trip."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "referential"), ("noun", "fem"), ("referent", "known"), ("pronoun", "they"), ("stage", "3"), ("firstStage", "3")] }

def ex7b : Datum :=
  { id := "konnellycowper2020_ex7b"
    source := ⟨"konnelly-cowper-2020", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We heard from Arthur that they needed time to think about the idea."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "referential"), ("noun", "masc"), ("referent", "known"), ("pronoun", "they"), ("stage", "3"), ("firstStage", "3")] }

def ex7c : Datum :=
  { id := "konnellycowper2020_ex7c"
    source := ⟨"konnelly-cowper-2020", "(7c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We asked the first girl in line to introduce themself."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("themselves", .acceptable)]
    readings := []
    paperFeatures := [("antecedent", "referential"), ("noun", "fem"), ("referent", "known"), ("pronoun", "they"), ("stage", "3"), ("firstStage", "3")] }

def ex7d : Datum :=
  { id := "konnellycowper2020_ex7d"
    source := ⟨"konnelly-cowper-2020", "(7d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Your brother called to say they would be late."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "referential"), ("noun", "masc"), ("referent", "known"), ("pronoun", "they"), ("stage", "3"), ("firstStage", "3")] }

def ex8a : Datum :=
  { id := "konnellycowper2020_ex8a"
    source := ⟨"konnelly-cowper-2020", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The professor said he wouldn't be giving us an exam."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "referential"), ("noun", "ungendered"), ("referent", "masc"), ("pronoun", "he"), ("stage", "3")] }

def ex8b : Datum :=
  { id := "konnellycowper2020_ex8b"
    source := ⟨"konnelly-cowper-2020", "(8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kelly said she was leaving early."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "referential"), ("noun", "ungendered"), ("referent", "fem"), ("pronoun", "she"), ("stage", "3")] }

def ex10_it : Datum :=
  { id := "konnellycowper2020_ex10_it"
    source := ⟨"konnelly-cowper-2020", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I put my favourite watch down somewhere, and now I can't find it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "referential"), ("noun", "inanimate"), ("referent", "unknown"), ("pronoun", "it"), ("stage", "3")] }

def ex10_them : Datum :=
  { id := "konnellycowper2020_ex10_them"
    source := ⟨"konnelly-cowper-2020", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I put my favourite watch down somewhere, and now I can't find them."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "referential"), ("noun", "inanimate"), ("referent", "unknown"), ("pronoun", "they"), ("stage", "3")] }

def ex12a : Datum :=
  { id := "konnellycowper2020_ex12a"
    source := ⟨"konnelly-cowper-2020", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There's not a man I meet but doth salute me as if I were their well-acquainted friend."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "quantified"), ("noun", "masc"), ("referent", "unknown"), ("pronoun", "they"), ("stage", "1"), ("firstStage", "1")] }

def ex12b : Datum :=
  { id := "konnellycowper2020_ex12b"
    source := ⟨"konnelly-cowper-2020", "(12b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every girl is responsible for completing her homework on time."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "quantified"), ("noun", "fem"), ("referent", "unknown"), ("pronoun", "she"), ("stage", "1")] }

def ex12c : Datum :=
  { id := "konnellycowper2020_ex12c"
    source := ⟨"konnelly-cowper-2020", "(12c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No mother should be forced by federal prosecutors to testify against their child."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "quantified"), ("noun", "fem"), ("referent", "unknown"), ("pronoun", "they"), ("stage", "1"), ("firstStage", "1")] }

def ex12d : Datum :=
  { id := "konnellycowper2020_ex12d"
    source := ⟨"konnelly-cowper-2020", "(12d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Any boy who thinks he is ready may take the test."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "quantified"), ("noun", "masc"), ("referent", "unknown"), ("pronoun", "he"), ("stage", "1")] }

def ex13_its : Datum :=
  { id := "konnellycowper2020_ex13_its"
    source := ⟨"konnelly-cowper-2020", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every book that needs its cover replaced should be sent to the bindery."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "quantified"), ("noun", "inanimate"), ("referent", "unknown"), ("pronoun", "it"), ("stage", "1")] }

def ex13_their : Datum :=
  { id := "konnellycowper2020_ex13_their"
    source := ⟨"konnelly-cowper-2020", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every book that needs their cover replaced should be sent to the bindery."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "quantified"), ("noun", "inanimate"), ("referent", "unknown"), ("pronoun", "they"), ("stage", "1")] }

def ex16b : Datum :=
  { id := "konnellycowper2020_ex16b"
    source := ⟨"konnelly-cowper-2020", "(16b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My eldest child got a bicycle for their birthday."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "referential"), ("noun", "ungendered"), ("referent", "known"), ("pronoun", "they"), ("stage", "2"), ("firstStage", "2")] }

def ex21a : Datum :=
  { id := "konnellycowper2020_ex21a"
    source := ⟨"konnelly-cowper-2020", "(21a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My father said they were leaving tomorrow."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "referential"), ("noun", "masc"), ("referent", "known"), ("pronoun", "they"), ("stage", "2")] }

def ex21b : Datum :=
  { id := "konnellycowper2020_ex21b"
    source := ⟨"konnelly-cowper-2020", "(21b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Janet left their book here."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "referential"), ("noun", "fem"), ("referent", "known"), ("pronoun", "they"), ("stage", "2")] }

def ex23 : Datum :=
  { id := "konnellycowper2020_ex23"
    source := ⟨"konnelly-cowper-2020", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The women said that they were leaving."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "referential"), ("noun", "fem"), ("referent", "fem"), ("number", "plural"), ("pronoun", "they"), ("stage", "2")] }

def ex24 : Datum :=
  { id := "konnellycowper2020_ex24"
    source := ⟨"konnelly-cowper-2020", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The women said that she was leaving."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "referential"), ("noun", "fem"), ("referent", "fem"), ("number", "plural"), ("pronoun", "she"), ("stage", "2")] }

def ex25a : Datum :=
  { id := "konnellycowper2020_ex25a"
    source := ⟨"konnelly-cowper-2020", "(25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sir Paul has always played their guitar left-handed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "referential"), ("noun", "masc"), ("referent", "known"), ("pronoun", "they"), ("stage", "3"), ("firstStage", "3")] }

def ex25b : Datum :=
  { id := "konnellycowper2020_ex25b"
    source := ⟨"konnelly-cowper-2020", "(25b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My grandmother always liked it when we asked them about their childhood."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "referential"), ("noun", "fem"), ("referent", "known"), ("pronoun", "they"), ("stage", "3"), ("firstStage", "3")] }

def ex26a : Datum :=
  { id := "konnellycowper2020_ex26a"
    source := ⟨"konnelly-cowper-2020", "(26a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My mother left her coat here."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "referential"), ("noun", "fem"), ("referent", "fem"), ("pronoun", "she"), ("stage", "3")] }

def ex26b : Datum :=
  { id := "konnellycowper2020_ex26b"
    source := ⟨"konnelly-cowper-2020", "(26b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Your mother left their coat here."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "referential"), ("noun", "fem"), ("referent", "known"), ("pronoun", "they"), ("stage", "3")] }

def ex26c : Datum :=
  { id := "konnellycowper2020_ex26c"
    source := ⟨"konnelly-cowper-2020", "(26c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Your mother left his coat here."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "referential"), ("noun", "fem"), ("referent", "masc"), ("pronoun", "he"), ("stage", "3")] }

def all : List Datum := [ex1a, ex1b, ex1c, ex3a, ex3b, ex3c, ex4a, ex4b, ex4c, ex5a, ex5b, ex6a, ex6b, ex7a, ex7b, ex7c, ex7d, ex8a, ex8b, ex10_it, ex10_them, ex12a, ex12b, ex12c, ex12d, ex13_its, ex13_their, ex16b, ex21a, ex21b, ex23, ex24, ex25a, ex25b, ex26a, ex26b, ex26c]

end KonnellyCowper2020.Examples
