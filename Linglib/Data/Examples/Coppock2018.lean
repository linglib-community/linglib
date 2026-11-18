module

public import Linglib.Data.Examples.Schema

/-!
# `Coppock2018` — typed example data

Auto-generated from `Linglib/Data/Examples/Coppock2018.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Coppock2018.Examples`.
-/

@[expose] public section

namespace Coppock2018.Examples

def ex_1a : Datum :=
  { id := "coppock2018_1a"
    source := ⟨"coppock-2018", "(1a)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Jag tycker att skolmaten är god."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tycka"), ("complement", "discretionary")] }

def ex_1b : Datum :=
  { id := "coppock2018_1b"
    source := ⟨"coppock-2018", "(1b)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Jag tycker att det är kul att jobba."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tycka"), ("complement", "discretionary")] }

def ex_1c : Datum :=
  { id := "coppock2018_1c"
    source := ⟨"coppock-2018", "(1c)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Jag tycker att det är fel att inte hela Sverige hjälps åt."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tycka"), ("complement", "discretionary")] }

def ex_1d : Datum :=
  { id := "coppock2018_1d"
    source := ⟨"coppock-2018", "(1d)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Jag tycker att vi ska ta hand om varandra."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tycka"), ("complement", "discretionary")] }

def ex_1e : Datum :=
  { id := "coppock2018_1e"
    source := ⟨"coppock-2018", "(1e)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Jag tycker att den ser ut som en champinjon."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tycka"), ("complement", "discretionary")] }

def ex_2a_tro : Datum :=
  { id := "coppock2018_2a_tro"
    source := ⟨"coppock-2018", "(2a)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Jag tror att hon är läkare."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tro"), ("complement", "objective")] }

def ex_2a_tycka : Datum :=
  { id := "coppock2018_2a_tycka"
    source := ⟨"coppock-2018", "(2a)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Jag tycker att hon är läkare."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tycka"), ("complement", "objective")] }

def ex_2b_tro : Datum :=
  { id := "coppock2018_2b_tro"
    source := ⟨"coppock-2018", "(2b)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Jag tror att det är tisdag idag."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tro"), ("complement", "objective")] }

def ex_2b_tycka : Datum :=
  { id := "coppock2018_2b_tycka"
    source := ⟨"coppock-2018", "(2b)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Jag tycker att det är tisdag idag."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tycka"), ("complement", "objective")] }

def ex_2c_tro : Datum :=
  { id := "coppock2018_2c_tro"
    source := ⟨"coppock-2018", "(2c)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Jag tror att jag kommer att vinna."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tro"), ("complement", "objective")] }

def ex_2c_tycka : Datum :=
  { id := "coppock2018_2c_tycka"
    source := ⟨"coppock-2018", "(2c)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Jag tycker att jag kommer att vinna."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tycka"), ("complement", "objective")] }

def ex_2d_tro : Datum :=
  { id := "coppock2018_2d_tro"
    source := ⟨"coppock-2018", "(2d)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Jag tror att det kanske borjar kvart över."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tro"), ("complement", "objective")] }

def ex_2d_tycka : Datum :=
  { id := "coppock2018_2d_tycka"
    source := ⟨"coppock-2018", "(2d)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Jag tycker att det kanske borjar kvart över."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tycka"), ("complement", "objective")] }

def ex_2e_tro : Datum :=
  { id := "coppock2018_2e_tro"
    source := ⟨"coppock-2018", "(2e)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Jag tror att det finns en Gud."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tro"), ("complement", "objective")] }

def ex_2e_tycka : Datum :=
  { id := "coppock2018_2e_tycka"
    source := ⟨"coppock-2018", "(2e)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Jag tycker att det finns en Gud."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tycka"), ("complement", "objective")] }

def ex_3 : Datum :=
  { id := "coppock2018_3"
    source := ⟨"coppock-2018", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John: This chili is tasty. Mary: No, it's not."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "faultless disagreement")] }

def ex_6 : Datum :=
  { id := "coppock2018_6"
    source := ⟨"coppock-2018", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: I am a doctor. B: No, I'm not a doctor!"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "indexical")] }

def ex_7 : Datum :=
  { id := "coppock2018_7"
    source := ⟨"coppock-2018", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Frog legs taste good to me. B: No, frog legs don't taste good to me."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "indexical")] }

def ex_8 : Datum :=
  { id := "coppock2018_8"
    source := ⟨"huvenes-2012", ""⟩
    reportedIn := some ⟨"coppock-2018", "(8)"⟩
    language := "stan1293"
    primaryText := "Sally: I like this chili. Mark: I disagree, it's too hot for me."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "indexical")] }

def ex_9a : Datum :=
  { id := "coppock2018_9a"
    source := ⟨"kennedy-willer-2016", ""⟩
    reportedIn := some ⟨"coppock-2018", "(9a)"⟩
    language := "stan1293"
    primaryText := "Kim considers Burgundy part of France."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "consider"), ("complement", "objective")] }

def ex_9b : Datum :=
  { id := "coppock2018_9b"
    source := ⟨"kennedy-willer-2016", ""⟩
    reportedIn := some ⟨"coppock-2018", "(9b)"⟩
    language := "stan1293"
    primaryText := "Kim considers Crimea part of Russia."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "consider"), ("complement", "discretionary")] }

def ex_10 : Datum :=
  { id := "coppock2018_10"
    source := ⟨"coppock-2018", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is a sexy linguist."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("complement", "hybrid")] }

def ex_11 : Datum :=
  { id := "coppock2018_11"
    source := ⟨"coppock-2018", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: John is a sexy linguist. B: No, he's not sexy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "faultless disagreement")] }

def ex_12 : Datum :=
  { id := "coppock2018_12"
    source := ⟨"coppock-2018", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: John is a sexy linguist. B: No, he's not a linguist."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "disagreement")] }

def ex_13a : Datum :=
  { id := "coppock2018_13a"
    source := ⟨"coppock-2018", "(13a)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Jag tror att hon tycker att…"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tro"), ("complement", "objective")] }

def ex_13b : Datum :=
  { id := "coppock2018_13b"
    source := ⟨"coppock-2018", "(13b)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Jag tycker att hon tycker att…"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tycka"), ("complement", "objective")] }

def ex_15 : Datum :=
  { id := "coppock2018_15"
    source := ⟨"coppock-2018", "(15)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Ebba tycker att Jonas är en sexig lingvist."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tycka"), ("complement", "hybrid"), ("commonGround", "objectiveGiven")] }

def ex_16 : Datum :=
  { id := "coppock2018_16"
    source := ⟨"coppock-2018", "(16)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Ebba tycker inte att Jonas är en sexig lingvist."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tycka"), ("complement", "hybrid"), ("commonGround", "objectiveGiven")] }

def ex_17 : Datum :=
  { id := "coppock2018_17"
    source := ⟨"coppock-2018", "(17)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Tycker Ebba att Jonas är en sexig lingvist?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tycka"), ("complement", "hybrid"), ("commonGround", "objectiveGiven")] }

def ex_20 : Datum :=
  { id := "coppock2018_20"
    source := ⟨"coppock-2018", "(20)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Ebba tycker att Jonas är sexig och en lingvist."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tycka")] }

def ex_21 : Datum :=
  { id := "coppock2018_21"
    source := ⟨"saebo-2009", "p. 338"⟩
    reportedIn := some ⟨"coppock-2018", "(21)"⟩
    language := "stan1293"
    primaryText := "She finds him handsome and below 45."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "find")] }

def ex_22 : Datum :=
  { id := "coppock2018_22"
    source := ⟨"coppock-2018", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He is a linguist. And he is a sexy linguist."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "presupposed conjunct")] }

def ex_23 : Datum :=
  { id := "coppock2018_23"
    source := ⟨"coppock-2018", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He is a linguist. And he is sexy, and (he is) a linguist."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "presupposed conjunct")] }

def ex_24 : Datum :=
  { id := "coppock2018_24"
    source := ⟨"coppock-2018", "(24)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Hon tycker att alla rökare är otrevliga."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tycka")] }

def ex_25 : Datum :=
  { id := "coppock2018_25"
    source := ⟨"coppock-2018", "(25)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Hon tycker att alla som är trevliga är icke-rökare."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tycka")] }

def ex_26 : Datum :=
  { id := "coppock2018_26"
    source := ⟨"kennedy-willer-2016", ""⟩
    reportedIn := some ⟨"coppock-2018", "(26)"⟩
    language := "stan1293"
    primaryText := "Kim finds everyone who is not vegetarian unpleasant."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "find")] }

def ex_27 : Datum :=
  { id := "coppock2018_27"
    source := ⟨"kennedy-willer-2016", ""⟩
    reportedIn := some ⟨"coppock-2018", "(27)"⟩
    language := "stan1293"
    primaryText := "Kim finds everyone who is pleasant vegetarian."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "find")] }

def ex_28 : Datum :=
  { id := "coppock2018_28"
    source := ⟨"coppock-2018", "(28)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Jag tycker inte att det är tisdag idag."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tycka"), ("complement", "objective")] }

def ex_29 : Datum :=
  { id := "coppock2018_29"
    source := ⟨"coppock-2018", "(29)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Om du tycker att det är tisdag idag, så har du fel."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tycka"), ("complement", "objective")] }

def ex_33 : Datum :=
  { id := "coppock2018_33"
    source := ⟨"coppock-2018", "(33)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Jag tycker att det är förjävligt att han dumpat henne."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tycka"), ("complement", "presupObjective"), ("commonGround", "objectiveGiven")] }

def ex_34_tro : Datum :=
  { id := "coppock2018_34_tro"
    source := ⟨"coppock-2018", "(34)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Jag tror att hon inte bryr sig att han är en idiot."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tro"), ("complement", "presupDiscretionary"), ("commonGround", "discretionaryGiven")] }

def ex_34_tycka : Datum :=
  { id := "coppock2018_34_tycka"
    source := ⟨"coppock-2018", "(34)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Jag tycker att hon inte bryr sig att han är en idiot."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tycka"), ("complement", "presupDiscretionary"), ("commonGround", "discretionaryGiven")] }

def ex_35_find : Datum :=
  { id := "coppock2018_35_find"
    source := ⟨"kennedy-willer-2016", ""⟩
    reportedIn := some ⟨"coppock-2018", "(35)"⟩
    language := "stan1293"
    primaryText := "Kim finds the sum of two and two equal to four."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "find"), ("complement", "objective")] }

def ex_36_find : Datum :=
  { id := "coppock2018_36_find"
    source := ⟨"kennedy-willer-2016", ""⟩
    reportedIn := some ⟨"coppock-2018", "(36)"⟩
    language := "stan1293"
    primaryText := "Kim finds Lee fascinating, because he is an expert on oysters."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "find"), ("complement", "discretionary")] }

def ex_35_consider : Datum :=
  { id := "coppock2018_35_consider"
    source := ⟨"kennedy-willer-2016", ""⟩
    reportedIn := some ⟨"coppock-2018", "(35)"⟩
    language := "stan1293"
    primaryText := "Kim considers the sum of two and two equal to four."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "consider"), ("complement", "objective")] }

def ex_36_consider : Datum :=
  { id := "coppock2018_36_consider"
    source := ⟨"kennedy-willer-2016", ""⟩
    reportedIn := some ⟨"coppock-2018", "(36)"⟩
    language := "stan1293"
    primaryText := "Kim considers Lee fascinating, because he is an expert on oysters."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "consider"), ("complement", "discretionary")] }

def ex_37_find : Datum :=
  { id := "coppock2018_37_find"
    source := ⟨"kennedy-willer-2016", ""⟩
    reportedIn := some ⟨"coppock-2018", "(37)"⟩
    language := "stan1293"
    primaryText := "Kim finds Lee vegetarian, because the only animals he eats are oysters."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "find"), ("complement", "hybrid")] }

def ex_37_consider : Datum :=
  { id := "coppock2018_37_consider"
    source := ⟨"kennedy-willer-2016", ""⟩
    reportedIn := some ⟨"coppock-2018", "(37)"⟩
    language := "stan1293"
    primaryText := "Kim considers Lee vegetarian, because the only animals he eats are oysters."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "consider"), ("complement", "hybrid")] }

def ex_38 : Datum :=
  { id := "coppock2018_38"
    source := ⟨"coppock-2018", "(38)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Det är inte så att jag tycker att det är viktigt, men jag tycker inte att det inte är viktigt heller."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tycka"), ("complement", "discretionary")] }

def ex_43a : Datum :=
  { id := "coppock2018_43a"
    source := ⟨"pearson-2013", "(31)"⟩
    reportedIn := some ⟨"coppock-2018", "(43a)"⟩
    language := "stan1293"
    primaryText := "The cake must be tasty, but I wouldn't like it."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "relevance of tastes")] }

def ex_43b : Datum :=
  { id := "coppock2018_43b"
    source := ⟨"pearson-2013", "(32)"⟩
    reportedIn := some ⟨"coppock-2018", "(43b)"⟩
    language := "stan1293"
    primaryText := "The cake must be tasty, but I wouldn't like it because I don't like chocolate."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "relevance of tastes")] }

def ex_44 : Datum :=
  { id := "coppock2018_44"
    source := ⟨"coppock-2018", "(44)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary thinks that John thinks that the cake is tasty."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "think")] }

def ex_45 : Datum :=
  { id := "coppock2018_45"
    source := ⟨"coppock-2018", "(45)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The cat thinks that John thinks that the cat food is tasty."
    glossedTokens := []
    context := "John keeps buying a certain kind of cat food for his cat, leading the cat to form the belief that John believes that the cat food is tasty to the cat, but does not, of course, enjoy eating the cat food himself."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "think")] }

def ex_46a : Datum :=
  { id := "coppock2018_46a"
    source := ⟨"coppock-2018", "(46a)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Katten tror att John tror att kattmaten är god."
    glossedTokens := []
    context := "John keeps buying a certain kind of cat food for his cat, leading the cat to form the belief that John believes that the cat food is tasty to the cat, but does not, of course, enjoy eating the cat food himself."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tro"), ("complement", "objective")] }

def ex_46b : Datum :=
  { id := "coppock2018_46b"
    source := ⟨"coppock-2018", "(46b)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Katten tror att John tycker att kattmaten är god."
    glossedTokens := []
    context := "John keeps buying a certain kind of cat food for his cat, leading the cat to form the belief that John believes that the cat food is tasty to the cat, but does not, of course, enjoy eating the cat food himself."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tycka")] }

def fn14_1_tro : Datum :=
  { id := "coppock2018_fn14_1_tro"
    source := ⟨"coppock-2018", "fn. 14, (1)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Jag tror att soppan är god."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tro")] }

def fn14_2_tro : Datum :=
  { id := "coppock2018_fn14_2_tro"
    source := ⟨"coppock-2018", "fn. 14, (2)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Jag tror att det är viktigt."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tro")] }

def fn14_1_tycka : Datum :=
  { id := "coppock2018_fn14_1_tycka"
    source := ⟨"coppock-2018", "fn. 14, (1)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Jag tycker att soppan är god."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tycka")] }

def fn14_2_tycka : Datum :=
  { id := "coppock2018_fn14_2_tycka"
    source := ⟨"coppock-2018", "fn. 14, (2)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Jag tycker att det är viktigt."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tycka")] }

def all : List Datum := [ex_1a, ex_1b, ex_1c, ex_1d, ex_1e, ex_2a_tro, ex_2a_tycka, ex_2b_tro, ex_2b_tycka, ex_2c_tro, ex_2c_tycka, ex_2d_tro, ex_2d_tycka, ex_2e_tro, ex_2e_tycka, ex_3, ex_6, ex_7, ex_8, ex_9a, ex_9b, ex_10, ex_11, ex_12, ex_13a, ex_13b, ex_15, ex_16, ex_17, ex_20, ex_21, ex_22, ex_23, ex_24, ex_25, ex_26, ex_27, ex_28, ex_29, ex_33, ex_34_tro, ex_34_tycka, ex_35_find, ex_36_find, ex_35_consider, ex_36_consider, ex_37_find, ex_37_consider, ex_38, ex_43a, ex_43b, ex_44, ex_45, ex_46a, ex_46b, fn14_1_tro, fn14_2_tro, fn14_1_tycka, fn14_2_tycka]

end Coppock2018.Examples
