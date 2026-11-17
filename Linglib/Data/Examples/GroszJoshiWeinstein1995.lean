module

public import Linglib.Data.Examples.Schema

/-!
# `GroszJoshiWeinstein1995` — typed example data

Auto-generated from `Linglib/Data/Examples/GroszJoshiWeinstein1995.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace GroszJoshiWeinstein1995.Examples`.
-/

@[expose] public section

namespace GroszJoshiWeinstein1995.Examples

def ex_1 : Datum :=
  { id := "groszjoshiweinstein1995_1"
    source := ⟨"grosz-joshi-weinstein-1995", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John went to his favorite music store to buy a piano. He had frequented the store for many years. He was excited that he could finally buy a piano. He arrived just as the store was closing for the day."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2"), ("phenomenon", "coherence"), ("coherence", "more")] }

def ex_2 : Datum :=
  { id := "groszjoshiweinstein1995_2"
    source := ⟨"grosz-joshi-weinstein-1995", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John went to his favorite music store to buy a piano. It was a store John had frequented for many years. He was excited that he could finally buy a piano. It was closing just as John arrived."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("section", "2"), ("phenomenon", "coherence"), ("coherence", "less")] }

def ex_3 : Datum :=
  { id := "groszjoshiweinstein1995_3"
    source := ⟨"grosz-joshi-weinstein-1995", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Terry really goofs sometimes. Yesterday was a beautiful day and he was excited about trying out his new sailboat. He wanted Tony to join him on a sailing expedition. He called him at 6 AM. He was sick and furious at being woken up so early."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("section", "2"), ("phenomenon", "pronounMisdirection")] }

def ex_4 : Datum :=
  { id := "groszjoshiweinstein1995_4"
    source := ⟨"grosz-joshi-weinstein-1995", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Terry really goofs sometimes. Yesterday was a beautiful day and he was excited about trying out his new sailboat. He wanted Tony to join him on a sailing expedition. He called him at 6 AM. Tony was sick and furious at being woken up so early. He told Terry to get lost and hung up. Of course, he hadn't intended to upset Tony."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("section", "2"), ("phenomenon", "pronounMisdirection")] }

def ex_5 : Datum :=
  { id := "groszjoshiweinstein1995_5"
    source := ⟨"grosz-joshi-weinstein-1995", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Terry really goofs sometimes. Yesterday was a beautiful day and he was excited about trying out his new sailboat. He wanted Tony to join him on a sailing expedition. He called him at 6 AM. Tony was sick and furious at being woken up so early. He told Terry to get lost and hung up. Of course, Terry hadn't intended to upset Tony."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2"), ("phenomenon", "pronounMisdirection")] }

def ex_6 : Datum :=
  { id := "groszjoshiweinstein1995_6"
    source := ⟨"grosz-joshi-weinstein-1995", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Susan gave Betsy a pet hamster. She reminded her that such hamsters were quite shy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5"), ("phenomenon", "uniqueCb")] }

def ex_7 : Datum :=
  { id := "groszjoshiweinstein1995_7"
    source := ⟨"grosz-joshi-weinstein-1995", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Susan gave Betsy a pet hamster. She reminded her that such hamsters were quite shy. She asked Betsy whether she liked the gift."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5"), ("phenomenon", "rule1"), ("rule1", "satisfied")] }

def ex_8 : Datum :=
  { id := "groszjoshiweinstein1995_8"
    source := ⟨"grosz-joshi-weinstein-1995", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Susan gave Betsy a pet hamster. She reminded her that such hamsters were quite shy. Betsy told her that she really liked the gift."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5"), ("phenomenon", "rule1"), ("rule1", "satisfied")] }

def ex_9 : Datum :=
  { id := "groszjoshiweinstein1995_9"
    source := ⟨"grosz-joshi-weinstein-1995", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Susan gave Betsy a pet hamster. She reminded her that such hamsters were quite shy. Susan asked her whether she liked the gift."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("section", "5"), ("phenomenon", "rule1"), ("rule1", "violated")] }

def ex_10 : Datum :=
  { id := "groszjoshiweinstein1995_10"
    source := ⟨"grosz-joshi-weinstein-1995", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Susan gave Betsy a pet hamster. She reminded her that such hamsters were quite shy. She told Susan that she really liked the gift."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5"), ("phenomenon", "rule1"), ("rule1", "violated")] }

def ex_11 : Datum :=
  { id := "groszjoshiweinstein1995_11"
    source := ⟨"grosz-joshi-weinstein-1995", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Susan is a fine friend. She gives people the most wonderful presents. She just gave Betsy a wonderful bottle of wine. She told her it was quite rare. She knows a lot about wine."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("she = Susan", .acceptable), ("she = Betsy", .marginal)]
    paperFeatures := [("section", "5"), ("phenomenon", "cfRanking")] }

def ex_12 : Datum :=
  { id := "groszjoshiweinstein1995_12"
    source := ⟨"grosz-joshi-weinstein-1995", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Susan is a fine friend. She gives people the most wonderful presents. She just gave Betsy a wonderful bottle of wine. She told her it was quite rare. Wine collecting gives her expertise that's fun to share."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("her = Susan", .acceptable), ("her = Betsy", .marginal)]
    paperFeatures := [("section", "5"), ("phenomenon", "cfRanking")] }

def ex_13 : Datum :=
  { id := "groszjoshiweinstein1995_13"
    source := ⟨"grosz-joshi-weinstein-1995", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Have you seen the new toys the kids got this weekend? Stuffed animals must really be out of fashion. Susie prefers the green plastic tugboat to the teddy bear. Tommy likes it better than the bear too, but only because the silly thing is bigger."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5"), ("phenomenon", "cfRanking"), ("coherence", "more")] }

def ex_14 : Datum :=
  { id := "groszjoshiweinstein1995_14"
    source := ⟨"grosz-joshi-weinstein-1995", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Have you seen the new toys the kids got this weekend? Stuffed animals must really be out of fashion. Susie prefers the green plastic tugboat to the teddy bear. Tommy likes it better than the bear too, although the silly thing is bigger."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("section", "5"), ("phenomenon", "cfRanking"), ("coherence", "less")] }

def ex_15 : Datum :=
  { id := "groszjoshiweinstein1995_15"
    source := ⟨"grosz-joshi-weinstein-1995", "(15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He has been acting quite odd. He called up Mike yesterday. John wanted to meet him urgently."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7"), ("phenomenon", "rule1"), ("rule1", "violated")] }

def ex_16 : Datum :=
  { id := "groszjoshiweinstein1995_16"
    source := ⟨"grosz-joshi-weinstein-1995", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John has been acting quite odd. He called up Mike yesterday. Mike was studying for his driver's test. He was annoyed by John's call."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7"), ("phenomenon", "rule1"), ("rule1", "satisfied")] }

def ex_17 : Datum :=
  { id := "groszjoshiweinstein1995_17"
    source := ⟨"grosz-joshi-weinstein-1995", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My dog is getting quite obstreperous. I took him to the vet the other day. The mangy old beast always hates these visits."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7"), ("phenomenon", "fullNounPhraseCb")] }

def ex_18 : Datum :=
  { id := "groszjoshiweinstein1995_18"
    source := ⟨"grosz-joshi-weinstein-1995", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I'm reading The French Lieutenant's Woman. The book, which is Fowles's best, was a bestseller last year."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7"), ("phenomenon", "fullNounPhraseCb")] }

def ex_19 : Datum :=
  { id := "groszjoshiweinstein1995_19"
    source := ⟨"grosz-joshi-weinstein-1995", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The house appeared to have been burgled. The door was ajar. The furniture was in disarray."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7"), ("phenomenon", "functionalDependence")] }

def ex_20 : Datum :=
  { id := "groszjoshiweinstein1995_20"
    source := ⟨"grosz-joshi-weinstein-1995", "(20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John has been having a lot of trouble arranging his vacation. He cannot find anyone to take over his responsibilities. He called up Mike yesterday to work out a plan. Mike has annoyed him a lot recently. He called John at 5 AM on Friday last week."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7"), ("phenomenon", "transitions"), ("rule1", "satisfied")] }

def ex_25 : Datum :=
  { id := "groszjoshiweinstein1995_25"
    source := ⟨"grosz-joshi-weinstein-1995", "(25)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The Vice-President of the United States is also President of the Senate. Historically, he is the President's key man in negotiations with Congress. He is required to be 35 years old."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "8"), ("phenomenon", "valueFreeLoaded")] }

def ex_26 : Datum :=
  { id := "groszjoshiweinstein1995_26"
    source := ⟨"grosz-joshi-weinstein-1995", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The Vice-President of the United States is also President of the Senate. Right now, he's the president's key person in negotiations with Congress. As Ambassador to China, he handled many tricky negotiations, so he is well prepared for this job."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "8"), ("phenomenon", "valueFreeLoaded")] }

def ex_27 : Datum :=
  { id := "groszjoshiweinstein1995_27"
    source := ⟨"grosz-joshi-weinstein-1995", "(27)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: The Vice-President of the U.S. is also President of the Senate. B: I thought he played some important role in the House. A: He did, but that was before he was the Vice-President."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "8"), ("phenomenon", "valueFreeLoaded")] }

def ex_28 : Datum :=
  { id := "groszjoshiweinstein1995_28"
    source := ⟨"grosz-joshi-weinstein-1995", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John thinks that the telephone is a nuisance. He curses it every day. He doesn't realize that it is an invention that changed the world."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "8"), ("phenomenon", "valueFreeLoaded")] }

def ex_32 : Datum :=
  { id := "groszjoshiweinstein1995_32"
    source := ⟨"grosz-joshi-weinstein-1995", "(32)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Her husband is kind to her. No, he isn't. The man you're referring to isn't her husband."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "8"), ("phenomenon", "referentialUse")] }

def ex_33 : Datum :=
  { id := "groszjoshiweinstein1995_33"
    source := ⟨"grosz-joshi-weinstein-1995", "(33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Her husband is kind to her. He is kind to her but he isn't her husband."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "8"), ("phenomenon", "referentialUse")] }

def ex_34 : Datum :=
  { id := "groszjoshiweinstein1995_34"
    source := ⟨"sidner-1979", "ch. 4, D9"⟩
    reportedIn := some ⟨"grosz-joshi-weinstein-1995", "(34)"⟩
    language := "stan1293"
    primaryText := "I haven't seen Jeff for several days. Carl thinks he's studying for his exams, but I think he went to the Cape with Linda."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("he in (c) = Jeff", .acceptable)]
    paperFeatures := [("section", "9"), ("phenomenon", "sidnerComparison")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, ex_10, ex_11, ex_12, ex_13, ex_14, ex_15, ex_16, ex_17, ex_18, ex_19, ex_20, ex_25, ex_26, ex_27, ex_28, ex_32, ex_33, ex_34]

end GroszJoshiWeinstein1995.Examples
