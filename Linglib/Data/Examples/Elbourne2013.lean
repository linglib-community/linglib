module

public import Linglib.Data.Examples.Schema

/-!
# `Elbourne2013` — typed example data

Auto-generated from `Linglib/Data/Examples/Elbourne2013.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Elbourne2013.Examples`.
-/

@[expose] public section

namespace Elbourne2013.Examples

def ch3_5 : Datum :=
  { id := "elbourne2013_ch3_5"
    source := ⟨"elbourne-2013", "ch. 3, (5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The cat grins."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("referential situation pronoun", .acceptable), ("bound situation pronoun", .acceptable)]
    paperFeatures := [("chapter", "3"), ("structure", "[[[the cat] s1] grins] or [ς1 [[[the cat] s1] grins]]")] }

def ch5_2 : Datum :=
  { id := "elbourne2013_ch5_2"
    source := ⟨"elbourne-2013", "ch. 5, (2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The murderer is insane."
    glossedTokens := []
    context := "Attributive: Smith is found foully murdered and no one knows by whom. Referential: Jones is on trial for the murder and behaving oddly in court."
    judgment := .acceptable
    contrasts := []
    readings := [("referential", .acceptable), ("attributive", .acceptable)]
    paperFeatures := [("chapter", "5"), ("referential", "free situation pronoun"), ("attributive", "bound situation pronoun")] }

def ch5_13 : Datum :=
  { id := "elbourne2013_ch5_13"
    source := ⟨"donnellan-1966", "p. 287"⟩
    reportedIn := some ⟨"elbourne-2013", "ch. 5, (13)"⟩
    language := "stan1293"
    primaryText := "Who is the man drinking a martini?"
    glossedTokens := []
    context := "The man gestured at is drinking water from a martini glass."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("chapter", "5"), ("misdescription", "yes")] }

def ch5_16 : Datum :=
  { id := "elbourne2013_ch5_16"
    source := ⟨"russell-1905", "pp. 487–488"⟩
    reportedIn := some ⟨"elbourne-2013", "ch. 5, (16)"⟩
    language := "stan1293"
    primaryText := "Scott is the author of Waverley."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Scott is Scott.", .acceptable)]
    readings := []
    paperFeatures := [("chapter", "5"), ("use", "predicative")] }

def ch6_3 : Datum :=
  { id := "elbourne2013_ch6_3"
    source := ⟨"elbourne-2013", "ch. 6, (3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every man who owns a donkey beats the donkey."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("strong", .acceptable)]
    paperFeatures := [("chapter", "6"), ("anaphora", "donkey-anaphoric definite description")] }

def ch6_15 : Datum :=
  { id := "elbourne2013_ch6_15"
    source := ⟨"elbourne-2013", "ch. 6, (15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If a man beats a donkey, the donkey always kicks him."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("If a man beats a donkey, the donkey kicks him.", .acceptable)]
    readings := []
    paperFeatures := [("chapter", "6"), ("anaphora", "donkey-anaphoric definite description under a quantificational adverb")] }

def ch6_21 : Datum :=
  { id := "elbourne2013_ch6_21"
    source := ⟨"elbourne-2013", "ch. 6, (21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John fed no cat of Mary's before the cat was bathed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("covarying", .acceptable)]
    paperFeatures := [("chapter", "6"), ("anaphora", "c-commanded bound definite description")] }

def ch7_7 : Datum :=
  { id := "elbourne2013_ch7_7"
    source := ⟨"elbourne-2013", "ch. 7, (7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary believes that the man who lives upstairs is a spy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("de dicto", .acceptable), ("de re", .acceptable)]
    paperFeatures := [("chapter", "7"), ("de dicto", "situation pronoun bound below believes"), ("de re", "situation pronoun referring to the actual world")] }

def ch7_16 : Datum :=
  { id := "elbourne2013_ch7_16"
    source := ⟨"elbourne-2013", "ch. 7, (16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The number of the planets is necessarily odd."
    glossedTokens := []
    context := "The speaker does not know how many planets there are, but astronomical theory dictates that the number is odd."
    judgment := .acceptable
    contrasts := []
    readings := [("attributive de re", .acceptable)]
    paperFeatures := [("chapter", "7"), ("structure", "[ς2 [[[the [number [of [[the planets] s2]]]] s2] [is [necessarily odd]]]]")] }

def ch8_3 : Datum :=
  { id := "elbourne2013_ch8_3"
    source := ⟨"elbourne-2013", "ch. 8, (3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Hans wants the ghost in his attic to be quiet tonight."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Hans wants there to be exactly one ghost in his attic and for it to be quiet tonight.", .acceptable)]
    readings := []
    paperFeatures := [("chapter", "8"), ("presupposition", "Hans believes there is exactly one ghost in his attic")] }

def ch8_5 : Datum :=
  { id := "elbourne2013_ch8_5"
    source := ⟨"elbourne-2013", "ch. 8, (5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If the ghost in his attic is quiet tonight, Hans will hold a party."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("chapter", "8"), ("presupposition", "there is exactly one ghost in Hans's attic")] }

def ch8_22 : Datum :=
  { id := "elbourne2013_ch8_22"
    source := ⟨"elbourne-2013", "ch. 8, (22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I do not know whether there are any ghosts in Hans's attic. But if the ghost in his attic is quiet tonight, he will hold a party."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("I do not know whether there are any ghosts in Hans's attic. But if there is exactly one ghost in his attic and it is quiet tonight, he will hold a party.", .acceptable)]
    readings := []
    paperFeatures := [("chapter", "8"), ("contrast", "definite description against its Russellian paraphrase"), ("felicity", "infelicitous")] }

def ch8_33 : Datum :=
  { id := "elbourne2013_ch8_33"
    source := ⟨"elbourne-2013", "ch. 8, (31), (33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I am unsure whether there is a ghost in my attic. I would like the ghost in my attic to be quiet tonight."
    glossedTokens := []
    context := "Hans sincerely says both."
    judgment := .acceptable
    contrasts := [("I am unsure whether there is a ghost in my attic. I would like there to be an entity such that it is a ghost in my attic and nothing else is a ghost in my attic and it is quiet tonight.", .acceptable)]
    readings := []
    paperFeatures := [("chapter", "8"), ("contrast", "definite description against its Russellian paraphrase under an attitude verb"), ("felicity", "infelicitous")] }

def ch8_36 : Datum :=
  { id := "elbourne2013_ch8_36"
    source := ⟨"elbourne-2013", "ch. 8, (36)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ponce de León is wondering whether the fountain of youth is in Florida."
    glossedTokens := []
    context := "The speaker does not believe in the existence of a fountain of youth."
    judgment := .acceptable
    contrasts := []
    readings := [("no speaker commitment to a fountain of youth", .acceptable)]
    paperFeatures := [("chapter", "8"), ("presupposition", "Ponce de León believes there is exactly one fountain of youth")] }

def ch9_4 : Datum :=
  { id := "elbourne2013_ch9_4"
    source := ⟨"strawson-1950", "p. 332"⟩
    reportedIn := some ⟨"elbourne-2013", "ch. 9, (4)"⟩
    language := "stan1293"
    primaryText := "The table is covered with books."
    glossedTokens := []
    context := "Said in a room containing exactly one table, in a world containing many."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("chapter", "9"), ("incompleteness", "situation pronoun referring to the room")] }

def ch9_17a : Datum :=
  { id := "elbourne2013_ch9_17a"
    source := ⟨"elbourne-2013", "ch. 9, (17a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In this village, if a farmer owns a donkey, he beats the donkey and the priest beats the donkey too."
    glossedTokens := []
    context := "The final verb phrase is downstressed."
    judgment := .acceptable
    contrasts := []
    readings := [("strict", .acceptable), ("sloppy", .ungrammatical)]
    paperFeatures := [("chapter", "9"), ("description", "the donkey")] }

def ch9_17b : Datum :=
  { id := "elbourne2013_ch9_17b"
    source := ⟨"elbourne-2013", "ch. 9, (17b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In this village, if a farmer owns a donkey, he beats the donkey he owns and the priest beats the donkey he owns too."
    glossedTokens := []
    context := "The final verb phrase is downstressed."
    judgment := .acceptable
    contrasts := []
    readings := [("strict", .acceptable), ("sloppy", .acceptable)]
    paperFeatures := [("chapter", "9"), ("description", "the donkey he owns")] }

def ch10_10a : Datum :=
  { id := "elbourne2013_ch10_10a"
    source := ⟨"elbourne-2013", "ch. 10, (10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every man who owns a donkey beats it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("strong", .acceptable)]
    paperFeatures := [("chapter", "10"), ("structure", "[σ3 [Q [beats [[it donkey] s3]]]]")] }

def ch10_21 : Datum :=
  { id := "elbourne2013_ch10_21"
    source := ⟨"elbourne-2013", "ch. 10, (21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I saw the Junior Dean. He was worried about the Bollinger dinner."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("chapter", "10"), ("structure", "[[he [Junior Dean]] s1]")] }

def ch10_34 : Datum :=
  { id := "elbourne2013_ch10_34"
    source := ⟨"elbourne-2013", "ch. 10, (34)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He is usually an Italian."
    glossedTokens := []
    context := "Said while pointing at Benedict XVI."
    judgment := .acceptable
    contrasts := [("Benedict XVI is usually an Italian.", .acceptable)]
    readings := [("descriptive indexical", .acceptable)]
    paperFeatures := [("chapter", "10"), ("structure", "[[he Pope] s3]")] }

def ch10_47 : Datum :=
  { id := "elbourne2013_ch10_47"
    source := ⟨"elbourne-2013", "ch. 10, (47)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He Who Must Not Be Named"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("It which rolls fastest gathers no moss.", .ungrammatical), ("he of the fiery sword", .acceptable), ("he of Mary", .ungrammatical)]
    readings := []
    paperFeatures := [("chapter", "10"), ("structure", "[[he [person [who ...]]] si]")] }

def all : List Datum := [ch3_5, ch5_2, ch5_13, ch5_16, ch6_3, ch6_15, ch6_21, ch7_7, ch7_16, ch8_3, ch8_5, ch8_22, ch8_33, ch8_36, ch9_4, ch9_17a, ch9_17b, ch10_10a, ch10_21, ch10_34, ch10_47]

end Elbourne2013.Examples
