module

public import Linglib.Data.Examples.Schema

/-!
# `ViknerJensen2002` — typed example data

Auto-generated from `Linglib/Data/Examples/ViknerJensen2002.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ViknerJensen2002.Examples`.
-/

@[expose] public section

namespace ViknerJensen2002.Examples

def ex_1a : Datum :=
  { id := "viknerjensen2002_1a"
    source := ⟨"vikner-jensen-2002", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the girl's sister"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inherent relation", .acceptable)]
    paperFeatures := [("headNoun", "relational"), ("relationType", "inherent")] }

def ex_1b : Datum :=
  { id := "viknerjensen2002_1b"
    source := ⟨"vikner-jensen-2002", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the girl's nose"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("part-whole relation", .acceptable)]
    paperFeatures := [("headNoun", "sortal"), ("relationType", "partWhole"), ("quale", "constitutive")] }

def ex_1c : Datum :=
  { id := "viknerjensen2002_1c"
    source := ⟨"vikner-jensen-2002", "(1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the girl's car"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("control relation", .acceptable)]
    paperFeatures := [("headNoun", "sortal"), ("relationType", "control")] }

def ex_2a : Datum :=
  { id := "viknerjensen2002_2a"
    source := ⟨"vikner-jensen-2002", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the girl's teacher"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("the person who is the teacher of the girl", .acceptable), ("the teacher she has married, is going to interview, is blackmailing, is dreaming of", .acceptable)]
    paperFeatures := [("headNoun", "relational"), ("interpretation", "lexical and pragmatic")] }

def ex_2b : Datum :=
  { id := "viknerjensen2002_2b"
    source := ⟨"vikner-jensen-2002", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the girl's poem"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("the poem that the girl has written", .acceptable), ("the poem she holds in her hand, has discovered, is going to analyze, is always talking about", .acceptable)]
    paperFeatures := [("headNoun", "sortal"), ("interpretation", "lexical and pragmatic")] }

def ex_4 : Datum :=
  { id := "viknerjensen2002_4"
    source := ⟨"vikner-jensen-2002", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The girl's poem is beautiful."
    glossedTokens := []
    context := "No knowledge of the background of the utterance situation."
    judgment := .acceptable
    alternatives := []
    readings := [("a poem that the girl has written", .acceptable)]
    paperFeatures := [("interpretation", "lexical"), ("relationType", "agentive")] }

def ex_5a : Datum :=
  { id := "viknerjensen2002_5a"
    source := ⟨"vikner-jensen-2002", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the girl's teacher"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("the person who is the teacher of the girl", .acceptable)]
    paperFeatures := [("interpretation", "lexical"), ("relationType", "inherent")] }

def ex_5b : Datum :=
  { id := "viknerjensen2002_5b"
    source := ⟨"vikner-jensen-2002", "(5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the girl's nose"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("the nose which is a part of the girl", .acceptable)]
    paperFeatures := [("interpretation", "lexical"), ("relationType", "partWhole")] }

def ex_5c : Datum :=
  { id := "viknerjensen2002_5c"
    source := ⟨"vikner-jensen-2002", "(5c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the girl's poem"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("the poem that the girl has written", .acceptable)]
    paperFeatures := [("interpretation", "lexical"), ("relationType", "agentive")] }

def ex_5d : Datum :=
  { id := "viknerjensen2002_5d"
    source := ⟨"vikner-jensen-2002", "(5d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the girl's car"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("the car which the girl has at her disposal", .acceptable)]
    paperFeatures := [("interpretation", "lexical"), ("relationType", "control")] }

def ex_6a : Datum :=
  { id := "viknerjensen2002_6a"
    source := ⟨"vikner-jensen-2002", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the girl's teacher"
    glossedTokens := []
    context := "A supporting context."
    judgment := .acceptable
    alternatives := []
    readings := [("the teacher whom the girl has married", .acceptable), ("the teacher she is dreaming of", .acceptable)]
    paperFeatures := [("interpretation", "pragmatic")] }

def ex_6d : Datum :=
  { id := "viknerjensen2002_6d"
    source := ⟨"vikner-jensen-2002", "(6d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the girl's car"
    glossedTokens := []
    context := "A supporting context."
    judgment := .acceptable
    alternatives := []
    readings := [("the car which the girl has ordered", .acceptable), ("the car she has smashed to pieces", .acceptable)]
    paperFeatures := [("interpretation", "pragmatic")] }

def ex_7a : Datum :=
  { id := "viknerjensen2002_7a"
    source := ⟨"vikner-jensen-2002", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the car's teacher"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("lexical", .unacceptable), ("pragmatic", .acceptable)]
    paperFeatures := [("interpretation", "no lexical interpretation")] }

def ex_7b : Datum :=
  { id := "viknerjensen2002_7b"
    source := ⟨"vikner-jensen-2002", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the company's nose"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("lexical", .unacceptable), ("pragmatic", .acceptable)]
    paperFeatures := [("interpretation", "no lexical interpretation")] }

def ex_7d : Datum :=
  { id := "viknerjensen2002_7d"
    source := ⟨"vikner-jensen-2002", "(7d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the car's cake"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("lexical", .unacceptable), ("pragmatic", .acceptable)]
    paperFeatures := [("interpretation", "no lexical interpretation")] }

def ex_11a : Datum :=
  { id := "viknerjensen2002_11a"
    source := ⟨"vikner-jensen-2002", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "a girl's teacher"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("some girl has exactly one teacher, who is P", .acceptable)]
    paperFeatures := [("construction", "quantified possessor"), ("definite", "narrow scope")] }

def ex_11b : Datum :=
  { id := "viknerjensen2002_11b"
    source := ⟨"vikner-jensen-2002", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "each girl's teacher"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("each girl has exactly one teacher, who is P", .acceptable)]
    paperFeatures := [("construction", "quantified possessor"), ("definite", "narrow scope")] }

def ex_28a : Datum :=
  { id := "viknerjensen2002_28a"
    source := ⟨"vikner-jensen-2002", "(28a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A brother was standing in the yard."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("headNoun", "relational"), ("test", "isolation")] }

def ex_28b : Datum :=
  { id := "viknerjensen2002_28b"
    source := ⟨"vikner-jensen-2002", "(28b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "An edge was lying in the yard."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("headNoun", "dependent part"), ("test", "isolation")] }

def ex_29a : Datum :=
  { id := "viknerjensen2002_29a"
    source := ⟨"vikner-jensen-2002", "(29a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A car was parked in the yard."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("headNoun", "sortal"), ("test", "isolation")] }

def ex_29b : Datum :=
  { id := "viknerjensen2002_29b"
    source := ⟨"vikner-jensen-2002", "(29b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A wheel was lying in the yard."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("headNoun", "autonomous part"), ("test", "isolation")] }

def ex_38 : Datum :=
  { id := "viknerjensen2002_38"
    source := ⟨"barker-1995", ""⟩
    reportedIn := some ⟨"vikner-jensen-2002", "(38)"⟩
    language := "stan1293"
    primaryText := "A man walked in. His daughter was with him."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("use", "referent-introducing"), ("relationType", "inherent")] }

def ex_39a : Datum :=
  { id := "viknerjensen2002_39a"
    source := ⟨"barker-1995", ""⟩
    reportedIn := some ⟨"vikner-jensen-2002", "(39a)"⟩
    language := "stan1293"
    primaryText := "I saw John's car yesterday."
    glossedTokens := []
    context := "The car is a novel referent."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("use", "referent-introducing"), ("relationType", "control")] }

def ex_39b : Datum :=
  { id := "viknerjensen2002_39b"
    source := ⟨"barker-1995", ""⟩
    reportedIn := some ⟨"vikner-jensen-2002", "(39b)"⟩
    method := some .elicitation
    language := "stan1293"
    primaryText := "I saw John's bus yesterday."
    glossedTokens := []
    context := "The bus is a novel referent."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("use", "referent-introducing"), ("relationType", "control")] }

def ex_40b : Datum :=
  { id := "viknerjensen2002_40b"
    source := ⟨"barker-1995", ""⟩
    reportedIn := some ⟨"vikner-jensen-2002", "(40b)"⟩
    method := some .elicitation
    language := "stan1293"
    primaryText := "John accidentally snapped his stick."
    glossedTokens := []
    context := "The stick is a novel referent."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("use", "referent-introducing"), ("relationType", "control")] }

def ex_41b : Datum :=
  { id := "viknerjensen2002_41b"
    source := ⟨"vikner-jensen-2002", "(41b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Auster's apartment was on the eleventh floor"
    glossedTokens := []
    context := "Paul Auster, The New York Trilogy."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("use", "referent-introducing"), ("relationType", "control"), ("source", "fiction")] }

def ex_42c : Datum :=
  { id := "viknerjensen2002_42c"
    source := ⟨"vikner-jensen-2002", "(42c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A man walked in. He started talking about his theory of quasars and black holes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("use", "referent-introducing"), ("relationType", "agentive")] }

def s4_favourite_sister : Datum :=
  { id := "viknerjensen2002_s4_favourite_sister"
    source := ⟨"vikner-jensen-2002", "§4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary's favourite sister"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("the sister of Mary's that Mary prefers to have as her sister out of all of her sisters", .acceptable)]
    paperFeatures := [("construction", "favourite"), ("headNoun", "relational")] }

def s4_favourite_chair : Datum :=
  { id := "viknerjensen2002_s4_favourite_chair"
    source := ⟨"vikner-jensen-2002", "§4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary's favourite chair"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("the chair that Mary prefers to sit in out of all chairs", .acceptable)]
    paperFeatures := [("construction", "favourite"), ("headNoun", "sortal"), ("quale", "telic")] }

def s4_favourite_movie : Datum :=
  { id := "viknerjensen2002_s4_favourite_movie"
    source := ⟨"vikner-jensen-2002", "§4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary's favourite movie"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("the movie that Mary prefers to watch out of all the movies she has watched", .acceptable)]
    paperFeatures := [("construction", "favourite"), ("headNoun", "sortal"), ("quale", "telic")] }

def s4_favourite_sky : Datum :=
  { id := "viknerjensen2002_s4_favourite_sky"
    source := ⟨"vikner-jensen-2002", "§4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Anne's favourite sky"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("lexical", .unacceptable), ("sky when it looks a certain way that Anne especially likes", .acceptable), ("sky-representation the way Anne prefers to paint it in her landscapes", .acceptable)]
    paperFeatures := [("construction", "favourite"), ("headNoun", "sortal"), ("quale", "none")] }

def ex_50 : Datum :=
  { id := "viknerjensen2002_50"
    source := ⟨"vikner-jensen-2002", "(50)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John's favourite rabbit"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("lexical", .unacceptable), ("the breed of rabbit that John prefers to hunt", .acceptable), ("the rabbit John prefers to have as a pet", .acceptable)]
    paperFeatures := [("construction", "favourite"), ("headNoun", "sortal"), ("quale", "none")] }

def ex_51 : Datum :=
  { id := "viknerjensen2002_51"
    source := ⟨"vikner-jensen-2002", "(51)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Anne's favourite colour is blue"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("lexical", .unacceptable), ("blue is the colour which Anne prefers to look at", .acceptable), ("blue is the colour which Anne prefers to wear", .acceptable)]
    paperFeatures := [("construction", "favourite"), ("headNoun", "sortal"), ("quale", "none")] }

def all : List Datum := [ex_1a, ex_1b, ex_1c, ex_2a, ex_2b, ex_4, ex_5a, ex_5b, ex_5c, ex_5d, ex_6a, ex_6d, ex_7a, ex_7b, ex_7d, ex_11a, ex_11b, ex_28a, ex_28b, ex_29a, ex_29b, ex_38, ex_39a, ex_39b, ex_40b, ex_41b, ex_42c, s4_favourite_sister, s4_favourite_chair, s4_favourite_movie, s4_favourite_sky, ex_50, ex_51]

end ViknerJensen2002.Examples
