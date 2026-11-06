module

public import Linglib.Data.Examples.Schema

/-!
# `Sidner1979` — typed example data

Auto-generated from `Linglib/Data/Examples/Sidner1979.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Sidner1979.Examples`.
-/

@[expose] public section

namespace Sidner1979.Examples

def ex_22 : Datum :=
  { id := "sidner1979_22"
    source := ⟨"sidner-1979", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I took my sister to the zoo today."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "expectedFocus"), ("form", "plain"), ("expectedFocus", "my sister")] }

def ex_23 : Datum :=
  { id := "sidner1979_23"
    source := ⟨"sidner-1979", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There once was an old man who lived in the woods."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "expectedFocus"), ("form", "thereInsertion"), ("expectedFocus", "an old man")] }

def ex_24 : Datum :=
  { id := "sidner1979_24"
    source := ⟨"sidner-1979", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Linda talked with her dog all day long."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "expectedFocus"), ("form", "plain"), ("expectedFocus", "her dog")] }

def d2 : Datum :=
  { id := "sidner1979_d2"
    source := ⟨"sidner-1979", "D2 (chapter 4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is giving a surprise party at Hilda's house. It's at 340 Cherry St."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("it = Hilda's house", .acceptable)]
    paperFeatures := [("phenomenon", "recencyRule")] }

def d7 : Datum :=
  { id := "sidner1979_d7"
    source := ⟨"sidner-1979", "D7 (chapter 4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I lost a necklace at the office yesterday. I inherited it from my grandmother, and it meant a lot to me."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("it = the necklace", .acceptable)]
    paperFeatures := [("phenomenon", "nonAgentPronoun")] }

def d8 : Datum :=
  { id := "sidner1979_d8"
    source := ⟨"sidner-1979", "D8 (chapter 4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yesterday Max went to Bloomingdales with Ned and Winston on a shopping trip. While he was there, he bought some sneakers for his mother."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("he = Max", .acceptable)]
    paperFeatures := [("phenomenon", "agentPronoun")] }

def d9 : Datum :=
  { id := "sidner1979_d9"
    source := ⟨"sidner-1979", "D9 (chapter 4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I haven't seen Jeff for several days. Carl thinks he's studying for his exams. Oscar says he is sick, but I think he went to the Cape with Linda."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("he = Jeff throughout", .acceptable)]
    paperFeatures := [("phenomenon", "animateDiscourseFocusRule")] }

def d10 : Datum :=
  { id := "sidner1979_d10"
    source := ⟨"sidner-1979", "D10 (chapter 4), 2a"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John called up Mike yesterday. He wanted to discuss his physics homework."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("he = John", .acceptable)]
    paperFeatures := [("phenomenon", "agentPronoun")] }

def d14a : Datum :=
  { id := "sidner1979_d14a"
    source := ⟨"sidner-1979", "D14 (chapter 4), 2a"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I took my dog to the vet yesterday. He bit him in the hand."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("he = my dog, him = the vet", .acceptable)]
    paperFeatures := [("phenomenon", "actorAndDiscourseFocus")] }

def d14b : Datum :=
  { id := "sidner1979_d14b"
    source := ⟨"sidner-1979", "D14 (chapter 4), 2b"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I took my dog to the vet yesterday. He injected him with a new medicine."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("he = the vet, him = my dog", .acceptable)]
    paperFeatures := [("phenomenon", "actorAndDiscourseFocus")] }

def d25 : Datum :=
  { id := "sidner1979_d25"
    source := ⟨"sidner-1979", "D25 (chapter 2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Last week there were some nice strawberries in the refrigerator. They came from our food co-op and were unusually fresh."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("they = the strawberries", .acceptable)]
    paperFeatures := [("phenomenon", "focusConfirmation")] }

def d31 : Datum :=
  { id := "sidner1979_d31"
    source := ⟨"sidner-1979", "D31 (chapter 2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Wilbur is a fine scientist and a thoughtful guy. He gave me a book a while back which I really liked. It was on relativity theory. It talks about quarks. They are hard to imagine, because they indicate the need for elementary field theories of a complex nature. These theories are absolutely essential to all relativity research. Anyway, I got it while I was working on the initial part of my research. He's really a helpful colleague to have thought of giving it to me."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("it in the eighth sentence = the book", .acceptable)]
    paperFeatures := [("phenomenon", "focusPopping")] }

def d35 : Datum :=
  { id := "sidner1979_d35"
    source := ⟨"sidner-1979", "D35 (chapter 2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alfred and Zohar liked to play baseball. They played it everyday after school before dinner. After their game, Alfred and Zohar had ice cream cones. They tasted really good. Alfred always had the vanilla super scooper, while Zohar tried the flavor of the day cone. After the cones had been eaten, the boys went home to study."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("they in the fourth sentence = the ice cream cones", .acceptable)]
    paperFeatures := [("phenomenon", "focusMovement")] }

def all : List Datum := [ex_22, ex_23, ex_24, d2, d7, d8, d9, d10, d14a, d14b, d25, d31, d35]

end Sidner1979.Examples
