module

public import Linglib.Data.Examples.Schema

/-!
# `Ariel2001` — typed example data

Auto-generated from `Linglib/Data/Examples/Ariel2001.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Ariel2001.Examples`.
-/

@[expose] public section

namespace Ariel2001.Examples

def ex_1 : Datum :=
  { id := "ariel2001_1"
    source := ⟨"ariel-2001", "(1)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Melissa: Well, I'll say awakened, cause that's what I have written down. Ron: (Sniff). Frank: Just watch, He'll put a note by it – note by that. I really like that word Melissa."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "proxDem"), ("marker", "unstressedPron"), ("marker", "distalDem"), ("marker", "distalDemNP")] }

def ex_3 : Datum :=
  { id := "ariel2001_3"
    source := ⟨"ariel-2001", "(3)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "In the complaint the woman claimed that on May 2, ∅ met Roter … Then the two demanded from her to have sex with them. According to her, when ∅ refused, Roter started punching her …"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("source", "Haaretz"), ("perspective", "victim"), ("victim", "zero"), ("rapists", "lastName")] }

def ex_4 : Datum :=
  { id := "ariel2001_4"
    source := ⟨"ariel-2001", "(4)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "According to the police, Roter and the rape victim met in the beginning of May … and at a certain point ∅ asked the rape victim to have sex with them. This one refused, and as a result, the two cruelly raped her …"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("source", "Maariv"), ("perspective", "rapists"), ("victim", "proxDem"), ("rapists", "zero")] }

def ex_5 : Datum :=
  { id := "ariel2001_5"
    source := ⟨"ariel-2001", "(5)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "But I insisted then. A person devoted two months and a half, ∅ built a whole program, ∅ took care of a budget, it is not as if Minister Katzav gave me, I took care, I went …"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("speaker", "self")] }

def ex_6 : Datum :=
  { id := "ariel2001_6"
    source := ⟨"ariel-2001", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In the garden, I saw a young girl kicking a tree. I looked at them for a while."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "girl and tree"), ("marker", "unstressedPron")] }

def ex_7 : Datum :=
  { id := "ariel2001_7"
    source := ⟨"ariel-2001", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Morris: We broke a STRING, Or HE broke a string"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "stressedPron")] }

def ex_8a : Datum :=
  { id := "ariel2001_8a"
    source := ⟨"ariel-2001", "(8a)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "Arafat invited Kadafi to pray in Jerusalem, when ∅ will be the Palestinian capital"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "headline"), ("marker", "lastName"), ("marker", "lastName"), ("marker", "fullName"), ("marker", "zero")] }

def ex_8b : Datum :=
  { id := "ariel2001_8b"
    source := ⟨"ariel-2001", "(8b)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "The Palestinian authority chair, Yassir Arafat, invited the Lybian leader, Muamar Kadafi, to pray in Eastern Jerusalem, when this one will become the capital of the Palestinian state"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "opening sentence"), ("marker", "fullNameMod"), ("marker", "fullNameMod"), ("marker", "fullNameMod"), ("marker", "proxDem")] }

def ex_9 : Datum :=
  { id := "ariel2001_9"
    source := ⟨"ariel-2001", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Frankly, I'm torn my own self as to which way to raise hell"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "stressedPron")] }

def ex_10 : Datum :=
  { id := "ariel2001_10"
    source := ⟨"ariel-2001", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "REBECCA: put the newspaper on his lap, RICKIE: Yeah, REBECCA: ∅ masturbated, and then lifted the paper up, RICKIE: Yeah, REBECCA: for her to see"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("the paper coreferent with the newspaper", .acceptable)]
    paperFeatures := [("marker", "shortDefDescription"), ("marker", "shortDefDescription")] }

def ex_12 : Datum :=
  { id := "ariel2001_12"
    source := ⟨"ariel-2001", "(12)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "It is not as if he looks like a hippie really, or anything like that. … Feil's grey-brown hair … covers his collar from behind. But one day in 93' the officer in charge of him demanded from him to have a haircut … The officer accused him …"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("topicMarker", "unstressedPron"), ("subjectMarker", "shortDefDescription")] }

def maya_rachel : Datum :=
  { id := "ariel2001_maya_rachel"
    source := ⟨"ariel-2001", "§1.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Maya kissed Rachel. And then she/SHE …"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("she = Maya", .acceptable), ("SHE = Rachel", .acceptable)]
    paperFeatures := [("maya", "unstressedPron"), ("rachel", "stressedPron")] }

def all : List Datum := [ex_1, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8a, ex_8b, ex_9, ex_10, ex_12, maya_rachel]

end Ariel2001.Examples
