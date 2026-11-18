module

public import Linglib.Data.Examples.Schema

/-!
# `Heim1994a` — typed example data

Auto-generated from `Linglib/Data/Examples/Heim1994a.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Heim1994a.Examples`.
-/

@[expose] public section

namespace Heim1994a.Examples

def s2 : Datum :=
  { id := "heim1994a_s2"
    source := ⟨"heim-1994-comments", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John cried."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("lf", "John PAST1 cry"), ("presupposition", "g(1) < t_c")] }

def s5 : Datum :=
  { id := "heim1994a_s5"
    source := ⟨"heim-1994-comments", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John was in Paris at some time."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("lf", "(6): (at) some time λ3 [John PAST3 be in Paris]"), ("presupposition", "every time in the restriction precedes t_c")] }

def s11 : Datum :=
  { id := "heim1994a_s11"
    source := ⟨"heim-1994-comments", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John believed Bill to be asleep."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("lf", "(12): John PAST1 believe λ0 [Bill to0 be asleep]"), ("reading", "simultaneous only")] }

def s13a : Datum :=
  { id := "heim1994a_s13a"
    source := ⟨"heim-1994-comments", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "When she was in her twenties, she thought she was unhappy on her 40th birthday."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2"), ("ulc", "cannot describe the situation of (13b)")] }

def s13b : Datum :=
  { id := "heim1994a_s13b"
    source := ⟨"heim-1994-comments", "(13b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "When she was in her twenties, she thought she would be unhappy on her 40th birthday."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2")] }

def s14a : Datum :=
  { id := "heim1994a_s14a"
    source := ⟨"heim-1994-comments", "(14a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John said that he had never been in Paris yet, but that he went there at some time in his life."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2"), ("ulc", "cannot describe the situation of (14b)")] }

def s14b : Datum :=
  { id := "heim1994a_s14b"
    source := ⟨"heim-1994-comments", "(14b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John said that he had never been in Paris yet, but that he would go there at some time in his life."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2")] }

def s19 : Datum :=
  { id := "heim1994a_s19"
    source := ⟨"heim-1994-comments", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John believed that Bill was happy on his 40th birthday."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2"), ("lf", "(20): John PAST1 believe λ0 [his 40th birthday λ2 [Bill PAST2 be happy]]"), ("presupposition", "(i) John believed the birthday to precede t_c; (ii) he located himself at or after it")] }

def s22 : Datum :=
  { id := "heim1994a_s22"
    source := ⟨"heim-1994-comments", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John thought that Bill was only 39, and he wondered whether he was happy on his 40th birthday."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2")] }

def s23 : Datum :=
  { id := "heim1994a_s23"
    source := ⟨"heim-1994-comments", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John thought that Bill was only 39, and he wondered whether he would be happy on his 40th birthday."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2")] }

def s24 : Datum :=
  { id := "heim1994a_s24"
    source := ⟨"heim-1994-comments", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John will cry."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2"), ("lf", "(25): PRES1 woll λ0 [John INF0 cry]"), ("entry", "(26): woll shifts the evaluation time forward")] }

def s27 : Datum :=
  { id := "heim1994a_s27"
    source := ⟨"heim-1994-comments", "(27)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She will marry a man who loves her."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2"), ("lf", "PRES1 woll λ0 [a man who PRES0 love her λ2 [she INF0 marry t2]]")] }

def s28 : Datum :=
  { id := "heim1994a_s28"
    source := ⟨"heim-1994-comments", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John believed that Bill was asleep."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2"), ("lf", "(29) simultaneous, John PAST1 believe λ0 [Bill PAST0 be asleep]; (32) back-shifted through res-movement"), ("readings", "simultaneous; back-shifted")] }

def s34 : Datum :=
  { id := "heim1994a_s34"
    source := ⟨"heim-1994-comments", "(34)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "When I woke up, I was convinced I had overslept. I wondered what happened at six when the alarm went off. I figured I probably turned it off in my sleep. Then I realized it was only five o'clock."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2"), ("lf", "(35): a de re report about six o'clock with g_c(1) = 5 o'clock, g_c(2) = 6 o'clock")] }

def s36 : Datum :=
  { id := "heim1994a_s36"
    source := ⟨"heim-1994-comments", "(36)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John thought Mary is pregnant."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2"), ("lf", "(38): John PAST1 think PRES2 λ3 λ0 [Mary t3 be pregnant]"), ("reading", "double access")] }

def s39 : Datum :=
  { id := "heim1994a_s39"
    source := ⟨"heim-1994-comments", "(39)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He will think that he is sick."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("counterexample", "PRES overlapping t_c")] }

def s40 : Datum :=
  { id := "heim1994a_s40"
    source := ⟨"heim-1994-comments", "(40)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He will think that he was sick."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("counterexample", "PAST preceding t_c")] }

def s41 : Datum :=
  { id := "heim1994a_s41"
    source := ⟨"heim-1994-comments", "(41)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I will use an iron that is hot."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3")] }

def s42 : Datum :=
  { id := "heim1994a_s42"
    source := ⟨"heim-1994-comments", "(42)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I will charge you whatever time it took."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3")] }

def s43 : Datum :=
  { id := "heim1994a_s43"
    source := ⟨"heim-1994-comments", "(43)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He decided a week ago that in ten days he would say to his mother that they were having their last meal together."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("source", "Abusch 1988"), ("lf", "(51)"), ("licensing", "the lowest PAST licensed non-locally by <-decide")] }

def s44 : Datum :=
  { id := "heim1994a_s44"
    source := ⟨"heim-1994-comments", "(44)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He said he would buy a fish that was still alive."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("source", "Ogihara 1989"), ("lf", "(52)"), ("licensing", "the lowest PAST licensed non-locally by <-say")] }

def s45 : Datum :=
  { id := "heim1994a_s45"
    source := ⟨"heim-1994-comments", "(45)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He decided to jump before they fired."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("source", "A. Santisteban, p.c.")] }

def s54 : Datum :=
  { id := "heim1994a_s54"
    source := ⟨"heim-1994-comments", "(54)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John was looking for a man who lives next door."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("lf", "(55): the object NP raised out of the argument of <-be looking for"), ("reading", "transparent only")] }

def s59 : Datum :=
  { id := "heim1994a_s59"
    source := ⟨"heim-1994-comments", "(59)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John met the man who lived next door."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("lf", "(60): John PAST1 <-meet [the man who PAST2 ¬<-live next door]")] }

def all : List Datum := [s2, s5, s11, s13a, s13b, s14a, s14b, s19, s22, s23, s24, s27, s28, s34, s36, s39, s40, s41, s42, s43, s44, s45, s54, s59]

end Heim1994a.Examples
