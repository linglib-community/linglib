module

public import Linglib.Data.Examples.Schema

/-!
# `Elliott2020` — typed example data

Auto-generated from `Linglib/Data/Examples/Elliott2020.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Elliott2020.Examples`.
-/

@[expose] public section

namespace Elliott2020.Examples

def ex_1 : Datum :=
  { id := "elliott2020_1"
    source := ⟨"elliott-2020", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I invited a philosopher; I'm relieved that she came."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1")] }

def ex_2 : Datum :=
  { id := "elliott2020_2"
    source := ⟨"elliott-2020", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone who invited a philosopher was relieved that she came."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1")] }

def ex_3a : Datum :=
  { id := "elliott2020_3a"
    source := ⟨"elliott-2020", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone who read any of these books and subsequently criticized it is a charlatan."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1.1")] }

def ex_3b : Datum :=
  { id := "elliott2020_3b"
    source := ⟨"elliott-2020", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone who read any of these books recommended it to their friends."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1.1")] }

def ex_4 : Datum :=
  { id := "elliott2020_4"
    source := ⟨"elliott-2020", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not true that any philosopher attended this talk. She was unwell."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1.1")] }

def ex_5 : Datum :=
  { id := "elliott2020_5"
    source := ⟨"elliott-2020", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No philosopher attended this talk. She was unwell."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1.1")] }

def ex_6 : Datum :=
  { id := "elliott2020_6"
    source := ⟨"elliott-2020", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not true that no philosopher is attending this talk; She's sitting in the back!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1.1")] }

def ex_7 : Datum :=
  { id := "elliott2020_7"
    source := ⟨"elliott-2020", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A philosopher is attending this talk; She's sitting in the back."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1.1")] }

def ex_8a : Datum :=
  { id := "elliott2020_8a"
    source := ⟨"elliott-2020", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either there is no bathroom, or the bathroom is upstairs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1.1")] }

def ex_8b : Datum :=
  { id := "elliott2020_8b"
    source := ⟨"elliott-2020", "(8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either there is no bathroom, or it's upstairs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1.1")] }

def ex_9 : Datum :=
  { id := "elliott2020_9"
    source := ⟨"elliott-2020", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either there is no bathroom, or there isn't no bathroom and it's upstairs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1.1")] }

def ex_10a : Datum :=
  { id := "elliott2020_10a"
    source := ⟨"elliott-2020", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A philosopher is attending this talk and she's sitting in the back."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1.2")] }

def ex_10b : Datum :=
  { id := "elliott2020_10b"
    source := ⟨"elliott-2020", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She's sitting in the back and a philosopher is attending this talk."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1.2")] }

def ex_21 : Datum :=
  { id := "elliott2020_21"
    source := ⟨"elliott-2020", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not the case that anyone walked in."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.4.4")] }

def ex_31 : Datum :=
  { id := "elliott2020_31"
    source := ⟨"elliott-2020", "(31)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either nobody walked in or they didn't sit down."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.7")] }

def ex_37 : Datum :=
  { id := "elliott2020_37"
    source := ⟨"elliott-2020", "(37)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If anyone is outside, then they are happy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("universal: everyone outside is happy", .acceptable)]
    paperFeatures := [("section", "2.9")] }

def ex_44 : Datum :=
  { id := "elliott2020_44"
    source := ⟨"elliott-2020", "(44)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either this house hasn't been renovated, or there's a bathroom."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1")] }

def ex_45 : Datum :=
  { id := "elliott2020_45"
    source := ⟨"elliott-2020", "(45)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either this house hasn't been renovated, or there's a bathroom. It's upstairs."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1")] }

def ex_46 : Datum :=
  { id := "elliott2020_46"
    source := ⟨"elliott-2020", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If this house has been renovated, then there's a bathroom. It's upstairs."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1")] }

def ex_47 : Datum :=
  { id := "elliott2020_47"
    source := ⟨"elliott-2020", "(47)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either a philosopher is in the audience or a linguist is. Either way, I hope she enjoys it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2")] }

def ex_48 : Datum :=
  { id := "elliott2020_48"
    source := ⟨"elliott-2020", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either it's a weekday, or a critic is watching our play. It's Saturday. They'd better give us a good review."
    glossedTokens := []
    context := "A director who has lost track of the day is certain that different critics attend on Saturday and Sunday; the assistant knows the day."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3")] }

def ex_49 : Datum :=
  { id := "elliott2020_49"
    source := ⟨"elliott-2020", "(49)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If it's the weekend, then a critic is watching our play. It's Saturday. They'd better give us a good review."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3")] }

def ex_51 : Datum :=
  { id := "elliott2020_51"
    source := ⟨"elliott-2020", "(51)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either someone was in the audience or the event was a disaster."
    glossedTokens := []
    context := "It is common ground that someone was in the audience."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.6")] }

def ex_52a : Datum :=
  { id := "elliott2020_52a"
    source := ⟨"elliott-2020", "(52a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either someone was in the audience, or the event was a disaster."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.6")] }

def ex_55 : Datum :=
  { id := "elliott2020_55"
    source := ⟨"elliott-2020", "(55)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either someone was in the audience, or the event was a disaster. She enjoyed it."
    glossedTokens := []
    context := "total ignorance"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.6")] }

def ex_56 : Datum :=
  { id := "elliott2020_56"
    source := ⟨"elliott-2020", "(56)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either someone was in the audience, or the event was a disaster. Actually, the event wasn't a disaster. So, I hope she enjoyed it."
    glossedTokens := []
    context := "total ignorance"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.6")] }

def ex_58 : Datum :=
  { id := "elliott2020_58"
    source := ⟨"elliott-2020", "(58)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either a linguist is here, or a philosopher is."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.7")] }

def ex_61 : Datum :=
  { id := "elliott2020_61"
    source := ⟨"elliott-2020", "(61)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A linguist is here and a philosopher is here."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.7")] }

def ex_65 : Datum :=
  { id := "elliott2020_65"
    source := ⟨"elliott-2020", "(65)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either someone is in the audience, or they're sitting down."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.8")] }

def ex_67 : Datum :=
  { id := "elliott2020_67"
    source := ⟨"elliott-2020", "(67)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either someone is in the audience, or the person in the audience is sitting down."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.8")] }

def ex_68 : Datum :=
  { id := "elliott2020_68"
    source := ⟨"elliott-2020", "(68)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either someone is in the audience, or someone in the audience is sitting down."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.8")] }

def ex_71a : Datum :=
  { id := "elliott2020_71a"
    source := ⟨"elliott-2020", "(71a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not the case that nobody is in the audience and they're sitting down."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.9")] }

def ex_78 : Datum :=
  { id := "elliott2020_78"
    source := ⟨"elliott-2020", "(78)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not true that someone is in the audience and someone in the audience is sitting down."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.9")] }

def ex_79 : Datum :=
  { id := "elliott2020_79"
    source := ⟨"elliott-2020", "(79)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not the case that someone walked in and they sat down."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.9")] }

def ex_80 : Datum :=
  { id := "elliott2020_80"
    source := ⟨"elliott-2020", "(80)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not the case that both someone is in the audience and they have a question. Well, the auditorium isn't empty. I hope they enjoyed the lecture."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.9")] }

def ex_81 : Datum :=
  { id := "elliott2020_81"
    source := ⟨"elliott-2020", "(81)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone who either has no credit card or paid with it has left the restaurant."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("existential: anyone with a credit card they paid with has left", .acceptable)]
    paperFeatures := [("section", "4.1")] }

def ex_82 : Datum :=
  { id := "elliott2020_82"
    source := ⟨"elliott-2020", "(82)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Logan doesn't have no credit card. They're on the table."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.1")] }

def ex_92 : Datum :=
  { id := "elliott2020_92"
    source := ⟨"elliott-2020", "(92)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If anyone is here, then they are unhappy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("universal: everyone here is unhappy", .acceptable)]
    paperFeatures := [("section", "B")] }

def ex_93 : Datum :=
  { id := "elliott2020_93"
    source := ⟨"elliott-2020", "(93)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either nobody is here, or they are unhappy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "B")] }

def ex_94a : Datum :=
  { id := "elliott2020_94a"
    source := ⟨"elliott-2020", "(94a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The boys played chess."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("universal: every boy played chess", .acceptable), ("existential: some boy played chess", .unacceptable)]
    paperFeatures := [("section", "B")] }

def ex_94b : Datum :=
  { id := "elliott2020_94b"
    source := ⟨"elliott-2020", "(94b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The boys didn't play chess."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("negated universal: not every boy played chess", .unacceptable), ("negated existential: no boy played chess", .acceptable)]
    paperFeatures := [("section", "B")] }

def ex_98 : Datum :=
  { id := "elliott2020_98"
    source := ⟨"elliott-2020", "(98)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If everyone is here, then they're happy."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "B")] }

def ex_100 : Datum :=
  { id := "elliott2020_100"
    source := ⟨"elliott-2020", "(100)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Someone who is here is unhappy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "B")] }

def ex_101 : Datum :=
  { id := "elliott2020_101"
    source := ⟨"elliott-2020", "(101)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone who is here is unhappy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "B")] }

def all : List Datum := [ex_1, ex_2, ex_3a, ex_3b, ex_4, ex_5, ex_6, ex_7, ex_8a, ex_8b, ex_9, ex_10a, ex_10b, ex_21, ex_31, ex_37, ex_44, ex_45, ex_46, ex_47, ex_48, ex_49, ex_51, ex_52a, ex_55, ex_56, ex_58, ex_61, ex_65, ex_67, ex_68, ex_71a, ex_78, ex_79, ex_80, ex_81, ex_82, ex_92, ex_93, ex_94a, ex_94b, ex_98, ex_100, ex_101]

end Elliott2020.Examples
