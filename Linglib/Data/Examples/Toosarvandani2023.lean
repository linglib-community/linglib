module

public import Linglib.Data.Examples.Schema

/-!
# `Toosarvandani2023` — typed example data

Auto-generated from `Linglib/Data/Examples/Toosarvandani2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Toosarvandani2023.Examples`.
-/

@[expose] public section

namespace Toosarvandani2023.Examples

def ex_16a : Datum :=
  { id := "toosarvandani2023_16a"
    source := ⟨"toosarvandani-2023", "(16a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We are (both) behind the gift shop."
    glossedTokens := []
    context := "Paul is by himself at his town's small zoo, visiting the lion's cage. After seeing a picture of Paul with the lion on Instagram, his friend Josie decides to come meet him. She has never been to the zoo before and does not know where any animals are located. Josie calls Paul, saying: 'I saw you in a picture with the lion. Where are you?'"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("pronoun", "1pl"), ("group", "speaker and lion"), ("property", "context-dependence")] }

def ex_16b : Datum :=
  { id := "toosarvandani2023_16b"
    source := ⟨"toosarvandani-2023", "(16b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They are (both) behind the gift shop."
    glossedTokens := []
    context := "Paul is by himself at his town's small zoo, visiting the lion's cage. After seeing a picture of Paul with the lion on Instagram, his friend Josie decides to come meet him. She has never been to the zoo before and does not know where any animals are located. Josie asks a zoo ranger: 'I saw my friend in a picture with the lion. Where are they?'"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("pronoun", "3pl"), ("group", "Paul and lion"), ("property", "context-dependence")] }

def ex_17a : Datum :=
  { id := "toosarvandani2023_17a"
    source := ⟨"toosarvandani-2023", "(17a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We are (both) behind the oak tree."
    glossedTokens := []
    context := "Sam is at the dog park with his beloved Doberman Pinscher Franz. His friend Leslie is supposed to meet him somewhere inside. Leslie calls Sam, saying: 'Are you here with Franz? Where are you?'"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("pronoun", "1pl"), ("group", "speaker and pet dog"), ("property", "context-dependence")] }

def ex_18a : Datum :=
  { id := "toosarvandani2023_18a"
    source := ⟨"toosarvandani-2023", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We are (both) in the field at the edge of town."
    glossedTokens := []
    context := "Maria is an avid skydiver. One day after a jump, she is blown off course. She calls the skydiving company to come pick her up. The receptionist who answers the phone says: 'We will come pick you up. We will also pick up your parachute at the same time. Where are you?'"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("pronoun", "1pl"), ("group", "speaker and parachute"), ("property", "context-dependence")] }

def ex_77a : Datum :=
  { id := "toosarvandani2023_77a"
    source := ⟨"toosarvandani-2023", "(77a)"⟩
    reportedIn := none
    language := "yala1267"
    primaryText := "Bet=gak=a'=ba'."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "1sg"), ("object", "3.an"), ("configuration", "1 > 3"), ("cliticization", "both")] }

def ex_77b : Datum :=
  { id := "toosarvandani2023_77b"
    source := ⟨"toosarvandani-2023", "(77b)"⟩
    reportedIn := none
    language := "yala1267"
    primaryText := "Bnaw=ba'=a'."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("subject", "3.an"), ("object", "1sg"), ("configuration", "3 > 1"), ("cliticization", "object blocked")] }

def ex_78a : Datum :=
  { id := "toosarvandani2023_78a"
    source := ⟨"toosarvandani-2023", "(78a)"⟩
    reportedIn := none
    language := "yala1267"
    primaryText := "Bet=te=o'=ba'."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "2sg"), ("object", "3.an"), ("configuration", "2 > 3"), ("cliticization", "both")] }

def ex_78b : Datum :=
  { id := "toosarvandani2023_78b"
    source := ⟨"toosarvandani-2023", "(78b)"⟩
    reportedIn := none
    language := "yala1267"
    primaryText := "Bet=te=ba'=o'."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("subject", "3.an"), ("object", "2sg"), ("configuration", "3 > 2"), ("cliticization", "object blocked")] }

def ex_79a : Datum :=
  { id := "toosarvandani2023_79a"
    source := ⟨"toosarvandani-2023", "(79a)"⟩
    reportedIn := none
    language := "yala1267"
    primaryText := "Wkwell=e'=be'."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "3.el"), ("object", "3.hu"), ("configuration", "3.el > 3.hu"), ("cliticization", "both")] }

def ex_79b : Datum :=
  { id := "toosarvandani2023_79b"
    source := ⟨"toosarvandani-2023", "(79b)"⟩
    reportedIn := none
    language := "yala1267"
    primaryText := "Wkwell=be'=e'."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("subject", "3.hu"), ("object", "3.el"), ("configuration", "3.hu > 3.el"), ("cliticization", "object blocked")] }

def ex_80a : Datum :=
  { id := "toosarvandani2023_80a"
    source := ⟨"toosarvandani-2023", "(80a)"⟩
    reportedIn := none
    language := "yala1267"
    primaryText := "Bchew=be'=ba'."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "3.hu"), ("object", "3.an"), ("configuration", "3.hu > 3.an"), ("cliticization", "both")] }

def ex_80b : Datum :=
  { id := "toosarvandani2023_80b"
    source := ⟨"toosarvandani-2023", "(80b)"⟩
    reportedIn := none
    language := "yala1267"
    primaryText := "Bdinn=ba'=be'."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("subject", "3.an"), ("object", "3.hu"), ("configuration", "3.an > 3.hu"), ("cliticization", "object blocked")] }

def ex_81a : Datum :=
  { id := "toosarvandani2023_81a"
    source := ⟨"toosarvandani-2023", "(81a)"⟩
    reportedIn := none
    language := "yala1267"
    primaryText := "Bchochj=ba'=n."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "3.an"), ("object", "3.in"), ("configuration", "3.an > 3.in"), ("cliticization", "both")] }

def ex_81b : Datum :=
  { id := "toosarvandani2023_81b"
    source := ⟨"toosarvandani-2023", "(81b)"⟩
    reportedIn := none
    language := "yala1267"
    primaryText := "Bchochj=en=ba'."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("subject", "3.in"), ("object", "3.an"), ("configuration", "3.in > 3.an"), ("cliticization", "object blocked")] }

def all : List Datum := [ex_16a, ex_16b, ex_17a, ex_18a, ex_77a, ex_77b, ex_78a, ex_78b, ex_79a, ex_79b, ex_80a, ex_80b, ex_81a, ex_81b]

end Toosarvandani2023.Examples
