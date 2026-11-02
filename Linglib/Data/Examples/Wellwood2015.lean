module

public import Linglib.Data.Examples.Schema

/-!
# `Wellwood2015` — typed example data

Auto-generated from `Linglib/Data/Examples/Wellwood2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Wellwood2015.Examples`.
-/

@[expose] public section

namespace Wellwood2015.Examples

def felicity_mass : Datum :=
  { id := "wellwood2015_felicity_mass"
    source := ⟨"wellwood-2015", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Al bought more coffee than Bill did."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("category", "massNoun")] }

def felicity_count : Datum :=
  { id := "wellwood2015_felicity_count"
    source := ⟨"wellwood-2015", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Al has more idea than Bill does."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("category", "countNoun")] }

def felicity_atelic : Datum :=
  { id := "wellwood2015_felicity_atelic"
    source := ⟨"wellwood-2015", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Al ran more than Bill did."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("category", "atelicVP")] }

def felicity_telic : Datum :=
  { id := "wellwood2015_felicity_telic"
    source := ⟨"wellwood-2015", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Al graduated high school more than Bill did."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("category", "telicVP")] }

def felicity_ga : Datum :=
  { id := "wellwood2015_felicity_ga"
    source := ⟨"wellwood-2015", "(59)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Al's coffee is hotter than Bill's is."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("category", "gradableAdj")] }

def felicity_nonga : Datum :=
  { id := "wellwood2015_felicity_nonga"
    source := ⟨"wellwood-2015", "(53a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This piece of wood is more wooden than that one is."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("category", "nonGradableAdj")] }

def dim_82a_hotter : Datum :=
  { id := "wellwood2015_dim_82a_hotter"
    source := ⟨"wellwood-2015", "ex. (82a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This coffee is hotter than that coffee is."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("category", "gradableAdj"), ("measuredDomain", "state"), ("dimension", "temperature"), ("intensive", "true")] }

def dim_82b_harder : Datum :=
  { id := "wellwood2015_dim_82b_harder"
    source := ⟨"wellwood-2015", "ex. (82b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This plastic is harder than that plastic is."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("category", "gradableAdj"), ("measuredDomain", "state"), ("dimension", "hardness"), ("intensive", "true")] }

def dim_83a_more_coffee : Datum :=
  { id := "wellwood2015_dim_83a_more_coffee"
    source := ⟨"wellwood-2015", "ex. (83a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Al has more coffee than Bill does."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("category", "massNoun"), ("measuredDomain", "entity"), ("dimension", "volume"), ("intensive", "false")] }

def dim_83b_more_plastic : Datum :=
  { id := "wellwood2015_dim_83b_more_plastic"
    source := ⟨"wellwood-2015", "ex. (83b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Al has more plastic than Bill does."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("category", "massNoun"), ("measuredDomain", "entity"), ("dimension", "weight"), ("intensive", "false")] }

def dim_84a_fuller : Datum :=
  { id := "wellwood2015_dim_84a_fuller"
    source := ⟨"wellwood-2015", "ex. (84a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This glass is fuller than that glass is."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("category", "gradableAdj"), ("measuredDomain", "state"), ("dimension", "volume"), ("intensive", "false")] }

def dim_84b_heavier : Datum :=
  { id := "wellwood2015_dim_84b_heavier"
    source := ⟨"wellwood-2015", "ex. (84b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This plastic is heavier than that plastic is."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("category", "gradableAdj"), ("measuredDomain", "state"), ("dimension", "weight"), ("intensive", "false")] }

def dim_85a_more_heat : Datum :=
  { id := "wellwood2015_dim_85a_more_heat"
    source := ⟨"wellwood-2015", "ex. (85a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This rock has more heat than that one does."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("category", "massNoun"), ("measuredDomain", "state"), ("dimension", "temperature"), ("intensive", "true")] }

def dim_85b_more_firmness : Datum :=
  { id := "wellwood2015_dim_85b_more_firmness"
    source := ⟨"wellwood-2015", "ex. (85b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This mattress has more firmness than that one does."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("category", "massNoun"), ("measuredDomain", "state"), ("dimension", "hardness"), ("intensive", "true")] }

def dim_89a_sped_up : Datum :=
  { id := "wellwood2015_dim_89a_sped_up"
    source := ⟨"wellwood-2015", "ex. (89a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Al sped up more than Peter did."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("category", "atelicVP"), ("measuredDomain", "event"), ("dimension", "speed"), ("intensive", "true")] }

def dim_87a_drove : Datum :=
  { id := "wellwood2015_dim_87a_drove"
    source := ⟨"wellwood-2015", "ex. (87a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Al drove more than Peter did."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("category", "atelicVP"), ("measuredDomain", "event"), ("dimension", "distance"), ("intensive", "false")] }

def very_ga : Datum :=
  { id := "wellwood2015_very_ga"
    source := ⟨"wellwood-2015", "(118)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Al wasn't very intelligent."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Al wasn't very much intelligent.", .ungrammatical)]
    readings := []
    paperFeatures := [("category", "gradableAdj"), ("requiresOvertMuch", "false")] }

def very_noun : Datum :=
  { id := "wellwood2015_very_noun"
    source := ⟨"wellwood-2015", "(117a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Al didn't eat very much soup."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Al didn't eat very soup.", .ungrammatical)]
    readings := []
    paperFeatures := [("category", "massNoun"), ("requiresOvertMuch", "true")] }

def very_verb : Datum :=
  { id := "wellwood2015_very_verb"
    source := ⟨"wellwood-2015", "(117b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Al didn't run very much."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Al didn't run very.", .ungrammatical)]
    readings := []
    paperFeatures := [("category", "atelicVP"), ("requiresOvertMuch", "true")] }

def shift_104_rock : Datum :=
  { id := "wellwood2015_shift_104_rock"
    source := ⟨"wellwood-2015", "(104a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Al found more rock than Bill did."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Al found more rocks than Bill did.", .acceptable)]
    readings := []
    paperFeatures := [("shift", "numberMorphology")] }

def shift_105_run : Datum :=
  { id := "wellwood2015_shift_105_run"
    source := ⟨"wellwood-2015", "(105a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Al ran in the park more than Bill did."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Al ran to the park more than Bill did.", .acceptable)]
    readings := []
    paperFeatures := [("shift", "telicization")] }

def all : List Datum := [felicity_mass, felicity_count, felicity_atelic, felicity_telic, felicity_ga, felicity_nonga, dim_82a_hotter, dim_82b_harder, dim_83a_more_coffee, dim_83b_more_plastic, dim_84a_fuller, dim_84b_heavier, dim_85a_more_heat, dim_85b_more_firmness, dim_89a_sped_up, dim_87a_drove, very_ga, very_noun, very_verb, shift_104_rock, shift_105_run]

end Wellwood2015.Examples
