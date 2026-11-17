module

public import Linglib.Data.Examples.Schema

/-!
# `DeoThomas2025` — typed example data

Auto-generated from `Linglib/Data/Examples/DeoThomas2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace DeoThomas2025.Examples`.
-/

@[expose] public section

namespace DeoThomas2025.Examples

def ex_1a : Datum :=
  { id := "deothomas2025_1a"
    source := ⟨"deo-thomas-2025", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary invited just John and Mike."
    glossedTokens := []
    context := "A: Who did Mary invite to the party?"
    judgment := .acceptable
    contrasts := [("Mary invited only John and Mike.", .acceptable)]
    readings := []
    paperFeatures := [("flavor", "complementExclusion"), ("only", "yes")] }

def ex_1b : Datum :=
  { id := "deothomas2025_1b"
    source := ⟨"deo-thomas-2025", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No, John is just a sophomore."
    glossedTokens := []
    context := "A: Is John graduating this Spring?"
    judgment := .acceptable
    contrasts := [("No, John is only a sophomore.", .acceptable)]
    readings := []
    paperFeatures := [("flavor", "rankOrder"), ("only", "yes")] }

def ex_2d : Datum :=
  { id := "deothomas2025_2d"
    source := ⟨"deo-thomas-2025", "(2d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Just the thought of you sends shivers down my spine."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Only the thought of you sends shivers down my spine.", .unacceptable)]
    readings := []
    paperFeatures := [("flavor", "minimalSufficiency"), ("only", "no")] }

def ex_3a : Datum :=
  { id := "deothomas2025_3a"
    source := ⟨"deo-thomas-2025", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She just went to Spain and Portugal."
    glossedTokens := []
    context := "A: Where did Mary go for her vacation this year?"
    judgment := .acceptable
    contrasts := [("She only went to Spain and Portugal.", .acceptable)]
    readings := []
    paperFeatures := [("flavor", "complementExclusion"), ("only", "yes"), ("case", "37a")] }

def ex_3b : Datum :=
  { id := "deothomas2025_3b"
    source := ⟨"deo-thomas-2025", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She is just an intern."
    glossedTokens := []
    context := "A: What is Mary's job at the hospital?"
    judgment := .acceptable
    contrasts := [("She is only an intern.", .acceptable)]
    readings := []
    paperFeatures := [("flavor", "rankOrder"), ("only", "yes"), ("case", "37a")] }

def ex_4a : Datum :=
  { id := "deothomas2025_4a"
    source := ⟨"beaver-clark-2008", "p. 252"⟩
    reportedIn := some ⟨"deo-thomas-2025", "(4a)"⟩
    language := "stan1293"
    primaryText := "I really expected a suite but just got a single room with 2 beds."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("I really expected a suite but only got a single room with 2 beds.", .acceptable)]
    readings := []
    paperFeatures := [("flavor", "exclusive"), ("only", "yes")] }

def ex_4b : Datum :=
  { id := "deothomas2025_4b"
    source := ⟨"beaver-clark-2008", "p. 252"⟩
    reportedIn := some ⟨"deo-thomas-2025", "(4b)"⟩
    language := "stan1293"
    primaryText := "London police expected a turnout of 100000 but just 15000 showed up. What happened?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("London police expected a turnout of 100000 but only 15000 showed up. What happened?", .acceptable)]
    readings := []
    paperFeatures := [("flavor", "exclusive"), ("only", "yes")] }

def ex_5a : Datum :=
  { id := "deothomas2025_5a"
    source := ⟨"deo-thomas-2025", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The food was just amazing!"
    glossedTokens := []
    context := "A: How good was the food?"
    judgment := .acceptable
    contrasts := [("The food was only amazing!", .unacceptable)]
    readings := []
    paperFeatures := [("flavor", "emphatic"), ("only", "no")] }

def ex_5b : Datum :=
  { id := "deothomas2025_5b"
    source := ⟨"deo-thomas-2025", "(5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The Empire State Building is just gigantic!"
    glossedTokens := []
    context := "A: How big is the Empire State Building?"
    judgment := .acceptable
    contrasts := [("The Empire State Building is just huge!", .acceptable), ("The Empire State Building is just enormous!", .acceptable)]
    readings := []
    paperFeatures := [("flavor", "emphatic")] }

def ex_6a : Datum :=
  { id := "deothomas2025_6a"
    source := ⟨"deo-thomas-2025", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The funeral was full of life and passion and emotional—and just every emotion you can imagine."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "emphatic")] }

def ex_6b : Datum :=
  { id := "deothomas2025_6b"
    source := ⟨"deo-thomas-2025", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My husband had a pink bathroom with burgundy trim in his apartment in New York. Pink bathrooms are just the BEST!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "emphatic")] }

def ex_7a : Datum :=
  { id := "deothomas2025_7a"
    source := ⟨"thomas-deo-2020", "corpus example"⟩
    reportedIn := some ⟨"deo-thomas-2025", "(7a)"⟩
    language := "stan1293"
    primaryText := "More and more evidence shows that relatively simple changes in lifestyle can have a big impact on your blood pressure—in many cases, just as big as popping a pill."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "precisifyingEquality")] }

def ex_7b : Datum :=
  { id := "deothomas2025_7b"
    source := ⟨"thomas-deo-2020", "corpus example"⟩
    reportedIn := some ⟨"deo-thomas-2025", "(7b)"⟩
    language := "stan1293"
    primaryText := "The blossoms are smaller and have longer, more trumpet-shaped blooms than the flat, flared faces of hybrid bulbs, but the stalks are apt to be just as tall."
    glossedTokens := []
    context := "Many gardeners are finding the new selections of miniature amaryllis more to their liking. ... don't be misled by the word \"miniature.\""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "precisifyingEquality")] }

def ex_8a : Datum :=
  { id := "deothomas2025_8a"
    source := ⟨"deo-thomas-2025", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They rely on gallonage, and the \"shell full\" gallonage, which is stenciled on the ends of the car, is the amount when the horizontal cylinder of the tank is just full, easily observed from the manway during filling."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "precisifyingEquality")] }

def ex_8b : Datum :=
  { id := "deothomas2025_8b"
    source := ⟨"deo-thomas-2025", "(8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The tea was just right, hot and sweetened with a teaspoon tip of honey."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "precisifyingEquality")] }

def ex_9a : Datum :=
  { id := "deothomas2025_9a"
    source := ⟨"deo-thomas-2025", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fafen, the daughter just older than Siri, had done the family duty and become a monk."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Fafen, the daughter only older than Siri, had done the family duty and become a monk.", .unacceptable)]
    readings := []
    paperFeatures := [("flavor", "precisifyingProximity"), ("only", "no"), ("case", "37a")] }

def ex_9b : Datum :=
  { id := "deothomas2025_9b"
    source := ⟨"deo-thomas-2025", "(9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The camera was a plastic but weighty box just bigger than a card deck."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "precisifyingProximity")] }

def ex_9c : Datum :=
  { id := "deothomas2025_9c"
    source := ⟨"deo-thomas-2025", "(9c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "At 11, Samantha is just over 5 feet tall and has wavy black hair."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "precisifyingProximity")] }

def ex_10a : Datum :=
  { id := "deothomas2025_10a"
    source := ⟨"deo-thomas-2025", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The city was just visible in the distance."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "precisifyingProximity")] }

def ex_10b : Datum :=
  { id := "deothomas2025_10b"
    source := ⟨"deo-thomas-2025", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The path is just wide enough for one person."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "precisifyingProximity")] }

def ex_11a : Datum :=
  { id := "deothomas2025_11a"
    source := ⟨"deo-thomas-2025", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We're at a very interesting juncture just now."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "precisifyingEquality"), ("domain", "temporal")] }

def ex_11b : Datum :=
  { id := "deothomas2025_11b"
    source := ⟨"deo-thomas-2025", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Just then there was a knock at the door."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "precisifyingEquality"), ("domain", "temporal")] }

def ex_11c : Datum :=
  { id := "deothomas2025_11c"
    source := ⟨"deo-thomas-2025", "(11c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My sister just got here."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "precisifyingProximity"), ("domain", "temporal")] }

def ex_12a : Datum :=
  { id := "deothomas2025_12a"
    source := ⟨"deo-thomas-2025", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He could see the woman crouched above the sand just at the waterline."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "precisifyingEquality"), ("domain", "spatial")] }

def ex_12b : Datum :=
  { id := "deothomas2025_12b"
    source := ⟨"deo-thomas-2025", "(12b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Just past the farmhouse front door is a small catering kitchen."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "precisifyingProximity"), ("domain", "spatial")] }

def ex_13a : Datum :=
  { id := "deothomas2025_13a"
    source := ⟨"deo-thomas-2025", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Just one cat will make Patrick happy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "minimalSufficiency"), ("only", "no")] }

def ex_13b : Datum :=
  { id := "deothomas2025_13b"
    source := ⟨"deo-thomas-2025", "(13b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Just a 3.5 GPA is sufficient for Jason to stay in the program."
    glossedTokens := []
    context := "What GPA is sufficient for Jason to stay in the program?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "minimalSufficiency"), ("only", "no")] }

def ex_14 : Datum :=
  { id := "deothomas2025_14"
    source := ⟨"wiegand-2018", "p. 419"⟩
    reportedIn := some ⟨"deo-thomas-2025", "(14)"⟩
    language := "stan1293"
    primaryText := "I was sitting there and the lamp just broke!"
    glossedTokens := []
    context := "A: Why is the lamp broken?"
    judgment := .acceptable
    contrasts := [("I was sitting there and the lamp only broke!", .unacceptable)]
    readings := []
    paperFeatures := [("flavor", "unexplanatory"), ("only", "no"), ("case", "37b")] }

def ex_15a : Datum :=
  { id := "deothomas2025_15a"
    source := ⟨"warstadt-2020", "§2"⟩
    reportedIn := some ⟨"deo-thomas-2025", "(15a)"⟩
    language := "stan1293"
    primaryText := "The lights just turn off and on."
    glossedTokens := []
    context := "The speaker is explaining why they think their house may be haunted. Current question: Why is the house haunted?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "unexplanatory")] }

def ex_15b : Datum :=
  { id := "deothomas2025_15b"
    source := ⟨"warstadt-2020", "§2"⟩
    reportedIn := some ⟨"deo-thomas-2025", "(15b)"⟩
    language := "stan1293"
    primaryText := "The lights just turn off and on. The wire is frayed."
    glossedTokens := []
    context := "The speaker is explaining why they think their house may be haunted. Current question: Why is the house haunted?"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "unexplanatory")] }

def ex_16a : Datum :=
  { id := "deothomas2025_16a"
    source := ⟨"deo-thomas-2025", "(16a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I just had extra mangoes."
    glossedTokens := []
    context := "A: Why did you make mango-mousse cake?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "weakExplanation"), ("only", "no")] }

def ex_16b : Datum :=
  { id := "deothomas2025_16b"
    source := ⟨"deo-thomas-2025", "(16b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She just lied about her age."
    glossedTokens := []
    context := "A: How did Mary get into the bar?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "weakExplanation"), ("only", "no")] }

def ex_17a : Datum :=
  { id := "deothomas2025_17a"
    source := ⟨"warstadt-2020", "p. 376"⟩
    reportedIn := some ⟨"deo-thomas-2025", "(17a)"⟩
    language := "stan1293"
    primaryText := "A proton is just a hydrogen atom without an electron."
    glossedTokens := []
    context := "A: What is a proton?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "unelaboratory"), ("only", "no"), ("case", "37c")] }

def ex_17b : Datum :=
  { id := "deothomas2025_17b"
    source := ⟨"warstadt-2020", "p. 376"⟩
    reportedIn := some ⟨"deo-thomas-2025", "(17b)"⟩
    language := "stan1293"
    primaryText := "I am just mad."
    glossedTokens := []
    context := "A: Why are you mad?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "unelaboratory"), ("only", "no"), ("case", "37c")] }

def ex_17c : Datum :=
  { id := "deothomas2025_17c"
    source := ⟨"warstadt-2020", "p. 376"⟩
    reportedIn := some ⟨"deo-thomas-2025", "(17c)"⟩
    language := "stan1293"
    primaryText := "Fido is just a dog."
    glossedTokens := []
    context := "A: What kind of dog is Fido?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "unelaboratory"), ("only", "no"), ("case", "37c")] }

def ex_18a : Datum :=
  { id := "deothomas2025_18a"
    source := ⟨"wiegand-2018", "p. 423"⟩
    reportedIn := some ⟨"deo-thomas-2025", "(18a)"⟩
    language := "stan1293"
    primaryText := "He started seeing an ex-girlfriend and just stopped texting me."
    glossedTokens := []
    context := "A: What happened to your relationship?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "counterexpectational"), ("only", "no"), ("case", "37a")] }

def ex_18b : Datum :=
  { id := "deothomas2025_18b"
    source := ⟨"wiegand-2018", "p. 424"⟩
    reportedIn := some ⟨"deo-thomas-2025", "(18b)"⟩
    language := "stan1293"
    primaryText := "The priest gave Charlotte her communion wafer and she just ate it!"
    glossedTokens := []
    context := "A: What happened at the church?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "counterexpectational"), ("only", "no"), ("case", "37a")] }

def ex_41 : Datum :=
  { id := "deothomas2025_41"
    source := ⟨"deo-thomas-2025", "(41)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He just got a B."
    glossedTokens := []
    context := "A: How did John do on the exam?"
    judgment := .acceptable
    contrasts := [("He only got a B.", .acceptable), ("He just got an A+.", .marginal), ("He only got an A+.", .marginal), ("He just sailed through.", .acceptable), ("He only sailed through.", .unacceptable)]
    readings := []
    paperFeatures := [("flavor", "rankOrder")] }

def ex_47 : Datum :=
  { id := "deothomas2025_47"
    source := ⟨"deo-thomas-2025", "(47)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alphonso just grabbed whatever tool was handy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Alphonso simply grabbed whatever tool was handy.", .acceptable)]
    readings := []
    paperFeatures := [("flavor", "unelaboratory"), ("case", "37c")] }

def ex_51 : Datum :=
  { id := "deothomas2025_51"
    source := ⟨"deo-thomas-2025", "(51)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yes, Fafen is just older than Siri."
    glossedTokens := []
    context := "A: Is Fafen older than Siri?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "precisifyingProximity")] }

def ex_52 : Datum :=
  { id := "deothomas2025_52"
    source := ⟨"deo-thomas-2025", "(52)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fafen is [just]F older than Siri."
    glossedTokens := []
    context := "A: How much older than Siri is Fafen?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "precisifyingProximity"), ("focus", "just"), ("case", "37a")] }

def ex_53a : Datum :=
  { id := "deothomas2025_53a"
    source := ⟨"deo-thomas-2025", "(53a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It was [just]F cheaper than this one."
    glossedTokens := []
    context := "A and B see a nice purse on sale. A knows that B recently bought a cheap purse on Amazon. A asks: How much cheaper was the purse you got?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "precisifyingProximity"), ("focus", "just")] }

def ex_53b : Datum :=
  { id := "deothomas2025_53b"
    source := ⟨"deo-thomas-2025", "(53b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It was just [cheaper]F than this one."
    glossedTokens := []
    context := "A and B see a nice purse on sale. A knows that B recently bought a cheap purse on Amazon. A asks: How much cheaper was the purse you got?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "unelaboratory"), ("focus", "cheaper")] }

def ex_55 : Datum :=
  { id := "deothomas2025_55"
    source := ⟨"deo-thomas-2025", "(55)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The tank is just full."
    glossedTokens := []
    context := "Q: How full is the tank?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "precisifyingEquality"), ("case", "37a")] }

def ex_56 : Datum :=
  { id := "deothomas2025_56"
    source := ⟨"deo-thomas-2025", "(56)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My sister just got here."
    glossedTokens := []
    context := "A: When did your sister get here?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "precisifyingProximity"), ("domain", "temporal"), ("case", "37a")] }

def ex_58a : Datum :=
  { id := "deothomas2025_58a"
    source := ⟨"deo-thomas-2025", "(58a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Roughly speaking, this soup is amazing."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := [("Roughly speaking, this essay is perfect.", .unacceptable)]
    readings := []
    paperFeatures := [("construction", "roughlySpeaking"), ("adjective", "extreme")] }

def ex_58b : Datum :=
  { id := "deothomas2025_58b"
    source := ⟨"deo-thomas-2025", "(58b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Roughly speaking, this tank is full."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Roughly speaking, this theater is empty.", .acceptable)]
    readings := []
    paperFeatures := [("construction", "roughlySpeaking"), ("adjective", "maximumStandard")] }

def ex_59 : Datum :=
  { id := "deothomas2025_59"
    source := ⟨"deo-thomas-2025", "(59)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This soup is just amazing!"
    glossedTokens := []
    context := "Q: How tasty is that soup?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "emphatic")] }

def ex_60a : Datum :=
  { id := "deothomas2025_60a"
    source := ⟨"deo-thomas-2025", "(60a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The door is just [closed]F!"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := [("The door is completely closed!", .acceptable), ("The door is absolutely closed!", .acceptable)]
    readings := []
    paperFeatures := [("flavor", "emphatic"), ("adjective", "maximumStandard")] }

def ex_60b : Datum :=
  { id := "deothomas2025_60b"
    source := ⟨"deo-thomas-2025", "(60b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The tank is just [full]F!"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := [("The tank is completely full!", .acceptable), ("The tank is absolutely full!", .acceptable)]
    readings := []
    paperFeatures := [("flavor", "emphatic"), ("adjective", "maximumStandard")] }

def ex_61 : Datum :=
  { id := "deothomas2025_61"
    source := ⟨"deo-thomas-2025", "(61)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The funeral was full of just every emotion you can imagine."
    glossedTokens := []
    context := "A: Which emotions was the funeral full of?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "emphatic")] }

def ex_62 : Datum :=
  { id := "deothomas2025_62"
    source := ⟨"deo-thomas-2025", "(62)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Pink bathrooms are just [the BEST]F!"
    glossedTokens := []
    context := "A: How do pink bathrooms compare to other-color bathrooms?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "emphatic")] }

def ex_63a : Datum :=
  { id := "deothomas2025_63a"
    source := ⟨"deo-thomas-2025", "(63a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Mary went to just Spain and Portugal (for vacation this year). B: No/that's not true! She also went to Italy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "complementExclusion"), ("response", "denial")] }

def ex_63b : Datum :=
  { id := "deothomas2025_63b"
    source := ⟨"deo-thomas-2025", "(63b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary didn't go to just Spain and Portugal."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "complementExclusion"), ("response", "negation")] }

def ex_64a : Datum :=
  { id := "deothomas2025_64a"
    source := ⟨"deo-thomas-2025", "(64a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: This soup is just amazing! B: That's not true! It is pretty mediocre."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("flavor", "emphatic"), ("response", "denial")] }

def ex_64b : Datum :=
  { id := "deothomas2025_64b"
    source := ⟨"deo-thomas-2025", "(64b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Just a cat will make Patrick happy. B: No, that's not true! (Even) a goldfish will make him happy."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := [("C: Yes! Even a goldfish will make him happy.", .acceptable)]
    readings := []
    paperFeatures := [("flavor", "minimalSufficiency"), ("response", "denial")] }

def ex_65 : Datum :=
  { id := "deothomas2025_65"
    source := ⟨"deo-thomas-2025", "(65)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: This essay is just perfect! B: Not really... did you notice the flaws in the reasoning?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("B': No, it isn't! I found it too verbose.", .acceptable), ("B'': I don't think so. I hate how pretentious it sounds.", .acceptable)]
    readings := []
    paperFeatures := [("flavor", "emphatic"), ("response", "faultlessDisagreement")] }

def all : List Datum := [ex_1a, ex_1b, ex_2d, ex_3a, ex_3b, ex_4a, ex_4b, ex_5a, ex_5b, ex_6a, ex_6b, ex_7a, ex_7b, ex_8a, ex_8b, ex_9a, ex_9b, ex_9c, ex_10a, ex_10b, ex_11a, ex_11b, ex_11c, ex_12a, ex_12b, ex_13a, ex_13b, ex_14, ex_15a, ex_15b, ex_16a, ex_16b, ex_17a, ex_17b, ex_17c, ex_18a, ex_18b, ex_41, ex_47, ex_51, ex_52, ex_53a, ex_53b, ex_55, ex_56, ex_58a, ex_58b, ex_59, ex_60a, ex_60b, ex_61, ex_62, ex_63a, ex_63b, ex_64a, ex_64b, ex_65]

end DeoThomas2025.Examples
