module

public import Linglib.Data.Examples.Schema

/-!
# `Tham2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Tham2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Tham2025.Examples`.
-/

@[expose] public section

namespace Tham2025.Examples

def ex_4a : Datum :=
  { id := "tham2025_4a"
    source := ⟨"tham-2025", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is a damage in X."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_5a : Datum :=
  { id := "tham2025_5a"
    source := ⟨"tham-2025", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is a shatter in X."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_9 : Datum :=
  { id := "tham2025_9"
    source := ⟨"tham-2025", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The mirror will crack in five minutes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("the cracking takes place after five minutes", .acceptable), ("the cracking lasts five minutes", .unacceptable)]
    paperFeatures := [] }

def ex_10a : Datum :=
  { id := "tham2025_10a"
    source := ⟨"tham-2025", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The ice will crack for two days."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_10c : Datum :=
  { id := "tham2025_10c"
    source := ⟨"tham-2025", "(10c)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "However, rock near the heater borehole sampled in the north heater drift was found to be more cracked than rock near the borehole sampled in the south heater drift."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_11a : Datum :=
  { id := "tham2025_11a"
    source := ⟨"tham-2025", "(11a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "The replacement is more dented than the first!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_11b : Datum :=
  { id := "tham2025_11b"
    source := ⟨"tham-2025", "(11b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Rough grit sandpaper will make the dashboard more scratched than it already is."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_12a : Datum :=
  { id := "tham2025_12a"
    source := ⟨"tham-2025", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The vase will shatter in two minutes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("the shattering takes place after two minutes", .acceptable), ("the shattering lasts two minutes", .unacceptable)]
    paperFeatures := [] }

def ex_12b : Datum :=
  { id := "tham2025_12b"
    source := ⟨"tham-2025", "(12b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The vase will shatter for two minutes."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_12c : Datum :=
  { id := "tham2025_12c"
    source := ⟨"tham-2025", "(12c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This vase is more shattered than that one."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_13b : Datum :=
  { id := "tham2025_13b"
    source := ⟨"tham-2025", "(13b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The soup cooled for ten minutes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_14a : Datum :=
  { id := "tham2025_14a"
    source := ⟨"tham-2025", "(14a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I put an empty cast iron skillet on my stove, turned on the power to preheat, and the pan cracked in a minute."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_14b : Datum :=
  { id := "tham2025_14b"
    source := ⟨"tham-2025", "(14b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "As far as the original cause of the break, who knows; though it like had cracked for a while until the crack propagated to the point where the whole thing failed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_15a : Datum :=
  { id := "tham2025_15a"
    source := ⟨"tham-2025", "(15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My screen cracked completely."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_15b : Datum :=
  { id := "tham2025_15b"
    source := ⟨"tham-2025", "(15b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If the glass cover has only cracked partially and can still absorb light, you can laminate or waterproof it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_16 : Datum :=
  { id := "tham2025_16"
    source := ⟨"tham-2025", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Hiya I recently dropped my iPhone 7, it cracked slightly …"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_17a : Datum :=
  { id := "tham2025_17a"
    source := ⟨"tham-2025", "(17a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My screen cracked completely/slightly ⊨ My screen is cracked."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_17b : Datum :=
  { id := "tham2025_17b"
    source := ⟨"tham-2025", "(17b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The basin filled completely/#slightly ⊨ The basin is filled."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_18c : Datum :=
  { id := "tham2025_18c"
    source := ⟨"tham-2025", "(18c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The ancient Mazda hatchback with three hubcaps and a badly cracked windshield hung in the gutter with its front wheels sideways."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_19a : Datum :=
  { id := "tham2025_19a"
    source := ⟨"tham-2025", "(19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Road maps in a well cracked ceiling the signs aren't hard to find."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("many branching cracks: the quantity dimension", .acceptable)]
    paperFeatures := [] }

def ex_20a : Datum :=
  { id := "tham2025_20a"
    source := ⟨"tham-2025", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have an LG G2 with a completely cracked screen, and the screen is black underneath."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_21a : Datum :=
  { id := "tham2025_21a"
    source := ⟨"tham-2025", "(21a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The concrete characteristic length, determined from the fracture energy represented by the first part of the stress–crack width relationship, controls the failure load of a partially cracked concrete slab."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_22b : Datum :=
  { id := "tham2025_22b"
    source := ⟨"tham-2025", "(22b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The first two times, the car was recovered, badly dented."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("many dents: the quantity dimension", .acceptable), ("one serious dent: the quality dimension", .acceptable)]
    paperFeatures := [] }

def ex_23b : Datum :=
  { id := "tham2025_23b"
    source := ⟨"tham-2025", "(23b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I once had a mass market copy of The Stand that had a well-cracked spine sitting on the back seat of my car."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("a deep crack: the quality dimension", .acceptable)]
    paperFeatures := [] }

def ex_26 : Datum :=
  { id := "tham2025_26"
    source := ⟨"tham-2025", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: My watch face is scratched. B: No, it's smooth."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_27 : Datum :=
  { id := "tham2025_27"
    source := ⟨"tham-2025", "(27)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: My watch face is badly scratched. B: No, it's not badly scratched at all, the scratch is long but not deep."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_28a : Datum :=
  { id := "tham2025_28a"
    source := ⟨"tham-2025", "(28a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Your front bumper is more dented with respect to dent size, but your rear bumper is more dented with respect to the sheer number of dents."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_28c : Datum :=
  { id := "tham2025_28c"
    source := ⟨"tham-2025", "(28c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Your front bumper is badly dented in every respect you can name!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_29 : Datum :=
  { id := "tham2025_29"
    source := ⟨"tham-2025", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This mirror is more badly cracked than that one with respect to the position of the cracks/how badly its functionality is affected/how the cracks are arrayed on the surface."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_30a : Datum :=
  { id := "tham2025_30a"
    source := ⟨"tham-2025", "(30a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is a much cracked dish of the \"Doghouse Club\" which was founded in 1962 by a group of driver's wives and girlfriends – including Betty Brabham – to provide some much needed paddock social activities and facilities."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("many cracks: the quantity dimension", .acceptable), ("one deep crack: the quality dimension", .unacceptable)]
    paperFeatures := [] }

def ex_32 : Datum :=
  { id := "tham2025_32"
    source := ⟨"tham-2025", "(32)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The floor is completely dirty already, but it can always get dirtier, especially after the kids come in from football."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_33 : Datum :=
  { id := "tham2025_33"
    source := ⟨"tham-2025", "(33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The windshield is completely cracked already – one more crack and it will break."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_36b : Datum :=
  { id := "tham2025_36b"
    source := ⟨"tham-2025", "(36b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My Surface Laptop screen completely cracked this morning."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_37a : Datum :=
  { id := "tham2025_37a"
    source := ⟨"tham-2025", "(37a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This drum cracked badly."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_40a : Datum :=
  { id := "tham2025_40a"
    source := ⟨"tham-2025", "(40a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "The bumper was dented severely with respect to dent size (although it was just a couple of dents)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_40b : Datum :=
  { id := "tham2025_40b"
    source := ⟨"tham-2025", "(40b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "The bumper dented severely with respect to dent size (although it was just a couple of dents)."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_41a : Datum :=
  { id := "tham2025_41a"
    source := ⟨"tham-2025", "(41a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "The windshield is badly cracked in every respect!"
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_41b : Datum :=
  { id := "tham2025_41b"
    source := ⟨"tham-2025", "(41b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "The windshield cracked badly in every respect!"
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_42a : Datum :=
  { id := "tham2025_42a"
    source := ⟨"tham-2025", "(42a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "The front bumper is dented more severely with respect to dent size, but the rear bumper is more severely dented with respect to the sheer number of dents."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_42b : Datum :=
  { id := "tham2025_42b"
    source := ⟨"tham-2025", "(42b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "The front bumper dented more severely with respect to dent size, but the rear bumper dented more severely with respect to the sheer number of dents."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_43a : Datum :=
  { id := "tham2025_43a"
    source := ⟨"tham-2025", "(43a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "The hailstones cracked the front windshield badly with respect to the number of cracks (although the cracks weren't too long or deep)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_44a : Datum :=
  { id := "tham2025_44a"
    source := ⟨"tham-2025", "(44a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The various tools differ with respect to their background, composition, psychometric properties, and sponsorship."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_45a : Datum :=
  { id := "tham2025_45a"
    source := ⟨"tham-2025", "(45a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most of the white pumpkins I grew were smooth, but this one had a completely cracked surface - which I thought was so cool."
    glossedTokens := []
    context := "A photograph shows the pumpkin's skin texture."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_45b : Datum :=
  { id := "tham2025_45b"
    source := ⟨"tham-2025", "(45b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My model is too smooth, I would like it to have a dented surface."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_45c : Datum :=
  { id := "tham2025_45c"
    source := ⟨"tham-2025", "(45c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Design Skinz Blue and Orange Scratched Surface with Glowing Gold Skin Decal Vinyl Full-Body Wrap Kit Compatible with Google Pixel 5A."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex_4a, ex_5a, ex_9, ex_10a, ex_10c, ex_11a, ex_11b, ex_12a, ex_12b, ex_12c, ex_13b, ex_14a, ex_14b, ex_15a, ex_15b, ex_16, ex_17a, ex_17b, ex_18c, ex_19a, ex_20a, ex_21a, ex_22b, ex_23b, ex_26, ex_27, ex_28a, ex_28c, ex_29, ex_30a, ex_32, ex_33, ex_36b, ex_37a, ex_40a, ex_40b, ex_41a, ex_41b, ex_42a, ex_42b, ex_43a, ex_44a, ex_45a, ex_45b, ex_45c]

end Tham2025.Examples
