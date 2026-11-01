module

public import Linglib.Data.Examples.Schema

/-!
# `RappaportHovavLevin2024` — typed example data

Auto-generated from `Linglib/Data/Examples/RappaportHovavLevin2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace RappaportHovavLevin2024.Examples`.
-/

@[expose] public section

namespace RappaportHovavLevin2024.Examples

def rhl2024_11d : Datum :=
  { id := "rhl2024_11d"
    source := ⟨"rappaport-hovav-levin-2024", "(11d)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "As a final touch I swept the terrace."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "routine"), ("mover", "instrument"), ("causer", "animate"), ("surfaceSlot", "object"), ("causerSlot", "subject")] }

def rhl2024_12a : Datum :=
  { id := "rhl2024_12a"
    source := ⟨"rappaport-hovav-levin-2024", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone who has ever swept the floor with a standard broom …"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "routine"), ("mover", "instrument"), ("causer", "animate"), ("moverSlot", "with"), ("surfaceSlot", "object"), ("causerSlot", "subject")] }

def rhl2024_13 : Datum :=
  { id := "rhl2024_13"
    source := ⟨"rappaport-hovav-levin-2024", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The wind swept the floor."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "routine"), ("mover", "instrument"), ("causer", "natural phenomenon"), ("surfaceSlot", "object"), ("causerSlot", "subject")] }

def rhl2024_82 : Datum :=
  { id := "rhl2024_82"
    source := ⟨"rappaport-hovav-levin-2024", "(82)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yesterday, I swept in the morning."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "routine"), ("mover", "instrument"), ("causer", "animate"), ("causerSlot", "subject")] }

def rhl2024_31a : Datum :=
  { id := "rhl2024_31a"
    source := ⟨"rappaport-hovav-levin-2024", "(31)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Danny swept the floor."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "routine"), ("mover", "instrument"), ("causer", "animate"), ("surfaceSlot", "object"), ("causerSlot", "subject")] }

def rhl2024_31b : Datum :=
  { id := "rhl2024_31b"
    source := ⟨"rappaport-hovav-levin-2024", "(31)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The floor swept."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "routine"), ("mover", "instrument"), ("surfaceSlot", "subject")] }

def rhl2024_88 : Datum :=
  { id := "rhl2024_88"
    source := ⟨"rappaport-hovav-levin-2024", "(88)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I swept the floor with a plastic broom."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "routine"), ("mover", "instrument"), ("causer", "animate"), ("moverSlot", "with"), ("surfaceSlot", "object"), ("causerSlot", "subject")] }

def rhl2024_83a : Datum :=
  { id := "rhl2024_83a"
    source := ⟨"rappaport-hovav-levin-2024", "(83a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I funneled all morning."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("verb", "funnel"), ("sense", "instrument"), ("mover", "instrument"), ("causer", "animate"), ("causerSlot", "subject")] }

def rhl2024_83b : Datum :=
  { id := "rhl2024_83b"
    source := ⟨"rappaport-hovav-levin-2024", "(83b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I mopped all morning."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "mop"), ("sense", "routine"), ("mover", "instrument"), ("causer", "animate"), ("causerSlot", "subject")] }

def rhl2024_24a : Datum :=
  { id := "rhl2024_24a"
    source := ⟨"rappaport-hovav-levin-2024", "(24a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Soon a torrent of rain sweeps the patio …"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "natural phenomenon"), ("moverSlot", "subject"), ("surfaceSlot", "object")] }

def rhl2024_25a : Datum :=
  { id := "rhl2024_25a"
    source := ⟨"rappaport-hovav-levin-2024", "(25a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "… frigid waves swept the deck."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "natural phenomenon"), ("moverSlot", "subject"), ("surfaceSlot", "object")] }

def rhl2024_25b : Datum :=
  { id := "rhl2024_25b"
    source := ⟨"rappaport-hovav-levin-2024", "(25b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "The north wind swept the open tundra …"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "natural phenomenon"), ("moverSlot", "subject"), ("surfaceSlot", "object")] }

def rhl2024_25d : Datum :=
  { id := "rhl2024_25d"
    source := ⟨"rappaport-hovav-levin-2024", "(25d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "… when the branch of the tree swept the window …"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "projectile"), ("moverSlot", "subject"), ("surfaceSlot", "object")] }

def rhl2024_25f : Datum :=
  { id := "rhl2024_25f"
    source := ⟨"rappaport-hovav-levin-2024", "(25f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Miriam gently swept the strings of her harp with slim, white fingers."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "body part"), ("causer", "animate"), ("moverSlot", "with"), ("surfaceSlot", "object"), ("causerSlot", "subject")] }

def rhl2024_75b_bare : Datum :=
  { id := "rhl2024_75b_bare"
    source := ⟨"rappaport-hovav-levin-2024", "(75b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Miriam gently swept the strings of her harp."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "body part"), ("causer", "animate"), ("surfaceSlot", "object"), ("causerSlot", "subject")] }

def rhl2024_75a : Datum :=
  { id := "rhl2024_75a"
    source := ⟨"rappaport-hovav-levin-2024", "(75a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The harpist swept the strings of her instrument with a bow …"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "instrument"), ("causer", "animate"), ("moverSlot", "with"), ("surfaceSlot", "object"), ("causerSlot", "subject")] }

def rhl2024_75a_bare : Datum :=
  { id := "rhl2024_75a_bare"
    source := ⟨"rappaport-hovav-levin-2024", "(75a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The harpist swept the strings of her instrument …"
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "instrument"), ("causer", "animate"), ("surfaceSlot", "object"), ("causerSlot", "subject")] }

def rhl2024_74b : Datum :=
  { id := "rhl2024_74b"
    source := ⟨"rappaport-hovav-levin-2024", "(74b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "A hurricane of projectiles swept Chih-Yuen [=a ship] …"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "projectile"), ("moverSlot", "subject"), ("surfaceSlot", "object")] }

def rhl2024_92 : Datum :=
  { id := "rhl2024_92"
    source := ⟨"rappaport-hovav-levin-2024", "(92)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "A breeze moved the willows, the tips of their branches sweeping the ground."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "projectile"), ("moverSlot", "subject"), ("surfaceSlot", "object")] }

def rhl2024_26 : Datum :=
  { id := "rhl2024_26"
    source := ⟨"rappaport-hovav-levin-2024", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The frigid waves swept."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "natural phenomenon"), ("moverSlot", "subject")] }

def rhl2024_27 : Datum :=
  { id := "rhl2024_27"
    source := ⟨"rappaport-hovav-levin-2024", "(27)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Miriam gently swept."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "body part"), ("causer", "animate"), ("causerSlot", "subject")] }

def rhl2024_32a : Datum :=
  { id := "rhl2024_32a"
    source := ⟨"rappaport-hovav-levin-2024", "(32a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The window swept."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "projectile"), ("surfaceSlot", "subject")] }

def rhl2024_32b : Datum :=
  { id := "rhl2024_32b"
    source := ⟨"rappaport-hovav-levin-2024", "(32b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The open tundra swept."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "natural phenomenon"), ("surfaceSlot", "subject")] }

def rhl2024_23 : Datum :=
  { id := "rhl2024_23"
    source := ⟨"rappaport-hovav-levin-2024", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He was sweeping."
    glossedTokens := []
    context := "Utah sweeps it [=the gun] under the bed with his foot."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "displaced"), ("causer", "animate"), ("causerSlot", "subject")] }

def rhl2024_22 : Datum :=
  { id := "rhl2024_22"
    source := ⟨"rappaport-hovav-levin-2024", "(22)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Utah sweeps it [=the gun] under the bed with his foot."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "displaced"), ("causer", "animate"), ("moverSlot", "object"), ("causerSlot", "subject"), ("path", "pp")] }

def rhl2024_24c : Datum :=
  { id := "rhl2024_24c"
    source := ⟨"rappaport-hovav-levin-2024", "(24c)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "She swept it [=her hand] through her hair."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "body part"), ("causer", "animate"), ("moverSlot", "object"), ("surfaceSlot", "path object"), ("causerSlot", "subject"), ("path", "pp")] }

def rhl2024_28a : Datum :=
  { id := "rhl2024_28a"
    source := ⟨"rappaport-hovav-levin-2024", "(28a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She began to sweep her fingers over the strings."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "body part"), ("causer", "animate"), ("moverSlot", "object"), ("surfaceSlot", "path object"), ("causerSlot", "subject"), ("path", "pp")] }

def rhl2024_28b : Datum :=
  { id := "rhl2024_28b"
    source := ⟨"rappaport-hovav-levin-2024", "(28b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She swept the brush through Megan's shiny hair …"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "instrument"), ("causer", "animate"), ("moverSlot", "object"), ("surfaceSlot", "path object"), ("causerSlot", "subject"), ("path", "pp")] }

def rhl2024_28c : Datum :=
  { id := "rhl2024_28c"
    source := ⟨"rappaport-hovav-levin-2024", "(28c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I swept the coins off the counter …"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "displaced"), ("causer", "animate"), ("moverSlot", "object"), ("surfaceSlot", "path object"), ("causerSlot", "subject"), ("path", "pp")] }

def rhl2024_29a : Datum :=
  { id := "rhl2024_29a"
    source := ⟨"rappaport-hovav-levin-2024", "(29a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "… the wind swept the fires quickly through the top growth …"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "natural phenomenon"), ("causer", "natural phenomenon"), ("moverSlot", "object"), ("surfaceSlot", "path object"), ("causerSlot", "subject"), ("path", "pp")] }

def rhl2024_29b : Datum :=
  { id := "rhl2024_29b"
    source := ⟨"rappaport-hovav-levin-2024", "(29b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "… the swift water swept the truck from the road."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "projectile"), ("causer", "natural phenomenon"), ("moverSlot", "object"), ("surfaceSlot", "path object"), ("causerSlot", "subject"), ("path", "pp")] }

def rhl2024_29c : Datum :=
  { id := "rhl2024_29c"
    source := ⟨"rappaport-hovav-levin-2024", "(29c)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Behind her the wind swept the leaves into the room …"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "projectile"), ("causer", "natural phenomenon"), ("moverSlot", "object"), ("causerSlot", "subject"), ("path", "pp")] }

def rhl2024_30a : Datum :=
  { id := "rhl2024_30a"
    source := ⟨"rappaport-hovav-levin-2024", "(30a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Pat swept a brush through her wavy hair."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "instrument"), ("causer", "animate"), ("moverSlot", "object"), ("surfaceSlot", "path object"), ("causerSlot", "subject"), ("path", "pp")] }

def rhl2024_30a_no_dp : Datum :=
  { id := "rhl2024_30a_no_dp"
    source := ⟨"rappaport-hovav-levin-2024", "(30a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Pat swept through her wavy hair."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "instrument"), ("causer", "animate"), ("surfaceSlot", "path object"), ("causerSlot", "subject"), ("path", "pp")] }

def rhl2024_30a_no_pp : Datum :=
  { id := "rhl2024_30a_no_pp"
    source := ⟨"rappaport-hovav-levin-2024", "(30a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Pat swept a brush."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "instrument"), ("causer", "animate"), ("moverSlot", "object"), ("causerSlot", "subject")] }

def rhl2024_30d : Datum :=
  { id := "rhl2024_30d"
    source := ⟨"rappaport-hovav-levin-2024", "(30d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Pat swept the coins into the jar."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "displaced"), ("causer", "animate"), ("moverSlot", "object"), ("causerSlot", "subject"), ("path", "pp")] }

def rhl2024_60b : Datum :=
  { id := "rhl2024_60b"
    source := ⟨"rappaport-hovav-levin-2024", "(60b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The flood swept the debris in through the Genaldon River Valley."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "projectile"), ("causer", "natural phenomenon"), ("moverSlot", "object"), ("surfaceSlot", "path object"), ("causerSlot", "subject"), ("path", "pp")] }

def rhl2024_62a : Datum :=
  { id := "rhl2024_62a"
    source := ⟨"rappaport-hovav-levin-2024", "(62a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "The man swept the roll through the gravy on his plate."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "displaced"), ("causer", "animate"), ("moverSlot", "object"), ("surfaceSlot", "path object"), ("causerSlot", "subject"), ("path", "pp")] }

def rhl2024_68b : Datum :=
  { id := "rhl2024_68b"
    source := ⟨"rappaport-hovav-levin-2024", "(68b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "… it [=the wind] just swept the fire up the side of the mountain."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "natural phenomenon"), ("causer", "natural phenomenon"), ("moverSlot", "object"), ("surfaceSlot", "path object"), ("causerSlot", "subject"), ("path", "pp")] }

def rhl2024_87 : Datum :=
  { id := "rhl2024_87"
    source := ⟨"rappaport-hovav-levin-2024", "(87)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I swept the plastic broom over the floor."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "instrument"), ("causer", "animate"), ("moverSlot", "object"), ("surfaceSlot", "path object"), ("causerSlot", "subject"), ("path", "pp")] }

def rhl2024_33a : Datum :=
  { id := "rhl2024_33a"
    source := ⟨"rappaport-hovav-levin-2024", "(33a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "… fire swept through their home …"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "natural phenomenon"), ("moverSlot", "subject"), ("surfaceSlot", "path object"), ("path", "pp")] }

def rhl2024_33a_bare : Datum :=
  { id := "rhl2024_33a_bare"
    source := ⟨"rappaport-hovav-levin-2024", "(33a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "… fire swept …"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "natural phenomenon"), ("moverSlot", "subject")] }

def rhl2024_33c : Datum :=
  { id := "rhl2024_33c"
    source := ⟨"rappaport-hovav-levin-2024", "(33c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "… a flashy new car swept in through the open gateway …"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "machine"), ("moverSlot", "subject"), ("path", "pp")] }

def rhl2024_34 : Datum :=
  { id := "rhl2024_34"
    source := ⟨"rappaport-hovav-levin-2024", "(34)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Liddie swept into the room."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "animate"), ("moverSlot", "subject"), ("path", "pp")] }

def rhl2024_34_bare : Datum :=
  { id := "rhl2024_34_bare"
    source := ⟨"rappaport-hovav-levin-2024", "(34)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Liddie swept."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "animate"), ("moverSlot", "subject")] }

def rhl2024_62b : Datum :=
  { id := "rhl2024_62b"
    source := ⟨"rappaport-hovav-levin-2024", "(62b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The roll swept through the gravy on his plate."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "displaced"), ("moverSlot", "subject"), ("surfaceSlot", "path object"), ("path", "pp")] }

def rhl2024_63a : Datum :=
  { id := "rhl2024_63a"
    source := ⟨"rappaport-hovav-levin-2024", "(63a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "The flood … swept across the flats to the sea."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "natural phenomenon"), ("moverSlot", "subject"), ("surfaceSlot", "path object"), ("path", "pp")] }

def rhl2024_66c : Datum :=
  { id := "rhl2024_66c"
    source := ⟨"rappaport-hovav-levin-2024", "(66c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The debris swept in through the Genaldon River Valley …"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "projectile"), ("moverSlot", "subject"), ("surfaceSlot", "path object"), ("path", "pp")] }

def rhl2024_66d : Datum :=
  { id := "rhl2024_66d"
    source := ⟨"rappaport-hovav-levin-2024", "(66d)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Ash swept through the streets like snow."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "projectile"), ("moverSlot", "subject"), ("surfaceSlot", "path object"), ("path", "pp")] }

def rhl2024_67a : Datum :=
  { id := "rhl2024_67a"
    source := ⟨"rappaport-hovav-levin-2024", "(67a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The brush swept through her hair."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "instrument"), ("moverSlot", "subject"), ("surfaceSlot", "path object"), ("path", "pp")] }

def rhl2024_67b : Datum :=
  { id := "rhl2024_67b"
    source := ⟨"rappaport-hovav-levin-2024", "(67b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The coins swept across the counter."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "displaced"), ("moverSlot", "subject"), ("surfaceSlot", "path object"), ("path", "pp")] }

def rhl2024_68a : Datum :=
  { id := "rhl2024_68a"
    source := ⟨"rappaport-hovav-levin-2024", "(68a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The fire swept up the side of the mountain."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sweep"), ("sense", "basic"), ("mover", "natural phenomenon"), ("moverSlot", "subject"), ("surfaceSlot", "path object"), ("path", "pp")] }

def rhl2024_36b : Datum :=
  { id := "rhl2024_36b"
    source := ⟨"rappaport-hovav-levin-2024", "(36b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "I got too close to the fence and scraped it with the tractor."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "scrape"), ("sense", "basic"), ("mover", "instrument"), ("causer", "animate"), ("moverSlot", "with"), ("surfaceSlot", "object"), ("causerSlot", "subject")] }

def rhl2024_37a : Datum :=
  { id := "rhl2024_37a"
    source := ⟨"rappaport-hovav-levin-2024", "(37a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "… his front tire rubbed the rear tire of the bike ahead …"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "rub"), ("sense", "basic"), ("mover", "projectile"), ("moverSlot", "subject"), ("surfaceSlot", "object")] }

def rhl2024_37b : Datum :=
  { id := "rhl2024_37b"
    source := ⟨"rappaport-hovav-levin-2024", "(37b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Branches and undergrowth slashed at their jackets, scraping the fabric with slithering sounds."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "scrape"), ("sense", "basic"), ("mover", "projectile"), ("moverSlot", "subject"), ("surfaceSlot", "object")] }

def rhl2024_38a : Datum :=
  { id := "rhl2024_38a"
    source := ⟨"rappaport-hovav-levin-2024", "(38a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Outside a wind bangs the iron roof and rubs branches against each other making a high-pitched see-saw sound …"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "rub"), ("sense", "basic"), ("mover", "projectile"), ("causer", "natural phenomenon"), ("moverSlot", "object"), ("surfaceSlot", "path object"), ("causerSlot", "subject"), ("path", "pp")] }

def rhl2024_38b : Datum :=
  { id := "rhl2024_38b"
    source := ⟨"rappaport-hovav-levin-2024", "(38b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Ashley rubs conditioner into her hair."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "rub"), ("sense", "basic"), ("mover", "displaced"), ("causer", "animate"), ("moverSlot", "object"), ("surfaceSlot", "path object"), ("causerSlot", "subject"), ("path", "pp")] }

def rhl2024_38c : Datum :=
  { id := "rhl2024_38c"
    source := ⟨"rappaport-hovav-levin-2024", "(38c)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "She rubbed a hand across her thick dark hair."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "rub"), ("sense", "basic"), ("mover", "body part"), ("causer", "animate"), ("moverSlot", "object"), ("surfaceSlot", "path object"), ("causerSlot", "subject"), ("path", "pp")] }

def rhl2024_38d : Datum :=
  { id := "rhl2024_38d"
    source := ⟨"rappaport-hovav-levin-2024", "(38d)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Emmanuel rubs the towel against his head …"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "rub"), ("sense", "basic"), ("mover", "instrument"), ("causer", "animate"), ("moverSlot", "object"), ("surfaceSlot", "path object"), ("causerSlot", "subject"), ("path", "pp")] }

def rhl2024_39a : Datum :=
  { id := "rhl2024_39a"
    source := ⟨"rappaport-hovav-levin-2024", "(39a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "… winds that scrape branches along the windows all day are spooky when home alone."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "scrape"), ("sense", "basic"), ("mover", "projectile"), ("causer", "natural phenomenon"), ("moverSlot", "object"), ("surfaceSlot", "path object"), ("causerSlot", "subject"), ("path", "pp")] }

def rhl2024_39b : Datum :=
  { id := "rhl2024_39b"
    source := ⟨"rappaport-hovav-levin-2024", "(39b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "At lunch, no one scraped their food into the new composting bins."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "scrape"), ("sense", "basic"), ("mover", "displaced"), ("causer", "animate"), ("moverSlot", "object"), ("causerSlot", "subject"), ("path", "pp")] }

def rhl2024_39c : Datum :=
  { id := "rhl2024_39c"
    source := ⟨"rappaport-hovav-levin-2024", "(39c)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "I scrape my fingers over the paper as I leave the office …"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "scrape"), ("sense", "basic"), ("mover", "body part"), ("causer", "animate"), ("moverSlot", "object"), ("surfaceSlot", "path object"), ("causerSlot", "subject"), ("path", "pp")] }

def rhl2024_39d : Datum :=
  { id := "rhl2024_39d"
    source := ⟨"rappaport-hovav-levin-2024", "(39d)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "He scraped the spoon across the bottom of the now-empty bowl …"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "scrape"), ("sense", "basic"), ("mover", "instrument"), ("causer", "animate"), ("moverSlot", "object"), ("surfaceSlot", "path object"), ("causerSlot", "subject"), ("path", "pp")] }

def rhl2024_40c : Datum :=
  { id := "rhl2024_40c"
    source := ⟨"rappaport-hovav-levin-2024", "(40c)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "… I listened to the water slowly scraping across the rocks."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "scrape"), ("sense", "basic"), ("mover", "natural phenomenon"), ("moverSlot", "subject"), ("surfaceSlot", "path object"), ("path", "pp")] }

def rhl2024_41b : Datum :=
  { id := "rhl2024_41b"
    source := ⟨"rappaport-hovav-levin-2024", "(41b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Outside a branch mewled, rubbing against the eave …"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "rub"), ("sense", "basic"), ("mover", "projectile"), ("moverSlot", "subject"), ("surfaceSlot", "path object"), ("path", "pp")] }

def all : List Datum := [rhl2024_11d, rhl2024_12a, rhl2024_13, rhl2024_82, rhl2024_31a, rhl2024_31b, rhl2024_88, rhl2024_83a, rhl2024_83b, rhl2024_24a, rhl2024_25a, rhl2024_25b, rhl2024_25d, rhl2024_25f, rhl2024_75b_bare, rhl2024_75a, rhl2024_75a_bare, rhl2024_74b, rhl2024_92, rhl2024_26, rhl2024_27, rhl2024_32a, rhl2024_32b, rhl2024_23, rhl2024_22, rhl2024_24c, rhl2024_28a, rhl2024_28b, rhl2024_28c, rhl2024_29a, rhl2024_29b, rhl2024_29c, rhl2024_30a, rhl2024_30a_no_dp, rhl2024_30a_no_pp, rhl2024_30d, rhl2024_60b, rhl2024_62a, rhl2024_68b, rhl2024_87, rhl2024_33a, rhl2024_33a_bare, rhl2024_33c, rhl2024_34, rhl2024_34_bare, rhl2024_62b, rhl2024_63a, rhl2024_66c, rhl2024_66d, rhl2024_67a, rhl2024_67b, rhl2024_68a, rhl2024_36b, rhl2024_37a, rhl2024_37b, rhl2024_38a, rhl2024_38b, rhl2024_38c, rhl2024_38d, rhl2024_39a, rhl2024_39b, rhl2024_39c, rhl2024_39d, rhl2024_40c, rhl2024_41b]

end RappaportHovavLevin2024.Examples
