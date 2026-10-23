module

public import Linglib.Data.Examples.Schema

/-!
# `AsherPelletier2013` — typed example data

Auto-generated from `Linglib/Data/Examples/AsherPelletier2013.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AsherPelletier2013.Examples`.
-/

@[expose] public section

namespace AsherPelletier2013.Examples

def ex_1 : Datum :=
  { id := "asherpelletier2013_1"
    source := ⟨"asher-pelletier-2013", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dogs bark."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "characterizing")] }

def ex_4a : Datum :=
  { id := "asherpelletier2013_4a"
    source := ⟨"asher-pelletier-2013", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ducks lay eggs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "characterizing"), ("problem", "restricted subkind")] }

def ex_4b : Datum :=
  { id := "asherpelletier2013_4b"
    source := ⟨"asher-pelletier-2013", "(4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Cardinals are bright red."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "characterizing"), ("problem", "restricted subkind")] }

def ex_5 : Datum :=
  { id := "asherpelletier2013_5"
    source := ⟨"asher-pelletier-2013", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mosquitoes carry the West Nile Virus."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "characterizing"), ("problem", "weak existential")] }

def ex_6a : Datum :=
  { id := "asherpelletier2013_6a"
    source := ⟨"asher-pelletier-2013", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ravens are normally black."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "characterizing")] }

def ex_6b : Datum :=
  { id := "asherpelletier2013_6b"
    source := ⟨"asher-pelletier-2013", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This machine crushes oranges."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "characterizing"), ("problem", "no actual instances")] }

def ex_7 : Datum :=
  { id := "asherpelletier2013_7"
    source := ⟨"asher-pelletier-2013", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Penguins don't fly."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "characterizing")] }

def ex_8 : Datum :=
  { id := "asherpelletier2013_8"
    source := ⟨"asher-pelletier-2013", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Birds fly."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "characterizing")] }

def ex_9 : Datum :=
  { id := "asherpelletier2013_9"
    source := ⟨"asher-pelletier-2013", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Turtles live to be 100."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("teleological", .acceptable), ("statistical", .acceptable)]
    paperFeatures := [("type", "characterizing")] }

def ex_10 : Datum :=
  { id := "asherpelletier2013_10"
    source := ⟨"asher-pelletier-2013", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Girls do better in school than boys."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "generic comparison")] }

def ex_13b : Datum :=
  { id := "asherpelletier2013_13b"
    source := ⟨"asher-pelletier-2013", "(13b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kim handles the mail from Antarctica."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "characterizing"), ("problem", "no actual instances")] }

def ex_14a : Datum :=
  { id := "asherpelletier2013_14a"
    source := ⟨"asher-pelletier-2013", "(14a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "People who go to bed late don't get up early."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "embedded generic"), ("embedding", "antecedent")] }

def ex_14b : Datum :=
  { id := "asherpelletier2013_14b"
    source := ⟨"asher-pelletier-2013", "(14b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dogs chase cats that chase mice."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "embedded generic"), ("embedding", "consequent")] }

def ex_15a : Datum :=
  { id := "asherpelletier2013_15a"
    source := ⟨"asher-pelletier-2013", "(15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dinosaurs are extinct."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "kind predication")] }

def ex_15b : Datum :=
  { id := "asherpelletier2013_15b"
    source := ⟨"asher-pelletier-2013", "(15b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ducks are widespread throughout Europe."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "kind predication")] }

def ex_16 : Datum :=
  { id := "asherpelletier2013_16"
    source := ⟨"asher-pelletier-2013", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ducks lay eggs and are widespread throughout Europe."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "copredication"), ("aspects", "individual, kind")] }

def ex_17a : Datum :=
  { id := "asherpelletier2013_17a"
    source := ⟨"asher-pelletier-2013", "(17a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Typhoons arise in this part of the Pacific."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("characterizing", .acceptable), ("existential", .acceptable)]
    paperFeatures := [("type", "characterizing")] }

def ex_17b : Datum :=
  { id := "asherpelletier2013_17b"
    source := ⟨"asher-pelletier-2013", "(17b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There are firemen available."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("existential", .acceptable)]
    paperFeatures := [("type", "existential"), ("restrictor", "tautologous")] }

def ex_20a : Datum :=
  { id := "asherpelletier2013_20a"
    source := ⟨"asher-pelletier-2013", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John drinks beer."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "characterizing"), ("focus", "beer")] }

def ex_20c : Datum :=
  { id := "asherpelletier2013_20c"
    source := ⟨"asher-pelletier-2013", "(20c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John drinks beer."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "characterizing"), ("focus", "drinks")] }

def ex_20e : Datum :=
  { id := "asherpelletier2013_20e"
    source := ⟨"asher-pelletier-2013", "(20e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John drinks beer."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "characterizing"), ("focus", "drinks beer")] }

def ex_23 : Datum :=
  { id := "asherpelletier2013_23"
    source := ⟨"asher-pelletier-2013", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Philosophers rarely smoke nowadays."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "adverb of quantification")] }

def ex_24 : Datum :=
  { id := "asherpelletier2013_24"
    source := ⟨"asher-pelletier-2013", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lots of animals make good pets. For instance, dogs make good pets."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "adverb of quantification")] }

def ex_25a : Datum :=
  { id := "asherpelletier2013_25a"
    source := ⟨"asher-pelletier-2013", "(25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Let's talk about Australian snakes. Australian snakes are poisonous."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "characterizing"), ("focus", "poisonous")] }

def ex_25b : Datum :=
  { id := "asherpelletier2013_25b"
    source := ⟨"asher-pelletier-2013", "(25b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Let's talk about poisonous snakes. Australian snakes are poisonous but South American snakes are not."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "characterizing"), ("focus", "Australian, South American")] }

def ex_28 : Datum :=
  { id := "asherpelletier2013_28"
    source := ⟨"asher-pelletier-2013", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Australian snakes are poisonous, Asian snakes are too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "characterizing"), ("focus", "Australian, Asian"), ("discourse", "parallelism")] }

def ex_30a : Datum :=
  { id := "asherpelletier2013_30a"
    source := ⟨"asher-pelletier-2013", "(30a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Frenchmen eat horsemeat."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "characterizing"), ("focus", "Frenchmen")] }

def ex_31 : Datum :=
  { id := "asherpelletier2013_31"
    source := ⟨"asher-pelletier-2013", "(31)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Let's talk about Frenchmen. Frenchmen eat horsemeat, though Belgians do too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "characterizing"), ("focus", "French, horsemeat")] }

def ex_33a : Datum :=
  { id := "asherpelletier2013_33a"
    source := ⟨"asher-pelletier-2013", "(33a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Female ducks lay eggs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "characterizing"), ("accommodated", "restrictor")] }

def ex_33b : Datum :=
  { id := "asherpelletier2013_33b"
    source := ⟨"asher-pelletier-2013", "(33b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Male cardinals are bright red."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "characterizing"), ("accommodated", "restrictor")] }

def ex_34 : Datum :=
  { id := "asherpelletier2013_34"
    source := ⟨"asher-pelletier-2013", "(34)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ducks lay eggs and are female."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("type", "characterizing")] }

def ex_36 : Datum :=
  { id := "asherpelletier2013_36"
    source := ⟨"asher-pelletier-2013", "(36)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "These farm animals have different means of reproduction. Cows bear live young, Ducks lay eggs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "characterizing"), ("discourse", "Elaboration")] }

def ex_38 : Datum :=
  { id := "asherpelletier2013_38"
    source := ⟨"asher-pelletier-2013", "(38)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Cardinals are bright red. B: Well, male cardinals are bright red; female cardinals are mostly dullish brown."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "characterizing"), ("discourse", "Correction")] }

def ex_39b : Datum :=
  { id := "asherpelletier2013_39b"
    source := ⟨"asher-pelletier-2013", "(39b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mosquitoes are widespread and carry WNV."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "copredication"), ("aspects", "kind, individual")] }

def ex_40a : Datum :=
  { id := "asherpelletier2013_40a"
    source := ⟨"asher-pelletier-2013", "(40a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Cardinals are bright red and lay smallish, speckled eggs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "copredication"), ("aspects", "disjoint subkinds")] }

def ex_40b : Datum :=
  { id := "asherpelletier2013_40b"
    source := ⟨"asher-pelletier-2013", "(40b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lions have large manes and rear their young in groups."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "copredication"), ("aspects", "disjoint subkinds")] }

def ex_40c : Datum :=
  { id := "asherpelletier2013_40c"
    source := ⟨"asher-pelletier-2013", "(40c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jade is green and black."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "copredication"), ("aspects", "disjoint subkinds")] }

def ex_40d : Datum :=
  { id := "asherpelletier2013_40d"
    source := ⟨"asher-pelletier-2013", "(40d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jade is green but also sometimes black."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "copredication"), ("aspects", "disjoint subkinds")] }

def ex_40e : Datum :=
  { id := "asherpelletier2013_40e"
    source := ⟨"asher-pelletier-2013", "(40e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jade is green. Jade is also black."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "copredication"), ("aspects", "disjoint subkinds")] }

def ex_41 : Datum :=
  { id := "asherpelletier2013_41"
    source := ⟨"asher-pelletier-2013", "(41)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You be careful about mosquitoes and deer ticks. Mosquitoes carry the WNV and deer ticks do too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "characterizing"), ("problem", "weak existential")] }

def ex_42a : Datum :=
  { id := "asherpelletier2013_42a"
    source := ⟨"asher-pelletier-2013", "(42a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Asteroids collide with Earth."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("type", "characterizing"), ("relativeAccount", "true")] }

def ex_42b : Datum :=
  { id := "asherpelletier2013_42b"
    source := ⟨"asher-pelletier-2013", "(42b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "US governors are bodybuilders."
    glossedTokens := []
    context := "There are only 50 governors and Schwarzenegger is a body builder; this is a much larger percentage of bodybuilders than the percentage of bodybuilders planet-wide."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("type", "characterizing"), ("relativeAccount", "true")] }

def ex_42c : Datum :=
  { id := "asherpelletier2013_42c"
    source := ⟨"asher-pelletier-2013", "(42c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Philosophers are athletes."
    glossedTokens := []
    context := "Supposing that there are 1000 philosophers and 1 or 2 manage to leave their armchairs to go do sport, whereas the vast majority of the 6 billion inhabitants of the planet are just couch potatoes or too poor to be able to afford to do sports."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("type", "characterizing"), ("relativeAccount", "true")] }

def ex_43a : Datum :=
  { id := "asherpelletier2013_43a"
    source := ⟨"asher-pelletier-2013", "(43a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Nicholas smokes after dinner."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "characterizing"), ("genericity", "events")] }

def ex_43c : Datum :=
  { id := "asherpelletier2013_43c"
    source := ⟨"asher-pelletier-2013", "(43c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sharks attack an injured bather."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "characterizing"), ("genericity", "individuals, events")] }

def ex_45 : Datum :=
  { id := "asherpelletier2013_45"
    source := ⟨"asher-pelletier-2013", "(45)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Australian snakes can be poisonous."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "characterizing"), ("genericity", "individuals, circumstances")] }

def ex_46a : Datum :=
  { id := "asherpelletier2013_46a"
    source := ⟨"asher-pelletier-2013", "(46a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Even mammals lay eggs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("existential over kinds", .acceptable)]
    paperFeatures := [("type", "focus-sensitive adverb")] }

def ex_46b : Datum :=
  { id := "asherpelletier2013_46b"
    source := ⟨"asher-pelletier-2013", "(46b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Even dogs eat garbage."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("type", "focus-sensitive adverb")] }

def ex_46c : Datum :=
  { id := "asherpelletier2013_46c"
    source := ⟨"asher-pelletier-2013", "(46c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "For instance body builders become important politicians."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := [("For instance body builders can become important politicians.", .acceptable), ("For instance body builders have become important politicians.", .acceptable)]
    readings := []
    paperFeatures := [("type", "focus-sensitive adverb")] }

def all : List Datum := [ex_1, ex_4a, ex_4b, ex_5, ex_6a, ex_6b, ex_7, ex_8, ex_9, ex_10, ex_13b, ex_14a, ex_14b, ex_15a, ex_15b, ex_16, ex_17a, ex_17b, ex_20a, ex_20c, ex_20e, ex_23, ex_24, ex_25a, ex_25b, ex_28, ex_30a, ex_31, ex_33a, ex_33b, ex_34, ex_36, ex_38, ex_39b, ex_40a, ex_40b, ex_40c, ex_40d, ex_40e, ex_41, ex_42a, ex_42b, ex_42c, ex_43a, ex_43c, ex_45, ex_46a, ex_46b, ex_46c]

end AsherPelletier2013.Examples
