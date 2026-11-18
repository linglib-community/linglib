module

public import Linglib.Data.Examples.Schema

/-!
# `Dowty1991` — typed example data

Auto-generated from `Linglib/Data/Examples/Dowty1991.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Dowty1991.Examples`.
-/

@[expose] public section

namespace Dowty1991.Examples

def buildSubject : Datum :=
  { id := "dowty1991_buildSubject"
    source := ⟨"dowty-1991", "(30e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John built a house"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "build"), ("argument", "subject"), ("participant", "the builder"), ("entails", "volition"), ("entails", "sentience"), ("entails", "causation"), ("entails", "movement"), ("entails", "independentExistence")] }

def buildObject : Datum :=
  { id := "dowty1991_buildObject"
    source := ⟨"dowty-1991", "(30e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John built a house"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "build"), ("argument", "object"), ("participant", "the thing built (a house)"), ("entails", "changeOfState"), ("entails", "incrementalTheme"), ("entails", "causallyAffected"), ("entails", "stationary"), ("entails", "dependentExistence")] }

def bePoliteSubject : Datum :=
  { id := "dowty1991_bePoliteSubject"
    source := ⟨"dowty-1991", "(29a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is being polite to Bill"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "be polite to"), ("argument", "subject"), ("participant", "the polite party"), ("entails", "volition")] }

def ignoreSubject : Datum :=
  { id := "dowty1991_ignoreSubject"
    source := ⟨"dowty-1991", "(29a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is ignoring Mary"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "ignore"), ("argument", "subject"), ("participant", "the ignorer"), ("entails", "volition")] }

def notEatSubject : Datum :=
  { id := "dowty1991_notEatSubject"
    source := ⟨"cruse-1973", "(32)"⟩
    reportedIn := some ⟨"dowty-1991", "(29a)"⟩
    language := "stan1293"
    primaryText := "What he did was not eat anything for two days"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "not eat"), ("argument", "subject"), ("participant", "the abstainer"), ("entails", "volition")] }

def knowSubject : Datum :=
  { id := "dowty1991_knowSubject"
    source := ⟨"dowty-1991", "(29b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knows the statement"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "know"), ("argument", "subject"), ("participant", "the knower"), ("entails", "sentience")] }

def believeSubject : Datum :=
  { id := "dowty1991_believeSubject"
    source := ⟨"dowty-1991", "(29b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John believes the statement"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "believe"), ("argument", "subject"), ("participant", "the believer"), ("entails", "sentience")] }

def seeSubject : Datum :=
  { id := "dowty1991_seeSubject"
    source := ⟨"dowty-1991", "(29b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John sees Mary"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "see"), ("argument", "subject"), ("participant", "the perceiver"), ("entails", "sentience")] }

def fearSubject : Datum :=
  { id := "dowty1991_fearSubject"
    source := ⟨"dowty-1991", "(29b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John fears Mary"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "fear"), ("argument", "subject"), ("participant", "the fearer"), ("entails", "sentience")] }

def causeSubject : Datum :=
  { id := "dowty1991_causeSubject"
    source := ⟨"dowty-1991", "(29c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "His loneliness causes his unhappiness"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "cause"), ("argument", "subject"), ("participant", "the causing state (his loneliness)"), ("entails", "causation"), ("denies", "movement")] }

def passSubject : Datum :=
  { id := "dowty1991_passSubject"
    source := ⟨"dowty-1991", "(29d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The rolling tumbleweed passed the rock"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "pass"), ("argument", "subject"), ("participant", "the mover (the rolling tumbleweed)"), ("entails", "movement"), ("denies", "volition"), ("denies", "causation")] }

def overtakeSubject : Datum :=
  { id := "dowty1991_overtakeSubject"
    source := ⟨"dowty-1991", "(29d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The bullet overtook the arrow"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "overtake"), ("argument", "subject"), ("participant", "the faster mover (the bullet)"), ("entails", "movement"), ("denies", "volition"), ("denies", "causation")] }

def fillSubject : Datum :=
  { id := "dowty1991_fillSubject"
    source := ⟨"dowty-1991", "(29d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Water filled the boat"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "fill"), ("argument", "subject"), ("participant", "the filling substance (water)"), ("entails", "movement"), ("denies", "volition"), ("denies", "causation")] }

def fallSubject : Datum :=
  { id := "dowty1991_fallSubject"
    source := ⟨"dowty-1991", "(29d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He accidentally fell"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "fall"), ("argument", "subject"), ("participant", "the faller"), ("entails", "movement"), ("denies", "volition"), ("denies", "causation")] }

def needSubject : Datum :=
  { id := "dowty1991_needSubject"
    source := ⟨"dowty-1991", "(29e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John needs a new car"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "need"), ("argument", "subject"), ("participant", "the needer"), ("entails", "independentExistence"), ("denies", "volition"), ("denies", "sentience"), ("denies", "causation"), ("denies", "movement")] }

def makeObject : Datum :=
  { id := "dowty1991_makeObject"
    source := ⟨"dowty-1991", "(30a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John made a mistake"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "make"), ("argument", "object"), ("participant", "the thing made (a mistake)"), ("entails", "changeOfState"), ("entails", "dependentExistence")] }

def moveObject : Datum :=
  { id := "dowty1991_moveObject"
    source := ⟨"dowty-1991", "(30a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John moved the rock"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "move"), ("argument", "object"), ("participant", "the thing moved (the rock)"), ("entails", "changeOfState")] }

def eraseObject : Datum :=
  { id := "dowty1991_eraseObject"
    source := ⟨"dowty-1991", "(30a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John erased the error"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "erase"), ("argument", "object"), ("participant", "the thing erased (the error)"), ("entails", "changeOfState"), ("entails", "dependentExistence")] }

def crossObject : Datum :=
  { id := "dowty1991_crossObject"
    source := ⟨"dowty-1991", "(30b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John crossed the driveway"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "cross"), ("argument", "object"), ("participant", "the path crossed (the driveway)"), ("entails", "incrementalTheme"), ("entails", "stationary")] }

def fillObject : Datum :=
  { id := "dowty1991_fillObject"
    source := ⟨"dowty-1991", "(30b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John filled the glass with water"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "fill"), ("argument", "object"), ("participant", "the container filled (the glass)"), ("entails", "incrementalTheme"), ("entails", "stationary")] }

def causeObject : Datum :=
  { id := "dowty1991_causeObject"
    source := ⟨"dowty-1991", "(30c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Smoking causes cancer"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "cause"), ("argument", "object"), ("participant", "the caused condition (cancer)"), ("entails", "causallyAffected")] }

def enterObject : Datum :=
  { id := "dowty1991_enterObject"
    source := ⟨"dowty-1991", "(30d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The bullet entered the target"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "enter"), ("argument", "object"), ("participant", "the target entered"), ("entails", "stationary")] }

def overtakeObject : Datum :=
  { id := "dowty1991_overtakeObject"
    source := ⟨"dowty-1991", "(30d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The bullet overtook the arrow"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "overtake"), ("argument", "object"), ("participant", "the slower mover (the arrow)"), ("entails", "stationary")] }

def constituteObject : Datum :=
  { id := "dowty1991_constituteObject"
    source := ⟨"dowty-1991", "(30e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This situation constitutes a major dilemma for us"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "constitute"), ("argument", "object"), ("participant", "the constituted state (a major dilemma)"), ("entails", "dependentExistence")] }

def needObject : Datum :=
  { id := "dowty1991_needObject"
    source := ⟨"dowty-1991", "(30e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John needs a car"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "need"), ("argument", "object"), ("participant", "the thing needed (a car, de dicto)"), ("entails", "dependentExistence")] }

def seekObject : Datum :=
  { id := "dowty1991_seekObject"
    source := ⟨"dowty-1991", "(30e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John seeks a unicorn"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "seek"), ("argument", "object"), ("participant", "the thing sought (a unicorn, de dicto)"), ("entails", "dependentExistence")] }

def lackObject : Datum :=
  { id := "dowty1991_lackObject"
    source := ⟨"dowty-1991", "(30e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John lacks enough money to buy it"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "lack"), ("argument", "object"), ("participant", "the thing lacked (de dicto)"), ("entails", "dependentExistence")] }

def writeSubject : Datum :=
  { id := "dowty1991_writeSubject"
    source := ⟨"dowty-1991", "(35)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "write a letter"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "write"), ("argument", "subject"), ("participant", "the writer"), ("entails", "volition"), ("entails", "sentience"), ("entails", "causation"), ("entails", "movement"), ("denies", "changeOfState"), ("denies", "incrementalTheme"), ("denies", "causallyAffected"), ("denies", "stationary"), ("denies", "dependentExistence")] }

def murderSubject : Datum :=
  { id := "dowty1991_murderSubject"
    source := ⟨"dowty-1991", "(35)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "murder"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "murder"), ("argument", "subject"), ("participant", "the murderer"), ("entails", "volition"), ("entails", "sentience"), ("entails", "causation"), ("entails", "movement"), ("denies", "changeOfState"), ("denies", "incrementalTheme"), ("denies", "causallyAffected"), ("denies", "stationary"), ("denies", "dependentExistence")] }

def eatSubject : Datum :=
  { id := "dowty1991_eatSubject"
    source := ⟨"dowty-1991", "(35)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "eat"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "eat"), ("argument", "subject"), ("participant", "the eater"), ("entails", "volition"), ("entails", "sentience"), ("entails", "causation"), ("entails", "movement"), ("denies", "changeOfState"), ("denies", "incrementalTheme"), ("denies", "causallyAffected"), ("denies", "stationary"), ("denies", "dependentExistence")] }

def washSubject : Datum :=
  { id := "dowty1991_washSubject"
    source := ⟨"dowty-1991", "(35)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "wash a plate"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "wash"), ("argument", "subject"), ("participant", "the washer"), ("entails", "volition"), ("entails", "sentience"), ("entails", "causation"), ("entails", "movement"), ("denies", "changeOfState"), ("denies", "incrementalTheme"), ("denies", "causallyAffected"), ("denies", "stationary"), ("denies", "dependentExistence")] }

def writeObject : Datum :=
  { id := "dowty1991_writeObject"
    source := ⟨"dowty-1991", "(35)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "write a letter"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "write"), ("argument", "object"), ("participant", "the thing written (a letter)"), ("entails", "changeOfState"), ("entails", "causallyAffected")] }

def murderObject : Datum :=
  { id := "dowty1991_murderObject"
    source := ⟨"dowty-1991", "(35)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "murder"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "murder"), ("argument", "object"), ("participant", "the victim"), ("entails", "changeOfState"), ("entails", "causallyAffected")] }

def eatObject : Datum :=
  { id := "dowty1991_eatObject"
    source := ⟨"dowty-1991", "(35)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "eat"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "eat"), ("argument", "object"), ("participant", "the thing eaten"), ("entails", "changeOfState"), ("entails", "causallyAffected")] }

def washObject : Datum :=
  { id := "dowty1991_washObject"
    source := ⟨"dowty-1991", "(35)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "wash a plate"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "wash"), ("argument", "object"), ("participant", "the thing washed (a plate)"), ("entails", "changeOfState"), ("entails", "causallyAffected")] }

def buySubject : Datum :=
  { id := "dowty1991_buySubject"
    source := ⟨"dowty-1991", "(4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary bought the piano from John for $1,000"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "buy"), ("argument", "subject"), ("participant", "the buyer"), ("entails", "volition")] }

def buySeller : Datum :=
  { id := "dowty1991_buySeller"
    source := ⟨"dowty-1991", "(4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary bought the piano from John for $1,000"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "buy"), ("argument", "oblique"), ("participant", "the seller (from-phrase)"), ("entails", "volition")] }

def sellSubject : Datum :=
  { id := "dowty1991_sellSubject"
    source := ⟨"dowty-1991", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John sold the piano to Mary for $1,000"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "sell"), ("argument", "subject"), ("participant", "the seller"), ("entails", "volition")] }

def sellBuyer : Datum :=
  { id := "dowty1991_sellBuyer"
    source := ⟨"dowty-1991", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John sold the piano to Mary for $1,000"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "sell"), ("argument", "oblique"), ("participant", "the buyer (to-phrase)"), ("entails", "volition")] }

def likeSubject : Datum :=
  { id := "dowty1991_likeSubject"
    source := ⟨"dowty-1991", "(38)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "x likes y"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "like"), ("argument", "subject"), ("participant", "the experiencer"), ("entails", "sentience")] }

def likeObject : Datum :=
  { id := "dowty1991_likeObject"
    source := ⟨"dowty-1991", "(38)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "x likes y"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "like"), ("argument", "object"), ("participant", "the stimulus"), ("entails", "causation"), ("denies", "sentience")] }

def pleaseSubject : Datum :=
  { id := "dowty1991_pleaseSubject"
    source := ⟨"dowty-1991", "(38)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "y pleases x"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "please"), ("argument", "subject"), ("participant", "the stimulus"), ("entails", "causation"), ("denies", "sentience")] }

def pleaseObject : Datum :=
  { id := "dowty1991_pleaseObject"
    source := ⟨"dowty-1991", "(38)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "y pleases x"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "please"), ("argument", "object"), ("participant", "the experiencer"), ("entails", "sentience")] }

def surpriseObjectInchoative : Datum :=
  { id := "dowty1991_surpriseObjectInchoative"
    source := ⟨"dowty-1991", "(38)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "y surprises x"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "surprise (inchoative)"), ("argument", "object"), ("participant", "the experiencer (coming to be surprised)"), ("entails", "sentience"), ("entails", "changeOfState")] }

def hitObject : Datum :=
  { id := "dowty1991_hitObject"
    source := ⟨"dowty-1991", "(62a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John hit the fence with the stick"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "hit"), ("argument", "object"), ("participant", "the location (the fence)"), ("denies", "movement"), ("denies", "changeOfState"), ("denies", "incrementalTheme")] }

def hitInstrument : Datum :=
  { id := "dowty1991_hitInstrument"
    source := ⟨"dowty-1991", "(62a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John hit the fence with the stick"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "hit"), ("argument", "oblique"), ("participant", "the instrument (the stick)"), ("entails", "movement"), ("denies", "changeOfState"), ("denies", "incrementalTheme")] }

def breakObject : Datum :=
  { id := "dowty1991_breakObject"
    source := ⟨"dowty-1991", "(63a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John broke the fence with the stick"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "break"), ("argument", "object"), ("participant", "the thing broken"), ("entails", "changeOfState"), ("entails", "incrementalTheme")] }

def loadTheme : Datum :=
  { id := "dowty1991_loadTheme"
    source := ⟨"dowty-1991", "(49a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary loaded the hay onto the truck"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "load"), ("argument", "nonsubject"), ("participant", "the locatum (the hay)"), ("entails", "changeOfState")] }

def loadLocation : Datum :=
  { id := "dowty1991_loadLocation"
    source := ⟨"dowty-1991", "(49a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary loaded the hay onto the truck"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "load"), ("argument", "nonsubject"), ("participant", "the location (the truck)"), ("entails", "changeOfState")] }

def kissSubject : Datum :=
  { id := "dowty1991_kissSubject"
    source := ⟨"dowty-1991", "(43)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kim kissed Sandy"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "kiss"), ("argument", "subject"), ("participant", "the kisser"), ("entails", "volition")] }

def kissObject : Datum :=
  { id := "dowty1991_kissObject"
    source := ⟨"dowty-1991", "(43)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kim kissed Sandy"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "kiss"), ("argument", "object"), ("participant", "the one kissed"), ("denies", "volition")] }

def collideSubject : Datum :=
  { id := "dowty1991_collideSubject"
    source := ⟨"dowty-1991", "(45a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The truck collided with the lamppost"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "collide with"), ("argument", "subject"), ("participant", "the moving body (the truck)"), ("entails", "movement")] }

def collideObject : Datum :=
  { id := "dowty1991_collideObject"
    source := ⟨"dowty-1991", "(45a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The truck collided with the lamppost"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "collide with"), ("argument", "oblique"), ("participant", "the body collided with (the lamppost)"), ("denies", "movement")] }

def surpriseSubject : Datum :=
  { id := "dowty1991_surpriseSubject"
    source := ⟨"dowty-1991", "(38)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "y surprises x"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "surprise"), ("argument", "subject"), ("participant", "the stimulus"), ("entails", "causation"), ("denies", "sentience")] }

def breakInstrument : Datum :=
  { id := "dowty1991_breakInstrument"
    source := ⟨"dowty-1991", "(63a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John broke the fence with the stick"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "break"), ("argument", "oblique"), ("participant", "the instrument (the stick in 63a)"), ("denies", "changeOfState"), ("denies", "incrementalTheme")] }

def putTheme : Datum :=
  { id := "dowty1991_putTheme"
    source := ⟨"dowty-1991", "§8.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John put the lamp on the table"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "put"), ("argument", "object"), ("participant", "the lamp"), ("entails", "changeOfState"), ("entails", "causallyAffected")] }

def putGoal : Datum :=
  { id := "dowty1991_putGoal"
    source := ⟨"dowty-1991", "§8.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John put the lamp on the table"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "put"), ("argument", "oblique"), ("participant", "the table"), ("entails", "stationary")] }

def removeTheme : Datum :=
  { id := "dowty1991_removeTheme"
    source := ⟨"dowty-1991", "§8.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John removed the lamp from the box"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "remove"), ("argument", "object"), ("participant", "the lamp"), ("entails", "changeOfState"), ("entails", "causallyAffected")] }

def removeSource : Datum :=
  { id := "dowty1991_removeSource"
    source := ⟨"dowty-1991", "§8.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John removed the lamp from the box"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "remove"), ("argument", "oblique"), ("participant", "the box"), ("entails", "stationary")] }

def all : List Datum := [buildSubject, buildObject, bePoliteSubject, ignoreSubject, notEatSubject, knowSubject, believeSubject, seeSubject, fearSubject, causeSubject, passSubject, overtakeSubject, fillSubject, fallSubject, needSubject, makeObject, moveObject, eraseObject, crossObject, fillObject, causeObject, enterObject, overtakeObject, constituteObject, needObject, seekObject, lackObject, writeSubject, murderSubject, eatSubject, washSubject, writeObject, murderObject, eatObject, washObject, buySubject, buySeller, sellSubject, sellBuyer, likeSubject, likeObject, pleaseSubject, pleaseObject, surpriseObjectInchoative, hitObject, hitInstrument, breakObject, loadTheme, loadLocation, kissSubject, kissObject, collideSubject, collideObject, surpriseSubject, breakInstrument, putTheme, putGoal, removeTheme, removeSource]

end Dowty1991.Examples
