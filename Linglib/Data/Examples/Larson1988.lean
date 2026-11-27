module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Larson1988` — typed example data

Auto-generated from `Linglib/Data/Examples/Larson1988.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Larson1988.Examples`.
-/

@[expose] public section

namespace Larson1988.Examples

def ex_1a : Datum :=
  { id := "larson1988_1a"
    source := ⟨"larson-1988", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John sent Mary a letter."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "doubleObject"), ("verb", "send")] }

def ex_1b : Datum :=
  { id := "larson1988_1b"
    source := ⟨"larson-1988", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I promised Felix a new set of golf clubs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "doubleObject"), ("verb", "promise")] }

def ex_3a_i : Datum :=
  { id := "larson1988_3a_i"
    source := ⟨"larson-1988", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I showed Mary herself."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "doubleObject"), ("phenomenon", "anaphor"), ("licensor", "goal")] }

def ex_3a_ii : Datum :=
  { id := "larson1988_3a_ii"
    source := ⟨"larson-1988", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I showed herself Mary."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("frame", "doubleObject"), ("phenomenon", "anaphor"), ("licensor", "theme")] }

def ex_3b_i : Datum :=
  { id := "larson1988_3b_i"
    source := ⟨"larson-1988", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I gave every worker his paycheck."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "doubleObject"), ("phenomenon", "quantifierBinding"), ("licensor", "goal")] }

def ex_3b_ii : Datum :=
  { id := "larson1988_3b_ii"
    source := ⟨"larson-1988", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I gave its owner every paycheck."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("frame", "doubleObject"), ("phenomenon", "quantifierBinding"), ("licensor", "theme")] }

def ex_3c_i : Datum :=
  { id := "larson1988_3c_i"
    source := ⟨"larson-1988", "(3c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which man did you send his paycheck?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "doubleObject"), ("phenomenon", "weakCrossover"), ("licensor", "goal")] }

def ex_3c_ii : Datum :=
  { id := "larson1988_3c_ii"
    source := ⟨"larson-1988", "(3c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Whose pay did you send his mother?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("frame", "doubleObject"), ("phenomenon", "weakCrossover"), ("licensor", "theme")] }

def ex_3d_i : Datum :=
  { id := "larson1988_3d_i"
    source := ⟨"larson-1988", "(3d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did you give which paycheck?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "doubleObject"), ("phenomenon", "superiority"), ("licensor", "goal")] }

def ex_3d_ii : Datum :=
  { id := "larson1988_3d_ii"
    source := ⟨"larson-1988", "(3d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which paycheck did you give who?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("frame", "doubleObject"), ("phenomenon", "superiority"), ("licensor", "theme")] }

def ex_3e_i : Datum :=
  { id := "larson1988_3e_i"
    source := ⟨"larson-1988", "(3e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I showed each man the other's socks."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "doubleObject"), ("phenomenon", "eachOther"), ("licensor", "goal")] }

def ex_3e_ii : Datum :=
  { id := "larson1988_3e_ii"
    source := ⟨"larson-1988", "(3e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I showed the other's friend each man."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("frame", "doubleObject"), ("phenomenon", "eachOther"), ("licensor", "theme")] }

def ex_3f_i : Datum :=
  { id := "larson1988_3f_i"
    source := ⟨"larson-1988", "(3f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I showed no one anything."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "doubleObject"), ("phenomenon", "negativePolarity"), ("licensor", "goal")] }

def ex_3f_ii : Datum :=
  { id := "larson1988_3f_ii"
    source := ⟨"larson-1988", "(3f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I showed anyone nothing."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("frame", "doubleObject"), ("phenomenon", "negativePolarity"), ("licensor", "theme")] }

def ex_5a_i : Datum :=
  { id := "larson1988_5a_i"
    source := ⟨"larson-1988", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I showed Mary to herself."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "oblique"), ("phenomenon", "anaphor"), ("licensor", "theme")] }

def ex_5a_ii : Datum :=
  { id := "larson1988_5a_ii"
    source := ⟨"larson-1988", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I showed herself to Mary."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("frame", "oblique"), ("phenomenon", "anaphor"), ("licensor", "goal")] }

def ex_5b_i : Datum :=
  { id := "larson1988_5b_i"
    source := ⟨"larson-1988", "(5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I sent every check to its owner."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "oblique"), ("phenomenon", "quantifierBinding"), ("licensor", "theme")] }

def ex_5b_ii : Datum :=
  { id := "larson1988_5b_ii"
    source := ⟨"larson-1988", "(5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I sent his paycheck to every worker."
    glossedTokens := []
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "oblique"), ("phenomenon", "quantifierBinding"), ("licensor", "goal")] }

def ex_5c_i : Datum :=
  { id := "larson1988_5c_i"
    source := ⟨"larson-1988", "(5c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which check did you send to its owner?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "oblique"), ("phenomenon", "weakCrossover"), ("licensor", "theme")] }

def ex_5c_ii : Datum :=
  { id := "larson1988_5c_ii"
    source := ⟨"larson-1988", "(5c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which worker did you send his check to?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("frame", "oblique"), ("phenomenon", "weakCrossover"), ("licensor", "goal")] }

def ex_5d_i : Datum :=
  { id := "larson1988_5d_i"
    source := ⟨"larson-1988", "(5d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which check did you send to who?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "oblique"), ("phenomenon", "superiority"), ("licensor", "theme")] }

def ex_5d_ii : Datum :=
  { id := "larson1988_5d_ii"
    source := ⟨"larson-1988", "(5d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Whom did you send which check to?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("frame", "oblique"), ("phenomenon", "superiority"), ("licensor", "goal")] }

def ex_5e_i : Datum :=
  { id := "larson1988_5e_i"
    source := ⟨"larson-1988", "(5e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I sent each boy to the other's parents."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "oblique"), ("phenomenon", "eachOther"), ("licensor", "theme")] }

def ex_5e_ii : Datum :=
  { id := "larson1988_5e_ii"
    source := ⟨"larson-1988", "(5e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I sent the other's check to each boy."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("frame", "oblique"), ("phenomenon", "eachOther"), ("licensor", "goal")] }

def ex_5f_i : Datum :=
  { id := "larson1988_5f_i"
    source := ⟨"larson-1988", "(5f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I sent no presents to any of the children."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "oblique"), ("phenomenon", "negativePolarity"), ("licensor", "theme")] }

def ex_5f_ii : Datum :=
  { id := "larson1988_5f_ii"
    source := ⟨"larson-1988", "(5f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I sent any of the packages to none of the children."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("frame", "oblique"), ("phenomenon", "negativePolarity"), ("licensor", "goal")] }

def ex_57a_i : Datum :=
  { id := "larson1988_57a_i"
    source := ⟨"larson-1988", "(57a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I donated money to charity."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "oblique"), ("verb", "donate")] }

def ex_57a_ii : Datum :=
  { id := "larson1988_57a_ii"
    source := ⟨"larson-1988", "(57a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I donated charity money."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("frame", "doubleObject"), ("verb", "donate")] }

def ex_57b_i : Datum :=
  { id := "larson1988_57b_i"
    source := ⟨"larson-1988", "(57b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I distributed apples to the children."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "oblique"), ("verb", "distribute")] }

def ex_57b_ii : Datum :=
  { id := "larson1988_57b_ii"
    source := ⟨"larson-1988", "(57b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I distributed the children apples."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("frame", "doubleObject"), ("verb", "distribute")] }

def ex_57c_i : Datum :=
  { id := "larson1988_57c_i"
    source := ⟨"larson-1988", "(57c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I contributed my time to the auction."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "oblique"), ("verb", "contribute")] }

def ex_57c_ii : Datum :=
  { id := "larson1988_57c_ii"
    source := ⟨"larson-1988", "(57c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I contributed the auction my time."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("frame", "doubleObject"), ("verb", "contribute")] }

def ex_58a_i : Datum :=
  { id := "larson1988_58a_i"
    source := ⟨"larson-1988", "(58a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I gave away money to charity."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "oblique"), ("verb", "give away")] }

def ex_58a_ii : Datum :=
  { id := "larson1988_58a_ii"
    source := ⟨"larson-1988", "(58a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I gave away charity money."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("frame", "doubleObject"), ("verb", "give away")] }

def ex_58a_iii : Datum :=
  { id := "larson1988_58a_iii"
    source := ⟨"larson-1988", "(58a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I gave charity away money."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("frame", "doubleObject"), ("verb", "give away")] }

def ex_58b_i : Datum :=
  { id := "larson1988_58b_i"
    source := ⟨"larson-1988", "(58b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I gave out apples to the children."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "oblique"), ("verb", "give out")] }

def ex_58b_ii : Datum :=
  { id := "larson1988_58b_ii"
    source := ⟨"larson-1988", "(58b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I gave out the children apples."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("frame", "doubleObject"), ("verb", "give out")] }

def ex_58b_iii : Datum :=
  { id := "larson1988_58b_iii"
    source := ⟨"larson-1988", "(58b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I gave the children out apples."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("frame", "doubleObject"), ("verb", "give out")] }

def all : List Datum := [ex_1a, ex_1b, ex_3a_i, ex_3a_ii, ex_3b_i, ex_3b_ii, ex_3c_i, ex_3c_ii, ex_3d_i, ex_3d_ii, ex_3e_i, ex_3e_ii, ex_3f_i, ex_3f_ii, ex_5a_i, ex_5a_ii, ex_5b_i, ex_5b_ii, ex_5c_i, ex_5c_ii, ex_5d_i, ex_5d_ii, ex_5e_i, ex_5e_ii, ex_5f_i, ex_5f_ii, ex_57a_i, ex_57a_ii, ex_57b_i, ex_57b_ii, ex_57c_i, ex_57c_ii, ex_58a_i, ex_58a_ii, ex_58a_iii, ex_58b_i, ex_58b_ii, ex_58b_iii]

/-- The two frames of a dative verb. -/
inductive Frame where
  /-- oblique: the oblique dative, V NP to NP -/
  | oblique
  /-- doubleObject: the double object construction, V NP NP -/
  | doubleObject
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `frame`. -/
def frame (e : Datum) : Option Frame :=
  e.parse? "frame" [("oblique", .oblique), ("doubleObject", .doubleObject)]

/-- The dependencies of section 1, each of which requires c-command. -/
inductive Phenomenon where
  /-- anaphor: an anaphor and its antecedent -/
  | anaphor
  /-- quantifierBinding: a pronoun bound by a quantifier -/
  | quantifierBinding
  /-- weakCrossover: a wh-phrase moved over a noun phrase containing a coreferential pronoun -/
  | weakCrossover
  /-- superiority: a wh-phrase moved over another -/
  | superiority
  /-- eachOther: each and the other on the reciprocal reading -/
  | eachOther
  /-- negativePolarity: a negative polarity item and the affective element licensing it -/
  | negativePolarity
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `phenomenon`. -/
def phenomenon (e : Datum) : Option Phenomenon :=
  e.parse? "phenomenon" [("anaphor", .anaphor), ("quantifierBinding", .quantifierBinding),
    ("weakCrossover", .weakCrossover), ("superiority", .superiority), ("eachOther", .eachOther),
    ("negativePolarity", .negativePolarity)]

/-- The object that must c-command the other for the dependency to hold: the antecedent, the quantifier, the wh-phrase that moves, each, or the affective element. -/
inductive Argument where
  /-- theme: the direct object -/
  | theme
  /-- goal: the indirect object -/
  | goal
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `licensor`. -/
def licensor (e : Datum) : Option Argument :=
  e.parse? "licensor" [("theme", .theme), ("goal", .goal)]

/-- The dative verbs whose shifting section 5 discusses. -/
inductive Verb where
  /-- send: send -/
  | send
  /-- promise: promise -/
  | promise
  /-- donate: donate -/
  | donate
  /-- distribute: distribute -/
  | distribute
  /-- contribute: contribute -/
  | contribute
  /-- give away: give away -/
  | giveAway
  /-- give out: give out -/
  | giveOut
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `verb`. -/
def verb (e : Datum) : Option Verb :=
  e.parse? "verb" [("send", .send), ("promise", .promise), ("donate", .donate), ("distribute", .distribute),
    ("contribute", .contribute), ("give away", .giveAway), ("give out", .giveOut)]

end Larson1988.Examples
