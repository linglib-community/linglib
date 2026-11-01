module

public import Linglib.Data.Examples.Schema

/-!
# `ChungMascarenhas2023` — typed example data

Auto-generated from `Linglib/Data/Examples/ChungMascarenhas2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ChungMascarenhas2023.Examples`.
-/

@[expose] public section

namespace ChungMascarenhas2023.Examples

def cm2024_1_korean_conditional_eval : Datum :=
  { id := "cm2024_1_korean_conditional_eval"
    source := ⟨"chung-mascarenhas-2023", "(1) / (42)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "John-un cip-ey iss-∅-eya toy-n-ta."
    glossedTokens := [("John-un", "John-TOP"), ("cip-ey", "home-DAT"), ("iss-∅-eya", "COP-PRES-only.if"), ("toy-n-ta", "EVAL-PRES-DECL")]
    context := "Korean conditional evaluative construction: -(e)ya 'only-if' + toy- 'EVAL/suffice'."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "koreanComposition"), ("construction", "conditional-evaluative")] }

def cm2024_4_linda_original : Datum :=
  { id := "cm2024_4_linda_original"
    source := ⟨"tversky-kahneman-1983", "Linda task"⟩
    reportedIn := some ⟨"chung-mascarenhas-2023", "(4) / (28)"⟩
    method := some .experiment
    language := "stan1293"
    primaryText := "Linda is 31 years old, single, outspoken, and very bright. She majored in philosophy. As a student, she was deeply concerned with issues of discrimination and social justice, and also participated in anti-nuclear demonstrations. Which is more probable?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Linda is a bank teller.", .acceptable), ("Linda is a bank teller and she is active in the feminist movement.", .acceptable)]
    readings := []
    paperFeatures := [("puzzle", "conjunctionFallacy"), ("empiricalDomain", "epistemic")] }

def cm2024_15a_minersBlockNeither : Datum :=
  { id := "cm2024_15a_minersBlockNeither"
    source := ⟨"kolodny-macfarlane-2010", "Miners puzzle"⟩
    reportedIn := some ⟨"chung-mascarenhas-2023", "(15a)"⟩
    language := "stan1293"
    primaryText := "We ought to block neither shaft."
    glossedTokens := []
    context := "Ten miners trapped in shaft A or shaft B (unknown which). Blocking A: 10 saved if in A, 0 if in B. Blocking B: 0/10. Blocking neither: 9 saved either way."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "miners"), ("modalForce", "ought")] }

def cm2024_15b_minersBlockA : Datum :=
  { id := "cm2024_15b_minersBlockA"
    source := ⟨"kolodny-macfarlane-2010", "Miners puzzle"⟩
    reportedIn := some ⟨"chung-mascarenhas-2023", "(15b)"⟩
    language := "stan1293"
    primaryText := "If the miners are in shaft A, we ought to block shaft A."
    glossedTokens := []
    context := "Same miners scenario as (15a). Conditional on miners-in-A info."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "miners"), ("modalForce", "ought"), ("conditional", "info-sensitive")] }

def cm2024_25a_minersMust : Datum :=
  { id := "cm2024_25a_minersMust"
    source := ⟨"chung-mascarenhas-2023", "(25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We must / have to block neither path."
    glossedTokens := []
    context := "Same miners scenario as (15a)."
    judgment := .acceptable
    alternatives := [("We mustn't block either path.", .acceptable), ("We must / have to refrain from blocking either path.", .acceptable), ("We cannot block either path.", .acceptable)]
    readings := []
    paperFeatures := [("puzzle", "miners"), ("modalForce", "must")] }

def cm2024_25b_minersMustA : Datum :=
  { id := "cm2024_25b_minersMustA"
    source := ⟨"chung-mascarenhas-2023", "(25b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If the miners are in shaft A, we must / have to block shaft A."
    glossedTokens := []
    context := "Same miners scenario as (15a)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "miners"), ("modalForce", "must"), ("prediction", "thresholdShift")] }

def cm2024_29b_modal_linda : Datum :=
  { id := "cm2024_29b_modal_linda"
    source := ⟨"chung-mascarenhas-2023", "(29b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Linda must be a bank teller and be active in the feminist movement."
    glossedTokens := []
    context := "Following the Linda description (cm2024_4_linda_original)."
    judgment := .acceptable
    alternatives := [("Linda must be a bank teller.", .acceptable)]
    readings := []
    paperFeatures := [("puzzle", "modalConjunctionFallacy"), ("empiricalDomain", "epistemic")] }

def cm2024_35_jack_description : Datum :=
  { id := "cm2024_35_jack_description"
    source := ⟨"kahneman-tversky-1973", "Jack description"⟩
    reportedIn := some ⟨"chung-mascarenhas-2023", "(35)"⟩
    language := "stan1293"
    primaryText := "Jack is a 45-year-old man. He is married and has four children. He is generally conservative, careful, and ambitious. He shows no interest in political and social issues and spends most of his free time on his many hobbies which include home carpentry, sailing, and mathematical puzzles."
    glossedTokens := []
    context := "Panel of psychologists interviewed 30 engineers and 70 lawyers (or 70/30 in reversed condition); descriptions written about each. Jack's description shown to subjects."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "baseRateNeglect"), ("empiricalDomain", "epistemic")] }

def cm2024_36_jack_must_engineer : Datum :=
  { id := "cm2024_36_jack_must_engineer"
    source := ⟨"chung-mascarenhas-2023", "(36)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jack must be an engineer."
    glossedTokens := []
    context := "Following the Jack description (cm2024_35_jack_description)."
    judgment := .acceptable
    alternatives := [("Jack must be a lawyer.", .acceptable)]
    readings := []
    paperFeatures := [("puzzle", "baseRateNeglect"), ("modalForce", "must")] }

def cm2024_49a_cold : Datum :=
  { id := "cm2024_49a_cold"
    source := ⟨"chung-mascarenhas-2023", "(49a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John did not come to work today. He must have caught a cold."
    glossedTokens := []
    context := "John absent; speaker reasoning about why."
    judgment := .acceptable
    alternatives := [("He must be dead.", .unacceptable)]
    readings := []
    paperFeatures := [("puzzle", "plausibilityFloor"), ("modalForce", "must")] }

def cm2024_54a_grammatical_mistake : Datum :=
  { id := "cm2024_54a_grammatical_mistake"
    source := ⟨"chung-mascarenhas-2023", "(54a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "One must under no circumstance ever make a grammatical mistake."
    glossedTokens := []
    context := "Deontic; speaker prescribing impossible standard."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "plausibilityFloor"), ("modalForce", "must"), ("modalType", "deontic")] }

def cm2024_55a_bushwick_helicopter : Datum :=
  { id := "cm2024_55a_bushwick_helicopter"
    source := ⟨"chung-mascarenhas-2023", "(55a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In order to get to Bushwick, you have to take a helicopter."
    glossedTokens := []
    context := "Teleological; multiple alternative means available."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "plausibilityFloor"), ("modalForce", "have-to"), ("modalType", "teleological")] }

def cm2024_60a_kim_marry_pat : Datum :=
  { id := "cm2024_60a_kim_marry_pat"
    source := ⟨"dretske-1972", "(adapted; PAT focus)"⟩
    reportedIn := some ⟨"chung-mascarenhas-2023", "(60a)"⟩
    language := "stan1293"
    primaryText := "Kim must marry Pat in order to inherit."
    glossedTokens := []
    context := "Kim will only inherit the considerable fortune their parents left them if they get married. They can marry anyone they like, the condition is simply that Kim be married in order to inherit. Suppose Kim is planning on marrying Pat."
    judgment := .acceptable
    alternatives := [("Kim must marry PAT in order to inherit.", .acceptable)]
    readings := []
    paperFeatures := [("puzzle", "focusContrast"), ("modalForce", "must")] }

def cm2024_63_billy_rain : Datum :=
  { id := "cm2024_63_billy_rain"
    source := ⟨"von-fintel-gillies-2010", "(6b)"⟩
    reportedIn := some ⟨"chung-mascarenhas-2023", "(63)"⟩
    language := "stan1293"
    primaryText := "Billy is looking out the window at the pouring rain. It must be raining."
    glossedTokens := []
    context := "Billy has direct perceptual evidence (looking at rain)."
    judgment := .unacceptable
    alternatives := [("It's raining.", .acceptable)]
    readings := []
    paperFeatures := [("puzzle", "vfgFelicity"), ("modalForce", "must"), ("modalType", "epistemic")] }

def all : List Datum := [cm2024_1_korean_conditional_eval, cm2024_4_linda_original, cm2024_15a_minersBlockNeither, cm2024_15b_minersBlockA, cm2024_25a_minersMust, cm2024_25b_minersMustA, cm2024_29b_modal_linda, cm2024_35_jack_description, cm2024_36_jack_must_engineer, cm2024_49a_cold, cm2024_54a_grammatical_mistake, cm2024_55a_bushwick_helicopter, cm2024_60a_kim_marry_pat, cm2024_63_billy_rain]

end ChungMascarenhas2023.Examples
