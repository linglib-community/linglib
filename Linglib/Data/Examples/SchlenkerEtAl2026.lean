module

public import Linglib.Data.Examples.Schema

/-!
# `SchlenkerEtAl2026` — typed example data

Auto-generated from `Linglib/Data/Examples/SchlenkerEtAl2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace SchlenkerEtAl2026.Examples`.
-/

@[expose] public section

namespace SchlenkerEtAl2026.Examples

def ex7a : Datum :=
  { id := "schlenkeretal2026_ex7a"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(7a)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "<RS> clumsy DRIVE POSS-1 POLE POLE-passing_right-cl"
    glossedTokens := []
    context := "POSS-1 HOUSE HAVE POLE-a. SOMETIME CAR HIT-a. YESTERDAY ANN-b SELF-b DRUNK. IX-b"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "70"), ("classifier", "POLE-cl"), ("direction", "passing_right"), ("roleShift", "broad"), ("verb", "DRIVE")] }

def ex7b : Datum :=
  { id := "schlenkeretal2026_ex7b"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(7b)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "<RS> clumsy DRIVE POSS-1 POLE POLE-passing_left-cl"
    glossedTokens := []
    context := "POSS-1 HOUSE HAVE POLE-a. SOMETIME CAR HIT-a. YESTERDAY ANN-b SELF-b DRUNK. IX-b"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "70"), ("classifier", "POLE-cl"), ("direction", "passing_left"), ("roleShift", "broad"), ("verb", "DRIVE")] }

def ex10a : Datum :=
  { id := "schlenkeretal2026_ex10a"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(10a)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "WALL-passing_right-cl"
    glossedTokens := []
    context := "YESTERDAY IX-1 SEE POSS-1 HOUSE-a. ANN SELF-b DRUNK. IX-b DRIVE b-VEHICLE-cl-mid POSS-1 HOUSE-a mid-VEHICLE-cl-a-afront"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "70"), ("classifier", "WALL-cl"), ("direction", "passing_right"), ("roleShift", "broad"), ("verb", "DRIVE")] }

def ex10b : Datum :=
  { id := "schlenkeretal2026_ex10b"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(10b)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "RECTANGLE-passing_right-cl"
    glossedTokens := []
    context := "YESTERDAY IX-1 SEE POSS-1 HOUSE-a. ANN SELF-b DRUNK. IX-b DRIVE b-VEHICLE-cl-mid POSS-1 HOUSE-a mid-VEHICLE-cl-a-afront"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "67"), ("classifier", "RECTANGLE-cl"), ("direction", "passing_right"), ("roleShift", "broad"), ("verb", "DRIVE")] }

def ex10c : Datum :=
  { id := "schlenkeretal2026_ex10c"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(10c)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "CORNER-passing_right-cl"
    glossedTokens := []
    context := "YESTERDAY IX-1 SEE POSS-1 HOUSE-a. ANN SELF-b DRUNK. IX-b DRIVE b-VEHICLE-cl-mid POSS-1 HOUSE-a mid-VEHICLE-cl-a-afront"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "70"), ("classifier", "CORNER-cl"), ("direction", "passing_right"), ("roleShift", "broad"), ("verb", "DRIVE")] }

def ex10d : Datum :=
  { id := "schlenkeretal2026_ex10d"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(10d)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "WALL-passing_left-cl"
    glossedTokens := []
    context := "YESTERDAY IX-1 SEE POSS-1 HOUSE-a. ANN SELF-b DRUNK. IX-b DRIVE b-VEHICLE-cl-mid POSS-1 HOUSE-a mid-VEHICLE-cl-a-afront"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "60"), ("classifier", "WALL-cl"), ("direction", "passing_left"), ("roleShift", "broad"), ("verb", "DRIVE")] }

def ex10e : Datum :=
  { id := "schlenkeretal2026_ex10e"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(10e)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "RECTANGLE-passing_left-cl"
    glossedTokens := []
    context := "YESTERDAY IX-1 SEE POSS-1 HOUSE-a. ANN SELF-b DRUNK. IX-b DRIVE b-VEHICLE-cl-mid POSS-1 HOUSE-a mid-VEHICLE-cl-a-afront"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "63"), ("classifier", "RECTANGLE-cl"), ("direction", "passing_left"), ("roleShift", "broad"), ("verb", "DRIVE")] }

def ex10f : Datum :=
  { id := "schlenkeretal2026_ex10f"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(10f)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "CORNER-passing_left-cl"
    glossedTokens := []
    context := "YESTERDAY IX-1 SEE POSS-1 HOUSE-a. ANN SELF-b DRUNK. IX-b DRIVE b-VEHICLE-cl-mid POSS-1 HOUSE-a mid-VEHICLE-cl-a-afront"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "63"), ("classifier", "CORNER-cl"), ("direction", "passing_left"), ("roleShift", "broad"), ("verb", "DRIVE")] }

def ex13a : Datum :=
  { id := "schlenkeretal2026_ex13a"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(13a)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "JOG TREE-passing_left-cl"
    glossedTokens := []
    context := "YESTERDAY IX-1 SEE TREE TREE-cl-b. ANN PERSON-cl-a, IX-a"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "70"), ("classifier", "TREE-cl"), ("direction", "passing_left"), ("roleShift", "broad"), ("verb", "JOG"), ("pathDisplayed", "none")] }

def ex13b : Datum :=
  { id := "schlenkeretal2026_ex13b"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(13b)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "a-RUN-front TREE-passing_left-cl"
    glossedTokens := []
    context := "YESTERDAY IX-1 SEE TREE TREE-cl-b. ANN PERSON-cl-a, IX-a"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "63"), ("classifier", "TREE-cl"), ("direction", "passing_left"), ("roleShift", "broad"), ("verb", "RUN-agreeing"), ("pathDisplayed", "forward")] }

def ex13c : Datum :=
  { id := "schlenkeretal2026_ex13c"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(13c)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "a-PERSON-front-cl TREE-passing_left-cl"
    glossedTokens := []
    context := "YESTERDAY IX-1 SEE TREE TREE-cl-b. ANN PERSON-cl-a, IX-a"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "50"), ("classifier", "TREE-cl"), ("direction", "passing_left"), ("roleShift", "broad"), ("verb", "PERSON-cl-agreeing"), ("pathDisplayed", "forward")] }

def ex13d : Datum :=
  { id := "schlenkeretal2026_ex13d"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(13d)"⟩
    reportedIn := none
    method := some .elicitation
    language := "amer1248"
    primaryText := "JOG TREE-passing_right-cl"
    glossedTokens := []
    context := "YESTERDAY IX-1 SEE TREE TREE-cl-b. ANN PERSON-cl-a, IX-a"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "63"), ("classifier", "TREE-cl"), ("direction", "passing_right"), ("roleShift", "broad"), ("verb", "JOG"), ("pathDisplayed", "none")] }

def ex13e : Datum :=
  { id := "schlenkeretal2026_ex13e"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(13e)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "a-RUN-front TREE-passing_right-cl"
    glossedTokens := []
    context := "YESTERDAY IX-1 SEE TREE TREE-cl-b. ANN PERSON-cl-a, IX-a"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "53"), ("classifier", "TREE-cl"), ("direction", "passing_right"), ("roleShift", "broad"), ("verb", "RUN-agreeing"), ("pathDisplayed", "forward")] }

def ex13f : Datum :=
  { id := "schlenkeretal2026_ex13f"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(13f)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "a-PERSON-front-cl TREE-passing_right-cl"
    glossedTokens := []
    context := "YESTERDAY IX-1 SEE TREE TREE-cl-b. ANN PERSON-cl-a, IX-a"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "50"), ("classifier", "TREE-cl"), ("direction", "passing_right"), ("roleShift", "broad"), ("verb", "PERSON-cl-agreeing"), ("pathDisplayed", "forward")] }

def ex16a : Datum :=
  { id := "schlenkeretal2026_ex16a"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(16a)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "JOG TREE TREE-cl-1[moves and hits the signer's forehead]"
    glossedTokens := []
    context := "YESTERDAY IX-1 SEE TREE TREE-cl-a SELF PLANT TREE GROW. ANN PERSON-cl-b SELF-b DRUNK. IX-b"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "63"), ("classifier", "TREE-cl-1"), ("direction", "toward"), ("roleShift", "broad"), ("verb", "JOG")] }

def ex16b : Datum :=
  { id := "schlenkeretal2026_ex16b"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(16b)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "b-RUN-a TREE TREE-cl-1[moves and hits the signer's forehead]"
    glossedTokens := []
    context := "YESTERDAY IX-1 SEE TREE TREE-cl-a SELF PLANT TREE GROW. ANN PERSON-cl-b SELF-b DRUNK. IX-b"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "57"), ("classifier", "TREE-cl-1"), ("direction", "toward"), ("roleShift", "broad"), ("verb", "RUN-agreeing")] }

def ex16c : Datum :=
  { id := "schlenkeretal2026_ex16c"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(16c)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "1-RUN-front[signer moves forward] TREE TREE-cl-1[moves and hits the signer's forehead]"
    glossedTokens := []
    context := "YESTERDAY IX-1 SEE TREE TREE-cl-a SELF PLANT TREE GROW. ANN PERSON-cl-b SELF-b DRUNK. IX-b"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "63"), ("classifier", "TREE-cl-1"), ("direction", "toward"), ("roleShift", "broad"), ("verb", "RUN-neutral"), ("signerMoves", "yes")] }

def ex16d : Datum :=
  { id := "schlenkeretal2026_ex16d"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(16d)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "1-RUN-front[signer doesn't move forward] TREE TREE-cl-1[moves and hits the signer's forehead]"
    glossedTokens := []
    context := "YESTERDAY IX-1 SEE TREE TREE-cl-a SELF PLANT TREE GROW. ANN PERSON-cl-b SELF-b DRUNK. IX-b"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "53"), ("classifier", "TREE-cl-1"), ("direction", "toward"), ("roleShift", "broad"), ("verb", "RUN-neutral"), ("signerMoves", "no")] }

def ex16e : Datum :=
  { id := "schlenkeretal2026_ex16e"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(16e)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "b-PERSON-cl-a TREE TREE-cl-1[moves and hits the signer's forehead]"
    glossedTokens := []
    context := "YESTERDAY IX-1 SEE TREE TREE-cl-a SELF PLANT TREE GROW. ANN PERSON-cl-b SELF-b DRUNK. IX-b"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "57"), ("classifier", "TREE-cl-1"), ("direction", "toward"), ("roleShift", "broad"), ("verb", "PERSON-cl-agreeing")] }

def ex16f : Datum :=
  { id := "schlenkeretal2026_ex16f"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(16f)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "1-PERSON-cl-front[signer moves forward] TREE TREE-cl-1[moves and hits the signer's forehead]"
    glossedTokens := []
    context := "YESTERDAY IX-1 SEE TREE TREE-cl-a SELF PLANT TREE GROW. ANN PERSON-cl-b SELF-b DRUNK. IX-b"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "60"), ("classifier", "TREE-cl-1"), ("direction", "toward"), ("roleShift", "broad"), ("verb", "PERSON-cl-neutral"), ("signerMoves", "yes")] }

def ex16g : Datum :=
  { id := "schlenkeretal2026_ex16g"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(16g)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "1-PERSON-cl-front[signer doesn't move forward] TREE TREE-cl-1[moves and hits the signer's forehead]"
    glossedTokens := []
    context := "YESTERDAY IX-1 SEE TREE TREE-cl-a SELF PLANT TREE GROW. ANN PERSON-cl-b SELF-b DRUNK. IX-b"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "53"), ("classifier", "TREE-cl-1"), ("direction", "toward"), ("roleShift", "broad"), ("verb", "PERSON-cl-neutral"), ("signerMoves", "no")] }

def ex19a : Datum :=
  { id := "schlenkeretal2026_ex19a"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(19a)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "RS-b clumsy DRIVE POLE POLE-passing_right-cl"
    glossedTokens := []
    context := "POSS-1 HOUSE HAVE POLE-a. SOMETIME CAR HIT-a. YESTERDAY ANN-b SELF-b DRUNK. IX-b"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "70"), ("classifier", "POLE-cl"), ("direction", "passing_right"), ("roleShift", "strict"), ("verb", "DRIVE")] }

def ex19b : Datum :=
  { id := "schlenkeretal2026_ex19b"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(19b)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "RS-b clumsy DRIVE POLE POLE-passing_left-cl"
    glossedTokens := []
    context := "POSS-1 HOUSE HAVE POLE-a. SOMETIME CAR HIT-a. YESTERDAY ANN-b SELF-b DRUNK. IX-b"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "70"), ("classifier", "POLE-cl"), ("direction", "passing_left"), ("roleShift", "strict"), ("verb", "DRIVE")] }

def ex21a : Datum :=
  { id := "schlenkeretal2026_ex21a"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(21a)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "RS-a hurry JOG TREE TREE-cl-1[moves and hits the signer's forehead]"
    glossedTokens := []
    context := "YESTERDAY IX-1 SEE TREE TREE-cl-a, SELF PLANT TREE GROW. ANN PERSON-cl-b SELF-b DRUNK. IX-b"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "70"), ("classifier", "TREE-cl-1"), ("direction", "toward"), ("roleShift", "strict"), ("verb", "JOG")] }

def ex21b : Datum :=
  { id := "schlenkeretal2026_ex21b"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(21b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "amer1248"
    primaryText := "RS-a hurry b-RUN-a TREE TREE-cl-1[moves and hits the signer's forehead]"
    glossedTokens := []
    context := "YESTERDAY IX-1 SEE TREE TREE-cl-a, SELF PLANT TREE GROW. ANN PERSON-cl-b SELF-b DRUNK. IX-b"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "57"), ("classifier", "TREE-cl-1"), ("direction", "toward"), ("roleShift", "strict"), ("verb", "RUN-agreeing")] }

def ex21c : Datum :=
  { id := "schlenkeretal2026_ex21c"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(21c)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "RS-a hurry 1-RUN-front[signer moves forward] TREE TREE-cl-1[moves and hits the signer's forehead]"
    glossedTokens := []
    context := "YESTERDAY IX-1 SEE TREE TREE-cl-a, SELF PLANT TREE GROW. ANN PERSON-cl-b SELF-b DRUNK. IX-b"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "70"), ("classifier", "TREE-cl-1"), ("direction", "toward"), ("roleShift", "strict"), ("verb", "RUN-neutral"), ("signerMoves", "yes")] }

def ex21d : Datum :=
  { id := "schlenkeretal2026_ex21d"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(21d)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "RS-a hurry 1-RUN-front[signer doesn't move forward] TREE TREE-cl-1[moves and hits the signer's forehead]"
    glossedTokens := []
    context := "YESTERDAY IX-1 SEE TREE TREE-cl-a, SELF PLANT TREE GROW. ANN PERSON-cl-b SELF-b DRUNK. IX-b"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "67"), ("classifier", "TREE-cl-1"), ("direction", "toward"), ("roleShift", "strict"), ("verb", "RUN-neutral"), ("signerMoves", "no")] }

def ex21e : Datum :=
  { id := "schlenkeretal2026_ex21e"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(21e)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "RS-a hurry b-PERSON-cl-a TREE TREE-cl-1[moves and hits the signer's forehead]"
    glossedTokens := []
    context := "YESTERDAY IX-1 SEE TREE TREE-cl-a, SELF PLANT TREE GROW. ANN PERSON-cl-b SELF-b DRUNK. IX-b"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "53"), ("classifier", "TREE-cl-1"), ("direction", "toward"), ("roleShift", "strict"), ("verb", "PERSON-cl-agreeing")] }

def ex21f : Datum :=
  { id := "schlenkeretal2026_ex21f"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(21f)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "RS-a hurry 1-PERSON-cl-front[signer moves forward] TREE TREE-cl-1[moves and hits the signer's forehead]"
    glossedTokens := []
    context := "YESTERDAY IX-1 SEE TREE TREE-cl-a, SELF PLANT TREE GROW. ANN PERSON-cl-b SELF-b DRUNK. IX-b"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "67"), ("classifier", "TREE-cl-1"), ("direction", "toward"), ("roleShift", "strict"), ("verb", "PERSON-cl-neutral"), ("signerMoves", "yes")] }

def ex21g : Datum :=
  { id := "schlenkeretal2026_ex21g"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(21g)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "RS-a hurry 1-PERSON-cl-front[signer doesn't move forward] TREE TREE-cl-1[moves and hits the signer's forehead]"
    glossedTokens := []
    context := "YESTERDAY IX-1 SEE TREE TREE-cl-a, SELF PLANT TREE GROW. ANN PERSON-cl-b SELF-b DRUNK. IX-b"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "60"), ("classifier", "TREE-cl-1"), ("direction", "toward"), ("roleShift", "strict"), ("verb", "PERSON-cl-neutral"), ("signerMoves", "no")] }

def ex23a : Datum :=
  { id := "schlenkeretal2026_ex23a"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(23a)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "RS-b effort PERSON-cl[run] ^ TREE-cl[passing]-rep"
    glossedTokens := []
    context := "YESTERDAY ANN IX-b WOW ESCAPE POLICE. FOREST AREA-a IX-b"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "70"), ("classifier", "TREE-cl"), ("direction", "passing_rep"), ("roleShift", "strict"), ("figure", "PERSON-cl")] }

def ex23b : Datum :=
  { id := "schlenkeretal2026_ex23b"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(23b)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "effort PERSON-cl[run] ^ TREE-cl[passing]-rep"
    glossedTokens := []
    context := "YESTERDAY ANN IX-b WOW ESCAPE POLICE. FOREST AREA-a IX-b"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "67"), ("classifier", "TREE-cl"), ("direction", "passing_rep"), ("roleShift", "broad"), ("figure", "PERSON-cl")] }

def ex24a : Datum :=
  { id := "schlenkeretal2026_ex24a"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(24a)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "RS-b effort VEHICLE-cl ^ POLE-cl[passing]-rep"
    glossedTokens := []
    context := "YESTERDAY ANN(-b) CAR RACE. IX-b MUST DRIVE PAST TELEPHONE POLE POLE-cl POLE-cl. IX-b"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "70"), ("classifier", "POLE-cl"), ("direction", "passing_rep"), ("roleShift", "strict"), ("figure", "VEHICLE-cl")] }

def ex24b : Datum :=
  { id := "schlenkeretal2026_ex24b"
    source := ⟨"schlenker-lamberton-lamberton-2026", "(24b)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "effort VEHICLE-cl ^ POLE-cl[passing]-rep"
    glossedTokens := []
    context := "YESTERDAY ANN(-b) CAR RACE. IX-b MUST DRIVE PAST TELEPHONE POLE POLE-cl POLE-cl. IX-b"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("score", "67"), ("classifier", "POLE-cl"), ("direction", "passing_rep"), ("roleShift", "broad"), ("figure", "VEHICLE-cl")] }

def all : List Datum := [ex7a, ex7b, ex10a, ex10b, ex10c, ex10d, ex10e, ex10f, ex13a, ex13b, ex13c, ex13d, ex13e, ex13f, ex16a, ex16b, ex16c, ex16d, ex16e, ex16f, ex16g, ex19a, ex19b, ex21a, ex21b, ex21c, ex21d, ex21e, ex21f, ex21g, ex23a, ex23b, ex24a, ex24b]

end SchlenkerEtAl2026.Examples
