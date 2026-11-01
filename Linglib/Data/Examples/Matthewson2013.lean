module

public import Linglib.Data.Examples.Schema

/-!
# `Matthewson2013` — typed example data

Auto-generated from `Linglib/Data/Examples/Matthewson2013.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Matthewson2013.Examples`.
-/

@[expose] public section

namespace Matthewson2013.Examples

def ex22 : Datum :=
  { id := "matthewson2013_ex22"
    source := ⟨"matthewson-2013", "(22)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa/ima'=hl wis"
    glossedTokens := [("yugw=imaa/ima'=hl", "IMPF=EPIS=CN"), ("wis", "rain")]
    context := "You hear pattering, and you're not entirely sure what it is."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "present"), ("prospective", "false"), ("figure", "4")] }

def ex29 : Datum :=
  { id := "matthewson2013_ex29"
    source := ⟨"matthewson-2013", "(29)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa=hl siipxw-t"
    glossedTokens := [("yugw=imaa=hl", "IMPF=EPIS=CN"), ("siipxw-t", "sick-3SG.II")]
    context := "Joe left the meeting looking really green in the face and sweaty. Someone asks you why he left."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "past"), ("prospective", "false"), ("figure", "4"), ("force", "necessity"), ("flavor", "epistemic")] }

def ex30 : Datum :=
  { id := "matthewson2013_ex30"
    source := ⟨"matthewson-2013", "(30)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa=hl da'awhl ixwt oo ligi nee=yimaa=dii ixwt"
    glossedTokens := [("yugw=imaa=hl", "IMPF=EPIS=CN"), ("da'awhl", "then"), ("ixwt", "fish"), ("oo", "or"), ("ligi", "INDEF"), ("nee=yimaa=dii", "NEG=EPIS=CNTR"), ("ixwt", "fish")]
    context := "You thought your friend was fishing. But you see his rod and tackle box are still at his house. You really don't know if he's fishing or not."
    judgment := .acceptable
    alternatives := []
    readings := [("possibly not", .acceptable)]
    paperFeatures := [("section", "3.1"), ("modal", "ima('a)"), ("negated", "true")] }

def ex37 : Datum :=
  { id := "matthewson2013_ex37"
    source := ⟨"matthewson-2013", "(37)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa=hl x̱sdaa-diit"
    glossedTokens := [("yugw=imaa=hl", "IMPF=EPIS=CN"), ("x̱sdaa-diit", "win-3PL.II")]
    context := "The Canucks were playing last night. You weren't watching the game but you heard your son sounding excited and happy from the living room where he was watching the game, so you thought they were winning. You found out after the game that the Canucks lost 20–0, and your son was happy about something else that his friend had told him on his cellphone."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "past"), ("orientation", "present"), ("prospective", "false"), ("figure", "4")] }

def ex38a : Datum :=
  { id := "matthewson2013_ex38a"
    source := ⟨"matthewson-2013", "(38a)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa=hl x̱sdaa-diit"
    glossedTokens := [("yugw=imaa=hl", "IMPF=EPIS=CN"), ("x̱sdaa-diit", "win-3PL.II")]
    context := "You can hear people hollering, so the Canucks might be winning."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "present"), ("prospective", "false")] }

def ex38b : Datum :=
  { id := "matthewson2013_ex38b"
    source := ⟨"matthewson-2013", "(38b)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa[=hl] dim x̱sdaa-diit"
    glossedTokens := [("yugw=imaa[=hl]", "IMPF=EPIS[=CN]"), ("dim", "FUT"), ("x̱sdaa-diit", "win-3PL.II")]
    context := "You are watching the Canucks. They might win."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "future"), ("prospective", "true")] }

def ex39a : Datum :=
  { id := "matthewson2013_ex39a"
    source := ⟨"matthewson-2013", "(39a)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa/ima'=hl wis"
    glossedTokens := [("yugw=imaa/ima'=hl", "IMPF=EPIS=CN"), ("wis", "rain")]
    context := "You see puddles, and the flowers looking fresh and damp."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "past"), ("prospective", "false")] }

def ex40a : Datum :=
  { id := "matthewson2013_ex40a"
    source := ⟨"matthewson-2013", "(40a)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa/ima'=hl dim wis"
    glossedTokens := [("yugw=imaa/ima'=hl", "IMPF=EPIS=CN"), ("dim", "FUT"), ("wis", "rain")]
    context := "You see puddles, and the flowers looking fresh and damp."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "past"), ("prospective", "true")] }

def ex41a : Datum :=
  { id := "matthewson2013_ex41a"
    source := ⟨"matthewson-2013", "(41a)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa/ima'=hl siipxw-t"
    glossedTokens := [("yugw=imaa/ima'=hl", "IMPF=EPIS=CN"), ("siipxw-t", "sick-3SG.II")]
    context := "Why wasn't Joe at the meeting yesterday?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "past"), ("prospective", "false")] }

def ex42a : Datum :=
  { id := "matthewson2013_ex42a"
    source := ⟨"matthewson-2013", "(42a)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa/ima'=hl dim siipxw-t"
    glossedTokens := [("yugw=imaa/ima'=hl", "IMPF=EPIS=CN"), ("dim", "FUT"), ("siipxw-t", "sick-3SG.II")]
    context := "Why wasn't Joe at the meeting yesterday?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "past"), ("prospective", "true")] }

def ex39b : Datum :=
  { id := "matthewson2013_ex39b"
    source := ⟨"matthewson-2013", "(39b)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa/ima'=hl wis"
    glossedTokens := [("yugw=imaa/ima'=hl", "IMPF=EPIS=CN"), ("wis", "rain")]
    context := "You hear pattering on the roof."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "present"), ("prospective", "false")] }

def ex40b : Datum :=
  { id := "matthewson2013_ex40b"
    source := ⟨"matthewson-2013", "(40b)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa/ima'=hl dim wis"
    glossedTokens := [("yugw=imaa/ima'=hl", "IMPF=EPIS=CN"), ("dim", "FUT"), ("wis", "rain")]
    context := "You hear pattering on the roof."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "present"), ("prospective", "true")] }

def ex41b : Datum :=
  { id := "matthewson2013_ex41b"
    source := ⟨"matthewson-2013", "(41b)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa/ima'=hl siipxw-t"
    glossedTokens := [("yugw=imaa/ima'=hl", "IMPF=EPIS=CN"), ("siipxw-t", "sick-3SG.II")]
    context := "Why isn't Joe here?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "present"), ("prospective", "false")] }

def ex42b : Datum :=
  { id := "matthewson2013_ex42b"
    source := ⟨"matthewson-2013", "(42b)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa/ima'=hl dim siipxw-t"
    glossedTokens := [("yugw=imaa/ima'=hl", "IMPF=EPIS=CN"), ("dim", "FUT"), ("siipxw-t", "sick-3SG.II")]
    context := "Why isn't Joe here?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "present"), ("prospective", "true")] }

def ex39c : Datum :=
  { id := "matthewson2013_ex39c"
    source := ⟨"matthewson-2013", "(39c)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa/ima'=hl wis"
    glossedTokens := [("yugw=imaa/ima'=hl", "IMPF=EPIS=CN"), ("wis", "rain")]
    context := "You hear thunder, so you think it might rain soon."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "future"), ("prospective", "false")] }

def ex40c : Datum :=
  { id := "matthewson2013_ex40c"
    source := ⟨"matthewson-2013", "(40c)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa/ima'=hl dim wis"
    glossedTokens := [("yugw=imaa/ima'=hl", "IMPF=EPIS=CN"), ("dim", "FUT"), ("wis", "rain")]
    context := "You hear thunder, so you think it might rain soon."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "future"), ("prospective", "true")] }

def ex41c : Datum :=
  { id := "matthewson2013_ex41c"
    source := ⟨"matthewson-2013", "(41c)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa/ima'=hl siipxw-t"
    glossedTokens := [("yugw=imaa/ima'=hl", "IMPF=EPIS=CN"), ("siipxw-t", "sick-3SG.II")]
    context := "He's wearing no coat in the rain, he might get sick."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "future"), ("prospective", "false")] }

def ex42c : Datum :=
  { id := "matthewson2013_ex42c"
    source := ⟨"matthewson-2013", "(42c)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa/ima'=hl dim siipxw-t"
    glossedTokens := [("yugw=imaa/ima'=hl", "IMPF=EPIS=CN"), ("dim", "FUT"), ("siipxw-t", "sick-3SG.II")]
    context := "He's wearing no coat in the rain, he might get sick."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "future"), ("prospective", "true")] }

def ex43a : Datum :=
  { id := "matthewson2013_ex43a"
    source := ⟨"matthewson-2013", "(43a)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa=hl wis da'awhl"
    glossedTokens := [("yugw=imaa=hl", "IMPF=EPIS=CN"), ("wis", "rain"), ("da'awhl", "then")]
    context := "When you looked out your window earlier today, the ground was wet, so it looked like it might have rained. But you found out later that the sprinklers had been watering the ground."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "past"), ("orientation", "past"), ("prospective", "false"), ("figure", "4")] }

def ex43a_prime : Datum :=
  { id := "matthewson2013_ex43a_prime"
    source := ⟨"matthewson-2013", "(43a')"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa=hl dim wis da'awhl"
    glossedTokens := [("yugw=imaa=hl", "IMPF=EPIS=CN"), ("dim", "FUT"), ("wis", "rain"), ("da'awhl", "then")]
    context := "When you looked out your window earlier today, the ground was wet, so it looked like it might have rained. But you found out later that the sprinklers had been watering the ground."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "past"), ("orientation", "past"), ("prospective", "true")] }

def ex44 : Datum :=
  { id := "matthewson2013_ex44"
    source := ⟨"matthewson-2013", "(44)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa=hl dim wis"
    glossedTokens := [("yugw=imaa=hl", "IMPF=EPIS=CN"), ("dim", "FUT"), ("wis", "rain")]
    context := "This morning you looked out your window and judging by the clouds, it looked like it might have been going to rain, so you took your raincoat. Later you're explaining to me why you did that."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "past"), ("orientation", "future"), ("prospective", "true"), ("figure", "4")] }

def ex44_prime : Datum :=
  { id := "matthewson2013_ex44_prime"
    source := ⟨"matthewson-2013", "(44')"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa=hl wis"
    glossedTokens := [("yugw=imaa=hl", "IMPF=EPIS=CN"), ("wis", "rain")]
    context := "This morning you looked out your window and judging by the clouds, it looked like it might have been going to rain, so you took your raincoat. Later you're explaining to me why you did that."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "past"), ("orientation", "future"), ("prospective", "false")] }

def ex47a : Datum :=
  { id := "matthewson2013_ex47a"
    source := ⟨"matthewson-2013", "(47a)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "limx=g̱at[=t] Bob"
    glossedTokens := [("limx=g̱at[=t]", "sing=REPORT[=DM]"), ("Bob", "Bob")]
    context := "Yesterday, Henry told you that Bob sang last week."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "g̱at"), ("perspective", "past"), ("orientation", "past"), ("prospective", "false"), ("figure", "4")] }

def ex48a : Datum :=
  { id := "matthewson2013_ex48a"
    source := ⟨"matthewson-2013", "(48a)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "dim limx=g̱at[=t] Bob"
    glossedTokens := [("dim", "FUT"), ("limx=g̱at[=t]", "sing=REPORT[=DM]"), ("Bob", "Bob")]
    context := "Yesterday, Henry told you that Bob sang last week."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "g̱at"), ("perspective", "past"), ("orientation", "past"), ("prospective", "true")] }

def ex47b : Datum :=
  { id := "matthewson2013_ex47b"
    source := ⟨"matthewson-2013", "(47b)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "limx=g̱at[=t] Bob"
    glossedTokens := [("limx=g̱at[=t]", "sing=REPORT[=DM]"), ("Bob", "Bob")]
    context := "Yesterday, Henry told you that Bob was singing (at that time)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "g̱at"), ("perspective", "past"), ("orientation", "present"), ("prospective", "false"), ("figure", "4")] }

def ex48b : Datum :=
  { id := "matthewson2013_ex48b"
    source := ⟨"matthewson-2013", "(48b)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "dim limx=g̱at[=t] Bob"
    glossedTokens := [("dim", "FUT"), ("limx=g̱at[=t]", "sing=REPORT[=DM]"), ("Bob", "Bob")]
    context := "Yesterday, Henry told you that Bob was singing (at that time)."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "g̱at"), ("perspective", "past"), ("orientation", "present"), ("prospective", "true")] }

def ex47c : Datum :=
  { id := "matthewson2013_ex47c"
    source := ⟨"matthewson-2013", "(47c)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "limx=g̱at[=t] Bob"
    glossedTokens := [("limx=g̱at[=t]", "sing=REPORT[=DM]"), ("Bob", "Bob")]
    context := "Yesterday, Henry told you that Bob would be singing later that day."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "g̱at"), ("perspective", "past"), ("orientation", "future"), ("prospective", "false")] }

def ex48c : Datum :=
  { id := "matthewson2013_ex48c"
    source := ⟨"matthewson-2013", "(48c)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "dim limx=g̱at[=t] Bob"
    glossedTokens := [("dim", "FUT"), ("limx=g̱at[=t]", "sing=REPORT[=DM]"), ("Bob", "Bob")]
    context := "Yesterday, Henry told you that Bob would be singing later that day."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "g̱at"), ("perspective", "past"), ("orientation", "future"), ("prospective", "true"), ("figure", "4")] }

def ex53 : Datum :=
  { id := "matthewson2013_ex53"
    source := ⟨"matthewson-2013", "(53)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "da'aḵxw-i=hl t'x̱alpx̱-a gat dim luu wan-diit g̱oo=hl ts'im kyaa tust"
    glossedTokens := [("da'aḵxw-i=hl", "CIRC.POSS-TRA=CN"), ("t'x̱alpx̱-a", "four-LINK"), ("gat", "people"), ("dim", "FUT"), ("luu", "in"), ("wan-diit", "sit-3PL.II"), ("g̱oo=hl", "LOC=CN"), ("ts'im", "inside"), ("kyaa", "car"), ("tust", "that")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("modal", "da'aḵhlxw"), ("perspective", "present"), ("orientation", "future"), ("prospective", "true")] }

def ex53_prime : Datum :=
  { id := "matthewson2013_ex53_prime"
    source := ⟨"matthewson-2013", "(53')"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "da'aḵxw-i=hl t'x̱alpx̱-a gat luu wan-diit g̱oo=hl ts'im kyaa tust"
    glossedTokens := [("da'aḵxw-i=hl", "CIRC.POSS-TRA=CN"), ("t'x̱alpx̱-a", "four-LINK"), ("gat", "people"), ("luu", "in"), ("wan-diit", "sit-3PL.II"), ("g̱oo=hl", "LOC=CN"), ("ts'im", "inside"), ("kyaa", "car"), ("tust", "that")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("modal", "da'aḵhlxw"), ("perspective", "present"), ("orientation", "future"), ("prospective", "false")] }

def ex56 : Datum :=
  { id := "matthewson2013_ex56"
    source := ⟨"matthewson-2013", "(56)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "da'aḵhlxw-i-'y dim hahla'lsd-i'y k'yoots"
    glossedTokens := [("da'aḵhlxw-i-'y", "CIRC.POSS-TRA-1SG.II"), ("dim", "FUT"), ("hahla'lsd-i'y", "work-1SG.II"), ("k'yoots", "yesterday")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("modal", "da'aḵhlxw"), ("perspective", "past"), ("orientation", "future"), ("prospective", "true")] }

def ex56_prime : Datum :=
  { id := "matthewson2013_ex56_prime"
    source := ⟨"matthewson-2013", "(56')"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "da'aḵhlxw-i-'y hahla'lsd-i'y k'yoots"
    glossedTokens := [("da'aḵhlxw-i-'y", "CIRC.POSS-TRA-1SG.II"), ("hahla'lsd-i'y", "work-1SG.II"), ("k'yoots", "yesterday")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("modal", "da'aḵhlxw"), ("perspective", "past"), ("orientation", "future"), ("prospective", "false")] }

def ex62 : Datum :=
  { id := "matthewson2013_ex62"
    source := ⟨"matthewson-2013", "(62)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "da'aḵhlxw-i-'y dim hahla'lsd-i'y k'yoots, ii ap nee=dii wil-'y"
    glossedTokens := [("da'aḵhlxw-i-'y", "CIRC.POSS-TRA-1SG.II"), ("dim", "FUT"), ("hahla'lsd-i'y", "work-1SG.II"), ("k'yoots", "yesterday"), ("ii", "and"), ("ap", "EMPH"), ("nee=dii", "NEG=CONT"), ("wil-'y", "COMP-1SG.II")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("modal", "da'aḵhlxw"), ("perspective", "past"), ("orientation", "future"), ("prospective", "true"), ("actualityEntailment", "false")] }

def ex63a : Datum :=
  { id := "matthewson2013_ex63a"
    source := ⟨"matthewson-2013", "(63a)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "da'aḵhlxw-i-n mi=dim sa=yeed-in=hl gabii=hl cake=hl gub-n"
    glossedTokens := [("da'aḵhlxw-i-n", "CIRC.POSS-TRA-2SG.II"), ("mi=dim", "2SG.I=FUT"), ("sa=yeed-in=hl", "off-go-CAUS=CN"), ("gabii=hl", "amount=CN"), ("cake=hl", "cake=CN"), ("gub-n", "eat-2SG.II")]
    context := "Given that you want to be thinner, ..."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("modal", "da'aḵhlxw"), ("force", "possibility"), ("flavor", "bouletic")] }

def ex64 : Datum :=
  { id := "matthewson2013_ex64"
    source := ⟨"matthewson-2013", "(64)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "woy hlaa dim da'aḵhlxw-'m dim ha'jim huxw g̱a-ts'eeḵxw-'m"
    glossedTokens := [("woy", "okay"), ("hlaa", "INCEPT"), ("dim", "FUT"), ("da'aḵhlxw-'m", "CIRC.POSS-1PL.II"), ("dim", "FUT"), ("ha'jim", "once"), ("huxw", "again"), ("g̱a-ts'eeḵxw-'m", "PL-make.noise-1PL.II")]
    context := "We are burglars in someone's house, and we discover the residents are still at home, so we have to be quiet if we don't want to be caught. Finally the people leave, so we can make noise now."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("modal", "da'aḵhlxw"), ("force", "possibility"), ("flavor", "teleological")] }

def ex65 : Datum :=
  { id := "matthewson2013_ex65"
    source := ⟨"matthewson-2013", "(65)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "mahl-d-i-s nox-'y da'aḵhlxw[-i]-'y dim ma'us-'y"
    glossedTokens := [("mahl-d-i-s", "tell-T-TRA-PN"), ("nox-'y", "mother-1SG.II"), ("da'aḵhlxw[-i]-'y", "CIRC.POSS[-TRA]-1SG.II"), ("dim", "FUT"), ("ma'us-'y", "play-1SG.II")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("modal", "da'aḵhlxw"), ("force", "possibility"), ("flavor", "deontic")] }

def ex66 : Datum :=
  { id := "matthewson2013_ex66"
    source := ⟨"matthewson-2013", "(66)"⟩
    reportedIn := none
    method := some .elicitation
    language := "gitx1241"
    primaryText := "da'aḵxw-i=hl dim sim siipxw-t"
    glossedTokens := [("da'aḵxw-i=hl", "CIRC.POSS-TRA=CN"), ("dim", "FUT"), ("sim", "very"), ("siipxw-t", "sick-3SG.II")]
    context := "Bob ate bad chicken last night. He should be sick now (given the facts about what he ate)."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("modal", "da'aḵhlxw"), ("force", "necessity"), ("flavor", "circumstantial")] }

def ex73 : Datum :=
  { id := "matthewson2013_ex73"
    source := ⟨"matthewson-2013", "(73)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "anooḵ-xw(=hl) dim ha'w-s Savanna k'yoots"
    glossedTokens := [("anooḵ-xw(=hl)", "DEON.POSS-MED(=CN)"), ("dim", "FUT"), ("ha'w-s", "go.home-PN"), ("Savanna", "Savanna"), ("k'yoots", "yesterday")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "anooḵ"), ("perspective", "past"), ("orientation", "future"), ("prospective", "true")] }

def ex73_prime : Datum :=
  { id := "matthewson2013_ex73_prime"
    source := ⟨"matthewson-2013", "(73')"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "anooḵ-xw(=hl) ha'w-s Savanna k'yoots"
    glossedTokens := [("anooḵ-xw(=hl)", "DEON.POSS-MED(=CN)"), ("ha'w-s", "go.home-PN"), ("Savanna", "Savanna"), ("k'yoots", "yesterday")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "anooḵ"), ("perspective", "past"), ("orientation", "future"), ("prospective", "false")] }

def ex79 : Datum :=
  { id := "matthewson2013_ex79"
    source := ⟨"matthewson-2013", "(79)"⟩
    reportedIn := none
    method := some .elicitation
    language := "gitx1241"
    primaryText := "anooḵ-xw=hl maa'y dim limx̱s-t"
    glossedTokens := [("anooḵ-xw=hl", "DEON.POSS-MED=CN"), ("maa'y", "berries"), ("dim", "FUT"), ("limx̱s-t", "grow.PL-3SG.II")]
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "anooḵ"), ("force", "possibility"), ("flavor", "pure circumstantial")] }

def ex80 : Datum :=
  { id := "matthewson2013_ex80"
    source := ⟨"matthewson-2013", "(80)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "anooḵ-xw=diit dim hahla'lsd-i'y yuxwsa tun"
    glossedTokens := [("anooḵ-xw=diit", "DEON.POSS-MED=3PL.II"), ("dim", "FUT"), ("hahla'lsd-i'y", "work-1SG.II"), ("yuxwsa", "evening"), ("tun", "DEM")]
    context := "\"Can you go out tonight?\" \"No, I have to work.\""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "anooḵ"), ("force", "necessity"), ("flavor", "deontic")] }

def ex83 : Datum :=
  { id := "matthewson2013_ex83"
    source := ⟨"matthewson-2013", "(83)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "sgi dim ap ha'w-s Lisa"
    glossedTokens := [("sgi", "CIRC.NECESS"), ("dim", "FUT"), ("ap", "EMPH"), ("ha'w-s", "go.home-PN"), ("Lisa", "Lisa")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("modal", "sgi"), ("perspective", "present"), ("orientation", "future"), ("prospective", "true"), ("flavor", "deontic")] }

def ex83_prime : Datum :=
  { id := "matthewson2013_ex83_prime"
    source := ⟨"matthewson-2013", "(83')"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "sgi ap ha'w-s Lisa"
    glossedTokens := [("sgi", "CIRC.NECESS"), ("ap", "EMPH"), ("ha'w-s", "go.home-PN"), ("Lisa", "Lisa")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("modal", "sgi"), ("perspective", "present"), ("orientation", "future"), ("prospective", "false"), ("flavor", "deontic")] }

def ex86a : Datum :=
  { id := "matthewson2013_ex86a"
    source := ⟨"matthewson-2013", "(86a)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "sgi dim siipxw-t gyuu'n"
    glossedTokens := [("sgi", "CIRC.NECESS"), ("dim", "FUT"), ("siipxw-t", "sick-3SG.II"), ("gyuu'n", "now")]
    context := "Bob ate bad chicken last night, so he should be sick now."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("modal", "sgi"), ("force", "necessity"), ("flavor", "circumstantial")] }

def ex89 : Datum :=
  { id := "matthewson2013_ex89"
    source := ⟨"matthewson-2013", "(89)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "ji daa hasaḵ-t dim yee-t g̱oo=hl Whistler ii sgi dim-t yuxw=hl g̱enim 99"
    glossedTokens := [("ji", "IRR"), ("daa", "ever"), ("hasaḵ-t", "want-3SG.II"), ("dim", "FUT"), ("yee-t", "go-3SG.II"), ("g̱oo=hl", "LOC=CN"), ("Whistler", "Whistler"), ("ii", "and"), ("sgi", "CIRC.NECESS"), ("dim-t", "FUT-3SG.II"), ("yuxw=hl", "follow=CN"), ("g̱enim", "road"), ("99", "99")]
    context := "There is only one way to get to Whistler: Highway 99."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("modal", "sgi"), ("force", "necessity"), ("flavor", "teleological")] }

def ex90 : Datum :=
  { id := "matthewson2013_ex90"
    source := ⟨"matthewson-2013", "(90)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "ji daa dim yee-n g̱oo=hl Lillooet ii sgi mi=dim yuxw=hl g̱enim 99"
    glossedTokens := [("ji", "IRR"), ("daa", "ever"), ("dim", "FUT"), ("yee-n", "go-2SG.II"), ("g̱oo=hl", "LOC=CN"), ("Lillooet", "Lillooet"), ("ii", "and"), ("sgi", "CIRC.NECESS"), ("mi=dim", "2SG.III=FUT"), ("yuxw=hl", "follow=CN"), ("g̱enim", "road"), ("99", "99")]
    context := "There are two ways to get to Lillooet: Highway 99 or Highway 1. Highway 99 is better."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("modal", "sgi"), ("force", "weak necessity"), ("flavor", "teleological")] }

def ex91 : Datum :=
  { id := "matthewson2013_ex91"
    source := ⟨"matthewson-2013", "(91)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "sgi mi=dim baḵ=hl cake tun"
    glossedTokens := [("sgi", "CIRC.NECESS"), ("mi=dim", "2SG.III=FUT"), ("baḵ=hl", "try=CN"), ("cake", "cake"), ("tun", "DEM")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("modal", "sgi"), ("flavor", "bouletic")] }

def ex92 : Datum :=
  { id := "matthewson2013_ex92"
    source := ⟨"matthewson-2013", "(92)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "ḵ'ap sim sgi mi=dim baḵ=hl cake tun"
    glossedTokens := [("ḵ'ap", "EMPH"), ("sim", "really"), ("sgi", "CIRC.NECESS"), ("mi=dim", "2SG.III=FUT"), ("baḵ=hl", "try=CN"), ("cake", "cake"), ("tun", "DEM")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("modal", "sgi"), ("force", "necessity"), ("flavor", "bouletic")] }

def ex95a : Datum :=
  { id := "matthewson2013_ex95a"
    source := ⟨"matthewson-2013", "(95a)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "dim hadiswa-'y"
    glossedTokens := [("dim", "FUT"), ("hadiswa-'y", "sneeze-1SG.II")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("test", "sneeze"), ("modal", "dim")] }

def ex96 : Datum :=
  { id := "matthewson2013_ex96"
    source := ⟨"matthewson-2013", "(96)"⟩
    reportedIn := none
    method := some .elicitation
    language := "gitx1241"
    primaryText := "sgi dim hajiswa-'y"
    glossedTokens := [("sgi", "CIRC.NECESS"), ("dim", "FUT"), ("hajiswa-'y", "sneeze-1SG.II")]
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("test", "sneeze"), ("modal", "sgi"), ("force", "necessity"), ("flavor", "pure circumstantial")] }

def ex100a : Datum :=
  { id := "matthewson2013_ex100a"
    source := ⟨"matthewson-2013", "(100a)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "k'ap sgi dim gwalg̱a daxw-'m"
    glossedTokens := [("k'ap", "EMPH"), ("sgi", "CIRC.NECESS"), ("dim", "FUT"), ("gwalg̱a", "all"), ("daxw-'m", "die.PL-1PL.II")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("modal", "sgi"), ("force", "necessity"), ("flavor", "pure circumstantial")] }

def ex100b : Datum :=
  { id := "matthewson2013_ex100b"
    source := ⟨"matthewson-2013", "(100b)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "ap sgi dim ap 'walg̱a didaw-'m"
    glossedTokens := [("ap", "EMPH"), ("sgi", "CIRC.NECESS"), ("dim", "FUT"), ("ap", "EMPH"), ("'walg̱a", "all"), ("didaw-'m", "die.PL-1PL.II")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("modal", "sgi"), ("force", "necessity"), ("flavor", "pure circumstantial")] }

def all : List Datum := [ex22, ex29, ex30, ex37, ex38a, ex38b, ex39a, ex40a, ex41a, ex42a, ex39b, ex40b, ex41b, ex42b, ex39c, ex40c, ex41c, ex42c, ex43a, ex43a_prime, ex44, ex44_prime, ex47a, ex48a, ex47b, ex48b, ex47c, ex48c, ex53, ex53_prime, ex56, ex56_prime, ex62, ex63a, ex64, ex65, ex66, ex73, ex73_prime, ex79, ex80, ex83, ex83_prime, ex86a, ex89, ex90, ex91, ex92, ex95a, ex96, ex100a, ex100b]

end Matthewson2013.Examples
