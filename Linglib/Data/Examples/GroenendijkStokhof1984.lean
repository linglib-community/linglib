module

public import Linglib.Data.Examples.Schema

/-!
# `GroenendijkStokhof1984` — typed example data

Auto-generated from `Linglib/Data/Examples/GroenendijkStokhof1984.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace GroenendijkStokhof1984.Examples`.
-/

@[expose] public section

namespace GroenendijkStokhof1984.Examples

def gs1984_i_11 : Datum :=
  { id := "gs1984_i_11"
    source := ⟨"groenendijk-stokhof-1984", "ch. I (11), p. 24"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which student did every professor recommend?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("John.", .acceptable), ("Professor Jones, John; professor Williams, William; professor Peters, Peter ...", .acceptable), ("His best one.", .acceptable)]
    readings := [("wh-wide-scope", .acceptable), ("pair-list", .acceptable), ("functional", .acceptable)]
    paperFeatures := [] }

def gs1984_i_15 : Datum :=
  { id := "gs1984_i_15"
    source := ⟨"groenendijk-stokhof-1984", "ch. I (15), p. 24"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which student did no professor recommend?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("His worst one.", .acceptable), ("Professor Jones, John; professor Williams, William; professor Peters, Peter ...", .unacceptable)]
    readings := [("functional", .acceptable), ("pair-list", .unacceptable)]
    paperFeatures := [] }

def gs1984_i_17 : Datum :=
  { id := "gs1984_i_17"
    source := ⟨"groenendijk-stokhof-1984", "ch. I (17), p. 25"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What did two of John's friends give him for Christmas?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("wh-wide-scope", .acceptable), ("choice", .acceptable)]
    paperFeatures := [] }

def gs1984_i_18 : Datum :=
  { id := "gs1984_i_18"
    source := ⟨"groenendijk-stokhof-1984", "ch. I (18), p. 25"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Where do they have all books written by Nooteboom in stock?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("mention-all", .acceptable), ("mention-some", .acceptable)]
    paperFeatures := [] }

def gs1984_i_19 : Datum :=
  { id := "gs1984_i_19"
    source := ⟨"groenendijk-stokhof-1984", "ch. I (19), p. 27"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Whom did John kiss at the party last night?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Mary.", .acceptable), ("The girl from next door.", .acceptable), ("A redhead.", .acceptable)]
    readings := []
    paperFeatures := [] }

def gs1984_v_29 : Datum :=
  { id := "gs1984_v_29"
    source := ⟨"groenendijk-stokhof-1984", "ch. V (29), p. 278"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Where can I buy an Italian newspaper?"
    glossedTokens := []
    context := "Asked by an Italian tourist in your home-town."
    judgment := .acceptable
    contrasts := []
    readings := [("mention-some", .acceptable)]
    paperFeatures := [] }

def gs1984_v_37 : Datum :=
  { id := "gs1984_v_37"
    source := ⟨"groenendijk-stokhof-1984", "ch. V (37), p. 359"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Whom did you talk to? Your father."
    glossedTokens := []
    context := "The questioner knows who their father is."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("answer", "complete-pragmatic")] }

def gs1984_v_38 : Datum :=
  { id := "gs1984_v_38"
    source := ⟨"groenendijk-stokhof-1984", "ch. V (38), p. 359"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who won the Tour de France in 1980? The one who ended second in 1979."
    glossedTokens := []
    context := "The questioner has the information that Joop Zoetemelk ended second in the Tour de France of 1979."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("answer", "complete-pragmatic")] }

def gs1984_v_39 : Datum :=
  { id := "gs1984_v_39"
    source := ⟨"groenendijk-stokhof-1984", "ch. V (39), p. 360"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who won the Tour de France in 1980? The one who won in 1979."
    glossedTokens := []
    context := "The questioner wrongly believes that Joop Zoetemelk was the winner in 1979."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("answer", "complete-pragmatic")] }

def gs1984_v_40 : Datum :=
  { id := "gs1984_v_40"
    source := ⟨"groenendijk-stokhof-1984", "ch. V (40), pp. 360-361"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who served you when you bought these boots? An elderly lady wearing glasses."
    glossedTokens := []
    context := "Asked by the salesmanager of a client; the property applies to a single member of her staff."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("answer", "complete-pragmatic")] }

def gs1984_v_41 : Datum :=
  { id := "gs1984_v_41"
    source := ⟨"groenendijk-stokhof-1984", "ch. V (41), p. 361"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "From which authors did the editors already receive their contribution to the proceedings? I don't know, but at least they received it from Professor A."
    glossedTokens := []
    context := "The questioner knows that Prof. A. is bound to be the last one to send in his contribution."
    judgment := .acceptable
    contrasts := [("At least from Prof. A.", .acceptable)]
    readings := []
    paperFeatures := [] }

def gs1984_v_43 : Datum :=
  { id := "gs1984_v_43"
    source := ⟨"groenendijk-stokhof-1984", "ch. V (43), p. 362"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "From whom did the organizers already receive a letter of acceptance to attend the conference? At least from Prof. A."
    glossedTokens := []
    context := "Prof. A. is also always the first to accept an invitation to attend a conference."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def gs1984_vi_1 : Datum :=
  { id := "gs1984_vi_1"
    source := ⟨"groenendijk-stokhof-1984", "ch. VI (1), p. 446"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which student was recommended by each professor?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("John.", .acceptable), ("Professor Jones, Bill; professor Williams, Mary; and professor Peters, John.", .acceptable)]
    readings := [("wh-wide-scope", .acceptable), ("pair-list", .acceptable)]
    paperFeatures := [] }

def gs1984_vi_5 : Datum :=
  { id := "gs1984_vi_5"
    source := ⟨"groenendijk-stokhof-1984", "ch. VI (5), p. 447"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knows which student was recommended by each professor"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("wh-wide-scope", .acceptable), ("pair-list", .acceptable), ("term-wide-scope", .acceptable)]
    paperFeatures := [] }

def gs1984_vi_6 : Datum :=
  { id := "gs1984_vi_6"
    source := ⟨"groenendijk-stokhof-1984", "ch. VI (6), p. 447"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John wonders which student was recommended by each professor"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("wh-wide-scope", .acceptable), ("pair-list", .acceptable), ("term-wide-scope", .acceptable)]
    paperFeatures := [] }

def gs1984_vi_12 : Datum :=
  { id := "gs1984_vi_12"
    source := ⟨"groenendijk-stokhof-1984", "ch. VI (12), pp. 450-451"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Whom does John or Mary love?"
    glossedTokens := []
    context := "John loves Suzy; Mary loves Suzy and Bill."
    judgment := .acceptable
    contrasts := [("Suzy and Bill.", .acceptable), ("John, Suzy.", .acceptable), ("Mary, Suzy and Bill.", .acceptable)]
    readings := [("wh-wide-scope", .acceptable), ("choice", .acceptable)]
    paperFeatures := [] }

def gs1984_vi_17 : Datum :=
  { id := "gs1984_vi_17"
    source := ⟨"groenendijk-stokhof-1984", "ch. VI (17), p. 451"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Whom do John and Mary love?"
    glossedTokens := []
    context := "John loves Suzy; Mary loves Suzy and Bill."
    judgment := .acceptable
    contrasts := [("Suzy.", .acceptable), ("John, Suzy; and Mary, Suzy and Bill.", .acceptable)]
    readings := [("wh-wide-scope", .acceptable), ("pair-list", .acceptable)]
    paperFeatures := [] }

def gs1984_vi_21 : Datum :=
  { id := "gs1984_vi_21"
    source := ⟨"groenendijk-stokhof-1984", "ch. VI (21), p. 453"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What did two of John's friends give him for Christmas?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("A watch.", .acceptable), ("Bill, a watch and a ball; Peter, a book and a pen.", .acceptable)]
    readings := [("wh-wide-scope", .acceptable), ("choice", .acceptable)]
    paperFeatures := [] }

def gs1984_vi_24 : Datum :=
  { id := "gs1984_vi_24"
    source := ⟨"groenendijk-stokhof-1984", "ch. VI (24), p. 454"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which student was recommended by no professor?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("pair-list", .unacceptable), ("choice", .unacceptable)]
    paperFeatures := [("termMonotonicity", "decreasing")] }

def gs1984_vi_25 : Datum :=
  { id := "gs1984_vi_25"
    source := ⟨"groenendijk-stokhof-1984", "ch. VI (25), p. 454"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What did at most one of John's friends give him for Christmas?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("pair-list", .unacceptable), ("choice", .unacceptable)]
    paperFeatures := [("termMonotonicity", "decreasing")] }

def gs1984_vi_26 : Datum :=
  { id := "gs1984_vi_26"
    source := ⟨"groenendijk-stokhof-1984", "ch. VI (26), p. 455"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill wonders whom John or Mary loves"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("wh-wide-scope", .acceptable), ("choice", .acceptable), ("term-widest-scope", .acceptable)]
    paperFeatures := [] }

def gs1984_vi_32 : Datum :=
  { id := "gs1984_vi_32"
    source := ⟨"groenendijk-stokhof-1984", "ch. VI (32), p. 457"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill knows whom John or Mary loves"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def gs1984_vi_33 : Datum :=
  { id := "gs1984_vi_33"
    source := ⟨"groenendijk-stokhof-1984", "ch. VI (33), p. 458"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Where do they sell Italian newspapers in Amsterdam?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("mention-some", .acceptable), ("mention-all", .acceptable)]
    paperFeatures := [] }

def gs1984_vi_34 : Datum :=
  { id := "gs1984_vi_34"
    source := ⟨"groenendijk-stokhof-1984", "ch. VI (34), p. 458"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who has got a light?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("mention-some", .acceptable), ("mention-all", .acceptable)]
    paperFeatures := [] }

def gs1984_vi_35 : Datum :=
  { id := "gs1984_vi_35"
    source := ⟨"groenendijk-stokhof-1984", "ch. VI (35), p. 458"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Where can I find a pen?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("mention-some", .acceptable), ("mention-all", .acceptable)]
    paperFeatures := [] }

def gs1984_vi_5_1 : Datum :=
  { id := "gs1984_vi_5_1"
    source := ⟨"groenendijk-stokhof-1984", "ch. VI §5.2 (1)-(2), p. 531"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Where is a pen? On my desk."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Not in the drawer.", .acceptable), ("Nowhere.", .acceptable)]
    readings := [("mention-some", .acceptable)]
    paperFeatures := [] }

def gs1984_vi_5_9 : Datum :=
  { id := "gs1984_vi_5_9"
    source := ⟨"groenendijk-stokhof-1984", "ch. VI §5.2 (9), p. 533"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knows where a pen is"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("mention-all", .acceptable), ("mention-some", .acceptable)]
    paperFeatures := [] }

def gs1984_vi_5_12 : Datum :=
  { id := "gs1984_vi_5_12"
    source := ⟨"groenendijk-stokhof-1984", "ch. VI §5.2 (12), p. 533"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John wonders where a pen is"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("mention-all", .acceptable), ("mention-some", .acceptable)]
    paperFeatures := [] }

def gs1984_vi_5_15 : Datum :=
  { id := "gs1984_vi_5_15"
    source := ⟨"groenendijk-stokhof-1984", "ch. VI §5.3 (15)-(16), p. 534"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who has a pen? John."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("mention-some", .acceptable)]
    paperFeatures := [] }

def gs1984_vi_5_24 : Datum :=
  { id := "gs1984_vi_5_24"
    source := ⟨"groenendijk-stokhof-1984", "ch. VI §5.3 (24), p. 536"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knows who has a pen"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("mention-some", .acceptable), ("mention-all", .acceptable), ("choice", .acceptable)]
    paperFeatures := [] }

def gs1984_vi_5_33 : Datum :=
  { id := "gs1984_vi_5_33"
    source := ⟨"groenendijk-stokhof-1984", "ch. VI §5.3 (33), pp. 539-540"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Where do two unicorns live?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Bel lives in the wood, and Nap lives near the lake", .acceptable), ("In the wood, and near the lake.", .acceptable)]
    readings := [("mention-some", .acceptable), ("mention-all", .acceptable), ("mention-two", .acceptable), ("choice", .acceptable)]
    paperFeatures := [] }

def gs1984_vi_5_41 : Datum :=
  { id := "gs1984_vi_5_41"
    source := ⟨"groenendijk-stokhof-1984", "ch. VI §5.4 (41), p. 544"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Maria wonders where they sell Italian newspapers"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("mention-some", .acceptable)]
    paperFeatures := [("humanSubject", "true")] }

def gs1984_vi_5_42 : Datum :=
  { id := "gs1984_vi_5_42"
    source := ⟨"groenendijk-stokhof-1984", "ch. VI §5.4 (42), p. 544"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mario asks where they sell Italian newspapers"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("mention-some", .acceptable)]
    paperFeatures := [("humanSubject", "true")] }

def gs1984_vi_5_43 : Datum :=
  { id := "gs1984_vi_5_43"
    source := ⟨"groenendijk-stokhof-1984", "ch. VI §5.4 (43), p. 544"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary knows where they sell Italian newspapers"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("mention-some", .acceptable)]
    paperFeatures := [("humanSubject", "true")] }

def gs1984_vi_5_44 : Datum :=
  { id := "gs1984_vi_5_44"
    source := ⟨"groenendijk-stokhof-1984", "ch. VI §5.4 (44), pp. 544-545"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What the average grade is depends on what grade each student has got"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("mention-some", .unacceptable), ("mention-all", .acceptable)]
    paperFeatures := [("humanSubject", "false")] }

def gs1984_vi_5_45 : Datum :=
  { id := "gs1984_vi_5_45"
    source := ⟨"groenendijk-stokhof-1984", "ch. VI §5.4 (45), p. 545"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Where you can get gas depends on what day it is"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("mention-some", .unacceptable), ("mention-all", .acceptable)]
    paperFeatures := [("humanSubject", "false")] }

def gs1984_vi_5_46 : Datum :=
  { id := "gs1984_vi_5_46"
    source := ⟨"groenendijk-stokhof-1984", "ch. VI §5.4 (46), p. 545"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Does it matter where a pen is?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("mention-some", .unacceptable), ("mention-all", .acceptable)]
    paperFeatures := [("humanSubject", "false")] }

def gs1984_vi_5_47 : Datum :=
  { id := "gs1984_vi_5_47"
    source := ⟨"groenendijk-stokhof-1984", "ch. VI §5.4 (47), p. 545"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who will come is partly determined by who is invited"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("mention-some", .unacceptable), ("mention-all", .acceptable)]
    paperFeatures := [("humanSubject", "false")] }

def gs1984_vi_5_48 : Datum :=
  { id := "gs1984_vi_5_48"
    source := ⟨"groenendijk-stokhof-1984", "ch. VI §5.4 (48), p. 545"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Where can I get gas around here? That depends on what time it is."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("mention-some", .acceptable)]
    paperFeatures := [] }

def all : List Datum := [gs1984_i_11, gs1984_i_15, gs1984_i_17, gs1984_i_18, gs1984_i_19, gs1984_v_29, gs1984_v_37, gs1984_v_38, gs1984_v_39, gs1984_v_40, gs1984_v_41, gs1984_v_43, gs1984_vi_1, gs1984_vi_5, gs1984_vi_6, gs1984_vi_12, gs1984_vi_17, gs1984_vi_21, gs1984_vi_24, gs1984_vi_25, gs1984_vi_26, gs1984_vi_32, gs1984_vi_33, gs1984_vi_34, gs1984_vi_35, gs1984_vi_5_1, gs1984_vi_5_9, gs1984_vi_5_12, gs1984_vi_5_15, gs1984_vi_5_24, gs1984_vi_5_33, gs1984_vi_5_41, gs1984_vi_5_42, gs1984_vi_5_43, gs1984_vi_5_44, gs1984_vi_5_45, gs1984_vi_5_46, gs1984_vi_5_47, gs1984_vi_5_48]

end GroenendijkStokhof1984.Examples
