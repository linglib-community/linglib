module

public import Linglib.Data.Examples.Schema

/-!
# `OsborneLi2023` — typed example data

Auto-generated from `Linglib/Data/Examples/OsborneLi2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace OsborneLi2023.Examples`.
-/

@[expose] public section

namespace OsborneLi2023.Examples

def ex2a : Datum :=
  { id := "osborneli2023_ex2a"
    source := ⟨"osborne-li-2023", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Max and Lucie talked about him."
    glossedTokens := []
    context := "Coordinate subject; pronoun in PP complement. CRDC predicts marginality of co-valuing `him` with `Max` (conjunct valent of the subject coordinate structure)."
    judgment := .questionable
    contrasts := []
    readings := [("him = Max (co-valued)", .questionable), ("him = external referent", .acceptable)]
    paperFeatures := [("coordinateSubject", "true"), ("coVValuedPair", "him;Max"), ("paperSection", "1"), ("paperMeanScore", "2.38"), ("paperNRespondents", "60")] }

def ex3a : Datum :=
  { id := "osborneli2023_ex3a"
    source := ⟨"osborne-li-2023", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John and Mary talked about himself."
    glossedTokens := []
    context := "Coordinate subject; reflexive in PP complement. Co-valuing `himself` with `John` (a conjunct valent of the subject) is marginal."
    judgment := .questionable
    contrasts := []
    readings := [("himself = John", .questionable)]
    paperFeatures := [("coordinateSubject", "true"), ("coVValuedPair", "himself;John"), ("anaphorType", "reflexive"), ("paperSection", "2"), ("paperMeanScore", "2.15"), ("paperNRespondents", "60")] }

def ex3b : Datum :=
  { id := "osborneli2023_ex3b"
    source := ⟨"osborne-li-2023", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John and Mary talked about him."
    glossedTokens := []
    context := "Co-valuing `him` with `John` (conjunct valent of subject coordinate structure). Same CRDC structure as (2a) with masculine antecedent."
    judgment := .questionable
    contrasts := []
    readings := [("him = John (co-valued)", .questionable)]
    paperFeatures := [("coordinateSubject", "true"), ("coVValuedPair", "him;John"), ("paperSection", "2"), ("paperMeanScore", "2.43"), ("paperNRespondents", "60")] }

def ex5a : Datum :=
  { id := "osborneli2023_ex5a"
    source := ⟨"osborne-li-2023", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Both John and Mary love him."
    glossedTokens := []
    context := "`both ... and ...` coordinator; pronoun as object of `love`. `both` forces the distributive reading, which blocks co-valuing `him` with `John` under Safir's Coargument Dependency Constraint (CDC)."
    judgment := .ungrammatical
    contrasts := []
    readings := [("him = John", .ungrammatical)]
    paperFeatures := [("coordinateSubject", "true"), ("coordinator", "both...and"), ("coVValuedPair", "him;John"), ("paperSection", "2"), ("paperMeanScore", "3.20"), ("paperNRespondents", "60")] }

def ex6a : Datum :=
  { id := "osborneli2023_ex6a"
    source := ⟨"osborne-li-2023", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill and Mary consider him to be ready for a raise."
    glossedTokens := []
    context := "Coordinate subject; pronoun in raising-to-object position. CRDC applies: `him` is a full valent of `consider` (raising-to-object); `Bill` is a conjunct valent of the coordinate subject. Co-valuation is marginal."
    judgment := .questionable
    contrasts := []
    readings := [("him = Bill", .questionable)]
    paperFeatures := [("coordinateSubject", "true"), ("construction", "raising-to-object"), ("coVValuedPair", "him;Bill"), ("paperSection", "2"), ("paperMeanScore", "2.42"), ("paperNRespondents", "60")] }

def ex9a : Datum :=
  { id := "osborneli2023_ex9a"
    source := ⟨"osborne-li-2023", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Max talked about himself."
    glossedTokens := []
    context := "Non-coordinate baseline; reflexive licensed by Condition A. CRDC is silent (no coordination); the example is fully acceptable."
    judgment := .acceptable
    contrasts := []
    readings := [("himself = Max", .acceptable)]
    paperFeatures := [("coordinateSubject", "false"), ("coVValuedPair", "himself;Max"), ("paperSection", "3"), ("paperMeanScore", "1.28"), ("paperNRespondents", "60")] }

def ex9b : Datum :=
  { id := "osborneli2023_ex9b"
    source := ⟨"osborne-li-2023", "(9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Max talked about him."
    glossedTokens := []
    context := "Non-coordinate baseline; co-valuing `him` with local subject `Max` violates Condition B (not CRDC, which is silent here)."
    judgment := .questionable
    contrasts := []
    readings := [("him = Max", .questionable), ("him = external referent", .acceptable)]
    paperFeatures := [("coordinateSubject", "false"), ("coVValuedPair", "him;Max"), ("paperSection", "3"), ("paperMeanScore", "2.92"), ("paperNRespondents", "60")] }

def ex11a : Datum :=
  { id := "osborneli2023_ex11a"
    source := ⟨"osborne-li-2023", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Max and Lucie talked about his work."
    glossedTokens := []
    context := "Coordinate subject; possessive pronoun inside object PP. Possessives embed the conjunct-valent referent inside a further DP, weakening CRDC's marginality prediction."
    judgment := .acceptable
    contrasts := []
    readings := [("his = Max", .acceptable)]
    paperFeatures := [("coordinateSubject", "true"), ("coVValuedPair", "his;Max"), ("anaphorType", "possessive"), ("paperSection", "3"), ("paperMeanScore", "1.20"), ("paperNRespondents", "60")] }

def ex11e : Datum :=
  { id := "osborneli2023_ex11e"
    source := ⟨"osborne-li-2023", "(11e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Max and Lucie talked about Max."
    glossedTokens := []
    context := "Coordinate subject; name repeated as object. Condition C is in play, not CRDC; the co-valued reading is available."
    judgment := .acceptable
    contrasts := []
    readings := [("object Max = subject Max (co-valued)", .acceptable)]
    paperFeatures := [("coordinateSubject", "true"), ("coVValuedPair", "Max;Max"), ("anaphorType", "R-expression"), ("paperSection", "3"), ("paperMeanScore", "1.47"), ("paperNRespondents", "100")] }

def ex20b : Datum :=
  { id := "osborneli2023_ex20b"
    source := ⟨"osborne-li-2023", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Hank and Hillary appear to her to be good friends."
    glossedTokens := []
    context := "Subject-to-subject raising over an experiencer PP. `her` is a full valent of `appear`; `Hillary` is a conjunct valent of the raised subject coordinate structure. CRDC predicts marginality of co-valuation."
    judgment := .questionable
    contrasts := []
    readings := [("her = Hillary", .questionable)]
    paperFeatures := [("coordinateSubject", "true"), ("construction", "raising-with-experiencer"), ("coVValuedPair", "her;Hillary"), ("paperSection", "3"), ("paperMeanScore", "2.68"), ("paperNRespondents", "60")] }

def ex24a : Datum :=
  { id := "osborneli2023_ex24a"
    source := ⟨"osborne-li-2023", "(24a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John talked about himself and his mother."
    glossedTokens := []
    context := "Coordinate *object*, not coordinate subject. `himself` is a conjunct valent of a full valent of `talked`; co-valuation with the full-valent subject `John` is the reverse direction of CRDC (conjunct anaphor of full antecedent), which CRDC explicitly permits."
    judgment := .acceptable
    contrasts := []
    readings := [("himself = John", .acceptable)]
    paperFeatures := [("coordinateObject", "true"), ("coVValuedPair", "himself;John"), ("paperSection", "3"), ("paperMeanScore", "1.14"), ("paperNRespondents", "60")] }

def ex25c : Datum :=
  { id := "osborneli2023_ex25c"
    source := ⟨"osborne-li-2023", "(25c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane defended her."
    glossedTokens := []
    context := "Non-coordinate Condition B violation. Co-valuing `her` with local subject `Jane` is straightforwardly ungrammatical. CRDC is silent (no coordination)."
    judgment := .ungrammatical
    contrasts := []
    readings := [("her = Jane", .ungrammatical)]
    paperFeatures := [("coordinateSubject", "false"), ("coVValuedPair", "her;Jane"), ("paperSection", "3"), ("paperMeanScore", "3.20"), ("paperNRespondents", "40")] }

def ex28d : Datum :=
  { id := "osborneli2023_ex28d"
    source := ⟨"osborne-li-2023", "(28d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John expected Mary and him to be able to leave soon."
    glossedTokens := []
    context := "Raising-to-object with coordinate object; `him` is a conjunct valent of the embedded subject. Co-valuing `him` with matrix-subject `John` (a full valent of `expected`) is acceptable — the reverse CRDC direction (conjunct anaphor of full antecedent)."
    judgment := .acceptable
    contrasts := []
    readings := [("him = John", .acceptable)]
    paperFeatures := [("coordinateObject", "true"), ("construction", "raising-to-object"), ("coVValuedPair", "him;John"), ("paperSection", "3"), ("paperMeanScore", "1.40"), ("paperNRespondents", "60")] }

def ex55a : Datum :=
  { id := "osborneli2023_ex55a"
    source := ⟨"osborne-li-2023", "(55a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who voted for Sophy? – Sophy and Edgar voted for her."
    glossedTokens := []
    context := "Coordinate-subject CRDC configuration, but a structural counterexample: speakers accept co-valuation of `her` with `Sophy` despite CRDC's marginality prediction. Paper discusses this as a candidate exception (Section 6)."
    judgment := .acceptable
    contrasts := []
    readings := [("her = Sophy", .acceptable)]
    paperFeatures := [("coordinateSubject", "true"), ("coVValuedPair", "her;Sophy"), ("paperSection", "6"), ("isCounterexample", "true"), ("paperMeanScore", "1.43"), ("paperNRespondents", "40")] }

def all : List Datum := [ex2a, ex3a, ex3b, ex5a, ex6a, ex9a, ex9b, ex11a, ex11e, ex20b, ex24a, ex25c, ex28d, ex55a]

end OsborneLi2023.Examples
