module

public import Linglib.Data.Examples.Schema

/-!
# `WangDavidson2026` — typed example data

Auto-generated from `Linglib/Data/Examples/WangDavidson2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace WangDavidson2026.Examples`.
-/

@[expose] public section

namespace WangDavidson2026.Examples

def ex_1 : Datum :=
  { id := "wangdavidson2026_1"
    source := ⟨"wang-davidson-2026", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John's violin is expensive."
    glossedTokens := []
    context := "We don't know whether John has a violin."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("presupposition", "John has a violin"), ("projection", "projects")] }

def ex_2 : Datum :=
  { id := "wangdavidson2026_2"
    source := ⟨"wang-davidson-2026", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John's violin is expensive, and he has a good violin."
    glossedTokens := []
    context := "We don't know whether John has a violin."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("presupposition", "John has a violin"), ("projection", "projects"), ("direction", "right-to-left")] }

def ex_3 : Datum :=
  { id := "wangdavidson2026_3"
    source := ⟨"wang-davidson-2026", "(1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John has a good violin, and his violin is expensive."
    glossedTokens := []
    context := "We don't know whether John has a violin."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("presupposition", "John has a violin"), ("projection", "filtered"), ("direction", "left-to-right")] }

def ex_4 : Datum :=
  { id := "wangdavidson2026_4"
    source := ⟨"wang-davidson-2026", "(13)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "我相信小张会来或者小王会来"
    glossedTokens := [("我", "I"), ("相信", "believe"), ("小张", "Zhang"), ("会", "will"), ("来", "come"), ("或者", "or"), ("小王", "Wang"), ("会", "will"), ("来", "come")]
    glossedWords := [⟨['我'], ['I'], [⟨['我'], ['I'], none⟩]⟩, ⟨['相', '信'], ['b', 'e', 'l', 'i', 'e', 'v', 'e'], [⟨['相', '信'], ['b', 'e', 'l', 'i', 'e', 'v', 'e'], none⟩]⟩, ⟨['小', '张'], ['Z', 'h', 'a', 'n', 'g'], [⟨['小', '张'], ['Z', 'h', 'a', 'n', 'g'], none⟩]⟩, ⟨['会'], ['w', 'i', 'l', 'l'], [⟨['会'], ['w', 'i', 'l', 'l'], none⟩]⟩, ⟨['来'], ['c', 'o', 'm', 'e'], [⟨['来'], ['c', 'o', 'm', 'e'], none⟩]⟩, ⟨['或', '者'], ['o', 'r'], [⟨['或', '者'], ['o', 'r'], none⟩]⟩, ⟨['小', '王'], ['W', 'a', 'n', 'g'], [⟨['小', '王'], ['W', 'a', 'n', 'g'], none⟩]⟩, ⟨['会'], ['w', 'i', 'l', 'l'], [⟨['会'], ['w', 'i', 'l', 'l'], none⟩]⟩, ⟨['来'], ['c', 'o', 'm', 'e'], [⟨['来'], ['c', 'o', 'm', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Li said the sentence as a prediction. In fact, afterwards both Zhang and Wang came. Do you consider Li's prediction correct or incorrect?"
    judgment := .acceptable
    alternatives := []
    readings := [("inclusive", .acceptable), ("exclusive", .marginal)]
    paperFeatures := [("task", "norming"), ("monotonicity", "UE")] }

def ex_5 : Datum :=
  { id := "wangdavidson2026_5"
    source := ⟨"wang-davidson-2026", "(15)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "如果小李已经戒酒了或者从来不喝酒，那么他今晚的行为很合理。"
    glossedTokens := [("如果", "if"), ("小李", "Li"), ("已经", "already"), ("戒", "quit"), ("酒", "alcohol"), ("了", "PFV"), ("或者", "or"), ("从来", "always"), ("不", "NEG"), ("喝", "drink"), ("酒", "alcohol"), ("那么", "then"), ("他", "he"), ("今晚的", "tonight-DE"), ("行为", "behavior"), ("很", "very"), ("合理", "reasonable")]
    glossedWords := [⟨['如', '果'], ['i', 'f'], [⟨['如', '果'], ['i', 'f'], none⟩]⟩, ⟨['小', '李'], ['L', 'i'], [⟨['小', '李'], ['L', 'i'], none⟩]⟩, ⟨['已', '经'], ['a', 'l', 'r', 'e', 'a', 'd', 'y'], [⟨['已', '经'], ['a', 'l', 'r', 'e', 'a', 'd', 'y'], none⟩]⟩, ⟨['戒'], ['q', 'u', 'i', 't'], [⟨['戒'], ['q', 'u', 'i', 't'], none⟩]⟩, ⟨['酒'], ['a', 'l', 'c', 'o', 'h', 'o', 'l'], [⟨['酒'], ['a', 'l', 'c', 'o', 'h', 'o', 'l'], none⟩]⟩, ⟨['了'], ['P', 'F', 'V'], [⟨['了'], ['P', 'F', 'V'], none⟩]⟩, ⟨['或', '者'], ['o', 'r'], [⟨['或', '者'], ['o', 'r'], none⟩]⟩, ⟨['从', '来'], ['a', 'l', 'w', 'a', 'y', 's'], [⟨['从', '来'], ['a', 'l', 'w', 'a', 'y', 's'], none⟩]⟩, ⟨['不'], ['N', 'E', 'G'], [⟨['不'], ['N', 'E', 'G'], none⟩]⟩, ⟨['喝'], ['d', 'r', 'i', 'n', 'k'], [⟨['喝'], ['d', 'r', 'i', 'n', 'k'], none⟩]⟩, ⟨['酒'], ['a', 'l', 'c', 'o', 'h', 'o', 'l'], [⟨['酒'], ['a', 'l', 'c', 'o', 'h', 'o', 'l'], none⟩]⟩, ⟨['那', '么'], ['t', 'h', 'e', 'n'], [⟨['那', '么'], ['t', 'h', 'e', 'n'], none⟩]⟩, ⟨['他'], ['h', 'e'], [⟨['他'], ['h', 'e'], none⟩]⟩, ⟨['今', '晚', '的'], ['t', 'o', 'n', 'i', 'g', 'h', 't', '-', 'D', 'E'], []⟩, ⟨['行', '为'], ['b', 'e', 'h', 'a', 'v', 'i', 'o', 'r'], [⟨['行', '为'], ['b', 'e', 'h', 'a', 'v', 'i', 'o', 'r'], none⟩]⟩, ⟨['很'], ['v', 'e', 'r', 'y'], [⟨['很'], ['v', 'e', 'r', 'y'], none⟩]⟩, ⟨['合', '理'], ['r', 'e', 'a', 's', 'o', 'n', 'a', 'b', 'l', 'e'], [⟨['合', '理'], ['r', 'e', 'a', 's', 'o', 'n', 'a', 'b', 'l', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "I didn't know Li at all before, and I didn't know if he ever drank. At tonight's dinner gathering, most people drank, but Li didn't drink a drop, so I thought:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("condition", "PSFIRST"), ("monotonicity", "DE"), ("trigger", "jie"), ("context", "explicitly ignorant")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_5]

end WangDavidson2026.Examples
