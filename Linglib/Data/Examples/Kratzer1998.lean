module

public import Linglib.Data.Examples.Schema

/-!
# `Kratzer1998` — typed example data

Auto-generated from `Linglib/Data/Examples/Kratzer1998.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Kratzer1998.Examples`.
-/

@[expose] public section

namespace Kratzer1998.Examples

def ex01 : Datum :=
  { id := "kratzer1998_ex01"
    source := ⟨"abusch-1988", "WCCFL 7 SOT example"⟩
    reportedIn := some ⟨"kratzer-1998", "(1)"⟩
    language := "stan1293"
    primaryText := "John decided a week ago that in ten days he would say to his mother that they were having their last meal together."
    glossedTokens := []
    context := "Showcases that the underlined past tense \"were\" need not be interpreted as semantically past — the meal time is in the future of utterance, not the past."
    judgment := .acceptable
    alternatives := []
    readings := [("uninterpreted-past (SOT)", .acceptable)]
    paperFeatures := [] }

def ex02 : Datum :=
  { id := "kratzer1998_ex02"
    source := ⟨"ogihara-1989", "ch. 2, (37)"⟩
    reportedIn := some ⟨"kratzer-1998", "(2)"⟩
    language := "stan1293"
    primaryText := "John said he would buy a fish that was still alive."
    glossedTokens := []
    context := "Past tense \"was\" inside the future-complement \"would buy\" — the alive-time is the future buying time, not the saying-time and not the utterance time."
    judgment := .acceptable
    alternatives := []
    readings := [("alive-at-buying (later-than-saying)", .acceptable), ("alive-at-saying", .acceptable)]
    paperFeatures := [] }

def ex03 : Datum :=
  { id := "kratzer1998_ex03"
    source := ⟨"kratzer-1998", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary predicted that she would know that she was pregnant the minute she got pregnant."
    glossedTokens := []
    context := "Multi-embedded SOT with two underlined past forms (\"was\", \"got\") both referring to future-of-utterance times."
    judgment := .acceptable
    alternatives := []
    readings := [("pregnancy-at-knowing (future-of-utterance)", .acceptable)]
    paperFeatures := [] }

def ex05 : Datum :=
  { id := "kratzer1998_ex05"
    source := ⟨"kratzer-1998", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He will marry a woman who went to Harvard."
    glossedTokens := []
    context := "The past tense \"went\" need not refer to a time before the utterance time: will shifts the evaluation time into the future and the embedded past takes us back from there, so the past cannot be analyzed as a pronoun."
    judgment := .acceptable
    alternatives := []
    readings := [("going-to-Harvard before the marrying time, not necessarily before utterance", .acceptable)]
    paperFeatures := [] }

def ex29 : Datum :=
  { id := "kratzer1998_ex29"
    source := ⟨"kratzer-1998", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John thinks that it is 10 o'clock."
    glossedTokens := []
    context := "Uttered at, say, 11 o'clock. John self-locates at 10 o'clock; his belief is not that the time of utterance is 10."
    judgment := .acceptable
    alternatives := []
    readings := [("de se (John self-locates at 10)", .acceptable), ("indexical (John thinks 11 is 10)", .marginal)]
    paperFeatures := [] }

def ex30 : Datum :=
  { id := "kratzer1998_ex30"
    source := ⟨"kratzer-1998", "(30)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John thinks that he has a headache."
    glossedTokens := []
    context := "Embedded present-under-present. John self-locates at a time when he has a headache."
    judgment := .acceptable
    alternatives := []
    readings := [("de se (headache at John's now)", .acceptable)]
    paperFeatures := [] }

def ex32a : Datum :=
  { id := "kratzer1998_ex32a"
    source := ⟨"kratzer-1998", "(32a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John bought a fish that was still alive."
    glossedTokens := []
    context := "Relative clause past tense under a matrix past. The relative-clause tense can be zero-bound (simultaneous with buying) or independently past."
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous (alive-at-buying, zero tense in RC)", .acceptable), ("independent past (alive-before-buying, past in RC)", .acceptable)]
    paperFeatures := [] }

def ex33a : Datum :=
  { id := "kratzer1998_ex33a"
    source := ⟨"kratzer-1998", "(33a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John said he would buy a fish that was still alive."
    glossedTokens := []
    context := "Same surface form as (2)/ex02, re-analyzed in Section 5 with zero-tense in the RC. Kratzer's own multi-LF variant (not attributed to Ogihara below this ex number in the paper)."
    judgment := .acceptable
    alternatives := []
    readings := [("RC zero-tense (alive-at-buying)", .acceptable), ("RC past-tense (alive-at-saying)", .acceptable)]
    paperFeatures := [] }

def ex34a : Datum :=
  { id := "kratzer1998_ex34a"
    source := ⟨"kratzer-1998", "(34a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John thought two days ago that you would be sick yesterday."
    glossedTokens := []
    context := "Sickness is at yesterday (between thought-time two-days-ago and utterance). \"Would\" makes the relative future-from-thought reachable."
    judgment := .acceptable
    alternatives := []
    readings := [("sickness yesterday, after the self-located thought time (de se)", .acceptable)]
    paperFeatures := [] }

def ex35a : Datum :=
  { id := "kratzer1998_ex35a"
    source := ⟨"kratzer-1998", "(35a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John thought two days ago that you were sick yesterday."
    glossedTokens := []
    context := "Without \"would\", the embedded past forces sickness at the thought-time (two days ago), which conflicts with the adverbial \"yesterday\"."
    judgment := .ungrammatical
    alternatives := []
    readings := [("sickness-at-thought-time", .ungrammatical)]
    paperFeatures := [] }

def ex36a : Datum :=
  { id := "kratzer1998_ex36a"
    source := ⟨"kratzer-1998", "(36a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The ultrasound picture indicated that Mary is pregnant."
    glossedTokens := []
    context := "Past matrix with present embedded. Embedded present can be de re about a present state of Mary that the past ultrasound picture is about."
    judgment := .acceptable
    alternatives := []
    readings := [("de re on present state", .marginal)]
    paperFeatures := [] }

def ex36b : Datum :=
  { id := "kratzer1998_ex36b"
    source := ⟨"kratzer-1998", "(36b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The ultrasound picture indicated of a present state of Mary's that it is a pregnancy."
    glossedTokens := []
    context := "Ogihara-style paraphrase that makes the temporal de re explicit."
    judgment := .acceptable
    alternatives := []
    readings := [("de re on present state (explicit)", .acceptable)]
    paperFeatures := [] }

def ex40a : Datum :=
  { id := "kratzer1998_ex40a"
    source := ⟨"kratzer-1998", "(40a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who built this Church? Borromini built this church."
    glossedTokens := []
    context := "Looking at churches in Italy, no previous discourse. English simple past acceptable out of the blue."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "simple past"), ("context", "out of the blue")] }

def ex40b : Datum :=
  { id := "kratzer1998_ex40b"
    source := ⟨"kratzer-1998", "(40b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wer baute diese Kirche? Borromini baute diese Kirche."
    glossedTokens := [("Wer", "Who"), ("baute", "built"), ("diese", "this"), ("Kirche", "church"), ("Borromini", "Borromini"), ("baute", "built"), ("diese", "this"), ("Kirche", "church")]
    context := "Looking at churches in Italy, no previous discourse. German simple past (Präteritum) infelicitous out of the blue."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("form", "Präteritum"), ("context", "out of the blue")] }

def ex40c : Datum :=
  { id := "kratzer1998_ex40c"
    source := ⟨"kratzer-1998", "(40c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wer hat diese Kirche gebaut? Borromini hat diese Kirche gebaut."
    glossedTokens := [("Wer", "Who"), ("hat", "has"), ("diese", "this"), ("Kirche", "church"), ("gebaut", "built"), ("Borromini", "Borromini"), ("hat", "has"), ("diese", "this"), ("Kirche", "church"), ("gebaut", "built")]
    context := "Same out-of-the-blue Italy-church scenario. Standard German Perfekt is felicitous where simple past is not."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "Perfekt"), ("context", "out of the blue")] }

def ex41a : Datum :=
  { id := "kratzer1998_ex41a"
    source := ⟨"kratzer-1998", "(41a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We will answer every letter that we got."
    glossedTokens := []
    context := "English simple past in a relative clause inside a future matrix. Felicitous even without a contextually salient past interval."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "simple past")] }

def ex41b : Datum :=
  { id := "kratzer1998_ex41b"
    source := ⟨"kratzer-1998", "(41b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wir werden jeden Brief beantworten, den wir bekamen."
    glossedTokens := [("Wir", "We"), ("werden", "will"), ("jeden", "every"), ("Brief", "letter"), ("beantworten", "answer"), ("den", "that"), ("wir", "we"), ("bekamen", "received")]
    context := "Same content as (41a) in Standard German Präteritum. Needs a contextually salient past time to be acceptable."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "Präteritum")] }

def ex41c : Datum :=
  { id := "kratzer1998_ex41c"
    source := ⟨"kratzer-1998", "(41c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wir werden jeden Brief beantworten, den wir bekommen haben."
    glossedTokens := [("Wir", "We"), ("werden", "will"), ("jeden", "every"), ("Brief", "letter"), ("beantworten", "answer"), ("den", "that"), ("wir", "we"), ("bekommen", "gotten"), ("haben", "have")]
    context := "Same content as (41a/b) but with German Perfekt in the RC. Felicitous without a salient past time."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "Perfekt")] }

def ex42a : Datum :=
  { id := "kratzer1998_ex42a"
    source := ⟨"kratzer-1998", "(42a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John dreamed about eating a fish that he caught himself."
    glossedTokens := []
    context := "RC past \"caught\" can have either an anaphoric reading (relative to the dream-time) or an independent backward-shifted reading."
    judgment := .acceptable
    alternatives := []
    readings := [("anaphoric (caught-before-dreaming)", .acceptable), ("backward-shifted (caught-before-eating)", .acceptable)]
    paperFeatures := [] }

def ex42b : Datum :=
  { id := "kratzer1998_ex42b"
    source := ⟨"kratzer-1998", "(42b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Hans träumte davon, einen Fisch zu essen, den er selber fing."
    glossedTokens := [("Hans", "Hans"), ("träumte", "dreamed"), ("davon", "of it"), ("einen", "a"), ("Fisch", "fish"), ("zu", "to"), ("essen", "eat"), ("den", "that"), ("er", "he"), ("selber", "himself"), ("fing", "caught")]
    context := "Same content as (42a) with German Präteritum in the RC. Per Kratzer, the past tense must be anaphoric (no backward-shifted reading)."
    judgment := .acceptable
    alternatives := []
    readings := [("anaphoric (caught-at-dreaming-time)", .acceptable), ("backward-shifted (caught-before-eating)", .unacceptable)]
    paperFeatures := [] }

def ex42c : Datum :=
  { id := "kratzer1998_ex42c"
    source := ⟨"kratzer-1998", "(42c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Hans träumte davon, einen Fisch zu essen, den er selber gefangen hatte."
    glossedTokens := [("Hans", "Hans"), ("träumte", "dreamed"), ("davon", "of it"), ("einen", "a"), ("Fisch", "fish"), ("zu", "to"), ("essen", "eat"), ("den", "that"), ("er", "he"), ("selber", "himself"), ("gefangen", "caught"), ("hatte", "had")]
    context := "To recover the backward-shifted reading in German, the past perfect (Plusquamperfekt) is required."
    judgment := .acceptable
    alternatives := []
    readings := [("backward-shifted (caught-before-eating)", .acceptable)]
    paperFeatures := [] }

def all : List Datum := [ex01, ex02, ex03, ex05, ex29, ex30, ex32a, ex33a, ex34a, ex35a, ex36a, ex36b, ex40a, ex40b, ex40c, ex41a, ex41b, ex41c, ex42a, ex42b, ex42c]

end Kratzer1998.Examples
