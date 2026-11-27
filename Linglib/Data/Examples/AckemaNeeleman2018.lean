module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `AckemaNeeleman2018` — typed example data

Auto-generated from `Linglib/Data/Examples/AckemaNeeleman2018.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AckemaNeeleman2018.Examples`.
-/

@[expose] public section

namespace AckemaNeeleman2018.Examples

def ex_2a : Datum :=
  { id := "ackemaneeleman2018_2a"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It seems that Mary has left for Paris."
    glossedTokens := [("It", ""), ("seems", ""), ("that", ""), ("Mary", ""), ("has", ""), ("left", ""), ("for", ""), ("Paris", "")]
    glossedWords := [⟨['I', 't'], [], [⟨['I', 't'], [], none⟩]⟩, ⟨['s', 'e', 'e', 'm', 's'], [], [⟨['s', 'e', 'e', 'm', 's'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['M', 'a', 'r', 'y'], [], [⟨['M', 'a', 'r', 'y'], [], none⟩]⟩, ⟨['h', 'a', 's'], [], [⟨['h', 'a', 's'], [], none⟩]⟩, ⟨['l', 'e', 'f', 't'], [], [⟨['l', 'e', 'f', 't'], [], none⟩]⟩, ⟨['f', 'o', 'r'], [], [⟨['f', 'o', 'r'], [], none⟩]⟩, ⟨['P', 'a', 'r', 'i', 's'], [], [⟨['P', 'a', 'r', 'i', 's'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "subject", some "it"⟩]
    paperFeatures := [("phenomenon", "expletive")] }

def ex_2b : Datum :=
  { id := "ackemaneeleman2018_2b"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is raining again in Edinburgh."
    glossedTokens := [("It", ""), ("is", ""), ("raining", ""), ("again", ""), ("in", ""), ("Edinburgh", "")]
    glossedWords := [⟨['I', 't'], [], [⟨['I', 't'], [], none⟩]⟩, ⟨['i', 's'], [], [⟨['i', 's'], [], none⟩]⟩, ⟨['r', 'a', 'i', 'n', 'i', 'n', 'g'], [], [⟨['r', 'a', 'i', 'n', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['a', 'g', 'a', 'i', 'n'], [], [⟨['a', 'g', 'a', 'i', 'n'], [], none⟩]⟩, ⟨['i', 'n'], [], [⟨['i', 'n'], [], none⟩]⟩, ⟨['E', 'd', 'i', 'n', 'b', 'u', 'r', 'g', 'h'], [], [⟨['E', 'd', 'i', 'n', 'b', 'u', 'r', 'g', 'h'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "subject", some "it"⟩]
    paperFeatures := [("phenomenon", "expletive")] }

def ex_20a : Datum :=
  { id := "ackemaneeleman2018_20a"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I can't believe your luck!"
    glossedTokens := []
    context := "John discovers he has a winning lottery ticket."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "self-talk")] }

def ex_21a : Datum :=
  { id := "ackemaneeleman2018_21a"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (21a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I can't believe your luck! If we hurry, we can still collect the money today."
    glossedTokens := []
    context := "John discovers he has a winning lottery ticket."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "self-talk")] }

def ex_24a : Datum :=
  { id := "ackemaneeleman2018_24a"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (24a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It seems that Vitesse won."
    glossedTokens := [("It", ""), ("seems", ""), ("that", ""), ("Vitesse", ""), ("won", "")]
    glossedWords := [⟨['I', 't'], [], [⟨['I', 't'], [], none⟩]⟩, ⟨['s', 'e', 'e', 'm', 's'], [], [⟨['s', 'e', 'e', 'm', 's'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['V', 'i', 't', 'e', 's', 's', 'e'], [], [⟨['V', 'i', 't', 'e', 's', 's', 'e'], [], none⟩]⟩, ⟨['w', 'o', 'n'], [], [⟨['w', 'o', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := [("It seem that Vitesse won.", .ungrammatical)]
    readings := []
    spans := [⟨0, 1, "subject", some "it"⟩]
    paperFeatures := [("phenomenon", "expletive")] }

def ex_24b_i : Datum :=
  { id := "ackemaneeleman2018_24b_i"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (24b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I seem that Vitesse won."
    glossedTokens := [("I", ""), ("seem", ""), ("that", ""), ("Vitesse", ""), ("won", "")]
    glossedWords := [⟨['I'], [], [⟨['I'], [], none⟩]⟩, ⟨['s', 'e', 'e', 'm'], [], [⟨['s', 'e', 'e', 'm'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['V', 'i', 't', 'e', 's', 's', 'e'], [], [⟨['V', 'i', 't', 'e', 's', 's', 'e'], [], none⟩]⟩, ⟨['w', 'o', 'n'], [], [⟨['w', 'o', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨0, 1, "subject", some "i"⟩]
    paperFeatures := [("phenomenon", "expletive")] }

def ex_24b_you : Datum :=
  { id := "ackemaneeleman2018_24b_you"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (24b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You seem that Vitesse won."
    glossedTokens := [("You", ""), ("seem", ""), ("that", ""), ("Vitesse", ""), ("won", "")]
    glossedWords := [⟨['Y', 'o', 'u'], [], [⟨['Y', 'o', 'u'], [], none⟩]⟩, ⟨['s', 'e', 'e', 'm'], [], [⟨['s', 'e', 'e', 'm'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['V', 'i', 't', 'e', 's', 's', 'e'], [], [⟨['V', 'i', 't', 'e', 's', 's', 'e'], [], none⟩]⟩, ⟨['w', 'o', 'n'], [], [⟨['w', 'o', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨0, 1, "subject", some "you"⟩]
    paperFeatures := [("phenomenon", "expletive")] }

def ex_25_is : Datum :=
  { id := "ackemaneeleman2018_25_is"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (25)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Nog jaren is naar een oplossing gezocht."
    glossedTokens := [("Nog", "still"), ("jaren", "years"), ("is", "be.3SG"), ("naar", "for"), ("een", "a"), ("oplossing", "solution"), ("gezocht", "searched")]
    glossedWords := [⟨['N', 'o', 'g'], ['s', 't', 'i', 'l', 'l'], [⟨['N', 'o', 'g'], ['s', 't', 'i', 'l', 'l'], none⟩]⟩, ⟨['j', 'a', 'r', 'e', 'n'], ['y', 'e', 'a', 'r', 's'], [⟨['j', 'a', 'r', 'e', 'n'], ['y', 'e', 'a', 'r', 's'], none⟩]⟩, ⟨['i', 's'], ['b', 'e', '.', '3', 'S', 'G'], [⟨['i', 's'], ['b', 'e', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['n', 'a', 'a', 'r'], ['f', 'o', 'r'], [⟨['n', 'a', 'a', 'r'], ['f', 'o', 'r'], none⟩]⟩, ⟨['e', 'e', 'n'], ['a'], [⟨['e', 'e', 'n'], ['a'], none⟩]⟩, ⟨['o', 'p', 'l', 'o', 's', 's', 'i', 'n', 'g'], ['s', 'o', 'l', 'u', 't', 'i', 'o', 'n'], [⟨['o', 'p', 'l', 'o', 's', 's', 'i', 'n', 'g'], ['s', 'o', 'l', 'u', 't', 'i', 'o', 'n'], none⟩]⟩, ⟨['g', 'e', 'z', 'o', 'c', 'h', 't'], ['s', 'e', 'a', 'r', 'c', 'h', 'e', 'd'], [⟨['g', 'e', 'z', 'o', 'c', 'h', 't'], ['s', 'e', 'a', 'r', 'c', 'h', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "agreement", none⟩]
    paperFeatures := [("phenomenon", "default agreement")] }

def ex_25_ben : Datum :=
  { id := "ackemaneeleman2018_25_ben"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (25)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Nog jaren ben naar een oplossing gezocht."
    glossedTokens := [("Nog", "still"), ("jaren", "years"), ("ben", "be.1SG"), ("naar", "for"), ("een", "a"), ("oplossing", "solution"), ("gezocht", "searched")]
    glossedWords := [⟨['N', 'o', 'g'], ['s', 't', 'i', 'l', 'l'], [⟨['N', 'o', 'g'], ['s', 't', 'i', 'l', 'l'], none⟩]⟩, ⟨['j', 'a', 'r', 'e', 'n'], ['y', 'e', 'a', 'r', 's'], [⟨['j', 'a', 'r', 'e', 'n'], ['y', 'e', 'a', 'r', 's'], none⟩]⟩, ⟨['b', 'e', 'n'], ['b', 'e', '.', '1', 'S', 'G'], [⟨['b', 'e', 'n'], ['b', 'e', '.', '1', 'S', 'G'], none⟩]⟩, ⟨['n', 'a', 'a', 'r'], ['f', 'o', 'r'], [⟨['n', 'a', 'a', 'r'], ['f', 'o', 'r'], none⟩]⟩, ⟨['e', 'e', 'n'], ['a'], [⟨['e', 'e', 'n'], ['a'], none⟩]⟩, ⟨['o', 'p', 'l', 'o', 's', 's', 'i', 'n', 'g'], ['s', 'o', 'l', 'u', 't', 'i', 'o', 'n'], [⟨['o', 'p', 'l', 'o', 's', 's', 'i', 'n', 'g'], ['s', 'o', 'l', 'u', 't', 'i', 'o', 'n'], none⟩]⟩, ⟨['g', 'e', 'z', 'o', 'c', 'h', 't'], ['s', 'e', 'a', 'r', 'c', 'h', 'e', 'd'], [⟨['g', 'e', 'z', 'o', 'c', 'h', 't'], ['s', 'e', 'a', 'r', 'c', 'h', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨2, 1, "agreement", none⟩]
    paperFeatures := [("phenomenon", "default agreement")] }

def ex_25_bent : Datum :=
  { id := "ackemaneeleman2018_25_bent"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (25)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Nog jaren bent naar een oplossing gezocht."
    glossedTokens := [("Nog", "still"), ("jaren", "years"), ("bent", "be.2SG"), ("naar", "for"), ("een", "a"), ("oplossing", "solution"), ("gezocht", "searched")]
    glossedWords := [⟨['N', 'o', 'g'], ['s', 't', 'i', 'l', 'l'], [⟨['N', 'o', 'g'], ['s', 't', 'i', 'l', 'l'], none⟩]⟩, ⟨['j', 'a', 'r', 'e', 'n'], ['y', 'e', 'a', 'r', 's'], [⟨['j', 'a', 'r', 'e', 'n'], ['y', 'e', 'a', 'r', 's'], none⟩]⟩, ⟨['b', 'e', 'n', 't'], ['b', 'e', '.', '2', 'S', 'G'], [⟨['b', 'e', 'n', 't'], ['b', 'e', '.', '2', 'S', 'G'], none⟩]⟩, ⟨['n', 'a', 'a', 'r'], ['f', 'o', 'r'], [⟨['n', 'a', 'a', 'r'], ['f', 'o', 'r'], none⟩]⟩, ⟨['e', 'e', 'n'], ['a'], [⟨['e', 'e', 'n'], ['a'], none⟩]⟩, ⟨['o', 'p', 'l', 'o', 's', 's', 'i', 'n', 'g'], ['s', 'o', 'l', 'u', 't', 'i', 'o', 'n'], [⟨['o', 'p', 'l', 'o', 's', 's', 'i', 'n', 'g'], ['s', 'o', 'l', 'u', 't', 'i', 'o', 'n'], none⟩]⟩, ⟨['g', 'e', 'z', 'o', 'c', 'h', 't'], ['s', 'e', 'a', 'r', 'c', 'h', 'e', 'd'], [⟨['g', 'e', 'z', 'o', 'c', 'h', 't'], ['s', 'e', 'a', 'r', 'c', 'h', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨2, 1, "agreement", none⟩]
    paperFeatures := [("phenomenon", "default agreement")] }

def ex_25_zijn : Datum :=
  { id := "ackemaneeleman2018_25_zijn"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (25)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Nog jaren zijn naar een oplossing gezocht."
    glossedTokens := [("Nog", "still"), ("jaren", "years"), ("zijn", "be.PL"), ("naar", "for"), ("een", "a"), ("oplossing", "solution"), ("gezocht", "searched")]
    glossedWords := [⟨['N', 'o', 'g'], ['s', 't', 'i', 'l', 'l'], [⟨['N', 'o', 'g'], ['s', 't', 'i', 'l', 'l'], none⟩]⟩, ⟨['j', 'a', 'r', 'e', 'n'], ['y', 'e', 'a', 'r', 's'], [⟨['j', 'a', 'r', 'e', 'n'], ['y', 'e', 'a', 'r', 's'], none⟩]⟩, ⟨['z', 'i', 'j', 'n'], ['b', 'e', '.', 'P', 'L'], [⟨['z', 'i', 'j', 'n'], ['b', 'e', '.', 'P', 'L'], none⟩]⟩, ⟨['n', 'a', 'a', 'r'], ['f', 'o', 'r'], [⟨['n', 'a', 'a', 'r'], ['f', 'o', 'r'], none⟩]⟩, ⟨['e', 'e', 'n'], ['a'], [⟨['e', 'e', 'n'], ['a'], none⟩]⟩, ⟨['o', 'p', 'l', 'o', 's', 's', 'i', 'n', 'g'], ['s', 'o', 'l', 'u', 't', 'i', 'o', 'n'], [⟨['o', 'p', 'l', 'o', 's', 's', 'i', 'n', 'g'], ['s', 'o', 'l', 'u', 't', 'i', 'o', 'n'], none⟩]⟩, ⟨['g', 'e', 'z', 'o', 'c', 'h', 't'], ['s', 'e', 'a', 'r', 'c', 'h', 'e', 'd'], [⟨['g', 'e', 'z', 'o', 'c', 'h', 't'], ['s', 'e', 'a', 'r', 'c', 'h', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨2, 1, "agreement", none⟩]
    paperFeatures := [("phenomenon", "default agreement")] }

def ex_30 : Datum :=
  { id := "ackemaneeleman2018_30"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (30)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Men schijnt dat men regent."
    glossedTokens := [("Men", "one"), ("schijnt", "seems"), ("dat", "that"), ("men", "one"), ("regent", "rains")]
    glossedWords := [⟨['M', 'e', 'n'], ['o', 'n', 'e'], [⟨['M', 'e', 'n'], ['o', 'n', 'e'], none⟩]⟩, ⟨['s', 'c', 'h', 'i', 'j', 'n', 't'], ['s', 'e', 'e', 'm', 's'], [⟨['s', 'c', 'h', 'i', 'j', 'n', 't'], ['s', 'e', 'e', 'm', 's'], none⟩]⟩, ⟨['d', 'a', 't'], ['t', 'h', 'a', 't'], [⟨['d', 'a', 't'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['m', 'e', 'n'], ['o', 'n', 'e'], [⟨['m', 'e', 'n'], ['o', 'n', 'e'], none⟩]⟩, ⟨['r', 'e', 'g', 'e', 'n', 't'], ['r', 'a', 'i', 'n', 's'], [⟨['r', 'e', 'g', 'e', 'n', 't'], ['r', 'a', 'i', 'n', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨0, 1, "subject", some "men"⟩, ⟨3, 1, "subject", some "men"⟩]
    paperFeatures := [("phenomenon", "expletive")] }

def all : List Datum := [ex_2a, ex_2b, ex_20a, ex_21a, ex_24a, ex_24b_i, ex_24b_you, ex_25_is, ex_25_ben, ex_25_bent, ex_25_zijn, ex_30]

/-- What the example is given to show. -/
inductive Phenomenon where
  /-- expletive: a subject pronoun with no referent -/
  | expletive
  /-- self-talk: a speaker addressing themself -/
  | selfTalk
  /-- default agreement: finite agreement with no agreeing argument -/
  | defaultAgreement
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `phenomenon`. -/
def phenomenon (e : Datum) : Option Phenomenon :=
  e.parse? "phenomenon" [("expletive", .expletive), ("self-talk", .selfTalk),
    ("default agreement", .defaultAgreement)]

/-- The labels of the spans the rows mark. -/
inductive SpanLabel where
  /-- subject: the subject pronoun under test -/
  | subject
  /-- agreement: the finite verb whose agreement is under test -/
  | agreement
  deriving DecidableEq, Repr, Fintype

/-- The label of a span, where it is a declared one. -/
def label? (p : Datum.Span) : Option SpanLabel :=
  List.lookup p.label [("subject", .subject), ("agreement", .agreement)]

/-- The subject pronouns under test. -/
inductive Lexeme where
  /-- it: English *it* -/
  | it
  /-- i: English *I* -/
  | i
  /-- you: English *you* -/
  | you
  /-- men: Dutch impersonal *men* 'one' -/
  | men
  deriving DecidableEq, Repr, Fintype

/-- The lexeme a span is a form of, where it names a declared one. -/
def lexeme? (p : Datum.Span) : Option Lexeme :=
  p.lexeme.bind (List.lookup · [("it", .it), ("i", .i), ("you", .you), ("men", .men)])

/-- The examples of chapter 2 on expletives, default agreement and self-talk. -/
inductive Example where
  | ex_2a
  | ex_2b
  | ex_20a
  | ex_21a
  | ex_24a
  | ex_24b_i
  | ex_24b_you
  | ex_25_is
  | ex_25_ben
  | ex_25_bent
  | ex_25_zijn
  | ex_30
  deriving DecidableEq, Repr, Fintype

/-- Every example of the file, in its order. -/
def Example.all : List Example :=
  [.ex_2a, .ex_2b, .ex_20a, .ex_21a, .ex_24a, .ex_24b_i, .ex_24b_you, .ex_25_is, .ex_25_ben,
    .ex_25_bent, .ex_25_zijn, .ex_30]

/-- The row of an example. -/
def Example.datum : Example → Datum
  | .ex_2a => _root_.AckemaNeeleman2018.Examples.ex_2a
  | .ex_2b => _root_.AckemaNeeleman2018.Examples.ex_2b
  | .ex_20a => _root_.AckemaNeeleman2018.Examples.ex_20a
  | .ex_21a => _root_.AckemaNeeleman2018.Examples.ex_21a
  | .ex_24a => _root_.AckemaNeeleman2018.Examples.ex_24a
  | .ex_24b_i => _root_.AckemaNeeleman2018.Examples.ex_24b_i
  | .ex_24b_you => _root_.AckemaNeeleman2018.Examples.ex_24b_you
  | .ex_25_is => _root_.AckemaNeeleman2018.Examples.ex_25_is
  | .ex_25_ben => _root_.AckemaNeeleman2018.Examples.ex_25_ben
  | .ex_25_bent => _root_.AckemaNeeleman2018.Examples.ex_25_bent
  | .ex_25_zijn => _root_.AckemaNeeleman2018.Examples.ex_25_zijn
  | .ex_30 => _root_.AckemaNeeleman2018.Examples.ex_30

theorem Example.map_datum_all :
    Example.all.map Example.datum = _root_.AckemaNeeleman2018.Examples.all := rfl

/-- The value the example records under `phenomenon`. -/
def Example.phenomenon : Example → Option Phenomenon
  | .ex_2a => some .expletive
  | .ex_2b => some .expletive
  | .ex_20a => some .selfTalk
  | .ex_21a => some .selfTalk
  | .ex_24a => some .expletive
  | .ex_24b_i => some .expletive
  | .ex_24b_you => some .expletive
  | .ex_25_is => some .defaultAgreement
  | .ex_25_ben => some .defaultAgreement
  | .ex_25_bent => some .defaultAgreement
  | .ex_25_zijn => some .defaultAgreement
  | .ex_30 => some .expletive

theorem Example.phenomenon_datum :
    ∀ x : Example, _root_.AckemaNeeleman2018.Examples.phenomenon x.datum = x.phenomenon := by
  decide +kernel

/-- The lexemes the spans of the example name, each with the span's label, in order. -/
def Example.labelledLexemes : Example → List (SpanLabel × Lexeme)
  | .ex_2a => [(.subject, .it)]
  | .ex_2b => [(.subject, .it)]
  | .ex_20a => []
  | .ex_21a => []
  | .ex_24a => [(.subject, .it)]
  | .ex_24b_i => [(.subject, .i)]
  | .ex_24b_you => [(.subject, .you)]
  | .ex_25_is => []
  | .ex_25_ben => []
  | .ex_25_bent => []
  | .ex_25_zijn => []
  | .ex_30 => [(.subject, .men), (.subject, .men)]

/-- The lexemes the spans of the example labelled `l` name, in order. -/
def Example.lexemes (x : Example) (l : SpanLabel) : List Lexeme :=
  (x.labelledLexemes.filter (·.1 = l)).map (·.2)

theorem Example.lexemes_datum : ∀ (x : Example) (l : SpanLabel),
    (x.datum.spans.filter (_root_.AckemaNeeleman2018.Examples.label? · = some l)).filterMap _root_.AckemaNeeleman2018.Examples.lexeme? =
      x.lexemes l := by
  decide +kernel

end AckemaNeeleman2018.Examples
