module

public import Linglib.Data.Examples.Schema

/-!
# `Gutzmann2015` — typed example data

Auto-generated from `Linglib/Data/Examples/Gutzmann2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Gutzmann2015.Examples`.
-/

@[expose] public section

namespace Gutzmann2015.Examples

def ex_5_34 : Datum :=
  { id := "gutzmann2015_5_34"
    source := ⟨"gutzmann-2015", "(5.34)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wann kommt Peter nach Hause?"
    glossedTokens := [("Wann", "when"), ("kommt", "comes"), ("Peter", "Peter"), ("nach", "to"), ("Hause?", "home?")]
    glossedWords := [⟨['W', 'a', 'n', 'n'], ['w', 'h', 'e', 'n'], [⟨['W', 'a', 'n', 'n'], ['w', 'h', 'e', 'n'], none⟩]⟩, ⟨['k', 'o', 'm', 'm', 't'], ['c', 'o', 'm', 'e', 's'], [⟨['k', 'o', 'm', 'm', 't'], ['c', 'o', 'm', 'e', 's'], none⟩]⟩, ⟨['P', 'e', 't', 'e', 'r'], ['P', 'e', 't', 'e', 'r'], [⟨['P', 'e', 't', 'e', 'r'], ['P', 'e', 't', 'e', 'r'], none⟩]⟩, ⟨['n', 'a', 'c', 'h'], ['t', 'o'], [⟨['n', 'a', 'c', 'h'], ['t', 'o'], none⟩]⟩, ⟨['H', 'a', 'u', 's', 'e', '?'], ['h', 'o', 'm', 'e', '?'], [⟨['H', 'a', 'u', 's', 'e'], ['h', 'o', 'm', 'e', '?'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.3"), ("phenomenon", "verbPosition"), ("sentenceType", "constituent"), ("embedding", "matrix")] }

def ex_5_35 : Datum :=
  { id := "gutzmann2015_5_35"
    source := ⟨"gutzmann-2015", "(5.35)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wann Peter nach Hause kommt?"
    glossedTokens := [("Wann", "when"), ("Peter", "Peter"), ("nach", "to"), ("Hause", "home"), ("kommt?", "comes?")]
    glossedWords := [⟨['W', 'a', 'n', 'n'], ['w', 'h', 'e', 'n'], [⟨['W', 'a', 'n', 'n'], ['w', 'h', 'e', 'n'], none⟩]⟩, ⟨['P', 'e', 't', 'e', 'r'], ['P', 'e', 't', 'e', 'r'], [⟨['P', 'e', 't', 'e', 'r'], ['P', 'e', 't', 'e', 'r'], none⟩]⟩, ⟨['n', 'a', 'c', 'h'], ['t', 'o'], [⟨['n', 'a', 'c', 'h'], ['t', 'o'], none⟩]⟩, ⟨['H', 'a', 'u', 's', 'e'], ['h', 'o', 'm', 'e'], [⟨['H', 'a', 'u', 's', 'e'], ['h', 'o', 'm', 'e'], none⟩]⟩, ⟨['k', 'o', 'm', 'm', 't', '?'], ['c', 'o', 'm', 'e', 's', '?'], [⟨['k', 'o', 'm', 'm', 't'], ['c', 'o', 'm', 'e', 's', '?'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.3"), ("phenomenon", "verbPosition"), ("sentenceType", "constituent"), ("embedding", "insubordinated")] }

def ex_5_36a : Datum :=
  { id := "gutzmann2015_5_36a"
    source := ⟨"gutzmann-2015", "(5.36a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Mag er immer noch kubanische Zigarren?"
    glossedTokens := []
    context := "Stefan: Ich hab seit Jahren nichts mehr von Peter gehört. 'I haven't heard from Peter in years.' Heiner: Ich auch nicht. 'Me neither.' Stefan continues:"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.3"), ("phenomenon", "hearerKnowledge"), ("sentenceType", "polar"), ("embedding", "matrix")] }

def ex_5_36b : Datum :=
  { id := "gutzmann2015_5_36b"
    source := ⟨"gutzmann-2015", "(5.36b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Ob er immer noch kubanische Zigarren mag?"
    glossedTokens := []
    context := "Stefan: Ich hab seit Jahren nichts mehr von Peter gehört. 'I haven't heard from Peter in years.' Heiner: Ich auch nicht. 'Me neither.' Stefan continues:"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.3"), ("phenomenon", "hearerKnowledge"), ("sentenceType", "polar"), ("embedding", "insubordinated")] }

def ex_5_44 : Datum :=
  { id := "gutzmann2015_5_44"
    source := ⟨"gutzmann-2015", "(5.44)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Dass du nicht wieder die Schlüssel vergisst!"
    glossedTokens := [("Dass", "that"), ("du", "you"), ("nicht", "not"), ("wieder", "again"), ("die", "the"), ("Schlüssel", "keys"), ("vergisst!", "forget!")]
    glossedWords := [⟨['D', 'a', 's', 's'], ['t', 'h', 'a', 't'], [⟨['D', 'a', 's', 's'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['d', 'u'], ['y', 'o', 'u'], [⟨['d', 'u'], ['y', 'o', 'u'], none⟩]⟩, ⟨['n', 'i', 'c', 'h', 't'], ['n', 'o', 't'], [⟨['n', 'i', 'c', 'h', 't'], ['n', 'o', 't'], none⟩]⟩, ⟨['w', 'i', 'e', 'd', 'e', 'r'], ['a', 'g', 'a', 'i', 'n'], [⟨['w', 'i', 'e', 'd', 'e', 'r'], ['a', 'g', 'a', 'i', 'n'], none⟩]⟩, ⟨['d', 'i', 'e'], ['t', 'h', 'e'], [⟨['d', 'i', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['S', 'c', 'h', 'l', 'ü', 's', 's', 'e', 'l'], ['k', 'e', 'y', 's'], [⟨['S', 'c', 'h', 'l', 'ü', 's', 's', 'e', 'l'], ['k', 'e', 'y', 's'], none⟩]⟩, ⟨['v', 'e', 'r', 'g', 'i', 's', 's', 't', '!'], ['f', 'o', 'r', 'g', 'e', 't', '!'], [⟨['v', 'e', 'r', 'g', 'i', 's', 's', 't'], ['f', 'o', 'r', 'g', 'e', 't', '!'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.3"), ("phenomenon", "deonticMood"), ("sentenceType", "declarative"), ("embedding", "insubordinated")] }

def ex_5_46 : Datum :=
  { id := "gutzmann2015_5_46"
    source := ⟨"gutzmann-2015", "(5.46)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Jim wohnt in Berlin."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.3"), ("phenomenon", "epistemicMood"), ("sentenceType", "declarative"), ("embedding", "matrix")] }

def ex_5_81 : Datum :=
  { id := "gutzmann2015_5_81"
    source := ⟨"gutzmann-2015", "(5.81)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Dass du nicht zu spät kommst!"
    glossedTokens := [("Dass", "that"), ("du", "you"), ("nicht", "not"), ("zu", "too"), ("spät", "late"), ("kommst!", "come!")]
    glossedWords := [⟨['D', 'a', 's', 's'], ['t', 'h', 'a', 't'], [⟨['D', 'a', 's', 's'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['d', 'u'], ['y', 'o', 'u'], [⟨['d', 'u'], ['y', 'o', 'u'], none⟩]⟩, ⟨['n', 'i', 'c', 'h', 't'], ['n', 'o', 't'], [⟨['n', 'i', 'c', 'h', 't'], ['n', 'o', 't'], none⟩]⟩, ⟨['z', 'u'], ['t', 'o', 'o'], [⟨['z', 'u'], ['t', 'o', 'o'], none⟩]⟩, ⟨['s', 'p', 'ä', 't'], ['l', 'a', 't', 'e'], [⟨['s', 'p', 'ä', 't'], ['l', 'a', 't', 'e'], none⟩]⟩, ⟨['k', 'o', 'm', 'm', 's', 't', '!'], ['c', 'o', 'm', 'e', '!'], [⟨['k', 'o', 'm', 'm', 's', 't'], ['c', 'o', 'm', 'e', '!'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.6"), ("phenomenon", "deonticMood"), ("sentenceType", "declarative"), ("embedding", "insubordinated")] }

def ex_6_20 : Datum :=
  { id := "gutzmann2015_6_20"
    source := ⟨"gutzmann-2015", "(6.20)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Anna fährt ja morgen nach Hause."
    glossedTokens := [("Anna", "Anna"), ("fährt", "drives"), ("ja", "MP"), ("morgen", "tomorrow"), ("nach", "to"), ("Hause.", "home.")]
    glossedWords := [⟨['A', 'n', 'n', 'a'], ['A', 'n', 'n', 'a'], [⟨['A', 'n', 'n', 'a'], ['A', 'n', 'n', 'a'], none⟩]⟩, ⟨['f', 'ä', 'h', 'r', 't'], ['d', 'r', 'i', 'v', 'e', 's'], [⟨['f', 'ä', 'h', 'r', 't'], ['d', 'r', 'i', 'v', 'e', 's'], none⟩]⟩, ⟨['j', 'a'], ['M', 'P'], [⟨['j', 'a'], ['M', 'P'], none⟩]⟩, ⟨['m', 'o', 'r', 'g', 'e', 'n'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['m', 'o', 'r', 'g', 'e', 'n'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩, ⟨['n', 'a', 'c', 'h'], ['t', 'o'], [⟨['n', 'a', 'c', 'h'], ['t', 'o'], none⟩]⟩, ⟨['H', 'a', 'u', 's', 'e', '.'], ['h', 'o', 'm', 'e', '.'], [⟨['H', 'a', 'u', 's', 'e'], ['h', 'o', 'm', 'e', '.'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "distribution"), ("sentenceType", "declarative"), ("embedding", "matrix"), ("particle", "ja")] }

def ex_6_21a : Datum :=
  { id := "gutzmann2015_6_21a"
    source := ⟨"gutzmann-2015", "(6.21a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Ist Peter ja gekommen?"
    glossedTokens := [("Ist", "is"), ("Peter", "Peter"), ("ja", "MP"), ("gekommen?", "come?")]
    glossedWords := [⟨['I', 's', 't'], ['i', 's'], [⟨['I', 's', 't'], ['i', 's'], none⟩]⟩, ⟨['P', 'e', 't', 'e', 'r'], ['P', 'e', 't', 'e', 'r'], [⟨['P', 'e', 't', 'e', 'r'], ['P', 'e', 't', 'e', 'r'], none⟩]⟩, ⟨['j', 'a'], ['M', 'P'], [⟨['j', 'a'], ['M', 'P'], none⟩]⟩, ⟨['g', 'e', 'k', 'o', 'm', 'm', 'e', 'n', '?'], ['c', 'o', 'm', 'e', '?'], [⟨['g', 'e', 'k', 'o', 'm', 'm', 'e', 'n'], ['c', 'o', 'm', 'e', '?'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "distribution"), ("sentenceType", "polar"), ("embedding", "matrix"), ("particle", "ja")] }

def ex_6_21b : Datum :=
  { id := "gutzmann2015_6_21b"
    source := ⟨"gutzmann-2015", "(6.21b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wer kommt ja nach Tübingen?"
    glossedTokens := [("Wer", "who"), ("kommt", "comes"), ("ja", "MP"), ("nach", "to"), ("Tübingen?", "Tübingen?")]
    glossedWords := [⟨['W', 'e', 'r'], ['w', 'h', 'o'], [⟨['W', 'e', 'r'], ['w', 'h', 'o'], none⟩]⟩, ⟨['k', 'o', 'm', 'm', 't'], ['c', 'o', 'm', 'e', 's'], [⟨['k', 'o', 'm', 'm', 't'], ['c', 'o', 'm', 'e', 's'], none⟩]⟩, ⟨['j', 'a'], ['M', 'P'], [⟨['j', 'a'], ['M', 'P'], none⟩]⟩, ⟨['n', 'a', 'c', 'h'], ['t', 'o'], [⟨['n', 'a', 'c', 'h'], ['t', 'o'], none⟩]⟩, ⟨['T', 'ü', 'b', 'i', 'n', 'g', 'e', 'n', '?'], ['T', 'ü', 'b', 'i', 'n', 'g', 'e', 'n', '?'], [⟨['T', 'ü', 'b', 'i', 'n', 'g', 'e', 'n'], ['T', 'ü', 'b', 'i', 'n', 'g', 'e', 'n', '?'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "distribution"), ("sentenceType", "constituent"), ("embedding", "matrix"), ("particle", "ja")] }

def ex_6_22a : Datum :=
  { id := "gutzmann2015_6_22a"
    source := ⟨"gutzmann-2015", "(6.22a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Geh ja nicht zum Museumsball!"
    glossedTokens := [("Geh", "go"), ("ja", "MP"), ("nicht", "not"), ("zum", "to-the"), ("Museumsball!", "museum-ball!")]
    glossedWords := [⟨['G', 'e', 'h'], ['g', 'o'], [⟨['G', 'e', 'h'], ['g', 'o'], none⟩]⟩, ⟨['j', 'a'], ['M', 'P'], [⟨['j', 'a'], ['M', 'P'], none⟩]⟩, ⟨['n', 'i', 'c', 'h', 't'], ['n', 'o', 't'], [⟨['n', 'i', 'c', 'h', 't'], ['n', 'o', 't'], none⟩]⟩, ⟨['z', 'u', 'm'], ['t', 'o', '-', 't', 'h', 'e'], []⟩, ⟨['M', 'u', 's', 'e', 'u', 'm', 's', 'b', 'a', 'l', 'l', '!'], ['m', 'u', 's', 'e', 'u', 'm', '-', 'b', 'a', 'l', 'l', '!'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "distribution"), ("sentenceType", "imperative"), ("embedding", "matrix"), ("particle", "ja")] }

def ex_6_22b : Datum :=
  { id := "gutzmann2015_6_22b"
    source := ⟨"gutzmann-2015", "(6.22b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Dass du ja nicht dein ganzes Geld ausgibst!"
    glossedTokens := [("Dass", "that"), ("du", "you"), ("ja", "MP"), ("nicht", "not"), ("dein", "your"), ("ganzes", "entire"), ("Geld", "money"), ("ausgibst!", "spend!")]
    glossedWords := [⟨['D', 'a', 's', 's'], ['t', 'h', 'a', 't'], [⟨['D', 'a', 's', 's'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['d', 'u'], ['y', 'o', 'u'], [⟨['d', 'u'], ['y', 'o', 'u'], none⟩]⟩, ⟨['j', 'a'], ['M', 'P'], [⟨['j', 'a'], ['M', 'P'], none⟩]⟩, ⟨['n', 'i', 'c', 'h', 't'], ['n', 'o', 't'], [⟨['n', 'i', 'c', 'h', 't'], ['n', 'o', 't'], none⟩]⟩, ⟨['d', 'e', 'i', 'n'], ['y', 'o', 'u', 'r'], [⟨['d', 'e', 'i', 'n'], ['y', 'o', 'u', 'r'], none⟩]⟩, ⟨['g', 'a', 'n', 'z', 'e', 's'], ['e', 'n', 't', 'i', 'r', 'e'], [⟨['g', 'a', 'n', 'z', 'e', 's'], ['e', 'n', 't', 'i', 'r', 'e'], none⟩]⟩, ⟨['G', 'e', 'l', 'd'], ['m', 'o', 'n', 'e', 'y'], [⟨['G', 'e', 'l', 'd'], ['m', 'o', 'n', 'e', 'y'], none⟩]⟩, ⟨['a', 'u', 's', 'g', 'i', 'b', 's', 't', '!'], ['s', 'p', 'e', 'n', 'd', '!'], [⟨['a', 'u', 's', 'g', 'i', 'b', 's', 't'], ['s', 'p', 'e', 'n', 'd', '!'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "distribution"), ("sentenceType", "declarative"), ("embedding", "insubordinated"), ("particle", "ja")] }

def ex_6_26 : Datum :=
  { id := "gutzmann2015_6_26"
    source := ⟨"gutzmann-2015", "(6.26)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Du kommst ja morgen um zehn?"
    glossedTokens := [("Du", "you"), ("kommst", "come"), ("ja", "MP"), ("morgen", "tomorrow"), ("um", "at"), ("zehn?", "ten?")]
    glossedWords := [⟨['D', 'u'], ['y', 'o', 'u'], [⟨['D', 'u'], ['y', 'o', 'u'], none⟩]⟩, ⟨['k', 'o', 'm', 'm', 's', 't'], ['c', 'o', 'm', 'e'], [⟨['k', 'o', 'm', 'm', 's', 't'], ['c', 'o', 'm', 'e'], none⟩]⟩, ⟨['j', 'a'], ['M', 'P'], [⟨['j', 'a'], ['M', 'P'], none⟩]⟩, ⟨['m', 'o', 'r', 'g', 'e', 'n'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['m', 'o', 'r', 'g', 'e', 'n'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩, ⟨['u', 'm'], ['a', 't'], [⟨['u', 'm'], ['a', 't'], none⟩]⟩, ⟨['z', 'e', 'h', 'n', '?'], ['t', 'e', 'n', '?'], [⟨['z', 'e', 'h', 'n'], ['t', 'e', 'n', '?'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "checkQuestion"), ("sentenceType", "declarative"), ("embedding", "matrix"), ("particle", "ja")] }

def ex_6_27 : Datum :=
  { id := "gutzmann2015_6_27"
    source := ⟨"gutzmann-2015", "(6.27)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wer will das Spiel ja nicht gewinnen?"
    glossedTokens := [("Wer", "who"), ("will", "want"), ("das", "the"), ("Spiel", "game"), ("ja", "MP"), ("nicht", "not"), ("gewinnen?", "win?")]
    glossedWords := [⟨['W', 'e', 'r'], ['w', 'h', 'o'], [⟨['W', 'e', 'r'], ['w', 'h', 'o'], none⟩]⟩, ⟨['w', 'i', 'l', 'l'], ['w', 'a', 'n', 't'], [⟨['w', 'i', 'l', 'l'], ['w', 'a', 'n', 't'], none⟩]⟩, ⟨['d', 'a', 's'], ['t', 'h', 'e'], [⟨['d', 'a', 's'], ['t', 'h', 'e'], none⟩]⟩, ⟨['S', 'p', 'i', 'e', 'l'], ['g', 'a', 'm', 'e'], [⟨['S', 'p', 'i', 'e', 'l'], ['g', 'a', 'm', 'e'], none⟩]⟩, ⟨['j', 'a'], ['M', 'P'], [⟨['j', 'a'], ['M', 'P'], none⟩]⟩, ⟨['n', 'i', 'c', 'h', 't'], ['n', 'o', 't'], [⟨['n', 'i', 'c', 'h', 't'], ['n', 'o', 't'], none⟩]⟩, ⟨['g', 'e', 'w', 'i', 'n', 'n', 'e', 'n', '?'], ['w', 'i', 'n', '?'], [⟨['g', 'e', 'w', 'i', 'n', 'n', 'e', 'n'], ['w', 'i', 'n', '?'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "rhetoricalQuestion"), ("sentenceType", "constituent"), ("embedding", "matrix"), ("particle", "ja")] }

def ex_6_28a : Datum :=
  { id := "gutzmann2015_6_28a"
    source := ⟨"gutzmann-2015", "(6.28a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Hast du denn ein Auto?"
    glossedTokens := [("Hast", "have"), ("du", "you"), ("denn", "MP"), ("ein", "a"), ("Auto?", "car?")]
    glossedWords := [⟨['H', 'a', 's', 't'], ['h', 'a', 'v', 'e'], [⟨['H', 'a', 's', 't'], ['h', 'a', 'v', 'e'], none⟩]⟩, ⟨['d', 'u'], ['y', 'o', 'u'], [⟨['d', 'u'], ['y', 'o', 'u'], none⟩]⟩, ⟨['d', 'e', 'n', 'n'], ['M', 'P'], [⟨['d', 'e', 'n', 'n'], ['M', 'P'], none⟩]⟩, ⟨['e', 'i', 'n'], ['a'], [⟨['e', 'i', 'n'], ['a'], none⟩]⟩, ⟨['A', 'u', 't', 'o', '?'], ['c', 'a', 'r', '?'], [⟨['A', 'u', 't', 'o'], ['c', 'a', 'r', '?'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "distribution"), ("sentenceType", "polar"), ("embedding", "matrix"), ("particle", "denn")] }

def ex_6_28b : Datum :=
  { id := "gutzmann2015_6_28b"
    source := ⟨"gutzmann-2015", "(6.28b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Warum lachst du denn?"
    glossedTokens := [("Warum", "why"), ("lachst", "laugh"), ("du", "you"), ("denn?", "MP?")]
    glossedWords := [⟨['W', 'a', 'r', 'u', 'm'], ['w', 'h', 'y'], [⟨['W', 'a', 'r', 'u', 'm'], ['w', 'h', 'y'], none⟩]⟩, ⟨['l', 'a', 'c', 'h', 's', 't'], ['l', 'a', 'u', 'g', 'h'], [⟨['l', 'a', 'c', 'h', 's', 't'], ['l', 'a', 'u', 'g', 'h'], none⟩]⟩, ⟨['d', 'u'], ['y', 'o', 'u'], [⟨['d', 'u'], ['y', 'o', 'u'], none⟩]⟩, ⟨['d', 'e', 'n', 'n', '?'], ['M', 'P', '?'], [⟨['d', 'e', 'n', 'n'], ['M', 'P', '?'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "distribution"), ("sentenceType", "constituent"), ("embedding", "matrix"), ("particle", "denn")] }

def ex_6_29 : Datum :=
  { id := "gutzmann2015_6_29"
    source := ⟨"gutzmann-2015", "(6.29)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Peter ist denn ein Philosoph."
    glossedTokens := [("Peter", "Peter"), ("ist", "is"), ("denn", "MP"), ("ein", "a"), ("Philosoph.", "philosopher.")]
    glossedWords := [⟨['P', 'e', 't', 'e', 'r'], ['P', 'e', 't', 'e', 'r'], [⟨['P', 'e', 't', 'e', 'r'], ['P', 'e', 't', 'e', 'r'], none⟩]⟩, ⟨['i', 's', 't'], ['i', 's'], [⟨['i', 's', 't'], ['i', 's'], none⟩]⟩, ⟨['d', 'e', 'n', 'n'], ['M', 'P'], [⟨['d', 'e', 'n', 'n'], ['M', 'P'], none⟩]⟩, ⟨['e', 'i', 'n'], ['a'], [⟨['e', 'i', 'n'], ['a'], none⟩]⟩, ⟨['P', 'h', 'i', 'l', 'o', 's', 'o', 'p', 'h', '.'], ['p', 'h', 'i', 'l', 'o', 's', 'o', 'p', 'h', 'e', 'r', '.'], [⟨['P', 'h', 'i', 'l', 'o', 's', 'o', 'p', 'h'], ['p', 'h', 'i', 'l', 'o', 's', 'o', 'p', 'h', 'e', 'r', '.'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "distribution"), ("sentenceType", "declarative"), ("embedding", "matrix"), ("particle", "denn")] }

def ex_6_30 : Datum :=
  { id := "gutzmann2015_6_30"
    source := ⟨"gutzmann-2015", "(6.30)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Lass mich denn nicht alleine!"
    glossedTokens := [("Lass", "let"), ("mich", "me"), ("denn", "MP"), ("nicht", "not"), ("alleine!", "alone!")]
    glossedWords := [⟨['L', 'a', 's', 's'], ['l', 'e', 't'], [⟨['L', 'a', 's', 's'], ['l', 'e', 't'], none⟩]⟩, ⟨['m', 'i', 'c', 'h'], ['m', 'e'], [⟨['m', 'i', 'c', 'h'], ['m', 'e'], none⟩]⟩, ⟨['d', 'e', 'n', 'n'], ['M', 'P'], [⟨['d', 'e', 'n', 'n'], ['M', 'P'], none⟩]⟩, ⟨['n', 'i', 'c', 'h', 't'], ['n', 'o', 't'], [⟨['n', 'i', 'c', 'h', 't'], ['n', 'o', 't'], none⟩]⟩, ⟨['a', 'l', 'l', 'e', 'i', 'n', 'e', '!'], ['a', 'l', 'o', 'n', 'e', '!'], [⟨['a', 'l', 'l', 'e', 'i', 'n', 'e'], ['a', 'l', 'o', 'n', 'e', '!'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "distribution"), ("sentenceType", "imperative"), ("embedding", "matrix"), ("particle", "denn")] }

def ex_6_31 : Datum :=
  { id := "gutzmann2015_6_31"
    source := ⟨"gutzmann-2015", "(6.31)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Dass du denn pünktlich nach Hause kommst!"
    glossedTokens := [("Dass", "that"), ("du", "you"), ("denn", "MP"), ("pünktlich", "on-time"), ("nach", "to"), ("Hause", "home"), ("kommst!", "come!")]
    glossedWords := [⟨['D', 'a', 's', 's'], ['t', 'h', 'a', 't'], [⟨['D', 'a', 's', 's'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['d', 'u'], ['y', 'o', 'u'], [⟨['d', 'u'], ['y', 'o', 'u'], none⟩]⟩, ⟨['d', 'e', 'n', 'n'], ['M', 'P'], [⟨['d', 'e', 'n', 'n'], ['M', 'P'], none⟩]⟩, ⟨['p', 'ü', 'n', 'k', 't', 'l', 'i', 'c', 'h'], ['o', 'n', '-', 't', 'i', 'm', 'e'], []⟩, ⟨['n', 'a', 'c', 'h'], ['t', 'o'], [⟨['n', 'a', 'c', 'h'], ['t', 'o'], none⟩]⟩, ⟨['H', 'a', 'u', 's', 'e'], ['h', 'o', 'm', 'e'], [⟨['H', 'a', 'u', 's', 'e'], ['h', 'o', 'm', 'e'], none⟩]⟩, ⟨['k', 'o', 'm', 'm', 's', 't', '!'], ['c', 'o', 'm', 'e', '!'], [⟨['k', 'o', 'm', 'm', 's', 't'], ['c', 'o', 'm', 'e', '!'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "distribution"), ("sentenceType", "declarative"), ("embedding", "insubordinated"), ("particle", "denn")] }

def ex_6_32 : Datum :=
  { id := "gutzmann2015_6_32"
    source := ⟨"gutzmann-2015", "(6.32)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Du kommst denn morgen um zehn?"
    glossedTokens := [("Du", "you"), ("kommst", "come"), ("denn", "MP"), ("morgen", "tomorrow"), ("um", "at"), ("zehn?", "ten?")]
    glossedWords := [⟨['D', 'u'], ['y', 'o', 'u'], [⟨['D', 'u'], ['y', 'o', 'u'], none⟩]⟩, ⟨['k', 'o', 'm', 'm', 's', 't'], ['c', 'o', 'm', 'e'], [⟨['k', 'o', 'm', 'm', 's', 't'], ['c', 'o', 'm', 'e'], none⟩]⟩, ⟨['d', 'e', 'n', 'n'], ['M', 'P'], [⟨['d', 'e', 'n', 'n'], ['M', 'P'], none⟩]⟩, ⟨['m', 'o', 'r', 'g', 'e', 'n'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['m', 'o', 'r', 'g', 'e', 'n'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩, ⟨['u', 'm'], ['a', 't'], [⟨['u', 'm'], ['a', 't'], none⟩]⟩, ⟨['z', 'e', 'h', 'n', '?'], ['t', 'e', 'n', '?'], [⟨['z', 'e', 'h', 'n'], ['t', 'e', 'n', '?'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "checkQuestion"), ("sentenceType", "declarative"), ("embedding", "matrix"), ("particle", "denn")] }

def ex_6_33 : Datum :=
  { id := "gutzmann2015_6_33"
    source := ⟨"gutzmann-2015", "(6.33)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wer will das Spiel denn nicht gewinnen?"
    glossedTokens := [("Wer", "who"), ("will", "want"), ("das", "the"), ("Spiel", "game"), ("denn", "MP"), ("nicht", "not"), ("gewinnen?", "win?")]
    glossedWords := [⟨['W', 'e', 'r'], ['w', 'h', 'o'], [⟨['W', 'e', 'r'], ['w', 'h', 'o'], none⟩]⟩, ⟨['w', 'i', 'l', 'l'], ['w', 'a', 'n', 't'], [⟨['w', 'i', 'l', 'l'], ['w', 'a', 'n', 't'], none⟩]⟩, ⟨['d', 'a', 's'], ['t', 'h', 'e'], [⟨['d', 'a', 's'], ['t', 'h', 'e'], none⟩]⟩, ⟨['S', 'p', 'i', 'e', 'l'], ['g', 'a', 'm', 'e'], [⟨['S', 'p', 'i', 'e', 'l'], ['g', 'a', 'm', 'e'], none⟩]⟩, ⟨['d', 'e', 'n', 'n'], ['M', 'P'], [⟨['d', 'e', 'n', 'n'], ['M', 'P'], none⟩]⟩, ⟨['n', 'i', 'c', 'h', 't'], ['n', 'o', 't'], [⟨['n', 'i', 'c', 'h', 't'], ['n', 'o', 't'], none⟩]⟩, ⟨['g', 'e', 'w', 'i', 'n', 'n', 'e', 'n', '?'], ['w', 'i', 'n', '?'], [⟨['g', 'e', 'w', 'i', 'n', 'n', 'e', 'n'], ['w', 'i', 'n', '?'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "rhetoricalQuestion"), ("sentenceType", "constituent"), ("embedding", "matrix"), ("particle", "denn")] }

def ex_6_35 : Datum :=
  { id := "gutzmann2015_6_35"
    source := ⟨"gutzmann-2015", "(6.35)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Hein ist wohl auf See."
    glossedTokens := [("Hein", "Hein"), ("ist", "is"), ("wohl", "MP"), ("auf", "at"), ("See.", "sea.")]
    glossedWords := [⟨['H', 'e', 'i', 'n'], ['H', 'e', 'i', 'n'], [⟨['H', 'e', 'i', 'n'], ['H', 'e', 'i', 'n'], none⟩]⟩, ⟨['i', 's', 't'], ['i', 's'], [⟨['i', 's', 't'], ['i', 's'], none⟩]⟩, ⟨['w', 'o', 'h', 'l'], ['M', 'P'], [⟨['w', 'o', 'h', 'l'], ['M', 'P'], none⟩]⟩, ⟨['a', 'u', 'f'], ['a', 't'], [⟨['a', 'u', 'f'], ['a', 't'], none⟩]⟩, ⟨['S', 'e', 'e', '.'], ['s', 'e', 'a', '.'], [⟨['S', 'e', 'e'], ['s', 'e', 'a', '.'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "distribution"), ("sentenceType", "declarative"), ("embedding", "matrix"), ("particle", "wohl")] }

def ex_6_36 : Datum :=
  { id := "gutzmann2015_6_36"
    source := ⟨"gutzmann-2015", "(6.36)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Ist Hein wohl auf See?"
    glossedTokens := [("Ist", "is"), ("Hein", "Hein"), ("wohl", "MP"), ("auf", "at"), ("See?", "sea?")]
    glossedWords := [⟨['I', 's', 't'], ['i', 's'], [⟨['I', 's', 't'], ['i', 's'], none⟩]⟩, ⟨['H', 'e', 'i', 'n'], ['H', 'e', 'i', 'n'], [⟨['H', 'e', 'i', 'n'], ['H', 'e', 'i', 'n'], none⟩]⟩, ⟨['w', 'o', 'h', 'l'], ['M', 'P'], [⟨['w', 'o', 'h', 'l'], ['M', 'P'], none⟩]⟩, ⟨['a', 'u', 'f'], ['a', 't'], [⟨['a', 'u', 'f'], ['a', 't'], none⟩]⟩, ⟨['S', 'e', 'e', '?'], ['s', 'e', 'a', '?'], [⟨['S', 'e', 'e'], ['s', 'e', 'a', '?'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "distribution"), ("sentenceType", "polar"), ("embedding", "matrix"), ("particle", "wohl")] }

def ex_6_37a : Datum :=
  { id := "gutzmann2015_6_37a"
    source := ⟨"gutzmann-2015", "(6.37a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Komm wohl pünktlich nach Hause!"
    glossedTokens := [("Komm", "come"), ("wohl", "MP"), ("pünktlich", "on-time"), ("nach", "to"), ("Hause!", "home!")]
    glossedWords := [⟨['K', 'o', 'm', 'm'], ['c', 'o', 'm', 'e'], [⟨['K', 'o', 'm', 'm'], ['c', 'o', 'm', 'e'], none⟩]⟩, ⟨['w', 'o', 'h', 'l'], ['M', 'P'], [⟨['w', 'o', 'h', 'l'], ['M', 'P'], none⟩]⟩, ⟨['p', 'ü', 'n', 'k', 't', 'l', 'i', 'c', 'h'], ['o', 'n', '-', 't', 'i', 'm', 'e'], []⟩, ⟨['n', 'a', 'c', 'h'], ['t', 'o'], [⟨['n', 'a', 'c', 'h'], ['t', 'o'], none⟩]⟩, ⟨['H', 'a', 'u', 's', 'e', '!'], ['h', 'o', 'm', 'e', '!'], [⟨['H', 'a', 'u', 's', 'e'], ['h', 'o', 'm', 'e', '!'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "distribution"), ("sentenceType", "imperative"), ("embedding", "matrix"), ("particle", "wohl")] }

def ex_6_37b : Datum :=
  { id := "gutzmann2015_6_37b"
    source := ⟨"gutzmann-2015", "(6.37b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Dass du wohl pünktlich nach Hause kommst!"
    glossedTokens := [("Dass", "that"), ("du", "you"), ("wohl", "MP"), ("pünktlich", "on-time"), ("nach", "to"), ("Hause", "home"), ("kommst!", "come!")]
    glossedWords := [⟨['D', 'a', 's', 's'], ['t', 'h', 'a', 't'], [⟨['D', 'a', 's', 's'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['d', 'u'], ['y', 'o', 'u'], [⟨['d', 'u'], ['y', 'o', 'u'], none⟩]⟩, ⟨['w', 'o', 'h', 'l'], ['M', 'P'], [⟨['w', 'o', 'h', 'l'], ['M', 'P'], none⟩]⟩, ⟨['p', 'ü', 'n', 'k', 't', 'l', 'i', 'c', 'h'], ['o', 'n', '-', 't', 'i', 'm', 'e'], []⟩, ⟨['n', 'a', 'c', 'h'], ['t', 'o'], [⟨['n', 'a', 'c', 'h'], ['t', 'o'], none⟩]⟩, ⟨['H', 'a', 'u', 's', 'e'], ['h', 'o', 'm', 'e'], [⟨['H', 'a', 'u', 's', 'e'], ['h', 'o', 'm', 'e'], none⟩]⟩, ⟨['k', 'o', 'm', 'm', 's', 't', '!'], ['c', 'o', 'm', 'e', '!'], [⟨['k', 'o', 'm', 'm', 's', 't'], ['c', 'o', 'm', 'e', '!'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "distribution"), ("sentenceType", "declarative"), ("embedding", "insubordinated"), ("particle", "wohl")] }

def ex_6_38 : Datum :=
  { id := "gutzmann2015_6_38"
    source := ⟨"gutzmann-2015", "(6.38)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Bist du wohl still?"
    glossedTokens := [("Bist", "are"), ("du", "you"), ("wohl", "MP"), ("still?", "quiet?")]
    glossedWords := [⟨['B', 'i', 's', 't'], ['a', 'r', 'e'], [⟨['B', 'i', 's', 't'], ['a', 'r', 'e'], none⟩]⟩, ⟨['d', 'u'], ['y', 'o', 'u'], [⟨['d', 'u'], ['y', 'o', 'u'], none⟩]⟩, ⟨['w', 'o', 'h', 'l'], ['M', 'P'], [⟨['w', 'o', 'h', 'l'], ['M', 'P'], none⟩]⟩, ⟨['s', 't', 'i', 'l', 'l', '?'], ['q', 'u', 'i', 'e', 't', '?'], [⟨['s', 't', 'i', 'l', 'l'], ['q', 'u', 'i', 'e', 't', '?'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "indirectRequest"), ("sentenceType", "polar"), ("embedding", "matrix"), ("particle", "wohl")] }

def ex_6_39 : Datum :=
  { id := "gutzmann2015_6_39"
    source := ⟨"gutzmann-2015", "(6.39)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Könnst du mir wohl das Salz reichen?"
    glossedTokens := [("Könnst", "could"), ("du", "you"), ("mir", "me"), ("wohl", "MP"), ("das", "the"), ("Salz", "salt"), ("reichen?", "pass?")]
    glossedWords := [⟨['K', 'ö', 'n', 'n', 's', 't'], ['c', 'o', 'u', 'l', 'd'], [⟨['K', 'ö', 'n', 'n', 's', 't'], ['c', 'o', 'u', 'l', 'd'], none⟩]⟩, ⟨['d', 'u'], ['y', 'o', 'u'], [⟨['d', 'u'], ['y', 'o', 'u'], none⟩]⟩, ⟨['m', 'i', 'r'], ['m', 'e'], [⟨['m', 'i', 'r'], ['m', 'e'], none⟩]⟩, ⟨['w', 'o', 'h', 'l'], ['M', 'P'], [⟨['w', 'o', 'h', 'l'], ['M', 'P'], none⟩]⟩, ⟨['d', 'a', 's'], ['t', 'h', 'e'], [⟨['d', 'a', 's'], ['t', 'h', 'e'], none⟩]⟩, ⟨['S', 'a', 'l', 'z'], ['s', 'a', 'l', 't'], [⟨['S', 'a', 'l', 'z'], ['s', 'a', 'l', 't'], none⟩]⟩, ⟨['r', 'e', 'i', 'c', 'h', 'e', 'n', '?'], ['p', 'a', 's', 's', '?'], [⟨['r', 'e', 'i', 'c', 'h', 'e', 'n'], ['p', 'a', 's', 's', '?'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "indirectRequest"), ("sentenceType", "polar"), ("embedding", "matrix"), ("particle", "wohl")] }

def ex_6_41 : Datum :=
  { id := "gutzmann2015_6_41"
    source := ⟨"gutzmann-2015", "(6.41)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Zeigen Sie mir wohl den Journalisten, der Gehaltseinbußen hinnimmt, um einem der vielen hundert Bewerber den Weg in eine Redaktion zu ebnen."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.2.3"), ("phenomenon", "rhetoricalRequest"), ("sentenceType", "imperative"), ("embedding", "matrix"), ("particle", "wohl")] }

def ex_6_108 : Datum :=
  { id := "gutzmann2015_6_108"
    source := ⟨"gutzmann-2015", "(6.108)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Geh wohl weg!"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.5.1"), ("phenomenon", "typeMismatch"), ("sentenceType", "imperative"), ("embedding", "matrix"), ("particle", "wohl")] }

def ex_6_117 : Datum :=
  { id := "gutzmann2015_6_117"
    source := ⟨"gutzmann-2015", "(6.117)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Peter ist wohl ein Philosoph."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.5.1"), ("phenomenon", "useConditions"), ("sentenceType", "declarative"), ("embedding", "matrix"), ("particle", "wohl")] }

def ex_6_124 : Datum :=
  { id := "gutzmann2015_6_124"
    source := ⟨"gutzmann-2015", "(6.124)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Georg ist ja ein Philosoph."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.5.2"), ("phenomenon", "useConditions"), ("sentenceType", "declarative"), ("embedding", "matrix"), ("particle", "ja")] }

def ex_6_128 : Datum :=
  { id := "gutzmann2015_6_128"
    source := ⟨"gutzmann-2015", "(6.128)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Ist Peter ja ein Philosoph?"
    glossedTokens := [("Ist", "is"), ("Peter", "Peter"), ("ja", "MP"), ("ein", "a"), ("Philosoph?", "philosopher?")]
    glossedWords := [⟨['I', 's', 't'], ['i', 's'], [⟨['I', 's', 't'], ['i', 's'], none⟩]⟩, ⟨['P', 'e', 't', 'e', 'r'], ['P', 'e', 't', 'e', 'r'], [⟨['P', 'e', 't', 'e', 'r'], ['P', 'e', 't', 'e', 'r'], none⟩]⟩, ⟨['j', 'a'], ['M', 'P'], [⟨['j', 'a'], ['M', 'P'], none⟩]⟩, ⟨['e', 'i', 'n'], ['a'], [⟨['e', 'i', 'n'], ['a'], none⟩]⟩, ⟨['P', 'h', 'i', 'l', 'o', 's', 'o', 'p', 'h', '?'], ['p', 'h', 'i', 'l', 'o', 's', 'o', 'p', 'h', 'e', 'r', '?'], [⟨['P', 'h', 'i', 'l', 'o', 's', 'o', 'p', 'h'], ['p', 'h', 'i', 'l', 'o', 's', 'o', 'p', 'h', 'e', 'r', '?'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.5.2"), ("phenomenon", "useConditions"), ("sentenceType", "polar"), ("embedding", "matrix"), ("particle", "ja")] }

def ex_6_134 : Datum :=
  { id := "gutzmann2015_6_134"
    source := ⟨"gutzmann-2015", "(6.134)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Hast du denn einen Führerschein?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.5.2"), ("phenomenon", "useConditions"), ("sentenceType", "polar"), ("embedding", "matrix"), ("particle", "denn")] }

def ex_6_138 : Datum :=
  { id := "gutzmann2015_6_138"
    source := ⟨"gutzmann-2015", "(6.138)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Entschuldigung, könnten Sie mir denn sagen, wo's hier nach Klein-Heubach geht?"
    glossedTokens := [("Entschuldigung,", "excuse"), ("könnten", "could"), ("Sie", "you"), ("mir", "me"), ("denn", "MP"), ("sagen,", "say"), ("wo's", "where-it"), ("hier", "here"), ("nach", "to"), ("Klein-Heubach", "Klein-Heubach"), ("geht?", "goes?")]
    glossedWords := [⟨['E', 'n', 't', 's', 'c', 'h', 'u', 'l', 'd', 'i', 'g', 'u', 'n', 'g', ','], ['e', 'x', 'c', 'u', 's', 'e'], [⟨['E', 'n', 't', 's', 'c', 'h', 'u', 'l', 'd', 'i', 'g', 'u', 'n', 'g'], ['e', 'x', 'c', 'u', 's', 'e'], none⟩]⟩, ⟨['k', 'ö', 'n', 'n', 't', 'e', 'n'], ['c', 'o', 'u', 'l', 'd'], [⟨['k', 'ö', 'n', 'n', 't', 'e', 'n'], ['c', 'o', 'u', 'l', 'd'], none⟩]⟩, ⟨['S', 'i', 'e'], ['y', 'o', 'u'], [⟨['S', 'i', 'e'], ['y', 'o', 'u'], none⟩]⟩, ⟨['m', 'i', 'r'], ['m', 'e'], [⟨['m', 'i', 'r'], ['m', 'e'], none⟩]⟩, ⟨['d', 'e', 'n', 'n'], ['M', 'P'], [⟨['d', 'e', 'n', 'n'], ['M', 'P'], none⟩]⟩, ⟨['s', 'a', 'g', 'e', 'n', ','], ['s', 'a', 'y'], [⟨['s', 'a', 'g', 'e', 'n'], ['s', 'a', 'y'], none⟩]⟩, ⟨['w', 'o', '\'', 's'], ['w', 'h', 'e', 'r', 'e', '-', 'i', 't'], []⟩, ⟨['h', 'i', 'e', 'r'], ['h', 'e', 'r', 'e'], [⟨['h', 'i', 'e', 'r'], ['h', 'e', 'r', 'e'], none⟩]⟩, ⟨['n', 'a', 'c', 'h'], ['t', 'o'], [⟨['n', 'a', 'c', 'h'], ['t', 'o'], none⟩]⟩, ⟨['K', 'l', 'e', 'i', 'n', '-', 'H', 'e', 'u', 'b', 'a', 'c', 'h'], ['K', 'l', 'e', 'i', 'n', '-', 'H', 'e', 'u', 'b', 'a', 'c', 'h'], [⟨['K', 'l', 'e', 'i', 'n'], ['K', 'l', 'e', 'i', 'n'], none⟩, ⟨['H', 'e', 'u', 'b', 'a', 'c', 'h'], ['H', 'e', 'u', 'b', 'a', 'c', 'h'], some '-'⟩]⟩, ⟨['g', 'e', 'h', 't', '?'], ['g', 'o', 'e', 's', '?'], [⟨['g', 'e', 'h', 't'], ['g', 'o', 'e', 's', '?'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.5.2"), ("phenomenon", "externalMotivation"), ("sentenceType", "polar"), ("embedding", "matrix"), ("particle", "denn")] }

def ex_6_139 : Datum :=
  { id := "gutzmann2015_6_139"
    source := ⟨"gutzmann-2015", "(6.139)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was schreibst du denn da?"
    glossedTokens := [("Was", "what"), ("schreibst", "write"), ("du", "you"), ("denn", "MP"), ("da?", "there?")]
    glossedWords := [⟨['W', 'a', 's'], ['w', 'h', 'a', 't'], [⟨['W', 'a', 's'], ['w', 'h', 'a', 't'], none⟩]⟩, ⟨['s', 'c', 'h', 'r', 'e', 'i', 'b', 's', 't'], ['w', 'r', 'i', 't', 'e'], [⟨['s', 'c', 'h', 'r', 'e', 'i', 'b', 's', 't'], ['w', 'r', 'i', 't', 'e'], none⟩]⟩, ⟨['d', 'u'], ['y', 'o', 'u'], [⟨['d', 'u'], ['y', 'o', 'u'], none⟩]⟩, ⟨['d', 'e', 'n', 'n'], ['M', 'P'], [⟨['d', 'e', 'n', 'n'], ['M', 'P'], none⟩]⟩, ⟨['d', 'a', '?'], ['t', 'h', 'e', 'r', 'e', '?'], [⟨['d', 'a'], ['t', 'h', 'e', 'r', 'e', '?'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.5.2"), ("phenomenon", "externalMotivation"), ("sentenceType", "constituent"), ("embedding", "matrix"), ("particle", "denn")] }

def ex_6_141 : Datum :=
  { id := "gutzmann2015_6_141"
    source := ⟨"gutzmann-2015", "(6.141)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Geh denn weg!"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.5.2"), ("phenomenon", "useConditions"), ("sentenceType", "imperative"), ("embedding", "matrix"), ("particle", "denn")] }

def all : List Datum := [ex_5_34, ex_5_35, ex_5_36a, ex_5_36b, ex_5_44, ex_5_46, ex_5_81, ex_6_20, ex_6_21a, ex_6_21b, ex_6_22a, ex_6_22b, ex_6_26, ex_6_27, ex_6_28a, ex_6_28b, ex_6_29, ex_6_30, ex_6_31, ex_6_32, ex_6_33, ex_6_35, ex_6_36, ex_6_37a, ex_6_37b, ex_6_38, ex_6_39, ex_6_41, ex_6_108, ex_6_117, ex_6_124, ex_6_128, ex_6_134, ex_6_138, ex_6_139, ex_6_141]

end Gutzmann2015.Examples
