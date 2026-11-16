module

public import Linglib.Data.Examples.Schema

/-!
# `RamchandSvenonius2014` — typed example data

Auto-generated from `Linglib/Data/Examples/RamchandSvenonius2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace RamchandSvenonius2014.Examples`.
-/

@[expose] public section

namespace RamchandSvenonius2014.Examples

def ex_3a : Datum :=
  { id := "ramchandsvenonius2014_3a"
    source := ⟨"ramchand-svenonius-2014", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He could have been being interviewed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_3b : Datum :=
  { id := "ramchandsvenonius2014_3b"
    source := ⟨"ramchand-svenonius-2014", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is having returned."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_20a : Datum :=
  { id := "ramchandsvenonius2014_20a"
    source := ⟨"ramchand-svenonius-2014", "(20a)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Kari kan ha gått på ski."
    glossedTokens := [("Kari", "Kari"), ("kan", "can"), ("ha", "have"), ("gått", "gone"), ("på", "on"), ("ski.", "ski")]
    glossedWords := [⟨[['K', 'a', 'r', 'i']], [['K', 'a', 'r', 'i']]⟩, ⟨[['k', 'a', 'n']], [['c', 'a', 'n']]⟩, ⟨[['h', 'a']], [['h', 'a', 'v', 'e']]⟩, ⟨[['g', 'å', 't', 't']], [['g', 'o', 'n', 'e']]⟩, ⟨[['p', 'å']], [['o', 'n']]⟩, ⟨[['s', 'k', 'i']], [['s', 'k', 'i']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_20b : Datum :=
  { id := "ramchandsvenonius2014_20b"
    source := ⟨"ramchand-svenonius-2014", "(20b)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Ola må ha måket."
    glossedTokens := [("Ola", "Ola"), ("må", "must"), ("ha", "have"), ("måket.", "shoveled")]
    glossedWords := [⟨[['O', 'l', 'a']], [['O', 'l', 'a']]⟩, ⟨[['m', 'å']], [['m', 'u', 's', 't']]⟩, ⟨[['h', 'a']], [['h', 'a', 'v', 'e']]⟩, ⟨[['m', 'å', 'k', 'e', 't']], [['s', 'h', 'o', 'v', 'e', 'l', 'e', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_21a : Datum :=
  { id := "ramchandsvenonius2014_21a"
    source := ⟨"ramchand-svenonius-2014", "(21a)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Kari har kunnet gå på ski til jobb hver dag."
    glossedTokens := [("Kari", "Kari"), ("har", "has"), ("kunnet", "could.PTCPL"), ("gå", "go"), ("på", "on"), ("ski", "ski"), ("til", "to"), ("jobb", "work"), ("hver", "every"), ("dag.", "day")]
    glossedWords := [⟨[['K', 'a', 'r', 'i']], [['K', 'a', 'r', 'i']]⟩, ⟨[['h', 'a', 'r']], [['h', 'a', 's']]⟩, ⟨[['k', 'u', 'n', 'n', 'e', 't']], [['c', 'o', 'u', 'l', 'd', '.', 'P', 'T', 'C', 'P', 'L']]⟩, ⟨[['g', 'å']], [['g', 'o']]⟩, ⟨[['p', 'å']], [['o', 'n']]⟩, ⟨[['s', 'k', 'i']], [['s', 'k', 'i']]⟩, ⟨[['t', 'i', 'l']], [['t', 'o']]⟩, ⟨[['j', 'o', 'b', 'b']], [['w', 'o', 'r', 'k']]⟩, ⟨[['h', 'v', 'e', 'r']], [['e', 'v', 'e', 'r', 'y']]⟩, ⟨[['d', 'a', 'g']], [['d', 'a', 'y']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_21b : Datum :=
  { id := "ramchandsvenonius2014_21b"
    source := ⟨"ramchand-svenonius-2014", "(21b)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Ola har måttet måke sne i hele dag."
    glossedTokens := [("Ola", "Ola"), ("har", "has"), ("måttet", "must.PTCPL"), ("måke", "shovel"), ("sne", "snow"), ("i", "in"), ("hele", "whole"), ("dag.", "day")]
    glossedWords := [⟨[['O', 'l', 'a']], [['O', 'l', 'a']]⟩, ⟨[['h', 'a', 'r']], [['h', 'a', 's']]⟩, ⟨[['m', 'å', 't', 't', 'e', 't']], [['m', 'u', 's', 't', '.', 'P', 'T', 'C', 'P', 'L']]⟩, ⟨[['m', 'å', 'k', 'e']], [['s', 'h', 'o', 'v', 'e', 'l']]⟩, ⟨[['s', 'n', 'e']], [['s', 'n', 'o', 'w']]⟩, ⟨[['i']], [['i', 'n']]⟩, ⟨[['h', 'e', 'l', 'e']], [['w', 'h', 'o', 'l', 'e']]⟩, ⟨[['d', 'a', 'g']], [['d', 'a', 'y']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_23a : Datum :=
  { id := "ramchandsvenonius2014_23a"
    source := ⟨"ramchand-svenonius-2014", "(23a)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Kari har kunnet gå på ski til jobb hver dag."
    glossedTokens := [("Kari", "Kari"), ("har", "has"), ("kunnet", "could.PTCPL"), ("gå", "go"), ("på", "on"), ("ski", "ski"), ("til", "to"), ("jobb", "work"), ("hver", "every"), ("dag.", "day")]
    glossedWords := [⟨[['K', 'a', 'r', 'i']], [['K', 'a', 'r', 'i']]⟩, ⟨[['h', 'a', 'r']], [['h', 'a', 's']]⟩, ⟨[['k', 'u', 'n', 'n', 'e', 't']], [['c', 'o', 'u', 'l', 'd', '.', 'P', 'T', 'C', 'P', 'L']]⟩, ⟨[['g', 'å']], [['g', 'o']]⟩, ⟨[['p', 'å']], [['o', 'n']]⟩, ⟨[['s', 'k', 'i']], [['s', 'k', 'i']]⟩, ⟨[['t', 'i', 'l']], [['t', 'o']]⟩, ⟨[['j', 'o', 'b', 'b']], [['w', 'o', 'r', 'k']]⟩, ⟨[['h', 'v', 'e', 'r']], [['e', 'v', 'e', 'r', 'y']]⟩, ⟨[['d', 'a', 'g']], [['d', 'a', 'y']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("root", .acceptable), ("epistemic", .unacceptable)]
    paperFeatures := [] }

def ex_23b : Datum :=
  { id := "ramchandsvenonius2014_23b"
    source := ⟨"ramchand-svenonius-2014", "(23b)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Ola har måttet måke sne i hele dag."
    glossedTokens := [("Ola", "Ola"), ("har", "has"), ("måttet", "must.PTCPL"), ("måke", "shovel"), ("sne", "snow"), ("i", "in"), ("hele", "whole"), ("dag.", "day")]
    glossedWords := [⟨[['O', 'l', 'a']], [['O', 'l', 'a']]⟩, ⟨[['h', 'a', 'r']], [['h', 'a', 's']]⟩, ⟨[['m', 'å', 't', 't', 'e', 't']], [['m', 'u', 's', 't', '.', 'P', 'T', 'C', 'P', 'L']]⟩, ⟨[['m', 'å', 'k', 'e']], [['s', 'h', 'o', 'v', 'e', 'l']]⟩, ⟨[['s', 'n', 'e']], [['s', 'n', 'o', 'w']]⟩, ⟨[['i']], [['i', 'n']]⟩, ⟨[['h', 'e', 'l', 'e']], [['w', 'h', 'o', 'l', 'e']]⟩, ⟨[['d', 'a', 'g']], [['d', 'a', 'y']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("root", .acceptable), ("epistemic", .unacceptable)]
    paperFeatures := [] }

def ex_24a : Datum :=
  { id := "ramchandsvenonius2014_24a"
    source := ⟨"ramchand-svenonius-2014", "(24a)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Kari må kunne gå på ski."
    glossedTokens := [("Kari", "Kari"), ("må", "must"), ("kunne", "could.INF"), ("gå", "go"), ("på", "on"), ("ski.", "ski")]
    glossedWords := [⟨[['K', 'a', 'r', 'i']], [['K', 'a', 'r', 'i']]⟩, ⟨[['m', 'å']], [['m', 'u', 's', 't']]⟩, ⟨[['k', 'u', 'n', 'n', 'e']], [['c', 'o', 'u', 'l', 'd', '.', 'I', 'N', 'F']]⟩, ⟨[['g', 'å']], [['g', 'o']]⟩, ⟨[['p', 'å']], [['o', 'n']]⟩, ⟨[['s', 'k', 'i']], [['s', 'k', 'i']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_24b : Datum :=
  { id := "ramchandsvenonius2014_24b"
    source := ⟨"ramchand-svenonius-2014", "(24b)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Ola kan måtte måke."
    glossedTokens := [("Ola", "Ola"), ("kan", "can"), ("måtte", "must.INF"), ("måke.", "shovel")]
    glossedWords := [⟨[['O', 'l', 'a']], [['O', 'l', 'a']]⟩, ⟨[['k', 'a', 'n']], [['c', 'a', 'n']]⟩, ⟨[['m', 'å', 't', 't', 'e']], [['m', 'u', 's', 't', '.', 'I', 'N', 'F']]⟩, ⟨[['m', 'å', 'k', 'e']], [['s', 'h', 'o', 'v', 'e', 'l']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_51a : Datum :=
  { id := "ramchandsvenonius2014_51a"
    source := ⟨"ramchand-svenonius-2014", "(51a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John fortunately already knows that."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_51b : Datum :=
  { id := "ramchandsvenonius2014_51b"
    source := ⟨"ramchand-svenonius-2014", "(51b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John already fortunately knows that."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_51c : Datum :=
  { id := "ramchandsvenonius2014_51c"
    source := ⟨"ramchand-svenonius-2014", "(51c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John already quietly declined."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_51d : Datum :=
  { id := "ramchandsvenonius2014_51d"
    source := ⟨"ramchand-svenonius-2014", "(51d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John quietly already declined."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_54a : Datum :=
  { id := "ramchandsvenonius2014_54a"
    source := ⟨"ramchand-svenonius-2014", "(54a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John has been twice intentionally insulted."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_60a : Datum :=
  { id := "ramchandsvenonius2014_60a"
    source := ⟨"ramchand-svenonius-2014", "(60a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John was probably once married."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_60b : Datum :=
  { id := "ramchandsvenonius2014_60b"
    source := ⟨"ramchand-svenonius-2014", "(60b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John was once probably married."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_61 : Datum :=
  { id := "ramchandsvenonius2014_61"
    source := ⟨"ramchand-svenonius-2014", "(61)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The Rolling Stones were once probably going to play in Tromsø."
    glossedTokens := []
    context := "In 2006 a promoter in Norway seemed about to sign the Rolling Stones to play in Tromsø, until the guitarist fell out of a tree and injured his head, the tour was shortened and the negotiations were cut off."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex_3a, ex_3b, ex_20a, ex_20b, ex_21a, ex_21b, ex_23a, ex_23b, ex_24a, ex_24b, ex_51a, ex_51b, ex_51c, ex_51d, ex_54a, ex_60a, ex_60b, ex_61]

end RamchandSvenonius2014.Examples
