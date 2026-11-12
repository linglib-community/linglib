module

public import Linglib.Data.Examples.Schema

/-!
# `DalrympleEtAl1998` — typed example data

Auto-generated from `Linglib/Data/Examples/DalrympleEtAl1998.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace DalrympleEtAl1998.Examples`.
-/

@[expose] public section

namespace DalrympleEtAl1998.Examples

def ex95 : Datum :=
  { id := "dalrympleetal1998_ex95"
    source := ⟨"dalrymple-et-al-1998", "(95), (2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "House of Commons legislators refer to each other indirectly."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1")] }

def ex96 : Datum :=
  { id := "dalrympleetal1998_ex96"
    source := ⟨"dalrymple-et-al-1998", "(96), (4)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "As the preposterous horde crowded around, waiting for the likes of Evans and Mike Greenwell, five Boston pitchers sat alongside each other: Larry Andersen, Jeff Reardon, Jeff Gray, Dennis Lamp and Tom Bolton."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1")] }

def ex98 : Datum :=
  { id := "dalrympleetal1998_ex98"
    source := ⟨"dalrymple-et-al-1998", "(98), (8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The third-grade students in Mrs. Smith's class gave each other measles."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1")] }

def ex108 : Datum :=
  { id := "dalrympleetal1998_ex108"
    source := ⟨"dalrymple-et-al-1998", "(108)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Their bunk beds are on top of one another."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.3")] }

def ex109 : Datum :=
  { id := "dalrympleetal1998_ex109"
    source := ⟨"dalrymple-et-al-1998", "(109)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John and Bill are taller than each other."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.3")] }

def ex110 : Datum :=
  { id := "dalrympleetal1998_ex110"
    source := ⟨"dalrymple-et-al-1998", "(110), (6), (43)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "\"The captain!\" said the pirates, staring at each other in surprise."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.3")] }

def all : List Datum := [ex95, ex96, ex98, ex108, ex109, ex110]

end DalrympleEtAl1998.Examples
