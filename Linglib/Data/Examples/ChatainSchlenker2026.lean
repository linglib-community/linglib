module

public import Linglib.Data.Examples.Schema

/-!
# `ChatainSchlenker2026` — typed example data

Auto-generated from `Linglib/Data/Examples/ChatainSchlenker2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ChatainSchlenker2026.Examples`.
-/

@[expose] public section

namespace ChatainSchlenker2026.Examples

def ex_26 : Datum :=
  { id := "chatainschlenker2026_26"
    source := ⟨"chatain-schlenker-2026", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Last Monday, Bill did not take the lab rat out of its cage. On Wednesday as well, but that’s just because I took it home on Tuesday and forgot to bring it back, so it wasn’t in the cage at all that day."
    glossedTokens := []
    context := "We’re supposed to take the lab rat out of its cage once a day. Otherwise, it feels stressed. Bill has been unreliable in performing this task."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_34a : Datum :=
  { id := "chatainschlenker2026_34a"
    source := ⟨"chatain-schlenker-2026", "(34a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Aucune de ces dix personnalités ne s’aperçoit qu’elle est impopulaire, car elles sont toutes mortes!"
    glossedTokens := [("Aucune", "none"), ("de", "of"), ("ces", "these"), ("dix", "ten"), ("personnalités", "public.figures"), ("ne", "NE"), ("s’aperçoit", "SE-notices"), ("qu’elle", "that-she"), ("est", "is"), ("impopulaire", "unpopular"), ("car", "because"), ("elles", "they"), ("sont", "are"), ("toutes", "all"), ("mortes", "dead")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("accommodated", "alive"), ("projected", "unpopular")] }

def ex_34b : Datum :=
  { id := "chatainschlenker2026_34b"
    source := ⟨"chatain-schlenker-2026", "(34b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Aucune de ces dix personnalités ne s’aperçoit qu’elle est impopulaire, car aucune ne l’est!"
    glossedTokens := [("Aucune", "none"), ("de", "of"), ("ces", "these"), ("dix", "ten"), ("personnalités", "public.figures"), ("ne", "NE"), ("s’aperçoit", "SE-notices"), ("qu’elle", "that-she"), ("est", "is"), ("impopulaire", "unpopular"), ("car", "because"), ("aucune", "none"), ("ne", "NE"), ("l’est", "it-is")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("accommodated", "unpopular"), ("projected", "alive")] }

def ex_38a : Datum :=
  { id := "chatainschlenker2026_38a"
    source := ⟨"chatain-schlenker-2026", "(38a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Josh won’t return the book to the library."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_38b : Datum :=
  { id := "chatainschlenker2026_38b"
    source := ⟨"chatain-schlenker-2026", "(38b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Josh won’t return the book to the library, because he never had the book."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("accommodated", "possession"), ("projected", "ownership")] }

def ex_38c : Datum :=
  { id := "chatainschlenker2026_38c"
    source := ⟨"chatain-schlenker-2026", "(38c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Josh won’t return the book to the library, because it’s not a book from the library."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("accommodated", "ownership"), ("projected", "possession")] }

def ex_39a : Datum :=
  { id := "chatainschlenker2026_39a"
    source := ⟨"chatain-schlenker-2026", "(39a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Dans mon pays, le roi ne s’aperçoit pas qu’il est impopulaire. Dans le mien aussi: il est mort."
    glossedTokens := [("Dans", "in"), ("mon", "my"), ("pays", "country"), ("le", "the"), ("roi", "king"), ("ne", "NE"), ("s’aperçoit", "himself-notices"), ("pas", "not"), ("qu’il", "that-he"), ("est", "is"), ("impopulaire", "unpopular"), ("Dans", "in"), ("le", "the"), ("mien", "mine"), ("aussi", "too"), ("il", "he"), ("est", "is"), ("mort", "dead")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("accommodated", "alive"), ("projected", "unpopular")] }

def ex_39b : Datum :=
  { id := "chatainschlenker2026_39b"
    source := ⟨"chatain-schlenker-2026", "(39b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Dans mon pays, le roi ne s’aperçoit pas qu’il est impopulaire. Dans le mien aussi: notre roi est très populaire."
    glossedTokens := [("Dans", "in"), ("mon", "my"), ("pays", "country"), ("le", "the"), ("roi", "king"), ("ne", "NE"), ("s’aperçoit", "himself-notices"), ("pas", "not"), ("qu’il", "that-he"), ("est", "is"), ("impopulaire", "unpopular"), ("Dans", "in"), ("le", "the"), ("mien", "mine"), ("aussi", "too"), ("notre", "our"), ("roi", "king"), ("est", "is"), ("très", "very"), ("populaire", "popular")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("accommodated", "unpopular"), ("projected", "alive")] }

def all : List Datum := [ex_26, ex_34a, ex_34b, ex_38a, ex_38b, ex_38c, ex_39a, ex_39b]

end ChatainSchlenker2026.Examples
