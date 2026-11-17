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
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_34a : Datum :=
  { id := "chatainschlenker2026_34a"
    source := ⟨"chatain-schlenker-2026", "(34a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Aucune de ces dix personnalités ne s’aperçoit qu’elle est impopulaire, car elles sont toutes mortes!"
    glossedTokens := [("Aucune", "none"), ("de", "of"), ("ces", "these"), ("dix", "ten"), ("personnalités", "public.figures"), ("ne", "NE"), ("s’aperçoit", "SE-notices"), ("qu’elle", "that-she"), ("est", "is"), ("impopulaire", "unpopular"), ("car", "because"), ("elles", "they"), ("sont", "are"), ("toutes", "all"), ("mortes", "dead")]
    glossedWords := [⟨['A', 'u', 'c', 'u', 'n', 'e'], ['n', 'o', 'n', 'e'], [⟨['A', 'u', 'c', 'u', 'n', 'e'], ['n', 'o', 'n', 'e'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['c', 'e', 's'], ['t', 'h', 'e', 's', 'e'], [⟨['c', 'e', 's'], ['t', 'h', 'e', 's', 'e'], none⟩]⟩, ⟨['d', 'i', 'x'], ['t', 'e', 'n'], [⟨['d', 'i', 'x'], ['t', 'e', 'n'], none⟩]⟩, ⟨['p', 'e', 'r', 's', 'o', 'n', 'n', 'a', 'l', 'i', 't', 'é', 's'], ['p', 'u', 'b', 'l', 'i', 'c', '.', 'f', 'i', 'g', 'u', 'r', 'e', 's'], [⟨['p', 'e', 'r', 's', 'o', 'n', 'n', 'a', 'l', 'i', 't', 'é', 's'], ['p', 'u', 'b', 'l', 'i', 'c', '.', 'f', 'i', 'g', 'u', 'r', 'e', 's'], none⟩]⟩, ⟨['n', 'e'], ['N', 'E'], [⟨['n', 'e'], ['N', 'E'], none⟩]⟩, ⟨['s', '’', 'a', 'p', 'e', 'r', 'ç', 'o', 'i', 't'], ['S', 'E', '-', 'n', 'o', 't', 'i', 'c', 'e', 's'], []⟩, ⟨['q', 'u', '’', 'e', 'l', 'l', 'e'], ['t', 'h', 'a', 't', '-', 's', 'h', 'e'], []⟩, ⟨['e', 's', 't'], ['i', 's'], [⟨['e', 's', 't'], ['i', 's'], none⟩]⟩, ⟨['i', 'm', 'p', 'o', 'p', 'u', 'l', 'a', 'i', 'r', 'e'], ['u', 'n', 'p', 'o', 'p', 'u', 'l', 'a', 'r'], [⟨['i', 'm', 'p', 'o', 'p', 'u', 'l', 'a', 'i', 'r', 'e'], ['u', 'n', 'p', 'o', 'p', 'u', 'l', 'a', 'r'], none⟩]⟩, ⟨['c', 'a', 'r'], ['b', 'e', 'c', 'a', 'u', 's', 'e'], [⟨['c', 'a', 'r'], ['b', 'e', 'c', 'a', 'u', 's', 'e'], none⟩]⟩, ⟨['e', 'l', 'l', 'e', 's'], ['t', 'h', 'e', 'y'], [⟨['e', 'l', 'l', 'e', 's'], ['t', 'h', 'e', 'y'], none⟩]⟩, ⟨['s', 'o', 'n', 't'], ['a', 'r', 'e'], [⟨['s', 'o', 'n', 't'], ['a', 'r', 'e'], none⟩]⟩, ⟨['t', 'o', 'u', 't', 'e', 's'], ['a', 'l', 'l'], [⟨['t', 'o', 'u', 't', 'e', 's'], ['a', 'l', 'l'], none⟩]⟩, ⟨['m', 'o', 'r', 't', 'e', 's'], ['d', 'e', 'a', 'd'], [⟨['m', 'o', 'r', 't', 'e', 's'], ['d', 'e', 'a', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("accommodated", "alive"), ("projected", "unpopular")] }

def ex_34b : Datum :=
  { id := "chatainschlenker2026_34b"
    source := ⟨"chatain-schlenker-2026", "(34b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Aucune de ces dix personnalités ne s’aperçoit qu’elle est impopulaire, car aucune ne l’est!"
    glossedTokens := [("Aucune", "none"), ("de", "of"), ("ces", "these"), ("dix", "ten"), ("personnalités", "public.figures"), ("ne", "NE"), ("s’aperçoit", "SE-notices"), ("qu’elle", "that-she"), ("est", "is"), ("impopulaire", "unpopular"), ("car", "because"), ("aucune", "none"), ("ne", "NE"), ("l’est", "it-is")]
    glossedWords := [⟨['A', 'u', 'c', 'u', 'n', 'e'], ['n', 'o', 'n', 'e'], [⟨['A', 'u', 'c', 'u', 'n', 'e'], ['n', 'o', 'n', 'e'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['c', 'e', 's'], ['t', 'h', 'e', 's', 'e'], [⟨['c', 'e', 's'], ['t', 'h', 'e', 's', 'e'], none⟩]⟩, ⟨['d', 'i', 'x'], ['t', 'e', 'n'], [⟨['d', 'i', 'x'], ['t', 'e', 'n'], none⟩]⟩, ⟨['p', 'e', 'r', 's', 'o', 'n', 'n', 'a', 'l', 'i', 't', 'é', 's'], ['p', 'u', 'b', 'l', 'i', 'c', '.', 'f', 'i', 'g', 'u', 'r', 'e', 's'], [⟨['p', 'e', 'r', 's', 'o', 'n', 'n', 'a', 'l', 'i', 't', 'é', 's'], ['p', 'u', 'b', 'l', 'i', 'c', '.', 'f', 'i', 'g', 'u', 'r', 'e', 's'], none⟩]⟩, ⟨['n', 'e'], ['N', 'E'], [⟨['n', 'e'], ['N', 'E'], none⟩]⟩, ⟨['s', '’', 'a', 'p', 'e', 'r', 'ç', 'o', 'i', 't'], ['S', 'E', '-', 'n', 'o', 't', 'i', 'c', 'e', 's'], []⟩, ⟨['q', 'u', '’', 'e', 'l', 'l', 'e'], ['t', 'h', 'a', 't', '-', 's', 'h', 'e'], []⟩, ⟨['e', 's', 't'], ['i', 's'], [⟨['e', 's', 't'], ['i', 's'], none⟩]⟩, ⟨['i', 'm', 'p', 'o', 'p', 'u', 'l', 'a', 'i', 'r', 'e'], ['u', 'n', 'p', 'o', 'p', 'u', 'l', 'a', 'r'], [⟨['i', 'm', 'p', 'o', 'p', 'u', 'l', 'a', 'i', 'r', 'e'], ['u', 'n', 'p', 'o', 'p', 'u', 'l', 'a', 'r'], none⟩]⟩, ⟨['c', 'a', 'r'], ['b', 'e', 'c', 'a', 'u', 's', 'e'], [⟨['c', 'a', 'r'], ['b', 'e', 'c', 'a', 'u', 's', 'e'], none⟩]⟩, ⟨['a', 'u', 'c', 'u', 'n', 'e'], ['n', 'o', 'n', 'e'], [⟨['a', 'u', 'c', 'u', 'n', 'e'], ['n', 'o', 'n', 'e'], none⟩]⟩, ⟨['n', 'e'], ['N', 'E'], [⟨['n', 'e'], ['N', 'E'], none⟩]⟩, ⟨['l', '’', 'e', 's', 't'], ['i', 't', '-', 'i', 's'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
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
    contrasts := []
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
    contrasts := []
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
    contrasts := []
    readings := []
    paperFeatures := [("accommodated", "ownership"), ("projected", "possession")] }

def ex_39a : Datum :=
  { id := "chatainschlenker2026_39a"
    source := ⟨"chatain-schlenker-2026", "(39a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Dans mon pays, le roi ne s’aperçoit pas qu’il est impopulaire. Dans le mien aussi: il est mort."
    glossedTokens := [("Dans", "in"), ("mon", "my"), ("pays", "country"), ("le", "the"), ("roi", "king"), ("ne", "NE"), ("s’aperçoit", "himself-notices"), ("pas", "not"), ("qu’il", "that-he"), ("est", "is"), ("impopulaire", "unpopular"), ("Dans", "in"), ("le", "the"), ("mien", "mine"), ("aussi", "too"), ("il", "he"), ("est", "is"), ("mort", "dead")]
    glossedWords := [⟨['D', 'a', 'n', 's'], ['i', 'n'], [⟨['D', 'a', 'n', 's'], ['i', 'n'], none⟩]⟩, ⟨['m', 'o', 'n'], ['m', 'y'], [⟨['m', 'o', 'n'], ['m', 'y'], none⟩]⟩, ⟨['p', 'a', 'y', 's'], ['c', 'o', 'u', 'n', 't', 'r', 'y'], [⟨['p', 'a', 'y', 's'], ['c', 'o', 'u', 'n', 't', 'r', 'y'], none⟩]⟩, ⟨['l', 'e'], ['t', 'h', 'e'], [⟨['l', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['r', 'o', 'i'], ['k', 'i', 'n', 'g'], [⟨['r', 'o', 'i'], ['k', 'i', 'n', 'g'], none⟩]⟩, ⟨['n', 'e'], ['N', 'E'], [⟨['n', 'e'], ['N', 'E'], none⟩]⟩, ⟨['s', '’', 'a', 'p', 'e', 'r', 'ç', 'o', 'i', 't'], ['h', 'i', 'm', 's', 'e', 'l', 'f', '-', 'n', 'o', 't', 'i', 'c', 'e', 's'], []⟩, ⟨['p', 'a', 's'], ['n', 'o', 't'], [⟨['p', 'a', 's'], ['n', 'o', 't'], none⟩]⟩, ⟨['q', 'u', '’', 'i', 'l'], ['t', 'h', 'a', 't', '-', 'h', 'e'], []⟩, ⟨['e', 's', 't'], ['i', 's'], [⟨['e', 's', 't'], ['i', 's'], none⟩]⟩, ⟨['i', 'm', 'p', 'o', 'p', 'u', 'l', 'a', 'i', 'r', 'e'], ['u', 'n', 'p', 'o', 'p', 'u', 'l', 'a', 'r'], [⟨['i', 'm', 'p', 'o', 'p', 'u', 'l', 'a', 'i', 'r', 'e'], ['u', 'n', 'p', 'o', 'p', 'u', 'l', 'a', 'r'], none⟩]⟩, ⟨['D', 'a', 'n', 's'], ['i', 'n'], [⟨['D', 'a', 'n', 's'], ['i', 'n'], none⟩]⟩, ⟨['l', 'e'], ['t', 'h', 'e'], [⟨['l', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['m', 'i', 'e', 'n'], ['m', 'i', 'n', 'e'], [⟨['m', 'i', 'e', 'n'], ['m', 'i', 'n', 'e'], none⟩]⟩, ⟨['a', 'u', 's', 's', 'i'], ['t', 'o', 'o'], [⟨['a', 'u', 's', 's', 'i'], ['t', 'o', 'o'], none⟩]⟩, ⟨['i', 'l'], ['h', 'e'], [⟨['i', 'l'], ['h', 'e'], none⟩]⟩, ⟨['e', 's', 't'], ['i', 's'], [⟨['e', 's', 't'], ['i', 's'], none⟩]⟩, ⟨['m', 'o', 'r', 't'], ['d', 'e', 'a', 'd'], [⟨['m', 'o', 'r', 't'], ['d', 'e', 'a', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("accommodated", "alive"), ("projected", "unpopular")] }

def ex_39b : Datum :=
  { id := "chatainschlenker2026_39b"
    source := ⟨"chatain-schlenker-2026", "(39b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Dans mon pays, le roi ne s’aperçoit pas qu’il est impopulaire. Dans le mien aussi: notre roi est très populaire."
    glossedTokens := [("Dans", "in"), ("mon", "my"), ("pays", "country"), ("le", "the"), ("roi", "king"), ("ne", "NE"), ("s’aperçoit", "himself-notices"), ("pas", "not"), ("qu’il", "that-he"), ("est", "is"), ("impopulaire", "unpopular"), ("Dans", "in"), ("le", "the"), ("mien", "mine"), ("aussi", "too"), ("notre", "our"), ("roi", "king"), ("est", "is"), ("très", "very"), ("populaire", "popular")]
    glossedWords := [⟨['D', 'a', 'n', 's'], ['i', 'n'], [⟨['D', 'a', 'n', 's'], ['i', 'n'], none⟩]⟩, ⟨['m', 'o', 'n'], ['m', 'y'], [⟨['m', 'o', 'n'], ['m', 'y'], none⟩]⟩, ⟨['p', 'a', 'y', 's'], ['c', 'o', 'u', 'n', 't', 'r', 'y'], [⟨['p', 'a', 'y', 's'], ['c', 'o', 'u', 'n', 't', 'r', 'y'], none⟩]⟩, ⟨['l', 'e'], ['t', 'h', 'e'], [⟨['l', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['r', 'o', 'i'], ['k', 'i', 'n', 'g'], [⟨['r', 'o', 'i'], ['k', 'i', 'n', 'g'], none⟩]⟩, ⟨['n', 'e'], ['N', 'E'], [⟨['n', 'e'], ['N', 'E'], none⟩]⟩, ⟨['s', '’', 'a', 'p', 'e', 'r', 'ç', 'o', 'i', 't'], ['h', 'i', 'm', 's', 'e', 'l', 'f', '-', 'n', 'o', 't', 'i', 'c', 'e', 's'], []⟩, ⟨['p', 'a', 's'], ['n', 'o', 't'], [⟨['p', 'a', 's'], ['n', 'o', 't'], none⟩]⟩, ⟨['q', 'u', '’', 'i', 'l'], ['t', 'h', 'a', 't', '-', 'h', 'e'], []⟩, ⟨['e', 's', 't'], ['i', 's'], [⟨['e', 's', 't'], ['i', 's'], none⟩]⟩, ⟨['i', 'm', 'p', 'o', 'p', 'u', 'l', 'a', 'i', 'r', 'e'], ['u', 'n', 'p', 'o', 'p', 'u', 'l', 'a', 'r'], [⟨['i', 'm', 'p', 'o', 'p', 'u', 'l', 'a', 'i', 'r', 'e'], ['u', 'n', 'p', 'o', 'p', 'u', 'l', 'a', 'r'], none⟩]⟩, ⟨['D', 'a', 'n', 's'], ['i', 'n'], [⟨['D', 'a', 'n', 's'], ['i', 'n'], none⟩]⟩, ⟨['l', 'e'], ['t', 'h', 'e'], [⟨['l', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['m', 'i', 'e', 'n'], ['m', 'i', 'n', 'e'], [⟨['m', 'i', 'e', 'n'], ['m', 'i', 'n', 'e'], none⟩]⟩, ⟨['a', 'u', 's', 's', 'i'], ['t', 'o', 'o'], [⟨['a', 'u', 's', 's', 'i'], ['t', 'o', 'o'], none⟩]⟩, ⟨['n', 'o', 't', 'r', 'e'], ['o', 'u', 'r'], [⟨['n', 'o', 't', 'r', 'e'], ['o', 'u', 'r'], none⟩]⟩, ⟨['r', 'o', 'i'], ['k', 'i', 'n', 'g'], [⟨['r', 'o', 'i'], ['k', 'i', 'n', 'g'], none⟩]⟩, ⟨['e', 's', 't'], ['i', 's'], [⟨['e', 's', 't'], ['i', 's'], none⟩]⟩, ⟨['t', 'r', 'è', 's'], ['v', 'e', 'r', 'y'], [⟨['t', 'r', 'è', 's'], ['v', 'e', 'r', 'y'], none⟩]⟩, ⟨['p', 'o', 'p', 'u', 'l', 'a', 'i', 'r', 'e'], ['p', 'o', 'p', 'u', 'l', 'a', 'r'], [⟨['p', 'o', 'p', 'u', 'l', 'a', 'i', 'r', 'e'], ['p', 'o', 'p', 'u', 'l', 'a', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("accommodated", "unpopular"), ("projected", "alive")] }

def all : List Datum := [ex_26, ex_34a, ex_34b, ex_38a, ex_38b, ex_38c, ex_39a, ex_39b]

end ChatainSchlenker2026.Examples
