module

public import Linglib.Data.Examples.Schema

/-!
# `DelPrete2013` — typed example data

Auto-generated from `Linglib/Data/Examples/DelPrete2013.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace DelPrete2013.Examples`.
-/

@[expose] public section

namespace DelPrete2013.Examples

def ex_1 : Datum :=
  { id := "delprete2013_1"
    source := ⟨"del-prete-2013", "(1)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "(In quel periodo / In quel momento) Gianni leggeva il giornale."
    glossedTokens := [("Gianni", "Gianni"), ("leggeva", "read(Imp, 3sg)"), ("il", "the"), ("giornale", "newspaper")]
    glossedWords := [⟨[['G', 'i', 'a', 'n', 'n', 'i']], [['G', 'i', 'a', 'n', 'n', 'i']]⟩, ⟨[['l', 'e', 'g', 'g', 'e', 'v', 'a']], [['r', 'e', 'a', 'd', '(', 'I', 'm', 'p', ',', ' ', '3', 's', 'g', ')']]⟩, ⟨[['i', 'l']], [['t', 'h', 'e']]⟩, ⟨[['g', 'i', 'o', 'r', 'n', 'a', 'l', 'e']], [['n', 'e', 'w', 's', 'p', 'a', 'p', 'e', 'r']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable), ("PROG", .acceptable)]
    paperFeatures := [("object", "definite"), ("qAdverb", "none"), ("soe", "none")] }

def ex_2a : Datum :=
  { id := "delprete2013_2a"
    source := ⟨"del-prete-2013", "(2a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "(In quel periodo / In quel momento) Gianni guidava un'auto sportiva."
    glossedTokens := [("Gianni", "Gianni"), ("guidava", "drive(Imp, 3sg)"), ("un'", "a"), ("auto", "car"), ("sportiva", "sports")]
    glossedWords := [⟨[['G', 'i', 'a', 'n', 'n', 'i']], [['G', 'i', 'a', 'n', 'n', 'i']]⟩, ⟨[['g', 'u', 'i', 'd', 'a', 'v', 'a']], [['d', 'r', 'i', 'v', 'e', '(', 'I', 'm', 'p', ',', ' ', '3', 's', 'g', ')']]⟩, ⟨[['u', 'n', '\'']], [['a']]⟩, ⟨[['a', 'u', 't', 'o']], [['c', 'a', 'r']]⟩, ⟨[['s', 'p', 'o', 'r', 't', 'i', 'v', 'a']], [['s', 'p', 'o', 'r', 't', 's']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable), ("PROG", .acceptable)]
    paperFeatures := [("object", "singularIndefinite"), ("qAdverb", "none"), ("soe", "individual")] }

def ex_2b : Datum :=
  { id := "delprete2013_2b"
    source := ⟨"del-prete-2013", "(2b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "(In quel periodo / In quel momento) Gianni leggeva un libro di filosofia."
    glossedTokens := [("Gianni", "Gianni"), ("leggeva", "read(Imp, 3sg)"), ("un", "a"), ("libro", "book"), ("di", "of"), ("filosofia", "philosophy")]
    glossedWords := [⟨[['G', 'i', 'a', 'n', 'n', 'i']], [['G', 'i', 'a', 'n', 'n', 'i']]⟩, ⟨[['l', 'e', 'g', 'g', 'e', 'v', 'a']], [['r', 'e', 'a', 'd', '(', 'I', 'm', 'p', ',', ' ', '3', 's', 'g', ')']]⟩, ⟨[['u', 'n']], [['a']]⟩, ⟨[['l', 'i', 'b', 'r', 'o']], [['b', 'o', 'o', 'k']]⟩, ⟨[['d', 'i']], [['o', 'f']]⟩, ⟨[['f', 'i', 'l', 'o', 's', 'o', 'f', 'i', 'a']], [['p', 'h', 'i', 'l', 'o', 's', 'o', 'p', 'h', 'y']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .unacceptable), ("PROG", .acceptable)]
    paperFeatures := [("object", "singularIndefinite"), ("qAdverb", "none"), ("soe", "individual")] }

def ex_3 : Datum :=
  { id := "delprete2013_3"
    source := ⟨"del-prete-2013", "(3)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "(In quel periodo) Gianni fumava un sigaro toscano (il Toscanello)."
    glossedTokens := [("Gianni", "Gianni"), ("fumava", "smoke(Imp, 3sg)"), ("un", "a"), ("sigaro", "cigar"), ("toscano", "Tuscan")]
    glossedWords := [⟨[['G', 'i', 'a', 'n', 'n', 'i']], [['G', 'i', 'a', 'n', 'n', 'i']]⟩, ⟨[['f', 'u', 'm', 'a', 'v', 'a']], [['s', 'm', 'o', 'k', 'e', '(', 'I', 'm', 'p', ',', ' ', '3', 's', 'g', ')']]⟩, ⟨[['u', 'n']], [['a']]⟩, ⟨[['s', 'i', 'g', 'a', 'r', 'o']], [['c', 'i', 'g', 'a', 'r']]⟩, ⟨[['t', 'o', 's', 'c', 'a', 'n', 'o']], [['T', 'u', 's', 'c', 'a', 'n']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable)]
    paperFeatures := [("object", "kindIndefinite"), ("qAdverb", "none"), ("soe", "kind")] }

def ex_4a : Datum :=
  { id := "delprete2013_4a"
    source := ⟨"del-prete-2013", "(4a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni viaggia in treno."
    glossedTokens := [("Gianni", "Gianni"), ("viaggia", "travel(Pres, 3sg)"), ("in", "in"), ("treno", "train")]
    glossedWords := [⟨[['G', 'i', 'a', 'n', 'n', 'i']], [['G', 'i', 'a', 'n', 'n', 'i']]⟩, ⟨[['v', 'i', 'a', 'g', 'g', 'i', 'a']], [['t', 'r', 'a', 'v', 'e', 'l', '(', 'P', 'r', 'e', 's', ',', ' ', '3', 's', 'g', ')']]⟩, ⟨[['i', 'n']], [['i', 'n']]⟩, ⟨[['t', 'r', 'e', 'n', 'o']], [['t', 'r', 'a', 'i', 'n']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable)]
    paperFeatures := [("object", "none"), ("qAdverb", "none"), ("soe", "none")] }

def ex_4b : Datum :=
  { id := "delprete2013_4b"
    source := ⟨"del-prete-2013", "(4b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni viaggia sempre in treno."
    glossedTokens := [("Gianni", "Gianni"), ("viaggia", "travel(Pres, 3sg)"), ("sempre", "always"), ("in", "in"), ("treno", "train")]
    glossedWords := [⟨[['G', 'i', 'a', 'n', 'n', 'i']], [['G', 'i', 'a', 'n', 'n', 'i']]⟩, ⟨[['v', 'i', 'a', 'g', 'g', 'i', 'a']], [['t', 'r', 'a', 'v', 'e', 'l', '(', 'P', 'r', 'e', 's', ',', ' ', '3', 's', 'g', ')']]⟩, ⟨[['s', 'e', 'm', 'p', 'r', 'e']], [['a', 'l', 'w', 'a', 'y', 's']]⟩, ⟨[['i', 'n']], [['i', 'n']]⟩, ⟨[['t', 'r', 'e', 'n', 'o']], [['t', 'r', 'a', 'i', 'n']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable)]
    paperFeatures := [("object", "none"), ("qAdverb", "sempre"), ("soe", "none")] }

def ex_6 : Datum :=
  { id := "delprete2013_6"
    source := ⟨"del-prete-2013", "(6)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Quando va a trovare i suoi parenti, Gianni viaggia sempre in treno."
    glossedTokens := [("Quando", "When"), ("va", "go(Pres, 3sg)"), ("a", "to"), ("trovare", "find"), ("i", "the"), ("suoi", "his"), ("parenti", "relatives"), ("Gianni", "Gianni"), ("viaggia", "travel(Pres, 3sg)"), ("sempre", "always"), ("in", "in"), ("treno", "train")]
    glossedWords := [⟨[['Q', 'u', 'a', 'n', 'd', 'o']], [['W', 'h', 'e', 'n']]⟩, ⟨[['v', 'a']], [['g', 'o', '(', 'P', 'r', 'e', 's', ',', ' ', '3', 's', 'g', ')']]⟩, ⟨[['a']], [['t', 'o']]⟩, ⟨[['t', 'r', 'o', 'v', 'a', 'r', 'e']], [['f', 'i', 'n', 'd']]⟩, ⟨[['i']], [['t', 'h', 'e']]⟩, ⟨[['s', 'u', 'o', 'i']], [['h', 'i', 's']]⟩, ⟨[['p', 'a', 'r', 'e', 'n', 't', 'i']], [['r', 'e', 'l', 'a', 't', 'i', 'v', 'e', 's']]⟩, ⟨[['G', 'i', 'a', 'n', 'n', 'i']], [['G', 'i', 'a', 'n', 'n', 'i']]⟩, ⟨[['v', 'i', 'a', 'g', 'g', 'i', 'a']], [['t', 'r', 'a', 'v', 'e', 'l', '(', 'P', 'r', 'e', 's', ',', ' ', '3', 's', 'g', ')']]⟩, ⟨[['s', 'e', 'm', 'p', 'r', 'e']], [['a', 'l', 'w', 'a', 'y', 's']]⟩, ⟨[['i', 'n']], [['i', 'n']]⟩, ⟨[['t', 'r', 'e', 'n', 'o']], [['t', 'r', 'a', 'i', 'n']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable)]
    paperFeatures := [("object", "none"), ("qAdverb", "sempre"), ("soe", "none")] }

def ex_8 : Datum :=
  { id := "delprete2013_8"
    source := ⟨"del-prete-2013", "(8)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "(In quel periodo) Gianni leggeva sempre / spesso un libro di filosofia."
    glossedTokens := [("Gianni", "Gianni"), ("leggeva", "read(Imp, 3sg)"), ("sempre", "always"), ("spesso", "often"), ("un", "a"), ("libro", "book"), ("di", "of"), ("filosofia", "philosophy")]
    glossedWords := [⟨[['G', 'i', 'a', 'n', 'n', 'i']], [['G', 'i', 'a', 'n', 'n', 'i']]⟩, ⟨[['l', 'e', 'g', 'g', 'e', 'v', 'a']], [['r', 'e', 'a', 'd', '(', 'I', 'm', 'p', ',', ' ', '3', 's', 'g', ')']]⟩, ⟨[['s', 'e', 'm', 'p', 'r', 'e']], [['a', 'l', 'w', 'a', 'y', 's']]⟩, ⟨[['s', 'p', 'e', 's', 's', 'o']], [['o', 'f', 't', 'e', 'n']]⟩, ⟨[['u', 'n']], [['a']]⟩, ⟨[['l', 'i', 'b', 'r', 'o']], [['b', 'o', 'o', 'k']]⟩, ⟨[['d', 'i']], [['o', 'f']]⟩, ⟨[['f', 'i', 'l', 'o', 's', 'o', 'f', 'i', 'a']], [['p', 'h', 'i', 'l', 'o', 's', 'o', 'p', 'h', 'y']]⟩]
    lgrConformance := some .wordAligned
    context := "A suitable discourse context which provides a restriction for the Q-adverb (footnote 9)."
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable)]
    paperFeatures := [("object", "singularIndefinite"), ("qAdverb", "sempre"), ("soe", "none")] }

def ex_9b : Datum :=
  { id := "delprete2013_9b"
    source := ⟨"del-prete-2013", "(9b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni non fumava nessun sigaro toscano (ma ora ha una passione per il Toscanello)."
    glossedTokens := [("Gianni", "Gianni"), ("non", "neg"), ("fumava", "smoke(Imp, 3sg)"), ("nessun", "neg-a"), ("sigaro", "cigar"), ("toscano", "Tuscan")]
    glossedWords := [⟨[['G', 'i', 'a', 'n', 'n', 'i']], [['G', 'i', 'a', 'n', 'n', 'i']]⟩, ⟨[['n', 'o', 'n']], [['n', 'e', 'g']]⟩, ⟨[['f', 'u', 'm', 'a', 'v', 'a']], [['s', 'm', 'o', 'k', 'e', '(', 'I', 'm', 'p', ',', ' ', '3', 's', 'g', ')']]⟩, ⟨[['n', 'e', 's', 's', 'u', 'n']], [['n', 'e', 'g'], ['a']]⟩, ⟨[['s', 'i', 'g', 'a', 'r', 'o']], [['c', 'i', 'g', 'a', 'r']]⟩, ⟨[['t', 'o', 's', 'c', 'a', 'n', 'o']], [['T', 'u', 's', 'c', 'a', 'n']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable)]
    paperFeatures := [("object", "negativeKindIndefinite"), ("qAdverb", "none"), ("soe", "none")] }

def ex_11 : Datum :=
  { id := "delprete2013_11"
    source := ⟨"del-prete-2013", "(11)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "(In quel periodo / In quel momento) Gianni leggeva libri di filosofia."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable), ("PROG", .unacceptable)]
    paperFeatures := [("object", "barePlural"), ("qAdverb", "none"), ("soe", "kind")] }

def ex_12 : Datum :=
  { id := "delprete2013_12"
    source := ⟨"del-prete-2013", "(12)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni leggeva un genere di libri di filosofia (libri di filosofia morale)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable), ("PROG", .unacceptable)]
    paperFeatures := [("object", "kindIndefinite"), ("qAdverb", "none"), ("soe", "kind")] }

def ex_13 : Datum :=
  { id := "delprete2013_13"
    source := ⟨"del-prete-2013", "(13)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni fumava sigari toscani."
    glossedTokens := []
    context := "Gianni had the habit of smoking Tuscan cigars without an inclination for any particular sub-kind (footnote 12)."
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable)]
    paperFeatures := [("object", "barePlural"), ("qAdverb", "none"), ("soe", "kind")] }

def ex_14 : Datum :=
  { id := "delprete2013_14"
    source := ⟨"del-prete-2013", "(14)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni leggeva un certo genere di libri (i.e. libri di filosofia)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable)]
    paperFeatures := [("object", "kindIndefinite"), ("qAdverb", "none"), ("soe", "kind")] }

def fn11 : Datum :=
  { id := "delprete2013_fn11"
    source := ⟨"del-prete-2013", "footnote 11 (i)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni mangiava ciliegie."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable), ("PROG", .acceptable)]
    paperFeatures := [("object", "barePlural"), ("qAdverb", "none"), ("soe", "kind")] }

def ex_17 : Datum :=
  { id := "delprete2013_17"
    source := ⟨"del-prete-2013", "(17)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Alle 15 Gianni era a casa, leggeva un libro."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("PROG", .acceptable)]
    paperFeatures := [("object", "singularIndefinite"), ("qAdverb", "none"), ("soe", "none")] }

def ex_19 : Datum :=
  { id := "delprete2013_19"
    source := ⟨"del-prete-2013", "(19)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ogni giorno alle 15 Gianni prendeva il caffè."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable)]
    paperFeatures := [("object", "definite"), ("qAdverb", "ogni"), ("soe", "none")] }

def ex_20 : Datum :=
  { id := "delprete2013_20"
    source := ⟨"del-prete-2013", "(20)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "In quel periodo, ogni giorno alle 15 Gianni prendeva il caffè."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable)]
    paperFeatures := [("object", "definite"), ("qAdverb", "ogni"), ("soe", "none")] }

def fn29 : Datum :=
  { id := "delprete2013_fn29"
    source := ⟨"del-prete-2013", "footnote 29 (i)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Alle 15 Gianni guidava auto sportive."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := [("PROG", .marginal)]
    paperFeatures := [("object", "barePlural"), ("qAdverb", "none"), ("soe", "kind")] }

def fn31 : Datum :=
  { id := "delprete2013_fn31"
    source := ⟨"del-prete-2013", "footnote 31 (i)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Quando voleva meditare, Gianni leggeva sempre un libro di filosofia."
    glossedTokens := [("Quando", "when"), ("voleva", "want(Imp, 3sg)"), ("meditare", "meditate(Inf)"), ("Gianni", "Gianni"), ("leggeva", "read(Imp, 3sg)"), ("sempre", "always"), ("un", "a"), ("libro", "book"), ("di", "of"), ("filosofia", "philosophy")]
    glossedWords := [⟨[['Q', 'u', 'a', 'n', 'd', 'o']], [['w', 'h', 'e', 'n']]⟩, ⟨[['v', 'o', 'l', 'e', 'v', 'a']], [['w', 'a', 'n', 't', '(', 'I', 'm', 'p', ',', ' ', '3', 's', 'g', ')']]⟩, ⟨[['m', 'e', 'd', 'i', 't', 'a', 'r', 'e']], [['m', 'e', 'd', 'i', 't', 'a', 't', 'e', '(', 'I', 'n', 'f', ')']]⟩, ⟨[['G', 'i', 'a', 'n', 'n', 'i']], [['G', 'i', 'a', 'n', 'n', 'i']]⟩, ⟨[['l', 'e', 'g', 'g', 'e', 'v', 'a']], [['r', 'e', 'a', 'd', '(', 'I', 'm', 'p', ',', ' ', '3', 's', 'g', ')']]⟩, ⟨[['s', 'e', 'm', 'p', 'r', 'e']], [['a', 'l', 'w', 'a', 'y', 's']]⟩, ⟨[['u', 'n']], [['a']]⟩, ⟨[['l', 'i', 'b', 'r', 'o']], [['b', 'o', 'o', 'k']]⟩, ⟨[['d', 'i']], [['o', 'f']]⟩, ⟨[['f', 'i', 'l', 'o', 's', 'o', 'f', 'i', 'a']], [['p', 'h', 'i', 'l', 'o', 's', 'o', 'p', 'h', 'y']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable)]
    paperFeatures := [("object", "singularIndefinite"), ("qAdverb", "sempre"), ("soe", "none")] }

def tennis : Datum :=
  { id := "delprete2013_tennis"
    source := ⟨"del-prete-2013", "§8.4"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "(In quel periodo) Gianni giocava a tennis."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable)]
    paperFeatures := [("object", "none"), ("qAdverb", "none"), ("soe", "none")] }

def frequentative : Datum :=
  { id := "delprete2013_frequentative"
    source := ⟨"del-prete-2013", "§8.4.3"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni ha fumato Toscanelli per vent'anni."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("object", "barePlural"), ("qAdverb", "none"), ("soe", "kind")] }

def all : List Datum := [ex_1, ex_2a, ex_2b, ex_3, ex_4a, ex_4b, ex_6, ex_8, ex_9b, ex_11, ex_12, ex_13, ex_14, fn11, ex_17, ex_19, ex_20, fn29, fn31, tennis, frequentative]

end DelPrete2013.Examples
