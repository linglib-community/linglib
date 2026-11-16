module

public import Linglib.Data.Examples.Schema

/-!
# `Cuervo2003` — typed example data

Auto-generated from `Linglib/Data/Examples/Cuervo2003.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Cuervo2003.Examples`.
-/

@[expose] public section

namespace Cuervo2003.Examples

def ex_29a : Datum :=
  { id := "cuervo2003_29a"
    source := ⟨"cuervo-2003", "(29a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Pablo le mandó un diccionario a Gabi."
    glossedTokens := [("Pablo", "Pablo"), ("le", "CL.DAT"), ("mandó", "sent"), ("un", "a"), ("diccionario", "dictionary"), ("a", "DAT"), ("Gabi", "Gabi")]
    glossedWords := [⟨[['P', 'a', 'b', 'l', 'o']], [['P', 'a', 'b', 'l', 'o']]⟩, ⟨[['l', 'e']], [['C', 'L', '.', 'D', 'A', 'T']]⟩, ⟨[['m', 'a', 'n', 'd', 'ó']], [['s', 'e', 'n', 't']]⟩, ⟨[['u', 'n']], [['a']]⟩, ⟨[['d', 'i', 'c', 'c', 'i', 'o', 'n', 'a', 'r', 'i', 'o']], [['d', 'i', 'c', 't', 'i', 'o', 'n', 'a', 'r', 'y']]⟩, ⟨[['a']], [['D', 'A', 'T']]⟩, ⟨[['G', 'a', 'b', 'i']], [['G', 'a', 'b', 'i']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "mandar"), ("animate", "yes"), ("dative", "dp"), ("meaning", "recipient")] }

def ex_30 : Datum :=
  { id := "cuervo2003_30"
    source := ⟨"cuervo-2003", "(30)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Pablo nos preparó sandwichitos de miga a todos."
    glossedTokens := [("Pablo", "Pablo"), ("nos", "CL.1.PL.DAT"), ("preparó", "fixed"), ("sandwichitos", "sandwiches"), ("de", "of"), ("miga", "crumb"), ("a", "DAT"), ("todos", "all")]
    glossedWords := [⟨[['P', 'a', 'b', 'l', 'o']], [['P', 'a', 'b', 'l', 'o']]⟩, ⟨[['n', 'o', 's']], [['C', 'L', '.', '1', '.', 'P', 'L', '.', 'D', 'A', 'T']]⟩, ⟨[['p', 'r', 'e', 'p', 'a', 'r', 'ó']], [['f', 'i', 'x', 'e', 'd']]⟩, ⟨[['s', 'a', 'n', 'd', 'w', 'i', 'c', 'h', 'i', 't', 'o', 's']], [['s', 'a', 'n', 'd', 'w', 'i', 'c', 'h', 'e', 's']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['m', 'i', 'g', 'a']], [['c', 'r', 'u', 'm', 'b']]⟩, ⟨[['a']], [['D', 'A', 'T']]⟩, ⟨[['t', 'o', 'd', 'o', 's']], [['a', 'l', 'l']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "preparar"), ("animate", "yes"), ("dative", "dp"), ("meaning", "recipient")] }

def ex_31 : Datum :=
  { id := "cuervo2003_31"
    source := ⟨"cuervo-2003", "(31)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Pablo le sacó la bicicleta a Andreína."
    glossedTokens := [("Pablo", "Pablo"), ("le", "CL.DAT"), ("sacó", "took.away"), ("la", "the"), ("bicicleta", "bicycle"), ("a", "DAT"), ("Andreína", "Andreína")]
    glossedWords := [⟨[['P', 'a', 'b', 'l', 'o']], [['P', 'a', 'b', 'l', 'o']]⟩, ⟨[['l', 'e']], [['C', 'L', '.', 'D', 'A', 'T']]⟩, ⟨[['s', 'a', 'c', 'ó']], [['t', 'o', 'o', 'k', '.', 'a', 'w', 'a', 'y']]⟩, ⟨[['l', 'a']], [['t', 'h', 'e']]⟩, ⟨[['b', 'i', 'c', 'i', 'c', 'l', 'e', 't', 'a']], [['b', 'i', 'c', 'y', 'c', 'l', 'e']]⟩, ⟨[['a']], [['D', 'A', 'T']]⟩, ⟨[['A', 'n', 'd', 'r', 'e', 'í', 'n', 'a']], [['A', 'n', 'd', 'r', 'e', 'í', 'n', 'a']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "sacar"), ("animate", "yes"), ("dative", "dp"), ("meaning", "source")] }

def ex_32 : Datum :=
  { id := "cuervo2003_32"
    source := ⟨"cuervo-2003", "(32)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Pablo le lavó el auto a Valeria."
    glossedTokens := [("Pablo", "Pablo"), ("le", "CL.DAT"), ("lavó", "washed"), ("el", "the"), ("auto", "car"), ("a", "DAT"), ("Valeria", "Valeria")]
    glossedWords := [⟨[['P', 'a', 'b', 'l', 'o']], [['P', 'a', 'b', 'l', 'o']]⟩, ⟨[['l', 'e']], [['C', 'L', '.', 'D', 'A', 'T']]⟩, ⟨[['l', 'a', 'v', 'ó']], [['w', 'a', 's', 'h', 'e', 'd']]⟩, ⟨[['e', 'l']], [['t', 'h', 'e']]⟩, ⟨[['a', 'u', 't', 'o']], [['c', 'a', 'r']]⟩, ⟨[['a']], [['D', 'A', 'T']]⟩, ⟨[['V', 'a', 'l', 'e', 'r', 'i', 'a']], [['V', 'a', 'l', 'e', 'r', 'i', 'a']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "lavar"), ("animate", "yes"), ("dative", "dp"), ("meaning", "possessor")] }

def ex_33 : Datum :=
  { id := "cuervo2003_33"
    source := ⟨"cuervo-2003", "(33)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Pablo le admira la paciencia a Valeria."
    glossedTokens := [("Pablo", "Pablo"), ("le", "CL.DAT"), ("admira", "admires"), ("la", "the"), ("paciencia", "patience"), ("a", "DAT"), ("Valeria", "Valeria")]
    glossedWords := [⟨[['P', 'a', 'b', 'l', 'o']], [['P', 'a', 'b', 'l', 'o']]⟩, ⟨[['l', 'e']], [['C', 'L', '.', 'D', 'A', 'T']]⟩, ⟨[['a', 'd', 'm', 'i', 'r', 'a']], [['a', 'd', 'm', 'i', 'r', 'e', 's']]⟩, ⟨[['l', 'a']], [['t', 'h', 'e']]⟩, ⟨[['p', 'a', 'c', 'i', 'e', 'n', 'c', 'i', 'a']], [['p', 'a', 't', 'i', 'e', 'n', 'c', 'e']]⟩, ⟨[['a']], [['D', 'A', 'T']]⟩, ⟨[['V', 'a', 'l', 'e', 'r', 'i', 'a']], [['V', 'a', 'l', 'e', 'r', 'i', 'a']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "admirar"), ("animate", "yes"), ("dative", "dp"), ("meaning", "possessor")] }

def ex_34 : Datum :=
  { id := "cuervo2003_34"
    source := ⟨"cuervo-2003", "(34)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A Gabi le llegaron dos cartas de Londres."
    glossedTokens := [("A", "DAT"), ("Gabi", "Gabi"), ("le", "CL.DAT"), ("llegaron", "arrived.PL"), ("dos", "two"), ("cartas", "letters"), ("de", "from"), ("Londres", "London")]
    glossedWords := [⟨[['A']], [['D', 'A', 'T']]⟩, ⟨[['G', 'a', 'b', 'i']], [['G', 'a', 'b', 'i']]⟩, ⟨[['l', 'e']], [['C', 'L', '.', 'D', 'A', 'T']]⟩, ⟨[['l', 'l', 'e', 'g', 'a', 'r', 'o', 'n']], [['a', 'r', 'r', 'i', 'v', 'e', 'd', '.', 'P', 'L']]⟩, ⟨[['d', 'o', 's']], [['t', 'w', 'o']]⟩, ⟨[['c', 'a', 'r', 't', 'a', 's']], [['l', 'e', 't', 't', 'e', 'r', 's']]⟩, ⟨[['d', 'e']], [['f', 'r', 'o', 'm']]⟩, ⟨[['L', 'o', 'n', 'd', 'r', 'e', 's']], [['L', 'o', 'n', 'd', 'o', 'n']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "llegar"), ("animate", "yes"), ("dative", "dp"), ("meaning", "recipient")] }

def ex_35 : Datum :=
  { id := "cuervo2003_35"
    source := ⟨"cuervo-2003", "(35)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Emilio le rompió la radio a Carolina."
    glossedTokens := [("Emilio", "Emilio"), ("le", "CL.DAT"), ("rompió", "broke"), ("la", "the"), ("radio", "radio"), ("a", "DAT"), ("Carolina", "Carolina")]
    glossedWords := [⟨[['E', 'm', 'i', 'l', 'i', 'o']], [['E', 'm', 'i', 'l', 'i', 'o']]⟩, ⟨[['l', 'e']], [['C', 'L', '.', 'D', 'A', 'T']]⟩, ⟨[['r', 'o', 'm', 'p', 'i', 'ó']], [['b', 'r', 'o', 'k', 'e']]⟩, ⟨[['l', 'a']], [['t', 'h', 'e']]⟩, ⟨[['r', 'a', 'd', 'i', 'o']], [['r', 'a', 'd', 'i', 'o']]⟩, ⟨[['a']], [['D', 'A', 'T']]⟩, ⟨[['C', 'a', 'r', 'o', 'l', 'i', 'n', 'a']], [['C', 'a', 'r', 'o', 'l', 'i', 'n', 'a']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "romperCausative"), ("animate", "yes"), ("dative", "dp"), ("meaning", "affected")] }

def ex_36 : Datum :=
  { id := "cuervo2003_36"
    source := ⟨"cuervo-2003", "(36)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A Carolina se le rompió la radio."
    glossedTokens := [("A", "DAT"), ("Carolina", "Carolina"), ("se", "SE"), ("le", "CL.DAT"), ("rompió", "broke"), ("la", "the"), ("radio", "radio")]
    glossedWords := [⟨[['A']], [['D', 'A', 'T']]⟩, ⟨[['C', 'a', 'r', 'o', 'l', 'i', 'n', 'a']], [['C', 'a', 'r', 'o', 'l', 'i', 'n', 'a']]⟩, ⟨[['s', 'e']], [['S', 'E']]⟩, ⟨[['l', 'e']], [['C', 'L', '.', 'D', 'A', 'T']]⟩, ⟨[['r', 'o', 'm', 'p', 'i', 'ó']], [['b', 'r', 'o', 'k', 'e']]⟩, ⟨[['l', 'a']], [['t', 'h', 'e']]⟩, ⟨[['r', 'a', 'd', 'i', 'o']], [['r', 'a', 'd', 'i', 'o']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "romperInchoative"), ("animate", "yes"), ("dative", "dp"), ("meaning", "affected")] }

def ex_37 : Datum :=
  { id := "cuervo2003_37"
    source := ⟨"cuervo-2003", "(37)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A Daniela no le gustan los gatos."
    glossedTokens := [("A", "DAT"), ("Daniela", "Daniela"), ("no", "not"), ("le", "CL.DAT"), ("gustan", "like.PL"), ("los", "the"), ("gatos", "cats")]
    glossedWords := [⟨[['A']], [['D', 'A', 'T']]⟩, ⟨[['D', 'a', 'n', 'i', 'e', 'l', 'a']], [['D', 'a', 'n', 'i', 'e', 'l', 'a']]⟩, ⟨[['n', 'o']], [['n', 'o', 't']]⟩, ⟨[['l', 'e']], [['C', 'L', '.', 'D', 'A', 'T']]⟩, ⟨[['g', 'u', 's', 't', 'a', 'n']], [['l', 'i', 'k', 'e', '.', 'P', 'L']]⟩, ⟨[['l', 'o', 's']], [['t', 'h', 'e']]⟩, ⟨[['g', 'a', 't', 'o', 's']], [['c', 'a', 't', 's']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "gustar"), ("animate", "yes"), ("dative", "dp"), ("meaning", "experiencer")] }

def ex_38 : Datum :=
  { id := "cuervo2003_38"
    source := ⟨"cuervo-2003", "(38)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A Laura le sobraron veinte pesos."
    glossedTokens := [("A", "DAT"), ("Laura", "Laura"), ("le", "CL.DAT"), ("sobraron", "were.extra.PL"), ("veinte", "twenty"), ("pesos", "pesos")]
    glossedWords := [⟨[['A']], [['D', 'A', 'T']]⟩, ⟨[['L', 'a', 'u', 'r', 'a']], [['L', 'a', 'u', 'r', 'a']]⟩, ⟨[['l', 'e']], [['C', 'L', '.', 'D', 'A', 'T']]⟩, ⟨[['s', 'o', 'b', 'r', 'a', 'r', 'o', 'n']], [['w', 'e', 'r', 'e', '.', 'e', 'x', 't', 'r', 'a', '.', 'P', 'L']]⟩, ⟨[['v', 'e', 'i', 'n', 't', 'e']], [['t', 'w', 'e', 'n', 't', 'y']]⟩, ⟨[['p', 'e', 's', 'o', 's']], [['p', 'e', 's', 'o', 's']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "sobrar"), ("animate", "yes"), ("dative", "dp"), ("meaning", "possessor")] }

def ex_39a : Datum :=
  { id := "cuervo2003_39a"
    source := ⟨"cuervo-2003", "(39a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Juanita ya le camina."
    glossedTokens := [("Juanita", "Juanita"), ("ya", "already"), ("le", "CL.DAT"), ("camina", "walks")]
    glossedWords := [⟨[['J', 'u', 'a', 'n', 'i', 't', 'a']], [['J', 'u', 'a', 'n', 'i', 't', 'a']]⟩, ⟨[['y', 'a']], [['a', 'l', 'r', 'e', 'a', 'd', 'y']]⟩, ⟨[['l', 'e']], [['C', 'L', '.', 'D', 'A', 'T']]⟩, ⟨[['c', 'a', 'm', 'i', 'n', 'a']], [['w', 'a', 'l', 'k', 's']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "caminar"), ("animate", "yes"), ("dative", "clitic"), ("meaning", "ethical")] }

def ex_49 : Datum :=
  { id := "cuervo2003_49"
    source := ⟨"cuervo-2003", "(49)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A Daniela le sucedió algo buenísimo."
    glossedTokens := [("A", "DAT"), ("Daniela", "Daniela"), ("le", "CL.DAT"), ("sucedió", "happened"), ("algo", "something.NOM"), ("buenísimo", "very.good")]
    glossedWords := [⟨[['A']], [['D', 'A', 'T']]⟩, ⟨[['D', 'a', 'n', 'i', 'e', 'l', 'a']], [['D', 'a', 'n', 'i', 'e', 'l', 'a']]⟩, ⟨[['l', 'e']], [['C', 'L', '.', 'D', 'A', 'T']]⟩, ⟨[['s', 'u', 'c', 'e', 'd', 'i', 'ó']], [['h', 'a', 'p', 'p', 'e', 'n', 'e', 'd']]⟩, ⟨[['a', 'l', 'g', 'o']], [['s', 'o', 'm', 'e', 't', 'h', 'i', 'n', 'g', '.', 'N', 'O', 'M']]⟩, ⟨[['b', 'u', 'e', 'n', 'í', 's', 'i', 'm', 'o']], [['v', 'e', 'r', 'y', '.', 'g', 'o', 'o', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "suceder"), ("animate", "yes"), ("dative", "dp"), ("meaning", "experiencer")] }

def ex_54a : Datum :=
  { id := "cuervo2003_54a"
    source := ⟨"cuervo-2003", "(54a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A las plantas les salieron flores."
    glossedTokens := [("A", "DAT"), ("las", "the"), ("plantas", "plants"), ("les", "CL.DAT.PL"), ("salieron", "came.out"), ("flores", "flowers.NOM")]
    glossedWords := [⟨[['A']], [['D', 'A', 'T']]⟩, ⟨[['l', 'a', 's']], [['t', 'h', 'e']]⟩, ⟨[['p', 'l', 'a', 'n', 't', 'a', 's']], [['p', 'l', 'a', 'n', 't', 's']]⟩, ⟨[['l', 'e', 's']], [['C', 'L', '.', 'D', 'A', 'T', '.', 'P', 'L']]⟩, ⟨[['s', 'a', 'l', 'i', 'e', 'r', 'o', 'n']], [['c', 'a', 'm', 'e', '.', 'o', 'u', 't']]⟩, ⟨[['f', 'l', 'o', 'r', 'e', 's']], [['f', 'l', 'o', 'w', 'e', 'r', 's', '.', 'N', 'O', 'M']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "salir"), ("animate", "no"), ("dative", "dp"), ("meaning", "possessor")] }

def ex_55 : Datum :=
  { id := "cuervo2003_55"
    source := ⟨"cuervo-2003", "(55)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Al tintorero se le quemaron los pantalones de Carolina."
    glossedTokens := [("Al", "DAT.the"), ("tintorero", "dry.cleaner"), ("se", "SE"), ("le", "CL.DAT"), ("quemaron", "burnt.PL"), ("los", "the"), ("pantalones", "trousers"), ("de", "of"), ("Carolina", "Carolina")]
    glossedWords := [⟨[['A', 'l']], [['D', 'A', 'T', '.', 't', 'h', 'e']]⟩, ⟨[['t', 'i', 'n', 't', 'o', 'r', 'e', 'r', 'o']], [['d', 'r', 'y', '.', 'c', 'l', 'e', 'a', 'n', 'e', 'r']]⟩, ⟨[['s', 'e']], [['S', 'E']]⟩, ⟨[['l', 'e']], [['C', 'L', '.', 'D', 'A', 'T']]⟩, ⟨[['q', 'u', 'e', 'm', 'a', 'r', 'o', 'n']], [['b', 'u', 'r', 'n', 't', '.', 'P', 'L']]⟩, ⟨[['l', 'o', 's']], [['t', 'h', 'e']]⟩, ⟨[['p', 'a', 'n', 't', 'a', 'l', 'o', 'n', 'e', 's']], [['t', 'r', 'o', 'u', 's', 'e', 'r', 's']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['C', 'a', 'r', 'o', 'l', 'i', 'n', 'a']], [['C', 'a', 'r', 'o', 'l', 'i', 'n', 'a']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("affected", .acceptable), ("unintentional responsibility", .acceptable)]
    paperFeatures := [("predicate", "quemarInchoative"), ("animate", "yes"), ("dative", "dp"), ("meaning", "affected")] }

def ex_60 : Datum :=
  { id := "cuervo2003_60"
    source := ⟨"cuervo-2003", "(60)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A la mesa se le rompieron dos patas."
    glossedTokens := [("A", "DAT"), ("la", "the"), ("mesa", "table"), ("se", "SE"), ("le", "CL.DAT"), ("rompieron", "broke"), ("dos", "two"), ("patas", "legs")]
    glossedWords := [⟨[['A']], [['D', 'A', 'T']]⟩, ⟨[['l', 'a']], [['t', 'h', 'e']]⟩, ⟨[['m', 'e', 's', 'a']], [['t', 'a', 'b', 'l', 'e']]⟩, ⟨[['s', 'e']], [['S', 'E']]⟩, ⟨[['l', 'e']], [['C', 'L', '.', 'D', 'A', 'T']]⟩, ⟨[['r', 'o', 'm', 'p', 'i', 'e', 'r', 'o', 'n']], [['b', 'r', 'o', 'k', 'e']]⟩, ⟨[['d', 'o', 's']], [['t', 'w', 'o']]⟩, ⟨[['p', 'a', 't', 'a', 's']], [['l', 'e', 'g', 's']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("affected", .acceptable), ("unintentional responsibility", .ungrammatical)]
    paperFeatures := [("predicate", "romperInchoative"), ("animate", "no"), ("dative", "dp"), ("meaning", "affected")] }

def ex_66 : Datum :=
  { id := "cuervo2003_66"
    source := ⟨"cuervo-2003", "(66)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Hugo le corrió a Vicki."
    glossedTokens := [("Hugo", "Hugo"), ("le", "CL.DAT"), ("corrió", "ran"), ("a", "DAT"), ("Vicki", "Vicki")]
    glossedWords := [⟨[['H', 'u', 'g', 'o']], [['H', 'u', 'g', 'o']]⟩, ⟨[['l', 'e']], [['C', 'L', '.', 'D', 'A', 'T']]⟩, ⟨[['c', 'o', 'r', 'r', 'i', 'ó']], [['r', 'a', 'n']]⟩, ⟨[['a']], [['D', 'A', 'T']]⟩, ⟨[['V', 'i', 'c', 'k', 'i']], [['V', 'i', 'c', 'k', 'i']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "correr"), ("animate", "yes"), ("dative", "dp")] }

def ex_67a : Datum :=
  { id := "cuervo2003_67a"
    source := ⟨"cuervo-2003", "(67a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Hugo le corrió una carrera a Vicki."
    glossedTokens := [("Hugo", "Hugo"), ("le", "CL.DAT"), ("corrió", "ran"), ("una", "a"), ("carrera", "race"), ("a", "DAT"), ("Vicki", "Vicki")]
    glossedWords := [⟨[['H', 'u', 'g', 'o']], [['H', 'u', 'g', 'o']]⟩, ⟨[['l', 'e']], [['C', 'L', '.', 'D', 'A', 'T']]⟩, ⟨[['c', 'o', 'r', 'r', 'i', 'ó']], [['r', 'a', 'n']]⟩, ⟨[['u', 'n', 'a']], [['a']]⟩, ⟨[['c', 'a', 'r', 'r', 'e', 'r', 'a']], [['r', 'a', 'c', 'e']]⟩, ⟨[['a']], [['D', 'A', 'T']]⟩, ⟨[['V', 'i', 'c', 'k', 'i']], [['V', 'i', 'c', 'k', 'i']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "correrTransitive"), ("animate", "yes"), ("dative", "dp")] }

def ex_78 : Datum :=
  { id := "cuervo2003_78"
    source := ⟨"cuervo-2003", "(78)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Juanita ya le camina a él."
    glossedTokens := [("Juanita", "Juanita"), ("ya", "already"), ("le", "CL.DAT"), ("camina", "walks"), ("a", "DAT"), ("él", "him")]
    glossedWords := [⟨[['J', 'u', 'a', 'n', 'i', 't', 'a']], [['J', 'u', 'a', 'n', 'i', 't', 'a']]⟩, ⟨[['y', 'a']], [['a', 'l', 'r', 'e', 'a', 'd', 'y']]⟩, ⟨[['l', 'e']], [['C', 'L', '.', 'D', 'A', 'T']]⟩, ⟨[['c', 'a', 'm', 'i', 'n', 'a']], [['w', 'a', 'l', 'k', 's']]⟩, ⟨[['a']], [['D', 'A', 'T']]⟩, ⟨[['é', 'l']], [['h', 'i', 'm']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "caminar"), ("animate", "yes"), ("dative", "dp")] }

def ex_90a : Datum :=
  { id := "cuervo2003_90a"
    source := ⟨"cuervo-2003", "(90a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Emilio le abrió las puertas a Carolina."
    glossedTokens := [("Emilio", "Emilio"), ("le", "CL.DAT"), ("abrió", "opened"), ("las", "the"), ("puertas", "doors"), ("a", "DAT"), ("Carolina", "Carolina")]
    glossedWords := [⟨[['E', 'm', 'i', 'l', 'i', 'o']], [['E', 'm', 'i', 'l', 'i', 'o']]⟩, ⟨[['l', 'e']], [['C', 'L', '.', 'D', 'A', 'T']]⟩, ⟨[['a', 'b', 'r', 'i', 'ó']], [['o', 'p', 'e', 'n', 'e', 'd']]⟩, ⟨[['l', 'a', 's']], [['t', 'h', 'e']]⟩, ⟨[['p', 'u', 'e', 'r', 't', 'a', 's']], [['d', 'o', 'o', 'r', 's']]⟩, ⟨[['a']], [['D', 'A', 'T']]⟩, ⟨[['C', 'a', 'r', 'o', 'l', 'i', 'n', 'a']], [['C', 'a', 'r', 'o', 'l', 'i', 'n', 'a']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "abrirCausative"), ("animate", "yes"), ("dative", "dp"), ("meaning", "affected")] }

def ex_90b : Datum :=
  { id := "cuervo2003_90b"
    source := ⟨"cuervo-2003", "(90b)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A Carolina se le abrió la puerta."
    glossedTokens := [("A", "DAT"), ("Carolina", "Carolina"), ("se", "CL.REF"), ("le", "CL.DAT"), ("abrió", "opened"), ("la", "the"), ("puerta", "door")]
    glossedWords := [⟨[['A']], [['D', 'A', 'T']]⟩, ⟨[['C', 'a', 'r', 'o', 'l', 'i', 'n', 'a']], [['C', 'a', 'r', 'o', 'l', 'i', 'n', 'a']]⟩, ⟨[['s', 'e']], [['C', 'L', '.', 'R', 'E', 'F']]⟩, ⟨[['l', 'e']], [['C', 'L', '.', 'D', 'A', 'T']]⟩, ⟨[['a', 'b', 'r', 'i', 'ó']], [['o', 'p', 'e', 'n', 'e', 'd']]⟩, ⟨[['l', 'a']], [['t', 'h', 'e']]⟩, ⟨[['p', 'u', 'e', 'r', 't', 'a']], [['d', 'o', 'o', 'r']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "abrirInchoative"), ("animate", "yes"), ("dative", "dp"), ("meaning", "affected")] }

def ex_85ap : Datum :=
  { id := "cuervo2003_85ap"
    source := ⟨"cuervo-2003", "(85a')"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John passed Mary the ring."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "pass"), ("animate", "yes"), ("dative", "dp"), ("meaning", "recipient")] }

def ex_88 : Datum :=
  { id := "cuervo2003_88"
    source := ⟨"cuervo-2003", "(88)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Daniel opened Stephanie the door."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "openCausative"), ("animate", "yes"), ("dative", "dp")] }

def ex_89a : Datum :=
  { id := "cuervo2003_89a"
    source := ⟨"cuervo-2003", "(89a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The door opened Stephanie."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "openInchoative"), ("animate", "yes"), ("dative", "dp")] }

def ex_92b : Datum :=
  { id := "cuervo2003_92b"
    source := ⟨"cuervo-2003", "(92b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Two letters arrived Daniel."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "arrive"), ("animate", "yes"), ("dative", "dp")] }

def all : List Datum := [ex_29a, ex_30, ex_31, ex_32, ex_33, ex_34, ex_35, ex_36, ex_37, ex_38, ex_39a, ex_49, ex_54a, ex_55, ex_60, ex_66, ex_67a, ex_78, ex_90a, ex_90b, ex_85ap, ex_88, ex_89a, ex_92b]

end Cuervo2003.Examples
