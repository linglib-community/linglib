module

public import Linglib.Data.Examples.Schema

/-!
# `Schwarzer2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Schwarzer2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Schwarzer2026.Examples`.
-/

@[expose] public section

namespace Schwarzer2026.Examples

def ex11a : Datum :=
  { id := "schwarzer2026_ex11a"
    source := ⟨"schwarzer-2026", "(11a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Stadt beendet zum Jahreswechsel dass für Neugeborene ein Baum gepflanzt wird."
    glossedTokens := [("Die", "the"), ("Stadt", "city"), ("beendet", "ends"), ("zum", "at.the"), ("Jahreswechsel", "year.turn"), ("dass", "that"), ("für", "for"), ("Neugeborene", "newborns"), ("ein", "a"), ("Baum", "tree"), ("gepflanzt", "planted"), ("wird", "AUX.PASS")]
    glossedWords := [⟨[['D', 'i', 'e']], [['t', 'h', 'e']]⟩, ⟨[['S', 't', 'a', 'd', 't']], [['c', 'i', 't', 'y']]⟩, ⟨[['b', 'e', 'e', 'n', 'd', 'e', 't']], [['e', 'n', 'd', 's']]⟩, ⟨[['z', 'u', 'm']], [['a', 't', '.', 't', 'h', 'e']]⟩, ⟨[['J', 'a', 'h', 'r', 'e', 's', 'w', 'e', 'c', 'h', 's', 'e', 'l']], [['y', 'e', 'a', 'r', '.', 't', 'u', 'r', 'n']]⟩, ⟨[['d', 'a', 's', 's']], [['t', 'h', 'a', 't']]⟩, ⟨[['f', 'ü', 'r']], [['f', 'o', 'r']]⟩, ⟨[['N', 'e', 'u', 'g', 'e', 'b', 'o', 'r', 'e', 'n', 'e']], [['n', 'e', 'w', 'b', 'o', 'r', 'n', 's']]⟩, ⟨[['e', 'i', 'n']], [['a']]⟩, ⟨[['B', 'a', 'u', 'm']], [['t', 'r', 'e', 'e']]⟩, ⟨[['g', 'e', 'p', 'f', 'l', 'a', 'n', 'z', 't']], [['p', 'l', 'a', 'n', 't', 'e', 'd']]⟩, ⟨[['w', 'i', 'r', 'd']], [['A', 'U', 'X', '.', 'P', 'A', 'S', 'S']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("verb", "beenden"), ("selectsCP", "no"), ("complement", "dass"), ("position", "postverbal")] }

def ex11b : Datum :=
  { id := "schwarzer2026_ex11b"
    source := ⟨"schwarzer-2026", "(11b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Stadt beendet zum Jahreswechsel die Überarbeitung des Nahverkehrskonzepts und dass für Neugeborene ein Baum gepflanzt wird."
    glossedTokens := [("Die", "the"), ("Stadt", "city"), ("beendet", "ends"), ("zum", "at.the"), ("Jahreswechsel", "year.turn"), ("die", "the"), ("Überarbeitung", "revision"), ("des", "of.the"), ("Nahverkehrskonzepts", "public.transport.plan"), ("und", "and"), ("dass", "that"), ("für", "for"), ("Neugeborene", "newborns"), ("ein", "a"), ("Baum", "tree"), ("gepflanzt", "planted"), ("wird", "AUX.PASS")]
    glossedWords := [⟨[['D', 'i', 'e']], [['t', 'h', 'e']]⟩, ⟨[['S', 't', 'a', 'd', 't']], [['c', 'i', 't', 'y']]⟩, ⟨[['b', 'e', 'e', 'n', 'd', 'e', 't']], [['e', 'n', 'd', 's']]⟩, ⟨[['z', 'u', 'm']], [['a', 't', '.', 't', 'h', 'e']]⟩, ⟨[['J', 'a', 'h', 'r', 'e', 's', 'w', 'e', 'c', 'h', 's', 'e', 'l']], [['y', 'e', 'a', 'r', '.', 't', 'u', 'r', 'n']]⟩, ⟨[['d', 'i', 'e']], [['t', 'h', 'e']]⟩, ⟨[['Ü', 'b', 'e', 'r', 'a', 'r', 'b', 'e', 'i', 't', 'u', 'n', 'g']], [['r', 'e', 'v', 'i', 's', 'i', 'o', 'n']]⟩, ⟨[['d', 'e', 's']], [['o', 'f', '.', 't', 'h', 'e']]⟩, ⟨[['N', 'a', 'h', 'v', 'e', 'r', 'k', 'e', 'h', 'r', 's', 'k', 'o', 'n', 'z', 'e', 'p', 't', 's']], [['p', 'u', 'b', 'l', 'i', 'c', '.', 't', 'r', 'a', 'n', 's', 'p', 'o', 'r', 't', '.', 'p', 'l', 'a', 'n']]⟩, ⟨[['u', 'n', 'd']], [['a', 'n', 'd']]⟩, ⟨[['d', 'a', 's', 's']], [['t', 'h', 'a', 't']]⟩, ⟨[['f', 'ü', 'r']], [['f', 'o', 'r']]⟩, ⟨[['N', 'e', 'u', 'g', 'e', 'b', 'o', 'r', 'e', 'n', 'e']], [['n', 'e', 'w', 'b', 'o', 'r', 'n', 's']]⟩, ⟨[['e', 'i', 'n']], [['a']]⟩, ⟨[['B', 'a', 'u', 'm']], [['t', 'r', 'e', 'e']]⟩, ⟨[['g', 'e', 'p', 'f', 'l', 'a', 'n', 'z', 't']], [['p', 'l', 'a', 'n', 't', 'e', 'd']]⟩, ⟨[['w', 'i', 'r', 'd']], [['A', 'U', 'X', '.', 'P', 'A', 'S', 'S']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("verb", "beenden"), ("selectsCP", "no"), ("complement", "coord"), ("position", "postverbal"), ("order", "dpFirst")] }

def ex12a : Datum :=
  { id := "schwarzer2026_ex12a"
    source := ⟨"schwarzer-2026", "(12a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Stadt veranlasst zum Jahreswechsel dass für Neugeborene ein Baum gepflanzt wird."
    glossedTokens := [("Die", "the"), ("Stadt", "city"), ("veranlasst", "starts"), ("zum", "at.the"), ("Jahreswechsel", "year.turn"), ("dass", "that"), ("für", "for"), ("Neugeborene", "newborns"), ("ein", "a"), ("Baum", "tree"), ("gepflanzt", "planted"), ("wird", "AUX.PASS")]
    glossedWords := [⟨[['D', 'i', 'e']], [['t', 'h', 'e']]⟩, ⟨[['S', 't', 'a', 'd', 't']], [['c', 'i', 't', 'y']]⟩, ⟨[['v', 'e', 'r', 'a', 'n', 'l', 'a', 's', 's', 't']], [['s', 't', 'a', 'r', 't', 's']]⟩, ⟨[['z', 'u', 'm']], [['a', 't', '.', 't', 'h', 'e']]⟩, ⟨[['J', 'a', 'h', 'r', 'e', 's', 'w', 'e', 'c', 'h', 's', 'e', 'l']], [['y', 'e', 'a', 'r', '.', 't', 'u', 'r', 'n']]⟩, ⟨[['d', 'a', 's', 's']], [['t', 'h', 'a', 't']]⟩, ⟨[['f', 'ü', 'r']], [['f', 'o', 'r']]⟩, ⟨[['N', 'e', 'u', 'g', 'e', 'b', 'o', 'r', 'e', 'n', 'e']], [['n', 'e', 'w', 'b', 'o', 'r', 'n', 's']]⟩, ⟨[['e', 'i', 'n']], [['a']]⟩, ⟨[['B', 'a', 'u', 'm']], [['t', 'r', 'e', 'e']]⟩, ⟨[['g', 'e', 'p', 'f', 'l', 'a', 'n', 'z', 't']], [['p', 'l', 'a', 'n', 't', 'e', 'd']]⟩, ⟨[['w', 'i', 'r', 'd']], [['A', 'U', 'X', '.', 'P', 'A', 'S', 'S']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("verb", "veranlassen"), ("selectsCP", "yes"), ("complement", "dass"), ("position", "postverbal")] }

def ex12b : Datum :=
  { id := "schwarzer2026_ex12b"
    source := ⟨"schwarzer-2026", "(12b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Stadt veranlasst zum Jahreswechsel die Überarbeitung des Nahverkehrskonzepts und dass für Neugeborene ein Baum gepflanzt wird."
    glossedTokens := [("Die", "the"), ("Stadt", "city"), ("veranlasst", "starts"), ("zum", "at.the"), ("Jahreswechsel", "year.turn"), ("die", "the"), ("Überarbeitung", "revision"), ("des", "of.the"), ("Nahverkehrskonzepts", "public.transport.plan"), ("und", "and"), ("dass", "that"), ("für", "for"), ("Neugeborene", "newborns"), ("ein", "a"), ("Baum", "tree"), ("gepflanzt", "planted"), ("wird", "AUX.PASS")]
    glossedWords := [⟨[['D', 'i', 'e']], [['t', 'h', 'e']]⟩, ⟨[['S', 't', 'a', 'd', 't']], [['c', 'i', 't', 'y']]⟩, ⟨[['v', 'e', 'r', 'a', 'n', 'l', 'a', 's', 's', 't']], [['s', 't', 'a', 'r', 't', 's']]⟩, ⟨[['z', 'u', 'm']], [['a', 't', '.', 't', 'h', 'e']]⟩, ⟨[['J', 'a', 'h', 'r', 'e', 's', 'w', 'e', 'c', 'h', 's', 'e', 'l']], [['y', 'e', 'a', 'r', '.', 't', 'u', 'r', 'n']]⟩, ⟨[['d', 'i', 'e']], [['t', 'h', 'e']]⟩, ⟨[['Ü', 'b', 'e', 'r', 'a', 'r', 'b', 'e', 'i', 't', 'u', 'n', 'g']], [['r', 'e', 'v', 'i', 's', 'i', 'o', 'n']]⟩, ⟨[['d', 'e', 's']], [['o', 'f', '.', 't', 'h', 'e']]⟩, ⟨[['N', 'a', 'h', 'v', 'e', 'r', 'k', 'e', 'h', 'r', 's', 'k', 'o', 'n', 'z', 'e', 'p', 't', 's']], [['p', 'u', 'b', 'l', 'i', 'c', '.', 't', 'r', 'a', 'n', 's', 'p', 'o', 'r', 't', '.', 'p', 'l', 'a', 'n']]⟩, ⟨[['u', 'n', 'd']], [['a', 'n', 'd']]⟩, ⟨[['d', 'a', 's', 's']], [['t', 'h', 'a', 't']]⟩, ⟨[['f', 'ü', 'r']], [['f', 'o', 'r']]⟩, ⟨[['N', 'e', 'u', 'g', 'e', 'b', 'o', 'r', 'e', 'n', 'e']], [['n', 'e', 'w', 'b', 'o', 'r', 'n', 's']]⟩, ⟨[['e', 'i', 'n']], [['a']]⟩, ⟨[['B', 'a', 'u', 'm']], [['t', 'r', 'e', 'e']]⟩, ⟨[['g', 'e', 'p', 'f', 'l', 'a', 'n', 'z', 't']], [['p', 'l', 'a', 'n', 't', 'e', 'd']]⟩, ⟨[['w', 'i', 'r', 'd']], [['A', 'U', 'X', '.', 'P', 'A', 'S', 'S']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("verb", "veranlassen"), ("selectsCP", "yes"), ("complement", "coord"), ("position", "postverbal"), ("order", "dpFirst")] }

def all : List Datum := [ex11a, ex11b, ex12a, ex12b]

end Schwarzer2026.Examples
