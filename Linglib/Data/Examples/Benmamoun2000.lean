module

public import Linglib.Data.Examples.Schema

/-!
# `Benmamoun2000` — typed example data

Auto-generated from `Linglib/Data/Examples/Benmamoun2000.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Benmamoun2000.Examples`.
-/

@[expose] public section

namespace Benmamoun2000.Examples

def ex_1a : Datum :=
  { id := "benmamoun2000_1a"
    source := ⟨"benmamoun-2000", "p. 94, (1a)"⟩
    reportedIn := none
    language := "stan1318"
    primaryText := "ṭ-ṭullaab-u ya-drus-uu-n"
    glossedTokens := [("ṭ-ṭullaab-u", "the-students"), ("ya-drus-uu-n", "3m-study.mp-ind")]
    glossedWords := [⟨[['ṭ'], ['ṭ', 'u', 'l', 'l', 'a', 'a', 'b'], ['u']], [['t', 'h', 'e'], ['s', 't', 'u', 'd', 'e', 'n', 't', 's']]⟩, ⟨[['y', 'a'], ['d', 'r', 'u', 's'], ['u', 'u'], ['n']], [['3', 'm'], ['s', 't', 'u', 'd', 'y', '.', 'm', 'p'], ['i', 'n', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_1b : Datum :=
  { id := "benmamoun2000_1b"
    source := ⟨"benmamoun-2000", "p. 95, (1b)"⟩
    reportedIn := none
    language := "stan1318"
    primaryText := "ṭ-ṭullaab-u laa ya-drus-uu-n"
    glossedTokens := [("ṭ-ṭullaab-u", "the-students"), ("laa", "neg"), ("ya-drus-uu-n", "3m-study-mp-ind")]
    glossedWords := [⟨[['ṭ'], ['ṭ', 'u', 'l', 'l', 'a', 'a', 'b'], ['u']], [['t', 'h', 'e'], ['s', 't', 'u', 'd', 'e', 'n', 't', 's']]⟩, ⟨[['l', 'a', 'a']], [['n', 'e', 'g']]⟩, ⟨[['y', 'a'], ['d', 'r', 'u', 's'], ['u', 'u'], ['n']], [['3', 'm'], ['s', 't', 'u', 'd', 'y'], ['m', 'p'], ['i', 'n', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("affirmative", "benmamoun2000_1a")] }

def ex_2a : Datum :=
  { id := "benmamoun2000_2a"
    source := ⟨"benmamoun-2000", "p. 95, (2a)"⟩
    reportedIn := none
    language := "stan1318"
    primaryText := "ṭ-ṭullaab-u ðahab-uu"
    glossedTokens := [("ṭ-ṭullaab-u", "the-students-nom"), ("ðahab-uu", "go.past-3mp")]
    glossedWords := [⟨[['ṭ'], ['ṭ', 'u', 'l', 'l', 'a', 'a', 'b'], ['u']], [['t', 'h', 'e'], ['s', 't', 'u', 'd', 'e', 'n', 't', 's'], ['n', 'o', 'm']]⟩, ⟨[['ð', 'a', 'h', 'a', 'b'], ['u', 'u']], [['g', 'o', '.', 'p', 'a', 's', 't'], ['3', 'm', 'p']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_2b : Datum :=
  { id := "benmamoun2000_2b"
    source := ⟨"benmamoun-2000", "p. 95, (2b)"⟩
    reportedIn := none
    language := "stan1318"
    primaryText := "ṭ-ṭullaab-u lam ya-ðhab-uu"
    glossedTokens := [("ṭ-ṭullaab-u", "the-students-nom"), ("lam", "neg.past"), ("ya-ðhab-uu", "3m-go-mp")]
    glossedWords := [⟨[['ṭ'], ['ṭ', 'u', 'l', 'l', 'a', 'a', 'b'], ['u']], [['t', 'h', 'e'], ['s', 't', 'u', 'd', 'e', 'n', 't', 's'], ['n', 'o', 'm']]⟩, ⟨[['l', 'a', 'm']], [['n', 'e', 'g', '.', 'p', 'a', 's', 't']]⟩, ⟨[['y', 'a'], ['ð', 'h', 'a', 'b'], ['u', 'u']], [['3', 'm'], ['g', 'o'], ['m', 'p']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("affirmative", "benmamoun2000_2a")] }

def ex_3a : Datum :=
  { id := "benmamoun2000_3a"
    source := ⟨"benmamoun-2000", "p. 95, (3a)"⟩
    reportedIn := none
    language := "stan1318"
    primaryText := "ṭ-ṭullaab-u sa-ya-ðhab-uun"
    glossedTokens := [("ṭ-ṭullaab-u", "the-students"), ("sa-ya-ðhab-uun", "fut-3m-go-mp")]
    glossedWords := [⟨[['ṭ'], ['ṭ', 'u', 'l', 'l', 'a', 'a', 'b'], ['u']], [['t', 'h', 'e'], ['s', 't', 'u', 'd', 'e', 'n', 't', 's']]⟩, ⟨[['s', 'a'], ['y', 'a'], ['ð', 'h', 'a', 'b'], ['u', 'u', 'n']], [['f', 'u', 't'], ['3', 'm'], ['g', 'o'], ['m', 'p']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_3b : Datum :=
  { id := "benmamoun2000_3b"
    source := ⟨"benmamoun-2000", "p. 95, (3b)"⟩
    reportedIn := none
    language := "stan1318"
    primaryText := "ṭ-ṭullaab-u lan ya-ðhab-uu"
    glossedTokens := [("ṭ-ṭullaab-u", "the-students"), ("lan", "neg.fut"), ("ya-ðhab-uu", "3m-go-mp")]
    glossedWords := [⟨[['ṭ'], ['ṭ', 'u', 'l', 'l', 'a', 'a', 'b'], ['u']], [['t', 'h', 'e'], ['s', 't', 'u', 'd', 'e', 'n', 't', 's']]⟩, ⟨[['l', 'a', 'n']], [['n', 'e', 'g', '.', 'f', 'u', 't']]⟩, ⟨[['y', 'a'], ['ð', 'h', 'a', 'b'], ['u', 'u']], [['3', 'm'], ['g', 'o'], ['m', 'p']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("affirmative", "benmamoun2000_3a")] }

def all : List Datum := [ex_1a, ex_1b, ex_2a, ex_2b, ex_3a, ex_3b]

end Benmamoun2000.Examples
