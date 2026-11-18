module

public import Linglib.Data.Examples.Schema

/-!
# `AbramskySadrzadeh2014` — typed example data

Auto-generated from `Linglib/Data/Examples/AbramskySadrzadeh2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AbramskySadrzadeh2014.Examples`.
-/

@[expose] public section

namespace AbramskySadrzadeh2014.Examples

def donkey : Datum :=
  { id := "abramskysadrzadeh2014_donkey"
    source := ⟨"abramsky-sadrzadeh-2014", "§1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If a farmer owns a donkey, he beats it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "donkey anaphora")] }

def drt_resolved : Datum :=
  { id := "abramskysadrzadeh2014_drt_resolved"
    source := ⟨"abramsky-sadrzadeh-2014", "§3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John owns a donkey. He beats it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("resolution", "full"), ("unification", "v = x, w = y")] }

def drt_partial : Datum :=
  { id := "abramskysadrzadeh2014_drt_partial"
    source := ⟨"abramsky-sadrzadeh-2014", "§3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John does not own a donkey. He beats it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("it = the donkey", .unacceptable)]
    paperFeatures := [("resolution", "partial"), ("unification", "v = x")] }

def ex1 : Datum :=
  { id := "abramskysadrzadeh2014_ex1"
    source := ⟨"abramsky-sadrzadeh-2014", "example 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John sleeps. He snores."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("cover", "x ↦ z ↤ y"), ("gluing", "{John(z), sleeps(z), snores(z)}")] }

def ex2 : Datum :=
  { id := "abramskysadrzadeh2014_ex2"
    source := ⟨"abramsky-sadrzadeh-2014", "example 2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John beats his donkey."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("cover", "x ↦ a, y ↦ b, u ↦ a, v ↦ b"), ("gluing", "{John(a), donkey(b), owns(a, b), beats(a, b)}")] }

def ex3 : Datum :=
  { id := "abramskysadrzadeh2014_ex3"
    source := ⟨"abramsky-sadrzadeh-2014", "example 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John owns a donkey. It is grey."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("it = the donkey", .acceptable), ("it = John", .unacceptable)]
    paperFeatures := [("resolution", "agreement"), ("cover", "x ↦ a, y ↦ b, z ↦ b")] }

def ex4 : Datum :=
  { id := "abramskysadrzadeh2014_ex4"
    source := ⟨"abramsky-sadrzadeh-2014", "example 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John put the cup on the plate. He broke it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("it = the cup", .acceptable), ("it = the plate", .acceptable)]
    paperFeatures := [("resolution", "ambiguous"), ("covers", "v ↦ y; v ↦ z")] }

def brother_happy : Datum :=
  { id := "abramskysadrzadeh2014_brother_happy"
    source := ⟨"abramsky-sadrzadeh-2014", "§5"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John has a brother. He is happy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("he = John", .acceptable), ("he = the brother", .acceptable)]
    paperFeatures := [("resolution", "preferential"), ("preferred", "he = John")] }

def brother_nice : Datum :=
  { id := "abramskysadrzadeh2014_brother_nice"
    source := ⟨"abramsky-sadrzadeh-2014", "§5"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John has a brother. He is nice."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("he = John", .acceptable), ("he = the brother", .acceptable)]
    paperFeatures := [("resolution", "preferential"), ("preferred", "he = the brother")] }

def cd : Datum :=
  { id := "abramskysadrzadeh2014_cd"
    source := ⟨"abramsky-sadrzadeh-2014", "§5"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John put a cd in the computer and copied it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("resolution", "preferential")] }

def jim : Datum :=
  { id := "abramskysadrzadeh2014_jim"
    source := ⟨"abramsky-sadrzadeh-2014", "§5"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John gave a donkey to Jim. James also gave him a dog."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("resolution", "preferential")] }

def bananas : Datum :=
  { id := "abramskysadrzadeh2014_bananas"
    source := ⟨"abramsky-sadrzadeh-2014", "§5 example"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John gave the bananas to the monkeys. They were ripe. They were cheeky."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("ripe bananas, cheeky bananas", .acceptable), ("ripe bananas, cheeky monkeys", .acceptable), ("ripe monkeys, cheeky bananas", .acceptable), ("ripe monkeys, cheeky monkeys", .acceptable)]
    paperFeatures := [("resolution", "preferential"), ("corpus", "British News, 200 million words"), ("selected", "ripe bananas, cheeky monkeys")] }

def all : List Datum := [donkey, drt_resolved, drt_partial, ex1, ex2, ex3, ex4, brother_happy, brother_nice, cd, jim, bananas]

end AbramskySadrzadeh2014.Examples
