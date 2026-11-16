module

public import Linglib.Data.Examples.Schema

/-!
# `LeBruynDeSwart2022` — typed example data

Auto-generated from `Linglib/Data/Examples/LeBruynDeSwart2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace LeBruynDeSwart2022.Examples`.
-/

@[expose] public section

namespace LeBruynDeSwart2022.Examples

def boeken_niet_uitgelezen : Datum :=
  { id := "lebruyndeswart2022_boeken_niet_uitgelezen"
    source := ⟨"le-bruyn-de-swart-2022", "(35)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Het klopt dat ik boeken niet heb uitgelezen. Dan begon ik er aan maar kwam ik er achter dat ik het toch niet leuk vond."
    glossedTokens := [("Het", "it"), ("klopt", "knocks"), ("dat", "that"), ("ik", "I"), ("boeken", "books"), ("niet", "not"), ("heb", "have"), ("uitgelezen", "UIT.read"), ("Dan", "then"), ("begon", "began"), ("ik", "I"), ("er", "ER"), ("aan", "on"), ("maar", "but"), ("kwam", "came"), ("ik", "I"), ("er", "ER"), ("achter", "after"), ("dat", "that"), ("ik", "I"), ("het", "it"), ("toch", "after_all"), ("niet", "not"), ("leuk", "fun"), ("vond", "found")]
    glossedWords := [⟨[['H', 'e', 't']], [['i', 't']]⟩, ⟨[['k', 'l', 'o', 'p', 't']], [['k', 'n', 'o', 'c', 'k', 's']]⟩, ⟨[['d', 'a', 't']], [['t', 'h', 'a', 't']]⟩, ⟨[['i', 'k']], [['I']]⟩, ⟨[['b', 'o', 'e', 'k', 'e', 'n']], [['b', 'o', 'o', 'k', 's']]⟩, ⟨[['n', 'i', 'e', 't']], [['n', 'o', 't']]⟩, ⟨[['h', 'e', 'b']], [['h', 'a', 'v', 'e']]⟩, ⟨[['u', 'i', 't', 'g', 'e', 'l', 'e', 'z', 'e', 'n']], [['U', 'I', 'T', '.', 'r', 'e', 'a', 'd']]⟩, ⟨[['D', 'a', 'n']], [['t', 'h', 'e', 'n']]⟩, ⟨[['b', 'e', 'g', 'o', 'n']], [['b', 'e', 'g', 'a', 'n']]⟩, ⟨[['i', 'k']], [['I']]⟩, ⟨[['e', 'r']], [['E', 'R']]⟩, ⟨[['a', 'a', 'n']], [['o', 'n']]⟩, ⟨[['m', 'a', 'a', 'r']], [['b', 'u', 't']]⟩, ⟨[['k', 'w', 'a', 'm']], [['c', 'a', 'm', 'e']]⟩, ⟨[['i', 'k']], [['I']]⟩, ⟨[['e', 'r']], [['E', 'R']]⟩, ⟨[['a', 'c', 'h', 't', 'e', 'r']], [['a', 'f', 't', 'e', 'r']]⟩, ⟨[['d', 'a', 't']], [['t', 'h', 'a', 't']]⟩, ⟨[['i', 'k']], [['I']]⟩, ⟨[['h', 'e', 't']], [['i', 't']]⟩, ⟨[['t', 'o', 'c', 'h']], [['a', 'f', 't', 'e', 'r', '_', 'a', 'l', 'l']]⟩, ⟨[['n', 'i', 'e', 't']], [['n', 'o', 't']]⟩, ⟨[['l', 'e', 'u', 'k']], [['f', 'u', 'n']]⟩, ⟨[['v', 'o', 'n', 'd']], [['f', 'o', 'u', 'n', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("wide_scope", .acceptable), ("narrow_scope", .unacceptable)]
    paperFeatures := [("position", "scrambled")] }

def boeken_gehaat : Datum :=
  { id := "lebruyndeswart2022_boeken_gehaat"
    source := ⟨"le-bruyn-de-swart-2022", "(36b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "dat ik boeken altijd gehaat heb"
    glossedTokens := [("dat", "that"), ("ik", "I"), ("boeken", "books"), ("altijd", "always"), ("gehaat", "hated"), ("heb", "have")]
    glossedWords := [⟨[['d', 'a', 't']], [['t', 'h', 'a', 't']]⟩, ⟨[['i', 'k']], [['I']]⟩, ⟨[['b', 'o', 'e', 'k', 'e', 'n']], [['b', 'o', 'o', 'k', 's']]⟩, ⟨[['a', 'l', 't', 'i', 'j', 'd']], [['a', 'l', 'w', 'a', 'y', 's']]⟩, ⟨[['g', 'e', 'h', 'a', 'a', 't']], [['h', 'a', 't', 'e', 'd']]⟩, ⟨[['h', 'e', 'b']], [['h', 'a', 'v', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("kind_reference", .acceptable)]
    paperFeatures := [("position", "scrambled")] }

def all : List Datum := [boeken_niet_uitgelezen, boeken_gehaat]

end LeBruynDeSwart2022.Examples
