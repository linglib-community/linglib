module

public import Linglib.Syntax.Negation
public import Linglib.Morphology.Morph

/-!
# Tigrinya Negation

Tigrinya negates a declarative verbal clause with the circumfix
*ʔaj-…-(ɨ)n* around the inflected verb (*ʔaj-Ø-ts'awɛtɨ-n* 'I do not
play'); WALS codes the language as obligatory double negation. The
suffix is confined to root declaratives, *ʔɨlu*-complements and the
negative future: relative, subjunctive and imperative clauses take the
prefix alone, in its post-prefixal allomorph *ɛj-* (*z-ɛj-nbɨb* 'that I
do not read').

## References

* [cacchioli-2026], ch. 5
* [dryer-haspelmath-2013], ch. 112A, 143A, 144A
-/

@[expose] public section

open Morphology Negation

namespace Tigrinya.Negation

/-- The negative prefix *ʔaj-*. -/
def aj : Morph := .pref "ʔaj"

/-- *ɛj-*, the allomorph of `aj` after *zɨ-* and *kɨ-*: the glottal stop
drops and the vowel changes. -/
def ej : Morph := .pref "ɛj"

/-- The negative suffix *-(ɨ)n*, with epenthetic *ɨ* after a consonant. -/
def n : Morph := .suff "n"

/-- *ʔaj-…-(ɨ)n* — the standard-negation circumfix. -/
def circumfix : Marker where
  pieces := [[aj], [n]]

end Tigrinya.Negation
