/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Morph

/-!
# Classifiers

A classifier is a morpheme that accompanies a noun in some construction and is chosen by the
noun. A numeral classifier stands next to a numeral or quantifier, as a free form in Mandarin
*sān ge rén* 'three CL person' and as a suffix on the numeral in Japanese *san-nin* 'three-CL'.
This file defines the lexical entry of a classifier.

## Main definitions

* `Classifier`: the lexical entry, a morph with its spelling in a native script and its gloss.

## Implementation notes

The entry records neither the nouns the classifier counts nor a semantic class. The choice of
classifier is made by the noun, so a noun's entry lists the classifiers that count it, and a
grouping of classifiers by animacy, shape or function is an analysis of a whole inventory.

Two classifiers of one language can share a form, as Japanese *-ken* 軒 for buildings and *-ken*
件 for incidents do, and they are then distinct entries by their spelling in the native script.

## References

* [aikhenvald-2000]
-/

@[expose] public section

open Morphology (Morph)

/-- A classifier lexical entry records its morph, which gives its attachment kind and its form (a
romanization where the language has a native script), its spelling in that script, and its
gloss. -/
structure Classifier extends Morph where
  /-- The spelling in the native script. -/
  script : Option String := none
  /-- The gloss. -/
  gloss : String := "CL"
  deriving DecidableEq, Repr
