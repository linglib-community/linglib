/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Data.UD.UPOS
public import Linglib.Morphology.Word.Features

/-!
# Word tokens

A word token is a surface form with its part of speech and its morphosyntactic features, the
unit of a Universal Dependencies annotation: the element that dependency relations connect, which
has morphological properties and enters into syntactic relations. It is a word in the
morphosyntactic sense, the unit that syntax treats as a word, which need not coincide with an
orthographic word or with a prosodic word, the unit that phonology treats as one: a clitic can
be a token of its own inside the prosodic word of its host.

## Main definitions

* `Morphology.Word`: a word token.

## Implementation notes

A token records no internal structure. The words of a sequence of morphs, its maximal runs of
morphs joined by affixation, are a separate construction on morphs, and a token's form is not
derived from one.

## References

* [de-marneffe-zeman-2021]
* [kalin-bjorkman-etal-2026]
-/

@[expose] public section

namespace Morphology

/-- A word token is a surface form with its category, in the Universal Dependencies
inventory, and its features. -/
structure Word where
  /-- The surface form. -/
  form : String
  /-- The category. -/
  cat : UD.UPOS
  /-- The features. -/
  features : Features := ⊥
  deriving Repr, DecidableEq

end Morphology
