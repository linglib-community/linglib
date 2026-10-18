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

A word token is a surface form with its part of speech and its morphosyntactic features. It is
the morphosyntactic word, which Kalin and colleagues distinguish from the prosodic word of
`Phonology/Prosody/Word.lean`.

## Main definitions

* `Morphology.Word`: a word token.
* `Morphology.Word.mk'`: the token with a form and a part of speech and no features.

## References

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

/-- The featureless word with the given form and category. -/
def Word.mk' (form : String) (cat : UD.UPOS) : Word := { form := form, cat := cat }

instance : ToString Word where
  toString w := w.form

end Morphology
