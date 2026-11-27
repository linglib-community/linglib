/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Category.Noun.Basic
public import Linglib.Morphology.Word.Basic

/-!
# Proper names as words

A proper name is realized as a word of the Universal Dependencies category `PROPN`, third person,
with the gender it restricts its referent to.

## Main definitions

* `ProperName.toWord`: the name as a word.

## References

* [de-marneffe-zeman-2021]
-/

@[expose] public section

/-- The word token of a name is a third-person `PROPN`, masculine or feminine by the gender it
restricts its referent to. -/
def ProperName.toWord (n : ProperName) : Morphology.Word :=
  { form := n.form, cat := .PROPN
    features := Morphology.Features.of (person := some .third)
      (gender := n.referentGender.map ReferentGender.toUD) }
