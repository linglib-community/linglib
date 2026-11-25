/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Category.Determiner.Basic
public import Linglib.Morphology.Word.Basic

/-!
# Determiners as words

A determiner is realized as a bare word of the Universal Dependencies category `DET`.

## Main definitions

* `Determiner.toWord`: the determiner as a word.

## References

* [de-marneffe-zeman-2021]
-/

@[expose] public section

namespace Determiner

/-- A determiner is realized as a bare word of category `DET`. -/
def toWord (d : Determiner) : Morphology.Word := { form := d.form, cat := .DET }

end Determiner
