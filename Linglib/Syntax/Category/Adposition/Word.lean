/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Category.Adposition.Basic
public import Linglib.Morphology.Word.Basic

/-!
# Adpositions as words

An adposition is realized as a word of the Universal Dependencies category `ADP`, with the
adposition's form.

## Main definitions

* `Adposition.toWord`: the adposition as a word.

## References

* [de-marneffe-zeman-2021]
-/

@[expose] public section

namespace Adposition

variable (a : Adposition)

/-- The adposition as a word, UD category `ADP`. A circumposition's pieces are separate words, and
its form joins them. -/
def toWord : Morphology.Word := { form := a.form, cat := .ADP }

@[simp] theorem cat_toWord : a.toWord.cat = .ADP := rfl

end Adposition
