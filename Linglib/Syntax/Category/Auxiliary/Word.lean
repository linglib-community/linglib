/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Word.Basic
public import Linglib.Syntax.Category.Auxiliary.Basic

/-!
# The token of an auxiliary

The token of an auxiliary is the word of its form and its features, of the Universal Dependencies
class `AUX`.

## Main definitions

* `Auxiliary.toWord`: the token of an auxiliary.

## References

* [de-marneffe-zeman-2021]
-/

@[expose] public section

/-- The token of an auxiliary, an `AUX` word with its form and features. -/
def Auxiliary.toWord (a : Auxiliary) : Morphology.Word :=
  { form := a.form, cat := .AUX, features := a.features }
