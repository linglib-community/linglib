/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Spine.Basic
public import Mathlib.Algebra.Free
public import Mathlib.Algebra.FreeMonoid.FreeSemigroup

/-!
# Words on a spine

Several heads of a spine may be pronounced as one word, at the position of one of them: a finite
verb with its tense in the position of T in French and of V in Danish. A word on a spine records
the position where it is pronounced and how its heads are grouped, a bracketing of them. Accounts
of how words are formed on a spine differ in which bracketings and positions they allow, so the
type allows all of them.

## Main definitions

* `Spine.Word`: a word on a spine, its site and the bracketing of its heads.
* `Spine.Word.heads`: the heads of a word, lowest first.

## References

* [harizanov-gribanova-2019]
* [arregi-pietraszko-2021]
-/

@[expose] public section

namespace Spine

open FreeMagma

variable {H : Type*}

/-- A word on a spine: the heads pronounced together, at the position of one of them. -/
structure Word (H : Type*) where
  /-- The head in whose position the word is pronounced. -/
  site : H
  /-- The grouping of the heads of the word, each product listing the lower constituent first. -/
  bracketing : FreeMagma H
  deriving DecidableEq, Repr

/-- The heads of a word, lowest first. -/
def Word.heads (w : Word H) : List H := (toFreeSemigroup w.bracketing).toFreeMonoid.toList

end Spine
