/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Spine.Basic

/-!
# The spine of a tree

The spine of a phrase is read off its tree by following each head to the head of its complement,
leaving specifiers and adjuncts aside. This file is to hold that map for a constituency tree,
`PhraseStructure.Tree`, and the heights at which the phrases off the spine attach. A framework's
own structure has its spine in the framework, in a file named for the spine, as
`Minimalist.HorizonSetting.spineOf` is for a syntactic object.

## TODO

* The map from a constituency tree to its spine, from the head and projection relations of
  `Syntax/Projection/`.
* The attachment height of a specifier or adjunct, which linearization reads.
-/
