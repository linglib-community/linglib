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
leaving specifiers and adjuncts aside. This file is to hold that map for each tree carrier, and
the heights at which the phrases off the spine attach.

## TODO

* The map from a constituency tree to its spine, from the head and projection relations of
  `Syntax/Projection/`.
* The map from a syntactic object to its spine, now `Minimalist.HorizonSetting.spineOf`, and the
  maps that studies define for themselves.
* The attachment height of a specifier or adjunct, which linearization reads.
-/
