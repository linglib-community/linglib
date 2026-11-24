/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Spine.Occurrence

/-!
# The order of the words of a spine

The words pronounced on a spine stand in an order with the phrases attached along it. On the rule
of Brody and of Svenonius a phrase attached at or above the position where a word is pronounced
precedes the word, and a phrase attached below it follows. This file is to hold the map from the
positions where words are pronounced, with the attachment heights of the phrases off the spine, to
an order of the words, a `WordOrder.Arrangement` in which several heads may share a rank.

## TODO

* The map, and the statement that the finite verb precedes a phrase exactly when it is
  pronounced above the height at which the phrase attaches.
* The relation to the accounts of linearization in `Syntax/Minimalist/Linearization/`.
* The order of the verbs of a periphrastic form, which English and German reverse relative to
  each other on the same `Tense.Form`.

## References

* [brody-2000]
* [svenonius-2016]
-/
