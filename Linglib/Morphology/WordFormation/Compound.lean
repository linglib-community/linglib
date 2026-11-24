/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

/-!
# Compounds

A compound is a complex lexeme made up of more than one lexeme stem. An endocentric compound
consists of a head and a dependent, and the source names coordinative, exocentric, appositional,
affix, phrasal and synthetic compounds beside it.

## TODO

* `Morphology.Word.Tree` has a constructor for compounding; a compound is a tree whose root is
  built by it, and its head is one of the two stems.
* The types of compounds and their hierarchical structure are in the chapter on morphological
  trees, which is not read yet.
* The distributional definition of the word (`Morphology/Word/Distributional.lean`) does not cover
  compounds.
* Compounds against phrases, and incorporation, which many studies treat and no shared file
  defines.

## References

* [haspelmath-sims-2010]
* [booij-2012]
-/
