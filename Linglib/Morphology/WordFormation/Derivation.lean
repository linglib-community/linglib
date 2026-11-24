/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

/-!
# Derivation

Derivation is the relationship between the lexemes of a word family, as inflection is the
relationship between the word-forms of a lexeme. A lexeme is derived from another when it is
formed on the basis of it, its base, and is then a derivative of it. Derivational patterns have
relatively concrete meanings, may be semantically irregular and are restricted in the bases they
apply to.

## TODO

* A derivational pattern relates a base lexeme to its derivative, with a change of shape and of
  meaning. `Morphology.Word.Tree` has a constructor for each of affixation, compounding,
  reduplication and conversion, and the schemas of `Morphology/ConstructionMorphology/` relate
  the words of a pattern; a shared statement of derivation should serve both.
* The properties held to tell inflection from derivation, and the view that the two lie on a
  continuum, are in the chapter on inflection and derivation, which is not read yet.

## References

* [haspelmath-sims-2010]
* [booij-2012]
-/
