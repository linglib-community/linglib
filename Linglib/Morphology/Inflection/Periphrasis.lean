/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

/-!
# Periphrasis

A periphrastic construction is a phrase of several words that expresses a set of inflectional
values together and fills a cell of an inflectional paradigm. In paradigmatic periphrasis a set
of values is always expressed periphrastically while each value of the set is expressed by a
single word elsewhere in the paradigm, as the Latin perfect passive is beside the perfect active
and the other passives.

## TODO

* A cell of a realization is periphrastic when a form that realizes it has several words, the
  words of a form being a map from forms to lists. `Studies/Bobaljik2012.lean` defines `Synthetic`
  and `Periphrastic` of a grade form this way, by `Morph.wordsAt`; state the two here once a
  second study uses them.
* Paradigmatic periphrasis is then a set of cells, all periphrastic, picked out by a conjunction
  of values none of which picks out only periphrastic cells
  (`Morphology/Inflection/Paradigm/Morphome.lean` has the conjunctions of values).
* Lexical and categorial periphrasis, which the source also distinguishes, are not read yet.

## References

* [haspelmath-sims-2010]
-/
