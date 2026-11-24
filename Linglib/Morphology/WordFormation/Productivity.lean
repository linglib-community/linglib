/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

/-!
# Productivity

A morphological pattern or rule is productive if it can be applied to new bases to create new
words. Two measures of it are the degree of generalization, or profitability, the type frequency
of the pattern, and the degree of exhaustion, the ratio of the words that exhibit the pattern to
all the words in its domain.

## TODO

* The two measures are counts over a lexicon: for a pattern with a domain of bases, the number of
  words that exhibit it, and that number over the size of the domain. State them of a finite set
  of bases and a decidable pattern.
* `Studies/Yang2016.lean` states the Tolerance Principle, a threshold on the exceptions of a
  productive rule, and `Morphology/Exponence/DomainRule.lean` cites [odonnell-2015]; say what of
  productivity each states and what belongs here.
* Possible words, occasionalisms and blocking are in the chapter on productivity, which is not
  read yet.

## References

* [haspelmath-sims-2010]
* [odonnell-2015]
* [yang-2016]
-/
