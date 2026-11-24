/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

/-!
# Lexical entries as superset rules

A rule over a containment hierarchy is read as a lexical entry that stores the spine up to the
rule's span, and on spines the spellout of the entries is the spellout of the rules.

## TODO

* Move `LexicalEntry.ofSupersetRule` and `spellout_ofSupersetRule` here from
  `Morphology/Nanosyntax/Lexicon.lean`.
* `Morphology/Exponence/Containment/SupersetRule.lean` relates its rules to span rules directly;
  each should instead prove what it generates in the shared form, contiguity of the paradigm.

## References

* [starke-2009]
* [caha-2009]
-/
