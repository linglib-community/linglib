module

public import Linglib.Data.Experiments.Schema

/-!
# Yang2016: experimental results (generated)

Auto-generated from `Linglib/Data/Experiments/Yang2016.json` by `scripts/gen_experiments.py`.
Do not edit by hand: edit the JSON and re-run the generator.

Yang's counts of the plurals of the German feminine nouns: the feminine nouns of the child-directed
corpus of section 4.4 and the feminine plurals of the TIGER newspaper corpus, with the number of
them that take the *-(e)n* suffix. Page numbers are those of the 2016 MIT Press edition.

## References

* [yang-2016]
-/

@[expose] public section

namespace Yang2016

open Data.Experiments

/-- The two corpora in which Yang counts the feminine plurals. -/
inductive Corpus where
  /-- child-directed: the child-directed German corpus of section 4.4 -/
  | childDirected
  /-- TIGER: the TIGER newspaper corpus, which does not mark compounds -/
  | tiger
  deriving DecidableEq, Repr, Fintype

/-- A row of pp. 127–128: The feminine nouns counted in a corpus and the number of them whose
plural takes the -(e)n suffix. -/
structure FemininePluralRow where
  /-- The number of feminine nouns, in TIGER of feminine plurals. -/
  nouns : ℕ
  /-- The number of them whose plural takes the -(e)n suffix. -/
  enPlurals : ℕ
  deriving DecidableEq, Repr

/-- The cells of pp. 127–128, by corpus; checked against the page images. -/
def femininePlural : Corpus → FemininePluralRow
  | .childDirected => ⟨166, 146⟩  -- (31), p. 127: the other 20 take -e (13), -ø (6) and -s (1)
  | .tiger => ⟨1549, 1446⟩  -- p. 128

end Yang2016
