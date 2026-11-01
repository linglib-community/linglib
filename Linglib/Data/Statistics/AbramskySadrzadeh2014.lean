module

public import Linglib.Data.Statistics.Schema

/-!
# AbramskySadrzadeh2014: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/AbramskySadrzadeh2014.json` by
`scripts/gen_statistics.py`. Do not edit by hand: edit the JSON and re-run the generator.

The corpus frequencies behind the paper's probabilistic anaphora example (John gave the bananas to
the monkeys. They were ripe. They were cheeky.): the British News corpus counts of the four
adjective-noun patterns, and the printed distribution over the four candidate gluings. Locations are
sections of the arXiv preprint (1403.3351v1).

## References

* [abramsky-sadrzadeh-2014]
-/

@[expose] public section

namespace AbramskySadrzadeh2014

open Data.Statistics

/-- The predicative adjectives of the two anaphoric sentences. -/
inductive Adjective where
  /-- ripe: They were ripe. -/
  | ripe
  /-- cheeky: They were cheeky. -/
  | cheeky
  deriving DecidableEq, Repr, Fintype

/-- The candidate antecedents of the two pronouns. -/
inductive Noun where
  /-- banana: the bananas, the referent y -/
  | banana
  /-- monkey: the monkeys, the referent z -/
  | monkey
  deriving DecidableEq, Repr, Fintype

/-- A row of section 5, example: the British News corpus frequency of an adjective-noun pattern. -/
structure Frequency where
  /-- The number of occurrences. -/
  count : ℕ
  deriving DecidableEq, Repr

/-- The cells of section 5, example, by adjective and noun; counted in a corpus; checked against
the page images. -/
def frequency : Adjective → Noun → Frequency
  | .ripe, .banana => ⟨14⟩
  | .ripe, .monkey => ⟨0⟩
  | .cheeky, .banana => ⟨0⟩
  | .cheeky, .monkey => ⟨10⟩

/-- A row of section 5, example, the table of d: the printed probability d(t) of the gluing
resolving the first pronoun (ripe) and the second (cheeky) to the given antecedents. -/
structure GluingProbability where
  /-- The printed d(t). -/
  probability : Decimal
  deriving DecidableEq, Repr

/-- The cells of section 5, example, the table of d, by ripe and cheeky; fitted or simulated by a
model; checked against the page images. -/
def gluingProbability : Noun → Noun → GluingProbability
  | .banana, .banana => ⟨⟨29, 2⟩⟩
  | .banana, .monkey => ⟨⟨5, 1⟩⟩
  | .monkey, .banana => ⟨⟨0, 0⟩⟩
  | .monkey, .monkey => ⟨⟨205, 3⟩⟩  -- 10/48 is 0.208

end AbramskySadrzadeh2014
