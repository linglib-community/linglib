module

public import Linglib.Data.Experiments.Schema

/-!
# Sheehan2017b: experimental results (generated)

Auto-generated from `Linglib/Data/Experiments/Sheehan2017b.json` by `scripts/gen_experiments.py`.
Do not edit by hand: edit the JSON and re-run the generator.

The cross-linguistic positions of polar question particles and complementizers, from features 92A
and 94A of the World Atlas of Language Structures. A language counts as initial or final for each
head; the four combinations are the two consistent orders, an initial complementizer over a final
particle (the inverse of the final-over-final configuration) and a final complementizer over an
initial particle (the final-over-final configuration).

## References

* [sheehan-2017b]
-/

@[expose] public section

namespace Sheehan2017b

open Data.Experiments

/-- The position of a head in its phrase. -/
inductive Position where
  /-- Initial: before its complement -/
  | initial
  /-- Final: after its complement -/
  | final
  deriving DecidableEq, Repr, Fintype

/-- A row of Table 5.2, p. 92: the languages with each combination of the positions of the polar
question particle and the complementizer. -/
structure PolarityComplementizer where
  /-- The languages. -/
  languages : ℕ
  /-- Their genera. -/
  genera : ℕ
  /-- Their families. -/
  families : ℕ
  /-- The count printed in parentheses, which is the cross-tabulation of WALS features 92A and
  94A (recomputed by `scripts/experiments/Sheehan2017b.py`). -/
  inParentheses : ℕ
  deriving DecidableEq, Repr

/-- The cells of Table 5.2, p. 92, by pol and c; checked against the page images. -/
def polarityComplementizer : Position → Position → PolarityComplementizer
  | .initial, .initial => ⟨72, 35, 13, 78⟩
  | .final, .final => ⟨45, 33, 20, 46⟩
  | .final, .initial => ⟨74, 40, 16, 82⟩
  | .initial, .final => ⟨4, 3, 3, 4⟩

end Sheehan2017b
