module

public import Linglib.Data.Experiments.Schema

/-!
# Labov2012: experimental results (generated)

Auto-generated from `Linglib/Data/Experiments/Labov2012.json` by `scripts/gen_experiments.py`.
Do not edit by hand: edit the JSON and re-run the generator.

Labov's figures for (ING) in Chapter 2: President Obama's percentage of *-in'* on three recorded
occasions of increasing formality. Page numbers are those of the 2014 paperback.

## References

* [labov-2012]
-/

@[expose] public section

namespace Labov2012

open Data.Experiments

/-- The three contextual styles of Figure 3, from the least to the most formal, each the occasion
of one recording. -/
inductive Style where
  /-- Casual: the Father's Day barbecue on the White House lawn, chatting with a chef about
  barbecue technique -/
  | casual
  /-- Careful: the Father's Day ceremonies that followed, asking and answering political
  questions -/
  | careful
  /-- Formal: the scripted acceptance speech at the Democratic National Convention -/
  | formal
  deriving DecidableEq, Repr, Fintype

/-- A row of Figure 3, pp. 13–14: President Obama's percentage of *-in'* out of all occurrences
of (ING) in a contextual style. -/
structure IngCell where
  /-- The percentage of *-in'*, as the text prints it. -/
  percent : ℕ
  deriving DecidableEq, Repr

/-- The cells of Figure 3, pp. 13–14, by style; checked against the page images. -/
def ingByStyle : Style → IngCell
  | .casual => ⟨72⟩
  | .careful => ⟨33⟩
  | .formal => ⟨3⟩

end Labov2012
