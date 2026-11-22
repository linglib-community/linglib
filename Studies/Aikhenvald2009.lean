module

public import Mathlib.Data.Finset.Lattice.Basic
public import Linglib.Data.Examples.Aikhenvald2008
public import Linglib.Data.Examples.Aikhenvald2009
public import Linglib.Data.Examples.Gloss
public import Linglib.Fragments.Manambu.Clause
public import Linglib.Syntax.Clause.Linking

/-!
# Aikhenvald (2009): The Semantics of Clause Linking in Manambu

Manambu links clauses chiefly by chaining medial clauses before a final clause, and the chapter
sorts the language's devices by Dixon's semantic types of clause linking. `linkings` gives each
marker of medial clauses the kinds it marks: temporal succession for *-taka* and *-kǝb*, relative
time for *-ta:y*, relative time, same-event addition or real manner for *-n*, cause for *-lǝk*,
an unlikely condition for *-ga:y*, and relative time, cause or real condition for the completives
*-ku* and *-k*. The completives are thus polysemous over time, cause and condition, and each of
the three has a dedicated device: the completive verb *napa-*, which with a completive marker
leaves only the reading 'after' (`completiveLinkings`), the causal *-lǝk*, and *-ga:y*
(`polysemy_resolved`). Medial clauses mark every temporal kind (`temporal_marked`) and never
unordered addition (`unorderedAddition_not_marked`).

## Implementation notes

*-ta:y-kǝb*, which the chapter's summary table omits, is given the linking of *-kǝb*, whose
same-subject form it is. The conditional reading of a completive clause arises when the focal
clause is in the future, which is not modelled: a completive clause is predicted to allow all
three readings, and only the readings an example is given are compared. The examples of the 2008
grammar are those of its chapter on medial clauses.

## References

* [aikhenvald-2009]
* [aikhenvald-2008]
* [dixon-2009]
-/

@[expose] public section

namespace Aikhenvald2009

open Manambu MedialMarker Clause

/-- The kinds of clause linking a marker of medial clauses marks. -/
def linkings : MedialMarker → Finset Linking
  | ku | k => {.relativeTime, .cause, .conditional}
  | tay => {.relativeTime}
  | taka | keb | taykeb => {.succession}
  | lek => {.cause}
  | gay => {.conditional}
  | n => {.relativeTime, .sameEventAddition, .realManner}

/-- The kinds of linking a medial clause marks when *napa-* carries its marker, the succession or
relative time of the marker. -/
def completiveLinkings (m : MedialMarker) : Finset Linking :=
  linkings m ∩ {.succession, .relativeTime}

/-- Medial clauses mark every kind of temporal linking. -/
theorem temporal_marked {l : Linking} (h : l.type = .temporal) : ∃ m, l ∈ linkings m := by
  decide +revert

theorem unorderedAddition_not_marked (m : MedialMarker) : .unorderedAddition ∉ linkings m := by
  decide +revert

/-- Each kind of linking a completive marks has a device that marks it alone: *napa-* for relative
time, *-lǝk* for cause and *-ga:y* for condition. -/
theorem polysemy_resolved {m : MedialMarker} (hm : m = ku ∨ m = k) :
    linkings m = completiveLinkings m ∪ linkings lek ∪ linkings gay ∧
      completiveLinkings m = {.relativeTime} ∧ linkings lek = {.cause} ∧
      linkings gay = {.conditional} := by
  rcases hm with rfl | rfl <;> decide

theorem completiveLinkings_nonempty {m : MedialMarker} (h : m.WithCompletive) :
    (completiveLinkings m).Nonempty := by
  decide +revert

/-! ### The readings of completive clauses -/

/-- The row has the completive verb *napa-*. -/
def WithNapa (e : Datum) : Prop := ∃ w ∈ e.glossedWords, "COMPL.VB".toList ∈ w.glosses

instance : DecidablePred WithNapa := fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The kinds of linking a completive clause of the row is predicted to mark. -/
def predicted (e : Datum) (m : MedialMarker) : Finset Linking :=
  if WithNapa e then completiveLinkings m else linkings m

/-- The kind of linking of a reading of the chapter's examples. -/
def linking : Examples.Reading → Linking
  | .after => .relativeTime
  | .because => .cause
  | .condition => .conditional

/-- The kind of linking of a reading of the grammar's examples. -/
def linking₂₀₀₈ : Aikhenvald2008.Examples.Reading → Linking
  | .after => .relativeTime
  | .because => .cause

/-- A completive clause has the readings 'after', 'because' and 'if' the chapter gives it, and
with *napa-* only 'after': (10), (11), (12). -/
theorem readings {m : MedialMarker} (hm : m = ku ∨ m = k) :
    ∀ e ∈ Examples.all, ∀ r, ∀ j ∈ Examples.reading e r,
      (j = .acceptable ↔ linking r ∈ predicted e m) := by
  rcases hm with rfl | rfl <;> decide

/-- So do the grammar's completive clauses, (18.17) and (18.53). -/
theorem readings₂₀₀₈ {m : MedialMarker} (hm : m = ku ∨ m = k) :
    ∀ e ∈ Aikhenvald2008.Examples.all, ∀ r, ∀ j ∈ Aikhenvald2008.Examples.reading e r,
      (j = .acceptable ↔ linking₂₀₀₈ r ∈ predicted e m) := by
  rcases hm with rfl | rfl <;> decide

end Aikhenvald2009
