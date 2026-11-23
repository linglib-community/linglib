module

public import Linglib.Data.Statistics.Narrog2009
public import Mathlib.Order.Monotone.Defs

/-!
# Narrog (2009): Modality in Japanese

[narrog-2009a] tests eighteen modal markers of Modern Japanese against aspect, negation, tense,
nominalization and illocutionary modulation in a corpus, recording for each marker and category
whether the marker can embed the category, be embedded by it, or both (`Narrog2009.scopes`), and
arranges the markers in a table by scopal behavior, narrowest scope first.

We order the markers as that table lists them and say that a marker contradicts a marker listed
below it, with respect to a category, when the lower one has the narrower scope there
(`Contradicts`). Leaving nominalization aside, the contradictions are with respect to external
negation only: the predictive evidential *-soo* embeds it and the five deontic and boulomaic
markers listed after it do not, and the hortative is embedded by it while the reportive evidential
*-soo* and *daroo* are not (`contradicts_iff`). In non-matrix clauses the one contradiction is
between the reportive *-soo* and *daroo* (`clauseLayer_lt_iff`). Every contradiction with
respect to a category is of a non-volitive marker with a volitive one
(`Contradicts.not_isVolitive_and_isVolitive`), so the markers of each side of volitivity line up
without one, and the volitive markers do so in non-matrix clauses too
(`clauseLayer_le_of_isVolitive`).

## Implementation notes

A cell that the table marks as holding only in a resultative reading or only in the
counterfactual past is taken at face value. The layering among the modal markers themselves,
which the table summarizes in one column (`MarkerRow.layer`), is not derived from the pairwise
tables it rests on.

## References

* [narrog-2009a]
-/

@[expose] public section

namespace Narrog2009

/-- The markers in the order of the table, narrowest scope first. -/
instance : LinearOrder Marker := LinearOrder.lift' Marker.ctorIdx (by decide)

instance : LinearOrder Layer := LinearOrder.lift' Layer.ctorIdx (by decide)

instance : LinearOrder ClauseLayer := LinearOrder.lift' ClauseLayer.ctorIdx (by decide)

/-- A scope relation is narrower than another when it lies before it in the sequence embedded,
both, embedding; the absence of interaction is not compared. -/
def Scope.Narrower : Scope → Scope → Prop
  | .embedded, .both | .embedded, .embeds | .both, .embeds => True
  | _, _ => False

instance : DecidableRel Scope.Narrower :=
  fun s s' ↦ by cases s <;> cases s' <;> unfold Scope.Narrower <;> infer_instance

/-- A marker is volitive when it is boulomaic, deontic or a mood. -/
def Marker.IsVolitive (m : Marker) : Prop :=
  (markers m).category = .boulomaic ∨ (markers m).category = .deontic ∨
    (markers m).category = .mood

instance : DecidablePred Marker.IsVolitive := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- With respect to category `c`, marker `m` contradicts a marker `m'` listed after it when `m'`
has the narrower scope. -/
def Contradicts (c : Category) (m m' : Marker) : Prop :=
  m < m' ∧ (scopes m' c).scope.Narrower (scopes m c).scope

instance (c : Category) (m m' : Marker) : Decidable (Contradicts c m m') :=
  inferInstanceAs (Decidable (_ ∧ _))

-- The table is sorted by the layering among the modal markers.
theorem monotone_layer : Monotone fun m ↦ (markers m).layer := by decide

/-- Nominalization aside, the contradictions of the table are those of the predictive evidential
with the deontic and boulomaic markers listed after it, and of the reportive evidential and
*daroo* with the hortative, all with respect to external negation. -/
theorem contradicts_iff {c : Category} (hc : c ≠ .nominalization) (m m' : Marker) :
    Contradicts c m m' ↔ c = .externalNegation ∧
      (m = .soo1 ∧ m' ∈ [.tai, .teHosii, .nakerebaNaranai, .rebaIi, .beki] ∨
        m ∈ [.soo2, .daroo] ∧ m' = .hortative) := by
  revert c m m'; decide +kernel

/-- A contradiction is always of a non-volitive marker with a volitive marker listed after it, so
that neither the volitive nor the non-volitive markers contradict one another. -/
theorem Contradicts.not_isVolitive_and_isVolitive {c : Category} (hc : c ≠ .nominalization)
    {m m' : Marker} (h : Contradicts c m m') : ¬ m.IsVolitive ∧ m'.IsVolitive := by
  obtain ⟨-, ⟨rfl, h'⟩ | ⟨h', rfl⟩⟩ := (contradicts_iff hc m m').1 h
  · clear h; revert h'; cases m' <;> decide
  · clear h; revert h'; cases m <;> decide

/-- In non-matrix clauses the one pair listed against its layers is the reportive evidential and
*daroo*. -/
theorem clauseLayer_lt_iff (m m' : Marker) :
    m < m' ∧ (markers m').clauseLayer < (markers m).clauseLayer ↔ m = .soo2 ∧ m' = .daroo := by
  cases m <;> cases m' <;> decide

theorem clauseLayer_le_of_isVolitive {m m' : Marker} (hm : m.IsVolitive) (hm' : m'.IsVolitive)
    (h : m ≤ m') : (markers m).clauseLayer ≤ (markers m').clauseLayer := by
  by_contra hlt
  obtain ⟨rfl, rfl⟩ := (clauseLayer_lt_iff m m').1
    ⟨lt_of_le_of_ne h fun e ↦ hlt (e ▸ le_rfl), not_le.1 hlt⟩
  revert hm; decide

end Narrog2009
