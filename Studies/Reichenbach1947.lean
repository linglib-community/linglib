module

public import Linglib.Semantics.Tense.Reichenbach
public import Mathlib.Data.Fintype.Prod

/-!
# Reichenbach (1947): the tenses of verbs

Reichenbach analyses a tense by the order of three time points, the point of speech S, the point
of reference R and the point of the event E. The three points can be ordered in thirteen ways.
He groups the orders that agree on how R stands to S and how E stands to R into nine fundamental
forms, since the position of E relative to S is usually irrelevant: R is past, present or future
relative to S, and E is anterior, simple or posterior relative to R. A fundamental form groups
more than one order only when it is retrogressive, the direction from S to R opposite to the
direction from R to E, and the posterior past and the anterior future each group three.

An order is recorded here by the comparisons of R with S, of E with R and of E with S, the last
one that the first two allow under composition (`structures`). The frame of any three points has
one of them and three points realize each, so there are thirteen. The fundamental forms are their
first two comparisons, nine in all, and a form groups as many orders as the composition of its two
positions has elements, more than one exactly for the two retrogressive forms.

## Main definitions

* `Reichenbach1947.structures`: the orders of S, R and E, as their three comparisons.

## Main results

* `Reichenbach1947.mem_structures`, `Reichenbach1947.exists_points`: the frame of three points
  has one of the orders, and every order is realized by three points.
* `Reichenbach1947.card_structures`, `Reichenbach1947.card_fundamentalForms`: thirteen orders
  and nine fundamental forms.
* `Reichenbach1947.card_filter_form`, `Reichenbach1947.one_lt_card_comp_iff`: a fundamental form
  groups as many orders as its composition has elements, more than one exactly when the form is
  the posterior past or the anterior future.

## Implementation notes

Reichenbach's frames are the `ReichenbachFrame.root` frames, the perspective at the point of
speech.

## References

* [reichenbach-1947]
-/

@[expose] public section

namespace Reichenbach1947

open Tense

/-- An order of S, R and E is recorded as the comparisons of R with S, of E with R and of E with S,
the last one that the composition of the first two allows. -/
def structures : Finset (Ordering × Ordering × Ordering) :=
  Finset.univ.filter fun x ↦ x.2.2 ∈ x.2.1.comp x.1

/-- The frame of three points has one of the orders. -/
theorem mem_structures {T : Type*} [LinearOrder T] (s r e : T) :
    ((ReichenbachFrame.root s r e).referencePosition, (ReichenbachFrame.root s r e).eventPosition,
      compare e s) ∈ structures := by
  simpa [structures] using (ReichenbachFrame.root s r e).compare_eventTime_perspectiveTime_mem

/-- Three points realize every order. -/
theorem exists_points :
    ∀ x ∈ structures, ∃ s r e : Fin 3, (compare r s, compare e r, compare e s) = x := by
  decide

/-- The three points can be ordered in thirteen ways (p. 296). -/
theorem card_structures : structures.card = 13 := by decide

/-- There are nine fundamental forms (p. 296). -/
theorem card_fundamentalForms : (structures.image fun x ↦ (x.1, x.2.1)).card = 9 := by decide

/-- A fundamental form groups as many orders as the composition of its two positions has
elements. -/
theorem card_filter_form (a b : Ordering) :
    (structures.filter fun x ↦ x.1 = a ∧ x.2.1 = b).card = (b.comp a).card := by
  revert a b; decide

/-- More than one order obtains only for the two retrogressive forms, in which the direction from
S to R is opposite to the direction from R to E: the posterior past and the anterior future
(p. 297). -/
theorem one_lt_card_comp_iff (a b : Ordering) :
    1 < (b.comp a).card ↔ (a = .lt ∧ b = .gt) ∨ (a = .gt ∧ b = .lt) := by
  revert a b; decide

end Reichenbach1947
