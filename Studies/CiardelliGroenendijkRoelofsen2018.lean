module

public import Linglib.Semantics.Questions.Basic

/-!
# Ciardelli, Groenendijk and Roelofsen 2018: Inquisitive Semantics

An information state is a set of possible worlds, an issue over it a non-empty downward-closed
set of its enhancements, and a proposition an issue over some state (Chapter 2): the states in it
settle it, it is true at a world when the singleton settles it, informative when its union, the
informative content, excludes a world, and inquisitive when that union does not itself settle
it, so that its alternatives, the maximal states in it, are several (Facts 2.14–2.19).
Entailment is inclusion, with the tautology and the contradiction as its extremes, and a context
is updated with a proposition by intersection, which reduces to standard update on
non-inquisitive inputs (Fact 2.36). Propositions form a Heyting algebra under meet, join and
relative pseudo-complement, and each is the meet of its non-inquisitive projection `!P` and its
non-informative projection `?P` (Chapter 3, Facts 3.1–3.15); polar, alternative, open
disjunctive and wh-questions, and their conjunctions, disjunctions and conditionalizations, are
these operations applied to declarative contents (Chapter 5).

The substrate `Semantics/Questions/` is this theory: `Question W` is the proposition, `info`,
`alt`, `IsInformative` and `IsInquisitive` its attributes, the lattice order its entailment with
`⊤`, `⊥`, `⊓`, `⊔` and `⇨` the operations, the double complement `Pᶜᶜ` and `query` the two
projections with `compl_compl_inf_query` the division law, the regular elements
(`Heyting.IsRegular`) the non-inquisitive propositions, and `polar` and `which` the polar and
mention-some forms.
This file proves the one Chapter 2 fact stated over two contents at once,
`update_nonInquisitive` (Fact 2.36). The logical language of Chapter 4 is the modal-free
fragment of `Inquisitive.Formula` (`Inquisitive.Formula.IsModalFree`); Chapters 6–9 are not
represented.

## References

* [I. Ciardelli, J. Groenendijk and F. Roelofsen, *Inquisitive Semantics*
  (2018)][ciardelli-groenendijk-roelofsen-2018]
-/

@[expose] public section

namespace CiardelliGroenendijkRoelofsen2018

variable {W : Type*}

open Question

/-- Updating a non-inquisitive context with a non-inquisitive proposition is non-inquisitive, with
the intersected informative content (Fact 2.36). -/
theorem update_nonInquisitive (C P : Question W) (hC : C.info ∈ C)
    (hP : P.info ∈ P) :
    (C ⊓ P).info ∈ C ⊓ P ∧ (C ⊓ P).info = C.info ∩ P.info := by
  refine ⟨?_, info_inf C P⟩
  show (C ⊓ P).info ∈ (C ⊓ P).props
  rw [info_inf]
  exact ⟨C.downward_closed C.info hC _ Set.inter_subset_left,
    P.downward_closed P.info hP _ Set.inter_subset_right⟩

end CiardelliGroenendijkRoelofsen2018
